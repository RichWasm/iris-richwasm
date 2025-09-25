open! Base
open Sexplib
open Syntax
open Result

module Path = struct
  type seg =
    | Tag of string
    | Field of string
    | Idx of int
  [@@deriving sexp]

  type t = seg list [@@deriving sexp]

  let empty : t = []

  let add (ctx : t) ~(tag : string) ~(field : string) =
    Field field :: Tag tag :: ctx
end

module Err = struct
  type t =
    | ExpectedType of Path.t * Sexp.t
    | MalformedProdArity of Path.t * Sexp.t list
    | MalformedProdSep of Path.t * Sexp.t
    | ExpectedBinding of Path.t * Sexp.t
    | ExpectedBinop of Path.t * Sexp.t
    | ExpectedValue of Path.t * Sexp.t
    | MalformedTuple of Path.t * Sexp.t
    | ExpectedExpr of Path.t * Sexp.t
    | ExpectedImport of Path.t * Sexp.t
    | ExpectedTopLevel of Path.t * Sexp.t
    | ExpectedModule of Sexp.t list
    | ParseError of (Parsexp.Parse_error.t[@sexp.opaque])
  [@@deriving sexp]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Res = Util.ResultM (Err)

let rec parse_type (p : Path.t) : Sexp.t -> Type.t Res.t =
  let open Res in
  function
  | Atom "int" -> ret @@ Type.Int
  | List [ Atom "ref"; t ] ->
      let* t' = parse_type (Tag "ref" :: p) t in
      ret @@ Type.Ref t'
  | List [ t1; Atom "⊸"; t2 ]
  | List [ t1; Atom "-o"; t2 ]
  | List [ t1; Atom "->"; t2 ] ->
      let p = Path.add p ~tag:"lollipop" in
      let* t1' = parse_type (p ~field:"t1") t1 in
      let* t2' = parse_type (p ~field:"t2") t2 in
      ret @@ Type.Lollipop (t1', t2')
  | List (Atom "prod" :: ts) ->
      let* ts' =
        List.mapi ~f:(fun i x -> parse_type (Idx i :: Tag "prod" :: p) x) ts
        |> Result.all
      in
      ret @@ Type.Prod ts'
  | List lst ->
      let n = List.length lst in
      if Int.equal (n % 2) 0 then
        fail Err.(MalformedProdArity (p, lst))
      else
        let* ts =
          List.mapi
            ~f:(fun i t ->
              let p' : Path.t = Idx i :: Tag "prod" :: p in
              if Int.equal (i % 2) 0 then
                let* t' = parse_type p' t in
                ret @@ Some t'
              else
                match t with
                | Atom ("⊗" | "*") -> Ok None
                | x -> fail Err.(MalformedProdSep (p', x)))
            lst
          |> Result.all
        in
        let ts =
          List.fold ~init:[]
            ~f:(fun acc x ->
              match x with
              | None -> acc
              | Some x -> x :: acc)
            ts
          |> List.rev
        in
        ret @@ Type.Prod ts
  | x -> fail Err.(ExpectedType (p, x))

let parse_binding (p : Path.t) : Sexp.t -> Binding.t Res.t =
  let open Res in
  function
  | List [ Atom var; Atom ":"; typ ] | List [ Atom var; typ ] ->
      let* typ' = parse_type (Path.add p ~field:"typ" ~tag:"binding") typ in
      ret (var, typ')
  | x -> fail Err.(ExpectedBinding (p, x))

let parse_binop (p : Path.t) : Sexp.t -> Binop.t Res.t =
  let open Res in
  function
  | Atom "+" -> ret Binop.Add
  | Atom "-" -> ret Binop.Sub
  | Atom ("×" | "*") -> ret Binop.Mul
  | Atom ("÷" | "/") -> ret Binop.Div
  | x -> fail Err.(ExpectedBinop (p, x))

let rec parse_value (p : Path.t) : Sexp.t -> Value.t Res.t =
  let open Res in
  function
  | Atom x -> (
      match Int.of_string_opt x with
      | Some x -> ret @@ Value.Int x
      | None -> ret @@ Value.Var x)
  | List [ Atom ("λ" | "lam"); binding; Atom ":"; ret_t; Atom "."; body ]
  | List [ Atom ("λ" | "lam"); binding; ret_t; body ] ->
      let p = Path.add p ~tag:"lam" in
      let* binding' = parse_binding (p ~field:"binding") binding in
      let* ret_t' = parse_type (p ~field:"ret_t") ret_t in
      let* body' = parse_expr (p ~field:"body") body in
      ret @@ Value.Lam (binding', ret_t', body')
  | List (Atom "tup" :: vs) ->
      let* vs' =
        List.mapi ~f:(fun i x -> parse_value (Idx i :: Tag "tup" :: p) x) vs
        |> Result.all
      in
      ret @@ Value.Tuple vs'
      (* FIXME: nested tuples are broken *)
  | List atoms ->
      (* Check if this is a comma-separated tuple eq (1, 2, 3) *)
      let rec check_and_parse acc idx : Sexp.t list -> 'a = function
        | [] -> ret (List.rev acc)
        | [ Atom last ] ->
            if String.contains last ',' then
              fail Err.(MalformedTuple (p, List atoms))
            else
              let* v = parse_value (Idx idx :: Tag "tuple" :: p) (Atom last) in
              ret (List.rev (v :: acc))
        | Atom s :: rest ->
            if String.is_suffix s ~suffix:"," then
              let s' = String.drop_suffix s 1 in
              let* v = parse_value (Idx idx :: Tag "tuple" :: p) (Atom s') in
              check_and_parse (v :: acc) (idx + 1) rest
            else
              fail Err.(MalformedTuple (p, List atoms))
        | _ -> fail Err.(ExpectedValue (p, List atoms))
      in
      let* values = check_and_parse [] 0 atoms in
      ret @@ Value.Tuple values

and parse_expr (p : Path.t) : Sexp.t -> Expr.t Res.t =
  let open Res in
  function
  | List [ Atom "app"; v1; v2 ] ->
      let p = Path.add p ~tag:"app" in
      let* v1' = parse_value (p ~field:"v1") v1 in
      let* v2' = parse_value (p ~field:"v2") v2 in
      ret @@ Expr.App (v1', v2')
  | List [ Atom "let"; binding; Atom "="; e1; Atom "in"; e2 ]
  | List [ Atom "let"; binding; e1; e2 ] ->
      let p = Path.add p ~tag:"let" in
      let* binding' = parse_binding (p ~field:"binding") binding in
      let* e1' = parse_expr (p ~field:"e1") e1 in
      let* e2' = parse_expr (p ~field:"e2") e2 in
      ret @@ Expr.Let (binding', e1', e2')
  | List (Atom "letprod" :: rst) as sexp ->
      let p : Path.t = Tag "letprod" :: p in
      (* Split on "=" to separate bindings from expressions *)
      let rec split_on_eq acc : Sexp.t list -> (Sexp.t list * Sexp.t list) Res.t
          = function
        | [] -> fail Err.(ExpectedExpr (p, sexp))
        | Atom "=" :: rest -> Ok (List.rev acc, rest)
        | x :: xs -> split_on_eq (x :: acc) xs
      in
      let* bindings, rest = split_on_eq [] rst in
      let* bindings' =
        List.mapi
          ~f:(fun i b -> parse_binding (Idx i :: Field "bindings" :: p) b)
          bindings
        |> Result.all
      in
      let* e1, e2 =
        match rest with
        | [ e1; Atom "in"; e2 ] -> Ok (e1, e2)
        | [ e1; e2 ] -> Ok (e1, e2)
        | _ -> fail Err.(ExpectedExpr (p, List (Atom "letprod" :: rst)))
      in
      let* e1' = parse_expr (Field "e1" :: p) e1 in
      let* e2' = parse_expr (Field "e2" :: p) e2 in
      ret @@ Expr.LetProd (bindings', e1', e2')
  | List [ Atom "if0"; v; Atom "then"; e1; Atom "else"; e2 ]
  | List [ Atom "if0"; v; e1; e2 ] ->
      let p = Path.add p ~tag:"if0" in
      let* v' = parse_value (p ~field:"v") v in
      let* e1' = parse_expr (p ~field:"e1") e1 in
      let* e2' = parse_expr (p ~field:"e2") e2 in
      ret @@ Expr.If0 (v', e1', e2')
  | List [ Atom "new"; v ] ->
      let* v' = parse_value (Tag "new" :: p) v in
      ret @@ Expr.New v'
  | List [ Atom "swap"; v1; v2 ] ->
      let p = Path.add p ~tag:"swap" in
      let* v1' = parse_value (p ~field:"v1") v1 in
      let* v2' = parse_value (p ~field:"v2") v2 in
      ret @@ Expr.Swap (v1', v2')
  | List [ Atom "free"; v ] ->
      let* v' = parse_value (Tag "free" :: p) v in
      ret @@ Expr.Free v'
  | List [ f1; f2; f3 ] -> (
      let p' = Path.add p ~tag:"binop" in
      (* try (op l r) if (l op r) fails (assumes valid op is not variable name) *)
      let foo =
        match parse_binop (p' ~field:"op-f2") f2 with
        | Ok x -> Ok (x, f1, f3)
        | Error err -> (
            match parse_binop (p' ~field:"op-f1") f1 with
            | Ok x -> Ok (x, f2, f3)
            | Error _ -> Error err)
      in
      match foo with
      | Ok (op', v1, v2) ->
          let* v1' = parse_value (p' ~field:"v1") v1 in
          let* v2' = parse_value (p' ~field:"v2") v2 in
          ret @@ Expr.Binop (op', v1', v2')
      | Error err -> (
          match
            parse_value
              (Tag "[VAL]" :: Tag "<BINOP>" :: p)
              (List [ f1; f2; f3 ] : Sexp.t)
          with
          | Ok v -> ret @@ Expr.Val v
          | Error _ -> Error err))
  | List [ l; r ] -> (
      match parse_value (Tag "[VAL]" :: p) (List [ l; r ] : Sexp.t) with
      | Ok v -> ret @@ Expr.Val v
      | Error _ ->
          parse_expr (Tag "[APP]" :: p) (List [ Atom "app"; l; r ] : Sexp.t))
  | x ->
      let* v = parse_value (Tag "val" :: p) x in
      ret @@ Expr.Val v

let parse_import (p : Path.t) : Sexp.t -> Import.t Res.t =
  let open Res in
  function
  | List [ Atom "import"; t; Atom "as"; Atom x ]
  | List [ Atom "import"; t; Atom x ] ->
      let* t' = parse_type (Path.add ~tag:"import" ~field:"t" p) t in
      ret @@ Import.{ name = x; typ = t' }
  | x -> fail Err.(ExpectedImport (p, x))

let parse_toplevel (p : Path.t) : Sexp.t -> TopLevel.t Res.t =
  let open Res in
  let help ?(export = false) binding e =
    let* binding' =
      parse_binding (Path.add ~tag:"tl let" ~field:"binding" p) binding
    in
    let* init' = parse_expr (Path.add ~tag:"tl let" ~field:"e" p) e in
    ret @@ TopLevel.{ export; binding = binding'; init = init' }
  in
  function
  | List [ Atom "export"; Atom "let"; binding; e ] ->
      help ~export:true binding e
  | List [ Atom "let"; binding; e ] -> help binding e
  | x -> fail Err.(ExpectedTopLevel (p, x))

let parse_module (p : Path.t) : Sexp.t list -> Module.t Res.t =
  let open Res in
  function
  | [] -> ret @@ Module.make ()
  | sexps ->
      let rec classify imports toplevels main_opt : Sexp.t list -> 'a = function
        | [] -> Ok (List.rev imports, List.rev toplevels, main_opt)
        | sexp :: rest -> (
            match sexp with
            | List (Atom "import" :: _) ->
                let* import = parse_import p sexp in
                classify (import :: imports) toplevels main_opt rest
            | List (Atom "export" :: _) ->
                let* tl = parse_toplevel p sexp in
                classify imports (tl :: toplevels) main_opt rest
            | List [ Atom "let"; _; _ ] ->
                (* tl let only 3 elems *)
                let* tl = parse_toplevel p sexp in
                classify imports (tl :: toplevels) main_opt rest
            | _ -> (
                match (main_opt, rest) with
                | None, [] ->
                    let* main = parse_expr p sexp in
                    classify imports toplevels (Some main) []
                | _, _ -> fail Err.(ExpectedModule sexps)))
      in
      let* imports, toplevels, main = classify [] [] None sexps in
      ret @@ Module.{ imports; toplevels; main }

let from_string (s : string) : Module.t Res.t =
  let open Res in
  match Parsexp.Many.parse_string s with
  | Error x -> fail (Err.ParseError x)
  | Ok sexps -> parse_module Path.empty sexps

let from_string_exn (s : string) : Module.t =
  match from_string s with
  | Ok x -> x
  | Error x -> failwith (Stdlib.Format.asprintf "Failed %a" Err.pp x)
