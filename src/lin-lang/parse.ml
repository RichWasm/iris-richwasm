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
    | MalformedInfixArity of Path.t * Sexp.t list
    | MalformedInfixSep of Path.t * Sexp.t
    | MalformedInjTag of Path.t * string
    | ExpectedBinding of Path.t * Sexp.t
    | ExpectedBinop of Path.t * Sexp.t
    | ExpectedValue of Path.t * Sexp.t
    | MalformedTuple of Path.t * Sexp.t
    | ExpectedExpr of Path.t * Sexp.t
    | ExpectedCase of Path.t * Sexp.t
    | ExpectedImport of Path.t * Sexp.t
    | ExpectedTopLevel of Path.t * Sexp.t
    | ExpectedModule of Sexp.t list
    | ParseError of Parsexp.Parse_error.t
  [@@deriving sexp_of]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Res = Util.ResultM (Err)

let rec parse_type (p : Path.t) : Sexp.t -> Type.t Res.t =
  let open Res in
  function
  | Atom "int" -> ret @@ Type.Int
  | Atom x -> ret @@ Type.Var x
  | List [ Atom "ref"; t ] ->
      let* t' = parse_type (Tag "ref" :: p) t in
      ret @@ Type.Ref t'
  | List [ t1; Atom ("⊸" | "-o" | "->"); t2 ] ->
      let p = Path.add p ~tag:"lollipop" in
      let* t1' = parse_type (p ~field:"t1") t1 in
      let* t2' = parse_type (p ~field:"t2") t2 in
      ret @@ Type.Lollipop (t1', t2')
  | List (Atom "prod" :: ts) ->
      let* ts' =
        mapiM ~f:(fun i x -> parse_type (Idx i :: Tag "prod" :: p) x) ts
      in
      ret @@ Type.Prod ts'
  | List (Atom "sum" :: ts) ->
      let* ts' =
        mapiM ~f:(fun i x -> parse_type (Idx i :: Tag "sum" :: p) x) ts
      in
      ret @@ Type.Sum ts'
  | List [ Atom "rec"; Atom x; t ] ->
      let* t' = parse_type (Path.add p ~tag:"rec" ~field:"t") t in
      ret @@ Type.Rec (x, t')
  | List lst ->
      let n = List.length lst in
      if Int.equal (n % 2) 0 && n <> 0 then
        fail Err.(MalformedInfixArity (p, lst))
      else
        let rec go i (kind : [ `Prod | `Sum ] option) (acc : Type.t list) =
          function
          | [] ->
              ret
                (match Option.value ~default:`Prod kind with
                | `Prod -> Type.Prod (List.rev acc)
                | `Sum -> Type.Sum (List.rev acc))
          | t :: ts -> (
              if Int.equal (i % 2) 0 then
                let tag =
                  match kind with
                  | Some `Sum -> "sum"
                  | Some `Prod -> "prod"
                  | None -> "prod?"
                in
                let* t' = parse_type (Idx i :: Tag tag :: p) t in
                go (i + 1) kind (t' :: acc) ts
              else
                let valid_prod = function
                  | Some `Prod | None -> true
                  | _ -> false
                in
                let valid_sum = function
                  | Some `Sum | None -> true
                  | _ -> false
                in
                match t with
                | Atom ("⊗" | "*") when valid_prod kind ->
                    go (i + 1) (Some `Prod) acc ts
                | Atom ("⊕" | "+") when valid_sum kind ->
                    go (i + 1) (Some `Sum) acc ts
                | x -> fail Err.(MalformedInfixSep (Idx i :: p, x)))
        in
        go 0 None [] lst

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
        mapiM ~f:(fun i x -> parse_value (Idx i :: Tag "tup" :: p) x) vs
      in
      ret @@ Value.Tuple vs'
  | List [ Atom "inj"; Atom i; v; Atom ":"; typ ]
  | List [ Atom "inj"; Atom i; v; typ ] ->
      let* i =
        match Int.of_string_opt i with
        | Some i -> ret i
        | None -> fail Err.(MalformedInjTag (p, i))
      in
      let p = Path.add p ~tag:"inj" in
      let* v' = parse_value (p ~field:"v") v in
      let* typ' = parse_type (p ~field:"typ") typ in
      ret @@ Value.Inj (i, v', typ')
  | List [ Atom "fold"; t; v ] ->
      let p = Path.add p ~tag:"fold" in
      let* t' = parse_type (p ~field:"t") t in
      let* v' = parse_value (p ~field:"v") v in
      ret @@ Value.Fold (t', v')
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
  | List (Atom "split" :: rst) as sexp ->
      let p : Path.t = Tag "split" :: p in
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
        | _ -> fail Err.(ExpectedExpr (p, List (Atom "split" :: rst)))
      in
      let* e1' = parse_expr (Field "e1" :: p) e1 in
      let* e2' = parse_expr (Field "e2" :: p) e2 in
      ret @@ Expr.Split (bindings', e1', e2')
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
  | List (Atom "cases" :: scrutinee :: cases) ->
      let p : Path.t = Tag "cases" :: p in
      let* scrutinee' = parse_value (Field "scrutinee" :: p) scrutinee in
      let* cases' =
        mapiM
          ~f:(fun i ->
            let p : Path.t = Idx i :: Field "cases" :: p in
            function
            | List [ Atom "case"; binding; expr ] ->
                let p : Path.t = Tag "case" :: p in
                let* binding' = parse_binding (Field "binding" :: p) binding in
                let* expr' = parse_expr (Field "expr" :: p) expr in
                ret (binding', expr')
            | s -> fail Err.(ExpectedCase (p, s)))
          cases
      in
      ret @@ Expr.Cases (scrutinee', cases')
  | List [ Atom "unfold"; t; v ] ->
      let p = Path.add p ~tag:"unfold" in
      let* t' = parse_type (p ~field:"t") t in
      let* v' = parse_value (p ~field:"v") v in
      ret @@ Expr.Unfold (t', v')
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

let parse_function (p : Path.t) : Sexp.t -> Function.t Res.t =
  let open Res in
  let help ?(export = false) name maybe_param maybe_return maybe_body =
    let tag = Stdlib.Format.sprintf "fun:%s" name in
    let* param = parse_binding (Path.add ~tag ~field:"param" p) maybe_param in
    let* return = parse_type (Path.add ~tag ~field:"return" p) maybe_return in
    let* body = parse_expr (Path.add ~tag ~field:"body" p) maybe_body in
    ret @@ Function.{ export; name; param; return; body }
  in
  function
  | List
      ( [
          Atom "export";
          Atom "fun";
          Atom name;
          param;
          Atom ":";
          return;
          Atom ".";
          body;
        ]
      | [ Atom "export"; Atom "fun"; Atom name; param; return; body ] ) ->
      help ~export:true name param return body
  | List
      ( [ Atom "fun"; Atom name; param; Atom ":"; return; Atom "."; body ]
      | [ Atom "fun"; Atom name; param; return; body ] ) ->
      help name param return body
  | x -> fail Err.(ExpectedTopLevel (p, x))

let parse_module (p : Path.t) : Sexp.t list -> Module.t Res.t =
  let open Res in
  function
  | [] -> ret @@ Module.make ()
  | sexps ->
      let rec classify imports functions main_opt : Sexp.t list -> 'a = function
        | [] -> Ok (List.rev imports, List.rev functions, main_opt)
        | sexp :: rest -> (
            match sexp with
            | List (Atom "import" :: _) ->
                let* import = parse_import p sexp in
                classify (import :: imports) functions main_opt rest
            | List (Atom ("export" | "fun") :: _) ->
                let* fn = parse_function p sexp in
                classify imports (fn :: functions) main_opt rest
            | _ -> (
                match (main_opt, rest) with
                | None, [] ->
                    let* main = parse_expr p sexp in
                    classify imports functions (Some main) []
                | _, _ -> fail Err.(ExpectedModule sexps)))
      in
      let+ imports, functions, main = classify [] [] None sexps in
      Module.{ imports; functions; main }

let from_string (s : string) : Module.t Res.t =
  let open Res in
  match Parsexp.Many.parse_string s with
  | Error x -> fail (Err.ParseError x)
  | Ok sexps -> parse_module Path.empty sexps

let from_string_exn (s : string) : Module.t =
  match from_string s with
  | Ok x -> x
  | Error x -> failwith (Stdlib.Format.asprintf "Failed %a" Err.pp x)
