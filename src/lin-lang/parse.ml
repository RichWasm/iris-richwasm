open! Base
open Sexplib
open Syntax
open Result

module Path = struct
  type seg =
    | Tag of string
    | Field of string
    | Idx of int
    | Choice of string
    | Alt of string
    | Commit
  [@@deriving sexp]

  type t = seg list [@@deriving sexp]

  let empty : t = []
  let length : Path.t -> int = List.length

  let add ?(commit = true) ~(tag : string) ~(field : string) (ctx : t) =
    if commit then
      Field field :: Commit :: Tag tag :: ctx
    else
      Field field :: Tag tag :: ctx

  let choose (p : t) (name : string) : t = Choice name :: p
  let alt (p : t) (alt : string) : t = Alt alt :: p
  let commit (p : t) : t = Commit :: p

  let score (p : t) : int * int =
    let commits, depth =
      List.fold_left
        ~f:(fun (c, d) -> function
          | Commit -> (c + 1, d + 1)
          | _ -> (c, d + 1))
        ~init:(0, 0) p
    in
    (commits, depth)
end

module Err = struct
  type t =
    | ExpectedType of Path.t * Sexp.t
    | MalformedInfixArity of Path.t * Sexp.t list
    | MalformedInfixSep of Path.t * Sexp.t
    | MalformedInjTag of Path.t * string
    | ExpectedBinding of Path.t * Sexp.t
    | ExpectedBinop of Path.t * Sexp.t
    | MalformedTuple of Path.t * Sexp.t
    | ExpectedTupElem of Path.t * Sexp.t
    | ExpectedExpr of Path.t * Sexp.t
    | ExpectedCase of Path.t * Sexp.t
    | ExpectedImport of Path.t * Sexp.t
    | ExpectedTopLevel of Path.t * Sexp.t
    | ExpectedModule of Sexp.t list
    | ParseError of Parsexp.Parse_error.t
  [@@deriving sexp_of]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let path_of = function
    | ExpectedType (p, _)
    | MalformedInfixArity (p, _)
    | MalformedInfixSep (p, _)
    | MalformedInjTag (p, _)
    | ExpectedBinding (p, _)
    | ExpectedBinop (p, _)
    | MalformedTuple (p, _)
    | ExpectedTupElem (p, _)
    | ExpectedExpr (p, _)
    | ExpectedCase (p, _)
    | ExpectedImport (p, _)
    | ExpectedTopLevel (p, _) -> p
    | ExpectedModule _ | ParseError _ -> Path.empty

  let prefer (e1 : t) (e2 : t) : t =
    let cmp_score (c1, d1) (c2, d2) =
      match Int.compare c1 c2 with
      | 0 -> Int.compare d1 d2
      | n -> n
    in
    let s1 = Path.score (path_of e1) in
    let s2 = Path.score (path_of e2) in
    if cmp_score s1 s2 >= 0 then e1 else e2
end

module Res = Util.ResultM (Err)

let choice
    (name : string)
    (p : Path.t)
    (sexp : Sexp.t)
    (alts : ((Path.t -> Sexp.t -> 'a Res.t) * string) list) : 'a Res.t =
  let p_choice = Path.choose p name in
  let rec go best = function
    | [] ->
        (match best with
        | None -> Error Err.(ExpectedExpr (p_choice, sexp))
        | Some e -> Error e)
    | (f, alt_name) :: fs ->
        let p_alt = Path.alt p_choice alt_name in
        (match f p_alt sexp with
        | Ok x -> Ok x
        | Error e ->
            let best' =
              Some
                (match best with
                | None -> e
                | Some b -> Err.prefer b e)
            in
            go best' fs)
  in
  go None alts

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
  | List [ Atom "rec"; Atom x; t ] | List [ Atom "rec"; Atom x; Atom "."; t ] ->
      let* t' = parse_type (Path.add p ~tag:"rec" ~field:"t") t in
      ret @@ Type.Rec (x, t')
  | List lst ->
      let n = List.length lst in
      let* () =
        fail_if
          (Int.equal (n % 2) 0 && n <> 0)
          Err.(MalformedInfixArity (p, lst))
      in
      let rec go i (kind : [ `Prod | `Sum ] option) (acc : Type.t list) =
        function
        | [] ->
            ret
              (match Option.value ~default:`Prod kind with
              | `Prod -> Type.Prod (List.rev acc)
              | `Sum -> Type.Sum (List.rev acc))
        | t :: ts ->
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
              (match t with
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
      let* typ' =
        parse_type (Path.add p ~commit:false ~field:"typ" ~tag:"binding") typ
      in
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

let rec parse_expr (p : Path.t) : Sexp.t -> Expr.t Res.t =
  let open Res in
  let open Expr in
  function
  | List [ Atom "app"; left; right ] ->
      let p = Path.add p ~tag:"app" in
      let* left' = parse_expr (p ~field:"left") left in
      let* right' = parse_expr (p ~field:"right") right in
      ret @@ App (left', right')
  | List [ Atom "let"; binding; Atom "="; lhs; Atom "in"; body ]
  | List [ Atom "let"; binding; lhs; body ] ->
      let p = Path.add p ~tag:"let" in
      let* binding' = parse_binding (p ~field:"binding") binding in
      let* lhs' = parse_expr (p ~field:"lhs") lhs in
      let* body' = parse_expr (p ~field:"body") body in
      ret @@ Let (binding', lhs', body')
  | List (Atom "split" :: rst) as sexp ->
      let p : Path.t = Commit :: Tag "split" :: p in
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
      let* rhs, body =
        match rest with
        | [ rhs; Atom "in"; body ] | [ rhs; body ] -> Ok (rhs, body)
        | _ -> fail Err.(ExpectedExpr (p, List (Atom "split" :: rst)))
      in
      let* rhs' = parse_expr (Field "rhs" :: p) rhs in
      let* body' = parse_expr (Field "body" :: p) body in
      ret @@ Split (bindings', rhs', body')
  | List [ Atom "if0"; cond; Atom "then"; thn; Atom "else"; els ]
  | List [ Atom "if0"; cond; thn; els ] ->
      let p = Path.add p ~tag:"if0" in
      let* cond' = parse_expr (p ~field:"cond") cond in
      let* thn' = parse_expr (p ~field:"thn") thn in
      let* els' = parse_expr (p ~field:"els") els in
      ret @@ If0 (cond', thn', els')
  | List [ Atom "swap"; e1; e2 ] ->
      let p = Path.add p ~tag:"swap" in
      let* e1' = parse_expr (p ~field:"e1") e1 in
      let* e2' = parse_expr (p ~field:"e2") e2 in
      ret @@ Swap (e1', e2')
  | List [ Atom "free"; e ] ->
      let* e' = parse_expr (Tag "free" :: p) e in
      ret @@ Expr.Free e'
  | List (Atom "cases" :: scrutinee :: cases) ->
      let p : Path.t = Tag "cases" :: p in
      let* scrutinee' = parse_expr (Field "scrutinee" :: p) scrutinee in
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
      ret @@ Cases (scrutinee', cases')
  | List [ Atom "unfold"; mu; e ] ->
      let p = Path.add p ~tag:"unfold" in
      let* mu' = parse_type (p ~field:"mu") mu in
      let* e' = parse_expr (p ~field:"e") e in
      ret @@ Unfold (mu', e')
  | Atom x ->
      (match Int.of_string_opt x with
      | Some x -> ret @@ Int x
      | None -> ret @@ Var x)
  | List [ Atom ("λ" | "lam"); binding; Atom ":"; ret_t; Atom "."; body ]
  | List [ Atom ("λ" | "lam"); binding; ret_t; body ] ->
      let p = Path.add p ~tag:"lam" in
      let* binding' = parse_binding (p ~field:"binding") binding in
      let* ret_t' = parse_type (p ~field:"ret_t") ret_t in
      let* body' = parse_expr (p ~field:"body") body in
      ret @@ Lam (binding', ret_t', body')
  | List (Atom "tup" :: es) ->
      let* es' =
        mapiM
          ~f:(fun i x -> parse_expr (Idx i :: Commit :: Tag "tup" :: p) x)
          es
      in
      ret @@ Tuple es'
  | List [ Atom "inj"; Atom i; e; Atom ":"; typ ]
  | List [ Atom "inj"; Atom i; e; typ ] ->
      let* i =
        match Int.of_string_opt i with
        | Some i -> ret i
        | None -> fail Err.(MalformedInjTag (p, i))
      in
      let p = Path.add p ~tag:"inj" in
      let* e' = parse_expr (p ~field:"e") e in
      let* typ' = parse_type (p ~field:"typ") typ in
      ret @@ Inj (i, e', typ')
  | List [ Atom "fold"; mu; e ] ->
      let p = Path.add p ~tag:"fold" in
      let* mu' = parse_type (p ~field:"mu") mu in
      let* e' = parse_expr (p ~field:"e") e in
      ret @@ Fold (mu', e')
  | List [ Atom "new"; e ] ->
      let* e' = parse_expr (Commit :: Tag "new" :: p) e in
      ret @@ New e'
  | List [ _; _ ] as sexp ->
      choice "generic-2-list" p sexp
        [ (parse_as_tup, "len-2-tup"); (parse_as_app, "no-kw-app") ]
  | List [ _; _; _ ] as sexp ->
      choice "generic-3-list" p sexp
        [
          (parse_as_tup, "len-3-tup");
          (parse_as_binop ~fix:`In, "infix-binop");
          (parse_as_binop ~fix:`Pre, "prefix-binop");
        ]
  | sexp -> parse_as_tup p sexp

and parse_as_binop ~(fix : [ `In | `Pre ]) (p : Path.t) (sexp : Sexp.t) :
    Expr.t Res.t =
  let open Res in
  let open Expr in
  let p' =
    Path.add p ~commit:false
      ~tag:
        (match fix with
        | `In -> "infix-binop"
        | `Pre -> "prefix-binop")
  in
  let parse (op : Binop.t) (left : Sexp.t) (right : Sexp.t) =
    let* v1' = parse_expr (p' ~field:"left") left in
    let* v2' = parse_expr (p' ~field:"right") right in
    ret @@ Binop (op, v1', v2')
  in
  match (sexp, fix) with
  | List [ op; left; right ], `Pre ->
      let* op' = parse_binop (p' ~field:"op") op in
      parse op' left right
  | List [ left; op; right ], `In ->
      let* op' = parse_binop (p' ~field:"op") op in
      parse op' left right
  | x, _ -> fail Err.(ExpectedExpr (p, x))

and parse_as_app (p : Path.t) : Sexp.t -> Expr.t Res.t = function
  | List [ l; r ] -> parse_expr p (List [ Atom "app"; l; r ] : Sexp.t)
  | x -> fail Err.(ExpectedExpr (p, x))

(* comma-separated tuple eg. (1, 2, 3) *)
and parse_as_tup (p : Path.t) : Sexp.t -> Expr.t Res.t =
  let open Res in
  let open Expr in
  function
  | List atoms ->
      let rec check_and_parse acc idx : Sexp.t list -> 'a =
        let p' = Path.Idx idx :: Tag "tuple" :: p in
        function
        | [] -> ret (List.rev acc)
        | [ Atom last ] ->
            let* () =
              fail_if
                (String.is_suffix last ~suffix:",")
                Err.(MalformedTuple (p', List atoms))
            in
            let+ expr = parse_expr p' (Atom last) in
            List.rev (expr :: acc)
        | [ sexp ] ->
            let+ expr = parse_expr p' sexp in
            List.rev (expr :: acc)
        | Atom s :: rest ->
            let* () =
              fail_ifn
                (String.is_suffix s ~suffix:",")
                Err.(MalformedTuple (p', List atoms))
            in
            let s' = String.drop_suffix s 1 in
            let* expr = parse_expr p' (Atom s') in
            check_and_parse (expr :: acc) (idx + 1) rest
        | expr :: Atom "," :: rest ->
            let* expr' = parse_expr p' expr in
            check_and_parse (expr' :: acc) (idx + 1) rest
        | _ -> fail Err.(ExpectedTupElem (p', List atoms))
      in
      let* values = check_and_parse [] 0 atoms in
      ret @@ Tuple values
  | x -> fail Err.(ExpectedExpr (p, x))

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
        | sexp :: rest ->
            (match sexp with
            | List (Atom "import" :: _) ->
                let* import = parse_import p sexp in
                classify (import :: imports) functions main_opt rest
            | List (Atom ("export" | "fun") :: _) ->
                let* fn = parse_function p sexp in
                classify imports (fn :: functions) main_opt rest
            | _ ->
                (match (main_opt, rest) with
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
