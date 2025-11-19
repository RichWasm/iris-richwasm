open! Base
open Sexplib
open Syntax
open Richwasm_common.Monads

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
    | ParseError of Parsexp.Parse_error.t
    | ExpectedExpr of Path.t * Sexp.t
    | ExpectedType of Path.t * Sexp.t
    | ExpectedTypeVar of Path.t * Sexp.t
    | ExpectedBind of Path.t * Sexp.t
    | InvalidOp of Path.t * string
    | InvalidIndex of Path.t * string
    | InvalidCaseBranch of Path.t * Sexp.t
    | InvalidImport of Path.t * Sexp.t
    | InvalidItem of Path.t * Sexp.t
    | ExpectedExportType of Path.t * string
    | InvalidModule of Sexp.t list
  [@@deriving sexp_of]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)

  let path_of = function
    | ExpectedExpr (p, _)
    | ExpectedType (p, _)
    | ExpectedTypeVar (p, _)
    | ExpectedBind (p, _)
    | InvalidIndex (p, _)
    | InvalidCaseBranch (p, _)
    | InvalidImport (p, _)
    | InvalidItem (p, _)
    | ExpectedExportType (p, _)
    | InvalidOp (p, _) -> p
    | ParseError _ | InvalidModule _ -> Path.empty

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

module Res = ResultM (Err)

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

let parse_type_var p =
  let open Res in
  function
  | Sexp.Atom v -> ret v
  | s -> fail @@ ExpectedTypeVar (p, s)

let rec parse_type p : Sexp.t -> Source.PreType.t Res.t =
  let open Path in
  let open Res in
  let open Source.PreType in
  function
  | Atom "int" -> ret @@ Int
  | Atom x -> ret @@ Var x
  | List [ List foralls; t1; Atom "->"; t2 ] ->
      let p = Path.add p ~tag:"arrow" in
      let* foralls' =
        foralls
        |> List.mapi ~f:(fun i ->
            parse_type_var (p ~field:("t" ^ Int.to_string i)))
        |> Res.all
      in
      let* t1' = parse_type (p ~field:"t1") t1 in
      let* t2' = parse_type (p ~field:"t2") t2 in
      ret @@ Fun { foralls = foralls'; arg = t1'; ret = t2' }
  | List (Atom "*" :: ts) ->
      let* ts' =
        ts
        |> List.mapi ~f:(fun i ->
            parse_type (Path.add p ~tag:"prod" ~field:("t" ^ Int.to_string i)))
        |> Res.all
      in
      ret @@ Prod ts'
  | List (Atom "+" :: ts) ->
      let* ts' =
        ts
        |> List.mapi ~f:(fun i ->
            parse_type (Path.add p ~tag:"sum" ~field:("t" ^ Int.to_string i)))
        |> Res.all
      in
      ret @@ Sum ts'
  | List [ Atom "ref"; t ] ->
      let* t' = parse_type (Tag "ref" :: p) t in
      ret @@ Ref t'
  | List [ Atom "rec"; List [ Atom v ]; t ] ->
      let* t' = parse_type (Path.add p ~tag:"rec" ~field:"t") t in
      ret @@ Rec (v, t')
  | v -> fail @@ ExpectedType (p, v)

let parse_bind p : Sexp.t -> Source.Binding.t Res.t =
  let open Res in
  let open Path in
  function
  | List [ Atom var; Atom ":"; t ] ->
      let* t' =
        parse_type (Path.add p ~commit:false ~field:"typ" ~tag:"bind") t
      in
      ret (var, t')
  | x -> fail @@ ExpectedBind (p, x)

let rec parse_expr p : Sexp.t -> Source.Expr.t Res.t =
  let open Res in
  let open Path in
  let open Source.Expr in
  function
  | Atom a ->
      ret
      @@
        (match Int.of_string_opt a with
        | None -> Var a
        | Some i -> Int i)
  | List (Atom "tup" :: es) ->
      let* es' =
        es
        |> List.mapi ~f:(fun i ->
            parse_expr (Path.add p ~tag:"tuple" ~field:("v" ^ Int.to_string i)))
        |> Res.all
      in
      ret @@ Tuple es'
  | List [ Atom "inj"; Atom i; e; Atom ":"; t ] ->
      let* i' =
        match Int.of_string_opt i with
        | Some i -> ret i
        | None -> fail @@ InvalidIndex (p, i)
      in
      let p = Path.add p ~tag:"inj" in
      let* e' = parse_expr (p ~field:"e") e in
      let* t' = parse_type (p ~field:"t") t in
      ret @@ Inj (i', e', t')
  | List [ Atom "app"; f; List ts; arg ] ->
      let p = Path.add p ~tag:"app" in
      let* f' = parse_expr (p ~field:"f") f in
      let* ts' = ts |> List.map ~f:(parse_type (p ~field:"ts")) |> Res.all in
      let* arg' = parse_expr (p ~field:"arg") arg in
      ret @@ Apply (f', ts', arg')
  | List [ Atom "proj"; Atom i; e ] ->
      let* i' =
        match Int.of_string_opt i with
        | Some i -> ret i
        | None -> fail @@ InvalidIndex (p, i)
      in
      let p = Path.add p ~tag:"proj" in
      let* e' = parse_expr (p ~field:"e") e in
      ret @@ Project (i', e')
  | List [ Atom "op"; Atom o; l; r ] ->
      let* o' =
        match o with
        | "+" -> ret `Add
        | "-" -> ret `Sub
        | "*" -> ret `Mul
        | "/" -> ret `Div
        | _ -> fail @@ InvalidOp (p, o)
      in
      let p = Path.add p ~tag:"op" in
      let* l' = parse_expr (p ~field:"l") l in
      let* r' = parse_expr (p ~field:"r") r in
      ret @@ Op (o', l', r')
  | List [ Atom "if"; c; t; e ] ->
      let p = Path.add p ~tag:"if" in
      let* c' = parse_expr (p ~field:"cond") c in
      let* t' = parse_expr (p ~field:"then") t in
      let* e' = parse_expr (p ~field:"else") e in
      ret @@ If0 (c', t', e')
  | List [ Atom "new"; e ] ->
      let* e' = parse_expr (Path.add p ~tag:"new" ~field:"e") e in
      ret @@ New e'
  | List [ Atom "!"; e ] ->
      let* e' = parse_expr (Path.add p ~tag:"deref" ~field:"e") e in
      ret @@ Deref e'
  | List [ Atom "assign"; r; v ] ->
      let p = Path.add p ~tag:"assign" in
      let* r' = parse_expr (p ~field:"e") r in
      let* v' = parse_expr (p ~field:"e") v in
      ret @@ Assign (r', v')
  | List [ Atom "fold"; t; e ] ->
      let p = Path.add p ~tag:"fold" in
      let* t' = parse_type (p ~field:"t") t in
      let* e' = parse_expr (p ~field:"e") e in
      ret @@ Fold (t', e')
  | List [ Atom "unfold"; e ] ->
      let* e' = parse_expr (Path.add p ~tag:"unfold" ~field:"e") e in
      ret @@ Unfold e'
  | List [ Atom "let"; b; e1; e2 ] ->
      let p = Path.add p ~tag:"let" in
      let* b' = parse_bind (p ~field:"bind") b in
      let* e1' = parse_expr (p ~field:"e1") e1 in
      let* e2' = parse_expr (p ~field:"e1") e2 in
      ret @@ Let (b', e1', e2')
  | List [ Atom "fun"; List foralls; b; Atom ":"; t; e ]
  | List [ Atom "lam"; List foralls; b; Atom ":"; t; e ] ->
      let p = Path.add p ~tag:"fun" in
      let* foralls' =
        foralls
        |> List.mapi ~f:(fun i ->
            parse_type_var (p ~field:("var" ^ Int.to_string i)))
        |> Res.all
      in
      let* b' = parse_bind (p ~field:"bind") b in
      let* t' = parse_type (p ~field:"ret") t in
      let* e' = parse_expr (p ~field:"body") e in
      ret @@ Fun { foralls = foralls'; arg = b'; ret_type = t'; body = e' }
  | List (Atom "cases" :: e :: branches) ->
      let p = Tag "cases" :: p in
      let* e' = parse_expr (Field "e" :: p) e in
      let parse_branch idx =
        let p = Idx idx :: Field "cases" :: p in
        function
        | Sexp.List [ b; e ] ->
            let* b' = parse_bind (Field "bind" :: p) b in
            let* e' = parse_expr (Field "e" :: p) e in
            ret (b', e')
        | s -> fail @@ InvalidCaseBranch (p, s)
      in
      let* branches' = branches |> List.mapi ~f:parse_branch |> Res.all in
      ret @@ Cases (e', branches')
  | s -> fail @@ ExpectedExpr (p, s)

let parse_import p : Sexp.t -> Source.Module.import Res.t =
  let open Path in
  let open Res in
  function
  | List [ Atom "import"; b ] ->
      let* b' = parse_bind (Tag "import" :: Field "bind" :: p) b in
      ret @@ Source.Module.Import b'
  | s -> fail @@ InvalidImport (p, s)

let parse_fun p : Sexp.t -> Source.Module.item Res.t =
  let open Path in
  let open Res in
  let pack v (b, e) =
    let open Source.Module in
    match v with
    | "export" -> ret @@ Export (b, e)
    | "private" -> ret @@ Private (b, e)
    | s -> fail @@ ExpectedExportType (p, s)
  in
  function
  | List [ Atom t; bind; f ] ->
      let repack = pack t in
      let* bind' = parse_bind (Tag "item" :: Field "bind" :: p) bind in
      let* f' = parse_expr (Tag "item" :: Field "f" :: p) f in
      let* item = repack (bind', f') in
      ret item
  | s -> fail @@ InvalidItem (p, s)

let parse_module p : Sexp.t list -> Source.Module.t Res.t =
  let open Res in
  let open Path in
  let open Source.Module in
  function
  | [] -> ret @@ Module ([], [], None)
  | sexps ->
      let rec classify imports items body : Sexp.t list -> 'a = function
        | [] -> Ok (List.rev imports, List.rev items, body)
        | (List (Atom "import" :: _) as imp) :: rest ->
            let* import = parse_import p imp in
            classify (import :: imports) items body rest
        | (List (Atom ("export" | "private") :: _) as item) :: rest ->
            let* f = parse_fun p item in
            classify imports (f :: items) body rest
        | b :: rest ->
            (match (body, rest) with
            | None, [] ->
                let* body' = parse_expr p b in
                classify imports items (Some body') []
            | _ -> fail @@ InvalidModule sexps)
      in
      let+ imports, items, body = classify [] [] None sexps in
      Module (imports, items, body)

let from_string s =
  let open Res in
  match Parsexp.Many.parse_string s with
  | Error err -> fail @@ ParseError err
  | Ok sexps -> parse_module Path.empty sexps

let from_string_exn s =
  match from_string s with
  | Ok m -> m
  | Error err -> failwith (Stdlib.Format.asprintf "Failed %a" Err.pp err)
