open Base

(* de Bruijn indices *)
module Indexed = struct
  open Sexplib.Std
  open Syntax

  type typ = Types.typ
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type binop = Types.binop
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type gvar = string
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type value =
    | Var of int
    | Global of gvar
    | Int of int
    | Lam of typ * typ * expr
    | Prod of value * value
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  and expr =
    | Val of value
    | App of value * value
    | Let of typ * expr * expr
    | If0 of value * expr * expr
    | Binop of binop * value * value
    (* let (x:tx, y:ty) = rhs in body; y -> 0, x -> 1 *)
    | LetPair of typ * typ * expr * expr
    | New of value
    | Swap of value * value
    | Free of value
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type import = Types.import
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type toplevel = TopLevel of bool * (string * typ) * expr
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type modul = Module of import list * toplevel list * expr option
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]
end

module IndexErr = struct
  type t
end

module Index = struct
  module A = Syntax.Types
  module B = Indexed
  open Result.Let_syntax

  type 'a index_res = ('a, IndexErr.t) Result.t
  type env = string list

  let rec compile_value (env : env) (value : A.value) : B.value index_res =
    match value with
    | Var x ->
        (match List.findi ~f:(fun _ -> String.equal x) env with
        | Some (i, _) -> B.Var i
        | None -> B.Global x)
        (* assumes WF *)
        |> return
    | Int n -> return @@ B.Int n
    | Lam ((var, typ), ret, body) ->
        let env' = var :: env in
        let%bind body' = compile_expr env' body in
        return @@ B.Lam (typ, ret, body')
    | Prod (l, r) ->
        let%bind l' = compile_value env l in
        let%bind r' = compile_value env r in
        return @@ B.Prod (l', r')

  and compile_expr (env : env) (expr : A.expr) : B.expr index_res =
    match expr with
    | Val v ->
        let%bind v' = compile_value env v in
        return @@ B.Val v'
    | App (l, r) ->
        let%bind l' = compile_value env l in
        let%bind r' = compile_value env r in
        return @@ B.App (l', r')
    | Let ((var, typ), e, body) ->
        let%bind e' = compile_expr env e in
        let env' = var :: env in
        let%bind body' = compile_expr env' body in
        return @@ B.Let (typ, e', body')
    | If0 (v, e1, e2) ->
        let%bind v' = compile_value env v in
        let%bind e1' = compile_expr env e1 in
        let%bind e2' = compile_expr env e2 in
        return @@ B.If0 (v', e1', e2')
    | Binop (op, l, r) ->
        let%bind l' = compile_value env l in
        let%bind r' = compile_value env r in
        return @@ B.Binop (op, l', r')
    | LetPair ((var1, typ1), (var2, typ2), e, body) ->
        let%bind e' = compile_expr env e in
        let env' = var2 :: var1 :: env in
        let%bind body' = compile_expr env' body in
        return @@ B.LetPair (typ1, typ2, e', body')
    | New v ->
        let%bind v' = compile_value env v in
        return @@ B.New v'
    | Swap (l, r) ->
        let%bind l' = compile_value env l in
        let%bind r' = compile_value env r in
        return @@ B.Swap (l', r')
    | Free v ->
        let%bind v' = compile_value env v in
        return @@ B.Free v'

  let compile_toplevel (TopLevel (exported, binding, init) : A.toplevel) :
      B.toplevel index_res =
    let%bind init' = compile_expr [] init in
    return @@ B.TopLevel (exported, binding, init')

  let compile_module (modul : A.modul) : B.modul index_res =
    match modul with
    | Module (imports, toplevels, main) ->
        let%bind toplevels' =
          List.map ~f:compile_toplevel toplevels |> Result.all
        in
        let%bind main' =
          match main with
          | Some e -> compile_expr [] e >>| Option.some
          | None -> return None
        in
        return @@ Indexed.Module (imports, toplevels', main')
end
