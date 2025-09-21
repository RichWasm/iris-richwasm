open! Base

module LVar = struct
  module T = struct
    type t = int * string option
    [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

    let compare (i1, _) (i2, _) = Int.compare i1 i2
  end

  include T
  include Comparator.Make (T)
end

(* de Bruijn indices *)
module Indexed = struct
  open Sexplib.Std
  open Syntax

  type typ = Types.typ
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type binop = Types.binop
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type lvar = LVar.t
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type gvar = string
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type value =
    | Var of lvar
    | Global of gvar
    | Int of int
    | Lam of typ * typ * expr
    | Tuple of value list
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  and expr =
    | Val of value
    | App of value * value
    | Let of typ * expr * expr
    | If0 of value * expr * expr
    | Binop of binop * value * value
    (* let (x_0:ty_0, ..., x_n:ty_n) = rhs in body; x_n -> 0, x_0 -> n *)
    | LetProd of typ list * expr * expr
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
  type t = UnknownGlobal of string
end

module Index = struct
  module A = Syntax.Types
  module B = Indexed

  type 'a index_res = ('a, IndexErr.t) Result.t
  type env = string list

  open Result.Let_syntax

  let rec compile_value (env : env) (value : A.value) : B.value index_res =
    match value with
    | Var x ->
        (match List.findi ~f:(fun _ -> String.equal x) env with
        | Some (i, n) -> B.Var (i, Some n)
        | None -> B.Global x)
        (* assumes WF *)
        |> return
    | Int n -> return @@ B.Int n
    | Lam ((var, typ), ret, body) ->
        let env' = var :: env in
        let%bind body' = compile_expr env' body in
        return @@ B.Lam (typ, ret, body')
    | Tuple vs ->
        let%bind vs' = vs |> List.map ~f:(compile_value env) |> Result.all in
        return @@ B.Tuple vs'

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
    | LetProd (bindings, e, body) ->
        let%bind e' = compile_expr env e in
        let vars, typs = List.unzip bindings in
        let env' = List.rev vars @ env in
        let%bind body' = compile_expr env' body in
        return @@ B.LetProd (typs, e', body')
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

  let compile_module (Module (imports, toplevels, main) : A.modul) :
      B.modul index_res =
    let%bind toplevels' =
      List.map ~f:compile_toplevel toplevels |> Result.all
    in
    let%bind main' =
      match main with
      | Some e -> compile_expr [] e >>| Option.some
      | None -> return None
    in
    return @@ B.Module (imports, toplevels', main')
end
