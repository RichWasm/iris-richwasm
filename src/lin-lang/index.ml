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

module IR = struct
  (* de Bruijn indices *)

  module Type = struct
    include Syntax.Type

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end

  module Binop = struct
    include Syntax.Binop

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end

  module rec Value : sig
    type t =
      | Var of LVar.t
      | Global of string
      | Int of int
      | Lam of Type.t * Type.t * Expr.t
      | Tuple of t list
    [@@deriving eq, ord, iter, map, fold, sexp]

    val pp : Stdlib.Format.formatter -> t -> unit
  end = struct
    type t =
      | Var of LVar.t
      | Global of string
      | Int of int
      | Lam of Type.t * Type.t * Expr.t
      | Tuple of t list
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end

  and Expr : sig
    type t =
      | Val of Value.t
      | App of Value.t * Value.t
      | Let of Type.t * t * t
      | If0 of Value.t * t * t
      | Binop of Binop.t * Value.t * Value.t
      (* let (x_0:ty_0, ..., x_n:ty_n) = rhs in body; x_n -> 0, x_0 -> n *)
      | LetProd of Type.t list * t * t
      | New of Value.t
      | Swap of Value.t * Value.t
      | Free of Value.t
    [@@deriving eq, ord, iter, map, fold, sexp]

    val pp : Stdlib.Format.formatter -> t -> unit
  end = struct
    type t =
      | Val of Value.t
      | App of Value.t * Value.t
      | Let of Type.t * t * t
      | If0 of Value.t * t * t
      | Binop of Binop.t * Value.t * Value.t
      | LetProd of Type.t list * t * t
      | New of Value.t
      | Swap of Value.t * Value.t
      | Free of Value.t
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end

  module Import = struct
    type t = Syntax.Import.t [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end

  module TopLevel = struct
    type t = {
      export : bool;
      binding : string * Type.t;
      init : Expr.t;
    }
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end

  module Module = struct
    type t = {
      imports : Import.t list;
      toplevels : TopLevel.t list;
      main : Expr.t option;
    }
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end
end

module Compile = struct
  module A = Syntax
  module B = IR

  type env = string list

  let rec compile_value (env : env) : A.Value.t -> B.Value.t =
    let open B.Value in
    function
    | Var x -> (
        match List.findi ~f:(fun _ -> String.equal x) env with
        | Some (i, n) -> Var (i, Some n)
        | None -> Global x (* assumes WF *))
    | Int n -> Int n
    | Lam ((var, typ), ret, body) ->
        let env' = var :: env in
        let body' = compile_expr env' body in
        Lam (typ, ret, body')
    | Tuple vs ->
        let vs' = List.map ~f:(compile_value env) vs in
        Tuple vs'

  and compile_expr (env : env) : A.Expr.t -> B.Expr.t =
    let open B.Expr in
    function
    | Val v ->
        let v' = compile_value env v in
        Val v'
    | App (l, r) ->
        let l' = compile_value env l in
        let r' = compile_value env r in
        App (l', r')
    | Let ((var, typ), e, body) ->
        let e' = compile_expr env e in
        let env' = var :: env in
        let body' = compile_expr env' body in
        Let (typ, e', body')
    | If0 (v, e1, e2) ->
        let v' = compile_value env v in
        let e1' = compile_expr env e1 in
        let e2' = compile_expr env e2 in
        If0 (v', e1', e2')
    | Binop (op, l, r) ->
        let l' = compile_value env l in
        let r' = compile_value env r in
        Binop (op, l', r')
    | LetProd (bindings, e, body) ->
        let e' = compile_expr env e in
        let vars, typs = List.unzip bindings in
        let env' = List.rev vars @ env in
        let body' = compile_expr env' body in
        LetProd (typs, e', body')
    | New v ->
        let v' = compile_value env v in
        New v'
    | Swap (l, r) ->
        let l' = compile_value env l in
        let r' = compile_value env r in
        Swap (l', r')
    | Free v ->
        let v' = compile_value env v in
        Free v'

  let compile_toplevel ({ export; binding; init } : A.TopLevel.t) : B.TopLevel.t
      =
    let init' = compile_expr [] init in
    B.TopLevel.{ export; binding; init = init' }

  let compile_module ({ imports; toplevels; main } : A.Module.t) : B.Module.t =
    let toplevels' = List.map ~f:compile_toplevel toplevels in
    let main' = Option.map ~f:(compile_expr []) main in
    B.Module.{ imports; toplevels = toplevels'; main = main' }
end
