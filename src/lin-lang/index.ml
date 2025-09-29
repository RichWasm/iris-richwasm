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
      | Coderef of string
      | Int of int
      | Lam of Type.t * Type.t * Expr.t
      | Tuple of t list
      | Inj of int * t * Type.t
    [@@deriving eq, ord, iter, map, fold, sexp]

    val pp : Stdlib.Format.formatter -> t -> unit
  end = struct
    type t =
      | Var of LVar.t
      | Coderef of string
      | Int of int
      | Lam of Type.t * Type.t * Expr.t
      | Tuple of t list
      | Inj of int * t * Type.t
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
      (* split (x_0:ty_0, ..., x_n:ty_n) = rhs in body; x_n -> 0, x_0 -> n *)
      | Split of Type.t list * t * t
      | Cases of Value.t * (Type.t * t) list
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
      | Split of Type.t list * t * t
      | Cases of Value.t * (Type.t * t) list
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

  module Function = struct
    type t = {
      export : bool;
      name : string;
      param : Type.t;
      return : Type.t;
      body : Expr.t;
    }
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end

  module Module = struct
    type t = {
      imports : Import.t list;
      functions : Function.t list;
      main : Expr.t option;
    }
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end
end

module Err = struct
  type t = UnboundLocal of string [@@deriving sexp]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Res = Util.ResultM (Err)

module Compile = struct
  module A = Syntax
  module B = IR

  module Env = struct
    type t = {
      locals : string list;
      fn_names : string list;
    }

    let empty = { locals = []; fn_names = [] }

    let resolve_name (env : t) (name : string) :
        [ `Local of int * string | `Function of string | `NotFound ] =
      match List.findi ~f:(fun _ -> String.equal name) env.locals with
      | Some (i, n) -> `Local (i, n)
      | None -> (
          match List.mem env.fn_names name ~equal:String.equal with
          | true -> `Function name
          | false -> `NotFound)

    let add (env : t) (lname : string) : t =
      { env with locals = lname :: env.locals }

    let add_all (env : t) (lnames : string list) : t =
      { env with locals = List.rev lnames @ env.locals }
  end

  let rec compile_value (env : Env.t) : A.Value.t -> B.Value.t Res.t =
    let open B.Value in
    let open Res in
    function
    | Var x -> (
        match Env.resolve_name env x with
        | `Local (i, n) -> Ok (Var (i, Some n))
        | `Function n -> Ok (Coderef n)
        | `NotFound -> Error (UnboundLocal x))
    | Int n -> ret (Int n)
    | Lam ((var, typ), return, body) ->
        let env' = Env.add env var in
        let* body' = compile_expr env' body in
        ret (Lam (typ, return, body'))
    | Tuple vs ->
        let* vs' = mapM ~f:(compile_value env) vs in
        ret (Tuple vs' : B.Value.t)
    | Inj (i, v, t) ->
        let* v' = compile_value env v in
        ret (Inj (i, v', t))

  and compile_expr (env : Env.t) : A.Expr.t -> B.Expr.t Res.t =
    let open B.Expr in
    let open Res in
    function
    | Val v ->
        let* v' = compile_value env v in
        ret @@ Val v'
    | App (l, r) ->
        let* l' = compile_value env l in
        let* r' = compile_value env r in
        ret @@ App (l', r')
    | Let ((var, typ), e, body) ->
        let* e' = compile_expr env e in
        let env' = Env.add env var in
        let* body' = compile_expr env' body in
        ret @@ Let (typ, e', body')
    | Split (bindings, e, body) ->
        let* e' = compile_expr env e in
        let vars, typs = List.unzip bindings in
        let env' = Env.add_all env vars in
        let* body' = compile_expr env' body in
        ret @@ Split (typs, e', body')
    | Cases (scrutinee, cases) ->
        let* scrutinee' = compile_value env scrutinee in
        let* cases' =
          mapM
            ~f:(fun ((x, t), body) ->
              let env' = Env.add env x in
              let+ body' = compile_expr env' body in
              (t, body'))
            cases
        in
        ret @@ Cases (scrutinee', cases')
    | If0 (v, e1, e2) ->
        let* v' = compile_value env v in
        let* e1' = compile_expr env e1 in
        let* e2' = compile_expr env e2 in
        ret @@ If0 (v', e1', e2')
    | Binop (op, l, r) ->
        let* l' = compile_value env l in
        let* r' = compile_value env r in
        ret @@ Binop (op, l', r')
    | New v ->
        let* v' = compile_value env v in
        ret @@ New v'
    | Swap (l, r) ->
        let* l' = compile_value env l in
        let* r' = compile_value env r in
        ret @@ Swap (l', r')
    | Free v ->
        let* v' = compile_value env v in
        ret @@ Free v'

  let compile_function
      (fn_names : string list)
      ({ export; name; param; return; body } : A.Function.t) :
      B.Function.t Res.t =
    let open Res in
    let env = Env.add { Env.empty with fn_names } (fst param) in
    let* body' = compile_expr env body in
    ret B.Function.{ export; name; param = snd param; return; body = body' }

  let compile_module ({ imports; functions; main } : A.Module.t) :
      B.Module.t Res.t =
    let open Res in
    let fn_names =
      List.map ~f:(fun fn -> fn.name) functions
      @ List.map ~f:(fun im -> im.name) imports
    in
    let* functions' = mapM ~f:(compile_function fn_names) functions in
    let* main' =
      match main with
      | None -> Ok None
      | Some m ->
          let* m = compile_expr { Env.empty with fn_names } m in
          Ok (Some m)
    in
    ret @@ B.Module.{ imports; functions = functions'; main = main' }
end
