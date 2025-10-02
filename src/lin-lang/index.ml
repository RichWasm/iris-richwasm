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
    type t =
      | Int
      | Var of LVar.t (* type de Bruijn *)
      | Lollipop of t * t
      | Prod of t list
      | Sum of t list
      | Rec of t
      | Ref of t
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end

  module Binop = struct
    include Syntax.Binop

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end

  module Expr = struct
    type t =
      | Int of int
      | Var of LVar.t (* val de Bruijn *)
      | Coderef of string
      | Lam of Type.t * Type.t * t
      | Tuple of t list
      | Inj of int * t * Type.t
      | Fold of Type.t * t
      | App of t * t
      | Let of Type.t * t * t
      | If0 of t * t * t
      | Binop of Binop.t * t * t
      (* split (x_0:ty_0, ..., x_n:ty_n) = rhs in body; x_n -> 0, x_0 -> n *)
      | Split of Type.t list * t * t
      | Cases of t * (Type.t * t) list
      | Unfold of Type.t * t
      | New of t
      | Swap of t * t
      | Free of t
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end

  module Import = struct
    type t = {
      typ : Type.t;
      name : string;
    }
    [@@deriving eq, ord, iter, map, fold, sexp, make]

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
  type t =
    | UnboundLocal of string
    | UnboundType of string
  [@@deriving sexp]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Res = Util.ResultM (Err)

module Compile = struct
  module A = Syntax
  module B = IR

  module Env = struct
    type t = {
      locals : string list;
      types : string list;
      fn_names : string list;
    }

    let empty = { locals = []; types = []; fn_names = [] }

    let resolve_name (env : t) (name : string) :
        [ `Local of int * string | `Function of string | `NotFound ] =
      match List.findi ~f:(fun _ -> String.equal name) env.locals with
      | Some (i, n) -> `Local (i, n)
      | None -> (
          match List.mem env.fn_names name ~equal:String.equal with
          | true -> `Function name
          | false -> `NotFound)

    let resolve_tname (env : t) (tname : string) : (int * string) option =
      List.findi ~f:(fun _ -> String.equal tname) env.types

    let add (env : t) (lname : string) : t =
      { env with locals = lname :: env.locals }

    let add_all (env : t) (lnames : string list) : t =
      { env with locals = List.rev lnames @ env.locals }

    let add_t (env : t) (tname : string) : t =
      { env with types = tname :: env.types }
  end

  let rec compile_typ (env : Env.t) : A.Type.t -> B.Type.t Res.t =
    let open B.Type in
    let open Res in
    function
    | Int -> ret @@ Int
    | Var x -> (
        match Env.resolve_tname env x with
        | Some (i, n) -> Ok (Var (i, Some n))
        | None -> Error (UnboundType x))
    | Lollipop (t1, t2) ->
        let* t1' = compile_typ env t1 in
        let* t2' = compile_typ env t2 in
        ret @@ Lollipop (t1', t2')
    | Prod ts ->
        let* ts' = mapM ~f:(compile_typ env) ts in
        ret @@ Prod ts'
    | Sum ts ->
        let* ts' = mapM ~f:(compile_typ env) ts in
        ret @@ Sum ts'
    | Rec (x, t) ->
        let env' = Env.add_t env x in
        let* t' = compile_typ env' t in
        ret @@ Rec t'
    | Ref t ->
        let* t' = compile_typ env t in
        ret @@ Ref t'

  let rec compile_expr (env : Env.t) : A.Expr.t -> B.Expr.t Res.t =
    let open B.Expr in
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
        let* typ' = compile_typ env typ in
        let* return' = compile_typ env return in
        let* body' = compile_expr env' body in
        ret (Lam (typ', return', body'))
    | Tuple vs ->
        let* vs' = mapM ~f:(compile_expr env) vs in
        ret (Tuple vs')
    | Inj (i, v, t) ->
        let* v' = compile_expr env v in
        let* t' = compile_typ env t in
        ret (Inj (i, v', t'))
    | Fold (t, v) ->
        let* t' = compile_typ env t in
        let* v' = compile_expr env v in
        ret (Fold (t', v'))
    | App (l, r) ->
        let* l' = compile_expr env l in
        let* r' = compile_expr env r in
        ret @@ App (l', r')
    | Let ((var, typ), e, body) ->
        let* typ' = compile_typ env typ in
        let* e' = compile_expr env e in
        let env' = Env.add env var in
        let* body' = compile_expr env' body in
        ret @@ Let (typ', e', body')
    | Split (bindings, e, body) ->
        let* e' = compile_expr env e in
        let vars, typs = List.unzip bindings in
        let* typs' = mapM ~f:(compile_typ env) typs in
        let env' = Env.add_all env vars in
        let* body' = compile_expr env' body in
        ret @@ Split (typs', e', body')
    | Cases (scrutinee, cases) ->
        let* scrutinee' = compile_expr env scrutinee in
        let* cases' =
          mapM
            ~f:(fun ((x, t), body) ->
              let env' = Env.add env x in
              let* t' = compile_typ env t in
              let* body' = compile_expr env' body in
              ret (t', body'))
            cases
        in
        ret @@ Cases (scrutinee', cases')
    | Unfold (t, v) ->
        let* t' = compile_typ env t in
        let* v' = compile_expr env v in
        ret @@ Unfold (t', v')
    | If0 (v, e1, e2) ->
        let* v' = compile_expr env v in
        let* e1' = compile_expr env e1 in
        let* e2' = compile_expr env e2 in
        ret @@ If0 (v', e1', e2')
    | Binop (op, l, r) ->
        let* l' = compile_expr env l in
        let* r' = compile_expr env r in
        ret @@ Binop (op, l', r')
    | Swap (l, r) ->
        let* l' = compile_expr env l in
        let* r' = compile_expr env r in
        ret @@ Swap (l', r')
    | Free v ->
        let* v' = compile_expr env v in
        ret @@ Free v'
    | New v ->
        let* v' = compile_expr env v in
        ret @@ New v'

  let compile_function
      (fn_names : string list)
      ({ export; name; param; return; body } : A.Function.t) :
      B.Function.t Res.t =
    let open Res in
    let env = Env.add { Env.empty with fn_names } (fst param) in
    let* param' = compile_typ env (snd param) in
    let* return' = compile_typ env return in
    let* body' = compile_expr env body in
    ret
      B.Function.
        { export; name; param = param'; return = return'; body = body' }

  let compile_module ({ imports; functions; main } : A.Module.t) :
      B.Module.t Res.t =
    let open Res in
    let* imports' =
      mapM
        ~f:(fun { typ; name } ->
          let+ typ' = compile_typ Env.empty typ in
          B.Import.{ typ = typ'; name })
        imports
    in
    let fn_names =
      List.map ~f:(fun fn -> fn.name) functions
      @ List.map ~f:(fun im -> im.name) imports
    in
    let* functions' = mapM ~f:(compile_function fn_names) functions in
    let* main' = omap ~f:(compile_expr { Env.empty with fn_names }) main in

    ret @@ B.Module.{ imports = imports'; functions = functions'; main = main' }
end
