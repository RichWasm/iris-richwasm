open! Base

(* NOTE: most of the interesting type checking actually happens at the RichWasm
         level, all this checks is that the annotations are consistent and
         elaborates the AST. *)

module LVar = Cc.LVar

module IR = struct
  module Type = Cc.IR.Type
  module Binop = Cc.IR.Binop

  module Value = struct
    type t =
      | Int of int * Type.t
      | Var of LVar.t * Type.t
      | Coderef of string * Type.t
      | Tuple of t list * Type.t
      | Inj of int * t * Type.t
      | Fold of t * Type.t
      | Pack of Type.t * t * Type.t
      | New of t * Type.t
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let type_of : t -> Type.t = function
      | Var (_, t)
      | Coderef (_, t)
      | Int (_, t)
      | Tuple (_, t)
      | Inj (_, _, t)
      | Fold (_, t)
      | Pack (_, _, t)
      | New (_, t) -> t
  end

  module Expr = struct
    type t =
      | Val of Value.t * Type.t
      | App of Value.t * Value.t * Type.t
      | Let of Type.t * t * t * Type.t
      | Split of Type.t list * t * t * Type.t
      | Cases of Value.t * (Type.t * t) list * Type.t
      | Unfold of Value.t * Type.t
      | Unpack of Value.t * t * Type.t
      | If0 of Value.t * t * t * Type.t
      | Binop of Binop.t * Value.t * Value.t * Type.t
      | Swap of Value.t * Value.t * Type.t
      | Free of Value.t * Type.t
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let type_of : t -> Type.t = function
      | Val (_, t)
      | App (_, _, t)
      | Let (_, _, _, t)
      | Split (_, _, _, t)
      | Cases (_, _, t)
      | Unfold (_, t)
      | Unpack (_, _, t)
      | If0 (_, _, _, t)
      | Binop (_, _, _, t)
      | Swap (_, _, t)
      | Free (_, t) -> t
  end

  module Import = Cc.IR.Import

  module Function = struct
    type t = {
      export : bool;
      name : string;
      param : Type.t;
      return : Type.t;
      body : Expr.t;
    }
    [@@deriving eq, ord, iter, map, fold, sexp, make]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end

  module Module = struct
    type t = {
      imports : Import.t list;
      functions : Function.t list;
      main : Expr.t option;
    }
    [@@deriving eq, ord, iter, map, fold, sexp, make]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end
end

module Env = struct
  open Cc.IR

  type t = {
    locals : Type.t list;
    fns : (Type.t * Type.t) Map.M(String).t;
  }
  [@@deriving sexp]

  let empty = { locals = []; fns = Map.empty (module String) }

  let add_local (env : t) (loc : Type.t) =
    { env with locals = loc :: env.locals }

  let add_locals (env : t) (locs : Type.t list) =
    { env with locals = List.rev locs @ env.locals }
end

module Err = struct
  module Type = Cc.IR.Type

  module Mismatch = struct
    module Info = struct
      type t = {
        expected : Type.t;
        actual : Type.t;
      }
      [@@deriving sexp]
    end

    module Ctx = struct
      type t =
        | InjAnn
        | FunRet
        | AppArg
        | LetBind
        | SplitBind of int
        | Binop
      [@@deriving sexp]
    end
  end

  type t =
    | TODO
    | IntenalError of string
    | MissingLocalEnv of LVar.t * Env.t
    | MissingGlobalEnv of string * Env.t
    | EmptyCases
    | FreeNonRef of Type.t
    | InjInvalidAnn of Type.t
    | InjInvalidIdx of int * Type.t list
    | AppNotFun of Type.t
    | SplitNotProd of Type.t
    | SplitWrongNum
    | Mismatch of Mismatch.Ctx.t * Mismatch.Info.t
  [@@deriving sexp]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Res = Util.ResultM (Err)

module Compile = struct
  module A = Cc.IR
  module B = IR
  open Res

  let teq ~(expected : B.Type.t) ~(actual : B.Type.t) (ctx : Err.Mismatch.Ctx.t)
      =
    if B.Type.equal expected actual then
      ret ()
    else
      fail (Mismatch (ctx, { expected; actual }))

  let rec compile_value (env : Env.t) : A.Value.t -> B.Value.t t =
    let open B.Type in
    let open B.Value in
    function
    | Var ((i, _) as lvar) ->
        let* t =
          match List.nth env.locals i with
          | None -> Error (MissingLocalEnv (lvar, env))
          | Some x -> Ok x
        in
        ret @@ Var (lvar, t)
    | Coderef n ->
        let* t =
          match Map.find env.fns n with
          | None -> Error (MissingGlobalEnv (n, env))
          | Some (p, r) -> Ok (Lollipop (p, r))
        in
        ret @@ Coderef (n, t)
    | Int n -> ret @@ Int (n, Int)
    | Tuple vs ->
        let* vs' = mapM ~f:(compile_value env) vs in
        let t = Prod (List.map ~f:type_of vs') in
        ret @@ Tuple (vs', t)
    | Inj (i, v, typ) ->
        let* v' = compile_value env v in
        let* inner_ts =
          match typ with
          | Sum ts -> ret ts
          | x -> fail (InjInvalidAnn x)
        in
        let* () =
          match List.nth inner_ts i with
          | None -> fail (InjInvalidIdx (i, inner_ts))
          | Some t -> teq ~expected:t ~actual:(type_of v') InjAnn
        in

        ret @@ Inj (i, v', typ)
    | Fold (typ, _) -> fail TODO
    | Pack (_, _, typ) -> fail TODO
    | New v ->
        let* v' = compile_value env v in
        let t = Ref (B.Value.type_of v') in
        ret @@ New (v', t)

  let rec compile_expr (env : Env.t) : A.Expr.t -> B.Expr.t t =
    let open B.Type in
    let open B.Expr in
    function
    | Val v ->
        let* v' = compile_value env v in
        let t = B.Value.type_of v' in
        ret @@ Val (v', t)
    | App (v1, v2) ->
        let* v1' = compile_value env v1 in
        let* v2' = compile_value env v2 in
        let* ft1, ft2 =
          match B.Value.type_of v1' with
          | Lollipop (t1, t2) -> ret (t1, t2)
          | x -> fail (AppNotFun x)
        in
        let v2t = B.Value.type_of v2' in
        let* () = teq ~expected:ft1 ~actual:v2t AppArg in
        ret @@ App (v1', v2', ft2)
    | Let (b_t, lhs, body) ->
        let* lhs' = compile_expr env lhs in
        let* () = teq ~expected:b_t ~actual:(type_of lhs') LetBind in
        let env' = Env.add_local env b_t in
        let* body' = compile_expr env' body in
        let t = type_of body' in
        ret @@ Let (b_t, lhs', body', t)
    | Split (ts, lhs, body) ->
        let* lhs' = compile_expr env lhs in
        let* tup_t =
          match type_of lhs' with
          | Prod ts -> ret ts
          | x -> fail (SplitNotProd x)
        in
        let* zipped =
          match List.zip ts tup_t with
          | Ok z -> ret z
          | Unequal_lengths -> fail SplitWrongNum
        in
        let* () =
          iteriM
            ~f:(fun i (b, t) -> teq ~actual:t ~expected:b (SplitBind i))
            zipped
        in
        let env' = Env.add_locals env ts in
        let* body' = compile_expr env' body in
        let t = type_of body' in
        ret @@ Split (ts, lhs', body', t)
    | Cases (scrutinee, cases) ->
        (*(match List.nth cases 0 with
        | Some (_, e) ->
            let* env' = fail TODO in
            type_of_expr env' e
        | None -> fail EmptyCases)*)
        fail TODO
    | Unfold (t, v) ->
        let* v' = compile_value env v in
        let* () = fail TODO in
        ret @@ Unfold (v', t)
    | Unpack (_, _, t) -> fail TODO
    | If0 (_, l, _) -> fail TODO
    | Binop (((Add | Sub | Mul | Div) as op), v1, v2) ->
        let* v1' = compile_value env v1 in
        let* v2' = compile_value env v2 in
        let v1t = B.Value.type_of v1' in
        let v2t = B.Value.type_of v2' in
        let* () = teq ~actual:v1t ~expected:Int Binop in
        let* () = teq ~actual:v2t ~expected:Int Binop in
        ret @@ Binop (op, v1', v2', Int)
    | Swap (v1, v2) -> fail TODO
    | Free v ->
        (*(let* v' = type_of_value env v in
        match v' with
        | Ref v -> ret v
        | x -> fail (FreeNonRef x))*)
        fail TODO

  let compile_function
      (env : Env.t)
      ({ export; name; param; return; body } : A.Function.t) : B.Function.t t =
    let open B.Function in
    let env' = Env.add_local env param in
    let* body' = compile_expr env' body in
    let body_t = B.Expr.type_of body' in
    let* () = teq ~expected:return ~actual:body_t FunRet in

    ret @@ { export; name; param; return; body = body' }

  let compile_module ({ imports; functions; main } : A.Module.t) : B.Module.t t
      =
    let open B.Module in
    let* fn_rets =
      match
        Map.of_list_with_key
          ~get_key:(fun x -> x.name)
          (module String)
          functions
      with
      | `Duplicate_key k -> fail (IntenalError ("dup fn " ^ k))
      | `Ok m -> ret @@ Map.map ~f:(fun x -> (x.param, x.return)) m
    in
    let env = { Env.empty with fns = fn_rets } in
    let* functions' = mapM ~f:(compile_function env) functions in
    let* main' = omap ~f:(compile_expr env) main in

    ret { imports; functions = functions'; main = main' }
end
