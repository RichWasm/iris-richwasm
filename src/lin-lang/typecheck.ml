open! Base

(* NOTE: most of the interesting type checking actually happens at the RichWasm
         level, all this checks is that the annotations are consistent and
         elaborates the AST. *)

module LVar = Index.LVar

module AnnLVar (Type : Index.Ast) = struct
  module T = struct
    type t = LVar.t * Type.t [@@deriving eq, sexp, show { with_path = false }]

    let compare (a, _) (b, _) = LVar.compare a b
  end

  include T
  include Comparator.Make (T)
end

module IR = struct
  module Type = Index.IR.Type
  module Binop = Index.IR.Binop

  module Expr = struct
    type t =
      | Int of int * Type.t
      | Var of LVar.t * Type.t
      | Coderef of string * Type.t
      | Lam of Type.t * Type.t * t * Type.t
      | Tuple of t list * Type.t
      | Inj of int * t * Type.t
      | Fold of Type.t * t * Type.t
      | App of t * t * Type.t
      | Let of Type.t * t * t * Type.t
      | Split of Type.t list * t * t * Type.t
      | Cases of t * (Type.t * t) list * Type.t
      | Unfold of Type.t * t * Type.t
      | If0 of t * t * t * Type.t
      | Binop of Binop.t * t * t * Type.t
      | New of t * Type.t
      | Swap of t * t * Type.t
      | Free of t * Type.t
    [@@deriving eq, ord, variants, sexp]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let type_of : t -> Type.t = function
      | Int (_, t)
      | Var (_, t)
      | Coderef (_, t)
      | Lam (_, _, _, t)
      | Tuple (_, t)
      | Inj (_, _, t)
      | Fold (_, _, t)
      | App (_, _, t)
      | Let (_, _, _, t)
      | Split (_, _, _, t)
      | Cases (_, _, t)
      | Unfold (_, _, t)
      | If0 (_, _, _, t)
      | Binop (_, _, _, t)
      | New (_, t)
      | Swap (_, _, t)
      | Free (_, t) -> t
  end

  include Index.IR.Mk (Type) (Expr)
end

module Env = struct
  open Index.IR

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
  module Type = Index.IR.Type

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
        | LamRet
        | AppArg
        | LetBind
        | SplitBind of int
        | Binop
        | IfEls
        | FoldExpr
        | UnfoldExpr
        | CaseAnn
        | CaseBody of int
      [@@deriving sexp]
    end
  end

  type t =
    | IntenalError of string
    | MissingLocalEnv of LVar.t * Env.t
    | MissingGlobalEnv of string * Env.t
    | CasesEmpty
    | CasesScrutineeNotSum of Type.t
    | CasesWrongNum
    | InjInvalidAnn of Type.t
    | InjInvalidIdx of int * Type.t list
    | AppNotFun of Type.t
    | SplitNotProd of Type.t
    | SplitWrongNum
    | InvalidFoldUnfoldAnn of Type.t
    | FreeNonRef of Type.t
    | SwapNonRef of Type.t
    | Mismatch of Mismatch.Ctx.t * Mismatch.Info.t
  [@@deriving sexp]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Res = Util.ResultM (Err)

module Compile = struct
  module A = Index.IR
  module B = IR
  open Res

  let teq ~(expected : B.Type.t) ~(actual : B.Type.t) (ctx : Err.Mismatch.Ctx.t)
      =
    if B.Type.equal expected actual then
      ret ()
    else
      fail (Mismatch (ctx, { expected; actual }))

  let rec subst ?(idx : int = 0) ~(repl : A.Type.t) : A.Type.t -> A.Type.t =
    function
    | Int -> Int
    | Var (i, _) when i = idx -> repl
    | Var x -> Var x
    | Lollipop (p, r) -> Lollipop (subst ~idx ~repl p, subst ~idx ~repl r)
    | Prod ts -> Prod (List.map ~f:(subst ~idx ~repl) ts)
    | Sum ts -> Sum (List.map ~f:(subst ~idx ~repl) ts)
    | Rec t -> Rec (subst ~idx:(idx + 1) ~repl t)
    | Ref t -> Ref (subst ~idx ~repl t)

  let unroll : A.Type.t -> A.Type.t t = function
    | Rec body as mu -> ret @@ subst ~repl:mu body
    | x -> fail (InvalidFoldUnfoldAnn x)

  let rec compile_expr (env : Env.t) : A.Expr.t -> B.Expr.t t =
    let open B.Type in
    let open B.Expr in
    function
    | Var ((i, _) as lvar) ->
        let* t =
          List.nth env.locals i |> lift_option (MissingLocalEnv (lvar, env))
        in
        ret @@ Var (lvar, t)
    | Coderef n ->
        let* t =
          match Map.find env.fns n with
          | None -> Error (MissingGlobalEnv (n, env))
          | Some (p, r) -> Ok (Lollipop (p, r))
        in
        ret @@ Coderef (n, t)
    | Lam (param_t, ret_t, body) ->
        let env' = Env.add_local env param_t in
        let* body' = compile_expr env' body in
        let* () = teq ~expected:ret_t ~actual:(type_of body') LamRet in
        ret @@ Lam (param_t, ret_t, body', Lollipop (param_t, ret_t))
    | Int n -> ret @@ Int (n, Int)
    | Tuple es ->
        let* es' = mapM ~f:(compile_expr env) es in
        let t = Prod (List.map ~f:type_of es') in
        ret @@ Tuple (es', t)
    | Inj (i, v, typ) ->
        let* v' = compile_expr env v in
        let* inner_ts =
          match typ with
          | Sum ts -> ret ts
          | x -> fail (InjInvalidAnn x)
        in
        let* () =
          match List.nth inner_ts i with
          | Some t -> teq ~expected:t ~actual:(type_of v') InjAnn
          | None -> fail (InjInvalidIdx (i, inner_ts))
        in
        ret @@ Inj (i, v', typ)
    | Fold (mu, expr) ->
        let* expr' = compile_expr env expr in
        let* unrolled = unroll mu in
        let* () = teq ~expected:unrolled ~actual:(type_of expr') FoldExpr in
        ret @@ Fold (mu, expr', mu)
    | App (applicand, applicant) ->
        let* applicand' = compile_expr env applicand in
        let* applicant' = compile_expr env applicant in
        let* ft_in, ft_out =
          match type_of applicand' with
          | Lollipop (t1, t2) -> ret (t1, t2)
          | x -> fail (AppNotFun x)
        in
        let* () = teq ~expected:ft_in ~actual:(type_of applicant') AppArg in
        ret @@ App (applicand', applicant', ft_out)
    | Let (b_t, rhs, body) ->
        let* rhs' = compile_expr env rhs in
        let* () = teq ~expected:b_t ~actual:(type_of rhs') LetBind in
        let env' = Env.add_local env b_t in
        let* body' = compile_expr env' body in
        ret @@ Let (b_t, rhs', body', type_of body')
    | Split (ts, rhs, body) ->
        let* rhs' = compile_expr env rhs in
        let* tup_t =
          match type_of rhs' with
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
        ret @@ Split (ts, rhs', body', t)
    | Cases (scrutinee, cases) ->
        let* scrutinee' = compile_expr env scrutinee in
        let* variants =
          match type_of scrutinee' with
          | Sum variants -> ret variants
          | x -> fail @@ CasesScrutineeNotSum x
        in
        let* zipped =
          match List.zip variants cases with
          | Ok x -> ret x
          | Unequal_lengths -> fail CasesWrongNum
        in
        let* cases' =
          mapM zipped ~f:(fun (actual, (ann, body)) ->
              let* () = teq ~actual ~expected:ann CaseAnn in
              let env' = Env.add_local env ann in
              let* body' = compile_expr env' body in
              ret (ann, body'))
        in
        let* t =
          match List.nth cases' 0 with
          | Some (_, body) -> ret @@ type_of body
          | None -> fail CasesEmpty
        in
        let* () =
          iteriM cases' ~f:(fun i (_, b) ->
              teq ~expected:t ~actual:(type_of b) (CaseBody i))
        in

        ret @@ Cases (scrutinee', cases', t)
    | Unfold (mu, expr) ->
        let* expr' = compile_expr env expr in
        let* () = teq ~expected:mu ~actual:(type_of expr') UnfoldExpr in
        let* t = unroll mu in
        ret @@ Unfold (mu, expr', t)
    | If0 (cond, thn, els) ->
        let* cond' = compile_expr env cond in
        let* thn' = compile_expr env thn in
        let* els' = compile_expr env els in
        let thn_t = type_of thn' in
        let els_t = type_of els' in
        let* () = teq ~expected:thn_t ~actual:els_t IfEls in
        ret @@ If0 (cond', thn', els', thn_t)
    | Binop (((Add | Sub | Mul | Div) as op), left, right) ->
        let* left' = compile_expr env left in
        let* right' = compile_expr env right in
        let left_t = type_of left' in
        let right_t = type_of right' in
        let* () = teq ~actual:left_t ~expected:Int Binop in
        let* () = teq ~actual:right_t ~expected:Int Binop in
        ret @@ Binop (op, left', right', Int)
    | New expr ->
        let* expr' = compile_expr env expr in
        ret @@ New (expr', Ref (type_of expr'))
    | Swap (ref, expr) ->
        let* ref' = compile_expr env ref in
        let* expr' = compile_expr env expr in
        let ref_t = type_of ref' in
        let expr_t = type_of expr' in
        let* inner_t =
          match ref_t with
          | Ref x -> ret x
          | x -> fail @@ SwapNonRef x
        in
        ret @@ Swap (ref', expr', Prod [ Ref expr_t; inner_t ])
    | Free expr ->
        let* expr' = compile_expr env expr in
        (match type_of expr' with
        | Ref t -> ret @@ Free (expr', t)
        | x -> fail @@ FreeNonRef x)

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
      List.map imports ~f:(fun i -> A.Import.(i.name, i.input, i.output))
      @ List.map functions ~f:(fun f -> A.Function.(f.name, f.param, f.return))
      |> Map.of_list_with_key
           ~get_key:(fun (name, _, _) -> name)
           (module String)
      |> function
      | `Duplicate_key k -> fail (IntenalError ("dup fn " ^ k))
      | `Ok m -> ret @@ Map.map ~f:(fun (_, param, return) -> (param, return)) m
    in
    let env = { Env.empty with fns = fn_rets } in
    let imports' =
      List.map
        ~f:(fun A.Import.{ name; input; output } ->
          B.Import.{ name; input; output })
        imports
    in
    let* functions' = mapM ~f:(compile_function env) functions in
    let* main' = omap ~f:(compile_expr env) main in

    ret { imports = imports'; functions = functions'; main = main' }
end
