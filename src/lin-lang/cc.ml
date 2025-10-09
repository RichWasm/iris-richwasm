open! Base
module LVar = Typecheck.LVar

module IR = struct
  module Type = struct
    type t =
      | Int
      | Var of LVar.t
      | Lollipop of t * t (* no free *)
      | Prod of t list
      | Sum of t list
      | Rec of t
      | Exists of t
      | Ref of t
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end

  module Binop = Index.IR.Binop

  module Expr = struct
    type t =
      | Int of int * Type.t
      | Var of LVar.t * Type.t
      | Coderef of string * Type.t
      | Tuple of t list * Type.t
      | Inj of int * t * Type.t
      | Fold of Type.t * t * Type.t
      | Pack of Type.t * t * Type.t
      | App of t * t * Type.t
      | Let of Type.t * t * t * Type.t
      | Split of Type.t list * t * t * Type.t
      | Cases of t * (Type.t * t) list * Type.t
      | Unfold of Type.t * t * Type.t
      | Unpack of t * t * Type.t
      | If0 of t * t * t * Type.t
      | Binop of Binop.t * t * t * Type.t
      | New of t * Type.t
      | Swap of t * t * Type.t
      | Free of t * Type.t
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)

    let type_of : t -> Type.t = function
      | Var (_, t)
      | Coderef (_, t)
      | Int (_, t)
      | Tuple (_, t)
      | Inj (_, _, t)
      | Fold (_, _, t)
      | Pack (_, _, t)
      | App (_, _, t)
      | Let (_, _, _, t)
      | Split (_, _, _, t)
      | Cases (_, _, t)
      | Unfold (_, _, t)
      | Unpack (_, _, t)
      | If0 (_, _, _, t)
      | Binop (_, _, _, t)
      | New (_, t)
      | Swap (_, _, t)
      | Free (_, t) -> t

    let mk_tuple es = Tuple (es, Prod (List.map ~f:type_of es))
    let mk_new e = New (e, Ref (type_of e))
    let mk_split ts lhs body = Split (ts, lhs, body, type_of body)

    let mk_split_var ~split_t ~i ?n body =
      Split (split_t, Var ((i, n), Prod split_t), body, type_of body)
  end

  include Index.IR.Mk (Type) (Expr)
end

module Compile = struct
  module A = Typecheck.IR
  module B = IR
  module AnnVar = Typecheck.AnnLVar (A.Type)

  module LS = struct
    module S = Set.M (AnnVar)
    include S

    let empty = Set.empty (module AnnVar)
    let singleton = Set.singleton (module AnnVar)
    let elements s = Set.elements s |> List.sort ~compare:AnnVar.compare
    let length = Set.length
    let union = Set.union
    let union3 (s1 : t) (s2 : t) (s3 : t) : t = Set.union (Set.union s1 s2) s3
    let union_list = Set.union_list (module AnnVar)
  end

  let rec fv_expr (depth : int) : A.Expr.t -> LS.t = function
    | Var ((i, x), t) ->
        if i >= depth then LS.singleton ((i - depth, x), t) else LS.empty
    | Coderef (_, _) | Int (_, _) -> LS.empty
    | Lam (_, _, body, _) -> fv_expr (depth + 1) body
    | Tuple (vs, _) -> vs |> List.map ~f:(fv_expr depth) |> LS.union_list
    | Inj (_, v, _) | Fold (_, v, _) -> fv_expr depth v
    | App (vf, va, _) -> LS.union (fv_expr depth vf) (fv_expr depth va)
    | Let (_, rhs, body, _) ->
        LS.union (fv_expr depth rhs) (fv_expr (depth + 1) body)
    | Split (ts, rhs, body, _) ->
        let n = List.length ts in
        LS.union (fv_expr depth rhs) (fv_expr (depth + n) body)
    | Cases (scrutinee, cases, _) ->
        let cases' = List.map ~f:(fun (_, b) -> fv_expr (depth + 1) b) cases in
        LS.union_list (fv_expr depth scrutinee :: cases')
    | Unfold (_, v, _) -> fv_expr depth v
    | If0 (cond, thn, els, _) ->
        LS.union3 (fv_expr depth cond) (fv_expr depth thn) (fv_expr depth els)
    | Binop (_, l, r, _) -> LS.union (fv_expr depth l) (fv_expr depth r)
    | New (e, _) | Free (e, _) -> fv_expr depth e
    | Swap (l, r, _) -> LS.union (fv_expr depth l) (fv_expr depth r)

  let rec shift_tidx d c : B.Type.t -> B.Type.t = function
    | Int -> Int
    | Var (i, n) -> Var ((if i >= c then i + d else i), n)
    | Lollipop (t1, t2) -> Lollipop (shift_tidx d c t1, shift_tidx d c t2)
    | Prod ts -> Prod (List.map ~f:(shift_tidx d c) ts)
    | Sum ts -> Sum (List.map ~f:(shift_tidx d c) ts)
    | Rec t -> Rec (shift_tidx d (c + 1) t)
    | Exists t -> Exists (shift_tidx d (c + 1) t)
    | Ref t -> Ref (shift_tidx d c t)

  (** assumes that nothing is free *)
  let rec compile_typ : A.Type.t -> B.Type.t = function
    | Int -> Int
    | Var x -> Var x
    | Lollipop (t1, t2) ->
        Exists
          (Lollipop
             ( Prod [ Var (0, None); compile_typ t1 |> shift_tidx 1 0 ],
               compile_typ t2 |> shift_tidx 1 0 ))
    | Prod ts -> Prod (List.map ~f:compile_typ ts)
    | Sum ts -> Sum (List.map ~f:compile_typ ts)
    | Ref t -> Ref (compile_typ t)
    | Rec t -> Rec (compile_typ t)

  module Env = struct
    type t = {
      vdepth : int;
      tenv : A.Type.t list;
      lambda_base : int;
      vmap : Int.t Map.M(Int).t; (* when in closure *)
      fns : (A.Type.t * A.Type.t) Map.M(String).t;
    }
    [@@deriving sexp_of]

    let empty : t =
      {
        vdepth = 0;
        tenv = [];
        lambda_base = 0;
        vmap = Map.empty (module Int);
        fns = Map.empty (module String);
      }

    let lookup_v_typ (e : t) (i : int) : A.Type.t option = List.nth e.tenv i

    let add_var (e : t) (t : A.Type.t) : t =
      { e with vdepth = e.vdepth + 1; tenv = t :: e.tenv }

    let add_vars (e : t) (ts : A.Type.t list) : t =
      { e with vdepth = e.vdepth + List.length ts; tenv = List.rev ts @ e.tenv }
  end

  module Err = struct
    type t =
      | TypeNotFound of LVar.t * Env.t
      | InvalidCoderefAnn of A.Type.t
      | UnexpectedApplicand of A.Type.t
      | DuplicateFunName of string
      | InternalError of string
      | TODO
    [@@deriving sexp_of]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end

  module State = struct
    type t = {
      fns : B.Function.t list;
      gensym : int;
    }
    [@@deriving sexp_of]

    let empty : t = { fns = []; gensym = 0 }
  end

  module M = struct
    include Util.StateM (State) (Err)

    let emit (fn : B.Function.t) : unit t =
     fun s -> Ok ((), { s with fns = fn :: s.fns })

    let fresh (prefix : string) : string t =
     fun s ->
      let n = s.gensym + 1 in
      let s' = { s with gensym = n } in
      Ok (Printf.sprintf "%s_%d" prefix n, s')
  end

  open M

  let split_clos_typs (fvs : LS.t) : B.Type.t list =
    let fv_list = LS.elements fvs in
    List.map ~f:(fun (_, t) -> compile_typ t) fv_list

  let closure_typ (fvs : LS.t) : B.Type.t =
    let typs = split_clos_typs fvs in
    Prod typs

  let build_closure (fvs : LS.t) : B.Expr.t =
    let fv_list = LS.elements fvs in
    let exprs =
      List.map ~f:(fun (lv, t) -> B.Expr.Var (lv, compile_typ t)) fv_list
    in
    Tuple (exprs, closure_typ fvs)

  let compile_var (env : Env.t) (((i, x), t) : AnnVar.t) : B.Expr.t t =
    let fbinders = env.vdepth - env.lambda_base in
    let k = Map.length env.vmap in
    let open B.Expr in
    let t' = compile_typ t in
    if i < fbinders then
      ret @@ Var ((i, x), t')
    else
      let key = i - fbinders in
      match Map.find env.vmap key with
      | Some slot -> ret (Var ((slot + fbinders, x), t'))
      | None -> ret @@ Var ((i + k, x), t')

  let build_vmap (fvs : LS.t) : Int.t Map.M(Int).t t =
    let fv_list = LS.elements fvs in
    let k = LS.length fvs in
    foldiM
      ~f:(fun i acc ((fv, _), _) ->
        match Map.add acc ~key:(fv + 1) ~data:(k - 1 - i) with
        | `Ok m -> ret m
        | `Duplicate -> fail (InternalError "duplicate vmap"))
      ~init:(Map.empty (module Int))
      fv_list

  let rec compile_expr (env : Env.t) : A.Expr.t -> B.Expr.t t =
    let open B.Expr in
    function
    | Var (l, t) ->
        let* v' = compile_var env (l, t) in
        ret @@ v'
    | Coderef (n, t) ->
        let* in_t, out_t =
          match t with
          | Lollipop (in_t, out_t) -> ret @@ (in_t, out_t)
          | _ -> fail (InvalidCoderefAnn t)
        in
        let coderef_t = B.Type.Lollipop (compile_typ in_t, compile_typ out_t) in
        let tuple = mk_tuple [ Coderef (n, coderef_t); mk_new (mk_tuple []) ] in
        ret @@ Pack (Prod [], tuple, compile_typ t)
    | Int (n, t) -> ret (Int (n, compile_typ t))
    | Tuple (es, t) ->
        let* es' = mapM ~f:(compile_expr env) es in
        ret @@ Tuple (es', compile_typ t)
    | Inj (i, expr, t) ->
        let* expr' = compile_expr env expr in
        ret @@ Inj (i, expr', compile_typ t)
    | Fold (mu, expr, t) ->
        let mu' = compile_typ mu in
        let* expr' = compile_expr env expr in
        ret @@ Fold (mu', expr', compile_typ t)
    | New (expr, t) ->
        let* expr' = compile_expr env expr in
        ret @@ New (expr', compile_typ t)
    | Lam (arg_t, ret_t, body, t) ->
        let fvs = fv_expr 1 body in
        let* fname = fresh "lam" in
        let orig_arg_t' = compile_typ arg_t in
        let ret_t' = compile_typ ret_t in
        let split_clos_typs = split_clos_typs fvs in
        let clos_typ = B.Type.Prod split_clos_typs in
        let ref_clos_typ = B.Type.Ref clos_typ in
        let split_clos_tup_typs = [ ref_clos_typ; orig_arg_t' ] in
        let clos_tup_typ = B.Type.(Prod split_clos_typs) in
        let* body' =
          let* vmap = build_vmap fvs in
          let env' = Env.add_var env arg_t in
          let env' = { env' with vmap; lambda_base = env.vdepth } in
          let+ body' = compile_expr env' body in
          mk_split_var ~split_t:split_clos_tup_typs ~i:0
            (mk_split split_clos_typs
               (Free (Var ((1, None), ref_clos_typ), clos_typ))
               body')
        in

        (*
          #`(func #,name (#,param -> #,return)
              (split (closure : #,ref_clos_typs) (orig_param : #,arg_t) = #,param in
                (split #,@split_clos_typs = (free closure) in
                  #,body)))
          *)
        let+ () =
          let param = clos_tup_typ in
          let return = ret_t' in
          emit { export = false; name = fname; param; return; body = body' }
        in

        (* #`(pack #,closure (new #,clos) as #,(lower clos)) *)
        Pack
          ( ref_clos_typ,
            mk_tuple
              [
                Coderef (fname, Lollipop (clos_tup_typ, ret_t'));
                mk_new (build_closure fvs);
              ],
            compile_typ t )
    | App (applicand, applicant, _) ->
        let* applicand' = compile_expr env applicand in
        let* applicant' = compile_expr env applicant in

        let* arg, return =
          match A.Expr.type_of applicand with
          | Lollipop (arg, return) -> ret (arg, return)
          | t -> fail (UnexpectedApplicand t)
        in

        let open B.Type in
        (*
        #`(unpack (package : α) from #,applicand where
            (split (coderef : ((α ⊗ #,tin) -> #,tout)) (closure : α) = package in
              (app coderef (closure, #,applicant))))
        *)
        let package_t = Var (0, None) in
        let in_t = Prod [ package_t; compile_typ arg |> shift_tidx 1 0 ] in
        let out_t = compile_typ return |> shift_tidx 1 0 in

        let real_ft = Lollipop (in_t, out_t) in
        let body : B.Expr.t =
          mk_split_var
            ~split_t:[ real_ft; Var (0, None) ]
            ~i:0
            (App
               ( Var ((1, None), real_ft),
                 mk_tuple [ Var ((0, None), package_t); applicant' ],
                 out_t ))
        in
        ret (Unpack (applicand', body, compile_typ return))
    | Let (b_t, rhs, body, t) ->
        let* rhs' = compile_expr env rhs in
        let env' = Env.add_var env t in
        let* body' = compile_expr env' body in
        ret @@ Let (compile_typ b_t, rhs', body', compile_typ t)
    | Split (es, rhs, body, t) ->
        let* rhs' = compile_expr env rhs in
        let env' = Env.add_vars env es in
        let* body' = compile_expr env' body in
        ret @@ Split (List.map ~f:compile_typ es, rhs', body', compile_typ t)
    | Cases (scrutinee, cases, t) ->
        let* scrutinee' = compile_expr env scrutinee in
        let* cases' =
          mapM
            ~f:(fun (t, body) ->
              let env' = Env.add_var env t in
              let+ body' = compile_expr env' body in
              (compile_typ t, body'))
            cases
        in
        ret @@ Cases (scrutinee', cases', compile_typ t)
    | Unfold (mu, expr, t) ->
        let mu' = compile_typ mu in
        let* expr' = compile_expr env expr in
        ret @@ Unfold (mu', expr', compile_typ t)
    | If0 (cond, thn, els, t) ->
        let* cond' = compile_expr env cond in
        let* thn' = compile_expr env thn in
        let* els' = compile_expr env els in
        ret (If0 (cond', thn', els', compile_typ t))
    | Binop (op, left, right, t) ->
        let* left' = compile_expr env left in
        let* right' = compile_expr env right in
        ret @@ Binop (op, left', right', compile_typ t)
    | Swap (left, right, t) ->
        let* left' = compile_expr env left in
        let* right' = compile_expr env right in
        ret @@ Swap (left', right', compile_typ t)
    | Free (expr, t) ->
        let* expr' = compile_expr env expr in
        ret @@ Free (expr', compile_typ t)

  let compile_function
      (env : Env.t)
      ({ export; name; param; return; body } : A.Function.t) : B.Function.t t =
    let open B.Function in
    let env' = Env.add_var env param in
    let* body' = compile_expr env' body in
    ret
      {
        export;
        name;
        param = Prod [ Ref (Prod []); compile_typ param ];
        return = compile_typ return;
        body = body';
      }

  module Res = Util.ResultM (Err)

  let compile_imports (imports : A.Import.t list) : B.Import.t list =
    List.fold_left
      ~f:(fun acc_imports A.Import.{ name; input; output } ->
        B.Import.
          {
            name;
            input = Prod [ Ref (Prod []); compile_typ input ];
            output = compile_typ output;
          }
        :: acc_imports)
      ~init:[] imports
    |> List.rev

  let compile_module ({ imports; functions; main } : A.Module.t) :
      B.Module.t Res.t =
    let open B.Module in
    let open Res in
    let imports' = compile_imports imports in
    let* fns =
      foldM
        ~f:(fun acc A.Import.{ name; input; output } ->
          match Map.add acc ~key:name ~data:(input, output) with
          | `Ok m -> ret m
          | `Duplicate -> fail (DuplicateFunName name))
        ~init:(Map.empty (module String))
        imports
    in
    let* fns =
      foldM
        ~f:(fun acc fn ->
          match Map.add acc ~key:fn.name ~data:(fn.param, fn.return) with
          | `Ok m -> ret m
          | `Duplicate -> fail (DuplicateFunName fn.name))
        ~init:fns functions
    in

    let env = { Env.empty with fns } in
    let prog : B.Module.t M.t =
      let open M in
      let* functions' = mapM ~f:(compile_function env) functions in
      let* main' = omap ~f:(compile_expr env) main in
      let* st = get in
      ret
        {
          imports = imports';
          functions = List.rev st.fns @ functions';
          main = main';
        }
    in
    let+ prog, _ = prog State.empty in
    prog
end
