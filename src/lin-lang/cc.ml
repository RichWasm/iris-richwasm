open! Base
module LVar = Index.LVar

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

  module Binop = struct
    type t = Syntax.Binop.t [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end

  module Expr = struct
    type t =
      | Int of int
      | Var of LVar.t
      | Coderef of string
      | Tuple of t list
      | Inj of int * t * Type.t
      | Fold of Type.t * t
      | Pack of Type.t * t * Type.t
      | App of t * t
      | Let of Type.t * t * t
      | Split of Type.t list * t * t
      | Cases of t * (Type.t * t) list
      | Unfold of Type.t * t
      | Unpack of t * t * Type.t
      | If0 of t * t * t
      | Binop of Binop.t * t * t
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

module Compile = struct
  module A = Index.IR
  module B = IR

  module LS = struct
    module S = Set.M (LVar)
    include S

    let empty = Set.empty (module LVar)
    let singleton = Set.singleton (module LVar)

    let elements s =
      Set.elements s
      |> List.sort ~compare:(fun (a, _) (b, _) -> Int.compare a b)

    let union = Set.union
    let union3 (s1 : t) (s2 : t) (s3 : t) : t = Set.union (Set.union s1 s2) s3
    let union_list = Set.union_list (module LVar)
  end

  let rec fv_expr (depth : int) : A.Expr.t -> LS.t = function
    | Var (i, x) -> if i >= depth then LS.singleton (i - depth, x) else LS.empty
    | Coderef _ | Int _ -> LS.empty
    | Lam (_, _, body) -> fv_expr (depth + 1) body
    | Tuple vs -> vs |> List.map ~f:(fv_expr depth) |> LS.union_list
    | Inj (_, v, _) | Fold (_, v) -> fv_expr depth v
    | App (vf, va) -> LS.union (fv_expr depth vf) (fv_expr depth va)
    | Let (_, rhs, body) ->
        LS.union (fv_expr depth rhs) (fv_expr (depth + 1) body)
    | Split (ts, rhs, body) ->
        let n = List.length ts in
        LS.union (fv_expr depth rhs) (fv_expr (depth + n) body)
    | Cases (scrutinee, cases) ->
        let cases' = List.map ~f:(fun (_, b) -> fv_expr (depth + 1) b) cases in
        LS.union_list (fv_expr depth scrutinee :: cases')
    | Unfold (_, v) -> fv_expr depth v
    | If0 (v, e1, e2) ->
        LS.union3 (fv_expr depth v) (fv_expr depth e1) (fv_expr depth e2)
    | Binop (_, v1, v2) -> LS.union (fv_expr depth v1) (fv_expr depth v2)
    | New v | Free v -> fv_expr depth v
    | Swap (v1, v2) -> LS.union (fv_expr depth v1) (fv_expr depth v2)

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
  let rec lower_typ : A.Type.t -> B.Type.t = function
    | Int -> Int
    | Var x -> Var x
    | Lollipop (t1, t2) ->
        Exists
          (Lollipop
             ( Prod [ Var (0, None); lower_typ t1 |> shift_tidx 1 0 ],
               lower_typ t2 |> shift_tidx 1 0 ))
    | Prod ts -> Prod (List.map ~f:lower_typ ts)
    | Sum ts -> Sum (List.map ~f:lower_typ ts)
    | Ref t -> Ref (lower_typ t)
    | Rec t -> Rec (lower_typ t)

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
      | LocalTypeLookupFailed of LVar.t * Env.t
      | FunctionLookupFailed of string * Env.t
      | UnexpectedApplicand of A.Type.t
      | DuplicateFunName of string
      | InvalidImport of string * A.Type.t
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

  let calc_closure_typs (env : Env.t) (fv_list : LVar.t list) : B.Type.t list t
      =
    fv_list
    |> mapM ~f:(fun (i, x) ->
           match Env.lookup_v_typ env i with
           | None -> fail (TypeNotFound ((i, x), env))
           | Some t -> ret (lower_typ t))

  let closure_typ (env : Env.t) (fvs : LS.t) : B.Type.t t =
    let fv_list = LS.elements fvs in
    let* typs = calc_closure_typs env fv_list in
    ret @@ B.Type.Prod typs

  let build_closure (fvs : LS.t) : B.Expr.t =
    let fv_list = LS.elements fvs in
    let open B.Expr in
    Tuple (List.map ~f:(fun i -> Var i) fv_list)

  let compile_var (env : Env.t) ((i, x) : LVar.t) : B.Expr.t t =
    let fbinders = env.vdepth - env.lambda_base in
    let k = Map.length env.vmap in
    let open B.Expr in
    if i < fbinders then
      ret @@ Var (i, x)
    else
      let key = i - fbinders in
      match Map.find env.vmap key with
      | Some slot -> ret (Var (slot + fbinders, x))
      | None -> ret @@ Var (i + k, x)

  let rec lookup_typ (env : Env.t) : A.Expr.t -> A.Type.t t =
    let open A.Type in
    function
    | Var (i, x) -> (
        match Env.lookup_v_typ env i with
        | Some t -> ret t
        | None -> fail (LocalTypeLookupFailed ((i, x), env)))
    | Coderef n -> (
        match Map.find env.fns n with
        | Some (param, return) -> ret (Lollipop (param, return))
        | None -> fail (FunctionLookupFailed (n, env)))
    | Int _ -> ret @@ Int
    | Lam (arg_t, ret_t, _) -> ret (Lollipop (arg_t, ret_t))
    | Tuple vs ->
        let+ vs' = mapM ~f:(fun v -> lookup_typ env v) vs in
        Prod vs'
    | Inj (_, _, t) -> ret t
    | Fold (t, _) -> ret t
    | New v ->
        let+ t = lookup_typ env v in
        Ref t
    | _ -> fail TODO

  let rec compile_expr (env : Env.t) : A.Expr.t -> B.Expr.t t =
    let open B.Expr in
    function
    | Var i ->
        let* v' = compile_var env i in
        ret v'
    | Coderef n ->
        let* typ =
          match Map.find env.fns n with
          | Some (param, return) -> ret (A.Type.Lollipop (param, return))
          | None -> fail (FunctionLookupFailed (n, env))
        in
        ret (Pack (Prod [], Tuple [ Coderef n; Tuple [] ], lower_typ typ))
    | Int n -> ret (Int n)
    | Tuple vs ->
        let* vs' = mapM ~f:(compile_expr env) vs in
        ret (Tuple vs')
    | Inj (i, v, t) ->
        let* v' = compile_expr env v in
        ret (Inj (i, v', lower_typ t))
    | Fold (t, v) ->
        let* v' = compile_expr env v in
        ret (Fold (lower_typ t, v'))
    | New v ->
        let* v' = compile_expr env v in
        ret (New v')
    | Lam (arg_t, ret_t, body) ->
        let fvs = fv_expr 1 body in
        let* fname = fresh "lam" in
        let fv_list = Set.elements fvs in
        let arg_t' = lower_typ arg_t in
        let* clos_typs = calc_closure_typs env fv_list in
        let* body' =
          let k = List.length fv_list in

          let* vmap =
            List.foldi
              ~f:(fun i acc (fv, _) ->
                let* acc = acc in
                match Map.add acc ~key:(fv + 1) ~data:(k - 1 - i) with
                | `Ok m -> ret m
                | `Duplicate -> fail (InternalError "duplicate vmap"))
              ~init:(ret (Map.empty (module Int)))
              fv_list
          in

          let env' = Env.add_var env arg_t in
          let env' = { env' with vmap; lambda_base = env.vdepth } in

          let+ body' = compile_expr env' body in
          Split
            ( [ Prod clos_typs; arg_t' ],
              Var (0, None),
              Split (clos_typs, Free (Var (1, None)), body') )
        in
        let* closure = closure_typ env fvs in
        let param : B.Type.t = Prod [ closure; arg_t' ] in
        let return = lower_typ ret_t in

        (*
          #`(func #,name (#,param -> #,return)
              (split (closure : #,clos_typs) (orig_param : #,arg_t) = #,param in
                (split #,@clos_typs = (free closure) in
                  #,body)))
          *)
        let+ () =
          emit { export = false; name = fname; param; return; body = body' }
        in

        let clos = Tuple (List.map ~f:(fun (i, x) -> Var (i, x)) fv_list) in
        (* #`(pack #,closure (new #,clos) as #,(lower clos)) *)
        Pack
          ( closure,
            Tuple [ Coderef fname; New clos ],
            lower_typ (Lollipop (arg_t, ret_t)) )
    | App (fn, arg) -> (
        let* fn' = compile_expr env fn in
        let* arg' = compile_expr env arg in

        (* TODO: do we really need a full lookup here? 

           we know it must contain function, does that let us do less work?? *)
        let* looked_up = lookup_typ env fn in

        match looked_up with
        | Lollipop (arg, return) ->
            (*
            #`(unpack (package : α) from #,vf where
                (split (coderef : ((α ⊗ #,tin) -> #,tout)) (closure : α) = package in
                  (app coderef (closure, #,va))))
            *)
            let in_t =
              B.Type.Prod [ Var (0, None); lower_typ arg |> shift_tidx 1 0 ]
            in
            let out_t = lower_typ return |> shift_tidx 1 0 in

            let body : B.Expr.t =
              Split
                ( [ Lollipop (in_t, out_t); Var (0, None) ],
                  Var (0, None),
                  App (Var (1, None), Tuple [ Var (0, None); arg' ]) )
            in
            ret (Unpack (fn', body, lower_typ return))
        | t -> fail (UnexpectedApplicand t))
    | Let (t, rhs, body) ->
        let* rhs' = compile_expr env rhs in
        let env' = Env.add_var env t in
        let* body' = compile_expr env' body in
        ret (Let (lower_typ t, rhs', body'))
    | Split (ts, rhs, body) ->
        let* rhs' = compile_expr env rhs in
        let env' = Env.add_vars env ts in
        let* body' = compile_expr env' body in
        ret (Split (List.map ~f:lower_typ ts, rhs', body'))
    | Cases (scrutinee, cases) ->
        let* scrutinee' = compile_expr env scrutinee in
        let* cases' =
          mapM
            ~f:(fun (t, body) ->
              let env' = Env.add_var env t in
              let+ body' = compile_expr env' body in
              (lower_typ t, body'))
            cases
        in
        ret (Cases (scrutinee', cases'))
    | Unfold (t, v) ->
        let t' = lower_typ t in
        let* v' = compile_expr env v in
        ret (Unfold (t', v'))
    | If0 (v, e1, e2) ->
        let* v' = compile_expr env v in
        let* e1' = compile_expr env e1 in
        let* e2' = compile_expr env e2 in
        ret (If0 (v', e1', e2'))
    | Binop (op, v1, v2) ->
        let* v1' = compile_expr env v1 in
        let* v2' = compile_expr env v2 in
        ret (Binop (op, v1', v2'))
    | Swap (v1, v2) ->
        let* v1' = compile_expr env v1 in
        let* v2' = compile_expr env v2 in
        ret (Swap (v1', v2'))
    | Free v ->
        let* v' = compile_expr env v in
        ret (Free v')

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
        param = Prod [ Ref (Prod []); lower_typ param ];
        return = lower_typ return;
        body = body';
      }

  module Res = Util.ResultM (Err)

  let compile_module ({ imports; functions; main } : A.Module.t) :
      B.Module.t Res.t =
    let open B.Module in
    let open Res in
    let imports' =
      List.fold_left
        ~f:(fun acc_imports { typ; name } ->
          B.Import.{ typ = lower_typ typ; name } :: acc_imports)
        ~init:[] imports
      |> List.rev
    in

    let* fns =
      foldM
        ~f:(fun acc ({ typ; name } : A.Import.t) ->
          match typ with
          | Lollipop (param, return) -> (
              match Map.add acc ~key:name ~data:(param, return) with
              | `Ok m -> ret m
              | `Duplicate -> fail (DuplicateFunName name))
          | _ -> fail (InvalidImport (name, typ)))
        ~init:(Map.empty (module String))
        imports
    in
    let* fns =
      foldM
        ~f:(fun acc (fn : A.Function.t) ->
          match Map.add acc ~key:fn.name ~data:(fn.param, fn.return) with
          | `Ok m -> ret m
          | `Duplicate -> fail (DuplicateFunName fn.name))
        ~init:fns functions
    in

    let env = { Env.empty with fns } in
    let prog : B.Module.t M.t =
      let open M in
      let* functions' = mapM ~f:(compile_function env) functions in
      let* main' =
        Option.value_map
          ~f:(compile_expr env >-> Option.return)
          ~default:(ret None) main
      in
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
