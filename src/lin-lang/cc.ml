open! Base
module LVar = Index.LVar

module IR = struct
  module Type = struct
    type t =
      | Int
      | Prod of t list
      | Ref of t
      | Lollipop of (t * t) * t (* no free *)
      | Var of int (* type de Bruijn *)
      | Exists of t
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end

  module Binop = struct
    type t = Syntax.Binop.t [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end

  module Value = struct
    type t =
      | Var of LVar.t (* val de Bruijn *)
      | Global of string
      | Coderef of string
      | Int of int
      | Tuple of t list
      | Pack of Type.t * t * Type.t
    [@@deriving eq, ord, iter, map, fold, sexp]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end

  module Expr = struct
    type t =
      | Val of Value.t
      | App of Value.t * Value.t
      | Let of Type.t * t * t
      | If0 of Value.t * t * t
      | Binop of Binop.t * Value.t * Value.t
      | LetTuple of Type.t list * t * t
      | New of Value.t
      | Swap of Value.t * Value.t
      | Free of Value.t
      | Unpack of Value.t * t * Type.t
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

  module TopLevel = struct
    type t =
      | Let of {
          export : bool;
          binding : string * Type.t;
          init : Expr.t;
        }
      | Func of {
          export : bool;
          name : string;
          params : Type.t list;
          ret : Type.t;
          body : Expr.t;
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

  let rec fv_value (depth : int) : A.Value.t -> LS.t = function
    | Var (i, x) -> if i >= depth then LS.singleton (i - depth, x) else LS.empty
    | Global _ | Int _ -> LS.empty
    | Lam (_, _, body) -> fv_expr (depth + 1) body
    | Tuple vs -> vs |> List.map ~f:(fv_value depth) |> LS.union_list

  and fv_expr (depth : int) : A.Expr.t -> LS.t = function
    | Val v -> fv_value depth v
    | App (vf, va) -> LS.union (fv_value depth vf) (fv_value depth va)
    | Let (_, rhs, body) ->
        LS.union (fv_expr depth rhs) (fv_expr (depth + 1) body)
    | If0 (v, e1, e2) ->
        LS.union3 (fv_value depth v) (fv_expr depth e1) (fv_expr depth e2)
    | Binop (_, v1, v2) -> LS.union (fv_value depth v1) (fv_value depth v2)
    | LetProd (ts, rhs, body) ->
        let n = List.length ts in
        LS.union (fv_expr depth rhs) (fv_expr (depth + n) body)
    | New v | Free v -> fv_value depth v
    | Swap (v1, v2) -> LS.union (fv_value depth v1) (fv_value depth v2)

  (** assumes that nothing is free *)
  let rec lower_typ : A.Type.t -> B.Type.t = function
    | Int -> Int
    | Lollipop (t1, t2) ->
        Exists (Lollipop ((Var 0, lower_typ t1), lower_typ t2))
    | Prod ts -> Prod (List.map ~f:lower_typ ts)
    | Ref t -> Ref (lower_typ t)

  module Env = struct
    type t = {
      vdepth : int;
      tenv : A.Type.t list;
      tls : B.TopLevel.t list;
      vmap : (int, int) Hashtbl.t; (* when in closure *)
      lambda_base : int;
      globals : (string * A.Type.t) list;
    }
    [@@deriving sexp_of]

    let empty : t =
      {
        vdepth = 0;
        tenv = [];
        tls = [];
        vmap = Hashtbl.create (module Int);
        lambda_base = 0;
        globals = [];
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
      | GlobalTypeLookupFailed of string * Env.t
      | UnexpectedApplicand of A.Type.t
      | InternalError of string

    let to_string =
      Stdlib.Format.(
        function
        | TypeNotFound ((i, None), env) ->
            asprintf "Type not found for variable %d;@;%a" i Sexp.pp_hum
              (Env.sexp_of_t env)
        | TypeNotFound ((i, Some x), env) ->
            asprintf "Type not found for variable %d (%s);@;%a" i x Sexp.pp_hum
              (Env.sexp_of_t env)
        | LocalTypeLookupFailed ((i, None), env) ->
            asprintf "type lookup failed for local %d;@;%a" i Sexp.pp_hum
              (Env.sexp_of_t env)
        | LocalTypeLookupFailed ((i, Some x), env) ->
            asprintf "type lookup failed for local %d (%s);@;%a" i x Sexp.pp_hum
              (Env.sexp_of_t env)
        | GlobalTypeLookupFailed (g, env) ->
            asprintf "type lookup failed for global %s;@;%a" g Sexp.pp_hum
              (Env.sexp_of_t env)
        | UnexpectedApplicand x ->
            asprintf "UnexpectedApplicand: %a" A.Type.pp x
        | InternalError s -> asprintf "Internal error: %s" s)
  end

  module State = struct
    type t = {
      tls : B.TopLevel.t list;
      gensym : int;
    }
    [@@deriving sexp_of]

    let empty : t = { tls = []; gensym = 0 }
  end

  module M = struct
    include Util.StateM (State) (Err)

    let emit (tl : B.TopLevel.t) : unit t =
     fun s -> Ok ((), { s with tls = tl :: s.tls })

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

  let build_closure (fvs : LS.t) : B.Value.t =
    let fv_list = LS.elements fvs in
    let open B.Value in
    Tuple (List.map ~f:(fun i -> Var i) fv_list)

  let compile_var (env : Env.t) ((i, x) : LVar.t) : B.Value.t t =
    let fbinders = env.vdepth - env.lambda_base in
    let k = Hashtbl.length env.vmap in
    let open B.Value in
    if i < fbinders then
      ret @@ Var (i, x)
    else
      let key = i - fbinders in
      match Hashtbl.find env.vmap key with
      | Some slot -> ret (Var (slot + fbinders, x))
      | None -> ret @@ Var (i + k, x)

  let rec compile_value (env : Env.t) : A.Value.t -> B.Value.t t =
    let open B.Expr in
    let open B.Value in
    function
    | Var i ->
        let* v' = compile_var env i in
        ret v'
    | Global g -> (
        match List.Assoc.find env.globals g ~equal:String.equal with
        | Some (Lollipop _ as t) ->
            ret (Pack (Prod [], Tuple [ Coderef g; Tuple [] ], lower_typ t))
        | Some _ -> ret @@ Global g
        | None -> fail (GlobalTypeLookupFailed (g, env)))
    | Int n -> ret (Int n)
    | Tuple vs ->
        let* vs' = mapM ~f:(compile_value env) vs in
        ret (Tuple vs')
    | Lam (arg_t, ret_t, body) ->
        let fvs = fv_expr 1 body in
        let* fname = fresh "lam" in
        let fv_list = Set.elements fvs in
        let* body' =
          let k = List.length fv_list in

          let vmap = Hashtbl.create (module Int) ~size:k in
          List.iteri
            ~f:(fun j (fv, _) ->
              Hashtbl.add vmap ~key:(fv + 1) ~data:(k - 1 - j) |> ignore)
            fv_list;

          let* clos_typs = calc_closure_typs env fv_list in
          let env' = Env.add_var env arg_t in
          let env' = { env' with vmap; lambda_base = env.vdepth } in

          let* body' = conv_expr env' body in
          ret @@ LetTuple (clos_typs, Val (Var (1, None)), body')
        in
        let* clos_typ = closure_typ env fvs in
        let arg_t' = lower_typ arg_t in
        let ret_t' = lower_typ ret_t in

        let* () =
          emit
            (Func
               {
                 export = false;
                 name = fname;
                 params = [ clos_typ; arg_t' ];
                 ret = ret_t';
                 body = body';
               })
        in

        let clos = Tuple (List.map ~f:(fun (i, x) -> Var (i, x)) fv_list) in
        ret
          (Pack
             ( clos_typ,
               Tuple [ Coderef fname; clos ],
               lower_typ (Lollipop (arg_t, ret_t)) ))

  and conv_expr (env : Env.t) : A.Expr.t -> B.Expr.t t = function
    | Val v ->
        let* v' = compile_value env v in
        ret @@ B.Expr.Val v'
    | App (vf, va) -> (
        let* vf' = compile_value env vf in
        let* va' = compile_value env va in

        let rec lookup_typ : A.Value.t -> A.Type.t t = function
          | Var (i, x) -> (
              match Env.lookup_v_typ env i with
              | Some t -> ret t
              | None -> fail (LocalTypeLookupFailed ((i, x), env)))
          | Global g -> (
              match List.Assoc.find env.globals g ~equal:String.equal with
              | Some t -> ret t
              | None -> fail (GlobalTypeLookupFailed (g, env)))
          | Int _ -> ret @@ (Int : A.Type.t)
          | Lam (arg_t, ret_t, _) -> ret (Lollipop (arg_t, ret_t) : A.Type.t)
          | Tuple vs ->
              let* vs' = mapM ~f:(fun v -> lookup_typ v) vs in
              ret (Prod vs' : A.Type.t)
        in

        let* looked_up = lookup_typ vf in

        match looked_up with
        | Lollipop (arg, return) ->
            let body : B.Expr.t =
              LetTuple
                (* tvar from unpack *)
                ( [ Lollipop ((Var 0, lower_typ arg), lower_typ return); Var 0 ],
                  Val (Var (0, None)),
                  App (Var (1, None), Tuple [ Var (0, None); va' ]) )
            in
            ret (Unpack (vf', body, lower_typ return) : B.Expr.t)
        | t -> fail (UnexpectedApplicand t))
    | Let (t, rhs, body) ->
        let* rhs' = conv_expr env rhs in
        let env' = Env.add_var env t in
        let* body' = conv_expr env' body in
        ret (Let (lower_typ t, rhs', body') : B.Expr.t)
    | If0 (v, e1, e2) ->
        let* v' = compile_value env v in
        let* e1' = conv_expr env e1 in
        let* e2' = conv_expr env e2 in
        ret (If0 (v', e1', e2') : B.Expr.t)
    | Binop (op, v1, v2) ->
        let* v1' = compile_value env v1 in
        let* v2' = compile_value env v2 in
        ret (Binop (op, v1', v2') : B.Expr.t)
    | LetProd (ts, rhs, body) ->
        let* rhs' = conv_expr env rhs in
        let env' = Env.add_vars env ts in
        let* body' = conv_expr env' body in

        ret (LetTuple (List.map ~f:lower_typ ts, rhs', body') : B.Expr.t)
    | New v ->
        let* v' = compile_value env v in
        ret (New v' : B.Expr.t)
    | Swap (v1, v2) ->
        let* v1' = compile_value env v1 in
        let* v2' = compile_value env v2 in
        ret (Swap (v1', v2') : B.Expr.t)
    | Free v ->
        let* v' = compile_value env v in
        ret (Free v' : B.Expr.t)

  let compile_toplevel
      (env : Env.t)
      ({ export; binding = name, typ; init } : A.TopLevel.t) :
      (B.TopLevel.t * Env.t) t =
    let env' = { env with globals = (name, typ) :: env.globals } in
    let* init' = conv_expr env' init in
    ret
      ( B.TopLevel.Let { export; binding = (name, lower_typ typ); init = init' },
        env' )

  let compile_module ({ imports; toplevels; main } : A.Module.t) :
      (B.Module.t, Err.t) Result.t =
    let imports_rev, globals =
      List.fold_left
        ~f:(fun (acc_imports, acc_globals) ({ typ; name } : A.Import.t) ->
          let acc_globals' = (name, typ) :: acc_globals in
          (B.Import.{ typ = lower_typ typ; name } :: acc_imports, acc_globals'))
        ~init:([], []) imports
    in
    let imports' = List.rev imports_rev in

    let rec compile_tls tls acc state env =
      match tls with
      | [] -> Ok (List.rev acc, env, state)
      | tl :: tls' -> (
          match compile_toplevel env tl state with
          | Error e -> Error e
          | Ok ((tl', env'), state') ->
              compile_tls tls' (tl' :: acc) state' env')
    in

    match compile_tls toplevels [] State.empty { Env.empty with globals } with
    | Error e -> Error e
    | Ok (tls', env, state) -> (
        match main with
        | None ->
            Ok
              (B.Module.make ~imports:imports'
                 ~toplevels:(List.rev state.tls @ tls')
                 ())
        | Some e -> (
            match conv_expr env e state with
            | Error e -> Error e
            | Ok (e', state') ->
                Ok
                  (B.Module.make ~imports:imports'
                     ~toplevels:(List.rev state'.tls @ tls')
                     ~main:e' ())))
end
