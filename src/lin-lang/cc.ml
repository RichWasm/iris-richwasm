open! Base

module Closed = struct
  open Sexplib.Std
  open Index

  type typ =
    | Int
    | Prod of typ list
    | Ref of typ
    | Lollipop of (typ * typ) * typ (* no free *)
    | Var of int (* type de Bruijn *)
    | Exists of typ
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type binop = Indexed.binop
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type lvar = Indexed.lvar
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type gvar = Indexed.gvar
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type value =
    | Var of lvar (* val de Bruijn *)
    | Global of gvar
    | Coderef of gvar
    | Int of int
    | Tuple of value list
    | Pack of typ * value * typ
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type expr =
    | Val of value
    | App of value * value
    | Let of typ * expr * expr
    | If0 of value * expr * expr
    | Binop of binop * value * value
    | LetTuple of typ list * expr * expr
    | New of value
    | Swap of value * value
    | Free of value
    | Unpack of value * expr * typ
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type import = Import of typ * gvar
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type toplevel =
    | Let of bool * (gvar * typ) * expr (* export *)
    | Func of bool * gvar * typ list * typ * expr
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]

  type modul = Module of import list * toplevel list * expr option
  [@@deriving show { with_path = false }, eq, iter, map, fold, sexp]
end

module ClosureConversion = struct
  open Index
  module A = Indexed
  module B = Closed

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

  let rec fv_value (depth : int) : A.value -> LS.t = function
    | Var (i, x) -> if i >= depth then LS.singleton (i - depth, x) else LS.empty
    | Global _ | Int _ -> LS.empty
    | Lam (_, _, body) -> fv_expr (depth + 1) body
    | Tuple vs -> vs |> List.map ~f:(fv_value depth) |> LS.union_list

  and fv_expr (depth : int) : A.expr -> LS.t = function
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
  let rec lower_typ : A.typ -> B.typ = function
    | Int -> Int
    | Lollipop (t1, t2) ->
        Exists (Lollipop ((Var 0, lower_typ t1), lower_typ t2))
    | Prod ts -> Prod (List.map ~f:lower_typ ts)
    | Ref t -> Ref (lower_typ t)

  module Env = struct
    type t = {
      vdepth : int;
      tenv : A.typ list;
      tls : B.toplevel list;
      vmap : (int, int) Hashtbl.t; (* when in closure *)
      lambda_base : int;
      globals : (string * A.typ) list;
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

    let lookup_v_typ (e : t) (i : int) : A.typ option = List.nth e.tenv i

    let add_var (e : t) (t : A.typ) : t =
      { e with vdepth = e.vdepth + 1; tenv = t :: e.tenv }

    let add_vars (e : t) (ts : A.typ list) : t =
      { e with vdepth = e.vdepth + List.length ts; tenv = List.rev ts @ e.tenv }
  end

  module CCErr = struct
    type t =
      | TypeNotFound of LVar.t * Env.t
      | LocalTypeLookupFailed of LVar.t * Env.t
      | GlobalTypeLookupFailed of string * Env.t
      | UnexpectedApplicand of A.typ
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
        | UnexpectedApplicand x -> asprintf "UnexpectedApplicand: %a" A.pp_typ x
        | InternalError s -> asprintf "Internal error: %s" s)
  end

  module State = struct
    type t = {
      tls : B.toplevel list;
      gensym : int;
    }
    [@@deriving sexp_of]

    let empty : t = { tls = []; gensym = 0 }
  end

  module M = struct
    type 'a t = State.t -> ('a * State.t, CCErr.t) Result.t

    let return (x : 'a) : 'a t = fun e -> Ok (x, e)

    let bind (m : 'a t) (f : 'a -> 'b t) : 'b t =
     fun e ->
      match m e with
      | Error _ as er -> er
      | Ok (x, e') -> f x e'

    let ( let* ) = bind

    let map m f =
     fun e ->
      match m e with
      | Error _ as er -> er
      | Ok (x, e') -> Ok (f x, e')

    let ( let+ ) = map
    let fail msg : 'a t = fun _ -> Error msg

    let all (ms : 'a t list) : 'a list t =
      let rec go acc = function
        | [] -> return (List.rev acc)
        | m :: ms ->
            let* x = m in
            go (x :: acc) ms
      in
      go [] ms

    let mapM (f : 'a -> 'b t) (xs : 'a list) : 'b list t =
      let rec go acc = function
        | [] -> return (List.rev acc)
        | x :: xs ->
            let* y = f x in
            go (y :: acc) xs
      in
      go [] xs

    let emit (tl : B.toplevel) : unit t =
     fun s -> Ok ((), { s with tls = tl :: s.tls })

    let fresh (prefix : string) : string t =
     fun s ->
      let n = s.gensym + 1 in
      let s' = { s with gensym = n } in
      Ok (Printf.sprintf "%s_%d" prefix n, s')
  end

  open M

  let calc_closure_typs (env : Env.t) (fv_list : LVar.t list) : B.typ list t =
    fv_list
    |> mapM (fun (i, x) ->
           match Env.lookup_v_typ env i with
           | None -> fail (CCErr.TypeNotFound ((i, x), env))
           | Some t -> return (lower_typ t))

  let closure_typ (env : Env.t) (fvs : LS.t) : B.typ t =
    let fv_list = LS.elements fvs in
    let* typs = calc_closure_typs env fv_list in
    return @@ B.Prod typs

  let build_closure (fvs : LS.t) : B.value =
    let fv_list = LS.elements fvs in
    Tuple (List.map ~f:(fun i -> B.Var i) fv_list)

  let compile_var (env : Env.t) ((i, x) : A.lvar) : B.value t =
    let fbinders = env.vdepth - env.lambda_base in
    let k = Hashtbl.length env.vmap in
    if i < fbinders then
      return @@ B.Var (i, x)
    else
      let key = i - fbinders in
      match Hashtbl.find env.vmap key with
      | Some slot -> return (B.Var (slot + fbinders, x))
      | None -> return @@ B.Var (i + k, x)

  let rec compile_value (env : Env.t) (v : A.value) : B.value t =
    match v with
    | A.Var i ->
        let* v' = compile_var env i in
        return v'
    | A.Global g -> (
        match List.Assoc.find env.globals g ~equal:String.equal with
        | Some (Lollipop _ as t) ->
            return
              B.(Pack (Prod [], Tuple [ Coderef g; Tuple [] ], lower_typ t))
        | Some _ -> return @@ B.Global g
        | None -> fail (GlobalTypeLookupFailed (g, env)))
    | A.Int n -> return (B.Int n)
    | A.Tuple vs ->
        let* vs' = mapM (compile_value env) vs in
        return (B.Tuple vs')
    | A.Lam (arg_t, ret_t, body) ->
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
          return @@ B.(LetTuple (clos_typs, Val (Var (1, None)), body'))
        in
        let* clos_typ = closure_typ env fvs in
        let arg_t' = lower_typ arg_t in
        let ret_t' = lower_typ ret_t in

        let* () =
          let func_typs = [ clos_typ; arg_t' ] in
          emit (B.Func (false, fname, func_typs, ret_t', body'))
        in

        let clos = B.(Tuple (List.map ~f:(fun (i, x) -> Var (i, x)) fv_list)) in
        return
          B.(
            Pack
              ( clos_typ,
                Tuple [ Coderef fname; clos ],
                lower_typ (Lollipop (arg_t, ret_t)) ))

  and conv_expr (env : Env.t) (e : A.expr) : B.expr t =
    match e with
    | A.Val v ->
        let* v' = compile_value env v in
        return @@ B.Val v'
    | A.App (vf, va) -> (
        let* vf' = compile_value env vf in
        let* va' = compile_value env va in

        let rec lookup_typ : A.value -> A.typ t = function
          | Var (i, x) -> (
              match Env.lookup_v_typ env i with
              | Some t -> return t
              | None -> fail (LocalTypeLookupFailed ((i, x), env)))
          | Global g -> (
              match List.Assoc.find env.globals g ~equal:String.equal with
              | Some t -> return t
              | None -> fail (GlobalTypeLookupFailed (g, env)))
          | Int _ -> return @@ (Int : A.typ)
          | Lam (arg_t, ret_t, _) -> return @@ (Lollipop (arg_t, ret_t) : A.typ)
          | Tuple vs ->
              let* vs' = mapM (fun v -> lookup_typ v) vs in
              return @@ (Prod vs' : A.typ)
        in

        let* looked_up = lookup_typ vf in

        let open B in
        match looked_up with
        | Lollipop (arg, ret) ->
            let body =
              LetTuple
                (* tvar from unpack *)
                ( [ Lollipop ((Var 0, lower_typ arg), lower_typ ret); Var 0 ],
                  Val (Var (0, None)),
                  App (Var (1, None), Tuple [ Var (0, None); va' ]) )
            in
            return @@ Unpack (vf', body, lower_typ ret)
        | t -> fail (UnexpectedApplicand t))
    | A.Let (t, rhs, body) ->
        let* rhs' = conv_expr env rhs in
        let env' = Env.add_var env t in
        let* body' = conv_expr env' body in
        return @@ (Let (lower_typ t, rhs', body') : B.expr)
    | A.If0 (v, e1, e2) ->
        let* v' = compile_value env v in
        let* e1' = conv_expr env e1 in
        let* e2' = conv_expr env e2 in
        return @@ B.If0 (v', e1', e2')
    | A.Binop (op, v1, v2) ->
        let* v1' = compile_value env v1 in
        let* v2' = compile_value env v2 in
        return @@ B.Binop (op, v1', v2')
    | A.LetProd (ts, rhs, body) ->
        let* rhs' = conv_expr env rhs in
        let env' = Env.add_vars env ts in
        let* body' = conv_expr env' body in

        return @@ B.LetTuple (List.map ~f:lower_typ ts, rhs', body')
    | A.New v ->
        let* v' = compile_value env v in
        return (B.New v')
    | A.Swap (v1, v2) ->
        let* v1' = compile_value env v1 in
        let* v2' = compile_value env v2 in
        return @@ B.Swap (v1', v2')
    | A.Free v ->
        let* v' = compile_value env v in
        return @@ B.Free v'

  let compile_toplevel
      (env : Env.t)
      (TopLevel (export, (name, typ), expr) : A.toplevel) :
      (B.toplevel * Env.t) t =
    let env' = { env with globals = (name, typ) :: env.globals } in
    let* expr' = conv_expr env' expr in
    return @@ (B.Let (export, (name, lower_typ typ), expr'), env')

  let compile_module (m : A.modul) : (B.modul, CCErr.t) Result.t =
    match m with
    | A.Module (imports, toplevels, main) -> (
        let imports_rev, globals =
          List.fold_left
            ~f:(fun (acc_imports, acc_globals) (Import (t, g) : A.import) ->
              let acc_globals' = (g, t) :: acc_globals in
              (B.Import (lower_typ t, g) :: acc_imports, acc_globals'))
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

        match
          compile_tls toplevels [] State.empty { Env.empty with globals }
        with
        | Error e -> Error e
        | Ok (tls', env, state) -> (
            match main with
            | None -> Ok (Module (imports', List.rev state.tls @ tls', None))
            | Some e -> (
                match conv_expr env e state with
                | Error e -> Error e
                | Ok (e', state') ->
                    Ok (Module (imports', List.rev state'.tls @ tls', Some e')))
            ))
end
