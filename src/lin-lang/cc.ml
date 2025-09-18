open! Base

module Declosure = struct
  open Sexplib.Std
  open Index

  type typ =
    | Int
    | Prod of typ list
    | Ref of typ
    | Lollipop of typ list * typ (* no closures *)
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
  module B = Declosure

  module LS = struct
    module S = Set.M (LVar)
    include S

    let empty = Set.empty (module LVar)
    let singleton = Set.singleton (module LVar)
    let elements = Set.elements
    let union = Set.union
    let union3 (s1 : t) (s2 : t) (s3 : t) : t = Set.union (Set.union s1 s2) s3
  end

  let rec fv_value (depth : int) : A.value -> LS.t = function
    | Var (i, x) -> if i >= depth then LS.singleton (i - depth, x) else LS.empty
    | Global _ | Int _ -> LS.empty
    | Lam (_, _, body) -> fv_expr (depth + 1) body
    | Prod (v1, v2) -> LS.union (fv_value depth v1) (fv_value depth v2)

  and fv_expr (depth : int) : A.expr -> LS.t = function
    | Val v -> fv_value depth v
    | App (vf, va) -> LS.union (fv_value depth vf) (fv_value depth va)
    | Let (_, rhs, body) ->
        LS.union (fv_expr depth rhs) (fv_expr (depth + 1) body)
    | If0 (v, e1, e2) ->
        LS.union3 (fv_value depth v) (fv_expr depth e1) (fv_expr depth e2)
    | Binop (_, v1, v2) -> LS.union (fv_value depth v1) (fv_value depth v2)
    | LetPair (_, _, rhs, body) ->
        LS.union (fv_expr depth rhs) (fv_expr (depth + 2) body)
    | New v | Free v -> fv_value depth v
    | Swap (v1, v2) -> LS.union (fv_value depth v1) (fv_value depth v2)

  (** assumes that there are no closures *)
  let rec lower_typ : A.typ -> B.typ = function
    | Int -> Int
    | Lollipop (t1, t2) -> Lollipop ([ lower_typ t1 ], lower_typ t2)
    | Prod (t1, t2) -> Prod [ lower_typ t1; lower_typ t2 ]
    | Ref t -> Ref (lower_typ t)

  module Env = struct
    type t = {
      vdepth : int;
      tdepth : int;
      tenv : A.typ list;
      tls : B.toplevel list;
      gensym : int;
      vmap : (int, int) Base.Hashtbl.t; (* when in closure *)
      lambda_base : int;
      fun_globals : string list;
    }
    [@@deriving sexp_of]

    let empty : t =
      {
        vdepth = 0;
        tdepth = 0;
        tenv = [];
        tls = [];
        gensym = 0;
        vmap = Hashtbl.create (module Int);
        lambda_base = 0;
        fun_globals = [];
      }

    let lookup_v_typ (i : int) (e : t) : A.typ option = List.nth e.tenv i
  end

  module CCErr = struct
    type t =
      | TypeNotFound of LVar.t * Env.t
      | UnexpectedClosure of string
      | InternalError of string

    let to_string = function
      | TypeNotFound ((i, None), env) ->
          Stdlib.Format.asprintf "Type not found for variable %d;@;%a" i
            Sexp.pp_hum (Env.sexp_of_t env)
      | TypeNotFound ((i, Some x), env) ->
          Stdlib.Format.asprintf "Type not found for variable %d (%s);@;%a" i x
            Sexp.pp_hum (Env.sexp_of_t env)
      | UnexpectedClosure s -> Printf.sprintf "Unexpected closure in %s" s
      | InternalError s -> Printf.sprintf "Internal error: %s" s
  end

  module M = struct
    type 'a t = Env.t -> ('a * Env.t, CCErr.t) Result.t

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
    let get : Env.t t = fun e -> Ok (e, e)
    let set (e : Env.t) : unit t = fun _ -> Ok ((), e)
    let modify (f : Env.t -> Env.t) : unit t = fun e -> Ok ((), f e)
  end

  open M

  let inc_v (t : A.typ) =
    modify (fun e -> { e with vdepth = e.vdepth + 1; tenv = t :: e.tenv })

  let inc_v2 (t1 : A.typ) (t2 : A.typ) =
    modify (fun e ->
        { e with vdepth = e.vdepth + 2; tenv = t1 :: t2 :: e.tenv })

  let synth_inc_v : unit t = modify (fun e -> { e with vdepth = e.vdepth + 1 })

  let dec_v : unit t =
    modify (fun e ->
        { e with vdepth = e.vdepth - 1; tenv = List.tl_exn e.tenv })

  let synth_dec_v : unit t = modify (fun e -> { e with vdepth = e.vdepth - 1 })
  let inc_t : unit t = modify (fun e -> { e with tdepth = e.tdepth + 1 })

  let emit_tl (tl : B.toplevel) : unit t =
    modify (fun e -> { e with tls = tl :: e.tls })

  let update_lambda_base : unit t =
    modify (fun e -> { e with lambda_base = e.vdepth })

  let mark_gfun (s : string) =
    modify (fun e -> { e with fun_globals = s :: e.fun_globals })

  let fresh (prefix : string) : string t =
    let* e = get in
    let n = e.gensym + 1 in
    let* () = set { e with gensym = n } in
    return @@ Printf.sprintf "%s_%d" prefix n

  type 'a vk = B.value -> 'a t
  (** value continuation *)

  type 'a ek = B.expr -> 'a t
  (** expr continuation *)

  let closure_typ (env : Env.t) (fvs : LS.t) : B.typ t =
    let fv_list = LS.elements fvs in
    let* typs =
      fv_list
      |> List.fold_left
           ~f:(fun acc (i, x) ->
             let* acc' = acc in
             match Env.lookup_v_typ i env with
             | None -> fail (CCErr.TypeNotFound ((i, x), env))
             | Some t -> return (lower_typ t :: acc'))
           ~init:(return [])
    in
    return @@ B.Prod (List.rev typs)

  let build_closure (fvs : LS.t) : B.value =
    let fv_list = LS.elements fvs in
    Tuple (List.map ~f:(fun i -> B.Var i) fv_list)

  let compile_var ((i, x) : A.lvar) : B.value t =
    let* env = get in
    let fbinders = env.vdepth - env.lambda_base in
    let k = Hashtbl.length env.vmap in
    if i < fbinders then
      return (B.Var (i, x))
    else
      let key = i - fbinders in
      match Hashtbl.find env.vmap key with
      | Some slot -> return (B.Var (slot + fbinders, x))
      | None -> return (B.Var (i + k, x))

  let rec compile_value (v : A.value) (k : 'a vk) : 'a t =
    match v with
    | A.Var i ->
        let* v' = compile_var i in
        k v'
    | A.Global g ->
        let* env = get in
        if List.mem env.fun_globals g ~equal:String.equal then
          k (B.Coderef g)
        else
          k (B.Global g)
    | A.Int n -> k (B.Int n)
    | A.Prod (v1, v2) ->
        compile_value v1 (fun v1' ->
            compile_value v2 (fun v2' -> k (B.Tuple [ v1'; v2' ])))
    | A.Lam (t_arg, t_ret, body) ->
        let fvs = fv_expr 1 body in
        let* fname = fresh "lam" in
        let* env = get in
        if Set.is_empty fvs then
          let* body' = conv_expr_as_func body [] in
          let* () =
            emit_tl
              (B.Func (false, fname, [ lower_typ t_arg ], lower_typ t_ret, body'))
          in
          k (B.Coderef fname)
        else
          let fv_list = Set.elements fvs in
          let* clos_typ = closure_typ env fvs in
          let* body' = conv_expr_as_func body fv_list in

          let func_typs =
            match clos_typ with
            | B.Prod _ -> [ clos_typ; lower_typ t_arg ]
            | t -> [ t; lower_typ t_arg ]
          in

          let* () =
            emit_tl (B.Func (false, fname, func_typs, lower_typ t_ret, body'))
          in

          let clos =
            B.Tuple (List.map ~f:(fun (i, x) -> B.Var (i, x)) fv_list)
          in
          let packed_typ =
            B.Exists
              (B.Lollipop ([ B.Var 0; lower_typ t_arg ], lower_typ t_ret))
          in
          k (B.Pack (clos_typ, B.Tuple [ B.Coderef fname; clos ], packed_typ))

  and conv_expr (e : A.expr) (k : 'a ek) : 'a t =
    match e with
    | A.Val v -> compile_value v (fun v' -> k (B.Val v'))
    | A.App (vf, va) ->
        compile_value vf (fun vf' ->
            compile_value va (fun va' ->
                match vf' with
                | B.Coderef _ -> k (B.App (vf', va'))
                | B.Pack (witness, _, B.Exists (B.Lollipop ([ _; arg ], ret)))
                  ->
                    let body =
                      B.LetTuple
                        ( [ B.Lollipop ([ witness; arg ], ret); witness ],
                          B.Val (B.Var (0, None)),
                          B.App
                            (B.Var (1, None), B.Tuple [ B.Var (0, None); va' ])
                        )
                    in
                    k (B.Unpack (vf', body, ret))
                | _ -> fail (CCErr.UnexpectedClosure "App")))
    | A.Let (t, rhs, body) ->
        conv_expr rhs (fun rhs' ->
            let* () = inc_v t in
            conv_expr body (fun body' ->
                let* () = dec_v in
                k (B.Let (lower_typ t, rhs', body'))))
    | A.If0 (v, e1, e2) ->
        compile_value v (fun v' ->
            conv_expr e1 (fun e1' ->
                conv_expr e2 (fun e2' -> k (B.If0 (v', e1', e2')))))
    | A.Binop (op, v1, v2) ->
        compile_value v1 (fun v1' ->
            compile_value v2 (fun v2' -> k (B.Binop (op, v1', v2'))))
    | A.LetPair (t1, t2, rhs, body) ->
        conv_expr rhs (fun rhs' ->
            let* () = inc_v2 t2 t1 in
            conv_expr body (fun body' ->
                let* () = dec_v in
                let* () = dec_v in
                k (B.LetTuple ([ lower_typ t1; lower_typ t2 ], rhs', body'))))
    | A.New v -> compile_value v (fun v' -> k (B.New v'))
    | A.Swap (v1, v2) ->
        compile_value v1 (fun v1' ->
            compile_value v2 (fun v2' -> k (B.Swap (v1', v2'))))
    | A.Free v -> compile_value v (fun v' -> k (B.Free v'))

  and conv_expr_as_func (body : A.expr) (fv_list : A.lvar list) : B.expr t =
    let* env = get in
    if List.is_empty fv_list then
      let* () = synth_inc_v in
      let* () = update_lambda_base in
      let* result = conv_expr body return in
      let* () = synth_dec_v in
      return result
    else
      let k = List.length fv_list in

      let vmap = Hashtbl.create (module Int) ~size:k in
      List.iteri
        ~f:(fun j (fv, _) ->
          Hashtbl.add vmap ~key:(fv + 1) ~data:(k - 1 - j) |> ignore)
        fv_list;

      let* clos_typs_rev =
        fv_list
        |> List.fold_left
             ~f:(fun acc (i, x) ->
               let* acc' = acc in
               match Env.lookup_v_typ i env with
               | None -> fail (CCErr.TypeNotFound ((i, x), env))
               | Some t -> return (lower_typ t :: acc'))
             ~init:(return [])
      in
      let clos_typs = List.rev clos_typs_rev in

      let* () = synth_inc_v in
      let* () = update_lambda_base in
      let* () = modify (fun e -> { e with vmap }) in

      let* body' = conv_expr body return in

      let* () = synth_dec_v in
      return (B.LetTuple (clos_typs, B.Val (B.Var (1, None)), body'))

  let compile_toplevel (tl : A.toplevel) : B.toplevel t =
    match tl with
    | A.TopLevel (export, (name, typ), expr) ->
        let* () =
          match typ with
          | Lollipop _ -> mark_gfun name
          | _ -> return ()
        in
        let* expr' = conv_expr expr return in
        return (B.Let (export, (name, lower_typ typ), expr'))

  let compile_module (m : A.modul) : (B.modul, CCErr.t) Result.t =
    match m with
    | A.Module (imports, toplevels, main) -> (
        let process_imports imports env =
          let open Env in
          List.fold_left
            ~f:(fun (acc_imports, env) (Import (t, g) : A.import) ->
              let env' =
                match t with
                | Lollipop _ -> { env with fun_globals = g :: env.fun_globals }
                | _ -> env
              in
              (B.Import (lower_typ t, g) :: acc_imports, env'))
            ~init:([], env) imports
        in

        let imports_rev, env_with_imports = process_imports imports Env.empty in
        let imports' = List.rev imports_rev in

        let rec compile_tls tls acc env =
          match tls with
          | [] -> Ok (List.rev acc, env)
          | tl :: tls' -> (
              match compile_toplevel tl env with
              | Error e -> Error e
              | Ok (tl', env') -> compile_tls tls' (tl' :: acc) env')
        in

        match compile_tls toplevels [] env_with_imports with
        | Error e -> Error e
        | Ok (tls', env') -> (
            match main with
            | None -> Ok (B.Module (imports', List.rev env'.tls @ tls', None))
            | Some e -> (
                match conv_expr e return env' with
                | Error e -> Error e
                | Ok (e', env'') ->
                    Ok (B.Module (imports', List.rev env''.tls @ tls', Some e'))
                )))
end
