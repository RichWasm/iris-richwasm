open! Base
open! Stdlib.Format
module RichWasm = Richwasm_common.Syntax

module StringMap = struct
  type 'a t = 'a Map.M(String).t [@@deriving sexp]
end

module State = struct
  type t = {
    next_local : int;
    rev_locals : RichWasm.Representation.t list; (* TODO: local fxs *)
  }
  [@@deriving sexp, make]

  let empty ~next_local = { next_local; rev_locals = [] }
end

module Env = struct
  type t = {
    function_map : int StringMap.t;
    local_map : int list;
    (* types vars have kinds, we only care about its representation here *)
    type_map : RichWasm.Representation.t option list;
  }
  [@@deriving sexp]

  let empty =
    { function_map = Map.empty (module String); local_map = []; type_map = [] }

  let add_local (env : t) (richwasm_local_index : int) : t =
    { env with local_map = richwasm_local_index :: env.local_map }

  let add_locals (env : t) (richwasm_local_indexs : int list) : t =
    { env with local_map = List.rev richwasm_local_indexs @ env.local_map }

  let add_type (env : t) (rep : RichWasm.Representation.t) : t =
    { env with type_map = Some rep :: env.type_map }

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Err = struct
  type t =
    | TODO of string
    | IntenalError of string
    | UnmappedLocal of (Cc.LVar.t * Env.t)
    | UnmappedCoderef of (string * Env.t)
    | InjInvalidAnn of Cc.IR.Type.t
    | UnexpectedOpenType of Cc.LVar.t
    | CannotFindRep of Cc.IR.Type.t
    | CannotResolveRepOfRecTypeWithoutIndirection of Cc.IR.Type.t
    | InvalidPackAnn of RichWasm.Type.t
    | UnpackNonExistential of Cc.IR.Type.t
    | Ctx of t * Cc.IR.Type.t * [ `Let | `Split | `Cases | `Free ]
  [@@deriving sexp]

  let pp ff : t -> unit = function
    | UnmappedLocal ((de_bruijn, Some orig_name), env) ->
        fprintf ff "Local %d (originally %s) is not mapped in env: %a" de_bruijn
          orig_name Env.pp env
    | UnmappedCoderef (cref, env) ->
        fprintf ff "Function named %s is not mapped in env: %a" cref Env.pp env
    | x -> Sexp.pp_hum ff (sexp_of_t x)
end

module M = struct
  include Util.StateM (State) (Err)

  let todo reason = fail (TODO reason)

  let new_local (rep : RichWasm.Representation.t) : int t =
    let* st = get in
    let num = st.next_local in
    let+ () = put { next_local = num + 1; rev_locals = rep :: st.rev_locals } in
    num
end

(* NOTE: the following comments will use the following notation for the RichWasm (operand) stack

  f32 i32 i64 -> i64 f32 i32
   ^       ^      ^       ^
  bot     top    bot     top
 *)

module Compile = struct
  module A = Cc.IR
  module B = RichWasm
  module Res = Util.ResultM (Err)
  include M

  let rec compile_type (env : Env.t) : A.Type.t -> B.Type.t Res.t =
    let open Res in
    let open B.Type in
    function
    | Int -> ret @@ Num (Int I32)
    | Var (i, _) -> ret @@ Var i
    | Lollipop (pt, rt) ->
        let* pt' = compile_type env pt in
        let* rt' = compile_type env rt in
        ret @@ CodeRef (FunctionType ([], [ pt' ], [ rt' ]))
    | Prod ts -> mapM ~f:(compile_type env) ts >>| prod
    | Sum ts -> mapM ~f:(compile_type env) ts >>| sum
    | Rec t ->
        let env' = { env with type_map = None :: env.type_map } in
        let* rep = rep_of_typ env' t in
        (* NOTE: if coderef is used for indirection, then could have less
           restrictive copyability and dropability *)
        let kind : B.Kind.t = VALTYPE (rep, NoCopy, ExDrop) in
        let env'' = Env.add_type env rep in
        let* t' = compile_type env'' t in
        Rec (kind, t') |> ret
    | Exists t ->
        let kind : B.Kind.t = VALTYPE (Atom Ptr, NoCopy, ExDrop) in
        let env' = Env.add_type env (Atom Ptr) in
        let* t' = compile_type env' t in
        ret @@ Exists (Type kind, t')
    | Ref t -> compile_type env t >>| fun t -> ref (Base MM) (Ser t)

  and rep_of_typ (env : Env.t) : A.Type.t -> B.Representation.t Res.t =
    let open Res in
    let open B.Representation in
    function
    | Var (x, _) as typ ->
        List.nth env.type_map x
        |> lift_option (CannotFindRep typ)
        >>= lift_option (CannotResolveRepOfRecTypeWithoutIndirection typ)
    | Int -> ret @@ Atom I32
    (* NOTE: a coderef doesn't have ptr rep *)
    | Lollipop (Prod [ closure; _ ], _) ->
        let* closure' = rep_of_typ env closure in
        ret @@ Prod [ Atom I32; closure' ]
    | Prod ts ->
        let* rs = mapM ~f:(rep_of_typ env) ts in
        ret @@ Prod rs
    | Sum ts ->
        let* rs = mapM ~f:(rep_of_typ env) ts in
        ret @@ Sum rs
    | Ref _ -> ret @@ Atom Ptr
    | Rec t ->
        let env' = { env with type_map = None :: env.type_map } in
        rep_of_typ env' t
    | Exists t ->
        let env' = Env.add_type env (Atom Ptr) in
        rep_of_typ env' t
    | x -> fail @@ CannotFindRep x

  let compile_binop (binop : A.Binop.t) : B.Instruction.t list =
    let binop' : B.Int.Binop.t =
      match binop with
      | Add -> Add
      | Sub -> Sub
      | Mul -> Mul
      | Div -> Div Signed
    in
    [ Num (Int2 (I32, binop')) ]

  let rec compile_expr (env : Env.t) : A.Expr.t -> B.Instruction.t list t =
    let open A.Expr in
    let open B.Instruction in
    function
    | Var (((de_bruijn, _) as lvar), _) ->
        (match List.nth env.local_map de_bruijn with
        | Some idx -> ret @@ [ LocalGet (idx, Follow) ]
        | None -> fail (UnmappedLocal (lvar, env)))
    | Coderef (g, _) ->
        (match Map.find env.function_map g with
        | Some i -> ret @@ [ CodeRef i ]
        | None -> fail (UnmappedCoderef (g, env)))
    | Int (n, _) -> ret @@ [ NumConst (Int I32, n) ]
    | Tuple (es, _) ->
        (* (1, 2, 3, 4) goes on stack as 1 2 3 4 group *)
        let* es' = flat_mapM ~f:(compile_expr env) es in
        ret @@ es' @ [ Group (List.length es) ]
    | Inj (i, expr, t) ->
        let* expr' = compile_expr env expr in
        let* ts =
          (let open Res in
           compile_type env t >>= function
           | Sum ts -> ret ts
           | _ -> fail (InjInvalidAnn t))
          |> lift_result
        in
        ret @@ expr' @ [ Inject (None, i, ts) ]
    | Fold (mu, expr, _) ->
        let* mu' = compile_type env mu |> lift_result in
        let* expr' = compile_expr env expr in
        ret @@ expr' @ [ Fold mu' ]
    | Pack (witness, expr, t) ->
        let* expr' = compile_expr env expr in
        let* witness' = compile_type env witness |> lift_result in
        let* t' = compile_type env t |> lift_result in
        let* mu' =
          match t' with
          | Exists (_, t) -> ret t
          | x -> fail (InvalidPackAnn x)
        in
        ret @@ expr' @ [ Pack (Type witness', mu') ]
    | App (applicand, applicant, _) ->
        let* applicand' = compile_expr env applicand in
        let* applicant' = compile_expr env applicant in
        ret @@ applicant' @ applicand' @ [ CallIndirect ]
    | Let (b_t, rhs, body, _) ->
        let* rhs' = compile_expr env rhs in
        let* rep =
          rep_of_typ env b_t
          |> Result.map_error ~f:(fun x -> Err.Ctx (x, b_t, `Let))
          |> lift_result
        in
        let* fresh_idx = new_local rep in
        let env' = Env.add_local env fresh_idx in
        let* body' = compile_expr env' body in
        let cleanup = [ LocalGet (fresh_idx, Move); Drop ] in
        ret @@ rhs' @ [ LocalSet fresh_idx ] @ body' @ cleanup
    | Split (ts, rhs, body, _) ->
        let* rhs' = compile_expr env rhs in
        let* reps =
          mapM
            ~f:(fun t ->
              rep_of_typ env t
              |> Result.map_error ~f:(fun x -> Err.Ctx (x, t, `Split))
              |> lift_result)
            ts
        in
        let* fresh_idxs = mapM ~f:new_local reps in
        let env' = Env.add_locals env fresh_idxs in
        let* body' = compile_expr env' body in
        let cleanup =
          List.map fresh_idxs ~f:(fun idx -> [ LocalGet (idx, Move); Drop ])
          |> List.concat
        in
        ret
        @@ rhs'
        @ [ Ungroup ]
        @ List.map ~f:(fun idx -> LocalSet idx) (fresh_idxs |> List.rev)
        @ body'
        @ cleanup
    | Cases (scrutinee, cases, t) ->
        let* scrutinee' = compile_expr env scrutinee in
        let* cases' =
          mapM
            ~f:(fun (t, body) ->
              let* rep =
                rep_of_typ env t
                |> Result.map_error ~f:(fun x -> Err.Ctx (x, t, `Cases))
                |> lift_result
              in
              let* fresh_idx = new_local rep in
              let env' = Env.add_local env fresh_idx in
              let* body' = compile_expr env' body in
              (* NOTE: binding is already on the stack *)
              ret @@ [ LocalSet fresh_idx ] @ body'
              @ [ LocalGet (fresh_idx, Move); Drop ])
            cases
        in
        let* bt = compile_type env t |> lift_result in
        ret @@ scrutinee' @ [ Case (ArrowType (1, [ bt ]), InferFx, cases') ]
    | Unfold (_, expr, _) ->
        let* expr' = compile_expr env expr in
        ret @@ expr' @ [ Unfold ]
    | Unpack (rhs, body, t) ->
        let* rhs' = compile_expr env rhs in
        let* rep =
          let pkg_type = A.Expr.type_of rhs in
          match pkg_type with
          | Exists t_inner ->
              let env' = Env.add_type env (Atom Ptr) in
              rep_of_typ env' t_inner |> lift_result
          | t -> fail (UnpackNonExistential t)
        in
        let* fresh_idx = new_local rep in
        let env' = Env.add_local env fresh_idx in
        let env' = Env.add_type env' rep in
        let* body' = compile_expr env' body in
        let* bt = compile_type env t |> lift_result in
        ret @@ rhs'
        @ [
            Unpack
              ( ArrowType (1, [ bt ]),
                InferFx,
                [ LocalSet fresh_idx ] @ body'
                @ [ LocalGet (fresh_idx, Move); Drop ] );
          ]
    | If0 (v, e1, e2, t) ->
        let* v' = compile_expr env v in
        let* e1' = compile_expr env e1 in
        let* e2' = compile_expr env e2 in
        let* bt = compile_type env t |> lift_result in
        (* FIXME: local effects *)
        ret @@ v'
        @ [ NumConst (Int I32, 0); Num (IntTest (I32, Eqz)) ]
        @ [ Ite (ArrowType (1, [ bt ]), InferFx, e1', e2') ]
    | Binop (op, v1, v2, _) ->
        let op' = compile_binop op in
        let* v1' = compile_expr env v1 in
        let* v2' = compile_expr env v2 in
        ret @@ v1' @ v2' @ op'
    | New (v, _) ->
        let* v' = compile_expr env v in
        ret @@ v' @ [ New MM ]
    | Swap (e1, e2, _) ->
        let* e1' = compile_expr env e1 in
        let* e2' = compile_expr env e2 in
        ret @@ e1' @ e2' @ [ Swap (Path []); Group 2 ]
    | Free (e, t) ->
        let* e' = compile_expr env e in
        let* rep =
          rep_of_typ env t
          |> Result.map_error ~f:(fun x -> Err.Ctx (x, t, `Free))
          |> lift_result
        in
        let* fresh_idx = new_local rep in
        ret @@ e'
        @ [
            Load (Path [], Move);
            LocalSet fresh_idx;
            Drop;
            LocalGet (fresh_idx, Move);
          ]

  let compile_import ({ input; output; _ } : A.Import.t) :
      B.FunctionType.t Res.t =
    let open Res in
    let open B.FunctionType in
    let* input' = compile_type Env.empty input in
    let* output' = compile_type Env.empty output in
    ret (FunctionType ([], [ input' ], [ output' ]))

  let base_compile_function
      (env : Env.t)
      (ft : B.FunctionType.t)
      (body : A.Expr.t) : B.Module.Function.t Res.t =
    let open Res in
    let open B.Module.Function in
    let (FunctionType (_, params, _)) = ft in
    let+ body', state =
      compile_expr env body (State.empty ~next_local:(List.length params))
    in
    let locals = List.rev state.rev_locals in

    { typ = ft; locals; body = body' }

  let compile_function
      (env : Env.t)
      ({ export = _; name = _; param; return; body } : A.Function.t) :
      B.Module.Function.t Res.t =
    let open Res in
    let* param' = compile_type env param in
    let* return' = compile_type env return in
    (* {Rich}Wasm starts indexing locals with parameters; we only ever have one *)
    let env' = Env.add_local env 0 in
    base_compile_function env' (FunctionType ([], [ param' ], [ return' ])) body

  let compile_module ({ imports; functions; main } : A.Module.t) :
      B.Module.t Res.t =
    let open Res in
    let imports_only_map = List.mapi imports ~f:(fun i im -> (im.name, i)) in
    let import_offset = List.length imports in
    let functions_only_map =
      List.mapi functions ~f:(fun i f -> (f.name, import_offset + i))
    in
    (* FIXME: add imported functions to table *)
    let table = List.map functions_only_map ~f:snd in
    let* function_map =
      imports_only_map @ functions_only_map
      |> Map.of_list_with_key ~get_key:fst (module String)
      |> function
      | `Ok x -> ret @@ Map.map ~f:snd x
      | `Duplicate_key k -> fail (IntenalError ("dup fn " ^ k))
    in
    let env = { Env.empty with function_map } in
    let* main' =
      omap
        ~f:(fun main ->
          let ret_t = A.Expr.type_of main in
          let* ret_t' = compile_type env ret_t in
          let ft : B.FunctionType.t = FunctionType ([], [], [ ret_t' ]) in
          base_compile_function env ft main)
        main
    in
    let main_fn = main' |> Option.value_map ~default:[] ~f:(fun x -> [ x ]) in

    let* functions' = mapM ~f:(compile_function env) functions in
    let functions' = functions' @ main_fn in
    let* imports = mapM ~f:compile_import imports in
    let main_export =
      main
      |> Option.map ~f:(fun _ : B.Module.Export.t ->
          { name = "_start"; desc = Func (List.length functions' - 1) })
      |> Option.map ~f:List.return
      |> Option.value_or_thunk ~default:(fun () -> [])
    in
    let exports =
      List.filter_mapi functions ~f:(fun i A.Function.{ export; name; _ } ->
          Option.some_if export B.Module.Export.{ name; desc = Func i })
      @ main_export
    in
    ret @@ B.Module.{ imports; exports; functions = functions'; table }
end
