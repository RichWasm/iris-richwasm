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
  }
  [@@deriving sexp]

  let empty = { function_map = Map.empty (module String); local_map = [] }

  let add_local (env : t) (richwasm_local_index : int) : t =
    { env with local_map = richwasm_local_index :: env.local_map }

  let add_locals (env : t) (richwasm_local_indexs : int list) : t =
    { env with local_map = List.rev richwasm_local_indexs @ env.local_map }

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

  module Type = struct
    include Res
  end

  include M

  let rec compile_type : A.Type.t -> B.Type.t = function
    | Int -> Num (Int I32)
    | Var (i, _) -> Var i
    | Lollipop (pt, rt) ->
        CodeRef (FunctionType ([], [ compile_type pt ], [ compile_type rt ]))
    | Prod ts -> Prod (List.map ~f:compile_type ts)
    | Sum ts -> Sum (List.map ~f:compile_type ts)
    | Rec t -> Rec (compile_type t)
    | Exists t ->
        Exists (Type (VALTYPE (Prim Ptr, ExCopy, ExDrop)), compile_type t)
    | Ref t -> Ref (MM, compile_type t)

  let rec rep_of_typ : A.Type.t -> B.Representation.t Res.t =
    let open Res in
    let open B.Representation in
    function
    | Int -> ret @@ Prim I32
    (* NOTE: a coderef doesn't have ptr rep *)
    | Lollipop (Prod [ closure; _ ], _) ->
        let* closure' = rep_of_typ closure in
        ret @@ Prod [ closure'; Prim I32 ]
    | Prod ts ->
        let* rs = mapM ~f:rep_of_typ ts in
        ret @@ Prod rs
    | Sum ts ->
        let* rs = mapM ~f:rep_of_typ ts in
        ret @@ Sum rs
    | Ref _ -> ret @@ Prim Ptr
    (* FIXME: all rec types are currently unboxed, where should this be changed? *)
    | Rec t -> rep_of_typ t
    | Exists t -> rep_of_typ t
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
    | Var (((de_bruijn, _) as lvar), _) -> (
        match List.nth env.local_map de_bruijn with
        | Some idx -> ret @@ [ LocalGet idx ]
        | None -> fail (UnmappedLocal (lvar, env)))
    | Coderef (g, _) -> (
        match Map.find env.function_map g with
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
          match compile_type t with
          | Sum ts -> ret ts
          | _ -> fail (InjInvalidAnn t)
        in
        ret @@ expr' @ [ Inject (None, i, ts) ]
    | Fold (mu, expr, _) ->
        let mu' = compile_type mu in
        let* expr' = compile_expr env expr in
        ret @@ expr' @ [ Fold mu' ]
    | Pack (witness, expr, t) ->
        let* expr' = compile_expr env expr in
        let witness' = compile_type witness in
        let t' = compile_type t in
        ret @@ expr' @ [ Pack (Type witness', t') ]
    | App (applicand, applicant, _) ->
        let* applicand' = compile_expr env applicand in
        let* applicant' = compile_expr env applicant in
        ret @@ applicant' @ applicand' @ [ CallIndirect ]
    | Let (b_t, rhs, body, _) ->
        let* rhs' = compile_expr env rhs in
        let* rep = lift_result @@ rep_of_typ b_t in
        let* fresh_idx = new_local rep in
        let env' = Env.add_local env fresh_idx in
        let* body' = compile_expr env' body in
        ret @@ rhs' @ [ LocalSet fresh_idx ] @ body'
    | Split (ts, rhs, body, _) ->
        let* rhs' = compile_expr env rhs in
        let* reps = mapM ~f:(fun t -> lift_result @@ rep_of_typ t) ts in
        let* fresh_idxs = mapM ~f:new_local reps in
        let env' = Env.add_locals env fresh_idxs in
        let* body' = compile_expr env' body in
        ret @@ rhs' @ List.map ~f:(fun idx -> LocalSet idx) fresh_idxs @ body'
    | Cases (scrutinee, cases, t) ->
        let* scrutinee' = compile_expr env scrutinee in
        let* cases' =
          mapM
            ~f:(fun (t, body) ->
              let* rep = lift_result @@ rep_of_typ t in
              let* fresh_idx = new_local rep in
              let env' = Env.add_local env fresh_idx in
              let* body' = compile_expr env' body in
              (* NOTE: binding is already on the stack *)
              ret @@ [ LocalSet fresh_idx ] @ body')
            cases
        in
        let bt = compile_type t in
        (* FIXME: local effects *)
        ret @@ scrutinee' @ [ Case (BlockType [ bt ], LocalFx [], cases') ]
    | Unfold (_, expr, _) ->
        let* expr' = compile_expr env expr in
        ret @@ expr' @ [ Unfold ]
    | Unpack (rhs, body, t) ->
        let* rhs' = compile_expr env rhs in
        let* fresh_idx = new_local (Prim Ptr) in
        let env' = Env.add_local env fresh_idx in
        let* body' = compile_expr env' body in
        let bt = compile_type t in
        (* FIXME: local fx *)
        ret @@ rhs'
        @ [ Unpack (BlockType [ bt ], LocalFx [], LocalGet fresh_idx :: body') ]
    | If0 (v, e1, e2, t) ->
        let* v' = compile_expr env v in
        let* e1' = compile_expr env e1 in
        let* e2' = compile_expr env e2 in
        let bt = compile_type t in
        (* FIXME: local effects *)
        ret @@ v'
        @ [ NumConst (Int I32, 0); Num (IntTest (I32, Eqz)) ]
        @ [ Ite (BlockType [ bt ], LocalFx [], e1', e2') ]
    | Binop (op, v1, v2, _) ->
        let op' = compile_binop op in
        let* v1' = compile_expr env v1 in
        let* v2' = compile_expr env v2 in
        ret @@ v1' @ v2' @ op'
    | New (v, _) ->
        let* v' = compile_expr env v in
        let t = type_of v in
        let t' = compile_type t in
        ret @@ v' @ [ New (MM, t') ]
    | Swap (e1, e2, _) ->
        let* e1' = compile_expr env e1 in
        let* e2' = compile_expr env e2 in
        ret @@ e1' @ e2' @ [ Swap (Path []); Group 2 ]
    | Free (e, t) ->
        let* e' = compile_expr env e in
        let* rep = lift_result @@ rep_of_typ t in
        let* fresh_idx = new_local rep in
        ret @@ e'
        @ [ Load (Path []); LocalSet fresh_idx; Drop; LocalGet fresh_idx ]

  let compile_import ({ input; output; _ } : A.Import.t) :
      B.FunctionType.t Res.t =
    let open Res in
    let open B.FunctionType in
    ret (FunctionType ([], [ compile_type input ], [ compile_type output ]))

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
    let param' = compile_type param in
    let return' = compile_type return in
    (* {Rich}Wasm starts indexing locals with parameters; we only ever have one *)
    let env' = Env.add_local env 0 in
    base_compile_function env' (FunctionType ([], [ param' ], [ return' ])) body

  let compile_module ({ imports; functions; main } : A.Module.t) :
      B.Module.t Res.t =
    let open Res in
    let imports_only_map = List.mapi imports ~f:(fun i im -> (im.name, i)) in
    let import_offset = List.length imports - 1 in
    let functions_only_map =
      List.mapi functions ~f:(fun i f -> (f.name, import_offset + i))
    in
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
          let ret_t' = compile_type ret_t in
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
      |> Option.map ~f:(fun _ -> List.length functions' - 1)
      |> Option.map ~f:List.return
      |> Option.value_or_thunk ~default:(fun () -> [])
    in
    let exports =
      List.filter_mapi functions ~f:(fun i A.Function.{ export; _ } ->
          Option.some_if export i)
      @ main_export
    in
    ret @@ B.Module.{ imports; exports; functions = functions'; table }
end
