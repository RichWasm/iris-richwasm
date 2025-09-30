open! Base
open! Stdlib.Format
module RichWasm = Richwasm_common.Syntax

module StringMap = struct
  type 'a t = 'a Map.M(String).t [@@deriving sexp]
end

module State = struct
  type t = {
    next_local : int;
    rev_locals : int list;
    num_params : int;
  }
  [@@deriving sexp]

  let empty = { next_local = 0; rev_locals = []; num_params = 0 }
end

module Env = struct
  type t = {
    global_map : (int * RichWasm.Type.t) StringMap.t;
    function_map : (int * RichWasm.FunctionType.t) StringMap.t;
        (*local_map : int *)
  }
  [@@deriving sexp]

  let empty =
    {
      global_map = Map.empty (module String);
      function_map = Map.empty (module String);
    }

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module TEnv = struct
  type t = {
    locals : Cc.IR.Type.t Map.M(Cc.LVar).t;
    tls : Cc.IR.Type.t Map.M(String).t;
  }
  [@@deriving sexp]

  let empty =
    { locals = Map.empty (module Cc.LVar); tls = Map.empty (module String) }
end

module Err = struct
  type t =
    | TODO
    | UnmappedGlobal of (string * Env.t)
    | UnmappedCoderef of (string * Env.t)
    | MissingLocalTEnv of (Cc.LVar.t * TEnv.t)
    | MissingGlobalTEnv of (string * TEnv.t)
    | InjInvalidAnn of Cc.IR.Type.t
    | EmptyCases
    | FreeNonRef of Cc.IR.Type.t
  [@@deriving sexp]

  let to_string : t -> string = function
    | TODO -> "TODO"
    | UnmappedGlobal (glob, env) ->
        asprintf "Global named %s is not mapped in env: %a" glob Env.pp env
    | UnmappedCoderef (cref, env) ->
        asprintf "Function named %s is not mapped in env: %a" cref Env.pp env
    | x -> asprintf "%a" Sexp.pp_hum (sexp_of_t x)
end

module M = struct
  include Util.StateM (State) (Err)
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

    let rec type_of_value (env : TEnv.t) : A.Value.t -> A.Type.t t = function
      | Var lvar -> (
          match Map.find env.locals lvar with
          | None -> Error (MissingLocalTEnv (lvar, env))
          | Some x -> Ok x)
      | Coderef n -> (
          match Map.find env.tls n with
          | None -> Error (MissingGlobalTEnv (n, env))
          | Some x -> Ok x)
      | Int _ -> Ok Int
      | Tuple vs ->
          let* vs' = mapM ~f:(type_of_value env) vs in
          Ok (Prod vs' : A.Type.t)
      | Inj (_, _, typ) -> Ok typ
      | Fold (typ, _) -> Ok typ
      | Pack (_, _, typ) -> Ok typ

    let rec type_of_expr (env : TEnv.t) : A.Expr.t -> A.Type.t t =
      let open A.Type in
      function
      | Val v -> type_of_value env v
      | App (v1, _) ->
          let* v1t = type_of_value env v1 in
          fail TODO
      | Let (t, lhs, body) -> fail TODO
      | Split (ts, lhs, body) -> fail TODO
      | Cases (scrutinee, cases) -> (
          match List.nth cases 0 with
          | Some (_, e) ->
              let* env' = fail TODO in
              type_of_expr env' e
          | None -> fail EmptyCases)
      | Unfold (t, _) -> ret t
      | Unpack (_, _, t) -> ret t
      | If0 (_, l, _) -> type_of_expr env l
      | Binop ((Add | Sub | Mul | Div), _, _) -> Ok Int
      | New v ->
          let* v' = type_of_value env v in
          ret @@ Ref v'
      | Swap (v1, v2) -> fail TODO
      | Free v -> (
          let* v' = type_of_value env v in
          match v' with
          | Ref v -> ret v
          | x -> fail (FreeNonRef x))
  end

  include M

  let rec compile_type : A.Type.t -> B.Type.t = function
    | Int -> Num (Int I32)
    | Var (i, _) -> Var i
    | Lollipop ((ct, pt), rt) ->
        CodeRef
          (FunctionType
             ([], [ compile_type ct; compile_type pt ], [ compile_type rt ]))
    | Prod ts -> Prod (List.map ~f:compile_type ts)
    | Sum ts -> Sum (List.map ~f:compile_type ts)
    | Rec t -> Rec (compile_type t)
    (* FIXME: what should the representation be? *)
    | Exists t -> Exists (Type (VALTYPE (Var 0, ExCopy, ExDrop)), compile_type t)
    | Ref t -> Ref (MM, compile_type t)

  let compile_binop (binop : A.Binop.t) : B.Instruction.t list =
    let binop' : B.Int.Binop.t =
      match binop with
      | Add -> Add
      | Sub -> Sub
      | Mul -> Mul
      | Div -> Div Signed
    in
    [ Num (Int2 (I32, binop')) ]

  let rec compile_value (env : Env.t) : A.Value.t -> B.Instruction.t list t =
    let open B.Instruction in
    function
    | Var (i, x) -> (*let* idx =  *) fail TODO
    | Coderef g -> (
        match Map.find env.function_map g with
        | Some (i, _) -> ret @@ [ CodeRef i ]
        | None -> fail (UnmappedCoderef (g, env)))
    | Int n -> ret @@ [ NumConst (Int I32, n) ]
    | Tuple vs ->
        (* (1, 2, 3, 4) goes on stack as 1 2 3 4 group *)
        let* vs' = flat_mapM ~f:(compile_value env) vs in
        ret @@ vs' @ [ Group (List.length vs) ]
    | Inj (i, v, t) ->
        let* v' = compile_value env v in
        let* ts =
          match compile_type t with
          | Sum ts -> ret ts
          | _ -> fail (InjInvalidAnn t)
        in
        ret @@ v' @ [ Inject (i, ts) ]
    | Fold (t, v) ->
        let* v' = compile_value env v in
        let t' = compile_type t in
        ret @@ v' @ [ Fold t' ]
    | Pack (w, v, t) ->
        let* v' = compile_value env v in
        let w' = compile_type w in
        let t' = compile_type t in
        ret @@ v' @ [ Pack (Type w', t') ]

  and compile_expr (env : Env.t) : A.Expr.t -> B.Instruction.t list t = function
    | Val v -> compile_value env v
    | App (v1, v2) ->
        let* v1' = compile_value env v1 in
        let* v2' = compile_value env v2 in
        ret @@ v2' @ v1' @ [ CallIndirect ]
    | Let (t, rhs, body) -> fail TODO
    | Split (ts, rhs, body) -> fail TODO
    | Cases (scrutinee, cases) ->
        let* scrutinee' = compile_value env scrutinee in
        let* cases' =
          mapM
            ~f:(fun (t, body) ->
              (* TODO: binding is already on the stack *)
              let env' = env in
              let* body' = compile_expr env' body in
              fail TODO)
            cases
        in
        let* it = fail TODO in
        let* lfx = fail TODO in
        ret @@ scrutinee' @ [ Case (it, lfx, cases') ]
    | Unfold (_, v) ->
        let* v' = compile_value env v in
        ret @@ v' @ [ Unfold ]
    | Unpack (v, e, t) ->
        let* v' = compile_value env v in
        let* env' = fail TODO in
        let* e' = compile_expr env' e in
        fail TODO
    | If0 (v, e1, e2) ->
        let* v' = compile_value env v in
        let* e1' = compile_expr env e1 in
        let* e2' = compile_expr env e2 in
        fail TODO
    | Binop (op, v1, v2) ->
        let op' = compile_binop op in
        let* v1' = compile_value env v1 in
        let* v2' = compile_value env v2 in
        (* TODO: confirm operand order *)
        ret @@ v1' @ v2' @ op'
    | New v ->
        let* v' = compile_value env v in
        let* tenv = fail TODO in
        let* t = lift_result @@ Type.type_of_value tenv v in
        let t' = compile_type t in
        ret @@ v' @ [ RefNew (MM, t') ]
    | Swap (v1, v2) ->
        let* v1' = compile_value env v1 in
        let* v2' = compile_value env v2 in
        (* TODO: double check Path *)
        ret @@ v1' @ v2' @ [ RefSwap (Path [ Unwrap ]) ]
    | Free v ->
        let* v' = compile_value env v in
        let* tenv = fail TODO in
        let* t = lift_result @@ Type.type_of_value tenv v in
        let t' = compile_type t in
        ret @@ v' @ [ RefLoad (Path [ Unwrap ], t') ]

  let compile_import ({ typ; name } : A.Import.t) = ()

  let compile_module ({ imports; functions; main } : A.Module.t) :
      B.Module.t Res.t =
    (* TODO: map function names to index into table *)
    let prog : B.Module.t M.t =
      let env = Env.empty in
      let* main_fn =
        match main with
        | None -> ret []
        | Some main ->
            let* body = compile_expr env main in
            (* TODO: init tenv *)
            let tenv = TEnv.empty in
            let* expr_typ = lift_result @@ Type.type_of_expr tenv main in
            let stack_typ = compile_type expr_typ in
            (* TODO: locals *)
            let func : B.Module.Function.t =
              { typ = FunctionType ([], [], [ stack_typ ]); locals = []; body }
            in
            ret [ func ]
      in

      let functions, table, globals = ([] @ main_fn, [], []) in
      (* NOTE: start should only be used for module initialization, not main *)
      let start = None in
      let imports = [] in
      let main_export =
        main
        |> Option.map ~f:(fun _ -> List.length functions - 1)
        |> Option.map ~f:(fun i ->
               [ B.Module.Export.{ name = "_start"; desc = ExFunction i } ])
        |> Option.value_or_thunk ~default:(fun () -> [])
      in
      let exports = [] @ main_export in

      ret @@ B.Module.{ imports; exports; globals; functions; table; start }
    in
    let open Res in
    let+ prog, _ = prog State.empty in
    prog
end
