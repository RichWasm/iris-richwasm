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

  (* let lookup_debruijn (i:int) : [`Local of int | `Env of int] t =
    let* st = get () in
    match st.env_layout with
    | None ->
        (* 0 = newest => map to depth-1, then subtract i *)
        let idx = depth st - 1 - i in
        if idx < 0 then fail TODO else ret (`Local idx)
    | Some (k, slot_of) ->
        if i < k then
          ret (`Local (k - 1 - i))
        else
          let slot = slot_of (i - k) in
          ret (`Env slot) *)
end

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
      | Pack (witness, value, typ) ->
          (* TODO: check? *)
          Ok typ

    let rec type_of_expr (env : TEnv.t) : A.Expr.t -> A.Type.t t = function
      | Val v -> type_of_value env v
  end

  include M

  let rec compile_type : A.Type.t -> B.Type.t = function
    | Int -> B.Type.Num (Int I32)
    | _ -> failwith "todo"

  let rec compile_value (env : Env.t) : A.Value.t -> B.Instruction.t list t =
    function
    | Var (i, x) -> (*let* idx =  *) fail TODO
    | Coderef g -> (
        match Map.find env.function_map g with
        | Some (i, typ) -> ret @@ [ B.Instruction.CodeRef i ]
        | None -> fail (UnmappedCoderef (g, env)))
    | Int n -> ret @@ [ B.Instruction.NumConst (Int I32, n) ]
    | Tuple n ->
        (* (1, 2, 3, 4, 5, 6) needs to go into the wasm stack st;
            what to do with family? *)
        fail TODO
    | _ -> fail TODO

  and compile_expr (env : Env.t) : A.Expr.t -> B.Instruction.t list t = function
    | Val v -> compile_value env v
    | _ -> fail TODO

  let compile_import ({ typ; name } : A.Import.t) = ()

  let compile_module ({ imports; functions; main } : A.Module.t) :
      B.Module.t Res.t =
    (* TODO: map function names to index into table *)
    (* TODO: function start must have [] -> [] ft, main therefore cannot leave anything on op stack *)

    (* TODO: this can't be empty when calling main *)
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
