open! Base
open! Stdlib.Format
open! Richwasm_common

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
      | Global n | Coderef n -> (
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
    | Int -> B.Type.NumT (VALTYPE (PrimR I32R, ImCopy, ImDrop), IntT I32T)
    | _ -> failwith "todo"

  let mk_it ?(before : B.Type.t list = []) ?(after : B.Type.t list = []) () :
      B.InstructionType.t =
    InstrT (before, after)

  let rec compile_value (env : Env.t) : A.Value.t -> B.Instruction.t list t =
    function
    | Var (i, x) -> (*let* idx =  *) fail TODO
    | Global g -> (
        match Map.find env.global_map g with
        | Some (i, typ) ->
            let it = (mk_it ~after:[ typ ]) () in
            ret @@ [ B.Instruction.IGlobalGet (it, Z.of_int i) ]
        | None -> fail (UnmappedCoderef (g, env)))
    | Coderef g -> (
        match Map.find env.function_map g with
        | Some (i, typ) ->
            let it =
              mk_it
                ~after:
                  [
                    (* TODO: double check kind *)
                    B.Type.CodeRefT (VALTYPE (PrimR PtrR, NoCopy, NoDrop), typ);
                  ]
                ()
            in
            ret @@ [ B.Instruction.ICodeRef (it, Z.of_int i) ])
    | Int n ->
        let it = mk_it ~after:[ compile_type Int ] () in
        ret @@ [ B.Instruction.INumConst (it, Z.of_int n) ]
    | Tuple n ->
        (* (1, 2, 3, 4, 5, 6) needs to go into the wasm stack st;
            what to do with family? *)
        fail TODO
    | _ -> fail TODO

  and compile_expr (env : Env.t) : A.Expr.t -> B.Instruction.t list t = function
    | Val v -> compile_value env v
    | _ -> fail TODO

  let compile_import ({ typ; name } : A.Import.t) = ()

  let compile_module ({ imports; toplevels; main } : A.Module.t) :
      B.Module.t Res.t =
    let open Res in
    (* TODO: map function names to index into table *)
    (* TODO: function start must have [] -> [] ft, main therefore cannot leave anything on op stack *)

    (* TODO: this can't be empty when calling main *)
    let env = Env.empty in
    let state = State.empty in
    let* main_fn, state' =
      match main with
      | None -> Ok ([], state)
      | Some main ->
          let* body, state = compile_expr env main state in
          (* TODO: init tenv *)
          let tenv = TEnv.empty in
          let* expr_typ = Type.type_of_expr tenv main in
          let stack_typ = compile_type expr_typ in
          let func : B.Module.Function.t =
            { mf_type = MonoFunT (InstrT ([], [ stack_typ ])); mf_body = body }
          in
          Ok ([ func ], state)
    in

    let m_funcs, m_table, m_globals = ([] @ main_fn, [], []) in
    (* NOTE: start should only be used for module initialization, not main *)
    let m_start = None in
    let m_imports = [] in
    let main_export =
      main
      |> Option.map ~f:(fun _ -> List.length m_funcs - 1)
      |> Option.map ~f:Z.of_int
      |> Option.map ~f:(fun i ->
             [ B.Module.Export.{ me_name = "_start"; me_desc = ExFunction i } ])
      |> Option.value_or_thunk ~default:(fun () -> [])
    in
    let m_exports = [] @ main_export in

    Ok B.Module.{ m_imports; m_exports; m_globals; m_funcs; m_table; m_start }
end
