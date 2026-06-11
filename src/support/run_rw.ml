open! Core
open Stdlib.Format
open Richwasm_common
open Monads

module type Runner1 = sig
  val run_wasm :
    ?start_type:String.t -> String.t -> (String.t, String.t) Result.t
end

module type Runner2 = sig
  (** [link] = module-1 export name imported by module 2 *)
  val run_wasm :
    ?start_type:String.t ->
    link:String.t ->
    String.t * String.t ->
    (String.t, String.t) Result.t
end

module type Runner3 = sig
  (** [links] = (module-1 export name, module-2 export name) *)
  val run_wasm :
    links:String.t * String.t ->
    String.t * String.t * String.t ->
    (String.t, String.t) Result.t
end

let inspect = false

module SingleRichWasm (Config : sig
  val rw_runtime_path : string
  val host_runtime_path : string
end) : Runner1 = struct
  let run_wasm ?start_type (wasm : string) =
    let open Config in
    let env =
      ("RW_RUNTIME_WASM_PATH", rw_runtime_path)
      ::
      (match start_type with
      | Some t -> [ ("RW_START_TYPE", t) ]
      | None -> [])
    in
    Process_utils.Process_capture.run_concat ~env:(`Extend env) ~input:wasm
      ~prog:"node"
      ~args:
        ((if inspect then [ "--inspect-wait" ] else []) @ [ host_runtime_path ])
      ()
end

module DoubleRichWasm (Config : sig
  val rw_runtime_path : string
  val host_runtime_path : string
end) : Runner2 = struct
  let run_wasm ?start_type ~link (module1, module2) =
    let open Config in
    let env =
      ("RW_RUNTIME_WASM_PATH", rw_runtime_path)
      ::
      (match start_type with
      | Some t -> [ ("RW_START_TYPE", t) ]
      | None -> [])
    in
    Process_utils.Process_capture.run_concat ~env:(`Extend env)
      ~inputs:[ module1; module2 ] ~prog:"node"
      ~args:
        ((if inspect then [ "--inspect-wait" ] else [])
        @ [ host_runtime_path; link ])
      ()
end

module TripleRichWasm (Config : sig
  val rw_runtime_path : string
  val host_runtime_path : string
end) : Runner3 = struct
  let run_wasm ~links:(link1, link2) (module1, module2, module3) =
    let open Config in
    Process_utils.Process_capture.run_concat
      ~env:(`Extend [ ("RW_RUNTIME_WASM_PATH", rw_runtime_path) ])
      ~inputs:[ module1; module2; module3 ] ~prog:"node"
      ~args:
        ((if inspect then [ "--inspect-wait" ] else [])
        @ [ host_runtime_path; link1; link2 ])
      ()
end

module UnnanotatedRW = Richwasm_common.Syntax
module AnnotatedRW = Richwasm_common.Annotated_syntax

(** Serialize [_start]'s result types (sexp) for the host walker; [None] if no [_start]. *)
let start_type_sexp (m : UnnanotatedRW.Module.t) : String.t option =
  let open UnnanotatedRW in
  let num_imports = List.length m.Module.imports in
  List.find_map m.Module.exports ~f:(fun (e : Module.Export.t) ->
      match e.Module.Export.desc with
      | Module.Export.Desc.Func idx
        when String.equal e.Module.Export.name "_start" ->
          List.nth m.Module.functions (idx - num_imports)
          |> Option.map ~f:(fun (f : Module.Function.t) ->
                 let (FunctionType.FunctionType (_, _, results)) =
                   f.Module.Function.typ
                 in
                 Sexp.to_string ([%sexp_of: Type.t list] results))
      | _ -> None)

module EndToEnd = struct
  (* need rank2 polymorphism *)
  type asprintf = { asprintf : 'a. ('a, formatter, unit, string) format4 -> 'a }

  module type SurfaceLang = sig
    module CompilerError : sig
      type t [@@deriving sexp_of]

      val pp : formatter -> t -> unit
    end

    val compile_to_richwasm :
      ?info:String.t ->
      asprintf:asprintf ->
      String.t ->
      UnnanotatedRW.Module.t LogResultM(CompilerError)(String).t
  end

  module Make_common (Surface : SurfaceLang) = struct
    module E2Err = struct
      type t =
        | Surface of Surface.CompilerError.t
        | Elaborate of Elaborate.Err.t
        | Typecheck of Richwasm_extract.Typechecker.type_error List.t
        | RichWasm of Extract_compat.CompilerError.t
        | Wat2WasmUnchecked of String.t
        | Wasm2WatUnchecked of String.t
        | Wat2Wasm of String.t
        | Runtime of String.t
      [@@deriving variants]

      let pp ff = function
        | Surface err -> fprintf ff "Surface:@ %a" Surface.CompilerError.pp err
        | Elaborate err -> fprintf ff "Elaborate:@ %a" Elaborate.Err.pp err
        | Typecheck err ->
            fprintf ff "Typecheck:@ %a" Pipeline.pp_typecheck_errors err
        | RichWasm err ->
            fprintf ff "RichWasm:@ %a" Extract_compat.CompilerError.pp err
        | Wat2WasmUnchecked err -> fprintf ff "Wat2WasmUnchecked:@ %s" err
        | Wasm2WatUnchecked err -> fprintf ff "Wasm2WatUnchecked:@ %s" err
        | Wat2Wasm err -> fprintf ff "Wat2Wasm:@ %s" err
        | Runtime err -> fprintf ff "Runtime:@ %s" err
    end

    module M = LogResultM (E2Err) (String)

    let compile_to_wasm
        ?(asprintf : asprintf = { asprintf })
        ?prefix
        (src : String.t) : (String.t * String.t option) M.t =
      let module SurfM = LogResultM (Surface.CompilerError) (String) in
      let open M in
      let ( >>? ) (type a) (m : a t) (f, err_map) =
        m >>= fun x -> f x |> Result.map_error ~f:err_map |> lift_result
      in

      let ( >>?! ) (type a) (m : a t) (name, f, pp, err_map) =
        let log_pp x : unit t =
          let len = String.length name in
          let fill = '=' in
          tell
            (asprintf.asprintf "@{<cyan>%a@} @{<yellow>%s@} @{<cyan>%a@}@.%a"
               (Util.pp_pad ~fill ~len) false name (Util.pp_pad ~fill ~len) true
               pp x)
        in

        m >>= fun x ->
        f x |> Result.map_error ~f:err_map |> lift_result >>= fun y ->
        log_pp y >>= fun () -> ret y
      in

      let stage name =
        match prefix with
        | None -> name
        | Some p -> p ^ ":" ^ name
      in

      let* rwmod =
        map_error_into E2Err.surface
          (Surface.compile_to_richwasm ?info:prefix ~asprintf src)
      in
      let start_type = start_type_sexp rwmod in
      let* wasm =
        ret rwmod
        >>?! ( stage "elaborate",
               Elaborate.elab_module,
               Richwasm_common.Annotated_syntax.Module.pp,
               E2Err.elaborate )
        >>? ( (fun x ->
                Richwasm_common.Main.typecheck x |> Result.map ~f:(fun () -> x)),
              E2Err.typecheck )
        >>? (Main.compile, E2Err.richwasm)
        >>| Main.wasm_ugly_printer
        >>? (Wat2wasm.wat2wasm ~check:false, E2Err.wat2wasmunchecked)
        >>?! ( stage "wat",
               Wasm2wat.wasm2wat ~pretty:true ~check:false,
               pp_print_string,
               E2Err.wasm2watunchecked )
        >>? (Wat2wasm.wat2wasm ~check:true, E2Err.wat2wasm)
      in
      ret (wasm, start_type)

    let run_runtime
        (type inp)
        ~(run : inp -> (String.t, String.t) Result.t)
        (input : inp) : String.t M.t =
      run input |> Result.map_error ~f:E2Err.runtime |> M.lift_result
  end

  module Make1 (Surface : SurfaceLang) (Runner : Runner1) = struct
    include Make_common (Surface)

    let run ?(asprintf : asprintf = { asprintf }) (src : String.t) :
        String.t M.t =
      let open M in
      let* wasm, start_type = compile_to_wasm ~asprintf src in
      run_runtime ~run:(Runner.run_wasm ?start_type) wasm
  end

  module Make2 (Surface : SurfaceLang) (Runner : Runner2) = struct
    include Make_common (Surface)

    let run2
        ?(asprintf : asprintf = { asprintf })
        ~(link : String.t)
        (src1 : String.t)
        (src2 : String.t) : String.t M.t =
      let open M in
      let* wasm1, _ = compile_to_wasm ~asprintf ~prefix:"m1" src1 in
      let* wasm2, start_type = compile_to_wasm ~asprintf ~prefix:"m2" src2 in
      run_runtime ~run:(Runner.run_wasm ?start_type ~link) (wasm1, wasm2)
  end

  module Make3 (Surface : SurfaceLang) (Runner : Runner3) = struct
    include Make_common (Surface)

    let run3
        ?(asprintf : asprintf = { asprintf })
        ~(links : String.t * String.t)
        (src1 : String.t)
        (src2 : String.t)
        (src3 : String.t) : String.t M.t =
      let open M in
      let* wasm1, _ = compile_to_wasm ~asprintf ~prefix:"m1" src1 in
      let* wasm2, _ = compile_to_wasm ~asprintf ~prefix:"m2" src2 in
      let* wasm3, _ = compile_to_wasm ~asprintf ~prefix:"m3" src3 in
      run_runtime ~run:(Runner.run_wasm ~links) (wasm1, wasm2, wasm3)
  end
end
