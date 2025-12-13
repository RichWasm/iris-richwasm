open! Core
open Stdlib.Format
open Richwasm_common
open Monads

module SingleRichWasm (Config : sig
  val rw_runtime_path : string
  val host_runtime_path : string
end) =
struct
  let run_wasm (wasm : string) =
    let open Config in
    Utils.Process_capture.run_concat
      ~env:(`Extend [ ("RW_RUNTIME_WASM_PATH", rw_runtime_path) ])
      ~input:wasm ~prog:"node" ~args:[ host_runtime_path ] ()
end

module UnnanotatedRW = Richwasm_common.Syntax
module AnnotatedRW = Richwasm_common.Annotated_syntax

module EndToEnd = struct
  module type SurfaceLang = sig
    module CompilerError : sig
      type t [@@deriving sexp_of]

      val pp : formatter -> t -> unit
    end

    val compile_to_richwasm :
      String.t -> UnnanotatedRW.Module.t LogResultM(CompilerError)(String).t
  end

  module type Runner = sig
    val run_wasm : String.t -> (String.t, String.t) Result.t
  end

  module Make (Surface : SurfaceLang) (Runner : Runner) = struct
    module E2Err = struct
      type t =
        | Surface of Surface.CompilerError.t
        | Elaborate of Elaborate.Err.t
        | RichWasm of Extract_compat.CompilerError.t
        | Wat2WasmUnchecked of String.t
        | Wasm2WatUnchecked of String.t
        | Wat2Wasm of String.t
        | Runtime of String.t
      [@@deriving sexp_of, variants]

      let pp ff = function
        | Surface err -> fprintf ff "Surface:@ %a" Surface.CompilerError.pp err
        | Elaborate err -> fprintf ff "Elaborate:@ %a" Elaborate.Err.pp err
        | RichWasm err ->
            fprintf ff "RichWasm:@ %a" Extract_compat.CompilerError.pp err
        | Wat2WasmUnchecked err -> fprintf ff "Wat2WasmUnchecked:@ %s" err
        | Wasm2WatUnchecked err -> fprintf ff "Wasm2WatUnchecked:@ %s" err
        | Wat2Wasm err -> fprintf ff "Wat2Wasm:@ %s" err
        | Runtime err -> fprintf ff "Runtime:@ %s" err
    end

    module SurfM = LogResultM (Surface.CompilerError) (String)
    module M = LogResultM (E2Err) (String)

    let lift_result_map_err (r : ('a, 'e) Result.t) ~(err_map : 'e -> M.error) :
        'a M.t =
      match r with
      | Ok x -> M.ret x
      | Error e -> M.fail (err_map e)

    let ( >>?! ) x (name, f, pp, err_map) =
      let open M in
      let log_pp ~name (pp : formatter -> 'a -> unit) (x : 'a) : unit t =
        let len = String.length name in
        let lpad = Util.pad ~fill:'=' ((78 - len) / 2) in
        let rpad = lpad ^ if len % 2 = 0 then "" else "=" in
        tell
          (Ocolor_format.asprintf "@{<cyan>%s@} @{<yellow>%s@} @{<cyan>%s@}@.%a"
             lpad name rpad pp x)
      in

      x >>= fun v ->
      lift_result_map_err (f v) ~err_map >>= fun out ->
      let+ () = log_pp ~name pp out in
      out

    let ( >>? ) x (f, err_map) =
      let open M in
      x >>= fun v -> lift_result_map_err (f v) ~err_map

    let run (src : String.t) : String.t M.t =
      let open M in
      SurfM.map_error_to ~f:E2Err.surface (Surface.compile_to_richwasm src)
      >>?! ( "elaborate",
             Elaborate.elab_module,
             Richwasm_common.Annotated_syntax.Module.pp_sexp,
             E2Err.elaborate )
      >>? (Main.compile, E2Err.richwasm)
      >>| Main.wasm_ugly_printer
      >>? (Wat2wasm.wat2wasm ~check:false, E2Err.wat2wasmunchecked)
      >>?! ( "wat",
             Wasm2wat.wasm2wat ~check:false,
             pp_print_string,
             E2Err.wasm2watunchecked )
      >>? (Wat2wasm.wat2wasm ~check:true, E2Err.wat2wasm)
      >>? (Runner.run_wasm, E2Err.runtime)
  end
end
