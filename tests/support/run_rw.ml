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
      String.t -> (UnnanotatedRW.Module.t, CompilerError.t) Result.t
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

    module M = ResultM (E2Err)

    let ( >>? ) x (f, map_err) =
      let open M in
      x >>= fun v -> f v |> Result.map_error ~f:map_err

    let run (src : String.t) : String.t M.t =
      let open M in
      ret src
      >>? (Surface.compile_to_richwasm, E2Err.surface)
      >>? (Elaborate.elab_module, E2Err.elaborate)
      >>? (Main.compile, E2Err.richwasm)
      >>| Main.wasm_ugly_printer
      >>? (Wat2wasm.wat2wasm ~check:false, E2Err.wat2wasmunchecked)
      >>? (Wasm2wat.wasm2wat ~check:false, E2Err.wasm2watunchecked)
      >>? (Wat2wasm.wat2wasm ~check:true, E2Err.wat2wasm)
      >>? (Runner.run_wasm, E2Err.runtime)
  end
end
