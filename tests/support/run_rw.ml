open! Core
open Stdlib.Format
open Richwasm_common
open Monads

module SingleRichWasm (Config : sig
  val rw_runtime_path : string
  val host_runtime_path : string
end) =
struct
  let inspect = false

  let run_wasm (wasm : string) =
    let open Config in
    Utils.Process_capture.run_concat
      ~env:(`Extend [ ("RW_RUNTIME_WASM_PATH", rw_runtime_path) ])
      ~input:wasm ~prog:"node" ~args:((if inspect then ["--inspect-wait"] else []) @ [host_runtime_path] ) ()
end

module UnnanotatedRW = Richwasm_common.Syntax
module AnnotatedRW = Richwasm_common.Annotated_syntax

module EndToEnd = struct
  (* need rank2 polymorphism *)
  type asprintf = { asprintf : 'a. ('a, formatter, unit, string) format4 -> 'a }

  module type SurfaceLang = sig
    module CompilerError : sig
      type t [@@deriving sexp_of]

      val pp : formatter -> t -> unit
    end

    val compile_to_richwasm :
      asprintf:asprintf ->
      String.t ->
      UnnanotatedRW.Module.t LogResultM(CompilerError)(String).t
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

    module M = LogResultM (E2Err) (String)

    let run ?(asprintf : asprintf = { asprintf }) (src : String.t) :
        String.t M.t =
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

      map_error_into E2Err.surface (Surface.compile_to_richwasm ~asprintf src)
      >>?! ( "elaborate",
             Elaborate.elab_module,
             Richwasm_common.Annotated_syntax.Module.pp,
             E2Err.elaborate )
      >>? (Main.compile, E2Err.richwasm)
      >>| Main.wasm_ugly_printer
      >>? (Wat2wasm.wat2wasm ~check:false, E2Err.wat2wasmunchecked)
      >>?! ( "wat",
             Wasm2wat.wasm2wat ~pretty:true ~check:false,
             pp_print_string,
             E2Err.wasm2watunchecked )
      >>? (Wat2wasm.wat2wasm ~check:true, E2Err.wat2wasm)
      >>? (Runner.run_wasm, E2Err.runtime)
  end
end
