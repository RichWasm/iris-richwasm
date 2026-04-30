open! Core
open! Stdlib.Format
open! Richwasm_common.Util
open Result_utils

let ll_pipeline x =
  let open Richwasm_lin_lang in
  x
  |> Main.compile_ast
  |> Main.Res.T.run
  |> fst
  |> or_fail_pp Main.CompileErr.pp

let ll_str_pipeline x =
  let open Richwasm_lin_lang in
  x |> Parse.from_string_exn |> ll_pipeline

let ml_pipeline x =
  let open Richwasm_mini_ml in
  x |> Convert.cc_module |> Codegen.compile_module

let ml_str_pipeline x =
  let open Richwasm_mini_ml in
  x |> Parse.from_string_exn |> ml_pipeline

let elab_pipeline (x : Richwasm_common.Syntax.Module.t) =
  x
  |> Richwasm_common.Elaborate.elab_module
  |> or_fail_pp Richwasm_common.Elaborate.Err.pp

let parse_richwasm s =
  s
  |> Parsexp.Single.parse_string_exn
  |> Richwasm_common.Syntax.Module.t_of_sexp

let pp_typecheck_error ff = function
  | Richwasm_extract.Typechecker.NormalError s -> fprintf ff "%s" s
  | Richwasm_extract.Typechecker.FrameError (s, a, b) ->
      let pp_it = Richwasm_common.Annotated_syntax.InstructionType.pp in
      fprintf ff "Frame error: %s (%a, %a)" s pp_it a pp_it b

let pp_typecheck_errors ff =
  let pp_list = pp_print_list_post ~pp_sep:(fun ff () -> fprintf ff ";@ ") in
  fprintf ff "%a" (pp_list pp_typecheck_error)

let pp_typecheck_errors_prefix ff =
  fprintf ff "Typechecker failed with error: %a" pp_typecheck_errors

let wasm_pipeline x =
  elab_pipeline x
  |> (fun x -> Richwasm_common.Main.typecheck x |> Result.map ~f:(fun () -> x))
  |> or_fail_pp pp_typecheck_errors_prefix
  |> Richwasm_common.Main.compile
  |> or_fail_pp Richwasm_common.Extract_compat.CompilerError.pp
  |> Richwasm_common.Main.wasm_ugly_printer

let pp_wasm ?(pretty = false) ff x =
  let fmted =
    Wat2wasm.wat2wasm ~check:false x
    |> Result.map_error ~f:(asprintf "wat2wasm(unchecked): %s")
    |> Result.bind ~f:(Wasm2wat.wasm2wat ~pretty ~check:false)
    |> Result.map_error ~f:(asprintf "wasm2wat(unchecked): %s")
    |> or_fail_pp pp_print_string
  in
  fmted
  |> Wat2wasm.wat2wasm
  |> or_fail_pp (fun ff x -> fprintf ff "wat2wasm: %s\n%s" x fmted)
  |> Wasm2wat.pp_as_wat ~pretty ff
