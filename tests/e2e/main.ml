open! Core
open! Test_support
open! Stdlib.Format
open Richwasm_common.Util

module IDontRespectLibraryInternals = struct
  module Core = Alcotest_engine__Core
  module Pp = Alcotest_engine__Pp

  (* if this ever breaks, its safe to go back to using `fail`.
     it just reports errors twice which is annoying *)
  let custom_fail header msg =
    raise
      (Core.Check_error
         (fun ppf () -> Fmt.pf ppf "%a %s@.%s" Pp.tag `Fail header msg))
end

module EndToEnd = Run_rw.EndToEnd

module type SurfaceLang = Run_rw.EndToEnd.SurfaceLang

module LL : Run_rw.EndToEnd.SurfaceLang = struct
  module CompilerError = Richwasm_lin_lang.Main.CompileErr

  let compile_to_richwasm ~(asprintf : EndToEnd.asprintf) =
    Richwasm_lin_lang.Main.compile_str
      ~asprintf:{ asprintf = asprintf.asprintf }
end

let color_asprintf_term_width
    (type a)
    (f : (a, Format.formatter, unit, string) format4) : a =
  kasprintf_cust
    ~cust:(fun fmt ->
      let cols =
        match Linux_ext.get_terminal_size with
        | Ok get_terminal_size ->
            (try get_terminal_size `Controlling |> snd with _ -> 80)
        | _ -> 80
      in
      Ocolor_format.prettify_formatter fmt;
      pp_set_margin fmt cols;
      pp_set_max_indent fmt cols)
    Fn.id f

let run (rw_runtime_path : string) (host_runtime_path : string) =
  let open Alcotest in
  let module SingleRW = Run_rw.SingleRichWasm (struct
    let rw_runtime_path = rw_runtime_path
    let host_runtime_path = host_runtime_path
  end) in
  let module LLSinglee2e = Run_rw.EndToEnd.Make (LL) (SingleRW) in
  let asprintf : EndToEnd.asprintf = { asprintf = color_asprintf_term_width } in
  run "single-file-lin-lang-e2e"
    [
      ( "simple",
        Lin_lang_single.simple_tests
        |> List.map ~f:(fun (name, src, expected) ->
            test_case name `Quick (fun () ->
                let result = LLSinglee2e.run ~asprintf src in
                match result with
                | Ok (res, _) -> (check string) "equal" res expected
                | Error (err, logs) ->
                    IDontRespectLibraryInternals.custom_fail
                      (asprintf.asprintf "Expected %a, but errored:" String.pp
                         expected)
                      (asprintf.asprintf "%a@.@.%a" LLSinglee2e.E2Err.pp err
                         (pp_print_list pp_print_string)
                         logs))) );
    ]
