open! Core
open! Test_support
open! Stdlib.Format

module LL = struct
  module CompilerError = Richwasm_lin_lang.Main.CompileErr

  let compile_to_richwasm = Richwasm_lin_lang.Main.compile_str
end

let run (rw_runtime_path : string) (host_runtime_path : string) =
  let open Alcotest in
  let module SingleRW = Run_rw.SingleRichWasm (struct
    let rw_runtime_path = rw_runtime_path
    let host_runtime_path = host_runtime_path
  end) in
  let module LLSinglee2e = Run_rw.EndToEnd.Make (LL) (SingleRW) in
  run "single-file-lin-lang-e2e"
    [
      ( "simple",
        Lin_lang_single.simple_tests
        |> List.map ~f:(fun (name, src, expected) ->
            test_case name `Quick (fun () ->
                let result = LLSinglee2e.run src in
                match result with
                | Ok (res, _) -> (check string) "equal" res expected
                | Error (err, logs) ->
                    fail
                      (asprintf "%a@.@.%a" LLSinglee2e.E2Err.pp err
                         (pp_print_list pp_print_string)
                         logs))) );
    ]
