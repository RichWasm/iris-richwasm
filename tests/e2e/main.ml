open! Core
open! Test_support
open! Stdlib.Format
open Richwasm_common.Util
open Richwasm_common.Monads
open Support.Testing
module EndToEnd = Run_rw.EndToEnd

module type SurfaceLang = Run_rw.EndToEnd.SurfaceLang

module LL : SurfaceLang = struct
  module CompilerError = Richwasm_lin_lang.Main.CompileErr

  let compile_to_richwasm ?info ~(asprintf : EndToEnd.asprintf) =
    ignore info;
    Richwasm_lin_lang.Main.compile_str
      ~asprintf:{ asprintf = asprintf.asprintf }
end

module MM : SurfaceLang = struct
  open Richwasm_mini_ml

  module CompilerError = struct
    type t = | [@@deriving sexp_of]

    let pp _ _ = ()
  end

  module M = LogResultM (CompilerError) (String)

  let compile_to_richwasm ?info ~(asprintf : EndToEnd.asprintf) src =
    ignore info;
    ignore asprintf;
    src
    |> Parse.from_string_exn
    |> Convert.cc_module
    |> Codegen.compile_module
    |> M.ret
end

module RW : SurfaceLang = struct
  module CompilerError = struct
    type t =
      | Read of Parsexp.Parse_error.t
      | Parse of exn
    [@@deriving sexp_of, variants]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end

  module M = LogResultM (CompilerError) (String)

  let compile_to_richwasm ?info ~(asprintf : EndToEnd.asprintf) s =
    ignore info;
    let open M in
    let log_pp (type a) name (pp : formatter -> a -> unit) (x : a) : unit t =
      let len = String.length name in
      let fill = '=' in
      tell
        (asprintf.asprintf "@{<blue>%a@} @{<orange>%s@} @{<blue>%a@}@.%a"
           (pp_pad ~fill ~len) false name (pp_pad ~fill ~len) true pp x)
    in

    let* sexp =
      Parsexp.Single.parse_string s
      |> Result.map_error ~f:CompilerError.read
      |> lift_result
    in
    let* () = log_pp "read" Sexp.pp_hum sexp in

    let* syntax =
      try ret @@ Richwasm_common.Syntax.Module.t_of_sexp sexp
      with e -> fail @@ Parse e
    in
    let+ () = log_pp "parse" Richwasm_common.Syntax.Module.pp syntax in
    syntax
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

type run_env = {
  rw_runtime : string;
  host_single : string;
  host_triple : string;
}

let run ({ rw_runtime; host_single; host_triple } : run_env) =
  let open Alcotest in
  let module SingleRW = Run_rw.SingleRichWasm (struct
    let rw_runtime_path = rw_runtime
    let host_runtime_path = host_single
  end) in
  let module TripleRW = Run_rw.TripleRichWasm (struct
    let rw_runtime_path = rw_runtime
    let host_runtime_path = host_triple
  end) in
  let asprintf : EndToEnd.asprintf = { asprintf = color_asprintf_term_width } in
  let check_result (type error) expected (pp : _ -> error -> _) logs :
      (String.t, error) Result.t -> _ = function
    | Ok res ->
        if String.equal expected res then
          (check string) "equal" expected res
        else
          custom_fail
            (asprintf.asprintf "Expected @{<green>%a@}, but got @{<red>%a@}"
               String.pp expected String.pp res)
            (asprintf.asprintf "@.%a" (pp_print_list pp_print_string) logs)
    | Error err ->
        custom_fail
          (asprintf.asprintf "Expected @{<green>%a@}, but @{<orange>errored@}:"
             String.pp expected)
          (asprintf.asprintf "%a@.%a" pp err
             (pp_print_list pp_print_string)
             logs)
  in

  let simple_mapper
      (module S : Run_rw.EndToEnd.SurfaceLang)
      (name, src, expected) =
    let module Single = Run_rw.EndToEnd.Make1 (S) (SingleRW) in
    test_case name `Quick (fun () ->
        let result, logs = Single.run ~asprintf src |> Single.M.run in
        check_result expected Single.E2Err.pp logs result)
  in
  run "e2e"
    [
      ( "lin-lang-single",
        Lin_lang_single.simple_tests |> List.map ~f:(simple_mapper (module LL))
      );
      ( "mini-ml-single",
        Mini_ml_single.simple_tests |> List.map ~f:(simple_mapper (module MM))
      );
      ( "richwasm-single",
        Richwasm_single.simple_tests |> List.map ~f:(simple_mapper (module RW))
      );
      ( "interop-glue",
        [
          test_case "numeric interop" `Quick (fun () ->
              let module Err = struct
                type t =
                  | Module1 of LL.CompilerError.t
                  | Module2 of RW.CompilerError.t
                  | Module3 of MM.CompilerError.t
                  | BadInfo of String.t Option.t
                [@@deriving sexp_of, variants]

                let pp ff = function
                  | Module1 err ->
                      fprintf ff "Module1: %a" LL.CompilerError.pp err
                  | Module2 err ->
                      fprintf ff "Module2: %a" RW.CompilerError.pp err
                  | Module3 err ->
                      fprintf ff "Module3: %a" MM.CompilerError.pp err
                  | BadInfo err ->
                      fprintf ff "BadInfo: %a"
                        (pp_print_option pp_print_string)
                        err
              end in
              let module SL : SurfaceLang = struct
                module CompilerError = Err

                let compile_to_richwasm
                    ?info
                    ~(asprintf : EndToEnd.asprintf)
                    src =
                  let module M = LogResultM (CompilerError) (String) in
                  let open M in
                  match info with
                  | Some "m1" ->
                      LL.compile_to_richwasm ~asprintf src
                      |> map_error_into CompilerError.module1
                  | Some "m2" ->
                      RW.compile_to_richwasm ~asprintf src
                      |> map_error_into CompilerError.module2
                  | Some "m3" ->
                      MM.compile_to_richwasm ~asprintf src
                      |> map_error_into CompilerError.module3
                  | _ -> fail (CompilerError.badinfo info)
              end in
              let module Triple = Run_rw.EndToEnd.Make3 (SL) (TripleRW) in
              let module1 =
                {|
                  (export fun add1 (i : int) : int .
                    (i + 1))
                |}
              in
              let module2 =
                {|
                  ((imports ((FunctionType () ((Num (Int I32))) ((Num (Int I32))))))
                   (functions
                    (((typ (FunctionType () (I31) ((Num (Int I32)))))
                      (locals ())
                      (body
                       ((LocalGet 0 Copy)
                        Untag
                        ;; TODO: call with closure
                        (Call 0 ())
                        Tag
                        )))))
                   (table ()) (exports (((name add1_wrapped) (desc (Func 0))))))
                |}
              in
              let module3 =
                {|
                  (import (add1 : (() int -> int)))

                  (app add1 () 1)
                |}
              in
              (* let result, logs =
                Triple.run3 ~asprintf module1 module2 module3 |> Triple.M.run
              in
              check_result "2" Triple.E2Err.pp logs result *)
              skip ());
        ] );
    ]
