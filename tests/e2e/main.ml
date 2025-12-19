open! Core
open! Test_support
open! Stdlib.Format
open Richwasm_common.Util
open Richwasm_common.Monads

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

module MM : Run_rw.EndToEnd.SurfaceLang = struct
  open Richwasm_mini_ml

  module CompilerError = struct
    type t = | [@@deriving sexp_of]

    let pp _ _ = ()
  end

  module M = LogResultM (CompilerError) (String)

  let compile_to_richwasm ~(asprintf : EndToEnd.asprintf) src =
    ignore asprintf;
    src
    |> Parse.from_string_exn
    |> Convert.cc_module
    |> Codegen.compile_module
    |> M.ret
end

module RW : Run_rw.EndToEnd.SurfaceLang = struct
  module CompilerError = struct
    type t =
      | Read of Parsexp.Parse_error.t
      | Parse of exn
    [@@deriving sexp_of, variants]

    let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
  end

  module M = LogResultM (CompilerError) (String)

  let compile_to_richwasm ~(asprintf : EndToEnd.asprintf) s =
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

let run (rw_runtime_path : string) (host_runtime_path : string) =
  let open Alcotest in
  let module SingleRW = Run_rw.SingleRichWasm (struct
    let rw_runtime_path = rw_runtime_path
    let host_runtime_path = host_runtime_path
  end) in
  let asprintf : EndToEnd.asprintf = { asprintf = color_asprintf_term_width } in
  let simple_mapper
      (module S : Run_rw.EndToEnd.SurfaceLang)
      (name, src, expected) =
    let module Single = Run_rw.EndToEnd.Make (S) (SingleRW) in
    test_case name `Quick (fun () ->
        let result, logs = Single.run ~asprintf src |> Single.M.run in
        match result with
        | Ok res ->
            if String.equal expected res then
              (check string) "equal" expected res
            else
              IDontRespectLibraryInternals.custom_fail
                (asprintf.asprintf "Expected @{<green>%a@}, but got @{<red>%a@}"
                   String.pp expected String.pp res)
                (asprintf.asprintf "@.%a" (pp_print_list pp_print_string) logs)
        | Error err ->
            IDontRespectLibraryInternals.custom_fail
              (asprintf.asprintf
                 "Expected @{<green>%a@}, but @{<orange>errored@}:" String.pp
                 expected)
              (asprintf.asprintf "%a@.%a" Single.E2Err.pp err
                 (pp_print_list pp_print_string)
                 logs))
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
    ]
