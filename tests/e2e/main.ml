open! Core
open! Test_support
open! Stdlib.Format
open Richwasm_common.Util
open Richwasm_common.Monads
open Richwasm_support
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
  module CompilerError = Richwasm_mini_ml.Main.CompileErr

  let compile_to_richwasm ?info ~(asprintf : EndToEnd.asprintf) =
    ignore info;
    Richwasm_mini_ml.Main.compile_str ~asprintf:{ asprintf = asprintf.asprintf }
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
          test_case "numeric interop (ll -> ml)" `Quick (fun () ->
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
                (* lin-lang *)
                {|
                  (export fun add1 (i : int) : int .
                    (i + 1))
                |}
              in
              let module2 =
                (* rwasm *)
                {|
                  ;; Glue module: adapts mini-ml's closure-style `add1` import
                  ;; to lin-lang's `add1` (m1). mini-ml calls with a GC closure
                  ;; struct (env, i31); lin-lang expects an unboxed (env, i32)
                  ;; product with an MM-allocated environment.
                  ((imports
                    ((FunctionType ()
                      ((Prod ((Ref (Base MM) Mut (Ser (Prod ()))) (Num (Int I32)))))
                      ((Num (Int I32))))))
                   (functions
                    (((typ
                       (FunctionType ()
                        ((Ref (Base GC) Imm
                          (Struct
                           ((Ser (Ref (Base GC) Imm (Struct ()))) (Ser I31)))))
                        (I31)))
                      (locals ((Atom Ptr)))
                      (body
                       ((LocalGet 0 Move)
                        ;; pull the i31 argument out of the closure struct
                        (Load (Path (1)) Follow)
                        (LocalSet 1)
                        Drop
                        ;; build lin-lang's (env, i32) argument
                        (Group 0)
                        (New MM Mut)
                        (LocalGet 1 Move)
                        Untag
                        (Group 2)
                        (Call 0 ())
                        Tag)))))
                   (table ())
                   (exports (((name add1_wrapped) (desc (Func 1))))))
                |}
              in
              let module3 =
                (* mini-ml *)
                {|
                  (import (add1 : (() int -> int)))

                  (app add1 () 5)
                |}
              in
              let result, logs =
                Triple.run3 ~asprintf ~links:("add1", "add1_wrapped") module1
                  module2 module3
                |> Triple.M.run
              in
              (* add1 1 = 2; the result is an i31, whose raw wasm value is the
                 tagged form 2 * 2 = 4 *)
              check_result "12" Triple.E2Err.pp logs result);
          (* --------------------------------------------------- *)
          test_case "numeric interop (ml -> ll)" `Quick (fun () ->
              let module Err = struct
                type t =
                  | Module1 of MM.CompilerError.t
                  | Module2 of RW.CompilerError.t
                  | Module3 of LL.CompilerError.t
                  | BadInfo of String.t Option.t
                [@@deriving sexp_of, variants]

                let pp ff = function
                  | Module1 err ->
                      fprintf ff "Module1: %a" MM.CompilerError.pp err
                  | Module2 err ->
                      fprintf ff "Module2: %a" RW.CompilerError.pp err
                  | Module3 err ->
                      fprintf ff "Module3: %a" LL.CompilerError.pp err
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
                      MM.compile_to_richwasm ~asprintf src
                      |> map_error_into CompilerError.module1
                  | Some "m2" ->
                      RW.compile_to_richwasm ~asprintf src
                      |> map_error_into CompilerError.module2
                  | Some "m3" ->
                      LL.compile_to_richwasm ~asprintf src
                      |> map_error_into CompilerError.module3
                  | _ -> fail (CompilerError.badinfo info)
              end in
              let module Triple = Run_rw.EndToEnd.Make3 (SL) (TripleRW) in
              let module1 =
                (* mini-ml *)
                {|
                  (export (add3 : (() int -> int))
                    (fun () (i : int) : int
                      (op + i 3)))
                |}
              in
              let module2 =
                (* rwasm *)
                {|
                  ;; Glue module: adapts lin-lang's closure-style `add3` import
                  ;; to mini-ml's `add3` (m1). lin-lang calls with a MM closure
                  ;; struct (env, i32); mini-ml expects an boxed (env, i31)
                  ;; product with an GC-allocated environment.
                  ((imports
                    ((FunctionType ()
                      ((Ref (Base GC) Imm
                        (Struct
                           ((Ser (Ref (Base GC) Imm (Struct ()))) (Ser I31)))))
                      (I31))))
                   (functions
                    (((typ
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) Mut (Ser (Prod ()))) (Num (Int I32)))))
                        ((Num (Int I32)))))
                      (locals ((Atom I32)))
                      (body
                       ((LocalGet 0 Move)
                        Ungroup
                        (LocalSet 1) ;; i32
                        Drop ;; env
                        ;; build mini-ml's (env, i32) argument
                        (Group 0)
                        (New GC Imm)
                        (Cast (Ref (Base GC) Imm (Struct ())))
                        (LocalGet 1 Move)
                        Tag ;; can error!!!
                        (Group 2) ;; ((), i31)
                        (New GC Imm)
                        (Cast (Ref (Base GC) Imm (Struct ((Ser (Ref (Base GC) Imm (Struct ()))) (Ser I31)))))
                        (Call 0 ())
                        Untag)))))
                   (table ())
                   (exports (((name add3_wrapped) (desc (Func 1))))))
                |}
              in
              let module3 =
                (* lin-lang *)
                {|
                  (import (int -> int) as add3)

                  (app add3 4)
                |}
              in
              let result, logs =
                Triple.run3 ~asprintf ~links:("add3", "add3_wrapped") module1
                  module2 module3
                |> Triple.M.run
              in
              check_result "7" Triple.E2Err.pp logs result);
          (*----------------------------------------------------------*)
          test_case "add1tuple (ll -> ml)" `Quick (fun () ->
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
                (* lin-lang *)
                {|
                 (export fun add1tuple (x : (int ⊗ int)) : (int ⊗ int) .
                       (split (a : int) (b : int) = x in
                       ((a + 1), (b + 1))))
                |}
              in
              let module2 =
                (* rwasm *)
                {|
                  ;; Glue module: adapts mini-ml's closure-style `add1` import
                  ;; to lin-lang's `add1` (m1). mini-ml calls with a GC closure
                  ;; struct (env, i31); lin-lang expects an unboxed (env, i32)
                  ;; product with an MM-allocated environment.
                  ((imports                          ;; note: this is mini ll add1tuple type
                    ((FunctionType ()
                      ((Prod ((Ref (Base MM) Mut (Ser (Prod ()))) (Prod ((Num (Int I32)) (Num (Int I32)) ) ))))
                      ( (Prod ( (Num (Int I32)) (Num (Int I32)) ) )  ))))
                   (functions
                    (((typ
                       (FunctionType ()             ;; note: this is mini ml add1tuplewrapped type, I THINK (can't get ml's add1tuple to compile yet)
                        ((Ref (Base GC) Imm
                          (Struct
                             ((Ser (Ref (Base GC) Imm (Struct ())))
                              (Ser (Ref (Base GC) Imm (Struct ((Ser I31) (Ser I31)))))
                          ))))
                        ((Ref (Base GC) Imm (Struct ((Ser I31) (Ser I31)) ) ))))
                      (locals ((Atom Ptr) (Atom Ptr) (Atom Ptr) (Atom I32)))
                      (body
                       ((LocalGet 0 Move)
                        ;; pull the ref [i31, i31] argument out of the closure struct
                        (Load (Path (1)) Follow)
                        (LocalSet 1)
                        Drop  ;; drop the empty everything else
                        ;; build lin-lang's (env, i32) argument
                        (Group 0)
                        (New MM Mut) ;; this is now env

                        (LocalGet 1 Move) ;; now env, ref gc [ser i31, ser i31] is on the stack, need to cast
                        (Load (Path (1)) Follow) ;; env, ref gc [ser i31(5) ser i31(6)], i31(6)
                        (LocalSet 2);; env, ref gc [ser i31(5), i31(6)]
                        (Load (Path (0)) Follow) ;; env, ref gc [..], i31(5)
                        (LocalSet 3) ;; env, ref gc
                        Drop ;; env
                        (LocalGet 3 Move) ;; env, i31(5)
                        Untag ;; env, i32(5)
                        (LocalGet 2 Move) ;; env, i32(5), i31(6)
                        Untag ;; env, i32(5), i32(6)
                        (Group 2) ;; env, [i32(5), i32(6)]
                        (Group 2) ;; [env, [i32(5), i32(6)]]
                        (Call 0 ()) ;; now [i32(6), i32(7)] hopefully. need ref gc of i31s
                        Ungroup ;; i32(6), i32(7)
                        (LocalSet 4) ;; i32(6)
                        Tag ;;i31(6)
                        (LocalGet 4 Move) ;; i31(6), i32(7)
                        Tag ;; i31(6) i31(7)
                        (Group 2) ;; [i31,i31]
                        (New GC Imm) ;; ref gc ..
                        (Cast (Ref (Base GC) Imm (Struct ((Ser I31) (Ser I31))))) ;; cast into proper form
                    )))))
                   (table ())
                   (exports (((name add1tuple_wrapped) (desc (Func 1))))))
                |}
              in
              let module3 =
                (* mini-ml *)
                {|
                  (import (add1tuple : (() ( * int int ) -> ( * int int))))

                  (app add1tuple () (tup 5 6))
                |}
              in
              let result, logs =
                Triple.run3 ~asprintf ~links:("add1", "add1_wrapped") module1
                  module2 module3
                |> Triple.M.run
              in
              (* add1 1 = 2; the result is an i31, whose raw wasm value is the
                 tagged form 2 * 2 = 4 *)
              check_result "12" Triple.E2Err.pp logs result);
        ] );
    ]
