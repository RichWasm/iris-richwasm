open! Core
open! Stdlib.Format
open! Test_support
open Richwasm_support.Pipeline
module AnnRichWasm = Richwasm_common.Annotated_syntax

include Test_runner.MultiOutputter.Make (struct
  let margin = 120
  let max_indent = margin

  open Richwasm_mini_ml

  type syntax = Syntax.Source.Module.t
  type text = string
  type res = AnnRichWasm.Module.t

  let syntax_pipeline x = ml_pipeline x |> elab_pipeline
  let string_pipeline s = ml_str_pipeline s |> elab_pipeline
  let examples = Test_examples.Mini_ml.all
  let pp = AnnRichWasm.Module.pp
  let pp_raw = AnnRichWasm.Module.pp_sexp
end)

let%expect_test "examples" =
  output_examples ();
  [%expect
    {xxx|
    -----------one-----------
    (module
      (func ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs)))
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------tuple-----------
    (module
      (func
          ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
          (ref (val ptr gcrefs) (base gc) imm
            (struct (mem (prod (rep ptr) (rep ptr) (rep ptr) (rep ptr)) norefs)
              (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
              (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        num_const 2 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        num_const 3 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        num_const 4 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        group ;; [(i31 (val ptr norefs)) (i31 (val ptr norefs)) (i31 (val ptr norefs)) (i31 (val ptr norefs))] ->
                 [(prod (val (prod ptr ptr ptr ptr) norefs) (i31 (val ptr norefs))
                    (i31 (val ptr norefs)) (i31 (val ptr norefs)) (i31 (val ptr norefs)))]
        new ;; [(prod (val (prod ptr ptr ptr ptr) norefs) (i31 (val ptr norefs))
                  (i31 (val ptr norefs)) (i31 (val ptr norefs)) (i31 (val ptr norefs)))]
               ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr ptr ptr ptr)) norefs)
                    (prod (val (prod ptr ptr ptr ptr) norefs) (i31 (val ptr norefs))
                      (i31 (val ptr norefs)) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr ptr ptr ptr)) norefs)
                     (prod (val (prod ptr ptr ptr ptr) norefs) (i31 (val ptr norefs))
                       (i31 (val ptr norefs)) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr) (rep ptr) (rep ptr)) norefs)
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------tuple_nested-----------
    (module
      (func
          ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
          (ref (val ptr gcrefs) (base gc) imm
            (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
              (ser (mem (rep ptr) gcrefs)
                (ref (val ptr gcrefs) (base gc) imm
                  (struct (mem (prod (rep ptr) (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                    (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))
              (ser (mem (rep ptr) gcrefs)
                (ref (val ptr gcrefs) (base gc) imm
                  (struct (mem (prod (rep ptr) (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                    (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        num_const 2 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        group ;; [(i31 (val ptr norefs)) (i31 (val ptr norefs))] ->
                 [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))]
        new ;; [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))] ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr ptr)) norefs)
                    (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr ptr)) norefs)
                     (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        num_const 3 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        num_const 4 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        group ;; [(i31 (val ptr norefs)) (i31 (val ptr norefs))] ->
                 [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))]
        new ;; [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))] ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr ptr)) norefs)
                    (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr ptr)) norefs)
                     (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        group ;; [(ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr) (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                      (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                  (ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr) (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                      (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                 ->
                 [(prod (val (prod ptr ptr) gcrefs)
                    (ref (val ptr gcrefs) (base gc) imm
                      (struct (mem (prod (rep ptr) (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                        (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                    (ref (val ptr gcrefs) (base gc) imm
                      (struct (mem (prod (rep ptr) (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                        (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
        new ;; [(prod (val (prod ptr ptr) gcrefs)
                  (ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr) (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                      (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                  (ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr) (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                      (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
               ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr ptr)) gcrefs)
                    (prod (val (prod ptr ptr) gcrefs)
                      (ref (val ptr gcrefs) (base gc) imm
                        (struct (mem (prod (rep ptr) (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                          (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                      (ref (val ptr gcrefs) (base gc) imm
                        (struct (mem (prod (rep ptr) (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                          (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr ptr)) gcrefs)
                     (prod (val (prod ptr ptr) gcrefs)
                       (ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr) (rep ptr)) norefs)
                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                       (ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr) (rep ptr)) norefs)
                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs)
                       (ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr) (rep ptr)) norefs)
                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))
                     (ser (mem (rep ptr) gcrefs)
                       (ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr) (rep ptr)) norefs)
                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------tuple_project-----------
    (module
      (func ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs))) (local ptr)
        num_const 42 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        num_const 7 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        group ;; [(i31 (val ptr norefs)) (i31 (val ptr norefs))] ->
                 [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))]
        new ;; [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))] ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr ptr)) norefs)
                    (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr ptr)) norefs)
                     (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        load (path 1) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep ptr)) norefs)
                                   (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                                   (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                              ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep ptr)) norefs)
                                   (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                                   (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                               (i31 (val ptr norefs))]
        local.set 1 ;; [(i31 (val ptr norefs))] -> []
        drop ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                -> []
        local.get move 1 ;; [] -> [(i31 (val ptr norefs))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------utuple-----------
    (module
      (func
          ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
          (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        num_const 2 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        group ;; [(i31 (val ptr norefs)) (i31 (val ptr norefs))] ->
                 [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------utuple_split-----------
    (module
      (func ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs))) (local ptr ptr)
        num_const 42 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        num_const 7 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        group ;; [(i31 (val ptr norefs)) (i31 (val ptr norefs))] ->
                 [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))]
        ungroup ;; [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))] ->
                   [(i31 (val ptr norefs)) (i31 (val ptr norefs))]
        local.set 2 ;; [(i31 (val ptr norefs))] -> []
        local.set 1 ;; [(i31 (val ptr norefs))] -> []
        local.get move 2 ;; [] -> [(i31 (val ptr norefs))]
        copy ;; [(i31 (val ptr norefs))] -> [(i31 (val ptr norefs)) (i31 (val ptr norefs))]
        local.set 2 ;; [(i31 (val ptr norefs))] -> []
        local.get move 1 ;; [] -> [(i31 (val ptr norefs))]
        drop ;; [(i31 (val ptr norefs))] -> []
        local.get move 2 ;; [] -> [(i31 (val ptr norefs))]
        drop ;; [(i31 (val ptr norefs))] -> []
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------utuple_let-----------
    (module
      (func ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs))) (local
          (prod ptr ptr) ptr ptr)
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        num_const 2 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        group ;; [(i31 (val ptr norefs)) (i31 (val ptr norefs))] ->
                 [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))]
        local.set 1 ;; [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))] -> []
        local.get move 1 ;; [] -> [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))]
        copy ;; [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))] ->
                [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))
                 (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))]
        local.set 1 ;; [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))] -> []
        ungroup ;; [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))] ->
                   [(i31 (val ptr norefs)) (i31 (val ptr norefs))]
        local.set 3 ;; [(i31 (val ptr norefs))] -> []
        local.set 2 ;; [(i31 (val ptr norefs))] -> []
        local.get move 2 ;; [] -> [(i31 (val ptr norefs))]
        copy ;; [(i31 (val ptr norefs))] -> [(i31 (val ptr norefs)) (i31 (val ptr norefs))]
        local.set 2 ;; [(i31 (val ptr norefs))] -> []
        local.get move 2 ;; [] -> [(i31 (val ptr norefs))]
        drop ;; [(i31 (val ptr norefs))] -> []
        local.get move 3 ;; [] -> [(i31 (val ptr norefs))]
        drop ;; [(i31 (val ptr norefs))] -> []
        local.get move 1 ;; [] -> [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))]
        drop ;; [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))] -> []
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------utuple_in_tuple-----------
    (module
      (func
          ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
          (ref (val ptr gcrefs) (base gc) imm
            (struct (mem (prod (rep (prod ptr ptr)) (rep ptr)) norefs)
              (ser (mem (rep (prod ptr ptr)) norefs)
                (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))
              (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        num_const 2 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        group ;; [(i31 (val ptr norefs)) (i31 (val ptr norefs))] ->
                 [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))]
        num_const 3 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        group ;; [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) (i31 (val ptr norefs))]
                 ->
                 [(prod (val (prod (prod ptr ptr) ptr) norefs)
                    (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))
                    (i31 (val ptr norefs)))]
        new ;; [(prod (val (prod (prod ptr ptr) ptr) norefs)
                  (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))
                  (i31 (val ptr norefs)))]
               ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod (prod ptr ptr) ptr)) norefs)
                    (prod (val (prod (prod ptr ptr) ptr) norefs)
                      (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))
                      (i31 (val ptr norefs)))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod (prod ptr ptr) ptr)) norefs)
                     (prod (val (prod (prod ptr ptr) ptr) norefs)
                       (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))
                       (i31 (val ptr norefs)))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep (prod ptr ptr)) (rep ptr)) norefs)
                     (ser (mem (rep (prod ptr ptr)) norefs)
                       (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------utuple_of_tuple-----------
    (module
      (func
          ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
          (prod (val (prod ptr ptr) gcrefs)
            (ref (val ptr gcrefs) (base gc) imm
              (struct (mem (prod (rep ptr) (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
            (i31 (val ptr norefs))))
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        num_const 2 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        group ;; [(i31 (val ptr norefs)) (i31 (val ptr norefs))] ->
                 [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))]
        new ;; [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))] ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr ptr)) norefs)
                    (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr ptr)) norefs)
                     (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        num_const 3 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        group ;; [(ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr) (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                      (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                  (i31 (val ptr norefs))]
                 ->
                 [(prod (val (prod ptr ptr) gcrefs)
                    (ref (val ptr gcrefs) (base gc) imm
                      (struct (mem (prod (rep ptr) (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                        (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                    (i31 (val ptr norefs)))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------utuple_ref-----------
    (module
      (func
          ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
          (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))) (local
          (prod ptr ptr))
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        num_const 2 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        group ;; [(i31 (val ptr norefs)) (i31 (val ptr norefs))] ->
                 [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))]
        new ;; [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))] ->
               [(ref (val ptr gcrefs) (base gc) mut
                  (ser (mem (rep (prod ptr ptr)) norefs)
                    (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
        load (path) copy ;; [(ref (val ptr gcrefs) (base gc) mut
                               (ser (mem (rep (prod ptr ptr)) norefs)
                                 (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
                            ->
                            [(ref (val ptr gcrefs) (base gc) mut
                               (ser (mem (rep (prod ptr ptr)) norefs)
                                 (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))
                             (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))]
        local.set 1 ;; [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))] -> []
        drop ;; [(ref (val ptr gcrefs) (base gc) mut
                   (ser (mem (rep (prod ptr ptr)) norefs)
                     (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
                -> []
        local.get move 1 ;; [] -> [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------utuple_fn-----------
    (module
      (func
          ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
          (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
          (i31 (val ptr norefs))) (local ptr ptr)
        local.get move 1 ;; [] -> [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))]
        copy ;; [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))] ->
                [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))
                 (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))]
        local.set 1 ;; [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))] -> []
        ungroup ;; [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))] ->
                   [(i31 (val ptr norefs)) (i31 (val ptr norefs))]
        local.set 3 ;; [(i31 (val ptr norefs))] -> []
        local.set 2 ;; [(i31 (val ptr norefs))] -> []
        local.get move 2 ;; [] -> [(i31 (val ptr norefs))]
        copy ;; [(i31 (val ptr norefs))] -> [(i31 (val ptr norefs)) (i31 (val ptr norefs))]
        local.set 2 ;; [(i31 (val ptr norefs))] -> []
        local.get move 2 ;; [] -> [(i31 (val ptr norefs))]
        drop ;; [(i31 (val ptr norefs))] -> []
        local.get move 3 ;; [] -> [(i31 (val ptr norefs))]
        drop ;; [(i31 (val ptr norefs))] -> []
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> []
        local.get move 1 ;; [] -> [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))]
        drop ;; [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))] -> [])
      (func ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs))) (local ptr ptr
          ptr ptr ptr)
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                        (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                        (i31 (val ptr norefs))))]
        group ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                    (i31 (val ptr norefs))))]
                 ->
                 [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (coderef (val i32 norefs)
                      ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                      (i31 (val ptr norefs)))))]
        new ;; [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                    (i31 (val ptr norefs)))))]
               ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr i32)) gcrefs)
                    (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                        (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                        (i31 (val ptr norefs)))))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr i32)) gcrefs)
                     (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                         (i31 (val ptr norefs)))))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                         (i31 (val ptr norefs)))))))]
        pack ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                         (i31 (val ptr norefs)))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                           (i31 (val ptr norefs))))))))]
        unpack (localfx [0 => (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
                 [1 => (plug (val (prod i32) norefs) (prod i32))] [2 => (plug (val (prod i32) norefs) (prod i32))]
                 [3 => (plug (val (prod i32) norefs) (prod i32))] [4 => (plug (val (prod i32) norefs) (prod i32))]
                 [5 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))
                                  -> (i31 (val ptr norefs)))))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0)
                                       (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                                       (i31 (val ptr norefs)))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                           (i31 (val ptr norefs)))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                           (i31 (val ptr norefs)))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                           (i31 (val ptr norefs)))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))
                                  -> (i31 (val ptr norefs)))))))]
                         -> []
          load (path 0) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0)
                                         (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))
                                         -> (i31 (val ptr norefs)))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0)
                                         (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))
                                         -> (i31 (val ptr norefs)))))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                           (i31 (val ptr norefs)))))))]
                  -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0)
                                       (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                                       (i31 (val ptr norefs)))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                           (i31 (val ptr norefs)))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                           (i31 (val ptr norefs)))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                           (i31 (val ptr norefs)))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))
                                  -> (i31 (val ptr norefs)))))))]
                         -> []
          load (path 1) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0)
                                         (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))
                                         -> (i31 (val ptr norefs)))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0)
                                         (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))
                                         -> (i31 (val ptr norefs)))))))
                                 (coderef (val i32 norefs)
                                   ((var 0)
                                   (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                                   (i31 (val ptr norefs))))]
          local.set 4 ;; [(coderef (val i32 norefs)
                            ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                            (i31 (val ptr norefs))))]
                         -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                           (i31 (val ptr norefs)))))))]
                  -> []
          local.get move 4 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))
                                 -> (i31 (val ptr norefs))))]
          local.set 5 ;; [(coderef (val i32 norefs)
                            ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                            (i31 (val ptr norefs))))]
                         -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          num_const 5 ;; [] -> [(num (val i32 norefs) i32)]
          tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
          num_const 6 ;; [] -> [(num (val i32 norefs) i32)]
          tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
          group ;; [(i31 (val ptr norefs)) (i31 (val ptr norefs))] ->
                   [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))
                                 -> (i31 (val ptr norefs))))]
          copy ;; [(coderef (val i32 norefs)
                     ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                     (i31 (val ptr norefs))))]
                  ->
                  [(coderef (val i32 norefs)
                     ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                     (i31 (val ptr norefs))))
                   (coderef (val i32 norefs)
                     ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                     (i31 (val ptr norefs))))]
          local.set 5 ;; [(coderef (val i32 norefs)
                            ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                            (i31 (val ptr norefs))))]
                         -> []
          call_indirect ;; [(var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))
                            (coderef (val i32 norefs)
                              ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                              (i31 (val ptr norefs))))]
                           -> [(i31 (val ptr norefs))]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))
                                 -> (i31 (val ptr norefs))))]
          drop ;; [(coderef (val i32 norefs)
                     ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                     (i31 (val ptr norefs))))]
                  -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0)
                                       (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                                       (i31 (val ptr norefs)))))))]
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                           (i31 (val ptr norefs)))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                      (ser (mem (rep i32) norefs)
                        (coderef (val i32 norefs)
                          ((var 0) (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))) ->
                          (i31 (val ptr norefs))))))))]
               -> [(i31 (val ptr norefs))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0 1)
      (export "_start" (func 1)))
    -----------utuple_ret-----------
    (module
      (func
          ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
          (i31 (val ptr norefs)) -> (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))
        local.get move 1 ;; [] -> [(i31 (val ptr norefs))]
        copy ;; [(i31 (val ptr norefs))] -> [(i31 (val ptr norefs)) (i31 (val ptr norefs))]
        local.set 1 ;; [(i31 (val ptr norefs))] -> []
        num_const 9 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        group ;; [(i31 (val ptr norefs)) (i31 (val ptr norefs))] ->
                 [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> []
        local.get move 1 ;; [] -> [(i31 (val ptr norefs))]
        drop ;; [(i31 (val ptr norefs))] -> [])
      (func ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs))) (local ptr ptr
          ptr ptr ptr ptr ptr)
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                        (i31 (val ptr norefs)) ->
                        (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
        group ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (i31 (val ptr norefs)) ->
                    (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
                 ->
                 [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (coderef (val i32 norefs)
                      ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (i31 (val ptr norefs)) ->
                      (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))]
        new ;; [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (i31 (val ptr norefs)) ->
                    (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))]
               ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr i32)) gcrefs)
                    (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                        (i31 (val ptr norefs)) ->
                        (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr i32)) gcrefs)
                     (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (i31 (val ptr norefs)) ->
                         (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (i31 (val ptr norefs)) ->
                         (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))))]
        pack ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (i31 (val ptr norefs)) ->
                         (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))))))]
        unpack (localfx [0 => (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
                 [1 => (plug (val (prod i32) norefs) (prod i32))] [2 => (plug (val (prod i32) norefs) (prod i32))]
                 [3 => (plug (val (prod i32) norefs) (prod i32))] [4 => (plug (val (prod i32) norefs) (prod i32))]
                 [5 => (plug (val (prod i32) norefs) (prod i32))] [6 => (plug (val (prod i32) norefs) (prod i32))]
                 [7 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (i31 (val ptr norefs)) ->
                                  (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (i31 (val ptr norefs)) ->
                                       (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (i31 (val ptr norefs)) ->
                                  (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))))]
                         -> []
          load (path 0) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))))]
                  -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (i31 (val ptr norefs)) ->
                                       (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (i31 (val ptr norefs)) ->
                                  (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))))]
                         -> []
          load (path 1) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))))
                                 (coderef (val i32 norefs)
                                   ((var 0) (i31 (val ptr norefs)) ->
                                   (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
          local.set 4 ;; [(coderef (val i32 norefs)
                            ((var 0) (i31 (val ptr norefs)) ->
                            (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
                         -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))))]
                  -> []
          local.get move 4 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (i31 (val ptr norefs)) ->
                                 (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
          local.set 5 ;; [(coderef (val i32 norefs)
                            ((var 0) (i31 (val ptr norefs)) ->
                            (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
                         -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          num_const 4 ;; [] -> [(num (val i32 norefs) i32)]
          tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (i31 (val ptr norefs)) ->
                                 (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
          copy ;; [(coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
                  ->
                  [(coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))
                   (coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
          local.set 5 ;; [(coderef (val i32 norefs)
                            ((var 0) (i31 (val ptr norefs)) ->
                            (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
                         -> []
          call_indirect ;; [(var 0) (i31 (val ptr norefs))
                            (coderef (val i32 norefs)
                              ((var 0) (i31 (val ptr norefs)) ->
                              (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
                           -> [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (i31 (val ptr norefs)) ->
                                 (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
          drop ;; [(coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))]
                  -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (i31 (val ptr norefs)) ->
                                       (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))))]
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs))))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                      (ser (mem (rep i32) norefs)
                        (coderef (val i32 norefs)
                          ((var 0) (i31 (val ptr norefs)) ->
                          (prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))))))))]
               -> [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))]
        ungroup ;; [(prod (val (prod ptr ptr) norefs) (i31 (val ptr norefs)) (i31 (val ptr norefs)))] ->
                   [(i31 (val ptr norefs)) (i31 (val ptr norefs))]
        local.set 7 ;; [(i31 (val ptr norefs))] -> []
        local.set 6 ;; [(i31 (val ptr norefs))] -> []
        local.get move 7 ;; [] -> [(i31 (val ptr norefs))]
        copy ;; [(i31 (val ptr norefs))] -> [(i31 (val ptr norefs)) (i31 (val ptr norefs))]
        local.set 7 ;; [(i31 (val ptr norefs))] -> []
        local.get move 6 ;; [] -> [(i31 (val ptr norefs))]
        drop ;; [(i31 (val ptr norefs))] -> []
        local.get move 7 ;; [] -> [(i31 (val ptr norefs))]
        drop ;; [(i31 (val ptr norefs))] -> []
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0 1)
      (export "_start" (func 1)))
    -----------lin_make-----------
    (module
      (import ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
              (i31 (val ptr norefs)) ->
              (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))
      (func
          ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
          (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))) (local ptr ptr ptr ptr
          ptr)
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                        (i31 (val ptr norefs)) ->
                        (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
        group ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (i31 (val ptr norefs)) ->
                    (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                 ->
                 [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (coderef (val i32 norefs)
                      ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (i31 (val ptr norefs)) ->
                      (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))]
        new ;; [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (i31 (val ptr norefs)) ->
                    (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))]
               ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr i32)) gcrefs)
                    (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                        (i31 (val ptr norefs)) ->
                        (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr i32)) gcrefs)
                     (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (i31 (val ptr norefs)) ->
                         (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (i31 (val ptr norefs)) ->
                         (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
        pack ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (i31 (val ptr norefs)) ->
                         (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))))))]
        unpack (localfx [0 => (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
                 [1 => (plug (val (prod i32) norefs) (prod i32))] [2 => (plug (val (prod i32) norefs) (prod i32))]
                 [3 => (plug (val (prod i32) norefs) (prod i32))] [4 => (plug (val (prod i32) norefs) (prod i32))]
                 [5 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (i31 (val ptr norefs)) ->
                                  (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (i31 (val ptr norefs)) ->
                                       (ref (val ptr anyrefs) (base mm) mut
                                         (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (i31 (val ptr norefs)) ->
                                  (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                         -> []
          load (path 0) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (ref (val ptr anyrefs) (base mm) mut
                                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (ref (val ptr anyrefs) (base mm) mut
                                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (i31 (val ptr norefs)) ->
                                       (ref (val ptr anyrefs) (base mm) mut
                                         (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (i31 (val ptr norefs)) ->
                                  (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                         -> []
          load (path 1) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (ref (val ptr anyrefs) (base mm) mut
                                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (ref (val ptr anyrefs) (base mm) mut
                                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))
                                 (coderef (val i32 norefs)
                                   ((var 0) (i31 (val ptr norefs)) ->
                                   (ref (val ptr anyrefs) (base mm) mut
                                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          local.set 4 ;; [(coderef (val i32 norefs)
                            ((var 0) (i31 (val ptr norefs)) ->
                            (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                         -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  -> []
          local.get move 4 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (i31 (val ptr norefs)) ->
                                 (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          local.set 5 ;; [(coderef (val i32 norefs)
                            ((var 0) (i31 (val ptr norefs)) ->
                            (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                         -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          num_const 5 ;; [] -> [(num (val i32 norefs) i32)]
          tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (i31 (val ptr norefs)) ->
                                 (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          copy ;; [(coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                  ->
                  [(coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))
                   (coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          local.set 5 ;; [(coderef (val i32 norefs)
                            ((var 0) (i31 (val ptr norefs)) ->
                            (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                         -> []
          call_indirect ;; [(var 0) (i31 (val ptr norefs))
                            (coderef (val i32 norefs)
                              ((var 0) (i31 (val ptr norefs)) ->
                              (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                           -> [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (i31 (val ptr norefs)) ->
                                 (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          drop ;; [(coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                  -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (i31 (val ptr norefs)) ->
                                       (ref (val ptr anyrefs) (base mm) mut
                                         (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                      (ser (mem (rep i32) norefs)
                        (coderef (val i32 norefs)
                          ((var 0) (i31 (val ptr norefs)) ->
                          (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))))))]
               -> [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0 1)
      (export "_start" (func 1)))
    -----------lin_deref-----------
    (module
      (import ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
              (i31 (val ptr norefs)) ->
              (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))
      (func
          ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
          (prod (val (prod ptr ptr) anyrefs)
            (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))
            (i31 (val ptr norefs))))
          (local ptr ptr ptr ptr ptr)
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                        (i31 (val ptr norefs)) ->
                        (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
        group ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (i31 (val ptr norefs)) ->
                    (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                 ->
                 [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (coderef (val i32 norefs)
                      ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (i31 (val ptr norefs)) ->
                      (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))]
        new ;; [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (i31 (val ptr norefs)) ->
                    (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))]
               ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr i32)) gcrefs)
                    (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                        (i31 (val ptr norefs)) ->
                        (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr i32)) gcrefs)
                     (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (i31 (val ptr norefs)) ->
                         (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (i31 (val ptr norefs)) ->
                         (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
        pack ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (i31 (val ptr norefs)) ->
                         (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))))))]
        unpack (localfx [0 => (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
                 [1 => (plug (val (prod i32) norefs) (prod i32))] [2 => (plug (val (prod i32) norefs) (prod i32))]
                 [3 => (plug (val (prod i32) norefs) (prod i32))] [4 => (plug (val (prod i32) norefs) (prod i32))]
                 [5 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (i31 (val ptr norefs)) ->
                                  (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (i31 (val ptr norefs)) ->
                                       (ref (val ptr anyrefs) (base mm) mut
                                         (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (i31 (val ptr norefs)) ->
                                  (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                         -> []
          load (path 0) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (ref (val ptr anyrefs) (base mm) mut
                                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (ref (val ptr anyrefs) (base mm) mut
                                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (i31 (val ptr norefs)) ->
                                       (ref (val ptr anyrefs) (base mm) mut
                                         (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (i31 (val ptr norefs)) ->
                                  (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                         -> []
          load (path 1) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (ref (val ptr anyrefs) (base mm) mut
                                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (ref (val ptr anyrefs) (base mm) mut
                                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))
                                 (coderef (val i32 norefs)
                                   ((var 0) (i31 (val ptr norefs)) ->
                                   (ref (val ptr anyrefs) (base mm) mut
                                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          local.set 4 ;; [(coderef (val i32 norefs)
                            ((var 0) (i31 (val ptr norefs)) ->
                            (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                         -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  -> []
          local.get move 4 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (i31 (val ptr norefs)) ->
                                 (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          local.set 5 ;; [(coderef (val i32 norefs)
                            ((var 0) (i31 (val ptr norefs)) ->
                            (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                         -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          num_const 5 ;; [] -> [(num (val i32 norefs) i32)]
          tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (i31 (val ptr norefs)) ->
                                 (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          copy ;; [(coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                  ->
                  [(coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))
                   (coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          local.set 5 ;; [(coderef (val i32 norefs)
                            ((var 0) (i31 (val ptr norefs)) ->
                            (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                         -> []
          call_indirect ;; [(var 0) (i31 (val ptr norefs))
                            (coderef (val i32 norefs)
                              ((var 0) (i31 (val ptr norefs)) ->
                              (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                           -> [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (i31 (val ptr norefs)) ->
                                 (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          drop ;; [(coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                  -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (i31 (val ptr norefs)) ->
                                       (ref (val ptr anyrefs) (base mm) mut
                                         (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                      (ser (mem (rep i32) norefs)
                        (coderef (val i32 norefs)
                          ((var 0) (i31 (val ptr norefs)) ->
                          (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))))))]
               -> [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))]
        load (path) copy ;; [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))] ->
                            [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))
                             (i31 (val ptr norefs))]
        group ;; [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))
                  (i31 (val ptr norefs))]
                 ->
                 [(prod (val (prod ptr ptr) anyrefs)
                    (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))
                    (i31 (val ptr norefs)))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0 1)
      (export "_start" (func 1)))
    -----------lin_assign-----------
    (module
      (import ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
              (i31 (val ptr norefs)) ->
              (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))
      (func
          ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
          (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))) (local ptr ptr ptr ptr
          ptr)
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                        (i31 (val ptr norefs)) ->
                        (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
        group ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (i31 (val ptr norefs)) ->
                    (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                 ->
                 [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (coderef (val i32 norefs)
                      ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (i31 (val ptr norefs)) ->
                      (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))]
        new ;; [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (i31 (val ptr norefs)) ->
                    (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))]
               ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr i32)) gcrefs)
                    (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                        (i31 (val ptr norefs)) ->
                        (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr i32)) gcrefs)
                     (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (i31 (val ptr norefs)) ->
                         (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (i31 (val ptr norefs)) ->
                         (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
        pack ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (i31 (val ptr norefs)) ->
                         (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))))))]
        unpack (localfx [0 => (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
                 [1 => (plug (val (prod i32) norefs) (prod i32))] [2 => (plug (val (prod i32) norefs) (prod i32))]
                 [3 => (plug (val (prod i32) norefs) (prod i32))] [4 => (plug (val (prod i32) norefs) (prod i32))]
                 [5 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (i31 (val ptr norefs)) ->
                                  (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (i31 (val ptr norefs)) ->
                                       (ref (val ptr anyrefs) (base mm) mut
                                         (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (i31 (val ptr norefs)) ->
                                  (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                         -> []
          load (path 0) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (ref (val ptr anyrefs) (base mm) mut
                                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (ref (val ptr anyrefs) (base mm) mut
                                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (i31 (val ptr norefs)) ->
                                       (ref (val ptr anyrefs) (base mm) mut
                                         (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (i31 (val ptr norefs)) ->
                                  (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                         -> []
          load (path 1) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (ref (val ptr anyrefs) (base mm) mut
                                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (ref (val ptr anyrefs) (base mm) mut
                                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))
                                 (coderef (val i32 norefs)
                                   ((var 0) (i31 (val ptr norefs)) ->
                                   (ref (val ptr anyrefs) (base mm) mut
                                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          local.set 4 ;; [(coderef (val i32 norefs)
                            ((var 0) (i31 (val ptr norefs)) ->
                            (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                         -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  -> []
          local.get move 4 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (i31 (val ptr norefs)) ->
                                 (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          local.set 5 ;; [(coderef (val i32 norefs)
                            ((var 0) (i31 (val ptr norefs)) ->
                            (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                         -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          num_const 5 ;; [] -> [(num (val i32 norefs) i32)]
          tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (i31 (val ptr norefs)) ->
                                 (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          copy ;; [(coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                  ->
                  [(coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))
                   (coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          local.set 5 ;; [(coderef (val i32 norefs)
                            ((var 0) (i31 (val ptr norefs)) ->
                            (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                         -> []
          call_indirect ;; [(var 0) (i31 (val ptr norefs))
                            (coderef (val i32 norefs)
                              ((var 0) (i31 (val ptr norefs)) ->
                              (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                           -> [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (i31 (val ptr norefs)) ->
                                 (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          drop ;; [(coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                  -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (i31 (val ptr norefs)) ->
                                       (ref (val ptr anyrefs) (base mm) mut
                                         (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                      (ser (mem (rep i32) norefs)
                        (coderef (val i32 norefs)
                          ((var 0) (i31 (val ptr norefs)) ->
                          (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))))))]
               -> [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))]
        num_const 8 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        store (path) ;; [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))
                         (i31 (val ptr norefs))]
                        -> [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0 1)
      (export "_start" (func 1)))
    -----------lin_let-----------
    (module
      (import ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
              (i31 (val ptr norefs)) ->
              (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))
      (func
          ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
          (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))) (local ptr ptr ptr ptr
          ptr ptr)
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                        (i31 (val ptr norefs)) ->
                        (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
        group ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (i31 (val ptr norefs)) ->
                    (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                 ->
                 [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (coderef (val i32 norefs)
                      ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (i31 (val ptr norefs)) ->
                      (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))]
        new ;; [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (i31 (val ptr norefs)) ->
                    (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))]
               ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr i32)) gcrefs)
                    (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                        (i31 (val ptr norefs)) ->
                        (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr i32)) gcrefs)
                     (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (i31 (val ptr norefs)) ->
                         (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (i31 (val ptr norefs)) ->
                         (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
        pack ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (i31 (val ptr norefs)) ->
                         (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))))))]
        unpack (localfx [0 => (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
                 [1 => (plug (val (prod i32) norefs) (prod i32))] [2 => (plug (val (prod i32) norefs) (prod i32))]
                 [3 => (plug (val (prod i32) norefs) (prod i32))] [4 => (plug (val (prod i32) norefs) (prod i32))]
                 [5 => (plug (val (prod i32) norefs) (prod i32))] [6 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (i31 (val ptr norefs)) ->
                                  (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (i31 (val ptr norefs)) ->
                                       (ref (val ptr anyrefs) (base mm) mut
                                         (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (i31 (val ptr norefs)) ->
                                  (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                         -> []
          load (path 0) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (ref (val ptr anyrefs) (base mm) mut
                                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (ref (val ptr anyrefs) (base mm) mut
                                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (i31 (val ptr norefs)) ->
                                       (ref (val ptr anyrefs) (base mm) mut
                                         (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (i31 (val ptr norefs)) ->
                                  (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                         -> []
          load (path 1) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (ref (val ptr anyrefs) (base mm) mut
                                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (ref (val ptr anyrefs) (base mm) mut
                                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))
                                 (coderef (val i32 norefs)
                                   ((var 0) (i31 (val ptr norefs)) ->
                                   (ref (val ptr anyrefs) (base mm) mut
                                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          local.set 4 ;; [(coderef (val i32 norefs)
                            ((var 0) (i31 (val ptr norefs)) ->
                            (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                         -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  -> []
          local.get move 4 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (i31 (val ptr norefs)) ->
                                 (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          local.set 5 ;; [(coderef (val i32 norefs)
                            ((var 0) (i31 (val ptr norefs)) ->
                            (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                         -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          num_const 3 ;; [] -> [(num (val i32 norefs) i32)]
          tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (i31 (val ptr norefs)) ->
                                 (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          copy ;; [(coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                  ->
                  [(coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))
                   (coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          local.set 5 ;; [(coderef (val i32 norefs)
                            ((var 0) (i31 (val ptr norefs)) ->
                            (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                         -> []
          call_indirect ;; [(var 0) (i31 (val ptr norefs))
                            (coderef (val i32 norefs)
                              ((var 0) (i31 (val ptr norefs)) ->
                              (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                           -> [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (i31 (val ptr norefs)) ->
                                 (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          drop ;; [(coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                  -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (i31 (val ptr norefs)) ->
                                       (ref (val ptr anyrefs) (base mm) mut
                                         (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                      (ser (mem (rep i32) norefs)
                        (coderef (val i32 norefs)
                          ((var 0) (i31 (val ptr norefs)) ->
                          (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))))))]
               -> [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))]
        local.set 6 ;; [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))] -> []
        local.get move 6 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))]
        num_const 9 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        store (path) ;; [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))
                         (i31 (val ptr norefs))]
                        -> [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))]
        local.get move 6 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
        drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0 1)
      (export "_start" (func 1)))
    -----------lin_roundtrip-----------
    (module
      (import ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
              (i31 (val ptr norefs)) ->
              (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))
      (func
          ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
          (prod (val (prod ptr ptr) anyrefs)
            (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))
            (i31 (val ptr norefs))))
          (local ptr ptr ptr ptr ptr ptr ptr)
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                        (i31 (val ptr norefs)) ->
                        (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
        group ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (i31 (val ptr norefs)) ->
                    (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                 ->
                 [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (coderef (val i32 norefs)
                      ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (i31 (val ptr norefs)) ->
                      (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))]
        new ;; [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (i31 (val ptr norefs)) ->
                    (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))]
               ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr i32)) gcrefs)
                    (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                        (i31 (val ptr norefs)) ->
                        (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr i32)) gcrefs)
                     (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (i31 (val ptr norefs)) ->
                         (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (i31 (val ptr norefs)) ->
                         (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
        pack ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (i31 (val ptr norefs)) ->
                         (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))))))]
        unpack (localfx [0 => (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
                 [1 => (plug (val (prod i32) norefs) (prod i32))] [2 => (plug (val (prod i32) norefs) (prod i32))]
                 [3 => (plug (val (prod i32) norefs) (prod i32))] [4 => (plug (val (prod i32) norefs) (prod i32))]
                 [5 => (plug (val (prod i32) norefs) (prod i32))] [6 => (plug (val (prod i32) norefs) (prod i32))]
                 [7 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (i31 (val ptr norefs)) ->
                                  (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (i31 (val ptr norefs)) ->
                                       (ref (val ptr anyrefs) (base mm) mut
                                         (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (i31 (val ptr norefs)) ->
                                  (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                         -> []
          load (path 0) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (ref (val ptr anyrefs) (base mm) mut
                                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (ref (val ptr anyrefs) (base mm) mut
                                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (i31 (val ptr norefs)) ->
                                       (ref (val ptr anyrefs) (base mm) mut
                                         (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (i31 (val ptr norefs)) ->
                                  (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                         -> []
          load (path 1) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (ref (val ptr anyrefs) (base mm) mut
                                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) ->
                                         (ref (val ptr anyrefs) (base mm) mut
                                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))
                                 (coderef (val i32 norefs)
                                   ((var 0) (i31 (val ptr norefs)) ->
                                   (ref (val ptr anyrefs) (base mm) mut
                                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          local.set 4 ;; [(coderef (val i32 norefs)
                            ((var 0) (i31 (val ptr norefs)) ->
                            (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                         -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  -> []
          local.get move 4 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (i31 (val ptr norefs)) ->
                                 (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          local.set 5 ;; [(coderef (val i32 norefs)
                            ((var 0) (i31 (val ptr norefs)) ->
                            (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                         -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          num_const 3 ;; [] -> [(num (val i32 norefs) i32)]
          tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (i31 (val ptr norefs)) ->
                                 (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          copy ;; [(coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                  ->
                  [(coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))
                   (coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          local.set 5 ;; [(coderef (val i32 norefs)
                            ((var 0) (i31 (val ptr norefs)) ->
                            (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                         -> []
          call_indirect ;; [(var 0) (i31 (val ptr norefs))
                            (coderef (val i32 norefs)
                              ((var 0) (i31 (val ptr norefs)) ->
                              (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                           -> [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (i31 (val ptr norefs)) ->
                                 (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
          drop ;; [(coderef (val i32 norefs)
                     ((var 0) (i31 (val ptr norefs)) ->
                     (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))]
                  -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (i31 (val ptr norefs)) ->
                                       (ref (val ptr anyrefs) (base mm) mut
                                         (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (i31 (val ptr norefs)) ->
                           (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                      (ser (mem (rep i32) norefs)
                        (coderef (val i32 norefs)
                          ((var 0) (i31 (val ptr norefs)) ->
                          (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))))))]
               -> [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))]
        num_const 8 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        store (path) ;; [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))
                         (i31 (val ptr norefs))]
                        -> [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))]
        load (path) copy ;; [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))] ->
                            [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))
                             (i31 (val ptr norefs))]
        group ;; [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))
                  (i31 (val ptr norefs))]
                 ->
                 [(prod (val (prod ptr ptr) anyrefs)
                    (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))
                    (i31 (val ptr norefs)))]
        ungroup ;; [(prod (val (prod ptr ptr) anyrefs)
                      (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))
                      (i31 (val ptr norefs)))]
                   ->
                   [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))
                    (i31 (val ptr norefs))]
        local.set 7 ;; [(i31 (val ptr norefs))] -> []
        local.set 6 ;; [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))] -> []
        local.get move 6 ;; [] ->
                            [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))]
        local.get move 7 ;; [] -> [(i31 (val ptr norefs))]
        copy ;; [(i31 (val ptr norefs))] -> [(i31 (val ptr norefs)) (i31 (val ptr norefs))]
        local.set 7 ;; [(i31 (val ptr norefs))] -> []
        group ;; [(ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))
                  (i31 (val ptr norefs))]
                 ->
                 [(prod (val (prod ptr ptr) anyrefs)
                    (ref (val ptr anyrefs) (base mm) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))
                    (i31 (val ptr norefs)))]
        local.get move 6 ;; [] -> [(plug (val (prod i32) norefs) (prod i32))]
        drop ;; [(plug (val (prod i32) norefs) (prod i32))] -> []
        local.get move 7 ;; [] -> [(i31 (val ptr norefs))]
        drop ;; [(i31 (val ptr norefs))] -> []
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0 1)
      (export "_start" (func 1)))
    -----------lin_reuse_rejected-----------
    FAILURE (InstrErr (error (NonRef Store (Plug (Prod ((Atom I32))))))
     (instr (Store (Path ())))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return
        ((Prod ((Ref (Base MM) Mut (Ser I31)) (Ref (Base MM) Mut (Ser I31))))))
       (functions
        ((FunctionType () ((Ref (Base GC) Imm (Struct ())) I31)
          ((Ref (Base MM) Mut (Ser I31))))
         (FunctionType () ((Ref (Base GC) Imm (Struct ())))
          ((Prod ((Ref (Base MM) Mut (Ser I31)) (Ref (Base MM) Mut (Ser I31))))))))
       (table
        ((FunctionType () ((Ref (Base GC) Imm (Struct ())) I31)
          ((Ref (Base MM) Mut (Ser I31))))
         (FunctionType () ((Ref (Base GC) Imm (Struct ())))
          ((Prod ((Ref (Base MM) Mut (Ser I31)) (Ref (Base MM) Mut (Ser I31))))))))
       (lfx ())))
     (state
      ((locals
        ((Ref (Base GC) Imm (Struct ())) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32))))))
       (stack (I31 (Plug (Prod ((Atom I32)))) (Ref (Base MM) Mut (Ser I31)))))))
    -----------sum_unit-----------
    (module
      (func
          ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
          (ref (val ptr gcrefs) (base gc) imm
            (variant (mem (sum (rep ptr)) gcrefs)
              (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))))))
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        inject_new 0 ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] ->
                        [(ref (val ptr gcrefs) (base gc) imm
                           (variant (mem (sum (rep ptr)) gcrefs)
                             (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------sum_option-----------
    (module
      (func
          ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
          (ref (val ptr gcrefs) (base gc) imm
            (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
              (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
              (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))
        num_const 15 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        inject_new 1 ;; [(i31 (val ptr norefs))] ->
                        [(ref (val ptr gcrefs) (base gc) imm
                           (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                             (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                             (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------basic_if-----------
    (module
      (func ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs)))
        num_const 0 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        untag ;; [(i31 (val ptr norefs))] -> [(num (val i32 norefs) i32)]
        num_const 0 ;; [] -> [(num (val i32 norefs) i32)]
        i32.eq ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        if (localfx [0 => (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))])
          num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
          tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        else
          num_const 2 ;; [] -> [(num (val i32 norefs) i32)]
          tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        end ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------add-----------
    (module
      (func ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs)))
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        untag ;; [(i31 (val ptr norefs))] -> [(num (val i32 norefs) i32)]
        num_const 2 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        untag ;; [(i31 (val ptr norefs))] -> [(num (val i32 norefs) i32)]
        i32.add ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------sub-----------
    (module
      (func ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs)))
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        untag ;; [(i31 (val ptr norefs))] -> [(num (val i32 norefs) i32)]
        num_const 2 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        untag ;; [(i31 (val ptr norefs))] -> [(num (val i32 norefs) i32)]
        i32.sub ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------mul-----------
    (module
      (func ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs)))
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        untag ;; [(i31 (val ptr norefs))] -> [(num (val i32 norefs) i32)]
        num_const 2 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        untag ;; [(i31 (val ptr norefs))] -> [(num (val i32 norefs) i32)]
        i32.mul ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------div-----------
    (module
      (func ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs)))
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        untag ;; [(i31 (val ptr norefs))] -> [(num (val i32 norefs) i32)]
        num_const 2 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        untag ;; [(i31 (val ptr norefs))] -> [(num (val i32 norefs) i32)]
        i32.div_s ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------math-----------
    (module
      (func ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs)))
        num_const 2 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        untag ;; [(i31 (val ptr norefs))] -> [(num (val i32 norefs) i32)]
        num_const 6 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        untag ;; [(i31 (val ptr norefs))] -> [(num (val i32 norefs) i32)]
        i32.mul ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        untag ;; [(i31 (val ptr norefs))] -> [(num (val i32 norefs) i32)]
        num_const 3 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        untag ;; [(i31 (val ptr norefs))] -> [(num (val i32 norefs) i32)]
        i32.div_s ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------basic_let-----------
    (module
      (func ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs))) (local ptr)
        num_const 10 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        local.set 1 ;; [(i31 (val ptr norefs))] -> []
        local.get move 1 ;; [] -> [(i31 (val ptr norefs))]
        copy ;; [(i31 (val ptr norefs))] -> [(i31 (val ptr norefs)) (i31 (val ptr norefs))]
        local.set 1 ;; [(i31 (val ptr norefs))] -> []
        local.get move 1 ;; [] -> [(i31 (val ptr norefs))]
        drop ;; [(i31 (val ptr norefs))] -> []
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------return_one-----------
    (module
      (func
          ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
          (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
          (i31 (val ptr norefs)))
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> []
        local.get move 1 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (func
          ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
          (exists.type (val ptr gcrefs) (val ptr gcrefs)
            (ref (val ptr gcrefs) (base gc) imm
              (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                (ser (mem (rep i32) norefs)
                  (coderef (val i32 norefs)
                    ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs)))))))))
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                        (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                        (i31 (val ptr norefs))))]
        group ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                    (i31 (val ptr norefs))))]
                 ->
                 [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (coderef (val i32 norefs)
                      ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                      (i31 (val ptr norefs)))))]
        new ;; [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                    (i31 (val ptr norefs)))))]
               ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr i32)) gcrefs)
                    (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                        (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                        (i31 (val ptr norefs)))))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr i32)) gcrefs)
                     (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                         (i31 (val ptr norefs)))))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                         (i31 (val ptr norefs)))))))]
        pack ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                         (i31 (val ptr norefs)))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs))))))))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0 1)
      (export "_start" (func 1)))
    -----------iife-----------
    (module
      (func
          ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
          (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
          (i31 (val ptr norefs)))
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> []
        local.get move 1 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (func ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs))) (local ptr ptr
          ptr ptr ptr)
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                        (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                        (i31 (val ptr norefs))))]
        group ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                    (i31 (val ptr norefs))))]
                 ->
                 [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (coderef (val i32 norefs)
                      ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                      (i31 (val ptr norefs)))))]
        new ;; [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                    (i31 (val ptr norefs)))))]
               ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr i32)) gcrefs)
                    (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                        (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                        (i31 (val ptr norefs)))))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr i32)) gcrefs)
                     (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                         (i31 (val ptr norefs)))))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                         (i31 (val ptr norefs)))))))]
        pack ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                         (i31 (val ptr norefs)))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs))))))))]
        unpack (localfx [0 => (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
                 [1 => (plug (val (prod i32) norefs) (prod i32))] [2 => (plug (val (prod i32) norefs) (prod i32))]
                 [3 => (plug (val (prod i32) norefs) (prod i32))] [4 => (plug (val (prod i32) norefs) (prod i32))]
                 [5 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                  (i31 (val ptr norefs)))))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                       (i31 (val ptr norefs)))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs)))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs)))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs)))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                  (i31 (val ptr norefs)))))))]
                         -> []
          load (path 0) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                         (i31 (val ptr norefs)))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                         (i31 (val ptr norefs)))))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs)))))))]
                  -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                       (i31 (val ptr norefs)))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs)))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs)))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs)))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                  (i31 (val ptr norefs)))))))]
                         -> []
          load (path 1) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                         (i31 (val ptr norefs)))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                         (i31 (val ptr norefs)))))))
                                 (coderef (val i32 norefs)
                                   ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                   (i31 (val ptr norefs))))]
          local.set 4 ;; [(coderef (val i32 norefs)
                            ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                            (i31 (val ptr norefs))))]
                         -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs)))))))]
                  -> []
          local.get move 4 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                 (i31 (val ptr norefs))))]
          local.set 5 ;; [(coderef (val i32 norefs)
                            ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                            (i31 (val ptr norefs))))]
                         -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          group ;; [] -> [(prod (val (prod) norefs))]
          new ;; [(prod (val (prod) norefs))] ->
                 [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
          cast ;; [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                  [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                 (i31 (val ptr norefs))))]
          copy ;; [(coderef (val i32 norefs)
                     ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs))))]
                  ->
                  [(coderef (val i32 norefs)
                     ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs))))
                   (coderef (val i32 norefs)
                     ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs))))]
          local.set 5 ;; [(coderef (val i32 norefs)
                            ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                            (i31 (val ptr norefs))))]
                         -> []
          call_indirect ;; [(var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                            (coderef (val i32 norefs)
                              ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                              (i31 (val ptr norefs))))]
                           -> [(i31 (val ptr norefs))]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                 (i31 (val ptr norefs))))]
          drop ;; [(coderef (val i32 norefs)
                     ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs))))]
                  -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                       (i31 (val ptr norefs)))))))]
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs)))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                      (ser (mem (rep i32) norefs)
                        (coderef (val i32 norefs)
                          ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                          (i31 (val ptr norefs))))))))]
               -> [(i31 (val ptr norefs))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0 1)
      (export "_start" (func 1)))
    -------------------------------
    (module
      (func
          ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
          (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))
        local.get move 1 ;; [] -> [(i31 (val ptr norefs))]
        copy ;; [(i31 (val ptr norefs))] -> [(i31 (val ptr norefs)) (i31 (val ptr norefs))]
        local.set 1 ;; [(i31 (val ptr norefs))] -> []
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> []
        local.get move 1 ;; [] -> [(i31 (val ptr norefs))]
        drop ;; [(i31 (val ptr norefs))] -> [])
      (func ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs))) (local ptr ptr
          ptr ptr ptr)
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                        (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
        group ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
                 ->
                 [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (coderef (val i32 norefs)
                      ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))]
        new ;; [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))]
               ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr i32)) gcrefs)
                    (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                        (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr i32)) gcrefs)
                     (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
        pack ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                         (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
        unpack (localfx [0 => (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
                 [1 => (plug (val (prod i32) norefs) (prod i32))] [2 => (plug (val (prod i32) norefs) (prod i32))]
                 [3 => (plug (val (prod i32) norefs) (prod i32))] [4 => (plug (val (prod i32) norefs) (prod i32))]
                 [5 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                         -> []
          load (path 0) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                  -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                         -> []
          load (path 1) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))
                                 (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
          local.set 4 ;; [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))] -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                  -> []
          local.get move 4 ;; [] -> [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
          local.set 5 ;; [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))] -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          num_const 5 ;; [] -> [(num (val i32 norefs) i32)]
          tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
          local.get move 5 ;; [] -> [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
          copy ;; [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))] ->
                  [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))
                   (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
          local.set 5 ;; [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))] -> []
          call_indirect ;; [(var 0) (i31 (val ptr norefs))
                            (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
                           -> [(i31 (val ptr norefs))]
          local.get move 5 ;; [] -> [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
          drop ;; [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))] -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                      (ser (mem (rep i32) norefs)
                        (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
               -> [(i31 (val ptr norefs))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0 1)
      (export "_start" (func 1)))
    -----------add_one-----------
    (module
      (func
          ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
          (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))
        local.get move 1 ;; [] -> [(i31 (val ptr norefs))]
        copy ;; [(i31 (val ptr norefs))] -> [(i31 (val ptr norefs)) (i31 (val ptr norefs))]
        local.set 1 ;; [(i31 (val ptr norefs))] -> []
        untag ;; [(i31 (val ptr norefs))] -> [(num (val i32 norefs) i32)]
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        untag ;; [(i31 (val ptr norefs))] -> [(num (val i32 norefs) i32)]
        i32.add ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> []
        local.get move 1 ;; [] -> [(i31 (val ptr norefs))]
        drop ;; [(i31 (val ptr norefs))] -> [])
      (table 0)
      (export "add1" (func 0)))
    -----------id-----------
    (module
      (func
          (forall.type (VALTYPE (AtomR PtrR) GCRefs)
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])); (VarT 0)]
              [ (VarT 0)]))
        local.get move 1 ;; [] -> [(var 0)]
        copy ;; [(var 0)] -> [(var 0) (var 0)]
        local.set 1 ;; [(var 0)] -> []
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> []
        local.get move 1 ;; [] -> [(var 0)]
        drop ;; [(var 0)] -> [])
      (table 0)
      (export "id" (func 0)))
    -----------assign-----------
    (module
      (func ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs))) (local ptr ptr
          ptr)
        num_const 0 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        new ;; [(i31 (val ptr norefs))] ->
               [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))]
        local.set 1 ;; [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))] -> []
        local.get move 1 ;; [] ->
                            [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))]
        copy ;; [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))] ->
                [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))
                 (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))]
        local.set 1 ;; [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))] -> []
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        store (path) ;; [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))
                         (i31 (val ptr norefs))]
                        -> [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))]
        local.set 2 ;; [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))] -> []
        local.get move 1 ;; [] ->
                            [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))]
        copy ;; [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))] ->
                [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))
                 (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))]
        local.set 1 ;; [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))] -> []
        load (path) copy ;; [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))] ->
                            [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))
                             (i31 (val ptr norefs))]
        local.set 3 ;; [(i31 (val ptr norefs))] -> []
        drop ;; [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))] -> []
        local.get move 3 ;; [] -> [(i31 (val ptr norefs))]
        local.get move 2 ;; [] ->
                            [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))]
        drop ;; [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))] -> []
        local.get move 1 ;; [] ->
                            [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))]
        drop ;; [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))] -> []
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------apply_id-----------
    (module
      (func
          (forall.type (VALTYPE (AtomR PtrR) GCRefs)
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])); (VarT 0)]
              [ (VarT 0)]))
        local.get move 1 ;; [] -> [(var 0)]
        copy ;; [(var 0)] -> [(var 0) (var 0)]
        local.set 1 ;; [(var 0)] -> []
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> []
        local.get move 1 ;; [] -> [(var 0)]
        drop ;; [(var 0)] -> [])
      (func ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs))) (local ptr ptr
          ptr ptr ptr)
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                              (VarT 0)]
                            [ (VarT 0)])))]
        group ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                      (MonoFunT
                        [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                          (VarT 0)]
                        [ (VarT 0)])))]
                 ->
                 [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (coderef (val i32 norefs)
                      (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                        (MonoFunT
                          [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                            (VarT 0)]
                          [ (VarT 0)]))))]
        new ;; [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                      (MonoFunT
                        [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                          (VarT 0)]
                        [ (VarT 0)]))))]
               ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr i32)) gcrefs)
                    (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (coderef (val i32 norefs)
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                              (VarT 0)]
                            [ (VarT 0)]))))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr i32)) gcrefs)
                     (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                       (coderef (val i32 norefs)
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT
                             [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                               (VarT 0)]
                             [ (VarT 0)]))))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT
                             [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                               (VarT 0)]
                             [ (VarT 0)]))))))]
        pack ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT
                             [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                               (VarT 0)]
                             [ (VarT 0)]))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))))))]
        unpack (localfx [0 => (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
                 [1 => (plug (val (prod i32) norefs) (prod i32))] [2 => (plug (val (prod i32) norefs) (prod i32))]
                 [3 => (plug (val (prod i32) norefs) (prod i32))] [4 => (plug (val (prod i32) norefs) (prod i32))]
                 [5 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                         -> []
          load (path 0) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                         -> []
          load (path 1) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                                 (coderef (val i32 norefs)
                                   (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          local.set 4 ;; [(coderef (val i32 norefs)
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                         -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  -> []
          local.get move 4 ;; [] ->
                              [(coderef (val i32 norefs)
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          local.set 5 ;; [(coderef (val i32 norefs)
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                         -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          num_const 42 ;; [] -> [(num (val i32 norefs) i32)]
          tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          copy ;; [(coderef (val i32 norefs)
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                  ->
                  [(coderef (val i32 norefs)
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))
                   (coderef (val i32 norefs)
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          local.set 5 ;; [(coderef (val i32 norefs)
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                         -> []
          inst (type (i31 (val ptr norefs))) ;; [(coderef (val i32 norefs)
                                                   (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                                     (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                                                ->
                                                [(coderef (val i32 norefs)
                                                   ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
          call_indirect ;; [(var 0) (i31 (val ptr norefs))
                            (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
                           -> [(i31 (val ptr norefs))]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          drop ;; [(coderef (val i32 norefs)
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                  -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                      (ser (mem (rep i32) norefs)
                        (coderef (val i32 norefs)
                          (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))))))]
               -> [(i31 (val ptr norefs))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0 1)
      (export "id" (func 0))
      (export "_start" (func 1)))
    -----------opt_case-----------
    (module
      (func ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs))) (local ptr ptr
          ptr ptr)
        num_const 42 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        inject_new 1 ;; [(i31 (val ptr norefs))] ->
                        [(ref (val ptr gcrefs) (base gc) imm
                           (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                             (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                             (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                          (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                            (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                            (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                       -> []
        local.get move 1 ;; [] ->
                            [(ref (val ptr gcrefs) (base gc) imm
                               (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                 (ser (mem (rep ptr) gcrefs)
                                   (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                 (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        copy ;; [(ref (val ptr gcrefs) (base gc) imm
                   (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                 (ref (val ptr gcrefs) (base gc) imm
                   (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                          (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                            (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                            (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                       -> []
        case_load copy
          (localfx [0 => (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
            [1 =>
            (ref (val ptr gcrefs) (base gc) imm
              (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
            [2 => (plug (val (prod i32) norefs) (prod i32))] [3 => (plug (val (prod i32) norefs) (prod i32))]
            [4 => (plug (val (prod i32) norefs) (prod i32))])
          (0
            local.set 2 ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> []
            num_const 0 ;; [] -> [(num (val i32 norefs) i32)]
            tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
            local.get move 2 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
            drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
          (1
            local.set 3 ;; [(i31 (val ptr norefs))] -> []
            local.get move 3 ;; [] -> [(i31 (val ptr norefs))]
            copy ;; [(i31 (val ptr norefs))] -> [(i31 (val ptr norefs)) (i31 (val ptr norefs))]
            local.set 3 ;; [(i31 (val ptr norefs))] -> []
            local.get move 3 ;; [] -> [(i31 (val ptr norefs))]
            drop ;; [(i31 (val ptr norefs))] -> [])
        end ;; [(ref (val ptr gcrefs) (base gc) imm
                  (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                    (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                    (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
               ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                    (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                    (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                (i31 (val ptr norefs))]
        local.set 4 ;; [(i31 (val ptr norefs))] -> []
        drop ;; [(ref (val ptr gcrefs) (base gc) imm
                   (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                -> []
        local.get move 4 ;; [] -> [(i31 (val ptr norefs))]
        local.get move 1 ;; [] ->
                            [(ref (val ptr gcrefs) (base gc) imm
                               (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                 (ser (mem (rep ptr) gcrefs)
                                   (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                 (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm
                   (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                -> []
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------poly_len-----------
    (module
      (func
          (forall.type (VALTYPE (AtomR PtrR) GCRefs)
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                (RecT (VALTYPE (AtomR PtrR) GCRefs)
                  (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                    (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                        (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                          (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
              [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))
          (local ptr ptr ptr ptr ptr ptr ptr ptr ptr)
        local.get move 1 ;; [] ->
                            [(rec (val ptr gcrefs)
                               (ref (val ptr gcrefs) (base gc) imm
                                 (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs)
                                     (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                   (ser (mem (rep ptr) gcrefs)
                                     (ref (val ptr gcrefs) (base gc) imm
                                       (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                         (ser (mem (rep ptr) gcrefs) (var 1))
                                         (ser (mem (rep ptr) gcrefs) (var 0))))))))]
        copy ;; [(rec (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                       (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                       (ser (mem (rep ptr) gcrefs)
                         (ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                             (ser (mem (rep ptr) gcrefs) (var 1)) (ser (mem (rep ptr) gcrefs) (var 0))))))))]
                ->
                [(rec (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                       (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                       (ser (mem (rep ptr) gcrefs)
                         (ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                             (ser (mem (rep ptr) gcrefs) (var 1)) (ser (mem (rep ptr) gcrefs) (var 0))))))))
                 (rec (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                       (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                       (ser (mem (rep ptr) gcrefs)
                         (ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                             (ser (mem (rep ptr) gcrefs) (var 1)) (ser (mem (rep ptr) gcrefs) (var 0))))))))]
        local.set 1 ;; [(rec (val ptr gcrefs)
                          (ref (val ptr gcrefs) (base gc) imm
                            (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                              (ser (mem (rep ptr) gcrefs)
                                (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                              (ser (mem (rep ptr) gcrefs)
                                (ref (val ptr gcrefs) (base gc) imm
                                  (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                    (ser (mem (rep ptr) gcrefs) (var 1))
                                    (ser (mem (rep ptr) gcrefs) (var 0))))))))]
                       -> []
        unfold ;; [(rec (val ptr gcrefs)
                     (ref (val ptr gcrefs) (base gc) imm
                       (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                         (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                         (ser (mem (rep ptr) gcrefs)
                           (ref (val ptr gcrefs) (base gc) imm
                             (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                               (ser (mem (rep ptr) gcrefs) (var 1)) (ser (mem (rep ptr) gcrefs) (var 0))))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                       (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                       (ser (mem (rep ptr) gcrefs)
                         (ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                             (ser (mem (rep ptr) gcrefs) (var 0))
                             (ser (mem (rep ptr) gcrefs)
                               (rec (val ptr gcrefs)
                                 (ref (val ptr gcrefs) (base gc) imm
                                   (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs)
                                       (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                     (ser (mem (rep ptr) gcrefs)
                                       (ref (val ptr gcrefs) (base gc) imm
                                         (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                           (ser (mem (rep ptr) gcrefs) (var 1))
                                           (ser (mem (rep ptr) gcrefs) (var 0))))))))))))))]
        case_load copy
          (localfx [0 => (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
            [1 =>
            (rec (val ptr gcrefs)
              (ref (val ptr gcrefs) (base gc) imm
                (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                  (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                  (ser (mem (rep ptr) gcrefs)
                    (ref (val ptr gcrefs) (base gc) imm
                      (struct (mem (prod (rep ptr) (rep ptr)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 1))
                        (ser (mem (rep ptr) gcrefs) (var 0))))))))]
            [2 => (plug (val (prod i32) norefs) (prod i32))] [3 => (plug (val (prod i32) norefs) (prod i32))]
            [4 => (plug (val (prod i32) norefs) (prod i32))] [5 => (plug (val (prod i32) norefs) (prod i32))]
            [6 => (plug (val (prod i32) norefs) (prod i32))] [7 => (plug (val (prod i32) norefs) (prod i32))]
            [8 => (plug (val (prod i32) norefs) (prod i32))] [9 => (plug (val (prod i32) norefs) (prod i32))]
            [10 => (plug (val (prod i32) norefs) (prod i32))])
          (0
            local.set 2 ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> []
            num_const 0 ;; [] -> [(num (val i32 norefs) i32)]
            tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
            local.get move 2 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
            drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
          (1
            local.set 3 ;; [(ref (val ptr gcrefs) (base gc) imm
                              (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                (ser (mem (rep ptr) gcrefs) (var 0))
                                (ser (mem (rep ptr) gcrefs)
                                  (rec (val ptr gcrefs)
                                    (ref (val ptr gcrefs) (base gc) imm
                                      (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                        (ser (mem (rep ptr) gcrefs)
                                          (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                        (ser (mem (rep ptr) gcrefs)
                                          (ref (val ptr gcrefs) (base gc) imm
                                            (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                              (ser (mem (rep ptr) gcrefs) (var 1))
                                              (ser (mem (rep ptr) gcrefs) (var 0)))))))))))]
                           -> []
            num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
            tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
            untag ;; [(i31 (val ptr norefs))] -> [(num (val i32 norefs) i32)]
            group ;; [] -> [(prod (val (prod) norefs))]
            new ;; [(prod (val (prod) norefs))] ->
                   [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
            cast ;; [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                    [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
            coderef 0 ;; [] ->
                         [(coderef (val i32 norefs)
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                                  (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                    (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                      (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                          (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                            (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                            (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                              (BaseM MemGC) Imm
                                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
            group ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (coderef (val i32 norefs)
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                              (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                  (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                      (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                        (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                        (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                          (BaseM MemGC) Imm
                                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                              (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                            [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
                     ->
                     [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                        (coderef (val i32 norefs)
                          (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                            (MonoFunT
                              [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                                (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                  (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                    (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                        (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                          (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                          (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                            (BaseM MemGC) Imm
                                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                              [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))]
            new ;; [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (coderef (val i32 norefs)
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                              (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                  (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                      (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                        (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                        (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                          (BaseM MemGC) Imm
                                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                              (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                            [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))]
                   ->
                   [(ref (val ptr gcrefs) (base gc) imm
                      (ser (mem (rep (prod ptr i32)) gcrefs)
                        (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                          (coderef (val i32 norefs)
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                                  (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                    (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                      (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                          (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                            (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                            (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                              (BaseM MemGC) Imm
                                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
            cast ;; [(ref (val ptr gcrefs) (base gc) imm
                       (ser (mem (rep (prod ptr i32)) gcrefs)
                         (prod (val (prod ptr i32) gcrefs)
                           (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                           (coderef (val i32 norefs)
                             (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                               (MonoFunT
                                 [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                   (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                                   (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                     (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                       (BaseM MemGC) Imm
                                       (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                         [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                           (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                             (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                           (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                             (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                               (BaseM MemGC) Imm
                                               (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                 [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                   (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                 [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                    ->
                    [(ref (val ptr gcrefs) (base gc) imm
                       (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                         (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                         (ser (mem (rep i32) norefs)
                           (coderef (val i32 norefs)
                             (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                               (MonoFunT
                                 [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                   (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                                   (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                     (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                       (BaseM MemGC) Imm
                                       (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                         [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                           (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                             (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                           (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                             (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                               (BaseM MemGC) Imm
                                               (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                 [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                   (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                 [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
            pack ;; [(ref (val ptr gcrefs) (base gc) imm
                       (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                         (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                         (ser (mem (rep i32) norefs)
                           (coderef (val i32 norefs)
                             (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                               (MonoFunT
                                 [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                   (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                                   (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                     (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                       (BaseM MemGC) Imm
                                       (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                         [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                           (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                             (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                           (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                             (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                               (BaseM MemGC) Imm
                                               (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                 [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                   (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                 [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                    ->
                    [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                       (ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                           (ser (mem (rep ptr) gcrefs) (var 0))
                           (ser (mem (rep i32) norefs)
                             (coderef (val i32 norefs)
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (MonoFunT
                                   [ (VarT 1);
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                         (BaseM MemGC) Imm
                                         (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                           [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                             (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                               (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                             (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                               (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (BaseM MemGC) Imm
                                                 (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                   [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                     (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                   [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))))))]
            unpack (localfx [0 => (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
                     [1 =>
                     (rec (val ptr gcrefs)
                       (ref (val ptr gcrefs) (base gc) imm
                         (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                           (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                           (ser (mem (rep ptr) gcrefs)
                             (ref (val ptr gcrefs) (base gc) imm
                               (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                 (ser (mem (rep ptr) gcrefs) (var 1)) (ser (mem (rep ptr) gcrefs) (var 0))))))))]
                     [2 => (plug (val (prod i32) norefs) (prod i32))]
                     [3 =>
                     (ref (val ptr gcrefs) (base gc) imm
                       (struct (mem (prod (rep ptr) (rep ptr)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                         (ser (mem (rep ptr) gcrefs)
                           (rec (val ptr gcrefs)
                             (ref (val ptr gcrefs) (base gc) imm
                               (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                 (ser (mem (rep ptr) gcrefs)
                                   (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                 (ser (mem (rep ptr) gcrefs)
                                   (ref (val ptr gcrefs) (base gc) imm
                                     (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                       (ser (mem (rep ptr) gcrefs) (var 1))
                                       (ser (mem (rep ptr) gcrefs) (var 0)))))))))))]
                     [4 => (plug (val (prod i32) norefs) (prod i32))] [5 => (plug (val (prod i32) norefs) (prod i32))]
                     [6 => (plug (val (prod i32) norefs) (prod i32))] [7 => (plug (val (prod i32) norefs) (prod i32))]
                     [8 => (plug (val (prod i32) norefs) (prod i32))] [9 => (plug (val (prod i32) norefs) (prod i32))]
                     [10 => (plug (val (prod i32) norefs) (prod i32))])
              local.set 4 ;; [(ref (val ptr gcrefs) (base gc) imm
                                (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                  (ser (mem (rep ptr) gcrefs) (var 0))
                                  (ser (mem (rep i32) norefs)
                                    (coderef (val i32 norefs)
                                      (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                        (MonoFunT
                                          [ (VarT 1);
                                            (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                              (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                (BaseM MemGC) Imm
                                                (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                    (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                      (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                    (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                      (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                        (BaseM MemGC) Imm
                                                        (ProdT
                                                          (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                            GCRefs)
                                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                          [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                             -> []
              local.get move 4 ;; [] ->
                                  [(ref (val ptr gcrefs) (base gc) imm
                                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                       (ser (mem (rep ptr) gcrefs) (var 0))
                                       (ser (mem (rep i32) norefs)
                                         (coderef (val i32 norefs)
                                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                             (MonoFunT
                                               [ (VarT 1);
                                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                   (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                     (BaseM MemGC) Imm
                                                     (VariantT
                                                       (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                       [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                           (BaseM MemGC) Imm
                                                           (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                         (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                           (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                             (BaseM MemGC) Imm
                                                             (ProdT
                                                               (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                                 GCRefs)
                                                               [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                                 (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                               [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
              copy ;; [(ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                           (ser (mem (rep ptr) gcrefs) (var 0))
                           (ser (mem (rep i32) norefs)
                             (coderef (val i32 norefs)
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (MonoFunT
                                   [ (VarT 1);
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                         (BaseM MemGC) Imm
                                         (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                           [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                             (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                               (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                             (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                               (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (BaseM MemGC) Imm
                                                 (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                   [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                     (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                   [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                      ->
                      [(ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                           (ser (mem (rep ptr) gcrefs) (var 0))
                           (ser (mem (rep i32) norefs)
                             (coderef (val i32 norefs)
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (MonoFunT
                                   [ (VarT 1);
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                         (BaseM MemGC) Imm
                                         (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                           [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                             (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                               (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                             (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                               (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (BaseM MemGC) Imm
                                                 (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                   [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                     (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                   [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))
                       (ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                           (ser (mem (rep ptr) gcrefs) (var 0))
                           (ser (mem (rep i32) norefs)
                             (coderef (val i32 norefs)
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (MonoFunT
                                   [ (VarT 1);
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                         (BaseM MemGC) Imm
                                         (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                           [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                             (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                               (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                             (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                               (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (BaseM MemGC) Imm
                                                 (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                   [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                     (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                   [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
              local.set 4 ;; [(ref (val ptr gcrefs) (base gc) imm
                                (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                  (ser (mem (rep ptr) gcrefs) (var 0))
                                  (ser (mem (rep i32) norefs)
                                    (coderef (val i32 norefs)
                                      (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                        (MonoFunT
                                          [ (VarT 1);
                                            (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                              (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                (BaseM MemGC) Imm
                                                (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                    (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                      (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                    (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                      (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                        (BaseM MemGC) Imm
                                                        (ProdT
                                                          (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                            GCRefs)
                                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                          [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                             -> []
              load (path 0) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                       (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                         (ser (mem (rep ptr) gcrefs) (var 0))
                                         (ser (mem (rep i32) norefs)
                                           (coderef (val i32 norefs)
                                             (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                               (MonoFunT
                                                 [ (VarT 1);
                                                   (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                     (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                       (BaseM MemGC) Imm
                                                       (VariantT
                                                         (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                         [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                           (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                             (BaseM MemGC) Imm
                                                             (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                           (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                             (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                               (BaseM MemGC) Imm
                                                               (ProdT
                                                                 (MEMTYPE
                                                                   (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                                   GCRefs)
                                                                 [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                                   (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                                 [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                                    ->
                                    [(ref (val ptr gcrefs) (base gc) imm
                                       (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                         (ser (mem (rep ptr) gcrefs) (var 0))
                                         (ser (mem (rep i32) norefs)
                                           (coderef (val i32 norefs)
                                             (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                               (MonoFunT
                                                 [ (VarT 1);
                                                   (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                     (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                       (BaseM MemGC) Imm
                                                       (VariantT
                                                         (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                         [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                           (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                             (BaseM MemGC) Imm
                                                             (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                           (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                             (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                               (BaseM MemGC) Imm
                                                               (ProdT
                                                                 (MEMTYPE
                                                                   (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                                   GCRefs)
                                                                 [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                                   (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                                 [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))
                                     (var 0)]
              local.set 5 ;; [(var 0)] -> []
              drop ;; [(ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                           (ser (mem (rep ptr) gcrefs) (var 0))
                           (ser (mem (rep i32) norefs)
                             (coderef (val i32 norefs)
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (MonoFunT
                                   [ (VarT 1);
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                         (BaseM MemGC) Imm
                                         (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                           [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                             (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                               (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                             (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                               (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (BaseM MemGC) Imm
                                                 (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                   [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                     (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                   [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                      -> []
              local.get move 5 ;; [] -> [(var 0)]
              local.set 6 ;; [(var 0)] -> []
              local.get move 4 ;; [] ->
                                  [(ref (val ptr gcrefs) (base gc) imm
                                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                       (ser (mem (rep ptr) gcrefs) (var 0))
                                       (ser (mem (rep i32) norefs)
                                         (coderef (val i32 norefs)
                                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                             (MonoFunT
                                               [ (VarT 1);
                                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                   (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                     (BaseM MemGC) Imm
                                                     (VariantT
                                                       (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                       [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                           (BaseM MemGC) Imm
                                                           (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                         (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                           (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                             (BaseM MemGC) Imm
                                                             (ProdT
                                                               (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                                 GCRefs)
                                                               [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                                 (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                               [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
              copy ;; [(ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                           (ser (mem (rep ptr) gcrefs) (var 0))
                           (ser (mem (rep i32) norefs)
                             (coderef (val i32 norefs)
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (MonoFunT
                                   [ (VarT 1);
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                         (BaseM MemGC) Imm
                                         (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                           [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                             (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                               (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                             (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                               (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (BaseM MemGC) Imm
                                                 (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                   [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                     (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                   [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                      ->
                      [(ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                           (ser (mem (rep ptr) gcrefs) (var 0))
                           (ser (mem (rep i32) norefs)
                             (coderef (val i32 norefs)
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (MonoFunT
                                   [ (VarT 1);
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                         (BaseM MemGC) Imm
                                         (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                           [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                             (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                               (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                             (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                               (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (BaseM MemGC) Imm
                                                 (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                   [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                     (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                   [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))
                       (ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                           (ser (mem (rep ptr) gcrefs) (var 0))
                           (ser (mem (rep i32) norefs)
                             (coderef (val i32 norefs)
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (MonoFunT
                                   [ (VarT 1);
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                         (BaseM MemGC) Imm
                                         (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                           [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                             (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                               (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                             (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                               (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (BaseM MemGC) Imm
                                                 (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                   [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                     (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                   [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
              local.set 4 ;; [(ref (val ptr gcrefs) (base gc) imm
                                (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                  (ser (mem (rep ptr) gcrefs) (var 0))
                                  (ser (mem (rep i32) norefs)
                                    (coderef (val i32 norefs)
                                      (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                        (MonoFunT
                                          [ (VarT 1);
                                            (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                              (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                (BaseM MemGC) Imm
                                                (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                    (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                      (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                    (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                      (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                        (BaseM MemGC) Imm
                                                        (ProdT
                                                          (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                            GCRefs)
                                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                          [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                             -> []
              load (path 1) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                       (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                         (ser (mem (rep ptr) gcrefs) (var 0))
                                         (ser (mem (rep i32) norefs)
                                           (coderef (val i32 norefs)
                                             (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                               (MonoFunT
                                                 [ (VarT 1);
                                                   (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                     (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                       (BaseM MemGC) Imm
                                                       (VariantT
                                                         (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                         [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                           (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                             (BaseM MemGC) Imm
                                                             (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                           (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                             (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                               (BaseM MemGC) Imm
                                                               (ProdT
                                                                 (MEMTYPE
                                                                   (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                                   GCRefs)
                                                                 [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                                   (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                                 [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                                    ->
                                    [(ref (val ptr gcrefs) (base gc) imm
                                       (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                         (ser (mem (rep ptr) gcrefs) (var 0))
                                         (ser (mem (rep i32) norefs)
                                           (coderef (val i32 norefs)
                                             (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                               (MonoFunT
                                                 [ (VarT 1);
                                                   (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                     (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                       (BaseM MemGC) Imm
                                                       (VariantT
                                                         (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                         [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                           (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                             (BaseM MemGC) Imm
                                                             (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                           (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                             (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                               (BaseM MemGC) Imm
                                                               (ProdT
                                                                 (MEMTYPE
                                                                   (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                                   GCRefs)
                                                                 [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                                   (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                                 [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))
                                     (coderef (val i32 norefs)
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                         (MonoFunT
                                           [ (VarT 1);
                                             (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (BaseM MemGC) Imm
                                                 (VariantT
                                                   (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                   [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                     (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                       (BaseM MemGC) Imm
                                                       (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                     (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                         (BaseM MemGC) Imm
                                                         (ProdT
                                                           (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                             GCRefs)
                                                           [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                             (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                           [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
              local.set 7 ;; [(coderef (val i32 norefs)
                                (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                  (MonoFunT
                                    [ (VarT 1);
                                      (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                        (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                          (BaseM MemGC) Imm
                                          (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                              (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                              (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                  (BaseM MemGC) Imm
                                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                    [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
                             -> []
              drop ;; [(ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                           (ser (mem (rep ptr) gcrefs) (var 0))
                           (ser (mem (rep i32) norefs)
                             (coderef (val i32 norefs)
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (MonoFunT
                                   [ (VarT 1);
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                         (BaseM MemGC) Imm
                                         (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                           [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                             (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                               (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                             (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                               (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (BaseM MemGC) Imm
                                                 (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                   [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                     (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                   [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                      -> []
              local.get move 7 ;; [] ->
                                  [(coderef (val i32 norefs)
                                     (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                       (MonoFunT
                                         [ (VarT 1);
                                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                             (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                               (BaseM MemGC) Imm
                                               (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                 [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                   (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                     (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                   (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                     (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                       (BaseM MemGC) Imm
                                                       (ProdT
                                                         (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                         [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                           (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                         [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
              local.set 8 ;; [(coderef (val i32 norefs)
                                (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                  (MonoFunT
                                    [ (VarT 1);
                                      (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                        (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                          (BaseM MemGC) Imm
                                          (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                              (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                              (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                  (BaseM MemGC) Imm
                                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                    [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
                             -> []
              local.get move 6 ;; [] -> [(var 0)]
              copy ;; [(var 0)] -> [(var 0) (var 0)]
              local.set 6 ;; [(var 0)] -> []
              local.get move 3 ;; [] ->
                                  [(ref (val ptr gcrefs) (base gc) imm
                                     (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                       (ser (mem (rep ptr) gcrefs) (var 1))
                                       (ser (mem (rep ptr) gcrefs)
                                         (rec (val ptr gcrefs)
                                           (ref (val ptr gcrefs) (base gc) imm
                                             (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                               (ser (mem (rep ptr) gcrefs)
                                                 (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                               (ser (mem (rep ptr) gcrefs)
                                                 (ref (val ptr gcrefs) (base gc) imm
                                                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                                     (ser (mem (rep ptr) gcrefs) (var 2))
                                                     (ser (mem (rep ptr) gcrefs) (var 0)))))))))))]
              copy ;; [(ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                           (ser (mem (rep ptr) gcrefs) (var 1))
                           (ser (mem (rep ptr) gcrefs)
                             (rec (val ptr gcrefs)
                               (ref (val ptr gcrefs) (base gc) imm
                                 (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs)
                                     (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                   (ser (mem (rep ptr) gcrefs)
                                     (ref (val ptr gcrefs) (base gc) imm
                                       (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                         (ser (mem (rep ptr) gcrefs) (var 2))
                                         (ser (mem (rep ptr) gcrefs) (var 0)))))))))))]
                      ->
                      [(ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                           (ser (mem (rep ptr) gcrefs) (var 1))
                           (ser (mem (rep ptr) gcrefs)
                             (rec (val ptr gcrefs)
                               (ref (val ptr gcrefs) (base gc) imm
                                 (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs)
                                     (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                   (ser (mem (rep ptr) gcrefs)
                                     (ref (val ptr gcrefs) (base gc) imm
                                       (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                         (ser (mem (rep ptr) gcrefs) (var 2))
                                         (ser (mem (rep ptr) gcrefs) (var 0)))))))))))
                       (ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                           (ser (mem (rep ptr) gcrefs) (var 1))
                           (ser (mem (rep ptr) gcrefs)
                             (rec (val ptr gcrefs)
                               (ref (val ptr gcrefs) (base gc) imm
                                 (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs)
                                     (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                   (ser (mem (rep ptr) gcrefs)
                                     (ref (val ptr gcrefs) (base gc) imm
                                       (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                         (ser (mem (rep ptr) gcrefs) (var 2))
                                         (ser (mem (rep ptr) gcrefs) (var 0)))))))))))]
              local.set 3 ;; [(ref (val ptr gcrefs) (base gc) imm
                                (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                  (ser (mem (rep ptr) gcrefs) (var 1))
                                  (ser (mem (rep ptr) gcrefs)
                                    (rec (val ptr gcrefs)
                                      (ref (val ptr gcrefs) (base gc) imm
                                        (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                          (ser (mem (rep ptr) gcrefs)
                                            (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                          (ser (mem (rep ptr) gcrefs)
                                            (ref (val ptr gcrefs) (base gc) imm
                                              (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                                (ser (mem (rep ptr) gcrefs) (var 2))
                                                (ser (mem (rep ptr) gcrefs) (var 0)))))))))))]
                             -> []
              load (path 1) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                       (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                         (ser (mem (rep ptr) gcrefs) (var 1))
                                         (ser (mem (rep ptr) gcrefs)
                                           (rec (val ptr gcrefs)
                                             (ref (val ptr gcrefs) (base gc) imm
                                               (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                                 (ser (mem (rep ptr) gcrefs)
                                                   (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                                 (ser (mem (rep ptr) gcrefs)
                                                   (ref (val ptr gcrefs)
                                                     (base gc) imm
                                                     (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                                       (ser (mem (rep ptr) gcrefs) (var 2))
                                                       (ser (mem (rep ptr) gcrefs) (var 0)))))))))))]
                                    ->
                                    [(ref (val ptr gcrefs) (base gc) imm
                                       (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                         (ser (mem (rep ptr) gcrefs) (var 1))
                                         (ser (mem (rep ptr) gcrefs)
                                           (rec (val ptr gcrefs)
                                             (ref (val ptr gcrefs) (base gc) imm
                                               (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                                 (ser (mem (rep ptr) gcrefs)
                                                   (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                                 (ser (mem (rep ptr) gcrefs)
                                                   (ref (val ptr gcrefs)
                                                     (base gc) imm
                                                     (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                                       (ser (mem (rep ptr) gcrefs) (var 2))
                                                       (ser (mem (rep ptr) gcrefs) (var 0)))))))))))
                                     (rec (val ptr gcrefs)
                                       (ref (val ptr gcrefs) (base gc) imm
                                         (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                           (ser (mem (rep ptr) gcrefs)
                                             (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                           (ser (mem (rep ptr) gcrefs)
                                             (ref (val ptr gcrefs) (base gc) imm
                                               (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                                 (ser (mem (rep ptr) gcrefs) (var 2))
                                                 (ser (mem (rep ptr) gcrefs) (var 0))))))))]
              local.set 9 ;; [(rec (val ptr gcrefs)
                                (ref (val ptr gcrefs) (base gc) imm
                                  (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                    (ser (mem (rep ptr) gcrefs)
                                      (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                    (ser (mem (rep ptr) gcrefs)
                                      (ref (val ptr gcrefs) (base gc) imm
                                        (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                          (ser (mem (rep ptr) gcrefs) (var 2))
                                          (ser (mem (rep ptr) gcrefs) (var 0))))))))]
                             -> []
              drop ;; [(ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                           (ser (mem (rep ptr) gcrefs) (var 1))
                           (ser (mem (rep ptr) gcrefs)
                             (rec (val ptr gcrefs)
                               (ref (val ptr gcrefs) (base gc) imm
                                 (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs)
                                     (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                   (ser (mem (rep ptr) gcrefs)
                                     (ref (val ptr gcrefs) (base gc) imm
                                       (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                         (ser (mem (rep ptr) gcrefs) (var 2))
                                         (ser (mem (rep ptr) gcrefs) (var 0)))))))))))]
                      -> []
              local.get move 9 ;; [] ->
                                  [(rec (val ptr gcrefs)
                                     (ref (val ptr gcrefs) (base gc) imm
                                       (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                         (ser (mem (rep ptr) gcrefs)
                                           (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                         (ser (mem (rep ptr) gcrefs)
                                           (ref (val ptr gcrefs) (base gc) imm
                                             (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                               (ser (mem (rep ptr) gcrefs) (var 2))
                                               (ser (mem (rep ptr) gcrefs) (var 0))))))))]
              local.get move 8 ;; [] ->
                                  [(coderef (val i32 norefs)
                                     (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                       (MonoFunT
                                         [ (VarT 1);
                                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                             (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                               (BaseM MemGC) Imm
                                               (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                 [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                   (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                     (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                   (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                     (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                       (BaseM MemGC) Imm
                                                       (ProdT
                                                         (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                         [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                           (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                         [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
              copy ;; [(coderef (val i32 norefs)
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT
                             [ (VarT 1);
                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                 (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                   (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                     [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                         (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                       (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                           (BaseM MemGC) Imm
                                           (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                             [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                               (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                             [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
                      ->
                      [(coderef (val i32 norefs)
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT
                             [ (VarT 1);
                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                 (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                   (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                     [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                         (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                       (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                           (BaseM MemGC) Imm
                                           (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                             [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                               (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                             [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))
                       (coderef (val i32 norefs)
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT
                             [ (VarT 1);
                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                 (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                   (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                     [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                         (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                       (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                           (BaseM MemGC) Imm
                                           (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                             [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                               (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                             [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
              local.set 8 ;; [(coderef (val i32 norefs)
                                (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                  (MonoFunT
                                    [ (VarT 1);
                                      (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                        (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                          (BaseM MemGC) Imm
                                          (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                              (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                              (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                  (BaseM MemGC) Imm
                                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                    [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
                             -> []
              inst (type (var 1)) ;; [(coderef (val i32 norefs)
                                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                          (MonoFunT
                                            [ (VarT 1);
                                              (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                  (BaseM MemGC) Imm
                                                  (VariantT
                                                    (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                      (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                        (BaseM MemGC) Imm
                                                        (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                        (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                          (BaseM MemGC) Imm
                                                          (ProdT
                                                            (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                              GCRefs)
                                                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                              (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                            [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
                                     ->
                                     [(coderef (val i32 norefs)
                                        ((var 0)
                                        (rec (val ptr gcrefs)
                                          (ref (val ptr gcrefs) (base gc) imm
                                            (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                              (ser (mem (rep ptr) gcrefs)
                                                (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                              (ser (mem (rep ptr) gcrefs)
                                                (ref (val ptr gcrefs) (base gc) imm
                                                  (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                                    (ser (mem (rep ptr) gcrefs) (var 2))
                                                    (ser (mem (rep ptr) gcrefs) (var 0))))))))
                                        -> (i31 (val ptr norefs))))]
              call_indirect ;; [(var 0)
                                (rec (val ptr gcrefs)
                                  (ref (val ptr gcrefs) (base gc) imm
                                    (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                      (ser (mem (rep ptr) gcrefs)
                                        (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                      (ser (mem (rep ptr) gcrefs)
                                        (ref (val ptr gcrefs) (base gc) imm
                                          (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                            (ser (mem (rep ptr) gcrefs) (var 2))
                                            (ser (mem (rep ptr) gcrefs) (var 0))))))))
                                (coderef (val i32 norefs)
                                  ((var 0)
                                  (rec (val ptr gcrefs)
                                    (ref (val ptr gcrefs) (base gc) imm
                                      (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                        (ser (mem (rep ptr) gcrefs)
                                          (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                        (ser (mem (rep ptr) gcrefs)
                                          (ref (val ptr gcrefs) (base gc) imm
                                            (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                              (ser (mem (rep ptr) gcrefs) (var 2))
                                              (ser (mem (rep ptr) gcrefs) (var 0))))))))
                                  -> (i31 (val ptr norefs))))]
                               -> [(i31 (val ptr norefs))]
              local.get move 8 ;; [] ->
                                  [(coderef (val i32 norefs)
                                     (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                       (MonoFunT
                                         [ (VarT 1);
                                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                             (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                               (BaseM MemGC) Imm
                                               (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                 [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                   (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                     (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                   (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                     (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                       (BaseM MemGC) Imm
                                                       (ProdT
                                                         (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                         [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                           (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                         [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
              drop ;; [(coderef (val i32 norefs)
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT
                             [ (VarT 1);
                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                 (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                   (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                     [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                         (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                       (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                           (BaseM MemGC) Imm
                                           (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                             [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                               (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                             [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
                      -> []
              local.get move 6 ;; [] -> [(var 0)]
              drop ;; [(var 0)] -> []
              local.get move 4 ;; [] ->
                                  [(ref (val ptr gcrefs) (base gc) imm
                                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                       (ser (mem (rep ptr) gcrefs) (var 0))
                                       (ser (mem (rep i32) norefs)
                                         (coderef (val i32 norefs)
                                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                             (MonoFunT
                                               [ (VarT 1);
                                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                   (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                     (BaseM MemGC) Imm
                                                     (VariantT
                                                       (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                       [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                           (BaseM MemGC) Imm
                                                           (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                         (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                           (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                             (BaseM MemGC) Imm
                                                             (ProdT
                                                               (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                                 GCRefs)
                                                               [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                                 (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                               [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
              drop ;; [(ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                           (ser (mem (rep ptr) gcrefs) (var 0))
                           (ser (mem (rep i32) norefs)
                             (coderef (val i32 norefs)
                               (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                 (MonoFunT
                                   [ (VarT 1);
                                     (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                         (BaseM MemGC) Imm
                                         (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                           [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                             (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                               (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                             (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                               (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (BaseM MemGC) Imm
                                                 (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                   [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                     (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                   [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                      -> []
            end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                      (ref (val ptr gcrefs) (base gc) imm
                        (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                          (ser (mem (rep i32) norefs)
                            (coderef (val i32 norefs)
                              (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                (MonoFunT
                                  [ (VarT 1);
                                    (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                      (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                        (BaseM MemGC) Imm
                                        (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                            (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                              (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                              (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                (BaseM MemGC) Imm
                                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                    (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                  [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))))))]
                   -> [(i31 (val ptr norefs))]
            untag ;; [(i31 (val ptr norefs))] -> [(num (val i32 norefs) i32)]
            i32.add ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
            tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
            local.get move 3 ;; [] ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep ptr) gcrefs)
                                       (rec (val ptr gcrefs)
                                         (ref (val ptr gcrefs) (base gc) imm
                                           (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                             (ser (mem (rep ptr) gcrefs)
                                               (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                             (ser (mem (rep ptr) gcrefs)
                                               (ref (val ptr gcrefs) (base gc) imm
                                                 (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                                   (ser (mem (rep ptr) gcrefs) (var 1))
                                                   (ser (mem (rep ptr) gcrefs) (var 0)))))))))))]
            drop ;; [(ref (val ptr gcrefs) (base gc) imm
                       (struct (mem (prod (rep ptr) (rep ptr)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                         (ser (mem (rep ptr) gcrefs)
                           (rec (val ptr gcrefs)
                             (ref (val ptr gcrefs) (base gc) imm
                               (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                 (ser (mem (rep ptr) gcrefs)
                                   (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                 (ser (mem (rep ptr) gcrefs)
                                   (ref (val ptr gcrefs) (base gc) imm
                                     (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                       (ser (mem (rep ptr) gcrefs) (var 1))
                                       (ser (mem (rep ptr) gcrefs) (var 0)))))))))))]
                    -> [])
        end ;; [(ref (val ptr gcrefs) (base gc) imm
                  (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                    (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                    (ser (mem (rep ptr) gcrefs)
                      (ref (val ptr gcrefs) (base gc) imm
                        (struct (mem (prod (rep ptr) (rep ptr)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                          (ser (mem (rep ptr) gcrefs)
                            (rec (val ptr gcrefs)
                              (ref (val ptr gcrefs) (base gc) imm
                                (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                  (ser (mem (rep ptr) gcrefs)
                                    (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                  (ser (mem (rep ptr) gcrefs)
                                    (ref (val ptr gcrefs) (base gc) imm
                                      (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                        (ser (mem (rep ptr) gcrefs) (var 1))
                                        (ser (mem (rep ptr) gcrefs) (var 0))))))))))))))]
               ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                    (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                    (ser (mem (rep ptr) gcrefs)
                      (ref (val ptr gcrefs) (base gc) imm
                        (struct (mem (prod (rep ptr) (rep ptr)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                          (ser (mem (rep ptr) gcrefs)
                            (rec (val ptr gcrefs)
                              (ref (val ptr gcrefs) (base gc) imm
                                (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                  (ser (mem (rep ptr) gcrefs)
                                    (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                  (ser (mem (rep ptr) gcrefs)
                                    (ref (val ptr gcrefs) (base gc) imm
                                      (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                        (ser (mem (rep ptr) gcrefs) (var 1))
                                        (ser (mem (rep ptr) gcrefs) (var 0))))))))))))))
                (i31 (val ptr norefs))]
        local.set 10 ;; [(i31 (val ptr norefs))] -> []
        drop ;; [(ref (val ptr gcrefs) (base gc) imm
                   (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep ptr) gcrefs)
                       (ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                           (ser (mem (rep ptr) gcrefs) (var 0))
                           (ser (mem (rep ptr) gcrefs)
                             (rec (val ptr gcrefs)
                               (ref (val ptr gcrefs) (base gc) imm
                                 (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs)
                                     (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                   (ser (mem (rep ptr) gcrefs)
                                     (ref (val ptr gcrefs) (base gc) imm
                                       (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                         (ser (mem (rep ptr) gcrefs) (var 1))
                                         (ser (mem (rep ptr) gcrefs) (var 0))))))))))))))]
                -> []
        local.get move 10 ;; [] -> [(i31 (val ptr norefs))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> []
        local.get move 1 ;; [] ->
                            [(rec (val ptr gcrefs)
                               (ref (val ptr gcrefs) (base gc) imm
                                 (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs)
                                     (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                   (ser (mem (rep ptr) gcrefs)
                                     (ref (val ptr gcrefs) (base gc) imm
                                       (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                         (ser (mem (rep ptr) gcrefs) (var 1))
                                         (ser (mem (rep ptr) gcrefs) (var 0))))))))]
        drop ;; [(rec (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                       (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                       (ser (mem (rep ptr) gcrefs)
                         (ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                             (ser (mem (rep ptr) gcrefs) (var 1)) (ser (mem (rep ptr) gcrefs) (var 0))))))))]
                -> [])
      (func ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs))) (local ptr ptr
          ptr ptr ptr)
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                              (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                  (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                      (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                        (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                        (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                          (BaseM MemGC) Imm
                                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                              (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                            [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
        group ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                      (MonoFunT
                        [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                          (RecT (VALTYPE (AtomR PtrR) GCRefs)
                            (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                              (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                  (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                    (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                    (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                        [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
                 ->
                 [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (coderef (val i32 norefs)
                      (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                        (MonoFunT
                          [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                            (RecT (VALTYPE (AtomR PtrR) GCRefs)
                              (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                    (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                      (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                    (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                      (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                        (BaseM MemGC) Imm
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                          [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))]
        new ;; [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                      (MonoFunT
                        [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                          (RecT (VALTYPE (AtomR PtrR) GCRefs)
                            (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                              (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                  (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                    (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                    (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                        [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))]
               ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr i32)) gcrefs)
                    (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (coderef (val i32 norefs)
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                              (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                  (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                      (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                        (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                        (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                          (BaseM MemGC) Imm
                                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                              (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                            [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr i32)) gcrefs)
                     (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                       (coderef (val i32 norefs)
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT
                             [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                 (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                   (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                     [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                         (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                       (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                           (BaseM MemGC) Imm
                                           (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                             [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                               (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                             [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT
                             [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                 (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                   (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                     [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                         (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                       (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                           (BaseM MemGC) Imm
                                           (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                             [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                               (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                             [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
        pack ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT
                             [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                 (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                   (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                     [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                         (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                       (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                           (BaseM MemGC) Imm
                                           (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                             [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                               (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                             [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 1);
                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                     (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                       [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                           (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                         (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                           (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                             (BaseM MemGC) Imm
                                             (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                               [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                 (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                               [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))))))]
        unpack (localfx [0 => (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
                 [1 => (plug (val (prod i32) norefs) (prod i32))] [2 => (plug (val (prod i32) norefs) (prod i32))]
                 [3 => (plug (val (prod i32) norefs) (prod i32))] [4 => (plug (val (prod i32) norefs) (prod i32))]
                 [5 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                    (MonoFunT
                                      [ (VarT 1);
                                        (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                          (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                            (BaseM MemGC) Imm
                                            (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                  (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                  (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                    (BaseM MemGC) Imm
                                                    (ProdT
                                                      (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                      [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                         (MonoFunT
                                           [ (VarT 1);
                                             (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (BaseM MemGC) Imm
                                                 (VariantT
                                                   (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                   [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                     (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                       (BaseM MemGC) Imm
                                                       (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                     (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                         (BaseM MemGC) Imm
                                                         (ProdT
                                                           (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                             GCRefs)
                                                           [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                             (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                           [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 1);
                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                     (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                       [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                           (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                         (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                           (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                             (BaseM MemGC) Imm
                                             (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                               [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                 (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                               [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 1);
                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                     (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                       [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                           (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                         (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                           (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                             (BaseM MemGC) Imm
                                             (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                               [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                 (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                               [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 1);
                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                     (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                       [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                           (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                         (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                           (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                             (BaseM MemGC) Imm
                                             (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                               [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                 (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                               [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                    (MonoFunT
                                      [ (VarT 1);
                                        (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                          (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                            (BaseM MemGC) Imm
                                            (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                  (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                  (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                    (BaseM MemGC) Imm
                                                    (ProdT
                                                      (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                      [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                         -> []
          load (path 0) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT
                                             [ (VarT 1);
                                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                   (BaseM MemGC) Imm
                                                   (VariantT
                                                     (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                     [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                         (BaseM MemGC) Imm
                                                         (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                       (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                           (BaseM MemGC) Imm
                                                           (ProdT
                                                             (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                               GCRefs)
                                                             [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                               (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                             [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT
                                             [ (VarT 1);
                                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                   (BaseM MemGC) Imm
                                                   (VariantT
                                                     (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                     [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                         (BaseM MemGC) Imm
                                                         (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                       (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                           (BaseM MemGC) Imm
                                                           (ProdT
                                                             (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                               GCRefs)
                                                             [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                               (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                             [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 1);
                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                     (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                       [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                           (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                         (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                           (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                             (BaseM MemGC) Imm
                                             (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                               [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                 (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                               [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                  -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                         (MonoFunT
                                           [ (VarT 1);
                                             (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (BaseM MemGC) Imm
                                                 (VariantT
                                                   (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                   [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                     (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                       (BaseM MemGC) Imm
                                                       (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                     (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                         (BaseM MemGC) Imm
                                                         (ProdT
                                                           (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                             GCRefs)
                                                           [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                             (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                           [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 1);
                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                     (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                       [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                           (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                         (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                           (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                             (BaseM MemGC) Imm
                                             (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                               [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                 (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                               [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 1);
                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                     (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                       [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                           (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                         (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                           (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                             (BaseM MemGC) Imm
                                             (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                               [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                 (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                               [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 1);
                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                     (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                       [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                           (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                         (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                           (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                             (BaseM MemGC) Imm
                                             (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                               [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                 (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                               [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                    (MonoFunT
                                      [ (VarT 1);
                                        (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                          (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                            (BaseM MemGC) Imm
                                            (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                  (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                  (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                    (BaseM MemGC) Imm
                                                    (ProdT
                                                      (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                      [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                         -> []
          load (path 1) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT
                                             [ (VarT 1);
                                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                   (BaseM MemGC) Imm
                                                   (VariantT
                                                     (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                     [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                         (BaseM MemGC) Imm
                                                         (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                       (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                           (BaseM MemGC) Imm
                                                           (ProdT
                                                             (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                               GCRefs)
                                                             [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                               (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                             [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT
                                             [ (VarT 1);
                                               (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                   (BaseM MemGC) Imm
                                                   (VariantT
                                                     (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                     [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                         (BaseM MemGC) Imm
                                                         (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                       (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                           (BaseM MemGC) Imm
                                                           (ProdT
                                                             (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                               GCRefs)
                                                             [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                               (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                             [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))
                                 (coderef (val i32 norefs)
                                   (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                     (MonoFunT
                                       [ (VarT 1);
                                         (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                           (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                             (BaseM MemGC) Imm
                                             (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                               [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                 (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                   (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                 (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                   (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                     (BaseM MemGC) Imm
                                                     (ProdT
                                                       (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                       [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                         (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                       [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
          local.set 4 ;; [(coderef (val i32 norefs)
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                              (MonoFunT
                                [ (VarT 1);
                                  (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                    (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                      (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                          (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                            (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                            (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                              (BaseM MemGC) Imm
                                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
                         -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 1);
                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                     (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                       [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                           (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                         (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                           (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                             (BaseM MemGC) Imm
                                             (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                               [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                 (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                               [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                  -> []
          local.get move 4 ;; [] ->
                              [(coderef (val i32 norefs)
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                   (MonoFunT
                                     [ (VarT 1);
                                       (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                           (BaseM MemGC) Imm
                                           (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                             [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                               (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                               (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                 (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                   (BaseM MemGC) Imm
                                                   (ProdT
                                                     (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                     [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                       (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                     [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
          local.set 5 ;; [(coderef (val i32 norefs)
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                              (MonoFunT
                                [ (VarT 1);
                                  (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                    (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                      (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                          (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                            (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                            (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                              (BaseM MemGC) Imm
                                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
                         -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
          tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
          group ;; [] -> [(prod (val (prod) norefs))]
          new ;; [(prod (val (prod) norefs))] ->
                 [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
          cast ;; [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                  [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
          inject_new 0 ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] ->
                          [(ref (val ptr gcrefs) (base gc) imm
                             (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                               (ser (mem (rep ptr) gcrefs)
                                 (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                               (ser (mem (rep ptr) gcrefs)
                                 (ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                                     (ser (mem (rep ptr) gcrefs)
                                       (rec (val ptr gcrefs)
                                         (ref (val ptr gcrefs) (base gc) imm
                                           (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                             (ser (mem (rep ptr) gcrefs)
                                               (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                             (ser (mem (rep ptr) gcrefs)
                                               (ref (val ptr gcrefs) (base gc) imm
                                                 (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                                   (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                                                   (ser (mem (rep ptr) gcrefs) (var 0))))))))))))))]
          fold ;; [(ref (val ptr gcrefs) (base gc) imm
                     (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                       (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                       (ser (mem (rep ptr) gcrefs)
                         (ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                             (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                             (ser (mem (rep ptr) gcrefs)
                               (rec (val ptr gcrefs)
                                 (ref (val ptr gcrefs) (base gc) imm
                                   (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs)
                                       (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                     (ser (mem (rep ptr) gcrefs)
                                       (ref (val ptr gcrefs) (base gc) imm
                                         (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                                           (ser (mem (rep ptr) gcrefs) (var 0))))))))))))))]
                  ->
                  [(rec (val ptr gcrefs)
                     (ref (val ptr gcrefs) (base gc) imm
                       (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                         (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                         (ser (mem (rep ptr) gcrefs)
                           (ref (val ptr gcrefs) (base gc) imm
                             (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                               (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                               (ser (mem (rep ptr) gcrefs) (var 0))))))))]
          group ;; [(i31 (val ptr norefs))
                    (rec (val ptr gcrefs)
                      (ref (val ptr gcrefs) (base gc) imm
                        (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                          (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                          (ser (mem (rep ptr) gcrefs)
                            (ref (val ptr gcrefs) (base gc) imm
                              (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                                (ser (mem (rep ptr) gcrefs) (var 0))))))))]
                   ->
                   [(prod (val (prod ptr ptr) gcrefs) (i31 (val ptr norefs))
                      (rec (val ptr gcrefs)
                        (ref (val ptr gcrefs) (base gc) imm
                          (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                            (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                            (ser (mem (rep ptr) gcrefs)
                              (ref (val ptr gcrefs) (base gc) imm
                                (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                  (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                                  (ser (mem (rep ptr) gcrefs) (var 0)))))))))]
          new ;; [(prod (val (prod ptr ptr) gcrefs) (i31 (val ptr norefs))
                    (rec (val ptr gcrefs)
                      (ref (val ptr gcrefs) (base gc) imm
                        (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                          (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                          (ser (mem (rep ptr) gcrefs)
                            (ref (val ptr gcrefs) (base gc) imm
                              (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                                (ser (mem (rep ptr) gcrefs) (var 0)))))))))]
                 ->
                 [(ref (val ptr gcrefs) (base gc) imm
                    (ser (mem (rep (prod ptr ptr)) gcrefs)
                      (prod (val (prod ptr ptr) gcrefs) (i31 (val ptr norefs))
                        (rec (val ptr gcrefs)
                          (ref (val ptr gcrefs) (base gc) imm
                            (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                              (ser (mem (rep ptr) gcrefs)
                                (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                              (ser (mem (rep ptr) gcrefs)
                                (ref (val ptr gcrefs) (base gc) imm
                                  (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                    (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                                    (ser (mem (rep ptr) gcrefs) (var 0)))))))))))]
          cast ;; [(ref (val ptr gcrefs) (base gc) imm
                     (ser (mem (rep (prod ptr ptr)) gcrefs)
                       (prod (val (prod ptr ptr) gcrefs) (i31 (val ptr norefs))
                         (rec (val ptr gcrefs)
                           (ref (val ptr gcrefs) (base gc) imm
                             (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                               (ser (mem (rep ptr) gcrefs)
                                 (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                               (ser (mem (rep ptr) gcrefs)
                                 (ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                                     (ser (mem (rep ptr) gcrefs) (var 0)))))))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep ptr)) gcrefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                       (ser (mem (rep ptr) gcrefs)
                         (rec (val ptr gcrefs)
                           (ref (val ptr gcrefs) (base gc) imm
                             (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                               (ser (mem (rep ptr) gcrefs)
                                 (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                               (ser (mem (rep ptr) gcrefs)
                                 (ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                                     (ser (mem (rep ptr) gcrefs) (var 0)))))))))))]
          inject_new 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                             (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                               (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                               (ser (mem (rep ptr) gcrefs)
                                 (rec (val ptr gcrefs)
                                   (ref (val ptr gcrefs) (base gc) imm
                                     (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                       (ser (mem (rep ptr) gcrefs)
                                         (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                       (ser (mem (rep ptr) gcrefs)
                                         (ref (val ptr gcrefs) (base gc) imm
                                           (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                             (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                                             (ser (mem (rep ptr) gcrefs) (var 0)))))))))))]
                          ->
                          [(ref (val ptr gcrefs) (base gc) imm
                             (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                               (ser (mem (rep ptr) gcrefs)
                                 (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                               (ser (mem (rep ptr) gcrefs)
                                 (ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                                     (ser (mem (rep ptr) gcrefs)
                                       (rec (val ptr gcrefs)
                                         (ref (val ptr gcrefs) (base gc) imm
                                           (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                             (ser (mem (rep ptr) gcrefs)
                                               (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                             (ser (mem (rep ptr) gcrefs)
                                               (ref (val ptr gcrefs) (base gc) imm
                                                 (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                                   (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                                                   (ser (mem (rep ptr) gcrefs) (var 0))))))))))))))]
          fold ;; [(ref (val ptr gcrefs) (base gc) imm
                     (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                       (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                       (ser (mem (rep ptr) gcrefs)
                         (ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                             (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                             (ser (mem (rep ptr) gcrefs)
                               (rec (val ptr gcrefs)
                                 (ref (val ptr gcrefs) (base gc) imm
                                   (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs)
                                       (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                     (ser (mem (rep ptr) gcrefs)
                                       (ref (val ptr gcrefs) (base gc) imm
                                         (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                                           (ser (mem (rep ptr) gcrefs) (var 0))))))))))))))]
                  ->
                  [(rec (val ptr gcrefs)
                     (ref (val ptr gcrefs) (base gc) imm
                       (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                         (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                         (ser (mem (rep ptr) gcrefs)
                           (ref (val ptr gcrefs) (base gc) imm
                             (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                               (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                               (ser (mem (rep ptr) gcrefs) (var 0))))))))]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                   (MonoFunT
                                     [ (VarT 1);
                                       (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                           (BaseM MemGC) Imm
                                           (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                             [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                               (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                               (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                 (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                   (BaseM MemGC) Imm
                                                   (ProdT
                                                     (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                     [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                       (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                     [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
          copy ;; [(coderef (val i32 norefs)
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                       (MonoFunT
                         [ (VarT 1);
                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                             (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                               (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                 [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                   (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                     (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                   (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                     (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                       (BaseM MemGC) Imm
                                       (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                         [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                           (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                         [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
                  ->
                  [(coderef (val i32 norefs)
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                       (MonoFunT
                         [ (VarT 1);
                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                             (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                               (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                 [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                   (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                     (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                   (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                     (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                       (BaseM MemGC) Imm
                                       (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                         [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                           (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                         [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))
                   (coderef (val i32 norefs)
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                       (MonoFunT
                         [ (VarT 1);
                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                             (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                               (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                 [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                   (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                     (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                   (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                     (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                       (BaseM MemGC) Imm
                                       (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                         [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                           (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                         [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
          local.set 5 ;; [(coderef (val i32 norefs)
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                              (MonoFunT
                                [ (VarT 1);
                                  (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                    (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                      (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                          (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                            (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                            (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                              (BaseM MemGC) Imm
                                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
                         -> []
          inst (type (i31 (val ptr norefs))) ;; [(coderef (val i32 norefs)
                                                   (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                                     (MonoFunT
                                                       [ (VarT 1);
                                                         (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                                           (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                             (BaseM MemGC) Imm
                                                             (VariantT
                                                               (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                                 GCRefs)
                                                               [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                                 (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                                   (BaseM MemGC) Imm
                                                                   (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                                 (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                                   (RefT
                                                                     (VALTYPE (AtomR PtrR) GCRefs)
                                                                     (BaseM MemGC) Imm
                                                                     (ProdT
                                                                       (MEMTYPE
                                                                        (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                                        GCRefs)
                                                                       [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                                        (SerT
                                                                        (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                                        (VarT 0))])))])))]
                                                       [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
                                                ->
                                                [(coderef (val i32 norefs)
                                                   ((var 0)
                                                   (rec (val ptr gcrefs)
                                                     (ref (val ptr gcrefs)
                                                       (base gc) imm
                                                       (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                                         (ser (mem (rep ptr) gcrefs)
                                                           (ref (val ptr gcrefs)
                                                             (base gc) imm
                                                             (struct (mem (prod) norefs))))
                                                         (ser (mem (rep ptr) gcrefs)
                                                           (ref (val ptr gcrefs)
                                                             (base gc) imm
                                                             (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                                               (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                                                               (ser (mem (rep ptr) gcrefs) (var 0))))))))
                                                   -> (i31 (val ptr norefs))))]
          call_indirect ;; [(var 0)
                            (rec (val ptr gcrefs)
                              (ref (val ptr gcrefs) (base gc) imm
                                (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                  (ser (mem (rep ptr) gcrefs)
                                    (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                  (ser (mem (rep ptr) gcrefs)
                                    (ref (val ptr gcrefs) (base gc) imm
                                      (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                        (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                                        (ser (mem (rep ptr) gcrefs) (var 0))))))))
                            (coderef (val i32 norefs)
                              ((var 0)
                              (rec (val ptr gcrefs)
                                (ref (val ptr gcrefs) (base gc) imm
                                  (variant (mem (sum (rep ptr) (rep ptr)) gcrefs)
                                    (ser (mem (rep ptr) gcrefs)
                                      (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                                    (ser (mem (rep ptr) gcrefs)
                                      (ref (val ptr gcrefs) (base gc) imm
                                        (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                          (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))
                                          (ser (mem (rep ptr) gcrefs) (var 0))))))))
                              -> (i31 (val ptr norefs))))]
                           -> [(i31 (val ptr norefs))]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                   (MonoFunT
                                     [ (VarT 1);
                                       (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                           (BaseM MemGC) Imm
                                           (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                             [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                               (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                               (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                 (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                   (BaseM MemGC) Imm
                                                   (ProdT
                                                     (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                     [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                       (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                     [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
          drop ;; [(coderef (val i32 norefs)
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                       (MonoFunT
                         [ (VarT 1);
                           (RecT (VALTYPE (AtomR PtrR) GCRefs)
                             (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                               (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                 [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                   (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                     (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                   (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                     (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                       (BaseM MemGC) Imm
                                       (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                         [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                           (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                         [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))]
                  -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                         (MonoFunT
                                           [ (VarT 1);
                                             (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                               (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                 (BaseM MemGC) Imm
                                                 (VariantT
                                                   (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                                   [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                     (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                       (BaseM MemGC) Imm
                                                       (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                                     (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                                       (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                                         (BaseM MemGC) Imm
                                                         (ProdT
                                                           (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                             GCRefs)
                                                           [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                             (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                                           [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                             (MonoFunT
                               [ (VarT 1);
                                 (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                   (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                     (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                       [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                         (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                           (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                         (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                           (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                             (BaseM MemGC) Imm
                                             (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                               [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                 (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                               [ (I31T (VALTYPE (AtomR PtrR) NoRefs))]))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                      (ser (mem (rep i32) norefs)
                        (coderef (val i32 norefs)
                          (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                            (MonoFunT
                              [ (VarT 1);
                                (RecT (VALTYPE (AtomR PtrR) GCRefs)
                                  (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                                    (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                        (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                          (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                                          (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                            (BaseM MemGC) Imm
                                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1));
                                                (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))])))])))]
                              [ (I31T (VALTYPE (AtomR PtrR) NoRefs))])))))))]
               -> [(i31 (val ptr norefs))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0 1)
      (export "len" (func 0))
      (export "_start" (func 1)))
    -----------poly_id_apply-----------
    (module
      (func
          (forall.type (VALTYPE (AtomR PtrR) GCRefs)
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])); (VarT 0)]
              [ (VarT 0)]))
        local.get move 1 ;; [] -> [(var 0)]
        copy ;; [(var 0)] -> [(var 0) (var 0)]
        local.set 1 ;; [(var 0)] -> []
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> []
        local.get move 1 ;; [] -> [(var 0)]
        drop ;; [(var 0)] -> [])
      (func
          (forall.type (VALTYPE (AtomR PtrR) GCRefs)
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) [])); (VarT 0)]
              [ (VarT 0)]))
          (local ptr ptr ptr ptr ptr)
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                              (VarT 0)]
                            [ (VarT 0)])))]
        group ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                      (MonoFunT
                        [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                          (VarT 0)]
                        [ (VarT 0)])))]
                 ->
                 [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (coderef (val i32 norefs)
                      (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                        (MonoFunT
                          [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                            (VarT 0)]
                          [ (VarT 0)]))))]
        new ;; [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                      (MonoFunT
                        [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                          (VarT 0)]
                        [ (VarT 0)]))))]
               ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr i32)) gcrefs)
                    (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (coderef (val i32 norefs)
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                              (VarT 0)]
                            [ (VarT 0)]))))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr i32)) gcrefs)
                     (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                       (coderef (val i32 norefs)
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT
                             [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                               (VarT 0)]
                             [ (VarT 0)]))))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT
                             [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                               (VarT 0)]
                             [ (VarT 0)]))))))]
        pack ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT
                             [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                               (VarT 0)]
                             [ (VarT 0)]))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))))))]
        unpack (localfx [0 => (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
                 [1 => (var 0)] [2 => (plug (val (prod i32) norefs) (prod i32))]
                 [3 => (plug (val (prod i32) norefs) (prod i32))] [4 => (plug (val (prod i32) norefs) (prod i32))]
                 [5 => (plug (val (prod i32) norefs) (prod i32))] [6 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 2 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                         -> []
          local.get move 2 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          local.set 2 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                         -> []
          load (path 0) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                                 (var 0)]
          local.set 3 ;; [(var 0)] -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  -> []
          local.get move 3 ;; [] -> [(var 0)]
          local.set 4 ;; [(var 0)] -> []
          local.get move 2 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          local.set 2 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                         -> []
          load (path 1) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                                 (coderef (val i32 norefs)
                                   (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          local.set 5 ;; [(coderef (val i32 norefs)
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                         -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  -> []
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          local.set 6 ;; [(coderef (val i32 norefs)
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                         -> []
          local.get move 4 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 4 ;; [(var 0)] -> []
          local.get move 1 ;; [] -> [(var 1)]
          copy ;; [(var 1)] -> [(var 1) (var 1)]
          local.set 1 ;; [(var 1)] -> []
          local.get move 6 ;; [] ->
                              [(coderef (val i32 norefs)
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          copy ;; [(coderef (val i32 norefs)
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                  ->
                  [(coderef (val i32 norefs)
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))
                   (coderef (val i32 norefs)
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          local.set 6 ;; [(coderef (val i32 norefs)
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                         -> []
          inst (type (var 1)) ;; [(coderef (val i32 norefs)
                                    (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                                 -> [(coderef (val i32 norefs) ((var 0) (var 1) -> (var 1)))]
          call_indirect ;; [(var 0) (var 1) (coderef (val i32 norefs) ((var 0) (var 1) -> (var 1)))] -> [(var 1)]
          local.get move 6 ;; [] ->
                              [(coderef (val i32 norefs)
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          drop ;; [(coderef (val i32 norefs)
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                  -> []
          local.get move 4 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 2 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                      (ser (mem (rep i32) norefs)
                        (coderef (val i32 norefs)
                          (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))))))]
               -> [(var 0)]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> []
        local.get move 1 ;; [] -> [(var 0)]
        drop ;; [(var 0)] -> [])
      (func ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs))) (local ptr ptr
          ptr ptr ptr)
        group ;; [] -> [(prod (val (prod) norefs))]
        new ;; [(prod (val (prod) norefs))] ->
               [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        coderef 1 ;; [] ->
                     [(coderef (val i32 norefs)
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                              (VarT 0)]
                            [ (VarT 0)])))]
        group ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                      (MonoFunT
                        [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                          (VarT 0)]
                        [ (VarT 0)])))]
                 ->
                 [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                    (coderef (val i32 norefs)
                      (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                        (MonoFunT
                          [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                            (VarT 0)]
                          [ (VarT 0)]))))]
        new ;; [(prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                  (coderef (val i32 norefs)
                    (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                      (MonoFunT
                        [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                          (VarT 0)]
                        [ (VarT 0)]))))]
               ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr i32)) gcrefs)
                    (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                      (coderef (val i32 norefs)
                        (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                              (VarT 0)]
                            [ (VarT 0)]))))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr i32)) gcrefs)
                     (prod (val (prod ptr i32) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                       (coderef (val i32 norefs)
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT
                             [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                               (VarT 0)]
                             [ (VarT 0)]))))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT
                             [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                               (VarT 0)]
                             [ (VarT 0)]))))))]
        pack ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                           (MonoFunT
                             [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                               (VarT 0)]
                             [ (VarT 0)]))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))))))]
        unpack (localfx [0 => (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
                 [1 => (plug (val (prod i32) norefs) (prod i32))] [2 => (plug (val (prod i32) norefs) (prod i32))]
                 [3 => (plug (val (prod i32) norefs) (prod i32))] [4 => (plug (val (prod i32) norefs) (prod i32))]
                 [5 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                         -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                         -> []
          load (path 0) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                                 (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  -> []
          local.get move 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                         -> []
          load (path 1) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                           (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))
                                 (coderef (val i32 norefs)
                                   (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          local.set 4 ;; [(coderef (val i32 norefs)
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                         -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  -> []
          local.get move 4 ;; [] ->
                              [(coderef (val i32 norefs)
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          local.set 5 ;; [(coderef (val i32 norefs)
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                         -> []
          local.get move 3 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 3 ;; [(var 0)] -> []
          num_const 5 ;; [] -> [(num (val i32 norefs) i32)]
          tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          copy ;; [(coderef (val i32 norefs)
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                  ->
                  [(coderef (val i32 norefs)
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))
                   (coderef (val i32 norefs)
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          local.set 5 ;; [(coderef (val i32 norefs)
                            (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                         -> []
          inst (type (i31 (val ptr norefs))) ;; [(coderef (val i32 norefs)
                                                   (forall.type (VALTYPE (AtomR PtrR) GCRefs)
                                                     (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                                                ->
                                                [(coderef (val i32 norefs)
                                                   ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
          call_indirect ;; [(var 0) (i31 (val ptr norefs))
                            (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
                           -> [(i31 (val ptr norefs))]
          local.get move 5 ;; [] ->
                              [(coderef (val i32 norefs)
                                 (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
          drop ;; [(coderef (val i32 norefs)
                     (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))]
                  -> []
          local.get move 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 1 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)]))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                      (ser (mem (rep i32) norefs)
                        (coderef (val i32 norefs)
                          (forall.type (VALTYPE (AtomR PtrR) GCRefs) (MonoFunT [ (VarT 1); (VarT 0)] [ (VarT 0)])))))))]
               -> [(i31 (val ptr norefs))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0 1 2)
      (export "id" (func 0))
      (export "apply" (func 1))
      (export "_start" (func 2)))
    -----------mini_zip-----------
    (module
      (func
          (forall.type (VALTYPE (AtomR PtrR) GCRefs)
            (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
              (MonoFunT
                [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm (ProdT (MEMTYPE (ProdS []) NoRefs) []));
                  (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                        (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Mut
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                          (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Mut
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1))))]))]
                [ (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Mut
                  (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs)
                    (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) GCRefs)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 1))]))))])))
          (local ptr ptr ptr ptr)
        local.get move 1 ;; [] ->
                            [(ref (val ptr gcrefs) (base gc) imm
                               (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                 (ser (mem (rep ptr) gcrefs)
                                   (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0))))
                                 (ser (mem (rep ptr) gcrefs)
                                   (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1))))))]
        copy ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0))))
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1))))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0))))
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1))))))
                 (ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0))))
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1))))))]
        local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                          (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                            (ser (mem (rep ptr) gcrefs)
                              (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0))))
                            (ser (mem (rep ptr) gcrefs)
                              (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1))))))]
                       -> []
        load (path 0) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs)
                                     (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0))))
                                   (ser (mem (rep ptr) gcrefs)
                                     (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1))))))]
                              ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs)
                                     (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0))))
                                   (ser (mem (rep ptr) gcrefs)
                                     (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1))))))
                               (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0)))]
        local.set 2 ;; [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0)))] -> []
        drop ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0))))
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1))))))]
                -> []
        local.get move 2 ;; [] -> [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0)))]
        load (path) copy ;; [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0)))] ->
                            [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0))) (var 0)]
        local.set 3 ;; [(var 0)] -> []
        drop ;; [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0)))] -> []
        local.get move 3 ;; [] -> [(var 0)]
        local.get move 1 ;; [] ->
                            [(ref (val ptr gcrefs) (base gc) imm
                               (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                 (ser (mem (rep ptr) gcrefs)
                                   (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0))))
                                 (ser (mem (rep ptr) gcrefs)
                                   (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1))))))]
        copy ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0))))
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1))))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0))))
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1))))))
                 (ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0))))
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1))))))]
        local.set 1 ;; [(ref (val ptr gcrefs) (base gc) imm
                          (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                            (ser (mem (rep ptr) gcrefs)
                              (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0))))
                            (ser (mem (rep ptr) gcrefs)
                              (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1))))))]
                       -> []
        load (path 1) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs)
                                     (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0))))
                                   (ser (mem (rep ptr) gcrefs)
                                     (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1))))))]
                              ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs)
                                     (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0))))
                                   (ser (mem (rep ptr) gcrefs)
                                     (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1))))))
                               (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1)))]
        local.set 4 ;; [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1)))] -> []
        drop ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0))))
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1))))))]
                -> []
        local.get move 4 ;; [] -> [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1)))]
        load (path) copy ;; [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1)))] ->
                            [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1))) (var 1)]
        local.set 5 ;; [(var 1)] -> []
        drop ;; [(ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1)))] -> []
        local.get move 5 ;; [] -> [(var 1)]
        group ;; [(var 0) (var 1)] -> [(prod (val (prod ptr ptr) gcrefs) (var 0) (var 1))]
        new ;; [(prod (val (prod ptr ptr) gcrefs) (var 0) (var 1))] ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr ptr)) gcrefs) (prod (val (prod ptr ptr) gcrefs) (var 0) (var 1))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr ptr)) gcrefs) (prod (val (prod ptr ptr) gcrefs) (var 0) (var 1))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                     (ser (mem (rep ptr) gcrefs) (var 1))))]
        new ;; [(ref (val ptr gcrefs) (base gc) imm
                  (struct (mem (prod (rep ptr) (rep ptr)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                    (ser (mem (rep ptr) gcrefs) (var 1))))]
               ->
               [(ref (val ptr gcrefs) (base gc) mut
                  (ser (mem (rep ptr) gcrefs)
                    (ref (val ptr gcrefs) (base gc) imm
                      (struct (mem (prod (rep ptr) (rep ptr)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                        (ser (mem (rep ptr) gcrefs) (var 1))))))]
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> []
        local.get move 1 ;; [] ->
                            [(ref (val ptr gcrefs) (base gc) imm
                               (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                 (ser (mem (rep ptr) gcrefs)
                                   (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0))))
                                 (ser (mem (rep ptr) gcrefs)
                                   (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1))))))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 0))))
                     (ser (mem (rep ptr) gcrefs) (ref (val ptr gcrefs) (base gc) mut (ser (mem (rep ptr) gcrefs) (var 1))))))]
                -> [])
      (table 0)
      (export "mini_zip" (func 0)))
    -----------closure_simpl-----------
    (module
      (func
          ((ref (val ptr gcrefs) (base gc) imm
             (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
          (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
          (i31 (val ptr norefs))) (local ptr ptr)
        local.get move 0 ;; [] ->
                            [(ref (val ptr gcrefs) (base gc) imm
                               (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        copy ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                 (ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        local.set 0 ;; [(ref (val ptr gcrefs) (base gc) imm
                          (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                       -> []
        load (path 0) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                              ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                               (i31 (val ptr norefs))]
        local.set 2 ;; [(i31 (val ptr norefs))] -> []
        drop ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                -> []
        local.get move 2 ;; [] -> [(i31 (val ptr norefs))]
        local.set 3 ;; [(i31 (val ptr norefs))] -> []
        local.get move 3 ;; [] -> [(i31 (val ptr norefs))]
        copy ;; [(i31 (val ptr norefs))] -> [(i31 (val ptr norefs)) (i31 (val ptr norefs))]
        local.set 3 ;; [(i31 (val ptr norefs))] -> []
        local.get move 3 ;; [] -> [(i31 (val ptr norefs))]
        drop ;; [(i31 (val ptr norefs))] -> []
        local.get move 0 ;; [] ->
                            [(ref (val ptr gcrefs) (base gc) imm
                               (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                -> []
        local.get move 1 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (func ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs))) (local ptr ptr
          ptr ptr ptr ptr ptr)
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        local.set 1 ;; [(i31 (val ptr norefs))] -> []
        local.get move 1 ;; [] -> [(i31 (val ptr norefs))]
        copy ;; [(i31 (val ptr norefs))] -> [(i31 (val ptr norefs)) (i31 (val ptr norefs))]
        local.set 1 ;; [(i31 (val ptr norefs))] -> []
        group ;; [(i31 (val ptr norefs))] -> [(prod (val (prod ptr) norefs) (i31 (val ptr norefs)))]
        new ;; [(prod (val (prod ptr) norefs) (i31 (val ptr norefs)))] ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr)) norefs) (prod (val (prod ptr) norefs) (i31 (val ptr norefs)))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr)) norefs) (prod (val (prod ptr) norefs) (i31 (val ptr norefs)))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                        (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                        (i31 (val ptr norefs))))]
        group ;; [(ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm
                       (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                    (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                    (i31 (val ptr norefs))))]
                 ->
                 [(prod (val (prod ptr i32) gcrefs)
                    (ref (val ptr gcrefs) (base gc) imm
                      (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                    (coderef (val i32 norefs)
                      ((ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                      (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                      (i31 (val ptr norefs)))))]
        new ;; [(prod (val (prod ptr i32) gcrefs)
                  (ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm
                       (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                    (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                    (i31 (val ptr norefs)))))]
               ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr i32)) gcrefs)
                    (prod (val (prod ptr i32) gcrefs)
                      (ref (val ptr gcrefs) (base gc) imm
                        (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                      (coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                        (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                        (i31 (val ptr norefs)))))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr i32)) gcrefs)
                     (prod (val (prod ptr i32) gcrefs)
                       (ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                         (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                         (i31 (val ptr norefs)))))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs)
                       (ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                         (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                         (i31 (val ptr norefs)))))))]
        pack ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs)
                       (ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                         (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                         (i31 (val ptr norefs)))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs))))))))]
        local.set 2 ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                  (i31 (val ptr norefs))))))))]
                       -> []
        local.get move 2 ;; [] ->
                            [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                       (i31 (val ptr norefs))))))))]
        copy ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs))))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs))))))))
                 (exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs))))))))]
        local.set 2 ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                  (i31 (val ptr norefs))))))))]
                       -> []
        unpack (localfx [0 => (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
                 [1 => (i31 (val ptr norefs))]
                 [2 =>
                 (exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs))))))))]
                 [3 => (plug (val (prod i32) norefs) (prod i32))] [4 => (plug (val (prod i32) norefs) (prod i32))]
                 [5 => (plug (val (prod i32) norefs) (prod i32))] [6 => (plug (val (prod i32) norefs) (prod i32))]
                 [7 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 3 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                  (i31 (val ptr norefs)))))))]
                         -> []
          local.get move 3 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                       (i31 (val ptr norefs)))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs)))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs)))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs)))))))]
          local.set 3 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                  (i31 (val ptr norefs)))))))]
                         -> []
          load (path 0) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                         (i31 (val ptr norefs)))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                         (i31 (val ptr norefs)))))))
                                 (var 0)]
          local.set 4 ;; [(var 0)] -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs)))))))]
                  -> []
          local.get move 4 ;; [] -> [(var 0)]
          local.set 5 ;; [(var 0)] -> []
          local.get move 3 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                       (i31 (val ptr norefs)))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs)))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs)))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs)))))))]
          local.set 3 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs)
                                  ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                  (i31 (val ptr norefs)))))))]
                         -> []
          load (path 1) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                         (i31 (val ptr norefs)))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                         (i31 (val ptr norefs)))))))
                                 (coderef (val i32 norefs)
                                   ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                   (i31 (val ptr norefs))))]
          local.set 6 ;; [(coderef (val i32 norefs)
                            ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                            (i31 (val ptr norefs))))]
                         -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs)))))))]
                  -> []
          local.get move 6 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                 (i31 (val ptr norefs))))]
          local.set 7 ;; [(coderef (val i32 norefs)
                            ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                            (i31 (val ptr norefs))))]
                         -> []
          local.get move 5 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 5 ;; [(var 0)] -> []
          group ;; [] -> [(prod (val (prod) norefs))]
          new ;; [(prod (val (prod) norefs))] ->
                 [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))]
          cast ;; [(ref (val ptr gcrefs) (base gc) imm (ser (mem (rep (prod)) norefs) (prod (val (prod) norefs))))] ->
                  [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
          local.get move 7 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                 (i31 (val ptr norefs))))]
          copy ;; [(coderef (val i32 norefs)
                     ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs))))]
                  ->
                  [(coderef (val i32 norefs)
                     ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs))))
                   (coderef (val i32 norefs)
                     ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs))))]
          local.set 7 ;; [(coderef (val i32 norefs)
                            ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                            (i31 (val ptr norefs))))]
                         -> []
          call_indirect ;; [(var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))
                            (coderef (val i32 norefs)
                              ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                              (i31 (val ptr norefs))))]
                           -> [(i31 (val ptr norefs))]
          local.get move 7 ;; [] ->
                              [(coderef (val i32 norefs)
                                 ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                 (i31 (val ptr norefs))))]
          drop ;; [(coderef (val i32 norefs)
                     ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs))))]
                  -> []
          local.get move 5 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 3 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                       (i31 (val ptr norefs)))))))]
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs)))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                      (ser (mem (rep i32) norefs)
                        (coderef (val i32 norefs)
                          ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                          (i31 (val ptr norefs))))))))]
               -> [(i31 (val ptr norefs))]
        local.get move 2 ;; [] ->
                            [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs)
                                       ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                                       (i31 (val ptr norefs))))))))]
        drop ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs)
                           ((var 0) (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) ->
                           (i31 (val ptr norefs))))))))]
                -> []
        local.get move 1 ;; [] -> [(i31 (val ptr norefs))]
        drop ;; [(i31 (val ptr norefs))] -> []
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0 1)
      (export "_start" (func 1)))
    -----------closure_complex-----------
    (module
      (func
          ((ref (val ptr gcrefs) (base gc) imm
             (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
               (ser (mem (rep ptr) gcrefs)
                 (exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
               (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
          (i31 (val ptr norefs)) -> (i31 (val ptr norefs))) (local ptr ptr ptr ptr ptr ptr ptr ptr ptr)
        local.get move 0 ;; [] ->
                            [(ref (val ptr gcrefs) (base gc) imm
                               (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                 (ser (mem (rep ptr) gcrefs)
                                   (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                     (ref (val ptr gcrefs) (base gc) imm
                                       (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                         (ser (mem (rep ptr) gcrefs) (var 0))
                                         (ser (mem (rep i32) norefs)
                                           (coderef (val i32 norefs)
                                             ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                                 (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        copy ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs)
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                             (ser (mem (rep ptr) gcrefs) (var 0))
                             (ser (mem (rep i32) norefs)
                               (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs)
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                             (ser (mem (rep ptr) gcrefs) (var 0))
                             (ser (mem (rep i32) norefs)
                               (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                 (ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs)
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                             (ser (mem (rep ptr) gcrefs) (var 0))
                             (ser (mem (rep i32) norefs)
                               (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        local.set 0 ;; [(ref (val ptr gcrefs) (base gc) imm
                          (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                            (ser (mem (rep ptr) gcrefs)
                              (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                (ref (val ptr gcrefs) (base gc) imm
                                  (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                    (ser (mem (rep ptr) gcrefs) (var 0))
                                    (ser (mem (rep i32) norefs)
                                      (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                            (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                       -> []
        load (path 0) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs)
                                     (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                       (ref (val ptr gcrefs) (base gc) imm
                                         (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                           (ser (mem (rep ptr) gcrefs) (var 0))
                                           (ser (mem (rep i32) norefs)
                                             (coderef (val i32 norefs)
                                               ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                                   (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                              ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs)
                                     (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                       (ref (val ptr gcrefs) (base gc) imm
                                         (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                           (ser (mem (rep ptr) gcrefs) (var 0))
                                           (ser (mem (rep i32) norefs)
                                             (coderef (val i32 norefs)
                                               ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                                   (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                               (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                 (ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
        local.set 2 ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
                       -> []
        drop ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs)
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                             (ser (mem (rep ptr) gcrefs) (var 0))
                             (ser (mem (rep i32) norefs)
                               (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                -> []
        local.get move 2 ;; [] ->
                            [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
        local.set 3 ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
                       -> []
        local.get move 0 ;; [] ->
                            [(ref (val ptr gcrefs) (base gc) imm
                               (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                 (ser (mem (rep ptr) gcrefs)
                                   (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                     (ref (val ptr gcrefs) (base gc) imm
                                       (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                         (ser (mem (rep ptr) gcrefs) (var 0))
                                         (ser (mem (rep i32) norefs)
                                           (coderef (val i32 norefs)
                                             ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                                 (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        copy ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs)
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                             (ser (mem (rep ptr) gcrefs) (var 0))
                             (ser (mem (rep i32) norefs)
                               (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs)
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                             (ser (mem (rep ptr) gcrefs) (var 0))
                             (ser (mem (rep i32) norefs)
                               (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                 (ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs)
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                             (ser (mem (rep ptr) gcrefs) (var 0))
                             (ser (mem (rep i32) norefs)
                               (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        local.set 0 ;; [(ref (val ptr gcrefs) (base gc) imm
                          (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                            (ser (mem (rep ptr) gcrefs)
                              (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                (ref (val ptr gcrefs) (base gc) imm
                                  (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                    (ser (mem (rep ptr) gcrefs) (var 0))
                                    (ser (mem (rep i32) norefs)
                                      (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                            (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                       -> []
        load (path 1) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs)
                                     (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                       (ref (val ptr gcrefs) (base gc) imm
                                         (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                           (ser (mem (rep ptr) gcrefs) (var 0))
                                           (ser (mem (rep i32) norefs)
                                             (coderef (val i32 norefs)
                                               ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                                   (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                              ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs)
                                     (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                       (ref (val ptr gcrefs) (base gc) imm
                                         (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                           (ser (mem (rep ptr) gcrefs) (var 0))
                                           (ser (mem (rep i32) norefs)
                                             (coderef (val i32 norefs)
                                               ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                                   (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                               (i31 (val ptr norefs))]
        local.set 4 ;; [(i31 (val ptr norefs))] -> []
        drop ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs)
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                             (ser (mem (rep ptr) gcrefs) (var 0))
                             (ser (mem (rep i32) norefs)
                               (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                -> []
        local.get move 4 ;; [] -> [(i31 (val ptr norefs))]
        local.set 5 ;; [(i31 (val ptr norefs))] -> []
        local.get move 3 ;; [] ->
                            [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
        copy ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))
                 (exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
        local.set 3 ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
                       -> []
        unpack (localfx
                 [0 =>
                 (ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs)
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                             (ser (mem (rep ptr) gcrefs) (var 0))
                             (ser (mem (rep i32) norefs)
                               (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                 [1 => (i31 (val ptr norefs))] [2 => (plug (val (prod i32) norefs) (prod i32))]
                 [3 =>
                 (exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
                 [4 => (plug (val (prod i32) norefs) (prod i32))] [5 => (i31 (val ptr norefs))]
                 [6 => (plug (val (prod i32) norefs) (prod i32))] [7 => (plug (val (prod i32) norefs) (prod i32))]
                 [8 => (plug (val (prod i32) norefs) (prod i32))] [9 => (plug (val (prod i32) norefs) (prod i32))]
                 [10 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 6 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                         -> []
          local.get move 6 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
          local.set 6 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                         -> []
          load (path 0) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))
                                 (var 0)]
          local.set 7 ;; [(var 0)] -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                  -> []
          local.get move 7 ;; [] -> [(var 0)]
          local.set 8 ;; [(var 0)] -> []
          local.get move 6 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
          local.set 6 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                         -> []
          load (path 1) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))
                                 (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
          local.set 9 ;; [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))] -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                  -> []
          local.get move 9 ;; [] -> [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
          local.set 10 ;; [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))] -> []
          local.get move 8 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 8 ;; [(var 0)] -> []
          local.get move 1 ;; [] -> [(i31 (val ptr norefs))]
          copy ;; [(i31 (val ptr norefs))] -> [(i31 (val ptr norefs)) (i31 (val ptr norefs))]
          local.set 1 ;; [(i31 (val ptr norefs))] -> []
          local.get move 10 ;; [] ->
                               [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
          copy ;; [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))] ->
                  [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))
                   (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
          local.set 10 ;; [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))] -> []
          call_indirect ;; [(var 0) (i31 (val ptr norefs))
                            (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
                           -> [(i31 (val ptr norefs))]
          local.get move 10 ;; [] ->
                               [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
          drop ;; [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))] -> []
          local.get move 8 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 6 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                      (ser (mem (rep i32) norefs)
                        (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
               -> [(i31 (val ptr norefs))]
        untag ;; [(i31 (val ptr norefs))] -> [(num (val i32 norefs) i32)]
        local.get move 5 ;; [] -> [(i31 (val ptr norefs))]
        copy ;; [(i31 (val ptr norefs))] -> [(i31 (val ptr norefs)) (i31 (val ptr norefs))]
        local.set 5 ;; [(i31 (val ptr norefs))] -> []
        untag ;; [(i31 (val ptr norefs))] -> [(num (val i32 norefs) i32)]
        i32.add ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        local.get move 5 ;; [] -> [(i31 (val ptr norefs))]
        drop ;; [(i31 (val ptr norefs))] -> []
        local.get move 3 ;; [] ->
                            [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
        drop ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
                -> []
        local.get move 0 ;; [] ->
                            [(ref (val ptr gcrefs) (base gc) imm
                               (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                                 (ser (mem (rep ptr) gcrefs)
                                   (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                     (ref (val ptr gcrefs) (base gc) imm
                                       (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                         (ser (mem (rep ptr) gcrefs) (var 0))
                                         (ser (mem (rep i32) norefs)
                                           (coderef (val i32 norefs)
                                             ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                                 (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs)
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                             (ser (mem (rep ptr) gcrefs) (var 0))
                             (ser (mem (rep i32) norefs)
                               (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                -> []
        local.get move 1 ;; [] -> [(i31 (val ptr norefs))]
        drop ;; [(i31 (val ptr norefs))] -> [])
      (func
          ((ref (val ptr gcrefs) (base gc) imm
             (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
          (i31 (val ptr norefs)) -> (i31 (val ptr norefs))) (local ptr ptr)
        local.get move 0 ;; [] ->
                            [(ref (val ptr gcrefs) (base gc) imm
                               (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        copy ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                 (ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        local.set 0 ;; [(ref (val ptr gcrefs) (base gc) imm
                          (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                       -> []
        load (path 0) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                              ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                               (i31 (val ptr norefs))]
        local.set 2 ;; [(i31 (val ptr norefs))] -> []
        drop ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                -> []
        local.get move 2 ;; [] -> [(i31 (val ptr norefs))]
        local.set 3 ;; [(i31 (val ptr norefs))] -> []
        local.get move 3 ;; [] -> [(i31 (val ptr norefs))]
        copy ;; [(i31 (val ptr norefs))] -> [(i31 (val ptr norefs)) (i31 (val ptr norefs))]
        local.set 3 ;; [(i31 (val ptr norefs))] -> []
        untag ;; [(i31 (val ptr norefs))] -> [(num (val i32 norefs) i32)]
        local.get move 1 ;; [] -> [(i31 (val ptr norefs))]
        copy ;; [(i31 (val ptr norefs))] -> [(i31 (val ptr norefs)) (i31 (val ptr norefs))]
        local.set 1 ;; [(i31 (val ptr norefs))] -> []
        untag ;; [(i31 (val ptr norefs))] -> [(num (val i32 norefs) i32)]
        i32.add ;; [(num (val i32 norefs) i32) (num (val i32 norefs) i32)] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        local.get move 3 ;; [] -> [(i31 (val ptr norefs))]
        drop ;; [(i31 (val ptr norefs))] -> []
        local.get move 0 ;; [] ->
                            [(ref (val ptr gcrefs) (base gc) imm
                               (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
                -> []
        local.get move 1 ;; [] -> [(i31 (val ptr norefs))]
        drop ;; [(i31 (val ptr norefs))] -> [])
      (func ((ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs))) -> (i31 (val ptr norefs))) (local ptr ptr
          ptr ptr ptr ptr ptr ptr)
        num_const 1 ;; [] -> [(num (val i32 norefs) i32)]
        tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
        local.set 1 ;; [(i31 (val ptr norefs))] -> []
        local.get move 1 ;; [] -> [(i31 (val ptr norefs))]
        copy ;; [(i31 (val ptr norefs))] -> [(i31 (val ptr norefs)) (i31 (val ptr norefs))]
        local.set 1 ;; [(i31 (val ptr norefs))] -> []
        group ;; [(i31 (val ptr norefs))] -> [(prod (val (prod ptr) norefs) (i31 (val ptr norefs)))]
        new ;; [(prod (val (prod ptr) norefs) (i31 (val ptr norefs)))] ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr)) norefs) (prod (val (prod ptr) norefs) (i31 (val ptr norefs)))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr)) norefs) (prod (val (prod ptr) norefs) (i31 (val ptr norefs)))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        coderef 1 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                        (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
        group ;; [(ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm
                       (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                    (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
                 ->
                 [(prod (val (prod ptr i32) gcrefs)
                    (ref (val ptr gcrefs) (base gc) imm
                      (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                    (coderef (val i32 norefs)
                      ((ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                      (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))]
        new ;; [(prod (val (prod ptr i32) gcrefs)
                  (ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm
                       (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                    (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))]
               ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr i32)) gcrefs)
                    (prod (val (prod ptr i32) gcrefs)
                      (ref (val ptr gcrefs) (base gc) imm
                        (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                      (coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                        (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr i32)) gcrefs)
                     (prod (val (prod ptr i32) gcrefs)
                       (ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                         (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs)
                       (ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                         (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
        pack ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs)
                       (ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr)) norefs) (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                         (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
        local.set 2 ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
                       -> []
        local.get move 2 ;; [] ->
                            [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
        copy ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))
                 (exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
        local.set 2 ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
                       -> []
        local.get move 1 ;; [] -> [(i31 (val ptr norefs))]
        copy ;; [(i31 (val ptr norefs))] -> [(i31 (val ptr norefs)) (i31 (val ptr norefs))]
        local.set 1 ;; [(i31 (val ptr norefs))] -> []
        group ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                    (ref (val ptr gcrefs) (base gc) imm
                      (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                        (ser (mem (rep i32) norefs)
                          (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))
                  (i31 (val ptr norefs))]
                 ->
                 [(prod (val (prod ptr ptr) gcrefs)
                    (exists.type (val ptr gcrefs) (val ptr gcrefs)
                      (ref (val ptr gcrefs) (base gc) imm
                        (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                          (ser (mem (rep i32) norefs)
                            (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))
                    (i31 (val ptr norefs)))]
        new ;; [(prod (val (prod ptr ptr) gcrefs)
                  (exists.type (val ptr gcrefs) (val ptr gcrefs)
                    (ref (val ptr gcrefs) (base gc) imm
                      (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                        (ser (mem (rep i32) norefs)
                          (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))
                  (i31 (val ptr norefs)))]
               ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr ptr)) gcrefs)
                    (prod (val (prod ptr ptr) gcrefs)
                      (exists.type (val ptr gcrefs) (val ptr gcrefs)
                        (ref (val ptr gcrefs) (base gc) imm
                          (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                            (ser (mem (rep ptr) gcrefs) (var 0))
                            (ser (mem (rep i32) norefs)
                              (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))
                      (i31 (val ptr norefs)))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr ptr)) gcrefs)
                     (prod (val (prod ptr ptr) gcrefs)
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                             (ser (mem (rep ptr) gcrefs) (var 0))
                             (ser (mem (rep i32) norefs)
                               (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))
                       (i31 (val ptr norefs)))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                     (ser (mem (rep ptr) gcrefs)
                       (exists.type (val ptr gcrefs) (val ptr gcrefs)
                         (ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                             (ser (mem (rep ptr) gcrefs) (var 0))
                             (ser (mem (rep i32) norefs)
                               (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                     (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))]
        coderef 0 ;; [] ->
                     [(coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                             (ser (mem (rep ptr) gcrefs)
                               (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                 (ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                             (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                        (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
        group ;; [(ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                      (ser (mem (rep ptr) gcrefs)
                        (exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                      (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm
                       (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                         (ser (mem (rep ptr) gcrefs)
                           (exists.type (val ptr gcrefs) (val ptr gcrefs)
                             (ref (val ptr gcrefs) (base gc) imm
                               (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                 (ser (mem (rep ptr) gcrefs) (var 0))
                                 (ser (mem (rep i32) norefs)
                                   (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                         (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                    (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
                 ->
                 [(prod (val (prod ptr i32) gcrefs)
                    (ref (val ptr gcrefs) (base gc) imm
                      (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                        (ser (mem (rep ptr) gcrefs)
                          (exists.type (val ptr gcrefs) (val ptr gcrefs)
                            (ref (val ptr gcrefs) (base gc) imm
                              (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                (ser (mem (rep ptr) gcrefs) (var 0))
                                (ser (mem (rep i32) norefs)
                                  (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                        (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                    (coderef (val i32 norefs)
                      ((ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                           (ser (mem (rep ptr) gcrefs)
                             (exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                      (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))]
        new ;; [(prod (val (prod ptr i32) gcrefs)
                  (ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                      (ser (mem (rep ptr) gcrefs)
                        (exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                      (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                  (coderef (val i32 norefs)
                    ((ref (val ptr gcrefs) (base gc) imm
                       (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                         (ser (mem (rep ptr) gcrefs)
                           (exists.type (val ptr gcrefs) (val ptr gcrefs)
                             (ref (val ptr gcrefs) (base gc) imm
                               (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                 (ser (mem (rep ptr) gcrefs) (var 0))
                                 (ser (mem (rep i32) norefs)
                                   (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                         (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                    (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))]
               ->
               [(ref (val ptr gcrefs) (base gc) imm
                  (ser (mem (rep (prod ptr i32)) gcrefs)
                    (prod (val (prod ptr i32) gcrefs)
                      (ref (val ptr gcrefs) (base gc) imm
                        (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                          (ser (mem (rep ptr) gcrefs)
                            (exists.type (val ptr gcrefs) (val ptr gcrefs)
                              (ref (val ptr gcrefs) (base gc) imm
                                (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                  (ser (mem (rep ptr) gcrefs) (var 0))
                                  (ser (mem (rep i32) norefs)
                                    (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                          (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                      (coderef (val i32 norefs)
                        ((ref (val ptr gcrefs) (base gc) imm
                           (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                             (ser (mem (rep ptr) gcrefs)
                               (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                 (ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                             (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                        (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
        cast ;; [(ref (val ptr gcrefs) (base gc) imm
                   (ser (mem (rep (prod ptr i32)) gcrefs)
                     (prod (val (prod ptr i32) gcrefs)
                       (ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                           (ser (mem (rep ptr) gcrefs)
                             (exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                              (ser (mem (rep ptr) gcrefs)
                                (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                  (ref (val ptr gcrefs) (base gc) imm
                                    (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                      (ser (mem (rep ptr) gcrefs) (var 0))
                                      (ser (mem (rep i32) norefs)
                                        (coderef (val i32 norefs)
                                          ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                              (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                         (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                ->
                [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs)
                       (ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                           (ser (mem (rep ptr) gcrefs)
                             (exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                              (ser (mem (rep ptr) gcrefs)
                                (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                  (ref (val ptr gcrefs) (base gc) imm
                                    (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                      (ser (mem (rep ptr) gcrefs) (var 0))
                                      (ser (mem (rep i32) norefs)
                                        (coderef (val i32 norefs)
                                          ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                              (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                         (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
        pack ;; [(ref (val ptr gcrefs) (base gc) imm
                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                     (ser (mem (rep ptr) gcrefs)
                       (ref (val ptr gcrefs) (base gc) imm
                         (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                           (ser (mem (rep ptr) gcrefs)
                             (exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                           (ser (mem (rep ptr) norefs) (i31 (val ptr norefs))))))
                     (ser (mem (rep i32) norefs)
                       (coderef (val i32 norefs)
                         ((ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep ptr)) gcrefs)
                              (ser (mem (rep ptr) gcrefs)
                                (exists.type (val ptr gcrefs) (val ptr gcrefs)
                                  (ref (val ptr gcrefs) (base gc) imm
                                    (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                      (ser (mem (rep ptr) gcrefs) (var 0))
                                      (ser (mem (rep i32) norefs)
                                        (coderef (val i32 norefs)
                                          ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))))
                              (ser (mem (rep ptr) norefs) (i31 (val ptr norefs)))))
                         (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
        local.set 3 ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
                       -> []
        local.get move 3 ;; [] ->
                            [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
        copy ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
                ->
                [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))
                 (exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
        local.set 3 ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                          (ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
                       -> []
        unpack (localfx [0 => (ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
                 [1 => (i31 (val ptr norefs))]
                 [2 =>
                 (exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
                 [3 =>
                 (exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
                 [4 => (plug (val (prod i32) norefs) (prod i32))] [5 => (plug (val (prod i32) norefs) (prod i32))]
                 [6 => (plug (val (prod i32) norefs) (prod i32))] [7 => (plug (val (prod i32) norefs) (prod i32))]
                 [8 => (plug (val (prod i32) norefs) (prod i32))])
          local.set 4 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                         -> []
          local.get move 4 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
          local.set 4 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                         -> []
          load (path 0) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))
                                 (var 0)]
          local.set 5 ;; [(var 0)] -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                  -> []
          local.get move 5 ;; [] -> [(var 0)]
          local.set 6 ;; [(var 0)] -> []
          local.get move 4 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
          copy ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                  ->
                  [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
          local.set 4 ;; [(ref (val ptr gcrefs) (base gc) imm
                            (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                              (ser (mem (rep ptr) gcrefs) (var 0))
                              (ser (mem (rep i32) norefs)
                                (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                         -> []
          load (path 1) copy ;; [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                                ->
                                [(ref (val ptr gcrefs) (base gc) imm
                                   (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                     (ser (mem (rep ptr) gcrefs) (var 0))
                                     (ser (mem (rep i32) norefs)
                                       (coderef (val i32 norefs)
                                         ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))
                                 (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
          local.set 7 ;; [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))] -> []
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                  -> []
          local.get move 7 ;; [] -> [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
          local.set 8 ;; [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))] -> []
          local.get move 6 ;; [] -> [(var 0)]
          copy ;; [(var 0)] -> [(var 0) (var 0)]
          local.set 6 ;; [(var 0)] -> []
          num_const 3 ;; [] -> [(num (val i32 norefs) i32)]
          tag ;; [(num (val i32 norefs) i32)] -> [(i31 (val ptr norefs))]
          local.get move 8 ;; [] -> [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
          copy ;; [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))] ->
                  [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))
                   (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
          local.set 8 ;; [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))] -> []
          call_indirect ;; [(var 0) (i31 (val ptr norefs))
                            (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
                           -> [(i31 (val ptr norefs))]
          local.get move 8 ;; [] -> [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))]
          drop ;; [(coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))] -> []
          local.get move 6 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get move 4 ;; [] ->
                              [(ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
          drop ;; [(ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs)))))))]
                  -> []
        end ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                  (ref (val ptr gcrefs) (base gc) imm
                    (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                      (ser (mem (rep i32) norefs)
                        (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
               -> [(i31 (val ptr norefs))]
        local.get move 3 ;; [] ->
                            [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
        drop ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
                -> []
        local.get move 2 ;; [] ->
                            [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                               (ref (val ptr gcrefs) (base gc) imm
                                 (struct (mem (prod (rep ptr) (rep i32)) gcrefs)
                                   (ser (mem (rep ptr) gcrefs) (var 0))
                                   (ser (mem (rep i32) norefs)
                                     (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
        drop ;; [(exists.type (val ptr gcrefs) (val ptr gcrefs)
                   (ref (val ptr gcrefs) (base gc) imm
                     (struct (mem (prod (rep ptr) (rep i32)) gcrefs) (ser (mem (rep ptr) gcrefs) (var 0))
                       (ser (mem (rep i32) norefs)
                         (coderef (val i32 norefs) ((var 0) (i31 (val ptr norefs)) -> (i31 (val ptr norefs))))))))]
                -> []
        local.get move 1 ;; [] -> [(i31 (val ptr norefs))]
        drop ;; [(i31 (val ptr norefs))] -> []
        local.get move 0 ;; [] -> [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))]
        drop ;; [(ref (val ptr gcrefs) (base gc) imm (struct (mem (prod) norefs)))] -> [])
      (table 0 1 2)
      (export "_start" (func 2)))
    |xxx}]
