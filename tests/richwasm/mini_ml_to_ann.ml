open! Core
open! Stdlib.Format
open! Test_support
module AnnRichWasm = Richwasm_common.Annotated_syntax

include Test_runner.MultiOutputter.Make (struct
  let margin = 120
  let max_indent = margin

  open Test_utils
  open Richwasm_mini_ml

  type syntax = Syntax.Source.Module.t
  type text = string
  type res = AnnRichWasm.Module.t

  let elab x =
    x
    |> Richwasm_common.Elaborate.elab_module
    |> or_fail_pp Richwasm_common.Elaborate.Err.pp

  let syntax_pipeline x =
    x |> Convert.cc_module |> Codegen.compile_module |> elab

  let string_pipeline s = s |> Parse.from_string_exn |> syntax_pipeline
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
      (func ((ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))) -> (i31 (val ptr imcopy imdrop))) (local
          ptr)
        num_const 1 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))])
      (table 0)
      (export "_start" (func 0)))
    -----------tuple-----------
    (module
      (func
          ((ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))) ->
          (ref (val ptr excopy exdrop) (base gc)
            (struct (mem (prod (rep ptr) (rep ptr) (rep ptr) (rep ptr)) imdrop)
              (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
              (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
              (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
              (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
          (local ptr)
        num_const 4 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        num_const 3 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        num_const 2 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        num_const 1 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        group ;; [(i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop))
                 (i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop))] ->
                 [(prod (val (prod ptr ptr ptr ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop))
                    (i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop))
                    (i31 (val ptr imcopy imdrop)))]
        new ;; [(prod (val (prod ptr ptr ptr ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop))
                  (i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop))
                  (i31 (val ptr imcopy imdrop)))]
               ->
               [(ref (val ptr excopy exdrop) (base gc)
                  (ser (mem (rep (prod ptr ptr ptr ptr)) imdrop)
                    (prod (val (prod ptr ptr ptr ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop))
                      (i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop))
                      (i31 (val ptr imcopy imdrop)))))]
        cast ;; [(ref (val ptr excopy exdrop) (base gc)
                   (ser (mem (rep (prod ptr ptr ptr ptr)) imdrop)
                     (prod (val (prod ptr ptr ptr ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop))
                       (i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop))
                       (i31 (val ptr imcopy imdrop)))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr) (rep ptr) (rep ptr)) imdrop)
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))])
      (table 0)
      (export "_start" (func 0)))
    -----------tuple_nested-----------
    (module
      (func
          ((ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))) ->
          (ref (val ptr excopy exdrop) (base gc)
            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
              (ser (mem (rep ptr) exdrop)
                (ref (val ptr excopy exdrop) (base gc)
                  (struct (mem (prod (rep ptr) (rep ptr)) imdrop)
                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
              (ser (mem (rep ptr) exdrop)
                (ref (val ptr excopy exdrop) (base gc)
                  (struct (mem (prod (rep ptr) (rep ptr)) imdrop)
                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))))))
          (local ptr)
        num_const 4 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        num_const 3 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        group ;; [(i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop))] ->
                 [(prod (val (prod ptr ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop)))]
        new ;; [(prod (val (prod ptr ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop)))] ->
               [(ref (val ptr excopy exdrop) (base gc)
                  (ser (mem (rep (prod ptr ptr)) imdrop)
                    (prod (val (prod ptr ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop)))))]
        cast ;; [(ref (val ptr excopy exdrop) (base gc)
                   (ser (mem (rep (prod ptr ptr)) imdrop)
                     (prod (val (prod ptr ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop)))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) imdrop)
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        num_const 2 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        num_const 1 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        group ;; [(i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop))] ->
                 [(prod (val (prod ptr ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop)))]
        new ;; [(prod (val (prod ptr ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop)))] ->
               [(ref (val ptr excopy exdrop) (base gc)
                  (ser (mem (rep (prod ptr ptr)) imdrop)
                    (prod (val (prod ptr ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop)))))]
        cast ;; [(ref (val ptr excopy exdrop) (base gc)
                   (ser (mem (rep (prod ptr ptr)) imdrop)
                     (prod (val (prod ptr ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop)))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) imdrop)
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        group ;; [(ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr) (rep ptr)) imdrop)
                      (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
                      (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                 (ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) imdrop)
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                 ->
                 [(prod (val (prod ptr ptr) excopy exdrop)
                    (ref (val ptr excopy exdrop) (base gc)
                      (struct (mem (prod (rep ptr) (rep ptr)) imdrop)
                        (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
                        (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                    (ref (val ptr excopy exdrop) (base gc)
                      (struct (mem (prod (rep ptr) (rep ptr)) imdrop)
                        (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
                        (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))]
        new ;; [(prod (val (prod ptr ptr) excopy exdrop)
                  (ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr) (rep ptr)) imdrop)
                      (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
                      (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                  (ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr) (rep ptr)) imdrop)
                      (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
                      (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))]
               ->
               [(ref (val ptr excopy exdrop) (base gc)
                  (ser (mem (rep (prod ptr ptr)) exdrop)
                    (prod (val (prod ptr ptr) excopy exdrop)
                      (ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr) (rep ptr)) imdrop)
                          (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
                          (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                      (ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr) (rep ptr)) imdrop)
                          (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
                          (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))))]
        cast ;; [(ref (val ptr excopy exdrop) (base gc)
                   (ser (mem (rep (prod ptr ptr)) exdrop)
                     (prod (val (prod ptr ptr) excopy exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr) (rep ptr)) imdrop)
                           (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
                           (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr) (rep ptr)) imdrop)
                           (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
                           (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr) (rep ptr)) imdrop)
                           (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
                           (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr) (rep ptr)) imdrop)
                           (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
                           (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))))])
      (table 0)
      (export "_start" (func 0)))
    -----------tuple_project-----------
    (module
      (func ((ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))) -> (i31 (val ptr imcopy imdrop))) (local
          ptr ptr)
        num_const 7 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        num_const 42 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        group ;; [(i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop))] ->
                 [(prod (val (prod ptr ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop)))]
        new ;; [(prod (val (prod ptr ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop)))] ->
               [(ref (val ptr excopy exdrop) (base gc)
                  (ser (mem (rep (prod ptr ptr)) imdrop)
                    (prod (val (prod ptr ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop)))))]
        cast ;; [(ref (val ptr excopy exdrop) (base gc)
                   (ser (mem (rep (prod ptr ptr)) imdrop)
                     (prod (val (prod ptr ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop)))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) imdrop)
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        load (path 1) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) imdrop)
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                              ->
                              [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) imdrop)
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                              (i31 (val ptr imcopy imdrop))]
        local.set 1 ;; [(i31 (val ptr imcopy imdrop))] -> []
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) imdrop)
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                -> []
        local.get 1 ;; [] -> [(i31 (val ptr imcopy imdrop))])
      (table 0)
      (export "_start" (func 0)))
    -----------sum_unit-----------
    (module
      (func
          ((ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))) ->
          (ref (val ptr excopy exdrop) (base gc)
            (variant (mem (sum (rep ptr)) exdrop)
              (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))))))
          (local ptr)
        group ;; [] -> [(prod (val (prod) imcopy imdrop))]
        new ;; [(prod (val (prod) imcopy imdrop))] ->
               [(ref (val ptr excopy exdrop) (base gc) (ser (mem (rep (prod)) imdrop) (prod (val (prod) imcopy imdrop))))]
        cast ;; [(ref (val ptr excopy exdrop) (base gc) (ser (mem (rep (prod)) imdrop) (prod (val (prod) imcopy imdrop))))]
                -> [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
        inject_new 0 ;; [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))] ->
                        [(ref (val ptr excopy exdrop) (base gc)
                           (variant (mem (sum (rep ptr)) exdrop)
                             (ser (mem (rep ptr) exdrop)
                               (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))])
      (table 0)
      (export "_start" (func 0)))
    -----------sum_option-----------
    (module
      (func
          ((ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))) ->
          (ref (val ptr excopy exdrop) (base gc)
            (variant (mem (sum (rep ptr) (rep ptr)) exdrop)
              (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
              (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
          (local ptr)
        num_const 15 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        inject_new 1 ;; [(i31 (val ptr imcopy imdrop))] ->
                        [(ref (val ptr excopy exdrop) (base gc)
                           (variant (mem (sum (rep ptr) (rep ptr)) exdrop)
                             (ser (mem (rep ptr) exdrop)
                               (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                             (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))])
      (table 0)
      (export "_start" (func 0)))
    -----------basic_if-----------
    (module
      (func ((ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))) -> (i31 (val ptr imcopy imdrop))) (local
          ptr)
        num_const 0 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        untag ;; [(i31 (val ptr imcopy imdrop))] -> [(num (val i32 imcopy imdrop) i32)]
        num_const 0 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        i32.eq ;; [(num (val i32 imcopy imdrop) i32) (num (val i32 imcopy imdrop) i32)] ->
                  [(num (val i32 imcopy imdrop) i32)]
        if
          (localfx [0 => (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
            [1 => (plug (val (prod i32) imcopy imdrop) (prod i32))])
          num_const 1 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
          tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        else
          num_const 2 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
          tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        end ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))])
      (table 0)
      (export "_start" (func 0)))
    -----------add-----------
    (module
      (func ((ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))) -> (i31 (val ptr imcopy imdrop))) (local
          ptr)
        num_const 1 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        untag ;; [(i31 (val ptr imcopy imdrop))] -> [(num (val i32 imcopy imdrop) i32)]
        num_const 2 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        untag ;; [(i31 (val ptr imcopy imdrop))] -> [(num (val i32 imcopy imdrop) i32)]
        i32.add ;; [(num (val i32 imcopy imdrop) i32) (num (val i32 imcopy imdrop) i32)] ->
                   [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))])
      (table 0)
      (export "_start" (func 0)))
    -----------sub-----------
    (module
      (func ((ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))) -> (i31 (val ptr imcopy imdrop))) (local
          ptr)
        num_const 1 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        untag ;; [(i31 (val ptr imcopy imdrop))] -> [(num (val i32 imcopy imdrop) i32)]
        num_const 2 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        untag ;; [(i31 (val ptr imcopy imdrop))] -> [(num (val i32 imcopy imdrop) i32)]
        i32.sub ;; [(num (val i32 imcopy imdrop) i32) (num (val i32 imcopy imdrop) i32)] ->
                   [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))])
      (table 0)
      (export "_start" (func 0)))
    -----------mul-----------
    (module
      (func ((ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))) -> (i31 (val ptr imcopy imdrop))) (local
          ptr)
        num_const 1 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        untag ;; [(i31 (val ptr imcopy imdrop))] -> [(num (val i32 imcopy imdrop) i32)]
        num_const 2 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        untag ;; [(i31 (val ptr imcopy imdrop))] -> [(num (val i32 imcopy imdrop) i32)]
        i32.mul ;; [(num (val i32 imcopy imdrop) i32) (num (val i32 imcopy imdrop) i32)] ->
                   [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))])
      (table 0)
      (export "_start" (func 0)))
    -----------div-----------
    (module
      (func ((ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))) -> (i31 (val ptr imcopy imdrop))) (local
          ptr)
        num_const 1 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        untag ;; [(i31 (val ptr imcopy imdrop))] -> [(num (val i32 imcopy imdrop) i32)]
        num_const 2 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        untag ;; [(i31 (val ptr imcopy imdrop))] -> [(num (val i32 imcopy imdrop) i32)]
        i32.div_s ;; [(num (val i32 imcopy imdrop) i32) (num (val i32 imcopy imdrop) i32)] ->
                     [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))])
      (table 0)
      (export "_start" (func 0)))
    -----------math-----------
    (module
      (func ((ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))) -> (i31 (val ptr imcopy imdrop))) (local
          ptr)
        num_const 2 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        untag ;; [(i31 (val ptr imcopy imdrop))] -> [(num (val i32 imcopy imdrop) i32)]
        num_const 6 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        untag ;; [(i31 (val ptr imcopy imdrop))] -> [(num (val i32 imcopy imdrop) i32)]
        i32.mul ;; [(num (val i32 imcopy imdrop) i32) (num (val i32 imcopy imdrop) i32)] ->
                   [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        untag ;; [(i31 (val ptr imcopy imdrop))] -> [(num (val i32 imcopy imdrop) i32)]
        num_const 3 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        untag ;; [(i31 (val ptr imcopy imdrop))] -> [(num (val i32 imcopy imdrop) i32)]
        i32.div_s ;; [(num (val i32 imcopy imdrop) i32) (num (val i32 imcopy imdrop) i32)] ->
                     [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))])
      (table 0)
      (export "_start" (func 0)))
    -----------basic_let-----------
    (module
      (func ((ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))) -> (i31 (val ptr imcopy imdrop))) (local
          ptr ptr)
        num_const 10 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        local.set 1 ;; [(i31 (val ptr imcopy imdrop))] -> []
        local.get 1 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        copy ;; [(i31 (val ptr imcopy imdrop))] -> [(i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop))]
        local.set 1 ;; [(i31 (val ptr imcopy imdrop))] -> []
        local.get 1 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        drop ;; [(i31 (val ptr imcopy imdrop))] -> [])
      (table 0)
      (export "_start" (func 0)))
    -----------return_one-----------
    (module
      (func
          ((ref (val ptr excopy exdrop) (base gc)
             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
               (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
               (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
          -> (i31 (val ptr imcopy imdrop))) (local ptr ptr ptr ptr ptr)
        local.get 0 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
        copy ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                (ref (val ptr excopy exdrop) (base gc)
                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                    (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                    (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
        local.set 0 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                       -> []
        load (path 0) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                              ->
                              [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
        local.set 1 ;; [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))] -> []
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                -> []
        local.get 1 ;; [] -> [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
        local.set 2 ;; [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))] -> []
        local.get 0 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
        copy ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                (ref (val ptr excopy exdrop) (base gc)
                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                    (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                    (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
        local.set 0 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                       -> []
        load (path 1) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                              ->
                              [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
        local.set 3 ;; [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))] -> []
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                -> []
        local.get 3 ;; [] -> [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
        local.set 4 ;; [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))] -> []
        num_const 1 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        local.get 4 ;; [] -> [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
        drop ;; [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))] -> []
        local.get 2 ;; [] -> [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
        drop ;; [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))] -> [])
      (func
          ((ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))) ->
          (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
            (ref (val ptr excopy exdrop) (base gc)
              (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                (ser (mem (rep i32) imdrop)
                  (coderef (val i32 imcopy imdrop)
                    ((ref (val ptr excopy exdrop) (base gc)
                       (struct (mem (prod (rep ptr) (rep ptr)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                         (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                    -> (i31 (val ptr imcopy imdrop)))))))))
          (local ptr)
        group ;; [] -> [(prod (val (prod) imcopy imdrop))]
        new ;; [(prod (val (prod) imcopy imdrop))] ->
               [(ref (val ptr excopy exdrop) (base gc) (ser (mem (rep (prod)) imdrop) (prod (val (prod) imcopy imdrop))))]
        cast ;; [(ref (val ptr excopy exdrop) (base gc) (ser (mem (rep (prod)) imdrop) (prod (val (prod) imcopy imdrop))))]
                -> [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
        coderef 0 ;; [] ->
                     [(coderef (val i32 imcopy imdrop)
                        ((ref (val ptr excopy exdrop) (base gc)
                           (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                             (ser (mem (rep ptr) exdrop)
                               (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                             (ser (mem (rep ptr) exdrop)
                               (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                        -> (i31 (val ptr imcopy imdrop))))]
        group ;; [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))
                 (coderef (val i32 imcopy imdrop)
                   ((ref (val ptr excopy exdrop) (base gc)
                      (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                        (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                        (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                   -> (i31 (val ptr imcopy imdrop))))]
                 ->
                 [(prod (val (prod ptr i32) excopy exdrop)
                    (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))
                    (coderef (val i32 imcopy imdrop)
                      ((ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                           (ser (mem (rep ptr) exdrop)
                             (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                           (ser (mem (rep ptr) exdrop)
                             (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                      -> (i31 (val ptr imcopy imdrop)))))]
        new ;; [(prod (val (prod ptr i32) excopy exdrop)
                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))
                  (coderef (val i32 imcopy imdrop)
                    ((ref (val ptr excopy exdrop) (base gc)
                       (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                         (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                         (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                    -> (i31 (val ptr imcopy imdrop)))))]
               ->
               [(ref (val ptr excopy exdrop) (base gc)
                  (ser (mem (rep (prod ptr i32)) exdrop)
                    (prod (val (prod ptr i32) excopy exdrop)
                      (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))
                      (coderef (val i32 imcopy imdrop)
                        ((ref (val ptr excopy exdrop) (base gc)
                           (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                             (ser (mem (rep ptr) exdrop)
                               (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                             (ser (mem (rep ptr) exdrop)
                               (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                        -> (i31 (val ptr imcopy imdrop)))))))]
        cast ;; [(ref (val ptr excopy exdrop) (base gc)
                   (ser (mem (rep (prod ptr i32)) exdrop)
                     (prod (val (prod ptr i32) excopy exdrop)
                       (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))
                       (coderef (val i32 imcopy imdrop)
                         ((ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                         -> (i31 (val ptr imcopy imdrop)))))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep i32) imdrop)
                       (coderef (val i32 imcopy imdrop)
                         ((ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                         -> (i31 (val ptr imcopy imdrop)))))))]
        pack ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep i32) imdrop)
                       (coderef (val i32 imcopy imdrop)
                         ((ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                         -> (i31 (val ptr imcopy imdrop)))))))]
                ->
                [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                   (ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) exdrop)
                                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                           -> (i31 (val ptr imcopy imdrop))))))))])
      (table 0 1)
      (export "_start" (func 1)))
    -----------iife-----------
    (module
      (func
          ((ref (val ptr excopy exdrop) (base gc)
             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
               (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
               (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
          -> (i31 (val ptr imcopy imdrop))) (local ptr ptr ptr ptr ptr)
        local.get 0 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
        copy ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                (ref (val ptr excopy exdrop) (base gc)
                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                    (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                    (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
        local.set 0 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                       -> []
        load (path 0) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                              ->
                              [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
        local.set 1 ;; [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))] -> []
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                -> []
        local.get 1 ;; [] -> [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
        local.set 2 ;; [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))] -> []
        local.get 0 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
        copy ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                (ref (val ptr excopy exdrop) (base gc)
                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                    (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                    (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
        local.set 0 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                       -> []
        load (path 1) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                              ->
                              [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
        local.set 3 ;; [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))] -> []
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                -> []
        local.get 3 ;; [] -> [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
        local.set 4 ;; [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))] -> []
        num_const 1 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        local.get 4 ;; [] -> [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
        drop ;; [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))] -> []
        local.get 2 ;; [] -> [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
        drop ;; [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))] -> [])
      (func ((ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))) -> (i31 (val ptr imcopy imdrop))) (local
          ptr ptr ptr ptr ptr ptr)
        group ;; [] -> [(prod (val (prod) imcopy imdrop))]
        new ;; [(prod (val (prod) imcopy imdrop))] ->
               [(ref (val ptr excopy exdrop) (base gc) (ser (mem (rep (prod)) imdrop) (prod (val (prod) imcopy imdrop))))]
        cast ;; [(ref (val ptr excopy exdrop) (base gc) (ser (mem (rep (prod)) imdrop) (prod (val (prod) imcopy imdrop))))]
                -> [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
        coderef 0 ;; [] ->
                     [(coderef (val i32 imcopy imdrop)
                        ((ref (val ptr excopy exdrop) (base gc)
                           (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                             (ser (mem (rep ptr) exdrop)
                               (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                             (ser (mem (rep ptr) exdrop)
                               (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                        -> (i31 (val ptr imcopy imdrop))))]
        group ;; [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))
                 (coderef (val i32 imcopy imdrop)
                   ((ref (val ptr excopy exdrop) (base gc)
                      (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                        (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                        (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                   -> (i31 (val ptr imcopy imdrop))))]
                 ->
                 [(prod (val (prod ptr i32) excopy exdrop)
                    (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))
                    (coderef (val i32 imcopy imdrop)
                      ((ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                           (ser (mem (rep ptr) exdrop)
                             (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                           (ser (mem (rep ptr) exdrop)
                             (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                      -> (i31 (val ptr imcopy imdrop)))))]
        new ;; [(prod (val (prod ptr i32) excopy exdrop)
                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))
                  (coderef (val i32 imcopy imdrop)
                    ((ref (val ptr excopy exdrop) (base gc)
                       (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                         (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                         (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                    -> (i31 (val ptr imcopy imdrop)))))]
               ->
               [(ref (val ptr excopy exdrop) (base gc)
                  (ser (mem (rep (prod ptr i32)) exdrop)
                    (prod (val (prod ptr i32) excopy exdrop)
                      (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))
                      (coderef (val i32 imcopy imdrop)
                        ((ref (val ptr excopy exdrop) (base gc)
                           (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                             (ser (mem (rep ptr) exdrop)
                               (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                             (ser (mem (rep ptr) exdrop)
                               (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                        -> (i31 (val ptr imcopy imdrop)))))))]
        cast ;; [(ref (val ptr excopy exdrop) (base gc)
                   (ser (mem (rep (prod ptr i32)) exdrop)
                     (prod (val (prod ptr i32) excopy exdrop)
                       (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))
                       (coderef (val i32 imcopy imdrop)
                         ((ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                         -> (i31 (val ptr imcopy imdrop)))))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep i32) imdrop)
                       (coderef (val i32 imcopy imdrop)
                         ((ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                         -> (i31 (val ptr imcopy imdrop)))))))]
        pack ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep i32) imdrop)
                       (coderef (val i32 imcopy imdrop)
                         ((ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                         -> (i31 (val ptr imcopy imdrop)))))))]
                ->
                [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                   (ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) exdrop)
                                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                           -> (i31 (val ptr imcopy imdrop))))))))]
        unpack (localfx [0 => (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
                 [1 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [2 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [3 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [4 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [5 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [6 => (plug (val (prod i32) imcopy imdrop) (prod i32))])
          local.set 1 ;; [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) exdrop)
                                         (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
                         -> []
          local.get 1 ;; [] ->
                         [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) exdrop)
                                         (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
          copy ;; [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) exdrop)
                                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                           -> (i31 (val ptr imcopy imdrop)))))))]
                  ->
                  [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) exdrop)
                                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                           -> (i31 (val ptr imcopy imdrop)))))))
                  (ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                      (ser (mem (rep i32) imdrop)
                        (coderef (val i32 imcopy imdrop)
                          ((ref (val ptr excopy exdrop) (base gc)
                             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                               (ser (mem (rep ptr) exdrop) (var 0))
                               (ser (mem (rep ptr) exdrop)
                                 (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                          -> (i31 (val ptr imcopy imdrop)))))))]
          local.set 1 ;; [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) exdrop)
                                         (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
                         -> []
          load (path 0) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                     (ser (mem (rep ptr) exdrop) (var 0))
                                     (ser (mem (rep i32) imdrop)
                                       (coderef (val i32 imcopy imdrop)
                                         ((ref (val ptr excopy exdrop) (base gc)
                                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                              (ser (mem (rep ptr) exdrop) (var 0))
                                              (ser (mem (rep ptr) exdrop)
                                                (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                         -> (i31 (val ptr imcopy imdrop)))))))]
                                ->
                                [(ref (val ptr excopy exdrop) (base gc)
                                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                     (ser (mem (rep ptr) exdrop) (var 0))
                                     (ser (mem (rep i32) imdrop)
                                       (coderef (val i32 imcopy imdrop)
                                         ((ref (val ptr excopy exdrop) (base gc)
                                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                              (ser (mem (rep ptr) exdrop) (var 0))
                                              (ser (mem (rep ptr) exdrop)
                                                (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                         -> (i31 (val ptr imcopy imdrop)))))))
                                (var 0)]
          local.set 2 ;; [(var 0)] -> []
          drop ;; [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) exdrop)
                                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                           -> (i31 (val ptr imcopy imdrop)))))))]
                  -> []
          local.get 2 ;; [] -> [(var 0)]
          local.set 3 ;; [(var 0)] -> []
          local.get 1 ;; [] ->
                         [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) exdrop)
                                         (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
          copy ;; [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) exdrop)
                                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                           -> (i31 (val ptr imcopy imdrop)))))))]
                  ->
                  [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) exdrop)
                                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                           -> (i31 (val ptr imcopy imdrop)))))))
                  (ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                      (ser (mem (rep i32) imdrop)
                        (coderef (val i32 imcopy imdrop)
                          ((ref (val ptr excopy exdrop) (base gc)
                             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                               (ser (mem (rep ptr) exdrop) (var 0))
                               (ser (mem (rep ptr) exdrop)
                                 (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                          -> (i31 (val ptr imcopy imdrop)))))))]
          local.set 1 ;; [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) exdrop)
                                         (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
                         -> []
          load (path 1) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                     (ser (mem (rep ptr) exdrop) (var 0))
                                     (ser (mem (rep i32) imdrop)
                                       (coderef (val i32 imcopy imdrop)
                                         ((ref (val ptr excopy exdrop) (base gc)
                                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                              (ser (mem (rep ptr) exdrop) (var 0))
                                              (ser (mem (rep ptr) exdrop)
                                                (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                         -> (i31 (val ptr imcopy imdrop)))))))]
                                ->
                                [(ref (val ptr excopy exdrop) (base gc)
                                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                     (ser (mem (rep ptr) exdrop) (var 0))
                                     (ser (mem (rep i32) imdrop)
                                       (coderef (val i32 imcopy imdrop)
                                         ((ref (val ptr excopy exdrop) (base gc)
                                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                              (ser (mem (rep ptr) exdrop) (var 0))
                                              (ser (mem (rep ptr) exdrop)
                                                (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                         -> (i31 (val ptr imcopy imdrop)))))))
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) exdrop)
                                         (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                  -> (i31 (val ptr imcopy imdrop))))]
          local.set 4 ;; [(coderef (val i32 imcopy imdrop)
                            ((ref (val ptr excopy exdrop) (base gc)
                               (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                 (ser (mem (rep ptr) exdrop) (var 0))
                                 (ser (mem (rep ptr) exdrop)
                                   (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                            -> (i31 (val ptr imcopy imdrop))))]
                         -> []
          drop ;; [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) exdrop)
                                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                           -> (i31 (val ptr imcopy imdrop)))))))]
                  -> []
          local.get 4 ;; [] ->
                         [(coderef (val i32 imcopy imdrop)
                            ((ref (val ptr excopy exdrop) (base gc)
                               (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                 (ser (mem (rep ptr) exdrop) (var 0))
                                 (ser (mem (rep ptr) exdrop)
                                   (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                            -> (i31 (val ptr imcopy imdrop))))]
          local.set 5 ;; [(coderef (val i32 imcopy imdrop)
                            ((ref (val ptr excopy exdrop) (base gc)
                               (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                 (ser (mem (rep ptr) exdrop) (var 0))
                                 (ser (mem (rep ptr) exdrop)
                                   (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                            -> (i31 (val ptr imcopy imdrop))))]
                         -> []
          group ;; [] -> [(prod (val (prod) imcopy imdrop))]
          new ;; [(prod (val (prod) imcopy imdrop))] ->
                 [(ref (val ptr excopy exdrop) (base gc) (ser (mem (rep (prod)) imdrop) (prod (val (prod) imcopy imdrop))))]
          cast ;; [(ref (val ptr excopy exdrop) (base gc)
                     (ser (mem (rep (prod)) imdrop) (prod (val (prod) imcopy imdrop))))]
                  -> [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
          local.get 5 ;; [] ->
                         [(coderef (val i32 imcopy imdrop)
                            ((ref (val ptr excopy exdrop) (base gc)
                               (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                 (ser (mem (rep ptr) exdrop) (var 0))
                                 (ser (mem (rep ptr) exdrop)
                                   (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                            -> (i31 (val ptr imcopy imdrop))))]
          copy ;; [(coderef (val i32 imcopy imdrop)
                     ((ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr) (rep ptr)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                          (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                     -> (i31 (val ptr imcopy imdrop))))]
                  ->
                  [(coderef (val i32 imcopy imdrop)
                     ((ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr) (rep ptr)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                          (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                     -> (i31 (val ptr imcopy imdrop))))
                  (coderef (val i32 imcopy imdrop)
                    ((ref (val ptr excopy exdrop) (base gc)
                       (struct (mem (prod (rep ptr) (rep ptr)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                         (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                    -> (i31 (val ptr imcopy imdrop))))]
          local.set 5 ;; [(coderef (val i32 imcopy imdrop)
                            ((ref (val ptr excopy exdrop) (base gc)
                               (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                 (ser (mem (rep ptr) exdrop) (var 0))
                                 (ser (mem (rep ptr) exdrop)
                                   (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                            -> (i31 (val ptr imcopy imdrop))))]
                         -> []
          call_indirect ;; [(ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) exdrop)
                                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                           (coderef (val i32 imcopy imdrop)
                             ((ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                  (ser (mem (rep ptr) exdrop) (var 0))
                                  (ser (mem (rep ptr) exdrop)
                                    (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                             -> (i31 (val ptr imcopy imdrop))))]
                           -> [(i31 (val ptr imcopy imdrop))]
          local.get 5 ;; [] ->
                         [(coderef (val i32 imcopy imdrop)
                            ((ref (val ptr excopy exdrop) (base gc)
                               (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                 (ser (mem (rep ptr) exdrop) (var 0))
                                 (ser (mem (rep ptr) exdrop)
                                   (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                            -> (i31 (val ptr imcopy imdrop))))]
          drop ;; [(coderef (val i32 imcopy imdrop)
                     ((ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr) (rep ptr)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                          (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                     -> (i31 (val ptr imcopy imdrop))))]
                  -> []
          local.get 3 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get 1 ;; [] ->
                         [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) exdrop)
                                         (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
          drop ;; [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) exdrop)
                                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                           -> (i31 (val ptr imcopy imdrop)))))))]
                  -> []
        end ;; [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                  (ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                      (ser (mem (rep i32) imdrop)
                        (coderef (val i32 imcopy imdrop)
                          ((ref (val ptr excopy exdrop) (base gc)
                             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                               (ser (mem (rep ptr) exdrop) (var 0))
                               (ser (mem (rep ptr) exdrop)
                                 (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                          -> (i31 (val ptr imcopy imdrop))))))))]
               -> [(i31 (val ptr imcopy imdrop))])
      (table 0 1)
      (export "_start" (func 1)))
    -----------add_one-----------
    (module
      (func
          ((ref (val ptr excopy exdrop) (base gc)
             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
               (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
               (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
          -> (i31 (val ptr imcopy imdrop))) (local ptr ptr ptr)
        local.get 0 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        copy ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                (ref (val ptr excopy exdrop) (base gc)
                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                    (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        local.set 0 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                       -> []
        load (path 1) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                              ->
                              [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                              (i31 (val ptr imcopy imdrop))]
        local.set 1 ;; [(i31 (val ptr imcopy imdrop))] -> []
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                -> []
        local.get 1 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        local.set 2 ;; [(i31 (val ptr imcopy imdrop))] -> []
        local.get 2 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        copy ;; [(i31 (val ptr imcopy imdrop))] -> [(i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop))]
        local.set 2 ;; [(i31 (val ptr imcopy imdrop))] -> []
        untag ;; [(i31 (val ptr imcopy imdrop))] -> [(num (val i32 imcopy imdrop) i32)]
        num_const 1 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        untag ;; [(i31 (val ptr imcopy imdrop))] -> [(num (val i32 imcopy imdrop) i32)]
        i32.add ;; [(num (val i32 imcopy imdrop) i32) (num (val i32 imcopy imdrop) i32)] ->
                   [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        local.get 2 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        drop ;; [(i31 (val ptr imcopy imdrop))] -> [])
      (table 0)
      (export "add1" (func 0)))
    -----------id-----------
    (module
      (func
          (forall.type (VALTYPE (AtomR PtrR) ExCopy ExDrop)
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))]))]
              [ (VarT 0)]))
          (local ptr ptr ptr)
        local.get 0 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                            (ser (mem (rep ptr) exdrop) (var 0))))]
        copy ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep ptr) exdrop) (var 0))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep ptr) exdrop) (var 0))))
                (ref (val ptr excopy exdrop) (base gc)
                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                    (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                    (ser (mem (rep ptr) exdrop) (var 0))))]
        local.set 0 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                            (ser (mem (rep ptr) exdrop) (var 0))))]
                       -> []
        load (path 1) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                                   (ser (mem (rep ptr) exdrop) (var 0))))]
                              ->
                              [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                                   (ser (mem (rep ptr) exdrop) (var 0))))
                              (var 0)]
        local.set 1 ;; [(var 0)] -> []
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep ptr) exdrop) (var 0))))]
                -> []
        local.get 1 ;; [] -> [(var 0)]
        local.set 2 ;; [(var 0)] -> []
        local.get 2 ;; [] -> [(var 0)]
        copy ;; [(var 0)] -> [(var 0) (var 0)]
        local.set 2 ;; [(var 0)] -> []
        local.get 2 ;; [] -> [(var 0)]
        drop ;; [(var 0)] -> [])
      (table 0)
      (export "id" (func 0)))
    -----------apply_id-----------
    FAILURE (InstrErr
     (error
      (BlockErr
       (error
        (ExpectedUnqualidfiedCoderef
         (CodeRef
          (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
           ((Ref (Base GC) (Struct ((Ser I31) (Ser (Var 0)))))) ((Var 0))))))
       (instr CallIndirect)
       (env
        ((local_offset 1) (kinds ((VALTYPE (Atom Ptr) ExCopy ExDrop)))
         (labels ((I31))) (return (I31))
         (functions
          ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
            ((Ref (Base GC)
              (Struct ((Ser (Ref (Base GC) (Struct ()))) (Ser (Var 0))))))
            ((Var 0)))
           (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
         (table
          ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
            ((Ref (Base GC)
              (Struct ((Ser (Ref (Base GC) (Struct ()))) (Ser (Var 0))))))
            ((Var 0)))
           (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
         (lfx (InferFx))))
       (state
        ((locals
          ((Ref (Base GC) (Struct ()))
           (Ref (Base GC)
            (Struct
             ((Ser (Var 0))
              (Ser
               (CodeRef
                (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
                 ((Ref (Base GC) (Struct ((Ser (Var 1)) (Ser (Var 0))))))
                 ((Var 0))))))))
           (Plug (Prod ((Atom I32)))) (Var 0) (Plug (Prod ((Atom I32))))
           (CodeRef
            (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
             ((Ref (Base GC) (Struct ((Ser (Var 1)) (Ser (Var 0)))))) ((Var 0))))
           (Plug (Prod ((Atom I32))))))
         (stack
          ((CodeRef
            (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
             ((Ref (Base GC) (Struct ((Ser I31) (Ser (Var 0)))))) ((Var 0))))
           I31))))))
     (instr
      (Unpack (ValType (I31)) InferFx
       ((LocalSet 1) (LocalGet 1 Move) Copy (LocalSet 1) (Load (Path (0)) Follow)
        (LocalSet 2) Drop (LocalGet 2 Move) (LocalSet 3) (LocalGet 1 Move) Copy
        (LocalSet 1) (Load (Path (1)) Follow) (LocalSet 4) Drop (LocalGet 4 Move)
        (LocalSet 5) (NumConst (Int I32) 42) Tag (LocalGet 5 Move) Copy
        (LocalSet 5) (Inst (Type I31)) CallIndirect (LocalGet 5 Move) Drop
        (LocalGet 3 Move) Drop (LocalGet 1 Move) Drop)))
     (env
      ((local_offset 1) (kinds ()) (labels ()) (return (I31))
       (functions
        ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
          ((Ref (Base GC)
            (Struct ((Ser (Ref (Base GC) (Struct ()))) (Ser (Var 0))))))
          ((Var 0)))
         (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
       (table
        ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
          ((Ref (Base GC)
            (Struct ((Ser (Ref (Base GC) (Struct ()))) (Ser (Var 0))))))
          ((Var 0)))
         (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
       (lfx ())))
     (state
      ((locals
        ((Ref (Base GC) (Struct ())) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32))))))
       (stack
        ((Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
          (Ref (Base GC)
           (Struct
            ((Ser (Var 0))
             (Ser
              (CodeRef
               (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
                ((Ref (Base GC) (Struct ((Ser (Var 1)) (Ser (Var 0))))))
                ((Var 0))))))))))))))
    -----------opt_case-----------
    FAILURE (InstrErr (error (PopEmptyStack Drop)) (instr Drop)
     (env
      ((local_offset 1) (kinds ()) (labels ()) (return (I31))
       (functions ((FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
       (table ((FunctionType () ((Ref (Base GC) (Struct ()))) (I31)))) (lfx ())))
     (state
      ((locals
        ((Ref (Base GC) (Struct ()))
         (Ref (Base GC) (Variant ((Ser (Ref (Base GC) (Struct ()))) (Ser I31))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32)))) I31
         (Plug (Prod ((Atom I32))))))
       (stack ()))))
    -----------poly_len-----------
    FAILURE (InstrErr
     (error
      (BlockErr
       (error
        (BlockErr
         (error
          (LoadRefNonSer
           (Variant
            ((Ser (Var 0))
             (Ser
              (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
               (Ref (Base GC)
                (Variant
                 ((Ser (Ref (Base GC) (Struct ())))
                  (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
         (instr (Load (Path ()) Follow))
         (env
          ((local_offset 1)
           (kinds
            ((VALTYPE (Atom Ptr) ExCopy ExDrop)
             (VALTYPE (Atom Ptr) ExCopy ExDrop)))
           (labels ((I31) (I31))) (return (I31))
           (functions
            ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
              ((Ref (Base GC)
                (Struct
                 ((Ser (Ref (Base GC) (Struct ())))
                  (Ser
                   (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                    (Ref (Base GC)
                     (Variant
                      ((Ser (Ref (Base GC) (Struct ())))
                       (Ser
                        (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
              (I31))
             (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
           (table
            ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
              ((Ref (Base GC)
                (Struct
                 ((Ser (Ref (Base GC) (Struct ())))
                  (Ser
                   (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                    (Ref (Base GC)
                     (Variant
                      ((Ser (Ref (Base GC) (Struct ())))
                       (Ser
                        (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
              (I31))
             (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
           (lfx (InferFx))))
         (state
          ((locals
            ((Ref (Base GC)
              (Struct
               ((Ser (Ref (Base GC) (Struct ())))
                (Ser
                 (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                  (Ref (Base GC)
                   (Variant
                    ((Ser (Ref (Base GC) (Struct ())))
                     (Ser
                      (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))))))
             (Plug (Prod ((Atom I32))))
             (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
              (Ref (Base GC)
               (Variant
                ((Ser (Ref (Base GC) (Struct ())))
                 (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))
             (Ref (Base GC)
              (Variant
               ((Ser (Var 0))
                (Ser
                 (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                  (Ref (Base GC)
                   (Variant
                    ((Ser (Ref (Base GC) (Struct ())))
                     (Ser
                      (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))))))
             (Ref (Base GC)
              (Struct
               ((Ser (Var 0))
                (Ser
                 (CodeRef
                  (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
                   ((Ref (Base GC)
                     (Struct
                      ((Ser (Var 1))
                       (Ser
                        (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                         (Ref (Base GC)
                          (Variant
                           ((Ser (Ref (Base GC) (Struct ())))
                            (Ser
                             (Ref (Base GC)
                              (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
                   (I31)))))))
             (Plug (Prod ((Atom I32)))) (Var 0) (Plug (Prod ((Atom I32))))
             (CodeRef
              (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
               ((Ref (Base GC)
                 (Struct
                  ((Ser (Var 1))
                   (Ser
                    (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                     (Ref (Base GC)
                      (Variant
                       ((Ser (Ref (Base GC) (Struct ())))
                        (Ser
                         (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
               (I31)))
             (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
             (Plug (Prod ((Atom I32))))))
           (stack
            ((Ref (Base GC)
              (Variant
               ((Ser (Var 0))
                (Ser
                 (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                  (Ref (Base GC)
                   (Variant
                    ((Ser (Ref (Base GC) (Struct ())))
                     (Ser
                      (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))))))))))))
       (instr
        (Unpack (ValType (I31)) InferFx
         ((LocalSet 4) (LocalGet 4 Move) Copy (LocalSet 4)
          (Load (Path (0)) Follow) (LocalSet 5) Drop (LocalGet 5 Move)
          (LocalSet 6) (LocalGet 4 Move) Copy (LocalSet 4)
          (Load (Path (1)) Follow) (LocalSet 7) Drop (LocalGet 7 Move)
          (LocalSet 8) (LocalGet 3 Move) Copy (LocalSet 3)
          (Load (Path ()) Follow)
          (Fold
           (Ref (Base GC)
            (Variant
             ((Ser (Ref (Base GC) (Struct ())))
              (Ser (Ref (Base GC) (Variant ((Ser (Var 2)) (Ser (Var 0))))))))))
          (New GC) (LocalGet 8 Move) Copy (LocalSet 8) (Inst (Type (Var 1)))
          CallIndirect (LocalGet 8 Move) Drop (LocalGet 6 Move) Drop
          (LocalGet 4 Move) Drop)))
       (env
        ((local_offset 1) (kinds ((VALTYPE (Atom Ptr) ExCopy ExDrop)))
         (labels ((I31))) (return (I31))
         (functions
          ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
            ((Ref (Base GC)
              (Struct
               ((Ser (Ref (Base GC) (Struct ())))
                (Ser
                 (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                  (Ref (Base GC)
                   (Variant
                    ((Ser (Ref (Base GC) (Struct ())))
                     (Ser
                      (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
            (I31))
           (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
         (table
          ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
            ((Ref (Base GC)
              (Struct
               ((Ser (Ref (Base GC) (Struct ())))
                (Ser
                 (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                  (Ref (Base GC)
                   (Variant
                    ((Ser (Ref (Base GC) (Struct ())))
                     (Ser
                      (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
            (I31))
           (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
         (lfx (InferFx))))
       (state
        ((locals
          ((Ref (Base GC)
            (Struct
             ((Ser (Ref (Base GC) (Struct ())))
              (Ser
               (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                (Ref (Base GC)
                 (Variant
                  ((Ser (Ref (Base GC) (Struct ())))
                   (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))))))
           (Plug (Prod ((Atom I32))))
           (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
            (Ref (Base GC)
             (Variant
              ((Ser (Ref (Base GC) (Struct ())))
               (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))
           (Ref (Base GC)
            (Variant
             ((Ser (Var 0))
              (Ser
               (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                (Ref (Base GC)
                 (Variant
                  ((Ser (Ref (Base GC) (Struct ())))
                   (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))))
         (stack
          ((Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
            (Ref (Base GC)
             (Struct
              ((Ser (Var 0))
               (Ser
                (CodeRef
                 (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
                  ((Ref (Base GC)
                    (Struct
                     ((Ser (Var 1))
                      (Ser
                       (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                        (Ref (Base GC)
                         (Variant
                          ((Ser (Ref (Base GC) (Struct ())))
                           (Ser
                            (Ref (Base GC)
                             (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
                  (I31))))))))
           (Num (Int I32))))))))
     (instr
      (CaseLoad (ValType (I31)) Copy InferFx
       (((LocalSet 9) (NumConst (Int I32) 0) Tag (LocalGet 9 Move) Drop)
        ((LocalSet 3) (NumConst (Int I32) 1) Tag Untag (Group 0) (New GC)
         (Cast (Ref (Base GC) (Struct ()))) (CodeRef 0) (Group 2) (New GC)
         (Cast
          (Ref (Base GC)
           (Struct
            ((Ser (Ref (Base GC) (Struct ())))
             (Ser
              (CodeRef
               (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
                ((Ref (Base GC)
                  (Struct
                   ((Ser (Ref (Base GC) (Struct ())))
                    (Ser
                     (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                      (Ref (Base GC)
                       (Variant
                        ((Ser (Ref (Base GC) (Struct ())))
                         (Ser
                          (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
                (I31))))))))
         (Pack (Type (Ref (Base GC) (Struct ())))
          (Ref (Base GC)
           (Struct
            ((Ser (Var 0))
             (Ser
              (CodeRef
               (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
                ((Ref (Base GC)
                  (Struct
                   ((Ser (Var 1))
                    (Ser
                     (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                      (Ref (Base GC)
                       (Variant
                        ((Ser (Ref (Base GC) (Struct ())))
                         (Ser
                          (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
                (I31))))))))
         (Unpack (ValType (I31)) InferFx
          ((LocalSet 4) (LocalGet 4 Move) Copy (LocalSet 4)
           (Load (Path (0)) Follow) (LocalSet 5) Drop (LocalGet 5 Move)
           (LocalSet 6) (LocalGet 4 Move) Copy (LocalSet 4)
           (Load (Path (1)) Follow) (LocalSet 7) Drop (LocalGet 7 Move)
           (LocalSet 8) (LocalGet 3 Move) Copy (LocalSet 3)
           (Load (Path ()) Follow)
           (Fold
            (Ref (Base GC)
             (Variant
              ((Ser (Ref (Base GC) (Struct ())))
               (Ser (Ref (Base GC) (Variant ((Ser (Var 2)) (Ser (Var 0))))))))))
           (New GC) (LocalGet 8 Move) Copy (LocalSet 8) (Inst (Type (Var 1)))
           CallIndirect (LocalGet 8 Move) Drop (LocalGet 6 Move) Drop
           (LocalGet 4 Move) Drop))
         Untag (Num (Int2 I32 Add)) Tag (LocalGet 3 Move) Drop))))
     (env
      ((local_offset 1) (kinds ((VALTYPE (Atom Ptr) ExCopy ExDrop))) (labels ())
       (return (I31))
       (functions
        ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
          ((Ref (Base GC)
            (Struct
             ((Ser (Ref (Base GC) (Struct ())))
              (Ser
               (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                (Ref (Base GC)
                 (Variant
                  ((Ser (Ref (Base GC) (Struct ())))
                   (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
          (I31))
         (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
       (table
        ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
          ((Ref (Base GC)
            (Struct
             ((Ser (Ref (Base GC) (Struct ())))
              (Ser
               (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                (Ref (Base GC)
                 (Variant
                  ((Ser (Ref (Base GC) (Struct ())))
                   (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
          (I31))
         (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
       (lfx ())))
     (state
      ((locals
        ((Ref (Base GC)
          (Struct
           ((Ser (Ref (Base GC) (Struct ())))
            (Ser
             (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
              (Ref (Base GC)
               (Variant
                ((Ser (Ref (Base GC) (Struct ())))
                 (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))))))
         (Plug (Prod ((Atom I32))))
         (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
          (Ref (Base GC)
           (Variant
            ((Ser (Ref (Base GC) (Struct ())))
             (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32))))))
       (stack
        ((Ref (Base GC)
          (Variant
           ((Ser (Ref (Base GC) (Struct ())))
            (Ser
             (Ref (Base GC)
              (Variant
               ((Ser (Var 0))
                (Ser
                 (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                  (Ref (Base GC)
                   (Variant
                    ((Ser (Ref (Base GC) (Struct ())))
                     (Ser
                      (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))))))))))
    -----------mini_zip-----------
    (module
      (func
          (forall.type (VALTYPE (AtomR PtrR) ExCopy ExDrop)
            (ForallTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
              (MonoFunT
                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                              (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (BaseM MemGC) (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC) (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))])))]))]
                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))]))))])))
          (local ptr ptr ptr ptr ptr ptr ptr)
        local.get 0 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                  (ser (mem (rep ptr) exdrop)
                                    (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                                  (ser (mem (rep ptr) exdrop)
                                    (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1)))))))))]
        copy ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                           (ser (mem (rep ptr) exdrop)
                             (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                           (ser (mem (rep ptr) exdrop)
                             (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1)))))))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                           (ser (mem (rep ptr) exdrop)
                             (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                           (ser (mem (rep ptr) exdrop)
                             (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1)))))))))
                (ref (val ptr excopy exdrop) (base gc)
                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                    (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                    (ser (mem (rep ptr) exdrop)
                      (ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                          (ser (mem (rep ptr) exdrop)
                            (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                          (ser (mem (rep ptr) exdrop)
                            (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1)))))))))]
        local.set 0 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                  (ser (mem (rep ptr) exdrop)
                                    (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                                  (ser (mem (rep ptr) exdrop)
                                    (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1)))))))))]
                       -> []
        load (path 1) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc)
                                       (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                         (ser (mem (rep ptr) exdrop)
                                           (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                                         (ser (mem (rep ptr) exdrop)
                                           (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1)))))))))]
                              ->
                              [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc)
                                       (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                         (ser (mem (rep ptr) exdrop)
                                           (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                                         (ser (mem (rep ptr) exdrop)
                                           (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1)))))))))
                              (ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                  (ser (mem (rep ptr) exdrop)
                                    (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                                  (ser (mem (rep ptr) exdrop)
                                    (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1))))))]
        local.set 1 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1))))))]
                       -> []
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                           (ser (mem (rep ptr) exdrop)
                             (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                           (ser (mem (rep ptr) exdrop)
                             (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1)))))))))]
                -> []
        local.get 1 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1))))))]
        local.set 2 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1))))))]
                       -> []
        local.get 2 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1))))))]
        copy ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1))))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1))))))
                (ref (val ptr excopy exdrop) (base gc)
                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                    (ser (mem (rep ptr) exdrop)
                      (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                    (ser (mem (rep ptr) exdrop)
                      (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1))))))]
        local.set 2 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1))))))]
                       -> []
        load (path 1) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1))))))]
                              ->
                              [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1))))))
                              (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1)))]
        local.set 3 ;; [(ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1)))] -> []
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1))))))]
                -> []
        local.get 3 ;; [] -> [(ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1)))]
        load (path) copy ;; [(ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1)))] ->
                            [(ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1)))
                            (var 1)]
        local.set 4 ;; [(var 1)] -> []
        drop ;; [(ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1)))] -> []
        local.get 4 ;; [] -> [(var 1)]
        local.get 2 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1))))))]
        copy ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1))))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1))))))
                (ref (val ptr excopy exdrop) (base gc)
                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                    (ser (mem (rep ptr) exdrop)
                      (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                    (ser (mem (rep ptr) exdrop)
                      (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1))))))]
        local.set 2 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1))))))]
                       -> []
        load (path 0) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1))))))]
                              ->
                              [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1))))))
                              (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0)))]
        local.set 5 ;; [(ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0)))] -> []
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1))))))]
                -> []
        local.get 5 ;; [] -> [(ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0)))]
        load (path) copy ;; [(ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0)))] ->
                            [(ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0)))
                            (var 0)]
        local.set 6 ;; [(var 0)] -> []
        drop ;; [(ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0)))] -> []
        local.get 6 ;; [] -> [(var 0)]
        group ;; [(var 1) (var 0)] -> [(prod (val (prod ptr ptr) excopy exdrop) (var 1) (var 0))]
        new ;; [(prod (val (prod ptr ptr) excopy exdrop) (var 1) (var 0))] ->
               [(ref (val ptr excopy exdrop) (base gc)
                  (ser (mem (rep (prod ptr ptr)) exdrop) (prod (val (prod ptr ptr) excopy exdrop) (var 1) (var 0))))]
        cast ;; [(ref (val ptr excopy exdrop) (base gc)
                   (ser (mem (rep (prod ptr ptr)) exdrop) (prod (val (prod ptr ptr) excopy exdrop) (var 1) (var 0))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop) (ser (mem (rep ptr) exdrop) (var 1))
                     (ser (mem (rep ptr) exdrop) (var 0))))]
        new ;; [(ref (val ptr excopy exdrop) (base gc)
                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop) (ser (mem (rep ptr) exdrop) (var 1))
                    (ser (mem (rep ptr) exdrop) (var 0))))]
               ->
               [(ref (val ptr excopy exdrop) (base gc)
                  (ser (mem (rep ptr) exdrop)
                    (ref (val ptr excopy exdrop) (base gc)
                      (struct (mem (prod (rep ptr) (rep ptr)) exdrop) (ser (mem (rep ptr) exdrop) (var 1))
                        (ser (mem (rep ptr) exdrop) (var 0))))))]
        local.get 2 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1))))))]
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 0))))
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc) (ser (mem (rep ptr) exdrop) (var 1))))))]
                -> [])
      (table 0)
      (export "mini_zip" (func 0)))
    -----------closure_simpl-----------
    (module
      (func
          ((ref (val ptr excopy exdrop) (base gc)
             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
               (ser (mem (rep ptr) exdrop)
                 (ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
               (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
          -> (i31 (val ptr imcopy imdrop))) (local ptr ptr ptr ptr ptr ptr ptr)
        local.get 0 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr)) imdrop)
                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
        copy ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                (ref (val ptr excopy exdrop) (base gc)
                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                    (ser (mem (rep ptr) exdrop)
                      (ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                    (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
        local.set 0 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr)) imdrop)
                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                       -> []
        load (path 0) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc)
                                       (struct (mem (prod (rep ptr)) imdrop)
                                         (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                              ->
                              [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc)
                                       (struct (mem (prod (rep ptr)) imdrop)
                                         (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                              (ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr)) imdrop)
                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        local.set 1 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                       -> []
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                -> []
        local.get 1 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        local.set 2 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                       -> []
        local.get 0 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr)) imdrop)
                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
        copy ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                (ref (val ptr excopy exdrop) (base gc)
                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                    (ser (mem (rep ptr) exdrop)
                      (ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                    (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
        local.set 0 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr)) imdrop)
                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                       -> []
        load (path 1) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc)
                                       (struct (mem (prod (rep ptr)) imdrop)
                                         (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                              ->
                              [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc)
                                       (struct (mem (prod (rep ptr)) imdrop)
                                         (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                              (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
        local.set 3 ;; [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))] -> []
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))]
                -> []
        local.get 3 ;; [] -> [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
        local.set 4 ;; [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))] -> []
        local.get 2 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        copy ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                (ref (val ptr excopy exdrop) (base gc)
                  (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        local.set 2 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                       -> []
        load (path 0) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr)) imdrop)
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                              ->
                              [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr)) imdrop)
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                              (i31 (val ptr imcopy imdrop))]
        local.set 5 ;; [(i31 (val ptr imcopy imdrop))] -> []
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                -> []
        local.get 5 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        local.set 6 ;; [(i31 (val ptr imcopy imdrop))] -> []
        local.get 6 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        copy ;; [(i31 (val ptr imcopy imdrop))] -> [(i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop))]
        local.set 6 ;; [(i31 (val ptr imcopy imdrop))] -> []
        local.get 6 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        drop ;; [(i31 (val ptr imcopy imdrop))] -> []
        local.get 4 ;; [] -> [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
        drop ;; [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))] -> []
        local.get 2 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                -> [])
      (func ((ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))) -> (i31 (val ptr imcopy imdrop))) (local
          ptr ptr ptr ptr ptr ptr ptr ptr)
        num_const 1 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        local.set 1 ;; [(i31 (val ptr imcopy imdrop))] -> []
        local.get 1 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        copy ;; [(i31 (val ptr imcopy imdrop))] -> [(i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop))]
        local.set 1 ;; [(i31 (val ptr imcopy imdrop))] -> []
        group ;; [(i31 (val ptr imcopy imdrop))] -> [(prod (val (prod ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop)))]
        new ;; [(prod (val (prod ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop)))] ->
               [(ref (val ptr excopy exdrop) (base gc)
                  (ser (mem (rep (prod ptr)) imdrop) (prod (val (prod ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop)))))]
        cast ;; [(ref (val ptr excopy exdrop) (base gc)
                   (ser (mem (rep (prod ptr)) imdrop) (prod (val (prod ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop)))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        coderef 0 ;; [] ->
                     [(coderef (val i32 imcopy imdrop)
                        ((ref (val ptr excopy exdrop) (base gc)
                           (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                             (ser (mem (rep ptr) exdrop)
                               (ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr)) imdrop)
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                             (ser (mem (rep ptr) exdrop)
                               (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                        -> (i31 (val ptr imcopy imdrop))))]
        group ;; [(ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                 (coderef (val i32 imcopy imdrop)
                   ((ref (val ptr excopy exdrop) (base gc)
                      (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                        (ser (mem (rep ptr) exdrop)
                          (ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr)) imdrop)
                              (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                        (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                   -> (i31 (val ptr imcopy imdrop))))]
                 ->
                 [(prod (val (prod ptr i32) excopy exdrop)
                    (ref (val ptr excopy exdrop) (base gc)
                      (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                    (coderef (val i32 imcopy imdrop)
                      ((ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                           (ser (mem (rep ptr) exdrop)
                             (ref (val ptr excopy exdrop) (base gc)
                               (struct (mem (prod (rep ptr)) imdrop)
                                 (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                           (ser (mem (rep ptr) exdrop)
                             (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                      -> (i31 (val ptr imcopy imdrop)))))]
        new ;; [(prod (val (prod ptr i32) excopy exdrop)
                  (ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                  (coderef (val i32 imcopy imdrop)
                    ((ref (val ptr excopy exdrop) (base gc)
                       (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                         (ser (mem (rep ptr) exdrop)
                           (ref (val ptr excopy exdrop) (base gc)
                             (struct (mem (prod (rep ptr)) imdrop)
                               (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                         (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                    -> (i31 (val ptr imcopy imdrop)))))]
               ->
               [(ref (val ptr excopy exdrop) (base gc)
                  (ser (mem (rep (prod ptr i32)) exdrop)
                    (prod (val (prod ptr i32) excopy exdrop)
                      (ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                      (coderef (val i32 imcopy imdrop)
                        ((ref (val ptr excopy exdrop) (base gc)
                           (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                             (ser (mem (rep ptr) exdrop)
                               (ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr)) imdrop)
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                             (ser (mem (rep ptr) exdrop)
                               (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                        -> (i31 (val ptr imcopy imdrop)))))))]
        cast ;; [(ref (val ptr excopy exdrop) (base gc)
                   (ser (mem (rep (prod ptr i32)) exdrop)
                     (prod (val (prod ptr i32) excopy exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                       (coderef (val i32 imcopy imdrop)
                         ((ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc)
                                  (struct (mem (prod (rep ptr)) imdrop)
                                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                         -> (i31 (val ptr imcopy imdrop)))))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep i32) imdrop)
                       (coderef (val i32 imcopy imdrop)
                         ((ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc)
                                  (struct (mem (prod (rep ptr)) imdrop)
                                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                         -> (i31 (val ptr imcopy imdrop)))))))]
        pack ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep i32) imdrop)
                       (coderef (val i32 imcopy imdrop)
                         ((ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc)
                                  (struct (mem (prod (rep ptr)) imdrop)
                                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                         -> (i31 (val ptr imcopy imdrop)))))))]
                ->
                [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                   (ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) exdrop)
                                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                           -> (i31 (val ptr imcopy imdrop))))))))]
        local.set 2 ;; [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                          (ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) exdrop)
                                         (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                  -> (i31 (val ptr imcopy imdrop))))))))]
                       -> []
        local.get 2 ;; [] ->
                       [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                          (ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) exdrop)
                                         (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                  -> (i31 (val ptr imcopy imdrop))))))))]
        copy ;; [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                   (ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) exdrop)
                                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                           -> (i31 (val ptr imcopy imdrop))))))))]
                ->
                [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                   (ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) exdrop)
                                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                           -> (i31 (val ptr imcopy imdrop))))))))
                (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                  (ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                      (ser (mem (rep i32) imdrop)
                        (coderef (val i32 imcopy imdrop)
                          ((ref (val ptr excopy exdrop) (base gc)
                             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                               (ser (mem (rep ptr) exdrop) (var 0))
                               (ser (mem (rep ptr) exdrop)
                                 (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                          -> (i31 (val ptr imcopy imdrop))))))))]
        local.set 2 ;; [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                          (ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) exdrop)
                                         (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                  -> (i31 (val ptr imcopy imdrop))))))))]
                       -> []
        unpack (localfx [0 => (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
                 [1 => (i31 (val ptr imcopy imdrop))]
                 [2 =>
                 (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                   (ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) exdrop)
                                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                           -> (i31 (val ptr imcopy imdrop))))))))]
                 [3 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [4 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [5 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [6 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [7 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [8 => (plug (val (prod i32) imcopy imdrop) (prod i32))])
          local.set 3 ;; [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) exdrop)
                                         (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
                         -> []
          local.get 3 ;; [] ->
                         [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) exdrop)
                                         (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
          copy ;; [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) exdrop)
                                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                           -> (i31 (val ptr imcopy imdrop)))))))]
                  ->
                  [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) exdrop)
                                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                           -> (i31 (val ptr imcopy imdrop)))))))
                  (ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                      (ser (mem (rep i32) imdrop)
                        (coderef (val i32 imcopy imdrop)
                          ((ref (val ptr excopy exdrop) (base gc)
                             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                               (ser (mem (rep ptr) exdrop) (var 0))
                               (ser (mem (rep ptr) exdrop)
                                 (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                          -> (i31 (val ptr imcopy imdrop)))))))]
          local.set 3 ;; [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) exdrop)
                                         (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
                         -> []
          load (path 0) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                     (ser (mem (rep ptr) exdrop) (var 0))
                                     (ser (mem (rep i32) imdrop)
                                       (coderef (val i32 imcopy imdrop)
                                         ((ref (val ptr excopy exdrop) (base gc)
                                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                              (ser (mem (rep ptr) exdrop) (var 0))
                                              (ser (mem (rep ptr) exdrop)
                                                (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                         -> (i31 (val ptr imcopy imdrop)))))))]
                                ->
                                [(ref (val ptr excopy exdrop) (base gc)
                                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                     (ser (mem (rep ptr) exdrop) (var 0))
                                     (ser (mem (rep i32) imdrop)
                                       (coderef (val i32 imcopy imdrop)
                                         ((ref (val ptr excopy exdrop) (base gc)
                                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                              (ser (mem (rep ptr) exdrop) (var 0))
                                              (ser (mem (rep ptr) exdrop)
                                                (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                         -> (i31 (val ptr imcopy imdrop)))))))
                                (var 0)]
          local.set 4 ;; [(var 0)] -> []
          drop ;; [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) exdrop)
                                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                           -> (i31 (val ptr imcopy imdrop)))))))]
                  -> []
          local.get 4 ;; [] -> [(var 0)]
          local.set 5 ;; [(var 0)] -> []
          local.get 3 ;; [] ->
                         [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) exdrop)
                                         (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
          copy ;; [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) exdrop)
                                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                           -> (i31 (val ptr imcopy imdrop)))))))]
                  ->
                  [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) exdrop)
                                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                           -> (i31 (val ptr imcopy imdrop)))))))
                  (ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                      (ser (mem (rep i32) imdrop)
                        (coderef (val i32 imcopy imdrop)
                          ((ref (val ptr excopy exdrop) (base gc)
                             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                               (ser (mem (rep ptr) exdrop) (var 0))
                               (ser (mem (rep ptr) exdrop)
                                 (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                          -> (i31 (val ptr imcopy imdrop)))))))]
          local.set 3 ;; [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) exdrop)
                                         (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
                         -> []
          load (path 1) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                     (ser (mem (rep ptr) exdrop) (var 0))
                                     (ser (mem (rep i32) imdrop)
                                       (coderef (val i32 imcopy imdrop)
                                         ((ref (val ptr excopy exdrop) (base gc)
                                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                              (ser (mem (rep ptr) exdrop) (var 0))
                                              (ser (mem (rep ptr) exdrop)
                                                (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                         -> (i31 (val ptr imcopy imdrop)))))))]
                                ->
                                [(ref (val ptr excopy exdrop) (base gc)
                                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                     (ser (mem (rep ptr) exdrop) (var 0))
                                     (ser (mem (rep i32) imdrop)
                                       (coderef (val i32 imcopy imdrop)
                                         ((ref (val ptr excopy exdrop) (base gc)
                                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                              (ser (mem (rep ptr) exdrop) (var 0))
                                              (ser (mem (rep ptr) exdrop)
                                                (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                         -> (i31 (val ptr imcopy imdrop)))))))
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) exdrop)
                                         (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                  -> (i31 (val ptr imcopy imdrop))))]
          local.set 6 ;; [(coderef (val i32 imcopy imdrop)
                            ((ref (val ptr excopy exdrop) (base gc)
                               (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                 (ser (mem (rep ptr) exdrop) (var 0))
                                 (ser (mem (rep ptr) exdrop)
                                   (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                            -> (i31 (val ptr imcopy imdrop))))]
                         -> []
          drop ;; [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) exdrop)
                                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                           -> (i31 (val ptr imcopy imdrop)))))))]
                  -> []
          local.get 6 ;; [] ->
                         [(coderef (val i32 imcopy imdrop)
                            ((ref (val ptr excopy exdrop) (base gc)
                               (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                 (ser (mem (rep ptr) exdrop) (var 0))
                                 (ser (mem (rep ptr) exdrop)
                                   (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                            -> (i31 (val ptr imcopy imdrop))))]
          local.set 7 ;; [(coderef (val i32 imcopy imdrop)
                            ((ref (val ptr excopy exdrop) (base gc)
                               (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                 (ser (mem (rep ptr) exdrop) (var 0))
                                 (ser (mem (rep ptr) exdrop)
                                   (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                            -> (i31 (val ptr imcopy imdrop))))]
                         -> []
          group ;; [] -> [(prod (val (prod) imcopy imdrop))]
          new ;; [(prod (val (prod) imcopy imdrop))] ->
                 [(ref (val ptr excopy exdrop) (base gc) (ser (mem (rep (prod)) imdrop) (prod (val (prod) imcopy imdrop))))]
          cast ;; [(ref (val ptr excopy exdrop) (base gc)
                     (ser (mem (rep (prod)) imdrop) (prod (val (prod) imcopy imdrop))))]
                  -> [(ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
          local.get 7 ;; [] ->
                         [(coderef (val i32 imcopy imdrop)
                            ((ref (val ptr excopy exdrop) (base gc)
                               (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                 (ser (mem (rep ptr) exdrop) (var 0))
                                 (ser (mem (rep ptr) exdrop)
                                   (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                            -> (i31 (val ptr imcopy imdrop))))]
          copy ;; [(coderef (val i32 imcopy imdrop)
                     ((ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr) (rep ptr)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                          (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                     -> (i31 (val ptr imcopy imdrop))))]
                  ->
                  [(coderef (val i32 imcopy imdrop)
                     ((ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr) (rep ptr)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                          (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                     -> (i31 (val ptr imcopy imdrop))))
                  (coderef (val i32 imcopy imdrop)
                    ((ref (val ptr excopy exdrop) (base gc)
                       (struct (mem (prod (rep ptr) (rep ptr)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                         (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                    -> (i31 (val ptr imcopy imdrop))))]
          local.set 7 ;; [(coderef (val i32 imcopy imdrop)
                            ((ref (val ptr excopy exdrop) (base gc)
                               (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                 (ser (mem (rep ptr) exdrop) (var 0))
                                 (ser (mem (rep ptr) exdrop)
                                   (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                            -> (i31 (val ptr imcopy imdrop))))]
                         -> []
          call_indirect ;; [(ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) exdrop)
                                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                           (coderef (val i32 imcopy imdrop)
                             ((ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                  (ser (mem (rep ptr) exdrop) (var 0))
                                  (ser (mem (rep ptr) exdrop)
                                    (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                             -> (i31 (val ptr imcopy imdrop))))]
                           -> [(i31 (val ptr imcopy imdrop))]
          local.get 7 ;; [] ->
                         [(coderef (val i32 imcopy imdrop)
                            ((ref (val ptr excopy exdrop) (base gc)
                               (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                 (ser (mem (rep ptr) exdrop) (var 0))
                                 (ser (mem (rep ptr) exdrop)
                                   (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                            -> (i31 (val ptr imcopy imdrop))))]
          drop ;; [(coderef (val i32 imcopy imdrop)
                     ((ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr) (rep ptr)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                          (ser (mem (rep ptr) exdrop) (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                     -> (i31 (val ptr imcopy imdrop))))]
                  -> []
          local.get 5 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get 3 ;; [] ->
                         [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) exdrop)
                                         (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
          drop ;; [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) exdrop)
                                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                           -> (i31 (val ptr imcopy imdrop)))))))]
                  -> []
        end ;; [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                  (ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                      (ser (mem (rep i32) imdrop)
                        (coderef (val i32 imcopy imdrop)
                          ((ref (val ptr excopy exdrop) (base gc)
                             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                               (ser (mem (rep ptr) exdrop) (var 0))
                               (ser (mem (rep ptr) exdrop)
                                 (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                          -> (i31 (val ptr imcopy imdrop))))))))]
               -> [(i31 (val ptr imcopy imdrop))]
        local.get 2 ;; [] ->
                       [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                          (ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) exdrop)
                                         (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                                  -> (i31 (val ptr imcopy imdrop))))))))]
        drop ;; [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                   (ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) exdrop)
                                  (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))))))
                           -> (i31 (val ptr imcopy imdrop))))))))]
                -> []
        local.get 1 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        drop ;; [(i31 (val ptr imcopy imdrop))] -> [])
      (table 0 1)
      (export "_start" (func 1)))
    -----------closure_complex-----------
    (module
      (func
          ((ref (val ptr excopy exdrop) (base gc)
             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
               (ser (mem (rep ptr) exdrop)
                 (ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                         (ref (val ptr excopy exdrop) (base gc)
                           (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                             (ser (mem (rep ptr) exdrop) (var 0))
                             (ser (mem (rep i32) imdrop)
                               (coderef (val i32 imcopy imdrop)
                                 ((ref (val ptr excopy exdrop) (base gc)
                                    (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                      (ser (mem (rep ptr) exdrop) (var 0))
                                      (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                 -> (i31 (val ptr imcopy imdrop)))))))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
               (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
          -> (i31 (val ptr imcopy imdrop))) (local ptr ptr ptr ptr ptr ptr ptr ptr ptr ptr ptr ptr ptr ptr)
        local.get 0 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                  (ser (mem (rep ptr) exdrop)
                                    (exists.type (val ptr excopy exdrop)
                                      (val ptr excopy exdrop)
                                      (ref (val ptr excopy exdrop) (base gc)
                                        (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                          (ser (mem (rep ptr) exdrop) (var 0))
                                          (ser (mem (rep i32) imdrop)
                                            (coderef (val i32 imcopy imdrop)
                                              ((ref (val ptr excopy exdrop)
                                                 (base gc)
                                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                                   (ser (mem (rep ptr) exdrop) (var 0))
                                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                              -> (i31 (val ptr imcopy imdrop)))))))))
                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        copy ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                           (ser (mem (rep ptr) exdrop)
                             (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                               (ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                   (ser (mem (rep ptr) exdrop) (var 0))
                                   (ser (mem (rep i32) imdrop)
                                     (coderef (val i32 imcopy imdrop)
                                       ((ref (val ptr excopy exdrop) (base gc)
                                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                            (ser (mem (rep ptr) exdrop) (var 0))
                                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                       -> (i31 (val ptr imcopy imdrop)))))))))
                           (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                           (ser (mem (rep ptr) exdrop)
                             (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                               (ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                   (ser (mem (rep ptr) exdrop) (var 0))
                                   (ser (mem (rep i32) imdrop)
                                     (coderef (val i32 imcopy imdrop)
                                       ((ref (val ptr excopy exdrop) (base gc)
                                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                            (ser (mem (rep ptr) exdrop) (var 0))
                                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                       -> (i31 (val ptr imcopy imdrop)))))))))
                           (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                (ref (val ptr excopy exdrop) (base gc)
                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                    (ser (mem (rep ptr) exdrop)
                      (ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                          (ser (mem (rep ptr) exdrop)
                            (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                              (ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                  (ser (mem (rep ptr) exdrop) (var 0))
                                  (ser (mem (rep i32) imdrop)
                                    (coderef (val i32 imcopy imdrop)
                                      ((ref (val ptr excopy exdrop) (base gc)
                                         (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                           (ser (mem (rep ptr) exdrop) (var 0))
                                           (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                      -> (i31 (val ptr imcopy imdrop)))))))))
                          (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        local.set 0 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                  (ser (mem (rep ptr) exdrop)
                                    (exists.type (val ptr excopy exdrop)
                                      (val ptr excopy exdrop)
                                      (ref (val ptr excopy exdrop) (base gc)
                                        (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                          (ser (mem (rep ptr) exdrop) (var 0))
                                          (ser (mem (rep i32) imdrop)
                                            (coderef (val i32 imcopy imdrop)
                                              ((ref (val ptr excopy exdrop)
                                                 (base gc)
                                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                                   (ser (mem (rep ptr) exdrop) (var 0))
                                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                              -> (i31 (val ptr imcopy imdrop)))))))))
                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                       -> []
        load (path 0) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc)
                                       (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                         (ser (mem (rep ptr) exdrop)
                                           (exists.type (val ptr excopy exdrop)
                                             (val ptr excopy exdrop)
                                             (ref (val ptr excopy exdrop)
                                               (base gc)
                                               (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                                 (ser (mem (rep ptr) exdrop) (var 0))
                                                 (ser (mem (rep i32) imdrop)
                                                   (coderef (val i32 imcopy imdrop)
                                                     ((ref (val ptr excopy exdrop)
                                                        (base gc)
                                                        (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                                          (ser (mem (rep ptr) exdrop) (var 0))
                                                          (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                                     -> (i31 (val ptr imcopy imdrop)))))))))
                                         (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                              ->
                              [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc)
                                       (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                         (ser (mem (rep ptr) exdrop)
                                           (exists.type (val ptr excopy exdrop)
                                             (val ptr excopy exdrop)
                                             (ref (val ptr excopy exdrop)
                                               (base gc)
                                               (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                                 (ser (mem (rep ptr) exdrop) (var 0))
                                                 (ser (mem (rep i32) imdrop)
                                                   (coderef (val i32 imcopy imdrop)
                                                     ((ref (val ptr excopy exdrop)
                                                        (base gc)
                                                        (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                                          (ser (mem (rep ptr) exdrop) (var 0))
                                                          (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                                     -> (i31 (val ptr imcopy imdrop)))))))))
                                         (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                              (ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                  (ser (mem (rep ptr) exdrop)
                                    (exists.type (val ptr excopy exdrop)
                                      (val ptr excopy exdrop)
                                      (ref (val ptr excopy exdrop) (base gc)
                                        (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                          (ser (mem (rep ptr) exdrop) (var 0))
                                          (ser (mem (rep i32) imdrop)
                                            (coderef (val i32 imcopy imdrop)
                                              ((ref (val ptr excopy exdrop)
                                                 (base gc)
                                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                                   (ser (mem (rep ptr) exdrop) (var 0))
                                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                              -> (i31 (val ptr imcopy imdrop)))))))))
                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        local.set 1 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                                (ref (val ptr excopy exdrop) (base gc)
                                  (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                    (ser (mem (rep ptr) exdrop) (var 0))
                                    (ser (mem (rep i32) imdrop)
                                      (coderef (val i32 imcopy imdrop)
                                        ((ref (val ptr excopy exdrop) (base gc)
                                           (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                             (ser (mem (rep ptr) exdrop) (var 0))
                                             (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                        -> (i31 (val ptr imcopy imdrop)))))))))
                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                       -> []
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                           (ser (mem (rep ptr) exdrop)
                             (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                               (ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                   (ser (mem (rep ptr) exdrop) (var 0))
                                   (ser (mem (rep i32) imdrop)
                                     (coderef (val i32 imcopy imdrop)
                                       ((ref (val ptr excopy exdrop) (base gc)
                                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                            (ser (mem (rep ptr) exdrop) (var 0))
                                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                       -> (i31 (val ptr imcopy imdrop)))))))))
                           (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                -> []
        local.get 1 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                                (ref (val ptr excopy exdrop) (base gc)
                                  (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                    (ser (mem (rep ptr) exdrop) (var 0))
                                    (ser (mem (rep i32) imdrop)
                                      (coderef (val i32 imcopy imdrop)
                                        ((ref (val ptr excopy exdrop) (base gc)
                                           (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                             (ser (mem (rep ptr) exdrop) (var 0))
                                             (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                        -> (i31 (val ptr imcopy imdrop)))))))))
                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        local.set 2 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                                (ref (val ptr excopy exdrop) (base gc)
                                  (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                    (ser (mem (rep ptr) exdrop) (var 0))
                                    (ser (mem (rep i32) imdrop)
                                      (coderef (val i32 imcopy imdrop)
                                        ((ref (val ptr excopy exdrop) (base gc)
                                           (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                             (ser (mem (rep ptr) exdrop) (var 0))
                                             (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                        -> (i31 (val ptr imcopy imdrop)))))))))
                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                       -> []
        local.get 0 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                  (ser (mem (rep ptr) exdrop)
                                    (exists.type (val ptr excopy exdrop)
                                      (val ptr excopy exdrop)
                                      (ref (val ptr excopy exdrop) (base gc)
                                        (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                          (ser (mem (rep ptr) exdrop) (var 0))
                                          (ser (mem (rep i32) imdrop)
                                            (coderef (val i32 imcopy imdrop)
                                              ((ref (val ptr excopy exdrop)
                                                 (base gc)
                                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                                   (ser (mem (rep ptr) exdrop) (var 0))
                                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                              -> (i31 (val ptr imcopy imdrop)))))))))
                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        copy ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                           (ser (mem (rep ptr) exdrop)
                             (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                               (ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                   (ser (mem (rep ptr) exdrop) (var 0))
                                   (ser (mem (rep i32) imdrop)
                                     (coderef (val i32 imcopy imdrop)
                                       ((ref (val ptr excopy exdrop) (base gc)
                                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                            (ser (mem (rep ptr) exdrop) (var 0))
                                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                       -> (i31 (val ptr imcopy imdrop)))))))))
                           (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                           (ser (mem (rep ptr) exdrop)
                             (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                               (ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                   (ser (mem (rep ptr) exdrop) (var 0))
                                   (ser (mem (rep i32) imdrop)
                                     (coderef (val i32 imcopy imdrop)
                                       ((ref (val ptr excopy exdrop) (base gc)
                                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                            (ser (mem (rep ptr) exdrop) (var 0))
                                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                       -> (i31 (val ptr imcopy imdrop)))))))))
                           (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                (ref (val ptr excopy exdrop) (base gc)
                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                    (ser (mem (rep ptr) exdrop)
                      (ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                          (ser (mem (rep ptr) exdrop)
                            (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                              (ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                  (ser (mem (rep ptr) exdrop) (var 0))
                                  (ser (mem (rep i32) imdrop)
                                    (coderef (val i32 imcopy imdrop)
                                      ((ref (val ptr excopy exdrop) (base gc)
                                         (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                           (ser (mem (rep ptr) exdrop) (var 0))
                                           (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                      -> (i31 (val ptr imcopy imdrop)))))))))
                          (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        local.set 0 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                  (ser (mem (rep ptr) exdrop)
                                    (exists.type (val ptr excopy exdrop)
                                      (val ptr excopy exdrop)
                                      (ref (val ptr excopy exdrop) (base gc)
                                        (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                          (ser (mem (rep ptr) exdrop) (var 0))
                                          (ser (mem (rep i32) imdrop)
                                            (coderef (val i32 imcopy imdrop)
                                              ((ref (val ptr excopy exdrop)
                                                 (base gc)
                                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                                   (ser (mem (rep ptr) exdrop) (var 0))
                                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                              -> (i31 (val ptr imcopy imdrop)))))))))
                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                       -> []
        load (path 1) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc)
                                       (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                         (ser (mem (rep ptr) exdrop)
                                           (exists.type (val ptr excopy exdrop)
                                             (val ptr excopy exdrop)
                                             (ref (val ptr excopy exdrop)
                                               (base gc)
                                               (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                                 (ser (mem (rep ptr) exdrop) (var 0))
                                                 (ser (mem (rep i32) imdrop)
                                                   (coderef (val i32 imcopy imdrop)
                                                     ((ref (val ptr excopy exdrop)
                                                        (base gc)
                                                        (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                                          (ser (mem (rep ptr) exdrop) (var 0))
                                                          (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                                     -> (i31 (val ptr imcopy imdrop)))))))))
                                         (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                              ->
                              [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc)
                                       (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                         (ser (mem (rep ptr) exdrop)
                                           (exists.type (val ptr excopy exdrop)
                                             (val ptr excopy exdrop)
                                             (ref (val ptr excopy exdrop)
                                               (base gc)
                                               (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                                 (ser (mem (rep ptr) exdrop) (var 0))
                                                 (ser (mem (rep i32) imdrop)
                                                   (coderef (val i32 imcopy imdrop)
                                                     ((ref (val ptr excopy exdrop)
                                                        (base gc)
                                                        (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                                          (ser (mem (rep ptr) exdrop) (var 0))
                                                          (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                                     -> (i31 (val ptr imcopy imdrop)))))))))
                                         (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                              (i31 (val ptr imcopy imdrop))]
        local.set 3 ;; [(i31 (val ptr imcopy imdrop))] -> []
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                           (ser (mem (rep ptr) exdrop)
                             (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                               (ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                   (ser (mem (rep ptr) exdrop) (var 0))
                                   (ser (mem (rep i32) imdrop)
                                     (coderef (val i32 imcopy imdrop)
                                       ((ref (val ptr excopy exdrop) (base gc)
                                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                            (ser (mem (rep ptr) exdrop) (var 0))
                                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                       -> (i31 (val ptr imcopy imdrop)))))))))
                           (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                -> []
        local.get 3 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        local.set 4 ;; [(i31 (val ptr imcopy imdrop))] -> []
        local.get 2 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                                (ref (val ptr excopy exdrop) (base gc)
                                  (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                    (ser (mem (rep ptr) exdrop) (var 0))
                                    (ser (mem (rep i32) imdrop)
                                      (coderef (val i32 imcopy imdrop)
                                        ((ref (val ptr excopy exdrop) (base gc)
                                           (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                             (ser (mem (rep ptr) exdrop) (var 0))
                                             (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                        -> (i31 (val ptr imcopy imdrop)))))))))
                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        copy ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                         (ref (val ptr excopy exdrop) (base gc)
                           (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                             (ser (mem (rep ptr) exdrop) (var 0))
                             (ser (mem (rep i32) imdrop)
                               (coderef (val i32 imcopy imdrop)
                                 ((ref (val ptr excopy exdrop) (base gc)
                                    (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                      (ser (mem (rep ptr) exdrop) (var 0))
                                      (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                 -> (i31 (val ptr imcopy imdrop)))))))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                         (ref (val ptr excopy exdrop) (base gc)
                           (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                             (ser (mem (rep ptr) exdrop) (var 0))
                             (ser (mem (rep i32) imdrop)
                               (coderef (val i32 imcopy imdrop)
                                 ((ref (val ptr excopy exdrop) (base gc)
                                    (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                      (ser (mem (rep ptr) exdrop) (var 0))
                                      (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                 -> (i31 (val ptr imcopy imdrop)))))))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                (ref (val ptr excopy exdrop) (base gc)
                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                    (ser (mem (rep ptr) exdrop)
                      (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                        (ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                            (ser (mem (rep ptr) exdrop) (var 0))
                            (ser (mem (rep i32) imdrop)
                              (coderef (val i32 imcopy imdrop)
                                ((ref (val ptr excopy exdrop) (base gc)
                                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                     (ser (mem (rep ptr) exdrop) (var 0))
                                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                -> (i31 (val ptr imcopy imdrop)))))))))
                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        local.set 2 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                                (ref (val ptr excopy exdrop) (base gc)
                                  (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                    (ser (mem (rep ptr) exdrop) (var 0))
                                    (ser (mem (rep i32) imdrop)
                                      (coderef (val i32 imcopy imdrop)
                                        ((ref (val ptr excopy exdrop) (base gc)
                                           (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                             (ser (mem (rep ptr) exdrop) (var 0))
                                             (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                        -> (i31 (val ptr imcopy imdrop)))))))))
                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                       -> []
        load (path 0) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (exists.type (val ptr excopy exdrop)
                                       (val ptr excopy exdrop)
                                       (ref (val ptr excopy exdrop) (base gc)
                                         (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                           (ser (mem (rep ptr) exdrop) (var 0))
                                           (ser (mem (rep i32) imdrop)
                                             (coderef (val i32 imcopy imdrop)
                                               ((ref (val ptr excopy exdrop)
                                                  (base gc)
                                                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                                    (ser (mem (rep ptr) exdrop) (var 0))
                                                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                               -> (i31 (val ptr imcopy imdrop)))))))))
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                              ->
                              [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (exists.type (val ptr excopy exdrop)
                                       (val ptr excopy exdrop)
                                       (ref (val ptr excopy exdrop) (base gc)
                                         (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                           (ser (mem (rep ptr) exdrop) (var 0))
                                           (ser (mem (rep i32) imdrop)
                                             (coderef (val i32 imcopy imdrop)
                                               ((ref (val ptr excopy exdrop)
                                                  (base gc)
                                                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                                    (ser (mem (rep ptr) exdrop) (var 0))
                                                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                               -> (i31 (val ptr imcopy imdrop)))))))))
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                              (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                                (ref (val ptr excopy exdrop) (base gc)
                                  (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                    (ser (mem (rep ptr) exdrop) (var 0))
                                    (ser (mem (rep i32) imdrop)
                                      (coderef (val i32 imcopy imdrop)
                                        ((ref (val ptr excopy exdrop) (base gc)
                                           (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                             (ser (mem (rep ptr) exdrop) (var 0))
                                             (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                        -> (i31 (val ptr imcopy imdrop))))))))]
        local.set 5 ;; [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                          (ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop))))))))]
                       -> []
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                         (ref (val ptr excopy exdrop) (base gc)
                           (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                             (ser (mem (rep ptr) exdrop) (var 0))
                             (ser (mem (rep i32) imdrop)
                               (coderef (val i32 imcopy imdrop)
                                 ((ref (val ptr excopy exdrop) (base gc)
                                    (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                      (ser (mem (rep ptr) exdrop) (var 0))
                                      (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                 -> (i31 (val ptr imcopy imdrop)))))))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                -> []
        local.get 5 ;; [] ->
                       [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                          (ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop))))))))]
        local.set 6 ;; [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                          (ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop))))))))]
                       -> []
        local.get 2 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                                (ref (val ptr excopy exdrop) (base gc)
                                  (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                    (ser (mem (rep ptr) exdrop) (var 0))
                                    (ser (mem (rep i32) imdrop)
                                      (coderef (val i32 imcopy imdrop)
                                        ((ref (val ptr excopy exdrop) (base gc)
                                           (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                             (ser (mem (rep ptr) exdrop) (var 0))
                                             (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                        -> (i31 (val ptr imcopy imdrop)))))))))
                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        copy ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                         (ref (val ptr excopy exdrop) (base gc)
                           (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                             (ser (mem (rep ptr) exdrop) (var 0))
                             (ser (mem (rep i32) imdrop)
                               (coderef (val i32 imcopy imdrop)
                                 ((ref (val ptr excopy exdrop) (base gc)
                                    (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                      (ser (mem (rep ptr) exdrop) (var 0))
                                      (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                 -> (i31 (val ptr imcopy imdrop)))))))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                         (ref (val ptr excopy exdrop) (base gc)
                           (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                             (ser (mem (rep ptr) exdrop) (var 0))
                             (ser (mem (rep i32) imdrop)
                               (coderef (val i32 imcopy imdrop)
                                 ((ref (val ptr excopy exdrop) (base gc)
                                    (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                      (ser (mem (rep ptr) exdrop) (var 0))
                                      (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                 -> (i31 (val ptr imcopy imdrop)))))))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                (ref (val ptr excopy exdrop) (base gc)
                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                    (ser (mem (rep ptr) exdrop)
                      (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                        (ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                            (ser (mem (rep ptr) exdrop) (var 0))
                            (ser (mem (rep i32) imdrop)
                              (coderef (val i32 imcopy imdrop)
                                ((ref (val ptr excopy exdrop) (base gc)
                                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                     (ser (mem (rep ptr) exdrop) (var 0))
                                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                -> (i31 (val ptr imcopy imdrop)))))))))
                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        local.set 2 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                                (ref (val ptr excopy exdrop) (base gc)
                                  (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                    (ser (mem (rep ptr) exdrop) (var 0))
                                    (ser (mem (rep i32) imdrop)
                                      (coderef (val i32 imcopy imdrop)
                                        ((ref (val ptr excopy exdrop) (base gc)
                                           (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                             (ser (mem (rep ptr) exdrop) (var 0))
                                             (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                        -> (i31 (val ptr imcopy imdrop)))))))))
                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                       -> []
        load (path 1) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (exists.type (val ptr excopy exdrop)
                                       (val ptr excopy exdrop)
                                       (ref (val ptr excopy exdrop) (base gc)
                                         (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                           (ser (mem (rep ptr) exdrop) (var 0))
                                           (ser (mem (rep i32) imdrop)
                                             (coderef (val i32 imcopy imdrop)
                                               ((ref (val ptr excopy exdrop)
                                                  (base gc)
                                                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                                    (ser (mem (rep ptr) exdrop) (var 0))
                                                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                               -> (i31 (val ptr imcopy imdrop)))))))))
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                              ->
                              [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (exists.type (val ptr excopy exdrop)
                                       (val ptr excopy exdrop)
                                       (ref (val ptr excopy exdrop) (base gc)
                                         (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                           (ser (mem (rep ptr) exdrop) (var 0))
                                           (ser (mem (rep i32) imdrop)
                                             (coderef (val i32 imcopy imdrop)
                                               ((ref (val ptr excopy exdrop)
                                                  (base gc)
                                                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                                    (ser (mem (rep ptr) exdrop) (var 0))
                                                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                               -> (i31 (val ptr imcopy imdrop)))))))))
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                              (i31 (val ptr imcopy imdrop))]
        local.set 7 ;; [(i31 (val ptr imcopy imdrop))] -> []
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                         (ref (val ptr excopy exdrop) (base gc)
                           (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                             (ser (mem (rep ptr) exdrop) (var 0))
                             (ser (mem (rep i32) imdrop)
                               (coderef (val i32 imcopy imdrop)
                                 ((ref (val ptr excopy exdrop) (base gc)
                                    (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                      (ser (mem (rep ptr) exdrop) (var 0))
                                      (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                 -> (i31 (val ptr imcopy imdrop)))))))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                -> []
        local.get 7 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        local.set 8 ;; [(i31 (val ptr imcopy imdrop))] -> []
        local.get 6 ;; [] ->
                       [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                          (ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop))))))))]
        copy ;; [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                   (ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop))))))))]
                ->
                [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                   (ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop))))))))
                (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                  (ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                      (ser (mem (rep i32) imdrop)
                        (coderef (val i32 imcopy imdrop)
                          ((ref (val ptr excopy exdrop) (base gc)
                             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                               (ser (mem (rep ptr) exdrop) (var 0))
                               (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                          -> (i31 (val ptr imcopy imdrop))))))))]
        local.set 6 ;; [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                          (ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop))))))))]
                       -> []
        unpack (localfx
                 [0 =>
                 (ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                           (ser (mem (rep ptr) exdrop)
                             (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                               (ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                   (ser (mem (rep ptr) exdrop) (var 0))
                                   (ser (mem (rep i32) imdrop)
                                     (coderef (val i32 imcopy imdrop)
                                       ((ref (val ptr excopy exdrop) (base gc)
                                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                            (ser (mem (rep ptr) exdrop) (var 0))
                                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                       -> (i31 (val ptr imcopy imdrop)))))))))
                           (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                 [1 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [2 =>
                 (ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                         (ref (val ptr excopy exdrop) (base gc)
                           (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                             (ser (mem (rep ptr) exdrop) (var 0))
                             (ser (mem (rep i32) imdrop)
                               (coderef (val i32 imcopy imdrop)
                                 ((ref (val ptr excopy exdrop) (base gc)
                                    (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                      (ser (mem (rep ptr) exdrop) (var 0))
                                      (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                 -> (i31 (val ptr imcopy imdrop)))))))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                 [3 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [4 => (i31 (val ptr imcopy imdrop))] [5 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [6 =>
                 (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                   (ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop))))))))]
                 [7 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [8 => (i31 (val ptr imcopy imdrop))] [9 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [10 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [11 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [12 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [13 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [14 => (plug (val (prod i32) imcopy imdrop) (prod i32))])
          local.set 9 ;; [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
                         -> []
          local.get 9 ;; [] ->
                         [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
          copy ;; [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop)))))))]
                  ->
                  [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop)))))))
                  (ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                      (ser (mem (rep i32) imdrop)
                        (coderef (val i32 imcopy imdrop)
                          ((ref (val ptr excopy exdrop) (base gc)
                             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                               (ser (mem (rep ptr) exdrop) (var 0))
                               (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                          -> (i31 (val ptr imcopy imdrop)))))))]
          local.set 9 ;; [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
                         -> []
          load (path 0) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                     (ser (mem (rep ptr) exdrop) (var 0))
                                     (ser (mem (rep i32) imdrop)
                                       (coderef (val i32 imcopy imdrop)
                                         ((ref (val ptr excopy exdrop) (base gc)
                                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                              (ser (mem (rep ptr) exdrop) (var 0))
                                              (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                         -> (i31 (val ptr imcopy imdrop)))))))]
                                ->
                                [(ref (val ptr excopy exdrop) (base gc)
                                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                     (ser (mem (rep ptr) exdrop) (var 0))
                                     (ser (mem (rep i32) imdrop)
                                       (coderef (val i32 imcopy imdrop)
                                         ((ref (val ptr excopy exdrop) (base gc)
                                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                              (ser (mem (rep ptr) exdrop) (var 0))
                                              (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                         -> (i31 (val ptr imcopy imdrop)))))))
                                (var 0)]
          local.set 10 ;; [(var 0)] -> []
          drop ;; [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop)))))))]
                  -> []
          local.get 10 ;; [] -> [(var 0)]
          local.set 11 ;; [(var 0)] -> []
          local.get 9 ;; [] ->
                         [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
          copy ;; [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop)))))))]
                  ->
                  [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop)))))))
                  (ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                      (ser (mem (rep i32) imdrop)
                        (coderef (val i32 imcopy imdrop)
                          ((ref (val ptr excopy exdrop) (base gc)
                             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                               (ser (mem (rep ptr) exdrop) (var 0))
                               (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                          -> (i31 (val ptr imcopy imdrop)))))))]
          local.set 9 ;; [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
                         -> []
          load (path 1) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                     (ser (mem (rep ptr) exdrop) (var 0))
                                     (ser (mem (rep i32) imdrop)
                                       (coderef (val i32 imcopy imdrop)
                                         ((ref (val ptr excopy exdrop) (base gc)
                                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                              (ser (mem (rep ptr) exdrop) (var 0))
                                              (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                         -> (i31 (val ptr imcopy imdrop)))))))]
                                ->
                                [(ref (val ptr excopy exdrop) (base gc)
                                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                     (ser (mem (rep ptr) exdrop) (var 0))
                                     (ser (mem (rep i32) imdrop)
                                       (coderef (val i32 imcopy imdrop)
                                         ((ref (val ptr excopy exdrop) (base gc)
                                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                              (ser (mem (rep ptr) exdrop) (var 0))
                                              (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                         -> (i31 (val ptr imcopy imdrop)))))))
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop))))]
          local.set 12 ;; [(coderef (val i32 imcopy imdrop)
                             ((ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                  (ser (mem (rep ptr) exdrop) (var 0))
                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                             -> (i31 (val ptr imcopy imdrop))))]
                          -> []
          drop ;; [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop)))))))]
                  -> []
          local.get 12 ;; [] ->
                          [(coderef (val i32 imcopy imdrop)
                             ((ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                  (ser (mem (rep ptr) exdrop) (var 0))
                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                             -> (i31 (val ptr imcopy imdrop))))]
          local.set 13 ;; [(coderef (val i32 imcopy imdrop)
                             ((ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                  (ser (mem (rep ptr) exdrop) (var 0))
                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                             -> (i31 (val ptr imcopy imdrop))))]
                          -> []
          local.get 4 ;; [] -> [(i31 (val ptr imcopy imdrop))]
          copy ;; [(i31 (val ptr imcopy imdrop))] -> [(i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop))]
          local.set 4 ;; [(i31 (val ptr imcopy imdrop))] -> []
          local.get 13 ;; [] ->
                          [(coderef (val i32 imcopy imdrop)
                             ((ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                  (ser (mem (rep ptr) exdrop) (var 0))
                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                             -> (i31 (val ptr imcopy imdrop))))]
          copy ;; [(coderef (val i32 imcopy imdrop)
                     ((ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr) (rep ptr)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                          (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                     -> (i31 (val ptr imcopy imdrop))))]
                  ->
                  [(coderef (val i32 imcopy imdrop)
                     ((ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr) (rep ptr)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                          (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                     -> (i31 (val ptr imcopy imdrop))))
                  (coderef (val i32 imcopy imdrop)
                    ((ref (val ptr excopy exdrop) (base gc)
                       (struct (mem (prod (rep ptr) (rep ptr)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                         (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                    -> (i31 (val ptr imcopy imdrop))))]
          local.set 13 ;; [(coderef (val i32 imcopy imdrop)
                             ((ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                  (ser (mem (rep ptr) exdrop) (var 0))
                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                             -> (i31 (val ptr imcopy imdrop))))]
                          -> []
          call_indirect ;; [(ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           (coderef (val i32 imcopy imdrop)
                             ((ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                  (ser (mem (rep ptr) exdrop) (var 0))
                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                             -> (i31 (val ptr imcopy imdrop))))]
                           -> [(i31 (val ptr imcopy imdrop))]
          local.get 13 ;; [] ->
                          [(coderef (val i32 imcopy imdrop)
                             ((ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                  (ser (mem (rep ptr) exdrop) (var 0))
                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                             -> (i31 (val ptr imcopy imdrop))))]
          drop ;; [(coderef (val i32 imcopy imdrop)
                     ((ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr) (rep ptr)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                          (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                     -> (i31 (val ptr imcopy imdrop))))]
                  -> []
          local.get 11 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get 9 ;; [] ->
                         [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
          drop ;; [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop)))))))]
                  -> []
        end ;; [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                  (ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                      (ser (mem (rep i32) imdrop)
                        (coderef (val i32 imcopy imdrop)
                          ((ref (val ptr excopy exdrop) (base gc)
                             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                               (ser (mem (rep ptr) exdrop) (var 0))
                               (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                          -> (i31 (val ptr imcopy imdrop))))))))]
               -> [(i31 (val ptr imcopy imdrop))]
        untag ;; [(i31 (val ptr imcopy imdrop))] -> [(num (val i32 imcopy imdrop) i32)]
        local.get 8 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        copy ;; [(i31 (val ptr imcopy imdrop))] -> [(i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop))]
        local.set 8 ;; [(i31 (val ptr imcopy imdrop))] -> []
        untag ;; [(i31 (val ptr imcopy imdrop))] -> [(num (val i32 imcopy imdrop) i32)]
        i32.add ;; [(num (val i32 imcopy imdrop) i32) (num (val i32 imcopy imdrop) i32)] ->
                   [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        local.get 8 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        drop ;; [(i31 (val ptr imcopy imdrop))] -> []
        local.get 6 ;; [] ->
                       [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                          (ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop))))))))]
        drop ;; [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                   (ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop))))))))]
                -> []
        local.get 4 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        drop ;; [(i31 (val ptr imcopy imdrop))] -> []
        local.get 2 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                                (ref (val ptr excopy exdrop) (base gc)
                                  (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                    (ser (mem (rep ptr) exdrop) (var 0))
                                    (ser (mem (rep i32) imdrop)
                                      (coderef (val i32 imcopy imdrop)
                                        ((ref (val ptr excopy exdrop) (base gc)
                                           (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                             (ser (mem (rep ptr) exdrop) (var 0))
                                             (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                        -> (i31 (val ptr imcopy imdrop)))))))))
                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                         (ref (val ptr excopy exdrop) (base gc)
                           (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                             (ser (mem (rep ptr) exdrop) (var 0))
                             (ser (mem (rep i32) imdrop)
                               (coderef (val i32 imcopy imdrop)
                                 ((ref (val ptr excopy exdrop) (base gc)
                                    (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                      (ser (mem (rep ptr) exdrop) (var 0))
                                      (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                 -> (i31 (val ptr imcopy imdrop)))))))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                -> [])
      (func
          ((ref (val ptr excopy exdrop) (base gc)
             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
               (ser (mem (rep ptr) exdrop)
                 (ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
               (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
          -> (i31 (val ptr imcopy imdrop))) (local ptr ptr ptr ptr ptr ptr ptr)
        local.get 0 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr)) imdrop)
                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        copy ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                (ref (val ptr excopy exdrop) (base gc)
                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                    (ser (mem (rep ptr) exdrop)
                      (ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        local.set 0 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr)) imdrop)
                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                       -> []
        load (path 0) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc)
                                       (struct (mem (prod (rep ptr)) imdrop)
                                         (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                              ->
                              [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc)
                                       (struct (mem (prod (rep ptr)) imdrop)
                                         (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                              (ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr)) imdrop)
                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        local.set 1 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                       -> []
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                -> []
        local.get 1 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        local.set 2 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                       -> []
        local.get 0 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr)) imdrop)
                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        copy ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                (ref (val ptr excopy exdrop) (base gc)
                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                    (ser (mem (rep ptr) exdrop)
                      (ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        local.set 0 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                            (ser (mem (rep ptr) exdrop)
                              (ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr)) imdrop)
                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                       -> []
        load (path 1) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc)
                                       (struct (mem (prod (rep ptr)) imdrop)
                                         (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                              ->
                              [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (ref (val ptr excopy exdrop) (base gc)
                                       (struct (mem (prod (rep ptr)) imdrop)
                                         (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                              (i31 (val ptr imcopy imdrop))]
        local.set 3 ;; [(i31 (val ptr imcopy imdrop))] -> []
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                -> []
        local.get 3 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        local.set 4 ;; [(i31 (val ptr imcopy imdrop))] -> []
        local.get 2 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        copy ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                (ref (val ptr excopy exdrop) (base gc)
                  (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        local.set 2 ;; [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                       -> []
        load (path 0) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr)) imdrop)
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                              ->
                              [(ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr)) imdrop)
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                              (i31 (val ptr imcopy imdrop))]
        local.set 5 ;; [(i31 (val ptr imcopy imdrop))] -> []
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                -> []
        local.get 5 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        local.set 6 ;; [(i31 (val ptr imcopy imdrop))] -> []
        local.get 6 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        copy ;; [(i31 (val ptr imcopy imdrop))] -> [(i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop))]
        local.set 6 ;; [(i31 (val ptr imcopy imdrop))] -> []
        untag ;; [(i31 (val ptr imcopy imdrop))] -> [(num (val i32 imcopy imdrop) i32)]
        local.get 4 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        copy ;; [(i31 (val ptr imcopy imdrop))] -> [(i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop))]
        local.set 4 ;; [(i31 (val ptr imcopy imdrop))] -> []
        untag ;; [(i31 (val ptr imcopy imdrop))] -> [(num (val i32 imcopy imdrop) i32)]
        i32.add ;; [(num (val i32 imcopy imdrop) i32) (num (val i32 imcopy imdrop) i32)] ->
                   [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        local.get 6 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        drop ;; [(i31 (val ptr imcopy imdrop))] -> []
        local.get 4 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        drop ;; [(i31 (val ptr imcopy imdrop))] -> []
        local.get 2 ;; [] ->
                       [(ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        drop ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
                -> [])
      (func ((ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop))) -> (i31 (val ptr imcopy imdrop))) (local
          ptr ptr ptr ptr ptr ptr ptr ptr ptr)
        num_const 1 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
        tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
        local.set 1 ;; [(i31 (val ptr imcopy imdrop))] -> []
        local.get 1 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        copy ;; [(i31 (val ptr imcopy imdrop))] -> [(i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop))]
        local.set 1 ;; [(i31 (val ptr imcopy imdrop))] -> []
        group ;; [(i31 (val ptr imcopy imdrop))] -> [(prod (val (prod ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop)))]
        new ;; [(prod (val (prod ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop)))] ->
               [(ref (val ptr excopy exdrop) (base gc)
                  (ser (mem (rep (prod ptr)) imdrop) (prod (val (prod ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop)))))]
        cast ;; [(ref (val ptr excopy exdrop) (base gc)
                   (ser (mem (rep (prod ptr)) imdrop) (prod (val (prod ptr) imcopy imdrop) (i31 (val ptr imcopy imdrop)))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        coderef 1 ;; [] ->
                     [(coderef (val i32 imcopy imdrop)
                        ((ref (val ptr excopy exdrop) (base gc)
                           (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                             (ser (mem (rep ptr) exdrop)
                               (ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr)) imdrop)
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                             (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                        -> (i31 (val ptr imcopy imdrop))))]
        group ;; [(ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                 (coderef (val i32 imcopy imdrop)
                   ((ref (val ptr excopy exdrop) (base gc)
                      (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                        (ser (mem (rep ptr) exdrop)
                          (ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr)) imdrop)
                              (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                        (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                   -> (i31 (val ptr imcopy imdrop))))]
                 ->
                 [(prod (val (prod ptr i32) excopy exdrop)
                    (ref (val ptr excopy exdrop) (base gc)
                      (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                    (coderef (val i32 imcopy imdrop)
                      ((ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                           (ser (mem (rep ptr) exdrop)
                             (ref (val ptr excopy exdrop) (base gc)
                               (struct (mem (prod (rep ptr)) imdrop)
                                 (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                           (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                      -> (i31 (val ptr imcopy imdrop)))))]
        new ;; [(prod (val (prod ptr i32) excopy exdrop)
                  (ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                  (coderef (val i32 imcopy imdrop)
                    ((ref (val ptr excopy exdrop) (base gc)
                       (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                         (ser (mem (rep ptr) exdrop)
                           (ref (val ptr excopy exdrop) (base gc)
                             (struct (mem (prod (rep ptr)) imdrop)
                               (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                         (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                    -> (i31 (val ptr imcopy imdrop)))))]
               ->
               [(ref (val ptr excopy exdrop) (base gc)
                  (ser (mem (rep (prod ptr i32)) exdrop)
                    (prod (val (prod ptr i32) excopy exdrop)
                      (ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                      (coderef (val i32 imcopy imdrop)
                        ((ref (val ptr excopy exdrop) (base gc)
                           (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                             (ser (mem (rep ptr) exdrop)
                               (ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr)) imdrop)
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                             (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                        -> (i31 (val ptr imcopy imdrop)))))))]
        cast ;; [(ref (val ptr excopy exdrop) (base gc)
                   (ser (mem (rep (prod ptr i32)) exdrop)
                     (prod (val (prod ptr i32) excopy exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                       (coderef (val i32 imcopy imdrop)
                         ((ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc)
                                  (struct (mem (prod (rep ptr)) imdrop)
                                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                              (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                         -> (i31 (val ptr imcopy imdrop)))))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep i32) imdrop)
                       (coderef (val i32 imcopy imdrop)
                         ((ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc)
                                  (struct (mem (prod (rep ptr)) imdrop)
                                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                              (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                         -> (i31 (val ptr imcopy imdrop)))))))]
        pack ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr)) imdrop) (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep i32) imdrop)
                       (coderef (val i32 imcopy imdrop)
                         ((ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc)
                                  (struct (mem (prod (rep ptr)) imdrop)
                                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                              (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                         -> (i31 (val ptr imcopy imdrop)))))))]
                ->
                [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                   (ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop))))))))]
        local.set 2 ;; [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                          (ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop))))))))]
                       -> []
        local.get 2 ;; [] ->
                       [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                          (ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop))))))))]
        copy ;; [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                   (ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop))))))))]
                ->
                [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                   (ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop))))))))
                (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                  (ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                      (ser (mem (rep i32) imdrop)
                        (coderef (val i32 imcopy imdrop)
                          ((ref (val ptr excopy exdrop) (base gc)
                             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                               (ser (mem (rep ptr) exdrop) (var 0))
                               (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                          -> (i31 (val ptr imcopy imdrop))))))))]
        local.set 2 ;; [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                          (ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop))))))))]
                       -> []
        local.get 1 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        copy ;; [(i31 (val ptr imcopy imdrop))] -> [(i31 (val ptr imcopy imdrop)) (i31 (val ptr imcopy imdrop))]
        local.set 1 ;; [(i31 (val ptr imcopy imdrop))] -> []
        group ;; [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                    (ref (val ptr excopy exdrop) (base gc)
                      (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                        (ser (mem (rep i32) imdrop)
                          (coderef (val i32 imcopy imdrop)
                            ((ref (val ptr excopy exdrop) (base gc)
                               (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                 (ser (mem (rep ptr) exdrop) (var 0))
                                 (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                            -> (i31 (val ptr imcopy imdrop))))))))
                 (i31 (val ptr imcopy imdrop))] ->
                 [(prod (val (prod ptr ptr) excopy exdrop)
                    (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                      (ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                          (ser (mem (rep i32) imdrop)
                            (coderef (val i32 imcopy imdrop)
                              ((ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop) (var 0))
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                              -> (i31 (val ptr imcopy imdrop))))))))
                    (i31 (val ptr imcopy imdrop)))]
        new ;; [(prod (val (prod ptr ptr) excopy exdrop)
                  (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                    (ref (val ptr excopy exdrop) (base gc)
                      (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                        (ser (mem (rep i32) imdrop)
                          (coderef (val i32 imcopy imdrop)
                            ((ref (val ptr excopy exdrop) (base gc)
                               (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                 (ser (mem (rep ptr) exdrop) (var 0))
                                 (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                            -> (i31 (val ptr imcopy imdrop))))))))
                  (i31 (val ptr imcopy imdrop)))]
               ->
               [(ref (val ptr excopy exdrop) (base gc)
                  (ser (mem (rep (prod ptr ptr)) exdrop)
                    (prod (val (prod ptr ptr) excopy exdrop)
                      (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                        (ref (val ptr excopy exdrop) (base gc)
                          (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                            (ser (mem (rep ptr) exdrop) (var 0))
                            (ser (mem (rep i32) imdrop)
                              (coderef (val i32 imcopy imdrop)
                                ((ref (val ptr excopy exdrop) (base gc)
                                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                     (ser (mem (rep ptr) exdrop) (var 0))
                                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                -> (i31 (val ptr imcopy imdrop))))))))
                      (i31 (val ptr imcopy imdrop)))))]
        cast ;; [(ref (val ptr excopy exdrop) (base gc)
                   (ser (mem (rep (prod ptr ptr)) exdrop)
                     (prod (val (prod ptr ptr) excopy exdrop)
                       (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                         (ref (val ptr excopy exdrop) (base gc)
                           (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                             (ser (mem (rep ptr) exdrop) (var 0))
                             (ser (mem (rep i32) imdrop)
                               (coderef (val i32 imcopy imdrop)
                                 ((ref (val ptr excopy exdrop) (base gc)
                                    (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                      (ser (mem (rep ptr) exdrop) (var 0))
                                      (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                 -> (i31 (val ptr imcopy imdrop))))))))
                       (i31 (val ptr imcopy imdrop)))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                         (ref (val ptr excopy exdrop) (base gc)
                           (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                             (ser (mem (rep ptr) exdrop) (var 0))
                             (ser (mem (rep i32) imdrop)
                               (coderef (val i32 imcopy imdrop)
                                 ((ref (val ptr excopy exdrop) (base gc)
                                    (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                      (ser (mem (rep ptr) exdrop) (var 0))
                                      (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                 -> (i31 (val ptr imcopy imdrop)))))))))
                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))]
        coderef 0 ;; [] ->
                     [(coderef (val i32 imcopy imdrop)
                        ((ref (val ptr excopy exdrop) (base gc)
                           (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                             (ser (mem (rep ptr) exdrop)
                               (ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (exists.type (val ptr excopy exdrop)
                                       (val ptr excopy exdrop)
                                       (ref (val ptr excopy exdrop) (base gc)
                                         (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                           (ser (mem (rep ptr) exdrop) (var 0))
                                           (ser (mem (rep i32) imdrop)
                                             (coderef (val i32 imcopy imdrop)
                                               ((ref (val ptr excopy exdrop)
                                                  (base gc)
                                                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                                    (ser (mem (rep ptr) exdrop) (var 0))
                                                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                               -> (i31 (val ptr imcopy imdrop)))))))))
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                             (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                        -> (i31 (val ptr imcopy imdrop))))]
        group ;; [(ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                      (ser (mem (rep ptr) exdrop)
                        (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                          (ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop)))))))))
                      (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                 (coderef (val i32 imcopy imdrop)
                   ((ref (val ptr excopy exdrop) (base gc)
                      (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                        (ser (mem (rep ptr) exdrop)
                          (ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                              (ser (mem (rep ptr) exdrop)
                                (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                                  (ref (val ptr excopy exdrop) (base gc)
                                    (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                      (ser (mem (rep ptr) exdrop) (var 0))
                                      (ser (mem (rep i32) imdrop)
                                        (coderef (val i32 imcopy imdrop)
                                          ((ref (val ptr excopy exdrop) (base gc)
                                             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                               (ser (mem (rep ptr) exdrop) (var 0))
                                               (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                          -> (i31 (val ptr imcopy imdrop)))))))))
                              (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                        (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                   -> (i31 (val ptr imcopy imdrop))))]
                 ->
                 [(prod (val (prod ptr i32) excopy exdrop)
                    (ref (val ptr excopy exdrop) (base gc)
                      (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                        (ser (mem (rep ptr) exdrop)
                          (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                            (ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep i32) imdrop)
                                  (coderef (val i32 imcopy imdrop)
                                    ((ref (val ptr excopy exdrop) (base gc)
                                       (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                         (ser (mem (rep ptr) exdrop) (var 0))
                                         (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                    -> (i31 (val ptr imcopy imdrop)))))))))
                        (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                    (coderef (val i32 imcopy imdrop)
                      ((ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                           (ser (mem (rep ptr) exdrop)
                             (ref (val ptr excopy exdrop) (base gc)
                               (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                 (ser (mem (rep ptr) exdrop)
                                   (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                                     (ref (val ptr excopy exdrop) (base gc)
                                       (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                         (ser (mem (rep ptr) exdrop) (var 0))
                                         (ser (mem (rep i32) imdrop)
                                           (coderef (val i32 imcopy imdrop)
                                             ((ref (val ptr excopy exdrop)
                                                (base gc)
                                                (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                                  (ser (mem (rep ptr) exdrop) (var 0))
                                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                             -> (i31 (val ptr imcopy imdrop)))))))))
                                 (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                           (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                      -> (i31 (val ptr imcopy imdrop)))))]
        new ;; [(prod (val (prod ptr i32) excopy exdrop)
                  (ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                      (ser (mem (rep ptr) exdrop)
                        (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                          (ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop)))))))))
                      (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                  (coderef (val i32 imcopy imdrop)
                    ((ref (val ptr excopy exdrop) (base gc)
                       (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                         (ser (mem (rep ptr) exdrop)
                           (ref (val ptr excopy exdrop) (base gc)
                             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                               (ser (mem (rep ptr) exdrop)
                                 (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                                   (ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep i32) imdrop)
                                         (coderef (val i32 imcopy imdrop)
                                           ((ref (val ptr excopy exdrop)
                                              (base gc)
                                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                                (ser (mem (rep ptr) exdrop) (var 0))
                                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                           -> (i31 (val ptr imcopy imdrop)))))))))
                               (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                         (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                    -> (i31 (val ptr imcopy imdrop)))))]
               ->
               [(ref (val ptr excopy exdrop) (base gc)
                  (ser (mem (rep (prod ptr i32)) exdrop)
                    (prod (val (prod ptr i32) excopy exdrop)
                      (ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                          (ser (mem (rep ptr) exdrop)
                            (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                              (ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                  (ser (mem (rep ptr) exdrop) (var 0))
                                  (ser (mem (rep i32) imdrop)
                                    (coderef (val i32 imcopy imdrop)
                                      ((ref (val ptr excopy exdrop) (base gc)
                                         (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                           (ser (mem (rep ptr) exdrop) (var 0))
                                           (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                      -> (i31 (val ptr imcopy imdrop)))))))))
                          (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                      (coderef (val i32 imcopy imdrop)
                        ((ref (val ptr excopy exdrop) (base gc)
                           (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                             (ser (mem (rep ptr) exdrop)
                               (ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                   (ser (mem (rep ptr) exdrop)
                                     (exists.type (val ptr excopy exdrop)
                                       (val ptr excopy exdrop)
                                       (ref (val ptr excopy exdrop) (base gc)
                                         (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                           (ser (mem (rep ptr) exdrop) (var 0))
                                           (ser (mem (rep i32) imdrop)
                                             (coderef (val i32 imcopy imdrop)
                                               ((ref (val ptr excopy exdrop)
                                                  (base gc)
                                                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                                    (ser (mem (rep ptr) exdrop) (var 0))
                                                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                               -> (i31 (val ptr imcopy imdrop)))))))))
                                   (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                             (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                        -> (i31 (val ptr imcopy imdrop)))))))]
        cast ;; [(ref (val ptr excopy exdrop) (base gc)
                   (ser (mem (rep (prod ptr i32)) exdrop)
                     (prod (val (prod ptr i32) excopy exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                           (ser (mem (rep ptr) exdrop)
                             (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                               (ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                   (ser (mem (rep ptr) exdrop) (var 0))
                                   (ser (mem (rep i32) imdrop)
                                     (coderef (val i32 imcopy imdrop)
                                       ((ref (val ptr excopy exdrop) (base gc)
                                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                            (ser (mem (rep ptr) exdrop) (var 0))
                                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                       -> (i31 (val ptr imcopy imdrop)))))))))
                           (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                       (coderef (val i32 imcopy imdrop)
                         ((ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc)
                                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                    (ser (mem (rep ptr) exdrop)
                                      (exists.type (val ptr excopy exdrop)
                                        (val ptr excopy exdrop)
                                        (ref (val ptr excopy exdrop) (base gc)
                                          (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                            (ser (mem (rep ptr) exdrop) (var 0))
                                            (ser (mem (rep i32) imdrop)
                                              (coderef (val i32 imcopy imdrop)
                                                ((ref (val ptr excopy exdrop)
                                                   (base gc)
                                                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                                     (ser (mem (rep ptr) exdrop) (var 0))
                                                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                                -> (i31 (val ptr imcopy imdrop)))))))))
                                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                              (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                         -> (i31 (val ptr imcopy imdrop)))))))]
                ->
                [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                           (ser (mem (rep ptr) exdrop)
                             (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                               (ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                   (ser (mem (rep ptr) exdrop) (var 0))
                                   (ser (mem (rep i32) imdrop)
                                     (coderef (val i32 imcopy imdrop)
                                       ((ref (val ptr excopy exdrop) (base gc)
                                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                            (ser (mem (rep ptr) exdrop) (var 0))
                                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                       -> (i31 (val ptr imcopy imdrop)))))))))
                           (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep i32) imdrop)
                       (coderef (val i32 imcopy imdrop)
                         ((ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc)
                                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                    (ser (mem (rep ptr) exdrop)
                                      (exists.type (val ptr excopy exdrop)
                                        (val ptr excopy exdrop)
                                        (ref (val ptr excopy exdrop) (base gc)
                                          (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                            (ser (mem (rep ptr) exdrop) (var 0))
                                            (ser (mem (rep i32) imdrop)
                                              (coderef (val i32 imcopy imdrop)
                                                ((ref (val ptr excopy exdrop)
                                                   (base gc)
                                                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                                     (ser (mem (rep ptr) exdrop) (var 0))
                                                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                                -> (i31 (val ptr imcopy imdrop)))))))))
                                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                              (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                         -> (i31 (val ptr imcopy imdrop)))))))]
        pack ;; [(ref (val ptr excopy exdrop) (base gc)
                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                     (ser (mem (rep ptr) exdrop)
                       (ref (val ptr excopy exdrop) (base gc)
                         (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                           (ser (mem (rep ptr) exdrop)
                             (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                               (ref (val ptr excopy exdrop) (base gc)
                                 (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                   (ser (mem (rep ptr) exdrop) (var 0))
                                   (ser (mem (rep i32) imdrop)
                                     (coderef (val i32 imcopy imdrop)
                                       ((ref (val ptr excopy exdrop) (base gc)
                                          (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                            (ser (mem (rep ptr) exdrop) (var 0))
                                            (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                       -> (i31 (val ptr imcopy imdrop)))))))))
                           (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                     (ser (mem (rep i32) imdrop)
                       (coderef (val i32 imcopy imdrop)
                         ((ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                              (ser (mem (rep ptr) exdrop)
                                (ref (val ptr excopy exdrop) (base gc)
                                  (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                    (ser (mem (rep ptr) exdrop)
                                      (exists.type (val ptr excopy exdrop)
                                        (val ptr excopy exdrop)
                                        (ref (val ptr excopy exdrop) (base gc)
                                          (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                            (ser (mem (rep ptr) exdrop) (var 0))
                                            (ser (mem (rep i32) imdrop)
                                              (coderef (val i32 imcopy imdrop)
                                                ((ref (val ptr excopy exdrop)
                                                   (base gc)
                                                   (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                                     (ser (mem (rep ptr) exdrop) (var 0))
                                                     (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                                -> (i31 (val ptr imcopy imdrop)))))))))
                                    (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop))))))
                              (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                         -> (i31 (val ptr imcopy imdrop)))))))]
                ->
                [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                   (ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop))))))))]
        local.set 3 ;; [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                          (ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop))))))))]
                       -> []
        local.get 3 ;; [] ->
                       [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                          (ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop))))))))]
        copy ;; [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                   (ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop))))))))]
                ->
                [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                   (ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop))))))))
                (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                  (ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                      (ser (mem (rep i32) imdrop)
                        (coderef (val i32 imcopy imdrop)
                          ((ref (val ptr excopy exdrop) (base gc)
                             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                               (ser (mem (rep ptr) exdrop) (var 0))
                               (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                          -> (i31 (val ptr imcopy imdrop))))))))]
        local.set 3 ;; [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                          (ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop))))))))]
                       -> []
        unpack (localfx [0 => (ref (val ptr excopy exdrop) (base gc) (struct (mem (prod) imdrop)))]
                 [1 => (i31 (val ptr imcopy imdrop))]
                 [2 =>
                 (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                   (ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop))))))))]
                 [3 =>
                 (exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                   (ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop))))))))]
                 [4 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [5 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [6 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [7 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [8 => (plug (val (prod i32) imcopy imdrop) (prod i32))]
                 [9 => (plug (val (prod i32) imcopy imdrop) (prod i32))])
          local.set 4 ;; [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
                         -> []
          local.get 4 ;; [] ->
                         [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
          copy ;; [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop)))))))]
                  ->
                  [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop)))))))
                  (ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                      (ser (mem (rep i32) imdrop)
                        (coderef (val i32 imcopy imdrop)
                          ((ref (val ptr excopy exdrop) (base gc)
                             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                               (ser (mem (rep ptr) exdrop) (var 0))
                               (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                          -> (i31 (val ptr imcopy imdrop)))))))]
          local.set 4 ;; [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
                         -> []
          load (path 0) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                     (ser (mem (rep ptr) exdrop) (var 0))
                                     (ser (mem (rep i32) imdrop)
                                       (coderef (val i32 imcopy imdrop)
                                         ((ref (val ptr excopy exdrop) (base gc)
                                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                              (ser (mem (rep ptr) exdrop) (var 0))
                                              (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                         -> (i31 (val ptr imcopy imdrop)))))))]
                                ->
                                [(ref (val ptr excopy exdrop) (base gc)
                                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                     (ser (mem (rep ptr) exdrop) (var 0))
                                     (ser (mem (rep i32) imdrop)
                                       (coderef (val i32 imcopy imdrop)
                                         ((ref (val ptr excopy exdrop) (base gc)
                                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                              (ser (mem (rep ptr) exdrop) (var 0))
                                              (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                         -> (i31 (val ptr imcopy imdrop)))))))
                                (var 0)]
          local.set 5 ;; [(var 0)] -> []
          drop ;; [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop)))))))]
                  -> []
          local.get 5 ;; [] -> [(var 0)]
          local.set 6 ;; [(var 0)] -> []
          local.get 4 ;; [] ->
                         [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
          copy ;; [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop)))))))]
                  ->
                  [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop)))))))
                  (ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                      (ser (mem (rep i32) imdrop)
                        (coderef (val i32 imcopy imdrop)
                          ((ref (val ptr excopy exdrop) (base gc)
                             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                               (ser (mem (rep ptr) exdrop) (var 0))
                               (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                          -> (i31 (val ptr imcopy imdrop)))))))]
          local.set 4 ;; [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
                         -> []
          load (path 1) copy ;; [(ref (val ptr excopy exdrop) (base gc)
                                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                     (ser (mem (rep ptr) exdrop) (var 0))
                                     (ser (mem (rep i32) imdrop)
                                       (coderef (val i32 imcopy imdrop)
                                         ((ref (val ptr excopy exdrop) (base gc)
                                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                              (ser (mem (rep ptr) exdrop) (var 0))
                                              (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                         -> (i31 (val ptr imcopy imdrop)))))))]
                                ->
                                [(ref (val ptr excopy exdrop) (base gc)
                                   (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                                     (ser (mem (rep ptr) exdrop) (var 0))
                                     (ser (mem (rep i32) imdrop)
                                       (coderef (val i32 imcopy imdrop)
                                         ((ref (val ptr excopy exdrop) (base gc)
                                            (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                              (ser (mem (rep ptr) exdrop) (var 0))
                                              (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                         -> (i31 (val ptr imcopy imdrop)))))))
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop))))]
          local.set 7 ;; [(coderef (val i32 imcopy imdrop)
                            ((ref (val ptr excopy exdrop) (base gc)
                               (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                 (ser (mem (rep ptr) exdrop) (var 0))
                                 (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                            -> (i31 (val ptr imcopy imdrop))))]
                         -> []
          drop ;; [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop)))))))]
                  -> []
          local.get 7 ;; [] ->
                         [(coderef (val i32 imcopy imdrop)
                            ((ref (val ptr excopy exdrop) (base gc)
                               (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                 (ser (mem (rep ptr) exdrop) (var 0))
                                 (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                            -> (i31 (val ptr imcopy imdrop))))]
          local.set 8 ;; [(coderef (val i32 imcopy imdrop)
                            ((ref (val ptr excopy exdrop) (base gc)
                               (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                 (ser (mem (rep ptr) exdrop) (var 0))
                                 (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                            -> (i31 (val ptr imcopy imdrop))))]
                         -> []
          num_const 3 ;; [] -> [(num (val i32 imcopy imdrop) i32)]
          tag ;; [(num (val i32 imcopy imdrop) i32)] -> [(i31 (val ptr imcopy imdrop))]
          local.get 8 ;; [] ->
                         [(coderef (val i32 imcopy imdrop)
                            ((ref (val ptr excopy exdrop) (base gc)
                               (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                 (ser (mem (rep ptr) exdrop) (var 0))
                                 (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                            -> (i31 (val ptr imcopy imdrop))))]
          copy ;; [(coderef (val i32 imcopy imdrop)
                     ((ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr) (rep ptr)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                          (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                     -> (i31 (val ptr imcopy imdrop))))]
                  ->
                  [(coderef (val i32 imcopy imdrop)
                     ((ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr) (rep ptr)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                          (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                     -> (i31 (val ptr imcopy imdrop))))
                  (coderef (val i32 imcopy imdrop)
                    ((ref (val ptr excopy exdrop) (base gc)
                       (struct (mem (prod (rep ptr) (rep ptr)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                         (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                    -> (i31 (val ptr imcopy imdrop))))]
          local.set 8 ;; [(coderef (val i32 imcopy imdrop)
                            ((ref (val ptr excopy exdrop) (base gc)
                               (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                 (ser (mem (rep ptr) exdrop) (var 0))
                                 (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                            -> (i31 (val ptr imcopy imdrop))))]
                         -> []
          call_indirect ;; [(ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           (coderef (val i32 imcopy imdrop)
                             ((ref (val ptr excopy exdrop) (base gc)
                                (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                  (ser (mem (rep ptr) exdrop) (var 0))
                                  (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                             -> (i31 (val ptr imcopy imdrop))))]
                           -> [(i31 (val ptr imcopy imdrop))]
          local.get 8 ;; [] ->
                         [(coderef (val i32 imcopy imdrop)
                            ((ref (val ptr excopy exdrop) (base gc)
                               (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                 (ser (mem (rep ptr) exdrop) (var 0))
                                 (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                            -> (i31 (val ptr imcopy imdrop))))]
          drop ;; [(coderef (val i32 imcopy imdrop)
                     ((ref (val ptr excopy exdrop) (base gc)
                        (struct (mem (prod (rep ptr) (rep ptr)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                          (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                     -> (i31 (val ptr imcopy imdrop))))]
                  -> []
          local.get 6 ;; [] -> [(var 0)]
          drop ;; [(var 0)] -> []
          local.get 4 ;; [] ->
                         [(ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop)))))))]
          drop ;; [(ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop)))))))]
                  -> []
        end ;; [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                  (ref (val ptr excopy exdrop) (base gc)
                    (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                      (ser (mem (rep i32) imdrop)
                        (coderef (val i32 imcopy imdrop)
                          ((ref (val ptr excopy exdrop) (base gc)
                             (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                               (ser (mem (rep ptr) exdrop) (var 0))
                               (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                          -> (i31 (val ptr imcopy imdrop))))))))]
               -> [(i31 (val ptr imcopy imdrop))]
        local.get 3 ;; [] ->
                       [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                          (ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop))))))))]
        drop ;; [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                   (ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop))))))))]
                -> []
        local.get 2 ;; [] ->
                       [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                          (ref (val ptr excopy exdrop) (base gc)
                            (struct (mem (prod (rep ptr) (rep i32)) exdrop)
                              (ser (mem (rep ptr) exdrop) (var 0))
                              (ser (mem (rep i32) imdrop)
                                (coderef (val i32 imcopy imdrop)
                                  ((ref (val ptr excopy exdrop) (base gc)
                                     (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                       (ser (mem (rep ptr) exdrop) (var 0))
                                       (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                                  -> (i31 (val ptr imcopy imdrop))))))))]
        drop ;; [(exists.type (val ptr excopy exdrop) (val ptr excopy exdrop)
                   (ref (val ptr excopy exdrop) (base gc)
                     (struct (mem (prod (rep ptr) (rep i32)) exdrop) (ser (mem (rep ptr) exdrop) (var 0))
                       (ser (mem (rep i32) imdrop)
                         (coderef (val i32 imcopy imdrop)
                           ((ref (val ptr excopy exdrop) (base gc)
                              (struct (mem (prod (rep ptr) (rep ptr)) exdrop)
                                (ser (mem (rep ptr) exdrop) (var 0))
                                (ser (mem (rep ptr) imdrop) (i31 (val ptr imcopy imdrop)))))
                           -> (i31 (val ptr imcopy imdrop))))))))]
                -> []
        local.get 1 ;; [] -> [(i31 (val ptr imcopy imdrop))]
        drop ;; [(i31 (val ptr imcopy imdrop))] -> [])
      (table 0 1 2)
      (export "_start" (func 2))) |xxx}]
