open! Base
open! Stdlib.Format
open! Test_support
open! Richwasm_mini_ml
module RichWasm = Richwasm_common.Syntax

include Test_runner.MultiOutputter.Make (struct
  include Test_runner.MultiOutputter.DefaultConfig

  type syntax = Syntax.Source.Module.t
  type text = string
  type res = RichWasm.Module.t

  let syntax_pipeline x = x |> Convert.cc_module |> Codegen.compile_module
  let string_pipeline s = s |> Parse.from_string_exn |> syntax_pipeline
  let examples = Test_examples.Mini_ml.all
  let pp = RichWasm.Module.pp
  let pp_raw = RichWasm.Module.pp_sexp
end)

let%expect_test "examples" =
  output_examples ();
  [%expect
    {|
    -----------one-----------
    (module
      (func ((ref (base gc) (ser (prod))) -> (ref (base gc) (ser (prod)))) (local
          ptr)
        i32.const 1
        tag)
      (table)
      (export "_start" (func 0)))
    -----------tuple-----------
    (module
      (func ((ref (base gc) (ser (prod))) -> (ref (base gc) (ser (prod)))) (local
          ptr)
        i32.const 4
        tag
        i32.const 3
        tag
        i32.const 2
        tag
        i32.const 1
        tag
        group 4
        new gc)
      (table)
      (export "_start" (func 0)))
    -----------tuple_nested-----------
    (module
      (func ((ref (base gc) (ser (prod))) -> (ref (base gc) (ser (prod)))) (local
          ptr)
        i32.const 4
        tag
        i32.const 3
        tag
        group 2
        new gc
        i32.const 2
        tag
        i32.const 1
        tag
        group 2
        new gc
        group 2
        new gc)
      (table)
      (export "_start" (func 0)))
    -----------tuple_project-----------
    (module
      (func ((ref (base gc) (ser (prod))) -> (ref (base gc) (ser (prod)))) (local
          ptr)
        i32.const 7
        tag
        i32.const 42
        tag
        group 2
        new gc
        load (Path [1]) follow)
      (table)
      (export "_start" (func 0)))
    -----------sum_unit-----------
    (module
      (func ((ref (base gc) (ser (prod))) -> (ref (base gc) (ser (prod)))) (local
          ptr)
        group 0
        new gc
        inject gc 0 (ref (base gc) (ser (prod))))
      (table)
      (export "_start" (func 0)))
    -----------sum_option-----------
    (module
      (func ((ref (base gc) (ser (prod))) -> (ref (base gc) (ser (prod)))) (local
          ptr)
        i32.const 15
        tag
        inject gc 1 (ref (base gc) (ser (prod))) i31)
      (table)
      (export "_start" (func 0)))
    -----------add-----------
    (module
      (func ((ref (base gc) (ser (prod))) -> (ref (base gc) (ser (prod)))) (local
          ptr)
        i32.const 1
        tag
        untag
        i32.const 2
        tag
        untag
        i32.add
        tag)
      (table)
      (export "_start" (func 0)))
    -----------sub-----------
    (module
      (func ((ref (base gc) (ser (prod))) -> (ref (base gc) (ser (prod)))) (local
          ptr)
        i32.const 1
        tag
        untag
        i32.const 2
        tag
        untag
        i32.sub
        tag)
      (table)
      (export "_start" (func 0)))
    -----------mul-----------
    (module
      (func ((ref (base gc) (ser (prod))) -> (ref (base gc) (ser (prod)))) (local
          ptr)
        i32.const 1
        tag
        untag
        i32.const 2
        tag
        untag
        i32.mul
        tag)
      (table)
      (export "_start" (func 0)))
    -----------div-----------
    (module
      (func ((ref (base gc) (ser (prod))) -> (ref (base gc) (ser (prod)))) (local
          ptr)
        i32.const 1
        tag
        untag
        i32.const 2
        tag
        untag
        i32.div_s
        tag)
      (table)
      (export "_start" (func 0)))
    -----------math-----------
    (module
      (func ((ref (base gc) (ser (prod))) -> (ref (base gc) (ser (prod)))) (local
          ptr)
        i32.const 2
        tag
        untag
        i32.const 6
        tag
        untag
        i32.mul
        tag
        untag
        i32.const 3
        tag
        untag
        i32.div_s
        tag)
      (table)
      (export "_start" (func 0)))
    -----------basic_let-----------
    (module
      (func ((ref (base gc) (ser (prod))) -> (ref (base gc) (ser (prod)))) (local
          ptr ptr)
        i32.const 10
        tag
        local.set 1
        local.get 1 move
        copy
        local.set 1
        local.get 1 move
        drop)
      (table)
      (export "_start" (func 0)))
    -----------return_one-----------
    (module
      (func
          ((ref (base gc)
             (ser (prod (ref (base gc) (ser (prod))) (ref (base gc) (ser (prod))))))
          -> i31) (local ptr ptr ptr)
        local.get 0 move
        copy
        local.set 0
        load (Path [0]) follow
        local.set 1
        local.get 0 move
        copy
        local.set 0
        load (Path [1]) follow
        local.set 2
        i32.const 1
        tag
        local.get 2 move
        drop
        local.get 1 move
        drop)
      (func ((ref (base gc) (ser (prod))) -> (ref (base gc) (ser (prod)))) (local
          ptr)
        group 0
        new gc
        coderef 0
        group 2
        new gc
        pack (Type (ref (base gc) (ser (prod))))
          (ref (base gc)
            (ser
              (exists type (VALTYPE (ptr, excopy, exdrop))
                (coderef
                  ((ref (base gc)
                     (ser (prod (var 0) (ref (base gc) (ser (prod))))))
                  -> i31)))))
        new gc)
      (table)
      (export "_start" (func 1)))
    -----------add_one-----------
    (module
      (func ((ref (base gc) (ser (prod (ref (base gc) (ser (prod))) i31))) -> i31)
          (local ptr ptr)
        local.get 0 move
        copy
        local.set 0
        load (Path [1]) follow
        local.set 1
        local.get 1 move
        copy
        local.set 1
        untag
        i32.const 1
        tag
        untag
        i32.add
        tag
        local.get 1 move
        drop)
      (table)
      (export "add1" (func 0)))
    -----------id-----------
    (module
      (func
          (forall.type (VALTYPE (ptr, excopy, exdrop))(ref (base gc)
                                                        (ser
                                                          (prod
                                                            (ref (base gc)
                                                              (ser (prod)))
                                                            (var 0))))
          -> (var 0)) (local ptr ptr)
        local.get 0 move
        copy
        local.set 0
        load (Path [1]) follow
        local.set 1
        local.get 1 move
        copy
        local.set 1
        local.get 1 move
        drop)
      (table)
      (export "id" (func 0)))
    -----------apply_id-----------
    (module
      (func
          (forall.type (VALTYPE (ptr, excopy, exdrop))(ref (base gc)
                                                        (ser
                                                          (prod
                                                            (ref (base gc)
                                                              (ser (prod)))
                                                            (var 0))))
          -> (var 0)) (local ptr ptr)
        local.get 0 move
        copy
        local.set 0
        load (Path [1]) follow
        local.set 1
        local.get 1 move
        copy
        local.set 1
        local.get 1 move
        drop)
      (func ((ref (base gc) (ser (prod))) -> (ref (base gc) (ser (prod)))) (local
          ptr ptr ptr ptr)
        group 0
        new gc
        coderef 0
        group 2
        new gc
        pack (Type (ref (base gc) (ser (prod))))
          (ref (base gc)
            (ser
              (exists type (VALTYPE (ptr, excopy, exdrop))
                (ref (base gc)
                  (ser
                    (prod (var 0)
                      (coderef
                        (forall.type (VALTYPE (ptr, excopy, exdrop))(ref
                                                                      (base gc)
                                                                      (ser
                                                                        (prod
                                                                        (var 1)
                                                                        (var 0))))
                        -> (var 0)))))))))
        new gc
        load (Path []) follow
        unpack (<1> -> i31) (LocalFx [(1, (prod))])
          local.set 1
          local.get 1 move
          copy
          local.set 1
          load (Path [0]) follow
          local.set 2
          local.get 1 move
          copy
          local.set 1
          load (Path [1]) follow
          local.set 3
          i32.const 42
          tag
          local.get 3 move
          copy
          local.set 3
          call_indirect
          local.get 3 move
          drop
          local.get 2 move
          drop
          local.get 1 move
          drop
        end)
      (table)
      (export "id" (func 0))
      (export "_start" (func 1)))
    -----------opt_case-----------
    (module
      (func ((ref (base gc) (ser (prod))) -> (ref (base gc) (ser (prod)))) (local
          ptr ptr ptr ptr)
        i32.const 42
        tag
        inject gc 1 (ref (base gc) (ser (prod))) i31
        local.set 1
        local.get 1 move
        copy
        local.set 1
        case (<1> -> i31) (LocalFx [])
          (0
            local.set 3
            i32.const 0
            tag
            local.get 3 move
            drop)
          (1
            local.set 2
            local.get 2 move
            copy
            local.set 2
            local.get 2 move
            drop)
        end
        local.get 1 move
        drop)
      (table)
      (export "_start" (func 0)))
    -----------poly_len-----------
    (module
      (func
          (forall.type (VALTYPE (ptr, excopy, exdrop))(ref (base gc)
                                                        (ser
                                                          (prod
                                                            (ref (base gc)
                                                              (ser (prod)))
                                                            (rec
                                                              (VALTYPE (ptr,
                                                                 excopy, exdrop))
                                                              (ref (base gc)
                                                                (ser
                                                                  (sum
                                                                    (ref
                                                                      (base gc)
                                                                      (ser (prod)))
                                                                    (ref
                                                                      (base gc)
                                                                      (ser
                                                                        (sum
                                                                        (var 1)
                                                                        (var 0)))))))))))
          -> i31) (local ptr ptr ptr ptr ptr ptr ptr)
        local.get 0 move
        copy
        local.set 0
        load (Path [1]) follow
        local.set 1
        local.get 1 move
        copy
        local.set 1
        unfold
        case (<1> -> i31) (LocalFx [(3, (prod))])
          (0
            local.set 6
            i32.const 0
            tag
            local.get 6 move
            drop)
          (1
            local.set 2
            i32.const 1
            tag
            untag
            group 0
            new gc
            coderef 0
            group 2
            new gc
            pack (Type (ref (base gc) (ser (prod))))
              (ref (base gc)
                (ser
                  (exists type (VALTYPE (ptr, excopy, exdrop))
                    (ref (base gc)
                      (ser
                        (prod (var 0)
                          (coderef
                            (forall.type (VALTYPE (ptr, excopy, exdrop))(ref
                                                                        (base gc)
                                                                        (ser
                                                                        (prod
                                                                        (var 1)
                                                                        (rec
                                                                        (VALTYPE (
                                                                        ptr,
                                                                        excopy,
                                                                        exdrop))
                                                                        (ref
                                                                        (base gc)
                                                                        (ser
                                                                        (sum
                                                                        (ref
                                                                        (base gc)
                                                                        (ser
                                                                        (prod)))
                                                                        (ref
                                                                        (base gc)
                                                                        (ser
                                                                        (sum
                                                                        (var 1)
                                                                        (var 0)))))))))))
                            -> i31))))))))
            new gc
            load (Path []) follow
            unpack (<1> -> i31) (LocalFx [(3, (prod))])
              local.set 3
              local.get 3 move
              copy
              local.set 3
              load (Path [0]) follow
              local.set 4
              local.get 3 move
              copy
              local.set 3
              load (Path [1]) follow
              local.set 5
              local.get 2 move
              copy
              local.set 2
              fold
                (rec (VALTYPE (ptr, excopy, exdrop))
                  (ref (base gc)
                    (ser
                      (sum (ref (base gc) (ser (prod)))
                        (ref (base gc) (ser (sum (var 2) (var 0))))))))
              local.get 5 move
              copy
              local.set 5
              call_indirect
              local.get 5 move
              drop
              local.get 4 move
              drop
              local.get 3 move
              drop
            end
            untag
            i32.add
            tag
            local.get 2 move
            drop)
        end
        local.get 1 move
        drop)
      (func ((ref (base gc) (ser (prod))) -> (ref (base gc) (ser (prod)))) (local
          ptr ptr ptr ptr)
        group 0
        new gc
        coderef 0
        group 2
        new gc
        pack (Type (ref (base gc) (ser (prod))))
          (ref (base gc)
            (ser
              (exists type (VALTYPE (ptr, excopy, exdrop))
                (ref (base gc)
                  (ser
                    (prod (var 0)
                      (coderef
                        (forall.type (VALTYPE (ptr, excopy, exdrop))(ref
                                                                      (base gc)
                                                                      (ser
                                                                        (prod
                                                                        (var 1)
                                                                        (rec
                                                                        (VALTYPE (
                                                                        ptr,
                                                                        excopy,
                                                                        exdrop))
                                                                        (ref
                                                                        (base gc)
                                                                        (ser
                                                                        (sum
                                                                        (ref
                                                                        (base gc)
                                                                        (ser
                                                                        (prod)))
                                                                        (ref
                                                                        (base gc)
                                                                        (ser
                                                                        (sum
                                                                        (var 1)
                                                                        (var 0)))))))))))
                        -> i31))))))))
        new gc
        load (Path []) follow
        unpack (<1> -> i31) (LocalFx [(1, (prod))])
          local.set 1
          local.get 1 move
          copy
          local.set 1
          load (Path [0]) follow
          local.set 2
          local.get 1 move
          copy
          local.set 1
          load (Path [1]) follow
          local.set 3
          group 0
          new gc
          inject gc
            0 (ref (base gc) (ser (prod))) (rec (VALTYPE (ptr, excopy, exdrop))
                                             (ref (base gc)
                                               (ser
                                                 (sum (ref (base gc) (ser (prod)))
                                                   (ref (base gc)
                                                     (ser (sum i31 (var 0))))))))
          fold
            (rec (VALTYPE (ptr, excopy, exdrop))
              (ref (base gc)
                (ser
                  (sum (ref (base gc) (ser (prod)))
                    (ref (base gc) (ser (sum i31 (var 0))))))))
          i32.const 1
          tag
          group 2
          new gc
          inject gc
            1 (ref (base gc) (ser (prod))) (ref (base gc)
                                             (ser
                                               (sum i31
                                                 (rec
                                                   (VALTYPE (ptr, excopy, exdrop))
                                                   (ref (base gc)
                                                     (ser
                                                       (sum
                                                         (ref (base gc)
                                                           (ser (prod)))
                                                         (ref (base gc)
                                                           (ser (sum i31 (var 0)))))))))))
          fold
            (rec (VALTYPE (ptr, excopy, exdrop))
              (ref (base gc)
                (ser
                  (sum (ref (base gc) (ser (prod)))
                    (ref (base gc) (ser (sum i31 (var 0))))))))
          local.get 3 move
          copy
          local.set 3
          call_indirect
          local.get 3 move
          drop
          local.get 2 move
          drop
          local.get 1 move
          drop
        end)
      (table)
      (export "len" (func 0))
      (export "_start" (func 1)))
    -----------mini_zip-----------
    (module
      (func
          (forall.type (VALTYPE (ptr, excopy, exdrop))(forall.type (VALTYPE (ptr,
                                                                      excopy,
                                                                      exdrop))
                                                      (ref (base gc)
                                                        (ser
                                                          (prod
                                                            (ref (base gc)
                                                              (ser (prod)))
                                                            (ref (base gc)
                                                              (ser
                                                                (prod
                                                                  (ref (base gc)
                                                                    (ser (var 0)))
                                                                  (ref (base gc)
                                                                    (ser (var 1)))))))))
                                                      ->
                                                      (ref (base gc)
                                                        (ser
                                                          (ref (base gc)
                                                            (ser
                                                              (prod (var 0)
                                                                (var 1))))))))
          (local ptr ptr)
        local.get 0 move
        copy
        local.set 0
        load (Path [1]) follow
        local.set 1
        local.get 1 move
        copy
        local.set 1
        load (Path [1]) follow
        load (Path []) follow
        local.get 1 move
        copy
        local.set 1
        load (Path [0]) follow
        load (Path []) follow
        group 2
        new gc
        new gc
        local.get 1 move
        drop)
      (table)
      (export "mini_zip" (func 0)))
    -----------closure_simpl-----------
    (module
      (func
          ((ref (base gc)
             (ser
               (prod (ref (base gc) (ser (prod i31))) (ref (base gc) (ser (prod))))))
          -> i31) (local ptr ptr ptr ptr)
        local.get 0 move
        copy
        local.set 0
        load (Path [0]) follow
        local.set 1
        local.get 0 move
        copy
        local.set 0
        load (Path [1]) follow
        local.set 2
        local.get 1 move
        copy
        local.set 1
        load (Path [0]) follow
        local.set 3
        local.get 3 move
        copy
        local.set 3
        local.get 3 move
        drop
        local.get 2 move
        drop
        local.get 1 move
        drop)
      (func ((ref (base gc) (ser (prod))) -> (ref (base gc) (ser (prod)))) (local
          ptr ptr ptr ptr ptr ptr)
        i32.const 1
        tag
        local.set 1
        local.get 1 move
        copy
        local.set 1
        group 1
        new gc
        coderef 0
        group 2
        new gc
        pack (Type (ref (base gc) (ser (prod i31))))
          (ref (base gc)
            (ser
              (exists type (VALTYPE (ptr, excopy, exdrop))
                (coderef
                  ((ref (base gc)
                     (ser (prod (var 0) (ref (base gc) (ser (prod))))))
                  -> i31)))))
        new gc
        local.set 2
        local.get 2 move
        copy
        local.set 2
        load (Path []) follow
        unpack (<1> -> i31) (LocalFx [(3, (prod))])
          local.set 3
          local.get 3 move
          copy
          local.set 3
          load (Path [0]) follow
          local.set 4
          local.get 3 move
          copy
          local.set 3
          load (Path [1]) follow
          local.set 5
          group 0
          new gc
          local.get 5 move
          copy
          local.set 5
          call_indirect
          local.get 5 move
          drop
          local.get 4 move
          drop
          local.get 3 move
          drop
        end
        local.get 2 move
        drop
        local.get 1 move
        drop)
      (table)
      (export "_start" (func 1)))
    -----------closure_complex-----------
    (module
      (func
          ((ref (base gc)
             (ser
               (prod
                 (ref (base gc)
                   (ser
                     (prod
                       (ref (base gc)
                         (ser
                           (exists type (VALTYPE (ptr, excopy, exdrop))
                             (ref (base gc)
                               (ser
                                 (prod (var 0)
                                   (coderef
                                     ((ref (base gc) (ser (prod (var 0) i31))) ->
                                     i31))))))))
                       i31)))
                 i31)))
          -> i31) (local ptr ptr ptr ptr ptr ptr ptr ptr)
        local.get 0 move
        copy
        local.set 0
        load (Path [0]) follow
        local.set 1
        local.get 0 move
        copy
        local.set 0
        load (Path [1]) follow
        local.set 2
        local.get 1 move
        copy
        local.set 1
        load (Path [0]) follow
        local.set 3
        local.get 1 move
        copy
        local.set 1
        load (Path [1]) follow
        local.set 4
        local.get 3 move
        copy
        local.set 3
        load (Path []) follow
        unpack (<1> -> i31) (LocalFx [(5, (prod))])
          local.set 5
          local.get 5 move
          copy
          local.set 5
          load (Path [0]) follow
          local.set 6
          local.get 5 move
          copy
          local.set 5
          load (Path [1]) follow
          local.set 7
          local.get 2 move
          copy
          local.set 2
          local.get 7 move
          copy
          local.set 7
          call_indirect
          local.get 7 move
          drop
          local.get 6 move
          drop
          local.get 5 move
          drop
        end
        untag
        local.get 4 move
        copy
        local.set 4
        untag
        i32.add
        tag
        local.get 4 move
        drop
        local.get 3 move
        drop
        local.get 2 move
        drop
        local.get 1 move
        drop)
      (func
          ((ref (base gc) (ser (prod (ref (base gc) (ser (prod i31))) i31))) ->
          i31) (local ptr ptr ptr ptr)
        local.get 0 move
        copy
        local.set 0
        load (Path [0]) follow
        local.set 1
        local.get 0 move
        copy
        local.set 0
        load (Path [1]) follow
        local.set 2
        local.get 1 move
        copy
        local.set 1
        load (Path [0]) follow
        local.set 3
        local.get 3 move
        copy
        local.set 3
        untag
        local.get 2 move
        copy
        local.set 2
        untag
        i32.add
        tag
        local.get 3 move
        drop
        local.get 2 move
        drop
        local.get 1 move
        drop)
      (func ((ref (base gc) (ser (prod))) -> (ref (base gc) (ser (prod)))) (local
          ptr ptr ptr ptr ptr ptr ptr)
        i32.const 1
        tag
        local.set 1
        local.get 1 move
        copy
        local.set 1
        group 1
        new gc
        coderef 1
        group 2
        new gc
        pack (Type (ref (base gc) (ser (prod i31))))
          (ref (base gc)
            (ser
              (exists type (VALTYPE (ptr, excopy, exdrop))
                (coderef ((ref (base gc) (ser (prod (var 0) i31))) -> i31)))))
        new gc
        local.set 2
        local.get 2 move
        copy
        local.set 2
        local.get 1 move
        copy
        local.set 1
        group 2
        new gc
        coderef 0
        group 2
        new gc
        pack
          (Type
             (ref (base gc)
               (ser
                 (prod
                   (ref (base gc)
                     (ser
                       (exists type (VALTYPE (ptr, excopy, exdrop))
                         (ref (base gc)
                           (ser
                             (prod (var 0)
                               (coderef
                                 ((ref (base gc) (ser (prod (var 0) i31))) -> i31))))))))
                   i31))))
          (ref (base gc)
            (ser
              (exists type (VALTYPE (ptr, excopy, exdrop))
                (coderef ((ref (base gc) (ser (prod (var 0) i31))) -> i31)))))
        new gc
        local.set 3
        local.get 3 move
        copy
        local.set 3
        load (Path []) follow
        unpack (<1> -> i31) (LocalFx [(4, (prod))])
          local.set 4
          local.get 4 move
          copy
          local.set 4
          load (Path [0]) follow
          local.set 5
          local.get 4 move
          copy
          local.set 4
          load (Path [1]) follow
          local.set 6
          i32.const 3
          tag
          local.get 6 move
          copy
          local.set 6
          call_indirect
          local.get 6 move
          drop
          local.get 5 move
          drop
          local.get 4 move
          drop
        end
        local.get 3 move
        drop
        local.get 2 move
        drop
        local.get 1 move
        drop)
      (table)
      (export "_start" (func 2))) |}]
