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
      (func ((ref (base gc) (struct)) -> i31) (local ptr)
        i32.const 1
        tag)
      (table 0)
      (export "_start" (func 0)))
    -----------tuple-----------
    (module
      (func
          ((ref (base gc) (struct)) ->
            (ref (base gc) (struct (ser i31) (ser i31) (ser i31) (ser i31))))
          (local ptr)
        i32.const 4
        tag
        i32.const 3
        tag
        i32.const 2
        tag
        i32.const 1
        tag
        group 4
        new gc
        cast (ref (base gc) (struct (ser i31) (ser i31) (ser i31) (ser i31))))
      (table 0)
      (export "_start" (func 0)))
    -----------tuple_nested-----------
    (module
      (func
          ((ref (base gc) (struct)) ->
            (ref (base gc)
              (struct (ser (ref (base gc) (struct (ser i31) (ser i31))))
                (ser (ref (base gc) (struct (ser i31) (ser i31)))))))
          (local ptr)
        i32.const 4
        tag
        i32.const 3
        tag
        group 2
        new gc
        cast (ref (base gc) (struct (ser i31) (ser i31)))
        i32.const 2
        tag
        i32.const 1
        tag
        group 2
        new gc
        cast (ref (base gc) (struct (ser i31) (ser i31)))
        group 2
        new gc
        cast
          (ref (base gc)
            (struct (ser (ref (base gc) (struct (ser i31) (ser i31))))
              (ser (ref (base gc) (struct (ser i31) (ser i31)))))))
      (table 0)
      (export "_start" (func 0)))
    -----------tuple_project-----------
    (module
      (func ((ref (base gc) (struct)) -> i31) (local ptr ptr)
        i32.const 7
        tag
        i32.const 42
        tag
        group 2
        new gc
        cast (ref (base gc) (struct (ser i31) (ser i31)))
        load (Path [1]) follow
        local.set 1
        drop
        local.get 1 move)
      (table 0)
      (export "_start" (func 0)))
    -----------sum_unit-----------
    (module
      (func
          ((ref (base gc) (struct)) ->
            (ref (base gc) (variant (ser (ref (base gc) (struct))))))
          (local ptr)
        group 0
        new gc
        cast (ref (base gc) (struct))
        inject_new gc 0 (ref (base gc) (struct)))
      (table 0)
      (export "_start" (func 0)))
    -----------sum_option-----------
    (module
      (func
          ((ref (base gc) (struct)) ->
            (ref (base gc) (variant (ser (ref (base gc) (struct))) (ser i31))))
          (local ptr)
        i32.const 15
        tag
        inject_new gc 1 (ref (base gc) (struct)) i31)
      (table 0)
      (export "_start" (func 0)))
    -----------basic_if-----------
    (module
      (func ((ref (base gc) (struct)) -> i31) (local ptr)
        i32.const 0
        tag
        untag
        i32.const 0
        i32.eq
        if (result i31) inferfx
          i32.const 1
          tag
        else
          i32.const 2
          tag
        end)
      (table 0)
      (export "_start" (func 0)))
    -----------add-----------
    (module
      (func ((ref (base gc) (struct)) -> i31) (local ptr)
        i32.const 1
        tag
        untag
        i32.const 2
        tag
        untag
        i32.add
        tag)
      (table 0)
      (export "_start" (func 0)))
    -----------sub-----------
    (module
      (func ((ref (base gc) (struct)) -> i31) (local ptr)
        i32.const 1
        tag
        untag
        i32.const 2
        tag
        untag
        i32.sub
        tag)
      (table 0)
      (export "_start" (func 0)))
    -----------mul-----------
    (module
      (func ((ref (base gc) (struct)) -> i31) (local ptr)
        i32.const 1
        tag
        untag
        i32.const 2
        tag
        untag
        i32.mul
        tag)
      (table 0)
      (export "_start" (func 0)))
    -----------div-----------
    (module
      (func ((ref (base gc) (struct)) -> i31) (local ptr)
        i32.const 1
        tag
        untag
        i32.const 2
        tag
        untag
        i32.div_s
        tag)
      (table 0)
      (export "_start" (func 0)))
    -----------math-----------
    (module
      (func ((ref (base gc) (struct)) -> i31) (local ptr)
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
      (table 0)
      (export "_start" (func 0)))
    -----------basic_let-----------
    (module
      (func ((ref (base gc) (struct)) -> i31) (local ptr ptr)
        i32.const 10
        tag
        local.set 1
        local.get 1 move
        copy
        local.set 1
        local.get 1 move
        drop)
      (table 0)
      (export "_start" (func 0)))
    -----------return_one-----------
    (module
      (func
          ((ref (base gc)
             (struct (ser (ref (base gc) (struct))) (ser (ref (base gc) (struct)))))
            -> i31)
          (local ptr ptr ptr ptr ptr)
        local.get 0 move
        copy
        local.set 0
        load (Path [0]) follow
        local.set 1
        drop
        local.get 1 move
        local.set 2
        local.get 0 move
        copy
        local.set 0
        load (Path [1]) follow
        local.set 3
        drop
        local.get 3 move
        local.set 4
        i32.const 1
        tag
        local.get 4 move
        drop
        local.get 2 move
        drop)
      (func
          ((ref (base gc) (struct)) ->
            (exists type (val ptr excopy exdrop)
              (ref (base gc)
                (struct (ser (var 0))
                  (ser
                    (coderef
                      ((ref (base gc)
                         (struct (ser (var 0)) (ser (ref (base gc) (struct)))))
                        -> i31)))))))
          (local ptr)
        group 0
        new gc
        cast (ref (base gc) (struct))
        coderef 0
        group 2
        new gc
        cast
          (ref (base gc)
            (struct (ser (ref (base gc) (struct)))
              (ser
                (coderef
                  ((ref (base gc)
                     (struct (ser (ref (base gc) (struct)))
                       (ser (ref (base gc) (struct)))))
                    -> i31)))))
        pack (type (ref (base gc) (struct)))
          (ref (base gc)
            (struct (ser (var 0))
              (ser
                (coderef
                  ((ref (base gc)
                     (struct (ser (var 0)) (ser (ref (base gc) (struct)))))
                    -> i31))))))
      (table 0 1)
      (export "_start" (func 1)))
    -----------iife-----------
    (module
      (func
          ((ref (base gc)
             (struct (ser (ref (base gc) (struct))) (ser (ref (base gc) (struct)))))
            -> i31)
          (local ptr ptr ptr ptr ptr)
        local.get 0 move
        copy
        local.set 0
        load (Path [0]) follow
        local.set 1
        drop
        local.get 1 move
        local.set 2
        local.get 0 move
        copy
        local.set 0
        load (Path [1]) follow
        local.set 3
        drop
        local.get 3 move
        local.set 4
        i32.const 1
        tag
        local.get 4 move
        drop
        local.get 2 move
        drop)
      (func ((ref (base gc) (struct)) -> i31) (local ptr ptr ptr ptr ptr ptr)
        group 0
        new gc
        cast (ref (base gc) (struct))
        coderef 0
        group 2
        new gc
        cast
          (ref (base gc)
            (struct (ser (ref (base gc) (struct)))
              (ser
                (coderef
                  ((ref (base gc)
                     (struct (ser (ref (base gc) (struct)))
                       (ser (ref (base gc) (struct)))))
                    -> i31)))))
        pack (type (ref (base gc) (struct)))
          (ref (base gc)
            (struct (ser (var 0))
              (ser
                (coderef
                  ((ref (base gc)
                     (struct (ser (var 0)) (ser (ref (base gc) (struct)))))
                    -> i31)))))
        unpack (result i31) inferfx
          local.set 1
          local.get 1 move
          copy
          local.set 1
          load (Path [0]) follow
          local.set 2
          drop
          local.get 2 move
          local.set 3
          local.get 1 move
          copy
          local.set 1
          load (Path [1]) follow
          local.set 4
          drop
          local.get 4 move
          local.set 5
          group 0
          new gc
          cast (ref (base gc) (struct))
          local.get 5 move
          copy
          local.set 5
          call_indirect
          local.get 5 move
          drop
          local.get 3 move
          drop
          local.get 1 move
          drop
        end)
      (table 0 1)
      (export "_start" (func 1)))
    -----------add_one-----------
    (module
      (func
          ((ref (base gc) (struct (ser (ref (base gc) (struct))) (ser i31))) ->
            i31)
          (local ptr ptr ptr)
        local.get 0 move
        copy
        local.set 0
        load (Path [1]) follow
        local.set 1
        drop
        local.get 1 move
        local.set 2
        local.get 2 move
        copy
        local.set 2
        untag
        i32.const 1
        tag
        untag
        i32.add
        tag
        local.get 2 move
        drop)
      (table 0)
      (export "add1" (func 0)))
    -----------id-----------
    (module
      (func
          (forall.type (val ptr excopy exdrop)
            (ref (base gc) (struct (ser (ref (base gc) (struct))) (ser (var 0))))
            -> (var 0))
          (local ptr ptr ptr)
        local.get 0 move
        copy
        local.set 0
        load (Path [1]) follow
        local.set 1
        drop
        local.get 1 move
        local.set 2
        local.get 2 move
        copy
        local.set 2
        local.get 2 move
        drop)
      (table 0)
      (export "id" (func 0)))
    -----------apply_id-----------
    (module
      (func
          (forall.type (val ptr excopy exdrop)
            (ref (base gc) (struct (ser (ref (base gc) (struct))) (ser (var 0))))
            -> (var 0))
          (local ptr ptr ptr)
        local.get 0 move
        copy
        local.set 0
        load (Path [1]) follow
        local.set 1
        drop
        local.get 1 move
        local.set 2
        local.get 2 move
        copy
        local.set 2
        local.get 2 move
        drop)
      (func ((ref (base gc) (struct)) -> i31) (local ptr ptr ptr ptr ptr ptr)
        group 0
        new gc
        cast (ref (base gc) (struct))
        coderef 0
        group 2
        new gc
        cast
          (ref (base gc)
            (struct (ser (ref (base gc) (struct)))
              (ser
                (coderef
                  (forall.type (val ptr excopy exdrop)
                    (ref (base gc)
                      (struct (ser (ref (base gc) (struct))) (ser (var 0))))
                    -> (var 0))))))
        pack (type (ref (base gc) (struct)))
          (ref (base gc)
            (struct (ser (var 0))
              (ser
                (coderef
                  (forall.type (val ptr excopy exdrop)
                    (ref (base gc) (struct (ser (var 1)) (ser (var 0)))) ->
                    (var 0))))))
        unpack (result i31) inferfx
          local.set 1
          local.get 1 move
          copy
          local.set 1
          load (Path [0]) follow
          local.set 2
          drop
          local.get 2 move
          local.set 3
          local.get 1 move
          copy
          local.set 1
          load (Path [1]) follow
          local.set 4
          drop
          local.get 4 move
          local.set 5
          i32.const 42
          tag
          local.get 5 move
          copy
          local.set 5
          inst (type i31)
          call_indirect
          local.get 5 move
          drop
          local.get 3 move
          drop
          local.get 1 move
          drop
        end)
      (table 0 1)
      (export "id" (func 0))
      (export "_start" (func 1)))
    -----------opt_case-----------
    (module
      (func ((ref (base gc) (struct)) -> i31) (local ptr ptr ptr ptr ptr)
        i32.const 42
        tag
        inject_new gc 1 (ref (base gc) (struct)) i31
        local.set 1
        local.get 1 move
        copy
        local.set 1
        case_load (result i31) copy inferfx
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
        local.set 4
        drop
        local.get 4 move
        local.get 1 move
        drop)
      (table 0)
      (export "_start" (func 0)))
    -----------poly_len-----------
    (module
      (func
          (forall.type (val ptr excopy exdrop)
            (ref (base gc)
              (struct (ser (ref (base gc) (struct)))
                (ser
                  (rec (val ptr excopy exdrop)
                    (ref (base gc)
                      (variant (ser (ref (base gc) (struct)))
                        (ser (ref (base gc) (variant (ser (var 1)) (ser (var 0)))))))))))
            -> i31)
          (local ptr ptr ptr ptr ptr ptr ptr ptr ptr ptr ptr)
        local.get 0 move
        copy
        local.set 0
        load (Path [1]) follow
        local.set 1
        drop
        local.get 1 move
        local.set 2
        local.get 2 move
        copy
        local.set 2
        unfold
        case_load (result i31) copy inferfx
          (0
            local.set 9
            i32.const 0
            tag
            local.get 9 move
            drop)
          (1
            local.set 3
            i32.const 1
            tag
            untag
            group 0
            new gc
            cast (ref (base gc) (struct))
            coderef 0
            group 2
            new gc
            cast
              (ref (base gc)
                (struct (ser (ref (base gc) (struct)))
                  (ser
                    (coderef
                      (forall.type (val ptr excopy exdrop)
                        (ref (base gc)
                          (struct (ser (ref (base gc) (struct)))
                            (ser
                              (rec (val ptr excopy exdrop)
                                (ref (base gc)
                                  (variant (ser (ref (base gc) (struct)))
                                    (ser
                                      (ref (base gc)
                                        (variant (ser (var 1)) (ser (var 0)))))))))))
                        -> i31)))))
            pack (type (ref (base gc) (struct)))
              (ref (base gc)
                (struct (ser (var 0))
                  (ser
                    (coderef
                      (forall.type (val ptr excopy exdrop)
                        (ref (base gc)
                          (struct (ser (var 1))
                            (ser
                              (rec (val ptr excopy exdrop)
                                (ref (base gc)
                                  (variant (ser (ref (base gc) (struct)))
                                    (ser
                                      (ref (base gc)
                                        (variant (ser (var 1)) (ser (var 0)))))))))))
                        -> i31)))))
            unpack (result i31) inferfx
              local.set 4
              local.get 4 move
              copy
              local.set 4
              load (Path [0]) follow
              local.set 5
              drop
              local.get 5 move
              local.set 6
              local.get 4 move
              copy
              local.set 4
              load (Path [1]) follow
              local.set 7
              drop
              local.get 7 move
              local.set 8
              local.get 3 move
              copy
              local.set 3
              fold
                (rec (val ptr excopy exdrop)
                  (ref (base gc)
                    (variant (ser (ref (base gc) (struct)))
                      (ser (ref (base gc) (variant (ser (var 2)) (ser (var 0))))))))
              local.get 8 move
              copy
              local.set 8
              inst (type (var 1))
              call_indirect
              local.get 8 move
              drop
              local.get 6 move
              drop
              local.get 4 move
              drop
            end
            untag
            i32.add
            tag
            local.get 3 move
            drop)
        end
        local.set 10
        drop
        local.get 10 move
        local.get 2 move
        drop)
      (func ((ref (base gc) (struct)) -> i31) (local ptr ptr ptr ptr ptr ptr)
        group 0
        new gc
        cast (ref (base gc) (struct))
        coderef 0
        group 2
        new gc
        cast
          (ref (base gc)
            (struct (ser (ref (base gc) (struct)))
              (ser
                (coderef
                  (forall.type (val ptr excopy exdrop)
                    (ref (base gc)
                      (struct (ser (ref (base gc) (struct)))
                        (ser
                          (rec (val ptr excopy exdrop)
                            (ref (base gc)
                              (variant (ser (ref (base gc) (struct)))
                                (ser
                                  (ref (base gc)
                                    (variant (ser (var 1)) (ser (var 0)))))))))))
                    -> i31)))))
        pack (type (ref (base gc) (struct)))
          (ref (base gc)
            (struct (ser (var 0))
              (ser
                (coderef
                  (forall.type (val ptr excopy exdrop)
                    (ref (base gc)
                      (struct (ser (var 1))
                        (ser
                          (rec (val ptr excopy exdrop)
                            (ref (base gc)
                              (variant (ser (ref (base gc) (struct)))
                                (ser
                                  (ref (base gc)
                                    (variant (ser (var 1)) (ser (var 0)))))))))))
                    -> i31)))))
        unpack (result i31) inferfx
          local.set 1
          local.get 1 move
          copy
          local.set 1
          load (Path [0]) follow
          local.set 2
          drop
          local.get 2 move
          local.set 3
          local.get 1 move
          copy
          local.set 1
          load (Path [1]) follow
          local.set 4
          drop
          local.get 4 move
          local.set 5
          group 0
          new gc
          cast (ref (base gc) (struct))
          inject_new gc 0 (ref (base gc) (struct))
            (rec (val ptr excopy exdrop)
              (ref (base gc)
                (variant (ser (ref (base gc) (struct)))
                  (ser (ref (base gc) (variant (ser i31) (ser (var 0))))))))
          fold
            (rec (val ptr excopy exdrop)
              (ref (base gc)
                (variant (ser (ref (base gc) (struct)))
                  (ser (ref (base gc) (variant (ser i31) (ser (var 0))))))))
          i32.const 1
          tag
          group 2
          new gc
          cast
            (ref (base gc)
              (struct
                (ser
                  (rec (val ptr excopy exdrop)
                    (ref (base gc)
                      (variant (ser (ref (base gc) (struct)))
                        (ser (ref (base gc) (variant (ser i31) (ser (var 0)))))))))
                (ser i31)))
          inject_new gc 1 (ref (base gc) (struct))
            (ref (base gc)
              (variant (ser i31)
                (ser
                  (rec (val ptr excopy exdrop)
                    (ref (base gc)
                      (variant (ser (ref (base gc) (struct)))
                        (ser (ref (base gc) (variant (ser i31) (ser (var 0)))))))))))
          fold
            (rec (val ptr excopy exdrop)
              (ref (base gc)
                (variant (ser (ref (base gc) (struct)))
                  (ser (ref (base gc) (variant (ser i31) (ser (var 0))))))))
          local.get 5 move
          copy
          local.set 5
          inst (type i31)
          call_indirect
          local.get 5 move
          drop
          local.get 3 move
          drop
          local.get 1 move
          drop
        end)
      (table 0 1)
      (export "len" (func 0))
      (export "_start" (func 1)))
    -----------mini_zip-----------
    (module
      (func
          (forall.type (val ptr excopy exdrop)
            (forall.type (val ptr excopy exdrop)
              (ref (base gc)
                (struct (ser (ref (base gc) (struct)))
                  (ser
                    (ref (base gc)
                      (struct (ser (ref (base gc) (ser (var 0))))
                        (ser (ref (base gc) (ser (var 1)))))))))
              ->
              (ref (base gc)
                (ser (ref (base gc) (struct (ser (var 0)) (ser (var 1))))))))
          (local ptr ptr ptr ptr ptr ptr ptr)
        local.get 0 move
        copy
        local.set 0
        load (Path [1]) follow
        local.set 1
        drop
        local.get 1 move
        local.set 2
        local.get 2 move
        copy
        local.set 2
        load (Path [1]) follow
        local.set 3
        drop
        local.get 3 move
        load (Path []) follow
        local.set 4
        drop
        local.get 4 move
        local.get 2 move
        copy
        local.set 2
        load (Path [0]) follow
        local.set 5
        drop
        local.get 5 move
        load (Path []) follow
        local.set 6
        drop
        local.get 6 move
        group 2
        new gc
        cast (ref (base gc) (struct (ser (var 1)) (ser (var 0))))
        new gc
        local.get 2 move
        drop)
      (table 0)
      (export "mini_zip" (func 0)))
    -----------closure_simpl-----------
    (module
      (func
          ((ref (base gc)
             (struct (ser (ref (base gc) (struct (ser i31))))
               (ser (ref (base gc) (struct)))))
            -> i31)
          (local ptr ptr ptr ptr ptr ptr ptr)
        local.get 0 move
        copy
        local.set 0
        load (Path [0]) follow
        local.set 1
        drop
        local.get 1 move
        local.set 2
        local.get 0 move
        copy
        local.set 0
        load (Path [1]) follow
        local.set 3
        drop
        local.get 3 move
        local.set 4
        local.get 2 move
        copy
        local.set 2
        load (Path [0]) follow
        local.set 5
        drop
        local.get 5 move
        local.set 6
        local.get 6 move
        copy
        local.set 6
        local.get 6 move
        drop
        local.get 4 move
        drop
        local.get 2 move
        drop)
      (func ((ref (base gc) (struct)) -> i31) (local ptr ptr ptr ptr ptr ptr ptr
          ptr)
        i32.const 1
        tag
        local.set 1
        local.get 1 move
        copy
        local.set 1
        group 1
        new gc
        cast (ref (base gc) (struct (ser i31)))
        coderef 0
        group 2
        new gc
        cast
          (ref (base gc)
            (struct (ser (ref (base gc) (struct (ser i31))))
              (ser
                (coderef
                  ((ref (base gc)
                     (struct (ser (ref (base gc) (struct (ser i31))))
                       (ser (ref (base gc) (struct)))))
                    -> i31)))))
        pack (type (ref (base gc) (struct (ser i31))))
          (ref (base gc)
            (struct (ser (var 0))
              (ser
                (coderef
                  ((ref (base gc)
                     (struct (ser (var 0)) (ser (ref (base gc) (struct)))))
                    -> i31)))))
        local.set 2
        local.get 2 move
        copy
        local.set 2
        unpack (result i31) inferfx
          local.set 3
          local.get 3 move
          copy
          local.set 3
          load (Path [0]) follow
          local.set 4
          drop
          local.get 4 move
          local.set 5
          local.get 3 move
          copy
          local.set 3
          load (Path [1]) follow
          local.set 6
          drop
          local.get 6 move
          local.set 7
          group 0
          new gc
          cast (ref (base gc) (struct))
          local.get 7 move
          copy
          local.set 7
          call_indirect
          local.get 7 move
          drop
          local.get 5 move
          drop
          local.get 3 move
          drop
        end
        local.get 2 move
        drop
        local.get 1 move
        drop)
      (table 0 1)
      (export "_start" (func 1)))
    -----------closure_complex-----------
    (module
      (func
          ((ref (base gc)
             (struct
               (ser
                 (ref (base gc)
                   (struct
                     (ser
                       (exists type (val ptr excopy exdrop)
                         (ref (base gc)
                           (struct (ser (var 0))
                             (ser
                               (coderef
                                 ((ref (base gc) (struct (ser (var 0)) (ser i31)))
                                   -> i31)))))))
                     (ser i31))))
               (ser i31)))
            -> i31)
          (local ptr ptr ptr ptr ptr ptr ptr ptr ptr ptr ptr ptr ptr ptr)
        local.get 0 move
        copy
        local.set 0
        load (Path [0]) follow
        local.set 1
        drop
        local.get 1 move
        local.set 2
        local.get 0 move
        copy
        local.set 0
        load (Path [1]) follow
        local.set 3
        drop
        local.get 3 move
        local.set 4
        local.get 2 move
        copy
        local.set 2
        load (Path [0]) follow
        local.set 5
        drop
        local.get 5 move
        local.set 6
        local.get 2 move
        copy
        local.set 2
        load (Path [1]) follow
        local.set 7
        drop
        local.get 7 move
        local.set 8
        local.get 6 move
        copy
        local.set 6
        unpack (result i31) inferfx
          local.set 9
          local.get 9 move
          copy
          local.set 9
          load (Path [0]) follow
          local.set 10
          drop
          local.get 10 move
          local.set 11
          local.get 9 move
          copy
          local.set 9
          load (Path [1]) follow
          local.set 12
          drop
          local.get 12 move
          local.set 13
          local.get 4 move
          copy
          local.set 4
          local.get 13 move
          copy
          local.set 13
          call_indirect
          local.get 13 move
          drop
          local.get 11 move
          drop
          local.get 9 move
          drop
        end
        untag
        local.get 8 move
        copy
        local.set 8
        untag
        i32.add
        tag
        local.get 8 move
        drop
        local.get 6 move
        drop
        local.get 4 move
        drop
        local.get 2 move
        drop)
      (func
          ((ref (base gc)
             (struct (ser (ref (base gc) (struct (ser i31)))) (ser i31)))
            -> i31)
          (local ptr ptr ptr ptr ptr ptr ptr)
        local.get 0 move
        copy
        local.set 0
        load (Path [0]) follow
        local.set 1
        drop
        local.get 1 move
        local.set 2
        local.get 0 move
        copy
        local.set 0
        load (Path [1]) follow
        local.set 3
        drop
        local.get 3 move
        local.set 4
        local.get 2 move
        copy
        local.set 2
        load (Path [0]) follow
        local.set 5
        drop
        local.get 5 move
        local.set 6
        local.get 6 move
        copy
        local.set 6
        untag
        local.get 4 move
        copy
        local.set 4
        untag
        i32.add
        tag
        local.get 6 move
        drop
        local.get 4 move
        drop
        local.get 2 move
        drop)
      (func ((ref (base gc) (struct)) -> i31) (local ptr ptr ptr ptr ptr ptr ptr
          ptr ptr)
        i32.const 1
        tag
        local.set 1
        local.get 1 move
        copy
        local.set 1
        group 1
        new gc
        cast (ref (base gc) (struct (ser i31)))
        coderef 1
        group 2
        new gc
        cast
          (ref (base gc)
            (struct (ser (ref (base gc) (struct (ser i31))))
              (ser
                (coderef
                  ((ref (base gc)
                     (struct (ser (ref (base gc) (struct (ser i31)))) (ser i31)))
                    -> i31)))))
        pack (type (ref (base gc) (struct (ser i31))))
          (ref (base gc)
            (struct (ser (var 0))
              (ser
                (coderef ((ref (base gc) (struct (ser (var 0)) (ser i31))) -> i31)))))
        local.set 2
        local.get 2 move
        copy
        local.set 2
        local.get 1 move
        copy
        local.set 1
        group 2
        new gc
        cast
          (ref (base gc)
            (struct
              (ser
                (exists type (val ptr excopy exdrop)
                  (ref (base gc)
                    (struct (ser (var 0))
                      (ser
                        (coderef
                          ((ref (base gc) (struct (ser (var 0)) (ser i31))) -> i31)))))))
              (ser i31)))
        coderef 0
        group 2
        new gc
        cast
          (ref (base gc)
            (struct
              (ser
                (ref (base gc)
                  (struct
                    (ser
                      (exists type (val ptr excopy exdrop)
                        (ref (base gc)
                          (struct (ser (var 0))
                            (ser
                              (coderef
                                ((ref (base gc) (struct (ser (var 0)) (ser i31)))
                                  -> i31)))))))
                    (ser i31))))
              (ser
                (coderef
                  ((ref (base gc)
                     (struct
                       (ser
                         (ref (base gc)
                           (struct
                             (ser
                               (exists type (val ptr excopy exdrop)
                                 (ref (base gc)
                                   (struct (ser (var 0))
                                     (ser
                                       (coderef
                                         ((ref (base gc)
                                            (struct (ser (var 0)) (ser i31)))
                                           -> i31)))))))
                             (ser i31))))
                       (ser i31)))
                    -> i31)))))
        pack
          (type
            (ref (base gc)
              (struct
                (ser
                  (exists type (val ptr excopy exdrop)
                    (ref (base gc)
                      (struct (ser (var 0))
                        (ser
                          (coderef
                            ((ref (base gc) (struct (ser (var 0)) (ser i31))) ->
                              i31)))))))
                (ser i31))))
          (ref (base gc)
            (struct (ser (var 0))
              (ser
                (coderef ((ref (base gc) (struct (ser (var 0)) (ser i31))) -> i31)))))
        local.set 3
        local.get 3 move
        copy
        local.set 3
        unpack (result i31) inferfx
          local.set 4
          local.get 4 move
          copy
          local.set 4
          load (Path [0]) follow
          local.set 5
          drop
          local.get 5 move
          local.set 6
          local.get 4 move
          copy
          local.set 4
          load (Path [1]) follow
          local.set 7
          drop
          local.get 7 move
          local.set 8
          i32.const 3
          tag
          local.get 8 move
          copy
          local.set 8
          call_indirect
          local.get 8 move
          drop
          local.get 6 move
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
      (table 0 1 2)
      (export "_start" (func 2))) |}]
