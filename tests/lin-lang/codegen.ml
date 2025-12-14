open! Base
open! Stdlib.Format
open! Test_support
open! Richwasm_lin_lang
module RichWasm = Richwasm_common.Syntax

include Test_runner.MultiOutputter.Make (struct
  include Test_runner.MultiOutputter.DefaultConfig
  open Test_utils

  type syntax = Syntax.Module.t
  type text = string
  type res = RichWasm.Module.t

  let syntax_pipeline x =
    x
    |> Index.Compile.compile_module
    |> or_fail_pp Index.Err.pp
    |> Typecheck.Compile.compile_module
    |> or_fail_pp Typecheck.Err.pp
    |> Cc.Compile.compile_module
    |> or_fail_pp Cc.Compile.Err.pp
    |> Codegen.Compile.compile_module
    |> or_fail_pp Codegen.Err.pp

  let string_pipeline s = s |> Parse.from_string_exn |> syntax_pipeline
  let examples = Test_examples.Lin_lang.all
  let pp = RichWasm.Module.pp
  let pp_raw = RichWasm.Module.pp_sexp
end)

let%expect_test "basic functionality" =
  run {| 1 |};
  [%expect
    {|
    (module
      (func (-> i32)
        i32.const 1)
      (table)
      (export "_start" (func 0))) |}];
  next ();
  [%expect
    {|
    ((imports ())
     (functions
      (((typ (FunctionType () () ((Num (Int I32))))) (locals ())
        (body ((NumConst (Int I32) 1))))))
     (table ()) (exports (((name _start) (desc (Func 0)))))) |}];

  run {| (1, 2, 3, 4) |};
  [%expect
    {|
    (module
      (func (-> (prod i32 i32 i32 i32))
        i32.const 1
        i32.const 2
        i32.const 3
        i32.const 4
        group 4)
      (table)
      (export "_start" (func 0))) |}];
  next ();
  [%expect
    {|
    ((imports ())
     (functions
      (((typ
         (FunctionType () ()
          ((Prod ((Num (Int I32)) (Num (Int I32)) (Num (Int I32)) (Num (Int I32)))))))
        (locals ())
        (body
         ((NumConst (Int I32) 1) (NumConst (Int I32) 2) (NumConst (Int I32) 3)
          (NumConst (Int I32) 4) (Group 4))))))
     (table ()) (exports (((name _start) (desc (Func 0)))))) |}];

  run {| (tup (tup 1 (tup 2 3) 4 5) (tup 6 7)) |};
  [%expect
    {|
    (module
      (func (-> (prod (prod i32 (prod i32 i32) i32 i32) (prod i32 i32)))
        i32.const 1
        i32.const 2
        i32.const 3
        group 2
        i32.const 4
        i32.const 5
        group 4
        i32.const 6
        i32.const 7
        group 2
        group 2)
      (table)
      (export "_start" (func 0))) |}];

  run {| (new 10) |};
  [%expect
    {|
    (module
      (func (-> (ref (base mm) (ser i32)))
        i32.const 10
        new mm)
      (table)
      (export "_start" (func 0))) |}];

  run {| (1 + 2) |};
  [%expect
    {|
    (module
      (func (-> i32)
        i32.const 1
        i32.const 2
        i32.add)
      (table)
      (export "_start" (func 0))) |}];
  next ();
  [%expect
    {|
    ((imports ())
     (functions
      (((typ (FunctionType () () ((Num (Int I32))))) (locals ())
        (body ((NumConst (Int I32) 1) (NumConst (Int I32) 2) (Num (Int2 I32 Add)))))))
     (table ()) (exports (((name _start) (desc (Func 0)))))) |}];

  run
    {|
      (cases (inj 0 -1 : (sum int int int int))
        (case (_ : int) 0)
        (case (_ : int) 1)
        (case (_ : int) 2)
        (case (_ : int) 3))
      |};
  [%expect
    {|
    (module
      (func (-> i32) (local i32 i32 i32 i32)
        i32.const -1
        inject 0 i32 i32 i32 i32
        case (result i32) inferfx
          (0
            local.set 0
            i32.const 0
            local.get 0 move
            drop)
          (1
            local.set 1
            i32.const 1
            local.get 1 move
            drop)
          (2
            local.set 2
            i32.const 2
            local.get 2 move
            drop)
          (3
            local.set 3
            i32.const 3
            local.get 3 move
            drop)
        end)
      (table)
      (export "_start" (func 0))) |}];

  next ();
  [%expect
    {|
    ((imports ())
     (functions
      (((typ (FunctionType () () ((Num (Int I32)))))
        (locals ((Atom I32) (Atom I32) (Atom I32) (Atom I32)))
        (body
         ((NumConst (Int I32) -1)
          (Inject 0
           ((Num (Int I32)) (Num (Int I32)) (Num (Int I32)) (Num (Int I32))))
          (Case (ValType ((Num (Int I32)))) InferFx
           (((LocalSet 0) (NumConst (Int I32) 0) (LocalGet 0 Move) Drop)
            ((LocalSet 1) (NumConst (Int I32) 1) (LocalGet 1 Move) Drop)
            ((LocalSet 2) (NumConst (Int I32) 2) (LocalGet 2 Move) Drop)
            ((LocalSet 3) (NumConst (Int I32) 3) (LocalGet 3 Move) Drop))))))))
     (table ()) (exports (((name _start) (desc (Func 0)))))) |}];

  ()

let%expect_test "examples" =
  output_examples ();
  [%expect
    {|
    -----------one-----------
    (module
      (func (-> i32)
        i32.const 1)
      (table)
      (export "_start" (func 0)))
    -----------flat_tuple-----------
    (module
      (func (-> (prod i32 i32 i32 i32))
        i32.const 1
        i32.const 2
        i32.const 3
        i32.const 4
        group 4)
      (table)
      (export "_start" (func 0)))
    -----------nested_tuple-----------
    (module
      (func (-> (prod (prod i32 i32) (prod i32 i32)))
        i32.const 1
        i32.const 2
        group 2
        i32.const 3
        i32.const 4
        group 2
        group 2)
      (table)
      (export "_start" (func 0)))
    -----------single_sum-----------
    (module
      (func (-> (sum (prod)))
        group 0
        inject 0 (prod))
      (table)
      (export "_start" (func 0)))
    -----------double_sum-----------
    (module
      (func (-> (sum (prod) i32))
        i32.const 15
        inject 1 (prod) i32)
      (table)
      (export "_start" (func 0)))
    -----------arith_add-----------
    (module
      (func (-> i32)
        i32.const 9
        i32.const 10
        i32.add)
      (table)
      (export "_start" (func 0)))
    -----------arith_sub-----------
    (module
      (func (-> i32)
        i32.const 67
        i32.const 41
        i32.sub)
      (table)
      (export "_start" (func 0)))
    -----------arith_mul-----------
    (module
      (func (-> i32)
        i32.const 42
        i32.const 10
        i32.mul)
      (table)
      (export "_start" (func 0)))
    -----------arith_div-----------
    (module
      (func (-> i32)
        i32.const -30
        i32.const 10
        i32.div_s)
      (table)
      (export "_start" (func 0)))
    -----------app_ident-----------
    (module
      (func ((prod (ref (base mm) (ser (prod))) i32) -> i32) (local ptr i32
          (prod) i32)
        local.get 0 follow
        ungroup
        local.set 2
        local.set 1
        local.get 1 follow
        load (Path []) move
        local.set 3
        drop
        local.get 3 move
        ungroup
        local.get 2 follow
        local.set 4
        local.get 4 follow
        local.get 4 move
        drop
        local.get 1 move
        drop
        local.get 2 move
        drop)
      (func (-> i32) (local (prod i32 ptr) i32 ptr)
        coderef 0
        group 0
        new mm
        group 2
        pack (type (prod))
          (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
            (ref (base mm) (ser (var 0))))
        unpack (result i32) inferfx
          local.set 0
          local.get 0 follow
          ungroup
          local.set 2
          local.set 1
          local.get 2 follow
          i32.const 10
          group 2
          local.get 1 follow
          call_indirect
          local.get 1 move
          drop
          local.get 2 move
          drop
          local.get 0 move
          drop
        end)
      (table 0)
      (export "_start" (func 1)))
    -----------nested_arith-----------
    (module
      (func (-> i32)
        i32.const 9
        i32.const 10
        i32.add
        i32.const 5
        i32.mul)
      (table)
      (export "_start" (func 0)))
    -----------let_bind-----------
    (module
      (func (-> i32) (local i32)
        i32.const 10
        local.set 0
        local.get 0 follow
        local.get 0 move
        drop)
      (table)
      (export "_start" (func 0)))
    -----------add_one_program-----------
    (module
      (func ((prod (ref (base mm) (ser (prod))) i32) -> i32) (local ptr i32)
        local.get 0 follow
        ungroup
        local.set 2
        local.set 1
        local.get 2 follow
        i32.const 1
        i32.add
        local.get 1 move
        drop
        local.get 2 move
        drop)
      (func (-> i32) (local (prod i32 ptr) i32 ptr)
        coderef 0
        group 0
        new mm
        group 2
        pack (type (prod))
          (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
            (ref (base mm) (ser (var 0))))
        unpack (result i32) inferfx
          local.set 0
          local.get 0 follow
          ungroup
          local.set 2
          local.set 1
          local.get 2 follow
          i32.const 42
          group 2
          local.get 1 follow
          call_indirect
          local.get 1 move
          drop
          local.get 2 move
          drop
          local.get 0 move
          drop
        end)
      (table 0)
      (export "add-one" (func 0))
      (export "_start" (func 1)))
    -----------add_tup_ref-----------
    (module
      (func (-> i32) (local ptr i32 ptr i32 i32)
        i32.const 2
        new mm
        local.set 0
        i32.const 1
        local.get 0 follow
        group 2
        ungroup
        local.set 2
        local.set 1
        local.get 2 follow
        load (Path []) move
        local.set 3
        drop
        local.get 3 move
        local.set 4
        local.get 1 follow
        local.get 4 follow
        i32.add
        local.get 4 move
        drop
        local.get 1 move
        drop
        local.get 2 move
        drop
        local.get 0 move
        drop)
      (table)
      (export "_start" (func 0)))
    -----------print_10-----------
    (module
      (import ((prod (ref (base mm) (ser (prod))) i32) -> (prod)))
      (func ((prod (ref (base mm) (ser (prod))) i32) -> (prod))
        local.get 0 move
        call 0 (inst))
      (func (-> (prod)) (local (prod i32 ptr) i32 ptr)
        coderef 0
        group 0
        new mm
        group 2
        pack (type (prod))
          (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> (prod)))
            (ref (base mm) (ser (var 0))))
        unpack (result (prod)) inferfx
          local.set 0
          local.get 0 follow
          ungroup
          local.set 2
          local.set 1
          local.get 2 follow
          i32.const 10
          group 2
          local.get 1 follow
          call_indirect
          local.get 1 move
          drop
          local.get 2 move
          drop
          local.get 0 move
          drop
        end)
      (table 0)
      (export "_start" (func 1)))
    -----------closure-----------
    (module
      (func ((prod (ref (base mm) (ser (prod i32))) (prod)) -> i32) (local ptr
          (prod) (prod i32) i32 (prod))
        local.get 0 follow
        ungroup
        local.set 2
        local.set 1
        local.get 1 follow
        load (Path []) move
        local.set 3
        drop
        local.get 3 move
        ungroup
        local.set 4
        local.get 2 follow
        local.set 5
        local.get 4 follow
        local.get 5 move
        drop
        local.get 4 move
        drop
        local.get 1 move
        drop
        local.get 2 move
        drop)
      (func (-> i32) (local i32 (prod i32 ptr) i32 ptr)
        i32.const 10
        local.set 0
        coderef 0
        local.get 0 follow
        group 1
        new mm
        group 2
        pack (type (prod i32))
          (prod (coderef ((prod (ref (base mm) (ser (var 0))) (prod)) -> i32))
            (ref (base mm) (ser (var 0))))
        unpack (result i32) inferfx
          local.set 1
          local.get 1 follow
          ungroup
          local.set 3
          local.set 2
          local.get 3 follow
          group 0
          group 2
          local.get 2 follow
          call_indirect
          local.get 2 move
          drop
          local.get 3 move
          drop
          local.get 1 move
          drop
        end
        local.get 0 move
        drop)
      (table 0)
      (export "_start" (func 1)))
    -----------closure_call_var-----------
    (module
      (func ((prod (ref (base mm) (ser (prod i32))) i32) -> i32) (local ptr i32
          (prod i32) i32 i32)
        local.get 0 follow
        ungroup
        local.set 2
        local.set 1
        local.get 1 follow
        load (Path []) move
        local.set 3
        drop
        local.get 3 move
        ungroup
        local.set 4
        local.get 2 follow
        local.set 5
        local.get 5 follow
        local.get 4 follow
        i32.add
        local.get 5 move
        drop
        local.get 4 move
        drop
        local.get 1 move
        drop
        local.get 2 move
        drop)
      (func (-> i32) (local i32 i32 (prod i32 ptr) i32 ptr)
        i32.const 21
        local.set 0
        i32.const 1
        local.set 1
        coderef 0
        local.get 1 follow
        group 1
        new mm
        group 2
        pack (type (prod i32))
          (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
            (ref (base mm) (ser (var 0))))
        unpack (result i32) inferfx
          local.set 2
          local.get 2 follow
          ungroup
          local.set 4
          local.set 3
          local.get 4 follow
          local.get 0 follow
          group 2
          local.get 3 follow
          call_indirect
          local.get 3 move
          drop
          local.get 4 move
          drop
          local.get 2 move
          drop
        end
        local.get 1 move
        drop
        local.get 0 move
        drop)
      (table 0)
      (export "_start" (func 1)))
    -----------triangle_tl-----------
    (module
      (func ((prod (ref (base mm) (ser (prod))) i32) -> i32) (local ptr i32
          (prod i32 ptr) i32 ptr)
        local.get 0 follow
        ungroup
        local.set 2
        local.set 1
        local.get 2 follow
        i32.eqz
        if (result i32) inferfx
          i32.const 0
        else
          local.get 2 follow
          coderef 0
          group 0
          new mm
          group 2
          pack (type (prod))
            (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
              (ref (base mm) (ser (var 0))))
          unpack (result i32) inferfx
            local.set 3
            local.get 3 follow
            ungroup
            local.set 5
            local.set 4
            local.get 5 follow
            local.get 2 follow
            i32.const 1
            i32.sub
            group 2
            local.get 4 follow
            call_indirect
            local.get 4 move
            drop
            local.get 5 move
            drop
            local.get 3 move
            drop
          end
          i32.add
        end
        local.get 1 move
        drop
        local.get 2 move
        drop)
      (func (-> i32) (local (prod i32 ptr) i32 ptr)
        coderef 0
        group 0
        new mm
        group 2
        pack (type (prod))
          (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
            (ref (base mm) (ser (var 0))))
        unpack (result i32) inferfx
          local.set 0
          local.get 0 follow
          ungroup
          local.set 2
          local.set 1
          local.get 2 follow
          i32.const 10
          group 2
          local.get 1 follow
          call_indirect
          local.get 1 move
          drop
          local.get 2 move
          drop
          local.get 0 move
          drop
        end)
      (table 0)
      (export "_start" (func 1)))
    -----------factorial_tl-----------
    (module
      (func ((prod (ref (base mm) (ser (prod))) i32) -> i32) (local ptr i32 i32
          (prod i32 ptr) i32 ptr i32)
        local.get 0 follow
        ungroup
        local.set 2
        local.set 1
        local.get 2 follow
        i32.eqz
        if (result i32) inferfx
          i32.const 1
        else
          local.get 2 follow
          i32.const 1
          i32.sub
          local.set 3
          coderef 0
          group 0
          new mm
          group 2
          pack (type (prod))
            (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
              (ref (base mm) (ser (var 0))))
          unpack (result i32) inferfx
            local.set 4
            local.get 4 follow
            ungroup
            local.set 6
            local.set 5
            local.get 6 follow
            local.get 3 follow
            group 2
            local.get 5 follow
            call_indirect
            local.get 5 move
            drop
            local.get 6 move
            drop
            local.get 4 move
            drop
          end
          local.set 7
          local.get 2 follow
          local.get 7 follow
          i32.mul
          local.get 7 move
          drop
          local.get 3 move
          drop
        end
        local.get 1 move
        drop
        local.get 2 move
        drop)
      (func (-> i32) (local (prod i32 ptr) i32 ptr)
        coderef 0
        group 0
        new mm
        group 2
        pack (type (prod))
          (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
            (ref (base mm) (ser (var 0))))
        unpack (result i32) inferfx
          local.set 0
          local.get 0 follow
          ungroup
          local.set 2
          local.set 1
          local.get 2 follow
          i32.const 5
          group 2
          local.get 1 follow
          call_indirect
          local.get 1 move
          drop
          local.get 2 move
          drop
          local.get 0 move
          drop
        end)
      (table 0)
      (export "factorial" (func 0))
      (export "_start" (func 1)))
    -----------safe_div-----------
    (module
      (func
          ((prod (ref (base mm) (ser (prod))) (prod i32 i32)) -> (sum i32 (prod)))
          (local ptr (prod i32 i32) i32 i32 i32)
        local.get 0 follow
        ungroup
        local.set 2
        local.set 1
        local.get 2 follow
        ungroup
        local.set 4
        local.set 3
        local.get 4 follow
        i32.eqz
        if (result (sum i32 (prod))) inferfx
          group 0
          inject 1 i32 (prod)
        else
          local.get 3 follow
          local.get 4 follow
          i32.div_s
          local.set 5
          local.get 5 follow
          inject 0 i32 (prod)
          local.get 5 move
          drop
        end
        local.get 3 move
        drop
        local.get 4 move
        drop
        local.get 1 move
        drop
        local.get 2 move
        drop)
      (func ((prod (ref (base mm) (ser (prod))) (sum i32 (prod))) -> i32) (local
          ptr (sum i32 (prod)) i32 (prod))
        local.get 0 follow
        ungroup
        local.set 2
        local.set 1
        local.get 2 follow
        case (result i32) inferfx
          (0
            local.set 3
            local.get 3 follow
            local.get 3 move
            drop)
          (1
            local.set 4
            i32.const 0
            local.get 4 move
            drop)
        end
        local.get 1 move
        drop
        local.get 2 move
        drop)
      (func (-> i32) (local (prod i32 ptr) i32 ptr (sum i32 (prod)) (prod i32 ptr)
          i32 ptr)
        coderef 0
        group 0
        new mm
        group 2
        pack (type (prod))
          (prod
            (coderef
              ((prod (ref (base mm) (ser (var 0))) (prod i32 i32)) ->
                (sum i32 (prod))))
            (ref (base mm) (ser (var 0))))
        unpack (result (sum i32 (prod))) inferfx
          local.set 0
          local.get 0 follow
          ungroup
          local.set 2
          local.set 1
          local.get 2 follow
          i32.const 10
          i32.const 0
          group 2
          group 2
          local.get 1 follow
          call_indirect
          local.get 1 move
          drop
          local.get 2 move
          drop
          local.get 0 move
          drop
        end
        local.set 3
        coderef 1
        group 0
        new mm
        group 2
        pack (type (prod))
          (prod
            (coderef
              ((prod (ref (base mm) (ser (var 0))) (sum i32 (prod))) -> i32))
            (ref (base mm) (ser (var 0))))
        unpack (result i32) inferfx
          local.set 4
          local.get 4 follow
          ungroup
          local.set 6
          local.set 5
          local.get 6 follow
          local.get 3 follow
          group 2
          local.get 5 follow
          call_indirect
          local.get 5 move
          drop
          local.get 6 move
          drop
          local.get 4 move
          drop
        end
        local.get 3 move
        drop)
      (table 0 1)
      (export "_start" (func 2)))
    -----------incr_n-----------
    (module
      (func
          ((prod (ref (base mm) (ser (prod))) (ref (base mm) (ser i32))) ->
            (ref (base mm) (ser i32)))
          (local ptr ptr ptr i32 ptr i32)
        local.get 0 follow
        ungroup
        local.set 2
        local.set 1
        local.get 2 follow
        i32.const 0
        swap (Path [])
        group 2
        ungroup
        local.set 4
        local.set 3
        local.get 3 follow
        local.get 4 follow
        i32.const 1
        i32.add
        swap (Path [])
        group 2
        ungroup
        local.set 6
        local.set 5
        local.get 5 follow
        local.get 5 move
        drop
        local.get 6 move
        drop
        local.get 3 move
        drop
        local.get 4 move
        drop
        local.get 1 move
        drop
        local.get 2 move
        drop)
      (func
          ((prod (ref (base mm) (ser (prod))) (prod (ref (base mm) (ser i32)) i32))
            -> i32)
          (local ptr (prod ptr i32) ptr i32 i32 (prod i32 ptr) i32 ptr
          (prod i32 ptr) i32 ptr)
        local.get 0 follow
        ungroup
        local.set 2
        local.set 1
        local.get 2 follow
        ungroup
        local.set 4
        local.set 3
        local.get 4 follow
        i32.eqz
        if (result i32) inferfx
          local.get 3 follow
          load (Path []) move
          local.set 5
          drop
          local.get 5 move
        else
          coderef 1
          group 0
          new mm
          group 2
          pack (type (prod))
            (prod
              (coderef
                ((prod (ref (base mm) (ser (var 0)))
                   (prod (ref (base mm) (ser i32)) i32))
                  -> i32))
              (ref (base mm) (ser (var 0))))
          unpack (result i32) inferfx
            local.set 6
            local.get 6 follow
            ungroup
            local.set 8
            local.set 7
            local.get 8 follow
            coderef 0
            group 0
            new mm
            group 2
            pack (type (prod))
              (prod
                (coderef
                  ((prod (ref (base mm) (ser (var 0))) (ref (base mm) (ser i32)))
                    -> (ref (base mm) (ser i32))))
                (ref (base mm) (ser (var 0))))
            unpack (result (ref (base mm) (ser i32))) inferfx
              local.set 9
              local.get 9 follow
              ungroup
              local.set 11
              local.set 10
              local.get 11 follow
              local.get 3 follow
              group 2
              local.get 10 follow
              call_indirect
              local.get 10 move
              drop
              local.get 11 move
              drop
              local.get 9 move
              drop
            end
            local.get 4 follow
            i32.const 1
            i32.sub
            group 2
            group 2
            local.get 7 follow
            call_indirect
            local.get 7 move
            drop
            local.get 8 move
            drop
            local.get 6 move
            drop
          end
        end
        local.get 3 move
        drop
        local.get 4 move
        drop
        local.get 1 move
        drop
        local.get 2 move
        drop)
      (func (-> i32) (local ptr (prod i32 ptr) i32 ptr)
        i32.const 10
        new mm
        local.set 0
        coderef 1
        group 0
        new mm
        group 2
        pack (type (prod))
          (prod
            (coderef
              ((prod (ref (base mm) (ser (var 0)))
                 (prod (ref (base mm) (ser i32)) i32))
                -> i32))
            (ref (base mm) (ser (var 0))))
        unpack (result i32) inferfx
          local.set 1
          local.get 1 follow
          ungroup
          local.set 3
          local.set 2
          local.get 3 follow
          local.get 0 follow
          i32.const 3
          group 2
          group 2
          local.get 2 follow
          call_indirect
          local.get 2 move
          drop
          local.get 3 move
          drop
          local.get 1 move
          drop
        end
        local.get 0 move
        drop)
      (table 0 1)
      (export "incr_n" (func 1))
      (export "_start" (func 2)))
    -----------fix_factorial[invalid]-----------
    (module
      (func
          ((prod
             (ref (base mm)
               (ser
                 (prod
                   (exists type (val ptr nocopy exdrop)
                     (prod
                       (coderef
                         ((prod (ref (base mm) (ser (var 0)))
                            (exists type (val ptr nocopy exdrop)
                              (prod
                                (coderef
                                  ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                                (ref (base mm) (ser (var 0))))))
                           ->
                           (exists type (val ptr nocopy exdrop)
                             (prod
                               (coderef
                                 ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                               (ref (base mm) (ser (var 0)))))))
                       (ref (base mm) (ser (var 0))))))))
             (rec (val (prod i32 ptr) nocopy exdrop)
               (exists type (val ptr nocopy exdrop)
                 (prod
                   (coderef
                     ((prod (ref (base mm) (ser (var 0))) (var 1)) ->
                       (exists type (val ptr nocopy exdrop)
                         (prod
                           (coderef
                             ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                           (ref (base mm) (ser (var 0)))))))
                   (ref (base mm) (ser (var 0)))))))
            ->
            (exists type (val ptr nocopy exdrop)
              (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                (ref (base mm) (ser (var 0))))))
          (local ptr (prod i32 ptr) (prod (prod i32 ptr)) (prod i32 ptr)
          (prod i32 ptr) (prod i32 ptr) (prod i32 ptr) i32 ptr (prod i32 ptr)
          (prod i32 ptr) i32 ptr)
        local.get 0 follow
        ungroup
        local.set 2
        local.set 1
        local.get 1 follow
        load (Path []) move
        local.set 3
        drop
        local.get 3 move
        ungroup
        local.set 4
        local.get 2 follow
        local.set 5
        local.get 5 follow
        unfold
        local.set 6
        local.get 6 follow
        unpack
          (result
          (exists type (val ptr nocopy exdrop)
            (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
              (ref (base mm) (ser (var 0))))))
          inferfx
          local.set 7
          local.get 7 follow
          ungroup
          local.set 9
          local.set 8
          local.get 9 follow
          local.get 5 follow
          group 2
          local.get 8 follow
          call_indirect
          local.get 8 move
          drop
          local.get 9 move
          drop
          local.get 7 move
          drop
        end
        local.set 10
        local.get 4 follow
        unpack
          (result
          (exists type (val ptr nocopy exdrop)
            (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
              (ref (base mm) (ser (var 0))))))
          inferfx
          local.set 11
          local.get 11 follow
          ungroup
          local.set 13
          local.set 12
          local.get 13 follow
          local.get 10 follow
          group 2
          local.get 12 follow
          call_indirect
          local.get 12 move
          drop
          local.get 13 move
          drop
          local.get 11 move
          drop
        end
        local.get 10 move
        drop
        local.get 6 move
        drop
        local.get 5 move
        drop
        local.get 4 move
        drop
        local.get 1 move
        drop
        local.get 2 move
        drop)
      (func
          ((prod (ref (base mm) (ser (prod)))
             (exists type (val ptr nocopy exdrop)
               (prod
                 (coderef
                   ((prod (ref (base mm) (ser (var 0)))
                      (exists type (val ptr nocopy exdrop)
                        (prod
                          (coderef
                            ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                          (ref (base mm) (ser (var 0))))))
                     ->
                     (exists type (val ptr nocopy exdrop)
                       (prod
                         (coderef
                           ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                         (ref (base mm) (ser (var 0)))))))
                 (ref (base mm) (ser (var 0))))))
            ->
            (exists type (val ptr nocopy exdrop)
              (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                (ref (base mm) (ser (var 0))))))
          (local ptr (prod i32 ptr) (prod) (prod i32 ptr) (prod i32 ptr)
          (prod i32 ptr) i32 ptr)
        local.get 0 follow
        ungroup
        local.set 2
        local.set 1
        local.get 1 follow
        load (Path []) move
        local.set 3
        drop
        local.get 3 move
        ungroup
        local.get 2 follow
        local.set 4
        coderef 0
        local.get 4 follow
        group 1
        new mm
        group 2
        pack
          (type
            (prod
              (exists type (val ptr nocopy exdrop)
                (prod
                  (coderef
                    ((prod (ref (base mm) (ser (var 0)))
                       (exists type (val ptr nocopy exdrop)
                         (prod
                           (coderef
                             ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                           (ref (base mm) (ser (var 0))))))
                      ->
                      (exists type (val ptr nocopy exdrop)
                        (prod
                          (coderef
                            ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                          (ref (base mm) (ser (var 0)))))))
                  (ref (base mm) (ser (var 0)))))))
          (prod
            (coderef
              ((prod (ref (base mm) (ser (var 0)))
                 (rec (val (prod i32 ptr) nocopy exdrop)
                   (exists type (val ptr nocopy exdrop)
                     (prod
                       (coderef
                         ((prod (ref (base mm) (ser (var 0))) (var 1)) ->
                           (exists type (val ptr nocopy exdrop)
                             (prod
                               (coderef
                                 ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                               (ref (base mm) (ser (var 0)))))))
                       (ref (base mm) (ser (var 0)))))))
                ->
                (exists type (val ptr nocopy exdrop)
                  (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                    (ref (base mm) (ser (var 0)))))))
            (ref (base mm) (ser (var 0))))
        local.set 5
        local.get 5 follow
        unpack
          (result
          (exists type (val ptr nocopy exdrop)
            (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
              (ref (base mm) (ser (var 0))))))
          inferfx
          local.set 6
          local.get 6 follow
          ungroup
          local.set 8
          local.set 7
          local.get 8 follow
          local.get 5 follow
          fold
            (rec (val (prod i32 ptr) nocopy exdrop)
              (exists type (val ptr nocopy exdrop)
                (prod
                  (coderef
                    ((prod (ref (base mm) (ser (var 0))) (var 1)) ->
                      (exists type (val ptr nocopy exdrop)
                        (prod
                          (coderef
                            ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                          (ref (base mm) (ser (var 0)))))))
                  (ref (base mm) (ser (var 0))))))
          group 2
          local.get 7 follow
          call_indirect
          local.get 7 move
          drop
          local.get 8 move
          drop
          local.get 6 move
          drop
        end
        local.get 5 move
        drop
        local.get 4 move
        drop
        local.get 1 move
        drop
        local.get 2 move
        drop)
      (func
          ((prod
             (ref (base mm)
               (ser
                 (prod
                   (exists type (val ptr nocopy exdrop)
                     (prod
                       (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                       (ref (base mm) (ser (var 0))))))))
             i32)
            -> i32)
          (local ptr i32 (prod (prod i32 ptr)) (prod i32 ptr) i32 i32
          (prod i32 ptr) i32 ptr i32)
        local.get 0 follow
        ungroup
        local.set 2
        local.set 1
        local.get 1 follow
        load (Path []) move
        local.set 3
        drop
        local.get 3 move
        ungroup
        local.set 4
        local.get 2 follow
        local.set 5
        local.get 5 follow
        i32.eqz
        if (result i32) inferfx
          i32.const 1
        else
          local.get 5 follow
          i32.const 1
          i32.sub
          local.set 6
          local.get 4 follow
          unpack (result i32) inferfx
            local.set 7
            local.get 7 follow
            ungroup
            local.set 9
            local.set 8
            local.get 9 follow
            local.get 6 follow
            group 2
            local.get 8 follow
            call_indirect
            local.get 8 move
            drop
            local.get 9 move
            drop
            local.get 7 move
            drop
          end
          local.set 10
          local.get 5 follow
          local.get 10 follow
          i32.mul
          local.get 10 move
          drop
          local.get 6 move
          drop
        end
        local.get 5 move
        drop
        local.get 4 move
        drop
        local.get 1 move
        drop
        local.get 2 move
        drop)
      (func
          ((prod (ref (base mm) (ser (prod)))
             (exists type (val ptr nocopy exdrop)
               (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                 (ref (base mm) (ser (var 0))))))
            ->
            (exists type (val ptr nocopy exdrop)
              (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                (ref (base mm) (ser (var 0))))))
          (local ptr (prod i32 ptr) (prod) (prod i32 ptr))
        local.get 0 follow
        ungroup
        local.set 2
        local.set 1
        local.get 1 follow
        load (Path []) move
        local.set 3
        drop
        local.get 3 move
        ungroup
        local.get 2 follow
        local.set 4
        coderef 2
        local.get 4 follow
        group 1
        new mm
        group 2
        pack
          (type
            (prod
              (exists type (val ptr nocopy exdrop)
                (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                  (ref (base mm) (ser (var 0)))))))
          (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
            (ref (base mm) (ser (var 0))))
        local.get 4 move
        drop
        local.get 1 move
        drop
        local.get 2 move
        drop)
      (func (-> i32) (local (prod i32 ptr) (prod i32 ptr) i32 ptr (prod i32 ptr)
          (prod i32 ptr) i32 ptr)
        coderef 1
        group 0
        new mm
        group 2
        pack (type (prod))
          (prod
            (coderef
              ((prod (ref (base mm) (ser (var 0)))
                 (exists type (val ptr nocopy exdrop)
                   (prod
                     (coderef
                       ((prod (ref (base mm) (ser (var 0)))
                          (exists type (val ptr nocopy exdrop)
                            (prod
                              (coderef
                                ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                              (ref (base mm) (ser (var 0))))))
                         ->
                         (exists type (val ptr nocopy exdrop)
                           (prod
                             (coderef
                               ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                             (ref (base mm) (ser (var 0)))))))
                     (ref (base mm) (ser (var 0))))))
                ->
                (exists type (val ptr nocopy exdrop)
                  (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                    (ref (base mm) (ser (var 0)))))))
            (ref (base mm) (ser (var 0))))
        local.set 0
        local.get 0 follow
        unpack
          (result
          (exists type (val ptr nocopy exdrop)
            (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
              (ref (base mm) (ser (var 0))))))
          inferfx
          local.set 1
          local.get 1 follow
          ungroup
          local.set 3
          local.set 2
          local.get 3 follow
          coderef 3
          group 0
          new mm
          group 2
          pack (type (prod))
            (prod
              (coderef
                ((prod (ref (base mm) (ser (var 0)))
                   (exists type (val ptr nocopy exdrop)
                     (prod
                       (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                       (ref (base mm) (ser (var 0))))))
                  ->
                  (exists type (val ptr nocopy exdrop)
                    (prod
                      (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                      (ref (base mm) (ser (var 0)))))))
              (ref (base mm) (ser (var 0))))
          group 2
          local.get 2 follow
          call_indirect
          local.get 2 move
          drop
          local.get 3 move
          drop
          local.get 1 move
          drop
        end
        local.set 4
        local.get 4 follow
        unpack (result i32) inferfx
          local.set 5
          local.get 5 follow
          ungroup
          local.set 7
          local.set 6
          local.get 7 follow
          i32.const 5
          group 2
          local.get 6 follow
          call_indirect
          local.get 6 move
          drop
          local.get 7 move
          drop
          local.get 5 move
          drop
        end
        local.get 4 move
        drop
        local.get 0 move
        drop)
      (table 0 1 2 3)
      (export "_start" (func 4)))
    -----------unboxed_list[invalid]-----------
    FAILURE (CannotResolveRepOfRecTypeWithoutIndirection (Var (0 ("\206\177"))))
    -----------boxed_list-----------
    (module
      (func ((prod (ref (base mm) (ser (prod))) i32) -> i32) (local ptr i32
          (prod) i32)
        local.get 0 follow
        ungroup
        local.set 2
        local.set 1
        local.get 1 follow
        load (Path []) move
        local.set 3
        drop
        local.get 3 move
        ungroup
        local.get 2 follow
        local.set 4
        local.get 4 follow
        i32.const 1
        i32.add
        local.get 4 move
        drop
        local.get 1 move
        drop
        local.get 2 move
        drop)
      (func
          ((prod (ref (base mm) (ser (prod)))
             (prod
               (exists type (val ptr nocopy exdrop)
                 (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                   (ref (base mm) (ser (var 0)))))
               (rec (val (sum (prod) (prod i32 ptr)) nocopy exdrop)
                 (sum (prod) (prod i32 (ref (base mm) (ser (var 0))))))))
            ->
            (rec (val (sum (prod) (prod i32 ptr)) nocopy exdrop)
              (sum (prod) (prod i32 (ref (base mm) (ser (var 0)))))))
          (local ptr (prod (prod i32 ptr) (sum (prod) (prod i32 ptr)))
          (prod i32 ptr) (sum (prod) (prod i32 ptr)) (prod) (prod i32 ptr) i32 ptr
          (prod i32 ptr) i32 ptr (prod i32 ptr) i32 ptr
          (sum (prod) (prod i32 ptr)))
        local.get 0 follow
        ungroup
        local.set 2
        local.set 1
        local.get 2 follow
        ungroup
        local.set 4
        local.set 3
        local.get 4 follow
        unfold
        case
          (result
          (sum (prod)
            (prod i32
              (ref (base mm)
                (ser
                  (rec (val (sum (prod) (prod i32 ptr)) nocopy exdrop)
                    (sum (prod) (prod i32 (ref (base mm) (ser (var 0)))))))))))
          inferfx
          (0
            local.set 5
            local.get 5 follow
            inject 0 (prod)
              (prod i32
                (ref (base mm)
                  (ser
                    (rec (val (sum (prod) (prod i32 ptr)) nocopy exdrop)
                      (sum (prod) (prod i32 (ref (base mm) (ser (var 0)))))))))
            local.get 5 move
            drop)
          (1
            local.set 6
            local.get 6 follow
            ungroup
            local.set 8
            local.set 7
            local.get 3 follow
            unpack (result i32) inferfx
              local.set 9
              local.get 9 follow
              ungroup
              local.set 11
              local.set 10
              local.get 11 follow
              local.get 7 follow
              group 2
              local.get 10 follow
              call_indirect
              local.get 10 move
              drop
              local.get 11 move
              drop
              local.get 9 move
              drop
            end
            coderef 1
            group 0
            new mm
            group 2
            pack (type (prod))
              (prod
                (coderef
                  ((prod (ref (base mm) (ser (var 0)))
                     (prod
                       (exists type (val ptr nocopy exdrop)
                         (prod
                           (coderef
                             ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                           (ref (base mm) (ser (var 0)))))
                       (rec (val (sum (prod) (prod i32 ptr)) nocopy exdrop)
                         (sum (prod) (prod i32 (ref (base mm) (ser (var 0))))))))
                    ->
                    (rec (val (sum (prod) (prod i32 ptr)) nocopy exdrop)
                      (sum (prod) (prod i32 (ref (base mm) (ser (var 0))))))))
                (ref (base mm) (ser (var 0))))
            unpack
              (result
              (rec (val (sum (prod) (prod i32 ptr)) nocopy exdrop)
                (sum (prod) (prod i32 (ref (base mm) (ser (var 0)))))))
              inferfx
              local.set 12
              local.get 12 follow
              ungroup
              local.set 14
              local.set 13
              local.get 14 follow
              local.get 3 follow
              local.get 8 follow
              load (Path []) move
              local.set 15
              drop
              local.get 15 move
              group 2
              group 2
              local.get 13 follow
              call_indirect
              local.get 13 move
              drop
              local.get 14 move
              drop
              local.get 12 move
              drop
            end
            new mm
            group 2
            inject 1 (prod)
              (prod i32
                (ref (base mm)
                  (ser
                    (rec (val (sum (prod) (prod i32 ptr)) nocopy exdrop)
                      (sum (prod) (prod i32 (ref (base mm) (ser (var 0)))))))))
            local.get 7 move
            drop
            local.get 8 move
            drop
            local.get 6 move
            drop)
        end
        fold
          (rec (val (sum (prod) (prod i32 ptr)) nocopy exdrop)
            (sum (prod) (prod i32 (ref (base mm) (ser (var 0))))))
        local.get 3 move
        drop
        local.get 4 move
        drop
        local.get 1 move
        drop
        local.get 2 move
        drop)
      (func
          (->
            (rec (val (sum (prod) (prod i32 ptr)) nocopy exdrop)
              (sum (prod) (prod i32 (ref (base mm) (ser (var 0)))))))
          (local (sum (prod) (prod i32 ptr)) (prod i32 ptr) i32 ptr)
        i32.const 5
        group 0
        inject 0 (prod)
          (prod i32
            (ref (base mm)
              (ser
                (rec (val (sum (prod) (prod i32 ptr)) nocopy exdrop)
                  (sum (prod) (prod i32 (ref (base mm) (ser (var 0)))))))))
        fold
          (rec (val (sum (prod) (prod i32 ptr)) nocopy exdrop)
            (sum (prod) (prod i32 (ref (base mm) (ser (var 0))))))
        new mm
        group 2
        inject 1 (prod)
          (prod i32
            (ref (base mm)
              (ser
                (rec (val (sum (prod) (prod i32 ptr)) nocopy exdrop)
                  (sum (prod) (prod i32 (ref (base mm) (ser (var 0)))))))))
        fold
          (rec (val (sum (prod) (prod i32 ptr)) nocopy exdrop)
            (sum (prod) (prod i32 (ref (base mm) (ser (var 0))))))
        local.set 0
        coderef 1
        group 0
        new mm
        group 2
        pack (type (prod))
          (prod
            (coderef
              ((prod (ref (base mm) (ser (var 0)))
                 (prod
                   (exists type (val ptr nocopy exdrop)
                     (prod
                       (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
                       (ref (base mm) (ser (var 0)))))
                   (rec (val (sum (prod) (prod i32 ptr)) nocopy exdrop)
                     (sum (prod) (prod i32 (ref (base mm) (ser (var 0))))))))
                ->
                (rec (val (sum (prod) (prod i32 ptr)) nocopy exdrop)
                  (sum (prod) (prod i32 (ref (base mm) (ser (var 0))))))))
            (ref (base mm) (ser (var 0))))
        unpack
          (result
          (rec (val (sum (prod) (prod i32 ptr)) nocopy exdrop)
            (sum (prod) (prod i32 (ref (base mm) (ser (var 0)))))))
          inferfx
          local.set 1
          local.get 1 follow
          ungroup
          local.set 3
          local.set 2
          local.get 3 follow
          coderef 0
          group 0
          new mm
          group 2
          pack (type (prod))
            (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
              (ref (base mm) (ser (var 0))))
          local.get 0 follow
          group 2
          group 2
          local.get 2 follow
          call_indirect
          local.get 2 move
          drop
          local.get 3 move
          drop
          local.get 1 move
          drop
        end
        local.get 0 move
        drop)
      (table 0 1)
      (export "_start" (func 2)))
    -----------peano_3-----------
    (module
      (func
          (->
            (rec (val (sum (prod) ptr) nocopy exdrop)
              (sum (prod) (ref (base mm) (ser (var 0))))))
        group 0
        inject 0 (prod)
          (ref (base mm)
            (ser
              (rec (val (sum (prod) ptr) nocopy exdrop)
                (sum (prod) (ref (base mm) (ser (var 0)))))))
        fold
          (rec (val (sum (prod) ptr) nocopy exdrop)
            (sum (prod) (ref (base mm) (ser (var 0)))))
        new mm
        inject 1 (prod)
          (ref (base mm)
            (ser
              (rec (val (sum (prod) ptr) nocopy exdrop)
                (sum (prod) (ref (base mm) (ser (var 0)))))))
        fold
          (rec (val (sum (prod) ptr) nocopy exdrop)
            (sum (prod) (ref (base mm) (ser (var 0)))))
        new mm
        inject 1 (prod)
          (ref (base mm)
            (ser
              (rec (val (sum (prod) ptr) nocopy exdrop)
                (sum (prod) (ref (base mm) (ser (var 0)))))))
        fold
          (rec (val (sum (prod) ptr) nocopy exdrop)
            (sum (prod) (ref (base mm) (ser (var 0)))))
        new mm
        inject 1 (prod)
          (ref (base mm)
            (ser
              (rec (val (sum (prod) ptr) nocopy exdrop)
                (sum (prod) (ref (base mm) (ser (var 0)))))))
        fold
          (rec (val (sum (prod) ptr) nocopy exdrop)
            (sum (prod) (ref (base mm) (ser (var 0))))))
      (table)
      (export "_start" (func 0)))
    -----------peano-----------
    (module
      (func
          ((prod (ref (base mm) (ser (prod)))
             (prod
               (rec (val (sum (prod) ptr) nocopy exdrop)
                 (sum (prod) (ref (base mm) (ser (var 0)))))
               (rec (val (sum (prod) ptr) nocopy exdrop)
                 (sum (prod) (ref (base mm) (ser (var 0)))))))
            ->
            (rec (val (sum (prod) ptr) nocopy exdrop)
              (sum (prod) (ref (base mm) (ser (var 0))))))
          (local ptr (prod (sum (prod) ptr) (sum (prod) ptr)) (sum (prod) ptr)
          (sum (prod) ptr) (prod) ptr (prod i32 ptr) i32 ptr (sum (prod) ptr))
        local.get 0 follow
        ungroup
        local.set 2
        local.set 1
        local.get 2 follow
        ungroup
        local.set 4
        local.set 3
        local.get 3 follow
        unfold
        case
          (result
          (rec (val (sum (prod) ptr) nocopy exdrop)
            (sum (prod) (ref (base mm) (ser (var 0))))))
          inferfx
          (0
            local.set 5
            local.get 4 follow
            local.get 5 move
            drop)
          (1
            local.set 6
            coderef 0
            group 0
            new mm
            group 2
            pack (type (prod))
              (prod
                (coderef
                  ((prod (ref (base mm) (ser (var 0)))
                     (prod
                       (rec (val (sum (prod) ptr) nocopy exdrop)
                         (sum (prod) (ref (base mm) (ser (var 0)))))
                       (rec (val (sum (prod) ptr) nocopy exdrop)
                         (sum (prod) (ref (base mm) (ser (var 0)))))))
                    ->
                    (rec (val (sum (prod) ptr) nocopy exdrop)
                      (sum (prod) (ref (base mm) (ser (var 0)))))))
                (ref (base mm) (ser (var 0))))
            unpack
              (result
              (rec (val (sum (prod) ptr) nocopy exdrop)
                (sum (prod) (ref (base mm) (ser (var 0))))))
              inferfx
              local.set 7
              local.get 7 follow
              ungroup
              local.set 9
              local.set 8
              local.get 9 follow
              local.get 6 follow
              load (Path []) move
              local.set 10
              drop
              local.get 10 move
              local.get 4 follow
              group 2
              group 2
              local.get 8 follow
              call_indirect
              local.get 8 move
              drop
              local.get 9 move
              drop
              local.get 7 move
              drop
            end
            new mm
            inject 1 (prod)
              (ref (base mm)
                (ser
                  (rec (val (sum (prod) ptr) nocopy exdrop)
                    (sum (prod) (ref (base mm) (ser (var 0)))))))
            fold
              (rec (val (sum (prod) ptr) nocopy exdrop)
                (sum (prod) (ref (base mm) (ser (var 0)))))
            local.get 6 move
            drop)
        end
        local.get 3 move
        drop
        local.get 4 move
        drop
        local.get 1 move
        drop
        local.get 2 move
        drop)
      (func
          ((prod (ref (base mm) (ser (prod))) i32) ->
            (rec (val (sum (prod) ptr) nocopy exdrop)
              (sum (prod) (ref (base mm) (ser (var 0))))))
          (local ptr i32 (prod i32 ptr) i32 ptr)
        local.get 0 follow
        ungroup
        local.set 2
        local.set 1
        local.get 2 follow
        i32.eqz
        if
          (result
          (sum (prod)
            (ref (base mm)
              (ser
                (rec (val (sum (prod) ptr) nocopy exdrop)
                  (sum (prod) (ref (base mm) (ser (var 0)))))))))
          inferfx
          group 0
          inject 0 (prod)
            (ref (base mm)
              (ser
                (rec (val (sum (prod) ptr) nocopy exdrop)
                  (sum (prod) (ref (base mm) (ser (var 0)))))))
        else
          coderef 1
          group 0
          new mm
          group 2
          pack (type (prod))
            (prod
              (coderef
                ((prod (ref (base mm) (ser (var 0))) i32) ->
                  (rec (val (sum (prod) ptr) nocopy exdrop)
                    (sum (prod) (ref (base mm) (ser (var 0)))))))
              (ref (base mm) (ser (var 0))))
          unpack
            (result
            (rec (val (sum (prod) ptr) nocopy exdrop)
              (sum (prod) (ref (base mm) (ser (var 0))))))
            inferfx
            local.set 3
            local.get 3 follow
            ungroup
            local.set 5
            local.set 4
            local.get 5 follow
            local.get 2 follow
            i32.const 1
            i32.sub
            group 2
            local.get 4 follow
            call_indirect
            local.get 4 move
            drop
            local.get 5 move
            drop
            local.get 3 move
            drop
          end
          new mm
          inject 1 (prod)
            (ref (base mm)
              (ser
                (rec (val (sum (prod) ptr) nocopy exdrop)
                  (sum (prod) (ref (base mm) (ser (var 0)))))))
        end
        fold
          (rec (val (sum (prod) ptr) nocopy exdrop)
            (sum (prod) (ref (base mm) (ser (var 0)))))
        local.get 1 move
        drop
        local.get 2 move
        drop)
      (func
          ((prod (ref (base mm) (ser (prod)))
             (rec (val (sum (prod) ptr) nocopy exdrop)
               (sum (prod) (ref (base mm) (ser (var 0))))))
            -> i32)
          (local ptr (sum (prod) ptr) (prod) ptr (prod i32 ptr) i32 ptr
          (sum (prod) ptr))
        local.get 0 follow
        ungroup
        local.set 2
        local.set 1
        local.get 2 follow
        unfold
        case (result i32) inferfx
          (0
            local.set 3
            i32.const 0
            local.get 3 move
            drop)
          (1
            local.set 4
            i32.const 1
            coderef 2
            group 0
            new mm
            group 2
            pack (type (prod))
              (prod
                (coderef
                  ((prod (ref (base mm) (ser (var 0)))
                     (rec (val (sum (prod) ptr) nocopy exdrop)
                       (sum (prod) (ref (base mm) (ser (var 0))))))
                    -> i32))
                (ref (base mm) (ser (var 0))))
            unpack (result i32) inferfx
              local.set 5
              local.get 5 follow
              ungroup
              local.set 7
              local.set 6
              local.get 7 follow
              local.get 4 follow
              load (Path []) move
              local.set 8
              drop
              local.get 8 move
              group 2
              local.get 6 follow
              call_indirect
              local.get 6 move
              drop
              local.get 7 move
              drop
              local.get 5 move
              drop
            end
            i32.add
            local.get 4 move
            drop)
        end
        local.get 1 move
        drop
        local.get 2 move
        drop)
      (func (-> i32) (local (prod i32 ptr) i32 ptr (sum (prod) ptr) (prod i32 ptr)
          i32 ptr (sum (prod) ptr) (prod i32 ptr) i32 ptr (sum (prod) ptr)
          (prod i32 ptr) i32 ptr)
        coderef 1
        group 0
        new mm
        group 2
        pack (type (prod))
          (prod
            (coderef
              ((prod (ref (base mm) (ser (var 0))) i32) ->
                (rec (val (sum (prod) ptr) nocopy exdrop)
                  (sum (prod) (ref (base mm) (ser (var 0)))))))
            (ref (base mm) (ser (var 0))))
        unpack
          (result
          (rec (val (sum (prod) ptr) nocopy exdrop)
            (sum (prod) (ref (base mm) (ser (var 0))))))
          inferfx
          local.set 0
          local.get 0 follow
          ungroup
          local.set 2
          local.set 1
          local.get 2 follow
          i32.const 6
          group 2
          local.get 1 follow
          call_indirect
          local.get 1 move
          drop
          local.get 2 move
          drop
          local.get 0 move
          drop
        end
        local.set 3
        coderef 1
        group 0
        new mm
        group 2
        pack (type (prod))
          (prod
            (coderef
              ((prod (ref (base mm) (ser (var 0))) i32) ->
                (rec (val (sum (prod) ptr) nocopy exdrop)
                  (sum (prod) (ref (base mm) (ser (var 0)))))))
            (ref (base mm) (ser (var 0))))
        unpack
          (result
          (rec (val (sum (prod) ptr) nocopy exdrop)
            (sum (prod) (ref (base mm) (ser (var 0))))))
          inferfx
          local.set 4
          local.get 4 follow
          ungroup
          local.set 6
          local.set 5
          local.get 6 follow
          i32.const 7
          group 2
          local.get 5 follow
          call_indirect
          local.get 5 move
          drop
          local.get 6 move
          drop
          local.get 4 move
          drop
        end
        local.set 7
        coderef 0
        group 0
        new mm
        group 2
        pack (type (prod))
          (prod
            (coderef
              ((prod (ref (base mm) (ser (var 0)))
                 (prod
                   (rec (val (sum (prod) ptr) nocopy exdrop)
                     (sum (prod) (ref (base mm) (ser (var 0)))))
                   (rec (val (sum (prod) ptr) nocopy exdrop)
                     (sum (prod) (ref (base mm) (ser (var 0)))))))
                ->
                (rec (val (sum (prod) ptr) nocopy exdrop)
                  (sum (prod) (ref (base mm) (ser (var 0)))))))
            (ref (base mm) (ser (var 0))))
        unpack
          (result
          (rec (val (sum (prod) ptr) nocopy exdrop)
            (sum (prod) (ref (base mm) (ser (var 0))))))
          inferfx
          local.set 8
          local.get 8 follow
          ungroup
          local.set 10
          local.set 9
          local.get 10 follow
          local.get 3 follow
          local.get 7 follow
          group 2
          group 2
          local.get 9 follow
          call_indirect
          local.get 9 move
          drop
          local.get 10 move
          drop
          local.get 8 move
          drop
        end
        local.set 11
        coderef 2
        group 0
        new mm
        group 2
        pack (type (prod))
          (prod
            (coderef
              ((prod (ref (base mm) (ser (var 0)))
                 (rec (val (sum (prod) ptr) nocopy exdrop)
                   (sum (prod) (ref (base mm) (ser (var 0))))))
                -> i32))
            (ref (base mm) (ser (var 0))))
        unpack (result i32) inferfx
          local.set 12
          local.get 12 follow
          ungroup
          local.set 14
          local.set 13
          local.get 14 follow
          local.get 11 follow
          group 2
          local.get 13 follow
          call_indirect
          local.get 13 move
          drop
          local.get 14 move
          drop
          local.get 12 move
          drop
        end
        local.get 11 move
        drop
        local.get 7 move
        drop
        local.get 3 move
        drop)
      (table 0 1 2)
      (export "_start" (func 3)))
    -----------mini_zip-----------
    (module
      (func ((prod (ref (base mm) (ser (prod))) i32) -> i32) (local ptr i32)
        local.get 0 follow
        ungroup
        local.set 2
        local.set 1
        local.get 2 follow
        i32.const 1
        i32.add
        local.get 1 move
        drop
        local.get 2 move
        drop)
      (func ((prod (ref (base mm) (ser (prod))) (prod i32 i32)) -> (prod i32 i32))
          (local ptr (prod i32 i32) i32 i32 (prod i32 ptr) i32 ptr (prod i32 ptr)
          i32 ptr)
        local.get 0 follow
        ungroup
        local.set 2
        local.set 1
        local.get 2 follow
        ungroup
        local.set 4
        local.set 3
        coderef 0
        group 0
        new mm
        group 2
        pack (type (prod))
          (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
            (ref (base mm) (ser (var 0))))
        unpack (result i32) inferfx
          local.set 5
          local.get 5 follow
          ungroup
          local.set 7
          local.set 6
          local.get 7 follow
          local.get 3 follow
          group 2
          local.get 6 follow
          call_indirect
          local.get 6 move
          drop
          local.get 7 move
          drop
          local.get 5 move
          drop
        end
        coderef 0
        group 0
        new mm
        group 2
        pack (type (prod))
          (prod (coderef ((prod (ref (base mm) (ser (var 0))) i32) -> i32))
            (ref (base mm) (ser (var 0))))
        unpack (result i32) inferfx
          local.set 8
          local.get 8 follow
          ungroup
          local.set 10
          local.set 9
          local.get 10 follow
          local.get 4 follow
          group 2
          local.get 9 follow
          call_indirect
          local.get 9 move
          drop
          local.get 10 move
          drop
          local.get 8 move
          drop
        end
        group 2
        local.get 3 move
        drop
        local.get 4 move
        drop
        local.get 1 move
        drop
        local.get 2 move
        drop)
      (func
          ((prod (ref (base mm) (ser (prod)))
             (prod (ref (base mm) (ser i32))
               (ref (base mm) (ser (ref (base mm) (ser i32))))))
            -> (ref (base mm) (ser (prod i32 (ref (base mm) (ser i32))))))
          (local ptr (prod ptr ptr) ptr ptr i32 ptr)
        local.get 0 follow
        ungroup
        local.set 2
        local.set 1
        local.get 2 follow
        ungroup
        local.set 4
        local.set 3
        local.get 3 follow
        load (Path []) move
        local.set 5
        drop
        local.get 5 move
        local.get 4 follow
        load (Path []) move
        local.set 6
        drop
        local.get 6 move
        group 2
        new mm
        local.get 3 move
        drop
        local.get 4 move
        drop
        local.get 1 move
        drop
        local.get 2 move
        drop)
      (table 0 1 2)
      (export "typle_add1" (func 1))) |}]
