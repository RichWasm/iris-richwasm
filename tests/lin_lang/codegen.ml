open! Base
open! Stdlib.Format
open! Richwasm_lin_lang
module RichWasm = Richwasm_common.Syntax

include Help.MultiOutputter.Make (struct
  open Help

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
  let examples = Examples.all
  let pp = RichWasm.Module.pp
  let pp_sexp = RichWasm.Module.pp_sexp
end)

let%expect_test "basic functionality" =
  run {| 1 |};
  [%expect
    {|
    (module
      (func (-> i32)
        i32.const 1)
      (table)
      0) |}];
  next ();
  [%expect
    {|
    ((imports ())
     (functions
      (((typ (FunctionType () () ((Num (Int I32))))) (locals ())
        (body ((NumConst (Int I32) 1))))))
     (table ()) (exports (0))) |}];

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
      0) |}];
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
     (table ()) (exports (0))) |}];

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
      0) |}];

  run {| (new 10) |};
  [%expect
    {|
    (module
      (func (-> (ref mm i32))
        i32.const 10
        new mm i32)
      (table)
      0) |}];

  run {| (1 + 2) |};
  [%expect
    {|
    (module
      (func (-> i32)
        i32.const 1
        i32.const 2
        i32.add)
      (table)
      0) |}];
  next ();
  [%expect
    {|
    ((imports ())
     (functions
      (((typ (FunctionType () () ((Num (Int I32))))) (locals ())
        (body ((NumConst (Int I32) 1) (NumConst (Int I32) 2) (Num (Int2 I32 Add)))))))
     (table ()) (exports (0))) |}];

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
      0)
    -----------flat_tuple-----------
    (module
      (func (-> (prod i32 i32 i32 i32))
        i32.const 1
        i32.const 2
        i32.const 3
        i32.const 4
        group 4)
      (table)
      0)
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
      0)
    -----------single_sum-----------
    (module
      (func (-> (sum (prod)))
        group 0
        inject 0 (prod))
      (table)
      0)
    -----------double_sum-----------
    (module
      (func (-> (sum (prod) i32))
        i32.const 15
        inject 1 (prod) i32)
      (table)
      0)
    -----------arith_add-----------
    (module
      (func (-> i32)
        i32.const 9
        i32.const 10
        i32.add)
      (table)
      0)
    -----------arith_sub-----------
    (module
      (func (-> i32)
        i32.const 67
        i32.const 41
        i32.sub)
      (table)
      0)
    -----------arith_mul-----------
    (module
      (func (-> i32)
        i32.const 42
        i32.const 10
        i32.mul)
      (table)
      0)
    -----------arith_div-----------
    (module
      (func (-> i32)
        i32.const -30
        i32.const 10
        i32.div_s)
      (table)
      0)
    -----------app_ident-----------
    (module
      (func ((prod) -> i32)(local ptr i32 (prod))
        local.get 0
        local.set 1
        local.set 2
        local.get 1
        load (Path [])
        local.set 3
        drop
        local.get 3
        local.get 2)
      (func (-> i32)(local ptr (prod ptr i32) ptr)
        coderef -1
        group 0
        new mm (prod)
        group 2
        pack (Type (ref mm (prod))) (exists type (VALTYPE (ptr, excopy, exdrop))
                                    (coderef ((prod (var 0) i32) -> i32))
        unpack (result i32) (LocalFx [])
                                           local.get 0
                                           local.get 0
                                           local.set 1
                                           local.set 2
                                           local.get 2
                                           i32.const 10
                                           group 2
                                           local.get 1
                                           call_indirect)
      (table  -1)
      1)
    -----------nested_arith-----------
    (module
      (func (-> i32)
        i32.const 9
        i32.const 10
        i32.add
        i32.const 5
        i32.mul)
      (table)
      0)
    -----------let_bind-----------
    (module
      (func (-> i32)(local i32)
        i32.const 10
        local.set 0
        local.get 0)
      (table)
      0)
    -----------add_one_program-----------
    (module
      (func ((prod (ref mm (prod)) i32) -> i32)
        local.get 0
        i32.const 1
        i32.add)
      (func (-> i32)(local ptr (prod ptr i32) ptr)
        coderef -1
        group 0
        new mm (prod)
        group 2
        pack (Type (prod)) (exists type (VALTYPE (ptr, excopy, exdrop)) (coderef
                                                                        (
                                                                        (prod
                                                                        (var 0)
                                                                        i32) ->
                                                                        i32))
        unpack (result i32) (LocalFx [])
                                           local.get 0
                                           local.get 0
                                           local.set 1
                                           local.set 2
                                           local.get 2
                                           i32.const 42
                                           group 2
                                           local.get 1
                                           call_indirect)
      (table  -1)
      0
      1)
    -----------add_tup_ref-----------
    (module
      (func (-> i32)(local ptr i32 ptr i32 i32)
        i32.const 2
        new mm i32
        local.set 0
        i32.const 1
        local.get 0
        group 2
        local.set 1
        local.set 2
        local.get 2
        load (Path [])
        local.set 3
        drop
        local.get 3
        local.set 4
        local.get 1
        local.get 4
        i32.add)
      (table)
      0)
    -----------print_10-----------
    (module
      ((prod (ref mm (prod)) i32) -> (prod))
      (func (-> (prod))(local ptr (prod ptr i32) ptr)
        coderef 0
        group 0
        new mm (prod)
        group 2
        pack (Type (prod)) (exists type (VALTYPE (ptr, excopy, exdrop)) (coderef
                                                                        (
                                                                        (prod
                                                                        (var 0)
                                                                        i32) ->
                                                                        (prod)))
        unpack (result (prod)) (LocalFx [])
                                              local.get 0
                                              local.get 0
                                              local.set 1
                                              local.set 2
                                              local.get 2
                                              i32.const 10
                                              group 2
                                              local.get 1
                                              call_indirect)
      (table)
      0)
    -----------factorial_program-----------
    (module
      (func ((prod (ref mm (prod)) i32) -> i32)(local i32 ptr (prod ptr i32) ptr
                                               i32)
        local.get 0
        i32.const 0
        i32.eqz
        if (result i32) (LocalFx [])
                                      i32.const 1
        else
              local.get 0
              i32.const 1
              i32.sub
              local.set 1
              coderef -1
              group 0
              new mm (prod)
              group 2
              pack (Type (prod)) (exists type (VALTYPE (ptr, excopy, exdrop))
                                 (coderef ((prod (var 0) i32) -> i32))
              unpack (result i32) (LocalFx [])
                                                 local.get 2
                                                 local.get 2
                                                 local.set 3
                                                 local.set 4
                                                 local.get 4
                                                 local.get 4
                                                 group 2
                                                 local.get 3
                                                 call_indirect
              local.set 5
              local.get 0
              local.get 5
              i32.mul
        end)
      (func (-> i32)(local ptr (prod ptr i32) ptr)
        coderef -1
        group 0
        new mm (prod)
        group 2
        pack (Type (prod)) (exists type (VALTYPE (ptr, excopy, exdrop)) (coderef
                                                                        (
                                                                        (prod
                                                                        (var 0)
                                                                        i32) ->
                                                                        i32))
        unpack (result i32) (LocalFx [])
                                           local.get 0
                                           local.get 0
                                           local.set 1
                                           local.set 2
                                           local.get 2
                                           i32.const 5
                                           group 2
                                           local.get 1
                                           call_indirect)
      (table  -1)
      0
      1)
    -----------safe_div-----------
    (module
      (func ((prod (ref mm (prod)) (prod i32 i32)) -> (sum i32 (prod)))(local i32
                                                                       i32 i32)
        local.get 0
        local.set 1
        local.set 2
        local.get 2
        i32.const 0
        i32.eqz
        if (result (sum i32 (prod))) (LocalFx [])
                                                   group 0
                                                   inject 1 i32 (prod)
        else
              local.get 1
              local.get 2
              i32.div_s
              local.set 3
              local.get 3
              inject 0 i32 (prod)
        end)
      (func ((prod (ref mm (prod)) (sum i32 (prod))) -> i32)(local i32 (prod))
        local.get 0
        case (result i32) (LocalFx [])(0

                                          local.set 1
                                          local.get 1)(1

                                                          local.set 2
                                                          i32.const 0)end
        )
      (func (-> i32)(local ptr (prod ptr i32) ptr (sum i32 (prod)) ptr
                    (prod ptr i32) ptr)
        coderef -1
        group 0
        new mm (prod)
        group 2
        pack (Type (prod)) (exists type (VALTYPE (ptr, excopy, exdrop)) (coderef
                                                                        (
                                                                        (prod
                                                                        (var 0)
                                                                        (prod i32
                                                                        i32)) ->
                                                                        (sum i32
                                                                        (prod))))
        unpack (result (sum i32 (prod))) (LocalFx [])
                                                        local.get 0
                                                        local.get 0
                                                        local.set 1
                                                        local.set 2
                                                        local.get 2
                                                        i32.const 10
                                                        i32.const 0
                                                        group 2
                                                        group 2
                                                        local.get 1
                                                        call_indirect
        local.set 3
        coderef 0
        group 0
        new mm (prod)
        group 2
        pack (Type (prod)) (exists type (VALTYPE (ptr, excopy, exdrop)) (coderef
                                                                        (
                                                                        (prod
                                                                        (var 0)
                                                                        (sum i32
                                                                        (prod))) ->
                                                                        i32))
        unpack (result i32) (LocalFx [])
                                           local.get 4
                                           local.get 4
                                           local.set 5
                                           local.set 6
                                           local.get 6
                                           local.get 6
                                           group 2
                                           local.get 5
                                           call_indirect)
      (table  -1 0)
      2)
    -----------incr_n-----------
    (module
      (func ((prod (ref mm (prod)) (ref mm i32)) -> (ref mm i32))(local ptr i32 i32
                                                                 ptr i32)
        local.get 0
        i32.const 0
        swap (Path [])
        group 2
        local.set 1
        local.set 2
        local.get 2
        i32.const 1
        i32.add
        local.set 3
        local.get 1
        local.get 3
        swap (Path [])
        group 2
        local.set 4
        local.set 5
        local.get 4)
      (func ((prod (ref mm (prod)) (prod (ref mm i32) i32)) -> i32)(local ptr i32
                                                                   i32 ptr
                                                                   (prod ptr i32)
                                                                   ptr ptr i32 ptr
                                                                   (prod ptr i32)
                                                                   ptr)
        local.get 0
        local.set 1
        local.set 2
        local.get 2
        i32.const 0
        i32.eqz
        if (result i32) (LocalFx [])
                                      local.get 1
                                      load (Path [])
                                      local.set 3
                                      drop
                                      local.get 3
        else
              coderef -1
              group 0
              new mm (prod)
              group 2
              pack (Type (prod)) (exists type (VALTYPE (ptr, excopy, exdrop))
                                 (coderef ((prod (var 0) (ref mm i32)) ->
                                          (ref mm i32)))
              unpack (result (ref mm i32)) (LocalFx [])
                                                          local.get 4
                                                          local.get 4
                                                          local.set 5
                                                          local.set 6
                                                          local.get 6
                                                          local.get 5
                                                          group 2
                                                          local.get 5
                                                          call_indirect
              local.set 7
              local.get 2
              i32.const 1
              i32.sub
              local.set 8
              coderef 0
              group 0
              new mm (prod)
              group 2
              pack (Type (prod)) (exists type (VALTYPE (ptr, excopy, exdrop))
                                 (coderef ((prod (var 0) (prod (ref mm i32) i32))
                                          -> i32))
              unpack (result i32) (LocalFx [])
                                                 local.get 9
                                                 local.get 9
                                                 local.set 10
                                                 local.set 11
                                                 local.get 11
                                                 local.get 10
                                                 local.get 11
                                                 group 2
                                                 group 2
                                                 local.get 10
                                                 call_indirect
        end)
      (func (-> i32)(local ptr ptr (prod ptr i32) ptr)
        i32.const 10
        new mm i32
        local.set 0
        coderef 0
        group 0
        new mm (prod)
        group 2
        pack (Type (prod)) (exists type (VALTYPE (ptr, excopy, exdrop)) (coderef
                                                                        (
                                                                        (prod
                                                                        (var 0)
                                                                        (prod
                                                                        (ref mm i32)
                                                                        i32)) ->
                                                                        i32))
        unpack (result i32) (LocalFx [])
                                           local.get 1
                                           local.get 1
                                           local.set 2
                                           local.set 3
                                           local.get 3
                                           local.get 3
                                           i32.const 3
                                           group 2
                                           group 2
                                           local.get 2
                                           call_indirect)
      (table  -1 0)
      1
      2)
    -----------fix_factorial[invalid]-----------
    FAILURE (Ctx (CannotFindRep (Var (0 ())))
     (Exists
      (Lollipop
       (Prod
        ((Var (0 ()))
         (Exists
          (Lollipop
           (Prod
            ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
           (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))
       (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
    -----------unboxed_list[invlaid]-----------
    FAILURE (Ctx (CannotFindRep (Var (0 ("\206\177"))))
     (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
    -----------boxed_list-----------
    FAILURE (Ctx (CannotFindRep (Var (0 ())))
     (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))) |}]
