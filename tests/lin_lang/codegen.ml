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
      (export 0)) |}];
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
      (export 0)) |}];
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
      (export 0)) |}];

  run {| (new 10) |};
  [%expect
    {|
    (module
      (func (-> (ref (concrete mm) i32))
        i32.const 10
        new mm i32)
      (table)
      (export 0)) |}];

  run {| (1 + 2) |};
  [%expect
    {|
    (module
      (func (-> i32)
        i32.const 1
        i32.const 2
        i32.add)
      (table)
      (export 0)) |}];
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
      (export 0))
    -----------flat_tuple-----------
    (module
      (func (-> (prod i32 i32 i32 i32))
        i32.const 1
        i32.const 2
        i32.const 3
        i32.const 4
        group 4)
      (table)
      (export 0))
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
      (export 0))
    -----------single_sum-----------
    (module
      (func (-> (sum (prod)))
        group 0
        inject 0 (prod))
      (table)
      (export 0))
    -----------double_sum-----------
    (module
      (func (-> (sum (prod) i32))
        i32.const 15
        inject 1 (prod) i32)
      (table)
      (export 0))
    -----------arith_add-----------
    (module
      (func (-> i32)
        i32.const 9
        i32.const 10
        i32.add)
      (table)
      (export 0))
    -----------arith_sub-----------
    (module
      (func (-> i32)
        i32.const 67
        i32.const 41
        i32.sub)
      (table)
      (export 0))
    -----------arith_mul-----------
    (module
      (func (-> i32)
        i32.const 42
        i32.const 10
        i32.mul)
      (table)
      (export 0))
    -----------arith_div-----------
    (module
      (func (-> i32)
        i32.const -30
        i32.const 10
        i32.div_s)
      (table)
      (export 0))
    -----------app_ident-----------
    (module
      (func ((prod) -> i32) (local ptr i32 (prod))
        local.get 0 follow
        local.set 1
        local.set 2
        local.get 1 follow
        load (Path []) move
        local.set 3
        drop
        local.get 3 move
        local.get 2 follow)
      (func (-> i32) (local ptr (prod ptr i32) ptr)
        coderef 0
        group 0
        new mm (prod)
        group 2
        pack (Type (ref (concrete mm) (prod)))
          (exists type (VALTYPE (ptr, nocopy, exdrop))
            (coderef ((prod (var 0) i32) -> i32)))
        unpack (<1> -> i32) (LocalFx [])
          local.set 0
          local.get 0 follow
          local.set 1
          local.set 2
          local.get 2 follow
          i32.const 10
          group 2
          local.get 1 follow
          call_indirect
        end)
      (table 0)
      (export 1))
    -----------nested_arith-----------
    (module
      (func (-> i32)
        i32.const 9
        i32.const 10
        i32.add
        i32.const 5
        i32.mul)
      (table)
      (export 0))
    -----------let_bind-----------
    (module
      (func (-> i32) (local i32)
        i32.const 10
        local.set 0
        local.get 0 follow)
      (table)
      (export 0))
    -----------add_one_program-----------
    (module
      (func ((prod (ref (concrete mm) (prod)) i32) -> i32)
        local.get 0 follow
        i32.const 1
        i32.add)
      (func (-> i32) (local ptr (prod ptr i32) ptr)
        coderef 0
        group 0
        new mm (prod)
        group 2
        pack (Type (prod))
          (exists type (VALTYPE (ptr, nocopy, exdrop))
            (coderef ((prod (var 0) i32) -> i32)))
        unpack (<1> -> i32) (LocalFx [])
          local.set 0
          local.get 0 follow
          local.set 1
          local.set 2
          local.get 2 follow
          i32.const 42
          group 2
          local.get 1 follow
          call_indirect
        end)
      (table 0)
      (export 0 1))
    -----------add_tup_ref-----------
    (module
      (func (-> i32) (local ptr i32 ptr i32 i32)
        i32.const 2
        new mm i32
        local.set 0
        i32.const 1
        local.get 0 follow
        group 2
        local.set 1
        local.set 2
        local.get 2 follow
        load (Path []) move
        local.set 3
        drop
        local.get 3 move
        local.set 4
        local.get 1 follow
        local.get 4 follow
        i32.add)
      (table)
      (export 0))
    -----------print_10-----------
    (module
      (import ((prod (ref (concrete mm) (prod)) i32) -> (prod))
      (func (-> (prod)) (local ptr (prod ptr i32) ptr)
        coderef 0
        group 0
        new mm (prod)
        group 2
        pack (Type (prod))
          (exists type (VALTYPE (ptr, nocopy, exdrop))
            (coderef ((prod (var 0) i32) -> (prod))))
        unpack (<1> -> (prod)) (LocalFx [])
          local.set 0
          local.get 0 follow
          local.set 1
          local.set 2
          local.get 2 follow
          i32.const 10
          group 2
          local.get 1 follow
          call_indirect
        end)
      (table)
      (export 0))
    -----------factorial_program-----------
    (module
      (func ((prod (ref (concrete mm) (prod)) i32) -> i32) (local i32 ptr
          (prod ptr i32) ptr i32)
        local.get 0 follow
        i32.const 0
        i32.eqz
        if (<1> -> i32) (LocalFx [])
          i32.const 1
        else
          local.get 0 follow
          i32.const 1
          i32.sub
          local.set 1
          coderef 0
          group 0
          new mm (prod)
          group 2
          pack (Type (prod))
            (exists type (VALTYPE (ptr, nocopy, exdrop))
              (coderef ((prod (var 0) i32) -> i32)))
          unpack (<1> -> i32) (LocalFx [])
            local.set 2
            local.get 2 follow
            local.set 3
            local.set 4
            local.get 4 follow
            local.get 4 follow
            group 2
            local.get 3 follow
            call_indirect
          end
          local.set 5
          local.get 0 follow
          local.get 5 follow
          i32.mul
        end)
      (func (-> i32) (local ptr (prod ptr i32) ptr)
        coderef 0
        group 0
        new mm (prod)
        group 2
        pack (Type (prod))
          (exists type (VALTYPE (ptr, nocopy, exdrop))
            (coderef ((prod (var 0) i32) -> i32)))
        unpack (<1> -> i32) (LocalFx [])
          local.set 0
          local.get 0 follow
          local.set 1
          local.set 2
          local.get 2 follow
          i32.const 5
          group 2
          local.get 1 follow
          call_indirect
        end)
      (table 0)
      (export 0 1))
    -----------safe_div-----------
    (module
      (func ((prod (ref (concrete mm) (prod)) (prod i32 i32)) -> (sum i32 (prod)))
          (local i32 i32 i32)
        local.get 0 follow
        local.set 1
        local.set 2
        local.get 2 follow
        i32.const 0
        i32.eqz
        if (<1> -> (sum i32 (prod))) (LocalFx [])
          group 0
          inject 1 i32 (prod)
        else
          local.get 1 follow
          local.get 2 follow
          i32.div_s
          local.set 3
          local.get 3 follow
          inject 0 i32 (prod)
        end)
      (func ((prod (ref (concrete mm) (prod)) (sum i32 (prod))) -> i32) (local i32
          (prod))
        local.get 0 follow
        case (<1> -> i32) (LocalFx [])
          (0
            local.set 1
            local.get 1 follow)
          (1
            local.set 2
            i32.const 0)
        end)
      (func (-> i32) (local ptr (prod ptr i32) ptr (sum i32 (prod)) ptr
          (prod ptr i32) ptr)
        coderef 0
        group 0
        new mm (prod)
        group 2
        pack (Type (prod))
          (exists type (VALTYPE (ptr, nocopy, exdrop))
            (coderef ((prod (var 0) (prod i32 i32)) -> (sum i32 (prod)))))
        unpack (<1> -> (sum i32 (prod))) (LocalFx [])
          local.set 0
          local.get 0 follow
          local.set 1
          local.set 2
          local.get 2 follow
          i32.const 10
          i32.const 0
          group 2
          group 2
          local.get 1 follow
          call_indirect
        end
        local.set 3
        coderef 1
        group 0
        new mm (prod)
        group 2
        pack (Type (prod))
          (exists type (VALTYPE (ptr, nocopy, exdrop))
            (coderef ((prod (var 0) (sum i32 (prod))) -> i32)))
        unpack (<1> -> i32) (LocalFx [])
          local.set 4
          local.get 4 follow
          local.set 5
          local.set 6
          local.get 6 follow
          local.get 6 follow
          group 2
          local.get 5 follow
          call_indirect
        end)
      (table 0 1)
      (export 2))
    -----------incr_n-----------
    (module
      (func
          ((prod (ref (concrete mm) (prod)) (ref (concrete mm) i32)) ->
          (ref (concrete mm) i32)) (local ptr i32 i32 ptr i32)
        local.get 0 follow
        i32.const 0
        swap (Path [])
        group 2
        local.set 1
        local.set 2
        local.get 2 follow
        i32.const 1
        i32.add
        local.set 3
        local.get 1 follow
        local.get 3 follow
        swap (Path [])
        group 2
        local.set 4
        local.set 5
        local.get 4 follow)
      (func
          ((prod (ref (concrete mm) (prod)) (prod (ref (concrete mm) i32) i32)) ->
          i32) (local ptr i32 i32 ptr (prod ptr i32) ptr ptr i32 ptr (prod ptr i32)
          ptr)
        local.get 0 follow
        local.set 1
        local.set 2
        local.get 2 follow
        i32.const 0
        i32.eqz
        if (<1> -> i32) (LocalFx [])
          local.get 1 follow
          load (Path []) move
          local.set 3
          drop
          local.get 3 move
        else
          coderef 0
          group 0
          new mm (prod)
          group 2
          pack (Type (prod))
            (exists type (VALTYPE (ptr, nocopy, exdrop))
              (coderef
                ((prod (var 0) (ref (concrete mm) i32)) -> (ref (concrete mm) i32))))
          unpack (<1> -> (ref (concrete mm) i32)) (LocalFx [])
            local.set 4
            local.get 4 follow
            local.set 5
            local.set 6
            local.get 6 follow
            local.get 5 follow
            group 2
            local.get 5 follow
            call_indirect
          end
          local.set 7
          local.get 2 follow
          i32.const 1
          i32.sub
          local.set 8
          coderef 1
          group 0
          new mm (prod)
          group 2
          pack (Type (prod))
            (exists type (VALTYPE (ptr, nocopy, exdrop))
              (coderef ((prod (var 0) (prod (ref (concrete mm) i32) i32)) -> i32)))
          unpack (<1> -> i32) (LocalFx [])
            local.set 9
            local.get 9 follow
            local.set 10
            local.set 11
            local.get 11 follow
            local.get 10 follow
            local.get 11 follow
            group 2
            group 2
            local.get 10 follow
            call_indirect
          end
        end)
      (func (-> i32) (local ptr ptr (prod ptr i32) ptr)
        i32.const 10
        new mm i32
        local.set 0
        coderef 1
        group 0
        new mm (prod)
        group 2
        pack (Type (prod))
          (exists type (VALTYPE (ptr, nocopy, exdrop))
            (coderef ((prod (var 0) (prod (ref (concrete mm) i32) i32)) -> i32)))
        unpack (<1> -> i32) (LocalFx [])
          local.set 1
          local.get 1 follow
          local.set 2
          local.set 3
          local.get 3 follow
          local.get 3 follow
          i32.const 3
          group 2
          group 2
          local.get 2 follow
          call_indirect
        end)
      (table 0 1)
      (export 1 2))
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
    FAILURE (CannotFindRep (Var (0 ("\206\177"))))
    -----------boxed_list-----------
    FAILURE (Ctx (CannotFindRep (Var (0 ())))
     (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
    -----------peano_3-----------
    (module
      (func
          (->
          (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
            (sum (prod) (ref (concrete mm) (var 0)))))
        group 0
        inject
          0 (prod) (ref (concrete mm)
                     (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                       (sum (prod) (ref (concrete mm) (var 0)))))
        fold
          (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
            (sum (prod) (ref (concrete mm) (var 0))))
        new mm
          (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
            (sum (prod) (ref (concrete mm) (var 0))))
        inject
          1 (prod) (ref (concrete mm)
                     (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                       (sum (prod) (ref (concrete mm) (var 0)))))
        fold
          (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
            (sum (prod) (ref (concrete mm) (var 0))))
        new mm
          (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
            (sum (prod) (ref (concrete mm) (var 0))))
        inject
          1 (prod) (ref (concrete mm)
                     (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                       (sum (prod) (ref (concrete mm) (var 0)))))
        fold
          (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
            (sum (prod) (ref (concrete mm) (var 0))))
        new mm
          (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
            (sum (prod) (ref (concrete mm) (var 0))))
        inject
          1 (prod) (ref (concrete mm)
                     (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                       (sum (prod) (ref (concrete mm) (var 0)))))
        fold
          (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
            (sum (prod) (ref (concrete mm) (var 0)))))
      (table)
      (export 0))
    -----------peano-----------
    (module
      (func
          ((prod (ref (concrete mm) (prod))
             (prod
               (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                 (sum (prod) (ref (concrete mm) (var 0))))
               (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                 (sum (prod) (ref (concrete mm) (var 0))))))
          ->
          (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
            (sum (prod) (ref (concrete mm) (var 0)))))
          (local (sum (prod) ptr) (sum (prod) ptr) (prod) ptr ptr (prod ptr i32)
          ptr (sum (prod) ptr))
        local.get 0 follow
        local.set 1
        local.set 2
        local.get 1 follow
        unfold
        case
          (<1> ->
          (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
            (sum (prod) (ref (concrete mm) (var 0)))))
          (LocalFx [])
          (0
            local.set 3
            local.get 2 follow)
          (1
            local.set 4
            coderef 0
            group 0
            new mm (prod)
            group 2
            pack (Type (prod))
              (exists type (VALTYPE (ptr, nocopy, exdrop))
                (coderef
                  ((prod (var 0)
                     (prod
                       (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                         (sum (prod) (ref (concrete mm) (var 0))))
                       (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                         (sum (prod) (ref (concrete mm) (var 0))))))
                  ->
                  (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                    (sum (prod) (ref (concrete mm) (var 0)))))))
            unpack
              (<1> ->
              (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                (sum (prod) (ref (concrete mm) (var 0)))))
              (LocalFx [])
              local.set 5
              local.get 5 follow
              local.set 6
              local.set 7
              local.get 7 follow
              local.get 7 follow
              load (Path []) move
              local.set 8
              drop
              local.get 8 move
              local.get 6 follow
              group 2
              group 2
              local.get 6 follow
              call_indirect
            end
            new mm
              (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                (sum (prod) (ref (concrete mm) (var 0))))
            inject
              1 (prod) (ref (concrete mm)
                         (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                           (sum (prod) (ref (concrete mm) (var 0)))))
            fold
              (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                (sum (prod) (ref (concrete mm) (var 0)))))
        end)
      (func
          ((prod (ref (concrete mm) (prod)) i32) ->
          (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
            (sum (prod) (ref (concrete mm) (var 0)))))
          (local ptr (prod ptr i32) ptr)
        local.get 0 follow
        i32.const 0
        i32.eqz
        if
          (<1> ->
          (sum (prod)
            (ref (concrete mm)
              (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                (sum (prod) (ref (concrete mm) (var 0)))))))
          (LocalFx [])
          group 0
          inject
            0 (prod) (ref (concrete mm)
                       (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                         (sum (prod) (ref (concrete mm) (var 0)))))
        else
          coderef 1
          group 0
          new mm (prod)
          group 2
          pack (Type (prod))
            (exists type (VALTYPE (ptr, nocopy, exdrop))
              (coderef
                ((prod (var 0) i32) ->
                (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                  (sum (prod) (ref (concrete mm) (var 0)))))))
          unpack
            (<1> ->
            (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
              (sum (prod) (ref (concrete mm) (var 0)))))
            (LocalFx [])
            local.set 1
            local.get 1 follow
            local.set 2
            local.set 3
            local.get 3 follow
            local.get 3 follow
            i32.const 1
            i32.sub
            group 2
            local.get 2 follow
            call_indirect
          end
          new mm
            (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
              (sum (prod) (ref (concrete mm) (var 0))))
          inject
            1 (prod) (ref (concrete mm)
                       (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                         (sum (prod) (ref (concrete mm) (var 0)))))
        end
        fold
          (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
            (sum (prod) (ref (concrete mm) (var 0)))))
      (func
          ((prod (ref (concrete mm) (prod))
             (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
               (sum (prod) (ref (concrete mm) (var 0)))))
          -> i32) (local (prod) ptr ptr (prod ptr i32) ptr (sum (prod) ptr))
        local.get 0 follow
        unfold
        case (<1> -> i32) (LocalFx [])
          (0
            local.set 1
            i32.const 0)
          (1
            local.set 2
            i32.const 1
            coderef 2
            group 0
            new mm (prod)
            group 2
            pack (Type (prod))
              (exists type (VALTYPE (ptr, nocopy, exdrop))
                (coderef
                  ((prod (var 0)
                     (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                       (sum (prod) (ref (concrete mm) (var 0)))))
                  -> i32)))
            unpack (<1> -> i32) (LocalFx [])
              local.set 3
              local.get 3 follow
              local.set 4
              local.set 5
              local.get 5 follow
              local.get 5 follow
              load (Path []) move
              local.set 6
              drop
              local.get 6 move
              group 2
              local.get 4 follow
              call_indirect
            end
            i32.add)
        end)
      (func (-> i32) (local ptr (prod ptr i32) ptr (sum (prod) ptr) ptr
          (prod ptr i32) ptr (sum (prod) ptr) ptr (prod ptr i32) ptr
          (sum (prod) ptr) ptr (prod ptr i32) ptr)
        coderef 1
        group 0
        new mm (prod)
        group 2
        pack (Type (prod))
          (exists type (VALTYPE (ptr, nocopy, exdrop))
            (coderef
              ((prod (var 0) i32) ->
              (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                (sum (prod) (ref (concrete mm) (var 0)))))))
        unpack
          (<1> ->
          (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
            (sum (prod) (ref (concrete mm) (var 0)))))
          (LocalFx [])
          local.set 0
          local.get 0 follow
          local.set 1
          local.set 2
          local.get 2 follow
          i32.const 6
          group 2
          local.get 1 follow
          call_indirect
        end
        local.set 3
        coderef 1
        group 0
        new mm (prod)
        group 2
        pack (Type (prod))
          (exists type (VALTYPE (ptr, nocopy, exdrop))
            (coderef
              ((prod (var 0) i32) ->
              (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                (sum (prod) (ref (concrete mm) (var 0)))))))
        unpack
          (<1> ->
          (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
            (sum (prod) (ref (concrete mm) (var 0)))))
          (LocalFx [])
          local.set 4
          local.get 4 follow
          local.set 5
          local.set 6
          local.get 6 follow
          i32.const 7
          group 2
          local.get 5 follow
          call_indirect
        end
        local.set 7
        coderef 0
        group 0
        new mm (prod)
        group 2
        pack (Type (prod))
          (exists type (VALTYPE (ptr, nocopy, exdrop))
            (coderef
              ((prod (var 0)
                 (prod
                   (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                     (sum (prod) (ref (concrete mm) (var 0))))
                   (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                     (sum (prod) (ref (concrete mm) (var 0))))))
              ->
              (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                (sum (prod) (ref (concrete mm) (var 0)))))))
        unpack
          (<1> ->
          (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
            (sum (prod) (ref (concrete mm) (var 0)))))
          (LocalFx [])
          local.set 8
          local.get 8 follow
          local.set 9
          local.set 10
          local.get 10 follow
          local.get 9 follow
          local.get 10 follow
          group 2
          group 2
          local.get 9 follow
          call_indirect
        end
        local.set 11
        coderef 2
        group 0
        new mm (prod)
        group 2
        pack (Type (prod))
          (exists type (VALTYPE (ptr, nocopy, exdrop))
            (coderef
              ((prod (var 0)
                 (rec (VALTYPE ((sum (prod) ptr), nocopy, exdrop))
                   (sum (prod) (ref (concrete mm) (var 0)))))
              -> i32)))
        unpack (<1> -> i32) (LocalFx [])
          local.set 12
          local.get 12 follow
          local.set 13
          local.set 14
          local.get 14 follow
          local.get 14 follow
          group 2
          local.get 13 follow
          call_indirect
        end)
      (table 0 1 2)
      (export 3))
    -----------mini_zip-----------
    (module
      (func ((prod (ref (concrete mm) (prod)) i32) -> i32)
        local.get 0 follow
        i32.const 1
        i32.add)
      (func ((prod (ref (concrete mm) (prod)) (prod i32 i32)) -> (prod i32 i32))
          (local i32 i32 ptr (prod ptr i32) ptr ptr (prod ptr i32) ptr)
        local.get 0 follow
        local.set 1
        local.set 2
        coderef 0
        group 0
        new mm (prod)
        group 2
        pack (Type (prod))
          (exists type (VALTYPE (ptr, nocopy, exdrop))
            (coderef ((prod (var 0) i32) -> i32)))
        unpack (<1> -> i32) (LocalFx [])
          local.set 3
          local.get 3 follow
          local.set 4
          local.set 5
          local.get 5 follow
          local.get 4 follow
          group 2
          local.get 4 follow
          call_indirect
        end
        coderef 0
        group 0
        new mm (prod)
        group 2
        pack (Type (prod))
          (exists type (VALTYPE (ptr, nocopy, exdrop))
            (coderef ((prod (var 0) i32) -> i32)))
        unpack (<1> -> i32) (LocalFx [])
          local.set 6
          local.get 6 follow
          local.set 7
          local.set 8
          local.get 8 follow
          local.get 8 follow
          group 2
          local.get 7 follow
          call_indirect
        end
        group 2)
      (func
          ((prod (ref (concrete mm) (prod))
             (prod (ref (concrete mm) i32)
               (ref (concrete mm) (ref (concrete mm) i32))))
          -> (ref (concrete mm) (prod i32 (ref (concrete mm) i32)))) (local ptr ptr
          i32 ptr)
        local.get 0 follow
        local.set 1
        local.set 2
        local.get 1 follow
        load (Path []) move
        local.set 3
        drop
        local.get 3 move
        local.get 2 follow
        load (Path []) move
        local.set 4
        drop
        local.get 4 move
        group 2
        new mm (prod i32 (ref (concrete mm) i32)))
      (table 0 1 2)
      (export 1)) |}]
