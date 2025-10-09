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
      (func -> i32
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
      (func -> (prod i32 i32 i32 i32)
        i32.const 1
        i32.const 2
        i32.const 3
        i32.const 4
        seq.group 4)
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
      (func -> (prod (prod i32 (prod i32 i32) i32 i32) (prod i32 i32))
        i32.const 1
        i32.const 2
        i32.const 3
        seq.group 2
        i32.const 4
        i32.const 5
        seq.group 4
        i32.const 6
        i32.const 7
        seq.group 2
        seq.group 2)
      (table)
      0) |}];

  run {| (new 10) |};
  [%expect
    {|
    (module
      (func -> (ref mm i32)
        i32.const 10
        ref.new mm i32)
      (table)
      0) |}];

  run {| (1 + 2) |};
  [%expect
    {|
    (module
      (func -> i32
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
      (func -> i32
        i32.const 1)
      (table)
      0)
    -----------flat_tuple-----------
    (module
      (func -> (prod i32 i32 i32 i32)
        i32.const 1
        i32.const 2
        i32.const 3
        i32.const 4
        seq.group 4)
      (table)
      0)
    -----------nested_tuple-----------
    (module
      (func -> (prod (prod i32 i32) (prod i32 i32))
        i32.const 1
        i32.const 2
        seq.group 2
        i32.const 3
        i32.const 4
        seq.group 2
        seq.group 2)
      (table)
      0)
    -----------single_sum-----------
    (module
      (func -> (sum (prod))
        seq.group 0
        (Inject (0, [(prod)])))
      (table)
      0)
    -----------double_sum-----------
    (module
      (func -> (sum (prod) i32)
        i32.const 15
        (Inject (1, [(prod); i32])))
      (table)
      0)
    -----------arith_add-----------
    (module
      (func -> i32
        i32.const 9
        i32.const 10
        i32.add)
      (table)
      0)
    -----------arith_sub-----------
    (module
      (func -> i32
        i32.const 67
        i32.const 41
        i32.sub)
      (table)
      0)
    -----------arith_mul-----------
    (module
      (func -> i32
        i32.const 42
        i32.const 10
        i32.mul)
      (table)
      0)
    -----------arith_div-----------
    (module
      (func -> i32
        i32.const -30
        i32.const 10
        i32.div_s)
      (table)
      0)
    -----------app_ident-----------
    FAILURE (CannotFindRep (Var (0 ())))
    -----------nested_arith-----------
    (module
      (func -> i32
        i32.const 9
        i32.const 10
        i32.add
        i32.const 5
        i32.mul)
      (table)
      0)
    -----------let_bind-----------
    (module
      (func -> i32(local (Prim I32)
        i32.const 10
        local.set 0
        local.get 0)
      (table)
      0)
    -----------add_one_program-----------
    FAILURE (CannotFindRep (Var (0 ())))
    -----------add_tup_ref-----------
    (module
      (func -> i32(local (Prim Ptr) (Prim I32) (Prim Ptr) (Prim I32) (Prim I32)
        i32.const 2
        ref.new mm i32
        local.set 0
        i32.const 1
        local.get 0
        seq.group 2
        local.set 1
        local.set 2
        local.get 2
        ref.store (Path [])
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
    FAILURE (CannotFindRep (Var (0 ())))
    -----------factorial_program-----------
    FAILURE (CannotFindRep (Var (0 ())))
    -----------safe_div-----------
    FAILURE (CannotFindRep (Var (0 ())))
    -----------incr_n-----------
    FAILURE (CannotFindRep (Var (0 ())))
    -----------fix_factorial-----------
    FAILURE (CannotFindRep (Var (0 ())))
    -----------unboxed_list-----------
    FAILURE (CannotFindRep (Var (0 ("\206\177")))) |}]
