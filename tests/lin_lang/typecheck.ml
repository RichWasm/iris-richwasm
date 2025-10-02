open! Base
open! Stdlib.Format
open! Richwasm_lin_lang
open Typecheck

include Help.Outputter.Make (struct
  open Help

  type syntax = Syntax.Module.t
  type text = string
  type res = IR.Module.t

  let syntax_pipeline x =
    x
    |> Index.Compile.compile_module
    |> or_fail_pp Index.Err.pp
    |> Cc.Compile.compile_module
    |> or_fail_pp Cc.Compile.Err.pp
    |> Typecheck.Compile.compile_module
    |> or_fail_pp Typecheck.Err.pp

  let string_pipeline s = s |> Parse.from_string_exn |> syntax_pipeline
  let examples = Examples.all
  let pp = IR.Module.pp
end)

let%expect_test "examples" =
  output_examples ();
  [%expect
    {|
    -----------one-----------
    ((imports ()) (functions ()) (main ((Val (Int 1 Int) Int))))
    -----------flat_tuple-----------
    ((imports ()) (functions ())
     (main
      ((Val
        (Tuple ((Int 1 Int) (Int 2 Int) (Int 3 Int) (Int 4 Int))
         (Prod (Int Int Int Int)))
        (Prod (Int Int Int Int))))))
    -----------nested_tuple-----------
    ((imports ()) (functions ())
     (main
      ((Val
        (Tuple
         ((Tuple ((Int 1 Int) (Int 2 Int)) (Prod (Int Int)))
          (Tuple ((Int 3 Int) (Int 4 Int)) (Prod (Int Int))))
         (Prod ((Prod (Int Int)) (Prod (Int Int)))))
        (Prod ((Prod (Int Int)) (Prod (Int Int))))))))
    -----------single_sum-----------
    ((imports ()) (functions ())
     (main
      ((Val (Inj 0 (Tuple () (Prod ())) (Sum ((Prod ())))) (Sum ((Prod ())))))))
    -----------double_sum-----------
    ((imports ()) (functions ())
     (main
      ((Val (Inj 1 (Int 15 Int) (Sum ((Prod ()) Int))) (Sum ((Prod ()) Int))))))
    -----------arith_add-----------
    ((imports ()) (functions ()) (main ((Binop Add (Int 9 Int) (Int 10 Int) Int))))
    -----------arith_sub-----------
    ((imports ()) (functions ())
     (main ((Binop Sub (Int 67 Int) (Int 41 Int) Int))))
    -----------arith_mul-----------
    ((imports ()) (functions ())
     (main ((Binop Mul (Int 42 Int) (Int 10 Int) Int))))
    -----------arith_div-----------
    ((imports ()) (functions ())
     (main ((Binop Div (Int -30 Int) (Int 10 Int) Int))))
    -----------app_ident-----------
    FAILURE TODO
    -----------add_one_program-----------
    FAILURE (Mismatch Binop ((expected Int) (actual (Prod ((Ref (Prod ())) Int)))))
    -----------add_tup_ref-----------
    FAILURE TODO
    -----------print_10-----------
    FAILURE TODO
    -----------factorial_program-----------
    FAILURE TODO
    -----------safe_div-----------
    FAILURE (Mismatch (SplitBind 0) ((expected Int) (actual (Ref (Prod ())))))
    -----------incr_n-----------
    FAILURE TODO
    -----------fix_factorial-----------
    FAILURE TODO |}]
