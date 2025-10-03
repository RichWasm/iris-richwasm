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
    |> Typecheck.Compile.compile_module
    |> or_fail_pp Typecheck.Err.pp

  let string_pipeline s = s |> Parse.from_string_exn |> syntax_pipeline
  let examples = Examples.all
  let pp = IR.Module.pp
end)

let%expect_test "examples" =
  output_examples ();
  [%expect{|
    -----------one-----------
    ((imports ()) (functions ()) (main ((Int 1 Int))))
    -----------flat_tuple-----------
    ((imports ()) (functions ())
     (main
      ((Tuple ((Int 1 Int) (Int 2 Int) (Int 3 Int) (Int 4 Int))
        (Prod (Int Int Int Int))))))
    -----------nested_tuple-----------
    ((imports ()) (functions ())
     (main
      ((Tuple
        ((Tuple ((Int 1 Int) (Int 2 Int)) (Prod (Int Int)))
         (Tuple ((Int 3 Int) (Int 4 Int)) (Prod (Int Int))))
        (Prod ((Prod (Int Int)) (Prod (Int Int))))))))
    -----------single_sum-----------
    ((imports ()) (functions ())
     (main ((Inj 0 (Tuple () (Prod ())) (Sum ((Prod ())))))))
    -----------double_sum-----------
    ((imports ()) (functions ())
     (main ((Inj 1 (Int 15 Int) (Sum ((Prod ()) Int))))))
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
    ((imports ()) (functions ())
     (main
      ((App (Lam Int Int (Var (0 (x)) Int) (Lollipop Int Int)) (Int 10 Int) Int))))
    -----------nested_arith-----------
    ((imports ()) (functions ())
     (main ((Binop Mul (Binop Add (Int 9 Int) (Int 10 Int) Int) (Int 5 Int) Int))))
    -----------let_bind-----------
    ((imports ()) (functions ())
     (main ((Let Int (Int 10 Int) (Var (0 (x)) Int) Int))))
    -----------add_one_program-----------
    ((imports ())
     (functions
      (((export true) (name add-one) (param Int) (return Int)
        (body (Binop Add (Var (0 (x)) Int) (Int 1 Int) Int)))))
     (main ((App (Coderef add-one (Lollipop Int Int)) (Int 42 Int) Int))))
    -----------add_tup_ref-----------
    ((imports ()) (functions ())
     (main
      ((Let (Ref Int) (New (Int 2 Int) (Ref Int))
        (Split (Int (Ref Int))
         (Tuple ((Int 1 Int) (Var (0 (r)) (Ref Int))) (Prod (Int (Ref Int))))
         (Let Int (Free (Var (0 (x2)) (Ref Int)) Int)
          (Binop Add (Var (2 (x1)) Int) (Var (0 (x2')) Int) Int) Int)
         Int)
        Int))))
    -----------print_10-----------
    FAILURE (MissingGlobalEnv print ((locals ()) (fns ())))
    -----------factorial_program-----------
    FAILURE TODO
    -----------safe_div-----------
    FAILURE TODO
    -----------incr_n-----------
    FAILURE TODO
    -----------fix_factorial-----------
    FAILURE TODO |}]
