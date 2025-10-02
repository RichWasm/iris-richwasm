open! Base
open! Stdlib.Format
open! Richwasm_lin_lang
open Index

include Help.Outputter.Make (struct
  open Help

  type syntax = Syntax.Module.t
  type text = string
  type res = IR.Module.t

  let syntax_pipeline x =
    x |> Index.Compile.compile_module |> or_fail_pp Index.Err.pp

  let string_pipeline s = s |> Parse.from_string_exn |> syntax_pipeline
  let examples = Examples.all
  let pp = IR.Module.pp
end)

let%expect_test "basic indexing" =
  let mk = Syntax.Module.make in
  output_syntax (mk ~main:(Let (("a", Int), Int 10, Var "a")) ());
  [%expect
    {|
      ((imports ()) (functions ()) (main ((Let Int (Int 10) (Var (0 (a))))))) |}];

  output_syntax
    (mk
       ~functions:
         [
           {
             export = true;
             name = "foo";
             param = ("x", Int);
             return = Int;
             body = Int 10;
           };
         ]
       ());
  [%expect
    {|
      ((imports ())
       (functions
        (((export true) (name foo) (param Int) (return Int) (body (Int 10)))))
       (main ())) |}]

let%expect_test "examples" =
  output_examples ();
  [%expect
    {|
    -----------one-----------
    ((imports ()) (functions ()) (main ((Int 1))))
    -----------flat_tuple-----------
    ((imports ()) (functions ())
     (main ((Tuple ((Int 1) (Int 2) (Int 3) (Int 4))))))
    -----------nested_tuple-----------
    ((imports ()) (functions ())
     (main ((Tuple ((Tuple ((Int 1) (Int 2))) (Tuple ((Int 3) (Int 4))))))))
    -----------single_sum-----------
    ((imports ()) (functions ()) (main ((Inj 0 (Tuple ()) (Sum ((Prod ())))))))
    -----------double_sum-----------
    ((imports ()) (functions ()) (main ((Inj 1 (Int 15) (Sum ((Prod ()) Int))))))
    -----------arith_add-----------
    ((imports ()) (functions ()) (main ((Binop Add (Int 9) (Int 10)))))
    -----------arith_sub-----------
    ((imports ()) (functions ()) (main ((Binop Sub (Int 67) (Int 41)))))
    -----------arith_mul-----------
    ((imports ()) (functions ()) (main ((Binop Mul (Int 42) (Int 10)))))
    -----------arith_div-----------
    ((imports ()) (functions ()) (main ((Binop Div (Int -30) (Int 10)))))
    -----------app_ident-----------
    ((imports ()) (functions ())
     (main ((App (Lam Int Int (Var (0 (x)))) (Int 10)))))
    -----------add_one_program-----------
    ((imports ())
     (functions
      (((export true) (name add-one) (param Int) (return Int)
        (body (Binop Add (Var (0 (x))) (Int 1))))))
     (main ((App (Coderef add-one) (Int 42)))))
    -----------add_tup_ref-----------
    ((imports ()) (functions ())
     (main
      ((Let (Ref Int) (New (Int 2))
        (Split (Int (Ref Int)) (Tuple ((Int 1) (Var (0 (r)))))
         (Let Int (Free (Var (0 (x2)))) (Binop Add (Var (2 (x1))) (Var (0 (x2'))))))))))
    -----------print_10-----------
    ((imports (((typ (Lollipop Int (Prod ()))) (name print)))) (functions ())
     (main ((App (Coderef print) (Int 10)))))
    -----------factorial_program-----------
    ((imports ())
     (functions
      (((export true) (name factorial) (param Int) (return Int)
        (body
         (If0 (Var (0 (n))) (Int 1)
          (Let Int (Binop Sub (Var (0 (n))) (Int 1))
           (Let Int (App (Coderef factorial) (Var (0 (n-sub1))))
            (Binop Mul (Var (2 (n))) (Var (0 (rec-res)))))))))))
     (main ((App (Coderef factorial) (Int 5)))))
    -----------safe_div-----------
    ((imports ())
     (functions
      (((export false) (name safe_div) (param (Prod (Int Int)))
        (return (Sum (Int (Prod ()))))
        (body
         (Split (Int Int) (Var (0 (p)))
          (If0 (Var (0 (y))) (Inj 1 (Tuple ()) (Sum (Int (Prod ()))))
           (Let Int (Binop Div (Var (1 (x))) (Var (0 (y))))
            (Inj 0 (Var (0 (q))) (Sum (Int (Prod ())))))))))
       ((export false) (name from_either) (param (Sum (Int (Prod ()))))
        (return Int)
        (body (Cases (Var (0 (e))) ((Int (Var (0 (ok)))) ((Prod ()) (Int 0))))))))
     (main
      ((Let (Sum (Int (Prod ())))
        (App (Coderef safe_div) (Tuple ((Int 10) (Int 0))))
        (App (Coderef from_either) (Var (0 (r))))))))
    -----------incr_n-----------
    ((imports ())
     (functions
      (((export false) (name incr_1) (param (Ref Int)) (return (Ref Int))
        (body
         (Split (Int (Ref Int)) (Swap (Var (0 (r))) (Int 0))
          (Let Int (Binop Add (Var (1 (old))) (Int 1))
           (Let (Prod (Int (Ref Int))) (Swap (Var (1 (r1))) (Var (0 (new))))
            (Split (Int (Ref Int)) (Var (0 (p2))) (Var (0 (r2)))))))))
       ((export true) (name incr_n) (param (Prod ((Ref Int) Int))) (return Int)
        (body
         (Split ((Ref Int) Int) (Var (0 (p)))
          (If0 (Var (0 (n))) (Free (Var (1 (r))))
           (Let (Ref Int) (App (Coderef incr_1) (Var (1 (r))))
            (Let Int (Binop Sub (Var (1 (n))) (Int 1))
             (App (Coderef incr_n) (Tuple ((Var (1 (r1))) (Var (0 (n1))))))))))))))
     (main
      ((Let (Ref Int) (New (Int 10))
        (App (Coderef incr_n) (Tuple ((Var (0 (r0))) (Int 3))))))))
    -----------fix_factorial-----------
    ((imports ()) (functions ())
     (main
      ((Let
        (Lollipop (Lollipop (Lollipop Int Int) (Lollipop Int Int))
         (Lollipop Int Int))
        (Lam (Lollipop (Lollipop Int Int) (Lollipop Int Int)) (Lollipop Int Int)
         (Let
          (Lollipop (Rec (Lollipop (Var (0 (a))) (Lollipop Int Int)))
           (Lollipop Int Int))
          (Lam (Rec (Lollipop (Var (0 (a))) (Lollipop Int Int))) (Lollipop Int Int)
           (Let
            (Lollipop (Rec (Lollipop (Var (0 (a))) (Lollipop Int Int)))
             (Lollipop Int Int))
            (Unfold (Rec (Lollipop (Var (0 (a))) (Lollipop Int Int)))
             (Var (0 (x))))
            (Let (Lollipop Int Int) (App (Var (0 (ux))) (Var (1 (x))))
             (App (Var (3 (f))) (Var (0 (xx)))))))
          (App (Var (0 (omega)))
           (Fold (Rec (Lollipop (Var (0 (a))) (Lollipop Int Int)))
            (Var (0 (omega)))))))
        (Let (Lollipop Int Int)
         (App (Var (0 (fix)))
          (Lam (Lollipop Int Int) (Lollipop Int Int)
           (Lam Int Int
            (If0 (Var (0 (n))) (Int 1)
             (Let Int (Binop Sub (Var (0 (n))) (Int 1))
              (Let Int (App (Var (2 (rec))) (Var (0 (n-sub1))))
               (Binop Mul (Var (2 (n))) (Var (0 (rec-res))))))))))
         (App (Var (0 (factorial))) (Int 5))))))) |}]
