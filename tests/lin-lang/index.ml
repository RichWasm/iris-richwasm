open! Base
open! Stdlib.Format
open! Test_support
open! Richwasm_lin_lang
open Index

include Test_runner.Outputter.Make (struct
  open Test_utils

  type syntax = Syntax.Module.t
  type text = string
  type res = IR.Module.t

  let syntax_pipeline x =
    x |> Index.Compile.compile_module |> or_fail_pp Index.Err.pp

  let string_pipeline s = s |> Parse.from_string_exn |> syntax_pipeline
  let examples = Test_examples.Lin_lang.all
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
    -----------nested_arith-----------
    ((imports ()) (functions ())
     (main ((Binop Mul (Binop Add (Int 9) (Int 10)) (Int 5)))))
    -----------let_bind-----------
    ((imports ()) (functions ()) (main ((Let Int (Int 10) (Var (0 (x)))))))
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
    ((imports (((name print) (input Int) (output (Prod ()))))) (functions ())
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
         (Split ((Ref Int) Int) (Swap (Var (0 (r))) (Int 0))
          (Let Int (Binop Add (Var (0 (old))) (Int 1))
           (Split ((Ref Int) Int) (Swap (Var (2 (r1))) (Var (0 (new))))
            (Var (1 (r2))))))))
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
    -----------fix_factorial[invalid]-----------
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
         (App (Var (0 (factorial))) (Int 5)))))))
    -----------unboxed_list[invlaid]-----------
    ((imports ())
     (functions
      (((export false) (name map_int)
        (param
         (Prod
          ((Lollipop Int Int)
           (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))
        (return (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
        (body
         (Split
          ((Lollipop Int Int)
           (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
          (Var (0 (p)))
          (Fold (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))
           (Cases
            (Unfold (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))
             (Var (0 (lst))))
            (((Prod ())
              (Inj 0 (Var (0 (nil)))
               (Sum
                ((Prod ())
                 (Prod
                  (Int (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))))))
             ((Prod
               (Int (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))
              (Split
               (Int (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
               (Var (0 (cons)))
               (Inj 1
                (Tuple
                 ((App (Var (4 (f))) (Var (1 (hd))))
                  (App (Coderef map_int) (Tuple ((Var (4 (f))) (Var (0 (tl))))))))
                (Sum
                 ((Prod ())
                  (Prod
                   (Int
                    (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))))))))))))))
     (main
      ((Let (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))
        (Fold (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))
         (Inj 0 (Tuple ())
          (Sum
           ((Prod ())
            (Prod
             (Int (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))))))
        (App (Coderef map_int)
         (Tuple ((Lam Int Int (Binop Add (Var (0 (x))) (Int 1))) (Var (0 (lst))))))))))
    -----------boxed_list-----------
    ((imports ())
     (functions
      (((export false) (name map_int)
        (param
         (Prod
          ((Lollipop Int Int)
           (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))))
        (return (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))
        (body
         (Split
          ((Lollipop Int Int)
           (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))
          (Var (0 (p)))
          (Fold (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))
           (Cases
            (Unfold
             (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))
             (Var (0 (lst))))
            (((Prod ())
              (Inj 0 (Var (0 (nil)))
               (Sum
                ((Prod ())
                 (Prod
                  (Int
                   (Ref
                    (Rec
                     (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))))))))
             ((Prod
               (Int
                (Ref
                 (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))))
              (Split
               (Int
                (Ref
                 (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))
               (Var (0 (cons)))
               (Inj 1
                (Tuple
                 ((App (Var (4 (f))) (Var (1 (hd))))
                  (New
                   (App (Coderef map_int)
                    (Tuple ((Var (4 (f))) (Free (Var (0 (tl))))))))))
                (Sum
                 ((Prod ())
                  (Prod
                   (Int
                    (Ref
                     (Rec
                      (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))))))))))))))))
     (main
      ((Let (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))
        (Fold (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))
         (Inj 1
          (Tuple
           ((Int 5)
            (New
             (Fold
              (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))
              (Inj 0 (Tuple ())
               (Sum
                ((Prod ())
                 (Prod
                  (Int
                   (Ref
                    (Rec
                     (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))))))))))
          (Sum
           ((Prod ())
            (Prod
             (Int
              (Ref
               (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))))))))
        (App (Coderef map_int)
         (Tuple ((Lam Int Int (Binop Add (Var (0 (x))) (Int 1))) (Var (0 (lst))))))))))
    -----------peano_3-----------
    ((imports ()) (functions ())
     (main
      ((Fold (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
        (Inj 1
         (New
          (Fold (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
           (Inj 1
            (New
             (Fold (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
              (Inj 1
               (New
                (Fold (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
                 (Inj 0 (Tuple ())
                  (Sum
                   ((Prod ()) (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))))
               (Sum ((Prod ()) (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))))
            (Sum ((Prod ()) (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))))
         (Sum ((Prod ()) (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))))))
    -----------peano-----------
    ((imports ())
     (functions
      (((export false) (name add)
        (param
         (Prod
          ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
           (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))
        (return (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
        (body
         (Split
          ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
           (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
          (Var (0 (p)))
          (Cases
           (Unfold (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))) (Var (1 (left))))
           (((Prod ()) (Var (1 (right))))
            ((Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
             (Fold (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
              (Inj 1
               (New
                (App (Coderef add)
                 (Tuple ((Free (Var (0 (succ)))) (Var (1 (right)))))))
               (Sum ((Prod ()) (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))))))))))
       ((export false) (name from-int) (param Int)
        (return (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
        (body
         (Fold (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
          (If0 (Var (0 (int)))
           (Inj 0 (Tuple ())
            (Sum ((Prod ()) (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
           (Inj 1
            (New (App (Coderef from-int) (Binop Sub (Var (0 (int))) (Int 1))))
            (Sum ((Prod ()) (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))))))
       ((export false) (name to-int)
        (param (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))) (return Int)
        (body
         (Cases
          (Unfold (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))) (Var (0 (peano))))
          (((Prod ()) (Int 0))
           ((Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
            (Binop Add (Int 1) (App (Coderef to-int) (Free (Var (0 (succ)))))))))))))
     (main
      ((Let (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
        (App (Coderef from-int) (Int 6))
        (Let (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
         (App (Coderef from-int) (Int 7))
         (Let (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
          (App (Coderef add) (Tuple ((Var (1 (six))) (Var (0 (seven))))))
          (App (Coderef to-int) (Var (0 (sum))))))))))
    -----------mini_zip-----------
    ((imports ())
     (functions
      (((export false) (name add1) (param Int) (return Int)
        (body (Binop Add (Var (0 (x))) (Int 1))))
       ((export true) (name typle_add1) (param (Prod (Int Int)))
        (return (Prod (Int Int)))
        (body
         (Split (Int Int) (Var (0 (x)))
          (Tuple
           ((App (Coderef add1) (Var (1 (x1))))
            (App (Coderef add1) (Var (0 (x2)))))))))
       ((export false) (name mini_zip_specialized)
        (param (Prod ((Ref Int) (Ref (Ref Int)))))
        (return (Ref (Prod (Int (Ref Int)))))
        (body
         (Split ((Ref Int) (Ref (Ref Int))) (Var (0 (p)))
          (New (Tuple ((Free (Var (1 (a)))) (Free (Var (0 (b))))))))))))
     (main ())) |}]
