open! Base
open! Stdlib.Format
open! Test_support
open! Richwasm_lin_lang
open Typecheck

include Test_runner.Outputter.Make (struct
  open Test_utils

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
  let examples = Test_examples.Lin_lang.all
  let pp = IR.Module.pp
end)

let%expect_test "examples" =
  output_examples ();
  [%expect
    {|
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
    ((imports (((name print) (input Int) (output (Prod ()))))) (functions ())
     (main ((App (Coderef print (Lollipop Int (Prod ()))) (Int 10 Int) (Prod ())))))
    -----------factorial_program-----------
    ((imports ())
     (functions
      (((export true) (name factorial) (param Int) (return Int)
        (body
         (If0 (Var (0 (n)) Int) (Int 1 Int)
          (Let Int (Binop Sub (Var (0 (n)) Int) (Int 1 Int) Int)
           (Let Int
            (App (Coderef factorial (Lollipop Int Int)) (Var (0 (n-sub1)) Int) Int)
            (Binop Mul (Var (2 (n)) Int) (Var (0 (rec-res)) Int) Int) Int)
           Int)
          Int)))))
     (main ((App (Coderef factorial (Lollipop Int Int)) (Int 5 Int) Int))))
    -----------safe_div-----------
    ((imports ())
     (functions
      (((export false) (name safe_div) (param (Prod (Int Int)))
        (return (Sum (Int (Prod ()))))
        (body
         (Split (Int Int) (Var (0 (p)) (Prod (Int Int)))
          (If0 (Var (0 (y)) Int) (Inj 1 (Tuple () (Prod ())) (Sum (Int (Prod ()))))
           (Let Int (Binop Div (Var (1 (x)) Int) (Var (0 (y)) Int) Int)
            (Inj 0 (Var (0 (q)) Int) (Sum (Int (Prod ())))) (Sum (Int (Prod ()))))
           (Sum (Int (Prod ()))))
          (Sum (Int (Prod ()))))))
       ((export false) (name from_either) (param (Sum (Int (Prod ()))))
        (return Int)
        (body
         (Cases (Var (0 (e)) (Sum (Int (Prod ()))))
          ((Int (Var (0 (ok)) Int)) ((Prod ()) (Int 0 Int))) Int)))))
     (main
      ((Let (Sum (Int (Prod ())))
        (App (Coderef safe_div (Lollipop (Prod (Int Int)) (Sum (Int (Prod ())))))
         (Tuple ((Int 10 Int) (Int 0 Int)) (Prod (Int Int))) (Sum (Int (Prod ()))))
        (App (Coderef from_either (Lollipop (Sum (Int (Prod ()))) Int))
         (Var (0 (r)) (Sum (Int (Prod ())))) Int)
        Int))))
    -----------incr_n-----------
    ((imports ())
     (functions
      (((export false) (name incr_1) (param (Ref Int)) (return (Ref Int))
        (body
         (Split ((Ref Int) Int)
          (Swap (Var (0 (r)) (Ref Int)) (Int 0 Int) (Prod ((Ref Int) Int)))
          (Let Int (Binop Add (Var (0 (old)) Int) (Int 1 Int) Int)
           (Split ((Ref Int) Int)
            (Swap (Var (2 (r1)) (Ref Int)) (Var (0 (new)) Int)
             (Prod ((Ref Int) Int)))
            (Var (1 (r2)) (Ref Int)) (Ref Int))
           (Ref Int))
          (Ref Int))))
       ((export true) (name incr_n) (param (Prod ((Ref Int) Int))) (return Int)
        (body
         (Split ((Ref Int) Int) (Var (0 (p)) (Prod ((Ref Int) Int)))
          (If0 (Var (0 (n)) Int) (Free (Var (1 (r)) (Ref Int)) Int)
           (Let (Ref Int)
            (App (Coderef incr_1 (Lollipop (Ref Int) (Ref Int)))
             (Var (1 (r)) (Ref Int)) (Ref Int))
            (Let Int (Binop Sub (Var (1 (n)) Int) (Int 1 Int) Int)
             (App (Coderef incr_n (Lollipop (Prod ((Ref Int) Int)) Int))
              (Tuple ((Var (1 (r1)) (Ref Int)) (Var (0 (n1)) Int))
               (Prod ((Ref Int) Int)))
              Int)
             Int)
            Int)
           Int)
          Int)))))
     (main
      ((Let (Ref Int) (New (Int 10 Int) (Ref Int))
        (App (Coderef incr_n (Lollipop (Prod ((Ref Int) Int)) Int))
         (Tuple ((Var (0 (r0)) (Ref Int)) (Int 3 Int)) (Prod ((Ref Int) Int))) Int)
        Int))))
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
             (Var (0 (x)) (Rec (Lollipop (Var (0 (a))) (Lollipop Int Int))))
             (Lollipop (Rec (Lollipop (Var (0 (a))) (Lollipop Int Int)))
              (Lollipop Int Int)))
            (Let (Lollipop Int Int)
             (App
              (Var (0 (ux))
               (Lollipop (Rec (Lollipop (Var (0 (a))) (Lollipop Int Int)))
                (Lollipop Int Int)))
              (Var (1 (x)) (Rec (Lollipop (Var (0 (a))) (Lollipop Int Int))))
              (Lollipop Int Int))
             (App (Var (3 (f)) (Lollipop (Lollipop Int Int) (Lollipop Int Int)))
              (Var (0 (xx)) (Lollipop Int Int)) (Lollipop Int Int))
             (Lollipop Int Int))
            (Lollipop Int Int))
           (Lollipop (Rec (Lollipop (Var (0 (a))) (Lollipop Int Int)))
            (Lollipop Int Int)))
          (App
           (Var (0 (omega))
            (Lollipop (Rec (Lollipop (Var (0 (a))) (Lollipop Int Int)))
             (Lollipop Int Int)))
           (Fold (Rec (Lollipop (Var (0 (a))) (Lollipop Int Int)))
            (Var (0 (omega))
             (Lollipop (Rec (Lollipop (Var (0 (a))) (Lollipop Int Int)))
              (Lollipop Int Int)))
            (Rec (Lollipop (Var (0 (a))) (Lollipop Int Int))))
           (Lollipop Int Int))
          (Lollipop Int Int))
         (Lollipop (Lollipop (Lollipop Int Int) (Lollipop Int Int))
          (Lollipop Int Int)))
        (Let (Lollipop Int Int)
         (App
          (Var (0 (fix))
           (Lollipop (Lollipop (Lollipop Int Int) (Lollipop Int Int))
            (Lollipop Int Int)))
          (Lam (Lollipop Int Int) (Lollipop Int Int)
           (Lam Int Int
            (If0 (Var (0 (n)) Int) (Int 1 Int)
             (Let Int (Binop Sub (Var (0 (n)) Int) (Int 1 Int) Int)
              (Let Int
               (App (Var (2 (rec)) (Lollipop Int Int)) (Var (0 (n-sub1)) Int) Int)
               (Binop Mul (Var (2 (n)) Int) (Var (0 (rec-res)) Int) Int) Int)
              Int)
             Int)
            (Lollipop Int Int))
           (Lollipop (Lollipop Int Int) (Lollipop Int Int)))
          (Lollipop Int Int))
         (App (Var (0 (factorial)) (Lollipop Int Int)) (Int 5 Int) Int) Int)
        Int))))
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
          (Var (0 (p))
           (Prod
            ((Lollipop Int Int)
             (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))
          (Fold (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))
           (Cases
            (Unfold (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))
             (Var (0 (lst))
              (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
             (Sum
              ((Prod ())
               (Prod
                (Int (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))))
            (((Prod ())
              (Inj 0 (Var (0 (nil)) (Prod ()))
               (Sum
                ((Prod ())
                 (Prod
                  (Int (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))))))
             ((Prod
               (Int (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))
              (Split
               (Int (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
               (Var (0 (cons))
                (Prod
                 (Int (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))
               (Inj 1
                (Tuple
                 ((App (Var (4 (f)) (Lollipop Int Int)) (Var (1 (hd)) Int) Int)
                  (App
                   (Coderef map_int
                    (Lollipop
                     (Prod
                      ((Lollipop Int Int)
                       (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))
                     (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))
                   (Tuple
                    ((Var (4 (f)) (Lollipop Int Int))
                     (Var (0 (tl))
                      (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))
                    (Prod
                     ((Lollipop Int Int)
                      (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))
                   (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))
                 (Prod
                  (Int (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))
                (Sum
                 ((Prod ())
                  (Prod
                   (Int
                    (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))))
               (Sum
                ((Prod ())
                 (Prod
                  (Int (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))))))
            (Sum
             ((Prod ())
              (Prod
               (Int (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))))
           (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
          (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))))
     (main
      ((Let (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))
        (Fold (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))
         (Inj 0 (Tuple () (Prod ()))
          (Sum
           ((Prod ())
            (Prod
             (Int (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))))
         (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
        (App
         (Coderef map_int
          (Lollipop
           (Prod
            ((Lollipop Int Int)
             (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))
           (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))
         (Tuple
          ((Lam Int Int (Binop Add (Var (0 (x)) Int) (Int 1 Int) Int)
            (Lollipop Int Int))
           (Var (0 (lst))
            (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))
          (Prod
           ((Lollipop Int Int)
            (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))
         (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
        (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))))
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
          (Var (0 (p))
           (Prod
            ((Lollipop Int Int)
             (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))))
          (Fold (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))
           (Cases
            (Unfold
             (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))
             (Var (0 (lst))
              (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))
             (Sum
              ((Prod ())
               (Prod
                (Int
                 (Ref
                  (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))))))
            (((Prod ())
              (Inj 0 (Var (0 (nil)) (Prod ()))
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
               (Var (0 (cons))
                (Prod
                 (Int
                  (Ref
                   (Rec
                    (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))))
               (Inj 1
                (Tuple
                 ((App (Var (4 (f)) (Lollipop Int Int)) (Var (1 (hd)) Int) Int)
                  (New
                   (App
                    (Coderef map_int
                     (Lollipop
                      (Prod
                       ((Lollipop Int Int)
                        (Rec
                         (Sum
                          ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))
                      (Rec
                       (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))
                    (Tuple
                     ((Var (4 (f)) (Lollipop Int Int))
                      (Free
                       (Var (0 (tl))
                        (Ref
                         (Rec
                          (Sum
                           ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))
                       (Rec
                        (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))
                     (Prod
                      ((Lollipop Int Int)
                       (Rec
                        (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))))
                    (Rec
                     (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))
                   (Ref
                    (Rec
                     (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))))
                 (Prod
                  (Int
                   (Ref
                    (Rec
                     (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))))
                (Sum
                 ((Prod ())
                  (Prod
                   (Int
                    (Ref
                     (Rec
                      (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))))))
               (Sum
                ((Prod ())
                 (Prod
                  (Int
                   (Ref
                    (Rec
                     (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))))))))
            (Sum
             ((Prod ())
              (Prod
               (Int
                (Ref
                 (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))))))
           (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))
          (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))))))
     (main
      ((Let (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))
        (Fold (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))
         (Inj 1
          (Tuple
           ((Int 5 Int)
            (New
             (Fold
              (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))
              (Inj 0 (Tuple () (Prod ()))
               (Sum
                ((Prod ())
                 (Prod
                  (Int
                   (Ref
                    (Rec
                     (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))))))
              (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))
             (Ref
              (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))))
           (Prod
            (Int
             (Ref
              (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))))
          (Sum
           ((Prod ())
            (Prod
             (Int
              (Ref
               (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))))))
         (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))
        (App
         (Coderef map_int
          (Lollipop
           (Prod
            ((Lollipop Int Int)
             (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))
           (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))
         (Tuple
          ((Lam Int Int (Binop Add (Var (0 (x)) Int) (Int 1 Int) Int)
            (Lollipop Int Int))
           (Var (0 (lst))
            (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))
          (Prod
           ((Lollipop Int Int)
            (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))))
         (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))
        (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))))
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
                 (Inj 0 (Tuple () (Prod ()))
                  (Sum
                   ((Prod ()) (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
                 (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
                (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
               (Sum ((Prod ()) (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
              (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
             (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
            (Sum ((Prod ()) (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
           (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
          (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
         (Sum ((Prod ()) (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
        (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
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
          (Var (0 (p))
           (Prod
            ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
             (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))
          (Cases
           (Unfold (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
            (Var (1 (left)) (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
            (Sum ((Prod ()) (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
           (((Prod ())
             (Var (1 (right)) (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
            ((Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
             (Fold (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
              (Inj 1
               (New
                (App
                 (Coderef add
                  (Lollipop
                   (Prod
                    ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
                     (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
                   (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
                 (Tuple
                  ((Free
                    (Var (0 (succ))
                     (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
                    (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
                   (Var (1 (right)) (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
                  (Prod
                   ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
                    (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))
                 (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
                (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
               (Sum ((Prod ()) (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
              (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))
           (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
          (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))
       ((export false) (name from-int) (param Int)
        (return (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
        (body
         (Fold (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
          (If0 (Var (0 (int)) Int)
           (Inj 0 (Tuple () (Prod ()))
            (Sum ((Prod ()) (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
           (Inj 1
            (New
             (App
              (Coderef from-int
               (Lollipop Int (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
              (Binop Sub (Var (0 (int)) Int) (Int 1 Int) Int)
              (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
             (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
            (Sum ((Prod ()) (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
           (Sum ((Prod ()) (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
          (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))
       ((export false) (name to-int)
        (param (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))) (return Int)
        (body
         (Cases
          (Unfold (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
           (Var (0 (peano)) (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
           (Sum ((Prod ()) (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
          (((Prod ()) (Int 0 Int))
           ((Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
            (Binop Add (Int 1 Int)
             (App
              (Coderef to-int
               (Lollipop (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))) Int))
              (Free
               (Var (0 (succ)) (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
               (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
              Int)
             Int)))
          Int)))))
     (main
      ((Let (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
        (App
         (Coderef from-int
          (Lollipop Int (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
         (Int 6 Int) (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
        (Let (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
         (App
          (Coderef from-int
           (Lollipop Int (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
          (Int 7 Int) (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
         (Let (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
          (App
           (Coderef add
            (Lollipop
             (Prod
              ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
               (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
             (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
           (Tuple
            ((Var (1 (six)) (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
             (Var (0 (seven)) (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
            (Prod
             ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
              (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))
           (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
          (App
           (Coderef to-int
            (Lollipop (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))) Int))
           (Var (0 (sum)) (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))) Int)
          Int)
         Int)
        Int))))
    -----------mini_zip-----------
    ((imports ())
     (functions
      (((export false) (name add1) (param Int) (return Int)
        (body (Binop Add (Var (0 (x)) Int) (Int 1 Int) Int)))
       ((export true) (name typle_add1) (param (Prod (Int Int)))
        (return (Prod (Int Int)))
        (body
         (Split (Int Int) (Var (0 (x)) (Prod (Int Int)))
          (Tuple
           ((App (Coderef add1 (Lollipop Int Int)) (Var (1 (x1)) Int) Int)
            (App (Coderef add1 (Lollipop Int Int)) (Var (0 (x2)) Int) Int))
           (Prod (Int Int)))
          (Prod (Int Int)))))
       ((export false) (name mini_zip_specialized)
        (param (Prod ((Ref Int) (Ref (Ref Int)))))
        (return (Ref (Prod (Int (Ref Int)))))
        (body
         (Split ((Ref Int) (Ref (Ref Int)))
          (Var (0 (p)) (Prod ((Ref Int) (Ref (Ref Int)))))
          (New
           (Tuple
            ((Free (Var (1 (a)) (Ref Int)) Int)
             (Free (Var (0 (b)) (Ref (Ref Int))) (Ref Int)))
            (Prod (Int (Ref Int))))
           (Ref (Prod (Int (Ref Int)))))
          (Ref (Prod (Int (Ref Int)))))))))
     (main ())) |}]
