open! Base
open! Stdlib.Format
open! Richwasm_lin_lang
open Cc

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

  let string_pipeline s = s |> Parse.from_string_exn |> syntax_pipeline
  let examples = Examples.all
  let pp = IR.Module.pp
end)

let%expect_test "simple" =
  let mk = Syntax.Module.make in
  output_syntax (mk ());
  [%expect {| ((imports ()) (functions ()) (main ())) |}];

  output_syntax (mk ~main:(Lam (("x", Int), Int, Int 69)) ());
  [%expect
    {|
    ((imports ())
     (functions
      (((export false) (name lam_1) (param (Prod ((Prod ()) Int))) (return Int)
        (body
         (Split ((Prod ()) Int) (Var (0 ()))
          (Split () (Free (Var (1 ()))) (Int 69)))))))
     (main
      ((Pack (Prod ()) (Tuple ((Coderef lam_1) (New (Tuple ()))))
        (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))) |}];

  output_syntax
    (mk
       ~main:
         (Let
            ( ("y", Int),
              Int 67,
              Lam (("x", Int), Int, Binop (Add, Var "x", Var "y")) ))
       ());
  [%expect
    {|
    ((imports ())
     (functions
      (((export false) (name lam_1) (param (Prod ((Prod (Int)) Int))) (return Int)
        (body
         (Split ((Prod (Int)) Int) (Var (0 ()))
          (Split (Int) (Free (Var (1 ()))) (Binop Add (Var (0 (x))) (Var (2 (y))))))))))
     (main
      ((Let Int (Int 67)
        (Pack (Prod (Int)) (Tuple ((Coderef lam_1) (New (Tuple ((Var (0 (y))))))))
         (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))) |}];

  output_syntax
    (mk
       ~main:
         (Let
            ( ("z", Int),
              Int 420,
              Let
                ( ("y", Int),
                  Int 67,
                  Lam
                    ( ("x", Int),
                      Int,
                      Let
                        ( ("r", Int),
                          Binop (Add, Var "x", Var "y"),
                          Binop (Mul, Var "z", Var "r") ) ) ) ))
       ());
  [%expect
    {|
    ((imports ())
     (functions
      (((export false) (name lam_1) (param (Prod ((Prod (Int Int)) Int)))
        (return Int)
        (body
         (Split ((Prod (Int Int)) Int) (Var (0 ()))
          (Split (Int Int) (Free (Var (1 ())))
           (Let Int (Binop Add (Var (0 (x))) (Var (3 (y))))
            (Binop Mul (Var (3 (z))) (Var (0 (r)))))))))))
     (main
      ((Let Int (Int 420)
        (Let Int (Int 67)
         (Pack (Prod (Int Int))
          (Tuple ((Coderef lam_1) (New (Tuple ((Var (0 (y))) (Var (1 (z))))))))
          (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))) |}];
  output_syntax
    (mk
       ~main:
         (Let
            ( ("y", Int),
              Int 67,
              Lam
                ( ("x", Int),
                  Int,
                  Split
                    ( [ ("a", Int); ("b", Int) ],
                      Tuple [ Var "x"; Var "y" ],
                      Binop (Add, Var "a", Var "b") ) ) ))
       ());
  [%expect
    {|
    ((imports ())
     (functions
      (((export false) (name lam_1) (param (Prod ((Prod (Int)) Int))) (return Int)
        (body
         (Split ((Prod (Int)) Int) (Var (0 ()))
          (Split (Int) (Free (Var (1 ())))
           (Split (Int Int) (Tuple ((Var (0 (x))) (Var (2 (y)))))
            (Binop Add (Var (1 (a))) (Var (0 (b)))))))))))
     (main
      ((Let Int (Int 67)
        (Pack (Prod (Int)) (Tuple ((Coderef lam_1) (New (Tuple ((Var (0 (y))))))))
         (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))) |}];
  output_syntax
    (mk
       ~main:
         (Let
            ( ("add1", Lollipop (Int, Int)),
              Lam (("x", Int), Int, Binop (Add, Var "x", Int 1)),
              App (Var "add1", Int 10) ))
       ());
  [%expect
    {|
    ((imports ())
     (functions
      (((export false) (name lam_1) (param (Prod ((Prod ()) Int))) (return Int)
        (body
         (Split ((Prod ()) Int) (Var (0 ()))
          (Split () (Free (Var (1 ()))) (Binop Add (Var (0 (x))) (Int 1))))))))
     (main
      ((Let (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
        (Pack (Prod ()) (Tuple ((Coderef lam_1) (New (Tuple ()))))
         (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
        (Unpack (Var (0 (add1)))
         (Split ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))
          (Var (0 ())) (App (Var (1 ())) (Tuple ((Var (0 ())) (Int 10)))))
         Int))))) |}];

  (* shadow type *)
  output
    {| (fold (rec a (rec a (a + int))) (inj 1 0 : (rec a (rec a (a + int))))) |};
  [%expect
    {|
    ((imports ()) (functions ())
     (main
      ((Fold (Rec (Rec (Sum ((Var (0 (a))) Int))))
        (Inj 1 (Int 0) (Rec (Rec (Sum ((Var (0 (a))) Int))))))))) |}]

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
    ((imports ())
     (functions
      (((export false) (name lam_1) (param (Prod ((Prod ()) Int))) (return Int)
        (body
         (Split ((Prod ()) Int) (Var (0 ()))
          (Split () (Free (Var (1 ()))) (Var (0 (x)))))))))
     (main
      ((Unpack
        (Pack (Prod ()) (Tuple ((Coderef lam_1) (New (Tuple ()))))
         (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
        (Split ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ()))) (Var (0 ()))
         (App (Var (1 ())) (Tuple ((Var (0 ())) (Int 10)))))
        Int))))
    -----------nested_arith-----------
    ((imports ()) (functions ())
     (main ((Binop Mul (Binop Add (Int 9) (Int 10)) (Int 5)))))
    -----------let_bind-----------
    ((imports ()) (functions ()) (main ((Let Int (Int 10) (Var (0 (x)))))))
    -----------add_one_program-----------
    ((imports ())
     (functions
      (((export true) (name add-one) (param (Prod ((Ref (Prod ())) Int)))
        (return Int) (body (Binop Add (Var (0 (x))) (Int 1))))))
     (main
      ((Unpack
        (Pack (Prod ()) (Tuple ((Coderef add-one) (Tuple ())))
         (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
        (Split ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ()))) (Var (0 ()))
         (App (Var (1 ())) (Tuple ((Var (0 ())) (Int 42)))))
        Int))))
    -----------add_tup_ref-----------
    ((imports ()) (functions ())
     (main
      ((Let (Ref Int) (New (Int 2))
        (Split (Int (Ref Int)) (Tuple ((Int 1) (Var (0 (r)))))
         (Let Int (Free (Var (0 (x2)))) (Binop Add (Var (2 (x1))) (Var (0 (x2'))))))))))
    -----------print_10-----------
    ((imports
      (((typ (Exists (Lollipop (Prod ((Var (0 ())) Int)) (Prod ())))) (name print))))
     (functions ())
     (main
      ((Unpack
        (Pack (Prod ()) (Tuple ((Coderef print) (Tuple ())))
         (Exists (Lollipop (Prod ((Var (0 ())) Int)) (Prod ()))))
        (Split ((Lollipop (Prod ((Var (0 ())) Int)) (Prod ())) (Var (0 ())))
         (Var (0 ())) (App (Var (1 ())) (Tuple ((Var (0 ())) (Int 10)))))
        (Prod ())))))
    -----------factorial_program-----------
    ((imports ())
     (functions
      (((export true) (name factorial) (param (Prod ((Ref (Prod ())) Int)))
        (return Int)
        (body
         (If0 (Var (0 (n))) (Int 1)
          (Let Int (Binop Sub (Var (0 (n))) (Int 1))
           (Let Int
            (Unpack
             (Pack (Prod ()) (Tuple ((Coderef factorial) (Tuple ())))
              (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
             (Split ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))
              (Var (0 ()))
              (App (Var (1 ())) (Tuple ((Var (0 ())) (Var (0 (n-sub1)))))))
             Int)
            (Binop Mul (Var (2 (n))) (Var (0 (rec-res)))))))))))
     (main
      ((Unpack
        (Pack (Prod ()) (Tuple ((Coderef factorial) (Tuple ())))
         (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
        (Split ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ()))) (Var (0 ()))
         (App (Var (1 ())) (Tuple ((Var (0 ())) (Int 5)))))
        Int))))
    -----------safe_div-----------
    ((imports ())
     (functions
      (((export false) (name safe_div)
        (param (Prod ((Ref (Prod ())) (Prod (Int Int)))))
        (return (Sum (Int (Prod ()))))
        (body
         (Split (Int Int) (Var (0 (p)))
          (If0 (Var (0 (y))) (Inj 1 (Tuple ()) (Sum (Int (Prod ()))))
           (Let Int (Binop Div (Var (1 (x))) (Var (0 (y))))
            (Inj 0 (Var (0 (q))) (Sum (Int (Prod ())))))))))
       ((export false) (name from_either)
        (param (Prod ((Ref (Prod ())) (Sum (Int (Prod ())))))) (return Int)
        (body (Cases (Var (0 (e))) ((Int (Var (0 (ok)))) ((Prod ()) (Int 0))))))))
     (main
      ((Let (Sum (Int (Prod ())))
        (Unpack
         (Pack (Prod ()) (Tuple ((Coderef safe_div) (Tuple ())))
          (Exists
           (Lollipop (Prod ((Var (0 ())) (Prod (Int Int)))) (Sum (Int (Prod ()))))))
         (Split
          ((Lollipop (Prod ((Var (0 ())) (Prod (Int Int)))) (Sum (Int (Prod ()))))
           (Var (0 ())))
          (Var (0 ()))
          (App (Var (1 ())) (Tuple ((Var (0 ())) (Tuple ((Int 10) (Int 0)))))))
         (Sum (Int (Prod ()))))
        (Unpack
         (Pack (Prod ()) (Tuple ((Coderef from_either) (Tuple ())))
          (Exists (Lollipop (Prod ((Var (0 ())) (Sum (Int (Prod ()))))) Int)))
         (Split
          ((Lollipop (Prod ((Var (0 ())) (Sum (Int (Prod ()))))) Int) (Var (0 ())))
          (Var (0 ())) (App (Var (1 ())) (Tuple ((Var (0 ())) (Var (0 (r)))))))
         Int)))))
    -----------incr_n-----------
    ((imports ())
     (functions
      (((export false) (name incr_1) (param (Prod ((Ref (Prod ())) (Ref Int))))
        (return (Ref Int))
        (body
         (Split (Int (Ref Int)) (Swap (Var (0 (r))) (Int 0))
          (Let Int (Binop Add (Var (1 (old))) (Int 1))
           (Let (Prod (Int (Ref Int))) (Swap (Var (1 (r1))) (Var (0 (new))))
            (Split (Int (Ref Int)) (Var (0 (p2))) (Var (0 (r2)))))))))
       ((export true) (name incr_n)
        (param (Prod ((Ref (Prod ())) (Prod ((Ref Int) Int))))) (return Int)
        (body
         (Split ((Ref Int) Int) (Var (0 (p)))
          (If0 (Var (0 (n))) (Free (Var (1 (r))))
           (Let (Ref Int)
            (Unpack
             (Pack (Prod ()) (Tuple ((Coderef incr_1) (Tuple ())))
              (Exists (Lollipop (Prod ((Var (0 ())) (Ref Int))) (Ref Int))))
             (Split
              ((Lollipop (Prod ((Var (0 ())) (Ref Int))) (Ref Int)) (Var (0 ())))
              (Var (0 ())) (App (Var (1 ())) (Tuple ((Var (0 ())) (Var (1 (r)))))))
             (Ref Int))
            (Let Int (Binop Sub (Var (1 (n))) (Int 1))
             (Unpack
              (Pack (Prod ()) (Tuple ((Coderef incr_n) (Tuple ())))
               (Exists (Lollipop (Prod ((Var (0 ())) (Prod ((Ref Int) Int)))) Int)))
              (Split
               ((Lollipop (Prod ((Var (0 ())) (Prod ((Ref Int) Int)))) Int)
                (Var (0 ())))
               (Var (0 ()))
               (App (Var (1 ()))
                (Tuple ((Var (0 ())) (Tuple ((Var (1 (r1))) (Var (0 (n1)))))))))
              Int)))))))))
     (main
      ((Let (Ref Int) (New (Int 10))
        (Unpack
         (Pack (Prod ()) (Tuple ((Coderef incr_n) (Tuple ())))
          (Exists (Lollipop (Prod ((Var (0 ())) (Prod ((Ref Int) Int)))) Int)))
         (Split
          ((Lollipop (Prod ((Var (0 ())) (Prod ((Ref Int) Int)))) Int)
           (Var (0 ())))
          (Var (0 ()))
          (App (Var (1 ()))
           (Tuple ((Var (0 ())) (Tuple ((Var (0 (r0))) (Int 3)))))))
         Int)))))
    -----------fix_factorial-----------
    ((imports ())
     (functions
      (((export false) (name lam_2)
        (param
         (Prod
          ((Prod
            ((Exists
              (Lollipop
               (Prod
                ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
               (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))
           (Rec
            (Exists
             (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
              (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))))
        (return (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
        (body
         (Split
          ((Prod
            ((Exists
              (Lollipop
               (Prod
                ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
               (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))
           (Rec
            (Exists
             (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
              (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))
          (Var (0 ()))
          (Split
           ((Exists
             (Lollipop
              (Prod
               ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
              (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
           (Free (Var (1 ())))
           (Let
            (Exists
             (Lollipop
              (Prod
               ((Var (0 ()))
                (Rec
                 (Exists
                  (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
                   (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
              (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
            (Unfold
             (Rec
              (Exists
               (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
                (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
             (Var (0 (x))))
            (Let (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
             (Unpack (Var (0 (ux)))
              (Split
               ((Lollipop
                 (Prod
                  ((Var (0 ()))
                   (Rec
                    (Exists
                     (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
                      (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
                 (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
                (Var (0 ())))
               (Var (0 ()))
               (App (Var (1 ())) (Tuple ((Var (0 ())) (Var (1 (x)))))))
              (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
             (Unpack (Var (4 (f)))
              (Split
               ((Lollipop
                 (Prod
                  ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                 (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
                (Var (0 ())))
               (Var (0 ()))
               (App (Var (1 ())) (Tuple ((Var (0 ())) (Var (0 (xx)))))))
              (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))))
       ((export false) (name lam_1)
        (param
         (Prod
          ((Prod ())
           (Exists
            (Lollipop
             (Prod
              ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
             (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
        (return (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
        (body
         (Split
          ((Prod ())
           (Exists
            (Lollipop
             (Prod
              ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
             (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
          (Var (0 ()))
          (Split () (Free (Var (1 ())))
           (Let
            (Exists
             (Lollipop
              (Prod
               ((Var (0 ()))
                (Rec
                 (Exists
                  (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
                   (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
              (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
            (Pack
             (Prod
              ((Exists
                (Lollipop
                 (Prod
                  ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                 (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))
             (Tuple ((Coderef lam_2) (New (Tuple ((Var (0 (f))))))))
             (Exists
              (Lollipop
               (Prod
                ((Var (0 ()))
                 (Rec
                  (Exists
                   (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
                    (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
               (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
            (Unpack (Var (0 (omega)))
             (Split
              ((Lollipop
                (Prod
                 ((Var (0 ()))
                  (Rec
                   (Exists
                    (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
                     (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
                (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
               (Var (0 ())))
              (Var (0 ()))
              (App (Var (1 ()))
               (Tuple
                ((Var (0 ()))
                 (Fold
                  (Rec
                   (Exists
                    (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
                     (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
                  (Var (0 (omega))))))))
             (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))))
       ((export false) (name lam_4)
        (param
         (Prod ((Prod ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))) Int)))
        (return Int)
        (body
         (Split ((Prod ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))) Int)
          (Var (0 ()))
          (Split ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
           (Free (Var (1 ())))
           (If0 (Var (0 (n))) (Int 1)
            (Let Int (Binop Sub (Var (0 (n))) (Int 1))
             (Let Int
              (Unpack (Var (3 (rec)))
               (Split ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))
                (Var (0 ()))
                (App (Var (1 ())) (Tuple ((Var (0 ())) (Var (0 (n-sub1)))))))
               Int)
              (Binop Mul (Var (2 (n))) (Var (0 (rec-res)))))))))))
       ((export false) (name lam_3)
        (param
         (Prod ((Prod ()) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
        (return (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
        (body
         (Split ((Prod ()) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
          (Var (0 ()))
          (Split () (Free (Var (1 ())))
           (Pack (Prod ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
            (Tuple ((Coderef lam_4) (New (Tuple ((Var (0 (rec))))))))
            (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))))
     (main
      ((Let
        (Exists
         (Lollipop
          (Prod
           ((Var (0 ()))
            (Exists
             (Lollipop
              (Prod
               ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
              (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))
          (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
        (Pack (Prod ()) (Tuple ((Coderef lam_1) (New (Tuple ()))))
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
        (Let (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
         (Unpack (Var (0 (fix)))
          (Split
           ((Lollipop
             (Prod
              ((Var (0 ()))
               (Exists
                (Lollipop
                 (Prod
                  ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                 (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))
             (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
            (Var (0 ())))
           (Var (0 ()))
           (App (Var (1 ()))
            (Tuple
             ((Var (0 ()))
              (Pack (Prod ()) (Tuple ((Coderef lam_3) (New (Tuple ()))))
               (Exists
                (Lollipop
                 (Prod
                  ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                 (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))))
          (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
         (Unpack (Var (0 (factorial)))
          (Split ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))
           (Var (0 ())) (App (Var (1 ())) (Tuple ((Var (0 ())) (Int 5)))))
          Int)))))) |}]
