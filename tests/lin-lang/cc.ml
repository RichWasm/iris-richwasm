open! Base
open! Stdlib.Format
open! Test_support
open! Richwasm_lin_lang
open Cc

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
    |> Cc.Compile.compile_module
    |> or_fail_pp Cc.Compile.Err.pp

  let string_pipeline s = s |> Parse.from_string_exn |> syntax_pipeline
  let examples = Test_examples.Lin_lang.all
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
      (((export false) (name lam_1) (param (Prod ())) (return Int)
        (body
         (Split ((Ref (Prod ())) Int) (Var (0 ()) (Prod ((Ref (Prod ())) Int)))
          (Split () (Free (Var (1 ()) (Ref (Prod ()))) (Prod ())) (Int 69 Int) Int)
          Int)))))
     (main
      ((Pack (Ref (Prod ()))
        (Tuple
         ((Coderef lam_1 (Lollipop (Prod ()) Int))
          (New (Tuple () (Prod ())) (Ref (Prod ()))))
         (Prod ((Lollipop (Prod ()) Int) (Ref (Prod ())))))
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
      (((export false) (name lam_1) (param (Prod (Int))) (return Int)
        (body
         (Split ((Ref (Prod (Int))) Int)
          (Var (0 ()) (Prod ((Ref (Prod (Int))) Int)))
          (Split (Int) (Free (Var (1 ()) (Ref (Prod (Int)))) (Prod (Int)))
           (Binop Add (Var (0 (x)) Int) (Var (2 (y)) Int) Int) Int)
          Int)))))
     (main
      ((Let Int (Int 67 Int)
        (Pack (Ref (Prod (Int)))
         (Tuple
          ((Coderef lam_1 (Lollipop (Prod (Int)) Int))
           (New (Tuple ((Var (0 (y)) Int)) (Prod (Int))) (Ref (Prod (Int)))))
          (Prod ((Lollipop (Prod (Int)) Int) (Ref (Prod (Int))))))
         (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
        (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))) |}];

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
      (((export false) (name lam_1) (param (Prod (Int Int))) (return Int)
        (body
         (Split ((Ref (Prod (Int Int))) Int)
          (Var (0 ()) (Prod ((Ref (Prod (Int Int))) Int)))
          (Split (Int Int)
           (Free (Var (1 ()) (Ref (Prod (Int Int)))) (Prod (Int Int)))
           (Let Int (Binop Add (Var (0 (x)) Int) (Var (3 (y)) Int) Int)
            (Binop Mul (Var (3 (z)) Int) (Var (0 (r)) Int) Int) Int)
           Int)
          Int)))))
     (main
      ((Let Int (Int 420 Int)
        (Let Int (Int 67 Int)
         (Pack (Ref (Prod (Int Int)))
          (Tuple
           ((Coderef lam_1 (Lollipop (Prod (Int Int)) Int))
            (New (Tuple ((Var (0 (y)) Int) (Var (1 (z)) Int)) (Prod (Int Int)))
             (Ref (Prod (Int Int)))))
           (Prod ((Lollipop (Prod (Int Int)) Int) (Ref (Prod (Int Int))))))
          (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
         (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
        (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))) |}];
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
      (((export false) (name lam_1) (param (Prod (Int))) (return Int)
        (body
         (Split ((Ref (Prod (Int))) Int)
          (Var (0 ()) (Prod ((Ref (Prod (Int))) Int)))
          (Split (Int) (Free (Var (1 ()) (Ref (Prod (Int)))) (Prod (Int)))
           (Split (Int Int)
            (Tuple ((Var (0 (x)) Int) (Var (2 (y)) Int)) (Prod (Int Int)))
            (Binop Add (Var (1 (a)) Int) (Var (0 (b)) Int) Int) Int)
           Int)
          Int)))))
     (main
      ((Let Int (Int 67 Int)
        (Pack (Ref (Prod (Int)))
         (Tuple
          ((Coderef lam_1 (Lollipop (Prod (Int)) Int))
           (New (Tuple ((Var (0 (y)) Int)) (Prod (Int))) (Ref (Prod (Int)))))
          (Prod ((Lollipop (Prod (Int)) Int) (Ref (Prod (Int))))))
         (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
        (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))) |}];
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
      (((export false) (name lam_1) (param (Prod ())) (return Int)
        (body
         (Split ((Ref (Prod ())) Int) (Var (0 ()) (Prod ((Ref (Prod ())) Int)))
          (Split () (Free (Var (1 ()) (Ref (Prod ()))) (Prod ()))
           (Binop Add (Var (0 (x)) Int) (Int 1 Int) Int) Int)
          Int)))))
     (main
      ((Let (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
        (Pack (Ref (Prod ()))
         (Tuple
          ((Coderef lam_1 (Lollipop (Prod ()) Int))
           (New (Tuple () (Prod ())) (Ref (Prod ()))))
          (Prod ((Lollipop (Prod ()) Int) (Ref (Prod ())))))
         (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
        (Unpack (Var (0 (add1)) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
         (Split ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))
          (Var (0 ())
           (Prod ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))))
          (App (Var (1 ()) (Lollipop (Prod ((Var (0 ())) Int)) Int))
           (Tuple ((Var (0 ()) (Var (0 ()))) (Int 10 Int))
            (Prod ((Var (0 ())) Int)))
           Int)
          Int)
         Int)
        Int)))) |}];

  (* shadow type *)
  output
    {| (fold (rec a (rec a (a + int))) (inj 1 0 : (rec a (rec a (a + int))))) |};
  [%expect {| FAILURE (InjInvalidAnn (Rec (Rec (Sum ((Var (0 (a))) Int))))) |}]

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
    ((imports ())
     (functions
      (((export false) (name lam_1) (param (Prod ())) (return Int)
        (body
         (Split ((Ref (Prod ())) Int) (Var (0 ()) (Prod ((Ref (Prod ())) Int)))
          (Split () (Free (Var (1 ()) (Ref (Prod ()))) (Prod ())) (Var (0 (x)) Int)
           Int)
          Int)))))
     (main
      ((Unpack
        (Pack (Ref (Prod ()))
         (Tuple
          ((Coderef lam_1 (Lollipop (Prod ()) Int))
           (New (Tuple () (Prod ())) (Ref (Prod ()))))
          (Prod ((Lollipop (Prod ()) Int) (Ref (Prod ())))))
         (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
        (Split ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))
         (Var (0 ())
          (Prod ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))))
         (App (Var (1 ()) (Lollipop (Prod ((Var (0 ())) Int)) Int))
          (Tuple ((Var (0 ()) (Var (0 ()))) (Int 10 Int))
           (Prod ((Var (0 ())) Int)))
          Int)
         Int)
        Int))))
    -----------nested_arith-----------
    ((imports ()) (functions ())
     (main ((Binop Mul (Binop Add (Int 9 Int) (Int 10 Int) Int) (Int 5 Int) Int))))
    -----------let_bind-----------
    ((imports ()) (functions ())
     (main ((Let Int (Int 10 Int) (Var (0 (x)) Int) Int))))
    -----------add_one_program-----------
    ((imports ())
     (functions
      (((export true) (name add-one) (param (Prod ((Ref (Prod ())) Int)))
        (return Int)
        (body
         (Split ((Ref (Prod ())) Int) (Var (0 ()) (Prod ((Ref (Prod ())) Int)))
          (Binop Add (Var (0 (x)) Int) (Int 1 Int) Int) Int)))))
     (main
      ((Unpack
        (Pack (Prod ())
         (Tuple
          ((Coderef add-one (Lollipop Int Int))
           (New (Tuple () (Prod ())) (Ref (Prod ()))))
          (Prod ((Lollipop Int Int) (Ref (Prod ())))))
         (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
        (Split ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))
         (Var (0 ())
          (Prod ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))))
         (App (Var (1 ()) (Lollipop (Prod ((Var (0 ())) Int)) Int))
          (Tuple ((Var (0 ()) (Var (0 ()))) (Int 42 Int))
           (Prod ((Var (0 ())) Int)))
          Int)
         Int)
        Int))))
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
    ((imports
      (((name print) (input (Prod ((Ref (Prod ())) Int))) (output (Prod ())))))
     (functions ())
     (main
      ((Unpack
        (Pack (Prod ())
         (Tuple
          ((Coderef print (Lollipop Int (Prod ())))
           (New (Tuple () (Prod ())) (Ref (Prod ()))))
          (Prod ((Lollipop Int (Prod ())) (Ref (Prod ())))))
         (Exists (Lollipop (Prod ((Var (0 ())) Int)) (Prod ()))))
        (Split ((Lollipop (Prod ((Var (0 ())) Int)) (Prod ())) (Var (0 ())))
         (Var (0 ())
          (Prod ((Lollipop (Prod ((Var (0 ())) Int)) (Prod ())) (Var (0 ())))))
         (App (Var (1 ()) (Lollipop (Prod ((Var (0 ())) Int)) (Prod ())))
          (Tuple ((Var (0 ()) (Var (0 ()))) (Int 10 Int))
           (Prod ((Var (0 ())) Int)))
          (Prod ()))
         (Prod ()))
        (Prod ())))))
    -----------factorial_program-----------
    ((imports ())
     (functions
      (((export true) (name factorial) (param (Prod ((Ref (Prod ())) Int)))
        (return Int)
        (body
         (Split ((Ref (Prod ())) Int) (Var (0 ()) (Prod ((Ref (Prod ())) Int)))
          (If0 (Var (0 (n)) Int) (Int 1 Int)
           (Let Int (Binop Sub (Var (0 (n)) Int) (Int 1 Int) Int)
            (Let Int
             (Unpack
              (Pack (Prod ())
               (Tuple
                ((Coderef factorial (Lollipop Int Int))
                 (New (Tuple () (Prod ())) (Ref (Prod ()))))
                (Prod ((Lollipop Int Int) (Ref (Prod ())))))
               (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
              (Split ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))
               (Var (0 ())
                (Prod ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))))
               (App (Var (1 ()) (Lollipop (Prod ((Var (0 ())) Int)) Int))
                (Tuple ((Var (0 ()) (Var (0 ()))) (Var (0 (n-sub1)) Int))
                 (Prod ((Var (0 ())) Int)))
                Int)
               Int)
              Int)
             (Binop Mul (Var (2 (n)) Int) (Var (0 (rec-res)) Int) Int) Int)
            Int)
           Int)
          Int)))))
     (main
      ((Unpack
        (Pack (Prod ())
         (Tuple
          ((Coderef factorial (Lollipop Int Int))
           (New (Tuple () (Prod ())) (Ref (Prod ()))))
          (Prod ((Lollipop Int Int) (Ref (Prod ())))))
         (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
        (Split ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))
         (Var (0 ())
          (Prod ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))))
         (App (Var (1 ()) (Lollipop (Prod ((Var (0 ())) Int)) Int))
          (Tuple ((Var (0 ()) (Var (0 ()))) (Int 5 Int)) (Prod ((Var (0 ())) Int)))
          Int)
         Int)
        Int))))
    -----------safe_div-----------
    ((imports ())
     (functions
      (((export false) (name safe_div)
        (param (Prod ((Ref (Prod ())) (Prod (Int Int)))))
        (return (Sum (Int (Prod ()))))
        (body
         (Split ((Ref (Prod ())) (Prod (Int Int)))
          (Var (0 ()) (Prod ((Ref (Prod ())) (Prod (Int Int)))))
          (Split (Int Int) (Var (0 (p)) (Prod (Int Int)))
           (If0 (Var (0 (y)) Int)
            (Inj 1 (Tuple () (Prod ())) (Sum (Int (Prod ()))))
            (Let Int (Binop Div (Var (1 (x)) Int) (Var (0 (y)) Int) Int)
             (Inj 0 (Var (0 (q)) Int) (Sum (Int (Prod ())))) (Sum (Int (Prod ()))))
            (Sum (Int (Prod ()))))
           (Sum (Int (Prod ()))))
          (Sum (Int (Prod ()))))))
       ((export false) (name from_either)
        (param (Prod ((Ref (Prod ())) (Sum (Int (Prod ())))))) (return Int)
        (body
         (Split ((Ref (Prod ())) (Sum (Int (Prod ()))))
          (Var (0 ()) (Prod ((Ref (Prod ())) (Sum (Int (Prod ()))))))
          (Cases (Var (0 (e)) (Sum (Int (Prod ()))))
           ((Int (Var (0 (ok)) Int)) ((Prod ()) (Int 0 Int))) Int)
          Int)))))
     (main
      ((Let (Sum (Int (Prod ())))
        (Unpack
         (Pack (Prod ())
          (Tuple
           ((Coderef safe_div (Lollipop (Prod (Int Int)) (Sum (Int (Prod ())))))
            (New (Tuple () (Prod ())) (Ref (Prod ()))))
           (Prod
            ((Lollipop (Prod (Int Int)) (Sum (Int (Prod ())))) (Ref (Prod ())))))
          (Exists
           (Lollipop (Prod ((Var (0 ())) (Prod (Int Int)))) (Sum (Int (Prod ()))))))
         (Split
          ((Lollipop (Prod ((Var (0 ())) (Prod (Int Int)))) (Sum (Int (Prod ()))))
           (Var (0 ())))
          (Var (0 ())
           (Prod
            ((Lollipop (Prod ((Var (0 ())) (Prod (Int Int))))
              (Sum (Int (Prod ()))))
             (Var (0 ())))))
          (App
           (Var (1 ())
            (Lollipop (Prod ((Var (0 ())) (Prod (Int Int)))) (Sum (Int (Prod ())))))
           (Tuple
            ((Var (0 ()) (Var (0 ())))
             (Tuple ((Int 10 Int) (Int 0 Int)) (Prod (Int Int))))
            (Prod ((Var (0 ())) (Prod (Int Int)))))
           (Sum (Int (Prod ()))))
          (Sum (Int (Prod ()))))
         (Sum (Int (Prod ()))))
        (Unpack
         (Pack (Prod ())
          (Tuple
           ((Coderef from_either (Lollipop (Sum (Int (Prod ()))) Int))
            (New (Tuple () (Prod ())) (Ref (Prod ()))))
           (Prod ((Lollipop (Sum (Int (Prod ()))) Int) (Ref (Prod ())))))
          (Exists (Lollipop (Prod ((Var (0 ())) (Sum (Int (Prod ()))))) Int)))
         (Split
          ((Lollipop (Prod ((Var (0 ())) (Sum (Int (Prod ()))))) Int) (Var (0 ())))
          (Var (0 ())
           (Prod
            ((Lollipop (Prod ((Var (0 ())) (Sum (Int (Prod ()))))) Int)
             (Var (0 ())))))
          (App
           (Var (1 ()) (Lollipop (Prod ((Var (0 ())) (Sum (Int (Prod ()))))) Int))
           (Tuple ((Var (0 ()) (Var (0 ()))) (Var (0 (r)) (Sum (Int (Prod ())))))
            (Prod ((Var (0 ())) (Sum (Int (Prod ()))))))
           Int)
          Int)
         Int)
        Int))))
    -----------incr_n-----------
    ((imports ())
     (functions
      (((export false) (name incr_1) (param (Prod ((Ref (Prod ())) (Ref Int))))
        (return (Ref Int))
        (body
         (Split ((Ref (Prod ())) (Ref Int))
          (Var (0 ()) (Prod ((Ref (Prod ())) (Ref Int))))
          (Split ((Ref Int) Int)
           (Swap (Var (0 (r)) (Ref Int)) (Int 0 Int) (Prod ((Ref Int) Int)))
           (Let Int (Binop Add (Var (0 (old)) Int) (Int 1 Int) Int)
            (Split ((Ref Int) Int)
             (Swap (Var (2 (r1)) (Ref Int)) (Var (0 (new)) Int)
              (Prod ((Ref Int) Int)))
             (Var (1 (r2)) (Ref Int)) (Ref Int))
            (Ref Int))
           (Ref Int))
          (Ref Int))))
       ((export true) (name incr_n)
        (param (Prod ((Ref (Prod ())) (Prod ((Ref Int) Int))))) (return Int)
        (body
         (Split ((Ref (Prod ())) (Prod ((Ref Int) Int)))
          (Var (0 ()) (Prod ((Ref (Prod ())) (Prod ((Ref Int) Int)))))
          (Split ((Ref Int) Int) (Var (0 (p)) (Prod ((Ref Int) Int)))
           (If0 (Var (0 (n)) Int) (Free (Var (1 (r)) (Ref Int)) Int)
            (Let (Ref Int)
             (Unpack
              (Pack (Prod ())
               (Tuple
                ((Coderef incr_1 (Lollipop (Ref Int) (Ref Int)))
                 (New (Tuple () (Prod ())) (Ref (Prod ()))))
                (Prod ((Lollipop (Ref Int) (Ref Int)) (Ref (Prod ())))))
               (Exists (Lollipop (Prod ((Var (0 ())) (Ref Int))) (Ref Int))))
              (Split
               ((Lollipop (Prod ((Var (0 ())) (Ref Int))) (Ref Int)) (Var (0 ())))
               (Var (0 ())
                (Prod
                 ((Lollipop (Prod ((Var (0 ())) (Ref Int))) (Ref Int))
                  (Var (0 ())))))
               (App
                (Var (1 ()) (Lollipop (Prod ((Var (0 ())) (Ref Int))) (Ref Int)))
                (Tuple ((Var (0 ()) (Var (0 ()))) (Var (1 (r)) (Ref Int)))
                 (Prod ((Var (0 ())) (Ref Int))))
                (Ref Int))
               (Ref Int))
              (Ref Int))
             (Let Int (Binop Sub (Var (1 (n)) Int) (Int 1 Int) Int)
              (Unpack
               (Pack (Prod ())
                (Tuple
                 ((Coderef incr_n (Lollipop (Prod ((Ref Int) Int)) Int))
                  (New (Tuple () (Prod ())) (Ref (Prod ()))))
                 (Prod ((Lollipop (Prod ((Ref Int) Int)) Int) (Ref (Prod ())))))
                (Exists
                 (Lollipop (Prod ((Var (0 ())) (Prod ((Ref Int) Int)))) Int)))
               (Split
                ((Lollipop (Prod ((Var (0 ())) (Prod ((Ref Int) Int)))) Int)
                 (Var (0 ())))
                (Var (0 ())
                 (Prod
                  ((Lollipop (Prod ((Var (0 ())) (Prod ((Ref Int) Int)))) Int)
                   (Var (0 ())))))
                (App
                 (Var (1 ())
                  (Lollipop (Prod ((Var (0 ())) (Prod ((Ref Int) Int)))) Int))
                 (Tuple
                  ((Var (0 ()) (Var (0 ())))
                   (Tuple ((Var (1 (r1)) (Ref Int)) (Var (0 (n1)) Int))
                    (Prod ((Ref Int) Int))))
                  (Prod ((Var (0 ())) (Prod ((Ref Int) Int)))))
                 Int)
                Int)
               Int)
              Int)
             Int)
            Int)
           Int)
          Int)))))
     (main
      ((Let (Ref Int) (New (Int 10 Int) (Ref Int))
        (Unpack
         (Pack (Prod ())
          (Tuple
           ((Coderef incr_n (Lollipop (Prod ((Ref Int) Int)) Int))
            (New (Tuple () (Prod ())) (Ref (Prod ()))))
           (Prod ((Lollipop (Prod ((Ref Int) Int)) Int) (Ref (Prod ())))))
          (Exists (Lollipop (Prod ((Var (0 ())) (Prod ((Ref Int) Int)))) Int)))
         (Split
          ((Lollipop (Prod ((Var (0 ())) (Prod ((Ref Int) Int)))) Int)
           (Var (0 ())))
          (Var (0 ())
           (Prod
            ((Lollipop (Prod ((Var (0 ())) (Prod ((Ref Int) Int)))) Int)
             (Var (0 ())))))
          (App
           (Var (1 ()) (Lollipop (Prod ((Var (0 ())) (Prod ((Ref Int) Int)))) Int))
           (Tuple
            ((Var (0 ()) (Var (0 ())))
             (Tuple ((Var (0 (r0)) (Ref Int)) (Int 3 Int)) (Prod ((Ref Int) Int))))
            (Prod ((Var (0 ())) (Prod ((Ref Int) Int)))))
           Int)
          Int)
         Int)
        Int))))
    -----------fix_factorial[invalid]-----------
    ((imports ())
     (functions
      (((export false) (name lam_2)
        (param
         (Prod
          ((Exists
            (Lollipop
             (Prod
              ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
             (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
        (return (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
        (body
         (Split
          ((Ref
            (Prod
             ((Exists
               (Lollipop
                (Prod
                 ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
           (Rec
            (Exists
             (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
              (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))
          (Var (0 ())
           (Prod
            ((Ref
              (Prod
               ((Exists
                 (Lollipop
                  (Prod
                   ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                  (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
             (Rec
              (Exists
               (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
                (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))))
          (Split
           ((Exists
             (Lollipop
              (Prod
               ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
              (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
           (Free
            (Var (1 ())
             (Ref
              (Prod
               ((Exists
                 (Lollipop
                  (Prod
                   ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                  (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))))
            (Prod
             ((Exists
               (Lollipop
                (Prod
                 ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
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
             (Var (0 (x))
              (Rec
               (Exists
                (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
                 (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))
             (Exists
              (Lollipop
               (Prod
                ((Var (0 ()))
                 (Rec
                  (Exists
                   (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
                    (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
               (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
            (Let (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
             (Unpack
              (Var (0 (ux))
               (Exists
                (Lollipop
                 (Prod
                  ((Var (0 ()))
                   (Rec
                    (Exists
                     (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
                      (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
                 (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
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
               (Var (0 ())
                (Prod
                 ((Lollipop
                   (Prod
                    ((Var (0 ()))
                     (Rec
                      (Exists
                       (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
                        (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
                   (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
                  (Var (0 ())))))
               (App
                (Var (1 ())
                 (Lollipop
                  (Prod
                   ((Var (0 ()))
                    (Rec
                     (Exists
                      (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
                       (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
                  (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                (Tuple
                 ((Var (0 ()) (Var (0 ())))
                  (Var (1 (x))
                   (Rec
                    (Exists
                     (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
                      (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
                 (Prod
                  ((Var (0 ()))
                   (Rec
                    (Exists
                     (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
                      (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))))
                (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
               (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
              (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
             (Unpack
              (Var (4 (f))
               (Exists
                (Lollipop
                 (Prod
                  ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                 (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
              (Split
               ((Lollipop
                 (Prod
                  ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                 (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
                (Var (0 ())))
               (Var (0 ())
                (Prod
                 ((Lollipop
                   (Prod
                    ((Var (0 ()))
                     (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                   (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
                  (Var (0 ())))))
               (App
                (Var (1 ())
                 (Lollipop
                  (Prod
                   ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                  (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                (Tuple
                 ((Var (0 ()) (Var (0 ())))
                  (Var (0 (xx)) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                 (Prod
                  ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
                (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
               (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
              (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
             (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
            (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
           (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
          (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
       ((export false) (name lam_1) (param (Prod ()))
        (return (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
        (body
         (Split
          ((Ref (Prod ()))
           (Exists
            (Lollipop
             (Prod
              ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
             (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
          (Var (0 ())
           (Prod
            ((Ref (Prod ()))
             (Exists
              (Lollipop
               (Prod
                ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
               (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
          (Split () (Free (Var (1 ()) (Ref (Prod ()))) (Prod ()))
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
             (Ref
              (Prod
               ((Exists
                 (Lollipop
                  (Prod
                   ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                  (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
             (Tuple
              ((Coderef lam_2
                (Lollipop
                 (Prod
                  ((Exists
                    (Lollipop
                     (Prod
                      ((Var (0 ()))
                       (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                     (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))
                 (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
               (New
                (Tuple
                 ((Var (0 (f))
                   (Exists
                    (Lollipop
                     (Prod
                      ((Var (0 ()))
                       (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                     (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))
                 (Prod
                  ((Exists
                    (Lollipop
                     (Prod
                      ((Var (0 ()))
                       (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                     (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
                (Ref
                 (Prod
                  ((Exists
                    (Lollipop
                     (Prod
                      ((Var (0 ()))
                       (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                     (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))))
              (Prod
               ((Lollipop
                 (Prod
                  ((Exists
                    (Lollipop
                     (Prod
                      ((Var (0 ()))
                       (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                     (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))
                 (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
                (Ref
                 (Prod
                  ((Exists
                    (Lollipop
                     (Prod
                      ((Var (0 ()))
                       (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                     (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))))))
             (Exists
              (Lollipop
               (Prod
                ((Var (0 ()))
                 (Rec
                  (Exists
                   (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
                    (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
               (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
            (Unpack
             (Var (0 (omega))
              (Exists
               (Lollipop
                (Prod
                 ((Var (0 ()))
                  (Rec
                   (Exists
                    (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
                     (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
                (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
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
              (Var (0 ())
               (Prod
                ((Lollipop
                  (Prod
                   ((Var (0 ()))
                    (Rec
                     (Exists
                      (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
                       (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
                  (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
                 (Var (0 ())))))
              (App
               (Var (1 ())
                (Lollipop
                 (Prod
                  ((Var (0 ()))
                   (Rec
                    (Exists
                     (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
                      (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
                 (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
               (Tuple
                ((Var (0 ()) (Var (0 ())))
                 (Fold
                  (Rec
                   (Exists
                    (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
                     (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
                  (Var (0 (omega))
                   (Exists
                    (Lollipop
                     (Prod
                      ((Var (0 ()))
                       (Rec
                        (Exists
                         (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
                          (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
                     (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
                  (Rec
                   (Exists
                    (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
                     (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
                (Prod
                 ((Var (0 ()))
                  (Rec
                   (Exists
                    (Lollipop (Prod ((Var (0 ())) (Var (1 (a)))))
                     (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))))
               (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
              (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
             (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
            (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
           (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
          (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
       ((export false) (name lam_4)
        (param (Prod ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
        (return Int)
        (body
         (Split
          ((Ref (Prod ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))) Int)
          (Var (0 ())
           (Prod
            ((Ref (Prod ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))) Int)))
          (Split ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
           (Free
            (Var (1 ())
             (Ref (Prod ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))
            (Prod ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
           (If0 (Var (0 (n)) Int) (Int 1 Int)
            (Let Int (Binop Sub (Var (0 (n)) Int) (Int 1 Int) Int)
             (Let Int
              (Unpack
               (Var (3 (rec)) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
               (Split ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))
                (Var (0 ())
                 (Prod ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))))
                (App (Var (1 ()) (Lollipop (Prod ((Var (0 ())) Int)) Int))
                 (Tuple ((Var (0 ()) (Var (0 ()))) (Var (0 (n-sub1)) Int))
                  (Prod ((Var (0 ())) Int)))
                 Int)
                Int)
               Int)
              (Binop Mul (Var (2 (n)) Int) (Var (0 (rec-res)) Int) Int) Int)
             Int)
            Int)
           Int)
          Int)))
       ((export false) (name lam_3) (param (Prod ()))
        (return (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
        (body
         (Split ((Ref (Prod ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
          (Var (0 ())
           (Prod
            ((Ref (Prod ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
          (Split () (Free (Var (1 ()) (Ref (Prod ()))) (Prod ()))
           (Pack (Ref (Prod ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
            (Tuple
             ((Coderef lam_4
               (Lollipop (Prod ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                Int))
              (New
               (Tuple
                ((Var (0 (rec)) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                (Prod ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
               (Ref (Prod ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
             (Prod
              ((Lollipop (Prod ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                Int)
               (Ref (Prod ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))))
            (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
           (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
          (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
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
        (Pack (Ref (Prod ()))
         (Tuple
          ((Coderef lam_1
            (Lollipop (Prod ()) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
           (New (Tuple () (Prod ())) (Ref (Prod ()))))
          (Prod
           ((Lollipop (Prod ()) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
            (Ref (Prod ())))))
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
         (Unpack
          (Var (0 (fix))
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
           (Var (0 ())
            (Prod
             ((Lollipop
               (Prod
                ((Var (0 ()))
                 (Exists
                  (Lollipop
                   (Prod
                    ((Var (0 ()))
                     (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                   (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))
               (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
              (Var (0 ())))))
           (App
            (Var (1 ())
             (Lollipop
              (Prod
               ((Var (0 ()))
                (Exists
                 (Lollipop
                  (Prod
                   ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                  (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))
              (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
            (Tuple
             ((Var (0 ()) (Var (0 ())))
              (Pack (Ref (Prod ()))
               (Tuple
                ((Coderef lam_3
                  (Lollipop (Prod ())
                   (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                 (New (Tuple () (Prod ())) (Ref (Prod ()))))
                (Prod
                 ((Lollipop (Prod ())
                   (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
                  (Ref (Prod ())))))
               (Exists
                (Lollipop
                 (Prod
                  ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                 (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))
             (Prod
              ((Var (0 ()))
               (Exists
                (Lollipop
                 (Prod
                  ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
                 (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))))
            (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
           (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
          (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
         (Unpack
          (Var (0 (factorial)) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
          (Split ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))
           (Var (0 ())
            (Prod ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))))
           (App (Var (1 ()) (Lollipop (Prod ((Var (0 ())) Int)) Int))
            (Tuple ((Var (0 ()) (Var (0 ()))) (Int 5 Int))
             (Prod ((Var (0 ())) Int)))
            Int)
           Int)
          Int)
         Int)
        Int))))
    -----------unboxed_list[invalid]-----------
    ((imports ())
     (functions
      (((export false) (name lam_1) (param (Prod ())) (return Int)
        (body
         (Split ((Ref (Prod ())) Int) (Var (0 ()) (Prod ((Ref (Prod ())) Int)))
          (Split () (Free (Var (1 ()) (Ref (Prod ()))) (Prod ()))
           (Binop Add (Var (0 (x)) Int) (Int 1 Int) Int) Int)
          Int)))
       ((export false) (name map_int)
        (param
         (Prod
          ((Ref (Prod ()))
           (Prod
            ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
             (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))))
        (return (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
        (body
         (Split
          ((Ref (Prod ()))
           (Prod
            ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
             (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))
          (Var (0 ())
           (Prod
            ((Ref (Prod ()))
             (Prod
              ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
               (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))))
          (Split
           ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
            (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
           (Var (0 (p))
            (Prod
             ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
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
                   (Int
                    (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))))))
              ((Prod
                (Int (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))
               (Split
                (Int (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
                (Var (0 (cons))
                 (Prod
                  (Int (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))
                (Inj 1
                 (Tuple
                  ((Unpack
                    (Var (4 (f)) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
                    (Split ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))
                     (Var (0 ())
                      (Prod
                       ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))))
                     (App (Var (1 ()) (Lollipop (Prod ((Var (0 ())) Int)) Int))
                      (Tuple ((Var (0 ()) (Var (0 ()))) (Var (1 (hd)) Int))
                       (Prod ((Var (0 ())) Int)))
                      Int)
                     Int)
                    Int)
                   (Unpack
                    (Pack (Prod ())
                     (Tuple
                      ((Coderef map_int
                        (Lollipop
                         (Prod
                          ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                           (Rec
                            (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))
                         (Rec
                          (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))
                       (New (Tuple () (Prod ())) (Ref (Prod ()))))
                      (Prod
                       ((Lollipop
                         (Prod
                          ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                           (Rec
                            (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))
                         (Rec
                          (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
                        (Ref (Prod ())))))
                     (Exists
                      (Lollipop
                       (Prod
                        ((Var (0 ()))
                         (Prod
                          ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                           (Rec
                            (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))))
                       (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))
                    (Split
                     ((Lollipop
                       (Prod
                        ((Var (0 ()))
                         (Prod
                          ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                           (Rec
                            (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))))
                       (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
                      (Var (0 ())))
                     (Var (0 ())
                      (Prod
                       ((Lollipop
                         (Prod
                          ((Var (0 ()))
                           (Prod
                            ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                             (Rec
                              (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))))
                         (Rec
                          (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
                        (Var (0 ())))))
                     (App
                      (Var (1 ())
                       (Lollipop
                        (Prod
                         ((Var (0 ()))
                          (Prod
                           ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                            (Rec
                             (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))))
                        (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))
                      (Tuple
                       ((Var (0 ()) (Var (0 ())))
                        (Tuple
                         ((Var (4 (f))
                           (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
                          (Var (0 (tl))
                           (Rec
                            (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))
                         (Prod
                          ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                           (Rec
                            (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))))
                       (Prod
                        ((Var (0 ()))
                         (Prod
                          ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                           (Rec
                            (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))))
                      (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
                     (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
                    (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))
                  (Prod
                   (Int
                    (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))
                 (Sum
                  ((Prod ())
                   (Prod
                    (Int
                     (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))))
                (Sum
                 ((Prod ())
                  (Prod
                   (Int
                    (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))))))
             (Sum
              ((Prod ())
               (Prod
                (Int (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))))
            (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
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
        (Unpack
         (Pack (Prod ())
          (Tuple
           ((Coderef map_int
             (Lollipop
              (Prod
               ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))
              (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))
            (New (Tuple () (Prod ())) (Ref (Prod ()))))
           (Prod
            ((Lollipop
              (Prod
               ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))
              (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
             (Ref (Prod ())))))
          (Exists
           (Lollipop
            (Prod
             ((Var (0 ()))
              (Prod
               ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))))
            (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))
         (Split
          ((Lollipop
            (Prod
             ((Var (0 ()))
              (Prod
               ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))))
            (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
           (Var (0 ())))
          (Var (0 ())
           (Prod
            ((Lollipop
              (Prod
               ((Var (0 ()))
                (Prod
                 ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                  (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))))
              (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
             (Var (0 ())))))
          (App
           (Var (1 ())
            (Lollipop
             (Prod
              ((Var (0 ()))
               (Prod
                ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                 (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))))
             (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))
           (Tuple
            ((Var (0 ()) (Var (0 ())))
             (Tuple
              ((Pack (Ref (Prod ()))
                (Tuple
                 ((Coderef lam_1 (Lollipop (Prod ()) Int))
                  (New (Tuple () (Prod ())) (Ref (Prod ()))))
                 (Prod ((Lollipop (Prod ()) Int) (Ref (Prod ())))))
                (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
               (Var (0 (lst))
                (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))
              (Prod
               ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))))
            (Prod
             ((Var (0 ()))
              (Prod
               ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))))))
           (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
          (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
         (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
        (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177"))))))))))))
    -----------boxed_list-----------
    ((imports ())
     (functions
      (((export false) (name lam_1) (param (Prod ())) (return Int)
        (body
         (Split ((Ref (Prod ())) Int) (Var (0 ()) (Prod ((Ref (Prod ())) Int)))
          (Split () (Free (Var (1 ()) (Ref (Prod ()))) (Prod ()))
           (Binop Add (Var (0 (x)) Int) (Int 1 Int) Int) Int)
          Int)))
       ((export false) (name map_int)
        (param
         (Prod
          ((Ref (Prod ()))
           (Prod
            ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
             (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))))))
        (return (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))
        (body
         (Split
          ((Ref (Prod ()))
           (Prod
            ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
             (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))))
          (Var (0 ())
           (Prod
            ((Ref (Prod ()))
             (Prod
              ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
               (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))))))
          (Split
           ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
            (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))
           (Var (0 (p))
            (Prod
             ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
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
                   (Rec
                    (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))))))
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
                  ((Unpack
                    (Var (4 (f)) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
                    (Split ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))
                     (Var (0 ())
                      (Prod
                       ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))))
                     (App (Var (1 ()) (Lollipop (Prod ((Var (0 ())) Int)) Int))
                      (Tuple ((Var (0 ()) (Var (0 ()))) (Var (1 (hd)) Int))
                       (Prod ((Var (0 ())) Int)))
                      Int)
                     Int)
                    Int)
                   (New
                    (Unpack
                     (Pack (Prod ())
                      (Tuple
                       ((Coderef map_int
                         (Lollipop
                          (Prod
                           ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                            (Rec
                             (Sum
                              ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))
                          (Rec
                           (Sum
                            ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))
                        (New (Tuple () (Prod ())) (Ref (Prod ()))))
                       (Prod
                        ((Lollipop
                          (Prod
                           ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                            (Rec
                             (Sum
                              ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))
                          (Rec
                           (Sum
                            ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))
                         (Ref (Prod ())))))
                      (Exists
                       (Lollipop
                        (Prod
                         ((Var (0 ()))
                          (Prod
                           ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                            (Rec
                             (Sum
                              ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))))
                        (Rec
                         (Sum
                          ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))))
                     (Split
                      ((Lollipop
                        (Prod
                         ((Var (0 ()))
                          (Prod
                           ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                            (Rec
                             (Sum
                              ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))))
                        (Rec
                         (Sum
                          ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))
                       (Var (0 ())))
                      (Var (0 ())
                       (Prod
                        ((Lollipop
                          (Prod
                           ((Var (0 ()))
                            (Prod
                             ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                              (Rec
                               (Sum
                                ((Prod ())
                                 (Prod (Int (Ref (Var (0 ("\206\177")))))))))))))
                          (Rec
                           (Sum
                            ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))
                         (Var (0 ())))))
                      (App
                       (Var (1 ())
                        (Lollipop
                         (Prod
                          ((Var (0 ()))
                           (Prod
                            ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                             (Rec
                              (Sum
                               ((Prod ())
                                (Prod (Int (Ref (Var (0 ("\206\177")))))))))))))
                         (Rec
                          (Sum
                           ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))
                       (Tuple
                        ((Var (0 ()) (Var (0 ())))
                         (Tuple
                          ((Var (4 (f))
                            (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
                           (Free
                            (Var (0 (tl))
                             (Ref
                              (Rec
                               (Sum
                                ((Prod ())
                                 (Prod (Int (Ref (Var (0 ("\206\177")))))))))))
                            (Rec
                             (Sum
                              ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))
                          (Prod
                           ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                            (Rec
                             (Sum
                              ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))))
                        (Prod
                         ((Var (0 ()))
                          (Prod
                           ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                            (Rec
                             (Sum
                              ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))))))
                       (Rec
                        (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))
                      (Rec
                       (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))
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
        (Unpack
         (Pack (Prod ())
          (Tuple
           ((Coderef map_int
             (Lollipop
              (Prod
               ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))
              (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))
            (New (Tuple () (Prod ())) (Ref (Prod ()))))
           (Prod
            ((Lollipop
              (Prod
               ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))
              (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))
             (Ref (Prod ())))))
          (Exists
           (Lollipop
            (Prod
             ((Var (0 ()))
              (Prod
               ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))))
            (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))))
         (Split
          ((Lollipop
            (Prod
             ((Var (0 ()))
              (Prod
               ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))))
            (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))
           (Var (0 ())))
          (Var (0 ())
           (Prod
            ((Lollipop
              (Prod
               ((Var (0 ()))
                (Prod
                 ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                  (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))))
              (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))
             (Var (0 ())))))
          (App
           (Var (1 ())
            (Lollipop
             (Prod
              ((Var (0 ()))
               (Prod
                ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                 (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))))
             (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))
           (Tuple
            ((Var (0 ()) (Var (0 ())))
             (Tuple
              ((Pack (Ref (Prod ()))
                (Tuple
                 ((Coderef lam_1 (Lollipop (Prod ()) Int))
                  (New (Tuple () (Prod ())) (Ref (Prod ()))))
                 (Prod ((Lollipop (Prod ()) Int) (Ref (Prod ())))))
                (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
               (Var (0 (lst))
                (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))
              (Prod
               ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177")))))))))))))
            (Prod
             ((Var (0 ()))
              (Prod
               ((Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))
                (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))))))
           (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))
          (Rec (Sum ((Prod ()) (Prod (Int (Ref (Var (0 ("\206\177"))))))))))
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
          ((Ref (Prod ()))
           (Prod
            ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
             (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))))
        (return (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
        (body
         (Split
          ((Ref (Prod ()))
           (Prod
            ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
             (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))
          (Var (0 ())
           (Prod
            ((Ref (Prod ()))
             (Prod
              ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
               (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))))
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
                 (Unpack
                  (Pack (Prod ())
                   (Tuple
                    ((Coderef add
                      (Lollipop
                       (Prod
                        ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
                         (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
                       (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
                     (New (Tuple () (Prod ())) (Ref (Prod ()))))
                    (Prod
                     ((Lollipop
                       (Prod
                        ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
                         (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
                       (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
                      (Ref (Prod ())))))
                   (Exists
                    (Lollipop
                     (Prod
                      ((Var (0 ()))
                       (Prod
                        ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
                         (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
                     (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))
                  (Split
                   ((Lollipop
                     (Prod
                      ((Var (0 ()))
                       (Prod
                        ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
                         (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
                     (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
                    (Var (0 ())))
                   (Var (0 ())
                    (Prod
                     ((Lollipop
                       (Prod
                        ((Var (0 ()))
                         (Prod
                          ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
                           (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
                       (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
                      (Var (0 ())))))
                   (App
                    (Var (1 ())
                     (Lollipop
                      (Prod
                       ((Var (0 ()))
                        (Prod
                         ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
                          (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
                      (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
                    (Tuple
                     ((Var (0 ()) (Var (0 ())))
                      (Tuple
                       ((Free
                         (Var (0 (succ))
                          (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
                         (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
                        (Var (1 (right))
                         (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
                       (Prod
                        ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
                         (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
                     (Prod
                      ((Var (0 ()))
                       (Prod
                        ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
                         (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))))
                    (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
                   (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
                  (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
                 (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
                (Sum ((Prod ()) (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
               (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))
            (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
           (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
          (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))
       ((export false) (name from-int) (param (Prod ((Ref (Prod ())) Int)))
        (return (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
        (body
         (Split ((Ref (Prod ())) Int) (Var (0 ()) (Prod ((Ref (Prod ())) Int)))
          (Fold (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
           (If0 (Var (0 (int)) Int)
            (Inj 0 (Tuple () (Prod ()))
             (Sum ((Prod ()) (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
            (Inj 1
             (New
              (Unpack
               (Pack (Prod ())
                (Tuple
                 ((Coderef from-int
                   (Lollipop Int (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
                  (New (Tuple () (Prod ())) (Ref (Prod ()))))
                 (Prod
                  ((Lollipop Int (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
                   (Ref (Prod ())))))
                (Exists
                 (Lollipop (Prod ((Var (0 ())) Int))
                  (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))
               (Split
                ((Lollipop (Prod ((Var (0 ())) Int))
                  (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
                 (Var (0 ())))
                (Var (0 ())
                 (Prod
                  ((Lollipop (Prod ((Var (0 ())) Int))
                    (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
                   (Var (0 ())))))
                (App
                 (Var (1 ())
                  (Lollipop (Prod ((Var (0 ())) Int))
                   (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
                 (Tuple
                  ((Var (0 ()) (Var (0 ())))
                   (Binop Sub (Var (0 (int)) Int) (Int 1 Int) Int))
                  (Prod ((Var (0 ())) Int)))
                 (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
                (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
               (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
              (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
             (Sum ((Prod ()) (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
            (Sum ((Prod ()) (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
           (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
          (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))
       ((export false) (name to-int)
        (param
         (Prod ((Ref (Prod ())) (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))
        (return Int)
        (body
         (Split ((Ref (Prod ())) (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
          (Var (0 ())
           (Prod ((Ref (Prod ())) (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))
          (Cases
           (Unfold (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
            (Var (0 (peano)) (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
            (Sum ((Prod ()) (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
           (((Prod ()) (Int 0 Int))
            ((Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
             (Binop Add (Int 1 Int)
              (Unpack
               (Pack (Prod ())
                (Tuple
                 ((Coderef to-int
                   (Lollipop (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))) Int))
                  (New (Tuple () (Prod ())) (Ref (Prod ()))))
                 (Prod
                  ((Lollipop (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))) Int)
                   (Ref (Prod ())))))
                (Exists
                 (Lollipop
                  (Prod ((Var (0 ())) (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
                  Int)))
               (Split
                ((Lollipop
                  (Prod ((Var (0 ())) (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
                  Int)
                 (Var (0 ())))
                (Var (0 ())
                 (Prod
                  ((Lollipop
                    (Prod
                     ((Var (0 ())) (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
                    Int)
                   (Var (0 ())))))
                (App
                 (Var (1 ())
                  (Lollipop
                   (Prod
                    ((Var (0 ())) (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
                   Int))
                 (Tuple
                  ((Var (0 ()) (Var (0 ())))
                   (Free
                    (Var (0 (succ))
                     (Ref (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
                    (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
                  (Prod ((Var (0 ())) (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))
                 Int)
                Int)
               Int)
              Int)))
           Int)
          Int)))))
     (main
      ((Let (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
        (Unpack
         (Pack (Prod ())
          (Tuple
           ((Coderef from-int
             (Lollipop Int (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
            (New (Tuple () (Prod ())) (Ref (Prod ()))))
           (Prod
            ((Lollipop Int (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
             (Ref (Prod ())))))
          (Exists
           (Lollipop (Prod ((Var (0 ())) Int))
            (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))
         (Split
          ((Lollipop (Prod ((Var (0 ())) Int))
            (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
           (Var (0 ())))
          (Var (0 ())
           (Prod
            ((Lollipop (Prod ((Var (0 ())) Int))
              (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
             (Var (0 ())))))
          (App
           (Var (1 ())
            (Lollipop (Prod ((Var (0 ())) Int))
             (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
           (Tuple ((Var (0 ()) (Var (0 ()))) (Int 6 Int))
            (Prod ((Var (0 ())) Int)))
           (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
          (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
         (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
        (Let (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
         (Unpack
          (Pack (Prod ())
           (Tuple
            ((Coderef from-int
              (Lollipop Int (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
             (New (Tuple () (Prod ())) (Ref (Prod ()))))
            (Prod
             ((Lollipop Int (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
              (Ref (Prod ())))))
           (Exists
            (Lollipop (Prod ((Var (0 ())) Int))
             (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))
          (Split
           ((Lollipop (Prod ((Var (0 ())) Int))
             (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
            (Var (0 ())))
           (Var (0 ())
            (Prod
             ((Lollipop (Prod ((Var (0 ())) Int))
               (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
              (Var (0 ())))))
           (App
            (Var (1 ())
             (Lollipop (Prod ((Var (0 ())) Int))
              (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
            (Tuple ((Var (0 ()) (Var (0 ()))) (Int 7 Int))
             (Prod ((Var (0 ())) Int)))
            (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
           (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
          (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
         (Let (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
          (Unpack
           (Pack (Prod ())
            (Tuple
             ((Coderef add
               (Lollipop
                (Prod
                 ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
                  (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
                (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
              (New (Tuple () (Prod ())) (Ref (Prod ()))))
             (Prod
              ((Lollipop
                (Prod
                 ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
                  (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
                (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
               (Ref (Prod ())))))
            (Exists
             (Lollipop
              (Prod
               ((Var (0 ()))
                (Prod
                 ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
                  (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
              (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))
           (Split
            ((Lollipop
              (Prod
               ((Var (0 ()))
                (Prod
                 ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
                  (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
              (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
             (Var (0 ())))
            (Var (0 ())
             (Prod
              ((Lollipop
                (Prod
                 ((Var (0 ()))
                  (Prod
                   ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
                    (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
                (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
               (Var (0 ())))))
            (App
             (Var (1 ())
              (Lollipop
               (Prod
                ((Var (0 ()))
                 (Prod
                  ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
                   (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
               (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
             (Tuple
              ((Var (0 ()) (Var (0 ())))
               (Tuple
                ((Var (1 (six)) (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
                 (Var (0 (seven)) (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
                (Prod
                 ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
                  (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))))
              (Prod
               ((Var (0 ()))
                (Prod
                 ((Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))
                  (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))))
             (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
            (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
           (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))
          (Unpack
           (Pack (Prod ())
            (Tuple
             ((Coderef to-int
               (Lollipop (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))) Int))
              (New (Tuple () (Prod ())) (Ref (Prod ()))))
             (Prod
              ((Lollipop (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))) Int)
               (Ref (Prod ())))))
            (Exists
             (Lollipop
              (Prod ((Var (0 ())) (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
              Int)))
           (Split
            ((Lollipop
              (Prod ((Var (0 ())) (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
              Int)
             (Var (0 ())))
            (Var (0 ())
             (Prod
              ((Lollipop
                (Prod ((Var (0 ())) (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
                Int)
               (Var (0 ())))))
            (App
             (Var (1 ())
              (Lollipop
               (Prod ((Var (0 ())) (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
               Int))
             (Tuple
              ((Var (0 ()) (Var (0 ())))
               (Var (0 (sum)) (Rec (Sum ((Prod ()) (Ref (Var (0 (a)))))))))
              (Prod ((Var (0 ())) (Rec (Sum ((Prod ()) (Ref (Var (0 (a))))))))))
             Int)
            Int)
           Int)
          Int)
         Int)
        Int))))
    -----------mini_zip-----------
    ((imports ())
     (functions
      (((export false) (name add1) (param (Prod ((Ref (Prod ())) Int)))
        (return Int)
        (body
         (Split ((Ref (Prod ())) Int) (Var (0 ()) (Prod ((Ref (Prod ())) Int)))
          (Binop Add (Var (0 (x)) Int) (Int 1 Int) Int) Int)))
       ((export true) (name typle_add1)
        (param (Prod ((Ref (Prod ())) (Prod (Int Int))))) (return (Prod (Int Int)))
        (body
         (Split ((Ref (Prod ())) (Prod (Int Int)))
          (Var (0 ()) (Prod ((Ref (Prod ())) (Prod (Int Int)))))
          (Split (Int Int) (Var (0 (x)) (Prod (Int Int)))
           (Tuple
            ((Unpack
              (Pack (Prod ())
               (Tuple
                ((Coderef add1 (Lollipop Int Int))
                 (New (Tuple () (Prod ())) (Ref (Prod ()))))
                (Prod ((Lollipop Int Int) (Ref (Prod ())))))
               (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
              (Split ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))
               (Var (0 ())
                (Prod ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))))
               (App (Var (1 ()) (Lollipop (Prod ((Var (0 ())) Int)) Int))
                (Tuple ((Var (0 ()) (Var (0 ()))) (Var (1 (x1)) Int))
                 (Prod ((Var (0 ())) Int)))
                Int)
               Int)
              Int)
             (Unpack
              (Pack (Prod ())
               (Tuple
                ((Coderef add1 (Lollipop Int Int))
                 (New (Tuple () (Prod ())) (Ref (Prod ()))))
                (Prod ((Lollipop Int Int) (Ref (Prod ())))))
               (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))
              (Split ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))
               (Var (0 ())
                (Prod ((Lollipop (Prod ((Var (0 ())) Int)) Int) (Var (0 ())))))
               (App (Var (1 ()) (Lollipop (Prod ((Var (0 ())) Int)) Int))
                (Tuple ((Var (0 ()) (Var (0 ()))) (Var (0 (x2)) Int))
                 (Prod ((Var (0 ())) Int)))
                Int)
               Int)
              Int))
            (Prod (Int Int)))
           (Prod (Int Int)))
          (Prod (Int Int)))))
       ((export false) (name mini_zip_specialized)
        (param (Prod ((Ref (Prod ())) (Prod ((Ref Int) (Ref (Ref Int)))))))
        (return (Ref (Prod (Int (Ref Int)))))
        (body
         (Split ((Ref (Prod ())) (Prod ((Ref Int) (Ref (Ref Int)))))
          (Var (0 ()) (Prod ((Ref (Prod ())) (Prod ((Ref Int) (Ref (Ref Int)))))))
          (Split ((Ref Int) (Ref (Ref Int)))
           (Var (0 (p)) (Prod ((Ref Int) (Ref (Ref Int)))))
           (New
            (Tuple
             ((Free (Var (1 (a)) (Ref Int)) Int)
              (Free (Var (0 (b)) (Ref (Ref Int))) (Ref Int)))
             (Prod (Int (Ref Int))))
            (Ref (Prod (Int (Ref Int)))))
           (Ref (Prod (Int (Ref Int)))))
          (Ref (Prod (Int (Ref Int)))))))))
     (main ())) |}]
