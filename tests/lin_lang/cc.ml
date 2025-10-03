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
    |> Typecheck.Compile.compile_module
    |> or_fail_pp Typecheck.Err.pp
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
  [%expect{|
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
  [%expect{|
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
  [%expect{|
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
  [%expect{|
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
  [%expect{|
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
  [%expect{| FAILURE TODO |}]

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
        (return Int) (body (Binop Add (Var (0 (x)) Int) (Int 1 Int) Int)))))
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
    FAILURE (MissingGlobalEnv print ((locals ()) (fns ())))
    -----------factorial_program-----------
    FAILURE TODO
    -----------safe_div-----------
    FAILURE TODO
    -----------incr_n-----------
    FAILURE TODO
    -----------fix_factorial-----------
    FAILURE TODO |}]
