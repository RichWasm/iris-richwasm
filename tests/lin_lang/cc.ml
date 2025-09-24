open! Base
open Richwasm_lin_lang
open Cc
open Stdlib.Format

let do_thing (x : Syntax.Module.t) =
  x |> Index.Compile.compile_module |> Cc.Compile.compile_module

let%expect_test "simple" =
  let output x =
    x |> do_thing |> function
    | Ok res -> printf "@.%a@." IR.Module.pp res
    | Error err -> printf "@.%s@." (Compile.Err.to_string err)
  in
  let mk = Syntax.Module.make in
  output (mk ());
  [%expect {| ((imports ()) (toplevels ()) (main ())) |}];

  output (mk ~main:(Val (Lam (("x", Int), Int, Val (Int 69)))) ());
  [%expect
    {|
    ((imports ())
     (toplevels
      ((Func (export false) (name lam_1) (params ((Prod ()) Int)) (ret Int)
        (body (LetTuple () (Val (Var (1 ()))) (Val (Int 69)))))))
     (main
      ((Val
        (Pack (Prod ()) (Tuple ((Coderef lam_1) (Tuple ())))
         (Exists (Lollipop ((Var 0) Int) Int))))))) |}];

  output
    (mk
       ~main:
         (Let
            ( ("y", Int),
              Val (Int 67),
              Val (Lam (("x", Int), Int, Binop (Add, Var "x", Var "y"))) ))
       ());
  [%expect
    {|
    ((imports ())
     (toplevels
      ((Func (export false) (name lam_1) (params ((Prod (Int)) Int)) (ret Int)
        (body
         (LetTuple (Int) (Val (Var (1 ())))
          (Binop Add (Var (0 (x))) (Var (2 (y)))))))))
     (main
      ((Let Int (Val (Int 67))
        (Val
         (Pack (Prod (Int)) (Tuple ((Coderef lam_1) (Tuple ((Var (0 (y)))))))
          (Exists (Lollipop ((Var 0) Int) Int)))))))) |}];

  output
    (mk
       ~main:
         (Let
            ( ("z", Int),
              Val (Int 420),
              Let
                ( ("y", Int),
                  Val (Int 67),
                  Val
                    (Lam
                       ( ("x", Int),
                         Int,
                         Let
                           ( ("r", Int),
                             Binop (Add, Var "x", Var "y"),
                             Binop (Mul, Var "z", Var "r") ) )) ) ))
       ());
  [%expect
    {|
    ((imports ())
     (toplevels
      ((Func (export false) (name lam_1) (params ((Prod (Int Int)) Int)) (ret Int)
        (body
         (LetTuple (Int Int) (Val (Var (1 ())))
          (Let Int (Binop Add (Var (0 (x))) (Var (3 (y))))
           (Binop Mul (Var (3 (z))) (Var (0 (r))))))))))
     (main
      ((Let Int (Val (Int 420))
        (Let Int (Val (Int 67))
         (Val
          (Pack (Prod (Int Int))
           (Tuple ((Coderef lam_1) (Tuple ((Var (0 (y))) (Var (1 (z)))))))
           (Exists (Lollipop ((Var 0) Int) Int))))))))) |}];
  output
    (mk
       ~main:
         (Let
            ( ("y", Int),
              Val (Int 67),
              Val
                (Lam
                   ( ("x", Int),
                     Int,
                     LetProd
                       ( [ ("a", Int); ("b", Int) ],
                         Val (Tuple [ Var "x"; Var "y" ]),
                         Binop (Add, Var "a", Var "b") ) )) ))
       ());
  [%expect
    {|
    ((imports ())
     (toplevels
      ((Func (export false) (name lam_1) (params ((Prod (Int)) Int)) (ret Int)
        (body
         (LetTuple (Int) (Val (Var (1 ())))
          (LetTuple (Int Int) (Val (Tuple ((Var (0 (x))) (Var (2 (y))))))
           (Binop Add (Var (1 (a))) (Var (0 (b))))))))))
     (main
      ((Let Int (Val (Int 67))
        (Val
         (Pack (Prod (Int)) (Tuple ((Coderef lam_1) (Tuple ((Var (0 (y)))))))
          (Exists (Lollipop ((Var 0) Int) Int)))))))) |}];
  output
    (mk
       ~main:
         (Let
            ( ("add1", Lollipop (Int, Int)),
              Val (Lam (("x", Int), Int, Binop (Add, Var "x", Int 1))),
              App (Var "add1", Int 10) ))
       ());
  [%expect
    {|
    ((imports ())
     (toplevels
      ((Func (export false) (name lam_1) (params ((Prod ()) Int)) (ret Int)
        (body (LetTuple () (Val (Var (1 ()))) (Binop Add (Var (0 (x))) (Int 1)))))))
     (main
      ((Let (Exists (Lollipop ((Var 0) Int) Int))
        (Val
         (Pack (Prod ()) (Tuple ((Coderef lam_1) (Tuple ())))
          (Exists (Lollipop ((Var 0) Int) Int))))
        (Unpack (Var (0 (add1)))
         (LetTuple ((Lollipop ((Var 0) Int) Int) (Var 0)) (Val (Var (0 ())))
          (App (Var (1 ())) (Tuple ((Var (0 ())) (Int 10)))))
         Int))))) |}]

let%expect_test "examples" =
  let examples = Examples.all in
  let fmt = std_formatter in
  pp_set_margin fmt 80;
  pp_set_max_indent fmt 80;
  examples
  |> List.iter ~f:(fun (n, m) ->
         match do_thing m with
         | Ok res -> printf "-----------%s-----------@.%a@." n IR.Module.pp res
         | Error err ->
             printf "-----------%s-----------@.%s@." n
               (Compile.Err.to_string err));
  [%expect
    {|
    -----------add_one_program-----------
    ((imports ())
     (toplevels
      ((Func (export false) (name lam_1) (params ((Prod ()) Int)) (ret Int)
        (body (LetTuple () (Val (Var (1 ()))) (Binop Add (Var (0 (x))) (Int 1)))))
       (Let (export true) (binding (add_one (Exists (Lollipop ((Var 0) Int) Int))))
        (init
         (Val
          (Pack (Prod ()) (Tuple ((Coderef lam_1) (Tuple ())))
           (Exists (Lollipop ((Var 0) Int) Int))))))))
     (main
      ((Unpack
        (Pack (Prod ()) (Tuple ((Coderef add_one) (Tuple ())))
         (Exists (Lollipop ((Var 0) Int) Int)))
        (LetTuple ((Lollipop ((Var 0) Int) Int) (Var 0)) (Val (Var (0 ())))
         (App (Var (1 ())) (Tuple ((Var (0 ())) (Int 42)))))
        Int))))
    -----------swap_pair_program-----------
    ((imports ())
     (toplevels
      ((Func (export false) (name lam_1) (params ((Prod ()) (Prod (Int Int))))
        (ret (Prod (Int Int)))
        (body
         (LetTuple () (Val (Var (1 ())))
          (LetTuple (Int Int) (Val (Var (0 (p))))
           (Val (Tuple ((Var (0 (y))) (Var (1 (x))))))))))
       (Let (export true)
        (binding
         (swap (Exists (Lollipop ((Var 0) (Prod (Int Int))) (Prod (Int Int))))))
        (init
         (Val
          (Pack (Prod ()) (Tuple ((Coderef lam_1) (Tuple ())))
           (Exists (Lollipop ((Var 0) (Prod (Int Int))) (Prod (Int Int))))))))))
     (main
      ((Unpack
        (Pack (Prod ()) (Tuple ((Coderef swap) (Tuple ())))
         (Exists (Lollipop ((Var 0) (Prod (Int Int))) (Prod (Int Int)))))
        (LetTuple ((Lollipop ((Var 0) (Prod (Int Int))) (Prod (Int Int))) (Var 0))
         (Val (Var (0 ())))
         (App (Var (1 ())) (Tuple ((Var (0 ())) (Tuple ((Int 1) (Int 2)))))))
        (Prod (Int Int))))))
    -----------compose_program-----------
    ((imports ())
     (toplevels
      ((Func (export false) (name lam_3)
        (params
         ((Prod
           ((Exists (Lollipop ((Var 0) Int) Int))
            (Exists (Lollipop ((Var 0) Int) Int))))
          Int))
        (ret Int)
        (body
         (LetTuple
          ((Exists (Lollipop ((Var 0) Int) Int))
           (Exists (Lollipop ((Var 0) Int) Int)))
          (Val (Var (1 ())))
          (Let Int
           (Unpack (Var (3 (g)))
            (LetTuple ((Lollipop ((Var 0) Int) Int) (Var 0)) (Val (Var (0 ())))
             (App (Var (1 ())) (Tuple ((Var (0 ())) (Var (0 (x)))))))
            Int)
           (Unpack (Var (3 (f)))
            (LetTuple ((Lollipop ((Var 0) Int) Int) (Var 0)) (Val (Var (0 ())))
             (App (Var (1 ())) (Tuple ((Var (0 ())) (Var (0 (g_result)))))))
            Int)))))
       (Func (export false) (name lam_2)
        (params
         ((Prod ((Exists (Lollipop ((Var 0) Int) Int))))
          (Exists (Lollipop ((Var 0) Int) Int))))
        (ret (Exists (Lollipop ((Var 0) Int) Int)))
        (body
         (LetTuple ((Exists (Lollipop ((Var 0) Int) Int))) (Val (Var (1 ())))
          (Val
           (Pack
            (Prod
             ((Exists (Lollipop ((Var 0) Int) Int))
              (Exists (Lollipop ((Var 0) Int) Int))))
            (Tuple ((Coderef lam_3) (Tuple ((Var (0 (g))) (Var (1 (f)))))))
            (Exists (Lollipop ((Var 0) Int) Int)))))))
       (Func (export false) (name lam_1)
        (params ((Prod ()) (Exists (Lollipop ((Var 0) Int) Int))))
        (ret
         (Exists
          (Lollipop ((Var 0) (Exists (Lollipop ((Var 0) Int) Int)))
           (Exists (Lollipop ((Var 0) Int) Int)))))
        (body
         (LetTuple () (Val (Var (1 ())))
          (Val
           (Pack (Prod ((Exists (Lollipop ((Var 0) Int) Int))))
            (Tuple ((Coderef lam_2) (Tuple ((Var (0 (f)))))))
            (Exists
             (Lollipop ((Var 0) (Exists (Lollipop ((Var 0) Int) Int)))
              (Exists (Lollipop ((Var 0) Int) Int)))))))))
       (Let (export true)
        (binding
         (compose
          (Exists
           (Lollipop ((Var 0) (Exists (Lollipop ((Var 0) Int) Int)))
            (Exists
             (Lollipop ((Var 0) (Exists (Lollipop ((Var 0) Int) Int)))
              (Exists (Lollipop ((Var 0) Int) Int))))))))
        (init
         (Val
          (Pack (Prod ()) (Tuple ((Coderef lam_1) (Tuple ())))
           (Exists
            (Lollipop ((Var 0) (Exists (Lollipop ((Var 0) Int) Int)))
             (Exists
              (Lollipop ((Var 0) (Exists (Lollipop ((Var 0) Int) Int)))
               (Exists (Lollipop ((Var 0) Int) Int))))))))))))
     (main ()))
    -----------reference_example-----------
    ((imports ())
     (toplevels
      ((Let (export false) (binding (test_ref Int))
        (init
         (Let (Ref Int) (New (Int 10))
          (Let Int (Swap (Var (0 (r))) (Int 20))
           (Let Int (Free (Var (1 (r)))) (Val (Var (1 (old_val)))))))))))
     (main ((Val (Global test_ref)))))
    -----------factorial_program-----------
    ((imports ())
     (toplevels
      ((Func (export false) (name lam_1) (params ((Prod ()) Int)) (ret Int)
        (body
         (LetTuple () (Val (Var (1 ())))
          (If0 (Var (0 (n))) (Val (Int 1))
           (Let Int (Binop Sub (Var (0 (n))) (Int 1))
            (Let Int
             (Unpack
              (Pack (Prod ()) (Tuple ((Coderef factorial) (Tuple ())))
               (Exists (Lollipop ((Var 0) Int) Int)))
              (LetTuple ((Lollipop ((Var 0) Int) Int) (Var 0)) (Val (Var (0 ())))
               (App (Var (1 ())) (Tuple ((Var (0 ())) (Var (0 (n_minus_1)))))))
              Int)
             (Let Int (Binop Mul (Var (2 (n))) (Var (0 (rec_result))))
              (Val (Var (0 (final_result)))))))))))
       (Let (export true)
        (binding (factorial (Exists (Lollipop ((Var 0) Int) Int))))
        (init
         (Val
          (Pack (Prod ()) (Tuple ((Coderef lam_1) (Tuple ())))
           (Exists (Lollipop ((Var 0) Int) Int))))))))
     (main
      ((Unpack
        (Pack (Prod ()) (Tuple ((Coderef factorial) (Tuple ())))
         (Exists (Lollipop ((Var 0) Int) Int)))
        (LetTuple ((Lollipop ((Var 0) Int) Int) (Var 0)) (Val (Var (0 ())))
         (App (Var (1 ())) (Tuple ((Var (0 ())) (Int 5)))))
        Int))))
    -----------module_with_imports-----------
    ((imports
      (((typ (Exists (Lollipop ((Var 0) Int) Int))) (name external_inc))
       ((typ (Exists (Lollipop ((Var 0) (Prod (Int Int))) Int)))
        (name external_add))))
     (toplevels
      ((Func (export false) (name lam_1) (params ((Prod ()) Int)) (ret Int)
        (body
         (LetTuple () (Val (Var (1 ())))
          (Let Int
           (Unpack
            (Pack (Prod ()) (Tuple ((Coderef external_inc) (Tuple ())))
             (Exists (Lollipop ((Var 0) Int) Int)))
            (LetTuple ((Lollipop ((Var 0) Int) Int) (Var 0)) (Val (Var (0 ())))
             (App (Var (1 ())) (Tuple ((Var (0 ())) (Var (0 (x)))))))
            Int)
           (Unpack
            (Pack (Prod ()) (Tuple ((Coderef external_inc) (Tuple ())))
             (Exists (Lollipop ((Var 0) Int) Int)))
            (LetTuple ((Lollipop ((Var 0) Int) Int) (Var 0)) (Val (Var (0 ())))
             (App (Var (1 ())) (Tuple ((Var (0 ())) (Var (0 (first_inc)))))))
            Int)))))
       (Let (export true)
        (binding (double_inc (Exists (Lollipop ((Var 0) Int) Int))))
        (init
         (Val
          (Pack (Prod ()) (Tuple ((Coderef lam_1) (Tuple ())))
           (Exists (Lollipop ((Var 0) Int) Int))))))))
     (main
      ((Unpack
        (Pack (Prod ()) (Tuple ((Coderef double_inc) (Tuple ())))
         (Exists (Lollipop ((Var 0) Int) Int)))
        (LetTuple ((Lollipop ((Var 0) Int) Int) (Var 0)) (Val (Var (0 ())))
         (App (Var (1 ())) (Tuple ((Var (0 ())) (Int 5)))))
        Int))))
    -----------complex_example-----------
    ((imports ())
     (toplevels
      ((Func (export false) (name lam_1) (params ((Prod ()) (Prod (Int Int))))
        (ret Int)
        (body
         (LetTuple () (Val (Var (1 ())))
          (LetTuple (Int Int) (Val (Var (0 (input))))
           (Let Int (Binop Add (Var (1 (a))) (Var (0 (b))))
            (Let (Ref Int) (New (Var (0 (sum))))
             (Let Int (Binop Mul (Var (3 (a))) (Var (2 (b))))
              (Let (Ref Int) (New (Var (0 (product))))
               (Let Int (Swap (Var (2 (r1))) (Int 0))
                (Let Int (Swap (Var (1 (r2))) (Int 0))
                 (Let Int (Free (Var (4 (r1))))
                  (Let Int (Free (Var (3 (r2))))
                   (Let Int (Binop Add (Var (3 (sum_val))) (Var (2 (prod_val))))
                    (Val (Var (0 (final_result)))))))))))))))))
       (Let (export true)
        (binding (process_pair (Exists (Lollipop ((Var 0) (Prod (Int Int))) Int))))
        (init
         (Val
          (Pack (Prod ()) (Tuple ((Coderef lam_1) (Tuple ())))
           (Exists (Lollipop ((Var 0) (Prod (Int Int))) Int))))))))
     (main
      ((Unpack
        (Pack (Prod ()) (Tuple ((Coderef process_pair) (Tuple ())))
         (Exists (Lollipop ((Var 0) (Prod (Int Int))) Int)))
        (LetTuple ((Lollipop ((Var 0) (Prod (Int Int))) Int) (Var 0))
         (Val (Var (0 ())))
         (App (Var (1 ())) (Tuple ((Var (0 ())) (Tuple ((Int 3) (Int 4)))))))
        Int))))
    -----------closure_example-----------
    ((imports ())
     (toplevels
      ((Func (export false) (name lam_2) (params ((Prod (Int)) Int)) (ret Int)
        (body
         (LetTuple (Int) (Val (Var (1 ())))
          (Binop Add (Var (2 (n))) (Var (0 (x)))))))
       (Func (export false) (name lam_1) (params ((Prod ()) Int))
        (ret (Exists (Lollipop ((Var 0) Int) Int)))
        (body
         (LetTuple () (Val (Var (1 ())))
          (Val
           (Pack (Prod (Int)) (Tuple ((Coderef lam_2) (Tuple ((Var (0 (n)))))))
            (Exists (Lollipop ((Var 0) Int) Int)))))))
       (Let (export true)
        (binding
         (make_adder
          (Exists (Lollipop ((Var 0) Int) (Exists (Lollipop ((Var 0) Int) Int))))))
        (init
         (Val
          (Pack (Prod ()) (Tuple ((Coderef lam_1) (Tuple ())))
           (Exists (Lollipop ((Var 0) Int) (Exists (Lollipop ((Var 0) Int) Int))))))))))
     (main
      ((Let (Exists (Lollipop ((Var 0) Int) Int))
        (Unpack
         (Pack (Prod ()) (Tuple ((Coderef make_adder) (Tuple ())))
          (Exists (Lollipop ((Var 0) Int) (Exists (Lollipop ((Var 0) Int) Int)))))
         (LetTuple
          ((Lollipop ((Var 0) Int) (Exists (Lollipop ((Var 0) Int) Int))) (Var 0))
          (Val (Var (0 ()))) (App (Var (1 ())) (Tuple ((Var (0 ())) (Int 5)))))
         (Exists (Lollipop ((Var 0) Int) Int)))
        (Unpack (Var (0 (add5)))
         (LetTuple ((Lollipop ((Var 0) Int) Int) (Var 0)) (Val (Var (0 ())))
          (App (Var (1 ())) (Tuple ((Var (0 ())) (Int 10)))))
         Int))))) |}]
