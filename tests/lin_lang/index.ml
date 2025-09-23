open! Base
open Richwasm_lin_lang
open Index
open Stdlib.Format

let do_thing x = x |> Compile.compile_module

let%expect_test "basic indexing" =
  let do_thing (x : Syntax.Module.t) =
    x |> do_thing |> printf "@.%a@." IR.Module.pp
  in
  let mk = Syntax.Module.make in

  do_thing (mk ~main:(Let (("a", Int), Val (Int 10), Val (Var "a"))) ());
  [%expect
    {| ((imports ()) (toplevels ()) (main ((Let Int (Val (Int 10)) (Val (Var (0 (a)))))))) |}];

  do_thing
    (mk
       ~toplevels:
         [
           {
             export = true;
             binding = ("foo", Lollipop (Int, Int));
             init = Val (Lam (("x", Int), Int, Val (Int 10)));
           };
         ]
       ());
  [%expect
    {|
      ((imports ())
       (toplevels (((export true) (binding (foo (Lollipop Int Int))) (init (Val (Lam Int Int (Val (Int 10))))))))
       (main ())) |}]

let%expect_test "indexes examples" =
  let examples = Examples.all in
  let fmt = std_formatter in
  pp_set_margin fmt 80;
  pp_set_max_indent fmt 80;
  examples
  |> List.iter ~f:(fun (n, m) ->
         let res = m |> do_thing in
         printf "-----------%s-----------@.%a@." n IR.Module.pp res);
  [%expect
    {|
    -----------add_one_program-----------
    ((imports ())
     (toplevels
      (((export true) (binding (add_one (Lollipop Int Int)))
        (init (Val (Lam Int Int (Binop Add (Var (0 (x))) (Int 1))))))))
     (main ((App (Global add_one) (Int 42)))))
    -----------swap_pair_program-----------
    ((imports ())
     (toplevels
      (((export true) (binding (swap (Lollipop (Prod (Int Int)) (Prod (Int Int)))))
        (init
         (Val
          (Lam (Prod (Int Int)) (Prod (Int Int))
           (LetProd (Int Int) (Val (Var (0 (p))))
            (Val (Tuple ((Var (0 (y))) (Var (1 (x)))))))))))))
     (main ((App (Global swap) (Tuple ((Int 1) (Int 2)))))))
    -----------compose_program-----------
    ((imports ())
     (toplevels
      (((export true)
        (binding
         (compose
          (Lollipop (Lollipop Int Int)
           (Lollipop (Lollipop Int Int) (Lollipop Int Int)))))
        (init
         (Val
          (Lam (Lollipop Int Int) (Lollipop (Lollipop Int Int) (Lollipop Int Int))
           (Val
            (Lam (Lollipop Int Int) (Lollipop Int Int)
             (Val
              (Lam Int Int
               (Let Int (App (Var (1 (g))) (Var (0 (x))))
                (App (Var (3 (f))) (Var (0 (g_result)))))))))))))))
     (main ()))
    -----------reference_example-----------
    ((imports ())
     (toplevels
      (((export false) (binding (test_ref Int))
        (init
         (Let (Ref Int) (New (Int 10))
          (Let Int (Swap (Var (0 (r))) (Int 20))
           (Let Int (Free (Var (1 (r)))) (Val (Var (1 (old_val)))))))))))
     (main ((Val (Global test_ref)))))
    -----------factorial_program-----------
    ((imports ())
     (toplevels
      (((export true) (binding (factorial (Lollipop Int Int)))
        (init
         (Val
          (Lam Int Int
           (If0 (Var (0 (n))) (Val (Int 1))
            (Let Int (Binop Sub (Var (0 (n))) (Int 1))
             (Let Int (App (Global factorial) (Var (0 (n_minus_1))))
              (Let Int (Binop Mul (Var (2 (n))) (Var (0 (rec_result))))
               (Val (Var (0 (final_result))))))))))))))
     (main ((App (Global factorial) (Int 5)))))
    -----------module_with_imports-----------
    ((imports
      (((typ (Lollipop Int Int)) (name external_inc))
       ((typ (Lollipop (Prod (Int Int)) Int)) (name external_add))))
     (toplevels
      (((export true) (binding (double_inc (Lollipop Int Int)))
        (init
         (Val
          (Lam Int Int
           (Let Int (App (Global external_inc) (Var (0 (x))))
            (App (Global external_inc) (Var (0 (first_inc)))))))))))
     (main ((App (Global double_inc) (Int 5)))))
    -----------complex_example-----------
    ((imports ())
     (toplevels
      (((export true) (binding (process_pair (Lollipop (Prod (Int Int)) Int)))
        (init
         (Val
          (Lam (Prod (Int Int)) Int
           (LetProd (Int Int) (Val (Var (0 (input))))
            (Let Int (Binop Add (Var (1 (a))) (Var (0 (b))))
             (Let (Ref Int) (New (Var (0 (sum))))
              (Let Int (Binop Mul (Var (3 (a))) (Var (2 (b))))
               (Let (Ref Int) (New (Var (0 (product))))
                (Let Int (Swap (Var (2 (r1))) (Int 0))
                 (Let Int (Swap (Var (1 (r2))) (Int 0))
                  (Let Int (Free (Var (4 (r1))))
                   (Let Int (Free (Var (3 (r2))))
                    (Let Int (Binop Add (Var (3 (sum_val))) (Var (2 (prod_val))))
                     (Val (Var (0 (final_result))))))))))))))))))))
     (main ((App (Global process_pair) (Tuple ((Int 3) (Int 4)))))))
    -----------closure_example-----------
    ((imports ())
     (toplevels
      (((export true) (binding (make_adder (Lollipop Int (Lollipop Int Int))))
        (init
         (Val
          (Lam Int (Lollipop Int Int)
           (Val (Lam Int Int (Binop Add (Var (1 (n))) (Var (0 (x))))))))))))
     (main
      ((Let (Lollipop Int Int) (App (Global make_adder) (Int 5))
        (App (Var (0 (add5))) (Int 10)))))) |}]
