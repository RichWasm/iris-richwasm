open! Base
open! Stdlib.Format
open! Richwasm_lin_lang
open Index

let do_thing x =
  x |> Compile.compile_module |> function
  | Ok x -> x
  | Error err -> failwith @@ asprintf "%a" Index.Err.pp err

let%expect_test "basic indexing" =
  pp_set_margin std_formatter 80;
  pp_set_max_indent std_formatter 80;

  let output (x : Syntax.Module.t) =
    try x |> do_thing |> printf "@.%a@." IR.Module.pp
    with Failure msg -> printf "FAILURE %s@." msg
  in
  let mk = Syntax.Module.make in

  output (mk ~main:(Let (("a", Int), Val (Int 10), Val (Var "a"))) ());
  [%expect
    {|
      ((imports ()) (functions ())
       (main ((Let Int (Val (Int 10)) (Val (Var (0 (a)))))))) |}];

  output
    (mk
       ~functions:
         [
           {
             export = true;
             name = "foo";
             param = ("x", Int);
             return = Int;
             body = Val (Int 10);
           };
         ]
       ());
  [%expect
    {|
      ((imports ())
       (functions
        (((export true) (name foo) (param Int) (return Int) (body (Val (Int 10))))))
       (main ())) |}]

let%expect_test "indexes examples" =
  pp_set_margin std_formatter 80;
  pp_set_max_indent std_formatter 80;
  Examples.all
  |> List.iter ~f:(fun (n, m) ->
         try
           let res = m |> do_thing in
           printf "-----------%s-----------@.%a@." n IR.Module.pp res
         with Failure msg ->
           printf "-----------%s-----------@.FAILURE %s@." n msg);
  [%expect{|
    -----------add_one_program-----------
    ((imports ())
     (functions
      (((export true) (name add_one) (param Int) (return Int)
        (body (Binop Add (Var (0 (x))) (Int 1))))))
     (main ((App (Coderef add_one) (Int 42)))))
    -----------swap_pair_program-----------
    ((imports ())
     (functions
      (((export true) (name swap) (param (Prod (Int Int)))
        (return (Prod (Int Int)))
        (body
         (LetProd (Int Int) (Val (Var (0 (p))))
          (Val (Tuple ((Var (0 (y))) (Var (1 (x)))))))))))
     (main ((App (Coderef swap) (Tuple ((Int 1) (Int 2)))))))
    -----------compose_program-----------
    ((imports ())
     (functions
      (((export true) (name compose) (param (Lollipop Int Int))
        (return (Lollipop (Lollipop Int Int) (Lollipop Int Int)))
        (body
         (Val
          (Lam (Lollipop Int Int) (Lollipop Int Int)
           (Val
            (Lam Int Int
             (Let Int (App (Var (1 (g))) (Var (0 (x))))
              (App (Var (3 (f))) (Var (0 (g_result)))))))))))))
     (main ()))
    -----------reference_example-----------
    ((imports ()) (functions ())
     (main
      ((Let (Ref Int) (New (Int 10))
        (Let Int (Swap (Var (0 (r))) (Int 20))
         (Let Int (Free (Var (1 (r)))) (Val (Var (1 (old_val))))))))))
    -----------factorial_program-----------
    ((imports ())
     (functions
      (((export true) (name factorial) (param Int) (return Int)
        (body
         (If0 (Var (0 (n))) (Val (Int 1))
          (Let Int (Binop Sub (Var (0 (n))) (Int 1))
           (Let Int (App (Coderef factorial) (Var (0 (n_minus_1))))
            (Let Int (Binop Mul (Var (2 (n))) (Var (0 (rec_result))))
             (Val (Var (0 (final_result))))))))))))
     (main ((App (Coderef factorial) (Int 5)))))
    -----------module_with_imports-----------
    ((imports
      (((typ (Lollipop Int Int)) (name external_inc))
       ((typ (Lollipop (Prod (Int Int)) Int)) (name external_add))))
     (functions
      (((export true) (name double_inc) (param Int) (return Int)
        (body
         (Let Int (App (Coderef external_inc) (Var (0 (x))))
          (App (Coderef external_inc) (Var (0 (first_inc)))))))))
     (main ((App (Coderef double_inc) (Int 5)))))
    -----------complex_example-----------
    ((imports ())
     (functions
      (((export true) (name process_pair) (param (Prod (Int Int))) (return Int)
        (body
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
                   (Val (Var (0 (final_result))))))))))))))))))
     (main ((App (Coderef process_pair) (Tuple ((Int 3) (Int 4)))))))
    -----------closure_example-----------
    ((imports ())
     (functions
      (((export true) (name make_adder) (param Int) (return (Lollipop Int Int))
        (body (Val (Lam Int Int (Binop Add (Var (1 (n))) (Var (0 (x))))))))))
     (main
      ((Let (Lollipop Int Int) (App (Coderef make_adder) (Int 5))
        (App (Var (0 (add5))) (Int 10)))))) |}]
