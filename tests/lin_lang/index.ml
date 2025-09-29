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
  [%expect
    {|
    -----------simple_app_lambda-----------
    ((imports ()) (functions ())
     (main ((App (Lam Int Int (Val (Var (0 (x))))) (Int 10)))))
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
        (Split (Int (Ref Int)) (Val (Tuple ((Int 1) (Var (0 (r))))))
         (Let Int (Free (Var (0 (x2)))) (Binop Add (Var (2 (x1))) (Var (0 (x2'))))))))))
    -----------print_10-----------
    ((imports (((typ (Lollipop Int (Prod ()))) (name print)))) (functions ())
     (main ((App (Coderef print) (Int 10)))))
    -----------factorial_program-----------
    ((imports ())
     (functions
      (((export true) (name factorial) (param Int) (return Int)
        (body
         (If0 (Var (0 (n))) (Val (Int 1))
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
         (Split (Int Int) (Val (Var (0 (p))))
          (If0 (Var (0 (y))) (Val (Inj 1 (Tuple ()) (Sum (Int (Prod ())))))
           (Let Int (Binop Div (Var (1 (x))) (Var (0 (y))))
            (Val (Inj 0 (Var (0 (q))) (Sum (Int (Prod ()))))))))))
       ((export false) (name from_either) (param (Sum (Int (Prod ()))))
        (return Int)
        (body
         (Cases (Var (0 (e)))
          ((Int (Val (Var (0 (ok))))) ((Prod ()) (Val (Int 0)))))))))
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
            (Split (Int (Ref Int)) (Val (Var (0 (p2)))) (Val (Var (0 (r2))))))))))
       ((export true) (name incr_n) (param (Prod ((Ref Int) Int))) (return Int)
        (body
         (Split ((Ref Int) Int) (Val (Var (0 (p))))
          (If0 (Var (0 (n))) (Free (Var (1 (r))))
           (Let (Ref Int) (App (Coderef incr_1) (Var (1 (r))))
            (Let Int (Binop Sub (Var (1 (n))) (Int 1))
             (App (Coderef incr_n) (Tuple ((Var (1 (r1))) (Var (0 (n1))))))))))))))
     (main
      ((Let (Ref Int) (New (Int 10))
        (App (Coderef incr_n) (Tuple ((Var (0 (r0))) (Int 3)))))))) |}]
