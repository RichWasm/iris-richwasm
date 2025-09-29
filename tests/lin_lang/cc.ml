open! Base
open! Stdlib.Format
open! Richwasm_lin_lang
open Cc

let do_thing (x : Syntax.Module.t) =
  x
  |> Index.Compile.compile_module
  |> ( function
  | Ok x -> x
  | Error err -> failwith @@ asprintf "%a" Index.Err.pp err )
  |> Cc.Compile.compile_module
  |> function
  | Ok x -> x
  | Error err -> failwith @@ asprintf "%a" Cc.Compile.Err.pp err

let%expect_test "simple" =
  pp_set_margin std_formatter 80;
  pp_set_max_indent std_formatter 80;

  let output x = x |> do_thing |> printf "%a" Cc.IR.Module.pp in
  let mk = Syntax.Module.make in
  output (mk ());
  [%expect {| ((imports ()) (functions ()) (main ())) |}];

  output (mk ~main:(Val (Lam (("x", Int), Int, Val (Int 69)))) ());
  [%expect
    {|
    ((imports ())
     (functions
      (((export false) (name lam_1) (closure (Prod ())) (param Int) (return Int)
        (body (Split () (Val (Var (1 ()))) (Val (Int 69)))))))
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
     (functions
      (((export false) (name lam_1) (closure (Prod (Int))) (param Int) (return Int)
        (body
         (Split (Int) (Val (Var (1 ()))) (Binop Add (Var (0 (x))) (Var (2 (y)))))))))
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
     (functions
      (((export false) (name lam_1) (closure (Prod (Int Int))) (param Int)
        (return Int)
        (body
         (Split (Int Int) (Val (Var (1 ())))
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
                     Split
                       ( [ ("a", Int); ("b", Int) ],
                         Val (Tuple [ Var "x"; Var "y" ]),
                         Binop (Add, Var "a", Var "b") ) )) ))
       ());
  [%expect
    {|
    ((imports ())
     (functions
      (((export false) (name lam_1) (closure (Prod (Int))) (param Int) (return Int)
        (body
         (Split (Int) (Val (Var (1 ())))
          (Split (Int Int) (Val (Tuple ((Var (0 (x))) (Var (2 (y))))))
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
     (functions
      (((export false) (name lam_1) (closure (Prod ())) (param Int) (return Int)
        (body (Split () (Val (Var (1 ()))) (Binop Add (Var (0 (x))) (Int 1)))))))
     (main
      ((Let (Exists (Lollipop ((Var 0) Int) Int))
        (Val
         (Pack (Prod ()) (Tuple ((Coderef lam_1) (Tuple ())))
          (Exists (Lollipop ((Var 0) Int) Int))))
        (Unpack (Var (0 (add1)))
         (Split ((Lollipop ((Var 0) Int) Int) (Var 0)) (Val (Var (0 ())))
          (App (Var (1 ())) (Tuple ((Var (0 ())) (Int 10)))))
         Int))))) |}]

let%expect_test "examples" =
  let examples = Examples.all in
  let fmt = std_formatter in
  pp_set_margin fmt 80;
  pp_set_max_indent fmt 80;
  examples
  |> List.iter ~f:(fun (n, m) ->
         try
           do_thing m |> printf "-----------%s-----------@.%a@." n IR.Module.pp
         with Failure msg -> printf "-----------%s-----------@.%s@." n msg);
  [%expect
    {|
    -----------simple_app_lambda-----------
    ((imports ())
     (functions
      (((export false) (name lam_1) (closure (Prod ())) (param Int) (return Int)
        (body (Split () (Val (Var (1 ()))) (Val (Var (0 (x)))))))))
     (main
      ((Unpack
        (Pack (Prod ()) (Tuple ((Coderef lam_1) (Tuple ())))
         (Exists (Lollipop ((Var 0) Int) Int)))
        (Split ((Lollipop ((Var 0) Int) Int) (Var 0)) (Val (Var (0 ())))
         (App (Var (1 ())) (Tuple ((Var (0 ())) (Int 10)))))
        Int))))
    -----------add_one_program-----------
    ((imports ())
     (functions
      (((export true) (name add-one) (closure (Prod ())) (param Int) (return Int)
        (body (Binop Add (Var (0 (x))) (Int 1))))))
     (main
      ((Unpack
        (Pack (Prod ()) (Tuple ((Coderef add-one) (Tuple ())))
         (Exists (Lollipop ((Var 0) Int) Int)))
        (Split ((Lollipop ((Var 0) Int) Int) (Var 0)) (Val (Var (0 ())))
         (App (Var (1 ())) (Tuple ((Var (0 ())) (Int 42)))))
        Int))))
    -----------add_tup_ref-----------
    ((imports ()) (functions ())
     (main
      ((Let (Ref Int) (New (Int 2))
        (Split (Int (Ref Int)) (Val (Tuple ((Int 1) (Var (0 (r))))))
         (Let Int (Free (Var (0 (x2)))) (Binop Add (Var (2 (x1))) (Var (0 (x2'))))))))))
    -----------print_10-----------
    ((imports (((typ (Exists (Lollipop ((Var 0) Int) (Prod ())))) (name print))))
     (functions ())
     (main
      ((Unpack
        (Pack (Prod ()) (Tuple ((Coderef print) (Tuple ())))
         (Exists (Lollipop ((Var 0) Int) (Prod ()))))
        (Split ((Lollipop ((Var 0) Int) (Prod ())) (Var 0)) (Val (Var (0 ())))
         (App (Var (1 ())) (Tuple ((Var (0 ())) (Int 10)))))
        (Prod ())))))
    -----------factorial_program-----------
    ((imports ())
     (functions
      (((export true) (name factorial) (closure (Prod ())) (param Int) (return Int)
        (body
         (If0 (Var (0 (n))) (Val (Int 1))
          (Let Int (Binop Sub (Var (0 (n))) (Int 1))
           (Let Int
            (Unpack
             (Pack (Prod ()) (Tuple ((Coderef factorial) (Tuple ())))
              (Exists (Lollipop ((Var 0) Int) Int)))
             (Split ((Lollipop ((Var 0) Int) Int) (Var 0)) (Val (Var (0 ())))
              (App (Var (1 ())) (Tuple ((Var (0 ())) (Var (0 (n-sub1)))))))
             Int)
            (Binop Mul (Var (2 (n))) (Var (0 (rec-res)))))))))))
     (main
      ((Unpack
        (Pack (Prod ()) (Tuple ((Coderef factorial) (Tuple ())))
         (Exists (Lollipop ((Var 0) Int) Int)))
        (Split ((Lollipop ((Var 0) Int) Int) (Var 0)) (Val (Var (0 ())))
         (App (Var (1 ())) (Tuple ((Var (0 ())) (Int 5)))))
        Int))))
    -----------safe_div-----------
    ((imports ())
     (functions
      (((export false) (name safe_div) (closure (Prod ())) (param (Prod (Int Int)))
        (return (Sum (Int (Prod ()))))
        (body
         (Split (Int Int) (Val (Var (0 (p))))
          (If0 (Var (0 (y))) (Val (Inj 1 (Tuple ()) (Sum (Int (Prod ())))))
           (Let Int (Binop Div (Var (1 (x))) (Var (0 (y))))
            (Val (Inj 0 (Var (0 (q))) (Sum (Int (Prod ()))))))))))
       ((export false) (name from_either) (closure (Prod ()))
        (param (Sum (Int (Prod ())))) (return Int)
        (body
         (Cases (Var (0 (e)))
          ((Int (Val (Var (0 (ok))))) ((Prod ()) (Val (Int 0)))))))))
     (main
      ((Let (Sum (Int (Prod ())))
        (Unpack
         (Pack (Prod ()) (Tuple ((Coderef safe_div) (Tuple ())))
          (Exists (Lollipop ((Var 0) (Prod (Int Int))) (Sum (Int (Prod ()))))))
         (Split
          ((Lollipop ((Var 0) (Prod (Int Int))) (Sum (Int (Prod ())))) (Var 0))
          (Val (Var (0 ())))
          (App (Var (1 ())) (Tuple ((Var (0 ())) (Tuple ((Int 10) (Int 0)))))))
         (Sum (Int (Prod ()))))
        (Unpack
         (Pack (Prod ()) (Tuple ((Coderef from_either) (Tuple ())))
          (Exists (Lollipop ((Var 0) (Sum (Int (Prod ())))) Int)))
         (Split ((Lollipop ((Var 0) (Sum (Int (Prod ())))) Int) (Var 0))
          (Val (Var (0 ())))
          (App (Var (1 ())) (Tuple ((Var (0 ())) (Var (0 (r)))))))
         Int)))))
    -----------incr_n-----------
    ((imports ())
     (functions
      (((export false) (name incr_1) (closure (Prod ())) (param (Ref Int))
        (return (Ref Int))
        (body
         (Split (Int (Ref Int)) (Swap (Var (0 (r))) (Int 0))
          (Let Int (Binop Add (Var (1 (old))) (Int 1))
           (Let (Prod (Int (Ref Int))) (Swap (Var (1 (r1))) (Var (0 (new))))
            (Split (Int (Ref Int)) (Val (Var (0 (p2)))) (Val (Var (0 (r2))))))))))
       ((export true) (name incr_n) (closure (Prod ()))
        (param (Prod ((Ref Int) Int))) (return Int)
        (body
         (Split ((Ref Int) Int) (Val (Var (0 (p))))
          (If0 (Var (0 (n))) (Free (Var (1 (r))))
           (Let (Ref Int)
            (Unpack
             (Pack (Prod ()) (Tuple ((Coderef incr_1) (Tuple ())))
              (Exists (Lollipop ((Var 0) (Ref Int)) (Ref Int))))
             (Split ((Lollipop ((Var 0) (Ref Int)) (Ref Int)) (Var 0))
              (Val (Var (0 ())))
              (App (Var (1 ())) (Tuple ((Var (0 ())) (Var (1 (r)))))))
             (Ref Int))
            (Let Int (Binop Sub (Var (1 (n))) (Int 1))
             (Unpack
              (Pack (Prod ()) (Tuple ((Coderef incr_n) (Tuple ())))
               (Exists (Lollipop ((Var 0) (Prod ((Ref Int) Int))) Int)))
              (Split ((Lollipop ((Var 0) (Prod ((Ref Int) Int))) Int) (Var 0))
               (Val (Var (0 ())))
               (App (Var (1 ()))
                (Tuple ((Var (0 ())) (Tuple ((Var (1 (r1))) (Var (0 (n1)))))))))
              Int)))))))))
     (main
      ((Let (Ref Int) (New (Int 10))
        (Unpack
         (Pack (Prod ()) (Tuple ((Coderef incr_n) (Tuple ())))
          (Exists (Lollipop ((Var 0) (Prod ((Ref Int) Int))) Int)))
         (Split ((Lollipop ((Var 0) (Prod ((Ref Int) Int))) Int) (Var 0))
          (Val (Var (0 ())))
          (App (Var (1 ()))
           (Tuple ((Var (0 ())) (Tuple ((Var (0 (r0))) (Int 3)))))))
         Int))))) |}]
