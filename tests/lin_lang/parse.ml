open Richwasm_lin_lang
open Stdlib.Format

let () =
  pp_set_margin std_formatter 80;
  pp_set_max_indent std_formatter 80

let%expect_test "basic functionality" =
  let suspended = ref (fun () -> ()) in

  let run (s : string) =
    try
      let x = Parse.from_string_exn s in
      printf "%a" Syntax.Module.pp x;
      suspended := fun () -> printf "%a" Syntax.Module.pp_sexp x
    with Failure msg ->
      printf "Failure: %s" msg;
      suspended := fun () -> printf "Failure ^^^"
  in

  let next () = !suspended () in

  (* values *)
  run {| 1 |};
  [%expect {| 1 |}];
  next ();
  [%expect {| ((imports ()) (toplevels ()) (main ((Val (Int 1))))) |}];

  run {| 1 |};
  [%expect {| 1 |}];
  next ();
  [%expect {| ((imports ()) (toplevels ()) (main ((Val (Int 1))))) |}];

  run {| -33 |};
  [%expect {| -33 |}];
  next ();
  [%expect {| ((imports ()) (toplevels ()) (main ((Val (Int -33))))) |}];

  run {| foobar |};
  [%expect {| foobar |}];
  next ();
  [%expect {| ((imports ()) (toplevels ()) (main ((Val (Var foobar))))) |}];

  run {| (lam (x : int) int (1 + 1)) |};
  [%expect {|
    (λ (x : int) : int .
      (1 + 1)) |}];
  next ();
  [%expect
    {|
      ((imports ()) (toplevels ())
       (main ((Val (Lam (x Int) Int (Binop Add (Int 1) (Int 1))))))) |}];

  run {| (λ (x : int) : int . (1 + 1)) |};
  [%expect {|
    (λ (x : int) : int .
      (1 + 1)) |}];
  next ();
  [%expect
    {|
    ((imports ()) (toplevels ())
     (main ((Val (Lam (x Int) Int (Binop Add (Int 1) (Int 1))))))) |}];

  run {| (1 + 1) |};
  [%expect {| (1 + 1) |}];
  next ();
  [%expect
    {| ((imports ()) (toplevels ()) (main ((Binop Add (Int 1) (Int 1))))) |}];

  run {| (tup 1 2 3 4 5) |};
  [%expect {| (1, 2, 3, 4, 5) |}];
  next ();
  [%expect
    {|
    ((imports ()) (toplevels ())
     (main ((Val (Tuple ((Int 1) (Int 2) (Int 3) (Int 4) (Int 5))))))) |}];

  run {| (1, 2, 3, 4, 5) |};
  [%expect {| (1, 2, 3, 4, 5) |}];
  next ();
  [%expect
    {|
    ((imports ()) (toplevels ())
     (main ((Val (Tuple ((Int 1) (Int 2) (Int 3) (Int 4) (Int 5))))))) |}];

  run {| (tup (tup 1 2 3 (tup -4))) |};
  (* prority over app *)
  [%expect {| ((1, 2, 3, (-4))) |}];
  next ();
  [%expect
    {|
    ((imports ()) (toplevels ())
     (main ((Val (Tuple ((Tuple ((Int 1) (Int 2) (Int 3) (Tuple ((Int -4))))))))))) |}];

  (* FIXME: this should work *)
  run {| ((), (1, 2, 3, (-4))) |};
  [%expect {| Failure: Failed (ExpectedBinop ((Field op-f2) (Tag binop)) ,) |}];
  next ();
  [%expect {|
    Failure ^^^ |}];

  (* expressions *)
  run {| (app a b) |};
  [%expect {| (app a b) |}];
  next ();
  [%expect {| ((imports ()) (toplevels ()) (main ((App (Var a) (Var b))))) |}];

  run {| (let (x : int) = 55 in (x + 1)) |};
  [%expect {|
    (let (x : int) = 55 in
    (x + 1)) |}];
  next ();
  [%expect
    {|
    ((imports ()) (toplevels ())
     (main ((Let (x Int) (Val (Int 55)) (Binop Add (Var x) (Int 1)))))) |}];

  run {| (let (x int) 55 (x + 1)) |};
  [%expect {|
    (let (x : int) = 55 in
    (x + 1)) |}];
  next ();
  [%expect
    {|
    ((imports ()) (toplevels ())
     (main ((Let (x Int) (Val (Int 55)) (Binop Add (Var x) (Int 1)))))) |}];

  run
    {| 
      (let (r : (ref int)) = (new 2) in
      (letprod (x1 : int) (x2 : (ref int)) = (tup 1 r) in
      (let (x2' : int) = (free x2) in
        (x1 * x2)))) |};
  [%expect
    {|
    (let (r : (ref int)) = (new 2) in
    (letprod ((x1 : int), (x2 : (ref int))) = (1, r) in
    (let (x2' : int) = (free x2) in
    (x1 × x2)))) |}];
  next ();
  [%expect
    {|
    ((imports ()) (toplevels ())
     (main
      ((Let (r (Ref Int)) (New (Int 2))
        (LetProd ((x1 Int) (x2 (Ref Int))) (Val (Tuple ((Int 1) (Var r))))
         (Let (x2' Int) (Free (Var x2)) (Binop Mul (Var x1) (Var x2)))))))) |}];

  run {| (if0 0 then 67 else 42) |};
  [%expect {| (if 0 then 67 else 42) |}];
  next ();
  [%expect
    {|
    ((imports ()) (toplevels ())
     (main ((If0 (Int 0) (Val (Int 67)) (Val (Int 42)))))) |}];

  run {| (if0 1 (/ 10 2) (* 10 2)) |};
  [%expect {| (if 1 then (10 ÷ 2) else (10 × 2)) |}];
  next ();
  [%expect
    {|
    ((imports ()) (toplevels ())
     (main
      ((If0 (Int 1) (Binop Div (Int 10) (Int 2)) (Binop Mul (Int 10) (Int 2)))))) |}];

  run {| (new (1, 2, 3, 4, 5, 6)) |};
  [%expect {| (new (1, 2, 3, 4, 5, 6)) |}];
  next ();
  [%expect
    {|
    ((imports ()) (toplevels ())
     (main ((New (Tuple ((Int 1) (Int 2) (Int 3) (Int 4) (Int 5) (Int 6))))))) |}];

  run
    {| 
      (let (r1 : (ref int)) = (new 32) in
      (let (r2 : (ref int)) = (new 64) in
      (letprod (r2' : (ref int)) (r1' : (ref int)) = (swap r1 r2) in
      (let (x2 : int) = (free r2') in
      (let (x1 : int) = (free r1') in
      (+ x1 x2)))))) |};
  [%expect
    {|
    (let (r1 : (ref int)) = (new 32) in
    (let (r2 : (ref int)) = (new 64) in
    (letprod ((r2' : (ref int)), (r1' : (ref int))) = (swap r1 r2) in
    (let (x2 : int) = (free r2') in
    (let (x1 : int) = (free r1') in
    (x1 + x2)))))) |}];
  next ();
  [%expect
    {|
    ((imports ()) (toplevels ())
     (main
      ((Let (r1 (Ref Int)) (New (Int 32))
        (Let (r2 (Ref Int)) (New (Int 64))
         (LetProd ((r2' (Ref Int)) (r1' (Ref Int))) (Swap (Var r1) (Var r2))
          (Let (x2 Int) (Free (Var r2'))
           (Let (x1 Int) (Free (Var r1')) (Binop Add (Var x1) (Var x2)))))))))) |}];

  run {| 
    (import (int -o int) as print)

    (print 10) |};
  [%expect {|
    (import (int ⊸ int) as print)

    (app print 10) |}];
  next ();
  [%expect
    {|
    ((imports (((typ (Lollipop Int Int)) (name print)))) (toplevels ())
     (main ((App (Var print) (Int 10))))) |}]
