open! Base
open! Stdlib.Format
open! Richwasm_lin_lang

include Help.MultiOutputter.Make (struct
  type syntax = Syntax.Module.t
  type text = string
  type res = Syntax.Module.t

  let syntax_pipeline x = x
  let string_pipeline s = s |> Parse.from_string_exn |> syntax_pipeline
  let examples = []
  let pp = Syntax.Module.pp
  let pp_sexp = Syntax.Module.pp_sexp
end)

let%expect_test "basic functionality" =
  (* values *)
  run {| 1 |};
  [%expect {| 1 |}];
  next ();
  [%expect {| ((imports ()) (functions ()) (main ((Int 1)))) |}];

  run {| -33 |};
  [%expect {| -33 |}];
  next ();
  [%expect {| ((imports ()) (functions ()) (main ((Int -33)))) |}];

  run {| foobar |};
  [%expect {| foobar |}];
  next ();
  [%expect {| ((imports ()) (functions ()) (main ((Var foobar)))) |}];

  run {| (lam (x : int) int (1 + 1)) |};
  [%expect {|
    (λ (x : int) : int .
      (1 + 1)) |}];
  next ();
  [%expect
    {|
      ((imports ()) (functions ())
       (main ((Lam (x Int) Int (Binop Add (Int 1) (Int 1)))))) |}];

  run {| (λ (x : int) : int . (1 + 1)) |};
  [%expect {|
    (λ (x : int) : int .
      (1 + 1)) |}];
  next ();
  [%expect
    {|
    ((imports ()) (functions ())
     (main ((Lam (x Int) Int (Binop Add (Int 1) (Int 1)))))) |}];

  run {| (1 + 1) |};
  [%expect {| (1 + 1) |}];
  next ();
  [%expect
    {| ((imports ()) (functions ()) (main ((Binop Add (Int 1) (Int 1))))) |}];

  run {| (tup 1 2 3 4 5) |};
  [%expect {| (1, 2, 3, 4, 5) |}];
  next ();
  [%expect
    {|
    ((imports ()) (functions ())
     (main ((Tuple ((Int 1) (Int 2) (Int 3) (Int 4) (Int 5)))))) |}];

  run {| (1, 2, 3, 4, 5) |};
  [%expect {| (1, 2, 3, 4, 5) |}];
  next ();
  [%expect
    {|
    ((imports ()) (functions ())
     (main ((Tuple ((Int 1) (Int 2) (Int 3) (Int 4) (Int 5)))))) |}];

  run {| (tup (tup 1 2 3 (tup -4))) |};
  (* prority over app *)
  [%expect {| ((1, 2, 3, (-4))) |}];
  next ();
  [%expect
    {|
    ((imports ()) (functions ())
     (main ((Tuple ((Tuple ((Int 1) (Int 2) (Int 3) (Tuple ((Int -4)))))))))) |}];

  (* FIXME: this should work *)
  run {| ((), (1, 2, 3, (-4))) |};
  [%expect {| ((), (1, 2, 3, (-4))) |}];
  next ();
  [%expect
    {|
    ((imports ()) (functions ())
     (main
      ((Tuple ((Tuple ()) (Tuple ((Int 1) (Int 2) (Int 3) (Tuple ((Int -4)))))))))) |}];

  (* expressions *)
  run {| (app a b) |};
  [%expect {| (app a b) |}];
  next ();
  [%expect {| ((imports ()) (functions ()) (main ((App (Var a) (Var b))))) |}];

  run {| (let (x : int) = 55 in (x + 1)) |};
  [%expect {|
    (let (x : int) = 55 in
    (x + 1)) |}];
  next ();
  [%expect
    {|
    ((imports ()) (functions ())
     (main ((Let (x Int) (Int 55) (Binop Add (Var x) (Int 1)))))) |}];

  run {| (let (x int) 55 (x + 1)) |};
  [%expect {|
    (let (x : int) = 55 in
    (x + 1)) |}];
  next ();
  [%expect
    {|
    ((imports ()) (functions ())
     (main ((Let (x Int) (Int 55) (Binop Add (Var x) (Int 1)))))) |}];

  run
    {| 
      (let (r : (ref int)) = (new 2) in
      (split (x1 : int) (x2 : (ref int)) = (tup 1 r) in
      (let (x2' : int) = (free x2) in
        (x1 * x2)))) |};
  [%expect
    {|
    (let (r : (ref int)) = (new 2) in
    (split (x1 : int) (x2 : (ref int)) = (1, r) in
    (let (x2' : int) = (free x2) in
    (x1 × x2)))) |}];
  next ();
  [%expect
    {|
    ((imports ()) (functions ())
     (main
      ((Let (r (Ref Int)) (New (Int 2))
        (Split ((x1 Int) (x2 (Ref Int))) (Tuple ((Int 1) (Var r)))
         (Let (x2' Int) (Free (Var x2)) (Binop Mul (Var x1) (Var x2)))))))) |}];

  run {| (if0 0 then 67 else 42) |};
  [%expect {| (if0 0 then 67 else 42) |}];
  next ();
  [%expect
    {|
    ((imports ()) (functions ()) (main ((If0 (Int 0) (Int 67) (Int 42))))) |}];

  run {| (if0 1 (/ 10 2) (* 10 2)) |};
  [%expect {| (if0 1 then (10 ÷ 2) else (10 × 2)) |}];
  next ();
  [%expect
    {|
    ((imports ()) (functions ())
     (main
      ((If0 (Int 1) (Binop Div (Int 10) (Int 2)) (Binop Mul (Int 10) (Int 2)))))) |}];

  run {| (new (1, 2, 3, 4, 5, 6)) |};
  [%expect {| (new (1, 2, 3, 4, 5, 6)) |}];
  next ();
  [%expect
    {|
    ((imports ()) (functions ())
     (main ((New (Tuple ((Int 1) (Int 2) (Int 3) (Int 4) (Int 5) (Int 6))))))) |}];

  run
    {|
      (let (r1 : (ref int)) = (new 32) in
      (let (r2 : (ref int)) = (new 64) in
      (split (r2' : (ref int)) (r1' : (ref int)) = (swap r1 r2) in
      (let (x2 : int) = (free r2') in
      (let (x1 : int) = (free r1') in
      (+ x1 x2)))))) |};
  [%expect
    {|
    (let (r1 : (ref int)) = (new 32) in
    (let (r2 : (ref int)) = (new 64) in
    (split (r2' : (ref int)) (r1' : (ref int)) = (swap r1 r2) in
    (let (x2 : int) = (free r2') in
    (let (x1 : int) = (free r1') in
    (x1 + x2)))))) |}];
  next ();
  [%expect
    {|
    ((imports ()) (functions ())
     (main
      ((Let (r1 (Ref Int)) (New (Int 32))
        (Let (r2 (Ref Int)) (New (Int 64))
         (Split ((r2' (Ref Int)) (r1' (Ref Int))) (Swap (Var r1) (Var r2))
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
    ((imports (((typ (Lollipop Int Int)) (name print)))) (functions ())
     (main ((App (Var print) (Int 10))))) |}]
