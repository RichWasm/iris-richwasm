open! Base
open Richwasm_mini_ml
open Parse
open Syntax

let parse s =
  s
  |> from_string_exn
  |> Source.Module.sexp_of_t
  |> Sexp.to_string_hum
  |> Stdlib.print_endline

let%expect_test "parse one" =
  parse "1";
  [%expect {| (Module () () ((Int 1))) |}]

let%expect_test "parse id" =
  parse {|
  (export (id : ((a) a -> a))
    (fun (a) (x : a) : a
      x))
  |};
  [%expect
    {|
  (Module ()
   ((Export (id (Fun (foralls (a)) (arg (Var a)) (ret (Var a))))
     (Fun (foralls (a)) (arg (x (Var a))) (ret_type (Var a)) (body (Var x)))))
   ()) |}]

let%expect_test "parse tuple" =
  parse {|(proj 1 (tup -1 1))|};
  [%expect {| (Module () () ((Project 1 (Tuple ((Int -1) (Int 1)))))) |}]
