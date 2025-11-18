open! Base
open! Richwasm_mini_ml
open Stdlib.Format
open Syntax.Source

let pipeline x = x |> Convert.cc_module |> Codegen.compile_module

let run name ast =
  ast
  |> pipeline
  |> printf "%s\n%a\n---\n" name Richwasm_common.Syntax.Module.pp

let one = Module.Module ([], [], Some (Expr.Value (Value.Int 1)))

let%expect_test "test_one" =
  run "one" one;
  [%expect
    {|
  one
  (module
        (func ((ref (base gc) (prod)) -> (ref (base gc) (prod))) (local ptr)
          i32.const 1
          tag)
        (table)
        (export 0))
  ---|}]

let identity =
  Module.Module
    ( [],
      [
        Module.Export
          ( ( "id",
              PreType.Fun
                {
                  foralls = [ "a" ];
                  arg = PreType.Var "a";
                  ret = PreType.Var "a";
                } ),
            Expr.Value
              (Value.Fun
                 {
                   foralls = [ "a" ];
                   arg = ("x", PreType.Var "a");
                   ret_type = PreType.Var "a";
                   body = Expr.Value (Value.Var "x");
                 }) );
      ],
      None )

let%expect_test "id_fun" =
  run "id_fun" identity;
  [%expect
    {|
  id_fun
  (module
           (func
               (forall.type (VALTYPE (ptr, excopy, exdrop))(var 0) -> (var 0))
               (local ptr)
             local.get 0 move
             copy
             local.set 0)
           (table)
           (export 0))
  ---|}]

let return_one =
  Module.Module
    ( [],
      [
        Module.Export
          ( ( "one",
              PreType.Fun
                { foralls = []; arg = PreType.Prod []; ret = PreType.Int } ),
            Expr.Value
              (Value.Fun
                 {
                   foralls = [];
                   arg = ("_", PreType.Prod []);
                   ret_type = PreType.Int;
                   body = Expr.Value (Value.Int 1);
                 }) );
      ],
      Some (Expr.Apply (Value.Var "one", [], Value.Tuple [])) )

let%expect_test "return_one" =
  run "return_one" return_one;
  [%expect ""]
