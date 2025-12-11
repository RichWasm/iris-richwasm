open! Base
open! Richwasm_mini_ml
open Stdlib.Format
open Syntax.Source
open Parse

let pipeline x = x |> Convert.cc_module |> Codegen.compile_module

let run name ast =
  ast
  |> pipeline
  |> printf "-------[%s]-------@.%a@." name Richwasm_common.Syntax.Module.pp

let to_converted src =
  src
  |> from_string_exn
  |> Convert.cc_module
  |> Syntax.Closed.Module.sexp_of_t
  |> Sexp.to_string_hum
  |> Stdlib.print_endline

let run_str name source = source |> from_string_exn |> run name
let one = Module.Module ([], [], Some (Expr.Int 1))

let%expect_test "test_one" =
  run "one" one;
  [%expect
    {|
  -------[one]-------
  (module
    (func ((ref (base gc) (struct)) -> i31) (local ptr)
      i32.const 1
      tag)
    (table 0)
    (export "_start" (func 0)))|}]

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
            Expr.Fun
              {
                foralls = [ "a" ];
                arg = ("x", PreType.Var "a");
                ret_type = PreType.Var "a";
                body = Expr.Var "x";
              } );
      ],
      None )

let%expect_test "id_fun" =
  run "id_fun" identity;
  [%expect
    {|
  -------[id_fun]-------
  (module
    (func
        (forall.type (VALTYPE (ptr, excopy, exdrop))(ref (base gc)
                                                      (struct
                                                        (ser
                                                          (ref (base gc)
                                                            (struct)))
                                                        (ser (var 0))))
        -> (var 0)) (local ptr ptr ptr)
      local.get 0 move
      copy
      local.set 0
      load (Path [1]) follow
      local.set 1
      drop
      local.get 1 move
      local.set 2
      local.get 2 move
      copy
      local.set 2
      local.get 2 move
      drop)
    (table 0)
    (export "id" (func 0)))|}]

let return_one =
  Module.Module
    ( [],
      [
        Module.Export
          ( ( "one",
              PreType.Fun
                { foralls = []; arg = PreType.Prod []; ret = PreType.Int } ),
            Expr.Fun
              {
                foralls = [];
                arg = ("_", PreType.Prod []);
                ret_type = PreType.Int;
                body = Expr.Int 1;
              } );
      ],
      Some (Expr.Apply (Expr.Var "one", [], Expr.Tuple [])) )

let%expect_test "return_one" =
  run "return_one" return_one;
  [%expect
    {|
  -------[return_one]-------
  (module
    (func
        ((ref (base gc)
           (struct (ser (ref (base gc) (struct)))
             (ser (ref (base gc) (struct)))))
        -> i31) (local ptr ptr ptr)
      local.get 0 move
      copy
      local.set 0
      load (Path [1]) follow
      local.set 1
      drop
      local.get 1 move
      local.set 2
      i32.const 1
      tag
      local.get 2 move
      drop)
    (func ((ref (base gc) (struct)) -> i31) (local ptr ptr ptr ptr ptr ptr)
      group 0
      new gc
      cast (ref (base gc) (struct))
      coderef 0
      group 2
      new gc
      cast
        (ref (base gc)
          (struct (ser (ref (base gc) (struct)))
            (ser
              (exists type (VALTYPE (ptr, excopy, exdrop))
                (ref (base gc)
                  (struct (ser (var 0))
                    (ser
                      (coderef
                        ((ref (base gc)
                           (struct (ser (var 0))
                             (ser (ref (base gc) (struct)))))
                        -> i31)))))))))
      pack (Type (ref (base gc) (struct)))
        (ref (base gc)
          (struct (ser (var 0))
            (ser
              (coderef
                ((ref (base gc)
                   (struct (ser (var 0)) (ser (ref (base gc) (struct)))))
                -> i31)))))
      unpack (<1> -> i31) InferFx
        local.set 1
        local.get 1 move
        copy
        local.set 1
        load (Path [0]) follow
        local.set 2
        drop
        local.get 2 move
        local.set 3
        local.get 1 move
        copy
        local.set 1
        load (Path [1]) follow
        local.set 4
        drop
        local.get 4 move
        local.set 5
        group 0
        new gc
        cast (ref (base gc) (struct))
        local.get 5 move
        copy
        local.set 5
        call_indirect
        local.get 5 move
        drop
        local.get 3 move
        drop
        local.get 1 move
        drop
      end)
    (table 0 1)
    (export "one" (func 0))
    (export "_start" (func 1)))|}]

let apply_id =
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
            Expr.Fun
              {
                foralls = [ "a" ];
                arg = ("x", PreType.Var "a");
                ret_type = PreType.Var "a";
                body = Expr.Var "x";
              } );
      ],
      Some (Expr.Apply (Expr.Var "id", [ PreType.Int ], Expr.Int 42)) )

let%expect_test "apply_id" =
  run "apply_id" apply_id;
  [%expect
    {|
  -------[apply_id]-------
  (module
    (func
        (forall.type (VALTYPE (ptr, excopy, exdrop))(ref (base gc)
                                                      (struct
                                                        (ser
                                                          (ref (base gc)
                                                            (struct)))
                                                        (ser (var 0))))
        -> (var 0)) (local ptr ptr ptr)
      local.get 0 move
      copy
      local.set 0
      load (Path [1]) follow
      local.set 1
      drop
      local.get 1 move
      local.set 2
      local.get 2 move
      copy
      local.set 2
      local.get 2 move
      drop)
    (func ((ref (base gc) (struct)) -> i31) (local ptr ptr ptr ptr ptr ptr)
      group 0
      new gc
      cast (ref (base gc) (struct))
      coderef 0
      group 2
      new gc
      cast
        (ref (base gc)
          (struct (ser (ref (base gc) (struct)))
            (ser
              (exists type (VALTYPE (ptr, excopy, exdrop))
                (ref (base gc)
                  (struct (ser (var 0))
                    (ser
                      (coderef
                        (forall.type (VALTYPE (ptr, excopy, exdrop))(ref
                                                                      (base gc)
                                                                      (struct
                                                                      (ser
                                                                      (var 1))
                                                                      (ser
                                                                      (var 0))))
                        -> (var 0))))))))))
      pack (Type (ref (base gc) (struct)))
        (ref (base gc)
          (struct (ser (var 0))
            (ser
              (coderef
                (forall.type (VALTYPE (ptr, excopy, exdrop))(ref (base gc)
                                                              (struct
                                                                (ser (var 1))
                                                                (ser (var 0))))
                -> (var 0))))))
      unpack (<1> -> i31) InferFx
        local.set 1
        local.get 1 move
        copy
        local.set 1
        load (Path [0]) follow
        local.set 2
        drop
        local.get 2 move
        local.set 3
        local.get 1 move
        copy
        local.set 1
        load (Path [1]) follow
        local.set 4
        drop
        local.get 4 move
        local.set 5
        i32.const 42
        tag
        local.get 5 move
        copy
        local.set 5
        inst (Type i31)
        call_indirect
        local.get 5 move
        drop
        local.get 3 move
        drop
        local.get 1 move
        drop
      end)
    (table 0 1)
    (export "id" (func 0))
    (export "_start" (func 1))) |}]

let tuple_and_project =
  Module.Module
    ([], [], Some (Expr.Project (1, Expr.Tuple [ Expr.Int 42; Expr.Int 7 ])))

let%expect_test "tuple_and_project" =
  run "tuple_and_project" tuple_and_project;
  [%expect
    {|
  -------[tuple_and_project]-------
  (module
    (func ((ref (base gc) (struct)) -> i31) (local ptr ptr)
      i32.const 7
      tag
      i32.const 42
      tag
      group 2
      new gc
      cast (ref (base gc) (struct (ser i31) (ser i31)))
      load (Path [1]) follow
      local.set 1
      drop
      local.get 1 move)
    (table 0)
    (export "_start" (func 0))) |}]

let opt_case =
  let option_type = PreType.Sum [ PreType.Prod []; PreType.Int ] in
  Module.Module
    ( [],
      [],
      Some
        (Expr.Let
           ( ("option", option_type),
             Expr.Inj (1, Expr.Int 42, option_type),
             Expr.Cases
               ( Expr.Var "option",
                 [
                   (("_", PreType.Prod []), Expr.Int 0);
                   (("v", PreType.Int), Expr.Var "v");
                 ] ) )) )

let%expect_test "opt_case" =
  run "opt_case" opt_case;
  [%expect
    {|
  -------[opt_case]-------
  (module
    (func ((ref (base gc) (struct)) -> i31) (local ptr ptr ptr ptr ptr)
      i32.const 42
      tag
      inject_new gc 1 (ref (base gc) (struct)) i31
      local.set 1
      local.get 1 move
      copy
      local.set 1
      case_load
        (<1> ->
        (ref (base gc) (variant (ser (ref (base gc) (struct))) (ser i31))) i31)
        copy InferFx
        (0
          local.set 3
          i32.const 0
          tag
          local.get 3 move
          drop)
        (1
          local.set 2
          local.get 2 move
          copy
          local.set 2
          local.get 2 move
          drop)
      end
      local.set 4
      drop
      local.get 4 move
      local.get 1 move
      drop)
    (table 0)
    (export "_start" (func 0))) |}]
