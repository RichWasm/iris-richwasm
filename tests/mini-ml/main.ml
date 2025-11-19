open! Base
open! Richwasm_mini_ml
open Stdlib.Format
open Syntax.Source
open Parse

let pipeline x = x |> Convert.cc_module |> Codegen.compile_module

let run name ast =
  ast
  |> pipeline
  |> printf "%s\n%a\n---\n" name Richwasm_common.Syntax.Module.pp

let run_str name source = source |> from_string_exn |> run name
let one = Module.Module ([], [], Some (Expr.Int 1))

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
  id_fun
  (module
           (func
               (forall.type (VALTYPE (ptr, excopy, exdrop))(ref (base gc)
                                                             (prod
                                                               (ser
                                                                 (ref (base gc)
                                                                   (prod)))
                                                               (ser (var 0))))
               -> (var 0)) (local ptr ptr)
             local.get 0 move
             copy
             local.set 0
             load (Path [1]) follow
             local.set 1
             local.get 1 move
             copy
             local.set 1
             local.get 1 move
             drop)
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
  return_one
  (module
               (func
                   ((ref (base gc)
                      (prod (ser (ref (base gc) (prod)))
                        (ser (ref (base gc) (prod)))))
                   -> i31) (local ptr ptr)
                 local.get 0 move
                 copy
                 local.set 0
                 load (Path [1]) follow
                 local.set 1
                 i32.const 1
                 tag
                 local.get 1 move
                 drop)
               (func ((ref (base gc) (prod)) -> (ref (base gc) (prod))) (local
                   ptr ptr ptr ptr)
                 group 0
                 new gc
                 coderef 0
                 group 2
                 new gc
                 pack (Type (ref (base gc) (prod)))
                   (ref (base gc)
                     (exists type (VALTYPE (ptr, excopy, exdrop))
                       (ref (base gc)
                         (prod (ser (var 0))
                           (ser
                             (coderef
                               ((ref (base gc)
                                  (prod (ser (var 0))
                                    (ser (ref (base gc) (prod)))))
                               -> i31)))))))
                 new gc
                 load (Path []) follow
                 unpack (<1> -> i31) (LocalFx [(1, (prod))])
                   local.set 1
                   local.get 1 move
                   copy
                   local.set 1
                   load (Path [0]) follow
                   local.set 2
                   local.get 1 move
                   copy
                   local.set 1
                   load (Path [1]) follow
                   local.set 3
                   group 0
                   new gc
                   local.get 3 move
                   copy
                   local.set 3
                   call_indirect
                   local.get 3 move
                   drop
                   local.get 2 move
                   drop
                   local.get 1 move
                   drop
                 end)
               (table)
               (export 0 1))
  ---|}]

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
  apply_id
  (module
             (func
                 (forall.type (VALTYPE (ptr, excopy, exdrop))(ref (base gc)
                                                               (prod
                                                                 (ser
                                                                   (ref
                                                                     (base gc)
                                                                     (prod)))
                                                                 (ser (var 0))))
                 -> (var 0)) (local ptr ptr)
               local.get 0 move
               copy
               local.set 0
               load (Path [1]) follow
               local.set 1
               local.get 1 move
               copy
               local.set 1
               local.get 1 move
               drop)
             (func ((ref (base gc) (prod)) -> (ref (base gc) (prod))) (local
                 ptr ptr ptr ptr)
               group 0
               new gc
               coderef 0
               group 2
               new gc
               pack (Type (ref (base gc) (prod)))
                 (ref (base gc)
                   (exists type (VALTYPE (ptr, excopy, exdrop))
                     (ref (base gc)
                       (prod (ser (var 0))
                         (ser
                           (coderef
                             (forall.type (VALTYPE (ptr, excopy, exdrop))
                             (ref (base gc) (prod (ser (var 1)) (ser (var 0))))
                             -> (var 0))))))))
               new gc
               load (Path []) follow
               unpack (<1> -> i31) (LocalFx [(1, (prod))])
                 local.set 1
                 local.get 1 move
                 copy
                 local.set 1
                 load (Path [0]) follow
                 local.set 2
                 local.get 1 move
                 copy
                 local.set 1
                 load (Path [1]) follow
                 local.set 3
                 i32.const 42
                 tag
                 local.get 3 move
                 copy
                 local.set 3
                 call_indirect
                 local.get 3 move
                 drop
                 local.get 2 move
                 drop
                 local.get 1 move
                 drop
               end)
             (table)
             (export 0 1))
  --- |}]

let tuple_and_project =
  Module.Module
    ([], [], Some (Expr.Project (1, Expr.Tuple [ Expr.Int 42; Expr.Int 7 ])))

let%expect_test "tuple_and_project" =
  run "tuple_and_project" tuple_and_project;
  [%expect
    {|
  tuple_and_project
  (module
                      (func ((ref (base gc) (prod)) -> (ref (base gc) (prod)))
                          (local ptr)
                        i32.const 7
                        tag
                        i32.const 42
                        tag
                        group 2
                        new gc
                        load (Path [1]) follow)
                      (table)
                      (export 0))
  --- |}]

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
  opt_case
  (module
             (func ((ref (base gc) (prod)) -> (ref (base gc) (prod))) (local
                 ptr ptr ptr ptr)
               i32.const 42
               tag
               inject gc 1 (ref (base gc) (prod)) i31
               local.set 1
               local.get 1 move
               copy
               local.set 1
               case (<1> -> i31) (LocalFx [])
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
               local.get 1 move
               drop)
             (table)
             (export 0))
  --- |}]

let%expect_test "poly len" =
  run_str "len"
    {|
  (export (len : ((a) (rec (b) (+ (*) (+ a b))) -> int))
    (fun (a) (x : (rec (b) (+ (*) (+ a b)))) : int
      (cases (unfold x)
        ((_ : (*)) 0)
        ((y : (+ a (rec (b) (+ (*) (+ a b)))))
          (op + 1 (app len (a) (fold (rec (b) (+ (*) (+ a b))) y)))))))

  (app len (int)
    (fold (rec (b) (+ (*) (+ int b)))
      (inj 1 (tup 1 (fold (rec (b) (+ (*) (+ int b))) (inj 0 (tup) : (+ (*) int))))
        : (+ (*) (+ int (rec (b) (+ (*) (+ int b))))))))
  |};
  [%expect
    {|
  len
  (module
        (func
            (forall.type (VALTYPE (ptr, excopy, exdrop))(ref (base gc)
                                                          (prod
                                                            (ser
                                                              (ref (base gc)
                                                                (prod)))
                                                            (ser
                                                              (rec
                                                                (VALTYPE (ptr,
                                                                   excopy,
                                                                   exdrop))
                                                                (ref (base gc)
                                                                  (sum
                                                                    (ser
                                                                      (ref
                                                                      (base gc)
                                                                      (prod)))
                                                                    (ser
                                                                      (ref
                                                                      (base gc)
                                                                      (sum
                                                                      (ser
                                                                      (var 1))
                                                                      (ser
                                                                      (var 0)))))))))))
            -> i31) (local ptr ptr ptr ptr ptr ptr ptr)
          local.get 0 move
          copy
          local.set 0
          load (Path [1]) follow
          local.set 1
          local.get 1 move
          copy
          local.set 1
          unfold
          case (<1> -> i31) (LocalFx [(3, (prod))])
            (0
              local.set 6
              i32.const 0
              tag
              local.get 6 move
              drop)
            (1
              local.set 2
              i32.const 1
              tag
              untag
              group 0
              new gc
              coderef 0
              group 2
              new gc
              pack (Type (ref (base gc) (prod)))
                (ref (base gc)
                  (exists type (VALTYPE (ptr, excopy, exdrop))
                    (ref (base gc)
                      (prod (ser (var 0))
                        (ser
                          (coderef
                            (forall.type (VALTYPE (ptr, excopy, exdrop))
                            (ref (base gc)
                              (prod (ser (var 1))
                                (ser
                                  (rec (VALTYPE (ptr, excopy, exdrop))
                                    (ref (base gc)
                                      (sum (ser (ref (base gc) (prod)))
                                        (ser
                                          (ref (base gc)
                                            (sum (ser (var 1)) (ser (var 0)))))))))))
                            -> i31)))))))
              new gc
              load (Path []) follow
              unpack (<1> -> i31) (LocalFx [(3, (prod))])
                local.set 3
                local.get 3 move
                copy
                local.set 3
                load (Path [0]) follow
                local.set 4
                local.get 3 move
                copy
                local.set 3
                load (Path [1]) follow
                local.set 5
                local.get 2 move
                copy
                local.set 2
                fold
                  (rec (VALTYPE (ptr, excopy, exdrop))
                    (ref (base gc)
                      (sum (ser (ref (base gc) (prod)))
                        (ser (ref (base gc) (sum (ser (var 2)) (ser (var 0))))))))
                local.get 5 move
                copy
                local.set 5
                call_indirect
                local.get 5 move
                drop
                local.get 4 move
                drop
                local.get 3 move
                drop
              end
              untag
              i32.add
              tag
              local.get 2 move
              drop)
          end
          local.get 1 move
          drop)
        (func ((ref (base gc) (prod)) -> (ref (base gc) (prod))) (local ptr ptr
            ptr ptr)
          group 0
          new gc
          coderef 0
          group 2
          new gc
          pack (Type (ref (base gc) (prod)))
            (ref (base gc)
              (exists type (VALTYPE (ptr, excopy, exdrop))
                (ref (base gc)
                  (prod (ser (var 0))
                    (ser
                      (coderef
                        (forall.type (VALTYPE (ptr, excopy, exdrop))(ref
                                                                      (base gc)
                                                                      (prod
                                                                      (ser
                                                                      (var 1))
                                                                      (ser
                                                                      (rec
                                                                      (VALTYPE (
                                                                      ptr,
                                                                      excopy,
                                                                      exdrop))
                                                                      (ref
                                                                      (base gc)
                                                                      (sum
                                                                      (ser
                                                                      (ref
                                                                      (base gc)
                                                                      (prod)))
                                                                      (ser
                                                                      (ref
                                                                      (base gc)
                                                                      (sum
                                                                      (ser
                                                                      (var 1))
                                                                      (ser
                                                                      (var 0)))))))))))
                        -> i31)))))))
          new gc
          load (Path []) follow
          unpack (<1> -> i31) (LocalFx [(1, (prod))])
            local.set 1
            local.get 1 move
            copy
            local.set 1
            load (Path [0]) follow
            local.set 2
            local.get 1 move
            copy
            local.set 1
            load (Path [1]) follow
            local.set 3
            group 0
            new gc
            inject gc 0 (ref (base gc) (prod)) i31
            fold
              (rec (VALTYPE (ptr, excopy, exdrop))
                (ref (base gc)
                  (sum (ser (ref (base gc) (prod)))
                    (ser (ref (base gc) (sum (ser i31) (ser (var 0))))))))
            i32.const 1
            tag
            group 2
            new gc
            inject gc
              1 (ref (base gc) (prod)) (ref (base gc)
                                         (sum (ser i31)
                                           (ser
                                             (rec
                                               (VALTYPE (ptr, excopy, exdrop))
                                               (ref (base gc)
                                                 (sum
                                                   (ser (ref (base gc) (prod)))
                                                   (ser
                                                     (ref (base gc)
                                                       (sum (ser i31)
                                                         (ser (var 0)))))))))))
            fold
              (rec (VALTYPE (ptr, excopy, exdrop))
                (ref (base gc)
                  (sum (ser (ref (base gc) (prod)))
                    (ser (ref (base gc) (sum (ser i31) (ser (var 0))))))))
            local.get 3 move
            copy
            local.set 3
            call_indirect
            local.get 3 move
            drop
            local.get 2 move
            drop
            local.get 1 move
            drop
          end)
        (table)
        (export 0 1))
  --- |}]

let%expect_test "add1" =
  run_str "add1"
    {|
  (export (add1 : (() int -> int))
    (fun () (x : int) : int
      (op + x 1)))
  |};
  [%expect
    {|
    add1
    (module
           (func
               ((ref (base gc) (prod (ser (ref (base gc) (prod))) (ser i31))) ->
               i31) (local ptr ptr)
             local.get 0 move
             copy
             local.set 0
             load (Path [1]) follow
             local.set 1
             local.get 1 move
             copy
             local.set 1
             untag
             i32.const 1
             tag
             untag
             i32.add
             tag
             local.get 1 move
             drop)
           (table)
           (export 0))
    --- |}]

let%expect_test "mini_zip" =
  run_str "mini_zip"
    {|
  (export (mini_zip : ((a b) (* (ref a) (ref b)) -> (ref (* a b))))
    (fun (a b) (x : (* (ref a) (ref b))) : (ref (* a b))
      (new (tup (! (proj 0 x)) (! (proj 1 x))))))
  |};
  [%expect
    {|
    mini_zip
    (module
               (func
                   (forall.type (VALTYPE (ptr, excopy, exdrop))(forall.type (
                                                               VALTYPE (ptr,
                                                                 excopy, exdrop))
                                                               (ref (base gc)
                                                                 (prod
                                                                   (ser
                                                                     (ref
                                                                       (base gc)
                                                                       (prod)))
                                                                   (ser
                                                                     (ref
                                                                       (base gc)
                                                                       (prod
                                                                        (ser
                                                                        (ref
                                                                        (base gc)
                                                                        (ser
                                                                        (var 0))))
                                                                        (ser
                                                                        (ref
                                                                        (base gc)
                                                                        (ser
                                                                        (var 1)))))))))
                                                               ->
                                                               (ref (base gc)
                                                                 (ser
                                                                   (ref (base gc)
                                                                     (prod
                                                                       (ser
                                                                        (var 0))
                                                                       (ser
                                                                        (var 1))))))))
                   (local ptr ptr)
                 local.get 0 move
                 copy
                 local.set 0
                 load (Path [1]) follow
                 local.set 1
                 local.get 1 move
                 copy
                 local.set 1
                 load (Path [1]) follow
                 load (Path []) follow
                 local.get 1 move
                 copy
                 local.set 1
                 load (Path [0]) follow
                 load (Path []) follow
                 group 2
                 new gc
                 new gc
                 local.get 1 move
                 drop)
               (table)
               (export 0))
    --- |}]
