open! Base
open Richwasm_lin_lang.Syntax
open Richwasm_lin_lang.Index
open Stdlib.Format

let do_thing x =
  x |> Index.compile_module |> function
  | Ok x -> x
  | Error _ -> failwith "unexpected"

let%expect_test "basic indexing" =
  let do_thing x = x |> do_thing |> printf "@.%a@." Indexed.pp_modul in

  do_thing
    Types.(
      Module ([], [], Some (Let (("a", Int), Val (Int 10), Val (Var "a")))));
  [%expect
    {| (Module ([], [], (Some (Let (Int, (Val (Int 10)), (Val (Var (0, (Some "a"))))))))) |}];

  do_thing
    Types.(
      Module
        ( [],
          [
            TopLevel
              ( true,
                ("foo", Lollipop (Int, Int)),
                Val (Lam (("x", Int), Int, Val (Int 10))) );
          ],
          None ));
  [%expect
    {| (Module ([], [(TopLevel (true, ("foo", (Lollipop (Int, Int))), (Val (Lam (Int, Int, (Val (Int 10)))))))], None)) |}]

let%expect_test "indexes examples" =
  let examples = Examples.all in
  let fmt = std_formatter in
  pp_set_margin fmt 80;
  pp_set_max_indent fmt 80;
  examples
  |> List.iter ~f:(fun (n, m) ->
         let res = m |> do_thing in
         printf "-----------%s-----------@.%a@." n Indexed.pp_modul res);
  [%expect
    {|
    -----------add_one_program-----------
    (Module ([],
       [(TopLevel (true, ("add_one", (Lollipop (Int, Int))),
           (Val (Lam (Int, Int, (Binop (`Add, (Var (0, (Some "x"))), (Int 1))))))))
         ],
       (Some (App ((Global "add_one"), (Int 42))))))
    -----------swap_pair_program-----------
    (Module ([],
       [(TopLevel (true,
           ("swap", (Lollipop ((Prod (Int, Int)), (Prod (Int, Int))))),
           (Val
              (Lam ((Prod (Int, Int)), (Prod (Int, Int)),
                 (LetPair (Int, Int, (Val (Var (0, (Some "p")))),
                    (Val (Prod ((Var (0, (Some "y"))), (Var (1, (Some "x"))))))))
                 )))
           ))
         ],
       (Some (App ((Global "swap"), (Prod ((Int 1), (Int 2))))))))
    -----------compose_program-----------
    (Module ([],
       [(TopLevel (true,
           ("compose",
            (Lollipop ((Lollipop (Int, Int)),
               (Lollipop ((Lollipop (Int, Int)), (Lollipop (Int, Int))))))),
           (Val
              (Lam ((Lollipop (Int, Int)),
                 (Lollipop ((Lollipop (Int, Int)), (Lollipop (Int, Int)))),
                 (Val
                    (Lam ((Lollipop (Int, Int)), (Lollipop (Int, Int)),
                       (Val
                          (Lam (Int, Int,
                             (Let (Int,
                                (App ((Var (1, (Some "g"))), (Var (0, (Some "x")))
                                   )),
                                (App ((Var (3, (Some "f"))),
                                   (Var (0, (Some "g_result")))))
                                ))
                             )))
                       )))
                 )))
           ))
         ],
       None))
    -----------reference_example-----------
    (Module ([],
       [(TopLevel (false, ("test_ref", Int),
           (Let ((Ref Int), (New (Int 10)),
              (Let (Int, (Swap ((Var (0, (Some "r"))), (Int 20))),
                 (Let (Int, (Free (Var (1, (Some "r")))),
                    (Val (Var (1, (Some "old_val"))))))
                 ))
              ))
           ))
         ],
       (Some (Val (Global "test_ref")))))
    -----------factorial_program-----------
    (Module ([],
       [(TopLevel (true, ("factorial", (Lollipop (Int, Int))),
           (Val
              (Lam (Int, Int,
                 (If0 ((Var (0, (Some "n"))), (Val (Int 1)),
                    (Let (Int, (Binop (`Sub, (Var (0, (Some "n"))), (Int 1))),
                       (Let (Int,
                          (App ((Global "factorial"), (Var (0, (Some "n_minus_1")))
                             )),
                          (Let (Int,
                             (Binop (`Mul, (Var (2, (Some "n"))),
                                (Var (0, (Some "rec_result"))))),
                             (Val (Var (0, (Some "final_result"))))))
                          ))
                       ))
                    ))
                 )))
           ))
         ],
       (Some (App ((Global "factorial"), (Int 5))))))
    -----------module_with_imports-----------
    (Module (
       [(Import ((Lollipop (Int, Int)), "external_inc"));
         (Import ((Lollipop ((Prod (Int, Int)), Int)), "external_add"))],
       [(TopLevel (true, ("double_inc", (Lollipop (Int, Int))),
           (Val
              (Lam (Int, Int,
                 (Let (Int, (App ((Global "external_inc"), (Var (0, (Some "x"))))),
                    (App ((Global "external_inc"), (Var (0, (Some "first_inc")))))
                    ))
                 )))
           ))
         ],
       (Some (App ((Global "double_inc"), (Int 5))))))
    -----------complex_example-----------
    (Module ([],
       [(TopLevel (true, ("process_pair", (Lollipop ((Prod (Int, Int)), Int))),
           (Val
              (Lam ((Prod (Int, Int)), Int,
                 (LetPair (Int, Int, (Val (Var (0, (Some "input")))),
                    (Let (Int,
                       (Binop (`Add, (Var (1, (Some "a"))), (Var (0, (Some "b"))))),
                       (Let ((Ref Int), (New (Var (0, (Some "sum")))),
                          (Let (Int,
                             (Binop (`Mul, (Var (3, (Some "a"))),
                                (Var (2, (Some "b"))))),
                             (Let ((Ref Int), (New (Var (0, (Some "product")))),
                                (Let (Int,
                                   (Swap ((Var (2, (Some "r1"))), (Int 0))),
                                   (Let (Int,
                                      (Swap ((Var (1, (Some "r2"))), (Int 0))),
                                      (Let (Int, (Free (Var (4, (Some "r1")))),
                                         (Let (Int, (Free (Var (3, (Some "r2")))),
                                            (Let (Int,
                                               (Binop (`Add,
                                                  (Var (3, (Some "sum_val"))),
                                                  (Var (2, (Some "prod_val"))))),
                                               (Val
                                                  (Var (0, (Some "final_result"))))
                                               ))
                                            ))
                                         ))
                                      ))
                                   ))
                                ))
                             ))
                          ))
                       ))
                    ))
                 )))
           ))
         ],
       (Some (App ((Global "process_pair"), (Prod ((Int 3), (Int 4))))))))
    -----------closure_example-----------
    (Module ([],
       [(TopLevel (true, ("make_adder", (Lollipop (Int, (Lollipop (Int, Int))))),
           (Val
              (Lam (Int, (Lollipop (Int, Int)),
                 (Val
                    (Lam (Int, Int,
                       (Binop (`Add, (Var (1, (Some "n"))), (Var (0, (Some "x")))))
                       )))
                 )))
           ))
         ],
       (Some (Let ((Lollipop (Int, Int)), (App ((Global "make_adder"), (Int 5))),
                (App ((Var (0, (Some "add5"))), (Int 10))))))
       )) |}]
