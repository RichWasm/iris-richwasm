open! Base
open Richwasm_lin_lang
open Index
open Cc
open Stdlib.Format

let do_thing (x : Syntax.Module.t) =
  x
  |> Index.compile_module
  |> ( function
  | Ok x -> x
  | Error _ -> failwith "couldn't index..." )
  |> ClosureConversion.compile_module

let%expect_test "simple" =
  let output x =
    x |> do_thing |> function
    | Ok res -> printf "@.%a@." Closed.pp_modul res
    | Error err -> printf "@.%s@." (ClosureConversion.CCErr.to_string err)
  in
  let open Syntax.Types in
  output (Module ([], [], None));
  [%expect {| (Module ([], [], None)) |}];

  output (Module ([], [], Some (Val (Lam (("x", Int), Int, Val (Int 69))))));
  [%expect
    {|
    (Module ([],
       [(Func (false, "lam_1", [(Prod []); Int], Int,
           (LetTuple ([], (Val (Var (1, None))), (Val (Int 69))))))
         ],
       (Some (Val
                (Pack ((Prod []), (Tuple [(Coderef "lam_1"); (Tuple [])]),
                   (Exists (Lollipop (((Var 0), Int), Int)))))))
       )) |}];

  output
    (Module
       ( [],
         [],
         Some
           (Let
              ( ("y", Int),
                Val (Int 67),
                Val (Lam (("x", Int), Int, Binop (`Add, Var "x", Var "y"))) ))
       ));
  [%expect
    {|
    (Module ([],
       [(Func (false, "lam_1", [(Prod [Int]); Int], Int,
           (LetTuple ([Int], (Val (Var (1, None))),
              (Binop (`Add, (Var (0, (Some "x"))), (Var (2, (Some "y")))))))
           ))
         ],
       (Some (Let (Int, (Val (Int 67)),
                (Val
                   (Pack ((Prod [Int]),
                      (Tuple [(Coderef "lam_1"); (Tuple [(Var (0, (Some "y")))])]),
                      (Exists (Lollipop (((Var 0), Int), Int))))))
                )))
       )) |}];

  output
    (Module
       ( [],
         [],
         Some
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
                               Binop (`Add, Var "x", Var "y"),
                               Binop (`Mul, Var "z", Var "r") ) )) ) )) ));
  [%expect
    {|
    (Module ([],
       [(Func (false, "lam_1", [(Prod [Int; Int]); Int], Int,
           (LetTuple ([Int; Int], (Val (Var (1, None))),
              (Let (Int,
                 (Binop (`Add, (Var (0, (Some "x"))), (Var (3, (Some "y"))))),
                 (Binop (`Mul, (Var (3, (Some "z"))), (Var (0, (Some "r")))))))
              ))
           ))
         ],
       (Some (Let (Int, (Val (Int 420)),
                (Let (Int, (Val (Int 67)),
                   (Val
                      (Pack ((Prod [Int; Int]),
                         (Tuple
                            [(Coderef "lam_1");
                              (Tuple [(Var (0, (Some "y"))); (Var (1, (Some "z")))])
                              ]),
                         (Exists (Lollipop (((Var 0), Int), Int))))))
                   ))
                )))
       )) |}];
  output
    (Module
       ( [],
         [],
         Some
           (Let
              ( ("y", Int),
                Val (Int 67),
                Val
                  (Lam
                     ( ("x", Int),
                       Int,
                       LetProd
                         ( [ ("a", Int); ("b", Int) ],
                           Val (Tuple [ Var "x"; Var "y" ]),
                           Binop (`Add, Var "a", Var "b") ) )) )) ));
  [%expect
    {|
    (Module ([],
       [(Func (false, "lam_1", [(Prod [Int]); Int], Int,
           (LetTuple ([Int], (Val (Var (1, None))),
              (LetTuple ([Int; Int],
                 (Val (Tuple [(Var (0, (Some "x"))); (Var (2, (Some "y")))])),
                 (Binop (`Add, (Var (1, (Some "a"))), (Var (0, (Some "b")))))))
              ))
           ))
         ],
       (Some (Let (Int, (Val (Int 67)),
                (Val
                   (Pack ((Prod [Int]),
                      (Tuple [(Coderef "lam_1"); (Tuple [(Var (0, (Some "y")))])]),
                      (Exists (Lollipop (((Var 0), Int), Int))))))
                )))
       )) |}];
  output
    (Module
       ( [],
         [],
         Some
           (Let
              ( ("add1", Lollipop (Int, Int)),
                Val (Lam (("x", Int), Int, Binop (`Add, Var "x", Int 1))),
                App (Var "add1", Int 10) )) ));
  [%expect
    {|
    (Module ([],
       [(Func (false, "lam_1", [(Prod []); Int], Int,
           (LetTuple ([], (Val (Var (1, None))),
              (Binop (`Add, (Var (0, (Some "x"))), (Int 1)))))
           ))
         ],
       (Some (Let ((Exists (Lollipop (((Var 0), Int), Int))),
                (Val
                   (Pack ((Prod []), (Tuple [(Coderef "lam_1"); (Tuple [])]),
                      (Exists (Lollipop (((Var 0), Int), Int)))))),
                (Unpack ((Var (0, (Some "add1"))),
                   (LetTuple ([(Lollipop (((Var 0), Int), Int)); (Var 0)],
                      (Val (Var (0, None))),
                      (App ((Var (1, None)), (Tuple [(Var (0, None)); (Int 10)])))
                      )),
                   Int))
                )))
       )) |}]

let%expect_test "examples" =
  let examples = Examples.all in
  let fmt = std_formatter in
  pp_set_margin fmt 80;
  pp_set_max_indent fmt 80;
  examples
  |> List.iter ~f:(fun (n, m) ->
         match do_thing m with
         | Ok res ->
             printf "-----------%s-----------@.%a@." n Closed.pp_modul res
         | Error err ->
             printf "-----------%s-----------@.%s@." n
               (ClosureConversion.CCErr.to_string err));
  [%expect
    {|
    -----------add_one_program-----------
    (Module ([],
       [(Func (false, "lam_1", [(Prod []); Int], Int,
           (LetTuple ([], (Val (Var (1, None))),
              (Binop (`Add, (Var (0, (Some "x"))), (Int 1)))))
           ));
         (Let (true, ("add_one", (Exists (Lollipop (((Var 0), Int), Int)))),
            (Val
               (Pack ((Prod []), (Tuple [(Coderef "lam_1"); (Tuple [])]),
                  (Exists (Lollipop (((Var 0), Int), Int))))))
            ))
         ],
       (Some (Unpack (
                (Pack ((Prod []), (Tuple [(Coderef "add_one"); (Tuple [])]),
                   (Exists (Lollipop (((Var 0), Int), Int))))),
                (LetTuple ([(Lollipop (((Var 0), Int), Int)); (Var 0)],
                   (Val (Var (0, None))),
                   (App ((Var (1, None)), (Tuple [(Var (0, None)); (Int 42)]))))),
                Int)))
       ))
    -----------swap_pair_program-----------
    (Module ([],
       [(Func (false, "lam_1", [(Prod []); (Prod [Int; Int])], (Prod [Int; Int]),
           (LetTuple ([], (Val (Var (1, None))),
              (LetTuple ([Int; Int], (Val (Var (0, (Some "p")))),
                 (Val (Tuple [(Var (0, (Some "y"))); (Var (1, (Some "x")))]))))
              ))
           ));
         (Let (true,
            ("swap",
             (Exists (Lollipop (((Var 0), (Prod [Int; Int])), (Prod [Int; Int]))))),
            (Val
               (Pack ((Prod []), (Tuple [(Coderef "lam_1"); (Tuple [])]),
                  (Exists
                     (Lollipop (((Var 0), (Prod [Int; Int])), (Prod [Int; Int]))))
                  )))
            ))
         ],
       (Some (Unpack (
                (Pack ((Prod []), (Tuple [(Coderef "swap"); (Tuple [])]),
                   (Exists
                      (Lollipop (((Var 0), (Prod [Int; Int])), (Prod [Int; Int]))))
                   )),
                (LetTuple (
                   [(Lollipop (((Var 0), (Prod [Int; Int])), (Prod [Int; Int])));
                     (Var 0)],
                   (Val (Var (0, None))),
                   (App ((Var (1, None)),
                      (Tuple [(Var (0, None)); (Tuple [(Int 1); (Int 2)])])))
                   )),
                (Prod [Int; Int]))))
       ))
    -----------compose_program-----------
    (Module ([],
       [(Func (false, "lam_3",
           [(Prod
               [(Exists (Lollipop (((Var 0), Int), Int)));
                 (Exists (Lollipop (((Var 0), Int), Int)))]);
             Int],
           Int,
           (LetTuple (
              [(Exists (Lollipop (((Var 0), Int), Int)));
                (Exists (Lollipop (((Var 0), Int), Int)))],
              (Val (Var (1, None))),
              (Let (Int,
                 (Unpack ((Var (3, (Some "g"))),
                    (LetTuple ([(Lollipop (((Var 0), Int), Int)); (Var 0)],
                       (Val (Var (0, None))),
                       (App ((Var (1, None)),
                          (Tuple [(Var (0, None)); (Var (0, (Some "x")))])))
                       )),
                    Int)),
                 (Unpack ((Var (3, (Some "f"))),
                    (LetTuple ([(Lollipop (((Var 0), Int), Int)); (Var 0)],
                       (Val (Var (0, None))),
                       (App ((Var (1, None)),
                          (Tuple [(Var (0, None)); (Var (0, (Some "g_result")))])))
                       )),
                    Int))
                 ))
              ))
           ));
         (Func (false, "lam_2",
            [(Prod [(Exists (Lollipop (((Var 0), Int), Int)))]);
              (Exists (Lollipop (((Var 0), Int), Int)))],
            (Exists (Lollipop (((Var 0), Int), Int))),
            (LetTuple ([(Exists (Lollipop (((Var 0), Int), Int)))],
               (Val (Var (1, None))),
               (Val
                  (Pack (
                     (Prod
                        [(Exists (Lollipop (((Var 0), Int), Int)));
                          (Exists (Lollipop (((Var 0), Int), Int)))]),
                     (Tuple
                        [(Coderef "lam_3");
                          (Tuple [(Var (0, (Some "g"))); (Var (1, (Some "f")))])]),
                     (Exists (Lollipop (((Var 0), Int), Int))))))
               ))
            ));
         (Func (false, "lam_1",
            [(Prod []); (Exists (Lollipop (((Var 0), Int), Int)))],
            (Exists
               (Lollipop (((Var 0), (Exists (Lollipop (((Var 0), Int), Int)))),
                  (Exists (Lollipop (((Var 0), Int), Int)))))),
            (LetTuple ([], (Val (Var (1, None))),
               (Val
                  (Pack ((Prod [(Exists (Lollipop (((Var 0), Int), Int)))]),
                     (Tuple [(Coderef "lam_2"); (Tuple [(Var (0, (Some "f")))])]),
                     (Exists
                        (Lollipop (
                           ((Var 0), (Exists (Lollipop (((Var 0), Int), Int)))),
                           (Exists (Lollipop (((Var 0), Int), Int))))))
                     )))
               ))
            ));
         (Let (true,
            ("compose",
             (Exists
                (Lollipop (((Var 0), (Exists (Lollipop (((Var 0), Int), Int)))),
                   (Exists
                      (Lollipop (
                         ((Var 0), (Exists (Lollipop (((Var 0), Int), Int)))),
                         (Exists (Lollipop (((Var 0), Int), Int))))))
                   )))),
            (Val
               (Pack ((Prod []), (Tuple [(Coderef "lam_1"); (Tuple [])]),
                  (Exists
                     (Lollipop (
                        ((Var 0), (Exists (Lollipop (((Var 0), Int), Int)))),
                        (Exists
                           (Lollipop (
                              ((Var 0), (Exists (Lollipop (((Var 0), Int), Int)))),
                              (Exists (Lollipop (((Var 0), Int), Int))))))
                        )))
                  )))
            ))
         ],
       None))
    -----------reference_example-----------
    (Module ([],
       [(Let (false, ("test_ref", Int),
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
       [(Func (false, "lam_1", [(Prod []); Int], Int,
           (LetTuple ([], (Val (Var (1, None))),
              (If0 ((Var (0, (Some "n"))), (Val (Int 1)),
                 (Let (Int, (Binop (`Sub, (Var (0, (Some "n"))), (Int 1))),
                    (Let (Int,
                       (Unpack (
                          (Pack ((Prod []),
                             (Tuple [(Coderef "factorial"); (Tuple [])]),
                             (Exists (Lollipop (((Var 0), Int), Int))))),
                          (LetTuple ([(Lollipop (((Var 0), Int), Int)); (Var 0)],
                             (Val (Var (0, None))),
                             (App ((Var (1, None)),
                                (Tuple
                                   [(Var (0, None)); (Var (0, (Some "n_minus_1")))])
                                ))
                             )),
                          Int)),
                       (Let (Int,
                          (Binop (`Mul, (Var (2, (Some "n"))),
                             (Var (0, (Some "rec_result"))))),
                          (Val (Var (0, (Some "final_result"))))))
                       ))
                    ))
                 ))
              ))
           ));
         (Let (true, ("factorial", (Exists (Lollipop (((Var 0), Int), Int)))),
            (Val
               (Pack ((Prod []), (Tuple [(Coderef "lam_1"); (Tuple [])]),
                  (Exists (Lollipop (((Var 0), Int), Int))))))
            ))
         ],
       (Some (Unpack (
                (Pack ((Prod []), (Tuple [(Coderef "factorial"); (Tuple [])]),
                   (Exists (Lollipop (((Var 0), Int), Int))))),
                (LetTuple ([(Lollipop (((Var 0), Int), Int)); (Var 0)],
                   (Val (Var (0, None))),
                   (App ((Var (1, None)), (Tuple [(Var (0, None)); (Int 5)]))))),
                Int)))
       ))
    -----------module_with_imports-----------
    (Module (
       [(Import ((Exists (Lollipop (((Var 0), Int), Int))), "external_inc"));
         (Import ((Exists (Lollipop (((Var 0), (Prod [Int; Int])), Int))),
            "external_add"))
         ],
       [(Func (false, "lam_1", [(Prod []); Int], Int,
           (LetTuple ([], (Val (Var (1, None))),
              (Let (Int,
                 (Unpack (
                    (Pack ((Prod []),
                       (Tuple [(Coderef "external_inc"); (Tuple [])]),
                       (Exists (Lollipop (((Var 0), Int), Int))))),
                    (LetTuple ([(Lollipop (((Var 0), Int), Int)); (Var 0)],
                       (Val (Var (0, None))),
                       (App ((Var (1, None)),
                          (Tuple [(Var (0, None)); (Var (0, (Some "x")))])))
                       )),
                    Int)),
                 (Unpack (
                    (Pack ((Prod []),
                       (Tuple [(Coderef "external_inc"); (Tuple [])]),
                       (Exists (Lollipop (((Var 0), Int), Int))))),
                    (LetTuple ([(Lollipop (((Var 0), Int), Int)); (Var 0)],
                       (Val (Var (0, None))),
                       (App ((Var (1, None)),
                          (Tuple [(Var (0, None)); (Var (0, (Some "first_inc")))])
                          ))
                       )),
                    Int))
                 ))
              ))
           ));
         (Let (true, ("double_inc", (Exists (Lollipop (((Var 0), Int), Int)))),
            (Val
               (Pack ((Prod []), (Tuple [(Coderef "lam_1"); (Tuple [])]),
                  (Exists (Lollipop (((Var 0), Int), Int))))))
            ))
         ],
       (Some (Unpack (
                (Pack ((Prod []), (Tuple [(Coderef "double_inc"); (Tuple [])]),
                   (Exists (Lollipop (((Var 0), Int), Int))))),
                (LetTuple ([(Lollipop (((Var 0), Int), Int)); (Var 0)],
                   (Val (Var (0, None))),
                   (App ((Var (1, None)), (Tuple [(Var (0, None)); (Int 5)]))))),
                Int)))
       ))
    -----------complex_example-----------
    (Module ([],
       [(Func (false, "lam_1", [(Prod []); (Prod [Int; Int])], Int,
           (LetTuple ([], (Val (Var (1, None))),
              (LetTuple ([Int; Int], (Val (Var (0, (Some "input")))),
                 (Let (Int,
                    (Binop (`Add, (Var (1, (Some "a"))), (Var (0, (Some "b"))))),
                    (Let ((Ref Int), (New (Var (0, (Some "sum")))),
                       (Let (Int,
                          (Binop (`Mul, (Var (3, (Some "a"))),
                             (Var (2, (Some "b"))))),
                          (Let ((Ref Int), (New (Var (0, (Some "product")))),
                             (Let (Int, (Swap ((Var (2, (Some "r1"))), (Int 0))),
                                (Let (Int,
                                   (Swap ((Var (1, (Some "r2"))), (Int 0))),
                                   (Let (Int, (Free (Var (4, (Some "r1")))),
                                      (Let (Int, (Free (Var (3, (Some "r2")))),
                                         (Let (Int,
                                            (Binop (`Add,
                                               (Var (3, (Some "sum_val"))),
                                               (Var (2, (Some "prod_val"))))),
                                            (Val (Var (0, (Some "final_result"))))
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
              ))
           ));
         (Let (true,
            ("process_pair",
             (Exists (Lollipop (((Var 0), (Prod [Int; Int])), Int)))),
            (Val
               (Pack ((Prod []), (Tuple [(Coderef "lam_1"); (Tuple [])]),
                  (Exists (Lollipop (((Var 0), (Prod [Int; Int])), Int))))))
            ))
         ],
       (Some (Unpack (
                (Pack ((Prod []), (Tuple [(Coderef "process_pair"); (Tuple [])]),
                   (Exists (Lollipop (((Var 0), (Prod [Int; Int])), Int))))),
                (LetTuple (
                   [(Lollipop (((Var 0), (Prod [Int; Int])), Int)); (Var 0)],
                   (Val (Var (0, None))),
                   (App ((Var (1, None)),
                      (Tuple [(Var (0, None)); (Tuple [(Int 3); (Int 4)])])))
                   )),
                Int)))
       ))
    -----------closure_example-----------
    (Module ([],
       [(Func (false, "lam_2", [(Prod [Int]); Int], Int,
           (LetTuple ([Int], (Val (Var (1, None))),
              (Binop (`Add, (Var (2, (Some "n"))), (Var (0, (Some "x")))))))
           ));
         (Func (false, "lam_1", [(Prod []); Int],
            (Exists (Lollipop (((Var 0), Int), Int))),
            (LetTuple ([], (Val (Var (1, None))),
               (Val
                  (Pack ((Prod [Int]),
                     (Tuple [(Coderef "lam_2"); (Tuple [(Var (0, (Some "n")))])]),
                     (Exists (Lollipop (((Var 0), Int), Int))))))
               ))
            ));
         (Let (true,
            ("make_adder",
             (Exists
                (Lollipop (((Var 0), Int),
                   (Exists (Lollipop (((Var 0), Int), Int))))))),
            (Val
               (Pack ((Prod []), (Tuple [(Coderef "lam_1"); (Tuple [])]),
                  (Exists
                     (Lollipop (((Var 0), Int),
                        (Exists (Lollipop (((Var 0), Int), Int))))))
                  )))
            ))
         ],
       (Some (Let ((Exists (Lollipop (((Var 0), Int), Int))),
                (Unpack (
                   (Pack ((Prod []), (Tuple [(Coderef "make_adder"); (Tuple [])]),
                      (Exists
                         (Lollipop (((Var 0), Int),
                            (Exists (Lollipop (((Var 0), Int), Int))))))
                      )),
                   (LetTuple (
                      [(Lollipop (((Var 0), Int),
                          (Exists (Lollipop (((Var 0), Int), Int)))));
                        (Var 0)],
                      (Val (Var (0, None))),
                      (App ((Var (1, None)), (Tuple [(Var (0, None)); (Int 5)]))))),
                   (Exists (Lollipop (((Var 0), Int), Int))))),
                (Unpack ((Var (0, (Some "add5"))),
                   (LetTuple ([(Lollipop (((Var 0), Int), Int)); (Var 0)],
                      (Val (Var (0, None))),
                      (App ((Var (1, None)), (Tuple [(Var (0, None)); (Int 10)])))
                      )),
                   Int))
                )))
       )) |}]
