open Richwasm_lin_lang
open Syntax
open Index
open Cc
open Format

let do_thing (x : Syntax.Module.t) =
  x |> Index.compile_module |> Result.get_ok |> ClosureConversion.compile_module

let%expect_test "simple" =
  let output x =
    x |> do_thing |> function
    | Ok res -> printf "@.%a@." Declosure.pp_modul res
    | Error err -> printf "@.%s@." (CCErr.to_string err)
  in
  let open Syntax.Types in
  output (Module ([], [], None));
  [%expect {| (Module ([], [], None)) |}];

  output (Module ([], [], Some (Val (Lam (("x", Int), Int, Val (Int 69))))));
  [%expect
    {|
    (Module ([], [(Func (false, "lam_1", [Int], Int, (Val (Int 69))))],
       (Some (Val (Coderef "lam_1"))))) |}];

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
              (Binop (`Add, (Var (1, (Some "x"))), (Var (0, (Some "y")))))))
           ))
         ],
       (Some (Let (Int, (Val (Int 67)),
                (Val
                   (Pack ((Prod [Int]),
                      (Tuple [(Coderef "lam_1"); (Tuple [(Var (0, (Some "y")))])]),
                      (Exists (Lollipop ([(Var 0); Int], Int))))))
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
                 (Binop (`Add, (Var (2, (Some "x"))), (Var (1, (Some "y"))))),
                 (Binop (`Mul, (Var (1, (Some "z"))), (Var (0, (Some "r")))))))
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
                         (Exists (Lollipop ([(Var 0); Int], Int))))))
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
                       LetPair
                         ( ("a", Int),
                           ("b", Int),
                           Val (Prod (Var "x", Var "y")),
                           Binop (`Add, Var "a", Var "b") ) )) )) ));
  [%expect
    {|
    (Module ([],
       [(Func (false, "lam_1", [(Prod [Int]); Int], Int,
           (LetTuple ([Int], (Val (Var (1, None))),
              (LetTuple ([Int; Int],
                 (Val (Tuple [(Var (1, (Some "x"))); (Var (0, (Some "y")))])),
                 (Binop (`Add, (Var (1, (Some "a"))), (Var (0, (Some "b")))))))
              ))
           ))
         ],
       (Some (Let (Int, (Val (Int 67)),
                (Val
                   (Pack ((Prod [Int]),
                      (Tuple [(Coderef "lam_1"); (Tuple [(Var (0, (Some "y")))])]),
                      (Exists (Lollipop ([(Var 0); Int], Int))))))
                )))
       )) |}]

let%expect_test "examples" =
  let examples = Examples.all in
  let fmt = Format.std_formatter in
  Format.pp_set_margin fmt 80;
  Format.pp_set_max_indent fmt 80;
  examples
  |> List.iter (fun (n, m) ->
         match do_thing m with
         | Ok res ->
             printf "-----------%s-----------@.%a@." n Declosure.pp_modul res
         | Error err ->
             printf "-----------%s-----------@.%s@." n (CCErr.to_string err));
  [%expect
    {|
    -----------add_one_program-----------
    (Module ([],
       [(Func (false, "lam_1", [Int], Int,
           (Binop (`Add, (Var (0, (Some "x"))), (Int 1)))));
         (Let (true, ("add_one", (Lollipop ([Int], Int))), (Val (Coderef "lam_1"))
            ))
         ],
       (Some (App ((Coderef "add_one"), (Int 42))))))
    -----------swap_pair_program-----------
    (Module ([],
       [(Func (false, "lam_1", [(Prod [Int; Int])], (Prod [Int; Int]),
           (LetTuple ([Int; Int], (Val (Var (0, (Some "p")))),
              (Val (Tuple [(Var (0, (Some "y"))); (Var (1, (Some "x")))]))))
           ));
         (Let (true, ("swap", (Lollipop ([(Prod [Int; Int])], (Prod [Int; Int])))),
            (Val (Coderef "lam_1"))))
         ],
       (Some (App ((Coderef "swap"), (Tuple [(Int 1); (Int 2)]))))))
    -----------compose_program-----------
    Type not found for variable 0 (f)
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
       [(Func (false, "lam_1", [Int], Int,
           (If0 ((Var (0, (Some "n"))), (Val (Int 1)),
              (Let (Int, (Binop (`Sub, (Var (0, (Some "n"))), (Int 1))),
                 (Let (Int,
                    (App ((Coderef "factorial"), (Var (0, (Some "n_minus_1"))))),
                    (Let (Int,
                       (Binop (`Mul, (Var (2, (Some "n"))),
                          (Var (0, (Some "rec_result"))))),
                       (Val (Var (0, (Some "final_result"))))))
                    ))
                 ))
              ))
           ));
         (Let (true, ("factorial", (Lollipop ([Int], Int))),
            (Val (Coderef "lam_1"))))
         ],
       (Some (App ((Coderef "factorial"), (Int 5))))))
    -----------module_with_imports-----------
    (Module (
       [(Import ((Lollipop ([Int], Int)), "external_inc"));
         (Import ((Lollipop ([(Prod [Int; Int])], Int)), "external_add"))],
       [(Func (false, "lam_1", [Int], Int,
           (Let (Int, (App ((Coderef "external_inc"), (Var (0, (Some "x"))))),
              (App ((Coderef "external_inc"), (Var (0, (Some "first_inc")))))))
           ));
         (Let (true, ("double_inc", (Lollipop ([Int], Int))),
            (Val (Coderef "lam_1"))))
         ],
       (Some (App ((Coderef "double_inc"), (Int 5))))))
    -----------complex_example-----------
    (Module ([],
       [(Func (false, "lam_1", [(Prod [Int; Int])], Int,
           (LetTuple ([Int; Int], (Val (Var (0, (Some "input")))),
              (Let (Int,
                 (Binop (`Add, (Var (1, (Some "a"))), (Var (0, (Some "b"))))),
                 (Let ((Ref Int), (New (Var (0, (Some "sum")))),
                    (Let (Int,
                       (Binop (`Mul, (Var (3, (Some "a"))), (Var (2, (Some "b"))))),
                       (Let ((Ref Int), (New (Var (0, (Some "product")))),
                          (Let (Int, (Swap ((Var (2, (Some "r1"))), (Int 0))),
                             (Let (Int, (Swap ((Var (1, (Some "r2"))), (Int 0))),
                                (Let (Int, (Free (Var (4, (Some "r1")))),
                                   (Let (Int, (Free (Var (3, (Some "r2")))),
                                      (Let (Int,
                                         (Binop (`Add, (Var (3, (Some "sum_val"))),
                                            (Var (2, (Some "prod_val"))))),
                                         (Val (Var (0, (Some "final_result"))))))
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
         (Let (true, ("process_pair", (Lollipop ([(Prod [Int; Int])], Int))),
            (Val (Coderef "lam_1"))))
         ],
       (Some (App ((Coderef "process_pair"), (Tuple [(Int 3); (Int 4)]))))))
    -----------closure_example-----------
    Type not found for variable 0 (n) |}]
