open Richwasm_lin_lang.Syntax

let example1 : Module.t =
  Module
    ( [ Import (Lollipop (Int, Prod (Int, Int)), "dup-int") ],
      [],
      Some (App (Lam (("x", Int), Int, Val (Var "x")), Int 10)) )

open Types

(* ChatGPT: *)

let add_one_program =
  Module
    ( [],
      [
        TopLevel
          ( true,
            ("add_one", Lollipop (Int, Int)),
            Val (Lam (("x", Int), Int, Binop (`Add, Var "x", Int 1))) );
      ],
      Some (App (Var "add_one", Int 42)) )

let swap_pair_program =
  Module
    ( [],
      [
        TopLevel
          ( true,
            ("swap", Lollipop (Prod (Int, Int), Prod (Int, Int))),
            Val
              (Lam
                 ( ("p", Prod (Int, Int)),
                   Prod (Int, Int),
                   LetPair
                     ( ("x", Int),
                       ("y", Int),
                       Val (Var "p"),
                       Val (Prod (Var "y", Var "x")) ) )) );
      ],
      Some (App (Var "swap", Prod (Int 1, Int 2))) )

let compose_program =
  let f_to_g_to_h =
    Lollipop
      (Lollipop (Int, Int), Lollipop (Lollipop (Int, Int), Lollipop (Int, Int)))
  in
  Module
    ( [],
      [
        TopLevel
          ( true,
            ("compose", f_to_g_to_h),
            Val
              (Lam
                 ( ("f", Lollipop (Int, Int)),
                   Lollipop (Lollipop (Int, Int), Lollipop (Int, Int)),
                   Val
                     (Lam
                        ( ("g", Lollipop (Int, Int)),
                          Lollipop (Int, Int),
                          Val
                            (Lam
                               ( ("x", Int),
                                 Int,
                                 Let
                                   ( ("g_result", Int),
                                     App (Var "g", Var "x"),
                                     App (Var "f", Var "g_result") ) )) )) )) );
      ],
      None )

let reference_example =
  Module
    ( [],
      [
        TopLevel
          ( false,
            ("test_ref", Int),
            Let
              ( ("r", Ref Int),
                New (Int 10),
                Let
                  ( ("old_val", Int),
                    Swap (Var "r", Int 20),
                    Let (("_", Int), Free (Var "r"), Val (Var "old_val")) ) ) );
      ],
      Some (Val (Var "test_ref")) )

let factorial_program =
  let fact_type = Lollipop (Int, Int) in
  Module
    ( [],
      [
        TopLevel
          ( true,
            ("factorial", fact_type),
            Val
              (Lam
                 ( ("n", Int),
                   Int,
                   If0
                     ( Var "n",
                       Val (Int 1),
                       Let
                         ( ("n_minus_1", Int),
                           Binop (`Sub, Var "n", Int 1),
                           Let
                             ( ("rec_result", Int),
                               App (Var "factorial", Var "n_minus_1"),
                               Let
                                 ( ("final_result", Int),
                                   Binop (`Mul, Var "n", Var "rec_result"),
                                   Val (Var "final_result") ) ) ) ) )) );
      ],
      Some (App (Var "factorial", Int 5)) )

let module_with_imports =
  Module
    ( [
        Import (Lollipop (Int, Int), "external_inc");
        Import (Lollipop (Prod (Int, Int), Int), "external_add");
      ],
      [
        TopLevel
          ( true,
            ("double_inc", Lollipop (Int, Int)),
            Val
              (Lam
                 ( ("x", Int),
                   Int,
                   Let
                     ( ("first_inc", Int),
                       App (Var "external_inc", Var "x"),
                       App (Var "external_inc", Var "first_inc") ) )) );
      ],
      Some (App (Var "double_inc", Int 5)) )

let complex_example =
  Module
    ( [],
      [
        TopLevel
          ( true,
            ("process_pair", Lollipop (Prod (Int, Int), Int)),
            Val
              (Lam
                 ( ("input", Prod (Int, Int)),
                   Int,
                   LetPair
                     ( ("a", Int),
                       ("b", Int),
                       Val (Var "input"),
                       Let
                         ( ("sum", Int),
                           Binop (`Add, Var "a", Var "b"),
                           Let
                             ( ("r1", Ref Int),
                               New (Var "sum"),
                               Let
                                 ( ("product", Int),
                                   Binop (`Mul, Var "a", Var "b"),
                                   Let
                                     ( ("r2", Ref Int),
                                       New (Var "product"),
                                       Let
                                         ( ("sum_val", Int),
                                           Swap (Var "r1", Int 0),
                                           Let
                                             ( ("prod_val", Int),
                                               Swap (Var "r2", Int 0),
                                               Let
                                                 ( ("_1", Int),
                                                   Free (Var "r1"),
                                                   Let
                                                     ( ("_2", Int),
                                                       Free (Var "r2"),
                                                       Let
                                                         ( ("final_result", Int),
                                                           Binop
                                                             ( `Add,
                                                               Var "sum_val",
                                                               Var "prod_val" ),
                                                           Val
                                                             (Var "final_result")
                                                         ) ) ) ) ) ) ) ) ) ) ))
          );
      ],
      Some (App (Var "process_pair", Prod (Int 3, Int 4))) )

let closure_example =
  Module
    ( [],
      [
        TopLevel
          ( true,
            ("make_adder", Lollipop (Int, Lollipop (Int, Int))),
            Val
              (Lam
                 ( ("n", Int),
                   Lollipop (Int, Int),
                   Val (Lam (("x", Int), Int, Binop (`Add, Var "n", Var "x")))
                 )) );
      ],
      Some
        (Let
           ( ("add5", Lollipop (Int, Int)),
             App (Var "make_adder", Int 5),
             App (Var "add5", Int 10) )) )
