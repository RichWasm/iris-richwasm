open! Base
open Richwasm_lin_lang.Syntax

let example1 : Module.t =
  Module.make
    ~imports:
      [ Import.make ~typ:(Lollipop (Int, Prod [ Int; Int ])) ~name:"dup-int" ]
    ~main:(App (Lam (("x", Int), Int, Val (Var "x")), Int 10))
    ()

(* TODO: generate proper examples once parser is done *)
(* ChatGPT: *)

let add_one_program : Module.t =
  {
    imports = [];
    toplevels =
      [
        {
          export = true;
          binding = ("add_one", Lollipop (Int, Int));
          init = Val (Lam (("x", Int), Int, Binop (Add, Var "x", Int 1)));
        };
      ];
    main = Some (App (Var "add_one", Int 42));
  }

let swap_pair_program : Module.t =
  {
    imports = [];
    toplevels =
      [
        {
          export = true;
          binding = ("swap", Lollipop (Prod [ Int; Int ], Prod [ Int; Int ]));
          init =
            Val
              (Lam
                 ( ("p", Prod [ Int; Int ]),
                   Prod [ Int; Int ],
                   LetProd
                     ( [ ("x", Int); ("y", Int) ],
                       Val (Var "p"),
                       Val (Tuple [ Var "y"; Var "x" ]) ) ));
        };
      ];
    main = Some (App (Var "swap", Tuple [ Int 1; Int 2 ]));
  }

let compose_program : Module.t =
  let f_to_g_to_h : Type.t =
    Lollipop
      (Lollipop (Int, Int), Lollipop (Lollipop (Int, Int), Lollipop (Int, Int)))
  in

  Module.make
    ~toplevels:
      [
        {
          export = true;
          binding = ("compose", f_to_g_to_h);
          init =
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
                                     App (Var "f", Var "g_result") ) )) )) ));
        };
      ]
    ()

let reference_example : Module.t =
  {
    imports = [];
    toplevels =
      [
        {
          export = false;
          binding = ("test_ref", Int);
          init =
            Let
              ( ("r", Ref Int),
                New (Int 10),
                Let
                  ( ("old_val", Int),
                    Swap (Var "r", Int 20),
                    Let (("_", Int), Free (Var "r"), Val (Var "old_val")) ) );
        };
      ];
    main = Some (Val (Var "test_ref"));
  }

let factorial_program : Module.t =
  let fact_type : Type.t = Lollipop (Int, Int) in
  {
    imports = [];
    toplevels =
      [
        {
          export = true;
          binding = ("factorial", fact_type);
          init =
            Val
              (Lam
                 ( ("n", Int),
                   Int,
                   If0
                     ( Var "n",
                       Val (Int 1),
                       Let
                         ( ("n_minus_1", Int),
                           Binop (Sub, Var "n", Int 1),
                           Let
                             ( ("rec_result", Int),
                               App (Var "factorial", Var "n_minus_1"),
                               Let
                                 ( ("final_result", Int),
                                   Binop (Mul, Var "n", Var "rec_result"),
                                   Val (Var "final_result") ) ) ) ) ));
        };
      ];
    main = Some (App (Var "factorial", Int 5));
  }

let module_with_imports : Module.t =
  {
    imports =
      [
        { typ = Lollipop (Int, Int); name = "external_inc" };
        { typ = Lollipop (Prod [ Int; Int ], Int); name = "external_add" };
      ];
    toplevels =
      [
        {
          export = true;
          binding = ("double_inc", Lollipop (Int, Int));
          init =
            Val
              (Lam
                 ( ("x", Int),
                   Int,
                   Let
                     ( ("first_inc", Int),
                       App (Var "external_inc", Var "x"),
                       App (Var "external_inc", Var "first_inc") ) ));
        };
      ];
    main = Some (App (Var "double_inc", Int 5));
  }

let complex_example : Module.t =
  {
    imports = [];
    toplevels =
      [
        {
          export = true;
          binding = ("process_pair", Lollipop (Prod [ Int; Int ], Int));
          init =
            Val
              (Lam
                 ( ("input", Prod [ Int; Int ]),
                   Int,
                   LetProd
                     ( [ ("a", Int); ("b", Int) ],
                       Val (Var "input"),
                       Let
                         ( ("sum", Int),
                           Binop (Add, Var "a", Var "b"),
                           Let
                             ( ("r1", Ref Int),
                               New (Var "sum"),
                               Let
                                 ( ("product", Int),
                                   Binop (Mul, Var "a", Var "b"),
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
                                                             ( Add,
                                                               Var "sum_val",
                                                               Var "prod_val" ),
                                                           Val
                                                             (Var "final_result")
                                                         ) ) ) ) ) ) ) ) ) ) ));
        };
      ];
    main = Some (App (Var "process_pair", Tuple [ Int 3; Int 4 ]));
  }

let closure_example : Module.t =
  Module.make
    ~toplevels:
      [
        TopLevel.make ~export:true
          ~binding:("make_adder", Lollipop (Int, Lollipop (Int, Int)))
          ~init:
            (Val
               (Lam
                  ( ("n", Int),
                    Lollipop (Int, Int),
                    Val (Lam (("x", Int), Int, Binop (Add, Var "n", Var "x")))
                  )));
      ]
    ~main:
      (Let
         ( ("add5", Lollipop (Int, Int)),
           App (Var "make_adder", Int 5),
           App (Var "add5", Int 10) ))
    ()

let all =
  [
    ("add_one_program", add_one_program);
    ("swap_pair_program", swap_pair_program);
    ("compose_program", compose_program);
    ("reference_example", reference_example);
    ("factorial_program", factorial_program);
    ("module_with_imports", module_with_imports);
    ("complex_example", complex_example);
    ("closure_example", closure_example);
  ]
