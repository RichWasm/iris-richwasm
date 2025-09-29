open! Base
open! Stdlib.Format
open! Richwasm_lin_lang
open Syntax

let swap_pair_program : Module.t =
  {
    imports = [];
    functions =
      [
        {
          export = true;
          name = "swap";
          param = ("p", Prod [ Int; Int ]);
          return = Prod [ Int; Int ];
          body =
            Split
              ( [ ("x", Int); ("y", Int) ],
                Val (Var "p"),
                Val (Tuple [ Var "y"; Var "x" ]) );
        };
      ];
    main = Some (App (Var "swap", Tuple [ Int 1; Int 2 ]));
  }

let compose_program : Module.t =
  Module.make
    ~functions:
      [
        {
          export = true;
          name = "compose";
          param = ("f", Lollipop (Int, Int));
          return = Lollipop (Lollipop (Int, Int), Lollipop (Int, Int));
          body =
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
                              App (Var "f", Var "g_result") ) )) ));
        };
      ]
    ()

let reference_example : Module.t =
  Module.make
    ~main:
      (Let
         ( ("r", Ref Int),
           New (Int 10),
           Let
             ( ("old_val", Int),
               Swap (Var "r", Int 20),
               Let (("_", Int), Free (Var "r"), Val (Var "old_val")) ) ))
    ()

let module_with_imports : Module.t =
  {
    imports =
      [
        { typ = Lollipop (Int, Int); name = "external_inc" };
        { typ = Lollipop (Prod [ Int; Int ], Int); name = "external_add" };
      ];
    functions =
      [
        {
          export = true;
          name = "double_inc";
          param = ("x", Int);
          return = Int;
          body =
            Let
              ( ("first_inc", Int),
                App (Var "external_inc", Var "x"),
                App (Var "external_inc", Var "first_inc") );
        };
      ];
    main = Some (App (Var "double_inc", Int 5));
  }

let complex_example : Module.t =
  {
    imports = [];
    functions =
      [
        {
          export = true;
          name = "process_pair";
          param = ("input", Prod [ Int; Int ]);
          return = Int;
          body =
            Split
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
                                                    Val (Var "final_result") )
                                              ) ) ) ) ) ) ) ) );
        };
      ];
    main = Some (App (Var "process_pair", Tuple [ Int 3; Int 4 ]));
  }

let extra_examples =
  [
    ("swap_pair_program", swap_pair_program);
    ("compose_program", compose_program);
    ("reference_example", reference_example);
    ("module_with_imports", module_with_imports);
    ("complex_example", complex_example);
  ]

let%expect_test "pretty prints examples" =
  pp_set_margin std_formatter 80;
  pp_set_max_indent std_formatter 80;

  let examples : (string * Module.t) list = Examples.all @ extra_examples in
  List.iter
    ~f:(fun (n, m) -> printf "-----------%s-----------@.%a@." n Module.pp m)
    examples;
  [%expect
    {|
    -----------simple_app_lambda-----------
    (app (λ (x : int) : int .
           x)
    10)
    -----------add_one_program-----------
    (export fun add-one (x : int) : int . (x + 1))

    (app add-one 42)
    -----------add_tup_ref-----------
    (let (r : (ref int)) = (new 2) in
    (split ((x1 : int), (x2 : (ref int))) = (1, r) in
    (let (x2' : int) = (free x2) in
    (x1 + x2'))))
    -----------print_10-----------
    (import (int ⊸ ()) as print)

    (app print 10)
    -----------factorial_program-----------
    (export fun factorial (n : int) : int .
      (if n then 1 else
        (let (n-sub1 : int) = (n - 1) in
        (let (rec-res : int) = (app factorial n-sub1) in
        (n × rec-res)))))


    (app factorial 5)
    -----------safe_div-----------
    (fun safe_div (p : (int ⊗ int)) : (int ⊕ ()) .
      (split ((x : int), (y : int)) = p in
      (if y
        then (inj 1 () : (int ⊕ ())) else
             (let (q : int) = (x ÷ y) in
             (inj 0 q : (int ⊕ ()))))))

    (fun from_either (e : (int ⊕ ())) : int .
      (cases e
        (case (ok : int) ok)
        (case (err : ()) 0)))


    (let (r : (int ⊕ ())) = (app safe_div (10, 0)) in
    (app from_either r))
    -----------incr_n-----------
    (fun incr_1 (r : (ref int)) : (ref int) .
      (split ((old : int), (r1 : (ref int))) = (swap r 0) in
      (let (new : int) = (old + 1) in
      (let (p2 : (int ⊗ (ref int))) = (swap r1 new) in
      (split ((_ : int), (r2 : (ref int))) = p2 in
      r2)))))
    (export fun incr_n (p : ((ref int) ⊗ int)) : int .
      (split ((r : (ref int)), (n : int)) = p in
      (if n then (free r) else
        (let (r1 : (ref int)) = (app incr_1 r) in
        (let (n1 : int) = (n - 1) in
        (app incr_n (r1, n1)))))))


    (let (r0 : (ref int)) = (new 10) in
    (app incr_n (r0, 3)))
    -----------fix_factorial-----------
    (let (fix : (((int ⊸ int) ⊸ (int ⊸ int)) ⊸ (int ⊸ int))) =
      (λ (f : ((int ⊸ int) ⊸ (int ⊸ int))) : (int ⊸ int) .
        (let (omega : ((rec a (a ⊸ (int ⊸ int))) ⊸ (int ⊸ int))) =
          (λ (x : (rec a (a ⊸ (int ⊸ int)))) : (int ⊸ int) .
            (let (ux : ((rec a (a ⊸ (int ⊸ int))) ⊸ (int ⊸ int))) =
              (unfold (rec a (a ⊸ (int ⊸ int))) x) in
            (let (xx : (int ⊸ int)) = (app ux x) in
            (app f xx))))
        in (app omega (fold (rec a (a ⊸ (int ⊸ int))) omega))))
    in
    (let (factorial : (int ⊸ int)) =
      (app fix
        (λ (rec : (int ⊸ int)) : (int ⊸ int) .
          (λ (n : int) : int .
            (if n then 1 else
              (let (n-sub1 : int) = (n - 1) in
              (let (rec-res : int) = (app rec n-sub1) in
              (n × rec-res)))))))
      in
    (app factorial 5)))
    -----------swap_pair_program-----------
    (export fun swap (p : (int ⊗ int)) : (int ⊗ int) .
      (split ((x : int), (y : int)) = p in
      (y, x)))

    (app swap (1, 2))
    -----------compose_program-----------
    (export fun compose (f : (int ⊸ int)) : ((int ⊸ int) ⊸ (int ⊸ int)) .
      (λ (g : (int ⊸ int)) : (int ⊸ int) .
        (λ (x : int) : int .
          (let (g_result : int) = (app g x) in
          (app f g_result)))))



    -----------reference_example-----------
    (let (r : (ref int)) = (new 10) in
    (let (old_val : int) = (swap r 20) in
    (let (_ : int) = (free r) in
    old_val)))
    -----------module_with_imports-----------
    (import (int ⊸ int) as external_inc)
    (import ((int ⊗ int) ⊸ int) as external_add)

    (export fun double_inc (x : int) : int .
      (let (first_inc : int) = (app external_inc x) in
      (app external_inc first_inc)))

    (app double_inc 5)
    -----------complex_example-----------
    (export fun process_pair (input : (int ⊗ int)) : int .
      (split ((a : int), (b : int)) = input in
      (let (sum : int) = (a + b) in
      (let (r1 : (ref int)) = (new sum) in
      (let (product : int) = (a × b) in
      (let (r2 : (ref int)) = (new product) in
      (let (sum_val : int) = (swap r1 0) in
      (let (prod_val : int) = (swap r2 0) in
      (let (_1 : int) = (free r1) in
      (let (_2 : int) = (free r2) in
      (let (final_result : int) = (sum_val + prod_val) in
      final_result)))))))))))

    (app process_pair (3, 4))
    |}]
