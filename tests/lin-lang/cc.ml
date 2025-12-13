open! Base
open! Stdlib.Format
open! Test_support
open! Richwasm_lin_lang
open Cc

include Test_runner.Outputter.Make (struct
  include Test_runner.Outputter.DefaultConfig
  open Test_utils

  type syntax = Syntax.Module.t
  type text = string
  type res = IR.Module.t

  let margin = 120
  let max_indent = margin

  let syntax_pipeline x =
    x
    |> Index.Compile.compile_module
    |> or_fail_pp Index.Err.pp
    |> Typecheck.Compile.compile_module
    |> or_fail_pp Typecheck.Err.pp
    |> Cc.Compile.compile_module
    |> or_fail_pp Cc.Compile.Err.pp

  let string_pipeline s = s |> Parse.from_string_exn |> syntax_pipeline
  let examples = Test_examples.Lin_lang.all
  let pp = IR.Module.pp
end)

let%expect_test "simple" =
  let mk = Syntax.Module.make in
  output_syntax (mk ());
  [%expect {| |}];

  output_syntax (mk ~main:(Lam (("x", Int), Int, Int 69)) ());
  [%expect
    {|
    (fun lam_1 (<> : (⊗ (ref (⊗)) int)) : int .
      (split (<> : (ref (⊗))) (<> : int) = (<0> : (⊗ (ref (⊗)) int)) in
       (split  = (free (<1> : (ref (⊗))) : (⊗)) in
        (let (<> : int) = (<0> : int) in
         (69 : int)
         : int) : int)
      : int))

    (pack (⊗)
       (tup (coderef lam_1 : ((⊗ (ref (⊗)) int) ⊸ int)) (new (tup : (⊗)) : (ref (⊗)))
        : (⊗ ((⊗ (ref (⊗)) int) ⊸ int) (ref (⊗))))
       : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0])))) |}];

  output_syntax
    (mk
       ~main:
         (Let
            ( ("y", Int),
              Int 67,
              Lam (("x", Int), Int, Binop (Add, Var "x", Var "y")) ))
       ());
  [%expect
    {|
    (fun lam_1 (<> : (⊗ (ref (⊗ int)) int)) : int .
      (split (<> : (ref (⊗ int))) (<> : int) = (<0> : (⊗ (ref (⊗ int)) int)) in
       (split (<> : int) = (free (<1> : (ref (⊗ int))) : (⊗ int)) in
        (let (<> : int) = (<1> : int) in
         (+ (<0:x> : int) (<1:y> : int) : int)
         : int) : int)
      : int))

    (let (<> : int) = (67 : int) in
     (pack (⊗ int)
        (tup (coderef lam_1 : ((⊗ (ref (⊗ int)) int) ⊸ int)) (new (tup (<0:y> : int) : (⊗ int)) : (ref (⊗ int)))
         : (⊗ ((⊗ (ref (⊗ int)) int) ⊸ int) (ref (⊗ int))))
        : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))))
     : (exists [] ((⊗ (ref [0]) int) ⊸ int))) |}];

  output_syntax
    (mk
       ~main:
         (Let
            ( ("z", Int),
              Int 420,
              Let
                ( ("y", Int),
                  Int 67,
                  Lam
                    ( ("x", Int),
                      Int,
                      Let
                        ( ("r", Int),
                          Binop (Add, Var "x", Var "y"),
                          Binop (Mul, Var "z", Var "r") ) ) ) ))
       ());
  [%expect
    {|
    (fun lam_1 (<> : (⊗ (ref (⊗ int int)) int)) : int .
      (split (<> : (ref (⊗ int int))) (<> : int) = (<0> : (⊗ (ref (⊗ int int)) int)) in
       (split (<> : int) (<> : int) = (free (<1> : (ref (⊗ int int))) : (⊗ int int)) in
        (let (<> : int) = (<2> : int) in
         (let (<> : int) = (+ (<0:x> : int) (<1:y> : int) : int) in
          (× (<3:z> : int) (<0:r> : int) : int)
          : int)
         : int) : int)
      : int))

    (let (<> : int) = (420 : int) in
     (let (<> : int) = (67 : int) in
      (pack (⊗ int int)
         (tup (coderef lam_1 : ((⊗ (ref (⊗ int int)) int) ⊸ int))
            (new (tup (<0:y> : int) (<1:z> : int) : (⊗ int int)) : (ref (⊗ int int)))
          : (⊗ ((⊗ (ref (⊗ int int)) int) ⊸ int) (ref (⊗ int int))))
         : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))))
      : (exists [] ((⊗ (ref [0]) int) ⊸ int)))
     : (exists [] ((⊗ (ref [0]) int) ⊸ int))) |}];
  output_syntax
    (mk
       ~main:
         (Let
            ( ("y", Int),
              Int 67,
              Lam
                ( ("x", Int),
                  Int,
                  Split
                    ( [ ("a", Int); ("b", Int) ],
                      Tuple [ Var "x"; Var "y" ],
                      Binop (Add, Var "a", Var "b") ) ) ))
       ());
  [%expect
    {|
    (fun lam_1 (<> : (⊗ (ref (⊗ int)) int)) : int .
      (split (<> : (ref (⊗ int))) (<> : int) = (<0> : (⊗ (ref (⊗ int)) int)) in
       (split (<> : int) = (free (<1> : (ref (⊗ int))) : (⊗ int)) in
        (let (<> : int) = (<1> : int) in
         (split (<> : int) (<> : int) = (tup (<0:x> : int) (<1:y> : int) : (⊗ int int)) in
          (+ (<1:a> : int) (<0:b> : int) : int) : int)
         : int) : int)
      : int))

    (let (<> : int) = (67 : int) in
     (pack (⊗ int)
        (tup (coderef lam_1 : ((⊗ (ref (⊗ int)) int) ⊸ int)) (new (tup (<0:y> : int) : (⊗ int)) : (ref (⊗ int)))
         : (⊗ ((⊗ (ref (⊗ int)) int) ⊸ int) (ref (⊗ int))))
        : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))))
     : (exists [] ((⊗ (ref [0]) int) ⊸ int))) |}];
  output_syntax
    (mk
       ~main:
         (Let
            ( ("add1", Lollipop (Int, Int)),
              Lam (("x", Int), Int, Binop (Add, Var "x", Int 1)),
              App (Var "add1", Int 10) ))
       ());
  [%expect
    {|
    (fun lam_1 (<> : (⊗ (ref (⊗)) int)) : int .
      (split (<> : (ref (⊗))) (<> : int) = (<0> : (⊗ (ref (⊗)) int)) in
       (split  = (free (<1> : (ref (⊗))) : (⊗)) in
        (let (<> : int) = (<0> : int) in
         (+ (<0:x> : int) (1 : int) : int)
         : int) : int)
      : int))

    (let (<> : (exists [] ((⊗ (ref [0]) int) ⊸ int))) =
       (pack (⊗)
          (tup (coderef lam_1 : ((⊗ (ref (⊗)) int) ⊸ int)) (new (tup : (⊗)) : (ref (⊗)))
           : (⊗ ((⊗ (ref (⊗)) int) ⊸ int) (ref (⊗))))
          : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))))
       in
     (unpack (<0:add1> : (exists [] ((⊗ (ref [0]) int) ⊸ int)))
        <> (split (<> : ((⊗ (ref [0]) int) ⊸ int)) (<> : (ref [0])) =
              (<0> : (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))) in
            (app (<1> : ((⊗ (ref [0]) int) ⊸ int)) (tup (<0> : (ref [0])) (10 : int) : (⊗ (ref [0]) int)) : int)
        : int) : int)
     : int) |}];

  (* shadow type *)
  output
    {| (fold (rec a (rec a (a + int))) (inj 1 0 : (rec a (rec a (a + int))))) |};
  [%expect {| FAILURE (InjInvalidAnn (Rec (Rec (Sum ((Var (0 (a))) Int))))) |}]

let%expect_test "examples" =
  output_examples ();
  [%expect
    {|
    -----------one-----------
    (1 : int)
    -----------flat_tuple-----------
    (tup (1 : int) (2 : int) (3 : int) (4 : int) : (⊗ int int int int))
    -----------nested_tuple-----------
    (tup (tup (1 : int) (2 : int) : (⊗ int int)) (tup (3 : int) (4 : int) : (⊗ int int))
     : (⊗ (⊗ int int) (⊗ int int)))
    -----------single_sum-----------
    (inj 0 (tup : (⊗)) : (⊕ (⊗)))
    -----------double_sum-----------
    (inj 1 (15 : int) : (⊕ (⊗) int))
    -----------arith_add-----------
    (+ (9 : int) (10 : int) : int)
    -----------arith_sub-----------
    (- (67 : int) (41 : int) : int)
    -----------arith_mul-----------
    (× (42 : int) (10 : int) : int)
    -----------arith_div-----------
    (÷ (-30 : int) (10 : int) : int)
    -----------app_ident-----------
    (fun lam_1 (<> : (⊗ (ref (⊗)) int)) : int .
      (split (<> : (ref (⊗))) (<> : int) = (<0> : (⊗ (ref (⊗)) int)) in
       (split  = (free (<1> : (ref (⊗))) : (⊗)) in
        (let (<> : int) = (<0> : int) in
         (<0:x> : int)
         : int) : int)
      : int))

    (unpack
       (pack (⊗)
          (tup (coderef lam_1 : ((⊗ (ref (⊗)) int) ⊸ int)) (new (tup : (⊗)) : (ref (⊗)))
           : (⊗ ((⊗ (ref (⊗)) int) ⊸ int) (ref (⊗))))
          : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))))
       <> (split (<> : ((⊗ (ref [0]) int) ⊸ int)) (<> : (ref [0])) =
             (<0> : (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))) in
           (app (<1> : ((⊗ (ref [0]) int) ⊸ int)) (tup (<0> : (ref [0])) (10 : int) : (⊗ (ref [0]) int)) : int)
       : int) : int)
    -----------nested_arith-----------
    (× (+ (9 : int) (10 : int) : int) (5 : int) : int)
    -----------let_bind-----------
    (let (<> : int) = (10 : int) in
     (<0:x> : int)
     : int)
    -----------add_one_program-----------
    (export fun add-one (<> : (⊗ (ref (⊗)) int)) : int .
      (split (<> : (ref (⊗))) (<> : int) = (<0> : (⊗ (ref (⊗)) int)) in
       (+ (<0:x> : int) (1 : int) : int)
      : int))

    (unpack
       (pack (⊗)
          (tup (coderef add-one : ((⊗ (ref [0]) int) ⊸ int)) (new (tup : (⊗)) : (ref (⊗)))
           : (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref (⊗))))
          : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))))
       <> (split (<> : ((⊗ (ref [0]) int) ⊸ int)) (<> : (ref [0])) =
             (<0> : (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))) in
           (app (<1> : ((⊗ (ref [0]) int) ⊸ int)) (tup (<0> : (ref [0])) (42 : int) : (⊗ (ref [0]) int)) : int)
       : int) : int)
    -----------add_tup_ref-----------
    (let (<> : (ref int)) = (new (2 : int) : (ref int)) in
     (split (<> : int) (<> : (ref int)) = (tup (1 : int) (<0:r> : (ref int)) : (⊗ int (ref int))) in
      (let (<> : int) = (free (<0:x2> : (ref int)) : int) in
       (+ (<2:x1> : int) (<0:x2'> : int) : int)
       : int) : int)
     : int)
    -----------print_10-----------
    (import ((⊗ (ref (⊗)) int) ⊸ (⊗)) as print)

    (unpack
       (pack (⊗)
          (tup (coderef print : ((⊗ (ref [0]) int) ⊸ (⊗))) (new (tup : (⊗)) : (ref (⊗)))
           : (⊗ ((⊗ (ref [0]) int) ⊸ (⊗)) (ref (⊗))))
          : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ (⊗)) (ref [0]))))
       <> (split (<> : ((⊗ (ref [0]) int) ⊸ (⊗))) (<> : (ref [0])) =
             (<0> : (⊗ ((⊗ (ref [0]) int) ⊸ (⊗)) (ref [0]))) in
           (app (<1> : ((⊗ (ref [0]) int) ⊸ (⊗))) (tup (<0> : (ref [0])) (10 : int) : (⊗ (ref [0]) int)) : (⊗))
       : (⊗)) : (⊗))
    -----------closure-----------
    (fun lam_1 (<> : (⊗ (ref (⊗ int)) (⊗))) : int .
      (split (<> : (ref (⊗ int))) (<> : (⊗)) = (<0> : (⊗ (ref (⊗ int)) (⊗))) in
       (split (<> : int) = (free (<1> : (ref (⊗ int))) : (⊗ int)) in
        (let (<> : (⊗)) = (<1> : (⊗)) in
         (<1:x> : int)
         : int) : int)
      : int))

    (let (<> : int) = (10 : int) in
     (unpack
        (pack (⊗ int)
           (tup (coderef lam_1 : ((⊗ (ref (⊗ int)) (⊗)) ⊸ int))
              (new (tup (<0:x> : int) : (⊗ int)) : (ref (⊗ int)))
            : (⊗ ((⊗ (ref (⊗ int)) (⊗)) ⊸ int) (ref (⊗ int))))
           : (exists [] (⊗ ((⊗ (ref [0]) (⊗)) ⊸ int) (ref [0]))))
        <> (split (<> : ((⊗ (ref [0]) (⊗)) ⊸ int)) (<> : (ref [0])) =
              (<0> : (⊗ ((⊗ (ref [0]) (⊗)) ⊸ int) (ref [0]))) in
            (app (<1> : ((⊗ (ref [0]) (⊗)) ⊸ int)) (tup (<0> : (ref [0])) (tup : (⊗)) : (⊗ (ref [0]) (⊗)))
               : int)
        : int) : int)
     : int)
    -----------closure_call_var-----------
    (fun lam_1 (<> : (⊗ (ref (⊗ int)) int)) : int .
      (split (<> : (ref (⊗ int))) (<> : int) = (<0> : (⊗ (ref (⊗ int)) int)) in
       (split (<> : int) = (free (<1> : (ref (⊗ int))) : (⊗ int)) in
        (let (<> : int) = (<1> : int) in
         (+ (<0:x> : int) (<1:add-amount> : int) : int)
         : int) : int)
      : int))

    (let (<> : int) = (21 : int) in
     (let (<> : int) = (1 : int) in
      (unpack
         (pack (⊗ int)
            (tup (coderef lam_1 : ((⊗ (ref (⊗ int)) int) ⊸ int))
               (new (tup (<0:add-amount> : int) : (⊗ int)) : (ref (⊗ int)))
             : (⊗ ((⊗ (ref (⊗ int)) int) ⊸ int) (ref (⊗ int))))
            : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))))
         <> (split (<> : ((⊗ (ref [0]) int) ⊸ int)) (<> : (ref [0])) =
               (<0> : (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))) in
             (app (<1> : ((⊗ (ref [0]) int) ⊸ int)) (tup (<0> : (ref [0])) (<4:input> : int) : (⊗ (ref [0]) int))
                : int)
         : int) : int)
      : int)
     : int)
    -----------triangle_tl-----------
    (fun triangle (<> : (⊗ (ref (⊗)) int)) : int .
      (split (<> : (ref (⊗))) (<> : int) = (<0> : (⊗ (ref (⊗)) int)) in
       (if0 (<0:n> : int)
        then (0 : int)
        else
          (+ (<0:n> : int)
             (unpack
                (pack (⊗)
                   (tup (coderef triangle : ((⊗ (ref [0]) int) ⊸ int)) (new (tup : (⊗)) : (ref (⊗)))
                    : (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref (⊗))))
                   : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))))
                <> (split (<> : ((⊗ (ref [0]) int) ⊸ int)) (<> : (ref [0])) =
                      (<0> : (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))) in
                    (app (<1> : ((⊗ (ref [0]) int) ⊸ int))
                       (tup (<0> : (ref [0])) (- (<3:n> : int) (1 : int) : int) : (⊗ (ref [0]) int)) : int)
                : int) : int)
             : int)
        : int)
      : int))

    (unpack
       (pack (⊗)
          (tup (coderef triangle : ((⊗ (ref [0]) int) ⊸ int)) (new (tup : (⊗)) : (ref (⊗)))
           : (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref (⊗))))
          : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))))
       <> (split (<> : ((⊗ (ref [0]) int) ⊸ int)) (<> : (ref [0])) =
             (<0> : (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))) in
           (app (<1> : ((⊗ (ref [0]) int) ⊸ int)) (tup (<0> : (ref [0])) (10 : int) : (⊗ (ref [0]) int)) : int)
       : int) : int)
    -----------factorial_tl-----------
    (export fun factorial (<> : (⊗ (ref (⊗)) int)) : int .
      (split (<> : (ref (⊗))) (<> : int) = (<0> : (⊗ (ref (⊗)) int)) in
       (if0 (<0:n> : int)
        then (1 : int)
        else
          (let (<> : int) = (- (<0:n> : int) (1 : int) : int) in
           (let (<> : int) =
              (unpack
                 (pack (⊗)
                    (tup (coderef factorial : ((⊗ (ref [0]) int) ⊸ int)) (new (tup : (⊗)) : (ref (⊗)))
                     : (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref (⊗))))
                    : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))))
                 <> (split (<> : ((⊗ (ref [0]) int) ⊸ int)) (<> : (ref [0])) =
                       (<0> : (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))) in
                     (app (<1> : ((⊗ (ref [0]) int) ⊸ int))
                        (tup (<0> : (ref [0])) (<3:n-sub1> : int) : (⊗ (ref [0]) int)) : int)
                 : int) : int)
              in
            (× (<2:n> : int) (<0:rec-res> : int) : int)
            : int)
           : int)
        : int)
      : int))

    (unpack
       (pack (⊗)
          (tup (coderef factorial : ((⊗ (ref [0]) int) ⊸ int)) (new (tup : (⊗)) : (ref (⊗)))
           : (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref (⊗))))
          : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))))
       <> (split (<> : ((⊗ (ref [0]) int) ⊸ int)) (<> : (ref [0])) =
             (<0> : (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))) in
           (app (<1> : ((⊗ (ref [0]) int) ⊸ int)) (tup (<0> : (ref [0])) (5 : int) : (⊗ (ref [0]) int)) : int)
       : int) : int)
    -----------safe_div-----------
    (fun safe_div (<> : (⊗ (ref (⊗)) (⊗ int int))) : (⊕ int (⊗)) .
      (split (<> : (ref (⊗))) (<> : (⊗ int int)) = (<0> : (⊗ (ref (⊗)) (⊗ int int))) in
       (split (<> : int) (<> : int) = (<0:p> : (⊗ int int)) in
        (if0 (<0:y> : int)
         then (inj 1 (tup : (⊗)) : (⊕ int (⊗)))
         else
           (let (<> : int) = (÷ (<1:x> : int) (<0:y> : int) : int) in
            (inj 0 (<0:q> : int) : (⊕ int (⊗)))
            : (⊕ int (⊗)))
         : (⊕ int (⊗))) : (⊕ int (⊗)))
      : (⊕ int (⊗))))

    (fun from_either (<> : (⊗ (ref (⊗)) (⊕ int (⊗)))) : int .
      (split (<> : (ref (⊗))) (<> : (⊕ int (⊗))) = (<0> : (⊗ (ref (⊗)) (⊕ int (⊗)))) in
       (cases (<0:e> : (⊕ int (⊗)))
          (case (<> : int) (<0:ok> : int))
          (case (<> : (⊗)) (0 : int))
        : int)
      : int))

    (let (<> : (⊕ int (⊗))) =
       (unpack
          (pack (⊗)
             (tup (coderef safe_div : ((⊗ (ref [0]) (⊗ int int)) ⊸ (⊕ int (⊗))))
                (new (tup : (⊗)) : (ref (⊗)))
              : (⊗ ((⊗ (ref [0]) (⊗ int int)) ⊸ (⊕ int (⊗))) (ref (⊗))))
             : (exists [] (⊗ ((⊗ (ref [0]) (⊗ int int)) ⊸ (⊕ int (⊗))) (ref [0]))))
          <> (split (<> : ((⊗ (ref [0]) (⊗ int int)) ⊸ (⊕ int (⊗)))) (<> :
                (ref [0])) = (<0> : (⊗ ((⊗ (ref [0]) (⊗ int int)) ⊸ (⊕ int (⊗))) (ref [0]))) in
              (app (<1> : ((⊗ (ref [0]) (⊗ int int)) ⊸ (⊕ int (⊗))))
                 (tup (<0> : (ref [0])) (tup (10 : int) (0 : int) : (⊗ int int)) : (⊗ (ref [0]) (⊗ int int)))
                 : (⊕ int (⊗)))
          : (⊕ int (⊗))) : (⊕ int (⊗)))
       in
     (unpack
        (pack (⊗)
           (tup (coderef from_either : ((⊗ (ref [0]) (⊕ int (⊗))) ⊸ int)) (new (tup : (⊗)) : (ref (⊗)))
            : (⊗ ((⊗ (ref [0]) (⊕ int (⊗))) ⊸ int) (ref (⊗))))
           : (exists [] (⊗ ((⊗ (ref [0]) (⊕ int (⊗))) ⊸ int) (ref [0]))))
        <> (split (<> : ((⊗ (ref [0]) (⊕ int (⊗))) ⊸ int)) (<> :
              (ref [0])) = (<0> : (⊗ ((⊗ (ref [0]) (⊕ int (⊗))) ⊸ int) (ref [0]))) in
            (app (<1> : ((⊗ (ref [0]) (⊕ int (⊗))) ⊸ int))
               (tup (<0> : (ref [0])) (<3:r> : (⊕ int (⊗))) : (⊗ (ref [0]) (⊕ int (⊗)))) : int)
        : int) : int)
     : int)
    -----------incr_n-----------
    (fun incr_1 (<> : (⊗ (ref (⊗)) (ref int))) : (ref int) .
      (split (<> : (ref (⊗))) (<> : (ref int)) = (<0> : (⊗ (ref (⊗)) (ref int))) in
       (split (<> : (ref int)) (<> : int) = (swap (<0:r> : (ref int)) (0 : int) : (⊗ (ref int) int)) in
        (let (<> : int) = (+ (<0:old> : int) (1 : int) : int) in
         (split (<> : (ref int)) (<> : int) = (swap (<2:r1> : (ref int)) (<0:new> : int) : (⊗ (ref int) int)) in
          (<1:r2> : (ref int)) : (ref int))
         : (ref int)) : (ref int))
      : (ref int)))

    (export fun incr_n (<> : (⊗ (ref (⊗)) (⊗ (ref int) int))) : int .
      (split (<> : (ref (⊗))) (<> : (⊗ (ref int) int)) = (<0> : (⊗ (ref (⊗)) (⊗ (ref int) int))) in
       (split (<> : (ref int)) (<> : int) = (<0:p> : (⊗ (ref int) int)) in
        (if0 (<0:n> : int)
         then (free (<1:r> : (ref int)) : int)
         else
           (let (<> : (ref int)) =
              (unpack
                 (pack (⊗)
                    (tup (coderef incr_1 : ((⊗ (ref [0]) (ref int)) ⊸ (ref int))) (new (tup : (⊗)) : (ref (⊗)))
                     : (⊗ ((⊗ (ref [0]) (ref int)) ⊸ (ref int)) (ref (⊗))))
                    : (exists [] (⊗ ((⊗ (ref [0]) (ref int)) ⊸ (ref int)) (ref [0]))))
                 <> (split (<> : ((⊗ (ref [0]) (ref int)) ⊸ (ref int))) (<> :
                       (ref [0])) = (<0> : (⊗ ((⊗ (ref [0]) (ref int)) ⊸ (ref int)) (ref [0]))) in
                     (app (<1> : ((⊗ (ref [0]) (ref int)) ⊸ (ref int)))
                        (tup (<0> : (ref [0])) (<4:r> : (ref int)) : (⊗ (ref [0]) (ref int))) :
                        (ref int))
                 : (ref int)) : (ref int))
              in
            (let (<> : int) = (- (<1:n> : int) (1 : int) : int) in
             (unpack
                (pack (⊗)
                   (tup (coderef incr_n : ((⊗ (ref [0]) (⊗ (ref int) int)) ⊸ int)) (new (tup : (⊗)) : (ref (⊗)))
                    : (⊗ ((⊗ (ref [0]) (⊗ (ref int) int)) ⊸ int) (ref (⊗))))
                   : (exists [] (⊗ ((⊗ (ref [0]) (⊗ (ref int) int)) ⊸ int) (ref [0]))))
                <> (split (<> : ((⊗ (ref [0]) (⊗ (ref int) int)) ⊸ int)) (<> :
                      (ref [0])) = (<0> : (⊗ ((⊗ (ref [0]) (⊗ (ref int) int)) ⊸ int) (ref [0]))) in
                    (app (<1> : ((⊗ (ref [0]) (⊗ (ref int) int)) ⊸ int))
                       (tup (<0> : (ref [0])) (tup (<4:r1> : (ref int)) (<3:n1> : int) : (⊗ (ref int) int))
                        : (⊗ (ref [0]) (⊗ (ref int) int)))
                       : int)
                : int) : int)
             : int)
            : int)
         : int) : int)
      : int))

    (let (<> : (ref int)) = (new (10 : int) : (ref int)) in
     (unpack
        (pack (⊗)
           (tup (coderef incr_n : ((⊗ (ref [0]) (⊗ (ref int) int)) ⊸ int)) (new (tup : (⊗)) : (ref (⊗)))
            : (⊗ ((⊗ (ref [0]) (⊗ (ref int) int)) ⊸ int) (ref (⊗))))
           : (exists [] (⊗ ((⊗ (ref [0]) (⊗ (ref int) int)) ⊸ int) (ref [0]))))
        <> (split (<> : ((⊗ (ref [0]) (⊗ (ref int) int)) ⊸ int)) (<> :
              (ref [0])) = (<0> : (⊗ ((⊗ (ref [0]) (⊗ (ref int) int)) ⊸ int) (ref [0]))) in
            (app (<1> : ((⊗ (ref [0]) (⊗ (ref int) int)) ⊸ int))
               (tup (<0> : (ref [0])) (tup (<3:r0> : (ref int)) (3 : int) : (⊗ (ref int) int))
                : (⊗ (ref [0]) (⊗ (ref int) int)))
               : int)
        : int) : int)
     : int)
    -----------fix_factorial[invalid]-----------
    (fun lam_2
      (<> : (⊗
              (ref
                (⊗
                  (exists []
                    ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                      (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
              (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))))) :
      (exists [] ((⊗ (ref [0]) int) ⊸ int)) .
      (split
         (<> : (ref
                 (⊗
                   (exists []
                     ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                       (exists [] ((⊗ (ref [0]) int) ⊸ int)))))))
         (<> : (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))))) =
         (<0>
            : (⊗
                (ref
                  (⊗
                    (exists []
                      ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                        (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
                (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))))))
         in
       (split
          (<> : (exists []
                  ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
          =
          (free
             (<1>
                : (ref
                    (⊗
                      (exists []
                        ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                          (exists [] ((⊗ (ref [0]) int) ⊸ int)))))))
             : (⊗
                 (exists []
                   ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                     (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
          in
        (let (<> : (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))))) =
           (<1> : (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))))) in
         (let
            (<> : (exists []
                    ((⊗ (ref [0])
                       (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
                      ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
            =
            (unfold (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
               (<0:x> : (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
               : (exists []
                   ((⊗ (ref [0])
                      (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
                     ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
            in
          (let (<> : (exists [] ((⊗ (ref [0]) int) ⊸ int))) =
             (unpack
                (<0:ux>
                   : (exists []
                       ((⊗ (ref [0])
                          (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
                         ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
                <> (split
                      (<> : ((⊗ (ref [0])
                               (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
                              ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))
                      (<> : (ref [0])) =
                      (<0>
                         : (⊗
                             ((⊗ (ref [0])
                                (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
                               ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))
                             (ref [0])))
                      in
                    (app
                       (<1>
                          : ((⊗ (ref [0])
                               (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
                              ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))
                       (tup (<0> : (ref [0]))
                          (<4:x>
                             : (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
                        : (⊗ (ref [0])
                            (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))))))
                       : (exists [] ((⊗ (ref [0]) int) ⊸ int)))
                : (exists [] ((⊗ (ref [0]) int) ⊸ int))) : (exists [] ((⊗ (ref [0]) int) ⊸ int)))
             in
           (unpack
              (<3:f>
                 : (exists []
                     ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                       (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
              <> (split
                    (<> : ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                            (exists [] ((⊗ (ref [0]) int) ⊸ int))))
                    (<> : (ref [0])) =
                    (<0>
                       : (⊗
                           ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                             (exists [] ((⊗ (ref [0]) int) ⊸ int)))
                           (ref [0])))
                    in
                  (app
                     (<1>
                        : ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                            (exists [] ((⊗ (ref [0]) int) ⊸ int))))
                     (tup (<0> : (ref [0])) (<3:xx> : (exists [] ((⊗ (ref [0]) int) ⊸ int)))
                      : (⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))))
                     : (exists [] ((⊗ (ref [0]) int) ⊸ int)))
              : (exists [] ((⊗ (ref [0]) int) ⊸ int))) : (exists [] ((⊗ (ref [0]) int) ⊸ int)))
           : (exists [] ((⊗ (ref [0]) int) ⊸ int)))
          : (exists [] ((⊗ (ref [0]) int) ⊸ int)))
         : (exists [] ((⊗ (ref [0]) int) ⊸ int))) : (exists [] ((⊗ (ref [0]) int) ⊸ int)))
      : (exists [] ((⊗ (ref [0]) int) ⊸ int))))

    (fun lam_1
      (<> : (⊗ (ref (⊗))
              (exists []
                ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))))) :
      (exists [] ((⊗ (ref [0]) int) ⊸ int)) .
      (split (<> : (ref (⊗)))
         (<> : (exists []
                 ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
         =
         (<0>
            : (⊗ (ref (⊗))
                (exists []
                  ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
         in
       (split  = (free (<1> : (ref (⊗))) : (⊗)) in
        (let
           (<> : (exists []
                   ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                     (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
           =
           (<0>
              : (exists []
                  ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
           in
         (let
            (<> : (exists []
                    ((⊗ (ref [0])
                       (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
                      ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
            =
            (pack
               (⊗
                 (exists []
                   ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                     (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
               (tup
                  (coderef lam_2
                     : ((⊗
                          (ref
                            (⊗
                              (exists []
                                ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                                  (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
                          (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
                         ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))
                  (new
                     (tup
                        (<0:f>
                           : (exists []
                               ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                                 (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
                      : (⊗
                          (exists []
                            ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                              (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
                     : (ref
                         (⊗
                           (exists []
                             ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                               (exists [] ((⊗ (ref [0]) int) ⊸ int)))))))
                : (⊗
                    ((⊗
                       (ref
                         (⊗
                           (exists []
                             ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                               (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
                       (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
                      ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))
                    (ref
                      (⊗
                        (exists []
                          ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                            (exists [] ((⊗ (ref [0]) int) ⊸ int))))))))
               : (exists []
                   (⊗
                     ((⊗ (ref [0])
                        (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
                       ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))
                     (ref [0]))))
            in
          (unpack
             (<0:omega>
                : (exists []
                    ((⊗ (ref [0])
                       (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
                      ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
             <> (split
                   (<> : ((⊗ (ref [0])
                            (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
                           ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))
                   (<> : (ref [0])) =
                   (<0>
                      : (⊗
                          ((⊗ (ref [0])
                             (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
                            ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))
                          (ref [0])))
                   in
                 (app
                    (<1>
                       : ((⊗ (ref [0])
                            (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
                           ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))
                    (tup (<0> : (ref [0]))
                       (fold (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
                          (<3:omega>
                             : (exists []
                                 ((⊗ (ref [0])
                                    (rec []
                                      (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
                                   ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
                          : (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
                     : (⊗ (ref [0])
                         (rec [] (exists [] ((⊗ (ref [0]) [1:a]) ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))))))
                    : (exists [] ((⊗ (ref [0]) int) ⊸ int)))
             : (exists [] ((⊗ (ref [0]) int) ⊸ int))) : (exists [] ((⊗ (ref [0]) int) ⊸ int)))
          : (exists [] ((⊗ (ref [0]) int) ⊸ int)))
         : (exists [] ((⊗ (ref [0]) int) ⊸ int))) : (exists [] ((⊗ (ref [0]) int) ⊸ int)))
      : (exists [] ((⊗ (ref [0]) int) ⊸ int))))

    (fun lam_4 (<> : (⊗ (ref (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)))) int)) : int .
      (split (<> : (ref (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int))))) (<> : int) =
         (<0> : (⊗ (ref (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)))) int)) in
       (split (<> : (exists [] ((⊗ (ref [0]) int) ⊸ int))) =
          (free (<1> : (ref (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
             : (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int))))
          in
        (let (<> : int) = (<1> : int) in
         (if0 (<0:n> : int)
          then (1 : int)
          else
            (let (<> : int) = (- (<0:n> : int) (1 : int) : int) in
             (let (<> : int) =
                (unpack (<2:rec> : (exists [] ((⊗ (ref [0]) int) ⊸ int)))
                   <> (split (<> : ((⊗ (ref [0]) int) ⊸ int)) (<> : (ref [0])) =
                         (<0> : (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))) in
                       (app (<1> : ((⊗ (ref [0]) int) ⊸ int))
                          (tup (<0> : (ref [0])) (<3:n-sub1> : int) : (⊗ (ref [0]) int)) : int)
                   : int) : int)
                in
              (× (<2:n> : int) (<0:rec-res> : int) : int)
              : int)
             : int)
          : int)
         : int) : int)
      : int))

    (fun lam_3 (<> : (⊗ (ref (⊗)) (exists [] ((⊗ (ref [0]) int) ⊸ int)))) :
      (exists [] ((⊗ (ref [0]) int) ⊸ int)) .
      (split (<> : (ref (⊗))) (<> : (exists [] ((⊗ (ref [0]) int) ⊸ int))) =
         (<0> : (⊗ (ref (⊗)) (exists [] ((⊗ (ref [0]) int) ⊸ int)))) in
       (split  = (free (<1> : (ref (⊗))) : (⊗)) in
        (let (<> : (exists [] ((⊗ (ref [0]) int) ⊸ int))) = (<0> : (exists [] ((⊗ (ref [0]) int) ⊸ int))) in
         (pack (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)))
            (tup (coderef lam_4 : ((⊗ (ref (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)))) int) ⊸ int))
               (new
                  (tup (<0:rec> : (exists [] ((⊗ (ref [0]) int) ⊸ int)))
                   : (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int))))
                  : (ref (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
             : (⊗ ((⊗ (ref (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)))) int) ⊸ int)
                 (ref (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int))))))
            : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))))
         : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))))
         : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))))
      : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0])))))

    (let
       (<> : (exists []
               ((⊗ (ref [0])
                  (exists []
                    ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                      (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
                 ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
       =
       (pack (⊗)
          (tup
             (coderef lam_1
                : ((⊗ (ref (⊗))
                     (exists []
                       ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                         (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
                    ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))
             (new (tup : (⊗)) : (ref (⊗)))
           : (⊗
               ((⊗ (ref (⊗))
                  (exists []
                    ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                      (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
                 ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))
               (ref (⊗))))
          : (exists []
              (⊗
                ((⊗ (ref [0])
                   (exists []
                     ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                       (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
                  ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))
                (ref [0]))))
       in
     (let (<> : (exists [] ((⊗ (ref [0]) int) ⊸ int))) =
        (unpack
           (<0:fix>
              : (exists []
                  ((⊗ (ref [0])
                     (exists []
                       ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                         (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
                    ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
           <> (split
                 (<> : ((⊗ (ref [0])
                          (exists []
                            ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                              (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
                         ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))
                 (<> : (ref [0])) =
                 (<0>
                    : (⊗
                        ((⊗ (ref [0])
                           (exists []
                             ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                               (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
                          ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int)))
                        (ref [0])))
                 in
               (app
                  (<1>
                     : ((⊗ (ref [0])
                          (exists []
                            ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                              (exists [] ((⊗ (ref [0]) int) ⊸ int)))))
                         ⊸ (exists [] ((⊗ (ref [0]) int) ⊸ int))))
                  (tup (<0> : (ref [0]))
                     (pack (⊗)
                        (tup
                           (coderef lam_3
                              : ((⊗ (ref (⊗)) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                                  (exists [] ((⊗ (ref [0]) int) ⊸ int))))
                           (new (tup : (⊗)) : (ref (⊗)))
                         : (⊗
                             ((⊗ (ref (⊗)) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                               (exists [] ((⊗ (ref [0]) int) ⊸ int)))
                             (ref (⊗))))
                        : (exists []
                            (⊗
                              ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                                (exists [] ((⊗ (ref [0]) int) ⊸ int)))
                              (ref [0]))))
                   : (⊗ (ref [0])
                       (exists []
                         (⊗
                           ((⊗ (ref [0]) (exists [] ((⊗ (ref [0]) int) ⊸ int))) ⊸
                             (exists [] ((⊗ (ref [0]) int) ⊸ int)))
                           (ref [0])))))
                  : (exists [] ((⊗ (ref [0]) int) ⊸ int)))
           : (exists [] ((⊗ (ref [0]) int) ⊸ int))) : (exists [] ((⊗ (ref [0]) int) ⊸ int)))
        in
      (unpack (<0:factorial> : (exists [] ((⊗ (ref [0]) int) ⊸ int)))
         <> (split (<> : ((⊗ (ref [0]) int) ⊸ int)) (<> : (ref [0])) =
               (<0> : (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))) in
             (app (<1> : ((⊗ (ref [0]) int) ⊸ int)) (tup (<0> : (ref [0])) (5 : int) : (⊗ (ref [0]) int)) : int)
         : int) : int)
      : int)
     : int)
    -----------unboxed_list[invalid]-----------
    (fun lam_1 (<> : (⊗ (ref (⊗)) int)) : int .
      (split (<> : (ref (⊗))) (<> : int) = (<0> : (⊗ (ref (⊗)) int)) in
       (split  = (free (<1> : (ref (⊗))) : (⊗)) in
        (let (<> : int) = (<0> : int) in
         (+ (<0:x> : int) (1 : int) : int)
         : int) : int)
      : int))

    (fun map_int
      (<> : (⊗ (ref (⊗)) (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int [0:α])))))) :
      (rec [] (⊕ (⊗) (⊗ int [0:α]))) .
      (split (<> : (ref (⊗)))
         (<> : (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int [0:α]))))) =
         (<0> : (⊗ (ref (⊗)) (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int [0:α])))))) in
       (split (<> : (exists [] ((⊗ (ref [0]) int) ⊸ int))) (<> : (rec [] (⊕ (⊗) (⊗ int [0:α])))) =
          (<0:p> : (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int [0:α]))))) in
        (fold (rec [] (⊕ (⊗) (⊗ int [0:α])))
           (cases (unfold (rec [] (⊕ (⊗) (⊗ int [0:α]))) (<0:lst> : (rec [] (⊕ (⊗) (⊗ int [0:α]))))
                     : (⊕ (⊗) (⊗ int (rec [] (⊕ (⊗) (⊗ int [0:α]))))))
              (case (<> : (⊗)) (inj 0 (<0:nil> : (⊗)) : (⊕ (⊗) (⊗ int (rec [] (⊕ (⊗) (⊗ int [0:α])))))))
              (case (<> : (⊗ int (rec [] (⊕ (⊗) (⊗ int [0:α])))))
                (split (<> : int) (<> : (rec [] (⊕ (⊗) (⊗ int [0:α])))) =
                   (<0:cons> : (⊗ int (rec [] (⊕ (⊗) (⊗ int [0:α]))))) in
                 (inj 1
                    (tup
                       (unpack (<4:f> : (exists [] ((⊗ (ref [0]) int) ⊸ int)))
                          <> (split (<> : ((⊗ (ref [0]) int) ⊸ int)) (<> :
                                (ref [0])) = (<0> : (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))) in
                              (app (<1> : ((⊗ (ref [0]) int) ⊸ int))
                                 (tup (<0> : (ref [0])) (<4:hd> : int) : (⊗ (ref [0]) int)) : int)
                          : int) : int)
                       (unpack
                          (pack (⊗)
                             (tup
                                (coderef map_int
                                   : ((⊗ (ref [0])
                                        (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int))
                                          (rec [] (⊕ (⊗) (⊗ int [0:α])))))
                                       ⊸ (rec [] (⊕ (⊗) (⊗ int [0:α])))))
                                (new (tup : (⊗)) : (ref (⊗)))
                              : (⊗
                                  ((⊗ (ref [0])
                                     (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int [0:α])))))
                                    ⊸ (rec [] (⊕ (⊗) (⊗ int [0:α]))))
                                  (ref (⊗))))
                             : (exists []
                                 (⊗
                                   ((⊗ (ref [0])
                                      (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int [0:α])))))
                                     ⊸ (rec [] (⊕ (⊗) (⊗ int [0:α]))))
                                   (ref [0]))))
                          <> (split
                                (<> : ((⊗ (ref [0])
                                         (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int))
                                           (rec [] (⊕ (⊗) (⊗ int [0:α])))))
                                        ⊸ (rec [] (⊕ (⊗) (⊗ int [0:α])))))
                                (<> : (ref [0])) =
                                (<0>
                                   : (⊗
                                       ((⊗ (ref [0])
                                          (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int))
                                            (rec [] (⊕ (⊗) (⊗ int [0:α])))))
                                         ⊸ (rec [] (⊕ (⊗) (⊗ int [0:α]))))
                                       (ref [0])))
                                in
                              (app
                                 (<1>
                                    : ((⊗ (ref [0])
                                         (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int))
                                           (rec [] (⊕ (⊗) (⊗ int [0:α])))))
                                        ⊸ (rec [] (⊕ (⊗) (⊗ int [0:α])))))
                                 (tup (<0> : (ref [0]))
                                    (tup (<7:f> : (exists [] ((⊗ (ref [0]) int) ⊸ int)))
                                       (<3:tl> : (rec [] (⊕ (⊗) (⊗ int [0:α]))))
                                     : (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int))
                                         (rec [] (⊕ (⊗) (⊗ int [0:α])))))
                                  : (⊗ (ref [0])
                                      (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int [0:α]))))))
                                 : (rec [] (⊕ (⊗) (⊗ int [0:α]))))
                          : (rec [] (⊕ (⊗) (⊗ int [0:α])))) : (rec [] (⊕ (⊗) (⊗ int [0:α]))))
                     : (⊗ int (rec [] (⊕ (⊗) (⊗ int [0:α])))))
                    : (⊕ (⊗) (⊗ int (rec [] (⊕ (⊗) (⊗ int [0:α]))))))
                : (⊕ (⊗) (⊗ int (rec [] (⊕ (⊗) (⊗ int [0:α])))))))
            : (⊕ (⊗) (⊗ int (rec [] (⊕ (⊗) (⊗ int [0:α]))))))
           : (rec [] (⊕ (⊗) (⊗ int [0:α]))))
         : (rec [] (⊕ (⊗) (⊗ int [0:α]))))
      : (rec [] (⊕ (⊗) (⊗ int [0:α])))))

    (let (<> : (rec [] (⊕ (⊗) (⊗ int [0:α])))) =
       (fold (rec [] (⊕ (⊗) (⊗ int [0:α])))
          (inj 0 (tup : (⊗)) : (⊕ (⊗) (⊗ int (rec [] (⊕ (⊗) (⊗ int [0:α]))))))
          : (rec [] (⊕ (⊗) (⊗ int [0:α]))))
       in
     (unpack
        (pack (⊗)
           (tup
              (coderef map_int
                 : ((⊗ (ref [0]) (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int [0:α])))))
                     ⊸ (rec [] (⊕ (⊗) (⊗ int [0:α])))))
              (new (tup : (⊗)) : (ref (⊗)))
            : (⊗
                ((⊗ (ref [0]) (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int [0:α]))))) ⊸
                  (rec [] (⊕ (⊗) (⊗ int [0:α]))))
                (ref (⊗))))
           : (exists []
               (⊗
                 ((⊗ (ref [0]) (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int [0:α]))))) ⊸
                   (rec [] (⊕ (⊗) (⊗ int [0:α]))))
                 (ref [0]))))
        <> (split
              (<> : ((⊗ (ref [0]) (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int [0:α])))))
                      ⊸ (rec [] (⊕ (⊗) (⊗ int [0:α])))))
              (<> : (ref [0])) =
              (<0>
                 : (⊗
                     ((⊗ (ref [0]) (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int [0:α])))))
                       ⊸ (rec [] (⊕ (⊗) (⊗ int [0:α]))))
                     (ref [0])))
              in
            (app
               (<1>
                  : ((⊗ (ref [0]) (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int [0:α])))))
                      ⊸ (rec [] (⊕ (⊗) (⊗ int [0:α])))))
               (tup (<0> : (ref [0]))
                  (tup
                     (pack (⊗)
                        (tup (coderef lam_1 : ((⊗ (ref (⊗)) int) ⊸ int)) (new (tup : (⊗)) : (ref (⊗)))
                         : (⊗ ((⊗ (ref (⊗)) int) ⊸ int) (ref (⊗))))
                        : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))))
                     (<3:lst> : (rec [] (⊕ (⊗) (⊗ int [0:α]))))
                   : (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int [0:α])))))
                : (⊗ (ref [0]) (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int [0:α]))))))
               : (rec [] (⊕ (⊗) (⊗ int [0:α]))))
        : (rec [] (⊕ (⊗) (⊗ int [0:α])))) : (rec [] (⊕ (⊗) (⊗ int [0:α]))))
     : (rec [] (⊕ (⊗) (⊗ int [0:α]))))
    -----------boxed_list-----------
    (fun lam_1 (<> : (⊗ (ref (⊗)) int)) : int .
      (split (<> : (ref (⊗))) (<> : int) = (<0> : (⊗ (ref (⊗)) int)) in
       (split  = (free (<1> : (ref (⊗))) : (⊗)) in
        (let (<> : int) = (<0> : int) in
         (+ (<0:x> : int) (1 : int) : int)
         : int) : int)
      : int))

    (fun map_int
      (<> : (⊗ (ref (⊗)) (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))) :
      (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))) .
      (split (<> : (ref (⊗)))
         (<> : (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))) =
         (<0>
            : (⊗ (ref (⊗)) (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))))
         in
       (split (<> : (exists [] ((⊗ (ref [0]) int) ⊸ int))) (<> : (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))) =
          (<0:p> : (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))) in
        (fold (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))
           (cases (unfold (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))
                     (<0:lst> : (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
                     : (⊕ (⊗) (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))))
              (case (<> : (⊗))
                (inj 0 (<0:nil> : (⊗)) : (⊕ (⊗) (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))))))
              (case (<> : (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))))
                (split (<> : int) (<> : (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))) =
                   (<0:cons> : (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))) in
                 (inj 1
                    (tup
                       (unpack (<4:f> : (exists [] ((⊗ (ref [0]) int) ⊸ int)))
                          <> (split (<> : ((⊗ (ref [0]) int) ⊸ int)) (<> :
                                (ref [0])) = (<0> : (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))) in
                              (app (<1> : ((⊗ (ref [0]) int) ⊸ int))
                                 (tup (<0> : (ref [0])) (<4:hd> : int) : (⊗ (ref [0]) int)) : int)
                          : int) : int)
                       (new
                          (unpack
                             (pack (⊗)
                                (tup
                                   (coderef map_int
                                      : ((⊗ (ref [0])
                                           (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int))
                                             (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
                                          ⊸ (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
                                   (new (tup : (⊗)) : (ref (⊗)))
                                 : (⊗
                                     ((⊗ (ref [0])
                                        (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int))
                                          (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
                                       ⊸ (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
                                     (ref (⊗))))
                                : (exists []
                                    (⊗
                                      ((⊗ (ref [0])
                                         (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int))
                                           (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
                                        ⊸ (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
                                      (ref [0]))))
                             <> (split
                                   (<> : ((⊗ (ref [0])
                                            (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int))
                                              (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
                                           ⊸ (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
                                   (<> : (ref [0])) =
                                   (<0>
                                      : (⊗
                                          ((⊗ (ref [0])
                                             (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int))
                                               (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
                                            ⊸ (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
                                          (ref [0])))
                                   in
                                 (app
                                    (<1>
                                       : ((⊗ (ref [0])
                                            (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int))
                                              (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
                                           ⊸ (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
                                    (tup (<0> : (ref [0]))
                                       (tup (<7:f> : (exists [] ((⊗ (ref [0]) int) ⊸ int)))
                                          (free (<3:tl> : (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
                                             : (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
                                        : (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int))
                                            (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
                                     : (⊗ (ref [0])
                                         (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int))
                                           (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))))
                                    : (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
                             : (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))) :
                             (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
                          : (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
                     : (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))))
                    : (⊕ (⊗) (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))))
                : (⊕ (⊗) (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))))))
            : (⊕ (⊗) (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))))
           : (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
         : (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
      : (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))

    (let (<> : (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))) =
       (fold (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))
          (inj 1
             (tup (5 : int)
                (new
                   (fold (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))
                      (inj 0 (tup : (⊗)) : (⊕ (⊗) (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))))
                      : (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
                   : (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
              : (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))))
             : (⊕ (⊗) (⊗ int (ref (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))))
          : (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
       in
     (unpack
        (pack (⊗)
           (tup
              (coderef map_int
                 : ((⊗ (ref [0])
                      (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
                     ⊸ (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
              (new (tup : (⊗)) : (ref (⊗)))
            : (⊗
                ((⊗ (ref [0])
                   (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
                  ⊸ (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
                (ref (⊗))))
           : (exists []
               (⊗
                 ((⊗ (ref [0])
                    (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
                   ⊸ (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
                 (ref [0]))))
        <> (split
              (<> : ((⊗ (ref [0])
                       (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
                      ⊸ (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
              (<> : (ref [0])) =
              (<0>
                 : (⊗
                     ((⊗ (ref [0])
                        (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
                       ⊸ (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
                     (ref [0])))
              in
            (app
               (<1>
                  : ((⊗ (ref [0])
                       (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
                      ⊸ (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
               (tup (<0> : (ref [0]))
                  (tup
                     (pack (⊗)
                        (tup (coderef lam_1 : ((⊗ (ref (⊗)) int) ⊸ int)) (new (tup : (⊗)) : (ref (⊗)))
                         : (⊗ ((⊗ (ref (⊗)) int) ⊸ int) (ref (⊗))))
                        : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))))
                     (<3:lst> : (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
                   : (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))))
                : (⊗ (ref [0])
                    (⊗ (exists [] ((⊗ (ref [0]) int) ⊸ int)) (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))))
               : (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
        : (rec [] (⊕ (⊗) (⊗ int (ref [0:α]))))) : (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
     : (rec [] (⊕ (⊗) (⊗ int (ref [0:α])))))
    -----------peano_3-----------
    (fold (rec [] (⊕ (⊗) (ref [0:a])))
       (inj 1
          (new
             (fold (rec [] (⊕ (⊗) (ref [0:a])))
                (inj 1
                   (new
                      (fold (rec [] (⊕ (⊗) (ref [0:a])))
                         (inj 1
                            (new
                               (fold (rec [] (⊕ (⊗) (ref [0:a])))
                                  (inj 0 (tup : (⊗)) : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a]))))))
                                  : (rec [] (⊕ (⊗) (ref [0:a]))))
                               : (ref (rec [] (⊕ (⊗) (ref [0:a])))))
                            : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a]))))))
                         : (rec [] (⊕ (⊗) (ref [0:a]))))
                      : (ref (rec [] (⊕ (⊗) (ref [0:a])))))
                   : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a]))))))
                : (rec [] (⊕ (⊗) (ref [0:a]))))
             : (ref (rec [] (⊕ (⊗) (ref [0:a])))))
          : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a]))))))
       : (rec [] (⊕ (⊗) (ref [0:a]))))
    -----------peano-----------
    (fun add (<> : (⊗ (ref (⊗)) (⊗ (rec [] (⊕ (⊗) (ref [0:a]))) (rec [] (⊕ (⊗) (ref [0:a])))))) :
      (rec [] (⊕ (⊗) (ref [0:a]))) .
      (split (<> : (ref (⊗))) (<> : (⊗ (rec [] (⊕ (⊗) (ref [0:a]))) (rec [] (⊕ (⊗) (ref [0:a]))))) =
         (<0> : (⊗ (ref (⊗)) (⊗ (rec [] (⊕ (⊗) (ref [0:a]))) (rec [] (⊕ (⊗) (ref [0:a])))))) in
       (split (<> : (rec [] (⊕ (⊗) (ref [0:a])))) (<> : (rec [] (⊕ (⊗) (ref [0:a])))) =
          (<0:p> : (⊗ (rec [] (⊕ (⊗) (ref [0:a]))) (rec [] (⊕ (⊗) (ref [0:a]))))) in
        (cases (unfold (rec [] (⊕ (⊗) (ref [0:a]))) (<1:left> : (rec [] (⊕ (⊗) (ref [0:a]))))
                  : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a]))))))
           (case (<> : (⊗)) (<1:right> : (rec [] (⊕ (⊗) (ref [0:a])))))
           (case (<> : (ref (rec [] (⊕ (⊗) (ref [0:a])))))
             (fold (rec [] (⊕ (⊗) (ref [0:a])))
                (inj 1
                   (new
                      (unpack
                         (pack (⊗)
                            (tup
                               (coderef add
                                  : ((⊗ (ref [0])
                                       (⊗ (rec [] (⊕ (⊗) (ref [0:a]))) (rec [] (⊕ (⊗) (ref [0:a])))))
                                      ⊸ (rec [] (⊕ (⊗) (ref [0:a])))))
                               (new (tup : (⊗)) : (ref (⊗)))
                             : (⊗
                                 ((⊗ (ref [0]) (⊗ (rec [] (⊕ (⊗) (ref [0:a]))) (rec [] (⊕ (⊗) (ref [0:a])))))
                                   ⊸ (rec [] (⊕ (⊗) (ref [0:a]))))
                                 (ref (⊗))))
                            : (exists []
                                (⊗
                                  ((⊗ (ref [0]) (⊗ (rec [] (⊕ (⊗) (ref [0:a]))) (rec [] (⊕ (⊗) (ref [0:a])))))
                                    ⊸ (rec [] (⊕ (⊗) (ref [0:a]))))
                                  (ref [0]))))
                         <> (split
                               (<> : ((⊗ (ref [0])
                                        (⊗ (rec [] (⊕ (⊗) (ref [0:a]))) (rec [] (⊕ (⊗) (ref [0:a])))))
                                       ⊸ (rec [] (⊕ (⊗) (ref [0:a])))))
                               (<> : (ref [0])) =
                               (<0>
                                  : (⊗
                                      ((⊗ (ref [0])
                                         (⊗ (rec [] (⊕ (⊗) (ref [0:a]))) (rec [] (⊕ (⊗) (ref [0:a])))))
                                        ⊸ (rec [] (⊕ (⊗) (ref [0:a]))))
                                      (ref [0])))
                               in
                             (app
                                (<1>
                                   : ((⊗ (ref [0])
                                        (⊗ (rec [] (⊕ (⊗) (ref [0:a]))) (rec [] (⊕ (⊗) (ref [0:a])))))
                                       ⊸ (rec [] (⊕ (⊗) (ref [0:a])))))
                                (tup (<0> : (ref [0]))
                                   (tup
                                      (free (<3:succ> : (ref (rec [] (⊕ (⊗) (ref [0:a])))))
                                         : (rec [] (⊕ (⊗) (ref [0:a]))))
                                      (<4:right> : (rec [] (⊕ (⊗) (ref [0:a]))))
                                    : (⊗ (rec [] (⊕ (⊗) (ref [0:a]))) (rec [] (⊕ (⊗) (ref [0:a])))))
                                 : (⊗ (ref [0]) (⊗ (rec [] (⊕ (⊗) (ref [0:a]))) (rec [] (⊕ (⊗) (ref [0:a]))))))
                                : (rec [] (⊕ (⊗) (ref [0:a]))))
                         : (rec [] (⊕ (⊗) (ref [0:a])))) : (rec [] (⊕ (⊗) (ref [0:a]))))
                      : (ref (rec [] (⊕ (⊗) (ref [0:a])))))
                   : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a]))))))
                : (rec [] (⊕ (⊗) (ref [0:a])))))
         : (rec [] (⊕ (⊗) (ref [0:a])))) : (rec [] (⊕ (⊗) (ref [0:a]))))
      : (rec [] (⊕ (⊗) (ref [0:a])))))

    (fun from-int (<> : (⊗ (ref (⊗)) int)) : (rec [] (⊕ (⊗) (ref [0:a]))) .
      (split (<> : (ref (⊗))) (<> : int) = (<0> : (⊗ (ref (⊗)) int)) in
       (fold (rec [] (⊕ (⊗) (ref [0:a])))
          (if0 (<0:int> : int)
           then (inj 0 (tup : (⊗)) : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a]))))))
           else
             (inj 1
                (new
                   (unpack
                      (pack (⊗)
                         (tup (coderef from-int : ((⊗ (ref [0]) int) ⊸ (rec [] (⊕ (⊗) (ref [0:a])))))
                            (new (tup : (⊗)) : (ref (⊗)))
                          : (⊗ ((⊗ (ref [0]) int) ⊸ (rec [] (⊕ (⊗) (ref [0:a])))) (ref (⊗))))
                         : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ (rec [] (⊕ (⊗) (ref [0:a])))) (ref [0]))))
                      <> (split (<> : ((⊗ (ref [0]) int) ⊸ (rec [] (⊕ (⊗) (ref [0:a]))))) (<> :
                            (ref [0])) = (<0> : (⊗ ((⊗ (ref [0]) int) ⊸ (rec [] (⊕ (⊗) (ref [0:a])))) (ref [0])))
                            in
                          (app (<1> : ((⊗ (ref [0]) int) ⊸ (rec [] (⊕ (⊗) (ref [0:a])))))
                             (tup (<0> : (ref [0])) (- (<3:int> : int) (1 : int) : int) : (⊗ (ref [0]) int))
                             : (rec [] (⊕ (⊗) (ref [0:a]))))
                      : (rec [] (⊕ (⊗) (ref [0:a])))) : (rec [] (⊕ (⊗) (ref [0:a]))))
                   : (ref (rec [] (⊕ (⊗) (ref [0:a])))))
                : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a]))))))
           : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a]))))))
          : (rec [] (⊕ (⊗) (ref [0:a]))))
      : (rec [] (⊕ (⊗) (ref [0:a])))))

    (fun to-int (<> : (⊗ (ref (⊗)) (rec [] (⊕ (⊗) (ref [0:a]))))) : int .
      (split (<> : (ref (⊗))) (<> : (rec [] (⊕ (⊗) (ref [0:a])))) =
         (<0> : (⊗ (ref (⊗)) (rec [] (⊕ (⊗) (ref [0:a]))))) in
       (cases (unfold (rec [] (⊕ (⊗) (ref [0:a]))) (<0:peano> : (rec [] (⊕ (⊗) (ref [0:a]))))
                 : (⊕ (⊗) (ref (rec [] (⊕ (⊗) (ref [0:a]))))))
          (case (<> : (⊗)) (0 : int))
          (case (<> : (ref (rec [] (⊕ (⊗) (ref [0:a])))))
            (+ (1 : int)
               (unpack
                  (pack (⊗)
                     (tup (coderef to-int : ((⊗ (ref [0]) (rec [] (⊕ (⊗) (ref [0:a])))) ⊸ int))
                        (new (tup : (⊗)) : (ref (⊗)))
                      : (⊗ ((⊗ (ref [0]) (rec [] (⊕ (⊗) (ref [0:a])))) ⊸ int) (ref (⊗))))
                     : (exists [] (⊗ ((⊗ (ref [0]) (rec [] (⊕ (⊗) (ref [0:a])))) ⊸ int) (ref [0]))))
                  <> (split (<> : ((⊗ (ref [0]) (rec [] (⊕ (⊗) (ref [0:a])))) ⊸ int)) (<> :
                        (ref [0])) = (<0> : (⊗ ((⊗ (ref [0]) (rec [] (⊕ (⊗) (ref [0:a])))) ⊸ int) (ref [0]))) in
                      (app (<1> : ((⊗ (ref [0]) (rec [] (⊕ (⊗) (ref [0:a])))) ⊸ int))
                         (tup (<0> : (ref [0]))
                            (free (<3:succ> : (ref (rec [] (⊕ (⊗) (ref [0:a]))))) : (rec [] (⊕ (⊗) (ref [0:a]))))
                          : (⊗ (ref [0]) (rec [] (⊕ (⊗) (ref [0:a])))))
                         : int)
                  : int) : int)
               : int))
        : int)
      : int))

    (let (<> : (rec [] (⊕ (⊗) (ref [0:a])))) =
       (unpack
          (pack (⊗)
             (tup (coderef from-int : ((⊗ (ref [0]) int) ⊸ (rec [] (⊕ (⊗) (ref [0:a])))))
                (new (tup : (⊗)) : (ref (⊗)))
              : (⊗ ((⊗ (ref [0]) int) ⊸ (rec [] (⊕ (⊗) (ref [0:a])))) (ref (⊗))))
             : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ (rec [] (⊕ (⊗) (ref [0:a])))) (ref [0]))))
          <> (split (<> : ((⊗ (ref [0]) int) ⊸ (rec [] (⊕ (⊗) (ref [0:a]))))) (<> :
                (ref [0])) = (<0> : (⊗ ((⊗ (ref [0]) int) ⊸ (rec [] (⊕ (⊗) (ref [0:a])))) (ref [0]))) in
              (app (<1> : ((⊗ (ref [0]) int) ⊸ (rec [] (⊕ (⊗) (ref [0:a])))))
                 (tup (<0> : (ref [0])) (6 : int) : (⊗ (ref [0]) int)) :
                 (rec [] (⊕ (⊗) (ref [0:a]))))
          : (rec [] (⊕ (⊗) (ref [0:a])))) : (rec [] (⊕ (⊗) (ref [0:a]))))
       in
     (let (<> : (rec [] (⊕ (⊗) (ref [0:a])))) =
        (unpack
           (pack (⊗)
              (tup (coderef from-int : ((⊗ (ref [0]) int) ⊸ (rec [] (⊕ (⊗) (ref [0:a])))))
                 (new (tup : (⊗)) : (ref (⊗)))
               : (⊗ ((⊗ (ref [0]) int) ⊸ (rec [] (⊕ (⊗) (ref [0:a])))) (ref (⊗))))
              : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ (rec [] (⊕ (⊗) (ref [0:a])))) (ref [0]))))
           <> (split (<> : ((⊗ (ref [0]) int) ⊸ (rec [] (⊕ (⊗) (ref [0:a]))))) (<> :
                 (ref [0])) = (<0> : (⊗ ((⊗ (ref [0]) int) ⊸ (rec [] (⊕ (⊗) (ref [0:a])))) (ref [0]))) in
               (app (<1> : ((⊗ (ref [0]) int) ⊸ (rec [] (⊕ (⊗) (ref [0:a])))))
                  (tup (<0> : (ref [0])) (7 : int) : (⊗ (ref [0]) int)) :
                  (rec [] (⊕ (⊗) (ref [0:a]))))
           : (rec [] (⊕ (⊗) (ref [0:a])))) : (rec [] (⊕ (⊗) (ref [0:a]))))
        in
      (let (<> : (rec [] (⊕ (⊗) (ref [0:a])))) =
         (unpack
            (pack (⊗)
               (tup
                  (coderef add
                     : ((⊗ (ref [0]) (⊗ (rec [] (⊕ (⊗) (ref [0:a]))) (rec [] (⊕ (⊗) (ref [0:a]))))) ⊸
                         (rec [] (⊕ (⊗) (ref [0:a])))))
                  (new (tup : (⊗)) : (ref (⊗)))
                : (⊗
                    ((⊗ (ref [0]) (⊗ (rec [] (⊕ (⊗) (ref [0:a]))) (rec [] (⊕ (⊗) (ref [0:a]))))) ⊸
                      (rec [] (⊕ (⊗) (ref [0:a]))))
                    (ref (⊗))))
               : (exists []
                   (⊗
                     ((⊗ (ref [0]) (⊗ (rec [] (⊕ (⊗) (ref [0:a]))) (rec [] (⊕ (⊗) (ref [0:a]))))) ⊸
                       (rec [] (⊕ (⊗) (ref [0:a]))))
                     (ref [0]))))
            <> (split
                  (<> : ((⊗ (ref [0]) (⊗ (rec [] (⊕ (⊗) (ref [0:a]))) (rec [] (⊕ (⊗) (ref [0:a]))))) ⊸
                          (rec [] (⊕ (⊗) (ref [0:a])))))
                  (<> : (ref [0])) =
                  (<0>
                     : (⊗
                         ((⊗ (ref [0]) (⊗ (rec [] (⊕ (⊗) (ref [0:a]))) (rec [] (⊕ (⊗) (ref [0:a]))))) ⊸
                           (rec [] (⊕ (⊗) (ref [0:a]))))
                         (ref [0])))
                  in
                (app
                   (<1>
                      : ((⊗ (ref [0]) (⊗ (rec [] (⊕ (⊗) (ref [0:a]))) (rec [] (⊕ (⊗) (ref [0:a]))))) ⊸
                          (rec [] (⊕ (⊗) (ref [0:a])))))
                   (tup (<0> : (ref [0]))
                      (tup (<4:six> : (rec [] (⊕ (⊗) (ref [0:a])))) (<3:seven> : (rec [] (⊕ (⊗) (ref [0:a]))))
                       : (⊗ (rec [] (⊕ (⊗) (ref [0:a]))) (rec [] (⊕ (⊗) (ref [0:a])))))
                    : (⊗ (ref [0]) (⊗ (rec [] (⊕ (⊗) (ref [0:a]))) (rec [] (⊕ (⊗) (ref [0:a]))))))
                   : (rec [] (⊕ (⊗) (ref [0:a]))))
            : (rec [] (⊕ (⊗) (ref [0:a])))) : (rec [] (⊕ (⊗) (ref [0:a]))))
         in
       (unpack
          (pack (⊗)
             (tup (coderef to-int : ((⊗ (ref [0]) (rec [] (⊕ (⊗) (ref [0:a])))) ⊸ int))
                (new (tup : (⊗)) : (ref (⊗)))
              : (⊗ ((⊗ (ref [0]) (rec [] (⊕ (⊗) (ref [0:a])))) ⊸ int) (ref (⊗))))
             : (exists [] (⊗ ((⊗ (ref [0]) (rec [] (⊕ (⊗) (ref [0:a])))) ⊸ int) (ref [0]))))
          <> (split (<> : ((⊗ (ref [0]) (rec [] (⊕ (⊗) (ref [0:a])))) ⊸ int)) (<> :
                (ref [0])) = (<0> : (⊗ ((⊗ (ref [0]) (rec [] (⊕ (⊗) (ref [0:a])))) ⊸ int) (ref [0]))) in
              (app (<1> : ((⊗ (ref [0]) (rec [] (⊕ (⊗) (ref [0:a])))) ⊸ int))
                 (tup (<0> : (ref [0])) (<3:sum> : (rec [] (⊕ (⊗) (ref [0:a]))))
                  : (⊗ (ref [0]) (rec [] (⊕ (⊗) (ref [0:a])))))
                 : int)
          : int) : int)
       : int)
      : int)
     : int)
    -----------mini_zip-----------
    (fun add1 (<> : (⊗ (ref (⊗)) int)) : int .
      (split (<> : (ref (⊗))) (<> : int) = (<0> : (⊗ (ref (⊗)) int)) in
       (+ (<0:x> : int) (1 : int) : int)
      : int))

    (export fun typle_add1 (<> : (⊗ (ref (⊗)) (⊗ int int))) : (⊗ int int) .
      (split (<> : (ref (⊗))) (<> : (⊗ int int)) = (<0> : (⊗ (ref (⊗)) (⊗ int int))) in
       (split (<> : int) (<> : int) = (<0:x> : (⊗ int int)) in
        (tup
           (unpack
              (pack (⊗)
                 (tup (coderef add1 : ((⊗ (ref [0]) int) ⊸ int)) (new (tup : (⊗)) : (ref (⊗)))
                  : (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref (⊗))))
                 : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))))
              <> (split (<> : ((⊗ (ref [0]) int) ⊸ int)) (<> : (ref [0])) =
                    (<0> : (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))) in
                  (app (<1> : ((⊗ (ref [0]) int) ⊸ int)) (tup (<0> : (ref [0])) (<4:x1> : int) : (⊗ (ref [0]) int))
                     : int)
              : int) : int)
           (unpack
              (pack (⊗)
                 (tup (coderef add1 : ((⊗ (ref [0]) int) ⊸ int)) (new (tup : (⊗)) : (ref (⊗)))
                  : (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref (⊗))))
                 : (exists [] (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))))
              <> (split (<> : ((⊗ (ref [0]) int) ⊸ int)) (<> : (ref [0])) =
                    (<0> : (⊗ ((⊗ (ref [0]) int) ⊸ int) (ref [0]))) in
                  (app (<1> : ((⊗ (ref [0]) int) ⊸ int)) (tup (<0> : (ref [0])) (<3:x2> : int) : (⊗ (ref [0]) int))
                     : int)
              : int) : int)
         : (⊗ int int)) : (⊗ int int))
      : (⊗ int int)))

    (fun mini_zip_specialized (<> : (⊗ (ref (⊗)) (⊗ (ref int) (ref (ref int))))) : (ref (⊗ int (ref int))) .
      (split (<> : (ref (⊗))) (<> : (⊗ (ref int) (ref (ref int)))) =
         (<0> : (⊗ (ref (⊗)) (⊗ (ref int) (ref (ref int))))) in
       (split (<> : (ref int)) (<> : (ref (ref int))) = (<0:p> : (⊗ (ref int) (ref (ref int)))) in
        (new (tup (free (<1:a> : (ref int)) : int) (free (<0:b> : (ref (ref int))) : (ref int)) : (⊗ int (ref int)))
           : (ref (⊗ int (ref int))))
         : (ref (⊗ int (ref int))))
      : (ref (⊗ int (ref int))))) |}]
