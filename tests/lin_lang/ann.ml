open! Base
open! Stdlib.Format
open! Richwasm_lin_lang
module AnnRichWasm = Richwasm_common.Annotated_syntax

include Help.MultiOutputter.Make (struct
  open Help

  type syntax = Syntax.Module.t
  type text = string
  type res = AnnRichWasm.Module.t

  let syntax_pipeline x =
    x
    |> Index.Compile.compile_module
    |> or_fail_pp Index.Err.pp
    |> Typecheck.Compile.compile_module
    |> or_fail_pp Typecheck.Err.pp
    |> Cc.Compile.compile_module
    |> or_fail_pp Cc.Compile.Err.pp
    |> Codegen.Compile.compile_module
    |> or_fail_pp Codegen.Err.pp
    |> Richwasm_common.Elaborate.elab_module
    |> or_fail_pp Richwasm_common.Elaborate.Err.pp


  let string_pipeline s = s |> Parse.from_string_exn |> syntax_pipeline
  let examples = Examples.all
  let pp = AnnRichWasm.Module.pp_roqc
  let pp_sexp = AnnRichWasm.Module.pp_sexp
end)

let%expect_test "basic functionality" =
  run {| 1 |};
  [%expect
    {xxx|
    {|
        m_imports := [];
        m_functions :=
          [{|
               mf_type :=
                 (MonoFunT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]);
               mf_locals := [];
               mf_body :=
                 [(INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 1)];
               |}];
        m_table := [];
        m_exports := [0];
        |} |xxx}];
  next ();
  [%expect
    {|
    ((m_imports ())
     (m_functions
      (((mf_type
         (MonoFunT () ((NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T)))))
        (mf_locals ())
        (mf_body
         ((INumConst
           (InstrT () ((NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T)))) 1))))))
     (m_table ()) (m_exports (0))) |}];

  run {| (1, 2, 3, 4) |};
  [%expect
    {|
    FAILURE TODO |}];
  next ();
  [%expect
    {|
    Failure ^^^ |}];

  run {| (tup (tup 1 (tup 2 3) 4 5) (tup 6 7)) |};
  [%expect
    {|
    FAILURE TODO |}];

  run {| (new 10) |};
  [%expect
    {|
    FAILURE TODO |}];

  run {| (1 + 2) |};
  [%expect
    {xxx|
    {|
        m_imports := [];
        m_functions :=
          [{|
               mf_type :=
                 (MonoFunT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]);
               mf_locals := [];
               mf_body :=
                 [(INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
                    (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
                    (INum (InstrT [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                     (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]
                    [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) (IInt2 I32T AddI))];
               |}];
        m_table := [];
        m_exports := [0];
        |} |xxx}];
  next ();
  [%expect
    {|
    ((m_imports ())
     (m_functions
      (((mf_type
         (MonoFunT () ((NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T)))))
        (mf_locals ())
        (mf_body
         ((INumConst
           (InstrT () ((NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T)))) 1)
          (INumConst
           (InstrT () ((NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T)))) 2)
          (INum
           (InstrT
            ((NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))
             (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T)))
            ((NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))))
           (IInt2 I32T AddI)))))))
     (m_table ()) (m_exports (0))) |}];

  ()


let%expect_test "examples" =
  output_examples ();
  [%expect
    {xxx|
    -----------one-----------
    {|
        m_imports := [];
        m_functions :=
          [{|
               mf_type :=
                 (MonoFunT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]);
               mf_locals := [];
               mf_body :=
                 [(INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 1)];
               |}];
        m_table := [];
        m_exports := [0];
        |}
    -----------flat_tuple-----------
    FAILURE TODO
    -----------nested_tuple-----------
    FAILURE TODO
    -----------single_sum-----------
    FAILURE TODO
    -----------double_sum-----------
    FAILURE TODO
    -----------arith_add-----------
    {|
        m_imports := [];
        m_functions :=
          [{|
               mf_type :=
                 (MonoFunT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]);
               mf_locals := [];
               mf_body :=
                 [(INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 9);
                    (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 10);
                    (INum (InstrT [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                     (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]
                    [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) (IInt2 I32T AddI))];
               |}];
        m_table := [];
        m_exports := [0];
        |}
    -----------arith_sub-----------
    {|
        m_imports := [];
        m_functions :=
          [{|
               mf_type :=
                 (MonoFunT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]);
               mf_locals := [];
               mf_body :=
                 [(INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 67);
                    (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 41);
                    (INum (InstrT [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                     (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]
                    [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) (IInt2 I32T SubI))];
               |}];
        m_table := [];
        m_exports := [0];
        |}
    -----------arith_mul-----------
    {|
        m_imports := [];
        m_functions :=
          [{|
               mf_type :=
                 (MonoFunT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]);
               mf_locals := [];
               mf_body :=
                 [(INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 42);
                    (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 10);
                    (INum (InstrT [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                     (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]
                    [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) (IInt2 I32T MulI))];
               |}];
        m_table := [];
        m_exports := [0];
        |}
    -----------arith_div-----------
    {|
        m_imports := [];
        m_functions :=
          [{|
               mf_type :=
                 (MonoFunT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]);
               mf_locals := [];
               mf_body :=
                 [(INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) -30);
                    (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 10);
                    (INum (InstrT [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                     (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]
                    [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) (IInt2 I32T (DivI SignS)))];
               |}];
        m_table := [];
        m_exports := [0];
        |}
    -----------app_ident-----------
    FAILURE TODO
    -----------nested_arith-----------
    {|
        m_imports := [];
        m_functions :=
          [{|
               mf_type :=
                 (MonoFunT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]);
               mf_locals := [];
               mf_body :=
                 [(INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 9);
                    (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 10);
                    (INum (InstrT [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                     (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]
                    [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) (IInt2 I32T AddI));
                    (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 5);
                    (INum (InstrT [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                     (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]
                    [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) (IInt2 I32T MulI))];
               |}];
        m_table := [];
        m_exports := [0];
        |}
    -----------let_bind-----------
    FAILURE TODO
    -----------add_one_program-----------
    FAILURE TODO
    -----------add_tup_ref-----------
    FAILURE TODO
    -----------print_10-----------
    FAILURE TODO
    -----------factorial_program-----------
    FAILURE TODO
    -----------safe_div-----------
    FAILURE TODO
    -----------incr_n-----------
    FAILURE TODO
    -----------fix_factorial[invalid]-----------
    FAILURE (Ctx (CannotFindRep (Var (0 ())))
     (Exists
      (Lollipop
       (Prod
        ((Var (0 ()))
         (Exists
          (Lollipop
           (Prod
            ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
           (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))
       (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int)))))
    -----------unboxed_list[invlaid]-----------
    FAILURE (Ctx (CannotFindRep (Var (0 ("\206\177"))))
     (Rec (Sum ((Prod ()) (Prod (Int (Var (0 ("\206\177")))))))))
    -----------boxed_list-----------
    FAILURE (Ctx (CannotFindRep (Var (0 ())))
     (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))) |xxx}]
