open! Core
open! Stdlib.Format
open! Test_support
module AnnRichWasm = Richwasm_common.Annotated_syntax

include Test_runner.MultiOutputter.Make (struct
  open Test_utils
  open Richwasm_lin_lang

  type syntax = Syntax.Module.t
  type text = string
  type res = AnnRichWasm.Module.t

  let elab x =
    x
    |> Richwasm_common.Elaborate.elab_module
    |> or_fail_pp Richwasm_common.Elaborate.Err.pp

  let syntax_pipeline x =
    x |> Main.compile_ast |> or_fail_pp Main.CompileErr.pp |> elab

  let string_pipeline s = s |> Parse.from_string_exn |> syntax_pipeline
  let examples = Test_examples.Lin_lang.all
  let pp = AnnRichWasm.Module.pp_roqc
  let pp_raw = AnnRichWasm.Module.pp_sexp
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
         (MonoFunT () ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))))
        (mf_locals ())
        (mf_body
         ((INumConst
           (InstrT () ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))) 1))))))
     (m_table ()) (m_exports (0))) |}];

  run {| (1, 2, 3, 4) |};
  [%expect
    {xxx|
    {|
        m_imports := [];
        m_functions :=
          [{|
               mf_type :=
                 (MonoFunT [] [(ProdT (VALTYPE (ProdR [(PrimR I32R);
                                                         (PrimR I32R);
                                                         (PrimR I32R);
                                                         (PrimR I32R)]) ImCopy ImDrop)
                                 [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                    (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                    (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                    (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))])]);
               mf_locals := [];
               mf_body :=
                 [(INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
                    (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
                    (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
                    (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
                    (IGroup (InstrT [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                       (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                       (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                       (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]
                    [(ProdT (VALTYPE (ProdR [(PrimR I32R);
                                               (PrimR I32R);
                                               (PrimR I32R);
                                               (PrimR I32R)]) ImCopy ImDrop)
                       [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                          (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                          (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                          (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))])]))];
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
         (MonoFunT ()
          ((ProdT
            (VALTYPE (ProdR ((AtomR I32R) (AtomR I32R) (AtomR I32R) (AtomR I32R)))
             ImCopy ImDrop)
            ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
             (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
             (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
             (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))))))
        (mf_locals ())
        (mf_body
         ((INumConst
           (InstrT () ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))) 1)
          (INumConst
           (InstrT () ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))) 2)
          (INumConst
           (InstrT () ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))) 3)
          (INumConst
           (InstrT () ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))) 4)
          (IGroup
           (InstrT
            ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
             (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
             (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
             (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))
            ((ProdT
              (VALTYPE
               (ProdR ((AtomR I32R) (AtomR I32R) (AtomR I32R) (AtomR I32R))) ImCopy
               ImDrop)
              ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
               (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
               (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
               (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))))))))))
     (m_table ()) (m_exports (0))) |}];

  run {| (tup (tup 1 (tup 2 3) 4 5) (tup 6 7)) |};
  [%expect
    {xxx|
    {|
        m_imports := [];
        m_functions :=
          [{|
               mf_type :=
                 (MonoFunT [] [(ProdT (VALTYPE (ProdR [(ProdR [(PrimR I32R);
                                                                 (ProdR [
                                                                        (PrimR I32R);
                                                                        (PrimR I32R)]);
                                                                 (PrimR I32R);
                                                                 (PrimR I32R)]);
                                                         (ProdR [(PrimR I32R);
                                                                   (PrimR I32R)])]) ImCopy ImDrop)
                                 [(ProdT (VALTYPE (ProdR [(PrimR I32R);
                                                            (ProdR [(PrimR I32R);
                                                                      (PrimR I32R)]);
                                                            (PrimR I32R);
                                                            (PrimR I32R)]) ImCopy ImDrop)
                                    [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                       (ProdT (VALTYPE (ProdR [(PrimR I32R);
                                                                 (PrimR I32R)]) ImCopy ImDrop)
                                       [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                          (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]);
                                       (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                       (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]);
                                    (ProdT (VALTYPE (ProdR [(PrimR I32R);
                                                              (PrimR I32R)]) ImCopy ImDrop)
                                    [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                       (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))])])]);
               mf_locals := [];
               mf_body :=
                 [(INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
                    (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
                    (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
                    (IGroup (InstrT [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                       (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]
                    [(ProdT (VALTYPE (ProdR [(PrimR I32R); (PrimR I32R)]) ImCopy ImDrop)
                       [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                          (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))])]));
                    (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
                    (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 5);
                    (IGroup (InstrT [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                       (ProdT (VALTYPE (ProdR [(PrimR I32R);
                                                                 (PrimR I32R)]) ImCopy ImDrop)
                                       [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                          (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]);
                                       (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                       (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]
                    [(ProdT (VALTYPE (ProdR [(PrimR I32R);
                                               (ProdR [(PrimR I32R); (PrimR I32R)]);
                                               (PrimR I32R);
                                               (PrimR I32R)]) ImCopy ImDrop)
                       [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                          (ProdT (VALTYPE (ProdR [(PrimR I32R); (PrimR I32R)]) ImCopy ImDrop)
                          [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                             (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]);
                          (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                          (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))])]));
                    (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 6);
                    (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 7);
                    (IGroup (InstrT [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                       (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]
                    [(ProdT (VALTYPE (ProdR [(PrimR I32R); (PrimR I32R)]) ImCopy ImDrop)
                       [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                          (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))])]));
                    (IGroup (InstrT [(ProdT (VALTYPE (ProdR [(PrimR I32R);
                                                               (ProdR [(PrimR I32R);
                                                                        (PrimR I32R)]);
                                                               (PrimR I32R);
                                                               (PrimR I32R)]) ImCopy ImDrop)
                                       [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                          (ProdT (VALTYPE (ProdR [(PrimR I32R);
                                                                    (PrimR I32R)]) ImCopy ImDrop)
                                          [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                             (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]);
                                          (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                          (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]);
                                       (ProdT (VALTYPE (ProdR [(PrimR I32R);
                                                                 (PrimR I32R)]) ImCopy ImDrop)
                                       [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                          (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))])]
                    [(ProdT (VALTYPE (ProdR [(ProdR [(PrimR I32R);
                                                       (ProdR [(PrimR I32R);
                                                                 (PrimR I32R)]);
                                                       (PrimR I32R);
                                                       (PrimR I32R)]);
                                               (ProdR [(PrimR I32R); (PrimR I32R)])]) ImCopy ImDrop)
                       [(ProdT (VALTYPE (ProdR [(PrimR I32R);
                                                  (ProdR [(PrimR I32R);
                                                            (PrimR I32R)]);
                                                  (PrimR I32R);
                                                  (PrimR I32R)]) ImCopy ImDrop)
                          [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                             (ProdT (VALTYPE (ProdR [(PrimR I32R); (PrimR I32R)]) ImCopy ImDrop)
                             [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]);
                             (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                             (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]);
                          (ProdT (VALTYPE (ProdR [(PrimR I32R); (PrimR I32R)]) ImCopy ImDrop)
                          [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                             (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))])])]))];
               |}];
        m_table := [];
        m_exports := [0];
        |} |xxx}];

  run {| (new 10) |};
  [%expect {|
    FAILURE (TODO memory) |}];

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
         (MonoFunT () ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))))
        (mf_locals ())
        (mf_body
         ((INumConst
           (InstrT () ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))) 1)
          (INumConst
           (InstrT () ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))) 2)
          (INum
           (InstrT
            ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
             (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))
            ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))
           (IInt2 I32T AddI)))))))
     (m_table ()) (m_exports (0))) |}];

  (* run {| (fun foo ()) |}; *)
  (* [%expect {| *)
    (* FAILURE (TODO memory) |}]; *)
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
    {|
        m_imports := [];
        m_functions :=
          [{|
               mf_type :=
                 (MonoFunT [] [(ProdT (VALTYPE (ProdR [(PrimR I32R);
                                                         (PrimR I32R);
                                                         (PrimR I32R);
                                                         (PrimR I32R)]) ImCopy ImDrop)
                                 [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                    (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                    (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                    (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))])]);
               mf_locals := [];
               mf_body :=
                 [(INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
                    (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
                    (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
                    (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
                    (IGroup (InstrT [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                       (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                       (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                       (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]
                    [(ProdT (VALTYPE (ProdR [(PrimR I32R);
                                               (PrimR I32R);
                                               (PrimR I32R);
                                               (PrimR I32R)]) ImCopy ImDrop)
                       [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                          (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                          (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                          (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))])]))];
               |}];
        m_table := [];
        m_exports := [0];
        |}
    -----------nested_tuple-----------
    {|
        m_imports := [];
        m_functions :=
          [{|
               mf_type :=
                 (MonoFunT [] [(ProdT (VALTYPE (ProdR [(ProdR [(PrimR I32R);
                                                                 (PrimR I32R)]);
                                                         (ProdR [(PrimR I32R);
                                                                   (PrimR I32R)])]) ImCopy ImDrop)
                                 [(ProdT (VALTYPE (ProdR [(PrimR I32R);
                                                            (PrimR I32R)]) ImCopy ImDrop)
                                    [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                       (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]);
                                    (ProdT (VALTYPE (ProdR [(PrimR I32R);
                                                              (PrimR I32R)]) ImCopy ImDrop)
                                    [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                       (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))])])]);
               mf_locals := [];
               mf_body :=
                 [(INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
                    (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
                    (IGroup (InstrT [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                       (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]
                    [(ProdT (VALTYPE (ProdR [(PrimR I32R); (PrimR I32R)]) ImCopy ImDrop)
                       [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                          (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))])]));
                    (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
                    (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
                    (IGroup (InstrT [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                       (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]
                    [(ProdT (VALTYPE (ProdR [(PrimR I32R); (PrimR I32R)]) ImCopy ImDrop)
                       [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                          (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))])]));
                    (IGroup (InstrT [(ProdT (VALTYPE (ProdR [(PrimR I32R);
                                                               (PrimR I32R)]) ImCopy ImDrop)
                                       [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                          (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]);
                                       (ProdT (VALTYPE (ProdR [(PrimR I32R);
                                                                 (PrimR I32R)]) ImCopy ImDrop)
                                       [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                                          (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))])]
                    [(ProdT (VALTYPE (ProdR [(ProdR [(PrimR I32R); (PrimR I32R)]);
                                               (ProdR [(PrimR I32R); (PrimR I32R)])]) ImCopy ImDrop)
                       [(ProdT (VALTYPE (ProdR [(PrimR I32R); (PrimR I32R)]) ImCopy ImDrop)
                          [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                             (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]);
                          (ProdT (VALTYPE (ProdR [(PrimR I32R); (PrimR I32R)]) ImCopy ImDrop)
                          [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                             (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))])])]))];
               |}];
        m_table := [];
        m_exports := [0];
        |}
    -----------single_sum-----------
    {|
        m_imports := [];
        m_functions :=
          [{|
               mf_type :=
                 (MonoFunT [] [(SumT (VALTYPE (SumR [(ProdR [])]) ImCopy ImDrop)
                                 [(ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [
                                                                        ])])]);
               mf_locals := [];
               mf_body :=
                 [(IGroup (InstrT [] [(ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [
                                                                        ])]));
                    (IInject (InstrT [(ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [
                                                                        ])]
                    [(SumT (VALTYPE (SumR [(ProdR [])]) ImCopy ImDrop) [(ProdT (VALTYPE (ProdR
                                                                        [
                                                                        ]) ImCopy ImDrop)
                                                                        [
                                                                        ])])]) 0)];
               |}];
        m_table := [];
        m_exports := [0];
        |}
    -----------double_sum-----------
    {|
        m_imports := [];
        m_functions :=
          [{|
               mf_type :=
                 (MonoFunT [] [(SumT (VALTYPE (SumR [(ProdR []); (PrimR I32R)]) ImCopy ImDrop)
                                 [(ProdT (VALTYPE (ProdR []) ImCopy ImDrop)
                                    []);
                                    (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))])]);
               mf_locals := [];
               mf_body :=
                 [(INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 15);
                    (IInject (InstrT [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]
                    [(SumT (VALTYPE (SumR [(ProdR []); (PrimR I32R)]) ImCopy ImDrop)
                       [(ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                          (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))])]) 1)];
               |}];
        m_table := [];
        m_exports := [0];
        |}
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
    FAILURE (UnexpectedUnitializedLocal 0)
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
    {|
        m_imports := [];
        m_functions :=
          [{|
               mf_type :=
                 (MonoFunT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]);
               mf_locals := [(PrimR I32R)];
               mf_body :=
                 [(INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 10);
                    (ILocalSet (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 0);
                    (ILocalGet (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 0)];
               |}];
        m_table := [];
        m_exports := [0];
        |}
    -----------add_one_program-----------
    FAILURE (InvalidLocalIdx 0)
    -----------add_tup_ref-----------
    FAILURE (TODO memory)
    -----------print_10-----------
    FAILURE (InvalidTableIdx 0)
    -----------factorial_program-----------
    FAILURE (UnexpectedUnitializedLocal 0)
    -----------safe_div-----------
    FAILURE (UnexpectedUnitializedLocal 0)
    -----------incr_n-----------
    FAILURE (UnexpectedUnitializedLocal 0)
    -----------fix_factorial[invalid]-----------
    FAILURE (Codegen
     (Ctx (CannotFindRep (Var (0 ())))
      (Exists
       (Lollipop
        (Prod
         ((Var (0 ()))
          (Exists
           (Lollipop
            (Prod
             ((Var (0 ())) (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
            (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))
        (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))))
    -----------unboxed_list[invlaid]-----------
    FAILURE (Codegen (CannotFindRep (Var (0 ("\206\177")))))
    -----------boxed_list-----------
    FAILURE (Codegen
     (Ctx (CannotFindRep (Var (0 ())))
      (Exists (Lollipop (Prod ((Var (0 ())) Int)) Int))))
    -----------peano_3-----------
    FAILURE (TODO memory)
    -----------peano-----------
    FAILURE (UnexpectedUnitializedLocal 0)
    -----------mini_zip-----------
    FAILURE (InvalidLocalIdx 0) |xxx}]
