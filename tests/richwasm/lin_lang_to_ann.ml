open! Core
open! Stdlib.Format
open! Test_support
module AnnRichWasm = Richwasm_common.Annotated_syntax

include Test_runner.MultiOutputter.Make (struct
  let margin = 120
  let max_indent = margin

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
  let pp = AnnRichWasm.Module.pp_rocq
  let pp_raw = AnnRichWasm.Module.pp_sexp
end)

let%expect_test "basic functionality" =
  run {| 1 |};
  [%expect
    {xxx|
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type := (MonoFunT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
          mf_locals := [];
          mf_body := [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1)];
        |}];
      m_table := [];
      m_exports := [ 0];
    |} |xxx}];
  next ();
  [%expect
    {|
    ((m_imports ())
     (m_functions
      (((mf_type (MonoFunT () ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))))
        (mf_locals ()) (mf_body ((INumConst (InstrT () ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))) 1))))))
     (m_table ()) (m_exports (0))) |}];

  run {| (1, 2, 3, 4) |};
  [%expect
    {xxx|
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT []
              [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]);
          mf_locals := [];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
              (IGroup
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |} |xxx}];
  next ();
  [%expect
    {|
    ((m_imports ())
     (m_functions
      (((mf_type
         (MonoFunT ()
          ((ProdT (VALTYPE (ProdR ((AtomR I32R) (AtomR I32R) (AtomR I32R) (AtomR I32R))) ImCopy ImDrop)
            ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
             (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
             (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
             (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))))))
        (mf_locals ())
        (mf_body
         ((INumConst (InstrT () ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))) 1)
          (INumConst (InstrT () ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))) 2)
          (INumConst (InstrT () ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))) 3)
          (INumConst (InstrT () ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))) 4)
          (IGroup
           (InstrT
            ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
             (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
             (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
             (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))
            ((ProdT (VALTYPE (ProdR ((AtomR I32R) (AtomR I32R) (AtomR I32R) (AtomR I32R))) ImCopy ImDrop)
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
        [ {|
          mf_type :=
            (MonoFunT []
              [ (ProdT
                (VALTYPE
                  (ProdR
                    [ (ProdR [ (AtomR I32R); (ProdR [ (AtomR I32R); (AtomR I32R)]); (AtomR I32R); (AtomR I32R)]);
                      (ProdR [ (AtomR I32R); (AtomR I32R)])])
                  ImCopy ImDrop)
                [ (ProdT
                  (VALTYPE (ProdR [ (AtomR I32R); (ProdR [ (AtomR I32R); (AtomR I32R)]); (AtomR I32R); (AtomR I32R)]) ImCopy
                    ImDrop)
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                  (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]);
          mf_locals := [];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
              (IGroup
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]));
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 5);
              (IGroup
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (ProdT
                    (VALTYPE (ProdR [ (AtomR I32R); (ProdR [ (AtomR I32R); (AtomR I32R)]); (AtomR I32R); (AtomR I32R)]) ImCopy
                      ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]));
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 6);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 7);
              (IGroup
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]));
              (IGroup
                (InstrT
                  [ (ProdT
                    (VALTYPE (ProdR [ (AtomR I32R); (ProdR [ (AtomR I32R); (AtomR I32R)]); (AtomR I32R); (AtomR I32R)]) ImCopy
                      ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                    (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                  [ (ProdT
                    (VALTYPE
                      (ProdR
                        [ (ProdR [ (AtomR I32R); (ProdR [ (AtomR I32R); (AtomR I32R)]); (AtomR I32R); (AtomR I32R)]);
                          (ProdR [ (AtomR I32R); (AtomR I32R)])])
                      ImCopy ImDrop)
                    [ (ProdT
                      (VALTYPE (ProdR [ (AtomR I32R); (ProdR [ (AtomR I32R); (AtomR I32R)]); (AtomR I32R); (AtomR I32R)])
                        ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                        (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |} |xxx}];

  run {| (new 10) |};
  [%expect
    {xxx|
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT []
              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]);
          mf_locals := [];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 10);
              (INew
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |} |xxx}];

  run {| (1 + 2) |};
  [%expect
    {xxx|
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type := (MonoFunT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
          mf_locals := [];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (INum
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (IInt2 I32T AddI))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |} |xxx}];
  next ();
  [%expect
    {|
    ((m_imports ())
     (m_functions
      (((mf_type (MonoFunT () ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))))
        (mf_locals ())
        (mf_body
         ((INumConst (InstrT () ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))) 1)
          (INumConst (InstrT () ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))) 2)
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
        [ {|
          mf_type := (MonoFunT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
          mf_locals := [];
          mf_body := [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1)];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------flat_tuple-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT []
              [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]);
          mf_locals := [];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
              (IGroup
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------nested_tuple-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT []
              [ (ProdT
                (VALTYPE (ProdR [ (ProdR [ (AtomR I32R); (AtomR I32R)]); (ProdR [ (AtomR I32R); (AtomR I32R)])]) ImCopy ImDrop)
                [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                  (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]);
          mf_locals := [];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (IGroup
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]));
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
              (IGroup
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]));
              (IGroup
                (InstrT
                  [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                    (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                  [ (ProdT
                    (VALTYPE (ProdR [ (ProdR [ (AtomR I32R); (AtomR I32R)]); (ProdR [ (AtomR I32R); (AtomR I32R)])]) ImCopy
                      ImDrop)
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------single_sum-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT [] [ (SumT (VALTYPE (SumR [ (ProdR [])]) ImCopy ImDrop) [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]);
          mf_locals := [];
          mf_body :=
            [ (IGroup (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
              (IInject
                (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]
                  [ (SumT (VALTYPE (SumR [ (ProdR [])]) ImCopy ImDrop) [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])
                0)];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------double_sum-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT []
              [ (SumT (VALTYPE (SumR [ (ProdR []); (AtomR I32R)]) ImCopy ImDrop)
                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []); (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]);
          mf_locals := [];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 15);
              (IInject
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (SumT (VALTYPE (SumR [ (ProdR []); (AtomR I32R)]) ImCopy ImDrop)
                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []); (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])
                1)];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------arith_add-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type := (MonoFunT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
          mf_locals := [];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 9);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 10);
              (INum
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (IInt2 I32T AddI))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------arith_sub-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type := (MonoFunT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
          mf_locals := [];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 67);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 41);
              (INum
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (IInt2 I32T SubI))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------arith_mul-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type := (MonoFunT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
          mf_locals := [];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 42);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 10);
              (INum
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (IInt2 I32T MulI))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------arith_div-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type := (MonoFunT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
          mf_locals := [];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) -30);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 10);
              (INum
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (IInt2 I32T (DivI SignS)))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------app_ident-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT
              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                  (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
          mf_locals := [ (AtomR PtrR); (AtomR I32R); (ProdR []); (AtomR I32R)];
          mf_body :=
            [ (ILocalGet
              (InstrT []
                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])
              0);
              (IUngroup
                (InstrT
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
              (ILocalSet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (ILocalSet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])
                1);
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])
                1);
              (ILoad
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SpanT (MEMTYPE (RepS (ProdR [])) ImDrop) (RepS (ProdR []))));
                    (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])
                [] Move);
              (ILocalSet (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]) 3);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SpanT (MEMTYPE (RepS (ProdR [])) ImDrop) (RepS (ProdR []))))]
                  []));
              (ILocalGet (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]) 3);
              (IUngroup (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])] []));
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (ILocalSet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
              (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []));
              (ILocalGet (InstrT [] [ (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))]) 1);
              (IDrop (InstrT [ (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))] []));
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []))];
        |};
          {|
            mf_type := (MonoFunT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
            mf_locals :=
              [ (ProdR [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR PtrR)]);
                (ProdR [ (AtomR I32R); (ProdR [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR PtrR)])]);
                (ProdR [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR PtrR)])];
            mf_body :=
              [ (ICodeRef
                (InstrT []
                  [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                    (MonoFunT
                      [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                0);
                (IGroup (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
                (INew
                  (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]));
                (IGroup
                  (InstrT
                    [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                      (MonoFunT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]));
                (IPack
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]
                    [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      (VALTYPE (ProdR []) ImCopy ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]));
                (IUnpack
                  (InstrT
                    [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      (VALTYPE (ProdR []) ImCopy ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR PtrR)]))
                  (PlugT (VALTYPE (AtomR I32R) ImCopy ImDrop) (AtomR I32R))
                  (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))
                  [ (ILocalSet
                    (InstrT []
                      [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])])
                    0);
                    (ILocalGet
                      (InstrT []
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])])
                      0);
                    (IUngroup
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]));
                    (ILocalSet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                      2);
                    (ILocalSet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      1);
                    (ILocalGet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                      2);
                    (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 10);
                    (IGroup
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      1);
                    (ICallIndirect
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      1);
                    (IDrop
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        []));
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))]) 2);
                    (IDrop (InstrT [ (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))] []));
                    (ILocalGet
                      (InstrT []
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR PtrR)]))])
                      0);
                    (IDrop
                      (InstrT
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR PtrR)]))]
                        []))])];
          |}];
      m_table := [ 0];
      m_exports := [ 1];
    |}
    -----------nested_arith-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type := (MonoFunT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
          mf_locals := [];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 9);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 10);
              (INum
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (IInt2 I32T AddI));
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 5);
              (INum
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (IInt2 I32T MulI))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------let_bind-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type := (MonoFunT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
          mf_locals := [ (AtomR I32R)];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 10);
              (ILocalSet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0);
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0);
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0);
              (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------add_one_program-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT
              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                  (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
          mf_locals := [ (AtomR PtrR); (AtomR I32R)];
          mf_body :=
            [ (ILocalGet
              (InstrT []
                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])
              0);
              (IUngroup
                (InstrT
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
              (ILocalSet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (ILocalSet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])
                1);
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
              (INum
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (IInt2 I32T AddI));
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])
                1);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                  []));
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []))];
        |};
          {|
            mf_type := (MonoFunT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
            mf_locals :=
              [ (ProdR [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR PtrR)]);
                (ProdR [ (AtomR I32R); (ProdR [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR PtrR)])]);
                (ProdR [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR PtrR)])];
            mf_body :=
              [ (ICodeRef
                (InstrT []
                  [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                    (MonoFunT
                      [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                0);
                (IGroup (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
                (INew
                  (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]));
                (IGroup
                  (InstrT
                    [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                      (MonoFunT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]));
                (IPack
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]
                    [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      (VALTYPE (ProdR []) ImCopy ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]));
                (IUnpack
                  (InstrT
                    [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      (VALTYPE (ProdR []) ImCopy ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR PtrR)]))
                  (PlugT (VALTYPE (AtomR I32R) ImCopy ImDrop) (AtomR I32R))
                  (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))
                  [ (ILocalSet
                    (InstrT []
                      [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])])
                    0);
                    (ILocalGet
                      (InstrT []
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])])
                      0);
                    (IUngroup
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]));
                    (ILocalSet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                      2);
                    (ILocalSet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      1);
                    (ILocalGet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                      2);
                    (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 42);
                    (IGroup
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      1);
                    (ICallIndirect
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      1);
                    (IDrop
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        []));
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))]) 2);
                    (IDrop (InstrT [ (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))] []));
                    (ILocalGet
                      (InstrT []
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR PtrR)]))])
                      0);
                    (IDrop
                      (InstrT
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR PtrR)]))]
                        []))])];
          |}];
      m_table := [ 0];
      m_exports := [ 0; 1];
    |}
    -----------add_tup_ref-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type := (MonoFunT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
          mf_locals := [ (AtomR PtrR); (AtomR I32R); (AtomR PtrR); (AtomR I32R); (AtomR I32R)];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (INew
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]));
              (ILocalSet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])
                0);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])
                0);
              (IGroup
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]
                  [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])]));
              (IUngroup
                (InstrT
                  [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]));
              (ILocalSet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])
                2);
              (ILocalSet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])
                2);
              (ILoad
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SpanT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (RepS (AtomR I32R))));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                [] Move);
              (ILocalSet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SpanT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (RepS (AtomR I32R))))]
                  []));
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
              (ILocalSet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
              (INum
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (IInt2 I32T AddI));
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
              (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []));
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
              (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []));
              (ILocalGet (InstrT [] [ (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))]) 2);
              (IDrop (InstrT [ (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))] []));
              (ILocalGet (InstrT [] [ (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))]) 0);
              (IDrop (InstrT [ (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))] []))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------print_10-----------
    FAILURE (InstrErr (error (InvalidTableIdx 0)) (instr (CodeRef 0))
     (env
      ((local_offset 0) (kinds ()) (labels ()) (return ((Prod ())))
       (functions ((FunctionType () () ((Prod ()))))) (table ()) (lfx ())))
     (state
      ((locals
        ((Plug (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))
         (Plug
          (Prod ((Atom I32) (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))))
         (Plug (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))))
       (stack ()))))
    -----------closure-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT
              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [])]) NoCopy ExDrop)
                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                  (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                    (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])));
                  (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
          mf_locals := [ (AtomR PtrR); (ProdR []); (ProdR [ (AtomR I32R)]); (AtomR I32R); (ProdR [])];
          mf_body :=
            [ (ILocalGet
              (InstrT []
                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [])]) NoCopy ExDrop)
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])));
                    (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])
              0);
              (IUngroup
                (InstrT
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [])]) NoCopy ExDrop)
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                        (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])));
                      (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])));
                    (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
              (ILocalSet (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]) 2);
              (ILocalSet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])))])
                1);
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])))])
                1);
              (ILoad
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])))]
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SpanT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (RepS (ProdR [ (AtomR I32R)]))));
                    (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])
                [] Move);
              (ILocalSet
                (InstrT []
                  [ (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])
                3);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SpanT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (RepS (ProdR [ (AtomR I32R)]))))]
                  []));
              (ILocalGet
                (InstrT []
                  [ (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])
                3);
              (IUngroup
                (InstrT
                  [ (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
              (ILocalSet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
              (ILocalGet (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]) 2);
              (ILocalSet (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]) 5);
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
              (ILocalGet (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]) 5);
              (IDrop (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])] []));
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
              (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []));
              (ILocalGet (InstrT [] [ (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))]) 1);
              (IDrop (InstrT [ (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))] []));
              (ILocalGet (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]) 2);
              (IDrop (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])] []))];
        |};
          {|
            mf_type := (MonoFunT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
            mf_locals :=
              [ (AtomR I32R);
                (ProdR [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR PtrR)]);
                (ProdR [ (AtomR I32R); (ProdR [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR PtrR)])]);
                (ProdR [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR PtrR)])];
            mf_body :=
              [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 10);
                (ILocalSet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0);
                (ICodeRef
                  (InstrT []
                    [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                      (MonoFunT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [])]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                              (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])));
                            (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                  0);
                (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0);
                (IGroup
                  (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]));
                (INew
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                        (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])))]));
                (IGroup
                  (InstrT
                    [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                      (MonoFunT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [])]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                              (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])));
                            (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                          (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [])]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                                (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])));
                              (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                            (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])))])]));
                (IPack
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [])]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                                (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])));
                              (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                            (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])))])]
                    [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)))]))]));
                (IUnpack
                  (InstrT
                    [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)))]))]
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR PtrR)]))
                  (PlugT (VALTYPE (AtomR I32R) ImCopy ImDrop) (AtomR I32R))
                  (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))
                  [ (ILocalSet
                    (InstrT []
                      [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)))])])
                    1);
                    (ILocalGet
                      (InstrT []
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [])]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                                  (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)))])])
                      1);
                    (IUngroup
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [])]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                                  (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)))])]
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)))]));
                    (ILocalSet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)))])
                      3);
                    (ILocalSet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      2);
                    (ILocalGet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)))])
                      3);
                    (IGroup (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
                    (IGroup
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                          (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [])]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                            (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      2);
                    (ICallIndirect
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [])]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                            (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      2);
                    (IDrop
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        []));
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))]) 3);
                    (IDrop (InstrT [ (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))] []));
                    (ILocalGet
                      (InstrT []
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR PtrR)]))])
                      1);
                    (IDrop
                      (InstrT
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR PtrR)]))]
                        []))]);
                (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0);
                (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []))];
          |}];
      m_table := [ 0];
      m_exports := [ 1];
    |}
    -----------factorial_program-----------
    FAILURE (InstrErr
     (error
      (CannotInferLfx
       (Ite
        (4
         ((Plug (Prod ((Atom Ptr) (Atom I32)))) (Ref (Base MM) (Ser (Prod ())))
          (Num (Int I32)) (Plug (Atom I32))
          (Plug (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))
          (Plug
           (Prod ((Atom I32) (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))))
          (Plug (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))
          (Plug (Atom I32)))
         ((Plug (Prod ((Atom Ptr) (Atom I32)))) (Ref (Base MM) (Ser (Prod ())))
          (Num (Int I32)) (Plug (Atom I32)) (Plug (Prod ((Atom I32) (Atom Ptr))))
          (Plug (Atom I32)) (Plug (Atom Ptr)) (Plug (Atom I32)))))))
     (instr
      (Ite (ArrowType 1 ((Num (Int I32)))) InferFx ((NumConst (Int I32) 1))
       ((LocalGet 2 Follow) (NumConst (Int I32) 1) (Num (Int2 I32 Sub))
        (LocalSet 3) (CodeRef 0) (Group 0) (New MM) (Group 2)
        (Pack (Type (Prod ()))
         (Prod
          ((CodeRef
            (FunctionType ()
             ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
             ((Num (Int I32)))))
           (Ref (Base MM) (Ser (Var 0))))))
        (Unpack (ArrowType 1 ((Num (Int I32)))) InferFx
         ((LocalSet 4) (LocalGet 4 Follow) Ungroup (LocalSet 6) (LocalSet 5)
          (LocalGet 6 Follow) (LocalGet 6 Follow) (Group 2) (LocalGet 5 Follow)
          CallIndirect (LocalGet 5 Move) Drop (LocalGet 6 Move) Drop
          (LocalGet 4 Move) Drop))
        (LocalSet 7) (LocalGet 2 Follow) (LocalGet 7 Follow) (Num (Int2 I32 Mul))
        (LocalGet 7 Move) Drop (LocalGet 3 Move) Drop)))
     (env
      ((local_offset 1) (kinds ()) (labels ()) (return ((Num (Int I32))))
       (functions
        ((FunctionType ()
          ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
          ((Num (Int I32))))
         (FunctionType () () ((Num (Int I32))))))
       (table
        ((FunctionType ()
          ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
          ((Num (Int I32))))))
       (lfx ())))
     (state
      ((locals
        ((Plug (Prod ((Atom Ptr) (Atom I32)))) (Ref (Base MM) (Ser (Prod ())))
         (Num (Int I32)) (Plug (Atom I32))
         (Plug (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))
         (Plug
          (Prod ((Atom I32) (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))))
         (Plug (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))
         (Plug (Atom I32))))
       (stack ((Num (Int I32)) (Num (Int I32)))))))
    -----------safe_div-----------
    FAILURE (InstrErr
     (error
      (CannotInferLfx
       (Case
        (1 3
         ((Plug (Prod ((Atom Ptr) (Sum ((Atom I32) (Prod ()))))))
          (Ref (Base MM) (Ser (Prod ()))) (Sum ((Num (Int I32)) (Prod ())))
          (Plug (Atom I32)) (Plug (Sum ((Atom I32) (Prod ())))))
         ((Plug (Prod ((Atom Ptr) (Sum ((Atom I32) (Prod ()))))))
          (Ref (Base MM) (Ser (Prod ()))) (Sum ((Num (Int I32)) (Prod ())))
          (Plug (Sum ((Atom I32) (Prod ())))) (Plug (Prod ())))))))
     (instr
      (Case (ArrowType 1 ((Num (Int I32)))) InferFx
       (((LocalSet 3) (LocalGet 3 Follow) (LocalGet 3 Move) Drop)
        ((LocalSet 4) (NumConst (Int I32) 0) (LocalGet 4 Move) Drop))))
     (env
      ((local_offset 1) (kinds ()) (labels ()) (return ((Num (Int I32))))
       (functions
        ((FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Prod ((Num (Int I32)) (Num (Int I32)))))))
          ((Sum ((Num (Int I32)) (Prod ())))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ()))) (Sum ((Num (Int I32)) (Prod ()))))))
          ((Num (Int I32))))
         (FunctionType () () ((Num (Int I32))))))
       (table
        ((FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Prod ((Num (Int I32)) (Num (Int I32)))))))
          ((Sum ((Num (Int I32)) (Prod ())))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ()))) (Sum ((Num (Int I32)) (Prod ()))))))
          ((Num (Int I32))))))
       (lfx ())))
     (state
      ((locals
        ((Plug (Prod ((Atom Ptr) (Sum ((Atom I32) (Prod ()))))))
         (Ref (Base MM) (Ser (Prod ()))) (Sum ((Num (Int I32)) (Prod ())))
         (Plug (Atom I32)) (Plug (Prod ()))))
       (stack ((Sum ((Num (Int I32)) (Prod ()))))))))
    -----------incr_n-----------
    FAILURE (InstrErr
     (error
      (CannotInferLfx
       (Ite
        (3
         ((Plug (Prod ((Atom Ptr) (Prod ((Atom Ptr) (Atom I32))))))
          (Ref (Base MM) (Ser (Prod ()))) (Plug (Prod ((Atom Ptr) (Atom I32))))
          (Plug (Atom Ptr)) (Num (Int I32)) (Plug (Atom I32))
          (Plug (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))
          (Plug
           (Prod ((Atom I32) (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))))
          (Plug (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))
          (Plug (Atom Ptr)) (Plug (Atom I32))
          (Plug (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))
          (Plug
           (Prod ((Atom I32) (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))))
          (Plug (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr)))))
         ((Plug (Prod ((Atom Ptr) (Prod ((Atom Ptr) (Atom I32))))))
          (Ref (Base MM) (Ser (Prod ()))) (Plug (Prod ((Atom Ptr) (Atom I32))))
          (Ref (Base MM) (Ser (Num (Int I32)))) (Num (Int I32)) (Plug (Atom I32))
          (Plug (Prod ((Atom I32) (Atom Ptr)))) (Plug (Atom I32))
          (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom I32))
          (Plug (Prod ((Atom I32) (Atom Ptr)))) (Plug (Atom I32))
          (Plug (Atom Ptr)))))))
     (instr
      (Ite (ArrowType 1 ((Num (Int I32)))) InferFx
       ((LocalGet 3 Follow) (Load (Path ()) Move) (LocalSet 5) Drop
        (LocalGet 5 Move))
       ((CodeRef 0) (Group 0) (New MM) (Group 2)
        (Pack (Type (Prod ()))
         (Prod
          ((CodeRef
            (FunctionType ()
             ((Prod
               ((Ref (Base MM) (Ser (Var 0)))
                (Ref (Base MM) (Ser (Num (Int I32)))))))
             ((Ref (Base MM) (Ser (Num (Int I32)))))))
           (Ref (Base MM) (Ser (Var 0))))))
        (Unpack (ArrowType 1 ((Ref (Base MM) (Ser (Num (Int I32)))))) InferFx
         ((LocalSet 6) (LocalGet 6 Follow) Ungroup (LocalSet 8) (LocalSet 7)
          (LocalGet 8 Follow) (LocalGet 7 Follow) (Group 2) (LocalGet 7 Follow)
          CallIndirect (LocalGet 7 Move) Drop (LocalGet 8 Move) Drop
          (LocalGet 6 Move) Drop))
        (LocalSet 9) (LocalGet 4 Follow) (NumConst (Int I32) 1)
        (Num (Int2 I32 Sub)) (LocalSet 10) (CodeRef 1) (Group 0) (New MM)
        (Group 2)
        (Pack (Type (Prod ()))
         (Prod
          ((CodeRef
            (FunctionType ()
             ((Prod
               ((Ref (Base MM) (Ser (Var 0)))
                (Prod ((Ref (Base MM) (Ser (Num (Int I32)))) (Num (Int I32)))))))
             ((Num (Int I32)))))
           (Ref (Base MM) (Ser (Var 0))))))
        (Unpack (ArrowType 1 ((Num (Int I32)))) InferFx
         ((LocalSet 11) (LocalGet 11 Follow) Ungroup (LocalSet 13) (LocalSet 12)
          (LocalGet 13 Follow) (LocalGet 12 Follow) (LocalGet 13 Follow)
          (Group 2) (Group 2) (LocalGet 12 Follow) CallIndirect
          (LocalGet 12 Move) Drop (LocalGet 13 Move) Drop (LocalGet 11 Move)
          Drop))
        (LocalGet 10 Move) Drop (LocalGet 9 Move) Drop)))
     (env
      ((local_offset 1) (kinds ()) (labels ()) (return ((Num (Int I32))))
       (functions
        ((FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Ref (Base MM) (Ser (Num (Int I32)))))))
          ((Ref (Base MM) (Ser (Num (Int I32))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Prod ((Ref (Base MM) (Ser (Num (Int I32)))) (Num (Int I32)))))))
          ((Num (Int I32))))
         (FunctionType () () ((Num (Int I32))))))
       (table
        ((FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Ref (Base MM) (Ser (Num (Int I32)))))))
          ((Ref (Base MM) (Ser (Num (Int I32))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Prod ((Ref (Base MM) (Ser (Num (Int I32)))) (Num (Int I32)))))))
          ((Num (Int I32))))))
       (lfx ())))
     (state
      ((locals
        ((Plug (Prod ((Atom Ptr) (Prod ((Atom Ptr) (Atom I32))))))
         (Ref (Base MM) (Ser (Prod ()))) (Plug (Prod ((Atom Ptr) (Atom I32))))
         (Ref (Base MM) (Ser (Num (Int I32)))) (Num (Int I32)) (Plug (Atom I32))
         (Plug (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))
         (Plug
          (Prod ((Atom I32) (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))))
         (Plug (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))
         (Plug (Atom Ptr)) (Plug (Atom I32))
         (Plug (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))
         (Plug
          (Prod ((Atom I32) (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))))
         (Plug (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))))
       (stack ((Num (Int I32)) (Num (Int I32)))))))
    -----------fix_factorial[invalid]-----------
    FAILURE (InstrErr
     (error
      (BlockErr
       (error
        (UngroupNonProd
         (CodeRef
          (FunctionType ()
           ((Prod
             ((Ref (Base MM) (Ser (Var 0)))
              (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) NoCopy ExDrop)
               (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                  ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (CodeRef
                     (FunctionType ()
                      ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                      ((Num (Int I32))))))))))))))
           ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
             (CodeRef
              (FunctionType ()
               ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
               ((Num (Int I32)))))))))))
       (instr Ungroup)
       (env
        ((local_offset 1) (kinds ((VALTYPE (Atom Ptr) NoCopy ExDrop)))
         (labels
          (((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
             (CodeRef
              (FunctionType ()
               ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
               ((Num (Int I32)))))))))
         (return
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32))))))))
         (functions
          ((FunctionType ()
            ((Prod
              ((Ref (Base MM)
                (Ser
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (CodeRef
                     (FunctionType ()
                      ((Prod
                        ((Ref (Base MM) (Ser (Var 0)))
                         (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                          (CodeRef
                           (FunctionType ()
                            ((Prod
                              ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                            ((Num (Int I32)))))))))
                      ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                        (CodeRef
                         (FunctionType ()
                          ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                          ((Num (Int I32))))))))))))))
               (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) NoCopy ExDrop)
                (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                 (CodeRef
                  (FunctionType ()
                   ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                   ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                     (CodeRef
                      (FunctionType ()
                       ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                       ((Num (Int I32))))))))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32))))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (CodeRef
                 (FunctionType ()
                  ((Prod
                    ((Ref (Base MM) (Ser (Var 0)))
                     (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                      (CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                        ((Num (Int I32)))))))))
                  ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (CodeRef
                     (FunctionType ()
                      ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                      ((Num (Int I32)))))))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32))))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM)
                (Ser
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (CodeRef
                     (FunctionType ()
                      ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                      ((Num (Int I32))))))))))
               (Num (Int I32)))))
            ((Num (Int I32))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32)))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32))))))))
           (FunctionType () () ((Num (Int I32))))))
         (table
          ((FunctionType ()
            ((Prod
              ((Ref (Base MM)
                (Ser
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (CodeRef
                     (FunctionType ()
                      ((Prod
                        ((Ref (Base MM) (Ser (Var 0)))
                         (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                          (CodeRef
                           (FunctionType ()
                            ((Prod
                              ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                            ((Num (Int I32)))))))))
                      ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                        (CodeRef
                         (FunctionType ()
                          ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                          ((Num (Int I32))))))))))))))
               (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) NoCopy ExDrop)
                (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                 (CodeRef
                  (FunctionType ()
                   ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                   ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                     (CodeRef
                      (FunctionType ()
                       ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                       ((Num (Int I32))))))))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32))))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (CodeRef
                 (FunctionType ()
                  ((Prod
                    ((Ref (Base MM) (Ser (Var 0)))
                     (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                      (CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                        ((Num (Int I32)))))))))
                  ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (CodeRef
                     (FunctionType ()
                      ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                      ((Num (Int I32)))))))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32))))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM)
                (Ser
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (CodeRef
                     (FunctionType ()
                      ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                      ((Num (Int I32))))))))))
               (Num (Int I32)))))
            ((Num (Int I32))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32)))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32))))))))))
         (lfx (InferFx))))
       (state
        ((locals
          ((Plug (Prod ((Atom Ptr) (Atom I32)))) (Plug (Atom Ptr))
           (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) NoCopy ExDrop)
            (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
             (CodeRef
              (FunctionType () ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
               ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                 (CodeRef
                  (FunctionType ()
                   ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                   ((Num (Int I32)))))))))))
           (Plug (Prod ((Atom I32))))
           (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType ()
              ((Prod
                ((Ref (Base MM) (Ser (Var 0)))
                 (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32)))))))))
              ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32))))))))))
           (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) NoCopy ExDrop)
            (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
             (CodeRef
              (FunctionType () ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
               ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                 (CodeRef
                  (FunctionType ()
                   ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                   ((Num (Int I32)))))))))))
           (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType ()
              ((Prod
                ((Ref (Base MM) (Ser (Var 0)))
                 (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) NoCopy ExDrop)
                  (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                   (CodeRef
                    (FunctionType ()
                     ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                     ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                       (CodeRef
                        (FunctionType ()
                         ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                         ((Num (Int I32))))))))))))))
              ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32))))))))))
           (CodeRef
            (FunctionType ()
             ((Prod
               ((Ref (Base MM) (Ser (Var 0)))
                (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) NoCopy ExDrop)
                 (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                    ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                      (CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                        ((Num (Int I32))))))))))))))
             ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
               (CodeRef
                (FunctionType ()
                 ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                 ((Num (Int I32)))))))))
           (Plug (Prod ((Atom I32) (Prod ((Atom I32) (Atom Ptr))))))
           (Plug (Prod ((Atom I32) (Atom Ptr))))
           (Plug (Prod ((Atom I32) (Atom Ptr))))
           (Plug (Prod ((Atom I32) (Atom Ptr))))
           (Plug (Prod ((Atom I32) (Prod ((Atom I32) (Atom Ptr))))))
           (Plug (Prod ((Atom I32) (Atom Ptr))))))
         (stack
          ((CodeRef
            (FunctionType ()
             ((Prod
               ((Ref (Base MM) (Ser (Var 0)))
                (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) NoCopy ExDrop)
                 (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                    ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                      (CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                        ((Num (Int I32))))))))))))))
             ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
               (CodeRef
                (FunctionType ()
                 ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                 ((Num (Int I32)))))))))))))))
     (instr
      (Unpack
       (ArrowType 1
        ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
          (CodeRef
           (FunctionType ()
            ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
            ((Num (Int I32))))))))
       InferFx
       ((LocalSet 7) (LocalGet 7 Follow) Ungroup (LocalSet 9) (LocalSet 8)
        (LocalGet 9 Follow) (LocalGet 8 Follow) (Group 2) (LocalGet 8 Follow)
        CallIndirect (LocalGet 8 Move) Drop (LocalGet 9 Move) Drop
        (LocalGet 7 Move) Drop)))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return
        ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
          (CodeRef
           (FunctionType ()
            ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
            ((Num (Int I32))))))))
       (functions
        ((FunctionType ()
          ((Prod
            ((Ref (Base MM)
              (Ser
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType ()
                    ((Prod
                      ((Ref (Base MM) (Ser (Var 0)))
                       (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                        (CodeRef
                         (FunctionType ()
                          ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                          ((Num (Int I32)))))))))
                    ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                      (CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                        ((Num (Int I32))))))))))))))
             (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) NoCopy ExDrop)
              (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
               (CodeRef
                (FunctionType () ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                 ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                   (CodeRef
                    (FunctionType ()
                     ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                     ((Num (Int I32))))))))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32))))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod
                  ((Ref (Base MM) (Ser (Var 0)))
                   (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (CodeRef
                     (FunctionType ()
                      ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                      ((Num (Int I32)))))))))
                ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32)))))))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32))))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM)
              (Ser
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32))))))))))
             (Num (Int I32)))))
          ((Num (Int I32))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32)))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32))))))))
         (FunctionType () () ((Num (Int I32))))))
       (table
        ((FunctionType ()
          ((Prod
            ((Ref (Base MM)
              (Ser
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType ()
                    ((Prod
                      ((Ref (Base MM) (Ser (Var 0)))
                       (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                        (CodeRef
                         (FunctionType ()
                          ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                          ((Num (Int I32)))))))))
                    ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                      (CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                        ((Num (Int I32))))))))))))))
             (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) NoCopy ExDrop)
              (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
               (CodeRef
                (FunctionType () ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                 ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                   (CodeRef
                    (FunctionType ()
                     ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                     ((Num (Int I32))))))))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32))))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod
                  ((Ref (Base MM) (Ser (Var 0)))
                   (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (CodeRef
                     (FunctionType ()
                      ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                      ((Num (Int I32)))))))))
                ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32)))))))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32))))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM)
              (Ser
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32))))))))))
             (Num (Int I32)))))
          ((Num (Int I32))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32)))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32))))))))))
       (lfx ())))
     (state
      ((locals
        ((Plug (Prod ((Atom Ptr) (Atom I32)))) (Plug (Atom Ptr))
         (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) NoCopy ExDrop)
          (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
           (CodeRef
            (FunctionType () ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
             ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
               (CodeRef
                (FunctionType ()
                 ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                 ((Num (Int I32)))))))))))
         (Plug (Prod ((Atom I32))))
         (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
          (CodeRef
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Var 0)))
               (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32)))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32))))))))))
         (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) NoCopy ExDrop)
          (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
           (CodeRef
            (FunctionType () ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
             ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
               (CodeRef
                (FunctionType ()
                 ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                 ((Num (Int I32)))))))))))
         (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
          (CodeRef
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Var 0)))
               (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) NoCopy ExDrop)
                (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                 (CodeRef
                  (FunctionType ()
                   ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                   ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                     (CodeRef
                      (FunctionType ()
                       ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                       ((Num (Int I32))))))))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32))))))))))
         (Plug (Prod ((Atom I32) (Atom Ptr))))
         (Plug (Prod ((Atom I32) (Prod ((Atom I32) (Atom Ptr))))))
         (Plug (Prod ((Atom I32) (Atom Ptr))))
         (Plug (Prod ((Atom I32) (Atom Ptr))))
         (Plug (Prod ((Atom I32) (Atom Ptr))))
         (Plug (Prod ((Atom I32) (Prod ((Atom I32) (Atom Ptr))))))
         (Plug (Prod ((Atom I32) (Atom Ptr))))))
       (stack
        ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
          (CodeRef
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Var 0)))
               (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) NoCopy ExDrop)
                (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                 (CodeRef
                  (FunctionType ()
                   ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                   ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                     (CodeRef
                      (FunctionType ()
                       ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                       ((Num (Int I32))))))))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32)))))))))))))))
    -----------unboxed_list[invalid]-----------
    FAILURE (Codegen
     (CannotResolveRepOfRecTypeWithoutIndirection (Var (0 ("\206\177")))))
    -----------boxed_list-----------
    FAILURE (InstrErr
     (error
      (BlockErr
       (error
        (UngroupNonProd
         (Sum
          ((Prod ())
           (Prod
            ((Num (Int I32))
             (Ref (Base MM)
              (Ser
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
                 ExDrop)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))))))
       (instr Ungroup)
       (env
        ((local_offset 1) (kinds ())
         (labels
          (((Sum
             ((Prod ())
              (Prod
               ((Num (Int I32))
                (Ref (Base MM)
                 (Ser
                  (Rec
                   (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                    NoCopy ExDrop)
                   (Sum
                    ((Prod ())
                     (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0)))))))))))))))))
         (return
          ((Rec
            (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
             ExDrop)
            (Sum
             ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))
         (functions
          ((FunctionType ()
            ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
            ((Num (Int I32))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32))))))
                 (Rec
                  (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                   NoCopy ExDrop)
                  (Sum
                   ((Prod ())
                    (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0)))))))))))))
            ((Rec
              (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
               ExDrop)
              (Sum
               ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))
           (FunctionType () ()
            ((Rec
              (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
               ExDrop)
              (Sum
               ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))
         (table
          ((FunctionType ()
            ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
            ((Num (Int I32))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32))))))
                 (Rec
                  (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                   NoCopy ExDrop)
                  (Sum
                   ((Prod ())
                    (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0)))))))))))))
            ((Rec
              (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
               ExDrop)
              (Sum
               ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))
         (lfx (InferFx))))
       (state
        ((locals
          ((Plug
            (Prod
             ((Atom Ptr)
              (Prod
               ((Atom I32) (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))))))))
           (Ref (Base MM) (Ser (Prod ())))
           (Plug
            (Prod ((Atom I32) (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))))))
           (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32))))))
           (Plug (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))))
           (Plug (Prod ()))
           (Plug (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))))
           (Plug (Atom I32)) (Plug (Atom Ptr))
           (Plug (Prod ((Atom I32) (Atom Ptr))))
           (Plug (Prod ((Atom I32) (Prod ((Atom I32) (Atom Ptr))))))
           (Plug (Prod ((Atom I32) (Atom Ptr))))
           (Plug (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))
           (Plug
            (Prod
             ((Atom I32) (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))))
           (Plug (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))
           (Plug (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))))))
         (stack
          ((Sum
            ((Prod ())
             (Prod
              ((Num (Int I32))
               (Ref (Base MM)
                (Ser
                 (Rec
                  (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                   NoCopy ExDrop)
                  (Sum
                   ((Prod ())
                    (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))))))))))
     (instr
      (Case
       (ArrowType 1
        ((Sum
          ((Prod ())
           (Prod
            ((Num (Int I32))
             (Ref (Base MM)
              (Ser
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
                 ExDrop)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))))))
       InferFx
       (((LocalSet 5) (LocalGet 5 Follow)
         (Inject () 0
          ((Prod ())
           (Prod
            ((Num (Int I32))
             (Ref (Base MM)
              (Ser
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
                 ExDrop)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))))
         (LocalGet 5 Move) Drop)
        ((LocalSet 6) (LocalGet 6 Follow) Ungroup (LocalSet 8) (LocalSet 7)
         (LocalGet 3 Follow)
         (Unpack (ArrowType 1 ((Num (Int I32)))) InferFx
          ((LocalSet 9) (LocalGet 9 Follow) Ungroup (LocalSet 11) (LocalSet 10)
           (LocalGet 11 Follow) (LocalGet 10 Follow) (Group 2)
           (LocalGet 10 Follow) CallIndirect (LocalGet 10 Move) Drop
           (LocalGet 11 Move) Drop (LocalGet 9 Move) Drop))
         (CodeRef 1) (Group 0) (New MM) (Group 2)
         (Pack (Type (Prod ()))
          (Prod
           ((CodeRef
             (FunctionType ()
              ((Prod
                ((Ref (Base MM) (Ser (Var 0)))
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (CodeRef
                     (FunctionType ()
                      ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                      ((Num (Int I32))))))
                   (Rec
                    (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                     NoCopy ExDrop)
                    (Sum
                     ((Prod ())
                      (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0)))))))))))))
              ((Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
                 ExDrop)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0)))))))))))
            (Ref (Base MM) (Ser (Var 0))))))
         (Unpack
          (ArrowType 1
           ((Rec
             (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
              ExDrop)
             (Sum
              ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))
          InferFx
          ((LocalSet 12) (LocalGet 12 Follow) Ungroup (LocalSet 14) (LocalSet 13)
           (LocalGet 14 Follow) (LocalGet 7 Follow) (LocalGet 14 Follow)
           (Load (Path ()) Move) (LocalSet 15) Drop (LocalGet 15 Move) (Group 2)
           (Group 2) (LocalGet 13 Follow) CallIndirect (LocalGet 13 Move) Drop
           (LocalGet 14 Move) Drop (LocalGet 12 Move) Drop))
         (New MM) (Group 2)
         (Inject () 1
          ((Prod ())
           (Prod
            ((Num (Int I32))
             (Ref (Base MM)
              (Ser
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
                 ExDrop)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))))
         (LocalGet 7 Move) Drop (LocalGet 8 Move) Drop (LocalGet 6 Move) Drop))))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return
        ((Rec
          (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
           ExDrop)
          (Sum
           ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))
       (functions
        ((FunctionType ()
          ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
          ((Num (Int I32))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Prod
              ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32))))))
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
                 ExDrop)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0)))))))))))))
          ((Rec
            (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
             ExDrop)
            (Sum
             ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))
         (FunctionType () ()
          ((Rec
            (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
             ExDrop)
            (Sum
             ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))
       (table
        ((FunctionType ()
          ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
          ((Num (Int I32))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Prod
              ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32))))))
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
                 ExDrop)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0)))))))))))))
          ((Rec
            (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
             ExDrop)
            (Sum
             ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))
       (lfx ())))
     (state
      ((locals
        ((Plug
          (Prod
           ((Atom Ptr)
            (Prod ((Atom I32) (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))))))))
         (Ref (Base MM) (Ser (Prod ())))
         (Plug
          (Prod ((Atom I32) (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))))))
         (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
          (CodeRef
           (FunctionType ()
            ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
            ((Num (Int I32))))))
         (Plug (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))) (Plug (Prod ()))
         (Plug (Prod ((Atom I32) (Atom Ptr)))) (Plug (Atom I32))
         (Plug (Atom Ptr)) (Plug (Prod ((Atom I32) (Atom Ptr))))
         (Plug (Prod ((Atom I32) (Prod ((Atom I32) (Atom Ptr))))))
         (Plug (Prod ((Atom I32) (Atom Ptr))))
         (Plug (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))
         (Plug
          (Prod ((Atom I32) (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))))
         (Plug (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))
         (Plug (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))))))
       (stack
        ((Sum
          ((Prod ())
           (Prod
            ((Num (Int I32))
             (Ref (Base MM)
              (Ser
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
                 ExDrop)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0)))))))))))))))))))
    -----------peano_3-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT []
              [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]);
          mf_locals := [];
          mf_body :=
            [ (IGroup (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
              (IInject
                (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]
                  [ (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                          (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))])])
                0);
              (IFold
                (InstrT
                  [ (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                          (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))])]
                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
              (INew
                (InstrT
                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))]));
              (IInject
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))]
                  [ (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                          (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))])])
                1);
              (IFold
                (InstrT
                  [ (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                          (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))])]
                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
              (INew
                (InstrT
                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))]));
              (IInject
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))]
                  [ (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                          (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))])])
                1);
              (IFold
                (InstrT
                  [ (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                          (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))])]
                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
              (INew
                (InstrT
                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))]));
              (IInject
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))]
                  [ (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                          (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))])])
                1);
              (IFold
                (InstrT
                  [ (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                          (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))])]
                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------peano-----------
    FAILURE (InstrErr
     (error
      (BlockErr
       (error
        (BlockErr (error (NonRef Load (Plug (Atom Ptr))))
         (instr (Load (Path ()) Move))
         (env
          ((local_offset 1) (kinds ((VALTYPE (Prod ()) ImCopy ImDrop)))
           (labels
            (((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
               (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))
             ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
               (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))
           (return
            ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
              (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
           (functions
            ((FunctionType ()
              ((Prod
                ((Ref (Base MM) (Ser (Prod ())))
                 (Prod
                  ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                    (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))
                   (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                    (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))))
              ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
              ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
             (FunctionType ()
              ((Prod
                ((Ref (Base MM) (Ser (Prod ())))
                 (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                  (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))
              ((Num (Int I32))))
             (FunctionType () () ((Num (Int I32))))))
           (table
            ((FunctionType ()
              ((Prod
                ((Ref (Base MM) (Ser (Prod ())))
                 (Prod
                  ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                    (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))
                   (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                    (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))))
              ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
              ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
             (FunctionType ()
              ((Prod
                ((Ref (Base MM) (Ser (Prod ())))
                 (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                  (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))
              ((Num (Int I32))))))
           (lfx (InferFx))))
         (state
          ((locals
            ((Plug
              (Prod
               ((Atom Ptr)
                (Prod
                 ((Sum ((Prod ()) (Atom Ptr))) (Sum ((Prod ()) (Atom Ptr))))))))
             (Ref (Base MM) (Ser (Prod ())))
             (Plug
              (Prod ((Sum ((Prod ()) (Atom Ptr))) (Sum ((Prod ()) (Atom Ptr))))))
             (Plug (Sum ((Prod ()) (Atom Ptr))))
             (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
              (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))
             (Plug (Prod ()))
             (Sum
              ((Prod ())
               (Ref (Base MM)
                (Ser
                 (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                  (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))))
             (Plug (Prod ((Atom I32) (Atom Ptr))))
             (CodeRef
              (FunctionType ()
               ((Prod
                 ((Ref (Base MM) (Ser (Var 0)))
                  (Prod
                   ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                     (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))
                    (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                     (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))))
               ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                 (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))
             (Plug (Atom Ptr)) (Plug (Sum ((Prod ()) (Atom Ptr))))))
           (stack ((Plug (Atom Ptr)) (Ref (Base MM) (Ser (Var 0)))))))))
       (instr
        (Unpack
         (ArrowType 1
          ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
            (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
         InferFx
         ((LocalSet 7) (LocalGet 7 Follow) Ungroup (LocalSet 9) (LocalSet 8)
          (LocalGet 9 Follow) (LocalGet 9 Follow) (Load (Path ()) Move)
          (LocalSet 10) Drop (LocalGet 10 Move) (LocalGet 8 Follow) (Group 2)
          (Group 2) (LocalGet 8 Follow) CallIndirect (LocalGet 8 Move) Drop
          (LocalGet 9 Move) Drop (LocalGet 7 Move) Drop)))
       (env
        ((local_offset 1) (kinds ())
         (labels
          (((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
             (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))
         (return
          ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
            (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
         (functions
          ((FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Prod
                ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                  (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))
                 (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                  (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))))
            ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
              (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
           (FunctionType ()
            ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
            ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
              (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))
            ((Num (Int I32))))
           (FunctionType () () ((Num (Int I32))))))
         (table
          ((FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Prod
                ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                  (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))
                 (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                  (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))))
            ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
              (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
           (FunctionType ()
            ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
            ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
              (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))
            ((Num (Int I32))))))
         (lfx (InferFx))))
       (state
        ((locals
          ((Plug
            (Prod
             ((Atom Ptr)
              (Prod ((Sum ((Prod ()) (Atom Ptr))) (Sum ((Prod ()) (Atom Ptr))))))))
           (Ref (Base MM) (Ser (Prod ())))
           (Plug
            (Prod ((Sum ((Prod ()) (Atom Ptr))) (Sum ((Prod ()) (Atom Ptr))))))
           (Plug (Sum ((Prod ()) (Atom Ptr))))
           (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
            (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))
           (Plug (Prod ()))
           (Sum
            ((Prod ())
             (Ref (Base MM)
              (Ser
               (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))))
           (Plug (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))
           (Plug
            (Prod
             ((Atom I32) (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))))
           (Plug (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))
           (Plug (Sum ((Prod ()) (Atom Ptr))))))
         (stack
          ((Exists (Type (VALTYPE (Prod ()) ImCopy ImDrop))
            (Prod
             ((CodeRef
               (FunctionType ()
                ((Prod
                  ((Ref (Base MM) (Ser (Var 0)))
                   (Prod
                    ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                      (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))
                     (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                      (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))))
                ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                  (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))
              (Ref (Base MM) (Ser (Var 0))))))))))))
     (instr
      (Case
       (ArrowType 1
        ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
          (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
       InferFx
       (((LocalSet 5) (LocalGet 4 Follow) (LocalGet 5 Move) Drop)
        ((LocalSet 6) (CodeRef 0) (Group 0) (New MM) (Group 2)
         (Pack (Type (Prod ()))
          (Prod
           ((CodeRef
             (FunctionType ()
              ((Prod
                ((Ref (Base MM) (Ser (Var 0)))
                 (Prod
                  ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                    (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))
                   (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                    (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))))
              ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))
            (Ref (Base MM) (Ser (Var 0))))))
         (Unpack
          (ArrowType 1
           ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
             (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
          InferFx
          ((LocalSet 7) (LocalGet 7 Follow) Ungroup (LocalSet 9) (LocalSet 8)
           (LocalGet 9 Follow) (LocalGet 9 Follow) (Load (Path ()) Move)
           (LocalSet 10) Drop (LocalGet 10 Move) (LocalGet 8 Follow) (Group 2)
           (Group 2) (LocalGet 8 Follow) CallIndirect (LocalGet 8 Move) Drop
           (LocalGet 9 Move) Drop (LocalGet 7 Move) Drop))
         (New MM)
         (Inject () 1
          ((Prod ())
           (Ref (Base MM)
            (Ser
             (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
              (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))))
         (Fold
          (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
           (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))
         (LocalGet 6 Move) Drop))))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return
        ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
          (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
       (functions
        ((FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Prod
              ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))
               (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))))
          ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
            (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
         (FunctionType ()
          ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
          ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
            (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
              (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))
          ((Num (Int I32))))
         (FunctionType () () ((Num (Int I32))))))
       (table
        ((FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Prod
              ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))
               (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))))
          ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
            (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
         (FunctionType ()
          ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
          ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
            (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
              (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))
          ((Num (Int I32))))))
       (lfx ())))
     (state
      ((locals
        ((Plug
          (Prod
           ((Atom Ptr)
            (Prod ((Sum ((Prod ()) (Atom Ptr))) (Sum ((Prod ()) (Atom Ptr))))))))
         (Ref (Base MM) (Ser (Prod ())))
         (Plug
          (Prod ((Sum ((Prod ()) (Atom Ptr))) (Sum ((Prod ()) (Atom Ptr))))))
         (Plug (Sum ((Prod ()) (Atom Ptr))))
         (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
          (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))
         (Plug (Prod ())) (Plug (Atom Ptr))
         (Plug (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))
         (Plug
          (Prod ((Atom I32) (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))))
         (Plug (Prod ((Prod ((Atom I32) (Atom Ptr))) (Atom Ptr))))
         (Plug (Sum ((Prod ()) (Atom Ptr))))))
       (stack
        ((Sum
          ((Prod ())
           (Ref (Base MM)
            (Ser
             (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
              (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))))))))
    -----------mini_zip-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT
              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                  (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
          mf_locals := [ (AtomR PtrR); (AtomR I32R)];
          mf_body :=
            [ (ILocalGet
              (InstrT []
                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])
              0);
              (IUngroup
                (InstrT
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
              (ILocalSet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (ILocalSet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])
                1);
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
              (INum
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (IInt2 I32T AddI));
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])
                1);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                  []));
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []))];
        |};
          {|
            mf_type :=
              (MonoFunT
                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]) NoCopy ExDrop)
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                    (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]);
            mf_locals :=
              [ (AtomR PtrR);
                (ProdR [ (AtomR I32R); (AtomR I32R)]);
                (AtomR I32R);
                (AtomR I32R);
                (ProdR [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR PtrR)]);
                (ProdR [ (AtomR I32R); (ProdR [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR PtrR)])]);
                (ProdR [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR PtrR)]);
                (ProdR [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR PtrR)]);
                (ProdR [ (AtomR I32R); (ProdR [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR PtrR)])]);
                (ProdR [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR PtrR)])];
            mf_body :=
              [ (ILocalGet
                (InstrT []
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]) NoCopy ExDrop)
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])])
                0);
                (IUngroup
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]) NoCopy ExDrop)
                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                        (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]));
                (ILocalSet
                  (InstrT []
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])
                  2);
                (ILocalSet
                  (InstrT []
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])
                  1);
                (ILocalGet
                  (InstrT []
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])
                  2);
                (IUngroup
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                (ILocalSet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
                (ILocalSet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
                (ICodeRef
                  (InstrT []
                    [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                      (MonoFunT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                  0);
                (IGroup (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
                (INew
                  (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]));
                (IGroup
                  (InstrT
                    [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                      (MonoFunT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]));
                (IPack
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]
                    [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      (VALTYPE (ProdR []) ImCopy ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]));
                (IUnpack
                  (InstrT
                    [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      (VALTYPE (ProdR []) ImCopy ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                  (PlugT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]) ImCopy ImDrop)
                    (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]))
                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))
                  (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR PtrR)]))
                  (PlugT (VALTYPE (AtomR I32R) ImCopy ImDrop) (AtomR I32R))
                  (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))
                  (PlugT (VALTYPE (ProdR [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR PtrR)]) ImCopy ImDrop)
                    (ProdR [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR PtrR)]))
                  (PlugT
                    (VALTYPE (ProdR [ (AtomR I32R); (ProdR [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR PtrR)])]) ImCopy
                      ImDrop)
                    (ProdR [ (AtomR I32R); (ProdR [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR PtrR)])]))
                  (PlugT (VALTYPE (ProdR [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR PtrR)]) ImCopy ImDrop)
                    (ProdR [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR PtrR)]))
                  [ (ILocalSet
                    (InstrT []
                      [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])])
                    5);
                    (ILocalGet
                      (InstrT []
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])])
                      5);
                    (IUngroup
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]));
                    (ILocalSet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                      7);
                    (ILocalSet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      6);
                    (ILocalGet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                      7);
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      6);
                    (IGroup
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      6);
                    (ICallIndirect
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      6);
                    (IDrop
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        []));
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))]) 7);
                    (IDrop (InstrT [ (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))] []));
                    (ILocalGet
                      (InstrT []
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR PtrR)]))])
                      5);
                    (IDrop
                      (InstrT
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR PtrR)]))]
                        []))]);
                (ICodeRef
                  (InstrT []
                    [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                      (MonoFunT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                  0);
                (IGroup (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
                (INew
                  (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]));
                (IGroup
                  (InstrT
                    [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                      (MonoFunT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]));
                (IPack
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]
                    [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      (VALTYPE (ProdR []) ImCopy ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]));
                (IUnpack
                  (InstrT
                    [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      (VALTYPE (ProdR []) ImCopy ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                  (PlugT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]) ImCopy ImDrop)
                    (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]))
                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))
                  (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR PtrR)]))
                  (PlugT (VALTYPE (AtomR I32R) ImCopy ImDrop) (AtomR I32R))
                  (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR PtrR)]))
                  (PlugT (VALTYPE (AtomR I32R) ImCopy ImDrop) (AtomR I32R))
                  (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))
                  [ (ILocalSet
                    (InstrT []
                      [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])])
                    8);
                    (ILocalGet
                      (InstrT []
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])])
                      8);
                    (IUngroup
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]));
                    (ILocalSet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                      10);
                    (ILocalSet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      9);
                    (ILocalGet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                      10);
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))]) 10);
                    (IGroup
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                          (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))]
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                            (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))])]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      9);
                    (ICallIndirect
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      9);
                    (IDrop
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        []));
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))]) 10);
                    (IDrop (InstrT [ (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))] []));
                    (ILocalGet
                      (InstrT []
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR PtrR)]))])
                      8);
                    (IDrop
                      (InstrT
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR PtrR)]))]
                        []))]);
                (IGroup
                  (InstrT
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]));
                (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
                (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []));
                (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
                (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []));
                (ILocalGet
                  (InstrT []
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])
                  1);
                (IDrop
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                    []));
                (ILocalGet
                  (InstrT []
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])
                  2);
                (IDrop
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                    []))];
          |};
          {|
            mf_type :=
              (MonoFunT
                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR PtrR)])]) NoCopy ExDrop)
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                    (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))))])])]
                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                  (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R); (AtomR PtrR)])) ExDrop)
                    (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])))]);
            mf_locals :=
              [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR PtrR)]); (AtomR PtrR); (AtomR PtrR); (AtomR I32R); (AtomR PtrR)];
            mf_body :=
              [ (ILocalGet
                (InstrT []
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR PtrR)])]) NoCopy ExDrop)
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                      (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))))])])])
                0);
                (IUngroup
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR PtrR)])]) NoCopy ExDrop)
                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                        (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))))])])]
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                      (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))))])]));
                (ILocalSet
                  (InstrT []
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))))])])
                  2);
                (ILocalSet
                  (InstrT []
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])
                  1);
                (ILocalGet
                  (InstrT []
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))))])])
                  2);
                (IUngroup
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))))])]
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))))]));
                (ILocalSet
                  (InstrT []
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))))])
                  4);
                (ILocalSet
                  (InstrT []
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])
                  3);
                (ILocalGet
                  (InstrT []
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])
                  3);
                (ILoad
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SpanT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (RepS (AtomR I32R))));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                  [] Move);
                (ILocalSet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 5);
                (IDrop
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SpanT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (RepS (AtomR I32R))))]
                    []));
                (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 5);
                (ILocalGet
                  (InstrT []
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))))])
                  4);
                (ILoad
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))))]
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SpanT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (RepS (AtomR PtrR))));
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])
                  [] Move);
                (ILocalSet
                  (InstrT []
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])
                  6);
                (IDrop
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SpanT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (RepS (AtomR PtrR))))]
                    []));
                (ILocalGet
                  (InstrT []
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])
                  6);
                (IGroup
                  (InstrT
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])]));
                (INew
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])]
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R); (AtomR PtrR)])) ExDrop)
                        (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])))]));
                (ILocalGet (InstrT [] [ (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))]) 3);
                (IDrop (InstrT [ (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))] []));
                (ILocalGet (InstrT [] [ (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))]) 4);
                (IDrop (InstrT [ (PlugT (VALTYPE (AtomR PtrR) ImCopy ImDrop) (AtomR PtrR))] []));
                (ILocalGet
                  (InstrT []
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])
                  1);
                (IDrop
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                    []));
                (ILocalGet
                  (InstrT []
                    [ (PlugT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ImCopy ImDrop) (ProdR [ (AtomR PtrR); (AtomR PtrR)]))])
                  2);
                (IDrop
                  (InstrT
                    [ (PlugT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ImCopy ImDrop) (ProdR [ (AtomR PtrR); (AtomR PtrR)]))]
                    []))];
          |}];
      m_table := [ 0; 1; 2];
      m_exports := [ 1];
    |} |xxx}]
