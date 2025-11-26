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
    FAILURE (InstrErr (error (PopEmptyStack LocalSet)) (instr (LocalSet 2))
     (env
      ((local_offset 1) (kinds ()) (labels ()) (return ((Num (Int I32))))
       (functions
        ((FunctionType () ((Prod ())) ((Num (Int I32))))
         (FunctionType () () ((Num (Int I32))))))
       (table ((FunctionType () ((Prod ())) ((Num (Int I32))))))))
     (state ((locals (((Prod ())) () () ())) (stack ()))))
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
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0)];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------add_one_program-----------
    FAILURE (InstrErr (error (TODO pack))
     (instr
      (Pack (Type (Prod ()))
       (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
        (CodeRef
         (FunctionType () ((Prod ((Var 0) (Num (Int I32))))) ((Num (Int I32))))))))
     (env
      ((local_offset 0) (kinds ()) (labels ()) (return ((Num (Int I32))))
       (functions
        ((FunctionType ()
          ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
          ((Num (Int I32))))
         (FunctionType () () ((Num (Int I32))))))
       (table
        ((FunctionType ()
          ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
          ((Num (Int I32))))))))
     (state
      ((locals (() () ()))
       (stack
        ((Prod
          ((CodeRef
            (FunctionType ()
             ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
             ((Num (Int I32)))))
           (Ref (Base MM) (Ser (Prod ()))))))))))
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
                (IInt2 I32T AddI))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------print_10-----------
    FAILURE (InstrErr (error (InvalidTableIdx 0)) (instr (CodeRef 0))
     (env
      ((local_offset 0) (kinds ()) (labels ()) (return ((Prod ())))
       (functions ((FunctionType () () ((Prod ()))))) (table ())))
     (state ((locals (() () ())) (stack ()))))
    -----------factorial_program-----------
    FAILURE (InstrErr (error (TODO pack))
     (instr
      (Ite (ArrowType 1 ((Num (Int I32)))) (LocalFx ()) ((NumConst (Int I32) 1))
       ((LocalGet 2 Follow) (NumConst (Int I32) 1) (Num (Int2 I32 Sub))
        (LocalSet 3) (CodeRef 0) (Group 0) (New MM) (Group 2)
        (Pack (Type (Prod ()))
         (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
          (CodeRef
           (FunctionType () ((Prod ((Var 0) (Num (Int I32))))) ((Num (Int I32)))))))
        (Unpack (ArrowType 1 ((Num (Int I32)))) (LocalFx ())
         ((LocalSet 4) (LocalGet 4 Follow) Ungroup (LocalSet 6) (LocalSet 5)
          (LocalGet 6 Follow) (LocalGet 6 Follow) (Group 2) (LocalGet 5 Follow)
          CallIndirect))
        (LocalSet 7) (LocalGet 2 Follow) (LocalGet 7 Follow)
        (Num (Int2 I32 Mul)))))
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
          ((Num (Int I32))))))))
     (state
      ((locals
        (() ((Ref (Base MM) (Ser (Prod ())))) ((Num (Int I32))) () () () () ()))
       (stack ((Num (Int I32)) (Num (Int I32)))))))
    -----------safe_div-----------
    FAILURE (InstrErr (error (TODO elab_local_fx))
     (instr
      (Ite (ArrowType 1 ((Sum ((Num (Int I32)) (Prod ()))))) (LocalFx ())
       ((Group 0) (Inject () 1 ((Num (Int I32)) (Prod ()))))
       ((LocalGet 3 Follow) (LocalGet 4 Follow) (Num (Int2 I32 (Div Signed)))
        (LocalSet 5) (LocalGet 5 Follow)
        (Inject () 0 ((Num (Int I32)) (Prod ()))))))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return ((Sum ((Num (Int I32)) (Prod ())))))
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
          ((Num (Int I32))))))))
     (state
      ((locals
        (() ((Ref (Base MM) (Ser (Prod ()))))
         ((Prod ((Num (Int I32)) (Num (Int I32))))) ((Num (Int I32)))
         ((Num (Int I32))) ()))
       (stack ((Num (Int I32)) (Num (Int I32)))))))
    -----------incr_n-----------
    FAILURE (InstrErr (error (TODO pack))
     (instr
      (Ite (ArrowType 1 ((Num (Int I32)))) (LocalFx ())
       ((LocalGet 3 Follow) (Load (Path ()) Move) (LocalSet 5) Drop
        (LocalGet 5 Move))
       ((CodeRef 0) (Group 0) (New MM) (Group 2)
        (Pack (Type (Prod ()))
         (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
          (CodeRef
           (FunctionType ()
            ((Prod ((Var 0) (Ref (Base MM) (Ser (Num (Int I32)))))))
            ((Ref (Base MM) (Ser (Num (Int I32)))))))))
        (Unpack (ArrowType 1 ((Ref (Base MM) (Ser (Num (Int I32))))))
         (LocalFx ())
         ((LocalSet 6) (LocalGet 6 Follow) Ungroup (LocalSet 8) (LocalSet 7)
          (LocalGet 8 Follow) (LocalGet 7 Follow) (Group 2) (LocalGet 7 Follow)
          CallIndirect))
        (LocalSet 9) (LocalGet 4 Follow) (NumConst (Int I32) 1)
        (Num (Int2 I32 Sub)) (LocalSet 10) (CodeRef 1) (Group 0) (New MM)
        (Group 2)
        (Pack (Type (Prod ()))
         (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
          (CodeRef
           (FunctionType ()
            ((Prod
              ((Var 0)
               (Prod ((Ref (Base MM) (Ser (Num (Int I32)))) (Num (Int I32)))))))
            ((Num (Int I32)))))))
        (Unpack (ArrowType 1 ((Num (Int I32)))) (LocalFx ())
         ((LocalSet 11) (LocalGet 11 Follow) Ungroup (LocalSet 13) (LocalSet 12)
          (LocalGet 13 Follow) (LocalGet 12 Follow) (LocalGet 13 Follow)
          (Group 2) (Group 2) (LocalGet 12 Follow) CallIndirect)))))
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
          ((Num (Int I32))))))))
     (state
      ((locals
        (() ((Ref (Base MM) (Ser (Prod ())))) ()
         ((Ref (Base MM) (Ser (Num (Int I32))))) ((Num (Int I32))) () () () () ()
         () () () ()))
       (stack ((Num (Int I32)) (Num (Int I32)))))))
    -----------fix_factorial[invalid]-----------
    FAILURE (InstrErr (error (PopEmptyStack LocalSet)) (instr (LocalSet 1))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return
        ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
          (CodeRef
           (FunctionType () ((Prod ((Var 0) (Num (Int I32))))) ((Num (Int I32))))))))
       (functions
        ((FunctionType ()
          ((Prod
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod
                  ((Var 0)
                   (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (CodeRef
                     (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                      ((Num (Int I32)))))))))
                ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                    ((Num (Int I32)))))))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
              ((Num (Int I32))))))))
         (FunctionType () ((Prod ()))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
              ((Num (Int I32))))))))
         (FunctionType ()
          ((Prod
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                ((Num (Int I32)))))))))
          ((Num (Int I32))))
         (FunctionType () ((Prod ()))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
              ((Num (Int I32))))))))
         (FunctionType () () ((Num (Int I32))))))
       (table
        ((FunctionType ()
          ((Prod
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod
                  ((Var 0)
                   (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (CodeRef
                     (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                      ((Num (Int I32)))))))))
                ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                    ((Num (Int I32)))))))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
              ((Num (Int I32))))))))
         (FunctionType () ((Prod ()))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
              ((Num (Int I32))))))))
         (FunctionType ()
          ((Prod
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                ((Num (Int I32)))))))))
          ((Num (Int I32))))
         (FunctionType () ((Prod ()))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
              ((Num (Int I32))))))))))))
     (state
      ((locals
        (((Prod
           ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
             (CodeRef
              (FunctionType ()
               ((Prod
                 ((Var 0)
                  (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                   (CodeRef
                    (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                     ((Num (Int I32)))))))))
               ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                 (CodeRef
                  (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                   ((Num (Int I32)))))))))))))
         ()
         ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
           (CodeRef
            (FunctionType ()
             ((Prod
               ((Var 0)
                (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                 (CodeRef
                  (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                   ((Num (Int I32)))))))))
             ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
               (CodeRef
                (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
                 ((Num (Int I32)))))))))))
         () () () () () () () () () ()))
       (stack ()))))
    -----------unboxed_list[invalid]-----------
    FAILURE (Codegen
     (CannotResolveRepOfRecTypeWithoutIndirection (Var (0 ("\206\177")))))
    -----------boxed_list-----------
    FAILURE (InstrErr (error (PopEmptyStack LocalSet)) (instr (LocalSet 2))
     (env
      ((local_offset 1) (kinds ()) (labels ()) (return ((Num (Int I32))))
       (functions
        ((FunctionType () ((Prod ())) ((Num (Int I32))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Prod
              ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (CodeRef
                 (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
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
        ((FunctionType () ((Prod ())) ((Num (Int I32))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Prod
              ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (CodeRef
                 (FunctionType () ((Prod ((Var 0) (Num (Int I32)))))
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
             ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))))
     (state ((locals (((Prod ())) () () ())) (stack ()))))
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
    FAILURE (InstrErr (error (TODO elab_local_fx))
     (instr
      (Case
       (ArrowType 1
        ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
          (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
       (LocalFx ())
       (((LocalSet 5) (LocalGet 4 Follow))
        ((LocalSet 6) (CodeRef 0) (Group 0) (New MM) (Group 2)
         (Pack (Type (Prod ()))
          (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
           (CodeRef
            (FunctionType ()
             ((Prod
               ((Var 0)
                (Prod
                 ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                   (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))
                  (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                   (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))))
             ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
               (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))))
         (Unpack
          (ArrowType 1
           ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
             (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
          (LocalFx ())
          ((LocalSet 7) (LocalGet 7 Follow) Ungroup (LocalSet 9) (LocalSet 8)
           (LocalGet 9 Follow) (LocalGet 9 Follow) (Load (Path ()) Move)
           (LocalSet 10) Drop (LocalGet 10 Move) (LocalGet 8 Follow) (Group 2)
           (Group 2) (LocalGet 8 Follow) CallIndirect))
         (New MM)
         (Inject () 1
          ((Prod ())
           (Ref (Base MM)
            (Ser
             (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
              (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))))
         (Fold
          (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
           (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))))
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
          ((Num (Int I32))))))))
     (state
      ((locals
        (() ((Ref (Base MM) (Ser (Prod ())))) () ()
         ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
           (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))
         () () () () () ()))
       (stack
        ((Sum
          ((Prod ())
           (Ref (Base MM)
            (Ser
             (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
              (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))))))))
    -----------mini_zip-----------
    FAILURE (InstrErr (error (TODO pack))
     (instr
      (Pack (Type (Prod ()))
       (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
        (CodeRef
         (FunctionType () ((Prod ((Var 0) (Num (Int I32))))) ((Num (Int I32))))))))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return ((Prod ((Num (Int I32)) (Num (Int I32))))))
       (functions
        ((FunctionType ()
          ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
          ((Num (Int I32))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Prod ((Num (Int I32)) (Num (Int I32)))))))
          ((Prod ((Num (Int I32)) (Num (Int I32))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Prod
              ((Ref (Base MM) (Ser (Num (Int I32))))
               (Ref (Base MM) (Ser (Ref (Base MM) (Ser (Num (Int I32)))))))))))
          ((Ref (Base MM)
            (Ser (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Num (Int I32))))))))))))
       (table
        ((FunctionType ()
          ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
          ((Num (Int I32))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Prod ((Num (Int I32)) (Num (Int I32)))))))
          ((Prod ((Num (Int I32)) (Num (Int I32))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Prod
              ((Ref (Base MM) (Ser (Num (Int I32))))
               (Ref (Base MM) (Ser (Ref (Base MM) (Ser (Num (Int I32)))))))))))
          ((Ref (Base MM)
            (Ser (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Num (Int I32))))))))))))))
     (state
      ((locals
        (() ((Ref (Base MM) (Ser (Prod ()))))
         ((Prod ((Num (Int I32)) (Num (Int I32))))) ((Num (Int I32)))
         ((Num (Int I32))) () () () () () ()))
       (stack
        ((Prod
          ((CodeRef
            (FunctionType ()
             ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
             ((Num (Int I32)))))
           (Ref (Base MM) (Ser (Prod ())))))))))) |xxx}]
