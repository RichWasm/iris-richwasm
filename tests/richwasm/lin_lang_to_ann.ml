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
    x
    |> Main.compile_ast
    |> Main.Res.run
    |> fst
    |> or_fail_pp Main.CompileErr.pp
    |> elab

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
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
    |} |xxx}];
  next ();
  [%expect
    {|
    ((m_imports ())
     (m_functions
      (((mf_type (MonoFunT () ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))))
        (mf_locals ()) (mf_body ((INumConst (InstrT () ((NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))) 1))))))
     (m_table ()) (m_exports (((me_name _start) (me_desc 0))))) |}];

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
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
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
     (m_table ()) (m_exports (((me_name _start) (me_desc 0))))) |}];

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
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
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
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
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
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
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
     (m_table ()) (m_exports (((me_name _start) (me_desc 0))))) |}];

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
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
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
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
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
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
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
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
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
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
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
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
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
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
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
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
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
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
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
              (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 2);
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                  [])
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
              (ILocalSet (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])] []) 3);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SpanT (MEMTYPE (RepS (ProdR [])) ImDrop) (RepS (ProdR []))))]
                  []));
              (ILocalGet (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]) 3);
              (IUngroup (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])] []));
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 4);
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
              (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []));
              (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 1);
              (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []))];
        |};
          {|
            mf_type := (MonoFunT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
            mf_locals := [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR I32R); (AtomR PtrR)];
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
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  [ (ILocalSet
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
                      [])
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
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]
                        [])
                      2);
                    (ILocalSet
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        [])
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
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
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
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 2);
                    (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                    (ILocalGet
                      (InstrT []
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                      0);
                    (IDrop
                      (InstrT
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                        []))])];
          |}];
      m_table := [ 0];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 1;
                   |}];
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
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
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
              (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 0);
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0);
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0);
              (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []))];
        |}];
      m_table := [];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
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
              (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 2);
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                  [])
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
            mf_locals := [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR I32R); (AtomR PtrR)];
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
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  [ (ILocalSet
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
                      [])
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
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]
                        [])
                      2);
                    (ILocalSet
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        [])
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
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
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
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 2);
                    (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                    (ILocalGet
                      (InstrT []
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                      0);
                    (IDrop
                      (InstrT
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                        []))])];
          |}];
      m_table := [ 0];
      m_exports := [ {|
                     me_name := "add-one"; me_desc := 0;
                   |}; {|
                         me_name := "_start"; me_desc := 1;
                       |}];
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
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]
                  [])
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
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]
                  [])
                2);
              (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 1);
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
              (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 3);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SpanT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (RepS (AtomR I32R))))]
                  []));
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
              (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 4);
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
              (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 2);
              (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
              (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 0);
              (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []))];
        |}];
      m_table := [];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
    |}
    -----------print_10-----------
    {|
      m_imports :=
        [ (MonoFunT
          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT
              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                  (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]);
          mf_locals := [];
          mf_body :=
            [ (ILocalGet
              (InstrT []
                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])
              0);
              (ICall
                (InstrT
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])
                0 [])];
        |};
          {|
            mf_type := (MonoFunT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]);
            mf_locals := [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR I32R); (AtomR PtrR)];
            mf_body :=
              [ (ICodeRef
                (InstrT []
                  [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                    (MonoFunT
                      [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]))])
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
                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
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
                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
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
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
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
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]
                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  [ (ILocalSet
                    (InstrT
                      [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                      [])
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
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
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
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]));
                    (ILocalSet
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]
                        [])
                      2);
                    (ILocalSet
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]))]
                        [])
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
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]))])
                      1);
                    (ICallIndirect
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]))]
                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]))])
                      1);
                    (IDrop
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]))]
                        []));
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 2);
                    (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                    (ILocalGet
                      (InstrT []
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                      0);
                    (IDrop
                      (InstrT
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                        []))])];
          |}];
      m_table := [ 0];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 1;
                   |}];
    |}
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
              (ILocalSet (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])] []) 2);
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])))]
                  [])
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
                (InstrT
                  [ (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                  [])
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
              (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 4);
              (ILocalGet (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]) 2);
              (ILocalSet (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])] []) 5);
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
              (ILocalGet (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]) 5);
              (IDrop (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])] []));
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
              (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []));
              (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 1);
              (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
              (ILocalGet (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]) 2);
              (IDrop (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])] []))];
        |};
          {|
            mf_type := (MonoFunT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
            mf_locals := [ (AtomR I32R); (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR I32R); (AtomR PtrR)];
            mf_body :=
              [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 10);
                (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 0);
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
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  [ (ILocalSet
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
                      [])
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
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)))]
                        [])
                      3);
                    (ILocalSet
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        [])
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
                            (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]);
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [])]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                                  (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
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
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 3);
                    (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                    (ILocalGet
                      (InstrT []
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                      1);
                    (IDrop
                      (InstrT
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                        []))]);
                (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0);
                (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []))];
          |}];
      m_table := [ 0];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 1;
                   |}];
    |}
    -----------closure_call_var-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT
              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                  (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                    (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])));
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
          mf_locals := [ (AtomR PtrR); (AtomR I32R); (ProdR [ (AtomR I32R)]); (AtomR I32R); (AtomR I32R)];
          mf_body :=
            [ (ILocalGet
              (InstrT []
                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])
              0);
              (IUngroup
                (InstrT
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                        (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
              (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 2);
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])))]
                  [])
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
                (InstrT
                  [ (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                  [])
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
              (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 4);
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 5);
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 5);
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
              (INum
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (IInt2 I32T AddI));
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 5);
              (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []));
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
              (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []));
              (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 1);
              (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []))];
        |};
          {|
            mf_type := (MonoFunT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
            mf_locals := [ (AtomR I32R); (AtomR I32R); (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR I32R); (AtomR PtrR)];
            mf_body :=
              [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 21);
                (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 0);
                (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
                (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 1);
                (ICodeRef
                  (InstrT []
                    [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                      (MonoFunT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                              (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                  0);
                (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
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
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                              (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                          (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                                (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])));
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
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
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop)
                                (ProdT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop)
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])));
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
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
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
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
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)))]))]
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  [ (ILocalSet
                    (InstrT
                      [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)))])]
                      [])
                    2);
                    (ILocalGet
                      (InstrT []
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)))])])
                      2);
                    (IUngroup
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)))])]
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)))]));
                    (ILocalSet
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)))]
                        [])
                      4);
                    (ILocalSet
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        [])
                      3);
                    (ILocalGet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)))])
                      4);
                    (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0);
                    (IGroup
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      3);
                    (ICallIndirect
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      3);
                    (IDrop
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [ (AtomR I32R)])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        []));
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 4);
                    (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                    (ILocalGet
                      (InstrT []
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                      2);
                    (IDrop
                      (InstrT
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                        []))]);
                (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
                (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []));
                (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0);
                (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []))];
          |}];
      m_table := [ 0];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 1;
                   |}];
    |}
    -----------triangle_tl-----------
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
          mf_locals := [ (AtomR PtrR); (AtomR I32R); (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR I32R); (AtomR PtrR)];
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
              (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 2);
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                  [])
                1);
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0);
              (INum
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (IIntTest I32T EqzI));
              (IIte
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                  (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))
                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0)]
                [ (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
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
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
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
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
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
                    (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                    (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                    (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                    (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                    [ (ILocalSet
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
                        [])
                      3);
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
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])])
                        3);
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
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
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
                        (InstrT
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]
                          [])
                        5);
                      (ILocalSet
                        (InstrT
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                          [])
                        4);
                      (ILocalGet
                        (InstrT []
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                        5);
                      (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
                      (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
                      (INum
                        (InstrT
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                        (IInt2 I32T SubI));
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
                        4);
                      (ICallIndirect
                        (InstrT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
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
                        4);
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
                      (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 5);
                      (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                      (ILocalGet
                        (InstrT []
                          [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                            (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                        3);
                      (IDrop
                        (InstrT
                          [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                            (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                          []))]);
                  (INum
                    (InstrT
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                    (IInt2 I32T AddI))]);
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
            mf_locals := [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR I32R); (AtomR PtrR)];
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
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  [ (ILocalSet
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
                      [])
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
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]
                        [])
                      2);
                    (ILocalSet
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        [])
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
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
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
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 2);
                    (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                    (ILocalGet
                      (InstrT []
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                      0);
                    (IDrop
                      (InstrT
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                        []))])];
          |}];
      m_table := [ 0];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 1;
                   |}];
    |}
    -----------factorial_tl-----------
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
          mf_locals :=
            [ (AtomR PtrR);
              (AtomR I32R);
              (AtomR I32R);
              (ProdR [ (AtomR I32R); (AtomR PtrR)]);
              (AtomR I32R);
              (AtomR PtrR);
              (AtomR I32R)];
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
              (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 2);
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                  [])
                1);
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0);
              (INum
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (IIntTest I32T EqzI));
              (IIte
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                  (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))
                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1)]
                [ (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
                  (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
                  (INum
                    (InstrT
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                    (IInt2 I32T SubI));
                  (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 3);
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
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
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
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
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
                    (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                    (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                    (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                    (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                    (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                    [ (ILocalSet
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
                        [])
                      4);
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
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])])
                        4);
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
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
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
                        (InstrT
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]
                          [])
                        6);
                      (ILocalSet
                        (InstrT
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                          [])
                        5);
                      (ILocalGet
                        (InstrT []
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                        6);
                      (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
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
                        5);
                      (ICallIndirect
                        (InstrT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
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
                        5);
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
                      (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 6);
                      (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                      (ILocalGet
                        (InstrT []
                          [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                            (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                        4);
                      (IDrop
                        (InstrT
                          [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                            (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                          []))]);
                  (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 7);
                  (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
                  (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 7);
                  (INum
                    (InstrT
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                    (IInt2 I32T MulI));
                  (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 7);
                  (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []));
                  (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
                  (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []))]);
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
            mf_locals := [ (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR I32R); (AtomR PtrR)];
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
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  [ (ILocalSet
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
                      [])
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
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]
                        [])
                      2);
                    (ILocalSet
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        [])
                      1);
                    (ILocalGet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                      2);
                    (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 5);
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
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
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
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 2);
                    (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                    (ILocalGet
                      (InstrT []
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                      0);
                    (IDrop
                      (InstrT
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                        []))])];
          |}];
      m_table := [ 0];
      m_exports := [ {|
                     me_name := "factorial"; me_desc := 0;
                   |}; {|
                         me_name := "_start"; me_desc := 1;
                       |}];
    |}
    -----------safe_div-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT
              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]) NoCopy ExDrop)
                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                  (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                  (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
              [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)); (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]);
          mf_locals := [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)]); (AtomR I32R); (AtomR I32R); (AtomR I32R)];
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
                (InstrT
                  [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                  [])
                2);
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                  [])
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
              (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 4);
              (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 3);
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0);
              (INum
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (IIntTest I32T EqzI));
              (IIte
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)); (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])
                (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                  (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R)]))
                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                  (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))
                (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                [ (IGroup (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
                  (IInject
                    (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]
                      [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                          (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])
                    1)]
                [ (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
                  (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
                  (INum
                    (InstrT
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                    (IInt2 I32T (DivI SignS)));
                  (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 5);
                  (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 5);
                  (IInject
                    (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                      [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                          (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])
                    0);
                  (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 5);
                  (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []))]);
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
                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (AtomR I32R); (ProdR [])])]) NoCopy ExDrop)
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                    (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)); (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])]
                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
            mf_locals := [ (AtomR PtrR); (SumR [ (AtomR I32R); (ProdR [])]); (AtomR I32R); (ProdR [])];
            mf_body :=
              [ (ILocalGet
                (InstrT []
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (AtomR I32R); (ProdR [])])]) NoCopy ExDrop)
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                      (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                          (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])])
                0);
                (IUngroup
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (AtomR I32R); (ProdR [])])]) NoCopy ExDrop)
                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                        (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                            (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])]
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                      (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                          (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]));
                (ILocalSet
                  (InstrT
                    [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)); (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                    [])
                  2);
                (ILocalSet
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                    [])
                  1);
                (ILocalGet
                  (InstrT []
                    [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)); (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])
                  2);
                (ICase
                  (InstrT
                    [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)); (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                    (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R)]))
                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))
                  (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)); (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR []) ImCopy ImDrop) (ProdR []))
                  [ [ (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 3);
                    (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
                    (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
                    (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []))];
                    [ (ILocalSet (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])] []) 4);
                      (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0);
                      (ILocalGet (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]) 4);
                      (IDrop (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])] []))]]);
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
                    [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)); (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])
                  2);
                (IDrop
                  (InstrT
                    [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)); (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                    []))];
          |};
          {|
            mf_type := (MonoFunT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
            mf_locals :=
              [ (ProdR [ (AtomR I32R); (AtomR PtrR)]);
                (AtomR I32R);
                (AtomR PtrR);
                (SumR [ (AtomR I32R); (ProdR [])]);
                (ProdR [ (AtomR I32R); (AtomR PtrR)]);
                (AtomR I32R);
                (AtomR PtrR)];
            mf_body :=
              [ (ICodeRef
                (InstrT []
                  [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                    (MonoFunT
                      [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]) NoCopy ExDrop)
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                          (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                      [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                          (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]))])
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
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                            (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                        [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                            (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]));
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                              (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                          [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                              (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]));
                (IPack
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                              (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                          [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                              (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]
                    [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      (VALTYPE (ProdR []) ImCopy ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                            [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]));
                (IUnpack
                  (InstrT
                    [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      (VALTYPE (ProdR []) ImCopy ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                            [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]
                    [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)); (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  [ (ILocalSet
                    (InstrT
                      [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                            [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                      [])
                    0);
                    (ILocalGet
                      (InstrT []
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                              [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                  (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])])
                      0);
                    (IUngroup
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                              [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                  (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                            [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]));
                    (ILocalSet
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]
                        [])
                      2);
                    (ILocalSet
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                            [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]))]
                        [])
                      1);
                    (ILocalGet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                      2);
                    (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 10);
                    (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0);
                    (IGroup
                      (InstrT
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]));
                    (IGroup
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                          (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                            (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                            [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]))])
                      1);
                    (ICallIndirect
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                            (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]);
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                              [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                  (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]))]
                        [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                            (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                            [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]))])
                      1);
                    (IDrop
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR I32R)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                            [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]))]
                        []));
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 2);
                    (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                    (ILocalGet
                      (InstrT []
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                      0);
                    (IDrop
                      (InstrT
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                        []))]);
                (ILocalSet
                  (InstrT
                    [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)); (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                    [])
                  3);
                (ICodeRef
                  (InstrT []
                    [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                      (MonoFunT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (AtomR I32R); (ProdR [])])]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                            (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                  1);
                (IGroup (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
                (INew
                  (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]));
                (IGroup
                  (InstrT
                    [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                      (MonoFunT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (AtomR I32R); (ProdR [])])]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                            (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (AtomR I32R); (ProdR [])])]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                              (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                  (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])]
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]));
                (IPack
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (AtomR I32R); (ProdR [])])]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                              (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                  (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])]
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]
                    [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      (VALTYPE (ProdR []) ImCopy ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (AtomR I32R); (ProdR [])])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                    (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])]
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
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (AtomR I32R); (ProdR [])])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                    (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)); (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  [ (ILocalSet
                    (InstrT
                      [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (AtomR I32R); (ProdR [])])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                    (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                      [])
                    4);
                    (ILocalGet
                      (InstrT []
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (AtomR I32R); (ProdR [])])]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                      (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])])
                      4);
                    (IUngroup
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (AtomR I32R); (ProdR [])])]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                      (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (AtomR I32R); (ProdR [])])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                    (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]));
                    (ILocalSet
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]
                        [])
                      6);
                    (ILocalSet
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (AtomR I32R); (ProdR [])])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                    (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        [])
                      5);
                    (ILocalGet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                      6);
                    (ILocalGet
                      (InstrT []
                        [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                            (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])
                      3);
                    (IGroup
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                          (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                              (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (AtomR I32R); (ProdR [])])]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                            (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (AtomR I32R); (ProdR [])])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                    (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      5);
                    (ICallIndirect
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (AtomR I32R); (ProdR [])])]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                            (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]);
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (AtomR I32R); (ProdR [])])]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                      (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (AtomR I32R); (ProdR [])])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                    (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      5);
                    (IDrop
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (AtomR I32R); (ProdR [])])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                                    (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        []));
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 6);
                    (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                    (ILocalGet
                      (InstrT []
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                      4);
                    (IDrop
                      (InstrT
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                        []))]);
                (ILocalGet
                  (InstrT []
                    [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)); (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])])
                  3);
                (IDrop
                  (InstrT
                    [ (SumT (VALTYPE (SumR [ (AtomR I32R); (ProdR [])]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)); (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])])]
                    []))];
          |}];
      m_table := [ 0; 1];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 2;
                   |}];
    |}
    -----------incr_n-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT
              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                  (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])]
              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]);
          mf_locals := [ (AtomR PtrR); (AtomR PtrR); (AtomR PtrR); (AtomR I32R); (AtomR I32R); (AtomR PtrR); (AtomR I32R)];
          mf_body :=
            [ (ILocalGet
              (InstrT []
                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])])
              0);
              (IUngroup
                (InstrT
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])]
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]));
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]
                  [])
                2);
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                  [])
                1);
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])
                2);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0);
              (ISwap
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                []);
              (IGroup
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]));
              (IUngroup
                (InstrT
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
              (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 4);
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]
                  [])
                3);
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
              (INum
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (IInt2 I32T AddI));
              (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 5);
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])
                3);
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 5);
              (ISwap
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                []);
              (IGroup
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]));
              (IUngroup
                (InstrT
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
              (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 7);
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]
                  [])
                6);
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])
                6);
              (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 6);
              (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 7);
              (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []));
              (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 5);
              (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []));
              (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 3);
              (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
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
              (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 2);
              (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []))];
        |};
          {|
            mf_type :=
              (MonoFunT
                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                    (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
            mf_locals :=
              [ (AtomR PtrR);
                (ProdR [ (AtomR PtrR); (AtomR I32R)]);
                (AtomR PtrR);
                (AtomR I32R);
                (AtomR I32R);
                (ProdR [ (AtomR I32R); (AtomR PtrR)]);
                (AtomR I32R);
                (AtomR PtrR);
                (AtomR PtrR);
                (AtomR I32R);
                (ProdR [ (AtomR I32R); (AtomR PtrR)]);
                (AtomR I32R);
                (AtomR PtrR)];
            mf_body :=
              [ (ILocalGet
                (InstrT []
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                      (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])])
                0);
                (IUngroup
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                        (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                      (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]));
                (ILocalSet
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                    [])
                  2);
                (ILocalSet
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                    [])
                  1);
                (ILocalGet
                  (InstrT []
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])
                  2);
                (IUngroup
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 4);
                (ILocalSet
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]
                    [])
                  3);
                (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
                (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0);
                (INum
                  (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                  (IIntTest I32T EqzI));
                (IIte
                  (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                    (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R)]))
                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  [ (ILocalGet
                    (InstrT []
                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])
                    3);
                    (ILoad
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SpanT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (RepS (AtomR I32R))));
                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                      [] Move);
                    (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 5);
                    (IDrop
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SpanT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (RepS (AtomR I32R))))]
                        []));
                    (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 5)]
                  [ (ICodeRef
                    (InstrT []
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])]
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]))])
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
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
                                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])]
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM)
                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])]
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]));
                    (IPack
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM)
                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])]
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]
                        [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          (VALTYPE (ProdR []) ImCopy ImDrop)
                          (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])]
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]));
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]));
                    (IUnpack
                      (InstrT
                        [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          (VALTYPE (ProdR []) ImCopy ImDrop)
                          (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])]
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]));
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                        (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R)]))
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                        (ProdR [ (AtomR I32R); (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                        (ProdR [ (AtomR I32R); (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                        (ProdR [ (AtomR I32R); (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                      [ (ILocalSet
                        (InstrT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])]
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]));
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                          [])
                        6);
                        (ILocalGet
                          (InstrT []
                            [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])]
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM)
                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]));
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])])
                          6);
                        (IUngroup
                          (InstrT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])]
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM)
                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]));
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])]
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]));
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]));
                        (ILocalSet
                          (InstrT
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]
                            [])
                          8);
                        (ILocalSet
                          (InstrT
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])]
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]))]
                            [])
                          7);
                        (ILocalGet
                          (InstrT []
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                          8);
                        (ILocalGet
                          (InstrT []
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])
                          3);
                        (IGroup
                          (InstrT
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])]));
                        (ILocalGet
                          (InstrT []
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])]
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]))])
                          7);
                        (ICallIndirect
                          (InstrT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]);
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])]
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM)
                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]))]
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]));
                        (ILocalGet
                          (InstrT []
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])]
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]))])
                          7);
                        (IDrop
                          (InstrT
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])]
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]))]
                            []));
                        (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))])
                          8);
                        (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                        (ILocalGet
                          (InstrT []
                            [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                              (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                          6);
                        (IDrop
                          (InstrT
                            [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                              (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                            []))]);
                    (ILocalSet
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]
                        [])
                      9);
                    (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
                    (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
                    (INum
                      (InstrT
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                      (IInt2 I32T SubI));
                    (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 10);
                    (ICodeRef
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
                                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                                (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM)
                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      1);
                    (IGroup (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
                    (INew
                      (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]));
                    (IGroup
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
                                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                                (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM)
                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                                  (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]));
                    (IPack
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                                  (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]
                        [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          (VALTYPE (ProdR []) ImCopy ImDrop)
                          (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]));
                    (IUnpack
                      (InstrT
                        [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          (VALTYPE (ProdR []) ImCopy ImDrop)
                          (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                        (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R)]))
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                        (ProdR [ (AtomR I32R); (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                        (ProdR [ (AtomR I32R); (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                        (ProdR [ (AtomR I32R); (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                      [ (ILocalSet
                        (InstrT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                          [])
                        11);
                        (ILocalGet
                          (InstrT []
                            [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                      (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])])
                          11);
                        (IUngroup
                          (InstrT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                      (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]));
                        (ILocalSet
                          (InstrT
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]
                            [])
                          13);
                        (ILocalSet
                          (InstrT
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                            [])
                          12);
                        (ILocalGet
                          (InstrT []
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                          13);
                        (ILocalGet
                          (InstrT []
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])
                          9);
                        (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 10);
                        (IGroup
                          (InstrT
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]));
                        (IGroup
                          (InstrT
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                              (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM)
                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]));
                        (ILocalGet
                          (InstrT []
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                          12);
                        (ICallIndirect
                          (InstrT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM)
                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]);
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                      (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                        (ILocalGet
                          (InstrT []
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                          12);
                        (IDrop
                          (InstrT
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                            []));
                        (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))])
                          13);
                        (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                        (ILocalGet
                          (InstrT []
                            [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                              (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                          11);
                        (IDrop
                          (InstrT
                            [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                              (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                            []))]);
                    (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 10);
                    (IDrop (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []));
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 9);
                    (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []))]);
                (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 3);
                (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
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
                    [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                  2);
                (IDrop
                  (InstrT
                    [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                    []))];
          |};
          {|
            mf_type := (MonoFunT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
            mf_locals := [ (AtomR PtrR); (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR I32R); (AtomR PtrR)];
            mf_body :=
              [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 10);
                (INew
                  (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]));
                (ILocalSet
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]
                    [])
                  0);
                (ICodeRef
                  (InstrT []
                    [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                      (MonoFunT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                            (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                  1);
                (IGroup (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
                (INew
                  (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]));
                (IGroup
                  (InstrT
                    [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                      (MonoFunT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                            (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                              (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]));
                (IPack
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                              (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]
                    [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      (VALTYPE (ProdR []) ImCopy ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM)
                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
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
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM)
                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  [ (ILocalSet
                    (InstrT
                      [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM)
                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                      [])
                    1);
                    (ILocalGet
                      (InstrT []
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])])
                      1);
                    (IUngroup
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM)
                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]));
                    (ILocalSet
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]
                        [])
                      3);
                    (ILocalSet
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM)
                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        [])
                      2);
                    (ILocalGet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                      3);
                    (ILocalGet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))])
                      0);
                    (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
                    (IGroup
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]));
                    (IGroup
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                          (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                            (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM)
                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      2);
                    (ICallIndirect
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                            (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]);
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM)
                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      2);
                    (IDrop
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (AtomR PtrR); (AtomR I32R)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM)
                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        []));
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 3);
                    (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                    (ILocalGet
                      (InstrT []
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                      1);
                    (IDrop
                      (InstrT
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                        []))]);
                (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 0);
                (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []))];
          |}];
      m_table := [ 0; 1];
      m_exports := [ {|
                     me_name := "incr_n"; me_desc := 1;
                   |}; {|
                         me_name := "_start"; me_desc := 2;
                       |}];
    |}
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
              (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
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
               (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
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
               (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
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
          ((Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
           (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
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
           (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
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
                 (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
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
                (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
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
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))))
         (stack
          ((CodeRef
            (FunctionType ()
             ((Prod
               ((Ref (Base MM) (Ser (Var 0)))
                (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
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
       (ValType
        ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
          (CodeRef
           (FunctionType ()
            ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
            ((Num (Int I32))))))))
       InferFx
       ((LocalSet 7) (LocalGet 7 Follow) Ungroup (LocalSet 9) (LocalSet 8)
        (LocalGet 9 Follow) (LocalGet 5 Follow) (Group 2) (LocalGet 8 Follow)
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
             (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
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
             (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
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
        ((Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
         (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
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
         (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
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
               (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
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
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32))))))
       (stack
        ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
          (CodeRef
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Var 0)))
               (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
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
        (BlockErr
         (error
          (UngroupNonProd
           (CodeRef
            (FunctionType ()
             ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
             ((Num (Int I32)))))))
         (instr Ungroup)
         (env
          ((local_offset 1) (kinds ((VALTYPE (Atom Ptr) NoCopy ExDrop)))
           (labels
            (((Num (Int I32)))
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
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))
             (FunctionType () ()
              ((Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
                 ExDrop)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))
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
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))
           (lfx (InferFx))))
         (state
          ((locals
            ((Plug
              (Prod ((Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32))))
             (Ref (Base MM) (Ser (Prod ())))
             (Plug (Prod ((Atom I32) (Atom I32) (Atom I32) (Atom I32))))
             (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32))))))
             (Plug (Prod ((Atom I32) (Atom I32) (Atom I32)))) (Plug (Prod ()))
             (Plug (Prod ((Atom I32) (Atom I32)))) (Num (Int I32))
             (Ref (Base MM)
              (Ser
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
                 ExDrop)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))
             (CodeRef
              (FunctionType ()
               ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
               ((Num (Int I32)))))
             (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
             (Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
             (Plug (Prod ((Atom I32))))
             (Plug (Prod ((Atom I32) (Atom I32) (Atom I32))))))
           (stack
            ((CodeRef
              (FunctionType ()
               ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
               ((Num (Int I32)))))))))))
       (instr
        (Unpack (ValType ((Num (Int I32)))) InferFx
         ((LocalSet 9) (LocalGet 9 Follow) Ungroup (LocalSet 11) (LocalSet 10)
          (LocalGet 11 Follow) (LocalGet 7 Follow) (Group 2) (LocalGet 10 Follow)
          CallIndirect (LocalGet 10 Move) Drop (LocalGet 11 Move) Drop
          (LocalGet 9 Move) Drop)))
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
          ((Plug (Prod ((Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32))))
           (Ref (Base MM) (Ser (Prod ())))
           (Plug (Prod ((Atom I32) (Atom I32) (Atom I32) (Atom I32))))
           (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32))))))
           (Plug (Prod ((Atom I32) (Atom I32) (Atom I32)))) (Plug (Prod ()))
           (Plug (Prod ((Atom I32) (Atom I32)))) (Num (Int I32))
           (Ref (Base MM)
            (Ser
             (Rec
              (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
               ExDrop)
              (Sum
               ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32) (Atom I32))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32) (Atom I32) (Atom I32))))))
         (stack
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32))))))))))))
     (instr
      (Case
       (ValType
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
         (Inject 0
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
         (Unpack (ValType ((Num (Int I32)))) InferFx
          ((LocalSet 9) (LocalGet 9 Follow) Ungroup (LocalSet 11) (LocalSet 10)
           (LocalGet 11 Follow) (LocalGet 7 Follow) (Group 2)
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
          (ValType
           ((Rec
             (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
              ExDrop)
             (Sum
              ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))
          InferFx
          ((LocalSet 12) (LocalGet 12 Follow) Ungroup (LocalSet 14) (LocalSet 13)
           (LocalGet 14 Follow) (LocalGet 3 Follow) (LocalGet 8 Follow)
           (Load (Path ()) Move) (LocalSet 15) Drop (LocalGet 15 Move) (Group 2)
           (Group 2) (LocalGet 13 Follow) CallIndirect (LocalGet 13 Move) Drop
           (LocalGet 14 Move) Drop (LocalGet 12 Move) Drop))
         (New MM) (Group 2)
         (Inject 1
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
        ((Plug (Prod ((Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32))))
         (Ref (Base MM) (Ser (Prod ())))
         (Plug (Prod ((Atom I32) (Atom I32) (Atom I32) (Atom I32))))
         (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
          (CodeRef
           (FunctionType ()
            ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
            ((Num (Int I32))))))
         (Plug (Prod ((Atom I32) (Atom I32) (Atom I32)))) (Plug (Prod ()))
         (Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32) (Atom I32) (Atom I32))))))
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
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
    |}
    -----------peano-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT
              [ (ProdT
                (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                  NoCopy ExDrop)
                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                  (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                  (ProdT (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                    [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
              [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]);
          mf_locals :=
            [ (AtomR PtrR);
              (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]);
              (SumR [ (ProdR []); (AtomR PtrR)]);
              (SumR [ (ProdR []); (AtomR PtrR)]);
              (ProdR []);
              (AtomR PtrR);
              (ProdR [ (AtomR I32R); (AtomR PtrR)]);
              (AtomR I32R);
              (AtomR PtrR);
              (SumR [ (ProdR []); (AtomR PtrR)])];
          mf_body :=
            [ (ILocalGet
              (InstrT []
                [ (ProdT
                  (VALTYPE (ProdR [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                    NoCopy ExDrop)
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                    (ProdT
                      (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                      [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                        (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])])
              0);
              (IUngroup
                (InstrT
                  [ (ProdT
                    (VALTYPE
                      (ProdR [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                      NoCopy ExDrop)
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                      (ProdT
                        (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                        [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                          (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                    (ProdT
                      (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                      [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                        (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]));
              (ILocalSet
                (InstrT
                  [ (ProdT (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                    [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                  [])
                2);
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                  [])
                1);
              (ILocalGet
                (InstrT []
                  [ (ProdT (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                    [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])
                2);
              (IUngroup
                (InstrT
                  [ (ProdT (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                    [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                    (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
              (ILocalSet
                (InstrT
                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]
                  [])
                4);
              (ILocalSet
                (InstrT
                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]
                  [])
                3);
              (ILocalGet
                (InstrT []
                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])
                3);
              (IUnfold
                (InstrT
                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]
                  [ (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                          (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))])]));
              (ICase
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
                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])
                (PlugT
                  (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R); (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                  (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R); (AtomR I32R); (AtomR I32R)]))
                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                  (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                  (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R); (AtomR I32R)]))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                (PlugT (VALTYPE (ProdR []) ImCopy ImDrop) (ProdR []))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                [ [ (ILocalSet (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])] []) 5);
                  (ILocalGet
                    (InstrT []
                      [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])
                    4);
                  (ILocalGet (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]) 5);
                  (IDrop (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])] []))];
                  [ (ILocalSet
                    (InstrT
                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                          (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))]
                      [])
                    6);
                    (ICodeRef
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT
                              (VALTYPE
                                (ProdR
                                  [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
                                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                                (ProdT
                                  (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy
                                    ExDrop)
                                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                    (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                            (BaseM MemMM)
                                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))])
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
                            [ (ProdT
                              (VALTYPE
                                (ProdR
                                  [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
                                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                                (ProdT
                                  (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy
                                    ExDrop)
                                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                    (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                            (BaseM MemMM)
                                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT
                                (VALTYPE
                                  (ProdR
                                    [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                  NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                                  (ProdT
                                    (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])
                                      NoCopy ExDrop)
                                    [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                            (BaseM MemMM)
                                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                              (BaseM MemMM)
                                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                              [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]));
                    (IPack
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT
                                (VALTYPE
                                  (ProdR
                                    [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                  NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                                  (ProdT
                                    (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])
                                      NoCopy ExDrop)
                                    [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                            (BaseM MemMM)
                                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                              (BaseM MemMM)
                                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                              [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]
                        [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          (VALTYPE (ProdR []) ImCopy ImDrop)
                          (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT
                                  (VALTYPE
                                    (ProdR
                                      [ (AtomR PtrR);
                                        (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                    NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (ProdT
                                      (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])
                                        NoCopy ExDrop)
                                      [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                              (BaseM MemMM)
                                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                        (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                                (BaseM MemMM)
                                                (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                                [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]));
                    (IUnpack
                      (InstrT
                        [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          (VALTYPE (ProdR []) ImCopy ImDrop)
                          (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT
                                  (VALTYPE
                                    (ProdR
                                      [ (AtomR PtrR);
                                        (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                    NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (ProdT
                                      (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])
                                        NoCopy ExDrop)
                                      [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                              (BaseM MemMM)
                                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                        (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                                (BaseM MemMM)
                                                (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                                [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]
                        [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])
                      (PlugT
                        (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R); (AtomR I32R); (AtomR I32R)]) ImCopy
                          ImDrop)
                        (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R); (AtomR I32R); (AtomR I32R)]))
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                        (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R); (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                        (ProdR [ (AtomR I32R); (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                        (ProdR [ (AtomR I32R); (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR []) ImCopy ImDrop) (ProdR []))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                        (ProdR [ (AtomR I32R); (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                        (ProdR [ (AtomR I32R); (AtomR I32R)]))
                      [ (ILocalSet
                        (InstrT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT
                                  (VALTYPE
                                    (ProdR
                                      [ (AtomR PtrR);
                                        (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                    NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (ProdT
                                      (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])
                                        NoCopy ExDrop)
                                      [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                              (BaseM MemMM)
                                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                        (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                                (BaseM MemMM)
                                                (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                                [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                          [])
                        7);
                        (ILocalGet
                          (InstrT []
                            [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (ProdT
                                    (VALTYPE
                                      (ProdR
                                        [ (AtomR PtrR);
                                          (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                      NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                      (ProdT
                                        (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])
                                          NoCopy ExDrop)
                                        [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                                (BaseM MemMM)
                                                (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                          (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                                  (BaseM MemMM)
                                                  (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])])
                          7);
                        (IUngroup
                          (InstrT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (ProdT
                                    (VALTYPE
                                      (ProdR
                                        [ (AtomR PtrR);
                                          (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                      NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                      (ProdT
                                        (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])
                                          NoCopy ExDrop)
                                        [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                                (BaseM MemMM)
                                                (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                          (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                                  (BaseM MemMM)
                                                  (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT
                                  (VALTYPE
                                    (ProdR
                                      [ (AtomR PtrR);
                                        (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                    NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (ProdT
                                      (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])
                                        NoCopy ExDrop)
                                      [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                              (BaseM MemMM)
                                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                        (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                                (BaseM MemMM)
                                                (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                                [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]));
                        (ILocalSet
                          (InstrT
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]
                            [])
                          9);
                        (ILocalSet
                          (InstrT
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT
                                  (VALTYPE
                                    (ProdR
                                      [ (AtomR PtrR);
                                        (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                    NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (ProdT
                                      (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])
                                        NoCopy ExDrop)
                                      [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                              (BaseM MemMM)
                                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                        (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                                (BaseM MemMM)
                                                (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                                [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))]
                            [])
                          8);
                        (ILocalGet
                          (InstrT []
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                          9);
                        (ILocalGet
                          (InstrT []
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                                (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))])
                          6);
                        (ILoad
                          (InstrT
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                                (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))]
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SpanT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ImDrop)
                                (RepS (SumR [ (ProdR []); (AtomR PtrR)]))));
                              (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])
                          [] Move);
                        (ILocalSet
                          (InstrT
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]
                            [])
                          10);
                        (IDrop
                          (InstrT
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SpanT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ImDrop)
                                (RepS (SumR [ (ProdR []); (AtomR PtrR)]))))]
                            []));
                        (ILocalGet
                          (InstrT []
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])
                          10);
                        (ILocalGet
                          (InstrT []
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])
                          4);
                        (IGroup
                          (InstrT
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                              (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]
                            [ (ProdT
                              (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy
                                ExDrop)
                              [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]));
                        (IGroup
                          (InstrT
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                              (ProdT
                                (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy
                                  ExDrop)
                                [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                  (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                            [ (ProdT
                              (VALTYPE
                                (ProdR
                                  [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT
                                  (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy
                                    ExDrop)
                                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                    (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                            (BaseM MemMM)
                                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]));
                        (ILocalGet
                          (InstrT []
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT
                                  (VALTYPE
                                    (ProdR
                                      [ (AtomR PtrR);
                                        (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                    NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (ProdT
                                      (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])
                                        NoCopy ExDrop)
                                      [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                              (BaseM MemMM)
                                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                        (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                                (BaseM MemMM)
                                                (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                                [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))])
                          8);
                        (ICallIndirect
                          (InstrT
                            [ (ProdT
                              (VALTYPE
                                (ProdR
                                  [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT
                                  (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy
                                    ExDrop)
                                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                    (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                            (BaseM MemMM)
                                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]);
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (ProdT
                                    (VALTYPE
                                      (ProdR
                                        [ (AtomR PtrR);
                                          (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                      NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                      (ProdT
                                        (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])
                                          NoCopy ExDrop)
                                        [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                                (BaseM MemMM)
                                                (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                          (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                                  (BaseM MemMM)
                                                  (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))]
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                        (ILocalGet
                          (InstrT []
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT
                                  (VALTYPE
                                    (ProdR
                                      [ (AtomR PtrR);
                                        (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                    NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (ProdT
                                      (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])
                                        NoCopy ExDrop)
                                      [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                              (BaseM MemMM)
                                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                        (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                                (BaseM MemMM)
                                                (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                                [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))])
                          8);
                        (IDrop
                          (InstrT
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT
                                  (VALTYPE
                                    (ProdR
                                      [ (AtomR PtrR);
                                        (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                    NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (ProdT
                                      (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])
                                        NoCopy ExDrop)
                                      [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                              (BaseM MemMM)
                                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                        (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                                (BaseM MemMM)
                                                (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                                [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))]
                            []));
                        (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))])
                          9);
                        (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                        (ILocalGet
                          (InstrT []
                            [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                              (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                          7);
                        (IDrop
                          (InstrT
                            [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                              (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                            []))]);
                    (INew
                      (InstrT
                        [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                            (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))]));
                    (IInject
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                            (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))]
                        [ (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                                (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))])])
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
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))])]
                        [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 6);
                    (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []))]]);
              (ILocalGet
                (InstrT []
                  [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                3);
              (IDrop
                (InstrT
                  [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                  []));
              (ILocalGet
                (InstrT []
                  [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                4);
              (IDrop
                (InstrT
                  [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                  []));
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
                  [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                    (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R); (AtomR I32R)]))])
                2);
              (IDrop
                (InstrT
                  [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                    (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R); (AtomR I32R)]))]
                  []))];
        |};
          {|
            mf_type :=
              (MonoFunT
                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]);
            mf_locals := [ (AtomR PtrR); (AtomR I32R); (ProdR [ (AtomR I32R); (AtomR PtrR)]); (AtomR I32R); (AtomR PtrR)];
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
                (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 2);
                (ILocalSet
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                    [])
                  1);
                (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
                (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0);
                (INum
                  (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                  (IIntTest I32T EqzI));
                (IIte
                  (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                    [ (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                            (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))])])
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
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
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))])])
                      0)]
                  [ (ICodeRef
                    (InstrT []
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                          [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))])
                    1);
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
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
                                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]));
                    (IPack
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
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
                                [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]));
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
                                [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]
                        [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                        (ProdR [ (AtomR I32R); (AtomR I32R)]))
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                        (ProdR [ (AtomR I32R); (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                      (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                      [ (ILocalSet
                        (InstrT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                                [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                          [])
                        3);
                        (ILocalGet
                          (InstrT []
                            [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])])
                          3);
                        (IUngroup
                          (InstrT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                                [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]));
                        (ILocalSet
                          (InstrT
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]
                            [])
                          5);
                        (ILocalSet
                          (InstrT
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                                [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))]
                            [])
                          4);
                        (ILocalGet
                          (InstrT []
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                          5);
                        (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
                        (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
                        (INum
                          (InstrT
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                          (IInt2 I32T SubI));
                        (IGroup
                          (InstrT
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]));
                        (ILocalGet
                          (InstrT []
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                                [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))])
                          4);
                        (ICallIndirect
                          (InstrT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))]
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                        (ILocalGet
                          (InstrT []
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                                [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))])
                          4);
                        (IDrop
                          (InstrT
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                                [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))]
                            []));
                        (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))])
                          5);
                        (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                        (ILocalGet
                          (InstrT []
                            [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                              (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                          3);
                        (IDrop
                          (InstrT
                            [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                              (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                            []))]);
                    (INew
                      (InstrT
                        [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                            (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))]));
                    (IInject
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                            (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))]
                        [ (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                                (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))])])
                      1)]);
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
                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                    (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
            mf_locals :=
              [ (AtomR PtrR);
                (SumR [ (ProdR []); (AtomR PtrR)]);
                (ProdR []);
                (AtomR PtrR);
                (ProdR [ (AtomR I32R); (AtomR PtrR)]);
                (AtomR I32R);
                (AtomR PtrR);
                (SumR [ (ProdR []); (AtomR PtrR)])];
            mf_body :=
              [ (ILocalGet
                (InstrT []
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])
                0);
                (IUngroup
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                        (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                (ILocalSet
                  (InstrT
                    [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]
                    [])
                  2);
                (ILocalSet
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                    [])
                  1);
                (ILocalGet
                  (InstrT []
                    [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])
                  2);
                (IUnfold
                  (InstrT
                    [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]
                    [ (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                            (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))])]));
                (ICase
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
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                    (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R)]))
                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR []) ImCopy ImDrop) (ProdR []))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  [ [ (ILocalSet (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])] []) 3);
                    (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0);
                    (ILocalGet (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]) 3);
                    (IDrop (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])] []))];
                    [ (ILocalSet
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                            (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))]
                        [])
                      4);
                      (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
                      (ICodeRef
                        (InstrT []
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                                  (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                        2);
                      (IGroup (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
                      (INew
                        (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]));
                      (IGroup
                        (InstrT
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM)
                                  (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                                  (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                          [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM)
                                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                                    (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                            (BaseM MemMM)
                                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
                                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]));
                      (IPack
                        (InstrT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM)
                                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                                    (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                            (BaseM MemMM)
                                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                                [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
                                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]
                          [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                            (VALTYPE (ProdR []) ImCopy ImDrop)
                            (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                              (BaseM MemMM)
                                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]));
                      (IUnpack
                        (InstrT
                          [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                            (VALTYPE (ProdR []) ImCopy ImDrop)
                            (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                              (BaseM MemMM)
                                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                        (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R)]))
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))
                        (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))
                        (PlugT (VALTYPE (ProdR []) ImCopy ImDrop) (ProdR []))
                        (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                        (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))
                        (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                        (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                        (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))
                        [ (ILocalSet
                          (InstrT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                              (BaseM MemMM)
                                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                            [])
                          5);
                          (ILocalGet
                            (InstrT []
                              [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                        (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                                (BaseM MemMM)
                                                (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])])
                            5);
                          (IUngroup
                            (InstrT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                        (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                                (BaseM MemMM)
                                                (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                              [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                              (BaseM MemMM)
                                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]));
                          (ILocalSet
                            (InstrT
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]
                              [])
                            7);
                          (ILocalSet
                            (InstrT
                              [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                              (BaseM MemMM)
                                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                              [])
                            6);
                          (ILocalGet
                            (InstrT []
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                            7);
                          (ILocalGet
                            (InstrT []
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
                                (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                                  (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))])
                            4);
                          (ILoad
                            (InstrT
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
                                (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop)
                                  (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))))]
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
                                (SpanT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ImDrop)
                                  (RepS (SumR [ (ProdR []); (AtomR PtrR)]))));
                                (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])
                            [] Move);
                          (ILocalSet
                            (InstrT
                              [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]
                              [])
                            8);
                          (IDrop
                            (InstrT
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM)
                                (SpanT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ImDrop)
                                  (RepS (SumR [ (ProdR []); (AtomR PtrR)]))))]
                              []));
                          (ILocalGet
                            (InstrT []
                              [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])
                            8);
                          (IGroup
                            (InstrT
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]));
                          (ILocalGet
                            (InstrT []
                              [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                              (BaseM MemMM)
                                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                            6);
                          (ICallIndirect
                            (InstrT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]);
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                        (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                                (BaseM MemMM)
                                                (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (ILocalGet
                            (InstrT []
                              [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                              (BaseM MemMM)
                                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                            6);
                          (IDrop
                            (InstrT
                              [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                              (BaseM MemMM)
                                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                              []));
                          (ILocalGet
                            (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 7);
                          (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                          (ILocalGet
                            (InstrT []
                              [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                                (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                            5);
                          (IDrop
                            (InstrT
                              [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                                (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                              []))]);
                      (INum
                        (InstrT
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                        (IInt2 I32T AddI));
                      (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 4);
                      (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []))]]);
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
                    [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                  2);
                (IDrop
                  (InstrT
                    [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                    []))];
          |};
          {|
            mf_type := (MonoFunT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
            mf_locals :=
              [ (ProdR [ (AtomR I32R); (AtomR PtrR)]);
                (AtomR I32R);
                (AtomR PtrR);
                (SumR [ (ProdR []); (AtomR PtrR)]);
                (ProdR [ (AtomR I32R); (AtomR PtrR)]);
                (AtomR I32R);
                (AtomR PtrR);
                (SumR [ (ProdR []); (AtomR PtrR)]);
                (ProdR [ (AtomR I32R); (AtomR PtrR)]);
                (AtomR I32R);
                (AtomR PtrR);
                (SumR [ (ProdR []); (AtomR PtrR)]);
                (ProdR [ (AtomR I32R); (AtomR PtrR)]);
                (AtomR I32R);
                (AtomR PtrR)];
            mf_body :=
              [ (ICodeRef
                (InstrT []
                  [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                    (MonoFunT
                      [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                          (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                      [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))])
                1);
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
                        [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                          [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
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
                          [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
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
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
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
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]
                    [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  [ (ILocalSet
                    (InstrT
                      [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                      [])
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
                              [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
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
                              [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]));
                    (ILocalSet
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]
                        [])
                      2);
                    (ILocalSet
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))]
                        [])
                      1);
                    (ILocalGet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                      2);
                    (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 6);
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
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))])
                      1);
                    (ICallIndirect
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))]
                        [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))])
                      1);
                    (IDrop
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))]
                        []));
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 2);
                    (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                    (ILocalGet
                      (InstrT []
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                      0);
                    (IDrop
                      (InstrT
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                        []))]);
                (ILocalSet
                  (InstrT
                    [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]
                    [])
                  3);
                (ICodeRef
                  (InstrT []
                    [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                      (MonoFunT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                        [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))])
                  1);
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
                        [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                              (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                          [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
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
                          [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
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
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
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
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]
                    [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  [ (ILocalSet
                    (InstrT
                      [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                      [])
                    4);
                    (ILocalGet
                      (InstrT []
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])])
                      4);
                    (IUngroup
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]));
                    (ILocalSet
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]
                        [])
                      6);
                    (ILocalSet
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))]
                        [])
                      5);
                    (ILocalGet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                      6);
                    (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 7);
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
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))])
                      5);
                    (ICallIndirect
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))]
                        [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))])
                      5);
                    (IDrop
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))]
                        []));
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 6);
                    (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                    (ILocalGet
                      (InstrT []
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                      4);
                    (IDrop
                      (InstrT
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                        []))]);
                (ILocalSet
                  (InstrT
                    [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]
                    [])
                  7);
                (ICodeRef
                  (InstrT []
                    [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                      (MonoFunT
                        [ (ProdT
                          (VALTYPE
                            (ProdR
                              [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                            NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                            (ProdT
                              (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy
                                ExDrop)
                              [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                        [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))])
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
                        [ (ProdT
                          (VALTYPE
                            (ProdR
                              [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                            NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                            (ProdT
                              (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy
                                ExDrop)
                              [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                        [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT
                            (VALTYPE
                              (ProdR
                                [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                              NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                              (ProdT
                                (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy
                                  ExDrop)
                                [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                  (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                          [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]));
                (IPack
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT
                            (VALTYPE
                              (ProdR
                                [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                              NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                              (ProdT
                                (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy
                                  ExDrop)
                                [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                  (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                          [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]
                    [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      (VALTYPE (ProdR []) ImCopy ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT
                              (VALTYPE
                                (ProdR
                                  [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT
                                  (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy
                                    ExDrop)
                                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                    (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                            (BaseM MemMM)
                                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]));
                (IUnpack
                  (InstrT
                    [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      (VALTYPE (ProdR []) ImCopy ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT
                              (VALTYPE
                                (ProdR
                                  [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT
                                  (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy
                                    ExDrop)
                                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                    (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                            (BaseM MemMM)
                                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]
                    [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  [ (ILocalSet
                    (InstrT
                      [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT
                              (VALTYPE
                                (ProdR
                                  [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT
                                  (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy
                                    ExDrop)
                                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                    (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                            (BaseM MemMM)
                                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                      [])
                    8);
                    (ILocalGet
                      (InstrT []
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT
                                (VALTYPE
                                  (ProdR
                                    [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                  NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (ProdT
                                    (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])
                                      NoCopy ExDrop)
                                    [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                            (BaseM MemMM)
                                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                              (BaseM MemMM)
                                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                              [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])])
                      8);
                    (IUngroup
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT
                                (VALTYPE
                                  (ProdR
                                    [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                  NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (ProdT
                                    (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])
                                      NoCopy ExDrop)
                                    [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                            (BaseM MemMM)
                                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                              (BaseM MemMM)
                                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                              [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT
                              (VALTYPE
                                (ProdR
                                  [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT
                                  (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy
                                    ExDrop)
                                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                    (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                            (BaseM MemMM)
                                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]));
                    (ILocalSet
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]
                        [])
                      10);
                    (ILocalSet
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT
                              (VALTYPE
                                (ProdR
                                  [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT
                                  (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy
                                    ExDrop)
                                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                    (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                            (BaseM MemMM)
                                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))]
                        [])
                      9);
                    (ILocalGet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                      10);
                    (ILocalGet
                      (InstrT []
                        [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])
                      3);
                    (ILocalGet
                      (InstrT []
                        [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])
                      7);
                    (IGroup
                      (InstrT
                        [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                          (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]
                        [ (ProdT
                          (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                          [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                            (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]));
                    (IGroup
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                          (ProdT
                            (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy
                              ExDrop)
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                              (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                        [ (ProdT
                          (VALTYPE
                            (ProdR
                              [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                            NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                            (ProdT
                              (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy
                                ExDrop)
                              [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT
                              (VALTYPE
                                (ProdR
                                  [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT
                                  (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy
                                    ExDrop)
                                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                    (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                            (BaseM MemMM)
                                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))])
                      9);
                    (ICallIndirect
                      (InstrT
                        [ (ProdT
                          (VALTYPE
                            (ProdR
                              [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                            NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                            (ProdT
                              (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy
                                ExDrop)
                              [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]);
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT
                                (VALTYPE
                                  (ProdR
                                    [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                  NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (ProdT
                                    (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])
                                      NoCopy ExDrop)
                                    [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                            (BaseM MemMM)
                                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                      (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                          [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                              (BaseM MemMM)
                                              (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                              [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))]
                        [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT
                              (VALTYPE
                                (ProdR
                                  [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT
                                  (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy
                                    ExDrop)
                                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                    (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                            (BaseM MemMM)
                                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))])
                      9);
                    (IDrop
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT
                              (VALTYPE
                                (ProdR
                                  [ (AtomR PtrR); (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])])])
                                NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (ProdT
                                  (VALTYPE (ProdR [ (SumR [ (ProdR []); (AtomR PtrR)]); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy
                                    ExDrop)
                                  [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]));
                                    (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                            (BaseM MemMM)
                                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])])]
                            [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]))]
                        []));
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 10);
                    (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                    (ILocalGet
                      (InstrT []
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                      8);
                    (IDrop
                      (InstrT
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                        []))]);
                (ILocalSet
                  (InstrT
                    [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                      (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]
                    [])
                  11);
                (ICodeRef
                  (InstrT []
                    [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                      (MonoFunT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                            (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                  2);
                (IGroup (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
                (INew
                  (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]));
                (IGroup
                  (InstrT
                    [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                      (MonoFunT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                            (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                              (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]));
                (IPack
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                            [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])));
                              (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                    (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                      (BaseM MemMM)
                                      (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))])]
                    [ (ExistsTypeT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                      (VALTYPE (ProdR []) ImCopy ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
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
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]))]
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  [ (ILocalSet
                    (InstrT
                      [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                      [])
                    12);
                    (ILocalGet
                      (InstrT []
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])])
                      12);
                    (IUngroup
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR PtrR)]) NoCopy ExDrop)
                          [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])]
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                          (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]));
                    (ILocalSet
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]
                        [])
                      14);
                    (ILocalSet
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        [])
                      13);
                    (ILocalGet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                      14);
                    (ILocalGet
                      (InstrT []
                        [ (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                          (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                              (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])
                      11);
                    (IGroup
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                          (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                            (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                            (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      13);
                    (ICallIndirect
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                            (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                              (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                    (BaseM MemMM) (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))]);
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                      [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                          (BaseM MemMM)
                                          (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))])
                      13);
                    (IDrop
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (SumR [ (ProdR []); (AtomR PtrR)])]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (RecT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                  (SumT (VALTYPE (SumR [ (ProdR []); (AtomR PtrR)]) NoCopy ExDrop)
                                    [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []);
                                      (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                        (BaseM MemMM)
                                        (SerT (MEMTYPE (RepS (SumR [ (ProdR []); (AtomR PtrR)])) ExDrop) (VarT 0)))]))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        []));
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 14);
                    (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                    (ILocalGet
                      (InstrT []
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                      12);
                    (IDrop
                      (InstrT
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                        []))]);
                (ILocalGet
                  (InstrT []
                    [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                  11);
                (IDrop
                  (InstrT
                    [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                    []));
                (ILocalGet
                  (InstrT []
                    [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                  7);
                (IDrop
                  (InstrT
                    [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                    []));
                (ILocalGet
                  (InstrT []
                    [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                  3);
                (IDrop
                  (InstrT
                    [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                    []))];
          |}];
      m_table := [ 0; 1; 2];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 3;
                   |}];
    |}
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
              (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 2);
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                  [])
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
                (ProdR [ (AtomR I32R); (AtomR PtrR)]);
                (AtomR I32R);
                (AtomR PtrR);
                (ProdR [ (AtomR I32R); (AtomR PtrR)]);
                (AtomR I32R);
                (AtomR PtrR)];
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
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                      [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                        (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                    [])
                  2);
                (ILocalSet
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                    [])
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
                (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 4);
                (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 3);
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
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                    (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R)]))
                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))
                  (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  [ (ILocalSet
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
                      [])
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
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]
                        [])
                      7);
                    (ILocalSet
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        [])
                      6);
                    (ILocalGet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                      7);
                    (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
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
                      6);
                    (ICallIndirect
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
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
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 7);
                    (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                    (ILocalGet
                      (InstrT []
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                      5);
                    (IDrop
                      (InstrT
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))]
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
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                    (ProdR [ (AtomR I32R); (AtomR I32R); (AtomR I32R)]))
                  (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))
                  (ProdT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                      (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  [ (ILocalSet
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
                      [])
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
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))]
                        [])
                      10);
                    (ILocalSet
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                              [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                            [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
                        [])
                      9);
                    (ILocalGet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)))])
                      10);
                    (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
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
                      9);
                    (ICallIndirect
                      (InstrT
                        [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                            (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) NoCopy ExDrop)
                                [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop)
                                  (BaseM MemMM) (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (VarT 0)));
                                  (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])]
                              [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]))]
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
                    (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 10);
                    (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                    (ILocalGet
                      (InstrT []
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                      8);
                    (IDrop
                      (InstrT
                        [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop)
                          (ProdR [ (AtomR I32R); (AtomR I32R)]))]
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
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) NoCopy ExDrop)
                      [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))));
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                            (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))))])]
                    [])
                  2);
                (ILocalSet
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                    [])
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
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))))]
                    [])
                  4);
                (ILocalSet
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]
                    [])
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
                (ILocalSet (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))] []) 5);
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
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) NoCopy ExDrop) (BaseM MemMM)
                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop) (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))))]
                    [])
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
                (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 3);
                (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
                (ILocalGet (InstrT [] [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))]) 4);
                (IDrop (InstrT [ (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))] []));
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
                    [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))])
                  2);
                (IDrop
                  (InstrT
                    [ (PlugT (VALTYPE (ProdR [ (AtomR I32R); (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R); (AtomR I32R)]))]
                    []))];
          |}];
      m_table := [ 0; 1; 2];
      m_exports := [ {|
                     me_name := "typle_add1"; me_desc := 1;
                   |}];
    |} |xxx}]
