open! Core
open! Stdlib.Format
open! Test_support
module AnnRichWasm = Richwasm_common.Annotated_syntax

include Test_runner.MultiOutputter.Make (struct
  let margin = 120
  let max_indent = margin

  open Test_utils
  open Richwasm_mini_ml

  type syntax = Syntax.Source.Module.t
  type text = string
  type res = AnnRichWasm.Module.t

  let elab x =
    x
    |> Richwasm_common.Elaborate.elab_module
    |> or_fail_pp Richwasm_common.Elaborate.Err.pp

  let syntax_pipeline x =
    x |> Convert.cc_module |> Codegen.compile_module |> elab

  let string_pipeline s = s |> Parse.from_string_exn |> syntax_pipeline
  let examples = Test_examples.Mini_ml.all
  let pp = AnnRichWasm.Module.pp_rocq
  let pp_raw = AnnRichWasm.Module.pp_sexp
end)

let%expect_test "examples" =
  output_examples ();
  [%expect {xxx|
    -----------one-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []))]
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []))]);
          mf_locals := [ (AtomR PtrR)];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------tuple-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []))]
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []))]);
          mf_locals := [ (AtomR PtrR)];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (IGroup
                (InstrT
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop));
                    (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop));
                    (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop));
                    (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR); (AtomR PtrR); (AtomR PtrR)]) ImCopy ImDrop)
                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop));
                      (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop));
                      (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop));
                      (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])]));
              (INew
                (InstrT
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR); (AtomR PtrR); (AtomR PtrR)]) ImCopy ImDrop)
                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop));
                      (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop));
                      (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop));
                      (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR PtrR); (AtomR PtrR); (AtomR PtrR)])) ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR); (AtomR PtrR); (AtomR PtrR)]) ImCopy ImDrop)
                        [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop));
                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop));
                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop));
                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------tuple_nested-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []))]
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []))]);
          mf_locals := [ (AtomR PtrR)];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 4);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (IGroup
                (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ImCopy ImDrop)
                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])]));
              (INew
                (InstrT
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ImCopy ImDrop)
                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR PtrR)])) ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ImCopy ImDrop)
                        [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]));
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (IGroup
                (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ImCopy ImDrop)
                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])]));
              (INew
                (InstrT
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ImCopy ImDrop)
                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR PtrR)])) ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ImCopy ImDrop)
                        [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]));
              (IGroup
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR PtrR)])) ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ImCopy ImDrop)
                        [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR PtrR)])) ImDrop)
                        (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ImCopy ImDrop)
                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ExCopy ExDrop)
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR PtrR)])) ImDrop)
                        (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ImCopy ImDrop)
                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])));
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR PtrR)])) ImDrop)
                          (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ImCopy ImDrop)
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])]));
              (INew
                (InstrT
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ExCopy ExDrop)
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR PtrR)])) ImDrop)
                        (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ImCopy ImDrop)
                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])));
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR PtrR)])) ImDrop)
                          (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ImCopy ImDrop)
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR PtrR)])) ExDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ExCopy ExDrop)
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR PtrR)])) ImDrop)
                            (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ImCopy ImDrop)
                              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])));
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR PtrR)])) ImDrop)
                              (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ImCopy ImDrop)
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------tuple_project-----------
    FAILURE (CannotResolvePath ExpectedStruct (Path (1)) (Prod (I31 I31)))
    -----------sum_unit-----------
    FAILURE (CannotMeet "expected memtype" (VALTYPE (AtomR PtrR) ExCopy ExDrop))
    -----------sum_option-----------
    FAILURE (CannotMeet "expected memtype" (VALTYPE (AtomR PtrR) ExCopy ExDrop))
    -----------add-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []))]
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []))]);
          mf_locals := [ (AtomR PtrR)];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (IUntag
                (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (IUntag
                (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
              (INum
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (IInt2 I32T AddI));
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------sub-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []))]
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []))]);
          mf_locals := [ (AtomR PtrR)];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (IUntag
                (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (IUntag
                (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
              (INum
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (IInt2 I32T SubI));
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------mul-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []))]
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []))]);
          mf_locals := [ (AtomR PtrR)];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (IUntag
                (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (IUntag
                (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
              (INum
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (IInt2 I32T MulI));
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------div-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []))]
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []))]);
          mf_locals := [ (AtomR PtrR)];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (IUntag
                (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (IUntag
                (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
              (INum
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (IInt2 I32T (DivI SignS)));
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------math-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []))]
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []))]);
          mf_locals := [ (AtomR PtrR)];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (IUntag
                (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 6);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (IUntag
                (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
              (INum
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (IInt2 I32T MulI));
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (IUntag
                (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (IUntag
                (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
              (INum
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (IInt2 I32T (DivI SignS)));
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------basic_let-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []))]
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []))]);
          mf_locals := [ (AtomR PtrR); (AtomR PtrR)];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 10);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (ILocalSet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 1);
              (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 1);
              (ICopy
                (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (ILocalSet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 1);
              (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 1);
              (IDrop (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []))];
        |}];
      m_table := [];
      m_exports := [ 0];
    |}
    -----------return_one-----------
    FAILURE (CannotMeet "expected valtype" (MEMTYPE (RepS (AtomR PtrR)) ExDrop))
    -----------add_one-----------
    FAILURE (CannotMeet "expected valtype" (MEMTYPE (RepS (AtomR PtrR)) ExDrop))
    -----------id-----------
    FAILURE (CannotMeet "expected valtype" (MEMTYPE (RepS (AtomR PtrR)) ExDrop))
    -----------apply_id-----------
    FAILURE (CannotMeet "expected valtype" (MEMTYPE (RepS (AtomR PtrR)) ExDrop))
    -----------opt_case-----------
    FAILURE (CannotMeet "expected memtype" (VALTYPE (AtomR PtrR) ExCopy ExDrop))
    -----------poly_len-----------
    FAILURE (CannotMeet "expected valtype" (MEMTYPE (RepS (AtomR PtrR)) ExDrop))
    -----------mini_zip-----------
    FAILURE (CannotMeet "expected valtype" (MEMTYPE (RepS (AtomR PtrR)) ExDrop))
    -----------closure_simpl-----------
    FAILURE (CannotMeet "expected valtype" (MEMTYPE (RepS (AtomR PtrR)) ImDrop))
    -----------closure_complex-----------
    FAILURE (CannotMeet "expected valtype" (MEMTYPE (RepS (AtomR PtrR)) ExDrop)) |xxx}]
