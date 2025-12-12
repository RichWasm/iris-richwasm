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
  [%expect
    {xxx|
    -----------one-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))]
              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]);
          mf_locals := [ (AtomR PtrR)];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))];
        |}];
      m_table := [ 0];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
    |}
    -----------tuple-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))]
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (ProdT
                  (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR)); (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                    ImDrop)
                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]);
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
                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]));
              (ICast
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR PtrR); (AtomR PtrR); (AtomR PtrR)])) ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR); (AtomR PtrR); (AtomR PtrR)]) ImCopy ImDrop)
                        [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop));
                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop));
                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop));
                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT
                      (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR)); (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                        ImDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]))];
        |}];
      m_table := [ 0];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
    |}
    -----------tuple_nested-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))]
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ImDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ImDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])))]))]);
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
              (ICast
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR PtrR)])) ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ImCopy ImDrop)
                        [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ImDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]));
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
              (ICast
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR PtrR)])) ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ImCopy ImDrop)
                        [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ImDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]));
              (IGroup
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ImDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ImDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ExCopy ExDrop)
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ImDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ImDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))])]));
              (INew
                (InstrT
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ExCopy ExDrop)
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ImDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ImDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))])]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR PtrR)])) ExDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ExCopy ExDrop)
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ImDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))])))]));
              (ICast
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR PtrR)])) ExDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ExCopy ExDrop)
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ImDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))])))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ImDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])))]))]))];
        |}];
      m_table := [ 0];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
    |}
    -----------tuple_project-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))]
              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]);
          mf_locals := [ (AtomR PtrR); (AtomR PtrR)];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 7);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 42);
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
              (ICast
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR PtrR)])) ImDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ImCopy ImDrop)
                        [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ImDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]));
              (ILoad
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ImDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ImDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                    (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])
                [ 1] Copy);
              (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 1);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ImDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  []));
              (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 1)];
        |}];
      m_table := [ 0];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
    |}
    -----------sum_unit-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))]
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR))]) ExDrop)
                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]);
          mf_locals := [ (AtomR PtrR)];
          mf_body :=
            [ (IGroup (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
              (INew
                (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]));
              (ICast
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))]));
              (IInjectNew
                (InstrT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))])
                0)];
        |}];
      m_table := [ 0];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
    |}
    -----------sum_option-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))]
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]);
          mf_locals := [ (AtomR PtrR)];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 15);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (IInjectNew
                (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (VariantT (MEMTYPE (SumS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))])
                1)];
        |}];
      m_table := [ 0];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
    |}
    -----------basic_if-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))]
              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]);
          mf_locals := [ (AtomR PtrR)];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (IUntag
                (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 0);
              (INum
                (InstrT
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
                    (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
                (IIntRel I32T EqI));
              (IIte
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])
                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
                  (ITag
                    (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]
                [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
                  (ITag
                    (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])];
        |}];
      m_table := [ 0];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
    |}
    -----------add-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))]
              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]);
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
      m_table := [ 0];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
    |}
    -----------sub-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))]
              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]);
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
      m_table := [ 0];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
    |}
    -----------mul-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))]
              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]);
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
      m_table := [ 0];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
    |}
    -----------div-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))]
              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]);
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
      m_table := [ 0];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
    |}
    -----------math-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))]
              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]);
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
      m_table := [ 0];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
    |}
    -----------basic_let-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))]
              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]);
          mf_locals := [ (AtomR PtrR); (AtomR PtrR)];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 10);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 1);
              (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 1);
              (ICopy
                (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 1);
              (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 1);
              (IDrop (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []))];
        |}];
      m_table := [ 0];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
    |}
    -----------return_one-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]);
          mf_locals := [ (AtomR PtrR); (AtomR PtrR); (AtomR PtrR); (AtomR PtrR); (AtomR PtrR)];
          mf_body :=
            [ (ILocalGet
              (InstrT []
                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))])
              0);
              (ICopy
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]));
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                  [])
                0);
              (ILoad
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))])
                [ 0] Copy);
              (ILocalSet
                (InstrT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))] [])
                1);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                  []));
              (ILocalGet
                (InstrT [] [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))])
                1);
              (ILocalSet
                (InstrT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))] [])
                2);
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))])
                0);
              (ICopy
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]));
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                  [])
                0);
              (ILoad
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))])
                [ 1] Copy);
              (ILocalSet
                (InstrT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))] [])
                3);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                  []));
              (ILocalGet
                (InstrT [] [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))])
                3);
              (ILocalSet
                (InstrT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))] [])
                4);
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (ILocalGet
                (InstrT [] [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))])
                4);
              (IDrop
                (InstrT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))] []));
              (ILocalGet
                (InstrT [] [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))])
                2);
              (IDrop
                (InstrT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))] []))];
        |};
          {|
            mf_type :=
              (MonoFunT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))]
                [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (BaseM MemGC)
                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]);
            mf_locals := [ (AtomR PtrR)];
            mf_body :=
              [ (IGroup (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
                (INew
                  (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]));
                (ICast
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))]));
                (ICodeRef
                  (InstrT []
                    [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                      (MonoFunT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                              (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                        [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])
                  0);
                (IGroup
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []));
                      (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) ExCopy ExDrop)
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []));
                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])]));
                (INew
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) ExCopy ExDrop)
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []));
                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])]
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR I32R)])) ExDrop)
                        (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) ExCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []));
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                          (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])))]));
                (ICast
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR I32R)])) ExDrop)
                        (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) ExCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []));
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                          (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])))]
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                          (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]));
                (IPack
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                          (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                            (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]))];
          |}];
      m_table := [ 0; 1];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 1;
                   |}];
    |}
    -----------add_one-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]);
          mf_locals := [ (AtomR PtrR); (AtomR PtrR); (AtomR PtrR)];
          mf_body :=
            [ (ILocalGet
              (InstrT []
                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))])
              0);
              (ICopy
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]));
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [])
                0);
              (ILoad
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                    (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])
                [ 1] Copy);
              (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 1);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  []));
              (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 1);
              (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 2);
              (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 2);
              (ICopy
                (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 2);
              (IUntag
                (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
              (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
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
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 2);
              (IDrop (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []))];
        |}];
      m_table := [ 0];
      m_exports := [ {|
                     me_name := "add1"; me_desc := 0;
                   |}];
    |}
    -----------id-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (ForallTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
              (MonoFunT
                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))]))]
                [ (VarT 0)]));
          mf_locals := [ (AtomR PtrR); (AtomR PtrR); (AtomR PtrR)];
          mf_body :=
            [ (ILocalGet
              (InstrT []
                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))]))])
              0);
              (ICopy
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))]));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))]))]));
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))]))]
                  [])
                0);
              (ILoad
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))]));
                    (VarT 0)])
                [ 1] Copy);
              (ILocalSet (InstrT [ (VarT 0)] []) 1);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))]))]
                  []));
              (ILocalGet (InstrT [] [ (VarT 0)]) 1);
              (ILocalSet (InstrT [ (VarT 0)] []) 2);
              (ILocalGet (InstrT [] [ (VarT 0)]) 2);
              (ICopy (InstrT [ (VarT 0)] [ (VarT 0); (VarT 0)]));
              (ILocalSet (InstrT [ (VarT 0)] []) 2);
              (ILocalGet (InstrT [] [ (VarT 0)]) 2);
              (IDrop (InstrT [ (VarT 0)] []))];
        |}];
      m_table := [ 0];
      m_exports := [ {|
                     me_name := "id"; me_desc := 0;
                   |}];
    |}
    -----------apply_id-----------
    FAILURE (InstrErr
     (error
      (PackMismatch
       (Ref (Base GC)
        (Struct
         ((Ser (Ref (Base GC) (Struct ())))
          (Ser
           (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
            (Ref (Base GC)
             (Struct
              ((Ser (Var 0))
               (Ser
                (CodeRef
                 (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
                  ((Ref (Base GC) (Struct ((Ser (Var 1)) (Ser (Var 0))))))
                  ((Var 0)))))))))))))
       (Ref (Base GC)
        (Struct
         ((Ser (Ref (Base GC) (Struct ())))
          (Ser
           (CodeRef
            (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
             ((Ref (Base GC)
               (Struct ((Ser (Ref (Base GC) (Struct ()))) (Ser (Var 0))))))
             ((Var 0))))))))))
     (instr
      (Pack (Type (Ref (Base GC) (Struct ())))
       (Ref (Base GC)
        (Struct
         ((Ser (Var 0))
          (Ser
           (CodeRef
            (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
             ((Ref (Base GC) (Struct ((Ser (Var 1)) (Ser (Var 0)))))) ((Var 0))))))))))
     (env
      ((local_offset 1) (kinds ()) (labels ()) (return (I31))
       (functions
        ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
          ((Ref (Base GC)
            (Struct ((Ser (Ref (Base GC) (Struct ()))) (Ser (Var 0))))))
          ((Var 0)))
         (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
       (table
        ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
          ((Ref (Base GC)
            (Struct ((Ser (Ref (Base GC) (Struct ()))) (Ser (Var 0))))))
          ((Var 0)))
         (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
       (lfx ())))
     (state
      ((locals
        ((Ref (Base GC) (Struct ())) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32))))))
       (stack
        ((Ref (Base GC)
          (Struct
           ((Ser (Ref (Base GC) (Struct ())))
            (Ser
             (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
              (Ref (Base GC)
               (Struct
                ((Ser (Var 0))
                 (Ser
                  (CodeRef
                   (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
                    ((Ref (Base GC) (Struct ((Ser (Var 1)) (Ser (Var 0))))))
                    ((Var 0))))))))))))))))))
    -----------opt_case-----------
    FAILURE (InstrErr
     (error
      (BlockErr (error (PopEmptyStack LocalSet)) (instr (LocalSet 3))
       (env
        ((local_offset 1) (kinds ()) (labels ((I31))) (return (I31))
         (functions ((FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
         (table ((FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
         (lfx (InferFx))))
       (state
        ((locals
          ((Ref (Base GC) (Struct ()))
           (Ref (Base GC)
            (Variant ((Ser (Ref (Base GC) (Struct ()))) (Ser I31))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))))
         (stack ())))))
     (instr
      (CaseLoad (ArrowType 0 (I31)) Copy InferFx
       (((LocalSet 3) (NumConst (Int I32) 0) Tag (LocalGet 3 Move) Drop)
        ((LocalSet 2) (LocalGet 2 Move) Copy (LocalSet 2) (LocalGet 2 Move) Drop))))
     (env
      ((local_offset 1) (kinds ()) (labels ()) (return (I31))
       (functions ((FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
       (table ((FunctionType () ((Ref (Base GC) (Struct ()))) (I31)))) (lfx ())))
     (state
      ((locals
        ((Ref (Base GC) (Struct ()))
         (Ref (Base GC) (Variant ((Ser (Ref (Base GC) (Struct ()))) (Ser I31))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))))
       (stack
        ((Ref (Base GC) (Variant ((Ser (Ref (Base GC) (Struct ()))) (Ser I31)))))))))
    -----------poly_len-----------
    FAILURE (InstrErr
     (error
      (BlockErr (error (PopEmptyStack LocalSet)) (instr (LocalSet 9))
       (env
        ((local_offset 1) (kinds ((VALTYPE (Atom Ptr) ExCopy ExDrop)))
         (labels ((I31))) (return (I31))
         (functions
          ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
            ((Ref (Base GC)
              (Struct
               ((Ser (Ref (Base GC) (Struct ())))
                (Ser
                 (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                  (Ref (Base GC)
                   (Variant
                    ((Ser (Ref (Base GC) (Struct ())))
                     (Ser
                      (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
            (I31))
           (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
         (table
          ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
            ((Ref (Base GC)
              (Struct
               ((Ser (Ref (Base GC) (Struct ())))
                (Ser
                 (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                  (Ref (Base GC)
                   (Variant
                    ((Ser (Ref (Base GC) (Struct ())))
                     (Ser
                      (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
            (I31))
           (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
         (lfx (InferFx))))
       (state
        ((locals
          ((Ref (Base GC)
            (Struct
             ((Ser (Ref (Base GC) (Struct ())))
              (Ser
               (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                (Ref (Base GC)
                 (Variant
                  ((Ser (Ref (Base GC) (Struct ())))
                   (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))))))
           (Plug (Prod ((Atom I32))))
           (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
            (Ref (Base GC)
             (Variant
              ((Ser (Ref (Base GC) (Struct ())))
               (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32))))))
         (stack ())))))
     (instr
      (CaseLoad (ArrowType 0 (I31)) Copy InferFx
       (((LocalSet 9) (NumConst (Int I32) 0) Tag (LocalGet 9 Move) Drop)
        ((LocalSet 3) (NumConst (Int I32) 1) Tag Untag (Group 0) (New GC)
         (Cast (Ref (Base GC) (Struct ()))) (CodeRef 0) (Group 2) (New GC)
         (Cast
          (Ref (Base GC)
           (Struct
            ((Ser (Ref (Base GC) (Struct ())))
             (Ser
              (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
               (Ref (Base GC)
                (Struct
                 ((Ser (Var 0))
                  (Ser
                   (CodeRef
                    (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
                     ((Ref (Base GC)
                       (Struct
                        ((Ser (Var 1))
                         (Ser
                          (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                           (Ref (Base GC)
                            (Variant
                             ((Ser (Ref (Base GC) (Struct ())))
                              (Ser
                               (Ref (Base GC)
                                (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
                     (I31)))))))))))))
         (Pack (Type (Ref (Base GC) (Struct ())))
          (Ref (Base GC)
           (Struct
            ((Ser (Var 0))
             (Ser
              (CodeRef
               (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
                ((Ref (Base GC)
                  (Struct
                   ((Ser (Var 1))
                    (Ser
                     (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                      (Ref (Base GC)
                       (Variant
                        ((Ser (Ref (Base GC) (Struct ())))
                         (Ser
                          (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
                (I31))))))))
         (Unpack (ArrowType 1 (I31)) InferFx
          ((LocalSet 4) (LocalGet 4 Move) Copy (LocalSet 4)
           (Load (Path (0)) Follow) (LocalSet 5) Drop (LocalGet 5 Move)
           (LocalSet 6) (LocalGet 4 Move) Copy (LocalSet 4)
           (Load (Path (1)) Follow) (LocalSet 7) Drop (LocalGet 7 Move)
           (LocalSet 8) (LocalGet 3 Move) Copy (LocalSet 3)
           (Fold
            (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
             (Ref (Base GC)
              (Variant
               ((Ser (Ref (Base GC) (Struct ())))
                (Ser (Ref (Base GC) (Variant ((Ser (Var 2)) (Ser (Var 0)))))))))))
           (LocalGet 8 Move) Copy (LocalSet 8) (Inst (Type (Var 1))) CallIndirect
           (LocalGet 8 Move) Drop (LocalGet 6 Move) Drop (LocalGet 4 Move) Drop))
         Untag (Num (Int2 I32 Add)) Tag (LocalGet 3 Move) Drop))))
     (env
      ((local_offset 1) (kinds ((VALTYPE (Atom Ptr) ExCopy ExDrop))) (labels ())
       (return (I31))
       (functions
        ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
          ((Ref (Base GC)
            (Struct
             ((Ser (Ref (Base GC) (Struct ())))
              (Ser
               (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                (Ref (Base GC)
                 (Variant
                  ((Ser (Ref (Base GC) (Struct ())))
                   (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
          (I31))
         (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
       (table
        ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
          ((Ref (Base GC)
            (Struct
             ((Ser (Ref (Base GC) (Struct ())))
              (Ser
               (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                (Ref (Base GC)
                 (Variant
                  ((Ser (Ref (Base GC) (Struct ())))
                   (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
          (I31))
         (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
       (lfx ())))
     (state
      ((locals
        ((Ref (Base GC)
          (Struct
           ((Ser (Ref (Base GC) (Struct ())))
            (Ser
             (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
              (Ref (Base GC)
               (Variant
                ((Ser (Ref (Base GC) (Struct ())))
                 (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))))))
         (Plug (Prod ((Atom I32))))
         (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
          (Ref (Base GC)
           (Variant
            ((Ser (Ref (Base GC) (Struct ())))
             (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32))))))
       (stack
        ((Ref (Base GC)
          (Variant
           ((Ser (Ref (Base GC) (Struct ())))
            (Ser
             (Ref (Base GC)
              (Variant
               ((Ser (Var 0))
                (Ser
                 (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                  (Ref (Base GC)
                   (Variant
                    ((Ser (Ref (Base GC) (Struct ())))
                     (Ser
                      (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))))))))))
    -----------mini_zip-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (ForallTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
              (ForallTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                (MonoFunT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC) (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC) (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))])))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))]))))])));
          mf_locals := [ (AtomR PtrR); (AtomR PtrR); (AtomR PtrR); (AtomR PtrR); (AtomR PtrR); (AtomR PtrR); (AtomR PtrR)];
          mf_body :=
            [ (ILocalGet
              (InstrT []
                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                              (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (BaseM MemGC) (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC) (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))])))]))])
              0);
              (ICopy
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC) (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC) (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))])))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC) (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC) (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))])))]));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC) (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC) (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))])))]))]));
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC) (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC) (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))])))]))]
                  [])
                0);
              (ILoad
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC) (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC) (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))])))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC) (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC) (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))])))]));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))]))])
                [ 1] Copy);
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))]))]
                  [])
                1);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC) (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC) (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))])))]))]
                  []));
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))]))])
                1);
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))]))]
                  [])
                2);
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))]))])
                2);
              (ICopy
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))]));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))]))]));
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))]))]
                  [])
                2);
              (ILoad
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))]));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1)))])
                [ 1] Copy);
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1)))]
                  [])
                3);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))]))]
                  []));
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1)))])
                3);
              (ILoad
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1)))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1)));
                    (VarT 1)])
                [] Copy);
              (ILocalSet (InstrT [ (VarT 1)] []) 4);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1)))]
                  []));
              (ILocalGet (InstrT [] [ (VarT 1)]) 4);
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))]))])
                2);
              (ICopy
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))]));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))]))]));
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))]))]
                  [])
                2);
              (ILoad
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))]));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0)))])
                [ 0] Copy);
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0)))]
                  [])
                5);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))]))]
                  []));
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0)))])
                5);
              (ILoad
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0)))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0)));
                    (VarT 0)])
                [] Copy);
              (ILocalSet (InstrT [ (VarT 0)] []) 6);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0)))]
                  []));
              (ILocalGet (InstrT [] [ (VarT 0)]) 6);
              (IGroup
                (InstrT [ (VarT 1); (VarT 0)]
                  [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ExCopy ExDrop) [ (VarT 1); (VarT 0)])]));
              (INew
                (InstrT [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ExCopy ExDrop) [ (VarT 1); (VarT 0)])]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR PtrR)])) ExDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ExCopy ExDrop) [ (VarT 1); (VarT 0)])))]));
              (ICast
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR PtrR)])) ExDrop)
                      (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ExCopy ExDrop) [ (VarT 1); (VarT 0)])))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))]))]));
              (INew
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1));
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))]))))]));
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))]))])
                2);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 1))))]))]
                  []))];
        |}];
      m_table := [ 0];
      m_exports := [ {|
                     me_name := "mini_zip"; me_desc := 0;
                   |}];
    |}
    -----------closure_simpl-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]);
          mf_locals := [ (AtomR PtrR); (AtomR PtrR); (AtomR PtrR); (AtomR PtrR); (AtomR PtrR); (AtomR PtrR); (AtomR PtrR)];
          mf_body :=
            [ (ILocalGet
              (InstrT []
                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))])
              0);
              (ICopy
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]));
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                  [])
                0);
              (ILoad
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))])
                [ 0] Copy);
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [])
                1);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                  []));
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))])
                1);
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [])
                2);
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))])
                0);
              (ICopy
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]));
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                  [])
                0);
              (ILoad
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))])
                [ 1] Copy);
              (ILocalSet
                (InstrT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))] [])
                3);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                  []));
              (ILocalGet
                (InstrT [] [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))])
                3);
              (ILocalSet
                (InstrT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))] [])
                4);
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))])
                2);
              (ICopy
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]));
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [])
                2);
              (ILoad
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                    (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])
                [ 0] Copy);
              (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 5);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  []));
              (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 5);
              (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 6);
              (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 6);
              (ICopy
                (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 6);
              (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 6);
              (IDrop (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []));
              (ILocalGet
                (InstrT [] [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))])
                4);
              (IDrop
                (InstrT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))] []));
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))])
                2);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  []))];
        |};
          {|
            mf_type :=
              (MonoFunT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))]
                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]);
            mf_locals :=
              [ (AtomR PtrR);
                (AtomR PtrR);
                (AtomR PtrR);
                (AtomR PtrR);
                (AtomR PtrR);
                (AtomR PtrR);
                (AtomR PtrR);
                (AtomR PtrR)];
            mf_body :=
              [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
                (ITag
                  (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
                (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 1);
                (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 1);
                (ICopy
                  (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
                (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 1);
                (IGroup
                  (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR)]) ImCopy ImDrop) [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])]));
                (INew
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR)]) ImCopy ImDrop) [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])]
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR)])) ImDrop)
                        (ProdT (VALTYPE (ProdR [ (AtomR PtrR)]) ImCopy ImDrop) [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]));
                (ICast
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR)])) ImDrop)
                        (ProdT (VALTYPE (ProdR [ (AtomR PtrR)]) ImCopy ImDrop) [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]));
                (ICodeRef
                  (InstrT []
                    [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                      (MonoFunT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                              (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (BaseM MemGC)
                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                        [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])
                  0);
                (IGroup
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                      (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) ExCopy ExDrop)
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])]));
                (INew
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) ExCopy ExDrop)
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])]
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR I32R)])) ExDrop)
                        (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) ExCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                          (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])))]));
                (ICast
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR I32R)])) ExDrop)
                        (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) ExCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                          (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])))]
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                          (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]));
                (IPack
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                          (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                            (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]));
                (ILocalSet
                  (InstrT
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                            (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]
                    [])
                  2);
                (ILocalGet
                  (InstrT []
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                            (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))])
                  2);
                (ICopy
                  (InstrT
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                            (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                            (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])));
                      (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]));
                (ILocalSet
                  (InstrT
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                            (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]
                    [])
                  2);
                (IUnpack
                  (InstrT
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                            (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]
                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])
                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))
                  (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))
                  (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                          (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  [ (ILocalSet
                    (InstrT
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                            (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                      [])
                    3);
                    (ILocalGet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))])
                      3);
                    (ICopy
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]));
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                    (MonoFunT
                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                              (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                                (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]));
                    (ILocalSet
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                        [])
                      3);
                    (ILoad
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]));
                          (VarT 0)])
                      [ 0] Copy);
                    (ILocalSet (InstrT [ (VarT 0)] []) 4);
                    (IDrop
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                        []));
                    (ILocalGet (InstrT [] [ (VarT 0)]) 4);
                    (ILocalSet (InstrT [ (VarT 0)] []) 5);
                    (ILocalGet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))])
                      3);
                    (ICopy
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]));
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                    (MonoFunT
                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                              (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                                (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]));
                    (ILocalSet
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                        [])
                      3);
                    (ILoad
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]));
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (BaseM MemGC)
                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])
                      [ 1] Copy);
                    (ILocalSet
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]
                        [])
                      6);
                    (IDrop
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                        []));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])
                      6);
                    (ILocalSet
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]
                        [])
                      7);
                    (IGroup (InstrT [] [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]));
                    (INew
                      (InstrT [ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])]
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]));
                    (ICast
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])
                      7);
                    (ICopy
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (BaseM MemGC)
                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]));
                    (ILocalSet
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]
                        [])
                      7);
                    (ICallIndirect
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]));
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (BaseM MemGC)
                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]
                        [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])
                      7);
                    (IDrop
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]
                        []));
                    (ILocalGet (InstrT [] [ (VarT 0)]) 5);
                    (IDrop (InstrT [ (VarT 0)] []));
                    (ILocalGet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))])
                      3);
                    (IDrop
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                        []))]);
                (ILocalGet
                  (InstrT []
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                            (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))])
                  2);
                (IDrop
                  (InstrT
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                            (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) [])))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]
                    []));
                (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 1);
                (IDrop (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []))];
          |}];
      m_table := [ 0; 1];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 1;
                   |}];
    |}
    -----------closure_complex-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                            (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                    (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                      (MonoFunT
                                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                          (BaseM MemGC)
                                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                        [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]);
          mf_locals :=
            [ (AtomR PtrR);
              (AtomR PtrR);
              (AtomR PtrR);
              (AtomR PtrR);
              (AtomR PtrR);
              (AtomR PtrR);
              (AtomR PtrR);
              (AtomR PtrR);
              (AtomR PtrR);
              (AtomR PtrR);
              (AtomR PtrR);
              (AtomR PtrR);
              (AtomR PtrR);
              (AtomR PtrR)];
          mf_body :=
            [ (ILocalGet
              (InstrT []
                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                            (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                              (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                              (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (BaseM MemGC)
                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                      (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                        (MonoFunT
                                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                            (BaseM MemGC)
                                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                  (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))])
              0);
              (ICopy
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                              (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                          (MonoFunT
                                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC)
                                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                    (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                              (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                          (MonoFunT
                                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC)
                                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                    (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                            (MonoFunT
                                              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                                (BaseM MemGC)
                                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                      (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]));
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                              (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                          (MonoFunT
                                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC)
                                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                    (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [])
                0);
              (ILoad
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                              (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                          (MonoFunT
                                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC)
                                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                    (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                              (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                          (MonoFunT
                                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC)
                                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                    (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                            (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                    (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                      (MonoFunT
                                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                          (BaseM MemGC)
                                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                        [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))])
                [ 0] Copy);
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                    (MonoFunT
                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [])
                1);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                              (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                          (MonoFunT
                                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC)
                                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                    (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  []));
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                    (MonoFunT
                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))])
                1);
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                    (MonoFunT
                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [])
                2);
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                              (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                          (MonoFunT
                                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC)
                                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                    (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))])
                0);
              (ICopy
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                              (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                          (MonoFunT
                                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC)
                                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                    (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                              (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                          (MonoFunT
                                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC)
                                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                    (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                            (MonoFunT
                                              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                                (BaseM MemGC)
                                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                      (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]));
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                              (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                          (MonoFunT
                                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC)
                                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                    (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [])
                0);
              (ILoad
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                              (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                          (MonoFunT
                                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC)
                                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                    (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                              (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                          (MonoFunT
                                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC)
                                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                    (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                    (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])
                [ 1] Copy);
              (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 3);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                              (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                          (MonoFunT
                                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (BaseM MemGC)
                                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                    (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  []));
              (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 3);
              (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 4);
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                    (MonoFunT
                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))])
                2);
              (ICopy
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                    (MonoFunT
                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                    (MonoFunT
                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                            (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                    (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                      (MonoFunT
                                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                          (BaseM MemGC)
                                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                        [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]));
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                    (MonoFunT
                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [])
                2);
              (ILoad
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                    (MonoFunT
                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                    (MonoFunT
                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                    (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))])
                [ 0] Copy);
              (ILocalSet
                (InstrT
                  [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]
                  [])
                5);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                    (MonoFunT
                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  []));
              (ILocalGet
                (InstrT []
                  [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))])
                5);
              (ILocalSet
                (InstrT
                  [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]
                  [])
                6);
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                    (MonoFunT
                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))])
                2);
              (ICopy
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                    (MonoFunT
                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                    (MonoFunT
                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                            (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                    (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                      (MonoFunT
                                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                          (BaseM MemGC)
                                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                        [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]));
              (ILocalSet
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                    (MonoFunT
                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [])
                2);
              (ILoad
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                    (MonoFunT
                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                    (MonoFunT
                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                    (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])
                [ 1] Copy);
              (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 7);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                    (MonoFunT
                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  []));
              (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 7);
              (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 8);
              (ILocalGet
                (InstrT []
                  [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))])
                6);
              (ICopy
                (InstrT
                  [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]
                  [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])));
                    (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]));
              (ILocalSet
                (InstrT
                  [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]
                  [])
                6);
              (IUnpack
                (InstrT
                  [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])
                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                            (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                              (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                              (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (BaseM MemGC)
                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                      (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                        (MonoFunT
                                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                            (BaseM MemGC)
                                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                  (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                      (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (BaseM MemGC)
                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                [ (ILocalSet
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                    [])
                  9);
                  (ILocalGet
                    (InstrT []
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))])
                    9);
                  (ICopy
                    (InstrT
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]));
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]));
                  (ILocalSet
                    (InstrT
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                      [])
                    9);
                  (ILoad
                    (InstrT
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]));
                        (VarT 0)])
                    [ 0] Copy);
                  (ILocalSet (InstrT [ (VarT 0)] []) 10);
                  (IDrop
                    (InstrT
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                      []));
                  (ILocalGet (InstrT [] [ (VarT 0)]) 10);
                  (ILocalSet (InstrT [ (VarT 0)] []) 11);
                  (ILocalGet
                    (InstrT []
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))])
                    9);
                  (ICopy
                    (InstrT
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]));
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]));
                  (ILocalSet
                    (InstrT
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                      [])
                    9);
                  (ILoad
                    (InstrT
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]));
                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])
                    [ 1] Copy);
                  (ILocalSet
                    (InstrT
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]
                      [])
                    12);
                  (IDrop
                    (InstrT
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                      []));
                  (ILocalGet
                    (InstrT []
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])
                    12);
                  (ILocalSet
                    (InstrT
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]
                      [])
                    13);
                  (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 4);
                  (ICopy
                    (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
                  (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 4);
                  (ILocalGet
                    (InstrT []
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])
                    13);
                  (ICopy
                    (InstrT
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]));
                  (ILocalSet
                    (InstrT
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]
                      [])
                    13);
                  (ICallIndirect
                    (InstrT
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]
                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
                  (ILocalGet
                    (InstrT []
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])
                    13);
                  (IDrop
                    (InstrT
                      [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]
                      []));
                  (ILocalGet (InstrT [] [ (VarT 0)]) 11);
                  (IDrop (InstrT [ (VarT 0)] []));
                  (ILocalGet
                    (InstrT []
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))])
                    9);
                  (IDrop
                    (InstrT
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                      []))]);
              (IUntag
                (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
              (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 8);
              (ICopy
                (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 8);
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
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
              (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 8);
              (IDrop (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []));
              (ILocalGet
                (InstrT []
                  [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))])
                6);
              (IDrop
                (InstrT
                  [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]
                  []));
              (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 4);
              (IDrop (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []));
              (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                    (MonoFunT
                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))])
                2);
              (IDrop
                (InstrT
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                    (MonoFunT
                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                  []))];
        |};
          {|
            mf_type :=
              (MonoFunT
                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]);
            mf_locals := [ (AtomR PtrR); (AtomR PtrR); (AtomR PtrR); (AtomR PtrR); (AtomR PtrR); (AtomR PtrR); (AtomR PtrR)];
            mf_body :=
              [ (ILocalGet
                (InstrT []
                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))])
                0);
                (ICopy
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]));
                (ILocalSet
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                    [])
                  0);
                (ILoad
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))])
                  [ 0] Copy);
                (ILocalSet
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                    [])
                  1);
                (IDrop
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                    []));
                (ILocalGet
                  (InstrT []
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))])
                  1);
                (ILocalSet
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                    [])
                  2);
                (ILocalGet
                  (InstrT []
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))])
                  0);
                (ICopy
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]));
                (ILocalSet
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                    [])
                  0);
                (ILoad
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                      (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])
                  [ 1] Copy);
                (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 3);
                (IDrop
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                    []));
                (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 3);
                (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 4);
                (ILocalGet
                  (InstrT []
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))])
                  2);
                (ICopy
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]));
                (ILocalSet
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                    [])
                  2);
                (ILoad
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                      (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])
                  [ 0] Copy);
                (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 5);
                (IDrop
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                    []));
                (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 5);
                (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 6);
                (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 6);
                (ICopy
                  (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
                (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 6);
                (IUntag
                  (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                    [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]));
                (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 4);
                (ICopy
                  (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
                (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 4);
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
                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
                (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 6);
                (IDrop (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []));
                (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 4);
                (IDrop (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []));
                (ILocalGet
                  (InstrT []
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))])
                  2);
                (IDrop
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                    []))];
          |};
          {|
            mf_type :=
              (MonoFunT [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))]
                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]);
            mf_locals :=
              [ (AtomR PtrR);
                (AtomR PtrR);
                (AtomR PtrR);
                (AtomR PtrR);
                (AtomR PtrR);
                (AtomR PtrR);
                (AtomR PtrR);
                (AtomR PtrR);
                (AtomR PtrR)];
            mf_body :=
              [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
                (ITag
                  (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
                (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 1);
                (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 1);
                (ICopy
                  (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
                (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 1);
                (IGroup
                  (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR)]) ImCopy ImDrop) [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])]));
                (INew
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR)]) ImCopy ImDrop) [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])]
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR)])) ImDrop)
                        (ProdT (VALTYPE (ProdR [ (AtomR PtrR)]) ImCopy ImDrop) [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]));
                (ICast
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR)])) ImDrop)
                        (ProdT (VALTYPE (ProdR [ (AtomR PtrR)]) ImCopy ImDrop) [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]));
                (ICodeRef
                  (InstrT []
                    [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                      (MonoFunT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                              (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (BaseM MemGC)
                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                        [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])
                  1);
                (IGroup
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                      (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) ExCopy ExDrop)
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])]));
                (INew
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) ExCopy ExDrop)
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])]
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR I32R)])) ExDrop)
                        (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) ExCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])))]));
                (ICast
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR I32R)])) ExDrop)
                        (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) ExCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])))]
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]));
                (IPack
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR))]) ImDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]));
                (ILocalSet
                  (InstrT
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]
                    [])
                  2);
                (ILocalGet
                  (InstrT []
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))])
                  2);
                (ICopy
                  (InstrT
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])));
                      (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]));
                (ILocalSet
                  (InstrT
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]
                    [])
                  2);
                (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 1);
                (ICopy
                  (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)); (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
                (ILocalSet (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []) 1);
                (IGroup
                  (InstrT
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])));
                      (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ExCopy ExDrop)
                      [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])));
                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])]));
                (INew
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ExCopy ExDrop)
                      [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])));
                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])]
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR PtrR)])) ExDrop)
                        (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ExCopy ExDrop)
                          [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                            (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                    (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                      (MonoFunT
                                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                          (BaseM MemGC)
                                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                        [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])));
                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]));
                (ICast
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR PtrR)])) ExDrop)
                        (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR PtrR)]) ExCopy ExDrop)
                          [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                            (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                    (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                      (MonoFunT
                                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                          (BaseM MemGC)
                                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                        [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])));
                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                            (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                    (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                      (MonoFunT
                                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                          (BaseM MemGC)
                                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                        [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]));
                (ICodeRef
                  (InstrT []
                    [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                      (MonoFunT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                              (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (BaseM MemGC)
                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                    (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                                (MonoFunT
                                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                                    (BaseM MemGC)
                                                    (ProdT
                                                      (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                        [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])
                  0);
                (IGroup
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                            (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                            (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                    (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                      (MonoFunT
                                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                          (BaseM MemGC)
                                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                        [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                      (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                        (MonoFunT
                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                      (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                          (BaseM MemGC)
                                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                                  (MonoFunT
                                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                                      (BaseM MemGC)
                                                      (ProdT
                                                        (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) ExCopy ExDrop)
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                            (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                              (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                              (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (BaseM MemGC)
                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                      (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                        (MonoFunT
                                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                            (BaseM MemGC)
                                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                  (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                        (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                          (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                            (BaseM MemGC)
                                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                                    (MonoFunT
                                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                                        (BaseM MemGC)
                                                        (ProdT
                                                          (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                            ExDrop)
                                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])]));
                (INew
                  (InstrT
                    [ (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) ExCopy ExDrop)
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                            (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                              (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                              (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (BaseM MemGC)
                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                      (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                        (MonoFunT
                                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                            (BaseM MemGC)
                                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                  (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                        (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                        (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                          (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                            (BaseM MemGC)
                                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                                    (MonoFunT
                                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                                        (BaseM MemGC)
                                                        (ProdT
                                                          (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                            ExDrop)
                                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])]
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR I32R)])) ExDrop)
                        (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) ExCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                            (MonoFunT
                                              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                                (BaseM MemGC)
                                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                      (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                            (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                                (BaseM MemGC)
                                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                                      (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                                        (MonoFunT
                                                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                                            (BaseM MemGC)
                                                            (ProdT
                                                              (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                                ExDrop)
                                                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                                  (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])))]));
                (ICast
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (SerT (MEMTYPE (RepS (ProdR [ (AtomR PtrR); (AtomR I32R)])) ExDrop)
                        (ProdT (VALTYPE (ProdR [ (AtomR PtrR); (AtomR I32R)]) ExCopy ExDrop)
                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                            (MonoFunT
                                              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                                (BaseM MemGC)
                                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                      (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                            (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                                (BaseM MemGC)
                                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                                      (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                                        (MonoFunT
                                                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                                            (BaseM MemGC)
                                                            (ProdT
                                                              (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                                ExDrop)
                                                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                                  (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])))]
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                            (MonoFunT
                                              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                                (BaseM MemGC)
                                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                      (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                            (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                                (BaseM MemGC)
                                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                                      (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                                        (MonoFunT
                                                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                                            (BaseM MemGC)
                                                            (ProdT
                                                              (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                                ExDrop)
                                                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                                  (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]));
                (IPack
                  (InstrT
                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                            (MonoFunT
                                              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                                (BaseM MemGC)
                                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                      (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop)
                                            (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                              (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                                (BaseM MemGC)
                                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                    (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                                      (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                                        (MonoFunT
                                                          [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                                            (BaseM MemGC)
                                                            (ProdT
                                                              (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))])
                                                                ExDrop)
                                                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                                                (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                                                  (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                                          [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))])));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]));
                (ILocalSet
                  (InstrT
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]
                    [])
                  3);
                (ILocalGet
                  (InstrT []
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))])
                  3);
                (ICopy
                  (InstrT
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])));
                      (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                        (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]));
                (ILocalSet
                  (InstrT
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]
                    [])
                  3);
                (IUnpack
                  (InstrT
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]
                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])
                  (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC) (ProdT (MEMTYPE (ProdS []) ImDrop) []))
                  (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))
                  (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))
                  (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                    (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                          (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                            (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                              (MonoFunT
                                [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                  (BaseM MemGC)
                                  (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                    [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                      (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                        (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) ImCopy ImDrop) (ProdR [ (AtomR I32R)]))
                  [ (ILocalSet
                    (InstrT
                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                      [])
                    4);
                    (ILocalGet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))])
                      4);
                    (ICopy
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]));
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                    (MonoFunT
                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]));
                    (ILocalSet
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                        [])
                      4);
                    (ILoad
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]));
                          (VarT 0)])
                      [ 0] Copy);
                    (ILocalSet (InstrT [ (VarT 0)] []) 5);
                    (IDrop
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                        []));
                    (ILocalGet (InstrT [] [ (VarT 0)]) 5);
                    (ILocalSet (InstrT [ (VarT 0)] []) 6);
                    (ILocalGet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))])
                      4);
                    (ICopy
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]));
                          (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                            (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                              [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                  (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                    (MonoFunT
                                      [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                        (BaseM MemGC)
                                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                            (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                              (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                      [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]));
                    (ILocalSet
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                        [])
                      4);
                    (ILoad
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]));
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (BaseM MemGC)
                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])
                      [ 1] Copy);
                    (ILocalSet
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]
                        [])
                      7);
                    (IDrop
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                        []));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])
                      7);
                    (ILocalSet
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]
                        [])
                      8);
                    (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 3);
                    (ITag
                      (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                        [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])
                      8);
                    (ICopy
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (BaseM MemGC)
                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]));
                    (ILocalSet
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]
                        [])
                      8);
                    (ICallIndirect
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]));
                          (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                            (MonoFunT
                              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                (BaseM MemGC)
                                (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                  [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                    (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                              [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]
                        [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]));
                    (ILocalGet
                      (InstrT []
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))])
                      8);
                    (IDrop
                      (InstrT
                        [ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                          (MonoFunT
                            [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                              (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                  (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop) (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                            [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))]
                        []));
                    (ILocalGet (InstrT [] [ (VarT 0)]) 6);
                    (IDrop (InstrT [ (VarT 0)] []));
                    (ILocalGet
                      (InstrT []
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))])
                      4);
                    (IDrop
                      (InstrT
                        [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                          (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                            [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                              (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                                (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                  (MonoFunT
                                    [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                      (BaseM MemGC)
                                      (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                        [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                          (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                            (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                    [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))]))]
                        []))]);
                (ILocalGet
                  (InstrT []
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))])
                  3);
                (IDrop
                  (InstrT
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]
                    []));
                (ILocalGet
                  (InstrT []
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))])
                  2);
                (IDrop
                  (InstrT
                    [ (ExistsTypeT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                      (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                        (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR I32R))]) ExDrop)
                          [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                            (SerT (MEMTYPE (RepS (AtomR I32R)) ImDrop)
                              (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop)
                                (MonoFunT
                                  [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop)
                                    (BaseM MemGC)
                                    (ProdT (MEMTYPE (ProdS [ (RepS (AtomR PtrR)); (RepS (AtomR PtrR))]) ExDrop)
                                      [ (SerT (MEMTYPE (RepS (AtomR PtrR)) ExDrop) (VarT 0));
                                        (SerT (MEMTYPE (RepS (AtomR PtrR)) ImDrop)
                                          (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop)))]))]
                                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))])))])))]
                    []));
                (ILocalGet (InstrT [] [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]) 1);
                (IDrop (InstrT [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))] []))];
          |}];
      m_table := [ 0; 1; 2];
      m_exports := [ {|
                     me_name := "_start"; me_desc := 2;
                   |}];
    |} |xxx}]
