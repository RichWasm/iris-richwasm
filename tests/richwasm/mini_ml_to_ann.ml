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
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]);
          mf_locals := [ (AtomR PtrR)];
          mf_body :=
            [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
              (ITag
                (InstrT [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
                  [ (I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop))]))];
        |}];
      m_table := [];
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
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]);
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
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]);
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
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
    |}
    -----------tuple_project-----------
    FAILURE (InstrErr
     (error (CannotResolvePath ExpectedStruct (Path (1)) (Ser (Prod (I31 I31)))))
     (instr (Load (Path (1)) Follow))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return ((Ref (Base GC) (Ser (Prod ())))))
       (functions
        ((FunctionType () ((Ref (Base GC) (Ser (Prod ()))))
          ((Ref (Base GC) (Ser (Prod ())))))))
       (table ()) (lfx ())))
     (state
      ((locals ((Ref (Base GC) (Ser (Prod ()))) (Plug (Atom Ptr))))
       (stack ((Ref (Base GC) (Ser (Prod (I31 I31)))))))))
    -----------sum_unit-----------
    FAILURE (InstrErr
     (error
      (Ctx
       (error
        (CannotMeet "expected memtype" (VALTYPE (AtomR PtrR) ExCopy ExDrop)))
       (ctx
        (InstrTOut ((Ref (Base GC) (Variant ((Ref (Base GC) (Ser (Prod ())))))))))))
     (instr (Inject (GC) 0 ((Ref (Base GC) (Ser (Prod ()))))))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return ((Ref (Base GC) (Ser (Prod ())))))
       (functions
        ((FunctionType () ((Ref (Base GC) (Ser (Prod ()))))
          ((Ref (Base GC) (Ser (Prod ())))))))
       (table ()) (lfx ())))
     (state
      ((locals ((Ref (Base GC) (Ser (Prod ()))) (Plug (Atom Ptr))))
       (stack ((Ref (Base GC) (Ser (Prod ()))))))))
    -----------sum_option-----------
    FAILURE (InstrErr
     (error
      (Ctx
       (error
        (CannotMeet "expected memtype" (VALTYPE (AtomR PtrR) ExCopy ExDrop)))
       (ctx
        (InstrTOut
         ((Ref (Base GC) (Variant ((Ref (Base GC) (Ser (Prod ()))) I31))))))))
     (instr (Inject (GC) 1 ((Ref (Base GC) (Ser (Prod ()))) I31)))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return ((Ref (Base GC) (Ser (Prod ())))))
       (functions
        ((FunctionType () ((Ref (Base GC) (Ser (Prod ()))))
          ((Ref (Base GC) (Ser (Prod ())))))))
       (table ()) (lfx ())))
     (state
      ((locals ((Ref (Base GC) (Ser (Prod ()))) (Plug (Atom Ptr))))
       (stack (I31)))))
    -----------add-----------
    {|
      m_imports := [];
      m_functions :=
        [ {|
          mf_type :=
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]);
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
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]);
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
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]);
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
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]);
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
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]);
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
            (MonoFunT
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]
              [ (RefT (VALTYPE (AtomR PtrR) ExCopy ExDrop) (BaseM MemGC)
                (SerT (MEMTYPE (RepS (ProdR [])) ImDrop) (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) [])))]);
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
      m_exports := [ {|
                     me_name := "_start"; me_desc := 0;
                   |}];
    |}
    -----------return_one-----------
    FAILURE (InstrErr
     (error
      (CannotResolvePath ExpectedStruct (Path (0))
       (Ser
        (Prod ((Ref (Base GC) (Ser (Prod ()))) (Ref (Base GC) (Ser (Prod ()))))))))
     (instr (Load (Path (0)) Follow))
     (env
      ((local_offset 1) (kinds ()) (labels ()) (return (I31))
       (functions
        ((FunctionType ()
          ((Ref (Base GC)
            (Ser
             (Prod
              ((Ref (Base GC) (Ser (Prod ()))) (Ref (Base GC) (Ser (Prod ()))))))))
          (I31))
         (FunctionType () ((Ref (Base GC) (Ser (Prod ()))))
          ((Ref (Base GC) (Ser (Prod ())))))))
       (table ()) (lfx ())))
     (state
      ((locals
        ((Ref (Base GC)
          (Ser
           (Prod
            ((Ref (Base GC) (Ser (Prod ()))) (Ref (Base GC) (Ser (Prod ())))))))
         (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr))))
       (stack
        ((Ref (Base GC)
          (Ser
           (Prod
            ((Ref (Base GC) (Ser (Prod ()))) (Ref (Base GC) (Ser (Prod ()))))))))))))
    -----------add_one-----------
    FAILURE (InstrErr
     (error
      (CannotResolvePath ExpectedStruct (Path (1))
       (Ser (Prod ((Ref (Base GC) (Ser (Prod ()))) I31)))))
     (instr (Load (Path (1)) Follow))
     (env
      ((local_offset 1) (kinds ()) (labels ()) (return (I31))
       (functions
        ((FunctionType ()
          ((Ref (Base GC) (Ser (Prod ((Ref (Base GC) (Ser (Prod ()))) I31)))))
          (I31))))
       (table ()) (lfx ())))
     (state
      ((locals
        ((Ref (Base GC) (Ser (Prod ((Ref (Base GC) (Ser (Prod ()))) I31))))
         (Plug (Atom Ptr)) (Plug (Atom Ptr))))
       (stack
        ((Ref (Base GC) (Ser (Prod ((Ref (Base GC) (Ser (Prod ()))) I31)))))))))
    -----------id-----------
    FAILURE (InstrErr
     (error
      (CannotResolvePath ExpectedStruct (Path (1))
       (Ser (Prod ((Ref (Base GC) (Ser (Prod ()))) (Var 0))))))
     (instr (Load (Path (1)) Follow))
     (env
      ((local_offset 1) (kinds ((VALTYPE (Atom Ptr) ExCopy ExDrop))) (labels ())
       (return ((Var 0)))
       (functions
        ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
          ((Ref (Base GC) (Ser (Prod ((Ref (Base GC) (Ser (Prod ()))) (Var 0))))))
          ((Var 0)))))
       (table ()) (lfx ())))
     (state
      ((locals
        ((Ref (Base GC) (Ser (Prod ((Ref (Base GC) (Ser (Prod ()))) (Var 0)))))
         (Plug (Atom Ptr)) (Plug (Atom Ptr))))
       (stack
        ((Ref (Base GC) (Ser (Prod ((Ref (Base GC) (Ser (Prod ()))) (Var 0))))))))))
    -----------apply_id-----------
    FAILURE (InstrErr
     (error
      (CannotResolvePath ExpectedStruct (Path (1))
       (Ser (Prod ((Ref (Base GC) (Ser (Prod ()))) (Var 0))))))
     (instr (Load (Path (1)) Follow))
     (env
      ((local_offset 1) (kinds ((VALTYPE (Atom Ptr) ExCopy ExDrop))) (labels ())
       (return ((Var 0)))
       (functions
        ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
          ((Ref (Base GC) (Ser (Prod ((Ref (Base GC) (Ser (Prod ()))) (Var 0))))))
          ((Var 0)))
         (FunctionType () ((Ref (Base GC) (Ser (Prod ()))))
          ((Ref (Base GC) (Ser (Prod ())))))))
       (table ()) (lfx ())))
     (state
      ((locals
        ((Ref (Base GC) (Ser (Prod ((Ref (Base GC) (Ser (Prod ()))) (Var 0)))))
         (Plug (Atom Ptr)) (Plug (Atom Ptr))))
       (stack
        ((Ref (Base GC) (Ser (Prod ((Ref (Base GC) (Ser (Prod ()))) (Var 0))))))))))
    -----------opt_case-----------
    FAILURE (InstrErr
     (error
      (Ctx
       (error
        (CannotMeet "expected memtype" (VALTYPE (AtomR PtrR) ExCopy ExDrop)))
       (ctx
        (InstrTOut
         ((Ref (Base GC) (Variant ((Ref (Base GC) (Ser (Prod ()))) I31))))))))
     (instr (Inject (GC) 1 ((Ref (Base GC) (Ser (Prod ()))) I31)))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return ((Ref (Base GC) (Ser (Prod ())))))
       (functions
        ((FunctionType () ((Ref (Base GC) (Ser (Prod ()))))
          ((Ref (Base GC) (Ser (Prod ())))))))
       (table ()) (lfx ())))
     (state
      ((locals
        ((Ref (Base GC) (Ser (Prod ()))) (Plug (Atom Ptr)) (Plug (Atom Ptr))
         (Plug (Atom Ptr)) (Plug (Atom Ptr))))
       (stack (I31)))))
    -----------poly_len-----------
    FAILURE (InstrErr
     (error
      (CannotResolvePath ExpectedStruct (Path (1))
       (Ser
        (Prod
         ((Ref (Base GC) (Ser (Prod ())))
          (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
           (Ref (Base GC)
            (Ser
             (Sum
              ((Ref (Base GC) (Ser (Prod ())))
               (Ref (Base GC) (Ser (Sum ((Var 1) (Var 0)))))))))))))))
     (instr (Load (Path (1)) Follow))
     (env
      ((local_offset 1) (kinds ((VALTYPE (Atom Ptr) ExCopy ExDrop))) (labels ())
       (return (I31))
       (functions
        ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
          ((Ref (Base GC)
            (Ser
             (Prod
              ((Ref (Base GC) (Ser (Prod ())))
               (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                (Ref (Base GC)
                 (Ser
                  (Sum
                   ((Ref (Base GC) (Ser (Prod ())))
                    (Ref (Base GC) (Ser (Sum ((Var 1) (Var 0)))))))))))))))
          (I31))
         (FunctionType () ((Ref (Base GC) (Ser (Prod ()))))
          ((Ref (Base GC) (Ser (Prod ())))))))
       (table ()) (lfx ())))
     (state
      ((locals
        ((Ref (Base GC)
          (Ser
           (Prod
            ((Ref (Base GC) (Ser (Prod ())))
             (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
              (Ref (Base GC)
               (Ser
                (Sum
                 ((Ref (Base GC) (Ser (Prod ())))
                  (Ref (Base GC) (Ser (Sum ((Var 1) (Var 0))))))))))))))
         (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr))
         (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr))))
       (stack
        ((Ref (Base GC)
          (Ser
           (Prod
            ((Ref (Base GC) (Ser (Prod ())))
             (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
              (Ref (Base GC)
               (Ser
                (Sum
                 ((Ref (Base GC) (Ser (Prod ())))
                  (Ref (Base GC) (Ser (Sum ((Var 1) (Var 0)))))))))))))))))))
    -----------mini_zip-----------
    FAILURE (InstrErr
     (error
      (CannotResolvePath ExpectedStruct (Path (1))
       (Ser
        (Prod
         ((Ref (Base GC) (Ser (Prod ())))
          (Ref (Base GC)
           (Ser
            (Prod ((Ref (Base GC) (Ser (Var 0))) (Ref (Base GC) (Ser (Var 1))))))))))))
     (instr (Load (Path (1)) Follow))
     (env
      ((local_offset 1)
       (kinds
        ((VALTYPE (Atom Ptr) ExCopy ExDrop) (VALTYPE (Atom Ptr) ExCopy ExDrop)))
       (labels ())
       (return
        ((Ref (Base GC) (Ser (Ref (Base GC) (Ser (Prod ((Var 0) (Var 1)))))))))
       (functions
        ((FunctionType
          ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
           (Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
          ((Ref (Base GC)
            (Ser
             (Prod
              ((Ref (Base GC) (Ser (Prod ())))
               (Ref (Base GC)
                (Ser
                 (Prod
                  ((Ref (Base GC) (Ser (Var 0))) (Ref (Base GC) (Ser (Var 1))))))))))))
          ((Ref (Base GC) (Ser (Ref (Base GC) (Ser (Prod ((Var 0) (Var 1)))))))))))
       (table ()) (lfx ())))
     (state
      ((locals
        ((Ref (Base GC)
          (Ser
           (Prod
            ((Ref (Base GC) (Ser (Prod ())))
             (Ref (Base GC)
              (Ser
               (Prod
                ((Ref (Base GC) (Ser (Var 0))) (Ref (Base GC) (Ser (Var 1)))))))))))
         (Plug (Atom Ptr)) (Plug (Atom Ptr))))
       (stack
        ((Ref (Base GC)
          (Ser
           (Prod
            ((Ref (Base GC) (Ser (Prod ())))
             (Ref (Base GC)
              (Ser
               (Prod
                ((Ref (Base GC) (Ser (Var 0))) (Ref (Base GC) (Ser (Var 1))))))))))))))))
    -----------closure_simpl-----------
    FAILURE (InstrErr
     (error
      (CannotResolvePath ExpectedStruct (Path (0))
       (Ser
        (Prod
         ((Ref (Base GC) (Ser (Prod (I31)))) (Ref (Base GC) (Ser (Prod ()))))))))
     (instr (Load (Path (0)) Follow))
     (env
      ((local_offset 1) (kinds ()) (labels ()) (return (I31))
       (functions
        ((FunctionType ()
          ((Ref (Base GC)
            (Ser
             (Prod
              ((Ref (Base GC) (Ser (Prod (I31))))
               (Ref (Base GC) (Ser (Prod ()))))))))
          (I31))
         (FunctionType () ((Ref (Base GC) (Ser (Prod ()))))
          ((Ref (Base GC) (Ser (Prod ())))))))
       (table ()) (lfx ())))
     (state
      ((locals
        ((Ref (Base GC)
          (Ser
           (Prod
            ((Ref (Base GC) (Ser (Prod (I31)))) (Ref (Base GC) (Ser (Prod ())))))))
         (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr))))
       (stack
        ((Ref (Base GC)
          (Ser
           (Prod
            ((Ref (Base GC) (Ser (Prod (I31)))) (Ref (Base GC) (Ser (Prod ()))))))))))))
    -----------closure_complex-----------
    FAILURE (InstrErr
     (error
      (CannotResolvePath ExpectedStruct (Path (0))
       (Ser
        (Prod
         ((Ref (Base GC)
           (Ser
            (Prod
             ((Ref (Base GC)
               (Ser
                (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
                 (Ref (Base GC)
                  (Ser
                   (Prod
                    ((Var 0)
                     (CodeRef
                      (FunctionType ()
                       ((Ref (Base GC) (Ser (Prod ((Var 0) I31))))) (I31))))))))))
              I31))))
          I31)))))
     (instr (Load (Path (0)) Follow))
     (env
      ((local_offset 1) (kinds ()) (labels ()) (return (I31))
       (functions
        ((FunctionType ()
          ((Ref (Base GC)
            (Ser
             (Prod
              ((Ref (Base GC)
                (Ser
                 (Prod
                  ((Ref (Base GC)
                    (Ser
                     (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
                      (Ref (Base GC)
                       (Ser
                        (Prod
                         ((Var 0)
                          (CodeRef
                           (FunctionType ()
                            ((Ref (Base GC) (Ser (Prod ((Var 0) I31)))))
                            (I31))))))))))
                   I31))))
               I31)))))
          (I31))
         (FunctionType ()
          ((Ref (Base GC) (Ser (Prod ((Ref (Base GC) (Ser (Prod (I31)))) I31)))))
          (I31))
         (FunctionType () ((Ref (Base GC) (Ser (Prod ()))))
          ((Ref (Base GC) (Ser (Prod ())))))))
       (table ()) (lfx ())))
     (state
      ((locals
        ((Ref (Base GC)
          (Ser
           (Prod
            ((Ref (Base GC)
              (Ser
               (Prod
                ((Ref (Base GC)
                  (Ser
                   (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
                    (Ref (Base GC)
                     (Ser
                      (Prod
                       ((Var 0)
                        (CodeRef
                         (FunctionType ()
                          ((Ref (Base GC) (Ser (Prod ((Var 0) I31))))) (I31))))))))))
                 I31))))
             I31))))
         (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr))
         (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr))))
       (stack
        ((Ref (Base GC)
          (Ser
           (Prod
            ((Ref (Base GC)
              (Ser
               (Prod
                ((Ref (Base GC)
                  (Ser
                   (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
                    (Ref (Base GC)
                     (Ser
                      (Prod
                       ((Var 0)
                        (CodeRef
                         (FunctionType ()
                          ((Ref (Base GC) (Ser (Prod ((Var 0) I31))))) (I31))))))))))
                 I31))))
             I31))))))))) |xxx}]
