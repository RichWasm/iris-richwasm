Require Import RecordUpdate.RecordUpdate.
From stdpp Require Import base list.
From Stdlib.Strings Require Import String.

From RichWasm Require Import layout syntax typing util.
From RichWasm Require Import typechecker.
Set Bullet Behavior "Strict Subproofs".


Definition ll_1_plus_2 := {|
  m_imports := [];
  m_functions := [{|
    mf_type := (MonoFunT [] [(NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))]);
    mf_locals := [];
    mf_body := [
      (INumConst (InstrT [] [(NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))]) 1);
      (INumConst (InstrT [] [(NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))]) 2);
      (INum
        (InstrT
          [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T));
            (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))]
          [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))])
        (IInt2 I32T AddI))
    ];
  |}];
  m_table := [];
  m_exports := [{| me_name := "test"%string; me_desc := 0 |}];
|}.

Compute (has_module_type_checker_with_synth ll_1_plus_2).
(* ==> inl () : type_checker_res *)

Definition ll_1_plus_2_bad := {|
  m_imports := [];
  m_functions := [{|
    mf_type := (MonoFunT [] [(NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))]);
    mf_locals := [];
    mf_body := [
      (INumConst (InstrT [] [(NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))]) 1);
      (INumConst (InstrT [] [(NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I64T))]) 2);
      (INum
        (InstrT
          [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T));
            (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))]
          [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))])
        (IInt2 I32T AddI))
    ];
  |}];
  m_table := [];
  m_exports := [{| me_name := "test"%string; me_desc := 0 |}];
|}.



Compute (has_module_type_checker_with_synth ll_1_plus_2_bad).
(* ==> inr "function types don't equal" : type_checker_res *)
(* which I recognize isn't insanely helpful *)


Definition m := {|
  m_imports := [];
  m_functions :=
    [ {|
      mf_type :=
        (MonoFunT [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))] []);
      mf_locals := [ (AtomR F32R)];
      mf_body :=
        [ (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))]) Copy
          0);
          (INum
            (InstrT [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))]
              [ (NumT (VALTYPE (AtomR F32R) NoRefs) (FloatT F32T))])
            (ICvt (CReinterpret (IntT I32T))));
          (ILocalSet
            (InstrT [ (NumT (VALTYPE (AtomR F32R) NoRefs) (FloatT F32T))] []) 1)];
    |}];
  m_table := [];
  m_exports := [ {|
                 me_name := "_start"; me_desc := 0;
               |}];
|}.


Compute (has_module_type_checker_with_synth m).


Definition my_unpack :=
  {|
  m_imports := [];
  m_functions :=
    [ {|
      mf_type := (MonoFunT [] []);
      mf_locals := [];
      mf_body :=
        [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))])
          5);
          (IPack
            (InstrT [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))]
              [ (ExistsTypeT (VALTYPE (AtomR I32R) NoRefs)
                (VALTYPE (AtomR I32R) NoRefs) (VarT 0))]));
          (IUnpack
            (InstrT
              [ (ExistsTypeT (VALTYPE (AtomR I32R) NoRefs)
                (VALTYPE (AtomR I32R) NoRefs) (VarT 0))]
              [])
             []
             [ (IDrop (InstrT [ (VarT 0)] []))])];
    |}];
  m_table := [];
  m_exports := [ {|
                 me_name := "_start"; me_desc := 0;
               |}];
  |}.

Compute (has_module_type_checker_with_synth my_unpack).


Definition my_unpack3 := {|
  m_imports := [];
  m_functions :=
    [ {|
      mf_type := (MonoFunT [] []);
      mf_locals := [ (AtomR I32R)];
      mf_body :=
        [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))])
          5);
          (IPack
            (InstrT [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))]
              [ (ExistsTypeT (VALTYPE (AtomR I32R) NoRefs)
                (VALTYPE (AtomR I32R) NoRefs) (VarT 0))]));
          (ILocalSet
            (InstrT
              [ (ExistsTypeT (VALTYPE (AtomR I32R) NoRefs)
                (VALTYPE (AtomR I32R) NoRefs) (VarT 0))]
              [])
            0);
          (INumConst
            (InstrT [] [ (NumT (VALTYPE (AtomR F32R) NoRefs) (FloatT F32T))]) 7);
          (IPack
            (InstrT [ (NumT (VALTYPE (AtomR F32R) NoRefs) (FloatT F32T))]
              [ (ExistsTypeT (VALTYPE (AtomR F32R) NoRefs)
                (VALTYPE (AtomR F32R) NoRefs) (VarT 0))]));
          (IUnpack
            (InstrT
              [ (ExistsTypeT (VALTYPE (AtomR F32R) NoRefs)
                (VALTYPE (AtomR F32R) NoRefs) (VarT 0))]
              [])
            [
            (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) NoRefs)
              (ProdR [ (AtomR I32R)]))]
            [ (ILocalGet
              (InstrT []
                [ (ExistsTypeT (VALTYPE (AtomR I32R) NoRefs)
                  (VALTYPE (AtomR I32R) NoRefs) (VarT 0))]) Move
              0);
              (IUnpack
                (InstrT
                  [ (VarT 0);
                    (ExistsTypeT (VALTYPE (AtomR I32R) NoRefs)
                      (VALTYPE (AtomR I32R) NoRefs) (VarT 0))]
                  [])
                [
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) NoRefs)
                  (ProdR [ (AtomR I32R)]))]
                [ (IDrop (InstrT [ (VarT 0)] [])); (IDrop (InstrT [ (VarT 1)] []))])])];
    |}];
  m_table := [];
  m_exports := [ {|
                 me_name := "_start"; me_desc := 0;
               |}];
|}.

Compute (has_module_type_checker_with_synth my_unpack3).
