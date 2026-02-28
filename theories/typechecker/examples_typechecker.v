Require Import RecordUpdate.RecordUpdate.
From stdpp Require Import base list.
From Stdlib.Strings Require Import String.

From RichWasm Require Import layout syntax typing util.
From RichWasm Require Import typechecker.
Set Bullet Behavior "Strict Subproofs".

Definition ll_1_plus_2 := {|
  m_imports := [];
  m_functions := [{|
    mf_type := (MonoFunT [] [(NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
    mf_locals := [];
    mf_body := [
      (INumConst (InstrT [] [(NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
      (INumConst (InstrT [] [(NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
      (INum
        (InstrT
          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
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
    mf_type := (MonoFunT [] [(NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]);
    mf_locals := [];
    mf_body := [
      (INumConst (InstrT [] [(NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
      (INumConst (InstrT [] [(NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I64T))]) 2);
      (INum
        (InstrT
          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T));
            (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))]
          [ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T))])
        (IInt2 I32T AddI))
    ];
  |}];
  m_table := [];
  m_exports := [{| me_name := "test"%string; me_desc := 0 |}];
|}.

Compute (has_module_type_checker_with_synth ll_1_plus_2_bad).
(* ==> inr "function types don't equal" : type_checker_res *)
(* which I recognize isn't insanely helpful *)
