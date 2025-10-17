From stdpp Require Import base list.
From RichWasm Require Import syntax typing autowp.

Set Bullet Behavior "Strict Subproofs".

Definition ll_1_plus_2 := {|
  m_imports := [];
  m_functions := [ {|
    mf_type := (MonoFunT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]);
    mf_locals := [];
    mf_body := [
      (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 1);
      (INumConst (InstrT [] [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) 2);
      (INum (InstrT [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T));
                          (NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]
                [(NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T))]) (IInt2 I32T AddI))
    ];
  |}];
  m_table := [];
  m_exports := [0];
|}.

Definition instr_t_ar (τ: instruction_type) : arity :=
  let '(InstrT ins outs) := τ in
  Ar (length ins) (length outs).

Definition instr_ar : instruction -> arity :=
  instr_t_ar ∘ proj_instr_ty.

Eval vm_compute in (instr_ar <$> (concat (mf_body <$> m_functions ll_1_plus_2))).

Ltac solve_mono_rep :=
  repeat match goal with
    | |- has_mono_rep _ _ =>
        econstructor;
        first by (econstructor; constructor)
    | |- layout.eval_rep _ = Some _ => reflexivity
    end.

Ltac solve_local_ctx_ok :=
  match goal with
  | |- local_ctx_ok ?F [] => by constructor
  | |- local_ctx_ok ?F (?x :: ?xs) => fail
  end.

Theorem one_plus_two_typed :
  exists T, has_module_type ll_1_plus_2 T.
Proof.
  eexists.
  econstructor.
  - cbn.
    reflexivity.
  - cbn.
    reflexivity.
  - constructor.
    + set (M:={| mc_functions := m_imports ll_1_plus_2 ++ map mf_type (m_functions ll_1_plus_2); mc_table := [] |}).
      simpl mf_type.
      econstructor.
      * cbn. reflexivity.
      * cbn.
        admit.
      * cbn.
        set (F := {|
                   fc_return := [NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T)];
                   typing.fc_locals := [];
                   fc_labels := [];
                   fc_kind_ctx :=
                     kc_of_fft
                       {|
                         fft_mem_vars := 0;
                         fft_rep_vars := 0;
                         fft_size_vars := 0;
                         fft_type_vars := [];
                         fft_in := [];
                         fft_out := [NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T)]
                       |};
                   fc_type_vars := []
                 |}).
        eapply TCons.
        { admit. }
        eapply TCons.
        { admit. }
        eapply TCons.
        {
          apply TNum; repeat constructor; solve_mono_rep.
        }
        eapply TFrame; first by solve_mono_rep.
        eapply TNil; by solve_local_ctx_ok.
    + constructor.
Admitted.
