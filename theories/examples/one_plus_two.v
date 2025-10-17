From stdpp Require Import base list.
From RichWasm Require Import syntax layout typing.

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

Definition arity : Type := nat * nat.

Definition instr_t_ar (τ: instruction_type) : nat * nat :=
  let '(InstrT ins outs) := τ in
  (length ins, length outs).

Definition instr_ar : instruction -> arity :=
  instr_t_ar ∘ proj_instr_ty.

Definition proj_args : arity -> nat := fst.
Definition proj_rets : arity -> nat := snd.

Definition instr_args : instruction -> nat :=
  proj_args ∘ instr_ar.

Definition instr_rets : instruction -> nat :=
  proj_rets ∘ instr_ar.

Eval vm_compute in (instr_ar <$> (concat (mf_body <$> m_functions ll_1_plus_2))).

Ltac solve_mono_rep :=
  repeat match goal with
    | |- has_mono_rep_instr _ _ => split
    | |- Forall (has_mono_rep _) _ => constructor
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

(* Like TNumConst but with an equation for ψ instead of a let binding. *)
Lemma TNumConst_lax M F L ν n ψ:
  ψ = InstrT [] [num_type_type ν] ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (INumConst ψ n) ψ L.
Proof.
  intros ->.
  apply TNumConst.
Qed.

Ltac solve_num_type_type_eq :=
  solve [transitivity (num_type_type (IntT I32T)); eauto
        |transitivity (num_type_type (IntT I64T)); eauto
        |transitivity (num_type_type (FloatT F64T)); eauto
        |transitivity (num_type_type (FloatT F64T)); eauto].

Ltac solve_instr_type_ok :=
  match goal with
  | |- has_instruction_type_ok ?F ?ψ ?L =>
      constructor; [solve_mono_rep | solve_local_ctx_ok]
  end.

Ltac solve_has_instr_type :=
  match goal with
  | |- has_instruction_type ?M ?F ?L (INumConst ?ψ0 ?c) ?ψ ?L' =>
      eapply TNumConst_lax;
        [by (repeat f_equal; solve_num_type_type_eq) | solve_instr_type_ok]
  end.

Ltac step_have_instr_type :=
  match goal with
  | |- have_instruction_type ?M ?F ?L (?e :: ?es) (InstrT ?ins ?outs) ?L' =>
      let stack_len := eval vm_compute in (length ins) in
      let e_args := eval vm_compute in (instr_args e) in
      match eval vm_compute in (Nat.eqb stack_len e_args) with
      | true => eapply TCons
      | false => eapply TFrame; first by solve_mono_rep  
      end
  | |- have_instruction_type ?M ?F ?L [] (InstrT _ _) ?L' =>
      apply TNil; by solve_local_ctx_ok
  | |- have_instruction_type ?M ?F ?L [] (InstrT _ _) ?L' =>
      apply TFrame; first by solve_mono_rep
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
        { instantiate (2:=[NumT (VALTYPE (PrimR I32R) ImCopy ImDrop) (IntT I32T)]). admit. }
        eapply TFrame.
        eapply TCons.
        { instantiate (3 := []). admit.}
        eapply TCons.
        {
          apply TNum; repeat constructor; solve_mono_rep.
        }
        eapply TFrame; first by solve_mono_rep.
        eapply TNil; by solve_local_ctx_ok.
        step_have_instr_type.
        solve_has_instr_type.
        apply TFrame.
        step_have_instr_type.
        step_have_instr_type.
        solve_has_instr_type.
        step_have_instr_type.
        {
          apply TNum; repeat constructor; solve_mono_rep.
        }
        step_have_instr_type.
        step_have_instr_type.
    + constructor.
Admitted.
