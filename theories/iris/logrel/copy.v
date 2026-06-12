Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.util.

Section copy.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable mr : module_runtime.
  Variable sr : store_runtime.

  Lemma type_dup se F τ κ sv :
    sem_env_interp F se ->
    has_kind F τ κ ->
    ref_flag_le (kind_ref_flag κ) GCRefs ->
    let T := type_interp rti sr τ se sv in
    T -∗ T ∗ T.
  Proof.
    intros Hse Hkind Hle.
    assert (kind_ok (fc_kind_ctx F) κ) as Hok.
    {
      eapply has_kind_inv in Hkind.
      by inversion Hkind.
    }
    pose proof Hok as Hok'.
    eapply eval_kind_ok_Some in Hok'; eauto.
    destruct Hok' as [sk Hev].
    pose proof Hkind as Hkind'.
    eapply (kinding_sound rti sr) in Hkind'; eauto.
    unfold skind_has_stype in Hkind'.
    destruct Hkind' as [Hrefflag _].
    erewrite <- eval_kind_flag in Hrefflag; eauto.
    eapply ref_flag_stype_interp_refine in Hrefflag; eauto.
    cbn in Hrefflag.
    specialize (Hrefflag sv).
    rewrite value_interp_eq in Hrefflag.
    intros T; unfold T.
    rewrite type_interp_eq.
    iIntros "#HT".
    by iSplit.
  Qed.

  Lemma gcrefs_atoms_copyable F se ρ ξ ιs τ os vs :
    has_kind F τ (VALTYPE ρ ξ) ->
    ref_flag_le ξ GCRefs ->
    eval_rep se ρ = Some ιs ->
    ref_flag_atoms_interp ξ (SAtoms os) ->
    Forall2 has_arep ιs os ->
    ⊢ ([∗ list] o;v ∈ os;vs, ⌜atom_copyable o⌝ -∗ atom_interp o v) -∗
      [∗ list] o;v ∈ os;vs, atom_interp o v.
  Proof.
    iIntros (Hkind Hle Hev Href Hrep) "Hos".
    iApply big_sepL2_mono; last by iFrame.
    intros k o v Ho Hv.
    iIntros "Ho".
    iApply "Ho".
    iPureIntro.
    eapply Forall2_lookup_r in Hrep; eauto.
    destruct Hrep as (ι & Hι & Hrep).
    unfold ref_flag_atoms_interp in Href; cbn in Href.
    eapply Forall_lookup in Href; eauto.
    destruct o; cbn in Href; try done.
    eapply ref_flag_ptr_interp_le in Href; eauto.
    destruct p as [| [|]]; done.
  Qed.

End copy.
