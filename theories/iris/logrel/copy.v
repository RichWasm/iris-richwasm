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

End copy.
