From RichWasm.iris.rules Require Import iris_rules_structural iris_rules_trap.
From RichWasm.iris.language Require Import iris_wp_def logpred lenient_wp.
Import iris.algebra.list.
From iris.proofmode Require Import base tactics classes.
Set Bullet Behavior "Strict Subproofs".

Section lwp_structural.
  Context `{!wasmG Σ}.
  Open Scope bi_scope.

  Lemma lenient_wp_nil s E Φ :
    denote_logpred Φ (immV []) ⊢ lenient_wp s E [] Φ.
  Proof.
    iIntros "HΦ".
    rewrite /lenient_wp wp_unfold /wp_pre /=.
    by iFrame.
  Qed.

  Lemma lenient_wp_wand s E es Φ Ψ :
    lp_entails Φ Ψ ->
    lenient_wp s E es Φ ⊢ lenient_wp s E es Ψ.
  Proof.
    unfold lp_entails, lenient_wp.
    intros Himp.
    iIntros "HΦ".
    iApply (wp_wand with "[$]").
    iIntros (v) "HΦv".
    by iApply Himp.
  Qed.

  Lemma lenient_wp_value s E Φ e v :
    IntoVal e v ->
    denote_logpred Φ v ⊢ lenient_wp s E e Φ.
  Proof.
    apply wp_value.
  Qed.

  Lemma lenient_wp_val_cons s E (Φ: logpred) v es :
    lenient_wp NotStuck E es (lp_combine Φ [v])
    ⊢ lenient_wp s E (AI_basic (BI_const v) :: es) Φ.
  Proof.
    iIntros "Hcomb".
    iApply (wp_wand with "[Hcomb]").
    - iApply (wp_val_can_trap_precise _ _ (lp_notrap Φ) _ _ (lp_fr Φ) (lp_trap Φ ∗ ↪[BAIL])).
      iSplitR; [done|].
      unfold lenient_wp.
      iApply (wp_wand with "[Hcomb]").
      iApply "Hcomb".
      iIntros (w) "Hden".
      setoid_rewrite <- lp_combine_val at 1.
      setoid_rewrite -> lp_expand at 1.
      iDestruct "Hden" as "[[(%Hcomb & Hbail & Htrap) | Hnotrap] Hfr]";
        iFrame.
      iLeft.
      iFrame.
      iPureIntro.
      destruct w; vm_compute in Hcomb; congruence.
    - iIntros (w) "[[(%Hcomb & Hbail & Htrap) | Hnotrap] Hfr]";
        rewrite lp_expand; iFrame.
      iLeft; by iFrame.
  Qed.

  Lemma lenient_wp_val_app E (Φ: logpred) vs es vs' :
    iris.to_val vs = Some (immV vs') ->
    lenient_wp NotStuck E es (lp_combine Φ vs')
    ⊢ lenient_wp NotStuck E (vs ++ es) Φ.
  Proof.
    revert vs' es Φ.
    induction vs; intros vs' es Φ.
    - iIntros (Hvs) "Hcomb".
      cbn in Hvs; inversion Hvs; subst vs'.
      rewrite app_nil_l.
      iApply (lenient_wp_wand with "[$]").
      unfold lp_entails; intros; cbn.
      by rewrite lp_combine_nil.
    - iIntros (Hvs) "Hcomb".
      apply to_val_is_immV in Hvs.
      cbn in *.
      symmetry in Hvs.
      apply map_eq_cons in Hvs.
      destruct Hvs as (a' & vs'' & Hvs' & Ha & Hxs).
      subst.
      iApply lenient_wp_val_cons.
      iApply IHvs.
      instantiate (1:= vs'').
      + replace @map with @seq.map by reflexivity.
        fold (v_to_e_list vs'').
        fold (iris.of_val (immV vs'')).
        apply iris.to_of_val.
      + iApply (lenient_wp_wand with "[$]").
        unfold lp_entails; intros lv.
        by rewrite lp_combine_cons.
  Qed.

  Lemma lenient_wp_val_app' E (Φ: logpred) vs es :
    lenient_wp NotStuck E es (lp_combine Φ vs)
    ⊢ lenient_wp NotStuck E (v_to_e_list vs ++ es) Φ.
  Proof.
    iIntros "Hcomb".
    iApply lenient_wp_val_app.
    - fold (iris.of_val (immV vs)).
      by apply iris.to_of_val.
    - done.
  Qed.

  Lemma lenient_wp_if_true s E Φ c tf (f: datatypes.frame) es1 es2:
    c <> Wasm_int.int_zero i32m ->
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷(↪[frame] f -∗ ↪[RUN] -∗ lenient_wp s E [AI_basic (BI_block tf es1)] Φ)
    ⊢ lenient_wp s E [AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_if tf es1 es2)] Φ.
  Proof.
    iIntros (Hc) "(Hf & Hrun & Hwp)".
    by iApply (wp_if_true with "[$] [$] [$]").
  Qed.

  Lemma lenient_wp_if_false s E Φ c tf (f: datatypes.frame) es1 es2:
    c = Wasm_int.int_zero i32m ->
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷(↪[frame] f -∗ ↪[RUN] -∗ lenient_wp s E [AI_basic (BI_block tf es2)] Φ)
    ⊢ lenient_wp s E [AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_if tf es1 es2)] Φ.
  Proof.
    iIntros (Hc) "(Hf & Hrun & Hwp)".
    by iApply (wp_if_false with "[$] [$] [$]").
  Qed.

  Lemma lenient_wp_seq s E (Φ Ψ: logpred) es1 es2 :
    lenient_wp NotStuck E es1 Ψ ∗
    (* trap case: old frame and trap conditions imply the new ones *)
    (∀ f, lp_trap Ψ ∗ lp_fr Ψ f -∗ lp_trap Φ ∗ lp_fr Φ f) ∗
    (* non-trap case: old frame and non-trap conditions imply the new wp *)
    (∀ w f, lp_notrap Ψ w ∗ ↪[frame] f ∗ lp_fr Ψ f -∗ lenient_wp s E (of_val w ++ es2) Φ)
    ⊢ lenient_wp s E (es1 ++ es2) Φ.
  Proof.
    iIntros "(Hes1 & Htrapimpl & Hes2)".
    iApply (wp_seq_can_trap s E _ (lp_notrap Ψ) _ _ Ψ.(lp_fr) (↪[BAIL] ∗ Ψ.(lp_trap))).
    iSplitR; [done |].
    unfold lenient_wp.
    iSplitL "Htrapimpl".
    {
      iIntros (f0) "[Hf0 [[Hbail Htrap] Hfr]]".
      iFrame.
      iApply "Htrapimpl".
      iFrame.
    }
    iSplitR "Hes2".
    - iApply (wp_wand with "[Hes1]").
      + iApply "Hes1".
      + iIntros (v). destruct v; unfold denote_logpred; cbn; iIntros "[Hlog Hfr]";
          try iFrame.
        iLeft.
        by iFrame.
    - iIntros (w f) "(Hnotrap & Hfr & Hfrcond)".
      iApply "Hes2".
      iFrame.
  Qed.


End lwp_structural.
