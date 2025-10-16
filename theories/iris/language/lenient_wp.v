From RichWasm.iris.rules Require Import iris_rules_structural iris_rules_trap.
From RichWasm.iris.language Require Import iris_wp_def logpred.
Import iris.algebra.list.
From iris.proofmode Require Import base tactics classes.
Set Bullet Behavior "Strict Subproofs".

Section lenient_wp.
  Context `{!wasmG Σ}.
  Open Scope bi_scope.

  Section wp_params.
    Variables (s: stuckness) (E: coPset).

    Definition lp_notrap (Φ: logpred) : val -> iProp Σ := 
        λ lv,
        match lv with
        | trapV => False
        | _ => lp_noframe Φ lv
        end.

    Definition lenient_wp (es: expr) (Φ: logpred): iProp Σ :=
        wp s E es (denote_logpred Φ).

    Definition lenient_wp_ctx (es: expr) (Φ: logpred) (i: nat) (lh: lholed) : iProp Σ :=
        wp_wasm_ctx s E es (denote_logpred Φ) i lh.

    Lemma lp_trap_sep (Φ Ψ: logpred) :
        lp_trap (Φ ∗ Ψ) ⊣⊢ lp_trap Φ ∗ lp_trap Ψ.
    Proof.
        reflexivity.
    Qed.

    (* TODO move this to the structural rules file with wp_seq_can_trap_ctx and the rest of those lemmas *)
    Lemma wp_seq_can_trap (Φ Ψ : iris.val -> iProp Σ) (es1 es2 : language.expr wasm_lang) (Φf : datatypes.frame -> iProp Σ) (Φt : iProp Σ) :
        (Ψ trapV ={E}=∗ ⌜False⌝) ∗
        (∀ f, ↪[frame] f ∗ Φt ∗ Φf f -∗ Φ trapV) ∗
        WP es1 @ NotStuck; E {{ w, (⌜w = trapV⌝ ∗ Φt ∨ Ψ w) ∗ ∃ f0, ↪[frame] f0 ∗ Φf f0 }} ∗
        (∀ w (f0: datatypes.frame),
            Ψ w ∗ ↪[frame] f0 ∗ Φf f0 -∗
            WP (of_val w ++ es2) @ s; E {{ v, Φ v }})
        ⊢ WP (es1 ++ es2) @ s; E {{ v, Φ v }}.
    Proof.
        iIntros "(HΨnotrap & Hframetrap & Hes1 & Hes2)".
        iApply wp_wasm_empty_ctx.
        iApply wp_seq_can_trap_ctx_precise; iFrame.
        iIntros (w f0) "(Hw & Hf0 & HΦf)".
        unfold wp_wasm_ctx.
        iIntros (LI Hfill).
        assert (LI = (iris.of_val w ++ es2)).
        {
        cbn in *.
        rewrite app_nil_r in Hfill.
        by destruct (@seq.eqseqP _ LI (iris.of_val w ++ es2)).
        }
        subst LI.
        iApply "Hes2".
        iFrame.
    Qed.

  End wp_params.

  Lemma lenient_wp_seq s E (Φ Ψ: logpred) es1 es2 :
    ⊢ lenient_wp NotStuck E es1 Ψ -∗
      (* trap case: old frame and trap conditions imply the new ones *)
      (∀ f, lp_trap Ψ -∗ lp_fr Ψ f -∗ lp_trap Φ ∗ lp_fr Φ f) -∗
      (* non-trap case: old frame and non-trap conditions imply the new wp *)
      (∀ w f, lp_notrap Ψ w -∗ ↪[frame] f -∗ lp_fr Ψ f -∗ lenient_wp s E (of_val w ++ es2) Φ) -∗
      lenient_wp s E (es1 ++ es2) Φ.
  Proof.
    iIntros "Hes1 Htrapimpl Hes2".
    iApply (wp_seq_can_trap s E _ (lp_notrap Ψ) _ _ Ψ.(lp_fr) (↪[BAIL] ∗ Ψ.(lp_trap))).
    iSplitR; [done |].
    unfold lenient_wp.
    iSplitL "Htrapimpl".
    {
      iIntros (f0) "[Hf0 [[Hbail Htrap] Hfr]]".
      iFrame.
      iApply ("Htrapimpl" with "[$] [$]").
    }
    iSplitR "Hes2".
    - iApply (wp_wand with "[Hes1]").
      + iApply "Hes1".
      + iIntros (v). destruct v; unfold denote_logpred; cbn; iIntros "[Hlog Hfr]";
          try iFrame.
        iLeft.
        by iFrame.
    - iIntros (w f) "(Hnotrap & Hfr & Hfrcond)".
      iApply ("Hes2" with "[$] [$] [$]").
  Qed.

  Definition sigT_apply {A} {P: A -> Type} (f: forall a, P a -> P a) (x: {a: A & P a}) : {a: A & P a} :=
    existT (projT1 x) (f _ (projT2 x)).

  (* This is like composition with val_combine *)
  Definition lp_combine {A} (l: logp A) vs : logp A :=
    {|
      lp_fr := lp_fr l;
      lp_val vs' := lp_val l (seq.cat vs vs');
      lp_trap := lp_trap l;
      lp_br vh := lp_br l (sigT_apply (λ _ vh0, vh_push_const vh0 vs) vh);
      lp_ret lh := lp_ret l (sh_push_const lh vs);
      lp_host tf h cvs sh := lp_host l tf h cvs (llh_push_const sh vs);
    |}.

  Lemma lp_combine_nil Φ lv :
    denote_logpred (lp_combine Φ []) lv ⊣⊢ denote_logpred Φ lv.
  Proof.
    destruct Φ.
    unfold denote_logpred, lp_combine; cbn.
    destruct lv; cbn; auto.
    - f_equiv.
      f_equiv.
      unfold sigT_apply.
      by rewrite vh_push_const_nil.
    - f_equiv.
      by rewrite sh_push_const_nil.
    - f_equiv.
      by rewrite llh_push_const_nil.
  Qed.

  Lemma lp_combine_cons Φ v vs lv :
    denote_logpred (lp_combine Φ (v :: vs)) lv ⊣⊢ denote_logpred (lp_combine (lp_combine Φ [v]) vs) lv.
  Proof.
    destruct Φ.
    unfold denote_logpred, lp_combine, sigT_apply; cbn.
    destruct lv; cbn; auto.
    - f_equiv.
      f_equiv.
      by rewrite -vh_push_const_app.
    - f_equiv.
      by rewrite -sh_push_const_app.
    - f_equiv.
      by rewrite -llh_push_const_app.
  Qed.

  Lemma lp_combine_val:
    forall (Φ: logpred) vs w,
      (denote_logpred Φ) (val_combine (immV vs) w) ⊣⊢ denote_logpred (lp_combine Φ vs) w.
  Proof.
    intros Φ vs w.
    unfold lp_combine, val_combine, denote_logpred, lp_noframe.
    cbn.
    by destruct w.
  Qed.

  Lemma lp_expand Φ w:
    denote_logpred Φ w ⊣⊢ (⌜w = trapV⌝ ∗ ↪[BAIL] ∗ lp_trap Φ ∨ lp_notrap Φ w) ∗ ∃ f, ↪[frame] f ∗ lp_fr Φ f.
  Proof.
    destruct w;
      unfold denote_logpred, lp_noframe;
      iSplit;
      cbn;
      iIntros "[Hpost Hfr]";
      iFrame.
    - by iDestruct "Hpost" as "[[%Hcontra _] | Hpost]".
    - iLeft. by iFrame.
    - iDestruct "Hpost" as "[[_ Hpost] | %Hcontra]"; [iFrame|by exfalso].
    - by iDestruct "Hpost" as "[[%Hcontra _] | Hpost]".
    - by iDestruct "Hpost" as "[[%Hcontra _] | Hpost]".
    - by iDestruct "Hpost" as "[[%Hcontra _] | Hpost]".
  Qed.

  Definition lp_fr_set f i v (Φ : @logpred Σ) : logpred :=
    {|
      lp_fr := λ f', ⌜f' = {| f_locs := seq.set_nth v (f_locs f) i v; f_inst := f_inst f |}⌝;
      lp_val := lp_val Φ;
      lp_trap := lp_trap Φ;
      lp_br := lp_br Φ;
      lp_ret := lp_ret Φ;
      lp_host := lp_host Φ;
    |}.

  Definition lp_with (Ψ: iProp Σ) Φ :=
    {|
      lp_fr := lp_fr Φ;
      lp_val := λ vs, lp_val Φ vs ∗ Ψ;
      lp_trap := lp_trap Φ ∗ Ψ;
      lp_br := λ x, lp_br Φ x ∗ Ψ;
      lp_ret := λ x, lp_ret Φ x ∗ Ψ;
      lp_host := λ ft hf vs lh, lp_host Φ ft hf vs lh ∗ Ψ;
    |}.

  Definition lp_run Φ := lp_with (↪[RUN])%I Φ.

  Lemma lp_with_sep Ψ Φ w :
    denote_logpred Φ w ∗ Ψ ⊣⊢ denote_logpred (lp_with Ψ Φ) w.
  Proof.
    unfold lp_run, denote_logpred.
    cbn.
    iSplit.
    - destruct w; cbn; iIntros "[HΦ Hrun]"; iFrame.
    - destruct w; cbn; try by (iIntros "[HΦ Hrun]"; iFrame).
      iIntros "[[HΦ [Htrap HΨ]] Hf]".
      iFrame.
  Qed.

End lenient_wp.
