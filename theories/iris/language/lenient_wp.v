From RWasm.iris.rules Require Import iris_rules_structural iris_rules_trap.
From RWasm.iris.language Require Import iris_wp_def logpred.
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
        Locate "CTX_EMPTY".
        Search (LH_base nil nil) wp_wasm_ctx.
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
    lenient_wp NotStuck E es1 Ψ ∗
    (* trap case: old frame and trap conditions imply the new ones *)
    (∀ f, lp_trap Ψ ∗ lp_fr Ψ f -∗ lp_trap Φ ∗ lp_fr Φ f) ∗
    (* non-trap case: old frame and non-trap conditions imply the new wp *)
    (∀ w f, lp_notrap Ψ w ∗ ↪[frame] f ∗ lp_fr Ψ f -∗ lenient_wp s E (of_val w ++ es2) Φ)
    ⊢ lenient_wp s E (es1 ++ es2) (Φ).
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

End lenient_wp.
