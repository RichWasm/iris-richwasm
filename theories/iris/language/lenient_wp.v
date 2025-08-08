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

  (*
  Definition has_a_frame (Φ: iProp Σ) :=
    ∃ Φ' (f: datatypes.frame), □(Φ ∗-∗ Φ' ∗ ↪[frame] f).

  Lemma wp_seq_can_trap' (Φ Ψ : iris.val -> iProp Σ) (Ψt: iProp Σ) (es1 es2 : language.expr wasm_lang) f :
    ↪[frame] f ∗
    (∀ w, has_a_frame (Ψ w)) ∗
    (∀ w, has_a_frame (Φ w)) ∗
    (((Ψ trapV ={E}=∗ ⌜False⌝)) ∗
     (Ψt -∗ Φ trapV) ∗
     (WP es1 @ NotStuck; E {{ w, (⌜w = trapV⌝ ∗ Ψt) ∨ Ψ w}}) ∗
     ∀ w, Ψ w -∗ WP (iris.of_val w ++ es2) @ s; E {{ v, Φ v }})%I
     ⊢ WP (es1 ++ es2) @ s; E {{ v, Φ v }}.
  Proof.
    iLöb as "IH" forall (Φ Ψ Ψt es1 es2 f).
    iIntros "(Hf & HfΨ & HfΦ & Hnotrap & Httrap & Hes1 & Hes2)".
    repeat rewrite wp_unfold /wp_pre /=.
    destruct (iris.to_val es1) as [vs|] eqn:Hes1tov.
    {
      iMod ("Hes1").
      iDestruct "Hes1" as "[[-> Hes1] | Hes1]".
      {
        apply to_val_trap_is_singleton in Hes1tov as ->.
        destruct es2; cycle 1.
        {
          iSpecialize ("Httrap" with "Hes1").
          iAssert (has_a_frame (Φ trapV)) with "[HfΦ]" as "HfΦ'".
          iApply "HfΦ".
          iDestruct "HfΦ'" as (Φ' fr) "#Hsplit".
          iAssert (Φ' ∗ ↪[frame] fr) with "[Httrap]" as "[HΦ' Hfr]".
          by iApply "Hsplit".
          iApply (wp_wand _ _ _ (λ v, Φ' ∗ ↪[frame] fr) with "[HΦ' Hfr]").
          change [AI_trap] with ([] ++ [AI_trap]).
          rewrite -app_assoc.
          iApply (wp_trap with "[HΦ'] [$Hfr]").
          done.
          iFrame.
          done.
          iApply "Hsplit" in "Httrap".


          iApply "Hes2".
          assert (iris.to_val ([AI_trap] ++ a :: es2) = None) as Hnone
              by (rewrite -(app_nil_l [AI_trap]) -app_assoc; apply to_val_not_trap_interweave; auto).
          rewrite /has_a_frame.
          iRewrite "HfΦ".
          Search wp AI_trap.
          eapply wp_trap.
          rewrite Hnone.
          congruence.

        }
          eapply to_val_None_lfilled in Hnone; [|eauto].
        
      unfold iris
      iDestruct H

      eapply lfilled_to_val_app in Hes1tov as HH;eauto.
      destruct HH as [vs' [Hvs' Hfilled']].
      unfold iris_wp_def.to_val in Hvs'.
    rewrite Hvs'.
      apply to_val_trap_is_singleton in Hvs'.
      *)

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
