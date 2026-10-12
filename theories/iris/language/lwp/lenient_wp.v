From RichWasm.iris.rules Require Import iris_rules_structural iris_rules_trap.
From RichWasm.iris.language Require Import iris_wp_def logpred.
Import iris.algebra.list.
From iris.proofmode Require Import base proofmode classes.
Set Bullet Behavior "Strict Subproofs".

Section lenient_wp.
  Context `{!wasmG Σ}.
  Open Scope bi_scope.

  Section wp_params.
    Variables (s: stuckness) (E: coPset).

    Definition lp_notrap (Φ: logpred) f : val -> iProp Σ := 
      λ lv,
        match lv with
        | trapV => False
        | _ => lp_noframe Φ f lv
        end.

    Definition lenient_wp (es: expr) (Φ: logpred): iProp Σ :=
        wp s E es (denote_logpred Φ).

    Global Instance lenient_wp_ne es : NonExpansive (lenient_wp es).
    Proof.
      unfold lenient_wp.
      intros n Φ Ψ (Hfr_inv & Hval & Htrap & Hbr & Hret & Hhost).
      unfold lenient_wp.
      eapply wp_ne; intros sv.
      by eapply denote_logpred_ne.
    Qed.

    Definition lenient_wp_ctx (es: expr) (Φ: logpred) (i: nat) (lh: lholed) : iProp Σ :=
        wp_wasm_ctx s E es (denote_logpred Φ) i lh.

  End wp_params.

  Lemma lenient_wp_seq s E (Φ Ψ: logpred) es1 es2 :
    ⊢ lenient_wp NotStuck E es1 Ψ -∗
      (* trap case: old frame and trap conditions imply the new ones *)
      (∀ f, lp_trap Ψ -∗ lp_fr_inv Ψ f -∗ lp_trap Φ ∗ lp_fr_inv Φ f) -∗
      (* non-trap case: old frame and non-trap conditions imply the new wp *)
      (∀ w f, lp_notrap Ψ f w -∗ ↪[frame] f -∗ lp_fr_inv Ψ f -∗ lenient_wp s E (of_val w ++ es2) Φ) -∗
      lenient_wp s E (es1 ++ es2) Φ.
  Proof.
    iIntros "Hes1 Htrapimpl Hes2".
    iApply (wp_seq_can_trap s E
              (denote_logpred Φ)
              (lp_notrap Ψ)
              Ψ.(lp_fr_inv)
              (↪[BAIL] ∗ Ψ.(lp_trap))
           with "[] [Htrapimpl] [Hes1]").
    - by iIntros "%f Hnotraptrap".
    - iIntros (f) "(Hf & [Hbail Htrap] & Hinv)".
      unfold denote_logpred; cbn.
      iExists f.
      iFrame.
      rewrite bi.sep_comm.
      iApply ("Htrapimpl" with "[$] [$]").
    - iApply (wp_wand with "[Hes1]"); first done.
      iIntros (v). 
      unfold denote_logpred; cbn.
      iIntros "(%f' & Hfr & Hfrinv & Hlog)".
      iExists f'; iFrame.
      destruct v; iFrame.
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
      lp_fr_inv := lp_fr_inv l;
      lp_val fr vs' := lp_val l fr (seq.cat vs vs');
      lp_trap := lp_trap l;
      lp_br fr n vh := lp_br l fr n (vh_push_const vh vs);
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
    denote_logpred Φ w ⊣⊢
      ∃ f, ↪[frame] f ∗ lp_fr_inv Φ f ∗ (⌜w = trapV⌝ ∗ ↪[BAIL] ∗ lp_trap Φ ∨ lp_notrap Φ f w).
  Proof.
    unfold denote_logpred.
    iSplit;
      cbn;
      iIntros "(%f & Hfr & Hfrinv & Hpost)";
      iFrame.
    - destruct w; cbn;
        solve [iRight; by iFrame | iLeft; by iFrame].
    - iDestruct "Hpost" as "[[-> Hpost] | Htrap]".
      + iFrame.
      + destruct w; by iFrame.
  Qed.

  Definition lp_with (Ψ: iProp Σ) Φ :=
    {|
      lp_fr_inv := lp_fr_inv Φ;
      lp_val := λ fr vs, lp_val Φ fr vs ∗ Ψ;
      lp_trap := lp_trap Φ ∗ Ψ;
      lp_br := λ fr n x, lp_br Φ fr n x ∗ Ψ;
      lp_ret := λ x, lp_ret Φ x ∗ Ψ;
      lp_host := λ ft hf vs lh, lp_host Φ ft hf vs lh ∗ Ψ;
    |}.

  Lemma lp_with_sep Ψ Φ w :
    denote_logpred (lp_with Ψ Φ) w ⊣⊢ denote_logpred Φ w ∗ Ψ.
  Proof.
    unfold denote_logpred.
    cbn.
    iSplit.
    - destruct w; cbn;
        iIntros "(%f' & Hf & Hfinv & Hfr & Hres & HΨ)";
        by iFrame.
    - destruct w; cbn; iIntros "[HΦ Hrun]"; iFrame.
  Qed.

End lenient_wp.
