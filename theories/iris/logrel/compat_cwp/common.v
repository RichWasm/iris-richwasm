From Stdlib Require Import ZArith.
From stdpp Require Import base list.

From iris.proofmode Require Import base tactics classes.
From Wasm Require Import operations.
From Wasm.iris.logrel Require Import iris_fundamental_composition.

From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import prelude codegen instruction module.
From RichWasm.iris Require Import autowp memory util wp_codegen.
From RichWasm.iris.language Require Import cwp logpred.
From RichWasm.iris.logrel Require Import relations_cwp fundamental_kinding.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Ltac clear_nils :=
  repeat rewrite <- ?app_assoc, -> ?app_nil_l, -> ?app_nil_r in *.

Section common.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma values_interp_app se τs1 τs2 os :
    values_interp rti sr se (τs1 ++ τs2) os -∗
    ∃ os1 os2,
      ⌜os = os1 ++ os2⌝ ∗
      values_interp rti sr se τs1 os1 ∗
      values_interp rti sr se τs2 os2.
  Proof.
  Admitted.

  (* There's gotta be a clearner way to do it *)
  Lemma atoms_interp_app os1 os2 vs :
    atoms_interp (os1 ++ os2) vs -∗
    ∃ vs1 vs2, ⌜vs = vs1 ++ vs2⌝ ∗ atoms_interp os1 vs1 ∗ atoms_interp os2 vs2.
  Proof.
    Search atoms_interp.
    generalize dependent os1; generalize dependent os2.
    induction vs; intros.
    - iIntros "Hat".
      iExists []; iExists [].
      iPoseProof (big_sepL2_length with "[$Hat]") as "%Hlens".
      simpl in Hlens. apply nil_length_inv in Hlens.
      destruct os1, os2; try inversion Hlens. clear_nils. auto.
    - iIntros "Hat".
      destruct os1.
      + clear_nils.
        destruct os2.
        * iPoseProof (big_sepL2_length with "[$Hat]") as "%Hlens".
          inversion Hlens.
        * iEval (unfold atoms_interp) in "Hat".
          iDestruct (big_sepL2_cons with "Hat") as "[Ha Hhyp]".
          specialize (IHvs os2 []).
          iPoseProof IHvs as "IHvs".
          clear_nils.
          iSpecialize ("IHvs" with "Hhyp").
          iDestruct "IHvs" as "(%vs1 & %vs2 & %Hlen & Hvs1 & Hvs2)".
          destruct vs1; iSimpl in "Hvs1"; auto.
          iExists []; iExists (a :: vs2).
          simpl; iFrame. iPureIntro; clear_nils; subst; auto.
      + rewrite <- app_comm_cons.
        iEval (unfold atoms_interp) in "Hat".
        iDestruct (big_sepL2_cons with "Hat") as "[Ha Hhyp]".
        specialize (IHvs os2 os1).
        iPoseProof IHvs as "IHvs".
        iSpecialize ("IHvs" with "Hhyp").
        iDestruct "IHvs" as "(%vs1 & %vs2 & %Hlen & Hvs1 & Hvs2)".
        iExists (a :: vs1); iExists vs2.
        iFrame. iPureIntro; simpl. subst. auto.
  Qed.

  Lemma translate_types_comp_interp_length F τs ts se os :
    sem_env_interp F se ->
    prelude.translate_types F.(fc_type_vars) τs = Some ts ->
    values_interp rti sr se τs os -∗
    ⌜length os = length ts⌝.
  Admitted.

  Lemma translate_types_sem_interp_length se τs ts os :
    translate_types se τs = Some ts ->
    values_interp rti sr se τs os -∗
    ⌜length os = length ts⌝.
  Admitted.

  Lemma translate_types_comp_sem F τs ts se :
    sem_env_interp F se ->
    prelude.translate_types F.(fc_type_vars) τs = Some ts ->
    @translate_types Σ se τs = Some ts.
  Admitted.

  Lemma values_interp_cons_inv se τ τs os :
    ⊢ values_interp rti sr se (τ :: τs) os -∗
      ∃ os1 os2,
        ⌜os = os1 ++ os2⌝ ∗
        value_interp rti sr se τ (SAtoms os1) ∗
        values_interp rti sr se τs os2.
  Proof.
    iIntros "(%vss & %Hconcat & Hval)".
    rewrite big_sepL2_cons_inv_l.
    iDestruct "Hval" as "(%vs1 & %vss2 & %Hvss & Hvs1 & Hvss2)".
    iExists vs1, (concat vss2).
    iSplit; first by rewrite Hconcat Hvss.
    iSplitL "Hvs1".
    - done.
    - iExists _.
      iSplit; done.
  Qed.

  Lemma values_interp_one_eq se τ os :
    values_interp rti sr se [τ] os ⊣⊢ value_interp rti sr se τ (SAtoms os).
  Proof.
    unfold values_interp.
    iSplit.
    - iIntros "(%vss & -> & H)".
      rewrite big_sepL2_cons_inv_l.
      iDestruct "H" as "(%vs & %lnil & -> & Hv & Hnils)".
      rewrite big_sepL2_nil_inv_l.
      iDestruct "Hnils" as "->".
      cbn.
      by rewrite app_nil_r.
    - iIntros "H".
      iExists [os].
      iSplit.
      + cbn. by rewrite app_nil_r.
      + iApply big_sepL2_cons.
        iFrame.
        by iApply big_sepL2_nil.
  Qed.

End common.
