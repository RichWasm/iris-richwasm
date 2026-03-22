From Stdlib Require Import ZArith.
From stdpp Require Import base list.

From iris.proofmode Require Import base proofmode classes.
From RichWasm.wasm Require Import operations.

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

  Lemma value_interp_i32 se os :
    value_interp rti sr se type_i32 (SAtoms os) -∗ ∃ n, ⌜os = [I32A n]⌝.
  Admitted.

  Lemma values_interp_nil se os :
    values_interp rti sr se [] os -∗ ⌜os = []⌝.
  Proof.
    iIntros "Hos".
    iDestruct "Hos" as "(%oss & -> & Hoss)".
    by iDestruct (big_sepL2_nil_inv_l with "Hoss") as "->".
  Qed.

  Lemma values_interp_cons se τ τs os :
    values_interp rti sr se (τ :: τs) os -∗
    ∃ os1 os2,
      ⌜os = os1 ++ os2⌝ ∗
      value_interp rti sr se τ (SAtoms os1) ∗
      values_interp rti sr se τs os2.
  Proof.
    iIntros "Hos".
    iDestruct "Hos" as "(%oss & -> & Hoss)".
    iDestruct (big_sepL2_cons_inv_l with "Hoss") as "(%os & %oss' & -> & Hos & Hoss')".
    iExists os, (concat oss').
    rewrite concat_cons.
    by iFrame.
  Qed.

  Lemma values_interp_app se τs1 τs2 os :
    values_interp rti sr se (τs1 ++ τs2) os -∗
    ∃ os1 os2,
      ⌜os = os1 ++ os2⌝ ∗
      values_interp rti sr se τs1 os1 ∗
      values_interp rti sr se τs2 os2.
  Proof.
  Admitted.

  Lemma atoms_interp_nil vs :
    atoms_interp [] vs -∗ ⌜vs = []⌝.
  Proof.
    iIntros "Hvs".
    by iDestruct (big_sepL2_nil_inv_l with "Hvs") as "->".
  Qed.

  Lemma atoms_interp_cons o os vs :
    atoms_interp (o :: os) vs -∗
    ∃ v vs',
      ⌜vs = v :: vs'⌝ ∗
      atom_interp o v ∗
      atoms_interp os vs'.
  Proof.
    iIntros "Hvs".
    iDestruct (big_sepL2_cons_inv_l with "Hvs") as "(%v & %vs' & -> & Hv & Hvs')".
    iExists v, vs'.
    by iFrame.
  Qed.

  (* There's gotta be a clearner way to do it *)
  Lemma atoms_interp_app os1 os2 vs :
    atoms_interp (os1 ++ os2) vs -∗
    ∃ vs1 vs2, ⌜vs = vs1 ++ vs2⌝ ∗ atoms_interp os1 vs1 ∗ atoms_interp os2 vs2.
  Proof.
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

  Lemma frame_interp_wl_interp se F L WL inst fr :
    frame_interp rti sr se L WL inst fr -∗
    ⌜wl_interp (fe_wlocal_offset (fe_of_context F)) WL fr⌝.
  Proof.
  Admitted.

  Lemma translate_types_comp_interp_length F τs ts se os :
    sem_env_interp F se ->
    prelude.translate_types F.(fc_type_vars) τs = Some ts ->
    values_interp rti sr se τs os -∗
    ⌜length os = length ts⌝.
  Proof.
    intros. iIntros "Hval".
    cbn.
  Admitted.

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

  Lemma translate_types_sem_interp_length se τs ts os :
    translate_types se τs = Some ts ->
    values_interp rti sr se τs os -∗
    ⌜length os = length ts⌝.
  Proof.
    generalize dependent se; generalize dependent ts; generalize dependent os.
    induction τs.
    - intros.
      iIntros  "(%oss & %ossconc & Hval)".
      iPoseProof (big_sepL2_length with "[$Hval]") as "%osslen".
      simpl in osslen; destruct oss; [ | inversion osslen].
      simpl in ossconc; subst; iPureIntro.
      cbn in H.
      inversion H; auto.
    - intros.
      rewrite separate1.
      iIntros "Hval".
      iPoseProof (values_interp_app with "[$Hval]") as "(%os1 & %os2 & %Hoslen & Ha & Hτs)".
      rewrite values_interp_one_eq.

      unfold translate_types in H.
      rewrite fmap_Some in H.
      destruct H as (tss & Hmapm & Htsconcat).
      simpl in Hmapm.
      apply bind_Some in Hmapm.
      destruct Hmapm as (ts1 & Htranslate & Hmapτs).
      set (asdf := translate_types se τs).
      assert (H: asdf = Some ts). {
        admit.
      }
      (* NOTE: I need to turn Hmapτs back into translate_types se τs = Some _. Or get it out of
         there at least. Not rn. For now I'll just show stuff about a, aka that os1 = ts1. *)

      subst.
      (* induction on a? I need to prove that length os1 = length ts1, and that'll
       depend on what sort of instruction a is. There's some annoying fixpoint here and there. *)


  Admitted.

  Lemma translate_types_comp_sem F τs ts se :
    sem_env_interp F se ->
    prelude.translate_types F.(fc_type_vars) τs = Some ts ->
    @translate_types Σ se τs = Some ts.
  Admitted.

  Lemma labels_interp_cons se inst wl F L B τs ts Φ :
    sem_env_interp F se ->
    prelude.translate_types (fc_type_vars F) τs = Some ts ->
    □ (∀ fr' vs',
       (frame_interp rti sr se L wl inst fr' ∗
        ∃ os' θ0, values_interp rti sr se τs os' ∗ atoms_interp os' vs' ∗ rt_token rti sr θ0) -∗
       Φ fr' vs') -∗
    labels_interp rti sr se inst wl F.(fc_labels) B -∗
    labels_interp rti sr se inst wl ((τs, L) :: F.(fc_labels)) ((length ts, Φ) :: B).
  Proof.
    iIntros (Hse Hts) "#HΦ Hlabels".
    unfold labels_interp.
    unfold const.
    rewrite big_sepL2_cons.
    iSplitL "HΦ".
    - iSplitR.
      + by erewrite translate_types_comp_sem.
      + iIntros (fr vs os θ) "!> Hvs Hos Hframe Hrti". iApply "HΦ". iFrame.
    - done.
  Qed.

(* This is a copy of values_interp_cons
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
  Qed. *)
  Lemma atoms_interp_length os vs :
    ⊢ atoms_interp os vs -∗ ⌜length os = length vs⌝.
  Proof.
    iApply big_sepL2_length.
  Qed.

  Lemma atoms_interp_one_inv o vs :
    atoms_interp [o] vs ⊣⊢ ∃ v, ⌜vs = [v]⌝ ∗ atom_interp o v.
  Proof.
    iSplit.
    - iIntros "Hvs".
      iPoseProof (atoms_interp_cons with "Hvs") as (v vs' Heq) "[Hv Hnil]".
      iPoseProof (atoms_interp_nil with "Hnil") as "->".
      iExists v; auto.
    - iIntros "(%v & -> & Hv)".
      cbn; auto.
  Qed.

  Lemma value_interp_ref_sz se κ μ τ os :
    ⊢ value_interp rti sr se (RefT κ μ τ) (SAtoms os) -∗ ⌜length os = 1⌝.
  Proof.
    iIntros "Hv".
    rewrite value_interp_eq; cbn.
    iDestruct "Hv" as "(%κ0 & %Heval & Hkind & Hmem)".
    destruct μ as [| [|]]; auto.
    - iDestruct "Hmem" as "(%ℓ & %fs & %ws & %Hos & _)".
      by inversion Hos.
    - iDestruct "Hmem" as "(%ℓ & %fs & %Hos & _)".
      by inversion Hos.
  Qed.

  Lemma rep_ref_kind_ptr F κ μ τ ρ χ δ :
    has_kind F (RefT κ μ τ) (VALTYPE ρ χ δ) ->
    ρ = AtomR PtrR /\
    exists χ', κ = VALTYPE (AtomR PtrR) χ' ExDrop.
  Proof.
    intros Hkind.
    remember (RefT κ μ τ) as ref.
    remember (VALTYPE ρ χ δ) as val.
    revert Heqval Heqref.
    revert ρ χ δ.
    induction Hkind using has_kind_ind'; intros; try congruence.
    - subst κ0.
      split; try congruence.
      inversion Heqref; eauto.
    - subst κ0.
      split; try congruence.
      inversion Heqref; eauto.
    - subst κ'.
      inversion H; subst; eapply IHHkind; eauto.
  Qed.

End common.
