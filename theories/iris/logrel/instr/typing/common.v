From Stdlib Require Export ZArith.

From stdpp Require Export base list.

Require Export RecordUpdate.RecordUpdate.

From iris.proofmode Require Export base proofmode classes.

From RichWasm.named_props Require Export named_props custom_syntax.
From RichWasm.wasm Require Export operations.
From RichWasm Require Export layout syntax typing.
From RichWasm.compiler Require Export prelude codegen instruction module.
From RichWasm.iris Require Export autowp memory util wp_codegen.
From RichWasm.iris.language Require Export cwp logpred.
Require Export RichWasm.iris.logrel.instr.

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
  Proof.
    iIntros "Hval".
    iPoseProof (value_interp_eq with "Hval") as "Hval".
    iEval (cbn) in "Hval".
    iDestruct "Hval" as "(%κ & %Hκ & Rest)".
    destruct κ; auto.
    iDestruct "Rest" as "((%Hareps & %Href) & _)".
    iPureIntro.
    inversion Hκ; subst; clear Hκ.
    destruct Hareps as (os' & Htemp & Harep).
    inversion Htemp; subst os'; clear Htemp.
    apply Forall2_length in Harep as Hlen.
    destruct os as [|o [|os]]; try (inversion Hlen).
    apply Forall2_cons_1 in Harep as [Harep _].
    cbn in Harep.
    destruct o; try (inversion Harep).
    exists n; auto.
  Qed.

  Lemma values_interp_nil_l se os :
    values_interp rti sr se [] os -∗ ⌜os = []⌝.
  Proof.
    iIntros "Hos".
    iDestruct "Hos" as "(%oss & -> & Hoss)".
    by iDestruct (big_sepL2_nil_inv_l with "Hoss") as "->".
  Qed.

  Lemma values_interp_cons_l se τ τs os :
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

  Lemma values_interp_app_l se τs1 τs2 os :
    values_interp rti sr se (τs1 ++ τs2) os -∗
    ∃ os1 os2,
      ⌜os = os1 ++ os2⌝ ∗
      values_interp rti sr se τs1 os1 ∗
      values_interp rti sr se τs2 os2.
  Proof.
  Admitted.

  Lemma atoms_interp_nil_l vs :
    atoms_interp [] vs -∗ ⌜vs = []⌝.
  Proof.
    iIntros "Hvs".
    by iDestruct (big_sepL2_nil_inv_l with "Hvs") as "->".
  Qed.

  Lemma atoms_interp_cons_l o os vs :
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

  Lemma atoms_interp_cons o os v vs:
    atoms_interp (o :: os) (v :: vs) ⊣⊢ atom_interp o v ∗ atoms_interp os vs.
  Proof.
    done.
  Qed.

  (* There's gotta be a clearner way to do it *)
  Lemma atoms_interp_app_l os1 os2 vs :
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

  Lemma frame_interp_wl_interp se F L WL fr :
    frame_interp rti sr se L WL fr -∗
    ⌜wl_interp (fe_wlocal_offset (fe_of_context F)) WL fr⌝.
  Proof.
    iIntros "Hframe".
    iDestruct "Hframe" as
      "(%oss_L & %vss_L & %vs_WL & %Hfr & %Hresult & Hatom & Hval)".
    unfold wl_interp.

    (* This is my best guess at the exists given Hfr and Hresult. Should be right *)
    iExists (concat vss_L). iExists vs_WL. iExists [].
    iSplit; [|iSplit]; clear_nils; subst; auto.

    iEval (cbn).
    iEval (cbn) in "Hval".
    iPoseProof (big_sepL2_length with "[$Hval]") as "%HlenossL".
    iPoseProof (big_sepL2_length with "[$Hatom]") as "%HlenvssL".
    unfold atoms_interp; unfold value_interp; destruct F; cbn.

    (* Currently unprovable bc there's nothing to relate F fc_locals to *)

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
      iPoseProof (values_interp_app_l with "[$Hval]") as "(%os1 & %os2 & %Hoslen & Ha & Hτs)".
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

  Lemma labels_interp_cons se fr wl lmask F L B τs ts Φ :
    sem_env_interp F se ->
    prelude.translate_types F.(fc_type_vars) τs = Some ts ->
    □ (∀ fr' vs',
       (⌜frame_rel lmask fr fr'⌝ ∗ frame_interp rti sr se L wl fr' ∗
          (∃ os', values_interp rti sr se τs os' ∗ atoms_interp os' vs') ∗
          (∃ θ0, rt_token rti sr θ0)) -∗
       Φ fr' vs') -∗
    labels_interp rti sr se fr wl lmask F.(fc_labels) B -∗
    labels_interp rti sr se fr wl lmask ((τs, L) :: F.(fc_labels)) ((length ts, Φ) :: B).
  Proof.
    iIntros (Hse Hts) "#HΦ Hlabels".
    unfold labels_interp.
    unfold const.
    rewrite big_sepL2_cons.
    iSplitL "HΦ".
    - iSplitR.
      + by erewrite translate_types_comp_sem.
      + iIntros (fr' vs os θ) "!> %Hlmask Hvs Hos Hframe Hrti".
        iApply "HΦ".
        by iFrame.
    - done.
  Qed.

  Lemma mask_locs_eq_trans lmask fr1 fr2 fr3 :
    mask_locs_eq lmask fr1 fr2 ->
    mask_locs_eq lmask fr2 fr3 ->
    mask_locs_eq lmask fr1 fr3.
  Proof.
    intros H12 H23 i Hi.
    apply H12 in Hi as Hi12.
    apply H23 in Hi as Hi23.
    by rewrite Hi12.
  Qed.

  Lemma frame_rel_trans lmask fr1 fr2 fr3 :
    frame_rel lmask fr1 fr2 ->
    frame_rel lmask fr2 fr3 ->
    frame_rel lmask fr1 fr3.
  Proof.
    intros [H12_locs H12_inst] [H23_locs H23_inst].
    split.
    - by eapply mask_locs_eq_trans.
    - by rewrite H12_inst.
  Qed.

  Lemma labels_interp_trans se wl fr fr' lmask labels B :
    frame_rel lmask fr fr' ->
    labels_interp rti sr se fr wl lmask labels B -∗
    labels_interp rti sr se fr' wl lmask labels B.
  Proof.
    iIntros (Heq) "#Hlabels".
    iApply (big_sepL2_mono with "[$]").
    iIntros (? [τs L] [n b] Hk_labels Hk_B) "[#Hlen #HP]".
    iFrame "#".
    iModIntro.
    iIntros (?????) "Hframe Hrt Hvs Hos".
    iApply ("HP" with "[] [$] [$] [$] [$]").
    iPureIntro.
    by eapply frame_rel_trans.
  Qed.

  Lemma wlmask_mono fe wl wl' :
    length wl <= length wl' ->
    ∀ i, wlmask fe wl i → wlmask fe wl' i.
  Proof.
    intros Hlen i [Hlo Hhi].
    split; first done.
    lia.
  Qed.

  Lemma frame_rel_mask_mono lmask lmask' fr fr' :
    (forall i, lmask' i -> lmask i) ->
    frame_rel lmask fr fr' ->
    frame_rel lmask' fr fr'.
  Proof.
    intros Hmask' [Hmask Hinst].
    split; last done.
    intros i Hi.
    apply Hmask.
    by apply Hmask'.
  Qed.

  Lemma frame_rel_wlmask_mono fe wl wl' fr fr' :
    length wl <= length wl' ->
    frame_rel (wlmask fe wl') fr fr' ->
    frame_rel (wlmask fe wl) fr fr'.
  Proof.
    intros Hlen Hrel.
    eapply frame_rel_mask_mono; last done.
    intros i [Hlo Hhi].
    split; first done.
    lia.
  Qed.

  Lemma labels_interp_mono se fr fr' wl lmask lmask' labels B :
    frame_rel lmask fr fr' ->
    (forall i, lmask i -> lmask' i) ->
    labels_interp rti sr se fr wl lmask labels B -∗
    labels_interp rti sr se fr' wl lmask' labels B.
  Proof.
    iIntros (Hrel Hmask) "#Hlabels".
    iApply big_sepL2_mono; last done.
    iIntros (? [τs L] [n b] Hk_labels Hk_B) "[Hlen #HP]".
    iFrame.
    iModIntro.
    iIntros (?????) "Hframe Hrt Hvs Hos".
    iApply ("HP" with "[] [$] [$] [$] [$]").
    iPureIntro.
    eapply frame_rel_trans.
    - exact Hrel.
    - by eapply frame_rel_mask_mono.
  Qed.

  Lemma fe_of_context_labels F f :
    fe_of_context F = fe_of_context (F <| fc_labels ::= f |>).
  Proof.
    done.
  Qed.

  Lemma frame_rel_mask_trans_combine lmask1 lmask2 fr1 fr2 fr3:
    frame_rel lmask1 fr1 fr2 ->
    frame_rel lmask2 fr2 fr3 ->
    frame_rel (λ i, lmask1 i ∧ lmask2 i) fr1 fr3.
  Proof.
    intros fr12 fr23.
    eapply frame_rel_trans;
      (eapply frame_rel_mask_mono; last done; by intros i [H1 H2]).
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
      iPoseProof (atoms_interp_cons_l with "Hvs") as (v vs' Heq) "[Hv Hnil]".
      iPoseProof (atoms_interp_nil_l with "Hnil") as "->".
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


  Lemma forall2_lookup_same {A B} (ls ls' : list A) (idxs : list B) (xs : list A) (j_excl : nat) (f: B -> nat) :
    (∀ j : B, f j ≠ j_excl → ls' !! f j = ls !! f j) ->
    Forall (λ i, f i ≠ j_excl) idxs ->
    Forall2 (λ (i : B) (v : A), ls  !! f i = Some v) idxs xs ->
    Forall2 (λ (i : B) (v : A), ls' !! f i = Some v) idxs xs.
  Proof.
    intros Hsame Hnotin Hf.
    induction Hf.
    - constructor.
    - inversion Hnotin; subst.
      constructor.
      + rewrite Hsame; auto.
      + apply IHHf; auto.
  Qed.

  Lemma seq_forall_leq base len :
    Forall (λ i, i < base + len) (seq base len).
  Proof.
    rewrite Forall_seq.
    intros j Hj.
    lia.
  Qed.

  Lemma map_seq_forall_localidx_leq base len :
    Forall (λ i : prelude.W.localidx, localimm i < base + len)
      (map prelude.W.Mk_localidx (seq base len)).
  Proof.
    apply Forall_map.
    apply seq_forall_leq.
  Qed.

  Lemma map_seq_forall_localidx_neq base len :
    Forall (λ i : prelude.W.localidx, localimm i ≠ base + len)
      (map prelude.W.Mk_localidx (seq base len)).
  Proof.
    eapply Forall_impl; first apply map_seq_forall_localidx_leq.
    lias.
  Qed.

End common.
