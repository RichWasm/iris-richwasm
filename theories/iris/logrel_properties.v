From Stdlib Require Export ZArith.

From stdpp Require Export base list.

Require Export RecordUpdate.RecordUpdate.

From iris.proofmode Require Export base proofmode classes.

From RichWasm.named_props Require Export named_props custom_syntax.
From RichWasm Require Export layout syntax typing util.
Require Export RichWasm.wasm.operations.
From RichWasm.compiler Require Export prelude codegen instruction module.
From RichWasm.iris Require Export autowp memory logrel util wp_codegen.
From RichWasm.iris.language Require Export cwp logpred.
Require Export RichWasm.iris.logrel.instr.kinding.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section properties.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma has_areps_cons_l ιs ι o os:
    has_areps (ι :: ιs) (SAtoms (o :: os)) ->
    has_areps ιs (SAtoms os) /\
    has_arep ι o.
  Proof.
    intros H.
    unfold has_areps in H.
    destruct H as [os' [Heq HF]].
    injection Heq as <-.
    inversion HF as [| ?? ?? Hhead Htail]; subst.
    split.
    - unfold has_areps. eauto.
    - exact Hhead.
  Qed.

  Lemma has_areps_cons_r ιs ι o os:
    has_areps ιs (SAtoms os) ->
    has_arep ι o ->
    has_areps (ι :: ιs) (SAtoms (o :: os)).
  Proof.
    intros Hareps Harep.
    unfold has_areps.
    exists (o :: os).
    split; first done.
    apply List.Forall2_cons; first done.
    destruct Hareps as (? & Heq & Hareps).
    by inversion Heq; subst.
  Qed.

  Lemma has_areps_cons ιs ι o os:
    has_areps ιs (SAtoms os) /\
    has_arep ι o <->
    has_areps (ι :: ιs) (SAtoms (o :: os)).
  Proof.
    split.
    - intros [? ?]. by apply has_areps_cons_r.
    - apply has_areps_cons_l.
  Qed.

  Lemma has_areps_cons_exists ιs o os:
    has_areps ιs (SAtoms (o :: os)) ->
    ∃ ι ιs' , ιs = ι :: ιs' /\
    has_areps ιs' (SAtoms os) /\
    has_arep ι o.
  Proof.
    intros H.
    destruct ιs as [| ι ιs'].
    - destruct H as [os' [Heq HF]].
      inversion Heq; subst.
      inversion HF.
    - do 2 eexists.
      split; first done.
      by apply has_areps_cons.
  Qed.

  Lemma has_areps_exists os :
    ∃ ιs, has_areps ιs (SAtoms os).
  Proof.
    induction os as [| o os' IH].
    - exists []. exists [].
      done.
    - destruct IH as [ιs' IH].
      destruct o; eexists (_ :: ιs'); apply has_areps_cons; split; try done; unfold has_arep.
      + by instantiate (1 := PtrR).
      + by instantiate (1 := I32R).
      + by instantiate (1 := I64R).
      + by instantiate (1 := F32R).
      + by instantiate (1 := F64R).
  Qed.

  Lemma has_areps_app_l ιs1 os1 ιs2 os2 :
    has_areps ιs1 (SAtoms os1) ->
    has_areps ιs2 (SAtoms os2) ->
    has_areps (ιs1 ++ ιs2) (SAtoms $ os1 ++ os2).
  Proof.
    intros [os1' [Heq1 Hf1]] [os2' [Heq2 Hf2]].
    simplify_eq.
    exists (os1' ++ os2').
    split.
    - done.
    - by apply Forall2_app.
  Qed.

  Lemma has_areps_app_r_exists ιs1 ιs2 os :
    has_areps (ιs1 ++ ιs2) (SAtoms os) ->
    ∃ os1 os2, os = os1 ++ os2 /\
    has_areps ιs1 (SAtoms os1) /\
    has_areps ιs2 (SAtoms os2).
  Proof.
    intros [os' [Heq Hf]].
    simplify_eq.
    apply Forall2_app_inv_l in Hf as [os1 [os2 [Hf1 [Hf2 ->]]]].
    exists os1, os2.
    split; [done|].
    split.
    - by exists os1.
    - by exists os2.
  Qed.

  Lemma has_areps_app_r_length ιs1 os1 ιs2 os2 :
    length ιs1 = length os1 ->
    has_areps (ιs1 ++ ιs2) (SAtoms $ os1 ++ os2) ->
    has_areps ιs1 (SAtoms os1) /\
    has_areps ιs2 (SAtoms os2).
  Proof.
    intros Hlen [os [Heq Hf]].
    simplify_eq.
    apply Forall2_app_inv in Hf as [Hf1 Hf2]; [|done].
    split.
    - by exists os1.
    - by exists os2.
  Qed.

  Lemma has_areps_length ιs os :
    has_areps ιs (SAtoms os) ->
    length ιs = length os.
  Proof.
    intros [os' [Heq Hf]].
    simplify_eq.
    by eapply Forall2_length.
  Qed.

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


  Lemma value_interp_i31 se os :
    value_interp rti sr se type_i31 (SAtoms os) -∗ ∃ n, ⌜os = [PtrA n]⌝.
  Proof.
    iIntros "Hval".
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
    exists p; auto.
  Qed.

  Lemma value_interp_i32 se os :
    value_interp rti sr se type_i32 (SAtoms os) -∗ ∃ n, ⌜os = [I32A n]⌝.
  Proof.
    iIntros "Hval".
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

  Lemma value_interp_coderef se os κ ϕ :
    value_interp rti sr se (CodeRefT κ ϕ) (SAtoms os) -∗ ∃ n, ⌜os = [I32A n]⌝.
  Proof.
    iIntros "Hval".
    iDestruct "Hval" as "(%κ0 & %Hκ & Rest)".
    destruct κ0; auto; [ | iDestruct "Rest" as "[[[] _] _]"].
    iDestruct "Rest" as "((%Hareps & %Href) & Oh)".
    iDestruct "Oh" as "(%i & %i32 & %j & %cl & %nrepr & %nos & what & nstab & nsfun)".
    inversion nos; subst; clear nos.
    auto.
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

  Lemma result_type_interp_split wl1 wl2 vs_wl :
    result_type_interp (wl1 ++ wl2) vs_wl ->
    ∃ vs_wl1 vs_wl2, vs_wl = vs_wl1 ++ vs_wl2 /\
    result_type_interp wl1 vs_wl1 /\
    result_type_interp wl2 vs_wl2.
  Proof.
    intros H.
    unfold result_type_interp in H.
    apply Forall2_app_inv_l in H.
    destruct H as [vs_wl1 [vs_wl2 [HF1 [HF2 ->]]]].
    exists vs_wl1, vs_wl2.
    eauto.
  Qed.

  Lemma result_type_interp_combine wl1 wl2 vs_wl1 vs_wl2 :
    result_type_interp wl1 vs_wl1 →
    result_type_interp wl2 vs_wl2 →
    result_type_interp (wl1 ++ wl2) (vs_wl1 ++ vs_wl2).
  Proof.
    intros H1 H2.
    unfold result_type_interp in *.
    apply Forall2_app; eauto.
  Qed.

  Lemma ref_flag_atoms_interp_cons ξ o os :
    ref_flag_atoms_interp ξ (SAtoms (o :: os)) ↔
    forall_ptr_atom (ref_flag_ptr_interp ξ) o ∧ ref_flag_atoms_interp ξ (SAtoms os).
  Proof.
    unfold ref_flag_atoms_interp, forall_satoms.
    by rewrite Forall_cons.
  Qed.

  Lemma ref_flag_atoms_interp_app ξ os1 os2 :
    ref_flag_atoms_interp ξ (SAtoms (os1 ++ os2)) ↔
    ref_flag_atoms_interp ξ (SAtoms os1) ∧ ref_flag_atoms_interp ξ (SAtoms os2).
  Proof.
    unfold ref_flag_atoms_interp, forall_satoms.
    by rewrite Forall_app.
  Qed.

  Lemma value_interp_ref_flag_atoms se τ ιs ξ sv :
    type_skind se τ = Some (SVALTYPE ιs ξ) →
    value_interp rti sr se τ sv -∗
    ⌜ref_flag_atoms_interp ξ sv⌝.
  Proof.
    iIntros (Hskind) "Hval".
    iDestruct (value_interp_skind with "Hval") as %(sκ & Hsκ & Hsv).
    rewrite Hskind in Hsκ. inversion Hsκ; subst.
    iPureIntro.
    by destruct Hsv.
  Qed.

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

  Lemma atom_interp_of_default ty :
    ⊢ ∃ o, atom_interp o (default_of_value_type ty).
  Proof.
    unfold default_of_value_types.
    destruct ty; iExists _.
    + instantiate (1 := I32A _); simpl; done.
    + instantiate (1 := I64A _); simpl; done.
    + instantiate (1 := F32A _); simpl; done.
    + instantiate (1 := F64A _); simpl; done.
  Qed.

  Lemma atoms_interp_of_defaults tys :
    ⊢ ∃ os, atoms_interp os (default_of_value_types tys).
  Proof.
    induction tys as [|ty tys' IH].
    - iExists [].
      by simpl.
    - iDestruct IH as "(%os & IH)".
      unfold default_of_value_types.
      rewrite map_cons.
      iDestruct (atom_interp_of_default ty) as "[%o Hatom]".
      iExists (o :: os).
      iApply atoms_interp_cons.
      by iSplitR.
  Qed.

  Lemma atom_interp_and_arep_of_default_of_arep ι :
    ⊢ ∃ o, atom_interp o (default_of_value_type $ translate_arep ι) ∗ ⌜has_arep ι o⌝ ∗ ⌜ref_flag_atoms_interp NoRefs (SAtoms [o])⌝.
  Proof.
    destruct ι.
    - iExists (PtrA _); iSplit; last (iSplit; first done).
      + simpl.
        iExists _, _.
        iSplit; last iSplit; first done.
        1: done.
        iExists (RootInt 0).
        iSplit; first iPureIntro; simpl.
        1: constructor.
        by instantiate (1 := PtrInt _).
      + iPureIntro.
        unfold ref_flag_atoms_interp, forall_satoms.
        by apply Forall_singleton.
    - iExists (I32A _); iSplit; first done.
      iSplit; first done.
      iPureIntro.
      unfold ref_flag_atoms_interp, forall_satoms.
      by apply Forall_singleton.
    - iExists (I64A _); iSplit; first done.
      iSplit; first done.
      iPureIntro.
      unfold ref_flag_atoms_interp, forall_satoms.
      by apply Forall_singleton.
    - iExists (F32A _); iSplit; first done.
      iSplit; first done.
      iPureIntro.
      unfold ref_flag_atoms_interp, forall_satoms.
      by apply Forall_singleton.
    - iExists (F64A _); iSplit; first done.
      iSplit; first done.
      iPureIntro.
      unfold ref_flag_atoms_interp, forall_satoms.
      by apply Forall_singleton.
  Qed.

  Lemma atoms_interp_and_areps_of_default_of_areps ιs :
    ⊢ ∃ os, atoms_interp os (default_of_value_types $ translate_arep <$> ιs) ∗ ⌜has_areps ιs (SAtoms os)⌝ ∗ ⌜ref_flag_atoms_interp NoRefs (SAtoms os)⌝.
  Proof.
    induction ιs as [|ι ιs' IH].
    - iExists [].
      iSplit; first by simpl.
      iSplit; first by iExists [].
      iPureIntro.
      cbn.
      done.
    - iDestruct IH as "(%os' & IHatoms & %IHareps & %IHref_flag)".
      iEval (unfold default_of_value_types).
      rewrite fmap_cons.
      rewrite map_cons.
      iDestruct (atom_interp_and_arep_of_default_of_arep ι) as "(%o & Hatom & %Harep & %Href_flag)".
      iExists (o :: os').
      rewrite atoms_interp_cons.
      iFrame "#".
      iPureIntro.
      split; first by apply has_areps_cons.
      apply ref_flag_atoms_interp_cons; split; last done.
      unfold ref_flag_atoms_interp, forall_satoms in Href_flag.
      by rewrite Forall_singleton in Href_flag.
  Qed.

  Lemma frame_interp_wl_interp se F L WL ηss fr :
    frame_interp rti sr se ηss L WL fr -∗
    ⌜wl_interp (fe_wlocal_offset (fe_of_context F)) WL fr⌝.
  Proof.
    iIntros "Hframe".
    iDestruct "Hframe" as
      "(%oss & %vss_L & %vs_WL & %Hfr & %Hprims & %Hresult & Hatom & Hval)".
    unfold wl_interp.

    (* This is my best guess at the exists given Hfr and Hresult. Should be right *)
    iExists (concat vss_L). iExists vs_WL. iExists [].
    iSplit; [|iSplit]; clear_nils; subst; auto.

    iEval (cbn).
    iEval (cbn) in "Hval".
    iPoseProof (big_sepL2_length with "[$Hval]") as "%HlenossL".
    iPoseProof (big_sepL2_length with "[$Hatom]") as "%HlenvssL".
    rewrite sum_list_with_length_concat.
    (* unfold atoms_interp; unfold value_interp; destruct F; cbn. *)

    (* Currently unprovable bc there's nothing to relate F fc_locals to *)
    (* probably need local_ctx_ok F L *)

  Admitted.

    Lemma root_pointer_heap_shp_inv rp μ ℓ :
    root_pointer_interp rp (PtrHeap μ ℓ) -∗
    ⌜∃ a, rp = RootHeap μ a⌝.
  Proof.
    iIntros "H".
    destruct rp; first done.
    cbn.
    iDestruct "H" as "(-> & _)".
    by iExists _.
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
       (⌜frame_rel lmask fr fr'⌝ ∗ frame_interp rti sr se F.(typing.fc_locals) L wl fr' ∗
          (∃ os', values_interp rti sr se τs os' ∗ atoms_interp os' vs') ∗
          (∃ θ0, rt_token rti sr θ0) ∗ na_own logrel_nais ⊤) -∗
       Φ fr' vs') -∗
    labels_interp rti sr se F.(typing.fc_locals) fr wl lmask F.(fc_labels) B -∗
    labels_interp rti sr se F.(typing.fc_locals) fr wl lmask
      ((τs, L) :: F.(fc_labels)) ((length ts, Φ) :: B).
  Proof.
    iIntros (Hse Hts) "#HΦ Hlabels".
    unfold labels_interp.
    unfold const.
    rewrite big_sepL2_cons.
    iSplitL "HΦ".
    - iSplitR.
      + by erewrite translate_types_comp_sem.
      + iIntros (fr' vs os θ) "!> %Hlmask Hvs Hos Hown Hframe Hrti".
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

  Lemma labels_interp_trans se wl ηss fr fr' lmask labels B :
    frame_rel lmask fr fr' ->
    labels_interp rti sr se ηss fr wl lmask labels B -∗
    labels_interp rti sr se ηss fr' wl lmask labels B.
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

  Lemma labels_interp_mono se ηss fr fr' wl lmask lmask' labels B :
    frame_rel lmask fr fr' ->
    (forall i, lmask i -> lmask' i) ->
    labels_interp rti sr se ηss fr wl lmask labels B -∗
    labels_interp rti sr se ηss fr' wl lmask' labels B.
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



End properties.
