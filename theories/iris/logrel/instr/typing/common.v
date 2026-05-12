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

Ltac clear_nils :=
  repeat rewrite <- ?app_assoc, -> ?app_nil_l, -> ?app_nil_r in *.

(* TODO relocate *)
Lemma get_base_l_append {i : nat} (lh : valid_holed i) e :
  get_base_l (vh_append lh e) = get_base_l lh.
Proof.
  induction lh;simpl;auto.
Qed.

Section common.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma has_kind_agree F τ κ κ' :
    has_kind F τ κ →
    has_kind F τ κ' →
    subkind_of κ κ' ∨ subkind_of κ' κ.
  Proof.
    intros H1 H2.
    have Hsome := type_kind_has_kind_is_Some _ _ _ H1.
    destruct Hsome as [κ'' Hκ''].
    have Hsub1 := type_kind_has_kind_agree _ _ _ _ H1 Hκ''.
    have Hsub2 := type_kind_has_kind_agree _ _ _ _ H2 Hκ''.
    inversion Hsub1; inversion Hsub2; subst.
    - injection H5 as <- <-.
      destruct (ref_flag_le_total ξ' ξ'0).
      + left. econstructor. eauto using ref_flag_le_trans.
      + right. econstructor. eauto using ref_flag_le_trans.
    - discriminate.
    - discriminate.
    - injection H5 as <- <-.
      destruct (ref_flag_le_total ξ' ξ'0).
      + left. econstructor. eauto using ref_flag_le_trans.
      + right. econstructor. eauto using ref_flag_le_trans.
  Qed.

  Lemma has_kind_agree_f F τ ρ ξ σ ξ' :
    has_kind F τ (VALTYPE ρ ξ) →
    has_kind F τ (MEMTYPE σ ξ') →
    False.
  Proof.
    intros H1 H2.
    have H := has_kind_agree _ _ _ _ H1 H2.
    destruct H; inversion H.
  Qed.

  Lemma Forall2_mini_impl {A B : Type} (P Q: A → B → Prop) (l : list A) (k: list B):
    Forall2 P l k -> Forall2 (λ a b, P a b → Q a b) l k -> Forall2 Q l k.
  Proof.
    generalize dependent k.
    induction l.
    - intros k HP Hall.
      destruct k; [done|by inversion HP].
    - intros k HP Hall.
      destruct k as [| b k]; [by inversion HP|].
      inversion HP; subst.
      inversion Hall; subst.
      apply Forall2_cons; auto.
  Qed.
  Lemma Forall2_mini_impl_Forall {A B : Type} (P Q: A → B → Prop) (l : list A) (k: list B):
    Forall2 P l k -> Forall (λ a, ∀ b, P a b → Q a b) l -> Forall2 Q l k.
  Proof.
    generalize dependent k.
    induction l.
    - intros k HP Hall.
      destruct k; [done|by inversion HP].
    - intros k HP Hall.
      destruct k as [| b k]; [by inversion HP|].
      inversion HP; subst.
      inversion Hall; subst.
      apply Forall2_cons; auto.
  Qed.

  Lemma mapM_take {A B : Type} n (f : A → option B) (l : list A) (k : list B) :
    mapM f l = Some k →
    mapM f (take n l) = Some (take n k).
  Proof.
    intros H.
    rewrite mapM_Some.
    apply Forall2_take.
    by apply mapM_Some.
  Qed.

  Lemma mapM_drop {A B : Type} n (f : A → option B) (l : list A) (k : list B) :
    mapM f l = Some k →
    mapM f (drop n l) = Some (drop n k).
  Proof.
    intros H.
    rewrite mapM_Some.
    apply Forall2_drop.
    by apply mapM_Some.
  Qed.

  Lemma mapM_lookup {A B} f (l : list A) (k : list B) (i : nat) :
    mapM f l = Some k ->
    (l !! i) ≫= f = k !! i.
  Proof.
    intros Hm%mapM_Some_1.
    destruct (l !! i) as [a|] eqn:Hl; simpl.
    - eapply Forall2_lookup_l in Hm as [b [-> Hab]]; eauto.
    - apply lookup_ge_None_1 in Hl.
      symmetry.
      apply lookup_ge_None_2.
      by rewrite -(Forall2_length _ _ _ Hm).
  Qed.

  Lemma mapM_app {A B : Type} (f : A → option B) (l : list A) (k1 k2 : list B) :
    mapM f l = Some (k1 ++ k2) →
    ∃ l1 l2,
    l = l1 ++ l2 /\
    mapM f l1 = Some k1 /\
    mapM f l2 = Some k2.
  Proof.
    intros H.
    exists (take (length k1) l), (drop (length k1) l).
    split; [by rewrite take_drop |].
    split.
    - erewrite mapM_take; [| exact H].
      by rewrite take_app_length.
    - erewrite mapM_drop; [| exact H].
      by rewrite drop_app_length.
  Qed.

  Lemma mapM_split {A B : Type} (f : A → option B) (l : list A) (b : B) (k1 k2 : list B) :
    mapM f l = Some (k1 ++ [b] ++ k2) →
    ∃ l1 l2 a,
    l = l1 ++ [a] ++ l2 /\
    mapM f l1 = Some k1 /\
    f a = Some b /\
    mapM f l2 = Some k2.
  Proof.
    intros H.
    apply mapM_app in H as (l1 & lrest & Hl & Hk1 & Hrest).
    apply mapM_app in Hrest as (lmid & l2 & Hlrest & Hmid & Hk2).
    apply length_mapM in Hmid as Hlen.
    destruct lmid as [| a [| ? ?]]; try done.
    subst lrest.
    exists l1, l2, a.
    repeat split; try done.
    simpl in Hmid.
    apply bind_Some in Hmid as (b' & Hfa & Hsb).
    inversion Hsb.
    by subst b'.
  Qed.

  Lemma has_values_length evs vs :
    has_values evs vs -> length evs = length vs.
  Proof.
    intros.
    unfold has_values in H.
    apply Is_true_true in H.
    apply all2_size in H.
    auto.
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

  Lemma ref_flag_atoms_interp_cons ξ o os :
    ref_flag_atoms_interp ξ (SAtoms (o :: os)) ↔
    forall_ptr_atom (ref_flag_interp ξ) o ∧ ref_flag_atoms_interp ξ (SAtoms os).
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

  Lemma eval_rep_emptyenv :
    forall ρ ιs,
      eval_rep EmptyEnv ρ = Some ιs ->
      ∀ (se: semantic_env (Σ:=Σ)),
        eval_rep se ρ = Some ιs.
  Proof.
    induction ρ using rep_ind; intros * Hev *; cbn in Hev; cbn.
    - inversion Hev.
    - rewrite -Hev.
      f_equal.
      apply fmap_Some in Hev.
      destruct Hev as (ιss & Hev & _).
      apply mk_is_Some in Hev.
      apply mapM_is_Some_1 in Hev.
      apply Forall_mapM_ext.
      eapply Forall_impl.
      { eapply (List.Forall_and H Hev). }
      cbn.
      intros ρ [Hev' [ιs' Hempty]].
      erewrite Hev'; eauto.
    - rewrite -Hev.
      f_equal.
      apply fmap_Some in Hev.
      destruct Hev as (ιss & Hev & _).
      apply mk_is_Some in Hev.
      apply mapM_is_Some_1 in Hev.
      apply Forall_mapM_ext.
      eapply Forall_impl.
      { eapply (List.Forall_and H Hev). }
      cbn.
      intros ρ [Hev' [ιs' Hempty]].
      erewrite Hev'; eauto.
    - done.
  Qed.

  Lemma mapM_eval_rep_emptyenv ρs ιss (se: semantic_env (Σ:=Σ)) :
    mapM (eval_rep EmptyEnv) ρs = Some ιss ->
    mapM (eval_rep se) ρs = Some ιss.
  Proof.
    intros Hemp.
    rewrite mapM_Some in Hemp.
    rewrite mapM_Some.
    eapply Forall2_impl.
    2: {
      intros.
      apply eval_rep_emptyenv.
      apply H.
    }
    done.
  Qed.

  Lemma sum_offset_emptyenv ρs i off (se: semantic_env (Σ:=Σ)) :
    sum_offset EmptyEnv ρs i = Some off ->
    sum_offset se ρs i = Some off.
  Proof.
    intros Hso.
    apply bind_Some in Hso as [ιss [Her H]].
    eapply mapM_eval_rep_emptyenv in Her.
    apply bind_Some.
    eauto.
  Qed.

  Lemma eval_kind_of_eval_rep (se: semantic_env (Σ:=Σ)) ρ ιs :
    eval_rep se ρ = Some ιs ->
    forall ξ, eval_kind se (VALTYPE ρ ξ) = Some (SVALTYPE ιs ξ).
  Proof.
    intros Heval ξ.
    unfold eval_kind.
    apply bind_Some.
    by eexists.
  Qed.

  Lemma type_skind_eval_rep (se: semantic_env (Σ:=Σ)) F ρ ιs ξ τ ιs' ξ' :
    has_kind F τ (VALTYPE ρ ξ) ->
    sem_env_interp F se ->
    eval_rep se ρ = Some ιs ->
    type_skind se τ = Some (SVALTYPE ιs' ξ') ->
    subskind_of (SVALTYPE ιs' ξ') (SVALTYPE ιs ξ).
  Proof.
    intros.
    eapply type_skind_has_kind_agree; try done.
    by apply eval_kind_of_eval_rep.
  Qed.

  Lemma type_skind_eval_rep_emptyenv (se: semantic_env (Σ:=Σ)) F ρ ιs ξ τ ιs' ξ' :
    has_kind F τ (VALTYPE ρ ξ) ->
    sem_env_interp F se ->
    eval_rep EmptyEnv ρ = Some ιs ->
    type_skind se τ = Some (SVALTYPE ιs' ξ') ->
    subskind_of (SVALTYPE ιs' ξ') (SVALTYPE ιs ξ).
  Proof.
    intros.
    eapply type_skind_eval_rep; try done.
    by apply eval_rep_emptyenv.
  Qed.

  Lemma to_e_list_app es1 es2 :
    to_e_list (es1 ++ es2) = to_e_list es1 ++ to_e_list es2.
  Proof.
    by rewrite to_e_list_cat cat_app.
  Qed.

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

  Lemma frame_f_locs_update fr fr' vs1 vs_new vs_old vs2 val_idxs :
    val_idxs = seq (length vs1) (length vs_old) ->
    frame_rel (λ i, i ∉ val_idxs) fr fr' ->
    Forall2 (λ i v, f_locs fr' !! i = Some v) val_idxs vs_new ->
    f_locs fr  = vs1 ++ vs_old ++ vs2 ->
    f_locs fr' = vs1 ++ vs_new ++ vs2.
  Proof.
    intros Hval_idxs [Hmask _] HF Hfr.
    (* First extract length vs_new = length vs_old from Forall2 *)
    have Hlen : length vs_new = length vs_old.
    { have := Forall2_length _ _ _ HF. rewrite Hval_idxs length_seq. lia. }
    (* Prove equality pointwise *)
    apply list_eq. intros i.
    destruct (decide (i ∈ val_idxs)) as [Hin | Hout].
    - (* i is in val_idxs, so fr' !! i = Some (vs_new !! ...) *)
      rewrite Hval_idxs in Hin.
      apply elem_of_seq in Hin as [Hlo Hhi].
      (* j is the position of i in val_idxs *)
      set j := i - length vs1.
      have Hj : j < length vs_old by unfold j; lia.
      have Hseq : seq (length vs1) (length vs_old) !! j = Some i.
      { rewrite lookup_seq. unfold j. split; lia. }
      rewrite <- Hval_idxs in Hseq.
      destruct (Forall2_lookup_l _ _ _ _ _ HF Hseq) as [v [Hv HP]].
      (* HP : f_locs fr' !! i = Some v *)
      rewrite HP.
      (* now show (vs1 ++ vs_new ++ vs2) !! i = Some v *)
      rewrite lookup_app_r; [|lia].
      rewrite lookup_app_l; [|rewrite Hlen; lia].
      (* vs_new !! j = Some v from Hv via HP *)
      by rewrite Hv.
    - (* i is not in val_idxs: fr and fr' agree *)
      rewrite <- Hmask; [|exact Hout].
      rewrite Hfr.
      rewrite Hval_idxs in Hout.
      have Hout' : i < length vs1 ∨ length vs1 + length vs_old ≤ i.
      { rewrite elem_of_seq in Hout.
        lia. }
      destruct Hout' as [Hlt | Hge].
      + (* i < length vs1: in the vs1 segment, both sides agree *)
        rewrite !lookup_app_l; lias.
      + (* i ≥ length vs1 + length vs_old: in the vs2 segment *)
        rewrite !lookup_app_r; [|lia..].
        f_equal. lia.
  Qed.

  Lemma frame_f_locs_update' fr fr' vs1 vs_new vs_old vs2 val_idxs val_localidxs :
    val_idxs = seq (length vs1) (length vs_old) ->
    val_localidxs = map prelude.W.Mk_localidx val_idxs ->
    frame_rel (λ i, i ∉ val_idxs) fr fr' ->
    Forall2 (λ i v, f_locs fr' !! localimm i = Some v) val_localidxs vs_new ->
    f_locs fr  = vs1 ++ vs_old ++ vs2 ->
    f_locs fr' = vs1 ++ vs_new ++ vs2.
  Proof.
    intros Hval_idxs Hval_localidxs Hframe_rel HF Hfr.
    eapply frame_f_locs_update; eauto.
    subst val_localidxs.
    rewrite Forall2_fmap_l in HF.
    eapply Forall2_impl; [exact HF|].
    done.
  Qed.

  Lemma frame_rel_Forall2_update fr fr' vs (val_idxs1 val_idxs2 : list nat) :
    frame_rel (λ i, i ∉ val_idxs1) fr fr' ->
    Forall (λ i, i ∉ val_idxs1) val_idxs2 ->
    Forall2 (λ i v, f_locs fr !! i = Some v) val_idxs2 vs ->
    Forall2 (λ i v, f_locs fr' !! i = Some v) val_idxs2 vs.
  Proof.
    intros [Hmask _] Hdisjoint Hforall.
    induction Hforall as [| i v idxs vs Hi Hrest IH].
    - constructor.
    - apply Forall_cons in Hdisjoint as [Hnotin Hdisjoint].
      constructor.
      + rewrite <- Hmask; last exact Hnotin.
        exact Hi.
      + exact (IH Hdisjoint).
  Qed.

  Lemma frame_rel_Forall2_update' fr fr' vs val_localidxs2 (val_idxs1 val_idxs2 : list nat) :
    val_localidxs2 = map prelude.W.Mk_localidx val_idxs2 ->
    frame_rel (λ i, i ∉ val_idxs1) fr fr' ->
    Forall (λ i, i ∉ val_idxs1) val_idxs2 ->
    Forall2 (λ i v, f_locs fr !! localimm i = Some v) val_localidxs2 vs ->
    Forall2 (λ i v, f_locs fr' !! localimm i = Some v) val_localidxs2 vs.
  Proof.
    intros -> Hfrel Hdisjoint Hforall.
    rewrite Forall2_fmap_l in Hforall.
    rewrite Forall2_fmap_l.
    eapply Forall2_impl.
    2: {
      intros x y Hxy.
      simpl.
      apply Hxy.
    }
    eapply frame_rel_Forall2_update; try done.
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
    value_interp rti sr se (RefT κ μ τ) (SAtoms os) -∗ ⌜length os = 1⌝.
  Proof.
    iIntros "(%sκ & _ & _ & H)".
    destruct μ.
    - destruct (lookup_mem se n) eqn:Hn; cbn in Hn.
      + cbn. rewrite Hn. destruct b.
        * iDestruct "H" as "(% & % & % & %Hos & _)". by inversion Hos.
        * iDestruct "H" as "(% & % & %Hos & _)". by inversion Hos.
      + cbn. by rewrite Hn.
    - cbn. destruct b.
      + iDestruct "H" as "(% & % & % & %Hos & _)". by inversion Hos.
      + iDestruct "H" as "(% & % & %Hos & _)". by inversion Hos.
  Qed.

  (* useful lemma for proving compat lemmas for instructions erased by the compiler. *)
  Lemma sem_type_erased M F L WT WL lmask ψ τs1 τs2 :
    ψ = InstrT τs1 τs2 ->
    ⊢ (∀ se vs,
          values_interp rti sr se τs1 vs -∗
          values_interp rti sr se τs2 vs) -∗
      have_instr_type_sem rti sr mr M F L WT WL lmask [] ψ L.
  Proof.
    iIntros (->) "Hcast".
    iIntros (se inst lh Henv fr rvs vs θ) "@@@@@@@@@@@@".
    rewrite app_nil_r.
    iApply (cwp_val with "[$] [$]"); first done.
    iFrame.
    iSplit.
    - unfold frame_rel.
      iPureIntro; split.
      + unfold mask_locs_eq; eauto.
      + eauto.
    - by iApply "Hcast".
  Qed.

  Lemma sem_type_erased_nop M F L WT WL lmask ψ τs1 τs2 :
    ψ = InstrT τs1 τs2 ->
    ⊢ (∀ se vs,
          values_interp rti sr se τs1 vs -∗
          ▷values_interp rti sr se τs2 vs) -∗
      have_instr_type_sem rti sr mr M F L WT WL lmask [BI_nop] ψ L.
  Proof.
    iIntros (->) "Hcast".
    iIntros (se inst lh fr rvs vs θ Henv) "@@@@@@@@@@@@".
    iApply cwp_val_app; first done.
    iApply (cwp_nop with "[$] [$]").
    iFrame.
    iSplit.
    - unfold frame_rel, mask_locs_eq; eauto.
    - rewrite app_nil_r.
      iFrame.
      by iApply "Hcast".
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

  (* Ugly lemma dealing with subkinding *)
  Lemma has_kind_SumT_inv F τs ρs ξ κ :
    has_kind F (SumT (VALTYPE (SumR ρs) ξ) τs) κ →
    Forall2 (λ τ ρ, has_kind F τ (VALTYPE ρ ξ)) τs ρs.
  Proof.
    intros H. remember (SumT (VALTYPE (SumR ρs) ξ) τs) as τ.
    induction H; try discriminate.
    - (* KSum *) injection Heqτ; intros; subst. eauto.
    - (* KSub *) eauto.
  Qed.

  Lemma lwp_wasm_empty_ctx s E es Φ:
    lenient_wp s E es Φ ∗-∗ lenient_wp_ctx s E es Φ 0 (LH_base nil nil).
  Proof.
    by iApply wp_wasm_empty_ctx.
  Qed.

  Lemma lwp_label_push s E Φ i lh n es es0 vs es':
    is_true (const_list vs) ->
    ⊢ lenient_wp_ctx s E es Φ (S i) (push_base lh n es0 vs es') -∗
      lenient_wp_ctx s E [AI_label n es0 (vs ++ es ++ es')] Φ i lh.
  Proof.
    iIntros (Hconst) "Hwp".
    change @app with @seq.cat.
    by iApply wp_label_push.
  Qed.


  Lemma append_lh_depth {i : nat} (lh : valid_holed i) e :
    lh_depth (lh_of_vh lh) = lh_depth (lh_of_vh (vh_append lh e)).
  Proof.
    induction lh; simpl; auto.
  Qed.

  Lemma wp_map_gc_ptr_duproot ι idx wt wl res wt' wl' es:
    run_codegen (memory.map_gc_ptr ι idx (memory.duproot mr)) wt wl = inr (res, wt', wl', es) ->
    res = () /\ wt' = [] /\ wl' = [].
  Proof.
    unfold memory.map_gc_ptr, memory.ite_gc_ptr; intros Hcg.
    destruct ι.
    - apply wp_ignore in Hcg.
      destruct Hcg as (-> & res' & Hcg).
      admit.
    - cbn; inv_cg_ret Hcg; done.
    - cbn; inv_cg_ret Hcg; done.
    - cbn; inv_cg_ret Hcg; done.
    - cbn; inv_cg_ret Hcg; done.
  Admitted.

  Lemma wp_map_gc_ptrs_duproot ιs idxs wt wl res wt' wl' es_gcs:
    run_codegen (memory.map_gc_ptrs ιs idxs (memory.duproot mr)) wt wl = inr (res, wt', wl', es_gcs) ->
    res = () /\ wt' = [] /\ wl' = [].
  Proof.
    unfold memory.map_gc_ptrs, util.mapM_.
    intros Hcg.
    apply wp_ignore in Hcg.
    destruct Hcg as (-> & res' & Hcg).
    remember (zip ιs idxs) as ιidxs.
    revert Heqιidxs Hcg.
    revert ιs idxs wt wl res' wt' wl' es_gcs.
    induction ιidxs as [|[ι idx] ιidxs].
    - intros.
      apply wp_mapM_nil in Hcg.
      destruct Hcg as (-> & -> & -> & ->).
      done.
    - intros.
      destruct ιs as [|ι' ιs], idxs as [|idx' idxs]; inversion Heqιidxs.
      subst ι' idx'.
      apply wp_mapM_cons in Hcg.
      destruct Hcg as (res & ?wt & ?wl & ?es & ?res & ?wt & ?wl & ?es & Hdup & Hcg & Heqs).
      destruct Heqs as (-> & -> & -> & ->).
      eapply IHιidxs in Hcg; eauto.
      destruct Hcg as (_ & -> & ->).
      split; auto.
      apply wp_map_gc_ptr_duproot in Hdup.
      destruct Hdup as (-> & -> & ->).
      done.
  Qed.

  Fixpoint replace_base {n} (vh: valid_holed n) vs :=
    match vh with
    | VH_base n _ es => VH_base n vs es
    | VH_rec n b c d vh e => VH_rec b c d (replace_base vh vs) e
    end.

  Lemma lfilled_get_replace_base {n} (vh: valid_holed n) es vs1 vs2:
    get_base_l vh = vs1 ++ vs2 ->
    lh_depth (lh_of_vh vh) = n ->
    is_true (lfilled n (lh_of_vh (replace_base vh vs1))
               (seq.cat (v_to_e_list vs2) es) (vfill vh es)).
  Proof.
    induction vh => //=.
    - intros -> <-.
      unfold lfilled, lfill => //=.
      rewrite v_to_e_is_const_list /=.
      rewrite -v_to_e_cat.
      repeat rewrite cat_app.
      repeat rewrite app_assoc.
      done.
    - intros Hbase Hdepth.
      apply eq_add_S in Hdepth.
      specialize (IHvh Hbase Hdepth).
      unfold lfilled, lfill; fold lfill.
      rewrite v_to_e_is_const_list.
      unfold lfilled in IHvh.
      destruct (lfill _ _ _) => //.
      apply b2p in IHvh as <-.
      done.
  Qed.

  Lemma atoms_interp_take os vs count :
    atoms_interp os vs -∗
    atoms_interp (take count os) (take count vs) ∗
    atoms_interp (drop count os) (drop count vs).
  Proof.
    iIntros "Hatoms".
    iDestruct (big_sepL2_length with "Hatoms") as %Hlen.
    rewrite -{1}(take_drop count os) -{1}(take_drop count vs).
    iDestruct (big_sepL2_app_inv with "Hatoms") as "[Htake Hdrop]".
    { rewrite !length_take. lia. }
    iFrame.
  Qed.

  Lemma atoms_interp_take_drop os vs off count :
    atoms_interp os vs -∗
    atoms_interp (take count (drop off os)) (take count (drop off vs)).
  Proof.
    iIntros "Hatoms".
    iDestruct (atoms_interp_take with "Hatoms") as "[_ Hdrop]".
    by iDestruct (atoms_interp_take with "Hdrop") as "[Htake_drop _]".
  Qed.

  Lemma atoms_interp_app_split_l os1 os2 vs1 vs2 :
    length os1 = length vs1 ->
    atoms_interp (os1 ++ os2) (vs1 ++ vs2) -∗
    atoms_interp os1 vs1 ∗
    atoms_interp os2 vs2.
  Proof.
    iIntros (Hlen) "Hatoms".
    iDestruct (atoms_interp_take _ _ (length os1) with "Hatoms") as "[H1 H2]".
    rewrite !take_app_length !drop_app_length Hlen !take_app_length !drop_app_length.
    iFrame.
  Qed.

  Lemma atoms_interp_app_split_r os1 os2 vs1 vs2 :
    atoms_interp os1 vs1 -∗
    atoms_interp os2 vs2 -∗
    atoms_interp (os1 ++ os2) (vs1 ++ vs2).
  Proof.
  iIntros "H1 H2".
  iApply (big_sepL2_app with "H1 H2").
Qed.

  Lemma atoms_interp_app_l os1 os2 vs :
    atoms_interp (os1 ++ os2) vs -∗
    ∃ vs1 vs2, ⌜vs = vs1 ++ vs2⌝ ∗ atoms_interp os1 vs1 ∗ atoms_interp os2 vs2.
  Proof.
    iIntros "Hos".
    iDestruct (atoms_interp_length with "Hos") as %Hlen.
    iDestruct (atoms_interp_take _ _ (length os1) with "Hos") as "[Hos1 Hos2]".
    iEval (rewrite take_app_length) in "Hos1".
    iEval (rewrite drop_app_length) in "Hos2".
    iExists (take (length os1) vs), (drop (length os1) vs).
    iSplit.
    - iPureIntro. rewrite take_drop. reflexivity.
    - iFrame.
  Qed.

  Lemma atoms_interp_app_r (os : list atom) (vs1 vs2 : list value) :
    atoms_interp os (vs1 ++ vs2) -∗
    ∃ os1 os2 : list atom, ⌜os = os1 ++ os2⌝ ∗ atoms_interp os1 vs1 ∗ atoms_interp os2 vs2.
  Proof.
    iIntros "Hos".
    iDestruct (atoms_interp_length with "Hos") as %Hlen.
    iDestruct (atoms_interp_take _ _ (length vs1) with "Hos") as "[Hos1 Hos2]".
    iEval (rewrite take_app_length) in "Hos1".
    iEval (rewrite drop_app_length) in "Hos2".
    iExists (take (length vs1) os), (drop (length vs1) os).
    iSplit.
    - iPureIntro. rewrite take_drop. reflexivity.
    - iFrame.
  Qed.

  Lemma locals_interp_lookup se L oss i τ_old :
    L !! i = Some τ_old →
    locals_interp rti sr se L oss -∗
    ∃ oss_pre os_mid oss_post,
    ⌜oss = oss_pre ++ [os_mid] ++ oss_post⌝ ∗
    locals_interp rti sr se (take i L) oss_pre ∗
    value_interp rti sr se τ_old (SAtoms os_mid) ∗
    locals_interp rti sr se (drop (S i) L) oss_post.
  Proof.
    iIntros (Hlookup_L) "Hval".
    iDestruct (big_sepL2_length with "Hval") as %Hoss_len.
    have Hlookup_oss_i : ∃ os_mid, oss !! i = Some os_mid.
    {
      apply lookup_lt_is_Some_2.
      rewrite -Hoss_len.
      by eapply lookup_lt_Some.
    }
    destruct Hlookup_oss_i as [os_mid Hlookup_oss_i].
    iExists (take i oss), os_mid, (drop (S i) oss).
    iSplit.
    { iPureIntro. symmetry. apply take_drop_middle. exact Hlookup_oss_i. }
    (* unfold locals_interp. *)
    have Hsplit_L := take_drop_middle L i τ_old Hlookup_L.
    have Hsplit_oss := take_drop_middle oss i os_mid Hlookup_oss_i.
    rewrite <- Hsplit_L, <- Hsplit_oss.
    iDestruct (big_sepL2_app_inv with "Hval") as "[Hval_pre Hval_rest]".
    { left. rewrite !length_take. lia. }
    rewrite Hsplit_L Hsplit_oss.
    iDestruct "Hval_rest" as "[Hval_mid Hval_post]".
    unfold locals_interp.
    iFrame.
  Qed.

  Lemma locals_interp_length se L oss :
    locals_interp rti sr se L oss -∗ ⌜length L = length oss⌝.
  Proof.
    iIntros "Hval".
    unfold locals_interp.
    iDestruct (big_sepL2_length with "Hval") as %Hlen.
    iPureIntro. exact Hlen.
  Qed.

  Lemma frame_interp_update_frame se ηss L wl1 wl2 wl vs_idxs vs_wl fr fr' :
    vs_idxs = seq ((length $ concat ηss) + length wl1) (length wl) ->
    Forall2 (λ i v, f_locs fr' !! i = Some v) vs_idxs vs_wl ->
    result_type_interp wl vs_wl ->
    frame_rel (λ i, i ∉ vs_idxs) fr fr' ->
    frame_interp rti sr se ηss L (wl1 ++ wl ++ wl2) fr -∗
    frame_interp rti sr se ηss L (wl1 ++ wl ++ wl2) fr'.
  Proof.
    intros Hvs_idxs_wl Hnew_vals Hres Hfrel.
    iIntros "Hframe".
    iDestruct "Hframe" as
      "(%oss & %vss_L & %vs_WL_old & %Hfr & %Hprims & %Hresult & Hatom & Hval)".
    apply result_type_interp_split in Hresult.
    destruct Hresult as [vs_wl1 [vs_rest [-> [Hvs_wl1 Hresult]]]].
    apply result_type_interp_split in Hresult.
    destruct Hresult as [vs_wl' [vs_wl2 [-> [Hvs_wl' Hvs_wl2]]]].
    iFrame.
    iExists (vs_wl1 ++ vs_wl ++ vs_wl2).
    iPureIntro; split; last split.
    - rewrite app_assoc.
      eapply (frame_f_locs_update); [ | done | done | by rewrite -app_assoc].
      rewrite length_app.
      apply Forall2_length in Hvs_wl' as <-.
      apply Forall2_length in Hvs_wl1 as <-.
      apply Forall2_concat in Hprims.
      apply Forall2_length in Hprims as <-.
      done.
    - done.
    - apply result_type_interp_combine; first done.
      by apply result_type_interp_combine; last done.
  Qed.

  Lemma frame_interp_update_frame' se ηss L wl1 wl2 wl vs_localidxs vs_idxs vs_wl fr fr' :
    vs_idxs = seq ((length $ concat ηss) + length wl1) (length wl) ->
    vs_localidxs = map prelude.W.Mk_localidx vs_idxs ->
    Forall2 (λ i v, f_locs fr' !! localimm i = Some v) vs_localidxs vs_wl ->
    result_type_interp wl vs_wl ->
    frame_rel (λ i, i ∉ vs_idxs) fr fr' ->
    frame_interp rti sr se ηss L (wl1 ++ wl ++ wl2) fr -∗
    frame_interp rti sr se ηss L (wl1 ++ wl ++ wl2) fr'.
  Proof.
    iIntros (Hvs_idxs Hvs_localidxs HF Hres Hframe_rel) "Hfr".
    iApply frame_interp_update_frame; eauto.
    subst vs_localidxs.
    rewrite Forall2_fmap_l in HF.
    eapply Forall2_impl; [exact HF|].
    done.
  Qed.

  Lemma frame_interp_locals_ctx_length se ηss L WL fr :
    frame_interp rti sr se ηss L WL fr -∗ ⌜length ηss = length L⌝.
  Proof.
    iIntros "Hframe".
    iDestruct "Hframe" as (oss vss_L vs_WL Hf_locs Hhas_prims Hresult) "[Hatom Hval]".
    iDestruct (locals_interp_length with "Hval") as "->".
    iDestruct (big_sepL2_length with "Hatom") as "%Hoss_len".
    iPureIntro.
    apply Forall2_length in Hhas_prims as ->.
    done.
  Qed.

  Lemma frame_interp_update_frame_label se τ_old ηs L wl vs_l vs_idxs os fe fr fr' i τ :
    let L' := <[i:=τ]> L in
    L !! i = Some τ_old ->
    wl_interp (fe_wlocal_offset fe) wl fr ->
    fe_locals fe !! i = Some ηs ->
    vs_idxs = seq (sum_list_with length (take i (fe_locals fe))) (length ηs) ->
    has_prims ηs vs_l ->
    Forall2 (λ j v, f_locs fr' !! j = Some v) vs_idxs vs_l ->
    frame_rel (λ j, j ∉ vs_idxs) fr fr' ->
    atoms_interp os vs_l -∗
    value_interp rti sr se τ (SAtoms os) -∗
    frame_interp rti sr se (fe_locals fe) L wl fr -∗
    frame_interp rti sr se (fe_locals fe) L' wl fr'.
  Proof.
    intros L' Hlookup_L Hwl_interp Hlookup Hvs_idxs Hhas_prims_new Hf2 Hfrel.
    iIntros "Hatoms_new Hvalues Hframe".

    iDestruct (frame_interp_locals_ctx_length with "Hframe") as "%HL_len".

    iDestruct "Hframe" as
      "(%oss & %vss_L & %vs_WL & %Hfr & %Hhas_prims & %Hresult & Hatoms & Hval)".
    iFrame (Hresult).

    have Hsplit := take_drop_middle (fe_locals fe) i ηs Hlookup.
    rewrite <- Hsplit in Hhas_prims.
    apply List.Forall2_app_inv_l in Hhas_prims as (vss_L_pre & vss_L_rest & Hpre & Hrest & ->).
    destruct vss_L_rest as [| vs_mid vss_L_post]; [inversion Hrest |].
    apply Forall2_cons_1 in Hrest as [Hmid Hpost].

    iDestruct (locals_interp_lookup _ _ _ _ _ Hlookup_L with "Hval") as (oss_pre os_mid oss_post Hoss_eq) "[Hval_pre [_ Hval_post]]".

    iEval (rewrite Hoss_eq) in "Hatoms".
    iDestruct (locals_interp_length with "Hval_pre") as %Hlen_pre.
    iDestruct (locals_interp_length with "Hval_post") as %Hlen_post.
    apply Forall2_length in Hpre as Hvs_pre_len.
    apply Forall2_length in Hmid as Hvs_mid_len.
    apply Forall2_length in Hpost as Hvs_post_len.

    have Hlen_oss_pre : length oss_pre = length vss_L_pre.
    { rewrite <- Hlen_pre, length_take, <- Hvs_pre_len, length_take. lia. }
    have Hlen_oss_post : length oss_post = length vss_L_post.
    { rewrite <- Hlen_post, length_drop, <- Hvs_post_len, length_drop. lia. }

    iDestruct (big_sepL2_app_inv _ _ _ _ _ with "Hatoms") as "[Hatoms_pre Hatoms_rest]"; first by left.
    (* NOTE: the atoms_interp for the middle is being thrown away, since the values are being overwritten *)
    iDestruct (big_sepL2_cons with "Hatoms_rest") as "[_ Hatoms_post]".

    iExists (oss_pre ++ [os] ++ oss_post), (vss_L_pre ++ [vs_l] ++ vss_L_post).
    iSplit.
    {
      iPureIntro.
      rewrite !concat_app.
      rewrite concat_app concat_cons in Hfr.
      rewrite -!app_assoc.
      rewrite -!app_assoc in Hfr.
      clear_nils.
      eapply frame_f_locs_update.
      4: apply Hfr.
      3: done.
      2: done.
      subst vs_idxs.
      f_equal; last done.
      rewrite -sum_list_with_length_concat.
      eapply Forall2_sum_list_with_length.
      eapply Forall2_impl; [exact Hpre |].
      intros ηs' vs' Hprims'.
      apply Forall2_length in Hprims'.
      done.
    }
    iSplit.
    {
      iPureIntro.
      rewrite <- (take_drop_middle (fe_locals fe) i ηs Hlookup).
      apply Forall2_app; [exact Hpre |].
      apply Forall2_cons; by split.
    }
    iSplitL "Hatoms_new Hatoms_pre Hatoms_post".
    - by iFrame.
    - unfold locals_interp, L'.
      rewrite insert_take_drop.
      2: { eapply lookup_lt_Some. exact Hlookup_L. }
      iApply (big_sepL2_app with "Hval_pre").
      iApply big_sepL2_cons.
      iFrame.
  Qed.

  Lemma frame_interp_update_frame_label' se τ_old ηs L wl vs_l vs_idxs vs_localidxs os fe fr fr' i τ :
    let L' := <[i:=τ]> L in
    L !! i = Some τ_old ->
    wl_interp (fe_wlocal_offset fe) wl fr ->
    fe_locals fe !! i = Some ηs ->
    vs_idxs = seq (sum_list_with length (take i (fe_locals fe))) (length ηs) ->
    vs_localidxs = map prelude.W.Mk_localidx vs_idxs ->
    has_prims ηs vs_l ->
    Forall2 (λ j v, f_locs fr' !! localimm j = Some v) vs_localidxs vs_l ->
    frame_rel (λ j, j ∉ vs_idxs) fr fr' ->
    atoms_interp os vs_l -∗
    value_interp rti sr se τ (SAtoms os) -∗
    frame_interp rti sr se (fe_locals fe) L wl fr -∗
    frame_interp rti sr se (fe_locals fe) L' wl fr'.
  Proof.
    intros L' HlookupL Hwl_interp Hlookup Hvs_idxs Hvs_localidxs Hhas_prims_new Hf2 Hfrel.
    iIntros "Hatoms Hvalues Hframe".
    iApply (frame_interp_update_frame_label with "[$] [$] [$]" ); eauto.
    subst vs_localidxs.
    rewrite Forall2_fmap_l in Hf2.
    eapply Forall2_impl; [exact Hf2|].
    done.
  Qed.

  Lemma fe_wlocal_offset_length F :
    fe_wlocal_offset (fe_of_context F) = length $ concat (typing.fc_locals F).
  Proof.
    unfold fe_wlocal_offset. simpl.
    apply sum_list_with_length_concat.
  Qed.

  Lemma atom_interp_value_type_interp (ι : atomic_rep) (o : atom) (v : value) :
    has_arep ι o →
    atom_interp o v -∗
    ⌜value_type_interp (translate_arep ι) v⌝.
  Proof.
    intros Harep.
    destruct ι, o; simpl in *; try done.
    {
      iIntros "(%n & %n32 & %Hrep & -> & _)".
      iExists _; eauto.
    }
    all: iIntros "->"; iPureIntro; exists n; done.
  Qed.

  Lemma result_type_interp_of_atoms_interp ιs os vs :
    has_areps ιs (SAtoms os) ->
    atoms_interp os vs -∗
    ⌜result_type_interp (map translate_arep ιs) vs⌝.
  Proof.
    revert os vs.
    induction ιs as [| ι ιs' IH]; intros os vs Hιs'.
    - (* ιs = [] *)
      destruct Hιs' as (os' & Heq & Hfa).
      inversion Heq; subst.
      inversion Hfa; subst.
      iIntros "Hinterp".
      iDestruct (atoms_interp_nil_l with "Hinterp") as "->".
      iPureIntro.
      constructor.
    - (* ιs = ι :: ιs' *)
      destruct os as [| o os].
      {
        destruct Hιs' as (os' & Heq & Hfa).
        inversion Heq; subst.
        inversion Hfa.
      }
      apply has_areps_cons in Hιs' as [Hιs'_tl Hιs'_hd].
      iIntros "Hinterp".
      iDestruct (atoms_interp_cons_l with "Hinterp") as
      "(%v & %vs' & -> & Hv & Hos)".
      iDestruct (IH _ _ Hιs'_tl with "Hos") as "%Htl".
      iDestruct (atom_interp_value_type_interp ι o v Hιs'_hd with "Hv") as "%Hhd".
      iPureIntro.
      simpl.
      by constructor.
  Qed.


  Lemma value_type_interp_of_default ty :
    value_type_interp ty (default_of_value_type ty).
  Proof. destruct ty; by eexists. Qed.

  Lemma result_type_interp_of_defaults tys :
    result_type_interp tys (default_of_value_types tys).
  Proof.
    induction tys as [| ty tys IH].
    - constructor.
    - constructor; last done.
      apply value_type_interp_of_default.
  Qed.

  Lemma empty_closure_interp se ϕ cl :
    closure_interp rti sr ϕ senv_empty cl -∗
    closure_interp rti sr ϕ se cl.
  Proof.
    (* This seems true? *)
    iIntros "H".
    cbn.
  Admitted.

  Definition expect_heap_ptr (o : atom) : option (base_memory * location) :=
    match o with
    | PtrA (PtrHeap μ ℓ) => Some (μ, ℓ)
    | _ => None
    end.

  Lemma atom_interp_dup o v :
    expect_heap_ptr o = None ->
    Persistent (atom_interp o v).
  Proof.
    destruct o; cbn; intros Heq; try apply bi.pure_persistent.
    repeat (apply bi.pure_persistent
    || (apply bi.exist_persistent; intros ?x)
    || apply bi.sep_persistent).
    destruct p; try congruence.
    destruct x1; cbn;
    repeat (apply bi.pure_persistent
    || (apply bi.exist_persistent; intros ?x)
    || apply bi.sep_persistent).
  Qed.

  Lemma atoms_interp_dup os vs :
    Forall (λ o, expect_heap_ptr o = None) os ->
    Persistent (atoms_interp os vs).
  Proof.
    intros Hall.
    unfold atoms_interp.
    apply big_sepL2_persistent.
    intros k o v Hok Hvk.
    apply atom_interp_dup.
    rewrite Forall_lookup in Hall.
    exact (Hall k o Hok).
  Qed.

  Lemma atoms_interp_norefs_persistent (se: semantic_env (Σ:=Σ)) os vs :
    ref_flag_atoms_interp NoRefs (SAtoms os) ->
    Persistent (atoms_interp os vs).
  Proof.
    intros Href.
    unfold ref_flag_atoms_interp, forall_satoms in Href.
    apply atoms_interp_dup.
    rewrite Forall_lookup. intros k o Hok.
    rewrite Forall_lookup in Href.
    specialize (Href k o Hok).
    destruct o; simpl in *; try done.
    destruct p; simpl in *; done.
  Qed.

  Lemma value_interp_norefs_persistent (se: semantic_env (Σ:=Σ)) τ sv :
    ref_flag_atoms_interp NoRefs sv ->
    Persistent (value_interp rti sr se τ sv).
  Proof.
(*   intros Href. *)
(*   rewrite value_interp_eq. *)
(*   rewrite /add_skind_interp. *)
(*   apply bi.exist_persistent. intros sκ. *)
(*   apply bi.sep_persistent; [apply bi.pure_persistent |]. *)
(*   apply bi.sep_persistent; [apply bi.pure_persistent |]. *)
(*   (* Now need to show pre_type_interp is persistent *) *)
(*   destruct τ; simpl. *)
(*   - (* VarT *) admit. *)
(*   - (* I31T *) apply _. *)
(*   - (* NumT *) apply _. *)
(*   - unfold sum_interp. *)
(*     destruct k; simpl; try apply _. *)
(*     destruct r; simpl; try apply _. *)
(*     apply bi.exist_persistent. intros i. *)
(*     apply bi.exist_persistent. intros os'. *)
(*     apply bi.exist_persistent. intros off. *)
(*     apply bi.exist_persistent. intros count. *)
(*     apply bi.sep_persistent; [apply bi.pure_persistent |]. *)
(*     apply bi.sep_persistent; [apply bi.pure_persistent |]. *)
(*     apply bi.sep_persistent; [apply bi.pure_persistent |]. *)
(*     destruct (list_lookup i (map (type_interp rti sr) l)) eqn:Hlookup; simpl; try apply _. *)
(*     admit. *)
(*   - (* SumT *) apply sum_interp_persistent. (* assume, uses IH *) *)
(*   - (* VariantT *) apply variant_interp_persistent. (* assume *) *)
(*   - (* ProdT *) apply prod_interp_persistent. (* assume, uses IH *) *)
(*   - (* StructT *) apply struct_interp_persistent. (* assume *) *)
(*   - (* RefT *) (* impossible since NoRefs rules out RefT *) *)
(*     exfalso. eapply has_kind_valtype_no_reftype. exact Hkind. *)
(*   - (* CodeRefT *) apply coderef_interp_persistent. (* assume *) *)
(*   - (* SerT *) apply ser_interp_persistent. (* assume *) *)
(*   - (* PlugT *) apply plug_interp_persistent. (* assume *) *)
(*   - (* SpanT *) apply span_interp_persistent. (* assume *) *)
(*   - (* RecT *) apply rec_interp_persistent. (* assume, uses IH *) *)
(*   - (* ExistsMemT *) apply exists_mem_interp_persistent. (* assume *) *)
(*   - (* ExistsRepT *) apply exists_rep_interp_persistent. (* assume *) *)
(*   - (* ExistsSizeT *) apply exists_size_interp_persistent. (* assume *) *)
(*   - (* ExistsTypeT *) apply exists_type_interp_persistent. (* assume *) *)
(* Qed. *)
  Admitted.

End common.
