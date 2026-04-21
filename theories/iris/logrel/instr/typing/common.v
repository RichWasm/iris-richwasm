From Stdlib Require Export ZArith.

From stdpp Require Export base list.

Require Export RecordUpdate.RecordUpdate.

From iris.proofmode Require Export base proofmode classes.

From RichWasm.wasm Require Export operations.
From RichWasm.named_props Require Export named_props custom_syntax.
From RichWasm Require Export layout syntax typing.
From RichWasm.compiler Require Export prelude codegen instruction module.
From RichWasm.iris Require Export autowp memory util wp_codegen.
From RichWasm.iris.language Require Export cwp logpred.
Require Export RichWasm.iris.logrel.instr.
Require Import RichWasm.util.

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
    exists p; auto.
  Qed.

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

  Lemma value_interp_coderef se os κ ϕ :
    value_interp rti sr se (CodeRefT κ ϕ) (SAtoms os) -∗ ∃ n, ⌜os = [I32A n]⌝.
  Proof.
    iIntros "Hval".
    iPoseProof (value_interp_eq with "Hval") as "Hval".
    iEval (cbn) in "Hval".
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
    ⊢ ∃ o, atom_interp o (default_of_value_type $ translate_arep ι) ∗ ⌜has_arep ι o⌝.
  Proof.
    destruct ι.
    - iExists (PtrA _); iSplit; last done.
      simpl.
      iExists _, _.
      iSplit; last iSplit; first done.
      1: done.
      iExists (RootInt 0).
      iSplit; first iPureIntro; simpl.
      1: constructor.
      by instantiate (1 := PtrInt _).
    - by iExists (I32A _).
    - by iExists (I64A _).
    - by iExists (F32A _).
    - by iExists (F64A _).
  Qed.

  Lemma atoms_interp_and_areps_of_default_of_areps ιs :
    ⊢ ∃ os, atoms_interp os (default_of_value_types $ translate_arep <$> ιs) ∗ ⌜has_areps ιs (SAtoms os)⌝.
  Proof.
    induction ιs as [|ι ιs' IH].
    - iExists [].
      iSplit; first by simpl.
      by iExists [].
    - iDestruct IH as "(%os' & IHatoms & %IHareps)".
      iEval (unfold default_of_value_types).
      rewrite fmap_cons.
      rewrite map_cons.
      iDestruct (atom_interp_and_arep_of_default_of_arep ι) as "(%o & Hatom & %Harep)".
      iExists (o :: os').
      rewrite atoms_interp_cons.
      iFrame "#".
      iPureIntro.
      by apply has_areps_cons.
  Qed.

  Lemma frame_interp_wl_interp se F L WL ηss fr :
    frame_interp rti sr se ηss L WL fr -∗
    ⌜wl_interp (fe_wlocal_offset (fe_of_context F)) WL fr⌝.
  Proof.
    iIntros "Hframe".
    iDestruct "Hframe" as
      "(%oss & %vs_L & %vs_WL & %Hfr & %Hprims & %Hresult & Hatom & Hval)".
    unfold wl_interp.

    (* This is my best guess at the exists given Hfr and Hresult. Should be right *)
    iExists vs_L. iExists vs_WL. iExists [].
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
    ∃ rf, Forall2 (λ τ ρ, has_kind F τ (VALTYPE ρ rf)) τs ρs.
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

(* Lemma frame_interp_update_frame se ηss L wl1 wl2 wl vs_idxs vs_wl fr fr' : *)
(*     vs_idxs = rev (seq ((length $ concat ηss) + length wl1) (length wl)) -> *)
(*     Forall2 (λ i v, f_locs fr' !! i = Some v) vs_idxs vs_wl -> *)
(*     result_type_interp wl vs_wl -> *)
(*     frame_rel (λ i, i ∉ vs_idxs) fr fr' -> *)
(*     frame_interp rti sr se ηss L (wl1 ++ wl ++ wl2) fr -∗ *)
(*     frame_interp rti sr se ηss L (wl1 ++ wl ++ wl2) fr'. *)
(*   Proof. *)
(*     intros Hvs_idxs_wl Hnew_vals Hres Hfrel. *)
(*     iIntros "Hframe". *)
(*     iDestruct "Hframe" as *)
(*       "(%oss & %vs_L & %vs_WL_old & %Hfr & %Hprims & %Hresult & Hatom & Hval)". *)
(*     apply result_type_interp_split in Hresult. *)
(*     destruct Hresult as [vs_wl1 [vs_rest [-> [Hvs_wl1 Hresult]]]]. *)
(*     apply result_type_interp_split in Hresult. *)
(*     destruct Hresult as [vs_wl' [vs_wl2 [-> [Hvs_wl' Hvs_wl2]]]]. *)
(*     iFrame. *)
(*     iExists (vs_wl1 ++ vs_wl ++ vs_wl2). *)
(*     iPureIntro; split; last split. *)
(*     - rewrite app_assoc. *)
(*       eapply (frame_f_locs_update); [ | done | done | by rewrite -app_assoc]. *)
(*       rewrite length_app. *)
(*       apply Forall2_length in Hvs_wl' as <-. *)
(*       apply Forall2_length in Hvs_wl1 as <-. *)
(*       apply Forall2_length in Hprims as <-. *)
(*       apply Forall2_length in Hnew_vals. *)
(*       rewrite Hvs_idxs_wl length_rev length_seq in Hnew_vals. *)
(*       lia. *)
(*     - done. *)
(*     - apply result_type_interp_combine; first done. *)
(*       by apply result_type_interp_combine; last done. *)
(*   Qed. *)

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
      "(%oss & %vs_L & %vs_WL_old & %Hfr & %Hprims & %Hresult & Hatom & Hval)".
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
    closure_interp rti sr senv_empty ϕ cl -∗
    closure_interp rti sr se ϕ cl.
  Proof.
    (* This seems true? *)
    iIntros "H".
    cbn.

  Admitted.

End common.
