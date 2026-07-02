From Stdlib Require Export ZArith.

From stdpp Require Export base list.

Require Export RecordUpdate.RecordUpdate.

From iris.proofmode Require Export base proofmode classes.

From RichWasm.named_props Require Export named_props custom_syntax.
From RichWasm Require Export layout syntax typing util.
Require Export RichWasm.wasm.operations.
From RichWasm.compiler Require Export prelude codegen instruction module.
From RichWasm.iris Require Export autowp memory logrel util numerics.
From RichWasm.iris.logrel Require Export util.
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

  Definition atom_copyable (o : atom) : Prop :=
    match o with
    | PtrA (PtrHeap MemMM ℓ) => False
    | _ => True
    end.

  Inductive ptr_shaped : pointer -> N -> Prop :=
  | IntShaped :
    ∀ n : N, ptr_shaped (PtrInt n) (2 * n)%N
  | PtrShaped :
    ∀ ℓ μ a,
    (a `mod` 4 = 0)%N ->
    a <> 0%N ->
    ptr_shaped (PtrHeap μ ℓ) (tag_address μ a).

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
    iIntros "Hos".
    iDestruct "Hos" as "(%oss & -> & Hoss)".
    iEval (rewrite map_app) in "Hoss".
    iDestruct (big_sepL2_app_inv_l with "Hoss") as (oss1 oss2 ->) "[Hoss1 Hoss2]".
    iExists (concat oss1), (concat oss2).
    rewrite concat_app.
    iSplit; first done.
    iSplitL "Hoss1".
    - iExists oss1. by iSplit.
    - iExists oss2. by iSplit.
  Qed.

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

  Definition value_to_atom (v : value) : atom :=
    match v with
    | VAL_int32 n32 => I32A n32
    | VAL_int64 n64 => I64A n64
    | VAL_float32 f32 => F32A f32
    | VAL_float64 f64 => F64A f64
    end.

  Definition values_to_atoms (vs : list value) :=
    map value_to_atom vs.

  Lemma atom_interp_value_as_atom v :
    ⊢ atom_interp (value_to_atom v) v.
  Proof.
    destruct v; simpl; by iIntros.
  Qed.

  Lemma atoms_interp_values_as_atoms vs :
   ⊢ atoms_interp (values_to_atoms vs) vs.
  Proof.
    iInduction vs as [|v vs] "IH"; first by simpl.
    rewrite /values_to_atoms map_cons.
    rewrite atoms_interp_cons.
    iFrame "#".
    iApply atom_interp_value_as_atom.
  Qed.

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
    destruct μ; typeclasses eauto.
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

  Global Instance atom_interp_value_to_atom_persistent v :
    Persistent (atom_interp (value_to_atom v) v).
  Proof.
    unfold Persistent.
    iIntros "H !>".
    iApply atom_interp_value_as_atom.
  Qed.

  Global Instance atoms_interp_values_to_atoms_persistent vs :
    Persistent (atoms_interp (values_to_atoms vs) vs).
  Proof.
    unfold Persistent.
    iIntros "H !>".
    iApply atoms_interp_values_as_atoms.
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



  Lemma frame_interp_wl_interp se F L WL fr :
    frame_interp rti sr se F.(typing.fc_locals) L WL fr -∗
    ⌜wl_interp (fe_wlocal_offset (fe_of_context F)) WL fr⌝.
  Proof.
    iIntros "Hframe".
    iDestruct "Hframe" as
      "(%oss & %vss_L & %vs_WL & %Hfr & %Hprims & %Hresult & Hatom & Hval)".
    iPureIntro.
    unfold wl_interp.
    exists (concat vss_L), vs_WL, [].
    rewrite app_nil_r.
    split; first exact Hfr.
    split; last exact Hresult.
    rewrite -sum_list_with_length_concat.
    symmetry.
    unfold fe_wlocal_offset, fe_of_context. simpl.
    apply Forall2_sum_list_with_length.
    eapply Forall2_impl; first exact Hprims.
    intros ηs vs Hprim.
    by apply Forall2_length in Hprim.
  Qed.

  Lemma root_pointer_heap_shp_inv rp μ ℓ :
    root_pointer_interp rp (PtrHeap μ ℓ) -∗
    ⌜∃ a, rp = RootHeap μ a⌝.
  Proof.
    iIntros "H".
    destruct rp; first done.
    cbn.
    destruct μ, μ0; try done; by iExists _.
  Qed.

  Lemma type_arep_of_type_kind F se τ ρ ξ ιs :
    type_ctx_interp F.(fc_type_vars) se ->
    type_kind F.(fc_type_vars) τ = Some (VALTYPE ρ ξ) ->
    eval_rep EmptyEnv ρ = Some ιs ->
    @type_arep Σ se τ = Some ιs.
  Proof.
    intros Htype Htk Heval.
    rewrite /type_arep.
    destruct τ; cbn [type_kind] in Htk.
    { (* VarT n *)
      apply (Forall2_lookup_l _ _ _ _ _ Htype) in Htk as [[sκ T] (Hse & Hek & _)].
      cbn. cbn in Hse. rewrite Hse. cbn.
      rewrite (eval_kind_of_eval_rep se _ _ (eval_rep_emptyenv _ _ Heval se) ξ) in Hek.
      by injection Hek as <-.
    }
    all: apply Some_inj in Htk; subst; cbn;
         rewrite (eval_rep_emptyenv _ _ Heval se); by cbn.
  Qed.

  Lemma translate_type_comp_sem F se τ t :
    sem_env_interp F se ->
    prelude.translate_type F.(fc_type_vars) τ = Some t ->
    @translate_type Σ se τ = Some t.
  Proof.
    intros [_ Htype] Hpre.
    unfold prelude.translate_type, type_rep, translate_rep in Hpre.
    apply bind_Some in Hpre as [ρ [Hkr Hpre]].
    apply bind_Some in Hkr as [κ [Htk Hkr]].
    apply fmap_Some in Hpre as [ιs [Heval ->]].
    destruct κ as [ρ' ξ | σ ξ]; [| discriminate Hkr].
    injection Hkr as <-.
    rewrite /translate_type.
    Opaque type_arep.
    simpl.
    Transparent type_arep.
    by rewrite (type_arep_of_type_kind F se τ _ ξ _ Htype Htk Heval).
  Qed.

  Lemma translate_types_comp_sem F τs ts se :
    sem_env_interp F se ->
    prelude.translate_types F.(fc_type_vars) τs = Some ts ->
    @translate_types Σ se τs = Some ts.
  Proof.
    intros Hsem Hpre.
    unfold prelude.translate_types in Hpre.
    apply fmap_Some in Hpre as [tss [Hmapm ->]].
    rewrite mapM_Some in Hmapm.
    unfold translate_types.
    rewrite fmap_Some.
    eexists; split; last done.
    rewrite mapM_Some.
    eapply Forall2_impl; first exact Hmapm.
    intros τ t' Ht'.
    by eapply translate_type_comp_sem.
  Qed.

  Lemma translate_type_interp_length se τ ts os :
    translate_type se τ = Some ts ->
    value_interp rti sr se τ (SAtoms os) -∗
    ⌜length os = length ts⌝.
  Proof.
    iIntros (Hts) "Hval".
    iDestruct (value_interp_skind with "Hval") as %(sκ & Hsκ & Hsv).
    iPureIntro.
    unfold translate_type in Hts.
    apply fmap_Some in Hts as [ιs [Harep ->]].
    unfold type_arep in Harep.
    apply bind_Some in Harep as [sκ' [Hskind Hrep]].
    destruct sκ' as [ιs' ξ' | σ']; last discriminate Hrep.
    cbn in Hrep. injection Hrep as ->.
    rewrite Hskind in Hsκ. injection Hsκ as <-.
    destruct Hsv as [Hareps _].
    rewrite length_map.
    symmetry.
    by apply has_areps_length.
  Qed.

  Lemma translate_types_sem_interp_length se τs ts os :
    translate_types se τs = Some ts ->
    values_interp rti sr se τs os -∗
    ⌜length os = length ts⌝.
  Proof.
    revert se ts os.
    induction τs as [|τ τs IHτs]; intros se ts os H.
    - unfold translate_types in H.
      apply fmap_Some in H as [tss [Hmapм ->]].
      cbn in Hmapм.
      injection Hmapм as <-.
      iIntros "Hval".
      iPoseProof (values_interp_nil_l with "Hval") as "->".
      done.
    - unfold translate_types in H.
      apply fmap_Some in H as [tss [Hmapм ->]].
      apply mapM_Some in Hmapм.
      destruct tss as [|t_head tss_rest]; first inversion Hmapм.
      apply Forall2_cons_1 in Hmapм as [Hhead Hrest].
      apply mapM_Some in Hrest.
      assert (Htail : translate_types se τs = Some (concat tss_rest)).
      {
        unfold translate_types.
        rewrite fmap_Some.
        eexists; by split.
      }
      iIntros "Hval".
      iPoseProof (values_interp_cons_l with "Hval") as "(%os1 & %os2 & -> & Hhd & Htl)".
      iDestruct (translate_type_interp_length with "Hhd") as %Hlen1; first done.
      iDestruct (IHτs se _ os2 Htail with "Htl") as %Hlen2.
      iPureIntro.
      by rewrite length_app Hlen1 Hlen2 concat_cons length_app.
  Qed.

  Lemma translate_types_comp_interp_length F τs ts se os :
    sem_env_interp F se ->
    prelude.translate_types F.(fc_type_vars) τs = Some ts ->
    values_interp rti sr se τs os -∗
    ⌜length os = length ts⌝.
  Proof.
    intros. iIntros "Hval".
    iApply translate_types_sem_interp_length; last done.
    by eapply translate_types_comp_sem.
  Qed.

  Lemma labels_interp_cons se fr wl lmask F L B τs ts Φ :
    sem_env_interp F se ->
    prelude.translate_types F.(fc_type_vars) τs = Some ts ->
    □ (∀ fr' vs',
       (⌜frame_rel lmask fr fr'⌝ ∗ frame_interp rti sr se F.(typing.fc_locals) L wl fr' ∗
          (∃ os', values_interp rti sr se τs os' ∗ atoms_interp os' vs') ∗
          (∃ θ0, rt_token rti sr lpall θ0) ∗ na_own logrel_nais ⊤) -∗
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



  (* place rt_otken lmask things here *)
  Lemma layout_ok_lmask_mono lm hm lmask1 lmask2 :
    (∀ ℓ, lmask1 ℓ → lmask2 ℓ) →
    layout_ok lmask2 lm hm →
    layout_ok lmask1 lm hm.
  Proof.
    unfold layout_ok.
    intros Hle Hall.
    eauto using map_Forall2_impl.
  Qed.

  Lemma rt_token_mono lmask lmask' θ:
    (∀ ℓ, lmask' ℓ -> lmask ℓ) ->
    rt_token rti sr lmask θ -∗ rt_token rti sr lmask' θ.
  Proof.
    intros Hmask. iIntros "Hrt".
    open_rt "Hrt".
    iFrame.
    iPureIntro.
    split; first done; split; first done; split; last done.
    unfold layout_ok in *.
    eapply map_Forall2_impl; [exact Hlayoutok|].
    intros *. cbn.
    intros Hold Hlmask'.
    apply Hmask in Hlmask'.
    apply Hold; done.
  Qed.

  Lemma rt_token_lpall lmask θ:
    rt_token rti sr lpall θ -∗ rt_token rti sr lmask θ.
  Proof.
    iIntros "Hrt".
    iApply rt_token_mono; last done.
    done.
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

  Lemma value_interp_ref_sz se κ μ β τ os :
    value_interp rti sr se (RefT κ μ β τ) (SAtoms os) -∗ ⌜length os = 1⌝.
  Proof.
    iIntros "(%sκ & _ & _ & H)".
    destruct μ; destruct β.
    - destruct (lookup_mem se n) eqn:Hn; cbn in Hn; last (cbn; by rewrite Hn).
      cbn.
      rewrite Hn.
      destruct b.
      + iDestruct "H" as "(% & % & % & %Hos & _)". by inversion Hos.
      + iDestruct "H" as "(% & % & %Hos & _)". by inversion Hos.
    - destruct (lookup_mem se n) eqn:Hn; cbn in Hn; last (cbn; by rewrite Hn).
      cbn.
      rewrite Hn.
      destruct b.
      + iDestruct "H" as "(% & % & % & %Hos & _)". by inversion Hos.
      + iDestruct "H" as "(% & % & % & %Hos & _)". by inversion Hos.
    - cbn. destruct b.
      + iDestruct "H" as "(% & % & % & %Hos & _)". by inversion Hos.
      + iDestruct "H" as "(% & % & %Hos & _)". by inversion Hos.
    - cbn. destruct b.
      + iDestruct "H" as "(% & % & % & %Hos & _)". by inversion Hos.
      + iDestruct "H" as "(% & % & % & %Hos & _)". by inversion Hos.
  Qed.

  (* useful lemma for proving compat lemmas for instructions erased by the compiler. *)
  Lemma sem_type_erased M F L WT WL lmask ψ τs1 τs2 :
    ψ = InstrT τs1 τs2 ->
    ⊢ (∀ se vs,
          ⌜sem_env_interp F se⌝ -∗
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
    - by iApply ("Hcast" with "[//]").
  Qed.

  Lemma sem_type_erased_nop M F L WT WL lmask ψ τs1 τs2 :
    ψ = InstrT τs1 τs2 ->
    ⊢ (∀ se fr B R os,
     "%Hse" ∷ ⌜sem_env_interp F se⌝ -∗
     "#Hinst" ∷ instance_interp rti sr mr M WT (f_inst fr) -∗
     "#Hlabels"
     ∷ labels_interp rti sr se (typing.fc_locals F) fr WL lmask 
         (fc_labels F) B -∗
     "#Hreturn" ∷ return_interp rti sr se (fc_return F) R -∗
          values_interp rti sr se τs1 os -∗
          ▷values_interp rti sr se τs2 os) -∗
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


  Lemma has_prim_has_arep η v :
    has_prim η v ->
    has_arep (prim_to_arep η) (value_to_atom v).
  Proof.
    intros Hprim.
    destruct v, η; simpl; done.
  Qed.

  Lemma has_prims_has_areps ηs vs :
    has_prims ηs vs ->
    has_areps (map prim_to_arep ηs) (SAtoms (values_to_atoms vs)).
  Proof.
    revert ηs.
    induction vs; intros ηs Hprims.
    - inversion Hprims; subst.
      simpl.
      eexists.
      by split.
    - destruct ηs as [| η ηs]; first inversion Hprims.
      simpl.
      apply has_areps_cons.
      apply Forall2_cons in Hprims as [Hprim Hprims].
      split; first by apply IHvs.
      by apply has_prim_has_arep.
  Qed.

  Lemma values_to_atoms_norefs vs :
    Forall (forall_ptr_atom norefs_ptr_interp) (values_to_atoms vs).
  Proof.
    induction vs as [|v vs]; simpl; first done.
    apply Forall_cons.
    split.
    - by destruct v.
    - apply IHvs.
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

  Lemma Forall2_Forall2_length {A B} {P : A -> B -> Prop} xss yss :
    Forall2 (Forall2 P) xss yss ->
    map length xss = map length yss.
  Proof.
    intros Hall. induction Hall.
    - reflexivity.
    - cbn.
      f_equal; last apply IHHall.
      by eapply Forall2_length.
  Qed.

  Lemma big_sep_atoms_lens oss vss_L :
    ⊢ ([∗ list] os;vs_L ∈ oss;vss_L, atoms_interp os vs_L) -∗ ⌜map length oss = map length vss_L⌝.
  Proof.
    revert vss_L.
    induction oss; iIntros (vss_L) "Hats".
    - iPoseProof (big_sepL2_nil_inv_l with "Hats") as "->".
      done.
    - iPoseProof (big_sepL2_cons_inv_l with "Hats") as "(%vs & %vss_L' & -> & Hvs & Hvss)".
      iPoseProof (atoms_interp_length with "Hvs") as "%Hvs".
      iPoseProof (IHoss vss_L' with "Hvss") as "%Hvss".
      by rewrite !map_cons Hvs Hvss.
  Qed.

  Lemma frame_interp_locs_len se ηss L WL fr :
    frame_interp rti sr se ηss L WL fr -∗ ⌜(length (f_locs fr) = length (concat ηss) + length WL)%nat⌝.
  Proof.
    iIntros "Hframe".
    iDestruct "Hframe" as (oss vss_L vs_WL Hf_locs Hhas_prims Hresult) "[Hatom Hval]".
    apply Forall2_Forall2_length in Hhas_prims.
    apply Forall2_length in Hresult.
    iPoseProof (big_sep_atoms_lens with "Hatom") as "%Hoss_len".
    iDestruct (big_sepL2_length with "Hval") as "%Hoss_len'".
    rewrite Hf_locs length_app !length_concat.
    iPureIntro; congruence.
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


  Lemma type_interp_skind_svalue (τ : type) se sv :
    type_interp rti sr τ se sv -∗ ∃ sκ, ⌜type_skind se τ = Some sκ⌝ ∗ ⌜skind_has_svalue sκ sv⌝.
  Proof.
    iIntros "H".
    rewrite type_interp_eq.
    iDestruct "H" as (sκ) "[%Hsk [%Hsv _]]".
    iExists sκ. by iSplit; iPureIntro.
  Qed.

  Lemma skind_rec_interp_unfold sκ T (se: semantic_env (Σ:=Σ)) sv :
    skind_rec_interp sκ T se sv ≡ (▷ T (senv_insert_type sκ (skind_rec_interp sκ T se) se) sv)%I.
  Proof.
    simpl.
    set f := (λ T0 : leibnizO semantic_value -n> iPropO Σ, λne sv0 : leibnizO semantic_value, (▷ T (se.1, (sκ, T0) :: se.2) sv0)%I).
     etransitivity.
     - exact (fixpoint_unfold f sv).
     - simpl. reflexivity.
  Qed.

  (* this is going to need some sκ κ things *)
  Lemma skind_rec_interp_unfold_TEST_NO_SV sκ κ τ (se: semantic_env (Σ:=Σ)) :
    eval_kind se κ = Some sκ ->
    skind_rec_interp sκ (type_interp rti sr τ) se ≡
      (value_interp rti sr se (RecT κ τ))%I.
  Proof.
    intros Heval.
    (* simpl. *)
    iIntros (sv).
    rewrite value_interp_eq.
    iSplitR; iIntros "H".
    - iExists sκ.
      assert (hhh: type_skind se (RecT κ τ) = Some sκ). {
        cbn.
        done.
      }

      iAssert ((⌜skind_has_svalue sκ sv⌝)%I) as "#hope". {
        (* scary *)
        (* PLEASE HELP IF THIS ISN'T TRUE A LOT OF THINGS HAVE TO CHANGE *)
        (* the reason it's so scary is bc I assume that things that you put into the sem env *)
        (* are equivalent to value_interp *)
        (* and the thing you put into the environment for rec stuff is skind_rec_interp *)
        (* so if it's not equal to value_interp....... *)
        simpl.
        set f := (λ T0 : leibnizO semantic_value -n> iPropO Σ, λne sv0 : leibnizO semantic_value,
                   (▷ type_interp rti sr τ (se.1, (sκ, T0) :: se.2) sv0)%I).
        rewrite (fixpoint_unfold f sv).
        unfold f.
        Opaque skind_has_svalue.
        cbn.
        rewrite type_interp_eq.
        unfold add_skind_interp.
        Opaque pre_type_interp.
        Opaque type_skind.
        cbn.
        fold f.
        (* okay so if we have has_kind? or some well formedness on τ *)
        (* which we DONT HAVE RN so this isn't provable *)
        (* then τ's kind is also κ and so I think the type_skind will also just be sκ? *)
        (* and if that's true (which honestly maybe not but I think it will end up okay) *)
        (* then we're done *)

        (* well, after dealing with the later. Hm. *)





        Transparent skind_has_svalue.
        Transparent pre_type_interp.
        Transparent type_skind.
        admit.
      }
      iSplitR; [done| iSplitR; [done|]].
      cbn.
      rewrite Heval.
      done.
    - cbn.
      iDestruct "H" as "(%sκ' & %toinvert & #hsvalue & H)".
      rewrite Heval in toinvert; inversion toinvert; subst sκ'.
      rewrite Heval.
      done.
  Admitted.

  (* As a test, this is true when you're given a specific sv with skind_has_svalue *)
  (* the reason this isn't enough for me is bc you just put semantic types into sem envs,
     not just iProps *)
  Lemma skind_rec_interp_unfold_TEST sκ κ τ (se: semantic_env (Σ:=Σ)) sv :
    eval_kind se κ = Some sκ -> skind_has_svalue sκ sv ->
    skind_rec_interp sκ (type_interp rti sr τ) se sv ≡
      (value_interp rti sr se (RecT κ τ) sv)%I.
  Proof.
    intros Heval Hsv.
    simpl.
    set f := (λ T0 : leibnizO semantic_value -n> iPropO Σ, λne sv0 : leibnizO semantic_value,
                   (▷ type_interp rti sr τ (se.1, (sκ, T0) :: se.2) sv0)%I).
    rewrite value_interp_eq.
    iSplitR; iIntros "H".
    - iExists sκ.
      (* ideally,  *)
      iSplitR; [done| iSplitR; [done|]].
      cbn.
      rewrite Heval. unfold f.
      done.
    - cbn.
      iDestruct "H" as "(%sκ' & %toinvert & #hsvalue & H)".
      rewrite Heval in toinvert; inversion toinvert; subst sκ'.
      rewrite Heval.
      done.
  Qed.

  Lemma rec_interp_unfold κ T (se: semantic_env (Σ:=Σ)) sv :
    rec_interp κ T se sv ≡
    match eval_kind_se se κ with
    | Some sκ => ▷ T (senv_insert_type sκ (skind_rec_interp sκ T se) se) sv
    | None => False
    end%I.
  Proof.
    unfold rec_interp. simpl.
    destruct (eval_kind se κ) as [sκ|]; simpl.
    - set f := (λ T0 : leibnizO semantic_value -n> iPropO Σ,
      λne sv0 : leibnizO semantic_value,
      (▷ T (se.1, (sκ, T0) :: se.2) sv0)%I).
      etransitivity.
      + exact (fixpoint_unfold f sv).
      + simpl. reflexivity.
    - reflexivity.
  Qed.

  Lemma value_interp_type_plug se vs ηs :
    ⌜has_prims ηs vs⌝ -∗
    value_interp rti sr se (type_plug_prim ηs) (SAtoms (values_to_atoms vs)).
  Proof.
    iIntros "%Hprims".
    rewrite value_interp_eq /add_skind_interp.
    unfold type_plug_prim, type_plug. simpl.
    set ρ := ProdR (map (AtomR ∘ prim_to_arep) ηs).
    have Heval : eval_rep se ρ = Some (map prim_to_arep ηs).
    { apply eval_rep_prod_atoms. }
    iExists (SVALTYPE (map prim_to_arep ηs) NoRefs).
    iSplit.
    - iPureIntro. unfold type_skind. simpl.
      have Heval_kind := eval_kind_of_eval_rep se ρ _ Heval NoRefs.
      rewrite -Heval_kind.
      done.
    - apply has_prims_has_areps in Hprims as Hareps.
      iSplit; last done.
      iPureIntro. simpl.
      split; first done.
      apply values_to_atoms_norefs.
  Qed.

  Lemma has_areps_imp_word_has_flag ιs os:
    has_areps ιs (SAtoms os) ->
    Forall2 word_has_flag (concat (map arep_flags ιs)) (flat_map serialize_atom os).
  Proof.
    generalize dependent ιs.
    induction os as [|o os].
    - intros ιs Hareps.
      inversion Hareps.
      destruct H as [toinvert Harepp].
      inversion toinvert; subst.
      apply Forall2_nil_inv_r in Harepp; subst; done.
    - intros ιs Hareps.
      inversion Hareps.
      destruct H as [toinvert Harepp].
      inversion toinvert; subst; clear toinvert.
      destruct ιs as [|ι ιs]; [apply Forall2_nil_cons_inv in Harepp; done|].
      cbn.
      inversion Harepp; subst.
      assert (length (arep_flags ι) = length (serialize_atom o)). {
        destruct ι; destruct o; try done.
      }
      apply Forall2_app.
      + destruct ι; destruct o; try done; cbn; try (apply Forall2_cons; cbn; done).
        * apply Forall2_cons. cbn.
          split; [done|].
          apply Forall2_cons; cbn; done.
        * apply Forall2_cons. cbn.
          split; [done|].
          apply Forall2_cons; cbn; done.
      + apply IHos.
        exists os; done.
  Qed.

  Lemma forall_ptr_atom_to_word_ref_flag_interp ξ os:
    Forall (forall_ptr_atom (ref_flag_ptr_interp ξ)) os ->
    Forall (forall_ptr_word (ref_flag_ptr_interp ξ)) (concat (map serialize_atom os)).
  Proof.
    intros Hatom.
    induction os as [|o os].
    - done.
    - apply Forall_cons in Hatom as (Ho & Hatom).
      apply IHos in Hatom.
      cbn.
      rewrite Forall_app.
      split; try done.
      clear Hatom IHos.
      destruct o; cbn in *; try (apply Forall_singleton; cbn in *; done).
      + apply Forall_cons.
        cbn.
        split; [done|].
        apply Forall_singleton.
        cbn; done.
      + apply Forall_cons.
        cbn.
        split; [done|].
        apply Forall_singleton.
        cbn; done.
  Qed.

  Lemma has_arep_means_equal_lengths ιs os:
    Forall2 has_arep ιs os ->
    length (concat (map serialize_atom os)) = length (concat (map arep_flags ιs)).
  Proof.
    generalize dependent os.
    induction ιs as [|ι ιs].
    - intros.
      destruct os; [|apply Forall2_nil_cons_inv in H; done].
      by cbn.
    - intros os Hareps.
      destruct os as [| o os]; [apply Forall2_cons_nil_inv in Hareps; done|].
      apply Forall2_cons in Hareps as (Harep & Hareps).
      cbn.
      rewrite !length_app.
      specialize (IHιs os Hareps).
      assert (length (serialize_atom o) = length (arep_flags ι)). {
        destruct ι; destruct o; try done.
      }
      lia.
  Qed.

  Lemma atom_interp_to_weak_memMM o v lmask θ:
    rt_token rti sr lmask θ -∗ atom_interp o v -∗
    rt_token rti sr lmask θ ∗ atom_interp_weak θ MemMM o v.
  Proof.
    iIntros "Hrt Ha".
    cbn.
    unfold atom_interp_weak.
    destruct o; try (by iFrame).
    destruct p.
    - cbn. unfold root_pointer_interp.
      iFrame.
      iDestruct "Ha" as "(%n0 & %n32 & %Nrepr & -> & (%rp & %Hrepr & Ha))".
      destruct rp; [| destruct μ; try done].
      iDestruct "Ha" as "<-".
      inversion Hrepr; subst.
      iExists ((2 * n1)%N), n32.
      iSplitR; [done| iSplitR; [done|]].
      iPureIntro. constructor.
    - cbn.
      unfold root_pointer_interp.
      iDestruct "Ha" as "(%n0 & %n32 & %Nrepr & -> & (%rp & %Hrepr & Ha))".
      destruct rp; try done; destruct μ0; destruct μ; try done.
      + iAssert (⌜θ !! ℓ = Some (MemMM, a)⌝)%I with "[Hrt Ha]" as "%Hθℓ". {
          iDestruct "Hrt" as "(%rm & %lm & %hm & Haddr & _)".
          iPoseProof (ghost_map_lookup with "[$] [$]") as "%Hθℓ".
          done.
        }
        iFrame.
        iExists n0, n32.
        iSplitR; [done| iSplitR; [done|]].
        inversion Hrepr; subst.
        iPureIntro.
        by constructor.
        (* WORRY: ℓ ↦addr is left here *)
        (* but actually probably fine lol *)
      + iFrame.
        iExists n0, n32.
        iSplitR; [done| iSplitR; [done|]].
        iFrame.
        iPureIntro.
        done.
  Qed.

  Lemma atoms_interp_to_weak_memMM os vs lmask θ:
    rt_token rti sr lmask θ -∗ atoms_interp os vs -∗
    rt_token rti sr lmask θ ∗ ([∗ list] o;v ∈ os;vs, atom_interp_weak θ MemMM o v).
  Proof.
    generalize dependent vs.
    induction os.
    - iIntros (vs) "Hrt Has".
      iFrame.
    - iIntros (vs) "Hrt Has".
      destruct vs as [|v vs]; [done|].
      iPoseProof (big_sepL2_cons with "[$Has]") as "[Hov Has]".
      iPoseProof (atom_interp_to_weak_memMM with "[$Hrt] [$Hov]") as "[Hrt Hweak]".
      rewrite big_sepL2_cons.
      iEval (cbn -[atom_interp]) in "Has".
      iPoseProof (IHos with "[$Hrt] [$Has]") as "[Hrt Hweaks]".
      iFrame.
  Qed.

  Lemma atom_interp_ptr_shaped ptr v :
    atom_interp (PtrA ptr) v -∗
    ∃ n n32, ⌜N_i32_repr n n32⌝ ∗
             ⌜v = VAL_int32 n32⌝ ∗
             ⌜ptr_shaped ptr n⌝ ∗
             ∃ rp, ⌜repr_root_pointer rp n⌝ ∗ root_pointer_interp rp ptr.
  Proof.
    iIntros "Hat".
    destruct ptr; cbn; unfold root_pointer_interp.
    - iDestruct "Hat" as "(%n' & %n32 & %Hn32 & %Hv & (%rp & %Hrp & Hrpn))".
      destruct rp; last (destruct μ; done).
      iDestruct "Hrpn" as "->".
      inversion Hrp; subst.
      iExists _, _.
      iSplit; first eauto.
      iSplit; first eauto.
      iSplit; first eauto using ptr_shaped.
      iExists (RootInt n); eauto.
    - iDestruct "Hat" as "(%n' & %n32 & %Hn32 & %Hv & (%rp & %Hrp & Hrpn))"; subst.
      destruct rp; first done.
      inversion Hrp; subst.
      destruct μ0, μ; try done.
      + iExists _, _.
        repeat (iSplit; first eauto using ptr_shaped).
        iExists _; eauto.
      + iExists _, _.
        repeat (iSplit; first eauto using ptr_shaped).
        iExists _; eauto.
  Qed.

  Lemma atom_interp_to_weak_memGC_nonptr o v ι θ :
    has_arep ι o -> ι <> PtrR ->
    atom_interp o v -∗ atom_interp_weak θ MemGC o v.
  Proof.
    iIntros (Harep Hnot) "Hoa".
    destruct ι; try done; cbn in Harep; destruct o; try inversion Harep; cbn; done.
  Qed.

  Lemma atom_interp_ptr_shaped_pure ptr v:
    atom_interp (PtrA ptr) v -∗
    ⌜∃ n n32, N_i32_repr n n32 /\ v = VAL_int32 n32 /\
      ptr_shaped ptr n⌝.
  Proof.
    iIntros "Hat".
    iPoseProof (atom_interp_ptr_shaped with "Hat") as
      "(%n & %n32 & %nrepr & -> & %ptrshaped & (%rp & %hrepr & _))".
    iPureIntro.
    exists n, n32.
    intuition.
  Qed.


  Lemma type_interp_implies_has_areps se τval:
    ∀ ιs ξ os,
      type_skind se τval = Some (SVALTYPE ιs ξ) ->
      type_interp rti sr τval se (SAtoms os) -∗
      ⌜has_areps ιs (SAtoms os)⌝.
  Proof.
    destruct τval; intros * Hsk; iIntros "Hτval";
      rewrite type_interp_eq; iEval (cbn) in "Hτval"; cbn in Hsk;
      rewrite Hsk; iDestruct "Hτval" as "(%sκ' & %toinv & %Facts & _)";
      iPureIntro; inversion toinv; subst; clear toinv; intuition.
  Qed.


  Lemma length_arep_flags_size ιs:
    length (concat (map arep_flags ιs)) = sum_list_with arep_size ιs.
  Proof.
    induction ιs as [|ι ιs].
    - cbn; done.
    - cbn.
      rewrite length_app.
      assert (length (arep_flags ι) = arep_size ι). {
        destruct ι; done.
      }
      lia.
  Qed.

  Lemma own_addr_mm_trivial (θ : address_map) (ℓ : location) :
    ⊢ ∃ a : N, ⌜θ !! ℓ = Some (MemMM, a)⌝ -∗ ℓ ↦addr (MemMM, a).
  Proof.
    destruct (θ !! ℓ) as [[μ a] |] eqn:Hθ.
    - iExists (a + 1)%N. iIntros "%H". simplify_eq. lia.
    - iExists 0%N. by iIntros "%H".
  Qed.

  Lemma own_addr_mm_trivial_list (θ : address_map) (ℓs : list location) :
    ⊢ [∗ list] ℓ ∈ ℓs,
        ∃ a : N, ⌜θ !! ℓ = Some (MemMM, a)⌝ -∗ ℓ ↦addr (MemMM, a).
  Proof.
    iInduction ℓs as [|ℓ rest] "IH".
    - done.
    - iSplitL.
      + iApply own_addr_mm_trivial.
      + iApply "IH".
  Qed.

  Lemma heap_memory_dom_eq θ hm :
    heap_memory sr θ hm ⊢ ⌜dom θ = dom hm⌝.
  Proof. iApply big_sepM2_dom. Qed.

  Lemma heap_memory_delete ℓ μ a ws θ hm :
    θ !! ℓ = Some (μ, a) →
    hm !! ℓ = Some ws →
    heap_memory sr θ hm ⊢
      (∃ ns ns32, ⌜Forall2 N_i32_repr ns ns32⌝ ∗
                  rt_memaddr sr μ ↦[wms][a] flat_map serialise_i32 ns32 ∗
                  words_interp θ μ ws ns) ∗
      ∀ ws',
        (∃ ns' ns32', ⌜Forall2 N_i32_repr ns' ns32'⌝ ∗
                      rt_memaddr sr μ ↦[wms][a] flat_map serialise_i32 ns32' ∗
                      words_interp θ μ ws' ns') -∗
        heap_memory sr θ (<[ℓ := ws']> hm).
  Proof.
    intros Hθℓ Hhm.
    iIntros "Hmem". unfold heap_memory.
    have Hθ : <[ℓ := (μ, a)]> (delete ℓ θ) = θ.
    { apply map_eq; intros k; destruct (decide (k = ℓ)) as [->|Hne].
      - rewrite lookup_insert -Hθℓ. by rewrite decide_True.
      - rewrite lookup_insert_ne // lookup_delete_ne //. }
    have Hhm0 : <[ℓ := ws]> (delete ℓ hm) = hm.
    { apply map_eq; intros k; destruct (decide (k = ℓ)) as [->|Hne].
      - rewrite lookup_insert -Hhm. by rewrite decide_True.
      - rewrite lookup_insert_ne // lookup_delete_ne //. }
    iEval (rewrite -{1 2}Hθ -{1}Hhm0) in "Hmem".
    iEval (rewrite big_sepM2_insert_delete) in "Hmem".
    rewrite !delete_delete_eq.
    iDestruct "Hmem" as "[Hentry Hrest]".
    iSplitL "Hentry"; first by rewrite Hθ.
    iIntros (ws') "Hws'".
    unfold heap_memory.
    have Hhm' : <[ℓ := ws']> hm = <[ℓ := ws']> (delete ℓ hm).
    { apply map_eq; intros k; destruct (decide (k = ℓ)) as [->|Hne].
      - rewrite !lookup_insert. by rewrite !decide_True.
      - by rewrite !lookup_insert_ne // lookup_delete_ne. }
    iEval (rewrite -{1 2}Hθ Hhm').
    iEval (rewrite big_sepM2_insert_delete).
    rewrite !delete_delete_eq.
    iFrame.
    by rewrite Hθ.
  Qed.



End properties.

(* Setting up Inhabited instances allows commuting existential quantifiers
   with later modalities, like this:

     ▷ (exists sk, P sk) ⊣⊢ exists sk, ▷ P sk

 *)
#[global]
Instance skind_inhabited : Inhabited skind :=
  populate (SVALTYPE [] NoRefs).

#[global]
Instance atom_inhabited : Inhabited atom :=
  populate (PtrA (PtrInt 0)).
