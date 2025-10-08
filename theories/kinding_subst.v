From mathcomp Require Import ssreflect.
From stdpp Require Import base list.
From RichWasm Require Import syntax typing util.
From RichWasm.iris.logrel Require Import relations.

Ltac fold_subst :=
  fold subst_type subst_size subst_representation subst_function_type.


Lemma subkind_of_subst s__mem s__rep s__size κ κ' :
  subkind_of κ κ' ->
  subkind_of (subst_kind s__mem s__rep s__size κ)
             (subst_kind s__mem s__rep s__size κ').
Proof.
  intros Hle.
  destruct Hle; constructor.
Qed.

Lemma rep_ok_subst K ρ :
  rep_ok K ρ ->
  forall s__rep,
    rep_subst_interp K s__rep ->
    rep_ok kc_empty (subst_representation s__rep ρ).
Proof.
  induction 1; intros; eauto.
Admitted.

Lemma kind_ok_subst K κ :
  kind_ok K κ ->
  forall s__mem s__rep s__size,
    subst_interp K s__mem s__rep s__size ->
    kind_ok kc_empty (subst_kind s__mem s__rep s__size κ).
Proof.
  unfold subst_interp.
  induction 1; intros * (Hmem & Hrep & Hsz).
  - constructor.
    eapply rep_ok_subst; eauto.
  - constructor.
    + admit.
    + admit.
Admitted.

Lemma has_kind_subst F τ κ :
  has_kind F τ κ ->
  forall s__mem s__rep s__size,
      subst_interp F.(fc_kind_ctx) s__mem s__rep s__size ->
      has_kind 
        (fc_clear_kind (subst_function_ctx s__mem s__rep s__size VarT F))
        (subst_type s__mem s__rep s__size VarT τ)
        (subst_kind s__mem s__rep s__size κ).
Proof.
  induction 1 using has_kind_ind'; intros s__mem s__rep s__size Hsubst; try solve [econstructor; eauto].
  - eapply IHhas_kind in Hsubst.
    econstructor; eauto using subkind_of_subst.
  - cbn.
    eapply KVar.
    + cbn.
      by rewrite list_lookup_fmap H.
    + by eapply kind_ok_subst.
  - eapply KSumVal.
    fold_subst.
    apply Forall2_fmap; eapply Forall2_impl; eauto.
  - eapply KSumMem.
    { admit. }
    apply Forall2_fmap; eapply Forall2_impl; eauto.
  - eapply KSumMemSized.
    { admit. }
    apply Forall2_fmap; eapply Forall2_impl; eauto.
  - eapply KProdVal.
    fold_subst.
    apply Forall2_fmap; eapply Forall2_impl; eauto.
  - eapply KProdMem.
    { admit. }
    fold_subst.
    apply Forall2_fmap; eapply Forall2_impl; eauto.
  - eapply KProdMemSized.
    { admit. }
    fold_subst.
    apply Forall2_fmap; eapply Forall2_impl; eauto.
  - eapply KCodeRef.
    fold_subst.
    admit.
  - eapply KPad.
    { admit. }
    fold_subst.
    eauto.
  - eapply KSer.
    { admit. }
    fold_subst; eauto.
  - eapply KRec.
    fold_subst.
    admit.
  - eapply KExistsMem.
    { eapply kind_ok_subst; eauto. }
    fold_subst.
    admit.
  - eapply KExistsRep.
    { eapply kind_ok_subst; eauto. }
    fold_subst.
    set (s__mem' := up_representation_memory s__mem).
    set (s__rep' := up_representation_representation s__rep).
    set (s__size' := up_representation_size s__size).
    set (F' := RecordSet.set _ _ _) in *.
    set (F'' := RecordSet.set _ _ _).
    erewrite ext_type; first last.
    + intros i.
      rewrite upId_representation_type; eauto.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + admit.
  - admit.
  - admit.
Admitted.
