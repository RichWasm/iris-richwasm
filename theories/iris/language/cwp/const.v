Require Import Stdlib.Lists.List.

From stdpp Require Import base.

From mathcomp Require Import ssreflect ssrbool.

From RichWasm.wasm Require Import common datatypes datatypes_properties operations.

Set Bullet Behavior "Strict Subproofs".

Definition is_const (e : basic_instruction) : bool :=
  match e with
  | BI_const _ => true
  | _ => false
  end.

Definition is_consts : list basic_instruction -> bool :=
  forallb is_const.

Definition to_consts : list value -> list basic_instruction :=
  map BI_const.


Lemma is_const_exists ev :
  is_const ev -> ∃ v, ev = BI_const v.
Proof.
  intros.
  destruct ev; try done.
  by eexists.
Qed.

Lemma is_consts_exists evs :
  is_consts evs -> ∃ vs, evs = to_consts vs.
Proof.
  induction evs as [| ev evs IH].
  - intros _. exists []. done.
  - intros Hconsts.
    unfold is_consts in Hconsts.
    cbn in Hconsts.
    apply andb_True in Hconsts as [Hev Hevs].
    apply IH in Hevs as [vs' Hevs'].
    apply is_const_exists in Hev as [v ->].
    exists (v :: vs').
    unfold to_consts.
    rewrite map_cons.
    by f_equal.
Qed.

Lemma is_consts_app evs1 evs2 :
  is_consts (evs1 ++ evs2) <-> is_consts evs1 /\ is_consts evs2.
Proof.
  unfold is_consts.
  rewrite forallb_app.
  apply andb_True.
Qed.

Definition has_value (e : basic_instruction) (v : value) : bool :=
  match e with
  | BI_const v' => value_eqb v v'
  | _ => false
  end.

Definition has_values : list basic_instruction -> list value -> bool :=
  seq.all2 has_value.

Lemma has_values_to_consts vs :
  has_values (to_consts vs) vs.
Proof.
  induction vs; first done.
  cbn.
  apply andb_True.
  split.
  - unfold value_eqb. by destruct (value_eq_dec a a).
  - apply IHvs.
Qed.

Lemma has_values_iff_to_consts es vs :
  has_values es vs <-> es = to_consts vs.
Proof.
  split.
  {
    generalize dependent vs. induction es.
    - intros vs H.
      apply Is_true_true in H.
      apply all2_size in H.
      symmetry in H.
      apply seq.size0nil in H.
      by rewrite H.
    - intros vs H. destruct vs.
      + apply Is_true_true in H. apply all2_size in H. inversion H.
      + cbn in H.
        apply andb_True in H as [Hv Hvs].
        apply IHes in Hvs.
        subst es.
        unfold to_consts.
        rewrite map_cons.
        destruct a; try inversion Hv.
        cbn in Hv.
        destruct (value_eq_dec v v0) as [-> | Hv0] eqn:Heq; first done.
        unfold value_eqb in Hv.
        by rewrite Heq in Hv.
  }
  { intros ->. apply has_values_to_consts. }
Qed.

Lemma to_e_list_map_BI_const vs :
  to_e_list $ to_consts vs = v_to_e_list vs.
Proof.
  induction vs as [| v vs IH].
  - reflexivity.
  - simpl. f_equal. exact IH.
Qed.

Lemma is_consts_to_consts vs :
  is_consts (to_consts vs).
Proof.
  by induction vs.
Qed.

Lemma const_list_consts evs :
  is_consts evs ->
  const_list (map AI_basic evs).
Proof.
  intros H.
  apply Is_true_true.
  induction evs; first done.
  cbn.
  cbn in H.
  apply Is_true_true.
  apply andb_True.
  apply andb_True in H as [Ha Hevs].
  destruct a; try inversion Ha.
  split; first done.
  apply Is_true_true.
  by apply IHevs.
Qed.

Lemma has_values_is_consts evs vs :
  has_values evs vs ->
  is_consts evs.
Proof.
  intros H.
  generalize dependent vs.
  induction evs; first done.
  intros vs H.
  destruct vs.
  { apply Is_true_true in H. apply all2_size in H. inversion H. }
  cbn in H.
  apply andb_True in H as [Hv Hvs].
  cbn.
  apply andb_True.
  destruct a; try inversion Hv.
  split; first done.
  eapply IHevs.
  apply Hvs.
Qed.

Lemma has_values_to_consts_inv evs vs :
  has_values evs vs ->
  evs = to_consts vs.
Proof.
  intros H.
  generalize dependent vs.
  induction evs.
  - intros vs H.
    apply Is_true_true in H.
    apply all2_size in H.
    symmetry in H.
    apply seq.size0nil in H.
    by subst vs.
  - intros vs H.
    destruct vs; first inversion H.
    cbn in H.
    apply andb_True in H as [Hv Hvs].
    cbn.
    f_equal.
    + destruct a; try inversion Hv.
      destruct (value_eq_dec v v0) eqn:Heq; first by subst v0.
      unfold has_value, value_eqb in Hv.
      by rewrite Heq in Hv.
    + by apply IHevs.
Qed.

Lemma has_values_app_inv evs vs1 vs2 :
  has_values evs (vs1 ++ vs2) ->
  exists evs1 evs2, evs = evs1 ++ evs2 /\ has_values evs1 vs1 /\ has_values evs2 vs2.
Proof.
  intros H.
  apply has_values_to_consts_inv in H.
  subst evs.
  exists (to_consts vs1), (to_consts vs2).
  split; last split.
  - unfold to_consts. by rewrite map_app.
  - apply has_values_to_consts.
  - apply has_values_to_consts.
Qed.

Lemma has_values_length evs vs :
  has_values evs vs ->
  length evs = length vs.
Proof.
  intros H.
  change (@length basic_instruction) with (@seq.size basic_instruction).
  change (@length value) with (@seq.size value).
  eapply all2_size.
  apply Is_true_true.
  apply H.
Qed.
