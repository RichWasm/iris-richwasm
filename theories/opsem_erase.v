From stdpp Require Import base option.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import datatypes operations logrel.iris_logrel.
From RichWasm Require Import obs obs_properties.
Require RichWasm.opsem_instr.
Require Wasm.opsem.
Set Bullet Behavior "Strict Subproofs".

(** [R]eduction semantics *)
Module R := Wasm.opsem.
(** [I]nstrumented reduction semantics *)
Module I := RichWasm.opsem_instr.

(** ERASURE *)
Definition erase : obs * store_record * frame * seq.seq administrative_instruction -> store_record * frame * seq.seq administrative_instruction :=
  λ '(o, s, f, e), (s, f, e).

Proposition erase_simple_step o e o' e':
  I.reduce_simple o e o' e' ->
  R.reduce_simple e e'.
Proof.
  induction 1; solve [econstructor; eauto; congruence].
Qed.

Proposition erase_step o s f e o' s' f' e':
  I.reduce o s f e o' s' f' e' ->
  R.reduce s f e s' f' e'.
Proof.
  induction 1; try solve [econstructor; eauto; congruence].
  {
    apply R.r_simple.
    eapply erase_simple_step; eauto.
  }
Qed.

Proposition erase_step_tuple cfg cfg':
  I.reduce_tuple cfg cfg' ->
  R.reduce_tuple (erase cfg) (erase cfg').
Proof.
  destruct cfg as [[[o s] f] e].
  destruct cfg' as [[[o' s'] f'] e'].
  apply erase_step.
Qed.

Proposition erase_step_trans cfg cfg':
  I.reduce_trans cfg cfg' ->
  R.reduce_trans (erase cfg) (erase cfg').
Proof.
  induction 1.
  - constructor; by apply erase_step_tuple.
  - by constructor.
  - by (econstructor; eauto).
Qed.

(** INSTRUMENTATION *)
Definition instrument : obs -> store_record * frame * seq.seq administrative_instruction -> obs * store_record * frame * seq.seq administrative_instruction :=
  λ o '(s, f, e), (o, s, f, e).

Proposition instr_simple_step e e':
  R.reduce_simple e e' ->
  exists o',
    I.reduce_simple Run e o' e'.
Proof.
  induction 1; eexists; by econstructor; eauto; congruence.
Qed.

Proposition instr_step s f e s' f' e':
  R.reduce s f e s' f' e' ->
  ∃ o',
    I.reduce Run s f e o' s' f' e'.
Proof.
  induction 1; try by (eexists; econstructor; eauto; congruence).
  - eapply instr_simple_step in H.
    destruct H as [o H].
    exists o; by constructor.
  - destruct IHreduce as [o' IH].
    exists o'.
    econstructor; eauto.
  - destruct IHreduce as [o' IH].
    exists o'.
    by apply I.r_local.
Qed.

Proposition instr_step_tuple cfg cfg':
  R.reduce_tuple cfg cfg' ->
  exists o, I.reduce_tuple (instrument Run cfg) (instrument o cfg').
Proof.
  destruct cfg as [[s f] e].
  destruct cfg' as [[s' f'] e'].
  apply instr_step.
Qed.

Proposition instr_step_trans cfg cfg':
  R.reduce_trans cfg cfg' ->
  exists o, I.reduce_trans (instrument Run cfg) (instrument o cfg').
Abort. (* Not true, the transitivity case is not provable *)
