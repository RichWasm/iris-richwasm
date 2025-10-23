From mathcomp Require Import ssreflect.
From stdpp Require Import base list.
From RichWasm Require Import syntax typing util.
From RichWasm.iris.logrel Require Import relations.

Ltac fold_subst :=
  fold subst_type subst_size subst_representation subst_function_type.

Lemma subkind_of_subst s__rep s__size κ κ' :
  subkind_of κ κ' ->
  subkind_of (subst_kind s__rep s__size κ)
             (subst_kind s__rep s__size κ').
Proof.
  intros Hle.
  destruct Hle; constructor.
Qed.
