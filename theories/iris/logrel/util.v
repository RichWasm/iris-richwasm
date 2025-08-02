From mathcomp Require Import eqtype seq.

Require Import iris.proofmode.tactics.

Require Import RichWasm.term.
Require Import RichWasm.compiler.types.
From RichWasm.iris Require Import num_reprs util.
Import uPred.

Definition wasm_deserialize_values (bs : bytes) (tys : list value_type) : list value :=
  let bs' := reshape (map length_t tys) bs in
  zip_with wasm_deserialise bs' tys.

Definition deserialize_values (bs : bytes) : Typ -> list value :=
  wasm_deserialize_values bs ∘ translate_type.

Definition word_aligned (n : N) : Prop :=
  (4 | n)%N.

Definition ptr_repr (l : R.Loc) (i : i32) : Prop :=
  match l with
  | R.LocV v => False
  | R.LocP ℓ R.GCMem => N_repr (ℓ + 1) i /\ word_aligned ℓ
  | R.LocP ℓ R.LinMem => N_repr ℓ i /\ word_aligned ℓ
  end.

Definition ptr_repr' (l : R.Loc) (n : N) : Prop :=
  match l with
  | R.LocV v => False
  | R.LocP ℓ R.GCMem => (ℓ + 1)%N = n /\ word_aligned ℓ
  | R.LocP ℓ R.LinMem => ℓ = n /\ word_aligned ℓ
  end.

Ltac solve_iprop_ne :=
  repeat (
    apply exist_ne +
    apply intuitionistically_ne +
    apply or_ne +
    apply sep_ne +
    apply and_ne +
    apply wp_ne +
    apply inv_ne +
    auto +
    (rewrite /pointwise_relation; intros) +
    apply forall_ne +
    apply wand_ne
  ).
