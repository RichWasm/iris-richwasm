From stdpp Require Import base.
From mathcomp Require Import eqtype boot.seq.

From Stdlib Require Import Lia.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.NArith.NArith.
Require Import Wasm.numerics.

Set Bullet Behavior "Strict Subproofs".

(* Representation relations for *unsigned* integers. *)
Definition N_Z_repr (n: N) (z: Z) : Prop :=
  Z.of_N n = z.

Definition Z_i32_repr (z : Z) (z32 : i32) : Prop :=
  z = Wasm_int.Int32.unsigned z32.

Definition N_i32_repr (n : N) (n32 : i32) : Prop :=
  n = Wasm_int.N_of_uint i32m n32.

(* Defining congruences for given pairs of operations. *)
Definition unop_cong_spec {A}
  (repr: A -> i32 -> Prop)
  (repr_dom: A -> Prop)
  (op32: i32 -> i32)
  (op: A -> A) : Prop :=
  forall (x: A) (x32: i32),
    repr x x32 ->
    repr_dom (op x) ->
    repr (op x) (op32 x32).

Definition unop_Z_cong_spec : (i32 → i32) → (Z → Z) → Prop :=
  unop_cong_spec Z_i32_repr (fun z => z < Wasm_int.Int32.modulus)%Z.

Definition unop_N_cong_spec : (i32 → i32) → (N → N) → Prop :=
  unop_cong_spec N_i32_repr (fun n => Z.of_N n < Wasm_int.Int32.modulus)%Z.

Definition binop_cong_spec {A}
  (repr: A -> i32 -> Prop)
  (repr_dom: A -> Prop)
  (op32: i32 -> i32 -> i32)
  (op: A -> A -> A) : Prop :=
  forall (x y: A) (x32 y32: i32),
    repr x x32 ->
    repr y y32 ->
    repr_dom (op x y) ->
    repr (op x y) (op32 x32 y32).

Definition binop_Z_cong_spec : (i32 → i32 → i32) → (Z → Z → Z) → Prop :=
  binop_cong_spec Z_i32_repr (fun z => z < Wasm_int.Int32.modulus)%Z.

Definition binop_N_cong_spec : (i32 → i32 → i32) → (N → N → N) → Prop :=
  binop_cong_spec N_i32_repr (fun n => Z.of_N n < Wasm_int.Int32.modulus)%Z.

Definition testop_cong_spec
  {A}
  (repr: A -> i32 -> Prop)
  (op32: i32 -> bool)
  (op: A -> bool) : Prop :=
  forall (x: A) (x32: i32),
    repr x x32 ->
    op x = op32 x32.

Definition testop_Z_cong_spec : (i32 -> bool) -> (Z -> bool) -> Prop :=
  testop_cong_spec Z_i32_repr.

Definition testop_N_cong_spec : (i32 -> bool) -> (N -> bool) -> Prop :=
  testop_cong_spec N_i32_repr.

(* Elimination and introduction principles for repr relations. *)
Lemma N_Z_repr_of_N n z :
  N_Z_repr n z <-> Z.of_N n = z.
Proof.
  now unfold N_Z_repr.
Qed.

Lemma N_Z_repr_to_N n z :
  N_Z_repr n z ->
  n = Z.to_N z.
Proof.
  intros Hrep.
  rewrite <- Hrep.
  symmetry.
  apply N2Z.id.
Qed.

(* Composition lemmas. *)
Lemma N_i32_Z_comp {n z i} :
  N_i32_repr n i ->
  Z_i32_repr z i ->
  N_Z_repr n z.
Proof.
  intros.
  rewrite H, H0.
  unfold N_Z_repr.
  cbn.
  rewrite Z2N.id; auto.
  apply Wasm_int.Int32.unsigned_range.
Qed.

Lemma N_Z_i32_comp {n z i} :
  N_Z_repr n z ->
  Z_i32_repr z i ->
  N_i32_repr n i.
Proof.
  intros Hnz Hzi.
  unfold N_i32_repr; cbn.
  rewrite <- Hzi.
  now eapply N_Z_repr_to_N.
Qed.

Lemma Z_N_i32_comp {n z i} :
  N_Z_repr n z ->
  N_i32_repr n i ->
  Z_i32_repr z i.
Proof.
  unfold N_Z_repr, N_i32_repr.
  intros Hnz Hni.
  unfold Z_i32_repr.
  rewrite <- Hnz, Hni; cbn.
  rewrite Z2N.id; eauto.
  apply Wasm_int.Int32.unsigned_range.
Qed.

(* numbers related to i32s are between 0 and 2^32-1 *)
Lemma Z_i32_repr_bdd z i :
  Z_i32_repr z i ->
  (-1 < z < Wasm_int.Int32.modulus)%Z.
Proof.
  unfold Z_i32_repr.
  intros Hz.
  pose proof (Wasm_int.Int32.unsigned_range i).
  lia.
Qed.

Lemma N_i32_repr_bdd n i :
  N_i32_repr n i ->
  (-1 < Z.of_N n < Wasm_int.Int32.modulus)%Z.
Proof.
  intros Hrep.
  eapply Z_i32_repr_bdd.
  eapply Z_N_i32_comp; eauto.
  reflexivity.
Qed.

Lemma N_i32_repr_N_of_uint :
  forall n n32,
    N_i32_repr n n32 ->
    n = Wasm_int.N_of_uint i32m n32.
Proof.
  unfold N_i32_repr.
  tauto.
Qed.

Lemma N_repr_i32repr :
  forall (n : N) (z : Z),
    (-1 < z < Wasm_int.Int32.modulus)%Z ->
    N_Z_repr n z ->
    N_i32_repr n (Wasm_int.Int32.repr z).
Proof.
  intros.
  unfold Wasm_int.Int32.repr, N_i32_repr; cbn.
  rewrite Wasm_int.Int32.Z_mod_modulus_id.
  - now apply N_Z_repr_to_N.
  - assumption.
Qed.

Lemma unsigned_is_N:
  forall z: i32,
  Wasm_int.Int32.unsigned z = Z.of_N (Wasm_int.N_of_uint i32m z).
Proof.
  intros.
  symmetry.
  eapply N_i32_Z_comp; reflexivity.
Qed.

Lemma unsigned_N_i32_repr (z: i32) :
  N_i32_repr (Z.to_N (Wasm_int.Int32.unsigned z)) z.
Proof.
  eapply N_Z_i32_comp.
  - unfold N_Z_repr.
    rewrite Z2N.id; eauto.
    apply (Wasm_int.Int32.unsigned_range z).
  - reflexivity.
Qed.

Lemma N_i32_repr_inj (z: i32) (a b: N) :
  N_i32_repr a z ->
  N_i32_repr b z ->
  a = b.
Proof.
  unfold N_i32_repr.
  intuition congruence.
Qed.

Lemma binop_Z_N_cong op32 opZ opN:
  (∀ n m : N, Z.of_N (opN n m) = opZ (Z.of_N n) (Z.of_N m)) ->
  binop_Z_cong_spec op32 opZ ->
  binop_N_cong_spec op32 opN.
Proof.
  unfold binop_Z_cong_spec, binop_N_cong_spec, binop_cong_spec.
  intros * Hop HZ.
  intros.
  eapply N_Z_i32_comp.
  - reflexivity.
  - rewrite Hop.
    eapply HZ; eauto.
    + eapply Z_N_i32_comp; eauto.
      reflexivity.
    + eapply Z_N_i32_comp; eauto.
      reflexivity.
    + rewrite <- Hop.
      congruence.
Qed.

Lemma i32_hom_Z_cong (op: Z -> Z -> Z) :
  (forall a b, 0 <= a -> 0 <= b -> 0 <= op a b)%Z ->
  binop_Z_cong_spec
    (λ x y, Wasm_int.Int32.repr (op (Wasm_int.Int32.unsigned x) (Wasm_int.Int32.unsigned y)))
    op.
Proof.
  unfold binop_Z_cong_spec, binop_cong_spec.
  intros Hpos * Hx Hy Hzbd.
  unfold Wasm_int.Int32.repr, Z_i32_repr, Wasm_int.Int32.unsigned; cbn.
  assert (Hop: (op (Wasm_int.Int32.intval x32) (Wasm_int.Int32.intval y32) = op x y)%Z)
    by (rewrite <- Hx, <- Hy; auto).
  rewrite Wasm_int.Int32.Z_mod_modulus_id; auto.
  rewrite Hop.
  split; [|assumption].
  rewrite Hx, Hy.
  pose proof (Wasm_int.Int32.unsigned_range x32).
  pose proof (Wasm_int.Int32.unsigned_range y32).
  specialize (Hpos (Wasm_int.Int32.unsigned x32) (Wasm_int.Int32.unsigned y32)).
  lia.
Qed.

Lemma imul_Z_cong:
  binop_Z_cong_spec Wasm_int.Int32.imul Z.mul.
Proof.
  apply i32_hom_Z_cong.
  lia.
Qed.

Lemma imul_N_cong:
  binop_N_cong_spec Wasm_int.Int32.imul N.mul.
Proof.
  eapply binop_Z_N_cong; eauto using imul_Z_cong, N2Z.inj_mul.
Qed.

Lemma iadd_Z_cong:
  binop_Z_cong_spec Wasm_int.Int32.iadd Z.add.
Proof.
  apply i32_hom_Z_cong.
  lia.
Qed.

Lemma iadd_N_cong:
  binop_N_cong_spec Wasm_int.Int32.iadd N.add.
Proof.
  eapply binop_Z_N_cong; eauto using iadd_Z_cong, N2Z.inj_add.
Qed.

Lemma divu_Z_cong:
  binop_Z_cong_spec Wasm_int.Int32.divu Z.div.
Proof.
  apply i32_hom_Z_cong.
  eapply Z_div_nonneg_nonneg; eauto.
Qed.

Lemma divu_N_cong:
  binop_N_cong_spec Wasm_int.Int32.divu N.div.
Proof.
  eapply binop_Z_N_cong; eauto using divu_Z_cong, N2Z.inj_div.
Qed.

Lemma shl_Z_cong:
  binop_Z_cong_spec Wasm_int.Int32.shl Z.shiftl.
Proof.
  apply i32_hom_Z_cong.
  intros.
  eapply Z.shiftl_nonneg; eauto.
Qed.

Lemma shl_N_cong:
  binop_N_cong_spec Wasm_int.Int32.shl N.shiftl.
Proof.
  eapply binop_Z_N_cong; eauto using shl_Z_cong, N2Z.inj_shiftl.
Qed.

Lemma shru_Z_cong:
  binop_Z_cong_spec Wasm_int.Int32.shru Z.shiftr.
Proof.
  apply i32_hom_Z_cong.
  intros.
  eapply Z.shiftr_nonneg; eauto.
Qed.

Lemma shru_N_cong:
  binop_N_cong_spec Wasm_int.Int32.shru N.shiftr.
Proof.
  eapply binop_Z_N_cong; eauto using shru_Z_cong, N2Z.inj_shiftr.
Qed.

Lemma and_Z_cong:
  binop_Z_cong_spec Wasm_int.Int32.and Z.land.
Proof.
  apply i32_hom_Z_cong.
  intros.
  eapply Z.land_nonneg; eauto.
Qed.

Lemma and_N_cong:
  binop_N_cong_spec Wasm_int.Int32.and N.land.
Proof.
  eapply binop_Z_N_cong; eauto using and_Z_cong, N2Z.inj_land.
Qed.

Check (Wasm_int.Int32.eq Wasm_int.Int32.zero).

Lemma eqz_Z_cong:
  testop_Z_cong_spec (Wasm_int.Int32.eq Wasm_int.Int32.zero) (Z.eqb 0).
Proof.
  unfold testop_Z_cong_spec, testop_cong_spec; intros x x32 Hrep.
  unfold Wasm_int.Int32.eq, Coqlib.zeq.
  rewrite Wasm_int.Int32.unsigned_zero.
  rewrite <- Hrep.
  destruct (Z.eq_dec 0 x); subst; eauto.
  now eapply Z.eqb_neq.
Qed.
