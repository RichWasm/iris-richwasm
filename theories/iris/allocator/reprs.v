From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From Wasm.iris.logrel Require Export iris_fundamental.
From Wasm.iris.rules Require Export proofmode.
From RWasm.iris.allocator Require Import allocator_common misc_relocate.
From RWasm.iris.allocator Require Export blocks memrsc.
Import blocks.

Section reprs.

Context `{!wasmG Σ}. 

(* beware:
    The i32 type is a record {intval: Z; proof: -1 < z < 2^32}.
    This means that nat_repr is not a functional relation
    (unless you assume propositional extensionality).
*)
Definition nat_repr (n: nat) (n32: i32) : Prop :=
  (-1 < Z.of_nat n < Wasm_int.Int32.modulus)%Z /\
  n = Wasm_int.nat_of_uint i32m n32.

(* beware:
    The i32 type is a record {intval: Z; proof: -1 < z < 2^32}.
    This means that N_repr is not a functional relation
    (unless you assume propositional extensionality).
*)
Definition N_repr (n: N) (n32: i32) : Prop :=
  (-1 < Z.of_N n < Wasm_int.Int32.modulus)%Z /\
  n = Wasm_int.N_of_uint i32m n32.

Lemma N_repr_uint:
  forall n n32,
    N_repr n n32 ->
    n = Wasm_int.N_of_uint i32m n32.
Proof.
  unfold N_repr.
  tauto.
Qed.

Lemma N_repr_i32repr: 
  forall (n: N) (z: Z),
    (-1 < Z.of_N n < Wasm_int.Int32.modulus)%Z ->
    z = Z.of_N n ->
    N_repr n (Wasm_int.Int32.repr z).
Proof.
  intros.
  unfold Wasm_int.Int32.repr, N_repr, Wasm_int.N_of_uint; cbn.
  split.
  - lia.
  - rewrite Wasm_int.Int32.Z_mod_modulus_id.
    + subst. by rewrite N2Z.id.
    + lia.
Qed.

Definition state_to_N (flag : state_flag) : N :=
  match flag with
  | Used => BLK_USED
  | Free => BLK_FREE
  | Final => BLK_FINAL
  end.

Definition alloc_tok (memidx: N) (data_addr: N) : iProp Σ.
Admitted.

Definition state_repr (memidx: N) (flag: state_flag) (base_addr: N) : iProp Σ :=
  ∃ st,
    ⌜N_repr (state_to_N flag) st⌝ ∗
    memidx ↦[wms][base_addr + state_off] bits (VAL_int32 st).

Definition size_repr (memidx: N) (sz: N) (base_addr: N) : iProp Σ :=
  ∃ sz32,
    ⌜N_repr sz sz32 ⌝ ∗
    memidx ↦[wms][base_addr + size_off] bits (VAL_int32 sz32).

Definition next_repr (memidx: N) (next: N) (base_addr: N) : iProp Σ :=
  ∃ next32,
    ⌜N_repr next next32 ⌝ ∗
  memidx ↦[wms][base_addr + next_off] bits (VAL_int32 next32).

Definition data_repr memidx blk base_addr :=
  match blk with
  | UsedBlk blk_used_size blk_leftover_size =>
      own_vec memidx (base_addr + data_off + blk_used_size) blk_leftover_size
  | FreeBlk blk_size =>
      own_vec memidx (base_addr + data_off) blk_size
  end.

Definition block_inbounds (memidx: N) (blk_size: N) (base_addr: N) : iProp Σ :=
  ⌜(Z.of_N (base_addr + blk_hdr_sz + blk_size) < Wasm_int.Int32.modulus)%Z⌝.

Definition block_repr (memidx: N) (blk: block) (base_addr next_addr: N) : iProp Σ :=
  block_inbounds memidx (block_size blk) base_addr ∗
  state_repr memidx (block_flag blk) base_addr ∗
  size_repr memidx (block_size blk) base_addr ∗
  next_repr memidx next_addr base_addr ∗
  data_repr memidx blk base_addr.

(* 
EXTERNAL SPEC
blks "allocator state"
1. Allocator invariant   freelist_repr blks 0
2. Allocation token      Allocated(blks, l, sz) <---> In (UsedBlk sz) blks


                                    { AInv(st) } malloc(sz) { v. exists st'. v |-> bs * |bs| = sz * tok(st', v) * AInv(st') }
{ AInv(st) * v |-> bs * |bs| = sz * tok(st, v) } free(v)    { (). exists st'. AInv(st') }
own_block (N.of_nat memidx) ret_addr reqd_sz ∗
*)

Fixpoint blocks_repr (memidx: N) (blks: list block) (base_addr: N) (out_addr: N) : iProp Σ :=
  match blks with
  | blk :: blks =>
      ∀ next_addr,
        block_repr memidx blk base_addr next_addr ∗
        blocks_repr memidx blks next_addr out_addr
  | [] =>
      ⌜base_addr = out_addr⌝
  end.

Definition final_block_repr (memidx: N) (blk: final_block) (base_addr: N) : iProp Σ :=
  match blk with
  | FinalBlk blk_size =>
      block_inbounds memidx blk_size base_addr ∧
      state_repr memidx Final base_addr ∗
      size_repr memidx blk_size base_addr ∗
      next_repr memidx 0%N base_addr ∗
      own_vec memidx (base_addr + data_off) blk_size
  end.

Definition final_block_sz (blk: final_block) : N :=
  match blk with
  | FinalBlk sz => sz
  end.

Lemma final_block_inbounds (memidx: N) (blk: final_block) (base_addr: N) :
  ⊢ final_block_repr memidx blk base_addr -∗
    ⌜(Z.of_N (base_addr + blk_hdr_sz + final_block_sz blk) < Wasm_int.Int32.modulus)%Z⌝ ∗
    final_block_repr memidx blk base_addr.
Proof.
  iIntros "H".
  destruct blk.
  iDestruct "H" as "(%Hinbounds & H')".
  iFrame; auto.
Qed.

Definition freelist_repr (memidx: N) (blks: list block * final_block) (base_addr: N) : iProp Σ :=
  let '(blks, final) := blks in
  ∀ next_addr,
    blocks_repr memidx blks base_addr next_addr ∗
    final_block_repr memidx final next_addr.

Lemma own_vec_split memidx ℓ sz1 sz2 :
  own_vec memidx ℓ (sz1 + sz2) ⊣⊢ own_vec memidx ℓ sz1 ∗ own_vec memidx (ℓ + sz1) sz2.
Proof.
  unfold own_vec.
  iSplit.
  - iIntros "(%bs & %Hlen & Hbs)".
    pose proof (take_drop (N.to_nat sz1) bs) as Hsplit.
    rewrite <- Hsplit.
    rewrite wms_app; [|eauto; lia].
    iDestruct "Hbs" as "(Hbs1 & Hbs2)".
    iSplitL "Hbs1".
    + iExists _; iFrame.
      iPureIntro.
      rewrite length_take_le; lia.
    + rewrite length_take_le; [|lia].
      rewrite N2Nat.id.
      iExists _; iFrame.
      iPureIntro.
      rewrite length_drop.
      lia.
  - iIntros "((%bs1 & (%Hlen1 & Hbs1)) & (%bs2 & (%Hlen2 & Hbs2)))".
    iExists (bs1 ++ bs2).
    erewrite (wms_app _ _ _ (sz1:=sz1)); [| lia].
    iFrame.
    iPureIntro.
    rewrite length_app.
    lia.
Qed.

Lemma serialise_i32_inj:
  forall i k,
    serialise_i32 i = serialise_i32 k ->
    i = k.
Admitted.

End reprs.
