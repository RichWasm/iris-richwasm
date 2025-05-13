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

Context `{!wasmG Σ} `{!allocG Σ}.
Variables (memidx: N).

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

Definition state_repr (flag: state_flag) (base_addr: N) : iProp Σ :=
  ∃ st,
    ⌜N_repr (state_to_N flag) st⌝ ∗
    memidx ↦[wms][base_addr + state_off] bits (VAL_int32 st).

Definition size_repr (sz: N) (base_addr: N) : iProp Σ :=
  ∃ sz32,
    ⌜N_repr sz sz32 ⌝ ∗
    memidx ↦[wms][base_addr + size_off] bits (VAL_int32 sz32).

Definition next_repr (next: N) (base_addr: N) : iProp Σ :=
  ∃ next32,
    ⌜N_repr next next32 ⌝ ∗
      memidx ↦[wms][base_addr + next_off] bits (VAL_int32 next32).

Definition data_repr blk :=
  match blk with
  | UsedBlk base_addr blk_used_size blk_leftover_size =>
      own_vec memidx (base_addr + data_off + blk_used_size) blk_leftover_size
  | FreeBlk base_addr blk_size =>
      own_vec memidx (base_addr + data_off) blk_size
  end.

Definition block_inbounds (blk_size: N) (base_addr: N) : iProp Σ :=
  ⌜(Z.of_N (base_addr + blk_hdr_sz + blk_size) < Wasm_int.Int32.modulus)%Z⌝.

Definition block_repr (blk: block) (next_addr: N) : iProp Σ :=
  block_inbounds (block_size blk) (block_addr blk) ∗
  state_repr (block_flag blk) (block_addr blk) ∗
  size_repr (block_size blk) (block_addr blk) ∗
  next_repr next_addr (block_addr blk) ∗
  data_repr blk.

(* 
EXTERNAL SPEC
blks "allocator state"
1. Allocator invariant   freelist_repr blks 0
2. Allocation token      Allocated(blks, l, sz) <---> In (UsedBlk sz) blks


                                    { AInv(st) } malloc(sz) { v. exists st'. v |-> bs * |bs| = sz * tok(st', v) * AInv(st') }
{ AInv(st) * v |-> bs * |bs| = sz * tok(st, v) } free(v)    { (). exists st'. AInv(st') }
own_block (N.of_nat memidx) ret_addr reqd_sz ∗
*)

Fixpoint blocks_repr (blks: list block) (base_addr next_addr: N) : iProp Σ :=
  match blks with
  | blk :: blks =>
      ⌜base_addr = block_addr blk⌝ ∗
      ∃ addr, block_repr blk addr ∗ blocks_repr blks addr next_addr
  | [] => ⌜base_addr = next_addr⌝
  end.

Definition final_block_repr (blk: final_block) (base_addr: N) : iProp Σ :=
  match blk with
  | FinalBlk base_addr' blk_size =>
      ⌜base_addr' = base_addr⌝ ∗
      block_inbounds blk_size base_addr ∧
      state_repr Final base_addr ∗
      size_repr blk_size base_addr ∗
      next_repr 0%N base_addr ∗
      own_vec memidx (base_addr + data_off) blk_size
  end.

Lemma final_block_inbounds (blk: final_block) (base_addr: N) :
  ⊢ final_block_repr blk base_addr -∗
    ⌜(Z.of_N (base_addr  + blk_hdr_sz + final_block_sz blk) < Wasm_int.Int32.modulus)%Z⌝ ∗
    final_block_repr blk base_addr.
Proof.
  iIntros "H".
  destruct blk.
  iDestruct "H" as "(-> & %Hinbounds & H')".
  iFrame; auto.
Qed.

Definition freelist_repr (blks: list block * final_block) (base_addr: N) : iProp Σ :=
  let '(blks, final) := blks in
  ∃ next_addr,
    blocks_repr blks base_addr next_addr ∗
    final_block_repr final next_addr.

Definition block_shp (blk: block) : gmap N N :=
  {[(block_addr blk + data_off)%N := block_size blk]}.

Definition final_block_shp (blk: final_block) : gmap N N :=
  {[(final_block_addr blk + data_off)%N := final_block_sz blk]}.

(* Note: this doesn't enforce disjointness of block addresses, but the
   freelist_repr relation does. *)
Fixpoint blocklist_shp (blks: list block) : gmap N N :=
  match blks with
  | [] => ∅
  | blk :: blks => block_shp blk ∪ (blocklist_shp blks)
  end.

Definition freelist_shp (blks: list block * final_block) (shp: gmap N N) : Prop :=
  let '(blks, final) := blks in
  (blocklist_shp blks) ∪ (final_block_shp final) = shp.

(* An allocator token. *)
Definition alloc_tok (data_addr: N) (sz: N) : iProp Σ :=
  (data_addr ↦[tok] sz)%I.

(* The allocator invariant. *)
Definition alloc_inv : iProp Σ := 
  ∃ (shp: gmap N N) (blks: list block * final_block),
    ↪[toks] shp ∗
    ⌜freelist_shp blks shp⌝ ∗
    freelist_repr blks 0.

Lemma final_blk_repr_addr_eq :
  forall addr addr' sz,
    final_block_repr (FinalBlk addr sz) addr' ⊢
    final_block_repr (FinalBlk addr sz) addr' ∗ ⌜addr' = addr⌝.
Proof.
  iIntros (a a' sz) "[%Heq ?]".
  by iFrame.
Qed.

Lemma blocks_repr_app blks1 : forall base1 next1 blks2 base2 next2,
  ⌜next1 = base2⌝ ∗
  blocks_repr blks1 base1 next1 ∗
  blocks_repr blks2 base2 next2 ⊢
  blocks_repr (blks1 ++ blks2) base1 next2.
Proof.
  induction blks1; iIntros "*".
  - iIntros "(%Heq & %Heq' & Hblks2)".
    by subst.
  - iIntros "(%Heq & (%Heq' & %addr & Hblk & Hblks1) & Hblks2)".
    rewrite <- app_comm_cons.
    simpl blocks_repr.
    fold blocks_repr.
    iSplitR; auto.
    iExists addr.
    iFrame.
    iApply IHblks1.
    by iFrame.
Qed.

End reprs.
