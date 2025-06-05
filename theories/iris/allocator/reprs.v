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
From RWasm Require Export num_repr.
Import blocks.

Set Bullet Behavior "Strict Subproofs".

Section reprs.

Context `{!wasmG Σ} `{!allocG Σ}.
Variables (memidx: N).

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
  match blk with
  | UsedBlk base_addr blk_used_size blk_leftover_size => {[(base_addr + data_off)%N := blk_used_size]}
  | _ => ∅
  end.

(* Note: this doesn't enforce disjointness of block addresses, but the
   freelist_repr relation does. *)
Definition blocklist_shp (blks: list block) : gmap N N :=
  ⋃ (map block_shp blks).

Definition freelist_shp (blks: list block * final_block) (shp: gmap N N) : Prop :=
  blocklist_shp (fst blks) = shp.

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

Lemma app_blocks_repr blks1 : forall blks2 base1 next2,
    blocks_repr (blks1 ++ blks2) base1 next2 ⊢
    ∃ next1, blocks_repr blks1 base1 next1 ∗
             blocks_repr blks2 next1 next2.
Proof.
  induction blks1.
  iIntros "* Hrep".
  - iExists base1.
    by iFrame.
  - iIntros "* Hrep".
    cbn.
    iDestruct "Hrep" as "(%Hbase & (%addr & Hrep & Hreps))".
    rewrite Hbase.
    iPoseProof (IHblks1 with "[$]") as "(%addr' & Hxs & Hys)".
    iExists addr'.
    rewrite <- bi.sep_assoc.
    by iFrame.
Qed.

Lemma i32_has_4_bytes i:
  exists b0 b1 b2 b3, 
    bits (VAL_int32 i) = [b0; b1; b2; b3].
Proof.
  cbn.
  remember (serialise_i32 i) as l eqn:Hl.
  apply (f_equal length) in Hl.
  unfold serialise_i32 in *.
  rewrite Memdata.encode_int_length in Hl.
  repeat (destruct l; (cbn in Hl; try congruence)).
  eauto.
Qed.

Lemma block_repr_addr_ne blk1 blk2 next1 next2 :
  block_repr blk1 next1 ∗ block_repr blk2 next2 ⊢ ⌜block_addr blk1 ≠ block_addr blk2⌝.
Proof.
  iIntros "((_ & (%st1 & _ & Hst1) & _) & (_ & (%st2 & _ & Hst2) & _))".
  destruct (i32_has_4_bytes st1) as (b10 & b11 & b12 & b13 & Hbs1).
  destruct (i32_has_4_bytes st2) as (b20 & b21 & b22 & b23 & Hbs2).
  rewrite Hbs1 Hbs2.
  iDestruct "Hst1" as "[Hst1 _]".
  iDestruct "Hst2" as "[Hst2 _]".
  cbn.
  unfold state_off.
  rewrite !Nat.add_0_r !N.add_0_r.
  rewrite !N2Nat.id.
  iPoseProof (@pointsto_ne with "[$Hst1] [$Hst2]") as "%Hneq".
  iPureIntro.
  congruence.
Qed.

Lemma two_block_shp_disjoint blk1 next1 blk2 next2 :
    block_repr blk1 next1 ∗
    block_repr blk2 next2 ⊢
    ⌜block_shp blk1 !! (block_addr blk2 + data_off)%N = None⌝.
Proof.
  iIntros "[Hblk1 Hblk2]".
  destruct blk1; cbn.
  - iPoseProof (block_repr_addr_ne with "[$]") as "%Hneq".
    iPureIntro.
    apply not_elem_of_dom.
    rewrite dom_singleton.
    apply not_elem_of_singleton_2.
    cbn in Hneq.
    lia.
  - done.
Qed.

Lemma blocks_shp_disjoint blks : forall blk next0 base next,
    block_repr blk next0 ∗ blocks_repr blks base next ⊢
    ⌜blocklist_shp blks !! (block_addr blk + data_off)%N = None⌝.
Proof.
  induction blks as [|blk' blks]; intros.
  - by iIntros "_ !%".
  - iIntros "(Hblk & Hblks)".
    rewrite lookup_union.
    fold blocklist_shp.
    rewrite union_None.
    iDestruct "Hblks" as "(%Hbase & %addr & H1 & H2)".
    fold blocks_repr.
    iSplit.
    + iApply two_block_shp_disjoint; by iFrame.
    + iApply IHblks.
      iFrame.
Qed.

Lemma freed_blocklist_shp xs : forall base start final ys sz_u sz_l sz' shp,
  blocks_repr (xs ++ UsedBlk base sz_u sz_l :: ys) start final ∗
  ⌜blocklist_shp (xs ++ UsedBlk base sz_u sz_l :: ys) = shp⌝ ⊢
  ⌜blocklist_shp (xs ++ FreeBlk base sz' :: ys) = delete (base + data_off)%N shp⌝.
Proof.
  induction xs; intros; cbn; iIntros "((-> & %addr & Hblk & Hblks) & <-)".
  - rewrite delete_union.
    rewrite delete_singleton.
    iPoseProof (blocks_shp_disjoint with "[$]") as "%Hdisj".
    by rewrite delete_notin.
  - iPoseProof ((IHxs _ _ _ _ _ _ sz') with "[$Hblks //]") as "%IH".
    iPoseProof (app_blocks_repr with "[$]") as "(%next1 & Hblks1 & Hblks2)".
    iDestruct "Hblks2" as "(%Hbase & %next2 & Hblk' & Hblks)".
    fold blocks_repr.
    iPoseProof (two_block_shp_disjoint with "[$Hblk $Hblk']") as "%Hdisj".
    (*iPoseProof (blocks_shp_disjoint with "[$Hblk $Hblks]") as "%Hdisj2".*)
    rewrite delete_union.
    unfold blocklist_shp in IH.
    erewrite IH.
    iPureIntro.
    f_equal.
    by rewrite delete_notin.
Qed.

End reprs.
