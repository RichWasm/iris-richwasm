From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From Wasm.iris.logrel Require Export iris_fundamental.
From Wasm.iris.rules Require Export proofmode.
From RWasm.iris.allocator Require Export allocator_common.

Require Import misc_relocate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Section malloc.


 Context `{!wasmG Σ}. 

Section code.
  
(*
IDEA
We are given an entire WebAssembly memory to work with.
[0   ......   mem_size - 1]

This memory is partitioned into a circular linked list of blocks.

enum state_t ::= FREE | USED | FINAL

struct block_t {
  state_t   state;
  i32       size; // must be nonzero
  i32       next;
  u8[size]  data; // user data
}

INITIAL STATE
If the memory has size mem_size,
put a block at address 0:
  { state = FINAL; next = 0; size = mem_size - 12 }

INVARIANTS
The first block is always at address 0.
The last block has next = 0.
If the last block is at address K, it occupies [ K ... mem_size - 1 ].
The last block is the unique block marked FINAL and never contains user data.

GROWING THE MEMORY
pinch_block(final_block, reqd_sz):
  new_total_sz = reqd_sz + 12
  new_block = final_block + new_total_sz

  new_block.state = FINAL
  new_block.size = final_block.size - new_total_sz
  new_block.next = 0
  final_block.state = FREE
  final_block.size = reqd_sz
  final_block.next = new_block
  return final_block

new_block(final_block, reqd_sz):
  if final_block.sz > reqd_sz + 12:
    return pinch_block(final_block, reqd_sz)
  else:
    final_block.state = FREE
    final_block.next = mem_size
    actual_sz = grow_mem(reqd_sz)
    new_block = final_block.next
    new_block.state = FINAL
    new_block.size = actual_sz
    return pinch_block(new_block, reqd_sz)

MALLOC
malloc(reqd_sz):
  b = 0
  while b.state != FINAL:
    if b.sz > reqd_sz && b.state == FREE:
       b.state = USED
       return b.data
    else:
       b = b.next
  // b is the final block
  new_block(b, reqd_sz)
  b.state = USED
  return b.data

FREE
free(addr):
  if addr < 12:
    trap
  reqd_block = addr - 12
  b = 0
  while b.state != STOP:
    if b == reqd_block && b.state = USED:
      b.state = FREE
    else:
      b = b.next
  // address wasn't the address of a known allocation
  trap

*)
  
Definition BLK_FREE  : N := 0.
Definition BLK_USED  : N := 1.
Definition BLK_FINAL : N := 2.

(* sizeof(state_t) *)
Definition state_sz : N := 4.
(* sizeof(block_t) sans data *)
Definition blk_hdr_sz : N := 12.

(* offsets for fields of block_t *)
Definition state_off : N := 0.
Definition size_off  : N := 4.
Definition next_off  : N := 8.
Definition data_off  : N := blk_hdr_sz.

Definition get_state blk :=
  BI_get_local blk ::
  BI_load T_i32 None 0%N state_off ::
  nil.

Definition get_next blk :=
  BI_get_local blk ::
  BI_load T_i32 None 0%N next_off ::
  nil.

(* compute data pointer *)
Definition get_data blk :=
  BI_get_local blk ::
  u32const data_off ::
  BI_binop T_i32 (Binop_i BOI_add) ::
  nil.

Definition set_next :=
  [BI_store T_i32 None 0%N next_off].

(* this is the size of the data segment of the block *)
Definition get_size blk :=
  BI_get_local blk ::
  BI_load T_i32 None 0%N size_off ::
  nil.
  
Definition set_size :=
  [BI_store T_i32 None 0%N size_off].

Definition add_hdr_sz :=
  u32const blk_hdr_sz ::
  BI_binop T_i32 (Binop_i BOI_add) ::
  nil.

Definition sub_hdr_sz :=
  u32const blk_hdr_sz ::
  BI_binop T_i32 (Binop_i BOI_sub) ::
  nil.

(* this is the size of the whole block, including header! *)
Definition get_total_size blk :=
  get_size blk ++
  add_hdr_sz.

Definition mark_free blk :=
  [
    BI_get_local blk;
    u32const BLK_FREE;
    BI_store T_i32 None 0%N 0%N
  ].

Definition mark_used blk :=
  [
    BI_get_local blk;
    u32const BLK_USED;
    BI_store T_i32 None 0%N 0%N
  ].

Definition mark_final blk :=
  [
    BI_get_local blk;
    u32const BLK_FINAL;
    BI_store T_i32 None 0%N 0%N
  ].

Definition mem_size :=
  [
    BI_current_memory;
    u32const Wasm.operations.page_size;
    BI_binop T_i32 (Binop_i BOI_mul)
  ].

Definition is_block_nonfinal blk :=
  get_state blk ++
  u32const BLK_FINAL ::
  BI_relop T_i32 (Relop_i ROI_ne) ::
  nil.

Definition is_block_free blk :=
  get_state blk ++
  u32const BLK_FREE ::
  BI_relop T_i32 (Relop_i ROI_eq) ::
  nil.

(*
  pinch_block final sz 
  locals declared: [i32]

  Take a final block of size M
    [hdr| M...                  ]
  and pinch off a new one of a given size N < M - 12. The leftovers become
  the new final block.
    [hdr| N ][hdr| ...          ]
  Returns the address of the new block.

  Parameters/Locals:
  0     rw, pointer to the final block.
  1     ro, requested size to pinch off.
  2     rw, storing the total size (incl headers) of the pinched block.
  3     rw, storing the address of the new final block.
*)
Definition pinch_block final_block reqd_sz total_sz new_block :=
  (* compute and save total size of reqd block *)
  (BI_get_local reqd_sz ::
   add_hdr_sz ++
   BI_set_local total_sz ::
   nil) ++ 
  (* compute address of new final block *)
  (BI_get_local final_block ::
   BI_get_local total_sz ::
   BI_binop T_i32 (Binop_i BOI_add) ::
   BI_set_local new_block ::
   nil) ++
  (* set up new final block's header *)
  mark_final new_block ++
  (* set new block size *)
  (BI_get_local new_block ::
   (* compute block size on top of stack *)
   get_size final_block ++
   BI_get_local reqd_sz :: 
   BI_binop T_i32 (Binop_i BOI_sub) ::
   (* write top of stack to $3.size *)
   set_size) ++
  (* new_block.next = 0 *)
  (u32const 0%N :: set_next) ++
  (* set up pinched block *)
  (mark_free final_block ++
   BI_get_local final_block ::
   BI_get_local reqd_sz ::
   set_size ++
   BI_get_local final_block ::
   BI_get_local new_block ::
   set_next).

(*
  new_block: [i32; i32] -> [i32]
  Returns address of a block at least the requested size
  Parameters/Locals:
  0     parameter, pointer to final_block
  1     parameter, requested size
  2     local, actual size allocated
*)
Definition new_block final_block reqd_sz total_sz new_block actual_size :=
  BI_get_local reqd_sz ::
  add_hdr_sz ++
  get_size final_block ++
  BI_relop T_i32 (Relop_i (ROI_lt SX_U)) ::
  BI_if (Tf [] [])
    (* then *)
    (pinch_block final_block reqd_sz total_sz new_block)
    (* else *)
    (mark_free final_block ++
     BI_get_local final_block ::
     BI_get_local reqd_sz ::
     u32const Wasm.operations.page_size ::
     BI_binop T_i32 (Binop_i (BOI_div SX_U)) ::
     u32const 1%N ::
     BI_tee_local actual_size ::
     BI_binop T_i32 (Binop_i BOI_add) ::
     BI_grow_memory ::
     set_next ++

     BI_get_local final_block ::
     BI_get_local actual_size ::
     u32const Wasm.operations.page_size ::
     BI_binop T_i32 (Binop_i BOI_mul) ::
     set_size ++
     pinch_block final_block reqd_sz total_sz new_block) ::
    nil.

Definition malloc_loop_body reqd_sz cur_block :=
  (* break out of the loop if the block is final. *)
  is_block_nonfinal cur_block ++
  BI_br_if 1 ::
  (* Check if the block fits and is free. *)
  (* put the free flag at the top of the stack*)
  is_block_free cur_block ++
  (* Put a boolean representing whether the size is big enough at the top of the stack *)
  BI_get_local reqd_sz ::
  get_size cur_block ++ 
  BI_relop T_i32 (Relop_i (ROI_le SX_U)) ::
  (* Compute free && fits *)
  BI_binop T_i32 (Binop_i BOI_and) ::
  [BI_if (Tf [] []) 
    (* it's free and it fits, mark block as not free and return start *)
    (mark_used cur_block ++
     get_data cur_block ++ 
     [BI_return]) 
    (* if it isn't free or doesn't fit, try the next block *)
    (get_next cur_block ++
     [BI_set_local cur_block])]
  .

Definition malloc_body reqd_sz cur_block tmp1 tmp2 tmp3 :=
  (* Location of first block in the free list. *)
  i32const 0 ::
  (* Store the current block. *)
  BI_set_local cur_block ::
  BI_loop (Tf [] []) (malloc_loop_body reqd_sz cur_block) ::
  (* OK, we are at the end of the list! *)
  new_block cur_block reqd_sz tmp1 tmp2 tmp3 ++
  mark_used cur_block ++
  BI_get_local cur_block ::
  BI_return ::
  nil.
  
(*
  malloc: [i32] -> [i32]
  locals declared: [i32]

  Allocate a new block of memory of the requested size.
*)
Definition malloc :=
  malloc_body 0 1 2 3.

Definition free_body data_ptr :=
  BI_get_local data_ptr ::
  sub_hdr_sz ++
  BI_set_local data_ptr ::
  mark_free data_ptr ++
  BI_return ::
  nil.

Definition free :=
  free_body 0.

End code.

Section specs.

Inductive state_flag :=
| Used
| Free
| Final.

Inductive block : Type :=
| UsedBlk
    (blk_used_size: N)
    (blk_leftover_size: N)
    (*(blk_padding: iProp Σ)*)
| FreeBlk
    (blk_size: N).

Inductive final_block : Type :=
| FinalBlk
    (blk_size: N).

Definition blocks : Type :=
  list block * final_block.

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

Definition block_flag blk :=
  match blk with
  | UsedBlk _ _ => Used
  | FreeBlk _ => Free
  end.

Definition final_block_flag blk :=
  match blk with
  | FinalBlk _ => Final
  end.

Definition block_size blk : N :=
  match blk with
  | UsedBlk sz_u sz_l => sz_u + sz_l
  | FreeBlk sz => sz
  end.

Definition state_to_N (flag : state_flag) : N :=
  match flag with
  | Used => BLK_USED
  | Free => BLK_FREE
  | Final => BLK_FINAL
  end.

Definition state_repr (memidx: N) (flag: state_flag) (base_addr: N) : iProp Σ :=
  ∃ st,
    ⌜N_repr (state_to_N flag) st⌝ ∗
    memidx ↦[wms][base_addr + state_off] bits (VAL_int32 st).

Definition own_vec (memidx: N) (base_addr: N) (sz: N) : iProp Σ :=
  ∃ bs: bytes, ⌜N.of_nat (length bs) = sz⌝ ∗ memidx ↦[wms][base_addr] bs.

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

Definition block_inbounds (memidx: N) (blk: block) (base_addr: N) : iProp Σ :=
  ⌜(Z.of_N (base_addr + blk_hdr_sz + block_size blk) < Wasm_int.Int32.modulus)%Z⌝.

Definition block_repr (memidx: N) (blk: block) (base_addr next_addr: N) : iProp Σ :=
  block_inbounds memidx blk base_addr ∗
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
      state_repr memidx Final base_addr ∗
      size_repr memidx blk_size base_addr ∗
      next_repr memidx 0%N base_addr ∗
      own_vec memidx (base_addr + data_off) blk_size
  end.

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

(* SPECS: block getters *)
Lemma spec_get_state E memidx blk blk_addr next_addr blk_addr32 blk_var f :
  ⊢ {{{{ block_repr memidx blk blk_addr next_addr ∗
         ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    (to_e_list (get_state blk_var)) @ E
    {{{{ v, ∃ st32, 
              ⌜v = (immV [VAL_int32 st32])⌝ ∗
              ⌜N_repr (state_to_N (block_flag blk)) st32 ⌝ ∗
              block_repr memidx blk blk_addr next_addr ∗
              ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(Hblk & (%Hbdd & %Haddr) & %Hvar & %Hmem & Hfr) HΦ".
  cbn.
  take_drop_app_rewrite 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗ ↪[frame] f)%I).
  iSplitR; [iIntros "(%H & ?)"; auto|].
  iSplitL "Hfr".
  - iApply wp_get_local; eauto.
  - iIntros (w) "(%Hw & Hfr)".
    subst w.
    simpl.
    iDestruct "Hblk" as "(Hbounds & (%st32 & (%Hst & Hstate)) & Hsize & Hnext & Hdata)".
    unfold state_off.
    replace memidx with (N.of_nat (N.to_nat memidx)) by lia.
    iApply (wp_wand with "[Hstate Hfr]").
    instantiate (1:=(λ w, 
                       ((⌜w = immV [VAL_int32 st32]⌝ ∗
                         N.of_nat (N.to_nat memidx)↦[wms][Wasm_int.N_of_uint i32m blk_addr32 + 0]bits (VAL_int32 st32)) ∗ ↪[frame]f)%I)).
    + subst blk_addr.
      iApply wp_load; auto.
      iFrame.
      by iModIntro.
    + iIntros (w) "((%Hw & Hptr) & Hfr)".
      subst w blk_addr.
      iApply "HΦ".
      unfold block_repr, state_repr.
      iExists st32; iFrame; auto.
Qed.

Lemma spec_get_final_state E memidx blk blk_addr blk_addr32 blk_var f :
  ⊢ {{{{ final_block_repr memidx blk blk_addr ∗
         ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    (to_e_list (get_state blk_var)) @ E
    {{{{ v, ∃ st32,
              ⌜v = (immV [VAL_int32 st32])⌝ ∗
              ⌜N_repr (state_to_N (final_block_flag blk)) st32 ⌝ ∗
              final_block_repr memidx blk blk_addr ∗
              ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(Hblk & (%Hbdd & %Haddr) & %Hvar & %Hmem & Hfr) HΦ".
  cbn.
  take_drop_app_rewrite 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗ ↪[frame] f)%I).
  iSplitR; [iIntros "(%H & ?)"; auto|].
  iSplitL "Hfr".
  - iApply wp_get_local; eauto.
  - iIntros (w) "(%Hw & Hfr)".
    subst w.
    simpl.
    destruct blk.
    iDestruct "Hblk" as "((%st32 & (%Hst & Hstate)) & Hsize & Hnext & Hdata)".
    unfold state_off.
    replace memidx with (N.of_nat (N.to_nat memidx)) by lia.
    iApply (wp_wand with "[Hstate Hfr]").
    instantiate (1:=(λ w, 
                       ((⌜w = immV [VAL_int32 st32]⌝ ∗
                         N.of_nat (N.to_nat memidx)↦[wms][Wasm_int.N_of_uint i32m blk_addr32 + 0]bits (VAL_int32 st32)) ∗ ↪[frame]f)%I)).
    + subst blk_addr.
      iApply wp_load; auto.
      iFrame.
      by iModIntro.
    + iIntros (w) "((%Hw & Hptr) & Hfr)".
      subst w blk_addr.
      iApply "HΦ".
      unfold block_repr, state_repr.
      iExists st32; iFrame; auto.
Qed.

Lemma spec_get_next E memidx blk blk_addr next_addr blk_addr32 f blk_var :
  ⊢ {{{{ block_repr memidx blk blk_addr next_addr ∗
         ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    (to_e_list (get_next blk_var)) @ E
    {{{{ v, ∃ next_addr32,
              ⌜v = (immV [VAL_int32 next_addr32])⌝ ∗
              ⌜N_repr next_addr next_addr32 ⌝ ∗
              block_repr memidx blk blk_addr next_addr ∗
              ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(Hblk & (%Hbdd & %Haddr) & %Hvar & %Hmem & Hfr) HΦ".
  cbn.
  take_drop_app_rewrite 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗ ↪[frame] f)%I).
  iSplitR; [iIntros "(%H & ?)"; auto|].
  iSplitL "Hfr".
  - iApply wp_get_local; eauto.
  - iIntros (w) "(%Hw & Hfr)".
    subst w.
    simpl.
    iDestruct "Hblk" as "(Hbounds & Hstate & Hsize & (%next_addr32 & ((%Hbdd' & %Hnext_addr) & Hnext)) & Hdata)".
    replace memidx with (N.of_nat (N.to_nat memidx)) by lia.
    rewrite Haddr.
    iApply (wp_wand with "[Hnext Hfr]").
    instantiate (1:= λ w, ((⌜w = immV [VAL_int32 next_addr32]⌝ ∗ _) ∗ ↪[frame] f)%I).
    + iApply wp_load; try iFrame; auto.
    + iIntros (w) "((%Hw & Hptr) & Hfr)".
      subst w blk_addr.
      iApply "HΦ".
      unfold block_repr, next_repr.
      iExists next_addr32; iFrame; auto.
Qed.

Lemma spec_get_final_next E memidx blk blk_addr blk_addr32 f blk_var :
  ⊢ {{{{ final_block_repr memidx blk blk_addr ∗
         ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    (to_e_list (get_next blk_var)) @ E
    {{{{ v, ∃ next_addr32,
            ⌜v = (immV [VAL_int32 next_addr32])⌝ ∗
            ⌜N_repr 0%N next_addr32 ⌝ ∗
            final_block_repr memidx blk blk_addr ∗
            ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(Hblk & (%Hbdd & %Haddr) & %Hvar & %Hmem & Hfr) HΦ".
  destruct blk.
  cbn.
  take_drop_app_rewrite 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗ ↪[frame] f)%I).
  iSplitR; [iIntros "(%H & ?)"; auto|].
  iSplitL "Hfr".
  - iApply wp_get_local; eauto.
  - iIntros (w) "(%Hw & Hfr)".
    subst w.
    simpl.
    iDestruct "Hblk" as "(Hstate & Hsize & (%next_addr32 & ((%Hbdd' & %Hnext_addr) & Hnext)) & Hdata)".
    replace memidx with (N.of_nat (N.to_nat memidx)) by lia.
    rewrite Haddr.
    iApply (wp_wand with "[Hnext Hfr]").
    instantiate (1:= λ w, ((⌜w = immV [VAL_int32 next_addr32]⌝ ∗ _) ∗ ↪[frame] f)%I).
    + iApply wp_load; try iFrame; auto.
    + iIntros (w) "((%Hw & Hptr) & Hfr)".
      subst w blk_addr.
      iApply "HΦ".
      unfold final_block_repr, next_repr.
      iExists next_addr32.
      iFrame; auto.
Qed.

Lemma spec_get_data E memidx blk blk_addr blk_addr32 next_addr f blk_var : 
  ⊢ {{{{ ⌜N_repr blk_addr blk_addr32⌝ ∗
         block_repr memidx blk blk_addr next_addr ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    (to_e_list (get_data blk_var)) @ E
    {{{{ v, block_repr memidx blk blk_addr next_addr ∗
              ∃ data_addr32,
                ⌜v = (immV [VAL_int32 data_addr32])⌝ ∗
                ⌜N_repr (blk_addr + data_off) data_addr32⌝ ∗
                ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "((%Hbdd & %Haddr) & Hblk & %Hvar & %Hmem & Hfr) HΦ".
  cbn.
  take_drop_app_rewrite 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗ ↪[frame] f)%I).
  iSplitR; [iIntros "(%H & ?)"; auto|].
  iSplitL "Hfr".
  - iApply wp_get_local; eauto.
  - iIntros (w) "(%Hw & Hfr)".
    iAssert (block_inbounds memidx blk blk_addr) as "%Hbds".
    {
      by iDestruct "Hblk" as "(Hbds & Hblk')".
    } 
    iApply (wp_wand with "[Hfr]").
    instantiate (1 := λ v, (⌜v = immV [VAL_int32 (Wasm_int.Int32.iadd blk_addr32 (Wasm_int.Int32.repr 12))]⌝ ∗ ↪[frame] f)%I).
    + subst; cbn.
      iApply (wp_binop with "[Hfr]"); auto.
    + subst. 
      iIntros (w) "(%Hw & Hfr)".
      iApply "HΦ".
      iFrame.
      subst.
      iExists _; iSplit; auto.
      unfold data_off, blk_hdr_sz in *.
      iPureIntro.
      unfold Wasm_int.Int32.iadd.
      eapply N_repr_i32repr.
      * lia.
      * rewrite Wasm_int.Int32.unsigned_repr_eq.
        change ((12 `mod` Wasm_int.Int32.modulus)%Z) with 12%Z.
        rewrite N2Z.inj_add.
        f_equal.
        cbn in *.
        rewrite Z2N.id; auto.
        apply Wasm_int.Int32.unsigned_range.
Qed.

Lemma spec_get_size E memidx blk blk_addr next_addr blk_addr32 f blk_var : 
  ⊢ {{{{ block_repr memidx blk blk_addr next_addr ∗
         ⌜N_repr blk_addr blk_addr32⌝ ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    to_e_list (get_size blk_var) @ E
    {{{{ v, ∃ sz32,
              ⌜N_repr (block_size blk) sz32⌝ ∗
              ⌜v = (immV [VAL_int32 sz32])⌝ ∗
              block_repr memidx blk blk_addr next_addr ∗
              ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(Hblk & (%Hbdd & %Haddr) & %Hvar & %Hmem & Hfr) HΦ".
  cbn.
  take_drop_app_rewrite 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗ ↪[frame] f)%I).
  iSplitR; [iIntros "(%H & ?)"; auto|].
  iSplitL "Hfr".
  - iApply wp_get_local; eauto.
  - iIntros (w) "(%Hw & Hfr)".
    subst w.
    simpl.
    iDestruct "Hblk" as "(Hbounds & Hstate & (%sz32 & (%Hsz & Hsize)) & Hnext & Hdata)".
    unfold state_off.
    replace memidx with (N.of_nat (N.to_nat memidx)) by lia.
    iApply (wp_wand with "[Hsize Hfr]").
    instantiate (1:=(λ w, 
                       ((⌜w = immV [VAL_int32 sz32]⌝ ∗
                         N.of_nat (N.to_nat memidx)↦[wms][Wasm_int.N_of_uint i32m blk_addr32 + size_off]bits (VAL_int32 sz32)) ∗ ↪[frame]f)%I)).
    + subst blk_addr.
      iApply wp_load; auto.
      iFrame.
      by iModIntro.
    + iIntros (w) "((%Hw & Hptr) & Hfr)".
      subst w blk_addr.
      iApply "HΦ".
      unfold block_repr, size_repr.
      iExists sz32; iFrame; auto.
Qed.

(* SPECS: block setters *)
Lemma spec_set_next E blk memidx blk_addr blk_addr32 next_addr0 next_addr next_addr32 f :
  ⊢ {{{{ ⌜N_repr blk_addr blk_addr32⌝ ∗
          ⌜N_repr next_addr next_addr32⌝ ∗
          block_repr memidx blk blk_addr next_addr0 ∗
          ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
          ↪[frame] f }}}}
    to_e_list (BI_const (VAL_int32 blk_addr32) :: BI_const (VAL_int32 next_addr32) :: set_next) @ E
    {{{{ w, block_repr memidx blk blk_addr next_addr ∗
            ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(%Hblk & %Hnext & (Hbdd & Hst & Hsz & Hnext & Hdata) & %Hmem & Hfr) HΦ".
  cbn.
  replace memidx with (N.of_nat (N.to_nat memidx)) by lia.
  destruct Hblk as [Hblkbd Hblk].
  subst blk_addr.
  iApply (wp_wand with "[Hfr Hnext]").
  {
    iDestruct "Hnext" as "(%next32 & _ & Hnext')".
    iApply (wp_store (λ w, (⌜w = immV []⌝)%I)); try iFrame; auto.
  }
  iIntros (v) "((Hv & Hnext) & Hfr)".
  iApply "HΦ".
  iFrame; auto.
Qed.

(* need a version of this for
   - final blocks
   - free blocks
*)
Lemma spec_set_size_decr E memidx sz sz' sz32' blk_addr blk_addr32 next_addr f :
  ⊢ {{{{ ⌜N_repr blk_addr blk_addr32⌝ ∗
          ⌜N_repr sz' sz32'⌝ ∗
          ⌜(sz > sz')%N⌝ ∗
          block_repr memidx (FreeBlk sz) blk_addr next_addr ∗
          ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
          ↪[frame] f }}}}
    to_e_list (BI_const (VAL_int32 blk_addr32) :: BI_const (VAL_int32 sz32') :: set_size) @ E
    {{{{ w, block_repr memidx (FreeBlk sz') blk_addr next_addr ∗
            own_vec memidx (blk_addr + data_off + sz') (sz - sz') ∗
            ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(%Hblk & %Hsz' & %Hdecr & (Hbdd & Hst & Hsz & Hnext & Hdata) & %Hmem & Hfr) HΦ".
  cbn.
  replace memidx with (N.of_nat (N.to_nat memidx)) by lia.
  destruct Hblk as [Hblkbd Hblk].
  subst blk_addr.
  iApply (wp_wand with "[Hfr Hsz]").
  {
    iDestruct "Hsz" as "(%sz32 & (Hszr & Hsz))".
    iApply (wp_store (λ w, (⌜w = immV []⌝)%I)); try iFrame; auto.
  }
  iIntros (v) "((%Hv & Hsz) & Hfr)".
  cbn.
  iApply "HΦ".
  remember (sz - sz')%N as δ.
  replace sz with (sz' + δ)%N by lia.
  rewrite own_vec_split.
  iDestruct "Hdata" as "(Hdata & Hleft)".
  iFrame; auto.
  unfold block_inbounds.
  cbn.
  iDestruct "Hbdd" as "%Hbdd".
  iPureIntro.
  split; lia || auto.
Qed.

Lemma spec_set_size_final E memidx sz sz' sz32' blk_addr blk_addr32 f :
  ⊢ {{{{ ⌜N_repr blk_addr blk_addr32⌝ ∗
          ⌜N_repr sz' sz32'⌝ ∗
          size_repr memidx sz blk_addr ∗
          own_vec memidx (blk_addr + data_off) sz' ∗
          ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
          ↪[frame] f }}}}
    to_e_list (BI_const (VAL_int32 blk_addr32) :: BI_const (VAL_int32 sz32') :: set_size) @ E
    {{{{ w, size_repr memidx sz' blk_addr ∗
            own_vec memidx (blk_addr + data_off) sz' ∗
            ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(%Hblk & %Hsz' & Hszr & Hdata & %Hmem & Hfr) HΦ".
  cbn.
  replace memidx with (N.of_nat (N.to_nat memidx)) by lia.
  destruct Hblk as [Hblkbd Hblk].
  subst blk_addr.
  iApply (wp_wand with "[Hfr Hszr]").
  {
    iDestruct "Hszr" as "(%sz32 & (Hszr & Hsz))".
    iApply (wp_store (λ w, (⌜w = immV []⌝)%I)); try iFrame; auto.
  }
  iIntros (v) "((%Hv & Hsz) & Hfr)".
  cbn.
  iApply "HΦ".
  iFrame; auto.
Qed.

Lemma spec_add_hdr_sz E f base32 base : 
  ⊢ {{{{ ⌜N_repr base base32⌝ ∗
          ⌜(Z.of_N (base+blk_hdr_sz) < Wasm_int.Int32.modulus)%Z⌝ ∗
          ↪[frame] f}}}}
     to_e_list (BI_const (VAL_int32 base32) :: add_hdr_sz) @ E
     {{{{ w, ∃ out32, ⌜w = immV [VAL_int32 out32]⌝ ∗ ⌜N_repr (base + blk_hdr_sz) out32⌝ ∗↪[frame] f}}}}.
Proof.
  iIntros "!>" (Φ) "(%Hbase & %Hbdd & Hfr) HΦ".
  cbn.
  iApply (wp_wand with "[Hfr]").
  instantiate (1:= λ w, ((∃ out32, ⌜w = immV [VAL_int32 out32]⌝ ∗
                                          ⌜N_repr (base + blk_hdr_sz) out32⌝)
                           ∗ ↪[frame] f)%I).
  {
    iApply (wp_binop with "[Hfr]"); auto.
    iModIntro.
    iExists _; iSplit; eauto.
    iPureIntro.
    destruct Hbase as [[Hpos Hbd] Hconv].
    apply N_repr_i32repr.
    - lia.
    - subst.
      cbn in *.
      revert Hbdd.
      replace blk_hdr_sz with (Z.to_N 12%Z) by reflexivity.
      rewrite !Z2N.id in Hpos.
      rewrite <- Z2N.inj_add; lia.
      apply Wasm_int.Int32.size_interval_1.
  }
  iIntros (w) "(Hw & Hfr)".
  iApply "HΦ"; iFrame.
Qed.

Lemma block_repr_inbounds memidx blk base_addr next_addr :
  block_repr memidx blk base_addr next_addr ⊢
  block_repr memidx blk base_addr next_addr ∗
  ⌜(Z.of_N (base_addr + blk_hdr_sz + block_size blk) < Wasm_int.Int32.modulus)%Z⌝.
Proof.
  iIntros "(%Hbounds & Hblk')".
  iFrame; auto.
Qed.

Lemma spec_get_total_size E memidx blk blk_addr next_addr blk_addr32 f blk_var : 
  ⊢ {{{{ block_repr memidx blk blk_addr next_addr ∗
         ⌜N_repr blk_addr blk_addr32⌝ ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    to_e_list (get_total_size blk_var) @ E
    {{{{ v, ∃ sz32,
              ⌜N_repr (block_size blk + blk_hdr_sz) sz32⌝ ∗
              ⌜v = (immV [VAL_int32 sz32])⌝ ∗
              block_repr memidx blk blk_addr next_addr ∗
              ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(Hblk & %Haddr & %Hvar & %Hmem & Hfr) HΦ".
  unfold get_total_size.
  erewrite to_e_list_cat.
  iApply wp_seq.
  iSplitR.
  all: swap 1 2.
  {
    iSplitR "HΦ".
    iApply (spec_get_size with "[Hblk Hfr]"); iFrame; auto.
    iIntros (w) "(%sz32 & %Hsz & %Hw & Hblk & Hfr)".
    iPoseProof (block_repr_inbounds with "Hblk") as "(Hblk & %Hbdd)".
    subst w.
    iApply (spec_add_hdr_sz with "[Hfr]"); iFrame; eauto.
    - iSplit.
      + auto.
      + iPureIntro; lia.
    - iIntros (w) "(%out32 & Hout & Houtr & Hfr)".
      iApply "HΦ".
      iExists _; iFrame.
  }
  iIntros "(%sz32 & %Hsz & %Heq & Hfr)".
  congruence.
Qed.

Lemma spec_mark_free E f memidx blk sz blk_addr blk_addr32 next_addr sz_u sz_left :
  ⊢ {{{{ block_repr memidx (UsedBlk sz_u sz_left) blk_addr next_addr ∗
         own_vec memidx (blk_addr + data_off) sz_u ∗
         ⌜(sz = sz_u + sz_left)%N⌝ ∗
         ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         ⌜f.(f_locs) !! blk = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    (to_e_list (mark_free blk)) @ E
    {{{{ v, ⌜v = immV []⌝ ∗
            ⌜f.(f_locs) !! blk = Some (VAL_int32 blk_addr32)⌝ ∗
            block_repr memidx (FreeBlk sz) blk_addr next_addr ∗
            ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(Hblk & Hu & %Hsz & (%Haddrpf & %Haddr) & %Hblkvar & %Hmem & Hfr) HΦ".
  unfold mark_used.
  take_drop_app_rewrite 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗
                           ↪[frame]f)%I).
  iSplitR; [iIntros "(%H & ?)"; auto|].
  iSplitL "Hfr".
  { iApply wp_get_local; eauto. }
  iIntros (w) "(%Hw & Hfr)".
  subst w.
  simpl block_repr at 1.
  iDestruct "Hblk" as "(Hbd & Hstate & Hsize & Hnext & Hvec)".
  iSimpl.
  iDestruct "Hstate" as (st32) "(%Hst32 & Hstfield)".
  iApply (wp_wand with "[Hstfield Hfr]").
  instantiate (1 := λ w, ((⌜w = immV [] ⌝ ∗ 
                        N.of_nat (N.to_nat memidx) ↦[wms][blk_addr + state_off]bits (value_of_uint BLK_FREE)) ∗
                        ↪[frame]f)%I).
  - unfold state_off.
    rewrite Haddr.
    iApply wp_store;
      eauto;
      try rewrite N2Nat.id;
      [| iFrame ];
      auto.
  - iIntros (w) "((%Hw & Hstfield) & Hfr)".
    subst w.
    iApply "HΦ".
    unfold block_repr, data_repr.
    rewrite Hsz.
    rewrite N2Nat.id.
    iFrame; auto.
    repeat iSplit; auto.
    rewrite own_vec_split.
    iFrame.
Qed.

Lemma spec_mark_used E f memidx blk sz blk_addr blk_addr32 next_addr sz_u sz_left :
  ⊢ {{{{ block_repr memidx (FreeBlk sz) blk_addr next_addr ∗
         ⌜(sz = sz_u + sz_left)%N⌝ ∗
         ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         ⌜f.(f_locs) !! blk = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    (to_e_list (mark_used blk)) @ E
    {{{{ v, ⌜v = immV []⌝ ∗
            ⌜f.(f_locs) !! blk = Some (VAL_int32 blk_addr32)⌝ ∗
            own_vec memidx (blk_addr + data_off) sz_u ∗
            block_repr memidx (UsedBlk sz_u sz_left) blk_addr next_addr ∗
            ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(Hblk & %Hsz & (%Haddrpf & %Hblk_addr_rep) & %Hblkvar & %Hmem &  Hfr) HΦ".
  unfold mark_used.
  take_drop_app_rewrite 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗
                           ↪[frame]f)%I).
  iSplitR; [iIntros "(%H & ?)"; auto|].
  iSplitL "Hfr".
  { iApply wp_get_local; eauto. }
  iIntros (w) "(%Hw & Hfr)".
  subst w.
  simpl block_repr at 1.
  iDestruct "Hblk" as "(Hbd & Hstate & Hsize & Hnext & Hvec)".
  iSimpl.
  iDestruct "Hstate" as (st32) "(%Hst32 & Hstfield)".
  iApply (wp_wand with "[Hstfield Hfr]").
  instantiate (1 := λ w, ((⌜w = immV [] ⌝ ∗ 
                        N.of_nat (N.to_nat memidx) ↦[wms][blk_addr + state_off]bits (value_of_uint BLK_USED)) ∗
                        ↪[frame]f)%I).
  - unfold state_off.
    rewrite Hblk_addr_rep.
    iApply wp_store;
      eauto;
      try rewrite N2Nat.id;
      [| iFrame ];
      auto.
  - iIntros (w) "((%Hw & Hstfield) & Hfr)".
    subst w.
    iApply "HΦ".
    unfold block_repr, state_repr.
    rewrite Hsz.
    rewrite N2Nat.id.
    iPoseProof (own_vec_split with "Hvec") as "(Hvec1 & Hvec2)".
    iFrame; auto.
Qed.


Lemma spec_mark_final
(*TODO
*)

(* SPECS: block tests *)
(*TODO
Lemma spec_is_block_nonfinal
Lemma spec_is_block_free
*)

(* SPECS: memory resizing *)
(*TODO
Lemma spec_mem_size
*)

(* SPECS: block pinching *)
(*TODO
Lemma spec_pinch_block
*)

(* SPECS: block creation *)
(*TODO
Lemma spec_new_block
*)

(* SPECS: malloc *)
(*TODO
Lemma spec_malloc_loop_body
Lemma spec_malloc_body
Lemma spec_malloc
*)

(* SPECS: free *)
(*TODO
Lemma spec_free
*)

(* Keeping these but commenting out since I broke the proofs
Lemma spec_malloc E f0 reqd_sz (memidx: memaddr) blk :
  ⊢ {{{{ ⌜f0.(f_inst).(inst_memory) !! 0 = Some memidx⌝ ∗
         ⌜f0.(f_locs) !! 0 = Some (VAL_int32 reqd_sz)⌝ ∗
         ⌜length (f_locs f0) >= 2⌝ ∗
         blk_rep blk (N.of_nat memidx) 0 ∗
         ↪[frame] f0
    }}}}
    (to_e_list malloc) @ E
    {{{{ v, ∃ ret_addr, ⌜v = immV [value_of_uint ret_addr]⌝ ∗
            ∃ blk', blk_rep blk' (N.of_nat memidx) 0 ∗ 
                    own_block (N.of_nat memidx) ret_addr reqd_sz ∗
                    ↪[frame] f0 }}}}.
Proof.
  iIntros "!>" (Φ) "(%Hmemidx & %Hsz & %Hlen & Hblk & Hfr) HΦ".
  unfold malloc.
  erewrite !to_e_list_cat.
  set (f1 := {| f_locs := set_nth (value_of_uint 0) (f_locs f0) 1 (value_of_uint 0);
                f_inst := f_inst f0 |}).
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV []⌝ ∗ ↪[frame] f1)%I).
  iSplitR.
  { iIntros "(%Htrap & _)". auto. }
  iSplitL "Hfr".
  {
    cbn. 
    unfold i32const.
    iApply wp_set_local => //.
  }
  iIntros (w) "(%Htrap & Hfr)".
  subst w.
  iApply wp_wasm_empty_ctx.
  iApply (wp_loop_ctx with "[Hfr] [HΦ]") => //; eauto.
  iIntros "!> Hfr".
  iApply wp_label_push_emp.
  iApply wp_ctx_bind; [cbn; tauto|].
  cbn.
  take_drop_app_rewrite 1.
  iApply wp_seq; cbn.
  instantiate (1 := λ v, (⌜v = immV [value_of_uint 0]⌝ ∗ ↪[frame] f1)%I).
  iSplitR.
  { iIntros "(%Htrap & _)" => //. }
  iSplitL "Hfr".
  { 
    iApply wp_get_local => //.
    apply set_nth_read.
  }
  iIntros (w) "(%Hzero & Hfr)".
  subst w.
  take_drop_app_rewrite 2.
  iApply wp_seq; cbn.
Abort.

*)
End specs.    
End malloc.    
      
