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

  final_block.size = reqd_sz
  final_block.state = FREE
  final_block.next = new_block

  new_block.state = FINAL
  new_block.size = final_block.size - new_total_sz
  new_block.next = 0
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
Definition pinch_block final_block reqd_sz old_sz new_block :=
  (* save size of entire block *)
   (get_size final_block ++
   BI_set_local old_sz ::
   nil) ++ 
  (* compute address of new final block *)
  ([BI_get_local final_block;
    BI_get_local reqd_sz] ++
   add_hdr_sz ++
   [BI_binop T_i32 (Binop_i BOI_add)]) ++
   (([BI_set_local new_block]) ++
  (* set up pinched block *)
  (BI_get_local final_block ::
   BI_get_local reqd_sz ::
   set_size ++
   mark_free final_block ++
   BI_get_local final_block ::
   BI_get_local new_block ::
   set_next)) ++
  (* set up new block's header *)
  mark_final new_block ++
  (* set new block size *)
  (BI_get_local new_block ::
   (* compute block size on top of stack *)
   BI_get_local old_sz ::
   BI_get_local reqd_sz :: 
   add_hdr_sz ++
   BI_binop T_i32 (Binop_i BOI_sub) ::
   (* write top of stack to $3.size *)
   set_size) ++
  (* new_block.next = 0 *)
  (BI_get_local new_block :: u32const 0%N :: set_next).

(*
  new_block: [i32; i32] -> [i32]
  Returns address of a block at least the requested size
  Parameters/Locals:
  0     parameter, pointer to final_block
  1     parameter, requested size
  2     local, actual size allocated
*)
Definition new_block final_block reqd_sz old_sz new_block actual_size :=
  BI_get_local reqd_sz ::
  add_hdr_sz ++
  get_size final_block ++
  BI_relop T_i32 (Relop_i (ROI_lt SX_U)) ::
  BI_if (Tf [] [])
    (* then *)
    (pinch_block final_block reqd_sz old_sz new_block)
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
     pinch_block final_block reqd_sz old_sz new_block) ::
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

Ltac wp_chomp := take_drop_app_rewrite.
Ltac wp_chomp2 := take_drop_app_rewrite_twice.

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
  wp_chomp 1.
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
  wp_chomp 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗ ↪[frame] f)%I).
  iSplitR; [iIntros "(%H & ?)"; auto|].
  iSplitL "Hfr".
  - iApply wp_get_local; eauto.
  - iIntros (w) "(%Hw & Hfr)".
    subst w.
    simpl.
    destruct blk.
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
  wp_chomp 1.
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
  wp_chomp 1.
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
  wp_chomp 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗ ↪[frame] f)%I).
  iSplitR; [iIntros "(%H & ?)"; auto|].
  iSplitL "Hfr".
  - iApply wp_get_local; eauto.
  - iIntros (w) "(%Hw & Hfr)".
    iAssert (block_inbounds memidx (block_size blk) blk_addr) as "%Hbds".
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
  wp_chomp 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗ ↪[frame] f)%I).
  iSplitR; [iIntros "(%H & ?)"; auto|].
  iSplitL "Hfr".
  - iApply wp_get_local; eauto.
  - iIntros (w) "(%Hw & Hfr)".
    subst w.
    simpl.
    iDestruct "Hblk" as "(Hbounds & Hstate & (%sz32 & (%Hsz & Hsize)) & Hnext & Hdata)".
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

Lemma spec_get_final_size E memidx blk_addr blk_addr32 f sz blk_var : 
  ⊢ {{{{ final_block_repr memidx (FinalBlk sz) blk_addr ∗
         ⌜N_repr blk_addr blk_addr32⌝ ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    to_e_list (get_size blk_var) @ E
    {{{{ v, ∃ sz32,
              ⌜N_repr sz sz32⌝ ∗
              ⌜v = (immV [VAL_int32 sz32])⌝ ∗
              final_block_repr memidx (FinalBlk sz) blk_addr ∗
              ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(Hblk & (%Hbdd & %Haddr) & %Hvar & %Hmem & Hfr) HΦ".
  wp_chomp 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗ ↪[frame] f)%I).
  iSplitR; [iIntros "(%H & ?)"; auto|].
  iSplitL "Hfr".
  - iApply wp_get_local; eauto.
  - iIntros (w) "(%Hw & Hfr)".
    subst w.
    simpl.
    iDestruct "Hblk" as "(Hbounds & Hstate & (%sz32 & (%Hsz & Hsize)) & Hdata)".
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
      iExists sz32.
      by iFrame.
Qed.

(* SPECS: block setters *)
Lemma spec_set_next_basic E memidx blk_addr blk_addr32 next_addr next_addr32 f :
  ⊢ {{{{ ⌜N_repr blk_addr blk_addr32⌝ ∗
          ⌜N_repr next_addr next_addr32⌝ ∗
          own_vec memidx (blk_addr + next_off) 4 ∗
          ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
          ↪[frame] f }}}}
    to_e_list (BI_const (VAL_int32 blk_addr32) :: BI_const (VAL_int32 next_addr32) :: set_next) @ E
    {{{{ w, ⌜w = immV [] ⌝ ∗
            next_repr memidx next_addr blk_addr ∗
            ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(%Hblk & %Hnext & Hvec & %Hmem & Hfr) HΦ".
  cbn.
  unfold own_vec.
  replace memidx with (N.of_nat (N.to_nat memidx)) by lia.
  rewrite (N_repr_uint Hblk).
  iApply (wp_wand with "[Hfr Hvec]").
  {
    iDestruct "Hvec" as "(%next32 & %Hlen & Hnext')".
    iApply (wp_store (λ w, (⌜w = immV []⌝)%I)); try iFrame; auto.
    cbn; lia.
  }
  iIntros (v) "((Hv & Hnext) & Hfr)".
  iApply "HΦ".
  iFrame; auto.
Qed.

Lemma spec_set_next E blk memidx blk_addr blk_addr32 next_addr0 next_addr next_addr32 f :
  ⊢ {{{{ ⌜N_repr blk_addr blk_addr32⌝ ∗
          ⌜N_repr next_addr next_addr32⌝ ∗
          block_repr memidx blk blk_addr next_addr0 ∗
          ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
          ↪[frame] f }}}}
    to_e_list (BI_const (VAL_int32 blk_addr32) :: BI_const (VAL_int32 next_addr32) :: set_next) @ E
    {{{{ w, ⌜w = immV [] ⌝ ∗
            block_repr memidx blk blk_addr next_addr ∗
            ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(%Hblk & %Hnext & (Hbdd & Hst & Hsz & Hnext & Hdata) & %Hmem & Hfr) HΦ".
  iDestruct "Hnext" as "(%next32 & %Hrepr & Hvec)".
  iApply (spec_set_next_basic with "[$Hfr Hvec]").
  {
    iSplit; auto.
    iSplit; auto.
    iSplit; auto.
    iExists _.
    iFrame.
    rewrite (length_bits _ T_i32); eauto.
  }
  iIntros (w) "(-> & Hnext & Hfr)".
  unfold block_repr.
  iApply "HΦ"; iFrame; auto.
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

Lemma spec_set_size_final_setup E memidx sz' sz32' blk_addr blk_addr32 f :
  ⊢ {{{{ ⌜N_repr blk_addr blk_addr32⌝ ∗
          ⌜N_repr sz' sz32'⌝ ∗
          own_vec memidx (blk_addr + size_off) 4 ∗
          own_vec memidx (blk_addr + data_off) sz' ∗
          ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
          ↪[frame] f }}}}
    to_e_list (BI_const (VAL_int32 blk_addr32) :: BI_const (VAL_int32 sz32') :: set_size) @ E
    {{{{ w, ⌜w = immV [] ⌝ ∗ 
            size_repr memidx sz' blk_addr ∗
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
    iDestruct "Hszr" as "(%bs & (%Hbslen & Hsz))".
    iApply (wp_store (λ w, (⌜w = immV []⌝)%I)); try iFrame; auto.
    cbn; lia.
  }
  iIntros (v) "((%Hv & Hsz) & Hfr)".
  cbn.
  iApply "HΦ".
  iFrame; auto.
Qed.

Lemma spec_set_size_final E memidx sz sz' sz32' blk_addr blk_addr32 f :
  ⊢ {{{{ ⌜N_repr blk_addr blk_addr32⌝ ∗
          ⌜N_repr sz' sz32'⌝ ∗
          size_repr memidx sz blk_addr ∗
          own_vec memidx (blk_addr + data_off) sz' ∗
          ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
          ↪[frame] f }}}}
    to_e_list (BI_const (VAL_int32 blk_addr32) :: BI_const (VAL_int32 sz32') :: set_size) @ E
    {{{{ w, ⌜w = immV [] ⌝ ∗ 
            size_repr memidx sz' blk_addr ∗
            own_vec memidx (blk_addr + data_off) sz' ∗
            ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(%Hblk & %Hsz' & (%sz32 & %Hszr & Hpts) & Hdata & %Hmem & Hfr) HΦ".
  cbn.
  iApply (spec_set_size_final_setup with "[$Hpts $Hdata $Hfr //]").
  auto.
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
  wp_chomp 1.
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

Lemma spec_mark_free_final E f memidx blk sz blk_addr blk_addr32 :
  ⊢ {{{{ final_block_repr memidx (FinalBlk sz) blk_addr ∗
         ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         ⌜f.(f_locs) !! blk = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    (to_e_list (mark_free blk)) @ E
    {{{{ v, ⌜v = immV []⌝ ∗
            ⌜f.(f_locs) !! blk = Some (VAL_int32 blk_addr32)⌝ ∗
            block_repr memidx (FreeBlk sz) blk_addr 0 ∗
            ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(Hblk & (%Haddrpf & %Haddr) & %Hblkvar & %Hmem & Hfr) HΦ".
  unfold mark_used.
  wp_chomp 1.
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
    rewrite N2Nat.id.
    iFrame; auto.
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
  wp_chomp 1.
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

Lemma spec_mark_final E memidx blk_addr blk_addr32 blk f :
  ⊢ {{{{ own_vec memidx (blk_addr + state_off) 4 ∗
          ⌜N_repr blk_addr blk_addr32 ⌝ ∗
          ⌜f.(f_locs) !! blk = Some (VAL_int32 blk_addr32)⌝ ∗
          ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
          ↪[frame] f }}}}
    (to_e_list (mark_final blk)) @ E
    {{{{ v, ⌜v = immV []⌝ ∗
            state_repr memidx Final blk_addr ∗
            ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "((%bs & %Hbs & Hslot) & (%Haddrpf & %Hblk_addr_rep) & %Hblkvar & %Hmem & Hfr) HΦ".
  wp_chomp 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗
                           ↪[frame]f)%I).
  iSplitR.
  { iIntros "(%Htrap & Hfr)"; congruence. }
  iSplitL "Hfr".
  {
    iApply wp_get_local; eauto.
  }
  iIntros (w) "(%Hw & Hfr)".
  subst w; cbn.
  iApply (wp_wand with "[Hslot Hfr]").
  {
    iApply wp_store; eauto.
    all: swap 1 2.
    rewrite <- Hblk_addr_rep.
    rewrite N2Nat.id.
    iFrame.
    instantiate (1:= λ w, ⌜w = immV [] ⌝%I).
    eauto.
    cbn.
    lia.
  }
  iIntros (w) "((%Hw & Hpts) & Hfr)".
  iApply "HΦ".
  subst.
  iFrame; auto.
  iSplit; auto.
  unfold state_repr.
  rewrite N2Nat.id.
  iExists (Wasm_int.int_of_Z i32m (Z.of_N BLK_FINAL)).
  iFrame.
  auto.
Qed.

(* SPECS: block tests *)

Lemma spec_is_block_nonfinal_true E memidx blk blk_var blk_addr blk_addr32 next_addr f :
  ⊢ {{{{ ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         block_repr memidx blk blk_addr next_addr ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    to_e_list (is_block_nonfinal blk_var) @ E
    {{{{ w,⌜w = immV [VAL_int32 (wasm_bool true)]⌝ ∗
         block_repr memidx blk blk_addr next_addr ∗
         ↪[frame] f }}}}.
Proof.
  iIntros (Φ) "!> (%Hblk_addr & Hblk & %Hvar & %Hmem & Hfr) HΦ".
  unfold is_block_nonfinal.
  erewrite to_e_list_cat.
  iApply wp_seq.
  iSplitR.
  all:swap 1 2.
  iSplitL "Hblk Hfr".
  - iApply (spec_get_state with "[Hblk Hfr]"); iFrame; eauto.
  - iIntros (w) "(%st32 & %Hw & %Hst & Hblk & Hfr)".
    subst w.
    cbn.
    iApply (wp_wand with "[Hfr]").
    + iApply (wp_relop with "[Hfr]"); auto.
      instantiate (1:=λ w, ⌜w = immV [VAL_int32 (wasm_bool true)]⌝%I).
      iModIntro.
      iPureIntro.
      assert (st32 <> (Wasm_int.int_of_Z i32m (Z.of_N BLK_FINAL))).
      {
        intro; subst.
        destruct blk; destruct Hst; cbn in *; discriminate.
      }
      cbn.
      rewrite Wasm_int.Int32.eq_false; auto.
    + iIntros (w) "(%Hw & Hfr)".
      subst.
      iApply "HΦ".
      iFrame; auto.
  - iIntros "(%st32 & %Htrap & _)".
    congruence.
Qed.

Lemma spec_is_block_nonfinal_false E memidx blk blk_var blk_addr blk_addr32 f :
  ⊢ {{{{ ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         final_block_repr memidx blk blk_addr ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    to_e_list (is_block_nonfinal blk_var) @ E
    {{{{ w,⌜w = immV [VAL_int32 (wasm_bool false)]⌝ ∗
         final_block_repr memidx blk blk_addr ∗
         ↪[frame] f }}}}.
Proof.
  iIntros (Φ) "!> (%Hblk_addr & Hblk & %Hvar & %Hmem & Hfr) HΦ".
  unfold is_block_nonfinal.
  erewrite to_e_list_cat.
  iApply wp_seq.
  iSplitR.
  all:swap 1 2.
  iSplitL "Hblk Hfr".
  - iApply (spec_get_final_state with "[Hblk Hfr]"); iFrame; eauto.
  - iIntros (w) "(%st32 & %Hw & %Hst & Hblk & Hfr)".
    subst w.
    cbn.
    iApply (wp_wand with "[Hfr]").
    + iApply (wp_relop with "[Hfr]"); auto.
      instantiate (1:=λ w, ⌜w = immV [VAL_int32 (wasm_bool false)]⌝%I).
      iModIntro.
      iPureIntro.
      assert (st32 = (Wasm_int.int_of_Z i32m (Z.of_N BLK_FINAL))).
      {
        inversion Hst as [Hbd Hst'].
        destruct blk.
        rewrite <- (Wasm_int.Int32.repr_unsigned st32).
        cbn in *.
        rewrite <- (Z2N.id (Wasm_int.Int32.unsigned st32)).
        rewrite <- Hst'.
        reflexivity.
        apply Wasm_int.Int32.size_interval_1.
      }
      cbn.
      subst.
      rewrite Wasm_int.Int32.eq_true; auto.
    + iIntros (w) "(%Hw & Hfr)".
      subst.
      iApply "HΦ".
      iFrame; auto.
  - iIntros "(%st32 & %Htrap & _)".
    congruence.
Qed.

Definition prop_repr (P : Prop) (b: bool) : Prop :=
  is_true b <-> P.

Lemma spec_is_block_free_true blk_addr blk_addr32 next_addr sz memidx blk_var f E:
  ⊢ {{{{ ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         block_repr memidx (FreeBlk sz) blk_addr next_addr ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    to_e_list (is_block_free blk_var) @ E
    {{{{ w, ⌜w = immV [VAL_int32 (wasm_bool true)]⌝ ∗
            block_repr memidx (FreeBlk sz) blk_addr next_addr ∗
            ↪[frame] f }}}}.
Proof.
  iIntros (Φ) "!> (%Hblk_addr & Hblk & %Hvar & %Hmem & Hfr) HΦ".
  unfold is_block_free.
  erewrite to_e_list_cat.
  iApply wp_seq.
  iSplitR.
  all:swap 1 2.
  iSplitL "Hblk Hfr".
  - iApply (spec_get_state with "[Hblk Hfr]"); iFrame; eauto.
  - iIntros (w) "(%st32 & %Hw & %Hst & Hblk & Hfr)".
    subst w.
    cbn.
    iApply (wp_wand with "[Hfr]").
    + iApply (wp_relop with "[Hfr]"); auto.
      instantiate (1:=λ w, ⌜w = immV [VAL_int32 (wasm_bool true)]⌝%I).
      iModIntro.
      iPureIntro.
      assert (st32 = (Wasm_int.int_of_Z i32m (Z.of_N BLK_FREE))).
      {
        inversion Hst as [Hbd Hst'].
        rewrite <- (Wasm_int.Int32.repr_unsigned st32).
        cbn in *.
        rewrite <- (Z2N.id (Wasm_int.Int32.unsigned st32)).
        rewrite <- Hst'.
        reflexivity.
        apply Wasm_int.Int32.size_interval_1.
      }
      subst.
      reflexivity.
    + iIntros (w) "(%Hw & Hfr)".
      subst.
      iApply "HΦ".
      iFrame; auto.
  - iIntros "(%st32 & %Htrap & _)".
    congruence.
Qed.

Lemma spec_is_block_free_false blk_addr blk_addr32 next_addr sz_u sz_l memidx blk_var f E:
  ⊢ {{{{ ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         block_repr memidx (UsedBlk sz_u sz_l) blk_addr next_addr ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    to_e_list (is_block_free blk_var) @ E
    {{{{ w, ⌜w = immV [VAL_int32 (wasm_bool false)]⌝ ∗
            block_repr memidx (UsedBlk sz_u sz_l) blk_addr next_addr ∗
            ↪[frame] f }}}}.
Proof.
  iIntros (Φ) "!> (%Hblk_addr & Hblk & %Hvar & %Hmem & Hfr) HΦ".
  unfold is_block_free.
  erewrite to_e_list_cat.
  iApply wp_seq.
  iSplitR.
  all:swap 1 2.
  iSplitL "Hblk Hfr".
  - iApply (spec_get_state with "[Hblk Hfr]"); iFrame; eauto.
  - iIntros (w) "(%st32 & %Hw & %Hst & Hblk & Hfr)".
    subst w.
    cbn.
    iApply (wp_wand with "[Hfr]").
    + iApply (wp_relop with "[Hfr]"); auto.
      instantiate (1:=λ w, ⌜w = immV [VAL_int32 (wasm_bool false)]⌝%I).
      iModIntro.
      iPureIntro.
      assert (st32 = (Wasm_int.int_of_Z i32m (Z.of_N BLK_USED))).
      {
        inversion Hst as [Hbd Hst'].
        rewrite <- (Wasm_int.Int32.repr_unsigned st32).
        cbn in *.
        rewrite <- (Z2N.id (Wasm_int.Int32.unsigned st32)).
        rewrite <- Hst'.
        reflexivity.
        apply Wasm_int.Int32.size_interval_1.
      }
      subst.
      reflexivity.
    + iIntros (w) "(%Hw & Hfr)".
      subst.
      iApply "HΦ".
      iFrame; auto.
  - iIntros "(%st32 & %Htrap & _)".
    congruence.
Qed.

Lemma spec_is_block_free_final blk_addr blk_addr32 blk memidx blk_var f E:
  ⊢ {{{{ ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         final_block_repr memidx blk blk_addr ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    to_e_list (is_block_free blk_var) @ E
    {{{{ w, ⌜w = immV [VAL_int32 (wasm_bool false)]⌝ ∗
            final_block_repr memidx blk blk_addr ∗
            ↪[frame] f }}}}.
Proof.
  iIntros (Φ) "!> (%Hblk_addr & Hblk & %Hvar & %Hmem & Hfr) HΦ".
  destruct blk.
  unfold is_block_free.
  erewrite to_e_list_cat.
  iApply wp_seq.
  iSplitR.
  all:swap 1 2.
  iSplitL "Hblk Hfr".
  - iApply (spec_get_final_state with "[Hblk Hfr]"); iFrame; eauto.
  - iIntros (w) "(%st32 & %Hw & %Hst & Hblk & Hfr)".
    subst w.
    cbn.
    iApply (wp_wand with "[Hfr]").
    + iApply (wp_relop with "[Hfr]"); auto.
      instantiate (1:=λ w, ⌜w = immV [VAL_int32 (wasm_bool false)]⌝%I).
      iModIntro.
      iPureIntro.
      assert (st32 = (Wasm_int.int_of_Z i32m (Z.of_N BLK_FINAL))).
      {
        inversion Hst as [Hbd Hst'].
        rewrite <- (Wasm_int.Int32.repr_unsigned st32).
        cbn in *.
        rewrite <- (Z2N.id (Wasm_int.Int32.unsigned st32)).
        rewrite <- Hst'.
        reflexivity.
        apply Wasm_int.Int32.size_interval_1.
      }
      subst.
      reflexivity.
    + iIntros (w) "(%Hw & Hfr)".
      subst.
      iApply "HΦ".
      iFrame; auto.
  - iIntros "(%st32 & %Htrap & _)".
    congruence.
Qed.

Lemma lt_ssrleq x y : 
  x < y ->
  ssrnat.leq (S x) y.
Proof.
  destruct (@ssrnat.ltP x y); auto.
Qed.

Lemma example E f n32 :
    ⊢ {{{{ 
            ⌜f.(f_locs) !! 0 = Some (VAL_int32 n32)⌝ ∗
            ↪[frame] f
      }}}}
      to_e_list ([BI_get_local 0; BI_get_local 0; BI_relop T_i32 (Relop_i ROI_eq)]) @ E
      {{{{ w, ⌜w = immV [VAL_int32 (wasm_bool true)]⌝ ∗ ↪[frame] f }}}}.
Proof.
  iIntros (Φ) "!> (%Hloc & Hfr) HΦ".
  wp_chomp 1.
  set (Φ' := (λ w, ⌜w = immV [VAL_int32 n32] ⌝ ∗ ↪[frame] f)%I).
  iApply (wp_seq _ _ _ Φ').
  iSplitR. { iIntros "(%Hw & _)" => //. }
  iSplitL "Hfr".
  {
    iApply wp_get_local; auto.
    assumption.
  }
  iIntros (w) "(%Hw & Hfr)".
  subst w.
  wp_chomp 2.
  iApply (wp_wand _ _ _ (λ w, ⌜w = immV [VAL_int32 Wasm_int.Int32.one]⌝ ∗  ↪[frame]f)%I with "[Hfr] [HΦ]"); auto.
  set (Φ'' := (λ w, ⌜w = immV [VAL_int32 n32; VAL_int32 n32] ⌝ ∗ ↪[frame] f)%I).
  iApply (wp_seq _ _ _ Φ'').
  iSplitR. { iIntros "(%Hw & _)" => //. }
  iSplitL "Hfr".
  {
    wp_chomp 1.
    iApply wp_val_app => //.
    iSplitR. { iIntros "!> (%Hw & _)" => //. }
    iApply wp_get_local; eauto.
  }
  iIntros (w) "(-> & Hfr)".
  simpl.
  iApply (wp_relop with "[Hfr]") =>//.
  cbn.
  rewrite Wasm_int.Int32.eq_true.
  auto.
Qed.

Lemma wp_get_locals vars vals E f :
  Forall2 (fun x v => f.(f_locs) !! x = Some v) vars vals ->
  ⊢ {{{{ ↪[frame] f }}}}
    to_e_list (List.map BI_get_local vars) @ E
    {{{{ w, ⌜w = immV vals⌝ ∗ ↪[frame] f }}}}.
Proof.
  induction 1.
  - iIntros (Φ) "!> Hfr HΦ".
    rewrite wp_unfold /wp_pre /=.
    iModIntro.
    iApply "HΦ".
    auto.
  - iIntros (Φ) "!> Hfr HΦ".
    wp_chomp 1.
    set (Φ' := (λ w, ⌜w = immV [y]⌝ ∗ ↪[frame]f)%I).
    iApply (wp_seq _ _ _ Φ').
    iSplitR. { iIntros "(%Hw & _)" => //. }
    iSplitL "Hfr".
    {
      iApply wp_get_local; auto.
      assumption.
    }
    iIntros (w) "(%Hw & Hfr)".
    subst w.
    iApply (wp_wand _ _ _ (λ w, ⌜w = immV (y::l')⌝ ∗ ↪[frame] f)%I with "[Hfr]"); auto.
    iApply wp_val_app; auto.
    iSplitR.
    { iIntros "!> (%Hw & _)" => //. }
    iApply (wp_wand with "[Hfr]").
    iApply (IHForall2 with "[Hfr]"); auto.
    iIntros (w) "(%Hw & Hfr)".
    iFrame.
    subst w; auto.
Qed.

Lemma unsigned_is_N:
  forall z: i32,
  Wasm_int.Int32.unsigned z = Z.of_N (Wasm_int.N_of_uint i32m z).
Proof.
  intros.
  cbn.
  rewrite Z2N.id =>//.
  apply Wasm_int.Int32.unsigned_range.
Qed.

Lemma unsigned_N_repr (z: i32) :
  N_repr (Z.to_N (Wasm_int.Int32.unsigned z)) z.
Proof.
  unfold N_repr.
  rewrite Z2N.id; [|apply Wasm_int.Int32.unsigned_range].
  split.
  - pose proof (Wasm_int.Int32.unsigned_range z).
    lia.
  - reflexivity.
Qed.

Lemma N_repr_inj (z: i32) (a b: N) :
  N_repr a z ->
  N_repr b z ->
  a = b.
Proof.
  unfold N_repr.
  intuition congruence.
Qed.

Lemma iadd_repr:
  forall (x y z: N) x32 y32,
    N_repr x x32 ->
    N_repr y y32 ->
    (Z.of_N z < Wasm_int.Int32.modulus)%Z ->
    (x + y = z)%N ->
    N_repr z (Wasm_int.Int32.iadd x32 y32).
Proof.
  intros ? ? ? ? ? [Hxbdd Hx] [Hybdd Hy] Hzbdd Hsum.
  split.
  - lia.
  - unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
    rewrite !unsigned_is_N.
    unfold Wasm_int.Int32.repr.
    cbn.
    rewrite Wasm_int.Int32.Z_mod_modulus_id.
    rewrite Z2N.id; [|apply Wasm_int.Int32.unsigned_range].
    rewrite Z2N.id; [|apply Wasm_int.Int32.unsigned_range].
    rewrite Z2N.inj_add; try apply Wasm_int.Int32.unsigned_range.
    rewrite !unsigned_is_N.
    rewrite <- Hy.
    rewrite <- Hx.
    now rewrite !N2Z.id.
    rewrite !Z2N.id; try apply Wasm_int.Int32.unsigned_range.
    rewrite !unsigned_is_N.
    lia.
Qed.

Lemma isub_repr:
  forall (x y z: N) x32 y32,
    N_repr x x32 ->
    N_repr y y32 ->
    (0 <= Z.of_N x - Z.of_N y)%Z ->
    (x - y = z)%N ->
    N_repr z (Wasm_int.Int32.isub x32 y32).
Proof.
  intros x y z x32 y32 [Hxbdd Hx] [Hybdd Hy] Hbdd Hsub.
  assert (Hzbdd: (-1 < Z.of_N z < Wasm_int.Int32.modulus)%Z) by lia.
  split; auto.
  unfold Wasm_int.Int32.isub.
  unfold Wasm_int.Int32.sub.
  cbn.
  rewrite Wasm_int.Int32.Z_mod_modulus_id.
  rewrite Z2N.inj_sub.
  rewrite !unsigned_is_N.
  rewrite <- Hx.
  rewrite <- Hy.
  rewrite !N2Z.id.
  auto.
  apply Wasm_int.Int32.unsigned_range.
  rewrite !unsigned_is_N.
  rewrite <- Hx, <- Hy.
  lia.
Qed.

Lemma ilt_repr_true:
  forall x y x32 y32,
    N_repr x x32 ->
    N_repr y y32 ->
    (x < y)%N ->
    Wasm_int.Int32.ltu x32 y32 = true.
Proof.
Admitted.

(* "Effective" or functional versions of NoDup and ∉ *)
Fixpoint NotInEff {A} (x: A) (l: list A) : Prop :=
  match l with
  | [] => True
  | y :: l => x <> y /\ NotInEff x l
  end.

Lemma equiv_NotInEff {A} (x: A) (l: list A) :
  x ∉ l <-> NotInEff x l.
Proof.
  induction l.
  - simpl.
    cut (x ∉ []); [tauto|].
    intros H.
    inversion H.
  - split; intros H.
    + cbn.
      split.
      * intros Heq.
        subst x.
        apply H.
        by constructor.
      * apply IHl.
        intros Hin.
        apply H.
        by constructor.
    + intros Hin.
      inversion Hin; clear Hin; subst.
      * cbn in H.
        tauto.
      * cbn in H.
        tauto.
Qed.

Fixpoint NoDupEff {A} (l: list A) : Prop := 
  match l with
  | [] => True
  | x :: l => NotInEff x l /\ NoDupEff l
  end.

Lemma equiv_NoDupEff {A} (l: list A) :
  NoDup l <-> NoDupEff l.
Proof.
  induction l; cbn.
  - apply NoDup_nil.
  - split; intros H.
    + inversion H; clear H; subst.
      apply equiv_NotInEff in H2.
      tauto.
    + destruct H as [Hnotin Hnodup].
      apply equiv_NotInEff in Hnotin.
      constructor; tauto.
Qed.

Lemma set_nth_length_eq {T} (x: T) (l: seq.seq T) (i: nat) (d: T) :
    i < seq.size l ->
    length (set_nth x l i d) = length l.
Proof.
  rewrite length_is_size.
  intros.
  by rewrite size_set_nth maxn_nat_max max_r.
Qed.

Lemma set_nth_gt (i: nat) :
  ∀ {A : Type} (l : seq.seq A) (x0 : A) (x : A),
    i >= length l ->
    set_nth x0 l i x = l ++ ncons (i - length l) x0 [x].
Proof.
  induction i; intros.
  - destruct l.
    + reflexivity.
    + inversion H.
  - destruct l; simpl.
    + reflexivity.
    + simpl in *.
      assert (Hi: i >= length l) by lia.
      rewrite IHi; auto.
Qed.

Lemma set_nth_read_neq:
  ∀ {A : Type} (l : seq.seq A) (i j : nat) (x y : A),
    i <> j ->
    l !! j = Some y ->
    set_nth x l i x !! j = Some y.
Proof.
  intros.
  destruct (Nat.lt_dec i (seq.size l)).
  - rewrite update_list_at_is_set_nth.
    rewrite update_ne; auto.
    auto using lt_ssrleq.
  - rewrite set_nth_gt.
    + rewrite lookup_app_l; auto.
      apply lookup_lt_is_Some_1; auto.
    + rewrite length_is_size.
      lia.
Qed.

(* SPECS: block pinching *)
Lemma spec_pinch_block E f memidx old_sz blk_addr blk_addr32 reqd_sz reqd_sz32
  old_sz_var old_sz0 reqd_sz_var new_blk_var new_blk0 final_blk_var :
  ⊢
  {{{{
         final_block_repr memidx (FinalBlk old_sz) blk_addr ∗
         ⌜(reqd_sz + blk_hdr_sz < old_sz)%N⌝ ∗
         ⌜N_repr blk_addr blk_addr32⌝ ∗
         ⌜N_repr reqd_sz reqd_sz32⌝ ∗
         ⌜NoDupEff [final_blk_var; reqd_sz_var; old_sz_var; new_blk_var]⌝ ∗
         ⌜f.(f_locs) !! final_blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_locs) !! reqd_sz_var = Some (VAL_int32 reqd_sz32)⌝ ∗
         ⌜f.(f_locs) !! old_sz_var = Some old_sz0⌝ ∗
         ⌜f.(f_locs) !! new_blk_var = Some new_blk0 ⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f
  }}}}
  to_e_list (pinch_block final_blk_var reqd_sz_var old_sz_var new_blk_var) @ E
  {{{{ w, ⌜w = immV [] ⌝ ∗
         block_repr memidx (FreeBlk reqd_sz) blk_addr (blk_addr + reqd_sz + blk_hdr_sz) ∗
         final_block_repr memidx (FinalBlk (old_sz - reqd_sz - blk_hdr_sz)) (blk_addr + reqd_sz + blk_hdr_sz) ∗
         ∃ new_addr32 old_sz32,
           ⌜N_repr (blk_addr + reqd_sz + blk_hdr_sz) new_addr32⌝ ∗
           ∃ f', ↪[frame] f' ∗
                 ⌜f'.(f_inst) = f.(f_inst)⌝ ∗
                 ⌜f'.(f_locs) = set_nth (VAL_int32 new_addr32)
                                  (set_nth (VAL_int32 old_sz32) (f_locs f) 
                                     old_sz_var (VAL_int32 old_sz32))
                                  new_blk_var (VAL_int32 new_addr32)⌝
  }}}}.
Proof.
  iIntros (Φ) "!> (Hblk & %Hspace & %Haddr32 & %Hsz32 & %Hdisj & %Hblk_var & %Hsz_var & %Hold_var & %Hnew_var & %Hmem & Hfr) HΦ".
  assert (final_blk_var < length f.(f_locs)) by auto using lookup_lt_is_Some_1.
  assert (reqd_sz_var < length f.(f_locs)) by auto using lookup_lt_is_Some_1.
  assert (old_sz_var < length f.(f_locs)) by auto using lookup_lt_is_Some_1.
  assert (new_blk_var < length f.(f_locs)) by auto using lookup_lt_is_Some_1.
  iPoseProof (final_block_inbounds _ _ _ with "Hblk") as "(%Hbdd & Hblk)".
  cbn in Hbdd.
  unfold pinch_block.
  erewrite !to_e_list_cat.
  set (Φ1 := λ w, (⌜w = immV []⌝ ∗
                  ∃ old32, 
                    ⌜N_repr old_sz old32 ⌝ ∗
                      final_block_repr memidx (FinalBlk old_sz) blk_addr ∗
                    ↪[frame] {| f_locs := set_nth (VAL_int32 old32) (f_locs f) old_sz_var (VAL_int32 old32);
                               f_inst := f_inst f |})%I).
  iApply (wp_seq _ _ _ Φ1).
  iSplitL "".
  { iIntros "(%Htrap & _)"; congruence. }
  iSplitL "Hfr Hblk".
  {
    set (Φ1' := λ w, (∃ old32, 
                    ⌜w = immV [VAL_int32 old32]⌝ ∗
                    ⌜N_repr old_sz old32 ⌝ ∗
                      final_block_repr memidx (FinalBlk old_sz) blk_addr ∗
                    ↪[frame] f)%I).
    iApply (wp_seq _ _ _ Φ1').
    iSplitR. { iIntros "(%tot & %Htrap & _)"; congruence. }
    iSplitL.
    + iApply (spec_get_final_size with "[Hblk Hfr]"); iFrame; eauto.
      unfold Φ1'.
      iIntros (v) "(%sz32 & %Hrep & -> & Hblk)".
      iExists sz32; auto.
    + iIntros (w) "(%sz32 & -> & %Hrep & Hblk & Hfr)".
      simpl app.
      iApply (wp_wand with "[Hfr]").
      {
        iApply wp_set_local; try iFrame; eauto.
        instantiate (1:= λ w, (⌜w = immV []⌝ ∗ ⌜N_repr old_sz sz32 ⌝)%I); auto.
      }
      iIntros (w) "(%Hw & H)".
      iFrame; auto.
  }
  iIntros (w) "(%Hw & (%old_sz32 & %Hold_sz & Hblk & Hfr))".
  clear Φ1.
  subst w.
  rewrite app_nil_l.
  set (new_addr := (blk_addr + reqd_sz + blk_hdr_sz)%N).
  set (f2 := {| f_locs := set_nth (VAL_int32 old_sz32) (f_locs f) old_sz_var (VAL_int32 old_sz32);
                f_inst := f_inst f |}).
  wp_chomp 2.
  set (Φ2 := λ w, (⌜w = immV [VAL_int32 blk_addr32; VAL_int32 reqd_sz32]⌝ ∗ ↪[frame] f2)%I).
  iApply (wp_seq _ _ _ Φ2).
  iSplitR. { iIntros "(%Hw & _)"; congruence. }
  iSplitL "Hfr".
  {
    iApply ((@wp_get_locals [final_blk_var; reqd_sz_var]) with "[Hfr]"); auto.
    repeat constructor.
    - cbn.
      rewrite update_list_at_is_set_nth; [|auto using lt_ssrleq].
      rewrite update_ne; auto.
      cbn in Hdisj.
      intuition.
    - cbn.
      rewrite update_list_at_is_set_nth; [|auto using lt_ssrleq].
      rewrite update_ne; auto.
      cbn in Hdisj.
      intuition.
  }
  iIntros (w) "(-> & Hfr)".
  set (Φ3 := λ w, (∃ tot32, ⌜w = immV [VAL_int32 blk_addr32; VAL_int32 tot32]⌝ ∗ ⌜N_repr (reqd_sz + blk_hdr_sz) tot32 ⌝ ∗ ↪[frame] f2)%I).
  wp_chomp 4.
  iApply (wp_seq _ _ _ Φ3).
  iSplitR. { iIntros "(%v & (%Hw & _))"; congruence. }
  iSplitL "Hfr".
  {
    wp_chomp 1.
    iApply wp_val_app =>//.
    iSplit. { iIntros "!> (%v & (%Hw & _))"; congruence. }
    iApply (spec_add_hdr_sz with "[Hfr]").
    + iFrame.
      iSplit; auto.
      iPureIntro. 
      lia.
    + iIntros (w) "(%out32 & (-> & %Hout & Hfr))".
      cbn.
      iExists _; iFrame; iSplit; auto.
  }
  iIntros (w) "(%out32 & (-> & %Hout & Hfr))".
  wp_chomp 3.
  set (Φ4 := λ w, ((∃ new_addr32, ⌜w = immV [VAL_int32 new_addr32]⌝ ∗ ⌜N_repr new_addr new_addr32 ⌝) ∗ ↪[frame]f2)%I).
  iApply (wp_seq _ _ _ Φ4).
  iSplitR. { iIntros "((%v & (%Hw & _)) & _)". congruence. }
  iSplitL "Hfr".
  {
    iApply (wp_binop with "[Hfr]"); auto.
    iModIntro.
    iExists _.
    cbn.
    iSplit; auto.
    iPureIntro.
    eapply iadd_repr; eauto || lia.
  }
  iIntros (w) "((%new_addr32 & %Hw & %Hnew_addr32) & Hfr)".
  subst w.
  clear Φ2.
  wp_chomp 2.
  set (f3 := {| f_locs := set_nth (VAL_int32 new_addr32) (f_locs f2) new_blk_var (VAL_int32 new_addr32);
                f_inst := f_inst f2 |}).
  set (Φ5 := λ w, (⌜w = immV []⌝ ∗ ↪[frame] f3)%I).
  iApply (wp_seq _ _ _ Φ5 _).
  iSplitR. { iIntros "(%Hw & _)"; congruence. }
  iSplitL "Hfr".
  {
    iApply wp_set_local; auto.
    eapply lookup_lt_is_Some_1.
    cbn.
    rewrite update_list_at_is_set_nth; [|auto using lt_ssrleq].
    rewrite update_ne; auto.
    cbn in Hdisj; intuition.
  }
  iIntros (w) "(%Hw & Hfr)".
  subst w.
  rewrite app_nil_l.
  wp_chomp 2.
  set (Φ6 := λ w, (⌜w = immV [VAL_int32 blk_addr32; VAL_int32 reqd_sz32]⌝ ∗ ↪[frame] f3)%I).
  iApply (wp_seq _ _ _ Φ6).
  iSplitR. { by iIntros "(%Hw & _)". }
  iSplitL "Hfr".
  {
    iApply (@wp_get_locals [final_blk_var; reqd_sz_var] with "[Hfr]"); [|eauto|].
    - constructor.
      + unfold f3.
        cbn.
        cbn in Hdisj.
        rewrite <- fmap_insert_set_nth; [| by rewrite set_nth_length_eq].
        rewrite list_lookup_insert_ne; [| intuition].
        rewrite <- fmap_insert_set_nth; [| auto ].
        rewrite list_lookup_insert_ne; [| intuition].
        eauto.
      + constructor; [| by constructor].
        cbn.
        cbn in Hdisj.
        rewrite <- fmap_insert_set_nth; [| by rewrite set_nth_length_eq].
        rewrite list_lookup_insert_ne; [| intuition].
        rewrite <- fmap_insert_set_nth; [| auto ].
        rewrite list_lookup_insert_ne; [| intuition].
        eauto.
    - iIntros (w) "(-> & Hfr)".
      iFrame; auto.
  }
  iIntros (w) "(%Hw & Hfr)". subst w.
  wp_chomp 3.
  set (Φ7 := λ w, (⌜w = immV []⌝ ∗ ↪[frame] f3 ∗ final_block_repr memidx (FinalBlk reqd_sz) blk_addr ∗
                    own_vec memidx (blk_addr + data_off + reqd_sz) (blk_hdr_sz + (old_sz - reqd_sz - blk_hdr_sz)))%I).
  iApply (wp_seq _ _ _ Φ7).
  iSplitR. { iIntros "(%Hw & _)"; congruence. }
  iSplitL "Hfr Hblk".
  {
    iDestruct "Hblk" as "(%Hbds & Hst & Hsz & Hnext & Hdata)".
    assert (Hszsplit: (old_sz = reqd_sz + (blk_hdr_sz + (old_sz - reqd_sz - blk_hdr_sz)))%N) by lia.
    rewrite Hszsplit.
    setoid_rewrite own_vec_split.
    iDestruct "Hdata" as "(Hdata & Hrest)".
    iApply (spec_set_size_final with "[Hfr Hsz Hdata]"); iFrame; auto.
    iIntros (w) "(-> & Hsz & Hdata & Hfr)".
    iFrame; auto.
    iSplit; auto.
    iPureIntro.
    lia.
  }
  (* mark_free *)
  iIntros (w) "(-> & Hfr & Hblk & Hrest)".
  rewrite app_nil_l.
  wp_chomp 3.
  iApply wp_seq.
  iSplitR; last first.
  iSplitL "Hfr Hblk".
  {
    iApply (spec_mark_free_final with "[Hfr Hblk]"); iFrame => //.
    - iSplit =>//.
      iSplit; iPureIntro; auto.
      cbn in Hdisj.
      apply set_nth_read_neq; [by intuition|].
      apply set_nth_read_neq; intuition.
    - auto.
  }
  (* get locals for set_next *)
  iIntros (w) "(-> & %Hfinal & Hblk & Hfr)".
  wp_chomp 2.
  iApply wp_seq.
  iSplitR; last first.
  iSplitL "Hfr".
  {
    iApply (@wp_get_locals [final_blk_var; new_blk_var] with "[Hfr]"); try iFrame; auto.
    constructor.
    cbn in Hdisj.
    apply set_nth_read_neq; [intuition|].
    apply set_nth_read_neq; [intuition|eauto].
    constructor; [|constructor].
    apply set_nth_read.
  }
  (* set_next *)
  iIntros (w) "(-> & Hfr)".
  wp_chomp 3.
  iApply wp_seq. iSplitR; last first.
  iSplitL "Hfr Hblk".
  {
    iApply (spec_set_next with "[Hfr Hblk]"); iFrame; auto.
  }
  (* subdivide remaining space into header fields + data *)
  iPoseProof (own_vec_split with "Hrest") as "(Hhdr & Hdata')".
  iAssert ((_ ∗ _) ∗ _)%I with "[Hhdr]" as "((Hst & Hsz) & Hnext)".
  { 
    replace blk_hdr_sz with (4 + 4 + 4)%N.
    rewrite !own_vec_split.
    iFrame.
    reflexivity.
  }
  (* mark_final *)
  iIntros (w) "(-> & Hblk & Hfr)".
  wp_chomp 3.
  iApply wp_seq. iSplitR; last first. iSplitL "Hfr Hst".
  {
    iApply (spec_mark_final with "[Hfr Hst]").
    - unfold state_off.
      rewrite N.add_0_r.
      iFrame.
      replace (_ + _ + reqd_sz)%N with new_addr
        by (unfold data_off, new_addr; lia).
      iSplit; auto.
      iSplit; iPureIntro; auto.
      by rewrite set_nth_read.
    - auto.
  }
  (* get_locals for computing block size *)
  iIntros (w) "(-> & Hst & Hfr)".
  wp_chomp 3.
  iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
  {
    iApply (@wp_get_locals [new_blk_var; old_sz_var; reqd_sz_var] with "[Hfr]"); try iFrame; auto.
    cbn in Hdisj.
    repeat constructor.
    - by rewrite set_nth_read.
    - cbn.
      apply set_nth_read_neq; [intuition|].
      by rewrite set_nth_read.
    - cbn.
      apply set_nth_read_neq; [intuition|].
      apply set_nth_read_neq; intuition eauto.
  }
  (* subtract reqd - old - hdr to compute remaining size *)
  iIntros (w) "(-> & Hfr)".
  wp_chomp 5.
  iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
  {
    wp_chomp 2.
    iApply wp_val_app =>//.
    iSplitR; last first.
    iApply (wp_wand with "[Hfr]").
    iApply (wp_binop with "[Hfr]"); eauto.
    instantiate (1:= λ w, ⌜w= (immV [VAL_int32 (Wasm_int.int_add Wasm_int.Int32.Tmixin reqd_sz32 (Wasm_int.int_of_Z i32m (Z.of_N blk_hdr_sz)))])⌝%I).
    auto.
    iIntros (w).
    instantiate (1:= λ w, (⌜w= (immV [VAL_int32 new_addr32; VAL_int32 old_sz32; VAL_int32 (Wasm_int.int_add Wasm_int.Int32.Tmixin reqd_sz32 (Wasm_int.int_of_Z i32m (Z.of_N blk_hdr_sz)))])⌝ ∗ ↪[frame] f3)%I).
    iIntros "(-> & Hfr)".
    iFrame; auto.
    iIntros "!> (%Hw & _)". congruence.
  }
  iIntros (w) "(-> & Hfr)".
  wp_chomp 4.
  iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
  {
    wp_chomp 1.
    iApply wp_val_app =>//.
    iSplitR; last first.
    iApply (wp_wand with "[Hfr]").
    iApply (wp_binop with "[Hfr]"); eauto.
    instantiate (1:= λ w, ⌜w= (immV [VAL_int32
            (Wasm_int.int_sub Wasm_int.Int32.Tmixin old_sz32
               (Wasm_int.Int32.iadd reqd_sz32 (Wasm_int.Int32.repr 12)))])⌝%I).
    auto.
    iIntros (w).
    instantiate (1:= λ w, (⌜w= (immV [VAL_int32 new_addr32; VAL_int32
        (Wasm_int.int_sub Wasm_int.Int32.Tmixin old_sz32 (Wasm_int.Int32.iadd reqd_sz32 (Wasm_int.Int32.repr 12)))])⌝ ∗ ↪[frame] f3)%I).
    iIntros "(-> & Hfr)".
    iFrame; auto.
    iIntros "!> (%Hw & _)". congruence.
  }
  (* set_size *)
  iIntros (w) "(-> & Hfr)".
  wp_chomp 3.
  iApply wp_seq. iSplitR; last first. iSplitL "Hsz Hdata' Hfr".
  {
    iApply (spec_set_size_final_setup with "[$Hsz $Hdata' $Hfr]").
    unfold data_off.
    iPureIntro.
    split; [| split].
    - replace (blk_addr + blk_hdr_sz + reqd_sz)%N with new_addr by lia.
      auto.
    - replace (old_sz - reqd_sz - blk_hdr_sz)%N with (old_sz - (reqd_sz + blk_hdr_sz))%N by lia.
      eapply isub_repr; eauto.
      eapply iadd_repr; eauto.
      constructor; [|reflexivity].
      all:lia.
    - auto.
    - auto.
  }
  (* get_local for set_next *)
  iIntros (w) "(-> & (Hsz & Hdata & Hfr))".
  wp_chomp 1.
  iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
  {
    iApply (wp_get_local with "[] [$Hfr //]").
    - apply set_nth_read.
    - instantiate (1 := (λ w, ⌜w = immV [VAL_int32 new_addr32]⌝)%I).
      auto.
  }
  (* set_next *)
  iIntros (w) "(-> & Hfr)".
  iApply (spec_set_next_basic with "[$Hfr $Hnext]").
  {
    replace (blk_addr + data_off + reqd_sz)%N with new_addr
      by (unfold data_off; lia).
    instantiate (1:= 0%N).
    auto.
  }
  iIntros (w) "(-> & Hnext & Hfr)".
  unfold final_block_repr.
  iApply ("HΦ" with "[$Hblk Hdata Hsz Hst Hnext Hfr]").
  {
    unfold new_addr.
    unfold data_off.
    replace (blk_addr + blk_hdr_sz + reqd_sz)%N with (blk_addr + reqd_sz + blk_hdr_sz)%N by lia.
    iFrame.
    iSplit; auto.
    iSplit.
    - unfold block_inbounds.
      unfold f3, f2.
      cbn.
      iPureIntro.
      lia.
    - iExists _, _; auto.
  }
  all:iIntros "(%Hw & _)"; congruence.
Qed.

(* SPECS: block creation *)
(*TODO
*)
Lemma spec_new_block_space memidx final_blk_var final_sz final_blk_addr final_blk_addr32 
  reqd_sz reqd_sz_var reqd_sz32 old_sz_var old_sz0 new_blk_var new_blk0 actual_size_var actual_sz0 f E  :
  ⊢ {{{{
      final_block_repr memidx (FinalBlk final_sz) final_blk_addr ∗
      ↪[frame] f ∗
      ⌜(reqd_sz + blk_hdr_sz < final_sz)%N ⌝ ∗
      ⌜N_repr final_blk_addr final_blk_addr32⌝ ∗
      ⌜N_repr reqd_sz reqd_sz32⌝ ∗
      ⌜NoDupEff [final_blk_var; reqd_sz_var; old_sz_var; new_blk_var; actual_size_var]⌝ ∗
      ⌜f.(f_locs) !! final_blk_var = Some (VAL_int32 final_blk_addr32)⌝ ∗
      ⌜f.(f_locs) !! reqd_sz_var = Some (VAL_int32 reqd_sz32)⌝ ∗
      ⌜f.(f_locs) !! old_sz_var = Some old_sz0⌝ ∗
      ⌜f.(f_locs) !! new_blk_var = Some new_blk0 ⌝ ∗
      ⌜f.(f_locs) !! actual_size_var = Some actual_sz0 ⌝ ∗
      ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝
  }}}}
  to_e_list (new_block final_blk_var reqd_sz_var old_sz_var new_blk_var actual_size_var) @ E
  {{{{ w, ⌜w = immV [] ⌝ ∗
         block_repr memidx (FreeBlk reqd_sz) final_blk_addr (final_blk_addr + reqd_sz + blk_hdr_sz) ∗
         final_block_repr memidx (FinalBlk (final_sz - reqd_sz - blk_hdr_sz)) (final_blk_addr + reqd_sz + blk_hdr_sz) ∗
         ∃ f', ↪[frame] f'
  }}}}.
Proof.
  iIntros (Φ) "!> (Hblk & Hfr & %Hspace & %Hfinal_blk_rep & %Hreqd_sz_rep & %Hfinal_blk & %Hreqd_sz & %Hdisj & %Hold_sz & %Hnew_blk & %Hactual_sz & %Hmem) HΦ".
  unfold new_block.
  iPoseProof (final_block_inbounds with "Hblk") as "(%Hfbdd & Hblk)".
  cbn in Hfbdd.
  wp_chomp 1.
  iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
  {
    iApply (wp_get_local with "[] [$Hfr //]"); eauto.
    by instantiate (1 := λ w, ⌜w = immV [VAL_int32 reqd_sz32]⌝%I).
  }
  iIntros (w) "(-> & Hfr)".
  wp_chomp 3.
  iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
  {
    iApply (spec_add_hdr_sz with "[$Hfr]"); eauto.
    iSplit; auto.
    iPureIntro.
    lia.
  }
  iIntros (w) "(%out32 & -> & %Houtrep & Hfr)".
  wp_chomp 3.
  iApply wp_seq. iSplitR; last first. iSplitL "Hfr Hblk".
  wp_chomp 1.
  iApply wp_val_app; eauto.
  iSplitR; last first.
  {
    iApply (wp_wand with "[Hfr Hblk]").
    iApply (spec_get_final_size _ _ _ _ _ _ final_blk_var with "[$Hblk $Hfr //]").
    eauto.
    iIntros (w) "(%sz32 & %Hszrep & -> & Hblk & Hfr)".
    instantiate (1 := λ w, (∃ sz32 : i32, ⌜N_repr final_sz sz32⌝ ∗ ⌜w = immV [VAL_int32 out32; VAL_int32 sz32]⌝ ∗ final_block_repr memidx (FinalBlk final_sz) final_blk_addr ∗  ↪[frame]f)%I).
    cbn.
    iExists _; iFrame; auto.
  }
  all:swap 1 2.
  iIntros (w) "(%sz32 & %Hszrep & -> & Hblk & Hfr)".
  wp_chomp 3.
  iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
  {
    iApply (wp_relop with "[$Hfr]"); auto.
    instantiate (1:= λ w, ⌜w = immV [VAL_int32 (wasm_bool true)]⌝%I).
    iIntros "!> !%".
    do 4 f_equal.
    eauto using ilt_repr_true.
  }
  iIntros (w) "(-> & Hfr)".
  iApply (wp_if_true with "[$Hfr]"); auto.
  {
    iIntros "!> Hfr".
    wp_chomp 0.
    iApply (wp_block with "[$Hfr]"); eauto.
    Locate "WP".
    Search wp_wasm_ctx wp.
    iIntros "!> Hfr".
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_emp; last first.
    cbn.
    iApply wp_ctx_bind; [by cbn |].
    assert (NoDupEff [final_blk_var; reqd_sz_var; old_sz_var; new_blk_var]).
    {
      cbn.
      cbn in Hfinal_blk.
      lia.
    }
    iApply (spec_pinch_block with "[$Hblk $Hfr //]").
    iIntros (w) "(-> & Hblk & Hfblk & (%new32 & %old32 & %Hnewrep & (%f' & Hfr & %Hfinst & %Hflocs)))".
    iIntros (x) "%Hfill".
    move /lfilledP in Hfill.
    inversion Hfill; subst.
    inversion H9; subst.
    cbn.
    (* ? *)
    admit.
  }
  all:cbn.
  all:try iIntros "!>".
  all:try (iIntros "(%Hw & _)"; congruence).
  all:try (iIntros "(%out & %Hw & _)"; congruence).
  all:try (iIntros "(%sz & H & (%Hw & _))"; congruence).
Admitted.

Lemma spec_new_block_no_space memidx final_blk_var final_sz final_blk_addr final_blk_addr32 
  reqd_sz reqd_sz_var reqd_sz32 old_sz_var old_sz0 new_blk_var new_blk0 actual_size_var actual_sz0 f E  :
  ⊢ {{{{
      final_block_repr memidx (FinalBlk final_sz) final_blk_addr ∗
      ⌜(reqd_sz + blk_hdr_sz >= final_sz)%N ⌝ ∗
      ⌜N_repr final_blk_addr final_blk_addr32⌝ ∗
      ⌜N_repr reqd_sz reqd_sz32⌝ ∗
      ⌜f.(f_locs) !! final_blk_var = Some (VAL_int32 final_blk_addr32)⌝ ∗
      ⌜f.(f_locs) !! reqd_sz_var = Some (VAL_int32 reqd_sz32)⌝ ∗
      ⌜f.(f_locs) !! old_sz_var = Some old_sz0⌝ ∗
      ⌜f.(f_locs) !! new_blk_var = Some new_blk0 ⌝ ∗
      ⌜f.(f_locs) !! actual_size_var = Some actual_sz0 ⌝
  }}}}
  to_e_list (new_block final_blk_var reqd_sz_var old_sz_var new_blk_var actual_size_var) @ E
  {{{{ w, ⌜w = immV [] ⌝ (* TODO good postcondition for this case *)
  }}}}.
Proof.
Abort.
  
(* This needs to have a freelist_repr postcondition *)
Lemma spec_new_block memidx final_blk_var final_sz final_blk_addr final_blk_addr32 
  reqd_sz reqd_sz_var reqd_sz32 old_sz_var old_sz0 new_blk_var new_blk0 actual_size_var actual_sz0 f E  :
  ⊢ {{{{
      final_block_repr memidx (FinalBlk final_sz) final_blk_addr ∗
      ⌜(reqd_sz + blk_hdr_sz >= final_sz)%N ⌝ ∗
      ⌜N_repr final_blk_addr final_blk_addr32⌝ ∗
      ⌜N_repr reqd_sz reqd_sz32⌝ ∗
      ⌜f.(f_locs) !! final_blk_var = Some (VAL_int32 final_blk_addr32)⌝ ∗
      ⌜f.(f_locs) !! reqd_sz_var = Some (VAL_int32 reqd_sz32)⌝ ∗
      ⌜f.(f_locs) !! old_sz_var = Some old_sz0⌝ ∗
      ⌜f.(f_locs) !! new_blk_var = Some new_blk0 ⌝ ∗
      ⌜f.(f_locs) !! actual_size_var = Some actual_sz0 ⌝
  }}}}
  to_e_list (new_block final_blk_var reqd_sz_var old_sz_var new_blk_var actual_size_var) @ E
  {{{{ w, ⌜w = immV [] ⌝ (* TODO good postcondition for both cases *)
  }}}}.
Proof.
Abort.


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
      
