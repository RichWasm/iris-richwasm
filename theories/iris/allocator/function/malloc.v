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
  BI_load T_i32 None state_off 0%N ::
  nil.

Definition get_next blk :=
  BI_get_local blk ::
  BI_load T_i32 None next_off 0%N ::
  nil.

Definition get_data blk :=
  BI_get_local blk ::
  BI_load T_i32 None data_off 0%N ::
  nil.

Definition set_next :=
  [BI_store T_i32 None next_off 0%N].

(* this is the size of the data segment of the block *)
Definition get_size blk :=
  BI_get_local blk ::
  BI_load T_i32 None size_off 0%N ::
  nil.
  
Definition set_size :=
  [BI_store T_i32 None size_off 0%N].

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

Definition nat_repr (n: nat) (m: i32) : Prop :=
  Z.of_nat n = Wasm_int.Int32.unsigned m.

Definition N_repr (n: N) (m: i32) : Prop :=
  n = Wasm_int.N_of_uint i32m m.

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

Definition block_repr (memidx: N) (blk: block) (base_addr next_addr: N) : iProp Σ :=
  match blk with
  | UsedBlk blk_used_size blk_leftover_size =>
      state_repr memidx Used base_addr ∗
      size_repr memidx (blk_used_size + blk_leftover_size)%N base_addr ∗
      next_repr memidx next_addr base_addr ∗
      own_vec memidx (base_addr + data_off + blk_used_size) blk_leftover_size
  | FreeBlk blk_size =>
      state_repr memidx Free base_addr ∗
      size_repr memidx blk_size base_addr ∗
      next_repr memidx next_addr base_addr ∗
      own_vec memidx (base_addr + data_off) blk_size
  end.

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
Lemma spec_get_state E memidx blk blk_addr next_addr blk_addr32 blk_var f st32 :
  ⊢ {{{{ block_repr memidx blk blk_addr next_addr ∗
         ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    (to_e_list (get_state blk_var)) @ E
    {{{{ v, ⌜v = (immV [VAL_int32 st32])⌝ ∗
            ⌜N_repr (state_to_N (block_flag blk)) st32 ⌝ ∗
            block_repr memidx blk blk_addr next_addr ∗
            ↪[frame] f }}}}.
Proof.
Admitted.

Lemma spec_get_final_state E memidx blk blk_addr blk_addr32 blk_var f st32 :
  ⊢ {{{{ final_block_repr memidx blk blk_addr ∗
         ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    (to_e_list (get_state blk_var)) @ E
    {{{{ v, ⌜v = (immV [VAL_int32 st32])⌝ ∗
            ⌜N_repr (state_to_N (final_block_flag blk)) st32 ⌝ ∗
            final_block_repr memidx blk blk_addr ∗
            ↪[frame] f }}}}.
Proof.
Admitted.

Lemma spec_get_next E memidx blk blk_addr next_addr blk_addr32 next_addr32 f blk_var :
  ⊢ {{{{ block_repr memidx blk blk_addr next_addr ∗
         ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         ⌜N_repr next_addr next_addr32 ⌝ ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    (to_e_list (get_next blk_var)) @ E
    {{{{ v, ⌜v = (immV [VAL_int32 next_addr32])⌝ ∗
            block_repr memidx blk blk_addr next_addr ∗
            ↪[frame] f }}}}.
Proof.
Admitted.

Lemma spec_get_final_next E memidx blk blk_addr blk_addr32 f blk_var :
  ⊢ {{{{ final_block_repr memidx blk blk_addr ∗
         ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    (to_e_list (get_next blk_var)) @ E
    {{{{ v, ⌜v = (immV [value_of_uint 0])⌝ ∗
            final_block_repr memidx blk blk_addr ∗
            ↪[frame] f }}}}.
Proof.
Admitted.

Lemma spec_get_data E memidx blk blk_addr next_addr blk_addr32 f blk_var data_addr32 : 
  ⊢ {{{{ block_repr memidx blk blk_addr next_addr ∗
         ⌜N_repr blk_addr blk_addr32⌝ ∗
         ⌜N_repr (blk_addr + data_off) data_addr32⌝ ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    (to_e_list (get_next blk_var)) @ E
    {{{{ v, ⌜v = (immV [VAL_int32 data_addr32])⌝ ∗
            block_repr memidx blk blk_addr next_addr ∗
            ↪[frame] f }}}}.
Proof.
Admitted.

Lemma spec_get_size E memidx blk blk_addr next_addr blk_addr32 f blk_var sz32 : 
  ⊢ {{{{ block_repr memidx blk blk_addr next_addr ∗
         ⌜N_repr blk_addr blk_addr32⌝ ∗
         ⌜N_repr (block_size blk) sz32⌝ ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    (to_e_list (get_next blk_var)) @ E
    {{{{ v, ⌜v = (immV [VAL_int32 sz32])⌝ ∗
            block_repr memidx blk blk_addr next_addr ∗
            ↪[frame] f }}}}.
Proof.
Admitted.

(* SPECS: block setters *)
(*TODO
Lemma spec_set_next
Lemma spec_set_size
Lemma spec_add_hdr_sz
Lemma spec_get_total_size
Lemma spec_mark_free <--- see below
Lemma spec_mark_used <--- see below
Lemma spec_mark_final
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
  iIntros "!>" (Φ) "(Hblk & Hu & %Hsz & %Hblkvar & %Hmem & %Hblk_addr_rep & Hfr) HΦ".
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
  iDestruct "Hblk" as "(Hstate & Hsize & Hnext & Hvec)".
  iSimpl.
  iDestruct "Hstate" as (st32) "(%Hst32 & Hstfield)".
  iApply (wp_wand with "[Hstfield Hfr]").
  instantiate (1 := λ w, ((⌜w = immV [] ⌝ ∗ 
                        N.of_nat (N.to_nat memidx) ↦[wms][blk_addr + state_off]bits (value_of_uint BLK_FREE)) ∗
                        ↪[frame]f)%I).
  - unfold state_off.
    rewrite Hblkvar.
    iApply wp_store;
      eauto;
      try rewrite N2Nat.id;
      [| iFrame ];
      auto.
  - iIntros (w) "((%Hw & Hstfield) & Hfr)".
    subst w.
    iApply "HΦ".
    unfold block_repr, state_repr.
    rewrite -Hsz.
    rewrite N2Nat.id.
    iFrame; auto.
    repeat iSplit; auto.
    rewrite Hsz.
    iApply own_vec_split.
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
  iIntros "!>" (Φ) "(Hblk & %Hsz & %Hblkvar & %Hmem & %Hblk_addr_rep & Hfr) HΦ".
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
  iDestruct "Hblk" as "(Hstate & Hsize & Hnext & Hvec)".
  iSimpl.
  iDestruct "Hstate" as (st32) "(%Hst32 & Hstfield)".
  iApply (wp_wand with "[Hstfield Hfr]").
  instantiate (1 := λ w, ((⌜w = immV [] ⌝ ∗ 
                        N.of_nat (N.to_nat memidx) ↦[wms][blk_addr + state_off]bits (value_of_uint BLK_USED)) ∗
                        ↪[frame]f)%I).
  - unfold state_off.
    rewrite Hblkvar.
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
      
