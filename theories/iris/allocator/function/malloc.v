From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From Wasm.iris.logrel Require Export iris_fundamental.
From Wasm.iris.rules Require Export proofmode.
From RWasm.iris.allocator Require Export allocator_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Section malloc.


 Context `{!wasmG Σ}. 

Section code.
  
(*
enum state_t ::= FREE | USED | STOP

struct block {
  state_t   state;
  // rest of this is only present if state != STOP
  i32       size; // must be nonzero
  i32       next;
  i32[size] data;
}
[ state ][ size ][ next ] .....  [ state ][ size ][ next ] ...

*)
  
Definition BLK_FREE : N := 0.
Definition BLK_USED : N := 1.
Definition BLK_STOP : N := 2.

(* Given a pointer to a block in the free list, return the block's state marker. *)
Definition get_block_state :=
  [
    BI_load T_i32 None 0%N 0%N
  ].

Definition get_block_stop := 
  get_block_state ++
  [u32const BLK_STOP;
   BI_relop T_i32 (Relop_i ROI_eq)].

Definition get_block_free := 
  get_block_state ++
  [u32const BLK_FREE;
   BI_relop T_i32 (Relop_i ROI_eq)].

Definition get_block_used := 
  get_block_state ++
  [u32const BLK_USED;
   BI_relop T_i32 (Relop_i ROI_eq)].

Definition mark_block_free :=
  [
    u32const BLK_FREE;
    BI_store T_i32 None 0%N 0%N
  ].

Definition mark_block_used :=
  [
    u32const BLK_USED;
    BI_store T_i32 None 0%N 0%N
  ].


Definition get_block_size :=
  [
    BI_load T_i32 None 4%N 0%N
  ].
  
Definition set_block_size :=
  [
    BI_store T_i32 None 4%N 0%N
  ].
  
Definition get_block_next :=
  [
    BI_load T_i32 None 8%N 0%N
  ].

Definition get_block_start :=
 [
   i32const 12;
   BI_binop T_i32 (Binop_i BOI_add)
 ].

(*
  malloc: [i32] -> [i32]
  locals declared: [i32]

  Allocate a new block of memory of the requested size.

  Parameters/Locals:
  0     local variable, storing the requested size.
  1     local variable, storing the current candidate block of the free list.
*)
Definition malloc :=
  [
    (* Location of first block in the free list. *)
    i32const 0;
    (* Store the current block in $1. *)
    BI_set_local 1
  ] ++ [
    (* Loop invariant: $1 is either -1 or it points to a valid block. *)
    BI_loop (Tf [] []) (
      (* Check if the block is a STOP marker. *)
      BI_get_local 1 ::
      get_block_stop ++ [
      BI_if (Tf [] [])
          (* put the free flag at the top of the stack*)
          (BI_get_local 1 ::
           get_block_free ++
           (* Put a boolean representing whether the size is big enough at the top of the stack *)
           BI_get_local 0 ::
           BI_get_local 1 ::
           get_block_size ++ 
           [BI_relop T_i32 (Relop_i (ROI_le SX_U));
            (* Compute free && fits *)
            BI_binop T_i32 (Binop_i BOI_and);
            BI_if (Tf [] []) (
                (* it's free and it fits, mark block as not free and return start *)
                BI_get_local 1 ::
                mark_block_used ++
                BI_get_local 1 ::
                get_block_start ++ 
                [BI_return]
            ) 
            (get_block_next ++ [BI_set_local 1])
          ]) [
          (* address of block was null: trap *)
          (* grow the free list *)
          (* ultimately, decide we're out of space & return -1 *)
          BI_unreachable
      ]
    ]) 
  ].

End code.

Section specs.

Lemma wp_label_push_emp
  (s : stuckness) (E : coPset) (Φ : val → iProp Σ)
  (es : language.expr iris_wp_def.wasm_lang) 
  (i : nat) (lh : lholed) (n : nat) 
  (es' : seq.seq administrative_instruction) :
  WP es @ s; E CTX S i; push_base lh n es' [] [] {{ v, Φ v }} ⊢ WP [AI_label n es' es] @ s; E CTX i; lh {{ v, Φ v }}.
Proof.
  replace [AI_label n es' es] 
     with [AI_label n es' ([] ++ es ++ [])]
    by (rewrite cats0; auto).
  eapply wp_label_push; auto.
Qed.

Lemma wp_label_push_cons
  (s : stuckness) (E : coPset) (Φ : val → iProp Σ)
  (e : administrative_instruction)
  (es : language.expr iris_wp_def.wasm_lang) 
  (i : nat) (lh : lholed) (n : nat) 
  (es' : seq.seq administrative_instruction) :
  WP [e] @ s; E CTX S i; push_base lh n es' [] es {{ v, Φ v }} ⊢ WP [AI_label n es' (e::es)] @ s; E CTX i; lh {{ v, Φ v }}.
Proof.
  replace [AI_label n es' (e::es)] 
     with [AI_label n es' ([] ++ [e] ++ es)]
    by (simpl; auto).
  eapply wp_label_push; auto.
Qed.

Inductive free_flag :=
| Used
| Free.

Definition flag_repr (flag : free_flag) : value :=
  match flag with
  | Used => value_of_uint BLK_USED
  | Free => value_of_uint BLK_FREE
  end.

Inductive block :=
| BlkStop: block
| BlkGo: 
  free_flag -> 
  i32 (* size *) ->
  block (* next *) ->
  block.

Definition nat_repr (n: nat) (m: i32) : Prop :=
  Z.of_nat n = Wasm_int.Int32.unsigned m.

Definition own_block (memidx: N) (base_addr: N) (sz: i32) : iProp Σ :=
  ∃ bs: bytes, ⌜nat_repr (length bs) sz⌝ ∗ memidx ↦[wms][base_addr] bs.

Definition data_repr (flag: free_flag) (sz: i32) (memidx: N) (base_addr: N) : iProp Σ :=
  match flag with
  | Used => ⌜True⌝
  | Free => own_block memidx base_addr sz
  end%I.

(* The block representation invariant *)
Fixpoint blk_rep blk memidx base_addr : iProp Σ :=
  match blk with
  | BlkStop =>
      memidx ↦[wms][base_addr] bits (value_of_uint BLK_STOP)
  | BlkGo flag sz next =>
      ∃ next_addr,
        memidx ↦[wms][base_addr] bits (flag_repr flag) ∗
        memidx ↦[wms][base_addr + 4] bits (VAL_int32 sz) ∗
        memidx ↦[wms][base_addr + 8] bits (value_of_uint next_addr) ∗
        data_repr flag sz memidx (base_addr + 12)%N ∗
        blk_rep next memidx next_addr
  end%I.

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
Admitted.

End specs.    
End malloc.    
      
