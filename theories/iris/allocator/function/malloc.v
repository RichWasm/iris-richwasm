From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From Wasm.iris.examples.stack Require Export stack_common.
From Wasm.iris.logrel Require Export iris_fundamental.
From Wasm.iris.rules Require Export proofmode.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Section malloc.


 Context `{!wasmG Σ}. 

Section code.

(* Given a pointer to a block in the free list, return its start (the
   address returned by malloc). *)
Definition get_block_start :=
 [
   i32const 8;
   BI_binop T_i32 (Binop_i BOI_add)
 ].
  
(* Given a pointer to a block in the free list, return the (possibly
   0, meaning null!) pointer to the next block. *)
Definition get_block_next :=
  [
    BI_load T_i32 None 4%N 0%N
  ].

(* Given a pointer to a block in the free list, return the block's free flag. *)
Definition get_block_free :=
  [
    BI_load T_i32 None 0%N 0%N
  ].

Definition mark_block_free :=
  [
    i32const 1;
    BI_store T_i32 None 0%N 0%N
  ].

Definition mark_block_used :=
  [
    i32const 0;
    BI_store T_i32 None 0%N 0%N
  ].

(* Given a pointer to a block in the free list in local index l, return its size.
   If block.next is null, this will compute a meaningless value.
   The size of a block is
      block.next - block.start.
*)
Definition get_block_size l :=
  BI_get_local l ::
  get_block_start ++ 
  BI_get_local l ::
  get_block_next ++
  [BI_binop T_i32 (Binop_i BOI_sub)].

(*
  malloc: [i32] -> [i32]
  locals declared: [i32]

  Allocate a new block of memory of the requested size.

  Can fail non-deterministically if grow_memory fails.

  Returns a pointer to the newly allocated block at the start of stack
  (0th cell), or -1 if allocation fails.

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
    BI_loop (Tf [] []) [
      BI_if (Tf [] [])
          (* address of block was non-null: check free flag and size *)
          (* put the free flag at the top of the stack*)
          (BI_get_local 1 ::
           get_block_free ++
           (* Put a boolean representing whether the size is big enough at the top of the stack *)
           BI_get_local 0 ::
           get_block_size 1 ++ 
           [BI_relop T_i32 (Relop_i (ROI_le SX_U));
            (* Compute free && fits *)
            BI_binop T_i32 (Binop_i BOI_and);
            BI_if (Tf [] []) (
                (* it's free and it fits, mark block as not free and return start *)
                BI_get_local 1 ::
                mark_block_free ++
                BI_get_local 1 ::
                get_block_start ++ 
                [BI_return]
            ) 
            (get_block_next ++ [BI_set_local 1])
      ]) [
          (* address of block was null: trap *)
          BI_unreachable
      ]
    ]
  ].

End code.

Section specs.

Lemma spec_malloc E free_flag next_ptr f0 sz: 
  ⊢ {{{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some free_flag⌝ ∗
         ⌜ f0.(f_inst).(inst_memory) !! 4 = Some next_ptr ⌝ ∗
         ⌜ f0.(f_locs) !! 0 = Some sz⌝ ∗
         ⌜ length (f_locs f0) >= 2 ⌝ ∗
        ↪[frame] f0
    }}}}
    (to_e_list malloc) @ E
    {{{{ v, ⌜True⌝ }}}}.
Proof.
  iIntros "!>" (Φ) "(%Hfree & %Hnext & %Hsz & %Hlen & Hfr) HΦ".
  unfold malloc.
  erewrite !to_e_list_cat.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV []⌝ ∗
                         ↪[frame] {|
                           f_locs := set_nth (value_of_uint 0) (f_locs f0) 1 (value_of_uint 0);
                           f_inst := f_inst f0 |})%I).
  iSplitR.
  { iIntros "(%Htrap & _)". auto. }
  iSplitL "Hfr".
  { cbn. 
    unfold i32const.
    iApply wp_set_local => //.
  }
  iIntros (w) "(%Htrap & Hfr)".
  subst w.

  iApply (wp_loop with "[Hfr] [HΦ]") => //; eauto.
  iIntros "!> Hfr".
  (* unsure what to do here. *)
Admitted.

End specs.    
End malloc.    
      
