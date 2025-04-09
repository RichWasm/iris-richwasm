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

[ free? ][ size ] [ next ] .....  [ free? ] [ size ] [ next ] ...

*)

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
    BI_loop (Tf [] []) [
      BI_if (Tf [] [])
          (* address of block was non-null: check free flag and size *)
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
      
