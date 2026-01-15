Require Import RecordUpdate.RecordUpdate.
From stdpp Require Import base list.

From iris.proofmode Require Import base tactics classes.
From Wasm Require Import operations.

From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import prelude codegen instruction module.
From RichWasm.iris Require Import autowp memory util wp_codegen.
From RichWasm.iris.language Require Import lenient_wp lwp_pure lwp_structural lwp_resources logpred.
From RichWasm.iris.logrel Require Import relations fundamental_kinding.

Require Import
  compat_nop
  compat_unreachable
  compat_copy
  compat_drop
  compat_num
  compat_num_const
  compat_block
  compat_loop
  compat_ite
  compat_br
  compat_return
  compat_local_get_copy
  compat_local_get_move
  compat_local_set
  compat_coderef
  compat_inst
  compat_call
  compat_call_indirect
  compat_inject
  compat_inject_new
  compat_case
  compat_case_load_copy
  compat_case_load_move
  compat_group
  compat_ungroup
  compat_fold
  compat_unfold
  compat_pack
  compat_unpack
  compat_tag
  compat_untag
  compat_cast
  compat_new
  compat_load_copy
  compat_load_move
  compat_store_weak
  compat_store_strong
  compat_swap
  compat_nil
  compat_app
  compat_singleton
  compat_frame.


Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Fundamental.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Theorem fundamental_theorem M F L L' wt wt' wtf wl wl' wlf es es' tf :
    have_instruction_type M F L es tf L' ->
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    run_codegen (compile_instrs mr fe es) wt wl = inr (tt, wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') tf L'.
  Proof.
    intros Htype.
    generalize dependent es'.
    generalize dependent wlf.
    generalize dependent wl'.
    generalize dependent wl.
    generalize dependent wtf.
    generalize dependent wt'.
    generalize dependent wt.
    induction Htype using have_instruction_type_mind with
      (P1 := fun M F L e ψ L' =>
               forall wt wt' wtf wl wl' wlf es',
                 let fe := fe_of_context F in
                 let WT := wt ++ wt' ++ wtf in
                 let WL := wl ++ wl' ++ wlf in
                 run_codegen (compile_instr mr fe e) wt wl = inr (tt, wt', wl', es') ->
                 ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L');
      intros wt wt' wtf wl wl' wlf wes fe WT WL Hcomp.
    - eapply compat_nop; eassumption.
    - eapply compat_unreachable; eassumption.
    - eapply compat_copy; eassumption.
    - eapply compat_drop; eassumption.
    - eapply compat_num; eassumption.
    - eapply compat_num_const; eassumption.
    - eapply compat_block; eassumption.
    - eapply compat_loop; eassumption.
    - eapply compat_ite in Hcomp; eassumption.
    - eapply compat_br; eassumption.
    - eapply compat_return; eassumption.
    - eapply compat_local_get_copy; eassumption.
    - eapply compat_local_get_move; eassumption.
    - eapply compat_local_set; eassumption.
    - eapply compat_coderef; eassumption.
    - eapply compat_inst; eassumption.
    - eapply compat_call; eassumption.
    - eapply compat_call_indirect; eassumption.
    - eapply compat_inject; eassumption.
    - eapply compat_inject_new; eassumption.
    - eapply compat_case; eassumption.
    - eapply compat_case_load_copy; eassumption.
    - eapply compat_case_load_move; eassumption.
    - eapply compat_group; eassumption.
    - eapply compat_ungroup; eassumption.
    - eapply compat_fold; eassumption.
    - eapply compat_unfold; eassumption.
    - eapply compat_pack; eassumption.
    - eapply compat_unpack; eassumption.
    - eapply compat_tag; eassumption.
    - eapply compat_untag; eassumption.
    - eapply compat_cast; eassumption.
    - eapply compat_new; eassumption.
    - eapply compat_load_copy; eassumption.
    - eapply compat_load_move; eassumption.
    - eapply compat_store_weak; eassumption.
    - eapply compat_store_strong; eassumption.
    - eapply compat_swap; eassumption.
    - eapply compat_nil; eassumption.
    - eapply compat_app in Hcomp; eassumption.
    - eapply compat_singleton; eassumption.
    - eapply compat_frame; eassumption.
  Qed.

End Fundamental.
