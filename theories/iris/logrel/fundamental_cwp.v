Require Import RecordUpdate.RecordUpdate.
From stdpp Require Import base list.

From iris.proofmode Require Import base tactics classes.
From Wasm Require Import operations.

From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import prelude codegen instruction module.
From RichWasm.iris Require Import autowp memory util wp_codegen.
From RichWasm.iris.language Require Import cwp logpred.
From RichWasm.iris.logrel Require Import relations_cwp fundamental_kinding.

From RichWasm.iris.logrel.compat_cwp Require Import
  nop
  unreachable
  copy
  drop
  num
  num_const
  block
  loop
  ite
  br
  return_
  local_get_copy
  local_get_move
  local_set
  coderef
  inst
  call
  call_indirect
  inject
  inject_new
  case
  case_load_copy
  case_load_move
  group
  ungroup
  fold
  unfold
  pack
  unpack
  tag
  untag
  cast
  new
  load_copy
  load_move
  store_weak
  store_strong
  swap
  nil
  app
  singleton
  frame.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Fundamental.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Theorem fundamental_theorem_aux M F L L' n_skip wt wt' wtf wl wl' wlf es es' tf :
    have_instruction_type M F L es tf L' ->
    let fe := fe_of_context F <| fe_br_skip := n_skip |> in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    run_codegen (compile_instrs mr fe es) wt wl = inr (tt, wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL es' tf L'.
  Proof.
    intros Htype.
    generalize dependent es'.
    generalize dependent wlf.
    generalize dependent wl'.
    generalize dependent wl.
    generalize dependent wtf.
    generalize dependent wt'.
    generalize dependent wt.
    generalize dependent n_skip.
    induction Htype using have_instruction_type_mind with
      (P1 := fun M F L e ψ L' =>
               forall n_skip wt wt' wtf wl wl' wlf es',
                 let fe := fe_of_context F <| fe_br_skip := n_skip |> in
                 let WT := wt ++ wt' ++ wtf in
                 let WL := wl ++ wl' ++ wlf in
                 run_codegen (compile_instr mr fe e) wt wl = inr (tt, wt', wl', es') ->
                 ⊢ have_instr_type_sem rti sr mr M F L WT WL es' ψ L');
      intros n_skip wt wt' wtf wl wl' wlf wes fe WT WL Hcomp.
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
    - specialize (IHHtype n_skip).
      specialize (IHHtype0 n_skip).
      eapply compat_app in Hcomp; eassumption.
    - eapply compat_singleton; eassumption.
    - specialize (IHHtype n_skip).
      eapply compat_frame; try eassumption.
  Qed.

  Theorem fundamental_theorem M F L L' wt wt' wtf wl wl' wlf es es' tf :
    have_instruction_type M F L es tf L' ->
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    run_codegen (compile_instrs mr fe es) wt wl = inr (tt, wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL es' tf L'.
  Proof.
    apply fundamental_theorem_aux with (n_skip := []).
  Qed.

End Fundamental.
