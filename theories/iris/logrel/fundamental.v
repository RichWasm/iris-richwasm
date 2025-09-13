From mathcomp Require Import ssreflect ssrbool eqtype seq.

From stdpp Require Import base fin_maps option list.

From ExtLib.Structures Require Import Monads.
From ExtLib.Data.Monads Require Import StateMonad.

From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import list.
From iris.prelude Require Import options.

From RichWasm.iris.helpers Require Export iris_properties.
From RichWasm.iris.language Require Export iris_atomicity lenient_wp lwp_pure lwp_structural lwp_resources lwp_trap.
From RichWasm.iris.rules Require Export iris_rules.

From RichWasm Require Import syntax typing.
From RichWasm.compiler Require Import codegen instrs modules util.
From RichWasm.iris Require Import autowp gc.
From RichWasm.iris.logrel Require Import relations.
Require Import RichWasm.util.

Module RT := RichWasm.syntax.
Module T := RichWasm.typing.

Import uPred.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "1".

Ltac fill_vals_pred' vs :=
  instantiate ( 1 := (λ w, ⌜w = vs⌝ ∗ _)%I).

Ltac curry_hyps :=
  iRevert "∗";
  rewrite ? wand_curry.

Ltac fill_goal :=
  match goal with
  | |- environments.envs_entails _ ?E =>
      is_evar E;
      curry_hyps;
      try (iApply wand_refl; solve_constraints);
      instantiate (1:= ⌜True⌝%I); done
  end.

Ltac fill_vals_pred :=
  match goal with
  | |- environments.envs_entails _ (?g ?vs) =>
      fill_vals_pred' vs; iSplitR; [done | fill_goal]
  end.

Section Fundamental.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!RichWasmGCG Σ}.

  Variable sr : store_runtime.

  Theorem fundamental_property M F L L' me fe es es' tf wl wl' :
    instrs_have_type M F L es tf L' ->
    run_codegen (compile_instrs me fe es) wl = inr (tt, wl', es') ->
    ⊢ has_type_semantic sr M F L wl' (to_e_list es') tf L'.
  Proof.
    intros Htyp Hcomp.
    generalize dependent es'.
    induction Htyp using instrs_have_type_mind with
      (P := fun C F L e ta L' _ =>
              forall es',
                run_codegen (compile_instr me fe e) wl = inr (tt, wl', es') ->
                ⊢ has_type_semantic sr C F L [] (to_e_list es') ta L');
    intros es' Hcomp.
  Admitted.

End Fundamental.
