Require Import RecordUpdate.RecordUpdate.
From stdpp Require Import base list.

From iris.proofmode Require Import base proofmode classes.
From RichWasm.wasm Require Import operations.

From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import prelude codegen instruction module.
From RichWasm.iris Require Import autowp memory util wp_codegen.
From RichWasm.iris.language Require Import cwp logpred.
From RichWasm.iris.logrel Require Import relations_cwp fundamental_kinding.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Fundamental.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_nil M F L wt wt' wtf wl wl' wlf es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    run_codegen (compile_instrs mr fe []) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL es' (InstrT [] []) L.
  Proof.
    intros fe WT WL Hcg.
    cbn in Hcg; inversion Hcg; subst.
    iIntros (se inst fr os vs evs θ B R Hse Hevs) "HIinst HIB HIR HIvs HIos HIfr Hrt Hfr Hrun".

    iApply cwp_val_app; first done.
    iApply (cwp_nil with "[$] [$]").
    iFrame. rewrite app_nil_r; iFrame.

  Qed.

End Fundamental.
