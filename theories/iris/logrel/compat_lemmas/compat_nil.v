Require Import RecordUpdate.RecordUpdate.
From stdpp Require Import base list.

From iris.proofmode Require Import base tactics classes.
From Wasm Require Import operations.

From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import prelude codegen instruction module.
From RichWasm.iris Require Import autowp memory util wp_codegen.
From RichWasm.iris.language Require Import lenient_wp lwp_pure lwp_structural lwp_resources logpred.
From RichWasm.iris.logrel Require Import relations fundamental_kinding.

Require Export shared.

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
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') (InstrT [] []) L.
  Proof.
    intros fe WT WL Hcompile.
    cbn in Hcompile.
    inversion Hcompile.

    iIntros (se inst lh fr rvs vs θ) "%Henv #Hinst #Hlf Hrvs Hvs Hframe Hrt Hfr Hrun".

    iEval (cbn) in "Hrvs"; iEval (cbn) in "Hvs".
    iDestruct "Hvs" as "(%rvss & %Hconcat & Hrvss)".
    iPoseProof (big_sepL2_length with "[$Hrvss]") as "%Hlens_rvss".
    iPoseProof (big_sepL2_length with "[$Hrvs]") as "%Hlens_rvs_vs".
    cbn in Hlens_rvss.
    destruct rvss, rvs; cbn in Hconcat, Hlens_rvss; try congruence.
    cbn in Hlens_rvs_vs. destruct vs; cbn in Hlens_rvs_vs; try congruence.

    rewrite !app_nil_l.
    unfold expr_interp.

    iApply lenient_wp_nil.
    unfold lp_combine, denote_logpred; cbn.
    iFrame.
    iExists []; auto.
    iSplit; auto.
    iExists []; auto.
  Qed.

End Fundamental.
