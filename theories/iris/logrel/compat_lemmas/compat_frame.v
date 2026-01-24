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

  Lemma compat_frame M F L L' n_skip wt wt' wtf wl wl' wlf es es' τ τs1 τs2 :
    let fe := fe_of_context F <| fe_br_skip := n_skip |> in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    has_mono_rep F τ ->
    (forall wt wt' wtf wl wl' wlf es',
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        run_codegen (compile_instrs mr fe es) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') (InstrT τs1 τs2) L') ->
    run_codegen (compile_instrs mr fe es) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') (InstrT (τ :: τs1) (τ :: τs2)) L'.
  Proof.
    intros fe WT WL Hmono IH Hcg.
    eapply (IH _ _ _ _ _ wlf) in Hcg.
    iIntros (se inst lh fr rvs vs θ) "%Henv #Hinst #Hlf Hrvs Hvs Hframe Hrt Hfr Hrun".
    iPoseProof (values_interp_cons_inv with "Hvs") as "(%rvs1 & %rvs2 & %Hvs & Hty1 & Hty2)".
    subst rvs.
    iPoseProof (big_sepL2_app_inv_l with "Hrvs") as "(%vs1 & %vs2 & -> & Hvs1 & Hvs2)".
    iPoseProof (Hcg $! se inst lh fr rvs2 vs2 θ Henv with "Hinst Hlf") as "IH".
    iSpecialize ("IH" with "Hvs2 Hty2 [$] [$] [$] [$]").
    simpl language.of_val.
    iEval (repeat rewrite -cat_app).
    rewrite -v_to_e_cat.
    repeat rewrite cat_app.
    rewrite -app_assoc.
    iEval (cbn [List.map]).
    iApply (expr_interp_val_app with "[$] [$] [$]").
  Qed.

End Fundamental.
