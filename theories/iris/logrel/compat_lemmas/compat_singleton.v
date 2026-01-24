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

  Lemma compat_singleton M F L L' n_skip wt wt' wtf wl wl' wlf e ψ es' :
    let fe := fe_of_context F <| fe_br_skip := n_skip |> in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    (forall m_skip wt wt' wtf wl wl' wlf es',
       let fe := fe_of_context F <| fe_br_skip := m_skip |> in
       let WT := wt ++ wt' ++ wtf in
       let WL := wl ++ wl' ++ wlf in
       run_codegen (compile_instr mr fe e) wt wl = inr ((), wt', wl', es') ->
       ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L') ->
    run_codegen (compile_instrs mr fe [e]) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L'.
  Proof.
    intros fe WT WL IH Hcg.
    unfold compile_instrs, util.mapM_ in Hcg.
    apply wp_ignore in Hcg.
    destruct Hcg as (_ & ? & Hcg).
    apply wp_mapM_cons in Hcg.
    destruct Hcg as ([] & ? & ? & ? & yss_xs & ? & ? & ? & He & Hret & -> & Hwt & Hwl & ->).
    cbn in Hret; inversion Hret; subst; clear Hret.
    eapply IH.
    rewrite -> !app_nil_r in *.
    eauto.
  Qed.

End Fundamental.
