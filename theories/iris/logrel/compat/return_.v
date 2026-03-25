Require Import RecordUpdate.RecordUpdate.
From stdpp Require Import base list.

From iris.proofmode Require Import base proofmode classes.

From RichWasm.named_props Require Import named_props custom_syntax.
From RichWasm.wasm Require Import operations.
From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import prelude codegen instruction module.
From RichWasm.iris Require Import autowp memory util wp_codegen.
From RichWasm.iris.language Require Import cwp logpred.
From RichWasm.iris.logrel Require Import relations fundamental_kinding.
Require Import RichWasm.iris.logrel.compat.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Fundamental.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_return M F L L' wt wt' wtf wl wl' wlf es' τs1 τs τs2 :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT (τs1 ++ τs) τs2 in
    F.(fc_return) = τs ->
    Forall (fun τ => has_ref_flag F τ NoRefs) τs1 ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (IReturn ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL es' ψ L'.
  Proof.
    iIntros (???? Hreturn Hdrop Hok Hcg ?????????) "@@@@@@@@@@@".
    inversion Hcg.
    subst fe WT WL ψ wt' wl' es'.
    clear Hcg.
    clear_nils.
    destruct R as [[n P]|]; last done.
    iDestruct "Hreturn" as "[Hlen_ts HP]".
    rewrite Hreturn.
    destruct (translate_types se τs) as [ts|] eqn:Hts; last done.
    iDestruct "Hlen_ts" as "%Hlen_ts".
    iDestruct (values_interp_app_l with "Hos") as "(%os1 & %os2 & -> & Hos1 & Hos2)"; first done.
    iDestruct (atoms_interp_app_l with "Hvs") as "(%vs1 & %vs2 & -> & Hvs1 & Hvs2)".
    iDestruct (translate_types_sem_interp_length with "Hos2") as "%Hlen_os2".
    1, 2: done.
    iDestruct (big_sepL2_length with "Hvs2") as "%Hlen_vs2".
    apply has_values_app_inv in Hevs as (evs1 & evs2 & -> & Hevs1 & Hevs2).
    rewrite <- app_assoc.
    iApply cwp_val_app; first done.
    iApply (cwp_return with "[$] [$]").
    - done.
    - rewrite <- Hlen_ts. rewrite <- Hlen_os2. rewrite Hlen_vs2. by apply has_values_length.
    - iApply ("HP" with "[$] [$] [$]").
  Qed.

End Fundamental.
