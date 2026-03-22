Require Import RecordUpdate.RecordUpdate.
From stdpp Require Import base list.

From iris.proofmode Require Import base proofmode classes.

From RichWasm.named_props Require Import named_props custom_syntax.
From RichWasm.wasm Require Import operations.
From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import prelude codegen instruction module.
From RichWasm.iris Require Import autowp memory util wp_codegen.
From RichWasm.iris.language Require Import cwp logpred.
From RichWasm.iris.logrel Require Import relations_cwp fundamental_kinding.
Require Import RichWasm.iris.logrel.compat_cwp.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Fundamental.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_loop M F L wt wt' wtf wl wl' wlf es es' τs1 τs2 :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let F' := F <| fc_labels ::= cons (τs1, L) |> in
    let ψ := InstrT τs1 τs2 in
    has_instruction_type_ok F ψ L ->
    (forall wt wt' wtf wl wl' wlf es',
        let fe' := fe_of_context F' in
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        run_codegen (compile_instrs mr fe' es) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instr_type_sem rti sr mr M F' L WT WL es' ψ L) ->
    run_codegen (compile_instr mr fe (ILoop ψ es)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL es' ψ L.
  Proof.
    iIntros (????? Hok IH Hcg ?????????) "@@@@@@@@@@@".
    cbn in Hcg.
    unfold compile_loop in Hcg.
    inv_cg_bind Hcg ?res ?wt ?wt ?wl ?wl ?es ?es ?Hcg ?Hcg.
    inv_cg_try_option Hcg.
    inv_cg_bind Hcg0 [[] ?res] ?wt ?wt ?wl ?wl ?es ?es ?Hcg ?Hcg.
    apply run_codegen_capture in Hcg as [Hcg ->].
    inv_cg_emit Hcg0.
    clear Hretval.
    destruct res as [ts1 ts2].
    subst WT WL ψ.
    rename Heq_some into Htrans.
    apply bind_Some in Htrans as (ts1' & Htrans1 & Htrans).
    apply bind_Some in Htrans as (ts2' & Htrans2 & Hts).
    inversion Hts.
    subst.
    clear_nils.
    iDestruct (translate_types_comp_interp_length with "Hos") as "%Hlen_ts1".
    1, 2, 3: done.
    iDestruct (big_sepL2_length with "Hvs") as "%Hlen_vs".
    eapply IH in Hcg.
    iApply (cwp_loop with "[$] [$] [Hvs Hos Hframe Hrt]").
    - by eapply has_values_is_consts.
    - rewrite <- Hlen_ts1. rewrite Hlen_vs. by apply has_values_length.
    - iIntros "!> Hfr Hrun".
      iApply (Hcg with "[] [] [$] [] [$] [$] [$] [$] [$] [$] [$]").
      1, 2: done.
      iApply labels_interp_cons.
      1, 2, 3, 5: done.
      iModIntro.
      iIntros (??) "(Hframe & %os' & %θ' & Hos' & Hvs' & Hrt)".
      instantiate (1 := fun fr' vs' =>
        (frame_interp rti sr se L (wl ++ wl2 ++ wlf) inst fr' ∗
           ∃ os' θ', values_interp rti sr se τs1 os' ∗ atoms_interp os' vs' ∗ rt_token rti sr θ')%I).
      iFrame.
    - do 2 iModIntro.
      iIntros (??) "Hfr Hrun (Hframe & %os' & %θ' & Hos & Hvs & Hrt)".
      iApply (Hcg with "[] [] [$] [] [$] [$] [$] [$] [$] [$] [$]").
      + done.
      + iPureIntro. apply has_values_to_consts.
      + iApply labels_interp_cons.
        1, 2, 3, 5: done.
        iModIntro.
        iIntros (??) "(Hframe & %os'' & %θ'' & Hos & Hvs & Hrt)".
        iFrame.
  Qed.

End Fundamental.
