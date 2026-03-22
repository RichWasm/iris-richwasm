Require Import RecordUpdate.RecordUpdate.
From stdpp Require Import base list.

From iris.proofmode Require Import base proofmode classes.
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

  Lemma compat_block M F L L' wt wt' wtf wl wl' wlf τs1 τs2 es es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let F' := F <| fc_labels ::= cons (τs2, L') |> in
    let ψ := InstrT τs1 τs2 in
    has_instruction_type_ok F ψ L' ->
    (forall wt wt' wtf wl wl' wlf es',
        let fe' := fe_of_context F' in
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        run_codegen (compile_instrs mr fe' es) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instr_type_sem rti sr mr M F' L WT WL es' ψ L') ->
    run_codegen (compile_instr mr fe (IBlock ψ L' es)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL es' ψ L'.
  Proof.
    iIntros (fe WT WL F' Ψ Hok IH Hrun se inst fr os vs evs θ B R Hse Hevs)
      "HIinst HIB HIR HIvs HIos HIfr Hrt Hfr Hrun".
    cbn [compile_instr] in Hrun.
    inv_cg_bind Hrun tf wt0 wt0' wl0 wl0' es_nil es0' Hrun1 Hrun2.
    inv_cg_try_option Hrun1.
    subst wt0 wl0 es_nil wt' wl' es'.
    inv_cg_bind Hrun2 res0 wt0 wt1 wl0 wl1 es1 es0 Hrun1 Hrun2.
    subst wt0' wl0' es0'.
    destruct res0 as [[] esb].
    inv_cg_emit Hrun2.
    subst wt1 wl1 es0.
    apply run_codegen_capture in Hrun1 as [Hrun1 ->].
    eapply IH in Hrun1.
    instantiate (1 := wlf) in Hrun1.
    instantiate (1 := wtf) in Hrun1.
    subst WT WL.
    clear IH.
    clear Hretval.
    clear_nils.
    subst Ψ.
    apply bind_Some in Heq_some as (ts1 & Hts1 & Htrans).
    apply bind_Some in Htrans as (ts2 & Hts2 & HSometf).
    inversion HSometf as [Htf].
    clear HSometf.
    subst tf.
    subst fe.
    cbn in Hts1, Hts2.
    iDestruct (translate_types_comp_interp_length with "HIos") as "%Hoslen".
    1, 2, 3: done.
    iDestruct (big_sepL2_length with "HIvs") as "%Hvslen".
    unfold ofe_car in Hvslen.
    iApply (cwp_block with "[$] [$]").
    { by eapply has_values_is_consts. }
    { rewrite <- Hoslen. rewrite Hvslen. by apply has_values_length in Hevs. }
    iIntros "!> Hfr Hrun".
    iPoseProof Hrun1 as "IH".
    clear Hrun1.
    iSpecialize
      ("IH" with "[] [] [$HIinst] [HIB] [$HIR] [$HIvs] [$HIos] [$HIfr] [$Hrt] [$Hfr] [$Hrun]");
      first done;
      first done;
      last iApply "IH".
    iApply labels_interp_cons.
    4: by iIntros (fr' vs') "!> H".
    all: done.
  Qed.

End Fundamental.
