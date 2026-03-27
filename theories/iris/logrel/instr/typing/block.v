Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section block.

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
    let lmask := wlmask fe wl in
    let F' := F <| fc_labels ::= cons (τs2, L') |> in
    let ψ := InstrT τs1 τs2 in
    has_instruction_type_ok F ψ L' ->
    (forall wt wt' wtf wl wl' wlf es',
        let fe' := fe_of_context F' in
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        let lmask := wlmask fe wl in
        run_codegen (compile_instrs mr fe' es) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instr_type_sem rti sr mr M F' L WT WL lmask es' ψ L') ->
    run_codegen (compile_instr mr fe (IBlock ψ L' es)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L'.
  Proof.
    iIntros (?????? Hok IH Hcg ????????) "@@@@@@@@@@@".
    cbn [compile_instr] in Hcg.
    inv_cg_bind Hcg tf wt0 wt0' wl0 wl0' es_nil es0' Hcg1 Hcg2.
    inv_cg_try_option Hcg1.
    subst wt0 wl0 es_nil wt' wl' es'.
    inv_cg_bind Hcg2 res0 wt0 wt1 wl0 wl1 es1 es0 Hcg1 Hcg2.
    subst wt0' wl0' es0'.
    destruct res0 as [[] esb].
    inv_cg_emit Hcg2.
    subst wt1 wl1 es0.
    apply run_codegen_capture in Hcg1 as [Hcg1 ->].
    eapply IH in Hcg1.
    instantiate (1 := wlf) in Hcg1.
    instantiate (1 := wtf) in Hcg1.
    subst WT WL lmask.
    clear IH.
    clear Hretval.
    clear_nils.
    subst ψ.
    apply bind_Some in Heq_some as (ts1 & Hts1 & Htrans).
    apply bind_Some in Htrans as (ts2 & Hts2 & HSometf).
    inversion HSometf as [Htf].
    clear HSometf.
    subst tf.
    subst fe.
    cbn in Hts1, Hts2.
    iDestruct (translate_types_comp_interp_length with "Hos") as "%Hoslen".
    1, 2, 3: done.
    iDestruct (big_sepL2_length with "Hvs") as "%Hvslen".
    unfold ofe_car in Hvslen.
    iApply (cwp_block with "[$] [$]").
    { by eapply has_values_is_consts. }
    { rewrite <- Hoslen. rewrite Hvslen. by apply has_values_length in Hevs. }
    iIntros "!> Hfr Hrun".
    iPoseProof Hcg1 as "IH".
    clear Hcg1.
    iSpecialize ("IH" with "[] [] [$] [Hlabels] [$] [$] [$] [$] [$] [$] [$]").
    1, 2: done.
    2: iApply "IH".
    iApply labels_interp_cons.
    4: by iIntros (??) "!> ?".
    all: done.
  Qed.

End block.
