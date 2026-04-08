Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section loop.

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
    let lmask := wlmask fe wl in
    let F' := F <| fc_labels ::= cons (τs1, L) |> in
    let ψ := InstrT τs1 τs2 in
    has_instruction_type_ok F ψ L ->
    (forall wt wt' wtf wl wl' wlf es',
        let fe' := fe_of_context F' in
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        let lmask := wlmask fe wl in
        run_codegen (compile_instrs mr fe' es) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instr_type_sem rti sr mr M F' L WT WL lmask es' ψ L) ->
    run_codegen (compile_instr mr fe (ILoop ψ es)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    iIntros (?????? Hok IH Hcg ????????) "@@@@@@@@@@@".
    inv_cg_bind Hcg ?res ?wt ?wt ?wl ?wl ?es ?es ?Hcg ?Hcg.
    inv_cg_try_option Hcg.
    inv_cg_bind Hcg0 [[] ?res] ?wt ?wt ?wl ?wl ?es ?es ?Hcg ?Hcg.
    apply run_codegen_capture in Hcg as [Hcg ->].
    inv_cg_emit Hcg0.
    destruct res as [ts1 ts2].
    subst WT WL ψ.
    apply bind_Some in Heq_some as (ts1' & Htrans1 & Htrans).
    apply bind_Some in Htrans as (ts2' & Htrans2 & Hts).
    inversion Hts.
    subst.
    clear_nils.
    iDestruct (translate_types_comp_interp_length with "Hos") as "%Hlen_ts1".
    1, 2, 3: done.
    iDestruct (big_sepL2_length with "Hvs") as "%Hlen_vs".
    eapply IH in Hcg.
    iApply (cwp_loop' with "[$] [$] [Hvs Hos Hframe Hrt]"); first done.
    - rewrite <- Hlen_ts1. rewrite Hlen_vs. by apply has_values_length.
    - instantiate (1 := fun fr' vs' =>
        (⌜frame_rel lmask fr fr'⌝ ∗ frame_interp rti sr se F.(fc_params) F.(typing.fc_locals) L (wl ++ wl2 ++ wlf) fr' ∗
           (∃ os', values_interp rti sr se τs1 os' ∗ atoms_interp os' vs') ∗
           (∃ θ', rt_token rti sr θ'))%I).
      by iFrame.
    - iIntros "!> !> %fr' %vs' Hfr Hrun (%Hrel & Hframe & (%os' & Hos & Hvs) & [%θ' Hrt])".
      iApply (cwp_wand with "[-]");
        first iApply (Hcg with "[] [] [] [] [$] [$] [$] [$] [$] [$] [$]").
      + done.
      + iPureIntro. apply has_values_to_consts.
      + by destruct Hrel as [_ ->].
      + iSimpl. iApply labels_interp_cons.
        1, 2, 3: done.
        * iIntros "!> %fr'' %vs'' (%Hfrel & Hframe & (%os'' & Hos & Hvs) & [%θ'' Hrt])".
          iFrame.
          iPureIntro.
          by eapply frame_rel_trans.
        * by iApply labels_interp_mono.
      + iIntros (fr'' vs'') "[%Hrel' ?]".
        iFrame.
        iPureIntro.
        eapply frame_rel_trans; last done.
        by eapply frame_rel_mask_mono.
  Qed.

End loop.
