Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section inject_new.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_inject_new M F L wt wt' wtf wl wl' wlf es' μ i τ τs κr κv κs :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let τs' := zip_with SerT κs τs in
    let ψ := InstrT [τ] [RefT κr μ Imm (VariantT κv τs')] in
    τs !! i = Some τ ->
    mono_mem μ ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IInjectNew ψ i)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    iIntros (?????? Hτ [bm ->] [[Hτ_mono Href_mono] HL_ok] Hcg ????????) "@@@@@@@@@@@@".
    rewrite Forall_singleton in Hτ_mono.
    destruct Hτ_mono as (ρ & Hτρ & Hρ_mono).
    inversion Hτρ.
    rename H into Hτ_kind.
    subst F0 τ0 ρ0.
    destruct κv as [|σ ξ']; first inversion Hcg.

    inv_cg_bind Hcg ρ' ?wt ?wt ?wl ?wl ?es ?es Hcg_rep Hcg.
    inv_cg_try_option Hcg_rep.
    rename Heq_some into Hρ'.
    inv_cg_bind Hcg ιs ?wt ?wt ?wl ?wl ?es ?es Hcg_arep Hcg.
    inv_cg_try_option Hcg_arep.
    rename Heq_some into Hιs.
    inv_cg_bind Hcg n ?wt ?wt ?wl ?wl ?es ?es Hcg_n Hcg.
    inv_cg_try_option Hcg_n.
    rename Heq_some into Hn.
    inv_cg_bind Hcg xs ?wt ?wt ?wl ?wl ?es ?es Hcg_save Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_alloc Hcg.
    inv_cg_bind Hcg laddr ?wt ?wt ?wl ?wl ?es ?es Hcg_laddr Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_set_laddr Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_flags Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_tag Hcg.
    inv_cg_bind Hcg ltag ?wt ?wt ?wl ?wl ?es ?es Hcg_ltag Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_set_ltag Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_store_tag Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_store Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_get_laddr Hcg_regroot.
    subst wt0 wl0 es wt2 wl2 es1 wt4 wl4 es3 wt25 wl25 es24 wt23 wl23 es22 wt21 wl21 es20 wt19 wl19
      es18 wt17 wl17 es16 wt15 wl15 es14 wt13 wl13 es12 wt11 wl11 es10 wt9 wl9 es8 wt7 wl7 es6 wt5
      wl5 es4 wt3 wl3 es2 wt1 wl1 es0 wt' wl' es'.
    clear_nils.

    apply type_rep_has_kind_agree in Hτ_kind as H.
    rewrite Hρ' in H.
    inversion H.
    subst ρ'.
    clear H.

    rewrite values_interp_one_eq value_interp_eq -type_interp_eq.
    iDestruct (type_interp_skind_svalue with "Hos") as "(%sκ & %Hsκ & %Hsv)".
    apply eval_rep_emptyenv with (se := se) in Hιs as Hιs_se.
    apply eval_kind_of_eval_rep with (ξ := ξ) in Hιs_se as Heval_kind.
    pose proof (type_skind_has_kind_agree _ _ _ _ _ _ Hτ_kind Hse Heval_kind Hsκ) as <-.
    iDestruct (type_interp_implies_has_areps with "Hos") as "%Hos"; first done.
    iDestruct (result_type_interp_of_atoms_interp with "Hvs") as "%Hvs"; first done.
    iDestruct (frame_interp_wl_interp with "Hframe") as "%HWL".

    rewrite app_assoc.
    eapply cwp_save_stack_w in Hcg_save as (-> & -> & -> & Hes5); first last.
    { by rewrite length_map length_map. }
    { by apply Is_true_true. }
    { by rewrite map_map. }
    { subst WL. by rewrite !app_nil_l -!app_assoc in HWL. }
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      iApply (Hes5 with "[$Hfr] [$Hrun]").
      iIntros (?) "[%Hfrel %Hlocs]".
      by instantiate
           (1 := fun f vs' =>
                   (⌜frame_rel (fun i => i ∉ seq (fe_wlocal_offset fe + length wl) (length ιs)) fr f⌝ ∗
                      ⌜Forall2 (fun i v => f_locs f !! localimm i = Some v)
                         (map Mk_localidx (seq (fe_wlocal_offset fe + length wl) (length ιs))) vs⌝ ∗
                   ⌜vs' = []⌝)%I).
    }

    iIntros (??) "(%Hfrel & %Hlocs & ->) Hfr Hrun".
    clear Hes5.
  Admitted.

End inject_new.
