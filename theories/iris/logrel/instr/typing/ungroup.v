Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section ungroup.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_ungroup M F L wt wt' wtf wl wl' wlf es' τs κ :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [ProdT κ τs] τs in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IUngroup ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    iIntros (????? Hok Hcg ????????) "@@@@@@@@@@@@".
    inv_cg_emit Hcg.
    subst ψ WT WL wt' wl' es'.
    clear Hretval.
    clear_nils.
    iApply cwp_val_app; first done.
    iApply (cwp_nop with "[$] [$]").

    iDestruct "Hos" as "(%oss & -> & Hos)".
    iDestruct (big_sepL2_cons_inv_l with "Hos") as "(%os & %oss' & %Hoss & Hos & Hemp)".
    iDestruct (big_sepL2_nil_inv_l with "Hemp") as "->".
    iClear "Hemp".
    subst oss.
    setoid_rewrite value_interp_eq.
    iDestruct "Hos" as "(%sκ & %Hskind & %Hsvalues & %oss & %Hoss & Hoss)".
    inversion Hoss.
    subst os.
    clear Hoss.
    iDestruct (big_sepL2_later_2 with "Hoss") as "Hoss".

    iModIntro.
    unfold fvs_combine.
    rewrite app_nil_r.
    iFrame.
    iSplitR; first done.
    iPureIntro.
    cbn.
    by rewrite app_nil_r.
  Qed.

End ungroup.
