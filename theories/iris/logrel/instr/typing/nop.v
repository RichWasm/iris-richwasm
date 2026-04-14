Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section nop.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_nop M F L wt wt' wtf wl wl' wlf es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [] [] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (INop ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmask ψ Hok Hcg.
    iIntros (????????) "@@@@@@@@@@@@".
    inv_cg_emit Hcg.
    subst.
    iApply cwp_val_app; first done.
    iApply (cwp_nop with "[$] [$]").
    iFrame.
    rewrite app_nil_r.
    by iFrame.
  Qed.

End nop.
