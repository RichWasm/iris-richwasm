Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section nil.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_nil M F L wt wt' wtf wl wl' wlf es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    run_codegen (compile_instrs mr fe []) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' (InstrT [] []) L.
  Proof.
    intros fe WT WL lmask Hcg.
    cbn in Hcg.
    inversion Hcg.
    subst.
    iIntros (????????) "@@@@@@@@@@@".
    iApply cwp_val_app; first done.
    iApply (cwp_nil with "[$] [$]").
    iFrame.
    rewrite app_nil_r.
    by iFrame.
  Qed.

End nil.
