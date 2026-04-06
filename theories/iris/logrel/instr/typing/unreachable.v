Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section unreachable.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_unreachable M F L L' wt wt' wtf wl wl' wlf ψ es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (IUnreachable ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L'.
  Proof.
    intros fe WT WL lmask Hok Hcg.
    inv_cg_emit Hcg.
    subst.
    destruct ψ as [τs1 τs2].
    iIntros (????????) "@@@@@@@@@@@".
    iApply cwp_val_app; first done.
    iApply (cwp_unreachable with "[$] [$]").
  Qed.

End unreachable.
