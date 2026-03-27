Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section call.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_call M F L wt wt' wtf wl wl' wlf es' i ixs ϕ τs1 τs2 :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT τs1 τs2 in
    M.(mc_functions) !! i = Some ϕ ->
    function_type_insts F ixs ϕ (MonoFunT τs1 τs2) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ICall ψ i ixs)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Admitted.

End call.
