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
    let ψ := InstrT [τ] [RefT κr μ (VariantT κv τs')] in
    τs !! i = Some τ ->
    mono_mem μ ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IInjectNew ψ i)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Admitted.

End inject_new.
