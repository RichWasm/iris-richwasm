Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section local_get_move.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_local_get_move M F L wt wt' wtf wl wl' wlf es' i τ ηs :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [] [τ] in
    let L' := <[ i := type_plug_prim ηs ]> L in
    F.(typing.fc_locals) !! i = Some ηs ->
    L !! i = Some τ ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ILocalGet ψ Move i)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L'.
  Admitted.

End local_get_move.
