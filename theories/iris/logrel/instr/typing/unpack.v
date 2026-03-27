Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section unpack.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_unpack M F F0' L L' L0 L0' wt wt' wtf wl wl' wlf es es' es0 τs1 τs2 ψ0 :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let F' := F <| fc_labels ::= cons (τs2, L') |> in
    let ψ := InstrT τs1 τs2 in
    unpacked_existential F' L es ψ L' F0' L0 es0 ψ0 L0' ->
    has_instruction_type_ok F ψ L' ->
    (forall wt wt' wtf wl wl' wlf es',
        let fe0' := fe_of_context F0' in
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        let lmask := wlmask fe0' wl in
        run_codegen (compile_instrs mr fe0' es0) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instr_type_sem rti sr mr M F0' L0 WT WL lmask es' ψ0 L0') ->
    run_codegen (compile_instr mr fe (IUnpack ψ L' es)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L'.
  Admitted.

End unpack.
