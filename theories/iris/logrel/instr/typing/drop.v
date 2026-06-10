Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section drop.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_drop M F L wt wt' wtf wl wl' wlf τ es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl  in
    let ψ := InstrT [τ] [] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IDrop ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros * Hty Hcg.
    iIntros (se fr os vs evs θ B R).
    repeat iIntros "@".
    inv_cg_bind Hcg ρ wt1 wt1' wl1 wl1' es_nil es1 Htype_rep Hcg.
    inv_cg_bind Hcg ιs wt2 wt2' wl2 wl2' es_nil' es_drops Heval_rep Hdrop.
    (* TODO need lemma about drop1 *)
    (* TODO need lemma about drop_ptr, which is just free/unreg depending on
            what kind of pointer it's dealing with *)
  Admitted.

End drop.
