Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section copy.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_copy M F L wt wt' wtf wl wl' wlf τ es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [τ] [τ; τ] in
    has_ref_flag F τ GCRefs ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ICopy ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros * Hcopy Hok Hcompile.
    unfold compile_instr in Hcompile.
    inv_cg_bind Hcompile ρ wt1 wt1' wl1 wl1' es_nil es1 Htype_rep Hcompile.
    inv_cg_bind Hcompile ιs wt2 wt2' wl2 wl2' es_nil' es2 Heval_rep Hcompile.
    inv_cg_bind Hcompile idxs ?wt ?wt ?wl ?wl es_save ?es Hsave Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_restore1 ?es Hrestore1 Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_gcs es_restore2 Hgcs Hrestore2.
    inv_cg_try_option Htype_rep.
    inv_cg_try_option Heval_rep.
    subst.
    unfold WT, WL.
    repeat rewrite <- ?app_assoc, -> ?app_nil_l, -> ?app_nil_r in *.
    unfold have_instr_type_sem.
    unfold ψ.
    iIntros (se fr os vs evs θ B R).
    repeat iIntros "@".
    inversion Hcopy as [κ [Hkind Hbd]].

    (* TODO need type_dup from load_copy.v *)
    (* TODO need facts about save/restore *)
    (* TODO need fact about map_gc_ptrs ιs ixs (duproot mr)
             cf map_gc_ptr_duproot in wp_codegen, but right now that says
                nothing about the emitted code *)
  Admitted.

End copy.
