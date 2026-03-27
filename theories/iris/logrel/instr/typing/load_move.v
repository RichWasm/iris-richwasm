Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section load_move.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma something_about_setflags: False.
  Abort.

  Lemma compat_load_move M F L wt wt' wtf wl wl' wlf es' κ κ' κser σ τ τval π pr :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [RefT κ (BaseM MemMM) τ] [RefT κ' (BaseM MemMM) (pr_replaced pr); τval] in
    resolves_path τ π (Some (type_span σ)) pr ->
    has_size F pr.(pr_target) σ ->
    pr.(pr_target) = SerT κser τval ->
    Forall (has_mono_size F) (pr_prefix pr) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ILoad ψ π Move)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmask ψ Hresolves Hsize Hser Hmonosize Htype Hcompile.
    unfold WT, WL; clear WT WL. (* If the WT := or WL := become necessary, comment the unfold/clear*)
    cbn in Hcompile.

    (* Mechanically get through some of the first few things in compile_load *)
    inv_cg_bind Hcompile off ?wt ?wt ?wl ?wl  es_fail ?es_rest Hoff Hcompile.
    inv_cg_bind Hcompile ρ ?wt ?wt ?wl ?wl es_off ?es_rest Hρ Hcompile.
    inv_cg_bind Hcompile ιs ?wt ?wt ?wl ?wl es_ρ ?es_rest Hιs Hcompile.
    inv_cg_try_option Hρ; rename Heq_some into Hρ.
    inv_cg_try_option Hιs; rename Heq_some into Hιs.
    inv_cg_try_option Hoff; rename Heq_some into Hoff.
    inv_cg_bind Hcompile a ?wt ?wt ?wl ?wl es_a ?es_rest Ha Hcompile.
    cbn in Ha; inversion Ha; subst; clear Ha.
    inv_cg_bind Hcompile res_emit ?wt ?wt ?wl ?wl  es_emit ?es_rest Hemit Hcompile.
    inv_cg_emit Hemit.
    inv_cg_bind Hcompile () ?wt ?wt ?wl ?wl es_ptr_flags ?es_rest Hptr_flags Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl  es_case_ptr ?es_rest Hcompile Hignore.
    cbn in Hignore; inversion Hignore; subst; clear Hignore.

    (* Some clean up *)
    destruct u.
    destruct p as [[] []].

    (* Next is case ptr *)
    (* WAITING FOE LEMMA *)
  Admitted.

End load_move.
