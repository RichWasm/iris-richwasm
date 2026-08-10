Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.case_ptr.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section case_load_move.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_case_load_move M F L L' wt wt' wtf wl wl' wlf ess es' τs τs' κr κv κs :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let F' := F <| fc_labels ::= cons (τs', L') |> in
    let τs_ser := zip_with SerT κs τs in
    let ψ := InstrT [RefT κr (BaseM MemMM) Imm (VariantT κv τs_ser)] τs' in
    Forall2
      (fun τ es =>
         (forall wt wt' wtf wl wl' wlf es',
            let fe' := fe_of_context F' in
            let WT := wt ++ wt' ++ wtf in
            let WL := wl ++ wl' ++ wlf in
            let lmask := wlmask fe' wl in
            run_codegen (compile_instrs mr fe' es) wt wl = inr ((), wt', wl', es') ->
           ⊢ have_instr_type_sem rti sr mr M F' L WT WL lmask es' (InstrT [τ] τs') L'))
      τs ess ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ICaseLoad ψ Move L' ess)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L'.
  Proof.
    iIntros (??????? IH Hok Hcg ????????) "@@@@@@@@@@@@".
    destruct κv.
    { admit. } (* contradiction *)
    destruct τs'.
    { admit. } (* contradiction *)
    destruct τs'; first last.
    { admit. } (* contradiction *)

    cbn in Hcg.
    inv_cg_bind Hcg n ?wt ?wt ?wl ?wl ?es ?es Hn Hcg.
    inv_cg_bind Hcg ts ?wt ?wt ?wl ?wl ?es ?es Hts Hcg.
    inv_cg_bind Hcg x ?wt ?wt ?wl ?wl ?es ?es Hx Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hsetx Hcg.
    inv_cg_bind Hcg [[] [[] []]] ?wt ?wt ?wl ?wl ?es ?es Hcg Hret.
    inv_cg_try_option Hn.
    inv_cg_try_option Hts.
    apply wp_wlalloc in Hx as (-> & -> & -> & ->).
    inv_cg_emit Hsetx.
    inv_cg_ret Hret.
    subst wt0 wl0 es wt2 wl2 es1 wt6 wl6 es5 wt9 wl9 es8 wt7 wl7 es6 wt5 wl5 es4 es2 es0 es' wt3 wl3 wt1 wl1 wt' wl'.
    clear Hretval Hretval0.
    clear_nils.

    rewrite values_interp_one_eq.
    iDestruct (value_interp_ref_sz with "Hos") as "%Hos".
    destruct (list_singleton_reflect os); last contradiction.
    rename x into o.
    subst os.
    clear Hos.
    rewrite atoms_interp_one_inv.
    iDestruct "Hvs" as "(% & % & Hvs)".
    subst vs.
    rewrite has_values_iff_to_consts in Hevs.
    cbn in Hevs.
    subst evs.

    set x := fe_wlocal_offset fe + length wl.

    rewrite app_assoc.
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      iApply (cwp_local_set with "[] [$Hfr] [$Hrun]").
      - admit.
      - by instantiate (1 := fun fr' vs => (⌜fr' = Build_frame (<[ x := v ]> fr.(f_locs)) fr.(f_inst)⌝ ∗
                                           ⌜vs = []⌝)%I).
    }

    iIntros (??) "[-> ->] Hfr Hrun".
    rewrite app_nil_l.

    (* case_ptr *)
  Admitted.

End case_load_move.
