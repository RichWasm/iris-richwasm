Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section fold.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_fold M F L wt wt' wtf wl wl' wlf es' τ κ :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
    let ψ := InstrT [τ0] [RecT κ τ] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IFold ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmask τrec Ψ Hok Hcg.
    subst Ψ.
    cbn [compile_instr] in Hcg.
    inv_cg_emit Hcg; subst.
    subst WT WL.
    clear_nils.
    simplify_eq.

    simpl to_e_list.
    iApply sem_type_erased_nop; first done.
    iIntros (?????) "@@@@ Hval".
    rewrite !values_interp_one_eq.
    rewrite !value_interp_eq.
    cbn [pre_type_interp rec_interp].
    iDestruct "Hval" as "(%sk & %Htsk & %Hskhsv & Htrec)".

    inversion Hok; subst.
    inversion H; subst.
    rewrite Forall_singleton in H2.
    inversion H2; subst.
    inversion H3; subst.

    apply has_kind_RecT_inv in H5 as [Hsubkind Hhas_kind].
    inversion Hsubkind; subst.

    pose proof (has_kind_inv _ _ _ Hhas_kind) as Hkind_ok.
    inversion Hkind_ok as [F' τ' κ' Ht Hk]; subst.
    (* iDestruct "Hval" as "(%sk & %Htsk & %Hskhsv & Htrec)". *)
    iExists _.
    rewrite rec_interp_unfold.
    (* eapply eval_kind_ok_Some in Hk; eauto. *)
    (* 2 : { *)
    (*   apply sem_env_interp_extend_type; try done. *)
    (**)
    (* } *)
    (* destruct Hk as [sκ Hev]. *)
    (* pose proof (kinding_sound rti sr mr _ _ _ _ _ Hκ HF Hev) as [_ Hsv]. *)
    (* iDestruct (Hsv with "Hws") as "%Hkind". *)
    (**)
    (* eval_kind_ok_Some *)
    unfold rec_interp.
    iSimpl.
    cbn [rec_interp].

  Admitted.

End fold.
