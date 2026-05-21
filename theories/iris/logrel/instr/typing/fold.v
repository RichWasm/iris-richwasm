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

  (* TODO: fix *)
  Lemma fold_type_skind (se : semantic_env (Σ:=Σ)) (τ : type) (κ : kind) sκ :
    type_skind se (subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ) = Some sκ →
    eval_kind se κ = Some sκ.
  Proof. Admitted.

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
    rewrite -!type_interp_eq.
    iPoseProof (type_interp_skind_svalue rti sr τrec se (SAtoms os) with "Hval") as (sκ) "[%Hτ0_sk %Hsv]".
    (* inversion Hok; subst. *)
    (* inversion H; subst. *)
    (* rewrite Forall_singleton in H2. *)
    (* inversion H2; subst. *)
    (* inversion H3; subst. *)
    (* inversion H5; subst; last admit. *)
    assert (eval_kind se κ = Some sκ) as Hκ.
    {
      apply (fold_type_skind se τ κ sκ Hτ0_sk).
    }
    iModIntro.
    rewrite (fold_type_interp rti sr mr se τ κ sκ (SAtoms os) Hκ).
    iSplit.
    - iPureIntro. exact Hsv.
    - iModIntro. iExact "Hval".
  Qed.

End fold.
