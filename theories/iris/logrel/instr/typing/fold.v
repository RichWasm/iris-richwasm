Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.instr.typing.inst. (* TODO: import proper subst file when created *)

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
    rewrite -!type_interp_eq.
    iPoseProof (type_interp_skind_svalue rti sr τrec se (SAtoms os) with "Hval") as (sκ) "[%Hτ0_sk %Hsv]".
    have Hkind : has_kind F (RecT κ τ) κ.
    {
      destruct Hok as [[_ Hmono] _].
      rewrite Forall_cons_iff in Hmono.
      destruct Hmono as [Hmono_rec _].
      destruct Hmono_rec as [ρ [Hrep _]].
      inversion Hrep as [? ? ? ? Hhas_kind]; subst.
      inversion Hhas_kind; subst.
      by constructor.
    }
    iEval (rewrite type_interp_eq).
    iModIntro.
    subst τrec.
    assert (eval_kind se κ = Some sκ) as Hκ.
    {
      admit.
    }
    iExists sκ.
    iSplit; first eauto.
    iSplit; first eauto.
    cbn -[skind_rec_interp1].
    rewrite Hκ.
    pose proof (fixpoint_unfold (skind_rec_interp1 sκ (type_interp rti sr τ) se)) as Hunf.
    specialize (Hunf (SAtoms os)).
    rewrite Hunf.
    cbn.
  Admitted.

End fold.
