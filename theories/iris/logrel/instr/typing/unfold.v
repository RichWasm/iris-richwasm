Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.substitution. (* TODO: import proper subst file when created *)
Require Import RichWasm.iris.logrel.env_props.
Require Import RichWasm.kinding_subst.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section unfold.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_unfold M F L wt wt' wtf wl wl' wlf es' τ κ :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
    let ψ := InstrT [RecT κ τ] [τ0] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IUnfold ψ)) wt wl = inr ((), wt', wl', es') ->
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
    iPoseProof (type_interp_skind_svalue rti sr (RecT κ τ) se (SAtoms os) with "Hval") as (sκ) "[%Hκ %H]".
    unfold type_skind in Hκ; simpl in Hκ.
    have Hkind : has_kind F (RecT κ τ) κ.
    {
      destruct Hok as [[Hmono _] _].
      rewrite Forall_cons_iff in Hmono.
      destruct Hmono as [Hmono _].
      destruct Hmono as [ρ [Hrep _]].
      inversion Hrep as [? ? ? ? Hhas_kind]; subst.
      inversion Hhas_kind; subst.
      constructor. assumption.
    }
    unfold τrec.

    iEval (rewrite type_interp_eq) in "Hval".
    iDestruct "Hval" as "(%sk & %Hsk & %Hsv & Hos)".
    iEval (cbn -[skind_rec_interp]) in "Hos".
    rewrite Hκ.
    unfold skind_rec_interp.
    iEval (cbn -[skind_rec_interp1]) in "Hos".

    pose proof (fixpoint_unfold (skind_rec_interp1 sκ (type_interp rti sr τ) se)) as Hunf.
    (* cbn in Hunf. *)
    specialize (Hunf (SAtoms os)).
    rewrite Hunf.
    Opaque skind_has_svalue. Opaque senv_insert_type.
    unfold skind_rec_interp1. iEval (cbn -[add_skind_interp_closed]) in "Hos".
    Transparent senv_insert_type.
    iModIntro.
    inversion Hkind; subst.
    assert (Hkindτrec: has_kind F τrec κ) by by apply has_kind_rec_subst.
    destruct (refresh_kinds_id) as (this & _).
    assert (refresh_kinds F τrec = τrec) by (symmetry; by eapply this).
    unfold τrec in H0.
    rewrite <- H0.
    iAssert (type_interp rti sr τ
               (senv_insert_type sκ sκ (value_interp rti sr se (RecT κ τ)) se) (SAtoms os))
      with "[Hos]" as "Hos". {
      (* rocq despises me I swear *)
      (* just use add_skind_interp_closed_equiv_value_interp *)
      (* but for some unknown reason it refuses to rewrite *)
      (* there's the senv_insert_type difference but even islating that and cbn-ing it didn't
        do anything *)
      pose proof (add_skind_interp_closed_equiv_value_interp rti sr sκ τ κ se Hκ).
      assert (Hproper: Proper (equiv ==> equiv) (type_interp rti sr τ)). {
        typeclasses eauto.
      }
      iApply Hproper.
      {
        apply senv_insert_type_proper.
        symmetry.
        apply H1.
      }
      done.
    }
    pose proof (sem_well_formed_from_interp F se Hse) as HseF.

    iApply (type_interp_subst_type_forwards with "[$Hos]").
    1: exact mr.
    11: exact H4.
    1-9: try done.
    - unfold sem_env_types_well_formed in *.
      apply Forall_cons; split; last exact HseF.
      split; first apply subskind_of_refl.
      cbn -[add_skind_interp_closed].
      eapply kinding_sound; try done.
    - apply sem_env_interp_insert_type; try done; first apply subskind_of_refl.
      eapply kinding_sound; try done.
    - unfold sem_env_rel_sκ_eq.
      intros i. destruct i; cbn; last apply subskind_of_option_refl.
      rewrite Hκ. apply subskind_of_option_refl.
    - unfold sem_env_rel_type_eq.
      intros i; destruct i; cbn -[add_skind_interp_closed].
      2: {
        Opaque type_skind. Opaque skind_has_svalue.
        rewrite value_interp_eq_no_sv; cbn.
        iIntros (sv); iSplitR; iIntros "Hoa".
        Transparent type_skind.
        all: cbn.
        all: destruct (snd <$> (snd <$> se.2 !! i)) eqn:HT; rewrite HT; try done.
        2-3: iDestruct "Hoa" as "(%sk' & %inf & %fo & Hoa)"; try done.
        apply fmap_Some in HT as ((sκ' & T) & lookp & ->).
        apply fmap_Some in lookp as ((sk_up & known) & lookp & a).
        cbn in a; subst known.
        rewrite lookp.
        iExists sk_up. (* cannot iframe yet *)
        cbn.
        destruct Hse as (_ & types).
        unfold type_ctx_interp in types; cbn in types.
        pose proof (Forall2_lookup_r _ _ _ _ _ types lookp) as (u & useless & (eval & subs & sksv)).
        destruct sksv as (refflag & ToUse).
        iPoseProof (ToUse with "[$Hoa]") as "%sksv2".
        iFrame.
        iSplitR; first done.
        iPureIntro.
        eapply skind_as_type_refine; try done.
        Transparent skind_has_svalue.
      }
      done.
    - intros i; destruct i; try done.
      cbn.
      apply this in H4.
      rewrite <- H4.
      done.
    - (* this is whatever the kinding admit above is *)
      rewrite H0.
      exact Hkindτrec.
      Transparent skind_has_svalue.
  Qed.

End unfold.
