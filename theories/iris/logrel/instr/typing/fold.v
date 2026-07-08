Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.substitution.
Require Import RichWasm.iris.logrel.env_props.
Require Import RichWasm.kinding_subst.

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
    (* subst τrec. *)
    inversion Hkind; subst.
    assert (Hkindτrec: has_kind F τrec κ) by by apply has_kind_rec_subst.
    destruct (refresh_kinds_id) as (this & _).
    assert (refresh_kinds F τrec = τrec) by (symmetry; by eapply this).
    assert (eval_kind se κ = Some sκ) as Hκ.
    {
      apply has_kind_inv in Hkindτrec as Hok_has.
      inversion Hok_has as [??? Hok_τ Hok_κ]; subst.
      clear Hok_has.
      destruct (eval_kind_ok_Some _ _ _ Hse Hok_κ) as [sκ_tosub Hsκ_T].
      rewrite Hsκ_T.
      f_equal.
      eapply type_skind_has_kind_agree; try done.
    }
    iExists sκ.
    iSplit; first eauto.
    iSplit; first eauto.

    cbn -[skind_rec_interp1].
    rewrite Hκ.
    pose proof (fixpoint_unfold (skind_rec_interp1 sκ (type_interp rti sr τ) se)) as Hunf.
    specialize (Hunf (SAtoms os)).
    rewrite Hunf.
    Opaque skind_has_svalue. Opaque senv_insert_type.
    unfold skind_rec_interp1. iEval (cbn -[add_skind_interp_closed]).
    Transparent senv_insert_type.
    iModIntro.
    unfold τrec in H.
    unfold τrec.
    rewrite <- H.
    pose proof (sem_well_formed_from_interp F se Hse) as HseF.


    iAssert (type_interp rti sr τ
               (senv_insert_type sκ sκ (value_interp rti sr se (RecT κ τ)) se) (SAtoms os))
    with "[Hval]" as "Hos". {
      iApply (type_interp_subst_type_backwards with "[$Hval]").
      1: exact mr.
      11: exact H3.
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
        apply this in H3.
        rewrite <- H3.
        done.
      - (* this is whatever the kinding admit above is *)
        rewrite H.
        exact Hkindτrec.
        Transparent skind_has_svalue.
    }

    pose proof (add_skind_interp_closed_equiv_value_interp rti sr sκ τ κ se Hκ).
    assert (Hproper: Proper (equiv ==> equiv) (type_interp rti sr τ)). {
      typeclasses eauto.
    }
    iApply Hproper.
    {
      apply senv_insert_type_proper.
      apply H0.
    }
    done.


  Qed.

End fold.
