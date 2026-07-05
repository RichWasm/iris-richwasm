Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.instr.typing.inst. (* TODO: import proper subst file when created *)
Require Import RichWasm.iris.logrel.env_props.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section unfold.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma has_kind_subst_stupid :
    (∀ τ F κ, let τrec := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
              has_kind F (RecT κ τ) κ -> has_kind F τrec κ) /\
      (∀ (ϕ :Core.function_type), True) /\ (∀ (iϕ:inner_function_type), True).
  Proof.
    apply type_and_function_ind; try done.
    all: repeat (intros ?).
    all: unfold τrec; cbn in *;
      match goal with
      | H: ( has_kind _ (RecT _ _) _ ) |- _ => inversion H; subst
      end.
    1: {
      destruct idx.
      + cbn.
        constructor. done.
      + cbn.
        inversion H4; subst.
        constructor; try done.
      }
    1: inversion H4; subst; try done; subst κ1; cbn; constructor.
    1: inversion H4; subst; cbn; try constructor.
    (* okay base cases are chill *)
    10: {
      inversion H5; subst.
      clear H3 H7.
      apply H in H5.
      subst τrec.
      rewrite instId'_kind.
      eapply KRec.
      cbn in H5.
      (* this seems probably true.. *)
      admit.
    }
  Admitted.

  Lemma has_kind_subst :
    (∀ τ F κ, let τrec := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
              has_kind F (RecT κ τ) κ -> has_kind F τrec κ).
  Proof. destruct has_kind_subst_stupid as (this & _). exact this. Admitted.

  (* copied: just because iApply was being annoying with doing the wrong
   direction *)
  Lemma type_interp_subst_type_forwards F F' se se' τ κ κ' sv sub_m sub_r sub_s sub_t :
    let τ' := refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ) in
    (sem_env_types_well_formed se') ->
    (sem_env_types_well_formed se) ->
    (sem_env_interp F' se') ->
    (sem_env_interp F se) ->
    (sem_env_rel_rep_eq se' se sub_r) ->
    (sem_env_rel_size_eq se' se sub_s) ->
    (sem_env_rel_mem_eq se' se sub_m) ->
    (sem_env_rel_sκ_eq se' se sub_t) ->
    (sem_env_rel_type_eq rti sr se' se sub_t) ->
    (∀ i, refresh_kinds F (sub_t i) = sub_t i) ->
    has_kind F' τ κ ->
    has_kind F τ' κ' ->
    (* type_eq_mod_kinds τ' (subst_type sub_m sub_r sub_s sub_t τ) -> *)
    type_interp rti sr τ se' sv -∗
    type_interp rti sr τ' se sv.
  Proof. Admitted.

  (* Note: the implicit hell below is because rocq can't figure out the contractive
   instances. In plain text, this lemma is the following:

  eval_kind se κ = Some sκ
  → add_skind_interp_closed sκ
      (fixpoint
         (λ T0 : leibnizO semantic_value -n> iPropO Σ,
            λne sv : leibnizO semantic_value,
            (▷ type_interp rti sr τ (se.1, (sκ, (sκ, add_skind_interp_closed sκ T0)) :: se.2) sv)%I))
    ≡ value_interp rti sr se (RecT κ τ)

   *)
  Lemma add_skind_interp_closed_equiv_value_interp sκ τ κ (se: semantic_env (Σ:=Σ)):
    eval_kind se κ = Some sκ ->
    (@add_skind_interp_closed Σ sκ)
    (@fixpoint natSI (leibnizO semantic_value -n> iPropO Σ)
       (@ofe_mor_cofe natSI (leibnizO semantic_value) (iPropO Σ) (@uPred_cofe (iResUR Σ)))
       (@ofe_mor_inhabited natSI (leibnizO semantic_value) (iPropO Σ) (@bi_inhabited (iPropI Σ)))
       (λ T0 : leibnizO semantic_value -n> iPropO Σ,
          λne sv : leibnizO semantic_value,
          (▷ (@type_interp Σ logrel_na_invs0 wasmG0 richwasmG0 rti sr τ)
               (senv_insert_type sκ sκ ((@add_skind_interp_closed Σ sκ) T0) se) sv)%I)
       (@skind_rec_interp1_contractive Σ sκ
          (@type_interp Σ logrel_na_invs0 wasmG0 richwasmG0 rti sr τ) se))
    ≡ (@value_interp Σ logrel_na_invs0 wasmG0 richwasmG0 rti sr) se (RecT κ τ).
  Proof.
    intros Hκ sv.
    rewrite value_interp_eq.
    iSplitR; iIntros "Hoa".
    + cbn.
      rewrite Hκ.
      iExists sκ.
      iSplitR; first done.
      done.
    + cbn.
      rewrite Hκ.
      iDestruct "Hoa" as "(%sκ_old & %toinv & this)".
      inversion toinv; subst.
      done.
  Qed.

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
    assert (Hkindτrec: has_kind F τrec κ) by by apply has_kind_subst.
    destruct (refresh_kinds_id rti sr mr) as (this & _).
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
      pose proof (add_skind_interp_closed_equiv_value_interp sκ τ κ se Hκ).
      (* I went through line by line and could only see the %I difference, but that shouldn't *)
      (* cause an issue..? I'm confused *)
      (* note that I did a pass through without doing this iAssert, and that would almost certainly
         also work, but just have the proof of add_skind-interp_closed_equiv_value_interp copied*)
      admit.
    }
    pose proof (sem_well_formed_from_interp F se Hse) as HseF.

    iApply (type_interp_subst_type_forwards with "[$Hos]").
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
  Admitted.

End unfold.
