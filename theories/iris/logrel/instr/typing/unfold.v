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
    pose proof (fixpoint_unfold (skind_rec_interp1 sκ (type_interp rti sr τ) se)) as Hunf.
    specialize (Hunf (SAtoms os)).
    rewrite Hunf.
    unfold skind_rec_interp1. iEval (cbn) in "Hos".
    iModIntro.
    inversion Hkind; subst.
    assert (refresh_kinds F τrec = τrec). {
      (* I need to prove has_kind F τrec for some κ'. subst κ? *)
      (* I'm unsure if that's true, but maybe *)
      admit.
    }
    unfold τrec in H0.
    rewrite <- H0.
    pose proof (sem_well_formed_from_interp F se Hse) as HseF.
    iApply (type_interp_subst_type_forwards with "[$Hos]").
    11: exact H4.
    1-9: try done.
    - unfold sem_env_types_well_formed in *.
      apply Forall_cons; split; try exact HseF.
      split; first apply subskind_of_refl.
      (* RYAN: from what you know of kinding, is this true? *)
      admit.
    - apply sem_env_interp_insert_type; try done; first apply subskind_of_refl.
      (* exactly the same as in the previous admit.  *)
      admit.
    - unfold sem_env_rel_sκ_eq.
      intros i. destruct i; cbn; last apply subskind_of_option_refl.
      rewrite Hκ. apply subskind_of_option_refl.
    - unfold sem_env_rel_type_eq.
      intros i; destruct i; cbn.
      2: {
        Opaque type_skind. Opaque skind_has_svalue.
        rewrite value_interp_eq_no_sv; cbn.
        Transparent type_skind. Transparent skind_has_svalue.
        (* this is fine because of Hse relating snd snd se.2 to sk *)
        admit.
      }
      (* hm this is suspicious. is this true? it's a different shape than
        it used to be, so maybe it is *)
      admit.
    - intros i; destruct i; try done.
      cbn.
      pose proof (refresh_kinds_id rti sr mr) as (this & _).
      apply this in H4.
      rewrite <- H4.
      done.
    - (* this is whatever the kinding admit above is *)
      admit.
  Admitted.

End unfold.
