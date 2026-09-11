Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.substitution.
Require Import RichWasm.iris.logrel.env_props.
Require Import RichWasm.kinding_subst.
Require Import RichWasm.kinding_scope.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section pack.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  (* Introducing one existential: the packed type is the body under the witness, so the value
     interpretation transports along the substitution lemma into the extended environment. *)
  Lemma type_interp_pack_mem F se μ κ κ0 τ sv :
    sem_env_interp F se ->
    kind_ok (fc_kind_ctx F) κ ->
    has_kind (add_mem_var F) τ κ ->
    has_kind F (subst_type (unscoped.scons μ VarM) VarR VarS VarT τ) κ0 ->
    type_interp rti sr (subst_type (unscoped.scons μ VarM) VarR VarS VarT τ) se sv -∗
    type_interp rti sr (ExistsMemT κ τ) se sv.
  Proof.
    intros Hse Hκ Hτ Hτ0.
    pose proof (proj1 refresh_kinds_id _ _ _ Hτ0) as Hrefresh.
    destruct (pack_mem_witness _ _ _ _ Hτ0) as (μ0 & Hμ0 & Heqsub).
    destruct (eval_mem_ok_Some _ _ _ Hse Hμ0) as [b Hb].
    destruct (proj1 has_kind_subst_refresh τ (unscoped.scons μ0 VarM) VarR VarS VarT
                _ _ _ (ctx_rel_inst_mem F μ0 Hμ0) Hτ) as (κ1 & Hsub & Hκ1).
    rewrite -Heqsub -Hrefresh in Hκ1.
    have Heqκ : κ1 = κ0.
    { pose proof (has_kind_type_kind _ _ _ Hκ1) as H1.
      pose proof (has_kind_type_kind _ _ _ Hτ0) as H0.
      rewrite H1 in H0; by injection H0. }
    subst κ1.
    rewrite instId'_kind in Hsub.
    destruct (eval_kind_ok_Some _ _ _ Hse Hκ) as [sκ Hsκ].
    iIntros "Hval".
    iPoseProof (type_interp_skind_svalue rti sr _ se sv with "Hval") as (sκ0) "[%Hsk0 %Hsv0]".
    iEval (rewrite type_interp_eq).
    iExists sκ.
    iSplit; [by cbn; rewrite Hsκ|].
    iSplit.
    { iPureIntro.
      eapply skind_as_type_refine; [|exact Hsv0].
      eapply subkind_subskind; [|exact Hsκ|exact Hsub].
      apply has_kind_inv in Hτ0 as Hok0.
      inversion Hok0 as [? ? ? Hτ0ok Hκ0ok]; subst.
      destruct (eval_kind_ok_Some _ _ _ Hse Hκ0ok) as [sκ0' Hsκ0'].
      rewrite Hsκ0'; f_equal.
      by eapply type_skind_has_kind_agree. }
    cbn.
    iExists b.
    have Hτ0eq : refresh_kinds F (subst_type (unscoped.scons μ0 VarM) VarR VarS VarT τ)
                 = subst_type (unscoped.scons μ VarM) VarR VarS VarT τ
      by rewrite -Heqsub -Hrefresh.
    iEval (rewrite -Hτ0eq) in "Hval".
    iApply (type_interp_subst_type_backwards rti sr F (add_mem_var F)
              se (senv_insert_mem b se) τ κ κ0 sv
              (unscoped.scons μ0 VarM) VarR VarS VarT with "[$Hval]").
    - by eapply sem_well_formed_from_interp, sem_env_insert_mem.
    - by eapply sem_well_formed_from_interp.
    - by apply sem_env_insert_mem.
    - done.
    - by intros i.
    - by intros i.
    - by intros [|i].
    - intros i; cbn; apply subskind_of_option_refl.
    - intros i.
      have Hwf : sem_env_types_well_formed se by eapply sem_well_formed_from_interp.
      exact (hsub_t_base_se_VarT rti sr se Hwf i).
    - by intros i.
    - done.
    - by rewrite Hτ0eq.
  Qed.

  Lemma type_interp_pack_rep F se ρ κ κ0 τ sv :
    sem_env_interp F se ->
    kind_ok (fc_kind_ctx F) κ ->
    has_kind (add_rep_var F) τ (ren_kind unscoped.shift unscoped.id κ) ->
    has_kind F (subst_type VarM (unscoped.scons ρ VarR) VarS VarT τ) κ0 ->
    type_interp rti sr (subst_type VarM (unscoped.scons ρ VarR) VarS VarT τ) se sv -∗
    type_interp rti sr (ExistsRepT κ τ) se sv.
  Proof.
    intros Hse Hκ Hτ Hτ0.
    destruct (pack_rep_witness _ _ _ _ Hτ0) as (ρ0 & Hρ0 & Heqsub).
    destruct (eval_rep_ok_Some _ _ _ Hse Hρ0) as [ιs Hιs].
    have Hkτ0 : has_kind F (subst_type VarM (unscoped.scons ρ VarR) VarS VarT τ) κ.
    { rewrite Heqsub -(subst_kind_scons_rep ρ0 κ).
      eapply (proj1 has_kind_subst_gen); [by intros n|by apply ctx_rel_inst_rep|done]. }
    destruct (eval_kind_ok_Some _ _ _ Hse Hκ) as [sκ Hsκ].
    iIntros "Hval".
    iPoseProof (type_interp_skind_svalue rti sr _ se sv with "Hval") as (sκ0) "[%Hsk0 %Hsv0]".
    have Heqsκ : sκ0 = sκ by symmetry; eapply type_skind_has_kind_agree.
    subst sκ0.
    iEval (rewrite type_interp_eq).
    iExists sκ.
    iSplit; [by cbn; rewrite Hsκ|].
    iSplit; [done|].
    cbn.
    iExists ιs.
    have Hτ0eq : refresh_kinds F (subst_type VarM (unscoped.scons ρ0 VarR) VarS VarT τ)
                 = subst_type VarM (unscoped.scons ρ VarR) VarS VarT τ.
    { rewrite -Heqsub; symmetry; by eapply (proj1 refresh_kinds_id). }
    iEval (rewrite -Hτ0eq) in "Hval".
    iApply (type_interp_subst_type_backwards rti sr F (add_rep_var F)
              se (senv_insert_rep ιs se) τ (ren_kind unscoped.shift unscoped.id κ) κ sv
              VarM (unscoped.scons ρ0 VarR) VarS VarT with "[$Hval]").
    - by eapply sem_well_formed_from_interp, sem_env_insert_rep.
    - by eapply sem_well_formed_from_interp.
    - by apply sem_env_insert_rep.
    - done.
    - by intros [|i].
    - by intros i.
    - by intros i.
    - intros i; cbn; apply subskind_of_option_refl.
    - intros i.
      have Hwf : sem_env_types_well_formed se by eapply sem_well_formed_from_interp.
      exact (hsub_t_base_se_VarT rti sr se Hwf i).
    - by intros i.
    - done.
    - by rewrite Hτ0eq.
  Qed.

  Lemma type_interp_pack_size F se σ κ κ0 τ sv :
    sem_env_interp F se ->
    kind_ok (fc_kind_ctx F) κ ->
    has_kind (add_size_var F) τ (ren_kind unscoped.id unscoped.shift κ) ->
    has_kind F (subst_type VarM VarR (unscoped.scons σ VarS) VarT τ) κ0 ->
    type_interp rti sr (subst_type VarM VarR (unscoped.scons σ VarS) VarT τ) se sv -∗
    type_interp rti sr (ExistsSizeT κ τ) se sv.
  Proof.
    intros Hse Hκ Hτ Hτ0.
    destruct (pack_size_witness _ _ _ _ Hτ0) as (σ0 & Hσ0 & Heqsub).
    destruct (eval_size_ok_Some _ _ _ Hse Hσ0) as [n Hn].
    have Hkτ0 : has_kind F (subst_type VarM VarR (unscoped.scons σ VarS) VarT τ) κ.
    { rewrite Heqsub -(subst_kind_scons_size σ0 κ).
      eapply (proj1 has_kind_subst_gen); [by intros m|by apply ctx_rel_inst_size|done]. }
    destruct (eval_kind_ok_Some _ _ _ Hse Hκ) as [sκ Hsκ].
    iIntros "Hval".
    iPoseProof (type_interp_skind_svalue rti sr _ se sv with "Hval") as (sκ0) "[%Hsk0 %Hsv0]".
    have Heqsκ : sκ0 = sκ by symmetry; eapply type_skind_has_kind_agree.
    subst sκ0.
    iEval (rewrite type_interp_eq).
    iExists sκ.
    iSplit; [by cbn; rewrite Hsκ|].
    iSplit; [done|].
    cbn.
    iExists n.
    have Hτ0eq : refresh_kinds F (subst_type VarM VarR (unscoped.scons σ0 VarS) VarT τ)
                 = subst_type VarM VarR (unscoped.scons σ VarS) VarT τ.
    { rewrite -Heqsub; symmetry; by eapply (proj1 refresh_kinds_id). }
    iEval (rewrite -Hτ0eq) in "Hval".
    iApply (type_interp_subst_type_backwards rti sr F (add_size_var F)
              se (senv_insert_size n se) τ (ren_kind unscoped.id unscoped.shift κ) κ sv
              VarM VarR (unscoped.scons σ0 VarS) VarT with "[$Hval]").
    - by eapply sem_well_formed_from_interp, sem_env_insert_size.
    - by eapply sem_well_formed_from_interp.
    - by apply sem_env_insert_size.
    - done.
    - by intros i.
    - by intros [|i].
    - by intros i.
    - intros i; cbn; apply subskind_of_option_refl.
    - intros i.
      have Hwf : sem_env_types_well_formed se by eapply sem_well_formed_from_interp.
      exact (hsub_t_base_se_VarT rti sr se Hwf i).
    - by intros i.
    - done.
    - by rewrite Hτ0eq.
  Qed.

  Lemma type_interp_pack_type F se τ_wit τ_in κ_wit κ_max κ_ex κ0 sv :
    let τ0 := refresh_kinds F (subst_type VarM VarR VarS (unscoped.scons τ_wit VarT) τ_in) in
    sem_env_interp F se ->
    has_kind F τ_wit κ_wit ->
    subkind_of κ_wit κ_max ->
    kind_ok (fc_kind_ctx F) κ_ex ->
    has_kind (add_type_var F κ_max) τ_in κ_ex ->
    has_kind F τ0 κ0 ->
    type_interp rti sr τ0 se sv -∗
    type_interp rti sr (ExistsTypeT κ_ex κ_max τ_in) se sv.
  Proof.
    intros τ0 Hse Hwit Hsubk Hκex Hτin Hτ0.
    apply has_kind_inv in Hwit as Hokwit.
    inversion Hokwit as [? ? ? Hwitok Hκwitok]; subst.
    have Hκmaxok : kind_ok (fc_kind_ctx F) κ_max by eapply kind_ok_subkind_of.
    destruct (eval_kind_ok_Some _ _ _ Hse Hκex) as [sκ_ex Hsκex].
    destruct (eval_kind_ok_Some _ _ _ Hse Hκwitok) as [sκ_wit Hsκwit].
    destruct (eval_kind_ok_Some _ _ _ Hse Hκmaxok) as [sκ_max Hsκmax].
    have Hsubsk : subskind_of sκ_wit sκ_max by eapply subkind_subskind.
    destruct (proj1 has_kind_subst_refresh τ_in VarM VarR VarS (unscoped.scons τ_wit VarT)
                _ _ _ (ctx_rel_inst_type F τ_wit κ_max κ_wit Hwit Hsubk) Hτin)
      as (κ1 & Hsub & Hκ1).
    have Heqκ : κ1 = κ0.
    { pose proof (has_kind_type_kind _ _ _ Hκ1) as H1.
      pose proof (has_kind_type_kind _ _ _ Hτ0) as H0.
      rewrite H1 in H0; by injection H0. }
    subst κ1.
    rewrite instId'_kind in Hsub.
    iIntros "Hval".
    iPoseProof (type_interp_skind_svalue rti sr _ se sv with "Hval") as (sκ0) "[%Hsk0 %Hsv0]".
    iEval (rewrite type_interp_eq).
    iExists sκ_ex.
    iSplit; [by cbn; rewrite Hsκex|].
    iSplit.
    { iPureIntro.
      eapply skind_as_type_refine; [|exact Hsv0].
      eapply subkind_subskind; [|exact Hsκex|exact Hsub].
      apply has_kind_inv in Hτ0 as Hok0.
      inversion Hok0 as [? ? ? Hτ0ok Hκ0ok]; subst.
      destruct (eval_kind_ok_Some _ _ _ Hse Hκ0ok) as [sκ0' Hsκ0'].
      rewrite Hsκ0'; f_equal.
      by eapply type_skind_has_kind_agree. }
    cbn.
    iExists (value_interp rti sr se τ_wit), sκ_max, sκ_wit.
    have Hstype : skind_has_stype sκ_wit (value_interp rti sr se τ_wit)
      by eapply kinding_sound.
    iSplit; [done|]; iSplit; [done|]; iSplit; [done|].
    iApply (type_interp_subst_type_backwards rti sr F (add_type_var F κ_max)
              se (senv_insert_type sκ_max sκ_wit (value_interp rti sr se τ_wit) se)
              τ_in κ_ex κ0 sv
              VarM VarR VarS (unscoped.scons τ_wit VarT) with "[$Hval]").
    - by eapply sem_well_formed_from_interp, sem_env_interp_insert_type.
    - by eapply sem_well_formed_from_interp.
    - by apply sem_env_interp_insert_type.
    - done.
    - by intros i.
    - by intros i.
    - by intros i.
    - intros [|i].
      + cbn -[type_skind].
        rewrite (type_skind_has_kind_Some F se τ_wit κ_wit sκ_wit Hwit Hse Hsκwit).
        exact Hsubsk.
      + cbn; apply subskind_of_option_refl.
    - intros [|i]; cbn; [done|].
      have Hwf : sem_env_types_well_formed se by eapply sem_well_formed_from_interp.
      exact (hsub_t_base_se_VarT rti sr se Hwf i).
    - intros [|i]; cbn; [|done].
      by symmetry; eapply (proj1 refresh_kinds_id).
    - done.
    - done.
  Qed.

  Lemma compat_pack M F L wt wt' wtf wl wl' wlf es' τ τ' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [τ] [τ'] in
    packed_existential F τ τ' ->
    has_instruction_type_ok M F ψ L ->
    run_codegen (compile_instr mr fe (IPack ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros *.
    intros Hpack Hty Hcg.
    cbn [compile_instr] in Hcg.
    cbn in Hcg.
    inversion Hcg; subst; clear Hcg.
    destruct Hty as [[Hmono1 Hmono2] _].
    rewrite Forall_cons_iff in Hmono1; destruct Hmono1 as [[ρ [Hrep _]] _].
    rewrite Forall_cons_iff in Hmono2; destruct Hmono2 as [[ρ' [Hrep' _]] _].
    inversion Hrep as [? ? ? ? Hkind]; subst.
    inversion Hrep' as [? ? ? ? Hkind']; subst.
    iApply sem_type_erased; first done.
    iIntros (se vs Hse) "Hex".
    rewrite !values_interp_one_eq !value_interp_eq -!type_interp_eq.
    inversion Hpack; subst.
    - inversion Hkind'; subst.
      by iApply (type_interp_pack_mem with "Hex").
    - inversion Hkind'; subst.
      by iApply (type_interp_pack_rep with "Hex").
    - inversion Hkind'; subst.
      by iApply (type_interp_pack_size with "Hex").
    - inversion Hkind'; subst.
      have Hτ0 : τ = refresh_kinds F (subst_type VarM VarR VarS (unscoped.scons τ_wit VarT) τ_in). {
        by apply refreshed_kinds_refresh.
      }
      rewrite Hτ0.
      rewrite Hτ0 in H1.
      by iApply (type_interp_pack_type with "Hex").
  Qed.

End pack.
