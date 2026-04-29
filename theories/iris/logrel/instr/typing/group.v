Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section group.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_group M F L wt wt' wtf wl wl' wlf es' τs κ :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT τs [ProdT κ τs] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IGroup ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    iIntros (????? Hok Hcg ????????) "@@@@@@@@@@@@".
    inv_cg_emit Hcg.
    subst ψ WT WL wt' wl' es'.
    clear Hretval.
    clear_nils.
    iApply cwp_val_app; first done.
    iApply (cwp_nop with "[$] [$]").
    iModIntro.
    unfold fvs_combine.
    rewrite app_nil_r.
    iFrame.
    iSplitR; first done.
    iDestruct "Hos" as "(% & -> & Hos)".
    iExists [concat oss].
    iSplitR.
    { cbn. by rewrite app_nil_r. }
    iApply big_sepL2_singleton.
    iApply value_interp_eq.

    inversion Hok as [F' ψ L' Hmono Hok_L].
    subst F' ψ L'.
    inversion Hmono as [Hmono1 Hmono2].
    rewrite Forall_singleton in Hmono2.
    inversion Hmono2 as [F' τ ρ Hrep Hmono_ρ].
    subst F' τ.
    inversion Hrep as [F' τ ρ' ξ Hkind].
    subst F' τ ρ'.
    apply has_kind_inv in Hkind as Hok_has_kind.
    inversion Hok_has_kind as [F' τ κ' Hok_prod Hok_kind].
    subst F' τ κ'.
    inversion Hok_prod.
    subst F0 κ0 τs0.
    rename H2 into Hok_κ.
    rename H3 into Hok_τs.
    destruct (eval_kind_ok_Some _ _ _ Hse Hok_κ) as [sκ Hsκ].
    iExists sκ.

    assert (Hsub : subkind_of κ (VALTYPE ρ ξ)) by by eapply type_kind_has_kind_agree.
    apply subkind_preserves_valtype in Hsub as (ξ0 & -> & Hξ0).
    apply bind_Some in Hsκ as (ιs & Hιs & Hsκ).
    inversion Hsκ.
    subst sκ.
    clear Hsκ.

    apply has_kind_prod_inv in Hkind as (ρs & ξ' & Hsub & Hkinds).
    inversion Hsub.
    subst ρ ξ0.
    clear Hsub.

    apply bind_Some in Hιs as (ιss & Hιss & Hιs).
    inversion Hιs.
    subst ιs.
    clear Hιs.
    fold (eval_rep se) in Hιss.

    iDestruct (big_sepL2_value_interp_skind with "Hos") as "%Hskinds".

    iSplitR; last iSplitR.
    - iPureIntro. cbn. by rewrite Hιss.
    - iPureIntro. split.
      (* TODO: Very messy. Clean up with helper lemmas. *)
      + eexists.
        split; first done.
        apply mapM_Some in Hιss.
        apply Forall2_length in Hιss as Hlen_ρs_ιss.
        apply Forall2_length in Hkinds as Hlen_τs_ρs.
        apply Forall2_length in Hskinds as Hlen_τs_oss.
        apply Forall2_concat.
        apply Forall2_lookup.
        intros i.
        destruct (ιss !! i) eqn:Hιss_i.
        * assert (i < length ιss).
          { apply lookup_lt_is_Some. by eexists. }
          assert (is_Some (oss !! i)).
          {
            apply lookup_lt_is_Some.
            rewrite <- Hlen_τs_oss.
            rewrite Hlen_τs_ρs.
            by rewrite Hlen_ρs_ιss.
          }
          destruct H0 as [os Hoss_i].
          rewrite Hoss_i.
          apply Some_Forall2.
          assert (is_Some (τs !! i)).
          { apply lookup_lt_is_Some. rewrite Hlen_τs_ρs. by rewrite Hlen_ρs_ιss. }
          destruct H0 as [τ Hτs_i].
          assert (is_Some (ρs !! i)).
          { apply lookup_lt_is_Some. by rewrite Hlen_ρs_ιss. }
          destruct H0 as [ρ Hρs_i].
          rewrite Forall2_lookup in Hskinds.
          specialize (Hskinds i).
          rewrite Hτs_i in Hskinds.
          rewrite Hoss_i in Hskinds.
          inversion Hskinds as [τ' os' (sκ & Hskind & Hsvalue)|].
          subst τ' os'.
          rewrite Forall2_lookup in Hιss.
          specialize (Hιss i).
          rewrite Hρs_i in Hιss.
          rewrite Hιss_i in Hιss.
          inversion Hιss as [ρ' ιs Hιss'|].
          subst ρ' l.
          clear Hιss.
          destruct sκ.
          2: { inversion Hsvalue. inversion H0. }
          destruct Hsvalue as (Hareps & os' & Hos' & Hrfinterp).
          inversion Hos'.
          subst os'.
          clear Hos'.
          destruct Hareps as (os' & Hos' & Hareps).
          inversion Hos'.
          subst os'.
          clear Hos'.
          rewrite Forall2_lookup in Hkinds.
          specialize (Hkinds i).
          rewrite Hτs_i in Hkinds.
          rewrite Hρs_i in Hkinds.
          inversion Hkinds as [τ' ρ' Hkind|].
          subst τ' ρ'.
          clear Hkinds.
          pose proof (type_skind_eval_rep _ _ _ _ _ _ _ _ Hkind Hse Hιss' Hskind) as Hyeah.
          inversion Hyeah.
          by subst.
        * apply lookup_ge_None in Hιss_i.
          rewrite <- Hlen_ρs_ιss in Hιss_i.
          rewrite <- Hlen_τs_ρs in Hιss_i.
          rewrite Hlen_τs_oss in Hιss_i.
          apply lookup_ge_None in Hιss_i.
          rewrite Hιss_i.
          constructor.
      + eexists.
        split; first done.
        apply Forall2_length in Hkinds as Hlen_τs_ρs.
        apply Forall2_length in Hskinds as Hlen_τs_oss.
        apply Forall_concat.
        eapply Forall2_Forall_r; first done.
        apply Forall_forall.
        intros τ Hτ os (sκ & Hsκ & Hsvalue).
        destruct sκ.
        2: { inversion Hsvalue. inversion H. }
        destruct Hsvalue as [Hareps (os' & Hos' & Hrfs)].
        inversion Hos'.
        subst os'.
        clear Hos'.
        eapply Forall_impl; first done.
        intros o Ho.
        destruct o; try done.
        cbn.
        cbn in Ho.
        destruct p; first by destruct ξ'.
        apply list_elem_of_lookup in Hτ as [i Hτs_i].
        rewrite Forall2_lookup in Hkinds.
        specialize (Hkinds i).
        rewrite Hτs_i in Hkinds.
        assert (is_Some (ρs !! i)).
        { apply lookup_lt_is_Some. rewrite <- Hlen_τs_ρs. apply lookup_lt_is_Some. by eexists. }
        destruct H as [ρ Hρs_i].
        rewrite Hρs_i in Hkinds.
        inversion Hkinds as [τ' ρ' Hkind|].
        subst τ' ρ'.
        clear Hkinds.
        apply mapM_Some in Hιss.
        apply Forall2_length in Hιss as Hlen_ρs_ιss.
        rewrite Forall2_lookup in Hιss.
        specialize (Hιss i).
        rewrite Hρs_i in Hιss.
        assert (is_Some (ιss !! i)).
        { apply lookup_lt_is_Some. rewrite <- Hlen_ρs_ιss. rewrite <- Hlen_τs_ρs.
          apply lookup_lt_is_Some. by eexists. }
        destruct H as [ιs Hιss_i].
        rewrite Hιss_i in Hιss.
        inversion Hιss as [ρ' ιs' Hrep'|].
        subst ρ' ιs'.
        clear Hιss.
        pose proof (type_skind_eval_rep _ _ _ _ _ _ _ _ Hkind Hse Hrep' Hsκ) as Hyeah.
        inversion Hyeah.
        subst.
        by eapply ref_flag_interp_le.
    - iExists oss.
      iSplitR; first done.
      iApply (big_sepL2_impl with "[$]").
      iModIntro.
      by iIntros.
  Qed.

End group.
