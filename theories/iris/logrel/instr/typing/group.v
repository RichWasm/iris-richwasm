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

  Lemma big_sepL2_value_interp_skind se τs oss :
    ([∗ list] τ;os ∈ τs;oss, value_interp rti sr se τ (SAtoms os)) -∗
    ⌜Forall2 (fun τ os => exists sκ, type_skind se τ = Some sκ /\ svalue_in_skind (SAtoms os) sκ) τs oss⌝.
  Proof.
    iIntros "H".
    rewrite Forall2_same_length_lookup.
    rewrite <- big_sepL2_pure.
    iDestruct (big_sepL2_length with "H") as "%Hlen".
    iApply (big_sepL2_wand with "[$]").
    iApply big_sepL2_intro; first done.
    iIntros "!> %k %τ %os %Hτ %Hos H".
    setoid_rewrite value_interp_eq.
    iDestruct "H" as "(% & %Hskind & %Hsvalue & _)".
    iPureIntro.
    by eexists.
  Qed.

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
    subst ρ0 ρ ξ1 ξ'0.
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
      + eexists.
        split; first done.
        admit.
      + eexists.
        split; first done.
        admit.
    - iExists oss.
      iSplitR; first done.
      iApply (big_sepL2_impl with "[$]").
      iModIntro.
      by iIntros.
  Admitted.

End group.
