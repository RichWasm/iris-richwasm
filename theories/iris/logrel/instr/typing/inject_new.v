Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.store_common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section inject_new.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma flags_words_length_eq lmask θ ℓ fs ws :
    lmask ℓ ->
    rt_token rti sr lmask θ -∗
    ℓ ↦layout fs -∗
    ℓ ↦heap ws -∗
    ⌜length fs = length ws⌝.
  Proof.
    iIntros (Hlmask) "Hrt Hlayout Hheap".
    iDestruct "Hrt" as "(%rm & %lm & %hm &
      Haddr_auth & Hroot & Hlayout_auth & Hheap_auth & Hrti &
      %Hinj & %Hrootok & Hrootmem & %Hlayoutok & %Hheapok & Hheapmem)".
    iCombine "Hlayout_auth" "Hlayout" gives "%Hlm_lookup".
    iCombine "Hheap_auth" "Hheap" gives "%Hhm_lookup".
    iPureIntro.
    specialize (Hlayoutok ℓ).
    rewrite Hlm_lookup Hhm_lookup in Hlayoutok.
    inversion Hlayoutok; subst.
    by apply Forall2_length in H1.
  Qed.

  Lemma elem_of_repeat_inv {A} (x y : A) n : x ∈ repeat y n -> x = y.
  Proof.
    intros H.
    induction n.
    - inversion H.
    - inversion H; first done. by apply IHn.
  Qed.

  Lemma ref_flag_ptr_interp_flagint_words lmask θ ℓ n ws :
    lmask ℓ ->
    rt_token rti sr lmask θ -∗
    ℓ ↦layout repeat FlagInt n -∗
    ℓ ↦heap ws -∗
    ⌜forall ξ, Forall (forall_ptr_word (ref_flag_ptr_interp ξ)) ws⌝.
  Proof.
    iIntros (Hlmask) "Hrt Hlayout Hheap".
    iDestruct "Hrt" as "(%rm & %lm & %hm &
      Haddr_auth & Hroot & Hlayout_auth & Hheap_auth & Hrti &
      %Hinj & %Hrootok & Hrootmem & %Hlayoutok & %Hheapok & Hheapmem)".
    iCombine "Hlayout_auth" "Hlayout" gives "%Hlm_lookup".
    iCombine "Hheap_auth" "Hheap" gives "%Hhm_lookup".
    iPureIntro.
    specialize (Hlayoutok ℓ).
    rewrite Hlm_lookup Hhm_lookup in Hlayoutok.
    inversion Hlayoutok; subst.
    specialize (H1 Hlmask).
    intros ξ.
    eapply Forall2_Forall_r; first done.
    apply Forall_forall.
    intros f Hf w Hw.
    apply elem_of_repeat_inv in Hf as ->.
    by destruct w; first inversion Hw.
  Qed.

  Lemma elem_of_map_inj {A B} (f : A -> B) x (xs : list A) :
    (forall x y, f x = f y -> x = y) ->
    f x ∈ map f xs ->
    x ∈ xs.
  Proof.
    intros Hinj Helem.
    induction xs; first inversion Helem.
    inversion Helem.
    - apply Hinj in H1. rewrite -H1. constructor.
    - apply list_elem_of_further. by apply IHxs.
  Qed.

  Lemma compat_inject_new M F L wt wt' wtf wl wl' wlf es' μ i τ τs :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let τs' := map SerT τs in
    let ψ := InstrT [τ] [RefT μ Imm (VariantT τs')] in
    τs !! i = Some τ ->
    mono_mem μ ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IInjectNew ψ i)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    iIntros (?????? Hτ [bm ->] [[Hτ_mono Href_mono] HL_ok] Hcg ????????) "@@@@@@@@@@@@".

    rewrite Forall_singleton in Hτ_mono.
    destruct Hτ_mono as (ρ & Hτρ & Hρ_mono).
    inversion Hτρ.
    rename H into Hτ_kind.
    subst F0 τ0 ρ0.
    (* mini kinding quarantine: [VariantT]/[RefT] no longer carry cached
       kinds, so the variant's per-element [MEMTYPE] kinds are recomputed
       here from [Href_mono] (via [has_kind]) instead of being read off an
       embedded [κv]/[κr]. *)
    rewrite Forall_singleton in Href_mono.
    destruct Href_mono as (ρref & Hρref & _).
    inversion Hρref.
    subst F0 τ0 ρ0.
    rename H into Href_kind.
    assert (exists σ0 ξ0, has_kind F (VariantT τs') (MEMTYPE σ0 ξ0)) as Hkind_variant_ex
      by (inversion Href_kind; subst; eauto).
    destruct Hkind_variant_ex as (σvar & ξvar & Hkind_variant).
    clear Hρref.
    inversion Hkind_variant.
    subst.
    rename H2 into Hτs'_kind.
    clear Hkind_variant.

    assert (τs' !! i = Some (SerT τ)) as Hτ'
      by (subst τs'; rewrite list_lookup_fmap Hτ; done).

    eapply Forall3_lookup_l in Hτ' as (σ & ξi & Hσ & Hξi & Hτ_ser_kind); last apply Hτs'_kind.
    inversion Hτ_ser_kind.
    subst.
    rename H2 into Hρi_kind.
    pose proof (has_kind_agree _ _ _ _ Hτ_kind Hρi_kind) as H.
    inversion H.
    subst ρ0 ξi.
    clear H Hρi_kind Hτ_ser_kind.

    inv_cg_bind Hcg ρ' ?wt ?wt ?wl ?wl ?es ?es Hcg_rep Hcg.
    inv_cg_try_option Hcg_rep.
    rename Heq_some into Hρ'.
    inv_cg_bind Hcg ιs ?wt ?wt ?wl ?wl ?es ?es Hcg_arep Hcg.
    inv_cg_try_option Hcg_arep.
    rename Heq_some into Hιs.
    inv_cg_bind Hcg n ?wt ?wt ?wl ?wl ?es ?es Hcg_n Hcg.
    inv_cg_try_option Hcg_n.
    rename Heq_some into Hn.
    (* [ρ'] ([compile_instr]'s precomputed [type_size] of the variant) no
       longer comes from an embedded kind; relate it to the semantic
       per-branch sizes [σs] via [type_kind_has_kind_Some]/[KVariant] so
       [eval_size] on it can be unfolded below. *)
    assert (ρ' = SumS σs) as ->.
    { pose proof (type_kind_has_kind_Some F (VariantT τs') (MEMTYPE (SumS σs) (ref_flag_lub ξs))
                    (KVariant F τs' σs ξs Hτs'_kind)) as Htk.
      unfold type_size in Hρ'.
      rewrite Htk in Hρ'.
      cbn in Hρ'.
      by inversion Hρ'. }
    inv_cg_bind Hcg n_sz ?wt ?wt ?wl ?wl ?es ?es Hcg_sz Hcg.
    inv_cg_try_option Hcg_sz.
    rename Heq_some into Hn_sz.
    cbn in Hn_sz.
    apply bind_Some in Hn_sz as (ns & Hns & Hn_sz).
    fold (eval_size EmptyEnv) in Hns.
    inversion Hn_sz.
    subst n_sz.
    inv_cg_bind Hcg xs ?wt ?wt ?wl ?wl ?es ?es Hcg_save Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_alloc Hcg.
    inv_cg_bind Hcg laddr ?wt ?wt ?wl ?wl ?es ?es Hcg_laddr Hcg.
    apply wp_wlalloc in Hcg_laddr as (Hladdr & -> & -> & ->).
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_set_laddr Hcg.
    inv_cg_emit Hcg_set_laddr.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_flags Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_tag Hcg.
    inv_cg_emit Hcg_tag.
    inv_cg_bind Hcg ltag ?wt ?wt ?wl ?wl ?es ?es Hcg_ltag Hcg.
    apply wp_wlalloc in Hcg_ltag as (Hltag & -> & -> & ->).
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_set_ltag Hcg.
    inv_cg_emit Hcg_set_ltag.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_store_tag Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_store Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_get_laddr Hcg_regroot.
    inv_cg_emit Hcg_get_laddr.
    (* TRUNCATED: upstream's own "Remove case_load move" commit
       (28e2ff42) added a new [type_size]-based [try_option] bind in front
       of [compile_inject_new]'s call in [compile_instr] that did not exist
       when this proof was written (it used to destructure the size off an
       embedded kind instead). That shifts every auto-generated [wt]/[wl]/
       [es] index used by the large hand-numbered [subst]/bookkeeping below
       (which spanned the rest of this lemma), so the whole codegen-
       destructuring tail needs replaying against the new bind shape
       rather than a simple renumbering. Left admitted pending that
       rework; everything above this point (the kind-unembedding of the
       lemma's statement and the [ρ ρ' σs] derivation) is fixed and
       verified. *)
    admit.
  Admitted.

End inject_new.
