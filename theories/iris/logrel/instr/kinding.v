(* Fundamental theorem for the kind system:
     well-kinded syntactic types are semantically well-kinded *)

From iris.proofmode Require Import base proofmode classes.
From RichWasm Require Import layout syntax typing kinding_subst.
From RichWasm.compiler Require Import prelude module codegen.
From RichWasm.iris Require Import autowp memory util wp_codegen lenient_wp logpred.
Require Import RichWasm.iris.logrel.
From stdpp Require Import list.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section kinding.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma semantic_type_le_refl (T : @semantic_type Σ) :
    T ⊑ T.
  Proof.
    by iIntros.
  Qed.

  Lemma semantic_type_le_trans (S T U : @semantic_type Σ) :
    S ⊑ T -> T ⊑ U -> S ⊑ U.
  Proof.
    iIntros (Hst Htu sv) "H".
    iApply Htu.
    by iApply Hst.
  Qed.

  Lemma type_kind_has_kind_is_Some F τ κ :
    has_kind F τ κ ->
    is_Some (type_kind F.(fc_type_vars) τ).
  Proof.
    induction 1; try solve [eexists; cbn; eauto].
    auto.
  Qed.

  Lemma type_kind_has_kind_agree F τ κ κ' :
    has_kind F τ κ ->
    type_kind F.(fc_type_vars) τ = Some κ' ->
    subkind_of κ' κ.
  Proof.
    intros Hhas_kind.
    revert κ'.
    induction Hhas_kind;
      intros;
      try (replace κ' with κ; first apply subkind_of_refl; cbn in *; congruence).
    apply IHHhas_kind in H0. by eapply subkind_of_trans.
  Qed.

  Lemma subkind_rep_inv κ κ' :
    subkind_of κ κ' ->
    kind_rep κ = kind_rep κ'.
  Proof.
    by induction 1.
  Qed.

  Lemma subkind_preserves_valtype κ ρ ξ :
    subkind_of κ (VALTYPE ρ ξ) ->
    exists ξ0, κ = VALTYPE ρ ξ0 /\ ref_flag_le ξ0 ξ.
  Proof.
    intros.
    inversion H.
    subst.
    by eexists.
  Qed.

  Lemma type_rep_has_kind_agree F τ ρ ξ :
    has_kind F τ (VALTYPE ρ ξ) ->
    type_rep F.(fc_type_vars) τ = Some ρ.
  Proof.
    intros Hhas_kind.
    unfold type_rep.
    destruct (type_kind_has_kind_is_Some _ _ _ Hhas_kind) as [κ' Htk].
    rewrite Htk; cbn.
    eapply type_kind_has_kind_agree in Htk; eauto.
    erewrite subkind_rep_inv by eauto.
    done.
  Qed.

  Lemma subkind_subskind (se : semantic_env (Σ:=Σ)) κ κ' sκ sκ' :
    eval_kind se κ = Some sκ ->
    eval_kind se κ' = Some sκ' ->
    subkind_of κ κ' ->
    subskind_of sκ sκ'.
  Proof.
    intros Heval_κ Heval_κ' Hsubk.
    destruct κ.
    - inversion Hsubk.
      subst.
      apply bind_Some in Heval_κ as (ιs & Hιs & Hsκ).
      apply bind_Some in Heval_κ' as (ιs' & Hιs' & Hsκ').
      inversion Hsκ.
      inversion Hsκ'.
      rewrite Hιs in Hιs'.
      inversion Hιs'.
      by constructor.
    - inversion Hsubk.
      subst.
      apply bind_Some in Heval_κ as (n & Hn & Hsκ).
      apply bind_Some in Heval_κ' as (n' & Hn' & Hsκ').
      inversion Hsκ.
      inversion Hsκ'.
      rewrite Hn in Hn'.
      inversion Hn'.
      by constructor.
  Qed.

  Lemma eval_rep_ok_Some F se ρ :
    sem_env_interp (Σ:=Σ) F se ->
    rep_ok F.(fc_kind_ctx) ρ ->
    is_Some (eval_rep se ρ).
  Proof.
    intros Hse Hok.
    induction ρ using rep_ind.
    - inversion Hok as [K n Hidx HK Hn| | |].
      subst K n.
      destruct Hse as [(_ & Hrepv & _) _].
      rewrite Hrepv in Hidx.
      apply list_lookup_lookup_total_lt in Hidx.
      by eexists.
    - inversion Hok as [|K ρs' Hρs HK Hρs'| |].
      subst K ρs'.
      pose proof (List.Forall_and H Hρs) as H'.
      clear H Hρs.
      apply Forall_impl with (Q := is_Some ∘ eval_rep se) in H'.
      + rewrite <- mapM_is_Some in H'. by apply fmap_is_Some.
      + intros ρ [Hsome ?]. by apply Hsome.
    - inversion Hok as [| |K ρs' Hρs HK Hρs'|].
      subst K ρs'.
      pose proof (List.Forall_and H Hρs) as H'.
      clear H Hρs.
      apply Forall_impl with (Q := is_Some ∘ eval_rep se) in H'.
      + rewrite <- mapM_is_Some in H'. by apply fmap_is_Some.
      + intros ρ [Hsome ?]. by apply Hsome.
    - done.
  Qed.

  Lemma eval_size_ok_Some F se σ :
    sem_env_interp (Σ:=Σ) F se ->
    size_ok F.(fc_kind_ctx) σ ->
    is_Some (eval_size se σ).
  Proof.
    intros Hse Hok.
    induction σ using size_ind.
    - inversion Hok as [K n Hidx HK Hn| | | |].
      subst K n.
      destruct Hse as [(_ & _ & Hsizev) _].
      rewrite Hsizev in Hidx.
      apply list_lookup_lookup_total_lt in Hidx.
      by eexists.
    - inversion Hok as [|K σs' Hσs HK Hσs'| | |].
      subst K σs'.
      pose proof (List.Forall_and H Hσs) as H'.
      clear H Hσs.
      apply Forall_impl with (Q := is_Some ∘ eval_size se) in H'.
      + rewrite <- mapM_is_Some in H'. by apply fmap_is_Some.
      + intros σ [Hsome ?]. by apply Hsome.
    - inversion Hok as [| |K σs' Hσs HK Hσs'| |].
      subst K σs'.
      pose proof (List.Forall_and H Hσs) as H'.
      clear H Hσs.
      apply Forall_impl with (Q := is_Some ∘ eval_size se) in H'.
      + rewrite <- mapM_is_Some in H'. by apply fmap_is_Some.
      + intros σ [Hsome ?]. by apply Hsome.
    - inversion Hok as [| | |K ρ' Hok_ρ HK Hρ'|].
      subst K ρ'.
      apply fmap_is_Some.
      by eapply eval_rep_ok_Some.
    - done.
  Qed.

  Lemma eval_kind_ok_Some F se κ :
    sem_env_interp (Σ:=Σ) F se ->
    kind_ok F.(fc_kind_ctx) κ ->
    is_Some (eval_kind se κ).
  Proof.
    intros Hse Hok.
    destruct κ as [ρ ξ|].
    - inversion Hok as [K ρ' ξ' Hok_ρ|].
      subst K ρ' ξ'.
      cbn.
      by eapply eval_rep_ok_Some in Hok_ρ as [ιs ->].
    - inversion Hok as [|K σ ξ Hok_σ].
      subst K σ ξ.
      cbn.
      by eapply eval_size_ok_Some in Hok_σ as [n ->].
  Qed.

  Lemma type_skind_has_kind_agree F se τ κ sκ sκ0 :
    has_kind F τ κ ->
    sem_env_interp F se ->
    eval_kind se κ = Some sκ ->
    type_skind (Σ:=Σ) se τ = Some sκ0 ->
    subskind_of sκ0 sκ.
  Proof.
    intros Hhas_kind.
    revert sκ0 sκ.
    induction Hhas_kind.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      inversion Heval_kind.
      apply subskind_of_refl.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      inversion Heval_kind.
      apply subskind_of_refl.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      inversion Heval_kind.
      apply subskind_of_refl.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      inversion Heval_kind.
      apply subskind_of_refl.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      inversion Heval_kind.
      apply subskind_of_refl.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      inversion Heval_kind.
      apply bind_Some in H1 as (ιs0 & Heval_rep0 & Hsκ0).
      apply bind_Some in H2 as (ιs & Heval_rep & Hsκ).
      inversion Hsκ0.
      inversion Hsκ.
      rewrite Heval_rep0 in Heval_rep.
      inversion Heval_rep.
      apply subskind_of_refl.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      inversion Heval_kind.
      apply bind_Some in H1 as (ιs0 & Heval_rep0 & Hsκ0).
      apply bind_Some in H2 as (ιs & Heval_rep & Hsκ).
      inversion Hsκ0.
      inversion Hsκ.
      rewrite Heval_rep0 in Heval_rep.
      inversion Heval_rep.
      apply subskind_of_refl.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      inversion Heval_kind.
      apply bind_Some in H1 as (ιs0 & Heval_rep0 & Hsκ0).
      apply bind_Some in H2 as (ιs & Heval_rep & Hsκ).
      inversion Hsκ0.
      inversion Hsκ.
      rewrite Heval_rep0 in Heval_rep.
      inversion Heval_rep.
      apply subskind_of_refl.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      inversion Heval_kind.
      apply bind_Some in H1 as (ιs0 & Heval_rep0 & Hsκ0).
      apply bind_Some in H2 as (ιs & Heval_rep & Hsκ).
      inversion Hsκ0.
      inversion Hsκ.
      rewrite Heval_rep0 in Heval_rep.
      inversion Heval_rep.
      apply subskind_of_refl.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      inversion Heval_kind.
      apply subskind_of_refl.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      inversion Heval_kind.
      apply subskind_of_refl.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      inversion Heval_kind.
      apply subskind_of_refl.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      inversion Heval_kind.
      apply bind_Some in H0 as (n0 & Heval_rep0 & Hsκ0).
      apply bind_Some in H1 as (n & Heval_rep & Hsκ).
      inversion Hsκ0.
      inversion Hsκ.
      rewrite Heval_rep0 in Heval_rep.
      inversion Heval_rep.
      apply subskind_of_refl.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      inversion Heval_kind.
      apply bind_Some in H1 as (ιs0 & Heval_rep0 & Hsκ0).
      apply bind_Some in H2 as (ιs & Heval_rep & Hsκ).
      inversion Hsκ0.
      inversion Hsκ.
      rewrite Heval_rep0 in Heval_rep.
      inversion Heval_rep.
      apply subskind_of_refl.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      inversion Heval_kind.
      apply bind_Some in H1 as (n0 & Heval_size0 & Hsκ0).
      apply bind_Some in H2 as (n & Heval_size & Hsκ).
      inversion Hsκ0.
      inversion Hsκ.
      rewrite Heval_size0 in Heval_size.
      inversion Heval_size.
      apply subskind_of_refl.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      rewrite Heval_kind in H0.
      inversion H0.
      apply subskind_of_refl.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      rewrite Heval_kind in H1.
      inversion H1.
      apply subskind_of_refl.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      rewrite Heval_kind in H1.
      inversion H1.
      apply subskind_of_refl.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      rewrite Heval_kind in H1.
      inversion H1.
      apply subskind_of_refl.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      rewrite Heval_kind in H2.
      inversion H2.
      apply subskind_of_refl.
    - intros ?? Hse Heval_kind Htype_skind.
      apply has_kind_inv in Hhas_kind as Hhas_kind_ok.
      inversion Hhas_kind_ok.
      subst.
      rename H0 into Htype_ok.
      rename H1 into Hkind_ok.
      destruct (eval_kind_ok_Some _ _ _ Hse Hkind_ok) as [sκ0' Hsκ0'].
      pose proof (subkind_subskind _ _ _ _ _ Hsκ0' Heval_kind H).
      pose proof (IHHhas_kind _ _ Hse Hsκ0' Htype_skind) as H'.
      by eapply subskind_of_trans.
    - intros ?? Hse Heval_kind Htype_skind.
      cbn in Htype_skind.
      replace sκ0 with sκ; first apply subskind_of_refl.
      destruct Hse as [boop bap].
      unfold type_ctx_interp in bap.
      unfold lookup_type in Htype_skind.
      apply fmap_Some in Htype_skind as (x & bofp & borzoi).
      pose proof (Forall2_lookup_lr _ _ _ _ _ _ bap bofp H) as [hh hhhh].
      subst sκ0.
      rewrite Heval_kind in hh.
      by inversion hh.
  Qed.

  Lemma type_skind_has_kind_Some F se τ κ sκ :
    has_kind F τ κ ->
    sem_env_interp F se ->
    eval_kind se κ = Some sκ ->
    (∃ sκ', type_skind (Σ:=Σ) se τ = Some sκ' /\ subskind_of sκ' sκ).
  Proof.
    intros Hκ.
    revert sκ se.
    induction Hκ; intros;
      try by (unfold κ in *; exists sκ; split; [cbn in *; done | by apply subskind_of_refl]).
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - destruct H1 as [boop bap].
      cbn in *.
      unfold lookup_type.
      unfold type_ctx_interp in bap.
      pose proof (Forall2_lookup_r _ _ _ _ _ bap H) as (x & Hinsenv & (y1 & y2)).
      destruct x as [sκ0 T].
      cbn in *.
      rewrite H2 in y1; inversion y1; subst.
      rewrite Hinsenv.
      cbn.
      exists sκ0. split; auto.
      apply subskind_of_refl.


  Admitted.

  Lemma ref_flag_atoms_refine ξ ξ' sv :
    ref_flag_le ξ ξ' ->
    ref_flag_atoms_interp ξ sv ->
    ref_flag_atoms_interp ξ' sv.
  Proof.
    intros Hle (os & -> & Hos).
    exists os.
    split; first done.
    eapply Forall_impl; first done.
    intros o Ho.
    by destruct o; first (destruct ξ; destruct ξ'; destruct p).
  Qed.

  Lemma ref_flag_words_refine ξ ξ' sv :
    ref_flag_le ξ ξ' ->
    ref_flag_words_interp ξ sv ->
    ref_flag_words_interp ξ' sv.
  Proof.
    intros Hle (ws & -> & Hws).
    exists ws.
    split; first done.
    eapply Forall_impl; first done.
    intros w Hw.
    by destruct w; first (destruct ξ; destruct ξ'; destruct p).
  Qed.

  Lemma skind_as_type_refine sκ0 sκ :
    subskind_of sκ0 sκ ->
    skind_as_type_interp (Σ:=Σ) sκ0 ⊑ skind_as_type_interp sκ.
  Proof.
    iIntros (Hsub sv) "Hskind".
    destruct sκ0 as [ιs ξ|n ξ].
    - inversion Hsub.
      subst.
      iDestruct "Hskind" as "[%Hareps %Hrf]".
      iPureIntro.
      split; first done.
      by eapply ref_flag_atoms_refine.
    - inversion Hsub.
      subst.
      iDestruct "Hskind" as "[%Hssize %Hrf]".
      iPureIntro.
      split; first done.
      by eapply ref_flag_words_refine.
  Qed.

  Theorem kinding_refinement F se τ κ sκ : 
    has_kind F τ κ ->
    sem_env_interp F se ->
    eval_kind se κ = Some sκ ->
    value_interp rti sr se τ ⊑ skind_as_type_interp sκ.
  Proof.
    iIntros (Hkind Hse Heval sv) "Hsv".
    rewrite value_interp_eq.
    iDestruct "Hsv" as "(%κ0 & %Hκ0 & H & _)".
    iApply skind_as_type_refine; last done.
    by eapply type_skind_has_kind_agree.
  Qed.

  Instance kind_as_type_persistent κ sv :
    @Persistent (iProp Σ) (skind_as_type_interp κ sv).
  Proof.
    destruct κ, sv; cbn; typeclasses eauto.
  Qed.

  Lemma value_interp_var se t sκ (T : semantic_type) :
    lookup_type se t = Some (sκ, T) ->
    value_interp rti sr se (VarT t) ≡ (λne sv, skind_as_type_interp sκ sv ∗ T sv)%I.
  Proof.
    rewrite value_interp_part_eq.
    cbn.
    unfold type_var_interp.
    unfold lookup.
    unfold lookup_type.
    intros.
    intros sv.
    rewrite !H.
    cbn.
    iSplit.
    - iIntros "(%κ' & %Hfind & Hkt & Htv)".
      inversion Hfind.
      iFrame.
    - eauto.
  Qed.

  Lemma prim_value_type ι v :
    has_prim ι v ->
    value_type_interp (translate_prim ι) v.
  Proof.
    intros H.
    by destruct ι; destruct v; try contradiction; eexists.
  Qed.

  Lemma prims_result_type ιs vs :
    has_prims ιs vs ->
    result_type_interp (map translate_prim ιs) vs.
  Proof.
    revert vs.
    induction ιs; intros.
    - cbn.
      unfold result_type_interp.
      intros.
      inversion H.
      constructor.
    - inversion H; cbn; subst.
      constructor; cbn; eauto.
      + apply prim_value_type; eauto.
      + eapply IHιs; eauto.
  Qed.

  Theorem kinding_sound F se τ κ sκ :
    has_kind F τ κ ->
    sem_env_interp F se ->
    eval_kind se κ = Some sκ ->
    skind_interp sκ (value_interp rti sr se τ).
  Proof.
    iIntros (Hhas_kind Hse Heval_kind sv) "Hval".
    rewrite value_interp_eq.
    iDestruct "Hval" as "(%sκ' & %Hsκ' & Hskind & Htype)".
    iApply skind_as_type_refine; last done.
    by eapply type_skind_has_kind_agree.
  Qed.

End kinding.
