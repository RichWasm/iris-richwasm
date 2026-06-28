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

  Lemma ref_flag_ptr_interp_le ξ ξ' p :
    ref_flag_le ξ' ξ ->
    ref_flag_ptr_interp ξ' p ->
    ref_flag_ptr_interp ξ p.
  Proof.
    intros Hle Hinterp.
    by destruct ξ; destruct ξ'; destruct p.
  Qed.

  Lemma type_kind_has_kind_is_Some F τ κ :
    has_kind F τ κ ->
    is_Some (type_kind F.(fc_type_vars) τ).
  Proof.
    induction 1; try solve [eexists; cbn; eauto].
  Qed.

  Lemma type_kind_has_kind_agree F τ κ κ' :
    has_kind F τ κ ->
    type_kind F.(fc_type_vars) τ = Some κ' ->
    κ = κ'.
  Proof.
    intros Hκ Hτ.
    inversion Hκ; subst; inversion Hτ; try done.
    rewrite H in H2.
    by inversion H2.
  Qed.

  Lemma has_kind_agree F τ κ κ' :
    has_kind F τ κ →
    has_kind F τ κ' →
    κ = κ'.
  Proof.
    intros H1 H2.
    have Hsome := type_kind_has_kind_is_Some _ _ _ H1.
    destruct Hsome as [κ'' Hκ''].
    have Hsub1 := type_kind_has_kind_agree _ _ _ _ H1 Hκ''.
    have Hsub2 := type_kind_has_kind_agree _ _ _ _ H2 Hκ''.
    by rewrite Hsub2.
  Qed.

  Lemma has_kind_agree_f F τ ρ ξ σ ξ' :
    has_kind F τ (VALTYPE ρ ξ) →
    has_kind F τ (MEMTYPE σ ξ') →
    False.
  Proof.
    intros H1 H2.
    have H := has_kind_agree _ _ _ _ H1 H2.
    inversion H.
  Qed.

  Lemma subkind_rep_inv κ κ' :
    subkind_of κ κ' ->
    kind_rep κ = kind_rep κ'.
  Proof.
    by induction 1.
  Qed.

  Lemma subkind_size_inv κ κ' :
    subkind_of κ κ' ->
    kind_size κ = kind_size κ'.
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

  Lemma has_kind_ref_ty F κ κ' μ β τ :
    has_kind F (RefT κ μ β τ) κ' ->
    ∃ σ ξ,
      has_kind F τ (MEMTYPE σ ξ).
  Proof.
    intros Hkind.
    remember (RefT κ μ β τ) as τ0 eqn:Href.
    revert Href.
    revert κ μ.
    induction Hkind; intros κ'' μ' Href;
      try congruence.
    - subst κ. inversion Href; subst.
      by exists σ, ξ.
    - subst κ.
      inversion Href.
      subst.
      by exists σ, ξ.
    - subst κ.
      inversion Href.
      subst.
      by exists σ, ξ.
  Qed.

  Lemma eval_rep_empty_ok_Some ρ :
    rep_ok kc_empty ρ ->
    is_Some (eval_rep EmptyEnv ρ).
  Proof.
    intros Hok.
    induction ρ using rep_ind.
    - inversion Hok as [K n Hidx HK Hn| | |].
      cbn in *; lia.
    - inversion Hok as [|K ρs' Hρs HK Hρs'| |].
      subst K ρs'.
      pose proof (List.Forall_and H Hρs) as H'.
      clear H Hρs.
      apply Forall_impl with (Q := is_Some ∘ eval_rep EmptyEnv) in H'.
      + rewrite <- mapM_is_Some in H'. by apply fmap_is_Some.
      + intros ρ [Hsome ?]. by apply Hsome.
    - inversion Hok as [| |K ρs' Hρs HK Hρs'|].
      subst K ρs'.
      pose proof (List.Forall_and H Hρs) as H'.
      clear H Hρs.
      apply Forall_impl with (Q := is_Some ∘ eval_rep EmptyEnv) in H'.
      + rewrite <- mapM_is_Some in H'. by apply fmap_is_Some.
      + intros ρ [Hsome ?]. by apply Hsome.
    - done.
  Qed.

  Lemma eval_size_empty_ok_Some σ :
    size_ok kc_empty σ ->
    is_Some (eval_size EmptyEnv σ).
  Proof.
    induction σ using size_ind; intros Hok.
    - inversion Hok. cbn in *; lia.
    - inversion Hok as [|K σs' Hσs HK Hσs'| | |].
      subst K σs'.
      pose proof (List.Forall_and H Hσs) as H'.
      clear H Hσs.
      apply Forall_impl with (Q := is_Some ∘ eval_size EmptyEnv) in H'.
      + rewrite <- mapM_is_Some in H'. by apply fmap_is_Some.
      + intros σ [Hsome ?]. by apply Hsome.
    - inversion Hok as [| |K σs' Hσs HK Hσs'| |].
      subst K σs'.
      pose proof (List.Forall_and H Hσs) as H'.
      clear H Hσs.
      apply Forall_impl with (Q := is_Some ∘ eval_size EmptyEnv) in H'.
      + rewrite <- mapM_is_Some in H'. by apply fmap_is_Some.
      + intros σ [Hsome ?]. by apply Hsome.
    - inversion Hok as [| | |K ρ' Hok_ρ HK Hρ'|].
      subst K ρ'.
      apply fmap_is_Some.
      by eapply eval_rep_empty_ok_Some.
    - done.
  Qed.

  Lemma has_mono_size_inv F τ :
    has_mono_size F τ ->
    ∃ σ ξ k,
      is_mono_size σ /\
      has_kind F τ (MEMTYPE σ ξ) /\
      eval_size EmptyEnv σ = Some k.
  Proof.
    intros Hmono.
    inversion Hmono as [F' τ' σ ξ Hkind Hsz HF' Hτ'].
    subst F' τ'.
    pose proof Hsz as Hev.
    unfold is_mono_size in Hev.
    eapply eval_size_empty_ok_Some in Hev.
    destruct Hev as [k Hev].
    repeat eexists; eauto.
  Qed.

  Lemma mono_size_eval_emp_Some σ :
    is_mono_size σ ->
    is_Some (eval_size EmptyEnv σ).
  Proof.
    intros Hmono.
    induction σ using size_ind; inversion Hmono; subst.
    - cbn in H1; lia.
    - cbn.
      rewrite !Forall_forall in H H2.
      assert (is_Some (mapM (eval_size EmptyEnv) σs)) as (ns & ->); last done.
      eapply mapM_is_Some_2, Forall_forall; intros; cbn.
      eapply H; try eapply H2; eauto.
    - cbn.
      rewrite !Forall_forall in H H2.
      assert (is_Some (mapM (eval_size EmptyEnv) σs)) as (ns & ->); last done.
      eapply mapM_is_Some_2, Forall_forall; intros; cbn.
      eapply H; try eapply H2; eauto.
    - cbn.
      eapply eval_rep_empty_ok_Some in H1.
      by destruct H1 as (rep & ->).
    - done.
  Qed.

  Lemma type_rep_has_kind_agree F τ ρ ξ :
    has_kind F τ (VALTYPE ρ ξ) ->
    type_rep F.(fc_type_vars) τ = Some ρ.
  Proof.
    intros Hκ.
    apply bind_Some.
    apply type_kind_has_kind_is_Some in Hκ as Htype_kind.
    destruct Htype_kind as [κ' Hκ'].
    eexists.
    split; first done.
    by pose proof (type_kind_has_kind_agree _ _ _ _ Hκ Hκ') as <-.
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

  Lemma type_skind_has_kind_agree F se τ κ sκ sκ' :
    has_kind F τ κ ->
    sem_env_interp F se ->
    eval_kind se κ = Some sκ ->
    type_skind (Σ:=Σ) se τ = Some sκ' ->
    sκ = sκ'.
  Proof.
    intros Hhas_kind.
    revert sκ sκ'.
    induction Hhas_kind.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      by inversion Heval_kind.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      by inversion Heval_kind.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      by inversion Heval_kind.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      by inversion Heval_kind.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      by inversion Heval_kind.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      inversion Heval_kind.
      apply bind_Some in H1 as (ιs0 & Heval_rep0 & Hsκ0).
      apply bind_Some in H2 as (ιs & Heval_rep & Hsκ).
      inversion Hsκ0.
      inversion Hsκ.
      rewrite Heval_rep0 in Heval_rep.
      by inversion Heval_rep.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      inversion Heval_kind.
      apply bind_Some in H1 as (ιs0 & Heval_rep0 & Hsκ0).
      apply bind_Some in H2 as (ιs & Heval_rep & Hsκ).
      inversion Hsκ0.
      inversion Hsκ.
      rewrite Heval_rep0 in Heval_rep.
      by inversion Heval_rep.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      inversion Heval_kind.
      apply bind_Some in H1 as (ιs0 & Heval_rep0 & Hsκ0).
      apply bind_Some in H2 as (ιs & Heval_rep & Hsκ).
      inversion Hsκ0.
      inversion Hsκ.
      rewrite Heval_rep0 in Heval_rep.
      by inversion Heval_rep.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      inversion Heval_kind.
      apply bind_Some in H1 as (ιs0 & Heval_rep0 & Hsκ0).
      apply bind_Some in H2 as (ιs & Heval_rep & Hsκ).
      inversion Hsκ0.
      inversion Hsκ.
      rewrite Heval_rep0 in Heval_rep.
      by inversion Heval_rep.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      by inversion Heval_kind.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      by inversion Heval_kind.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      by inversion Heval_kind.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      by inversion Heval_kind.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      inversion Heval_kind.
      apply bind_Some in H0 as (n0 & Heval_rep0 & Hsκ0).
      apply bind_Some in H1 as (n & Heval_rep & Hsκ).
      inversion Hsκ0.
      inversion Hsκ.
      rewrite Heval_rep0 in Heval_rep.
      by inversion Heval_rep.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      inversion Heval_kind.
      apply bind_Some in H1 as (ιs0 & Heval_rep0 & Hsκ0).
      apply bind_Some in H2 as (ιs & Heval_rep & Hsκ).
      inversion Hsκ0.
      inversion Hsκ.
      rewrite Heval_rep0 in Heval_rep.
      by inversion Heval_rep.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      inversion Heval_kind.
      apply bind_Some in H1 as (n0 & Heval_size0 & Hsκ0).
      apply bind_Some in H2 as (n & Heval_size & Hsκ).
      inversion Hsκ0.
      inversion Hsκ.
      rewrite Heval_size0 in Heval_size.
      by inversion Heval_size.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      rewrite Heval_kind in H0.
      by inversion H0.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      rewrite Heval_kind in H1.
      by inversion H1.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      rewrite Heval_kind in H1.
      by inversion H1.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      rewrite Heval_kind in H1.
      by inversion H1.
    - intros ?? Hse Heval_kind Htype_skind.
      inversion Htype_skind.
      rewrite Heval_kind in H2.
      by inversion H2.
    - intros ?? Hse Heval_kind Htype_skind.
      cbn in Htype_skind.
      destruct Hse as [boop bap].
      unfold type_ctx_interp in bap.
      unfold lookup_type in Htype_skind.
      apply fmap_Some in Htype_skind as ([sκ_T T] & bofp & borzoi).
      pose proof (Forall2_lookup_lr _ _ _ _ _ _ bap H bofp) as [hh hhhh].
      subst sκ'.
      rewrite Heval_kind in hh.
      by inversion hh.
  Qed.

  Lemma type_skind_has_kind_Some F se τ κ sκ :
    has_kind F τ κ ->
    sem_env_interp F se ->
    eval_kind se κ = Some sκ ->
    type_skind (Σ:=Σ) se τ = Some sκ.
  Proof.
    intros Hκ Hse Hsκ.
    generalize dependent sκ.
    induction Hκ; intros ??; try by cbn in *.
    inversion Hse as [_ Htype_ctx].
    unfold type_ctx_interp in Htype_ctx.
    pose proof (Forall2_lookup_l _ _ _ _ _ Htype_ctx H) as [[sκ_T T] (Ht & Hsκ_T & _)].
    cbn.
    cbn in Ht.
    rewrite Ht.
    by rewrite Hsκ in Hsκ_T.
  Qed.

  Lemma ref_flag_atoms_refine ξ ξ' sv :
    ref_flag_le ξ ξ' ->
    ref_flag_atoms_interp ξ sv ->
    ref_flag_atoms_interp ξ' sv.
  Proof.
    intros Hle Hos.
    destruct sv as [os | ]; cbn in Hos; last tauto.
    eapply Forall_impl; first done.
    intros o Ho.
    by destruct o; first (destruct ξ; destruct ξ'; destruct p).
  Qed.

  Lemma ref_flag_words_refine ξ ξ' sv :
    ref_flag_le ξ ξ' ->
    ref_flag_words_interp ξ sv ->
    ref_flag_words_interp ξ' sv.
  Proof.
    intros Hle Hws.
    destruct sv; cbn in Hws; first done.
    eapply Forall_impl; first done.
    intros w Hw.
    by destruct w; first (destruct ξ; destruct ξ'; destruct p).
  Qed.

  Lemma skind_as_type_refine sκ0 sκ :
    subskind_of sκ0 sκ ->
    forall sv, skind_has_svalue sκ0 sv -> skind_has_svalue sκ sv.
  Proof.
    intros Hsub sv Hskind.
    destruct sκ0 as [ιs ξ|n ξ].
    - inversion Hsub.
      subst.
      destruct Hskind as [Hareps Hrf].
      split; first done.
      by eapply ref_flag_atoms_refine.
    - inversion Hsub.
      subst.
      destruct Hskind as [Hssize Hrf].
      split; first done.
      by eapply ref_flag_words_refine.
  Qed.

  Lemma value_interp_var se t sκ T :
    lookup_type se t = Some (sκ, T) ->
    value_interp rti sr se (VarT t) ≡ (λne sv, ⌜skind_has_svalue sκ sv⌝ ∗ T sv)%I.
  Proof.
    unfold lookup_type.
    cbn.
    intros H sv.
    rewrite value_interp_eq; cbn.
    rewrite H.
    cbn.
    iSplit; last eauto.
    iIntros "(%sκ' & %Hsκ' & %Hskind & HT)".
    inversion Hsκ'.
    subst sκ'.
    by iFrame.
  Qed.

  Lemma prim_value_type_l ι v :
    has_prim ι v ->
    value_type_interp (translate_prim ι) v.
  Proof.
    intros H.
    by destruct ι; destruct v; try contradiction; eexists.
  Qed.

  Lemma prim_value_type_r ι v :
    value_type_interp (translate_prim ι) v ->
    has_prim ι v.
  Proof.
    intros H.
    destruct ι; destruct v; destruct H as [n H]; done.
  Qed.

  Lemma prim_value_type ι v :
    value_type_interp (translate_prim ι) v <->
    has_prim ι v.
  Proof.
    split.
    - apply prim_value_type_r.
    - apply prim_value_type_l.
  Qed.

  Lemma prims_result_type_l ιs vs :
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

  Lemma prims_result_type_r ιs vs :
    result_type_interp (map translate_prim ιs) vs ->
    has_prims ιs vs.
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

  Lemma prims_result_type ιs vs :
    result_type_interp (map translate_prim ιs) vs <->
    has_prims ιs vs.
  Proof.
    split.
    - apply prims_result_type_r.
    - apply prims_result_type_l.
  Qed.

  Lemma value_interp_skind se τ sv :
    value_interp rti sr se τ sv -∗
    ⌜exists sκ, type_skind se τ = Some sκ /\ skind_has_svalue sκ sv⌝.
  Proof.
    iIntros "H".
    destruct τ;
      iDestruct "H" as "(% & % & % & _)";
      iPureIntro;
      by eexists.
  Qed.

  Lemma big_sepL2_value_interp_skind se τs oss :
    ([∗ list] τ;os ∈ τs;oss, value_interp rti sr se τ (SAtoms os)) -∗
    ⌜Forall2 (fun τ os => exists sκ, type_skind se τ = Some sκ /\ skind_has_svalue sκ (SAtoms os)) τs oss⌝.
  Proof.
    iIntros "H".
    rewrite Forall2_same_length_lookup.
    rewrite <- big_sepL2_pure.
    iDestruct (big_sepL2_length with "H") as "%Hlen".
    iApply (big_sepL2_wand with "[$]").
    iApply big_sepL2_intro; first done.
    iIntros "!> %k %τ %os %Hτ %Hos H".
    destruct τ;
      iDestruct "H" as "(% & %Hskind & %Hsvalue & _)";
      iPureIntro;
      by eexists.
  Qed.

  Lemma ref_flag_stype_interp_refine ξ ξ' T :
    ref_flag_le ξ ξ' ->
    ref_flag_stype_interp ξ T ->
    ref_flag_stype_interp (Σ:=Σ) ξ' T.
  Proof.
    intros Hξ HT.
    by destruct ξ; destruct ξ'.
  Qed.

  Lemma kinding_sound_ref_flag F se τ κ sκ :
    has_kind F τ κ ->
    sem_env_interp F se ->
    eval_kind se κ = Some sκ ->
    ref_flag_stype_interp (skind_ref_flag sκ) (value_interp rti sr se τ).
  Proof.
    intros Hκ Hse Hsκ.
    generalize dependent κ.
    generalize dependent sκ.
    induction τ using type_ind with (P0 := const True) (Pi := const True).
    - (* VarT *)
      intros ?? Hκ Hsκ.
      admit.
    - (* I31T *)
      intros ?? Hκ0 Hsκ.
      eapply ref_flag_stype_interp_refine; first apply least_ref_flag.
      intros ?.
      typeclasses eauto.
    - (* NumT *)
      intros ?? Hκ0 Hsκ.
      eapply ref_flag_stype_interp_refine; first apply least_ref_flag.
      intros ?.
      typeclasses eauto.
    - (* SumT *)
      admit.
    - (* VariantT *)
      admit.
    - (* ProdT *)
      admit.
    - (* StructT *)
      admit.
    - (* RefT *)
      intros ?? Hκ0 Hsκ.
      destruct μ.
      + (* VarM *)
        admit.
      + destruct b.
        * (* MemMM *)
          admit.
        * (* MemGC *)
          eapply ref_flag_stype_interp_refine; first apply least_ref_flag.
          intros ?.
          destruct β; typeclasses eauto.
    - (* CodeRefT *)
      intros ?? Hκ0 Hsκ.
      eapply ref_flag_stype_interp_refine; first apply least_ref_flag.
      intros ?.
      rewrite value_interp_eq.
      typeclasses eauto.
    - (* SerT *)
      admit.
    - (* PlugT *)
      intros ?? Hκ0 Hsκ.
      eapply ref_flag_stype_interp_refine; first apply least_ref_flag.
      intros ?.
      typeclasses eauto.
    - intros ?? Hκ0 Hsκ.
      eapply ref_flag_stype_interp_refine; first apply least_ref_flag.
      intros ?.
      typeclasses eauto.
    - (* RecT *)
      admit.
    - (* ExistsMemT *)
      admit.
    - (* ExistsRepT *)
      admit.
    - (* ExistsSizeT *)
      admit.
    - (* ExistsTypeT *)
      admit.
    - done.
    - done.
    - done.
    - done.
    - done.
  Admitted.

  Lemma kinding_sound_svalue F se τ κ sκ sv :
    has_kind F τ κ ->
    sem_env_interp F se ->
    eval_kind se κ = Some sκ ->
    value_interp rti sr se τ sv -∗
    ⌜skind_has_svalue sκ sv⌝.
  Proof.
    iIntros (Hhas_kind Hse Heval_kind) "H".
    destruct τ;
      iDestruct "H" as "(% & % & % & _)";
      iPureIntro;
      (replace sκ0 with sκ in *; [done|by eapply type_skind_has_kind_agree]).
  Qed.

  Theorem kinding_sound F se τ κ sκ :
    has_kind F τ κ ->
    sem_env_interp F se ->
    eval_kind se κ = Some sκ ->
    skind_has_stype sκ (value_interp rti sr se τ).
  Proof.
    iIntros (Hhas_kind Hse Heval_kind).
    split.
    - by eapply kinding_sound_ref_flag.
    - intros sv. by eapply kinding_sound_svalue.
  Qed.

End kinding.
