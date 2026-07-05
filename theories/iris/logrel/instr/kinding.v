(* Fundamental theorem for the kind system:
     well-kinded syntactic types are semantically well-kinded *)

Require Import RecordUpdate.RecordUpdate.
From iris.proofmode Require Import base proofmode classes.
From iris Require Import
          bi.bi
          bi.lib.fixpoint_banach.
Import bi.
From RichWasm Require Import layout syntax typing kinding_subst.
From RichWasm.compiler Require Import prelude module codegen.
From RichWasm.iris Require Import autowp memory util wp_codegen lenient_wp logpred.
Require Import RichWasm.iris.logrel.
Require Import RichWasm.iris.logrel.env_props.
From stdpp Require Import list.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

(* Setting up Inhabited instances allows commuting existential quantifiers
   with later modalities, like this:

     ▷ (exists sk, P sk) ⊣⊢ exists sk, ▷ P sk

 *)
#[global]
Instance skind_inhabited : Inhabited skind :=
  populate (SVALTYPE [] NoRefs).

#[global]
Instance atom_inhabited : Inhabited atom :=
  populate (PtrA (PtrInt 0)).

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

  Lemma eval_rep_ok_Some' K se ρ :
    kind_ctx_interp (Σ:=Σ) K se ->
    rep_ok K ρ ->
    is_Some (eval_rep se ρ).
  Proof.
    intros Hse Hok.
    induction ρ using rep_ind.
    - inversion Hok as [K' n Hidx HK Hn| | |]; subst K' n.
      destruct Hse as (_ & Hrepv & _).
      rewrite Hrepv in Hidx.
      apply list_lookup_lookup_total_lt in Hidx.
      by eexists.
    - inversion Hok as [|K' ρs' Hρs HK Hρs'| |].
      subst K' ρs'.
      pose proof (List.Forall_and H Hρs) as H'.
      clear H Hρs.
      apply Forall_impl with (Q := is_Some ∘ eval_rep se) in H'.
      + rewrite <- mapM_is_Some in H'. by apply fmap_is_Some.
      + intros ρ [Hsome ?]. by apply Hsome.
    - inversion Hok as [| |K' ρs' Hρs HK Hρs'|].
      subst K' ρs'.
      pose proof (List.Forall_and H Hρs) as H'.
      clear H Hρs.
      apply Forall_impl with (Q := is_Some ∘ eval_rep se) in H'.
      + rewrite <- mapM_is_Some in H'. by apply fmap_is_Some.
      + intros ρ [Hsome ?]. by apply Hsome.
    - done.
  Qed.

  Lemma eval_rep_ok_Some F se ρ :
    sem_env_interp (Σ:=Σ) F se ->
    rep_ok F.(fc_kind_ctx) ρ ->
    is_Some (eval_rep se ρ).
  Proof.
    intros [Hsek _] Hok.
    by eapply eval_rep_ok_Some'.
  Qed.

  Lemma eval_size_ok_Some' K se σ :
    kind_ctx_interp (Σ:=Σ) K se ->
    size_ok K σ ->
    is_Some (eval_size se σ).
  Proof.
    intros Hse Hok.
    induction σ using size_ind.
    - inversion Hok as [K' n Hidx HK Hn| | | |].
      subst K' n.
      destruct Hse as (_ & _ & Hsizev).
      rewrite Hsizev in Hidx.
      apply list_lookup_lookup_total_lt in Hidx.
      by eexists.
    - inversion Hok as [|K' σs' Hσs HK Hσs'| | |].
      subst K' σs'.
      pose proof (List.Forall_and H Hσs) as H'.
      clear H Hσs.
      apply Forall_impl with (Q := is_Some ∘ eval_size se) in H'.
      + rewrite <- mapM_is_Some in H'. by apply fmap_is_Some.
      + intros σ [Hsome ?]. by apply Hsome.
    - inversion Hok as [| |K' σs' Hσs HK Hσs'| |].
      subst K' σs'.
      pose proof (List.Forall_and H Hσs) as H'.
      clear H Hσs.
      apply Forall_impl with (Q := is_Some ∘ eval_size se) in H'.
      + rewrite <- mapM_is_Some in H'. by apply fmap_is_Some.
      + intros σ [Hsome ?]. by apply Hsome.
    - inversion Hok as [| | |K' ρ' Hok_ρ HK Hρ'|].
      subst K' ρ'.
      apply fmap_is_Some.
      by eapply eval_rep_ok_Some'.
    - done.
  Qed.

  Lemma eval_size_ok_Some F se σ :
    sem_env_interp (Σ:=Σ) F se ->
    size_ok F.(fc_kind_ctx) σ ->
    is_Some (eval_size se σ).
  Proof.
    intros [Hsek _] Hok.
    by eapply eval_size_ok_Some'.
  Qed.

  Lemma eval_kind_ok_Some' K se κ :
    kind_ctx_interp (Σ:=Σ) K se ->
    kind_ok K κ ->
    is_Some (eval_kind se κ).
  Proof.
    intros Hse Hok.
    destruct κ as [ρ ξ|].
    - inversion Hok as [K' ρ' ξ' Hok_ρ|].
      subst K' ρ' ξ'.
      cbn.
      by eapply eval_rep_ok_Some' in Hok_ρ as [ιs ->].
    - inversion Hok as [|K' σ ξ Hok_σ].
      subst K' σ ξ.
      cbn.
      by eapply eval_size_ok_Some' in Hok_σ as [n ->].
  Qed.

  Lemma eval_kind_ok_Some F se κ :
    sem_env_interp (Σ:=Σ) F se ->
    kind_ok F.(fc_kind_ctx) κ ->
    is_Some (eval_kind se κ).
  Proof.
    intros [Hsek _] Hok.
    by eapply eval_kind_ok_Some'.
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
      apply fmap_Some in Htype_skind as ([sκ_true T] & bofp & borzoi).
      cbn in bap.
      pose proof (Forall2_lookup_lr _ _ _ _ _ _ bap H bofp) as help.
      cbn in help.
      destruct T as [sκ_T T].
      cbn in borzoi.
      subst sκ'.
      destruct help as [hh _].
      rewrite Heval_kind in hh.
      by inversion hh. (* yaaaaaay *)
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
    pose proof (Forall2_lookup_l _ _ _ _ _ Htype_ctx H) as [[sκ_true [sκ_T T]] (Ht & Hsκ_T & _)].
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

  (* NOTE SAVE is this bad *)
  Lemma value_interp_var se t sκ sκ_T T :
    subskind_of sκ_T sκ ->
    lookup_type se t = Some (sκ, (sκ_T, T)) ->
    value_interp rti sr se (VarT t) ≡ (λne sv, ⌜skind_has_svalue sκ sv⌝ ∗ T sv)%I.
  Proof.
    unfold lookup_type.
    Opaque skind_has_svalue.
    cbn.
    intros Hsubs H sv.
    rewrite value_interp_eq; cbn.
    rewrite H.
    cbn.
    iSplit.
    - iIntros "(%sκ' & %Hsκ' & %Hskind & HT)".
      iFrame.
      iPureIntro.
      inversion Hsκ'.
      subst sκ'.
      done.
    - eauto.
  Qed.
  Transparent skind_has_svalue.

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

  Notation refok sk T := (ref_flag_stype_interp (skind_ref_flag sk) T).

  Lemma srec_interp_pers_aux (T : semantic_type) sk (se : semantic_env (Σ := Σ)) :
    (∀ (Φ : leibnizO semantic_value -n> iPropO Σ),
       refok sk Φ →
       refok sk (T (se.1, (sk, (sk, add_skind_interp_closed sk Φ)) :: se.2))) →
    refok sk (fixpoint (skind_rec_interp1 sk T se)).
  Proof.
    intros.
    apply fixpoint_ind.
    - intros U V Huv Hu.
      unfold equiv in Huv.
      destruct (skind_ref_flag sk); cbn in Hu; try done; intros sv.
      * specialize (Huv sv).
        unfold Persistent.
        unfold Persistent in Hu.
        iIntros "H".
        setoid_rewrite <- Huv.
        by iApply Hu.
      * specialize (Huv sv).
        unfold Persistent.
        unfold Persistent in Hu.
        iIntros "H".
        setoid_rewrite <- Huv.
        by iApply Hu.
    - exists (λne (sv : leibnizO semantic_value), emp%I).
      destruct (skind_ref_flag sk); cbn; try done; typeclasses eauto.
    - intros T0 Hsk.
      cbn.
      destruct (skind_ref_flag sk); cbn; last done; intros sv.
      + eapply later_persistent; eapply H; done.
      + eapply later_persistent; eapply H; done.
    - destruct (skind_ref_flag sk); cbn; last done.
      + apply limit_preserving_forall => sv.
        apply limit_preserving_Persistent; solve_proper.
      + apply limit_preserving_forall => sv.
        apply limit_preserving_Persistent; solve_proper.
  Qed.

  Lemma add_skind_interp_pers τ (T : semantic_type) (se : semantic_env (Σ := Σ)) (sv : semantic_value) :
    Persistent (T se sv) →
    Persistent (add_skind_interp τ T se sv).
  Proof.
    intros H.
    unfold add_skind_interp.
    apply bi.exist_persistent; intros sk.
    apply bi.sep_persistent; first typeclasses eauto.
    apply bi.sep_persistent; first typeclasses eauto.
    done.
  Qed.

  Lemma ref_flag_interp_pers sk τ (T : semantic_type) (se : semantic_env (Σ := Σ)) :
    ref_flag_stype_interp sk (T se) →
    ref_flag_stype_interp sk (add_skind_interp τ T se).
  Proof.
    unfold ref_flag_stype_interp.
    destruct sk; last done; intros sv; eauto using add_skind_interp_pers.
  Qed.

  Lemma type_interp_equiv τ se :
    type_interp rti sr τ se ≡ add_skind_interp τ (pre_type_interp rti sr τ) se.
  Proof.
    intros sv.
    apply type_interp_eq.
  Qed.

  Lemma value_interp_equiv τ se :
    value_interp rti sr se τ ≡ add_skind_interp τ (pre_type_interp rti sr τ) se.
  Proof.
    intros sv.
    apply value_interp_eq.
  Qed.

  Instance ref_flag_stype_interp_proper_impl ξ :
    Proper (equiv ==> flip impl) (ref_flag_stype_interp (Σ := Σ) ξ).
  Proof.
    iIntros (t1 t2 Ht Ht1).
    destruct ξ; cbn in *; last done;
      intros sv; specialize (Ht sv); by rewrite Ht.
  Qed.

  Notation sval_ok sκ T := (∀ sv : leibnizO semantic_value, T sv ⊢ ⌜skind_has_svalue sκ sv⌝).

  Instance sval_ok_proper sκ :
    Proper (equiv ==> impl) (skind_has_stype (Σ := Σ) sκ).
  Proof.
    unfold skind_has_stype, refok, Persistent.
    intros t1 t2 Ht [Hp Hs]; destruct (skind_ref_flag sκ).
    - split; iIntros (sv) "Ht2"; setoid_rewrite <- (Ht sv);
        [by iApply Hp | by iApply Hs].
    - split; iIntros (sv) "Ht2"; setoid_rewrite <- (Ht sv);
        [by iApply Hp | by iApply Hs].
    - split; first done.
      iIntros (sv) "Ht2"; setoid_rewrite <- (Ht sv);
        by iApply Hs.
  Qed.

  Definition type_ctx_refs_interp (κs : list kind) (se : semantic_env (Σ := Σ)) : Prop :=
    Forall2
      (fun κ '(sκ, (sκT, T)) => eval_kind se κ = Some sκ /\ subskind_of sκT sκ /\ refok sκT T)
      κs
      (senv_types se).

  Definition sem_env_interp_refs F se :=
    kind_ctx_interp (fc_kind_ctx F) se ∧
    type_ctx_refs_interp (fc_type_vars F) se.

  Lemma type_ctx_interp_proj_refs tys se :
    type_ctx_interp tys se →
    type_ctx_refs_interp tys se.
  Proof.
    unfold type_ctx_interp, type_ctx_refs_interp.
    intros Hse.
    eapply Forall2_impl; first apply Hse.
    intros k [sk [sk_T T]] [Hev [Hsub [Hp Hs]]].
    tauto.
  Qed.

  Lemma sem_env_interp_proj_refs F se :
    sem_env_interp F se →
    sem_env_interp_refs F se.
  Proof.
    unfold sem_env_interp, sem_env_interp_refs.
    intros [Hk Ht].
    eauto using type_ctx_interp_proj_refs.
  Qed.

  Lemma sem_env_interp_refs_insert_type F (se : semantic_env (Σ:=Σ)) κ sκ sκ_T T :
    sem_env_interp_refs F se →
    eval_kind se κ = Some sκ →
    subskind_of sκ_T sκ ->
    refok sκ_T T →
    sem_env_interp_refs (F <| fc_type_vars ::= cons κ |>) (senv_insert_type sκ sκ_T T se).
  Proof.
    intros [Hkind Htypes] Hκ Hsubsk HT.
    split.
    - destruct Hkind as (Hmem & Hrep & Hsize).
      repeat split; cbn; done.
    - cbn [fc_type_vars].
      apply Forall2_cons.
      split.
      + split.
        * by eapply eval_kind_type_irrel.
        * done.
      + eapply Forall2_impl; [exact Htypes|].
        intros κ' [sκ' [sκ_T' T']] [Heval' HT'].
        split; [by eapply eval_kind_type_irrel | exact HT'].
  Qed.

  Lemma sem_env_interp_refs_insert_mem F (se : semantic_env (Σ:=Σ)) μ :
    sem_env_interp_refs F se →
    sem_env_interp_refs (F <| fc_kind_ctx; kc_mem_vars ::= S |>) (senv_insert_mem μ se).
  Proof.
    intros [Hkind Htypes].
    destruct se as [[[m r] s] t].
    destruct F as [ret loc lab K tys]; destruct K.
    cbn in *;  split.
    - destruct Hkind as (Hmem & Hrep & Hsize); cbn in *.
      repeat split; cbn; try done.
      congruence.
    - cbn [fc_type_vars].
      eapply Forall2_impl; [exact Htypes|].
      intros κ' [sκ' [sκ_T' T']] [Heval' HT'].
      admit.
  Admitted.

  Lemma eval_kind_flags (se : semantic_env (Σ := Σ)) κ sκ :
    eval_kind se κ = Some sκ →
    kind_ref_flag κ = skind_ref_flag sκ.
  Proof.
  Admitted.

  Lemma refok_add_skind_closed sκ (T : leibnizO semantic_value -n> iPropO Σ) :
    refok sκ T →
    refok sκ (add_skind_interp_closed sκ T).
  Proof.
  Admitted.

  Lemma kinding_sound_ref_flag F se τ κ sκ :
    has_kind F τ κ ->
    sem_env_interp_refs F se ->
    eval_kind se κ = Some sκ ->
    refok sκ (value_interp rti sr se τ).
  Proof.
    intros Hκ.
    revert se sκ.
    induction Hκ using has_kind_ind' with (P0 := λ _ _, True) (Pi := λ _ _, True);
      try intros * Hse Hsκ.
    - (* I31T *)
      eapply ref_flag_stype_interp_refine; first apply least_ref_flag.
      intros ?.
      typeclasses eauto.
    - (* i32 *)
      eapply ref_flag_stype_interp_refine; first apply least_ref_flag.
      intros ?.
      typeclasses eauto.
    - (* i64 *)
      eapply ref_flag_stype_interp_refine; first apply least_ref_flag.
      intros ?.
      typeclasses eauto.
    - (* f32 *)
      eapply ref_flag_stype_interp_refine; first apply least_ref_flag.
      intros ?.
      typeclasses eauto.
    - (* f64 *)
      eapply ref_flag_stype_interp_refine; first apply least_ref_flag.
      intros ?.
      typeclasses eauto.
    - (* SumT *)
      setoid_rewrite type_interp_equiv.
      apply ref_flag_interp_pers.
      setoid_rewrite <- eval_kind_flags; last by eauto.
      cbn.

      subst κ.
      cbn in Hsκ.
      apply bind_Some in Hsκ.
      destruct Hsκ as (ιs & Hcat & Hret).
      apply fmap_Some in Hcat.
      destruct Hcat as (ιss & Hιss & ->).
      inversion Hret; subst sκ; clear Hret.
      pose proof (length_mapM _ _ _ Hιss) as Hlens1.
      pose proof (Forall3_length_lm _ _ _ _ H).
      pose proof (Forall3_length_lr _ _ _ _ H).

      destruct (ref_flag_lub ξs) eqn:Hlub; cbn; last done.
      + intros sv.
        apply bi.exist_persistent; intros i.
        apply bi.exist_persistent; intros os.
        apply bi.exist_persistent; intros off.
        apply bi.exist_persistent; intros count.
        unfold Persistent.
        iIntros "(-> & %Hoff & %Hev & Hty)".

        apply bind_Some in Hev.
        destruct Hev as (ιs & Hev & Hret).
        inversion Hret; subst count; clear Hret.
        apply bind_Some in Hev.
        destruct Hev as (ρ & Hev & Hret).
        assert (i < length ρs).
        { by apply lookup_lt_is_Some. }
        assert (is_Some (τs !! i)) as [τ Hτ].
        { apply lookup_lt_is_Some; lia. }
        assert (is_Some (ξs !! i)) as [ξ Hξ].
        { apply lookup_lt_is_Some; lia. }
        apply (util.mapM_lookup _ _ _ i) in Hιss.
        rewrite Hev in Hιss; cbn in Hιss.
        rewrite Hret in Hιss; symmetry in Hιss.

        pose proof (list_lookup_fmap (type_interp rti sr) τs i) as Hfmap.
        unfold fmap in Hfmap.
        replace list_fmap with map in Hfmap by done.
        unfold lookup in Hfmap, Hτ.
        rewrite Hfmap Hτ.
        cbn.
        iSplit; first eauto.
        iSplit; first eauto.
        iSplit.
        {  cbn.
           rewrite Hev; cbn; rewrite Hret.
           iModIntro; iPureIntro.
           done. }

        eapply Forall3_lookup_lmr in H; eauto.
        specialize (H se (SVALTYPE ιs ξ) ltac:(done) ltac:(cbn; rewrite Hret; done)).
        unfold refok in H.
        cbn in H.
        pose proof (ref_flag_lub_ub ξ ξs (list_elem_of_lookup_2 _ _ _ Hξ)) as Hub.
        rewrite Hlub in Hub.
        destruct ξ; last by inversion Hub; eauto.
        * specialize (H (SAtoms (take (length ιs) (drop off os)))).
          unfold Persistent in H.
          by iApply H.
        * specialize (H (SAtoms (take (length ιs) (drop off os)))).
          unfold Persistent in H.
          by iApply H.
      + intros sv.
        apply bi.exist_persistent; intros i.
        apply bi.exist_persistent; intros os.
        apply bi.exist_persistent; intros off.
        apply bi.exist_persistent; intros count.
        unfold Persistent.
        iIntros "(-> & %Hoff & %Hev & Hty)".

        apply bind_Some in Hev.
        destruct Hev as (ιs & Hev & Hret).
        inversion Hret; subst count; clear Hret.
        apply bind_Some in Hev.
        destruct Hev as (ρ & Hev & Hret).
        assert (i < length ρs).
        { by apply lookup_lt_is_Some. }
        assert (is_Some (τs !! i)) as [τ Hτ].
        { apply lookup_lt_is_Some; lia. }
        assert (is_Some (ξs !! i)) as [ξ Hξ].
        { apply lookup_lt_is_Some; lia. }
        apply (util.mapM_lookup _ _ _ i) in Hιss.
        rewrite Hev in Hιss; cbn in Hιss.
        rewrite Hret in Hιss; symmetry in Hιss.

        pose proof (list_lookup_fmap (type_interp rti sr) τs i) as Hfmap.
        unfold fmap in Hfmap.
        replace list_fmap with map in Hfmap by done.
        unfold lookup in Hfmap, Hτ.
        rewrite Hfmap Hτ.
        cbn.
        iSplit; first eauto.
        iSplit; first eauto.
        iSplit.
        {  cbn.
           rewrite Hev; cbn; rewrite Hret.
           iModIntro; iPureIntro.
           done. }

        eapply Forall3_lookup_lmr in H; eauto.
        specialize (H se (SVALTYPE ιs ξ) ltac:(done) ltac:(cbn; rewrite Hret; done)).
        unfold refok in H.
        cbn in H.
        pose proof (ref_flag_lub_ub ξ ξs (list_elem_of_lookup_2 _ _ _ Hξ)) as Hub.
        rewrite Hlub in Hub.
        destruct ξ; last by inversion Hub; eauto.
        * specialize (H (SAtoms (take (length ιs) (drop off os)))).
          unfold Persistent in H.
          by iApply H.
        * specialize (H (SAtoms (take (length ιs) (drop off os)))).
          unfold Persistent in H.
          by iApply H.
    - (* VariantT *)
      setoid_rewrite type_interp_equiv.
      apply ref_flag_interp_pers.
      setoid_rewrite <- eval_kind_flags; last by eauto.
      cbn.

      subst κ.
      cbn in Hsκ.
      apply bind_Some in Hsκ.
      destruct Hsκ as (n & Hcat & Hret).
      apply fmap_Some in Hcat.
      destruct Hcat as (ns & Hns & ->).
      inversion Hret; subst sκ; clear Hret.
      pose proof (length_mapM _ _ _ Hns) as Hlens1.
      pose proof (Forall3_length_lm _ _ _ _ H).
      pose proof (Forall3_length_lr _ _ _ _ H).

      destruct (ref_flag_lub ξs) eqn:Hlub; cbn; last done.
      + intros sv.
        apply bi.exist_persistent; intros i.
        apply bi.exist_persistent; intros n.
        apply bi.exist_persistent; intros ws.
        apply bi.exist_persistent; intros ws'.
        unfold Persistent.
        iIntros "(%Hrep & -> & Hty)".

        pose proof (list_lookup_fmap (type_interp rti sr) τs i) as Hfmap.
        unfold fmap in Hfmap.
        replace list_fmap with map in Hfmap by done.
        unfold lookup in Hfmap.
        rewrite Hfmap.
        destruct (list_lookup i τs) eqn:Hτs; rewrite Hτs; cbn; last done.

        assert (i < length τs).
        { by apply lookup_lt_is_Some. }
        assert (is_Some (ns !! i)) as [m Hm].
        { apply lookup_lt_is_Some; lia. }
        assert (is_Some (σs !! i)) as [σ Hσ].
        { apply lookup_lt_is_Some; lia. }
        assert (is_Some (ξs !! i)) as [ξ Hξ].
        { apply lookup_lt_is_Some; lia. }
        apply (util.mapM_lookup _ _ _ i) in Hns.
        rewrite Hσ in Hns; cbn in Hns.
        rewrite Hm in Hns.

        iSplit; first eauto.
        iSplit; first eauto.

        eapply Forall3_lookup_lmr in H; eauto.
        specialize (H se (SMEMTYPE m ξ) ltac:(done) ltac:(cbn; rewrite Hns; done)).
        unfold refok in H.
        cbn in H.
        pose proof (ref_flag_lub_ub ξ ξs (list_elem_of_lookup_2 _ _ _ Hξ)) as Hub.
        rewrite Hlub in Hub.
        destruct ξ; last by inversion Hub; eauto.
        * unfold Persistent in H.
          by iApply H.
        * unfold Persistent in H.
          by iApply H.
      + intros sv.
        apply bi.exist_persistent; intros i.
        apply bi.exist_persistent; intros n.
        apply bi.exist_persistent; intros ws.
        apply bi.exist_persistent; intros ws'.
        unfold Persistent.
        iIntros "(%Hrep & -> & Hty)".

        pose proof (list_lookup_fmap (type_interp rti sr) τs i) as Hfmap.
        unfold fmap in Hfmap.
        replace list_fmap with map in Hfmap by done.
        unfold lookup in Hfmap.
        rewrite Hfmap.
        destruct (list_lookup i τs) eqn:Hτs; rewrite Hτs; cbn; last done.

        assert (i < length τs).
        { by apply lookup_lt_is_Some. }
        assert (is_Some (ns !! i)) as [m Hm].
        { apply lookup_lt_is_Some; lia. }
        assert (is_Some (σs !! i)) as [σ Hσ].
        { apply lookup_lt_is_Some; lia. }
        assert (is_Some (ξs !! i)) as [ξ Hξ].
        { apply lookup_lt_is_Some; lia. }
        apply (util.mapM_lookup _ _ _ i) in Hns.
        rewrite Hσ in Hns; cbn in Hns.
        rewrite Hm in Hns.

        iSplit; first eauto.
        iSplit; first eauto.

        eapply Forall3_lookup_lmr in H; eauto.
        specialize (H se (SMEMTYPE m ξ) ltac:(done) ltac:(cbn; rewrite Hns; done)).
        unfold refok in H.
        cbn in H.
        pose proof (ref_flag_lub_ub ξ ξs (list_elem_of_lookup_2 _ _ _ Hξ)) as Hub.
        rewrite Hlub in Hub.
        destruct ξ; last by inversion Hub; eauto.
        * unfold Persistent in H.
          by iApply H.
        * unfold Persistent in H.
          by iApply H.
    - (* ProdT *)
      setoid_rewrite type_interp_equiv.
      apply ref_flag_interp_pers.
      setoid_rewrite <- eval_kind_flags; last by eauto.
      cbn.

      subst κ.
      cbn in Hsκ.
      apply bind_Some in Hsκ.
      destruct Hsκ as (ιs & Hcat & Hret).
      apply fmap_Some in Hcat.
      destruct Hcat as (ιss & Hιss & ->).
      inversion Hret; subst sκ; clear Hret.
      pose proof (length_mapM _ _ _ Hιss) as Hlens1.
      pose proof (Forall3_length_lm _ _ _ _ H).
      pose proof (Forall3_length_lr _ _ _ _ H).

      unfold ref_flag_stype_interp.
      destruct (ref_flag_lub ξs) eqn:Hlub; last done.
      + intros sv.
        apply bi.exist_persistent; intros oss.
        apply bi.sep_persistent; first typeclasses eauto.
        rewrite big_sepL2_fmap_l.
        apply big_sepL2_persistent; intros k τ os Hτ Hos.
        assert (k < length τs).
        { by apply lookup_lt_is_Some. }
        assert (is_Some (ρs !! k)) as [ρ Hρ].
        { apply lookup_lt_is_Some; lia. }
        assert (is_Some (ξs !! k)) as [ξ Hξ].
        { apply lookup_lt_is_Some; lia. }
        assert (is_Some (ιss !! k)) as [ιs Hιs].
        { apply lookup_lt_is_Some; lia. }
        eapply Forall3_lookup_lmr in H; eauto.
        apply (util.mapM_lookup _ _ _ k) in Hιss.
        rewrite Hιs Hρ in Hιss; cbn in Hιss.
        specialize (H se (SVALTYPE ιs ξ) ltac:(done) ltac:(cbn; by rewrite Hιss)).
        unfold refok in H.
        cbn in H.
        pose proof (ref_flag_lub_ub ξ ξs (list_elem_of_lookup_2 _ _ _ Hξ)) as Hub.
        rewrite Hlub in Hub.
        destruct ξ; eauto; last by inversion Hub.
      + intros sv.
        apply bi.exist_persistent; intros oss.
        apply bi.sep_persistent; first typeclasses eauto.
        rewrite big_sepL2_fmap_l.
        apply big_sepL2_persistent; intros k τ os Hτ Hos.
        assert (k < length τs).
        { by apply lookup_lt_is_Some. }
        assert (is_Some (ρs !! k)) as [ρ Hρ].
        { apply lookup_lt_is_Some; lia. }
        assert (is_Some (ξs !! k)) as [ξ Hξ].
        { apply lookup_lt_is_Some; lia. }
        assert (is_Some (ιss !! k)) as [ιs Hιs].
        { apply lookup_lt_is_Some; lia. }
        eapply Forall3_lookup_lmr in H; eauto.
        apply (util.mapM_lookup _ _ _ k) in Hιss.
        rewrite Hιs Hρ in Hιss; cbn in Hιss.
        specialize (H se (SVALTYPE ιs ξ) ltac:(done) ltac:(cbn; by rewrite Hιss)).
        unfold refok in H.
        cbn in H.
        pose proof (ref_flag_lub_ub ξ ξs (list_elem_of_lookup_2 _ _ _ Hξ)) as Hub.
        rewrite Hlub in Hub.
        destruct ξ; eauto; last by inversion Hub.
    - (* StructT *)
      setoid_rewrite type_interp_equiv.
      apply ref_flag_interp_pers.
      setoid_rewrite <- eval_kind_flags; last by eauto.
      cbn.

      subst κ.
      cbn in Hsκ.
      apply bind_Some in Hsκ.
      destruct Hsκ as (ιs & Hcat & Hret).
      apply fmap_Some in Hcat.
      destruct Hcat as (ns & Hns & ->).
      inversion Hret; subst sκ; clear Hret.
      pose proof (length_mapM _ _ _ Hns) as Hlens1.
      pose proof (Forall3_length_lm _ _ _ _ H).
      pose proof (Forall3_length_lr _ _ _ _ H).

      unfold ref_flag_stype_interp.
      destruct (ref_flag_lub ξs) eqn:Hlub; last done.
      + intros sv.
        apply bi.exist_persistent; intros oss.
        apply bi.sep_persistent; first typeclasses eauto.
        rewrite big_sepL2_fmap_r.
        apply big_sepL2_persistent; intros k os τ Hos Hτ.
        assert (k < length τs).
        { by apply lookup_lt_is_Some. }
        assert (is_Some (σs !! k)) as [ρ Hρ].
        { apply lookup_lt_is_Some; lia. }
        assert (is_Some (ξs !! k)) as [ξ Hξ].
        { apply lookup_lt_is_Some; lia. }
        assert (is_Some (ns !! k)) as [n Hn].
        { apply lookup_lt_is_Some; lia. }
        eapply Forall3_lookup_lmr in H; eauto.
        apply (util.mapM_lookup _ _ _ k) in Hns.
        rewrite Hn Hρ in Hns; cbn in Hns.
        specialize (H se (SMEMTYPE n ξ) ltac:(done) ltac:(cbn; by rewrite Hns)).
        unfold refok in H.
        cbn in H.
        pose proof (ref_flag_lub_ub ξ ξs (list_elem_of_lookup_2 _ _ _ Hξ)) as Hub.
        rewrite Hlub in Hub.
        destruct ξ; eauto; last by inversion Hub.
      + intros sv.
        apply bi.exist_persistent; intros oss.
        apply bi.sep_persistent; first typeclasses eauto.
        rewrite big_sepL2_fmap_r.
        apply big_sepL2_persistent; intros k os τ Hos Hτ.
        assert (k < length τs).
        { by apply lookup_lt_is_Some. }
        assert (is_Some (σs !! k)) as [ρ Hρ].
        { apply lookup_lt_is_Some; lia. }
        assert (is_Some (ξs !! k)) as [ξ Hξ].
        { apply lookup_lt_is_Some; lia. }
        assert (is_Some (ns !! k)) as [n Hn].
        { apply lookup_lt_is_Some; lia. }
        eapply Forall3_lookup_lmr in H; eauto.
        apply (util.mapM_lookup _ _ _ k) in Hns.
        rewrite Hn Hρ in Hns; cbn in Hns.
        specialize (H se (SMEMTYPE n ξ) ltac:(done) ltac:(cbn; by rewrite Hns)).
        unfold refok in H.
        cbn in H.
        pose proof (ref_flag_lub_ub ξ ξs (list_elem_of_lookup_2 _ _ _ Hξ)) as Hub.
        rewrite Hlub in Hub.
        destruct ξ; eauto; last by inversion Hub.
    - (* RefT VarM *)
      subst κ.
      cbn in Hsκ; inversion Hsκ; subst.
      done.
    - (* RefT MemMM *)
      subst κ.
      cbn in Hsκ; inversion Hsκ.
      done.
    - (* RefT MemGC *)
      subst κ.
      cbn in Hsκ; inversion Hsκ.
      cbn.
      intros ?.
      destruct β; typeclasses eauto.
    - (* CodeRefT *)
      subst κ; cbn in Hsκ; inversion Hsκ; subst.
      intros ?.
      rewrite value_interp_eq.
      typeclasses eauto.
    - (* SerT *)
      subst κ.
      cbn in Hsκ.
      apply bind_Some in Hsκ.
      destruct Hsκ as (n & Hn & Hret).
      apply fmap_Some in Hn.
      destruct Hn as (ιs & Hιs & Hsum).
      inversion Hret; subst sκ.
      cbn.
      specialize (IHHκ se (SVALTYPE ιs ξ) Hse).
      cbn in IHHκ.
      rewrite Hιs in IHHκ.
      cbn in IHHκ.
      specialize (IHHκ eq_refl).
      unfold ref_flag_stype_interp.
      destruct ξ.
      * cbn in *.
        intros sv.
        setoid_rewrite value_interp_eq.
        apply add_skind_interp_pers.
        cbn.
        apply bi.exist_persistent; intros os.
        apply bi.sep_persistent; first typeclasses eauto.
        eapply IHHκ.
      * cbn in *.
        intros sv.
        setoid_rewrite value_interp_eq.
        apply add_skind_interp_pers.
        cbn.
        apply bi.exist_persistent; intros os.
        apply bi.sep_persistent; first typeclasses eauto.
        eapply IHHκ.
      * done.
    - (* PlugT *)
      eapply ref_flag_stype_interp_refine; first apply least_ref_flag.
      intros ?.
      typeclasses eauto.
    - eapply ref_flag_stype_interp_refine; first apply least_ref_flag.
      intros ?.
      typeclasses eauto.
    - (* RecT *)
      setoid_rewrite type_interp_equiv.
      apply ref_flag_interp_pers.
      cbn -[rec_interp].
      unfold rec_interp.
      cbn.
      rewrite Hsκ.
      apply srec_interp_pers_aux.
      intros T Ht.
      apply IHHκ; eauto.
      + apply sem_env_interp_refs_insert_type; eauto using subskind_of_refl, refok_add_skind_closed.
      + by apply eval_kind_type_irrel.
    - (* ExistsMemT *)
      rewrite value_interp_equiv.
      apply ref_flag_interp_pers.
      cbn.
      unfold refok.
      destruct (skind_ref_flag sκ) eqn:Hflag; last done.
      + intros sv.
        apply bi.exist_persistent; intros μ.
        specialize (IHHκ (μ :: se.1.1.1, se.1.1.2, se.1.2, se.2) sκ).
        unfold refok in IHHκ.
        rewrite Hflag in IHHκ.
        eapply IHHκ.
        * admit.
        * admit.
      + admit.
    - (* ExistsRepT *)
      rewrite value_interp_equiv.
      apply ref_flag_interp_pers.
      cbn.
      unfold refok.
      destruct (skind_ref_flag sκ) eqn:Hflag; last done.
      + intros sv.
        apply bi.exist_persistent; intros ιs.
        specialize (IHHκ (se.1.1.1, ιs :: se.1.1.2, se.1.2, se.2) sκ).
        unfold refok in IHHκ.
        rewrite Hflag in IHHκ.
        eapply IHHκ.
        * destruct Hse as [[Hsem [Hser Hses]] Hset].
          repeat split; cbn; try done.
          -- destruct F; destruct fc_kind_ctx; cbn in *.
             congruence.
          -- admit.
        * admit.
      + intros sv.
        apply bi.exist_persistent; intros ιs.
        specialize (IHHκ (se.1.1.1, ιs :: se.1.1.2, se.1.2, se.2) sκ).
        unfold refok in IHHκ.
        rewrite Hflag in IHHκ.
        eapply IHHκ.
        * destruct Hse as [[Hsem [Hser Hses]] Hset].
          repeat split; cbn; try done.
          -- destruct F; destruct fc_kind_ctx; cbn in *.
             congruence.
          -- admit.
        * admit.
    - (* ExistsSizeT *)
      rewrite value_interp_equiv.
      apply ref_flag_interp_pers.
      cbn.
      unfold refok.
      destruct (skind_ref_flag sκ) eqn:Hflag; last done.
      + intros sv.
        apply bi.exist_persistent; intros n.
        specialize (IHHκ (se.1.1.1, se.1.1.2, n :: se.1.2, se.2) sκ).
        unfold refok in IHHκ.
        rewrite Hflag in IHHκ.
        eapply IHHκ.
        * destruct Hse as [[Hsem [Hser Hses]] Hset].
          repeat split; cbn; try done.
          -- destruct F; destruct fc_kind_ctx; cbn in *.
             congruence.
          -- admit.
        * admit.
      + intros sv.
        apply bi.exist_persistent; intros n.
        specialize (IHHκ (se.1.1.1, se.1.1.2, n :: se.1.2, se.2) sκ).
        unfold refok in IHHκ.
        rewrite Hflag in IHHκ.
        eapply IHHκ.
        * destruct Hse as [[Hsem [Hser Hses]] Hset].
          repeat split; cbn; try done.
          -- destruct F; destruct fc_kind_ctx; cbn in *.
             congruence.
          -- admit.
        * admit.
    - (* ExistsTypeT *)
      rewrite value_interp_equiv.
      apply ref_flag_interp_pers.
      pose proof H as Hevκ0.
      cbn -[senv_insert_type].
      unfold refok.
      destruct (skind_ref_flag sκ) eqn:Hflag; last done.
      + intros sv.
        unfold Persistent; iIntros "(%T' & %sk0 & %sk_T & %Hev & %Hsub & %Hst & Hty)".
        iExists T', sk0, sk_T.
        iSplit; first eauto.
        iSplit; first eauto.
        iSplit; first eauto.
        set (se' := senv_insert_type sk0 sk_T T' se).
        specialize (IHHκ se' sκ).
        unfold refok, Persistent in IHHκ.
        rewrite Hflag in IHHκ.
        iApply IHHκ; last done.
        * destruct Hst.
          apply sem_env_interp_refs_insert_type; eauto.
        * by apply eval_kind_type_irrel.
      + intros sv.
        unfold Persistent; iIntros "(%T' & %sk0 & %sk_T & %Hev & %Hsub & %Hst & Hty)".
        iExists T', sk0, sk_T.
        iSplit; first eauto.
        iSplit; first eauto.
        iSplit; first eauto.
        set (se' := senv_insert_type sk0 sk_T T' se).
        specialize (IHHκ se' sκ).
        unfold refok, Persistent in IHHκ.
        rewrite Hflag in IHHκ.
        iApply IHHκ; last done.
        * destruct Hst.
          apply sem_env_interp_refs_insert_type; eauto.
        * by apply eval_kind_type_irrel.
    - (* VarT *)
      cbn.
      setoid_rewrite value_interp_equiv.
      apply ref_flag_interp_pers.
      cbn.
      destruct Hse as [Hsek Hset].
      eapply Forall2_lookup in Hset.
      erewrite H in Hset.
      inversion Hset; subst.
      destruct y as [sk [skT T]].
      setoid_rewrite <- H2.
      destruct H3 as (Hev & Hsub & Hok).
      cbn.
      rewrite Hsκ in Hev; inversion Hev; subst.
      eapply ref_flag_stype_interp_refine; last done.
      inversion Hsub; subst; cbn; eauto.
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
    value_interp rti sr se τ sv ⊢ ⌜skind_has_svalue sκ sv⌝.
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
    - eapply kinding_sound_ref_flag; eauto using sem_env_interp_proj_refs.
    - intros sv. eapply kinding_sound_svalue; eauto.
  Qed.

End kinding.
