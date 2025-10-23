(* Fundamental theorem for the kind system:
     well-kinded syntactic types are semantically well-kinded *)

From iris.proofmode Require Import base tactics classes.
From RichWasm Require Import layout syntax typing kinding_subst.
From RichWasm.compiler Require Import prelude module codegen.
From RichWasm.iris Require Import autowp memory util wp_codegen lenient_wp logpred.
From RichWasm.iris.logrel Require Import relations.
From Stdlib Require Import Relations.Relation_Operators.
From stdpp Require Import list.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section FundamentalKinding.
  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.
  
  Lemma semantic_type_le_refl :
    ∀ (T: @semantic_type Σ), 
      T ⊑ T.
  Proof.
    by iIntros (T sv) "H".
  Qed.

  Lemma semantic_type_le_trans :
    ∀ (S T U: @semantic_type Σ), 
      S ⊑ T ->
      T ⊑ U ->
      S ⊑ U.
  Proof.
    iIntros (S T U Hst Htu sv) "H".
    iApply Htu.
    iApply Hst.
    done.
  Qed.

  (*
  Lemma sizity_sized_le_unsized σ :
    sizity_interp (Sized σ) ⊑ sizity_interp Unsized.
  Proof.
    iIntros "%sv (%μ & %ws & %Hsv & %Hsz)".
    iPureIntro.
    do 2 eexists; split; eauto.
    intros; congruence.
  Qed.
  *)
  
  Lemma type_kind_has_kind_Some F τ κ :
    has_kind F τ κ ->
    ∃ κ', type_kind (fe_type_vars (fe_of_context F)) τ = Some κ'.
  Proof.
    induction 1; try solve [eexists; cbn; eauto].
    auto.
  Qed.

  Lemma type_kind_has_kind_agree F τ κ κ' :
    has_kind F τ κ ->
    type_kind (fe_type_vars (fe_of_context F)) τ = Some κ' ->
    clos_refl_trans _ subkind_of κ' κ.
  Proof.
    intros Hhas_kind.
    revert κ'.
    induction Hhas_kind;
      try solve [intros;
                 replace κ' with κ; 
                 [by constructor|]; 
                 cbn in *; congruence].
    intros.
    eapply IHHhas_kind in H0.
    eapply rt_trans; [|apply rt_step]; by eauto.
  Qed.
  
  Lemma subkind_rep_inv :
    forall κ κ',
      clos_refl_trans _ subkind_of κ κ' ->
      kind_rep κ = kind_rep κ'.
  Proof.
    induction 1; try congruence.
    inversion H; reflexivity.
  Qed.

  Lemma subkind_preserves_valtype :
    forall ρ χ δ κ,
      clos_refl_trans _ subkind_of κ (VALTYPE ρ χ δ) ->
      ∃ χ' δ',
        κ = VALTYPE ρ χ' δ'.
  Proof.
    intros.
    remember (VALTYPE ρ χ δ) as κ'.
    revert Heqκ'.
    revert ρ δ χ.
    induction H; intros; subst.
    - inversion H; eauto.
    - eauto.
    - destruct (IHclos_refl_trans2 _ _ _ eq_refl) as (χ' & δ' & Hy).
      eauto.
  Qed.

  Lemma type_rep_has_kind_agree F τ ρ χ δ :
    has_kind F τ (VALTYPE ρ χ δ) ->
    type_rep (fe_type_vars (fe_of_context F)) τ = Some ρ.
  Proof.
    intros Hhas_kind.
    unfold type_rep.
    destruct (type_kind_has_kind_Some _ _ _ Hhas_kind) as [κ' Htk].
    rewrite Htk; cbn.
    eapply type_kind_has_kind_agree in Htk; eauto.
    erewrite subkind_rep_inv by eauto.
    done.
  Qed.
  
  Lemma subkind_sound κ κ' :
    subkind_of κ κ' ->
    kind_as_type_interp (Σ := Σ) κ ⊑ kind_as_type_interp κ'.
  Proof.
    induction 1; cbn; eauto using semantic_type_le_refl.
    (*
    iIntros (sv [(μ' & ws & Hwords & Hsz) Hmem]).
    iSplit; eauto.
    iPureIntro.
    exists μ', ws.
    split; auto.
    intros; congruence.
    *)
  Admitted.

  Lemma rt_subkind_sound κ κ' :
    clos_refl_trans _ subkind_of κ κ' ->
    kind_as_type_interp (Σ := Σ) κ ⊑ kind_as_type_interp κ'.
  Proof. 
    intros H.
    induction H.
    - by apply subkind_sound.
    - by apply semantic_type_le_refl.
    - by eapply semantic_type_le_trans.
  Qed.

  Lemma subst_interp_kinds_map κs s__rep s__size se :
    sem_env_interp (Σ := Σ) κs s__rep s__size se ->
    map fst se = map (subst_kind s__rep s__size) κs.
  Proof.
  Admitted.

  Theorem kinding_refinement F s__mem s__rep s__size se τ κ : 
    has_kind F τ κ ->
    subst_env_interp F s__mem s__rep s__size se ->
    value_interp rti sr se (subst_type s__mem s__rep s__size VarT τ) ⊑
      kind_as_type_interp (subst_kind s__rep s__size κ).
  Proof.
    (*
    iIntros "%Hhas_kind [%Hsubst Hse]".
    iPoseProof (subst_interp_kinds_map with "Hse") as "%Hfsteq".
    unfold sem_env_interp.
    setoid_rewrite bi.sep_comm.
    rewrite big_sepL2_sep_sepL_l.
    iDestruct "Hse" as "[Hkinding Hsubst]".
    rewrite big_sepL2_pure.
    iDestruct "Hsubst" as "[%Htylen %Htysub]".
    iPureIntro.
    intros sv.
    iIntros "Hval".
    rewrite value_interp_eq.
    iDestruct "Hval" as "(%κ' & %Htyk & Hinterp & _)".
    rewrite Hfsteq in Htyk.
    eapply has_kind_subst in Hhas_kind; eauto.
    eapply type_kind_has_kind_agree in Hhas_kind; eauto.
    by iApply rt_subkind_sound.
    *)
  Admitted.

  Instance kind_as_type_persistent κ sv :
    @Persistent (iProp Σ) (kind_as_type_interp κ sv).
  Proof.
    destruct κ, sv; cbn; typeclasses eauto.
  Qed.

  Lemma value_interp_var (se: semantic_env) (t: nat) (κ: kind) (T: semantic_type) :
    se !! t = Some (κ, T) ->
    value_interp rti sr se (VarT t) ≡ (λne sv, kind_as_type_interp κ sv ∗ T sv)%I.
  Proof.
    intros.
    rewrite value_interp_part_eq.
    intros sv.
    cbn.
    unfold type_var_interp.
    rewrite !list_lookup_fmap.
    rewrite !H.
    cbn.
    iSplit.
    - iIntros "(%κ' & %Hfind & Hkt & Htv)".
      inversion Hfind.
      iFrame.
    - eauto.
  Qed.

  (*
  Lemma prim_rep_val_type ι v :
    primitive_rep_interp ι v ->
    value_type_interp (translate_prim_rep ι) v.
  Proof.
    destruct ι; cbn; intros; eauto.
    destruct H as (θ & p & n & -> & Hrep); eauto.
  Qed.
  *)

  (*
  Lemma prim_reps_result_type ιs vs :
    prim_reps_interp sr ιs (SValues vs) ->
    result_type_interp (map translate_prim_rep ιs) vs.
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
      + apply prim_rep_val_type; eauto.
      + eapply IHιs; eauto.
  Qed.
  *)

  (*
  Lemma explicit_copy_prim_reps_interp ιs :
    explicit_copy_spec rti sr ιs (λne (sv: leibnizO semantic_value), ⌜prim_reps_interp sr ιs sv⌝)%I.
  Proof.
    unfold explicit_copy_spec; intros.
    iIntros "%Hcopy %Hwl %Hreg %Hfunc Hregcl Hfr Hrun %Hprim".
    unfold is_copy_operation in Hcopy.
    destruct Hcopy as (es' & Hcg & <-).
    inv_cg_bind Hcg res wl1 wl2 es1 es2 Hcg1 Hcg2.
    inv_cg_bind Hcg2 res1 wl3 wl4 es3 es4 Hcg2 Hcg3.
    inv_cg_bind Hcg3 res2 wl5 wl6 es5 es6 Hcg3 Hcg4.
    subst.
    rewrite <- !app_assoc in Hwl.
    eapply lwp_save_stack_w in Hcg1; 
      [| done |by apply prim_reps_result_type].
    destruct Hcg1 as (Hres & Hwl1 & Hwpes1).
    repeat rewrite to_e_list_cat W.cat_app.
    rewrite app_assoc.
    iApply (lenient_wp_seq with "[Hfr Hrun]");
      [ iApply (Hwpes1 with "[$] [$]")
      | iIntros (?) "%Hfalse"; tauto 
      | ].
    clear Hwpes1.
    cbn.
    iIntros (w f) "Hnotrap Hfr _".
    destruct w; cbn; try (done || by iDestruct "Hnotrap" as "[? ?]").
    iDestruct "Hnotrap" as "([%Hlocs %Hsaved] & Hrun & ->)".
    rewrite app_nil_l.
    eapply lwp_restore_stack_w in Hcg2; 
      [| by eapply Forall2_length].
    destruct Hcg2 as (-> & -> & Hwpes3).
    iApply (lenient_wp_seq with "[Hfr Hrun]");
      [ iApply (Hwpes3 with "[$] [$]"); done
      | iIntros (?) "%Hfalse"; tauto 
      | ].
    clear Hwpes3.
    iIntros (w f') "Hwes Hfr _".
    destruct w; cbn; try (done || by iDestruct "Hwes" as "[? ?]").
    cbn.
    iDestruct "Hwes" as "(-> & Hrun & ->)".
    rewrite app_assoc.
    iApply (lenient_wp_seq with "[Hfr Hrun]").
    - admit.
    - admit.
    - admit.
  Admitted.
  *)

  Lemma copyability_kind ρ ιs χ δ :
    eval_rep ρ = Some ιs ->
    copyability_interp (Σ := Σ) χ (kind_as_type_interp (VALTYPE ρ χ δ)).
  Proof.
    unfold copyability_interp.
    intros H.
    (*
    rewrite H.
    destruct χ.
    - auto.
    - unfold kind_as_type_interp.
      cbn.
      unfold representation_interp.
      rewrite H.
      apply explicit_copy_prim_reps_interp.
    - intros.
      apply kind_as_type_persistent.
    *)
  Admitted.

  Lemma copyability_sep χ S T :
    copyability_interp χ S ->
    copyability_interp χ T ->
    copyability_interp (Σ := Σ) χ (λne sv, (S sv ∗ T sv)%I).
  Proof.
    destruct χ; cbn.
    - auto.
    - admit.
    - intros HS HT sv.
      (* typeclasses eauto. *)
  Admitted.

  Instance copyability_proper : Proper (eq ==> equiv ==> equiv) (copyability_interp (Σ := Σ)).
  Admitted.

  Theorem kinding_copyable F s__mem s__rep s__size se τ ρ χ δ : 
    has_kind F τ (VALTYPE ρ χ δ) ->
    subst_env_interp F s__mem s__rep s__size se ->
    copyability_interp χ (value_interp rti sr se (subst_type s__mem s__rep s__size VarT τ)).
  Proof.
    intros Hkind.
    remember (VALTYPE ρ χ δ) as κ.
    revert Heqκ.
    revert ρ χ δ.
    induction Hkind; intros ? ? ? Hκeq; rewrite -> Hκeq in *;
      intros [Hsubst Henv]; try subst κ; try subst κ'.
    - unfold copyability_interp; inversion Hκeq; subst; eauto.
      cbn.
      intros.
      rewrite value_interp_eq; cbn.
      (* typeclasses eauto. *)
      admit.
    - unfold copyability_interp; inversion Hκeq; subst; eauto.
      intros sv.
      rewrite value_interp_eq; cbn.
      (* typeclasses eauto. *)
      admit.
    - unfold copyability_interp; inversion Hκeq; subst; eauto.
      intros sv.
      (* rewrite value_interp_eq; cbn; typeclasses eauto. *)
      admit.
    - unfold copyability_interp; inversion Hκeq; subst; eauto.
      intros sv.
      (* rewrite value_interp_eq; cbn; typeclasses eauto. *)
      admit.
    - unfold copyability_interp; inversion Hκeq; subst; eauto.
      intros sv.
      (* rewrite value_interp_eq; cbn; typeclasses eauto. *)
      admit.
    - admit. (* sums *)
    - inversion Hκeq; subst; eauto.
    - inversion Hκeq; subst; eauto.
    - admit. (* products *)
    - inversion Hκeq; subst; eauto.
    - inversion Hκeq; subst; eauto.
    - inversion Hκeq; subst; done.
    - admit. (* refs *)
    - admit. (* coderef *)
    - cbn in *. 
      admit.
    - unfold copyability_interp; inversion Hκeq; subst; eauto.
    - admit. (* recursive types *)
    - admit. (* exists (mem) *)
    - admit. (* exists (repr) *)
    - admit. (* exists (size) *)
    - admit. (* exists (type) *)
    - inversion H; subst; eauto.
      + specialize (IHHkind _ _ _ eq_refl).
        cbn in IHHkind.
        cbn.
        admit.
      + cbn; done.
      + specialize (IHHkind _ _ _ eq_refl).
        eapply IHHkind.
        split; auto.
      + specialize (IHHkind _ _ _ eq_refl).
        eapply IHHkind.
        split; eauto.
    - simpl subst_type.
      unfold sem_env_interp in Henv.
      pose proof (Forall2_length _ _ _ Henv) as Hlen.
      eapply Forall2_lookup_r in H; eauto.
      destruct H as [[κt' T] [Hκt' [Hκsubst Hκinterp]]].
      cbn in Hκsubst, Hκinterp.
      cbn in *; subst.
      rewrite value_interp_var; eauto.
      apply copyability_sep.
      + eapply copyability_kind; eauto.
        admit.
      + cbn.
        by destruct Hκinterp.
  Admitted.

  Theorem kinding_sound F s__mem s__rep s__size se τ κ : 
    has_kind F τ κ ->
    subst_env_interp F s__mem s__rep s__size se ->
    kind_interp (subst_kind s__rep s__size κ)
      (value_interp rti sr se (subst_type s__mem s__rep s__size VarT τ)).
  Proof.
    intros Hkind. 
    revert s__mem s__rep s__size se.
    intros * Hsubst.
    split.
    - eapply kinding_refinement; eauto.
    - destruct κ; [| done].
      cbn.
      eapply kinding_copyable; eauto.
  Qed.

End FundamentalKinding.
