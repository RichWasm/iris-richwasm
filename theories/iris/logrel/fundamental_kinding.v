(* Fundamental theorem for the kind system:
     well-kinded syntactic types are semantically well-kinded *)

From iris.proofmode Require Import base tactics classes.
From RichWasm Require Import layout syntax typing kinding_subst.
From RichWasm.compiler Require Import prelude module codegen.
From RichWasm.iris Require Import autowp gc wp_codegen.
From RichWasm.iris.logrel Require Import relations.
From Stdlib Require Import Relations.Relation_Operators.
From stdpp Require Import list.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section FundamentalKinding.
  Context `{Σ: gFunctors}.
  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!RichWasmGCG Σ}.

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

  Lemma sizity_sized_le_unsized σ :
    sizity_interp (Σ:=Σ) (Sized σ) ⊑ sizity_interp Unsized.
  Proof.
    iIntros "%sv (%μ & %ws & %Hsv & %Hsz)".
    iPureIntro.
    do 2 eexists; split; eauto.
    intros; congruence.
  Qed.
  
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
    kind_as_type_interp (Σ := Σ) sr κ ⊑ kind_as_type_interp sr κ'.
  Proof.
    induction 1; cbn; eauto using semantic_type_le_refl.
    iIntros (sv [(μ' & ws & Hwords & Hsz) Hmem]).
    iSplit; eauto.
    iPureIntro.
    exists μ', ws.
    split; auto.
    intros; congruence.
  Qed.

  Lemma rt_subkind_sound κ κ' :
    clos_refl_trans _ subkind_of κ κ' ->
    kind_as_type_interp (Σ := Σ) sr κ ⊑ kind_as_type_interp sr κ'.
  Proof. 
    intros H.
    induction H.
    - by apply subkind_sound.
    - by apply semantic_type_le_refl.
    - by eapply semantic_type_le_trans.
  Qed.

  Lemma subst_interp_kinds_map κs s__mem s__rep s__size se :
    ⊢ sem_env_interp sr mr κs s__mem s__rep s__size se -∗
    ⌜ map fst se = map (subst_kind s__mem s__rep s__size) κs⌝.
  Proof.
  Admitted.

  Theorem kinding_refinement F s__mem s__rep s__size se τ κ : 
    has_kind F τ κ ->
    subst_env_interp sr mr F s__mem s__rep s__size se
    ⊢ ⌜value_interp sr mr se (subst_type s__mem s__rep s__size VarT τ) ⊑
         kind_as_type_interp sr (subst_kind s__mem s__rep s__size κ)⌝.
  Proof.
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
  Qed.
  
  Instance kind_as_type_persistent κ sv :
    @Persistent (iProp Σ) (kind_as_type_interp sr κ sv).
  Proof.
    destruct κ, sv; cbn; try typeclasses eauto.
    - unfold representation_interp.
      destruct (eval_rep r); typeclasses eauto.
    - unfold representation_interp.
      destruct (eval_rep r); typeclasses eauto.
  Qed.

  Instance copyability_proper : Proper (eq ==> eq ==> eq ==> equiv ==> equiv) copyability_interp.
  Admitted.

  Lemma value_interp_var (se: semantic_env) (t: nat) (κ: kind) (T: semantic_type) :
    se !! t = Some (κ, T) ->
    value_interp sr mr se (VarT t) ≡ (λne sv, kind_as_type_interp sr κ sv ∗ T sv)%I.
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

  Lemma explicit_copy_prim_reps_interp ιs :
    ⊢ explicit_copy_spec mr ιs (prim_reps_interp sr ιs).
  Proof.
  Admitted.

  Lemma copyability_kind ρ ιs χ δ :
    eval_rep ρ = Some ιs ->
    ⊢ copyability_interp mr ρ χ (kind_as_type_interp sr (VALTYPE ρ χ δ)).
  Proof.
    unfold copyability_interp.
    intros H.
    rewrite H.
    destruct χ.
    - auto.
    - unfold kind_as_type_interp.
      cbn.
      unfold representation_interp.
      rewrite H.
      apply explicit_copy_prim_reps_interp.
    - iIntros "!% %sv".
      apply kind_as_type_persistent.
  Qed.

  Lemma copyability_sep ρ χ S T :
    ⊢ copyability_interp mr ρ χ S -∗
      copyability_interp mr ρ χ T -∗
      copyability_interp mr ρ χ (λne sv, S sv ∗ T sv).
  Proof.
    destruct χ; cbn.
    - auto.
    - admit.
    - iIntros "%HS %HT !% %sv".
      typeclasses eauto.
  Admitted.

  Theorem kinding_copyable F s__mem s__rep s__size se τ ρ χ δ : 
    has_kind F τ (VALTYPE ρ χ δ) ->
    subst_env_interp sr mr F s__mem s__rep s__size se
    ⊢ copyability_interp mr (subst_representation s__rep ρ) χ (value_interp sr mr se (subst_type s__mem s__rep s__size VarT τ)).
  Proof.
    intros Hkind.
    remember (VALTYPE ρ χ δ) as κ.
    revert Heqκ.
    revert ρ χ δ.
    induction Hkind; intros ? ? ? Hκeq; rewrite -> Hκeq in *;
      iIntros "[%Hsubst Henv]"; try subst κ; try subst κ'.
    - inversion H; subst; eauto.
      + specialize (IHHkind _ _ _ eq_refl).
        cbn in IHHkind.
        admit.
      + iApply IHHkind; eauto.
        by iFrame.
      + iApply IHHkind; eauto.
        by iFrame.
    - simpl subst_type.
      unfold sem_env_interp.
      iPoseProof (big_sepL2_length with "Henv") as "%Hlen".
      assert (Hκt': exists κt', se !! t = Some κt').
      {
        apply lookup_lt_is_Some.
        rewrite Hlen.
        apply lookup_lt_is_Some.
        eauto.
      }
      destruct Hκt' as [[κt' T] Hκt'].
      iPoseProof (big_sepL2_lookup_acc with "Henv") as "[[%Hκsubst Hκinterp] Henv]"; eauto.
      cbn in *; subst.
      rewrite value_interp_var; eauto.
      iApply (copyability_sep ).
      + iApply copyability_kind.
        admit.
      + cbn.
        iDestruct "Hκinterp" as "[_ Hcopy]".
        iFrame.
    - unfold copyability_interp; inversion Hκeq; subst; eauto.
      cbn.
      iIntros "%sv !%".
      rewrite value_interp_eq; cbn.
      typeclasses eauto.
    - unfold copyability_interp; inversion Hκeq; subst; eauto.
      iIntros "%sv !%".
      rewrite value_interp_eq; cbn.
      typeclasses eauto.
    - unfold copyability_interp; inversion Hκeq; subst; eauto.
      iIntros "%sv !%".
      rewrite value_interp_eq; cbn; typeclasses eauto.
    - unfold copyability_interp; inversion Hκeq; subst; eauto.
      iIntros "%sv !%".
      rewrite value_interp_eq; cbn; typeclasses eauto.
    - unfold copyability_interp; inversion Hκeq; subst; eauto.
      iIntros "%sv !%".
      rewrite value_interp_eq; cbn; typeclasses eauto.
    - admit. (* sums *)
    - inversion Hκeq; subst; eauto.
    - inversion Hκeq; subst; eauto.
    - admit. (* products *)
    - inversion Hκeq; subst; eauto.
    - inversion Hκeq; subst; eauto.
    - inversion Hκeq; subst; eauto.
    - inversion Hκeq; subst; eauto.
    - admit. (* refs *)
    - inversion Hκeq; subst.
    - admit. (* coderef *)
    - cbn in *. 
      admit.
    - unfold copyability_interp; inversion Hκeq; subst; eauto.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Theorem kinding_sound F s__mem s__rep s__size se τ κ : 
    has_kind F τ κ ->
    subst_env_interp sr mr F s__mem s__rep s__size se
    ⊢ kind_interp sr mr (subst_kind s__mem s__rep s__size κ)
                        (value_interp sr mr se (subst_type s__mem s__rep s__size VarT τ)).
  Proof.
    intros Hkind. 
    revert s__mem s__rep s__size se.
    iIntros "* Hsubst".
    iSplit.
    - iApply kinding_refinement; eauto.
    - destruct κ; [| done].
      cbn.
      iApply kinding_copyable; eauto.
  Qed.

End FundamentalKinding.
