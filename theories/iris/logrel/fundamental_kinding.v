(* Fundamental theorem for the kind system:
     well-kinded syntactic types are semantically well-kinded *)

From iris.proofmode Require Import base tactics classes.
From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import codegen instrs modules util.
From RichWasm.iris Require Import autowp gc.
From RichWasm.iris.logrel Require Import relations.
From Stdlib Require Import Relations.Relation_Operators.

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
  Admitted.

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
  Admitted.

  Lemma rt_subkind_sound κ κ' :
    clos_refl_trans _ subkind_of κ κ' ->
    kind_as_type_interp (Σ := Σ) sr κ ⊑ kind_as_type_interp sr κ'.
  Proof. 
  Admitted.
  
  Lemma has_kind_subst F τ κ s__mem s__rep s__size :
    has_kind F τ κ ->
    subst_interp F.(fc_kind_ctx) s__mem s__rep s__size ->
    has_kind fc_empty (subst_type s__mem s__rep s__size VarT τ) (subst_kind s__mem s__rep s__size κ).
  Proof.
  Admitted.

  Theorem kinding_refinement F s__mem s__rep s__size se τ κ : 
    has_kind F τ κ ->
    subst_env_interp sr F s__mem s__rep s__size se
    ⊢ ⌜value_interp sr mr se (subst_type s__mem s__rep s__size VarT τ) ⊑
         kind_as_type_interp sr (subst_kind s__mem s__rep s__size κ)⌝.
  Proof.
    iIntros "%Hhas_kind [%Hsubst _]".
    iPureIntro.
    intros sv.
    iIntros "Hval".
    rewrite value_interp_eq.
    iDestruct "Hval" as "(%κ' & %Htyk & Hinterp & _)".
    eapply has_kind_subst in Hhas_kind; eauto.
    eapply (type_kind_has_kind_agree fc_empty) in Hhas_kind; eauto.
    iApply rt_subkind_sound; eauto.
  Qed.

  Theorem kinding_copyable F s__mem s__rep s__size se τ ρ χ δ : 
    has_kind F τ (VALTYPE ρ χ δ) ->
    subst_env_interp sr F s__mem s__rep s__size se
    ⊢ copyability_interp (subst_representation s__rep ρ) χ (value_interp sr mr se (subst_type s__mem s__rep s__size VarT τ)).
  Proof.
    intros Hkind.
    remember (VALTYPE ρ χ δ) as κ.
    revert Heqκ.
    revert ρ χ δ.
    induction Hkind; intros ? ? ? Hκeq; rewrite -> Hκeq in *;
      iIntros "[%Hsubst Henv]"; unfold copyability_interp;
      try (subst κ; inversion Hκeq; subst).
    - subst.
      admit.
    - assert (Ht: exists Tt, se !! t = Some Tt) by admit.
      destruct Ht as [Tt Ht].
      eapply big_sepL2_lookup_acc in H; eauto.
      iPoseProof (H with "Henv") as "[H _]".
      iDestruct "H" as "[%Ht' Ht'']".
      remember (value_interp _ _ _ _) as T.
      assert (T ≡ Tt).
      {
        rewrite HeqT.
        cbn.
        intros x.
        rewrite value_interp_eq.
        cbn.
        rewrite Ht; cbn.
        admit.
      }
      admit.
    - iIntros "%sv !%".
      rewrite value_interp_eq; cbn.
      eapply bi.exist_persistent; intros κ.
      destruct κ; cbn; typeclasses eauto.
    - iIntros "%sv !%".
      rewrite value_interp_eq; cbn.
      eapply bi.exist_persistent; intros κ.
      destruct κ; cbn; typeclasses eauto.
    - iIntros "%sv !%".
      rewrite value_interp_eq; cbn.
      eapply bi.exist_persistent; intros κ.
      destruct κ; cbn; typeclasses eauto.
    - iIntros "%sv !%".
      rewrite value_interp_eq; cbn.
      eapply bi.exist_persistent; intros κ.
      destruct κ; cbn; typeclasses eauto.
    - admit.
    - admit.
    - auto.
    - auto.
    - admit. (* explicit copy *)
    - admit. (* function type stuff...? *)
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Theorem kinding_sound F s__mem s__rep s__size se τ κ : 
    has_kind F τ κ ->
    subst_env_interp sr F s__mem s__rep s__size se
    ⊢ kind_interp sr (subst_kind s__mem s__rep s__size κ)
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
