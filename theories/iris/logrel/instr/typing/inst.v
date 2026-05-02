Require Import RichWasm.iris.logrel.instr.typing.common.
Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section inst.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Definition mem_ok_se (se : semantic_env) (μ : Core.memory) : Prop :=
    match μ with
    | VarM i => i < length (senv_mems (Σ:=Σ) se)
    | BaseM _ => True
    end.

  Lemma mem_ok_se_up_mem μ se sub_m i :
    mem_ok_se se (sub_m i) <->
      mem_ok_se (senv_insert_mem μ se) (up_memory_memory sub_m (S i)).
  Proof.
    unfold mem_ok_se.
    assert (Hope: ren_memory unscoped.shift (sub_m i) = up_memory_memory sub_m (S i)) by by substify.
    split.
    {
      intros H.
      rewrite <- Hope.
      cbn.
      destruct (sub_m i) eqn:Hsubi.
      - cbn. unfold unscoped.shift. cbn in H. lia.
      - cbn. auto.
    }
    {
      intros H.
      rewrite <- Hope in H.
      cbn in *.
      destruct (sub_m i) eqn:Hsubi.
      - cbn in H. unfold unscoped.shift in H. lia.
      - auto.
    }
  Qed.

  Lemma mem_ok_se_up_rep ρ se sub_m i :
    mem_ok_se se (sub_m i) <->
      mem_ok_se (senv_insert_rep ρ se) (up_representation_memory sub_m i).
  Proof.
    unfold mem_ok_se.
    split.
    {
      intros H.
      unfold up_representation_memory, core.funcomp.
      by rewrite rinstId'_memory.
    }
    {
      intros H.
      unfold up_representation_memory, core.funcomp in H.
      by rewrite rinstId'_memory in H.
    }
  Qed.

  Lemma mem_ok_se_up_size ρ se sub_m i :
    mem_ok_se se (sub_m i) <->
      mem_ok_se (senv_insert_size ρ se) (up_size_memory sub_m i).
  Proof.
    unfold mem_ok_se.
    split.
    {
      intros H.
      unfold up_size_memory, core.funcomp.
      by rewrite rinstId'_memory.
    }
    {
      intros H.
      unfold up_size_memory, core.funcomp in H.
      by rewrite rinstId'_memory in H.
    }
  Qed.

  Lemma mem_ok_se_up_type sκ T se sub_m i :
    mem_ok_se se (sub_m i) <->
      mem_ok_se (senv_insert_type sκ T se) (up_type_memory sub_m i).
  Proof.
    unfold mem_ok_se.
    split.
    {
      intros H.
      unfold up_type_memory, core.funcomp.
      by rewrite rinstId'_memory.
    }
    {
      intros H.
      unfold up_type_memory, core.funcomp in H.
      by rewrite rinstId'_memory in H.
    }
  Qed.

  (* moved type_skind_has_kind_Some to kinding.v *)

  Ltac shred_for_up_mini n2 Hn2 :=
      apply fmap_Some;
      exists n2; split; last done;
      apply mapM_Some in Hn2;
      apply mapM_Some;
      eapply Forall2_mini_impl_Forall; first done;
      done.
  Ltac shred_for_up n2 Hn2 :=
      apply fmap_Some;
      exists n2; split; last done;
      apply mapM_Some in Hn2;
      apply mapM_Some;
      rewrite <- (list_fmap_id n2);
      rewrite map_fmap;
      apply Forall2_fmap;
      eapply Forall2_mini_impl_Forall; first done;
      done.

  Lemma eval_rep_mem_irrel se ρ ιs μ :
    eval_rep se ρ = Some ιs ->
    eval_rep (senv_insert_mem (Σ:=Σ) μ se) ρ = Some ιs.
  Proof.
    revert ιs.
    induction ρ using rep_ind; intros; auto.
    - cbn in *.
      apply fmap_Some in H0 as (ρss & H02 & ->).
      shred_for_up_mini ρss H02.
    - cbn in *.
      apply fmap_Some in H0 as (ιss & H02 & ->).
      shred_for_up_mini ιss H02.
  Qed.

  Lemma eval_rep_size_irrel se ρ ιs n :
    eval_rep se ρ = Some ιs ->
    eval_rep (senv_insert_size (Σ:=Σ) n se) ρ = Some ιs.
  Proof.
    revert ιs.
    induction ρ using rep_ind; intros; auto.
    - cbn in *.
      apply fmap_Some in H0 as (ρss & H02 & ->).
      shred_for_up_mini ρss H02.
    - cbn in *.
      apply fmap_Some in H0 as (ιss & H02 & ->).
      shred_for_up_mini ιss H02.
  Qed.

  Lemma eval_rep_type_irrel se ρ ιs sκ T :
    eval_rep se ρ = Some ιs ->
    eval_rep (senv_insert_type (Σ:=Σ) sκ T se) ρ = Some ιs.
  Proof.
    revert ιs.
    induction ρ using rep_ind; intros; auto.
    - cbn in *.
      apply fmap_Some in H0 as (ρss & H02 & ->).
      shred_for_up_mini ρss H02.
    - cbn in *.
      apply fmap_Some in H0 as (ιss & H02 & ->).
      shred_for_up_mini ιss H02.
  Qed.

  Lemma eval_size_mem_irrel se σ n μ :
    eval_size se σ = Some n ->
    eval_size (senv_insert_mem (Σ:=Σ) μ se) σ = Some n.
  Proof.
    revert n.
    induction σ using size_ind; intros; auto.
    - cbn in *.
      apply fmap_Some in H0 as (ρss & H02 & ->).
      shred_for_up_mini ρss H02.
    - cbn in *.
      apply fmap_Some in H0 as (ρss & H02 & ->).
      shred_for_up_mini ρss H02.
    - cbn in *.
      apply fmap_Some in H as (ρss & H02 & ->).
      apply fmap_Some.
      exists ρss; split; last done.
      by apply eval_rep_mem_irrel.
  Qed.

  Lemma eval_size_type_irrel se σ n sκ T :
    eval_size se σ = Some n ->
    eval_size (senv_insert_type (Σ:=Σ) sκ T se) σ = Some n.
  Proof.
    revert n.
    induction σ using size_ind; intros; auto.
    - cbn in *.
      apply fmap_Some in H0 as (ρss & H02 & ->).
      shred_for_up_mini ρss H02.
    - cbn in *.
      apply fmap_Some in H0 as (ρss & H02 & ->).
      shred_for_up_mini ρss H02.
    - cbn in *.
      apply fmap_Some in H as (ρss & H02 & ->).
      apply fmap_Some.
      exists ρss; split; last done.
      by apply eval_rep_type_irrel.
  Qed.

  Lemma eval_kind_mem_irrel se κ sκ μ :
    eval_kind se κ = Some sκ ->
    eval_kind (senv_insert_mem (Σ:=Σ) μ se) κ = Some sκ.
  Proof.
    revert sκ.
    destruct κ; intros; cbn in *.
    - apply fmap_Some in H as (ρss & H02 & ->).
      apply fmap_Some.
      pose proof (eval_rep_mem_irrel _ _ _ μ H02).
      rewrite H. eexists; split; done.
    - apply fmap_Some in H as (ρss & H02 & ->).
      apply fmap_Some.
      pose proof (eval_size_mem_irrel _ _ _ μ H02).
      rewrite H. eexists; split; done.
  Qed.

  Lemma eval_kind_type_irrel se κ sκ sκ' T :
    eval_kind se κ = Some sκ ->
    eval_kind (senv_insert_type (Σ:=Σ) sκ' T se) κ = Some sκ.
  Proof.
    revert sκ.
    destruct κ; intros; cbn in *.
    - apply fmap_Some in H as (ρss & H02 & ->).
      apply fmap_Some.
      pose proof (eval_rep_type_irrel _ _ _ sκ' T H02).
      rewrite H. eexists; split; done.
    - apply fmap_Some in H as (ρss & H02 & ->).
      apply fmap_Some.
      pose proof (eval_size_type_irrel _ _ _ sκ' T H02).
      rewrite H. eexists; split; done.
  Qed.

  Lemma type_skind_mem_irrel se μ τ sκ :
    type_skind (Σ:=Σ) se τ = Some sκ ->
    type_skind (Σ:=Σ) (senv_insert_mem μ se)
      (ren_type unscoped.shift unscoped.id unscoped.id unscoped.id τ) = Some sκ.
  Proof.
    revert sκ.
    destruct τ.
    1: done.
    all: intros; cbn in *.
    all: rewrite rinstId'_kind.
    all: unfold eval_kind in *.
    all: by apply eval_kind_mem_irrel.
  Qed.

  Lemma eval_rep_up_rep se sub_r ιs0 i ιs :
    eval_rep se (sub_r i) = Some ιs ->
    eval_rep (senv_insert_rep (Σ:=Σ) ιs0 se) (up_representation_representation sub_r (S i)) = Some ιs.
  Proof.
    intros H.
    asimpl'.
    unfold core.funcomp, unscoped.scons.

    generalize dependent ιs.
    induction (sub_r i) using rep_ind.
    - done.
    - intros; cbn in *.
      apply fmap_Some in H0 as (n2 & Hn2 & ->).
      shred_for_up n2 Hn2.
    - intros; cbn in *.
      apply fmap_Some in H0 as (n2 & Hn2 & ->).
      shred_for_up n2 Hn2.
    - intros; by cbn in *.
  Qed.

  Lemma eval_rep_up_size se sub_r ιs i n :
    eval_rep se (sub_r i) = Some ιs ->
    eval_rep (senv_insert_size (Σ:=Σ) n se) (up_size_representation sub_r i) = Some ιs.
  Proof.
    asimpl'.
    by apply eval_rep_size_irrel.
  Qed.

  Lemma eval_rep_up_memory se sub_r ιs i μ :
    eval_rep se (sub_r i) = Some ιs ->
    eval_rep (senv_insert_mem (Σ:=Σ) μ se) (up_memory_representation sub_r i) = Some ιs.
  Proof.
    asimpl'.
    by apply eval_rep_mem_irrel.
  Qed.

  Lemma eval_size_up_memory se sub_s n i μ :
    eval_size se (sub_s i) = Some n ->
    eval_size (senv_insert_mem (Σ:=Σ) μ se) (up_memory_size sub_s i) = Some n.
  Proof.
    asimpl'.
    by apply eval_size_mem_irrel.
  Qed.

  Lemma eval_size_up_rep se sub_s ιs i n :
    eval_size se (sub_s i) = Some n ->
    eval_size (senv_insert_rep (Σ:=Σ) ιs se) (up_representation_size sub_s i) = Some n.
  Proof.
    intros H.
    asimpl'.
    unfold core.funcomp.
    generalize dependent n.

    induction (sub_s i) using size_ind.
    - intros; done.
    - intros; cbn in *.
      apply fmap_Some in H0 as (n2 & Hn2 & ->).
      shred_for_up n2 Hn2.
    - intros; cbn in *.
      apply fmap_Some in H0 as (n2 & Hn2 & ->).
      shred_for_up n2 Hn2.
    - intros.
      apply fmap_Some in H as (n2 & Hn2 & ->).
      apply fmap_Some.
      exists n2; split; last done.
      generalize dependent n2.
      clear i.
      clear sub_s.
      induction ρ using rep_ind; intros; cbn in *; auto.
      + rename n2 into n; rename Hn2 into Hn.
        apply fmap_Some in Hn as (ιss & Hιss & ->).
        shred_for_up ιss Hιss.
      + rename n2 into n; rename Hn2 into Hn.
        apply fmap_Some in Hn as (ιss & Hιss & ->).
        shred_for_up ιss Hιss.
    - intros; by cbn in *.
  Qed.

  Lemma eval_rep_up_shift_rep se ρ n ιs :
    eval_rep se ρ = Some n ->
    eval_rep (senv_insert_rep (Σ:=Σ) ιs se) (ren_representation unscoped.shift ρ) = Some n.
  Proof.
    generalize dependent n.
    induction ρ using rep_ind.
    - intros; cbn in *; done.
    - intros; cbn in *.
      apply fmap_Some in H0 as (ns & Hns & ->).
      shred_for_up ns Hns.
    - intros; cbn in *.
      apply fmap_Some in H0 as (ns & Hns & ->).
      shred_for_up ns Hns.
    - intros; by cbn in *.
  Qed.

  Lemma eval_kind_up_shift_rep se κ sκ ιs :
    eval_kind se κ = Some sκ ->
    eval_kind (senv_insert_rep (Σ:=Σ) ιs se) (ren_kind unscoped.shift unscoped.id κ) = Some sκ.
  Proof.
    generalize dependent sκ.
    destruct κ as [ρ ξ | σ ξ].
    - intros; cbn in *.
      apply bind_Some in H as (sρ & Hsρ & toinvert).
      inversion toinvert; subst; clear toinvert.
      apply bind_Some.
      exists sρ; split; auto.
      by apply eval_rep_up_shift_rep.
    - intros; cbn in *.
      apply bind_Some in H as (sσ & Hsσ & toinvert).
      inversion toinvert; subst; clear toinvert.
      apply bind_Some.
      exists sσ; split; auto.
      generalize dependent sσ.
      induction σ using size_ind.
      + intros; cbn in *; done.
      + intros; cbn in *.
        apply fmap_Some in Hsσ as (ns & Hns & ->).
        shred_for_up ns Hns.
      + intros; cbn in *.
        apply fmap_Some in Hsσ as (ns & Hns & ->).
        shred_for_up ns Hns.
      + intros; cbn in *.
        apply fmap_Some in Hsσ as (n & Hn & ->).
        apply fmap_Some.
        exists n; split; auto.
        cbn.
        by apply eval_rep_up_shift_rep.
      + intros; by cbn in *.
  Qed.

  Lemma type_skind_up_rep se sub_t ιs sκ i :
    type_skind se (sub_t i) = Some sκ ->
    type_skind (Σ:=Σ) (senv_insert_rep ιs se) (up_representation_type sub_t i) = Some sκ.
  Proof.
    intros H.
    asimpl'.
    unfold core.funcomp.
    generalize dependent sκ.
    induction (sub_t i) using type_ind with (P0 := λ ft, True);
      intros; cbn in *; auto; try (by apply eval_kind_up_shift_rep).
  Qed.

  Lemma type_skind_up_memory se sub_t μ sκ i :
    type_skind se (sub_t i) = Some sκ ->
    type_skind (Σ:=Σ) (senv_insert_mem μ se) (up_memory_type sub_t i) = Some sκ.
  Proof.
    intros H.
    asimpl'.
    unfold core.funcomp.
    generalize dependent sκ.
    induction (sub_t i) using type_ind with (P0 := λ ft, True);
      intros; cbn in *; auto; asimpl'; try (by apply eval_kind_mem_irrel).
  Qed.

  Lemma type_skind_up_type se sub_t sκ' T sκ i :
    type_skind se (sub_t i) = Some sκ ->
    type_skind (Σ:=Σ) (senv_insert_type sκ' T se) (up_type_type sub_t (S i)) = Some sκ.
  Proof.
    intros H.
    asimpl'.
    unfold core.funcomp.
    generalize dependent sκ.
    induction (sub_t i) using type_ind with (P0 := λ ft, True).
    all: intros; cbn in *; auto; asimpl'.
    all: try (by apply eval_kind_type_irrel).
  Qed.


  (** STARTING FROM HERE, we begin to have these assumptions about how substitutions and semantic envs
      relate to one another. These relations are strong enough to prove the necessary subsitution
      lemmas, and weak enough to be proven about the outermost substitution we're working on. *)

  Definition sem_env_rel_rep (se' : @semantic_env Σ) (se : @semantic_env Σ) (sub_r:nat → representation) :=
    (forall i ιs', lookup_rep se' i = Some ιs' -> eval_rep se (sub_r i) = Some ιs').
  Definition sem_env_rel_size (se' : @semantic_env Σ) (se : @semantic_env Σ) (sub_s:nat → Core.size) :=
    (forall i n, lookup_size se' i = Some n -> eval_size se (sub_s i) = Some n).
  Definition sem_env_rel_type (se' : @semantic_env Σ) (se : @semantic_env Σ) (sub_t:nat → type) :=
    (forall i sκ' T', lookup_type se' i = Some (sκ', T') ->
    type_skind se (sub_t i) = Some sκ' /\
      (∀ sv, (T' sv -∗ ⌜skind_has_svalue sκ' sv⌝ -∗ value_interp rti sr se (sub_t i) sv))).
  Definition sem_env_rel_sκ (se' : @semantic_env Σ) (se : @semantic_env Σ) (sub_t:nat → type) :=
    (forall i sκ', fst <$> lookup_type se' i = Some sκ' ->
    type_skind se (sub_t i) = Some sκ').

  Lemma rel_type_implies_rel_sκ se' se sub_t :
    sem_env_rel_type se' se sub_t -> sem_env_rel_sκ se' se sub_t.
  Proof.
    unfold sem_env_rel_type, sem_env_rel_sκ; intros.
    apply fmap_Some in H0 as ((sκ & T) & Hlookup & b).
    cbn in b. subst sκ.
    by apply H in Hlookup as (H0 & _).
  Qed.

  Ltac unfold_sem_rels := unfold sem_env_rel_rep, sem_env_rel_size, sem_env_rel_type, sem_env_rel_sκ in *.



  Lemma eval_rep_subst_senv (se se' : semantic_env (Σ:=Σ)) sub_r ρ ιs :
    sem_env_rel_rep se' se sub_r ->
    eval_rep se' ρ = Some ιs ->
    eval_rep se (subst_representation sub_r ρ) = Some ιs.
  Proof.
    intros Hsub_r; unfold_sem_rels.
    generalize dependent ιs.
    induction ρ as [n|ρs IH|ρs IH|ιs'] using rep_ind.
    - intros ? H. cbn in *. by apply Hsub_r.
    - intros ? H.
      cbn in *.
      apply fmap_Some in H as (ιss & Hρs & ->).
      shred_for_up ιss Hρs.
    - intros ??; cbn in *.
      apply fmap_Some in H as (ιss & Hρs & ->).
      shred_for_up ιss Hρs.
    - intros ??; cbn in *; done.
  Qed.

  Lemma eval_size_subst_env (se se' : semantic_env (Σ:=Σ)) sub_r sub_s σ n :
    sem_env_rel_rep se' se sub_r ->
    sem_env_rel_size se' se sub_s ->
    eval_size se' σ = Some n ->
    eval_size se (subst_size sub_r sub_s σ) = Some n.
  Proof.
    intros Hsub_r Hsub_s; unfold_sem_rels.
    generalize dependent n.
    induction σ using size_ind.
    - intros ? H. cbn in *. by apply Hsub_s.
    - intros ??; cbn in *.
      apply fmap_Some in H0 as (n2 & Hn2 & ->).
      shred_for_up n2 Hn2.
    - intros ??; cbn in *.
      apply fmap_Some in H0 as (n2 & Hn2 & ->).
      shred_for_up n2 Hn2.
    - intros ??.
      cbn in *.
      apply fmap_Some in H as (ιss & Hρ & ->).
      apply fmap_Some.
      eexists.
      split; last done.
      eapply eval_rep_subst_senv; last done.
      unfold_sem_rels; apply Hsub_r.
    - done.
  Qed.

  Lemma eval_kind_subst_senv (se se' : semantic_env (Σ:=Σ)) sub_r sub_s κ sκ :
    sem_env_rel_rep se' se sub_r ->
    sem_env_rel_size se' se sub_s ->
    eval_kind se' κ = Some sκ ->
    eval_kind se (subst_kind sub_r sub_s κ) = Some sκ.
  Proof.
    unfold eval_kind; unfold_sem_rels.
    intros Hsub_r Hsub_s H.
    destruct κ as [ρ rf|σ rf].
    - apply bind_Some in H as (ιs & Hρ & <-).
      apply bind_Some.
      eexists.
      split; last done.
      by eapply eval_rep_subst_senv.
    - apply bind_Some in H as (n & Hσ & <-).
      apply bind_Some.
      eexists.
      split; last done.
      by eapply eval_size_subst_env.
  Qed.

  (* Later: move this to kinding.v? *)
  Lemma skind_rep_subskinds sκ sκ' ιs:
    skind_rep sκ = Some ιs -> subskind_of sκ' sκ -> skind_rep sκ' = Some ιs.
  Proof.
    intros.
    destruct sκ; inversion H; subst.
    destruct sκ'; inversion H0; subst.
    by cbn.
  Qed.

  (* This is safe now *)
  Lemma type_skind_subst_senv se se' sub_m sub_r sub_s sub_t τ sκ :
    sem_env_rel_rep se' se sub_r ->
    sem_env_rel_size se' se sub_s ->
    sem_env_rel_sκ se' se sub_t ->
    type_skind (Σ:=Σ) se' τ = Some sκ ->
    type_skind (Σ:=Σ) se (subst_type sub_m sub_r sub_s sub_t τ) = Some sκ.
  Proof.
    unfold type_skind; unfold_sem_rels.
    intros Hsub_r Hsub_s Hsub_t H.
    destruct τ.
    1: by apply Hsub_t.
    (* all: exists sκ; split; [|by apply subskind_of_refl]; by eapply eval_kind_subst_senv. *)
    all: cbn.
    all: by eapply eval_kind_subst_senv.
  Qed.

  Lemma type_arep_subst_senv se se' sub_m sub_r sub_s sub_t τ ιs :
    sem_env_rel_rep se' se sub_r ->
    sem_env_rel_size se' se sub_s ->
    sem_env_rel_sκ se' se sub_t ->
    type_arep (Σ:=Σ) se' τ = Some ιs ->
    type_arep (Σ:=Σ) se (subst_type sub_m sub_r sub_s sub_t τ) = Some ιs.
  Proof.
    unfold type_arep; unfold_sem_rels.
    intros Hsub_r Hsub_s Hsub_t H.
    apply bind_Some in H as (sκ & Hsκ & Hιs).
    apply bind_Some.
    pose proof (type_skind_subst_senv se se' sub_m sub_r sub_s sub_t _ _ Hsub_r Hsub_s Hsub_t Hsκ)
      as Hsκ'.
    exists sκ.
    split; done.
  Qed.

  Lemma translate_type_subst_senv se se' sub_m sub_r sub_s sub_t τ ts :
    sem_env_rel_rep se' se sub_r ->
    sem_env_rel_size se' se sub_s ->
    sem_env_rel_sκ se' se sub_t ->
    translate_type (Σ:=Σ) se' τ = Some ts ->
    translate_type (Σ:=Σ) se (subst_type sub_m sub_r sub_s sub_t τ) = Some ts.
  Proof.
    unfold translate_type; unfold_sem_rels.
    intros Hsub_r Hsub_s Hsub_t H.
    apply fmap_Some in H as (ιs & H & ->).
    apply fmap_Some.
    eexists.
    split; last done.
    by eapply type_arep_subst_senv.
  Qed.

  Lemma translate_types_subst_senv se se' sub_m sub_r sub_s sub_t τs ts :
    sem_env_rel_rep se' se sub_r ->
    sem_env_rel_size se' se sub_s ->
    sem_env_rel_sκ se' se sub_t ->
    translate_types (Σ:=Σ) se' τs = Some ts ->
    translate_types (Σ:=Σ) se (map (subst_type sub_m sub_r sub_s sub_t) τs) = Some ts.
  Proof.
    unfold translate_types; unfold_sem_rels.
    intros Hsub_r Hsub_s Hsub_t H.
    apply fmap_Some in H as (tss & H & ->).
    apply fmap_Some.
    eexists.
    split; last done.
    apply mapM_Some in H.
    apply mapM_Some.
    rewrite <- (list_fmap_id tss).
    rewrite map_fmap.
    apply Forall2_fmap.
    eapply Forall2_impl; first done.
    clear H.
    intros τ ts H.
    cbn in H.
    by eapply translate_type_subst_senv.
  Qed.

  Lemma map_lookup_helper {A B:Type} (f:A → B) (l: list A) (i:nat) (a:A) :
    l !! i = Some a -> map f l !! i = Some (f a).
  Proof.
    (* obvious, prove later *)
  Admitted.

  Lemma ref_flag_le_preserves_atoms_interp ξ ξ' os:
    ref_flag_le ξ ξ' -> ref_flag_atoms_interp ξ (SAtoms os) ->
    ref_flag_atoms_interp ξ' (SAtoms os).
  Proof.
    intros.
    destruct ξ, ξ'; try done.
    - destruct H0 as (os0 & toinvert & H0); inversion toinvert; subst os0; clear toinvert.
      exists os; split; [done|].
      unfold ref_flag_interp in *.
      unfold norefs_ptr_interp in H0.
      unfold gcrefs_ptr_interp.
      (* yup okay true *)
      admit.
    - destruct H0 as (os0 & toinvert & H0); inversion toinvert; subst os0; clear toinvert.
      exists os; split; [done|].
      unfold ref_flag_interp in *.
      unfold norefs_ptr_interp in H0.
      (* yup also true *)
      admit.
    - destruct H0 as (os0 & toinvert & H0); inversion toinvert; subst os0; clear toinvert.
      exists os; split; [done|].
      unfold ref_flag_interp in *.
      unfold gcrefs_ptr_interp in H0.
      (* also true *)
      admit.
  Admitted.


  (* As mentioned in a lower comment, this might require an additional assumption *)
  (* this is also now safe from contamination :3 *)
  Lemma values_interp_subst_type se se' τs os sub_m sub_r sub_s sub_t :
    (sem_env_rel_rep se' se sub_r) ->
    (sem_env_rel_size se' se sub_s) ->
    (sem_env_rel_type se' se sub_t) ->
    values_interp rti sr se' τs os -∗
    values_interp rti sr se (map (subst_type sub_m sub_r sub_s sub_t) τs) os.
  Proof.
    iIntros (Hsub_r Hsub_s Hsub_T).
    pose proof (rel_type_implies_rel_sκ se' se sub_t Hsub_T) as Hsub_t.
    (* comment/uncomment if you want/dont' want to see them *)
    unfold_sem_rels.
    generalize dependent os; generalize dependent τs.
    induction τs as [| τ τs].
    - intros os. iIntros "Hos". destruct os; done.
    - intros os_big; iIntros "Hos".
      cbn.
      iDestruct "Hos" as "(%oss_big & %Hos_big & Hos)".
      destruct oss_big as [|o oss]; [done|].
      rewrite big_sepL2_cons.
      rewrite big_sepL2_fmap_l.
      iDestruct "Hos" as "[Hoa Hτsoss]".
      cbn in IHτs.
      setoid_rewrite big_sepL2_fmap_l in IHτs.
      specialize (IHτs (concat oss)).
      iDestruct IHτs as "#IHτs".
      iAssert (∃ oss0, ⌜concat oss = concat oss0⌝ ∗
            ([∗ list] τ0;os ∈ τs;oss0, value_interp rti sr se' τ0 (SAtoms os)))%I with "[Hτsoss]"
        as "Hτs'". {
        iExists oss; iSplitR; done.
      }
      iPoseProof ("IHτs" with "[$Hτs']") as "Hτs''".
      iDestruct "Hτs''" as "(%oss' & %Hc & Hτoss')".
      (* note: concat oss = concat oss' does not simply oss = oss'. A bit stupid but okay. *)

      iExists (o :: oss'); iSplitR. {
        iPureIntro.
        rewrite concat_cons; rewrite concat_cons in Hos_big. by rewrite <- Hc.
      }
      iApply big_sepL2_cons.
      rewrite !big_sepL2_fmap_l.
      iSplitL "Hoa"; first last.
      + done.
        (* I could have said first done but then there'd be so many bullets to change... *)
      + (* this is where the fun begins *)
        iClear "IHτs".
        clear IHτs Hos_big Hc os_big oss τs Hsub_t.
        generalize dependent o.
        generalize dependent se'.
        generalize dependent se.
        generalize dependent sub_m.
        generalize dependent sub_s.
        generalize dependent sub_r.
        generalize dependent sub_t.
        generalize dependent τ.
        induction τ using type_ind with
          (P0 := λ ft, ∀ se se' cl sub_m sub_r sub_s sub_t,
               sem_env_rel_rep se' se sub_r ->
               sem_env_rel_size se' se sub_s ->
               sem_env_rel_type se' se sub_t ->
               (* (forall i ιs', lookup_rep se' i = Some ιs' -> eval_rep se (sub_r i) = Some ιs') -> *)
               (* (forall i n, lookup_size se' i = Some n -> eval_size se (sub_s i) = Some n) -> *)
               (* (forall i sκ', fst <$> lookup_type se' i = Some sκ' -> *)
               (*     type_skind se (sub_t i) = Some sκ') -> *)
               closure_interp rti sr ft se' cl -∗
               closure_interp rti sr (subst_function_type sub_m sub_r sub_s sub_t ft) se cl).
        * (** vart, need extra hypothesis about semantic types *)
          intros; cbn in *.
          iDestruct "Hoa" as "(%sκ & %Hse'skind & Hoa & Htypevar)".
          destruct sκ as [ιs ξ | n ξ]; [iDestruct "Hoa" as "[%Harep %Hflag]"
                                       |iDestruct "Hoa" as "[[] _]"].
          (* This is now using the correct Hsub_t *)
          pose proof (rel_type_implies_rel_sκ se' se sub_t Hsub_T) as Hsub_t.
          apply Hsub_t in Hse'skind as Htypeskind.
          (* destruct Htypeskind as (sκ' & Htypeskind & Hsubsk). *)
          (* inversion Hsubsk; subst. *)


          (* TODO: *)
          (*
          iExists (SVALTYPE ιs ξ).
          iFrame "∗".
          iSplitR; auto.
          unfold type_var_interp.
          (* note to self: T : skind x semantic_type *)
          (* semantic_type : semantic_value -> iProp  *)
          (* semantic value: SAtoms/SWords *)
          destruct (lookup_type se' idx) eqn:Hse'typenv; auto.

          destruct p as [sκ' T].

          (* okay we def need something about se' !! idx = Some . T *)
          (* Hsub_t probably needs to just talk about both *)

          (* also it's true but maybe not relevant: *)
          assert (temp: sκ' = SVALTYPE ιs ξ). {
            cbn in Hse'skind. by inversion Hse'skind.
          }
          subst sκ'.

          iSplitR.
          -- cbn.
             iSplitL; iPureIntro; done.
          -- (* This hypothesis works and is provable :) *)

             (* assert (temp: snd <$> lookup_type se' idx = Some T) by (rewrite Hse'typenv; by cbn). *)
             specialize (Hsub_T idx (SVALTYPE ιs ξ) T Hse'typenv).
             destruct Hsub_T as [_ Hsub_T].
             specialize (Hsub_T (SAtoms o)).

             iAssert (⌜svalue_in_skind (SAtoms o) (SVALTYPE ιs ξ)⌝%I) as "#Hs".
             { iPureIntro; by cbn. }
             iPoseProof (Hsub_T with "[$Htypevar] [$Hs]") as "Ho".
             iPoseProof (value_interp_eq with "Ho") as "Ho".
             cbn.
             iDestruct "Ho" as "(%sκ & %a & %b & c)".
             done.
           *)
          admit.
        * (* i31, qed, TODO *)
          intros; cbn.
          (*
          iPoseProof (value_interp_eq with "Hoa") as "Hoa".
          iApply value_interp_eq.
          cbn.
          iDestruct "Hoa" as "(%sk & %HEval & Hoa & _)".
          destruct sk as [ιs ξ | n ξ]; [|iDestruct "Hoa" as "[[] _]"].

          iExists (SVALTYPE ιs ξ).
          iSplitR; [iPureIntro; by eapply eval_kind_subst_senv; done|iFrame].
          *)
          admit.
        * (* numt, qed, TODO *)
          intros. cbn.
          (*
          iPoseProof (value_interp_eq with "Hoa") as "Hoa".
          iApply value_interp_eq.
          cbn.
          iDestruct "Hoa" as "(%sk & %HEval & Hoa & _)".
          destruct sk as [ιs ξ | n ξ]; [|iDestruct "Hoa" as "[[] _]"].
          iExists (SVALTYPE ιs ξ); cbn; iFrame.
          iPureIntro.
          eapply eval_kind_subst_senv; done.
          *)
          admit.
        * (* sum, nearly qed except for map/forall2 lemma, TODO *)
          intros; cbn.
          (*
          iPoseProof (value_interp_eq with "Hoa") as "Hoa".
          iApply value_interp_eq.
          cbn.
          iDestruct "Hoa" as "(%sk & %HEval & Hoa & Hk)".
          destruct sk as [ιs ξ | n ξ]; [|iDestruct "Hoa" as "[[] _]"].
          iExists (SVALTYPE ιs ξ); cbn; iFrame.
          iSplitR; [iPureIntro; eapply eval_kind_subst_senv; done|].
          destruct κ; [|done].
          destruct r; try done.
          rename l into ρs; rename r0 into ξ'.
          cbn.
          iDestruct "Hk" as "(%i & %os & %off & %count & %τi &
                              %H1 & %H2 & %H3 & %H4 & Hoa)".
          (* I've convinced myself these are right *)
          iExists i, os, off, count.

          (* I'm just going to make τi what I need it to be *)
          iExists (subst_type sub_m sub_r sub_s sub_t τi).

          iSplitR; auto.

          (* now these are a bit interesting *)
          iSplitR; [iPureIntro | iSplitR; [iPureIntro | iSplitR;
                [iPureIntro|iModIntro]]]; last first.
          -- (* okay yay, this is exactly what H is for *)
             (* plan: using that τi is in τs (H4), get H's assertion for
                τi. Then, specialize with take count (drop off os) *)
             (* using Forall_lookup_1 *)
             pose proof (Forall_lookup_1 _ _ i τi H H4).
             cbn in H0.
             by specialize (H0 sub_t sub_r sub_s sub_m se se' Hsub_r Hsub_s Hsub_T
                           (take count (drop off os))).
          -- by apply map_lookup_helper.
          -- apply fmap_Some.
             apply fmap_Some in H3 as (ιs_ρ & Hy & Hah).
             exists ιs_ρ.
             split; [|done].
             apply bind_Some.
             apply bind_Some in Hy as (ρ & Hz & Hbh).
             cbn in Hbh.
             (* I hope this is right?? *)
             exists (subst_representation sub_r ρ).
             split.
             ++ by apply map_lookup_helper.
             ++ eapply eval_rep_subst_senv; done.
          -- unfold sum_offset in *.
             apply bind_Some in H2 as (ιss & Hy & Hah).
             apply bind_Some.
             (* hopefully *)
             exists ιss. split; [|done].
             (* Okay this is true by a combo of mapM lemmas and
                eval_rep_subst_senv:
                Hsub_r -> eval_rep se' ρ = Some ιs ->
                eval_rep se (subst_representation sub_r ρ) = Some ιs
              *)

             apply mapM_Some.
             apply mapM_Some in Hy.
             (* seems a bit annoying to prove but definitely true:
                - take i ρs and take i (map (..) ρs) operate on the same things
                - On those things, use eval_rep_subst_senv, and you're good
              *)
             admit.
          *)
          admit.
        * (* variant *)
          admit.
        * (* prod *)
          admit.
        * (* struct *)
          admit.
        * (** refT, worried due to SAtoms rather than SWords, aka bad induction *)
          intros; cbn.
          (* TODO: *)
          (*
          iPoseProof (value_interp_eq with "Hoa") as "Hoa".
          iApply value_interp_eq.
          cbn.
          iDestruct "Hoa" as "(%sκ & %Hsκ & Hsκ & Hm)".
          destruct sκ as [ιs ξ | n ξ]; [|iDestruct "Hsκ" as "[[]_]"].
          iExists (SVALTYPE ιs ξ).
          iFrame.
          iSplitR; [iPureIntro; by eapply eval_kind_subst_senv|].

          destruct m; [done|].
          cbn.
          destruct b.
          -- cbn.
             (* HWY IS IH\TAU SATOMS AAAAAAAAAA *)
             iDestruct "Hm" as "(%ℓ & %fs & %ws & h1 & h2 & h3 & Hoa)".
             iFrame.
             iModIntro.
             (* this is where you use the IHτ if it was correct *)

             admit.
          -- cbn.
             admit.
          *)
          admit.
        * (* coderef, qed, TODO *)
          (* I think this IH for function types is what we need but we'll see *)
          intros.
          (*
          iPoseProof (value_interp_eq with "Hoa") as "Hoa".
          iApply value_interp_eq.
          cbn.
          iDestruct "Hoa" as "(%sκ & %Hsκ & Hsκ & (%i & %i32 & %j & %cl & Hcl))".
          destruct sκ as [ιs ξ | n ξ]; [|iDestruct "Hsκ" as "[[]_]"].
          iExists (SVALTYPE ιs ξ).
          iFrame.
          iSplitR; [iPureIntro; by eapply eval_kind_subst_senv|].
          iExists i, i32, j, cl.
          iDestruct "Hcl" as "(H1 & H2 & H3 & H4 & H5)".
          iFrame.
          specialize (IHτ se se' cl sub_m sub_r sub_s sub_t Hsub_r Hsub_s Hsub_T).
          iPoseProof IHτ as "IHτ".
          iApply IHτ; auto.
          *)
          admit.
        * (* sert *)
          admit.
        * (* plug *)
          admit.
        * (* span *)
          admit.
        * (* rec *)
          admit.
        * (* exists mem, need to fix with new T hypothesis *)
          intros.
          (* TODO *)
          (*
          iPoseProof (value_interp_eq with "Hoa") as "Hoa".
          iApply value_interp_eq.
          iDestruct "Hoa" as "(%sκ & %Hsκ & Hsκ & (%μ & Hμ))".
          destruct sκ as [ιs ξ | n ξ]; [|iDestruct "Hsκ" as "[[]_]"].
          iExists (SVALTYPE ιs ξ).
          iFrame. (* this does delete some pure things *)
          iSplitR; [iPureIntro; eapply eval_kind_subst_senv; done|].

          (* this might be wrong *)
          cbn.
          iExists μ.
          iModIntro.
          iRename "Hμ" into "Hoa".

          specialize (IHτ (up_memory_type sub_t) (up_memory_representation sub_r)
                     (up_memory_size sub_s) (up_memory_memory sub_m))
            as IHτ.
          specialize (IHτ (senv_insert_mem μ se) (senv_insert_mem μ se'))
            as IHτ.
          apply IHτ.
          -- intros.
             assert (H': lookup_rep se' i = Some ιs'). {
               unfold senv_insert_mem in H.
               destruct se'.
               destruct o0. destruct o0.
               cbn in H.
               cbn. done.
             }
             apply Hsub_r in H'.
             by apply eval_rep_up_memory.
          -- intros.
             assert (H': lookup_size se' i = Some n). {
               cbn in H. destruct se'; destruct o0; destruct o0.
               cbn in H; cbn.
               done.
             }
             apply Hsub_s in H'.
             by apply eval_size_up_memory.
          -- intros.
             assert (H': lookup_type se' i = Some (sκ', T')). {
               destruct se'; destruct o0; destruct o0.
               unfold senv_insert_mem in H. cbn in H.
               unfold lookup_type in *; cbn in H; by cbn.
             }
             apply Hsub_T in H' as (Hsκ0' & HT').
             split; [by apply type_skind_up_memory|].
             (* oh no...
                need a lemma like
                value_interp rti sr se (sub_t i) sv -∗
                value_interp rti sr (senv_insert_mem μ se) (up_memory_type sub_t i) sv
                and all the other combinations for all the other exists
                jeez
              *)
             admit.
             *)
          admit.
        * (* exists rep *)
          admit.
        * (* exists size *)
          admit.
        * (* exists type *)

          admit.
        * (** MonoFun, WORRIED due to potential bi-implication *)
          (* base case for P0 *)
          iIntros (??????? Hsub_r Hsub_s Hsub_T) "#Hcl".
          cbn.
          (* I'm so scared *)
          destruct cl; [|auto].
          destruct f as [τs1_trans τs2_trans] eqn:Hf.
          iDestruct "Hcl" as "(%Hτs1 & %Hτs2 & Hcl)".
          iSplitR; [iPureIntro| iSplitR; [iPureIntro|]]; fold (subst_type sub_m sub_r sub_s sub_t).
          -- pose proof (rel_type_implies_rel_sκ se' se sub_t Hsub_T) as Hsub_t.
             by eapply translate_types_subst_senv.
          -- pose proof (rel_type_implies_rel_sκ se' se sub_t Hsub_T) as Hsub_t.
             by eapply translate_types_subst_senv.
          -- iIntros "!> !> %%% Hvs Hos Hrt Hown Hfr Hrun".
             iApply (cwp_label_wand with "[-]").
             ++ iApply (cwp_return_wand with "[-]").
                ** iApply (cwp_wand with "[-]").
                   --- iApply ("Hcl" with "[$] [Hos] [$] [$] [$] [$]").
                       iClear "Hcl".
                       (* IT'S THE OTHER WAY AROUND WHYYYYY :SOB: *)
                       admit. (* values_interp0 *)
                   --- iClear "Hcl".
                       iIntros (f' vs) "((%os & Hvs & Hos) & [% Hrt] & Hown)".
                       iSplitL "Hvs Hos"; last iFrame.
                       iExists _.
                       iFrame.
                       (* this is the correct direction to use H *)
                       admit. (* values_interp0 *)
                ** iClear "Hcl".
                   iSplitL; first done.
                   iIntros (? Hlen) "((% & Hvs & Hos) & [% Hrt] & Hown)".
                   cbn in Hlen.
                   iSplitL "Hvs Hos"; last iFrame.
                   iExists _.
                   iFrame.
                   (* correct direction to use H0 *)
                   admit. (* values_interp0 *)
             ++ iClear "Hcl".
                iSplitL; first done.
                iApply big_sepL2_singleton.
                iSplitL; first done.
                iIntros (f' vs Hlen) "((% & Hvs & Hos) & [% Hrt] & Hown)".
                cbn in Hlen.
                iSplitL "Hvs Hos"; last iFrame.
                iExists _.
                iFrame.
                (* correct direction to use H0 *)
                admit.
        * (* ForallMemT case *)
          intros ??????? Hsub_r Hsub_s Hsub_T.
          iIntros "Hcl".
          cbn.
          iIntros.
          (* TODO: *)
          (*
          iSpecialize ("Hcl" $! μ).
          iApply IHτ; last done.
          ++ intros ?? H'. asimpl'. apply eval_rep_mem_irrel. by apply Hsub_r.
          ++ intros ?? H'. asimpl'.
             apply eval_size_mem_irrel. by apply Hsub_s.
          ++ intros ??? H'. asimpl'.
             apply Hsub_T in H'.
             destruct H' as [H1' H2'].
             unfold core.funcomp.
             split; [by apply type_skind_mem_irrel|].
             (* this is going to be a value interp mem shifting thing *)
             admit.
          *)
          admit.
        * (* ForallRepT *)
          admit.
        * (* ForallSizeT *)
          intros ??????? Hsub_r Hsub_s Hsub_T.
          admit.
        * (* ForallTypeT *)
          intros ??????? Hsub_r Hsub_s Hsub_T.
          iIntros "Hcl"; cbn.
          iDestruct "Hcl" as "(%sκ & %Hκ & Hcl)".
          iExists sκ.
          iSplitR; [iPureIntro; by eapply eval_kind_subst_senv|].
          iIntros (?? Hsubs Hskind).
          iSpecialize ("Hcl" $! sκ_T T Hsubs Hskind).

          (* TODO: *)
          (*
          iApply IHτ; last done.
          ++ intros ?? H'; asimpl'. unfold core.funcomp.
             cbn in H'.
             apply eval_rep_type_irrel.
             by apply Hsub_r.
          ++ intros ?? H'; asimpl'; unfold core.funcomp.
             apply eval_size_type_irrel.
             by apply Hsub_s.
          ++ intros ??? H'.
             cbn in H'.
             destruct i.
             -- cbn in *; inversion H'; subst.
                split; [done|].
                unfold unscoped.var_zero.
                (* this is true *)
                admit.
             -- cbn in H'.
                apply Hsub_T in H' as [H1' H2'].
                split; [by apply type_skind_up_type|].
                (* this is a value interp type shifting thing *)
                admit.
           *)
  Admitted.


  (* TODO: The lemma for values_interp0 might require adding an assumption about
     the memory substitution? *)
  Lemma closure_interp_subst_senv se se' ϕ cl sub_m sub_r sub_s sub_t :
    (sem_env_rel_rep se' se sub_r) ->
    (sem_env_rel_size se' se sub_s) ->
    (sem_env_rel_type se' se sub_t) ->
    closure_interp rti sr ϕ se' cl -∗
    let ϕ' := subst_function_type sub_m sub_r sub_s sub_t ϕ in
    closure_interp rti sr ϕ' se cl.
  Proof.
    generalize dependent sub_t.
    generalize dependent sub_s.
    generalize dependent sub_r.
    generalize dependent sub_m.
    generalize dependent se.
    generalize dependent se'.

    (** NOTE: THESE ARE THE SAME CASES AS THE LAST 5 CASES IN VALUE_INTERP0_SUBST_SENV ABOVE
        So technically more of these are done than it seems
     *)
    induction ϕ as [τs1 τs2| | | |κ] .
    - iIntros (?????? Hsub_r Hsub_s Hsub_T) "#Hcl".
      pose proof (rel_type_implies_rel_sκ se' se sub_t Hsub_T) as Hsub_t.
      unfold_sem_rels.
      destruct cl; [|auto].
      destruct f as [τs1_trans τs2_trans] eqn:Hf.
      iDestruct "Hcl" as "(%Hτs1 & %Hτs2 & Hcl)".
      iSplitR; [iPureIntro| iSplitR; [iPureIntro|]]; fold (subst_type sub_m sub_r sub_s sub_t).
      + by eapply translate_types_subst_senv.
      + by eapply translate_types_subst_senv.
      + iIntros "!> !> %%% Hvs Hos Hrt Hown Hfr Hrun".
        iApply (cwp_label_wand with "[-]").
        * iApply (cwp_return_wand with "[-]").
          -- iApply (cwp_wand with "[-]").
             ++ iApply ("Hcl" with "[$] [Hos] [$] [$] [$] [$]").
                iClear "Hcl".
                admit. (* values_interp0 *)
             ++ iClear "Hcl".
                iIntros (f' vs) "((%os & Hvs & Hos) & [% Hrt] & Hown)".
                iSplitL "Hvs Hos"; last iFrame.
                iExists _.
                iFrame.
                admit. (* values_interp0 *)
          -- iClear "Hcl".
             iSplitL; first done.
             iIntros (? Hlen) "((% & Hvs & Hos) & [% Hrt] & Hown)".
             cbn in Hlen.
             iSplitL "Hvs Hos"; last iFrame.
             iExists _.
             iFrame.
             admit. (* values_interp0 *)
        * iClear "Hcl".
          iSplitL; first done.
          iApply big_sepL2_singleton.
          iSplitL; first done.
          iIntros (f' vs Hlen) "((% & Hvs & Hos) & [% Hrt] & Hown)".
          cbn in Hlen.
          iSplitL "Hvs Hos"; last iFrame.
          iExists _.
          iFrame.
          admit. (* values_interp0 *)
    - iIntros (?????? Hsub_r Hsub_s Hsub_T) "#Hcl %".
      pose proof (rel_type_implies_rel_sκ se' se sub_t Hsub_T) as Hsub_t.
      unfold_sem_rels.
      (* TODO: *)
      (*
      iApply IHϕ; last done.
      + intros ?? H. asimpl'. apply eval_rep_mem_irrel. by apply Hsub_r.
      + intros ?? H. asimpl'. apply eval_size_mem_irrel. by apply Hsub_s.
      + intros ??? H. asimpl'.
        apply Hsub_T in H as (H & H1).
        (* destruct H as (sκ0' & H & Hsubsk). *)
        unfold core.funcomp.
        split; [by apply type_skind_mem_irrel|].
        (* same uh oh as above *)
        admit.
      *)
      admit.
    - iIntros (?????? Hsub_r Hsub_s Hsub_T) "#Hcl %".
      pose proof (rel_type_implies_rel_sκ se' se sub_t Hsub_T) as Hsub_t.
      unfold_sem_rels.
      (* TODO: *)
      (*
      iApply IHϕ; last done.
      + intros ?? H.
        destruct i.
        * cbn. by rewrite <- H.
        * apply eval_rep_up_rep. by apply Hsub_r.
      + intros ?? H. apply eval_size_up_rep. by apply Hsub_s.
      + intros ??? H.
        (* apply Hsub_t in H as (sκ0' & H & Hsubsk). *)
        apply Hsub_T in H as (H & H1).
        (* exists sκ0'. *)
        (* split; [by apply type_skind_up_rep|done]. *)
        split; [by apply type_skind_up_rep|].
        admit.
      *)
      admit.
    - iIntros (?????? Hsub_r Hsub_s Hsub_T) "#Hcl %".
      (* TODO: *)
      (*
      iApply IHϕ; last done.
      + intros ?? H. apply eval_rep_up_size. admit.
      + admit.
      + admit.
      *)
      admit.
    - admit.
  Admitted.

  Lemma closure_interp_scons_insert_mem F se μ ϕ cl :
    mem_ok F.(fc_kind_ctx) μ ->
    sem_env_interp F se ->
    (∀ μ', closure_interp rti sr ϕ (senv_insert_mem μ' se) cl) -∗
    let ϕ' := subst_function_type (unscoped.scons μ VarM) VarR VarS VarT ϕ in
    closure_interp rti sr ϕ' se cl.
  Proof using mr. (* NOTE: don't know why rocq wants using mr *)
    iIntros (Hok Hse) "Hcl".
    iApply closure_interp_subst_senv; unfold_sem_rels; last done; try done.
    Unshelve.
    2: exact MemMM.

    intros i sκ' T' H.
    split.
    + destruct se.
      unfold senv_insert_mem in *; unfold lookup_type in *; cbn in *.
      apply fmap_Some; eexists; split; done.
    + iIntros (sv) "HT' %Hsvalue".
      pose proof (value_interp_var rti sr se i sκ' T' H) as Hval.
      iApply Hval.
      cbn. iFrame.
      by iPureIntro.
  Qed.

  Lemma closure_interp_scons_insert_rep F se ρ ϕ cl :
    rep_ok (fc_kind_ctx F) ρ ->
    sem_env_interp F se ->
    (∀ ιs, closure_interp rti sr ϕ (senv_insert_rep ιs se) cl) -∗
    let ϕ' := subst_function_type VarM (unscoped.scons ρ VarR) VarS VarT ϕ in
    closure_interp rti sr ϕ' se cl.
  Proof using mr.
    iIntros (Hok Hse) "Hcl".
    destruct (eval_rep_ok_Some _ _ _ Hse Hok) as [ιs Hιs].
    iSpecialize ("Hcl" $! ιs).
    iApply closure_interp_subst_senv; unfold_sem_rels; last done.
    - intros ?? H.
      destruct i.
      + by rewrite <- H.
      + done.
    - done.
    - intros ??? H.
      cbn in *.
      split.
      + destruct se.
        unfold senv_insert_rep in *; unfold lookup_type in *; cbn in *.
        apply fmap_Some; eexists; split; done.
      + iIntros (sv) "HT' %Hsvalue".
        pose proof (value_interp_var rti sr se i sκ' T' H) as Hval.
        iApply Hval.
        cbn. iFrame.
        by iPureIntro.
  Qed.

  Lemma closure_interp_scons_insert_size F se σ ϕ cl :
    size_ok (fc_kind_ctx F) σ ->
    sem_env_interp F se ->
    (∀ n, closure_interp rti sr ϕ (senv_insert_size n se) cl) -∗
    let ϕ' := subst_function_type VarM VarR (unscoped.scons σ VarS) VarT ϕ in
    closure_interp rti sr ϕ' se cl.
  Proof using mr.
    iIntros (Hok Hse) "Hcl".
    destruct (eval_size_ok_Some _ _ _ Hse Hok) as [n Hn].
    iSpecialize ("Hcl" $! n).
    iApply closure_interp_subst_senv; unfold_sem_rels; last done.
    - done.
    - intros ?? H.
      destruct i.
      + by rewrite <- H.
      + done.
    - intros ??? H.
      cbn in *.
      split.
      + destruct se.
        unfold senv_insert_size in *; unfold lookup_type in *; cbn in *.
        apply fmap_Some; eexists; split; done.
      + iIntros (sv) "HT' %Hsvalue".
        pose proof (value_interp_var rti sr se i sκ' T' H) as Hval.
        iApply Hval.
        cbn. iFrame.
        by iPureIntro.
  Qed.

  Lemma closure_interp_scons_insert_type F se τ κ sκ ϕ cl :
    has_kind F τ κ ->
    sem_env_interp F se ->
    eval_kind se κ = Some sκ ->
    (∀ sκ_T T,
       ⌜subskind_of sκ_T sκ⌝ -∗
       ⌜skind_has_stype sκ_T T⌝ -∗
       closure_interp rti sr ϕ (senv_insert_type sκ_T T se) cl) -∗
    let ϕ' := subst_function_type VarM VarR VarS (unscoped.scons τ VarT) ϕ in
    closure_interp rti sr ϕ' se cl.
  Proof using mr.
    iIntros (Hok Hse Hsκ) "Hcl".
    pose proof (type_skind_has_kind_Some _ _ _ _ _ Hok Hse Hsκ) as (sκ_T & Hskind & Hsub).
    set T := value_interp rti sr se τ.
    iSpecialize ("Hcl" $! sκ_T T).
    iApply closure_interp_subst_senv; unfold_sem_rels; last iApply "Hcl".
    - done.
    - done.
    - (* this an attempt to figure out the T hypothesis *)
      intros ??? H.
      split.
      {
        destruct i; cbn in *; first (inversion H; by subst).
        apply fmap_Some. eexists; cbn; split; done.
      }
      {
      iIntros (sv) "HT' %Hsvalue".
      destruct i; cbn in *.
      + inversion H; subst; unfold T. done.
      + pose proof (value_interp_var rti sr se i sκ' T' H) as Hval.
        iApply Hval.
        cbn. iFrame.
        by iPureIntro.
      }
    - done.
    - iPureIntro.
      subst T.
      iIntros (sv) "H".
      iDestruct (value_interp_skind with "H") as "(%sκ' & %Hsκ' & %Hskind')".
      rewrite Hskind in Hsκ'.
      by inversion Hsκ'; subst.
  Qed.

  Lemma compat_inst M F L wt wt' wtf wl wl' wlf es' ix ϕ ϕ' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let κ := VALTYPE (AtomR I32R) NoRefs in
    let ψ := InstrT [CodeRefT κ ϕ] [CodeRefT κ ϕ'] in
    function_type_inst F ix ϕ ϕ' ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IInst ψ ix)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmask κ ψ Hfinst Hok Hcg.
    cbn in Hcg; inversion Hcg; subst wt' wl' es'; clear Hcg.

    iIntros (??????????) "@@@@@@@@@@".
    clear_nils.

    iApply (cwp_val with "[$Hfr] [$Hrun]"); [apply H0|].
    iSplitR; auto.
    iFrame.
    iPoseProof (values_interp_one_eq with "Hos") as "Hos".
    iPoseProof (value_interp_coderef with "Hos") as "%Hos".
    destruct Hos as (n32 & ->).
    iApply values_interp_one_eq.

    (* now we need to use the key hypothesis: Hfinst *)
    destruct Hfinst.

    (* dig into all at once down to closure interp *)
    all: unfold ϕ'; cbn.

    all: iDestruct "Hos" as "(%κ' & %toinvert & HKindInterp & Rest)".
    all: inversion toinvert; subst; clear toinvert.

    all: iExists (SVALTYPE [I32R] NoRefs).
    all: iFrame.
    all: iSplitR; auto.

    all: iDestruct "Rest" as
      "(%n & %n32subst & %j & %cl & %HRepr & %toinvert &
          Hclosure & Hwt & Hwf)".
    all: inversion toinvert; subst n32subst; clear toinvert.

    all: iExists n, n32.
    all: iExists j, cl.
    all: iFrame.
    all: iSplitR; auto; iSplitR; auto.

    - by iApply closure_interp_scons_insert_mem; last inversion Hok.
    - by iApply closure_interp_scons_insert_rep; last inversion Hok.
    - by iApply closure_interp_scons_insert_size; last inversion Hok.
    - iDestruct "Hclosure" as "(% & % & ?)".
      by iApply closure_interp_scons_insert_type; last inversion Hok.
  Qed.

End inst.
