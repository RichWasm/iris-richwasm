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

  (* wow that was much easier than I thought it'd be *)
  Lemma eval_rep_mem_irrel_eq se ρ μ :
    eval_rep se ρ =
    eval_rep (senv_insert_mem (Σ:=Σ) μ se) ρ.
  Proof.
    induction ρ using rep_ind; auto.
    - cbn in *.
      assert (H': mapM (eval_rep se) ρs = mapM (eval_rep (senv_insert_mem μ se)) ρs)
        by by apply Forall_mapM_ext.
      by rewrite H'.
    - cbn in *.
      assert (H': mapM (eval_rep se) ρs = mapM (eval_rep (senv_insert_mem μ se)) ρs)
        by by apply Forall_mapM_ext.
      by rewrite H'.
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

  Lemma eval_rep_size_irrel_eq se ρ n :
    eval_rep se ρ =
    eval_rep (senv_insert_size (Σ:=Σ) n se) ρ.
  Proof.
    induction ρ using rep_ind; auto.
    - cbn in *.
      assert (H': mapM (eval_rep se) ρs = mapM (eval_rep (senv_insert_size n se)) ρs)
        by by apply Forall_mapM_ext.
      by rewrite H'.
    - cbn in *.
      assert (H': mapM (eval_rep se) ρs = mapM (eval_rep (senv_insert_size n se)) ρs)
        by by apply Forall_mapM_ext.
      by rewrite H'.
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

  Lemma eval_rep_type_irrel_eq se ρ sκ T :
    eval_rep se ρ =
    eval_rep (senv_insert_type (Σ:=Σ) sκ T se) ρ.
  Proof.
    induction ρ using rep_ind; auto.
    - cbn in *.
      assert (H': mapM (eval_rep se) ρs = mapM (eval_rep (senv_insert_type sκ T se)) ρs)
        by by apply Forall_mapM_ext.
      by rewrite H'.
    - cbn in *.
      assert (H': mapM (eval_rep se) ρs = mapM (eval_rep (senv_insert_type sκ T se)) ρs)
        by by apply Forall_mapM_ext.
      by rewrite H'.
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

  Lemma eval_size_mem_irrel_eq se σ μ :
    eval_size se σ =
    eval_size (senv_insert_mem (Σ:=Σ) μ se) σ.
  Proof.
    induction σ using size_ind; intros; auto.
    - cbn in *.
      assert (H': mapM (eval_size se) σs = mapM (eval_size (senv_insert_mem μ se)) σs)
        by by apply Forall_mapM_ext.
      by rewrite H'.
    - cbn in *.
      assert (H': mapM (eval_size se) σs = mapM (eval_size (senv_insert_mem μ se)) σs)
        by by apply Forall_mapM_ext.
      by rewrite H'.
    - cbn -[senv_insert_mem].
      by rewrite <- eval_rep_mem_irrel_eq.
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

  Lemma eval_size_type_irrel_eq se σ sκ T :
    eval_size se σ =
    eval_size (senv_insert_type (Σ:=Σ) sκ T se) σ.
  Proof.
    induction σ using size_ind; intros; auto.
    - cbn in *.
      assert (H': mapM (eval_size se) σs = mapM (eval_size (senv_insert_type sκ T se)) σs)
        by by apply Forall_mapM_ext.
      by rewrite H'.
    - cbn in *.
      assert (H': mapM (eval_size se) σs = mapM (eval_size (senv_insert_type sκ T se)) σs)
        by by apply Forall_mapM_ext.
      by rewrite H'.
    - cbn -[senv_insert_type].
      by rewrite <- eval_rep_type_irrel_eq.
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

  Lemma eval_kind_mem_irrel_eq se κ μ :
    eval_kind se κ =
    eval_kind (senv_insert_mem (Σ:=Σ) μ se) κ .
  Proof.
    destruct κ; intros; cbn -[senv_insert_mem senv_insert_type] in *.
    - by rewrite <- eval_rep_mem_irrel_eq.
    - by rewrite <- eval_size_mem_irrel_eq.
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

  Lemma eval_kind_type_irrel_eq se κ sκ T :
    eval_kind se κ =
    eval_kind (senv_insert_type (Σ:=Σ) sκ T se) κ .
  Proof.
    destruct κ; intros; cbn -[senv_insert_type] in *.
    - by rewrite <- eval_rep_type_irrel_eq.
    - by rewrite <- eval_size_type_irrel_eq.
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

  Lemma type_skind_mem_irrel_eq se μ τ :
    type_skind (Σ:=Σ) se τ =
    type_skind (Σ:=Σ) (senv_insert_mem μ se)
      (ren_type unscoped.shift unscoped.id unscoped.id unscoped.id τ).
  Proof.
    destruct τ.
    1: done.
    all: intros; cbn in *.
    all: rewrite rinstId'_kind.
    all: by apply eval_kind_mem_irrel_eq.
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

  Lemma type_interp_eq_r τ se sv :
    type_interp rti sr τ se sv -∗ (add_skind_interp τ $ pre_type_interp rti sr τ) se sv.
  Proof.
    iDestruct (type_interp_eq rti sr τ se sv) as "[help _]".
    done.
  Qed.

  Lemma type_interp_eq_l τ se sv :
    (add_skind_interp τ $ pre_type_interp rti sr τ) se sv -∗
    type_interp rti sr τ se sv.
  Proof.
    iDestruct (type_interp_eq rti sr τ se sv) as "[_ help]".
    done.
  Qed.

  (* seems fine, but omg we'll have to do All of them.... all four....
     probably a decent amount of overlap but this is just so annoying
   *)
  Lemma type_interp_up_memory se sub_t μ sv i :
    type_interp rti sr (sub_t i) se sv ∗-∗
    type_interp rti sr (up_memory_type sub_t i) (senv_insert_mem μ se) sv.
  Proof.
    asimpl'.
    unfold core.funcomp.
    generalize dependent se.
    generalize dependent sv.
    induction (sub_t i) using type_ind with
      (P0 := λ ft, ∀ cl se, closure_interp rti sr ft se cl ∗-∗
        closure_interp rti sr (ren_function_type unscoped.shift unscoped.id unscoped.id unscoped.id ft)
                               (senv_insert_mem μ se) cl).
    1: { (* vart *)
      intros; iSplitL; iIntros; cbn; done.
    }
    1: (* numbers *) {
        intros; iSplitL; iIntros "H".
      all: iDestruct "H" as "(%sκ & %h1 & %h2 & h4)".
      all: iExists sκ; iFrame.
      all: iPureIntro.
      all: split; cbn -[senv_insert_mem]; try done.
      - rewrite rinstId'_kind; by rewrite <- eval_kind_mem_irrel_eq.
      - rewrite rinstId'_kind in h1.
        by erewrite eval_kind_mem_irrel_eq.
    }
    1: admit. (* should be the same as numbers *)
    1: { (* sum *)
      (* iIntros (?) "H"; cbn. *)
      (* iDestruct "H" as "(%sκ & %h1 & h2 & h4)". *)
      (* iExists sκ; iFrame. *)
      (* iSplitR; rewrite rinstId'_kind; [iPureIntro; by apply eval_kind_mem_irrel|]. *)
      (* cbn in H. *)
      (* okay yes it's forall stuffs *)
      admit.
    }

    4: { (* reft *)
      intros. iSplitL; iIntros "H";
        iPoseProof (type_interp_eq_r with "[$H]") as "H";
        iApply type_interp_eq_l;
        iDestruct "H" as "(%sκ & %h1 & h2 & h4)";
        iExists sκ; iFrame;
        [ iSplitR; [iPureIntro; by rewrite <- type_skind_mem_irrel_eq|]
        | iSplitR; [iPureIntro; by rewrite <- type_skind_mem_irrel_eq in h1|]].
      {
        (* now to figure out how to use the IH *)
        cbn.
        assert (eval_mem_up_shift_mem: eval_mem se m =
                                         eval_mem (senv_insert_mem μ se) (ren_memory unscoped.shift m)
               ). {
          admit.
        }
        rewrite eval_mem_up_shift_mem.
        destruct (eval_mem (senv_insert_mem μ se) (ren_memory unscoped.shift m)) eqn:h.
        2: rewrite h; cbn; done.
        rewrite h; cbn.
        destruct b.
        - (* memmm *)
          cbn.
          iDestruct "h4" as "(%ℓ & %fs & %ws & #h1 & h2 & h3 & h4)".
          iExists ℓ, fs, ws.
          iFrame "∗".
          iSplitR; auto.
          iModIntro.
          by iApply IHo.
        - (* memgc *)
          cbn.
          iDestruct "h4" as "(%ℓ & %fs & h1 & hinv)".
          iExists ℓ, fs. iFrame.
          iApply (na_inv_iff with "[$] [-]").
          repeat iModIntro.
          iSplitR; iIntros "H".
          all: iDestruct "H" as "(%ws & h1 & h2 & h3)".
          all: iExists ws; iFrame.
          all: iModIntro.
          all: by iApply IHo.
      }
      {
        cbn.
        assert (eval_mem_up_shift_mem: eval_mem se m =
                                         eval_mem (senv_insert_mem μ se) (ren_memory unscoped.shift m)
               ). {
          admit.
        }
        rewrite eval_mem_up_shift_mem.
        destruct (eval_mem (senv_insert_mem μ se) (ren_memory unscoped.shift m)) eqn:h.
        2: rewrite h; cbn; done.
        rewrite h; cbn.
        destruct b.
        - (* memmm *)
          cbn.
          iDestruct "h4" as "(%ℓ & %fs & %ws & #h1 & h2 & h3 & h4)".
          iExists ℓ, fs, ws.
          iFrame "∗".
          iSplitR; auto.
          iModIntro.
          by iApply IHo.
        - (* memgc *)
          cbn.
          iDestruct "h4" as "(%ℓ & %fs & h1 & hinv)".
          iExists ℓ, fs. iFrame.
          iApply (na_inv_iff with "[$] [-]").
          repeat iModIntro.
          iSplitR; iIntros "H".
          all: iDestruct "H" as "(%ws & h1 & h2 & h3)".
          all: iExists ws; iFrame.
          all: iModIntro.
          all: by iApply IHo.
      }
    }

    4: { (* codereft, test of the inductive hypothesis *)
      intros; iSplitL; iIntros "H";
        iPoseProof (type_interp_eq_r with "[$H]") as "H";
        iApply type_interp_eq_l;
        iDestruct "H" as "(%sκ & %h1 & h2 & h4)";
        iExists sκ; iFrame;
        [ iSplitR; [iPureIntro; by rewrite <- type_skind_mem_irrel_eq|]
        | iSplitR; [iPureIntro; by rewrite <- type_skind_mem_irrel_eq in h1|]].
      all: cbn.
      all: iDestruct "h4" as "(%i0 & %i32 & %j & %cl & h1 & h2 & h3 & h4)".
      all: iExists i0, i32, j, cl.
      all: iFrame.
      all: by iApply IHo.
    }

    8: { (* exists mem *)
      intros; iSplitL; iIntros "H";
        iPoseProof (type_interp_eq_r with "[$H]") as "H";
        iApply type_interp_eq_l;
        iDestruct "H" as "(%sκ & %h1 & h2 & h4)";
        iExists sκ; iFrame;
        [ iSplitR; [iPureIntro; by rewrite <- type_skind_mem_irrel_eq|]
        | iSplitR; [iPureIntro; by rewrite <- type_skind_mem_irrel_eq in h1|]].
      all: cbn in *.
      {
        asimpl'.
        (* okay I think this is true but this looks really damn annoying to prove *)
        admit.
      }
      {
        admit.
      }
    }

    11: { (* monofun, base case of inductive hyp *)
      intros; iSplitL; iIntros "H".
      {
        assert (H': closure_interp rti sr (MonoFunT τs1 τs2) se cl -∗
               mono_closure_interp rti sr τs1 τs2
                  (map (type_interp rti sr) τs1) (map (type_interp rti sr) τs2) se cl). {
          iIntros "H"; iApply "H".
        }
        iPoseProof (H' with "[$H]") as "H".
        unfold mono_closure_interp.
        (* okay staring at it seems doable *)
        admit.
      }
      {
        admit.
      }


    }

  Admitted.

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

  Definition sem_env_rel_rep_eq (se' : @semantic_env Σ) (se : @semantic_env Σ) (sub_r:nat → representation) :=
    (forall i, lookup_rep se' i = eval_rep se (sub_r i)).
  Definition sem_env_rel_size_eq (se' : @semantic_env Σ) (se : @semantic_env Σ) (sub_s:nat → Core.size) :=
    (forall i, lookup_size se' i = eval_size se (sub_s i)).
  Definition sem_env_rel_type_eq_BAD (se' : @semantic_env Σ) (se : @semantic_env Σ) (sub_t:nat → type) :=
    (forall i sκ' T', lookup_type se' i = Some (sκ', T') ->
    type_skind se (sub_t i) = Some sκ' /\
      (∀ sv, (T' sv -∗ ⌜skind_has_svalue sκ' sv⌝ -∗ value_interp rti sr se (sub_t i) sv))).
  Definition sem_env_rel_sκ_eq (se' : @semantic_env Σ) (se : @semantic_env Σ) (sub_t:nat → type) :=
    (forall i, fst <$> lookup_type se' i =
    type_skind se (sub_t i)).


  Ltac unfold_sem_rels := unfold sem_env_rel_rep, sem_env_rel_size, sem_env_rel_type, sem_env_rel_sκ,
    sem_env_rel_rep_eq, sem_env_rel_size_eq, sem_env_rel_type_eq_BAD, sem_env_rel_sκ_eq in *.



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

  Lemma eval_rep_subst_senv_eq (se se' : semantic_env (Σ:=Σ)) sub_r ρ :
    sem_env_rel_rep_eq se' se sub_r ->
    eval_rep se' ρ =
    eval_rep se (subst_representation sub_r ρ).
  Proof.
    intros Hsub_r; unfold_sem_rels.
    induction ρ as [n|ρs IH|ρs IH|ιs'] using rep_ind.
    - cbn in *. by apply Hsub_r.
    - cbn.
      assert (H': mapM (eval_rep se') ρs = mapM (eval_rep se) (map (subst_representation sub_r) ρs)). {
        apply Forall2_mapM_ext.
        (* yes this is true by IH *)
        admit.
      }
      by rewrite H'.
    - cbn.
      assert (H': mapM (eval_rep se') ρs = mapM (eval_rep se) (map (subst_representation sub_r) ρs)). {
        apply Forall2_mapM_ext.
        admit.
      }
      by rewrite H'.
    - cbn in *; done.
  Admitted.

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
    apply ref_flag_atoms_refine.
  Qed.

  Lemma type_interp_subst_type_BIDIRECTIONAL se se' τ o sub_m sub_r sub_s sub_t :
    (sem_env_rel_rep se' se sub_r) ->
    (sem_env_rel_size se' se sub_s) ->
    (sem_env_rel_type se' se sub_t) ->
    type_interp rti sr τ se' o ∗-∗
    type_interp rti sr (subst_type sub_m sub_r sub_s sub_t τ) se o.
  Proof.
    iIntros (Hsub_r Hsub_s Hsub_T).
    (* pose proof (rel_type_implies_rel_sκ se' se sub_t Hsub_T) as Hsub_t. *)
    (* comment/uncomment if you want/don't want to see them *)
    unfold_sem_rels.
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
           closure_interp rti sr ft se' cl ∗-∗
              closure_interp rti sr (subst_function_type sub_m sub_r sub_s sub_t ft) se cl).
    * (** vart, qed *)
      intros. cbn.
      iSplitL.
      {
        iIntros "Hoa".
        rewrite !type_interp_eq.
        iDestruct "Hoa" as "(%sκ & %Hse'skind & Hoa & Htypevar)".
        cbn in Hse'skind.
        pose proof (rel_type_implies_rel_sκ se' se sub_t Hsub_T) as Hsub_t.
        apply Hsub_t in Hse'skind as Htypeskind.
        (* destruct Htypeskind as (sκ' & Htypeskind & Hsubsk). *)
        (* inversion Hsubsk; subst. *)
        destruct (se'.2 !! idx) eqn:Hse'typenv;
          [| rewrite Hse'typenv in Hse'skind; cbn in Hse'skind; by inversion Hse'skind].
        destruct o0 as [sκ' T].
        assert (temp: sκ' = sκ). {
          rewrite Hse'typenv in Hse'skind. cbn in Hse'skind. by inversion Hse'skind.
        }
        subst sκ'.

        iEval (cbn; rewrite Hse'typenv; cbn) in "Htypevar".

        apply Hsub_T in Hse'typenv as [_ Hsub_T_true].
        specialize (Hsub_T_true o).
        rewrite value_interp_eq in Hsub_T_true.
        iApply (Hsub_T_true with "[$] [$]").
      }
      {
        iIntros "Hoa".
        admit.
      }
      (*
    * (* i31, qed *)
      intros; cbn.
      iDestruct "Hoa" as "(%sk & %HEval & %Hoa & _)".
      iExists sk; iSplitR; [iPureIntro | iSplitR; [iPureIntro; done | done]].
      by eapply eval_kind_subst_senv.





        * (* numt, qed *)
          intros. cbn.
          iDestruct "Hoa" as "(%sk & %HEval & %Hoa & _)".
          iExists sk; iSplitR; [iPureIntro | iSplitR; [iPureIntro; done | done]].
          by eapply eval_kind_subst_senv.
        * (* sum, nearly qed except for map/forall2 lemmas *)
          intros.
          iPoseProof (type_interp_eq_r with "[$Hoa]") as "Hoa".
          iApply type_interp_eq_l.
          iDestruct "Hoa" as "(%sk & %HEval & %Hoa & Hsuminterp)".
          iExists sk; iSplitR;
            [iPureIntro; by eapply eval_kind_subst_senv |
            iSplitR; [iPureIntro; done|]].
          destruct κ as [ρ ξ|n ξ]; cbn in HEval;
            apply bind_Some in HEval as (ιs & Hea & toinvert);
            inversion toinvert; subst; cbn in Hoa; [|done]; clear toinvert.

          destruct ρ; iEval (cbn) in "Hsuminterp"; try done.
          rename l into ρs.

          (* need to destruct Hsuminterp a bit more *)
          iDestruct "Hsuminterp" as "(%i & %os & %off & %count &
                              %H1 & %H2 & %H3 & Hoa)".
          destruct (list_lookup i (map (type_interp rti sr) τs)) eqn:Hτi_interp; try done.
          rename o0 into τi_interp.

          (* idk how to work with these maps but lemme get some of this out *)
          assert (H': ∃ τi, τs !! i = Some τi /\ τi_interp = type_interp rti sr τi). {
            (* obvious by Hτi_interp *)

            admit.
          }
          destruct H' as (τi & Hτi_lookup & Hτi).
          subst τi_interp.

          iExists i, os, off, count.

          (* let's try to work with this now! *)
          iSplitR; [done |
            iSplitR; [iPureIntro |
            iSplitR; [iPureIntro |]]]; last first.
          -- pose proof (Forall_lookup_1 _ _ i τi H Hτi_lookup) as IH_τi.
             specialize (IH_τi sub_t sub_r sub_s sub_m se se' Hsub_r Hsub_s Hsub_T
                        (SAtoms (take count (drop off os)))).

             assert (H': list_lookup i (map (type_interp rti sr)
                              (map (subst_type sub_m sub_r sub_s sub_t) τs)) =
                           Some (type_interp rti sr (subst_type sub_m sub_r sub_s sub_t τi))).
                  {
                    (* this by τs !! i = Some τi *)

                    admit.
                  }
             by rewrite H'.
          -- apply fmap_Some.
             apply fmap_Some in H3 as (ιs_ρ & Hy & Hah).
             exists ιs_ρ.
             split; [|done].
             apply bind_Some.
             apply bind_Some in Hy as (ρ & Hz & Hbh).
             cbn in Hbh.
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
        * (* variant qed except for map lemmas *)
          intros.
          iPoseProof (type_interp_eq_r with "[$Hoa]") as "Hoa".
          iApply type_interp_eq_l.
          iDestruct "Hoa" as "(%sκ & %Hsκ & %Hso & Hvariant)".

          iExists sκ.
          iSplitR; [iPureIntro; by eapply eval_kind_subst_senv|].
          iSplitR; [done|].

          iDestruct "Hvariant" as "(%i & %n & %ws & %ws' & %Hnat & %tosubst & Hoa)".
          subst s.
          destruct (list_lookup i (map (type_interp rti sr) τs)) eqn:Hτi_interp;
            rewrite Hτi_interp; [|by cbn].
          rename o0 into τi_interp.
          assert (H': ∃ τi, τs !! i = Some τi /\ τi_interp = type_interp rti sr τi). {
            (* obvious by Hτi_interp *)
            admit.
          }
          destruct H' as (τi & Hτi_lookup & Hτi).
          subst τi_interp.

          iEval (cbn).
          iExists i, n, ws, ws'.
          iSplitR; [done | iSplitR; [done |]].
          assert (H': list_lookup i (map (type_interp rti sr)
                                       (map (subst_type sub_m sub_r sub_s sub_t) τs)) =
                        Some (type_interp rti sr (subst_type sub_m sub_r sub_s sub_t τi))).
          {
            (* this by τs !! i = Some τi *)
            admit.
          }
          rewrite H'.
          pose proof (Forall_lookup_1 _ _ i τi H Hτi_lookup) as IH_τi.
          by specialize (IH_τi sub_t sub_r sub_s sub_m se se' Hsub_r Hsub_s Hsub_T
                        (SWords ws)).
        * (* prod *)
          admit.
        * (* struct *)
          admit.
        * (** refT, induction fixed, now need varm relation and potential bidirectional *)
          intros.
          iPoseProof (type_interp_eq_r with "[$Hoa]") as "Hoa".
          iDestruct "Hoa" as "(%sκ & %Hsκ & Hsκ & Hm)".
          iApply type_interp_eq_l.
          iExists sκ. (* used to destruct sκ first *)
          iFrame.
          iSplitR; [iPureIntro; by eapply eval_kind_subst_senv|].
          (* huh. sure okay. I guess I don't need to have κ be valtype? *)
          destruct m; [|destruct b].
          --
             (* I think this is where we now need some sort of varm relation? *)
             (* interesting that before this was just done. Probably because of the
                incorrect satoms *)
             admit.
          --
             (* HWY IS IH\TAU SATOMS AAAAAAAAAA *)
             (* is outdated :) no longer panic :) *)
             iDestruct "Hm" as "(%ℓ & %fs & %ws & h1 & h2 & h3 & Hoa)".
             iFrame.
             iModIntro.
             by eapply IHτ.
          --
             iDestruct "Hm" as "(%ℓ & %fs & h1 & Hinv)".
             iFrame.
             iExists fs.
             (* I need some sort of "invariant implies another" *)
             (* Search na_inv. *)
             (* uh oh. na_inv_iff is similar. But. It's iff. *)
             (* we only have one way. Uhoh. another place that requires bidirectional *)
             (* Locate na_inv_iff. *)
             (* hmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmm TODO *)
             admit.
        * (* coderef, qed *)
          (* I think this IH for function types is what we need but we'll see *)
          intros.
          iPoseProof (type_interp_eq_r with "[$Hoa]") as "Hoa".
          iApply type_interp_eq_l.
          iDestruct "Hoa" as "(%sκ & %Hsκ & Hsκ & (%i & %i32 & %j & %cl & Hcl))".
          destruct sκ as [ιs ξ | n ξ]; [|].
          2: { (* contradictory case, sκ = SMEMTYPE *)
            iDestruct "Hcl" as "(_ & %tosubst & _)".
            subst s.
            iEval (cbn) in "Hsκ".
            by iDestruct "Hsκ" as "[[]_]".
          }
          iExists (SVALTYPE ιs ξ).
          iFrame.
          iSplitR; [iPureIntro; by eapply eval_kind_subst_senv|].
          iExists i, i32, j, cl.
          iDestruct "Hcl" as "(H1 & H2 & H3 & H4 & H5)".
          iFrame.
          specialize (IHτ se se' cl sub_m sub_r sub_s sub_t Hsub_r Hsub_s Hsub_T).
          iPoseProof IHτ as "IHτ".
          by iApply IHτ.
        * (* sert *)
          admit.
        * (* plug *)
          admit.
        * (* span *)
          admit.
        * (* rec *)
          intros.

          admit.
        * (* exists mem, need mini value interp lemma, fix for memtype *)
          intros.
          iPoseProof (type_interp_eq_r with "[$Hoa]") as "Hoa".
          iApply type_interp_eq_l.
          iDestruct "Hoa" as "(%sκ & %Hsκ & Hsκ & (%μ & Hμ))".
          iExists sκ.
          iFrame. (* this does delete some pure things *)
          iSplitR; [iPureIntro; eapply eval_kind_subst_senv; done|].

          (* this might be wrong *)
          cbn.
          iExists μ.
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
               done.
             }
             apply Hsub_r in H'.
             by apply eval_rep_up_memory.
          -- intros.
             assert (H': lookup_size se' i = Some n). {
               cbn in H. done.
             }
             apply Hsub_s in H'.
             by apply eval_size_up_memory.
          -- intros.
             assert (H': lookup_type se' i = Some (sκ', T')). {
               unfold senv_insert_mem in H. cbn in H.
               unfold lookup_type in *; cbn in H; by cbn.
             }
             apply Hsub_T in H' as (Hsκ0' & HT').
             split; [by apply type_skind_up_memory|].
             iIntros (sv) "HT' #Hsv".
             iPoseProof (HT' with "[$] [$]") as "Hval".
             (* HERE *)
             (* oh no...
                need a lemma like
                value_interp rti sr se (sub_t i) sv -∗
                value_interp rti sr (senv_insert_mem μ se) (up_memory_type sub_t i) sv
                and all the other combinations for all the other exists
                jeez
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
          (* cbn. *)
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
        * (* ForallMemT case, done except value interp mini lemma *)
          intros ??????? Hsub_r Hsub_s Hsub_T.
          iIntros "Hcl".
          cbn.
          iPoseProof "Hcl" as "#Hcl". (* to avoid cbn while in persistent *)
          iModIntro.
          iIntros.
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
          iPoseProof "Hcl" as "#Hcl".
          iModIntro.

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

  (* As mentioned in a lower comment, this might require an additional assumption *)
  (* this need to be a bimplication. Terrifying. *)
  Lemma values_interp_subst_type se se' τs os sub_m sub_r sub_s sub_t :
    (sem_env_rel_rep se' se sub_r) ->
    (sem_env_rel_size se' se sub_s) ->
    (sem_env_rel_type se' se sub_t) ->
    values_interp rti sr se' τs os -∗
    values_interp rti sr se (map (subst_type sub_m sub_r sub_s sub_t) τs) os.
  Proof.
    iIntros (Hsub_r Hsub_s Hsub_T).
    pose proof (rel_type_implies_rel_sκ se' se sub_t Hsub_T) as Hsub_t.
    (* comment/uncomment if you want/don't want to see them *)
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
      (* note: concat oss = concat oss' does not imply oss = oss'. A bit stupid but okay. *)

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
        (* I need it to not be SAtoms o. I'm scared. *)
        (* it turned out okay :) *)
        (* generalize dependent o. *)
        generalize dependent (SAtoms o).
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
               closure_interp rti sr ft se' cl -∗
               closure_interp rti sr (subst_function_type sub_m sub_r sub_s sub_t ft) se cl).
        * (** vart, qed *)
          intros.
          iDestruct "Hoa" as "(%sκ & %Hse'skind & Hoa & Htypevar)".
          (* This is now using the correct Hsub_t *)
          pose proof (rel_type_implies_rel_sκ se' se sub_t Hsub_T) as Hsub_t.
          apply Hsub_t in Hse'skind as Htypeskind.
          (* destruct Htypeskind as (sκ' & Htypeskind & Hsubsk). *)
          (* inversion Hsubsk; subst. *)
          cbn in Hse'skind.
          destruct (se'.2 !! idx) eqn:Hse'typenv;
            [| rewrite Hse'typenv in Hse'skind; cbn in Hse'skind; by inversion Hse'skind].
          destruct o0 as [sκ' T].
          assert (temp: sκ' = sκ). {
            rewrite Hse'typenv in Hse'skind. cbn in Hse'skind. by inversion Hse'skind.
          }
          subst sκ'.


          iEval (cbn; rewrite Hse'typenv; cbn) in "Htypevar".


          apply Hsub_T in Hse'typenv as [_ Hsub_T_true].
          specialize (Hsub_T_true s).
          iApply (Hsub_T_true with "[$] [$]").
        * (* i31, qed *)
          intros; cbn.
          iDestruct "Hoa" as "(%sk & %HEval & %Hoa & _)".
          iExists sk; iSplitR; [iPureIntro | iSplitR; [iPureIntro; done | done]].
          by eapply eval_kind_subst_senv.
        * (* numt, qed *)
          intros. cbn.
          iDestruct "Hoa" as "(%sk & %HEval & %Hoa & _)".
          iExists sk; iSplitR; [iPureIntro | iSplitR; [iPureIntro; done | done]].
          by eapply eval_kind_subst_senv.
        * (* sum, nearly qed except for map/forall2 lemmas *)
          intros.
          iPoseProof (type_interp_eq_r with "[$Hoa]") as "Hoa".
          iApply type_interp_eq_l.
          iDestruct "Hoa" as "(%sk & %HEval & %Hoa & Hsuminterp)".
          iExists sk; iSplitR;
            [iPureIntro; by eapply eval_kind_subst_senv |
            iSplitR; [iPureIntro; done|]].
          destruct κ as [ρ ξ|n ξ]; cbn in HEval;
            apply bind_Some in HEval as (ιs & Hea & toinvert);
            inversion toinvert; subst; cbn in Hoa; [|done]; clear toinvert.

          destruct ρ; iEval (cbn) in "Hsuminterp"; try done.
          rename l into ρs.

          (* need to destruct Hsuminterp a bit more *)
          iDestruct "Hsuminterp" as "(%i & %os & %off & %count &
                              %H1 & %H2 & %H3 & Hoa)".
          destruct (list_lookup i (map (type_interp rti sr) τs)) eqn:Hτi_interp; try done.
          rename o0 into τi_interp.

          (* idk how to work with these maps but lemme get some of this out *)
          assert (H': ∃ τi, τs !! i = Some τi /\ τi_interp = type_interp rti sr τi). {
            (* obvious by Hτi_interp *)

            admit.
          }
          destruct H' as (τi & Hτi_lookup & Hτi).
          subst τi_interp.
          rewrite type_interp_eq.

          iEval (cbn).
          iExists i, os, off, count.

          (* let's try to work with this now! *)
          iSplitR; [done |
            iSplitR; [iPureIntro |
            iSplitR; [iPureIntro |]]]; last first.
          -- pose proof (Forall_lookup_1 _ _ i τi H Hτi_lookup) as IH_τi.
             specialize (IH_τi sub_t sub_r sub_s sub_m se se' Hsub_r Hsub_s Hsub_T
                        (SAtoms (take count (drop off os)))).

             assert (H': list_lookup i (map (type_interp rti sr)
                              (map (subst_type sub_m sub_r sub_s sub_t) τs)) =
                           Some (type_interp rti sr (subst_type sub_m sub_r sub_s sub_t τi))).
                  {
                    (* this by τs !! i = Some τi *)

                    admit.
                  }
             by rewrite H' -type_interp_eq.
          -- apply fmap_Some.
             apply fmap_Some in H3 as (ιs_ρ & Hy & Hah).
             exists ιs_ρ.
             split; [|done].
             apply bind_Some.
             apply bind_Some in Hy as (ρ & Hz & Hbh).
             cbn in Hbh.
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
        * (* variant qed except for map lemmas *)
          intros.
          iPoseProof (type_interp_eq_r with "[$Hoa]") as "Hoa".
          iApply type_interp_eq_l.
          iDestruct "Hoa" as "(%sκ & %Hsκ & %Hso & Hvariant)".

          iExists sκ.
          iSplitR; [iPureIntro; by eapply eval_kind_subst_senv|].
          iSplitR; [done|].

          iDestruct "Hvariant" as "(%i & %n & %ws & %ws' & %Hnat & %tosubst & Hoa)".
          subst s.
          destruct (list_lookup i (map (type_interp rti sr) τs)) eqn:Hτi_interp;
            rewrite Hτi_interp; [|by cbn].
          rename o0 into τi_interp.
          assert (H': ∃ τi, τs !! i = Some τi /\ τi_interp = type_interp rti sr τi). {
            (* obvious by Hτi_interp *)
            admit.
          }
          destruct H' as (τi & Hτi_lookup & Hτi).
          subst τi_interp.

          iEval (cbn).
          iExists i, n, ws, ws'.
          iSplitR; [done | iSplitR; [done |]].
          assert (H': list_lookup i (map (type_interp rti sr)
                                       (map (subst_type sub_m sub_r sub_s sub_t) τs)) =
                        Some (type_interp rti sr (subst_type sub_m sub_r sub_s sub_t τi))).
          {
            (* this by τs !! i = Some τi *)
            admit.
          }
          rewrite H'.
          pose proof (Forall_lookup_1 _ _ i τi H Hτi_lookup) as IH_τi.
          by specialize (IH_τi sub_t sub_r sub_s sub_m se se' Hsub_r Hsub_s Hsub_T
                        (SWords ws)).
        * (* prod *)
          admit.
        * (* struct *)
          admit.
        * (** refT, induction fixed, now need varm relation and potential bidirectional *)
          intros.
          iPoseProof (type_interp_eq_r with "[$Hoa]") as "Hoa".
          iDestruct "Hoa" as "(%sκ & %Hsκ & Hsκ & Hm)".
          iApply type_interp_eq_l.
          iExists sκ. (* used to destruct sκ first *)
          iFrame.
          iSplitR; [iPureIntro; by eapply eval_kind_subst_senv|].
          (* huh. sure okay. I guess I don't need to have κ be valtype? *)
          destruct m; [|destruct b].
          --
             (* I think this is where we now need some sort of varm relation? *)
             (* interesting that before this was just done. Probably because of the
                incorrect satoms *)
             admit.
          --
             (* HWY IS IH\TAU SATOMS AAAAAAAAAA *)
             (* is outdated :) no longer panic :) *)
             iDestruct "Hm" as "(%ℓ & %fs & %ws & h1 & h2 & h3 & Hoa)".
             iFrame.
             iModIntro.
             by eapply IHτ.
          --
             iDestruct "Hm" as "(%ℓ & %fs & h1 & Hinv)".
             iFrame.
             iExists fs.
             (* I need some sort of "invariant implies another" *)
             (* Search na_inv. *)
             (* uh oh. na_inv_iff is similar. But. It's iff. *)
             (* we only have one way. Uhoh. another place that requires bidirectional *)
             (* Locate na_inv_iff. *)
             (* hmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmm TODO *)
             admit.
        * (* coderef, qed *)
          (* I think this IH for function types is what we need but we'll see *)
          intros.
          iPoseProof (type_interp_eq_r with "[$Hoa]") as "Hoa".
          iApply type_interp_eq_l.
          iDestruct "Hoa" as "(%sκ & %Hsκ & Hsκ & (%i & %i32 & %j & %cl & Hcl))".
          destruct sκ as [ιs ξ | n ξ]; [|].
          2: { (* contradictory case, sκ = SMEMTYPE *)
            iDestruct "Hcl" as "(_ & %tosubst & _)".
            subst s.
            iEval (cbn) in "Hsκ".
            by iDestruct "Hsκ" as "[[]_]".
          }
          iExists (SVALTYPE ιs ξ).
          iFrame.
          iSplitR; [iPureIntro; by eapply eval_kind_subst_senv|].
          cbn.
          iExists i, i32, j, cl.
          iDestruct "Hcl" as "(H1 & H2 & H3 & H4 & H5)".
          iFrame.
          specialize (IHτ se se' cl sub_m sub_r sub_s sub_t Hsub_r Hsub_s Hsub_T).
          iPoseProof IHτ as "IHτ".
          by iApply IHτ.
        * (* sert *)
          admit.
        * (* plug *)
          admit.
        * (* span *)
          admit.
        * (* rec *)
          intros.

          admit.
        * (* exists mem, need mini value interp lemma, fix for memtype *)
          intros.
          iPoseProof (type_interp_eq_r with "[$Hoa]") as "Hoa".
          iApply type_interp_eq_l.
          iDestruct "Hoa" as "(%sκ & %Hsκ & Hsκ & (%μ & Hμ))".
          iExists sκ.
          iFrame. (* this does delete some pure things *)
          iSplitR; [iPureIntro; eapply eval_kind_subst_senv; done|].

          (* this might be wrong *)
          cbn.
          iExists μ.
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
               done.
             }
             apply Hsub_r in H'.
             by apply eval_rep_up_memory.
          -- intros.
             assert (H': lookup_size se' i = Some n). {
               cbn in H. done.
             }
             apply Hsub_s in H'.
             by apply eval_size_up_memory.
          -- intros.
             assert (H': lookup_type se' i = Some (sκ', T')). {
               unfold senv_insert_mem in H. cbn in H.
               unfold lookup_type in *; cbn in H; by cbn.
             }
             apply Hsub_T in H' as (Hsκ0' & HT').
             split; [by apply type_skind_up_memory|].
             iIntros (sv) "HT' #Hsv".
             iPoseProof (HT' with "[$] [$]") as "Hval".
             (* HERE *)
             (* oh no...
                need a lemma like
                value_interp rti sr se (sub_t i) sv -∗
                value_interp rti sr (senv_insert_mem μ se) (up_memory_type sub_t i) sv
                and all the other combinations for all the other exists
                jeez
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
          setoid_rewrite closure_interp_eq.
          (* cbn. *)
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
        * (* ForallMemT case, done except value interp mini lemma *)
          intros ??????? Hsub_r Hsub_s Hsub_T.
          setoid_rewrite closure_interp_eq.
          iIntros "Hcl".
          cbn.
          iPoseProof "Hcl" as "#Hcl". (* to avoid cbn while in persistent *)
          iModIntro.
          iIntros.
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
        * (* ForallRepT *)
          admit.
        * (* ForallSizeT *)
          intros ??????? Hsub_r Hsub_s Hsub_T.
          setoid_rewrite closure_interp_eq.
          admit.
        * (* ForallTypeT *)
          setoid_rewrite closure_interp_eq.
          intros ??????? Hsub_r Hsub_s Hsub_T.
          iIntros "Hcl"; cbn.
          iDestruct "Hcl" as "(%sκ & %Hκ & Hcl)".
          iExists sκ.
          iSplitR; [iPureIntro; by eapply eval_kind_subst_senv|].
          iIntros (?? Hsubs Hskind).
          iSpecialize ("Hcl" $! sκ_T T Hsubs Hskind).
          iPoseProof "Hcl" as "#Hcl".
          iModIntro.

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
  Admitted.


  (* TODO: The lemma for values_interp0 might require adding an assumption about
     the memory substitution? *)
    (** NOTE: THESE ARE THE SAME CASES AS THE LAST 5 CASES IN VALUE_INTERP0_SUBST_SENV ABOVE
        So technically more of these are done than it seems. I'll either copy-paste above
        cases when above lemma is done or be smarter about it somehow.
     *)
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

    induction ϕ as [τs1 τs2| | | |κ] .
    - iIntros (?????? Hsub_r Hsub_s Hsub_T) "#Hcl".
      pose proof (rel_type_implies_rel_sκ se' se sub_t Hsub_T) as Hsub_t.
      unfold_sem_rels.
      destruct cl; [|auto].
      destruct f as [τs1_trans τs2_trans] eqn:Hf.
      setoid_rewrite closure_interp_eq.
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
    - setoid_rewrite closure_interp_eq.
      iIntros (?????? Hsub_r Hsub_s Hsub_T) "#Hcl".
      (* had to simplify before iIntros or iIntros would unfold closure_interp. *)
      cbn.
      iIntros "%".
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
    - setoid_rewrite closure_interp_eq.
      iIntros (?????? Hsub_r Hsub_s Hsub_T) "#Hcl".
      cbn.
      iIntros "%".
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
    - setoid_rewrite closure_interp_eq.
      iIntros (?????? Hsub_r Hsub_s Hsub_T) "#Hcl".
      cbn.
      iIntros "%".
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
      destruct i; cbn -[type_skind skind_has_svalue] in *.
      + unfold senv_insert_type in H.
        inversion H; subst; unfold T. done.
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
    setoid_rewrite value_interp_eq.

    (* now we need to use the key hypothesis: Hfinst *)
    destruct Hfinst.

    (* dig into all at once down to closure interp *)
    all: unfold ϕ'.

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
