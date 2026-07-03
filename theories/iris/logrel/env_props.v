Require Import RecordUpdate.RecordUpdate.
Require Import RichWasm.iris.language.iris_wp_def.
Require Import RichWasm.iris.logrel.
Require Import RichWasm.layout.
Require Import RichWasm.syntax.
Require Import RichWasm.typing.
Require Import RichWasm.util.
Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section env_props.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  (* note: first half of file is 10 billion eval insertion/substitution
     for lemmas related to actually inserting into, search INSERTION LEMMAS *)

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

  Lemma eval_rep_mem_irrel se ρ ιs μ :
    eval_rep se ρ = Some ιs ->
    eval_rep (senv_insert_mem (Σ:=Σ) μ se) ρ = Some ιs.
  Proof.
    intros; rewrite <- eval_rep_mem_irrel_eq; done.
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

  Lemma eval_rep_size_irrel se ρ ιs n :
    eval_rep se ρ = Some ιs ->
    eval_rep (senv_insert_size (Σ:=Σ) n se) ρ = Some ιs.
  Proof.
    intros; rewrite <- eval_rep_size_irrel_eq; done.
  Qed.

  Lemma eval_rep_type_irrel_eq se ρ sκ sκ_T T :
    eval_rep se ρ =
    eval_rep (senv_insert_type (Σ:=Σ) sκ sκ_T T se) ρ.
  Proof.
    induction ρ using rep_ind; auto.
    - cbn in *.
      assert (H': mapM (eval_rep se) ρs = mapM (eval_rep (senv_insert_type sκ sκ_T T se)) ρs)
        by by apply Forall_mapM_ext.
      by rewrite H'.
    - cbn in *.
      assert (H': mapM (eval_rep se) ρs = mapM (eval_rep (senv_insert_type sκ sκ_T T se)) ρs)
        by by apply Forall_mapM_ext.
      by rewrite H'.
  Qed.

  Lemma eval_rep_type_irrel se ρ ιs sκ sκ_T T :
    eval_rep se ρ = Some ιs ->
    eval_rep (senv_insert_type (Σ:=Σ) sκ sκ_T T se) ρ = Some ιs.
  Proof.
    intros; rewrite <- eval_rep_type_irrel_eq; done.
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

  Lemma eval_size_mem_irrel se σ n μ :
    eval_size se σ = Some n ->
    eval_size (senv_insert_mem (Σ:=Σ) μ se) σ = Some n.
  Proof.
    intros; rewrite <- eval_size_mem_irrel_eq; done.
  Qed.

  Lemma eval_size_type_irrel_eq se σ sκ sκ_T T :
    eval_size se σ =
    eval_size (senv_insert_type (Σ:=Σ) sκ sκ_T T se) σ.
  Proof.
    induction σ using size_ind; intros; auto.
    - cbn in *.
      assert (H': mapM (eval_size se) σs = mapM (eval_size (senv_insert_type sκ sκ_T T se)) σs)
        by by apply Forall_mapM_ext.
      by rewrite H'.
    - cbn in *.
      assert (H': mapM (eval_size se) σs = mapM (eval_size (senv_insert_type sκ sκ_T T se)) σs)
        by by apply Forall_mapM_ext.
      by rewrite H'.
    - cbn -[senv_insert_type].
      by rewrite <- eval_rep_type_irrel_eq.
  Qed.

  Lemma eval_size_type_irrel se σ n sκ sκ_T T :
    eval_size se σ = Some n ->
    eval_size (senv_insert_type (Σ:=Σ) sκ sκ_T T se) σ = Some n.
  Proof.
    intros; rewrite <- eval_size_type_irrel_eq; done.
  Qed.

  Lemma eval_mem_type_irrel_eq se m sκ sκ_T T :
    eval_mem se m =
    eval_mem (senv_insert_type (Σ:=Σ) sκ sκ_T T se) m.
  Proof.
    destruct m; auto.
  Qed.

  Lemma eval_kind_mem_irrel_eq se κ μ :
    eval_kind se κ =
    eval_kind (senv_insert_mem (Σ:=Σ) μ se) κ .
  Proof.
    destruct κ; intros; cbn -[senv_insert_mem senv_insert_type] in *.
    - by rewrite <- eval_rep_mem_irrel_eq.
    - by rewrite <- eval_size_mem_irrel_eq.
  Qed.

  Lemma eval_kind_mem_irrel se κ sκ μ :
    eval_kind se κ = Some sκ ->
    eval_kind (senv_insert_mem (Σ:=Σ) μ se) κ = Some sκ.
  Proof.
    intros; rewrite <- eval_kind_mem_irrel_eq; done.
  Qed.

  Lemma eval_kind_type_irrel_eq se κ sκ sκ_T T :
    eval_kind se κ =
    eval_kind (senv_insert_type (Σ:=Σ) sκ sκ_T T se) κ .
  Proof.
    destruct κ; intros; cbn -[senv_insert_type] in *.
    - by rewrite <- eval_rep_type_irrel_eq.
    - by rewrite <- eval_size_type_irrel_eq.
  Qed.

  Lemma eval_kind_type_irrel se κ sκ sκ' sκ_T T :
    eval_kind se κ = Some sκ ->
    eval_kind (senv_insert_type (Σ:=Σ) sκ' sκ_T T se) κ = Some sκ.
  Proof.
    intros; rewrite <- eval_kind_type_irrel_eq; done.
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

  Lemma type_skind_mem_irrel se μ τ sκ :
    type_skind (Σ:=Σ) se τ = Some sκ ->
    type_skind (Σ:=Σ) (senv_insert_mem μ se)
      (ren_type unscoped.shift unscoped.id unscoped.id unscoped.id τ) = Some sκ.
  Proof.
    intros; rewrite <- type_skind_mem_irrel_eq; done.
  Qed.


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

  Lemma mem_ok_se_up_type sκ sκ_T T se sub_m i :
    mem_ok_se se (sub_m i) <->
      mem_ok_se (senv_insert_type sκ sκ_T T se) (up_type_memory sub_m i).
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

  Lemma eval_rep_up_rep_eq se sub_r ιs0 i :
    eval_rep se (sub_r i) =
    eval_rep (senv_insert_rep (Σ:=Σ) ιs0 se) (up_representation_representation sub_r (S i)).
  Proof.
    asimpl'.
    unfold core.funcomp.
    induction (sub_r i) using rep_ind; try (by cbn).
    - Opaque senv_insert_rep.
      cbn.
      assert (H': mapM (eval_rep se) ρs = mapM (eval_rep (senv_insert_rep ιs0 se))
             (map (ren_representation unscoped.shift) ρs)) by (by apply Forall_mapM_map_ext).
      by rewrite H'.
    - cbn.
      assert (H': mapM (eval_rep se) ρs = mapM (eval_rep (senv_insert_rep ιs0 se))
             (map (ren_representation unscoped.shift) ρs)) by (by apply Forall_mapM_map_ext).
      by rewrite H'.
  Qed.

  Lemma eval_rep_up_rep se sub_r ιs0 i ιs :
    eval_rep se (sub_r i) = Some ιs ->
    eval_rep (senv_insert_rep (Σ:=Σ) ιs0 se) (up_representation_representation sub_r (S i)) = Some ιs.
  Proof.
    intros; rewrite <- eval_rep_up_rep_eq; done.
  Qed.

  Lemma eval_rep_up_size_eq se sub_r i n :
    eval_rep se (sub_r i) =
    eval_rep (senv_insert_size (Σ:=Σ) n se) (up_size_representation sub_r i).
  Proof.
    asimpl'.
    unfold core.funcomp.
    by rewrite <- eval_rep_size_irrel_eq.
  Qed.

  Lemma eval_rep_up_size se sub_r ιs i n :
    eval_rep se (sub_r i) = Some ιs ->
    eval_rep (senv_insert_size (Σ:=Σ) n se) (up_size_representation sub_r i) = Some ιs.
  Proof.
    asimpl'.
    by apply eval_rep_size_irrel.
  Qed.

  Lemma eval_rep_up_memory_eq se sub_r i μ :
    eval_rep se (sub_r i) =
    eval_rep (senv_insert_mem (Σ:=Σ) μ se) (up_memory_representation sub_r i).
  Proof.
    asimpl'.
    unfold core.funcomp.
    by rewrite <- eval_rep_mem_irrel_eq.
  Qed.

  Lemma eval_rep_up_type_eq se sub_r i sκ sκ_T T :
    eval_rep se (sub_r i) =
    eval_rep (senv_insert_type (Σ:=Σ) sκ sκ_T T se) (up_type_representation sub_r i).
  Proof.
    asimpl'.
    unfold core.funcomp.
    by rewrite <- eval_rep_type_irrel_eq.
  Qed.

  Lemma eval_rep_up_memory se sub_r ιs i μ :
    eval_rep se (sub_r i) = Some ιs ->
    eval_rep (senv_insert_mem (Σ:=Σ) μ se) (up_memory_representation sub_r i) = Some ιs.
  Proof.
    asimpl'.
    by apply eval_rep_mem_irrel.
  Qed.

  Lemma eval_size_up_memory_eq se sub_s i μ :
    eval_size se (sub_s i) =
    eval_size (senv_insert_mem (Σ:=Σ) μ se) (up_memory_size sub_s i).
  Proof.
    asimpl'.
    unfold core.funcomp.
    by rewrite <- eval_size_mem_irrel_eq.
  Qed.

  Lemma eval_size_up_memory se sub_s n i μ :
    eval_size se (sub_s i) = Some n ->
    eval_size (senv_insert_mem (Σ:=Σ) μ se) (up_memory_size sub_s i) = Some n.
  Proof.
    asimpl'.
    by apply eval_size_mem_irrel.
  Qed.

  Lemma eval_size_up_type_eq se sub_s i sκ sκ_T T :
    eval_size se (sub_s i) =
    eval_size (senv_insert_type (Σ:=Σ) sκ sκ_T T se) (up_type_size sub_s i).
  Proof.
    asimpl'.
    unfold core.funcomp.
    by rewrite <- eval_size_type_irrel_eq.
  Qed.

  Lemma eval_mem_up_type_eq se sub_m i sκ sκ_T T :
    eval_mem se (sub_m i) =
    eval_mem (senv_insert_type (Σ:=Σ) sκ sκ_T T se) (up_type_memory sub_m i).
  Proof.
    asimpl'.
    unfold core.funcomp.
    by rewrite <- eval_mem_type_irrel_eq.
  Qed.

  Lemma eval_mem_up_shift_mem_eq se μ mm :
    eval_mem se mm =
    eval_mem (senv_insert_mem (Σ:=Σ) μ se) (ren_memory unscoped.shift mm).
  Proof.
    destruct mm; by cbn.
  Qed.

  Lemma eval_rep_up_shift_rep_eq se ρ ιs :
    eval_rep se ρ =
    eval_rep (senv_insert_rep (Σ:=Σ) ιs se) (ren_representation unscoped.shift ρ) .
  Proof.
    induction ρ using rep_ind; try (by cbn).
    - cbn.
      assert (H': mapM (eval_rep se) ρs = mapM (eval_rep (senv_insert_rep ιs se))
             (map (ren_representation unscoped.shift) ρs)) by (by apply Forall_mapM_map_ext).
      by rewrite H'.
    - cbn.
      assert (H': mapM (eval_rep se) ρs = mapM (eval_rep (senv_insert_rep ιs se))
             (map (ren_representation unscoped.shift) ρs)) by (by apply Forall_mapM_map_ext).
      by rewrite H'.
  Qed.

  Lemma eval_rep_up_shift_rep se ρ n ιs :
    eval_rep se ρ = Some n ->
    eval_rep (senv_insert_rep (Σ:=Σ) ιs se) (ren_representation unscoped.shift ρ) = Some n.
  Proof.
    rewrite <- eval_rep_up_shift_rep_eq. done.
  Qed.

  Lemma eval_size_up_shift_rep_eq se σ ιs :
    eval_size se σ =
    eval_size (senv_insert_rep (Σ:=Σ) ιs se) (ren_size unscoped.shift unscoped.id σ) .
  Proof.
    induction σ using size_ind; try (by cbn).
    - cbn.
      assert (H': mapM (eval_size se) σs = mapM (eval_size (senv_insert_rep ιs se))
             (map (ren_size unscoped.shift unscoped.id) σs)) by (by apply Forall_mapM_map_ext).
      by rewrite H'.
    - cbn.
      assert (H': mapM (eval_size se) σs = mapM (eval_size (senv_insert_rep ιs se))
             (map (ren_size unscoped.shift unscoped.id) σs)) by (by apply Forall_mapM_map_ext).
      by rewrite H'.
    - cbn. by rewrite <- eval_rep_up_shift_rep_eq.
  Qed.

  Lemma eval_size_up_shift_size_eq se n σ :
    eval_size se σ =
      eval_size (senv_insert_size (Σ:=Σ) n se) (ren_size unscoped.id unscoped.shift σ).
  Proof.
    induction σ using size_ind; try by cbn.
    - cbn.
      assert (H': mapM (eval_size se) σs = mapM (eval_size (senv_insert_size n se))
             (map (ren_size unscoped.id unscoped.shift) σs)) by (by apply Forall_mapM_map_ext).
      by rewrite H'.
    - cbn.
      assert (H': mapM (eval_size se) σs = mapM (eval_size (senv_insert_size n se))
             (map (ren_size unscoped.id unscoped.shift) σs)) by (by apply Forall_mapM_map_ext).
      by rewrite H'.
    - cbn -[senv_insert_size].
      rewrite rinstId'_representation.
      by rewrite <- eval_rep_size_irrel_eq.
  Qed.

  Lemma eval_size_up_shift_rep se ρ n ιs :
    eval_rep se ρ = Some n ->
    eval_rep (senv_insert_rep (Σ:=Σ) ιs se) (ren_representation unscoped.shift ρ) = Some n.
  Proof.
    rewrite <- eval_rep_up_shift_rep_eq. done.
  Qed.

  Lemma eval_size_up_rep_eq se sub_s ιs i :
    eval_size se (sub_s i) =
    eval_size (senv_insert_rep (Σ:=Σ) ιs se) (up_representation_size sub_s i).
  Proof.
    asimpl'; unfold core.funcomp.
    induction (sub_s i) using size_ind; try (by cbn).
    - cbn.
      assert (H': mapM (eval_size se) σs = mapM (eval_size (senv_insert_rep ιs se))
             (map (ren_size unscoped.shift unscoped.id) σs)) by (by apply Forall_mapM_map_ext).
      by rewrite H'.
    - cbn.
      assert (H': mapM (eval_size se) σs = mapM (eval_size (senv_insert_rep ιs se))
             (map (ren_size unscoped.shift unscoped.id) σs)) by (by apply Forall_mapM_map_ext).
      by rewrite H'.
    - cbn.
      by rewrite <- eval_rep_up_shift_rep_eq.
  Qed.

  Lemma eval_size_up_rep se sub_s ιs i n :
    eval_size se (sub_s i) = Some n ->
    eval_size (senv_insert_rep (Σ:=Σ) ιs se) (up_representation_size sub_s i) = Some n.
  Proof.
    intros H.
    rewrite <- eval_size_up_rep_eq; done.
  Qed.

  Lemma eval_kind_up_shift_rep_eq se κ ιs :
    eval_kind se κ =
    eval_kind (senv_insert_rep (Σ:=Σ) ιs se) (ren_kind unscoped.shift unscoped.id κ) .
  Proof.
    induction κ as [ρ ξ | σ ξ].
    - cbn. by rewrite <- eval_rep_up_shift_rep_eq.
    - cbn. by rewrite <- eval_size_up_shift_rep_eq.
  Qed.

  Lemma eval_kind_up_shift_size_eq se κ n:
    eval_kind se κ =
    eval_kind (senv_insert_size (Σ:=Σ) n se) (ren_kind unscoped.id unscoped.shift κ) .
  Proof.
    induction κ as [ρ ξ | σ ξ].
    - cbn -[senv_insert_size].
      rewrite rinstId'_representation.
      by rewrite <- eval_rep_size_irrel_eq.
    - cbn -[senv_insert_size].
      by rewrite <- eval_size_up_shift_size_eq.
  Qed.

  Lemma eval_kind_up_shift_rep se κ sκ ιs :
    eval_kind se κ = Some sκ ->
    eval_kind (senv_insert_rep (Σ:=Σ) ιs se) (ren_kind unscoped.shift unscoped.id κ) = Some sκ.
  Proof.
    by rewrite <- eval_kind_up_shift_rep_eq.
  Qed.

  Lemma type_skind_up_rep_eq se sub_t ιs i :
    type_skind se (sub_t i) =
    type_skind (Σ:=Σ) (senv_insert_rep ιs se) (up_representation_type sub_t i) .
  Proof.
    asimpl'; unfold core.funcomp.
    induction (sub_t i) using type_ind with (P0 := λ ft, True) (Pi := λ ft, True);
      cbn in *; auto; by apply eval_kind_up_shift_rep_eq.
  Qed.

  Lemma type_skind_up_rep se sub_t ιs sκ i :
    type_skind se (sub_t i) = Some sκ ->
    type_skind (Σ:=Σ) (senv_insert_rep ιs se) (up_representation_type sub_t i) = Some sκ.
  Proof.
    by rewrite <- type_skind_up_rep_eq.
  Qed.

  Lemma type_skind_up_memory_eq se sub_t μ i :
    type_skind se (sub_t i) =
    type_skind (Σ:=Σ) (senv_insert_mem μ se) (up_memory_type sub_t i) .
  Proof.
    asimpl'; unfold core.funcomp.
    induction (sub_t i) using type_ind with (P0 := λ ft, True) (Pi := λ ft, True);
      cbn in *; auto; rewrite rinstId'_kind; by apply eval_kind_mem_irrel_eq.
  Qed.

  Lemma type_skind_up_memory se sub_t μ sκ i :
    type_skind se (sub_t i) = Some sκ ->
    type_skind (Σ:=Σ) (senv_insert_mem μ se) (up_memory_type sub_t i) = Some sκ.
  Proof.
    by rewrite <- type_skind_up_memory_eq.
  Qed.

  Lemma type_skind_up_type_eq se sub_t sκ' sκ_T T i :
    type_skind se (sub_t i) =
    type_skind (Σ:=Σ) (senv_insert_type sκ' sκ_T T se) (up_type_type sub_t (S i)) .
  Proof.
    asimpl'; unfold core.funcomp.
    induction (sub_t i) using type_ind with (P0 := λ ft, True) (Pi := λ ft, True);
      cbn in *; auto; rewrite rinstId'_kind; by apply eval_kind_type_irrel_eq.
  Qed.

  Lemma type_skind_up_type se sub_t sκ' sκ_T T sκ i :
    type_skind se (sub_t i) = Some sκ ->
    type_skind (Σ:=Σ) (senv_insert_type sκ' sκ_T T se) (up_type_type sub_t (S i)) = Some sκ.
  Proof.
    by rewrite <- type_skind_up_type_eq.
  Qed.


  (* INSERTION LEMMAS *)

  Lemma sem_env_interp_insert_type F (se : semantic_env (Σ:=Σ)) κ sκ sκ_T T :
    sem_env_interp F se →
    eval_kind se κ = Some sκ →
    subskind_of sκ_T sκ ->
    skind_has_stype sκ_T T →
    sem_env_interp (F <| fc_type_vars ::= cons κ |>) (senv_insert_type sκ sκ_T T se).
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

End env_props.
