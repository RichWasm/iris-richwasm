Require Import RecordUpdate.RecordUpdate.
Require Import RichWasm.iris.language.iris_wp_def.
Require Import RichWasm.iris.logrel.
Require Import RichWasm.layout.
Require Import RichWasm.syntax.
Require Import RichWasm.typing.
Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section env_props.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.


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
