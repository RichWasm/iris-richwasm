From Stdlib Require Export ZArith.

From stdpp Require Export base list.

Require Export RecordUpdate.RecordUpdate.

From iris.proofmode Require Export base proofmode classes.

From RichWasm.named_props Require Export named_props custom_syntax.
From RichWasm Require Export layout syntax typing util.
From RichWasm.compiler Require Export prelude codegen instruction module.
From RichWasm.iris Require Export autowp memory logrel util.
Require Export RichWasm.iris.logrel.instr.kinding.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section util.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Lemma eval_rep_emptyenv :
    forall ρ ιs,
      eval_rep EmptyEnv ρ = Some ιs ->
      ∀ (se: semantic_env (Σ:=Σ)),
        eval_rep se ρ = Some ιs.
  Proof.
    induction ρ using rep_ind; intros * Hev *; cbn in Hev; cbn.
    - inversion Hev.
    - rewrite -Hev.
      f_equal.
      apply fmap_Some in Hev.
      destruct Hev as (ιss & Hev & _).
      apply mk_is_Some in Hev.
      apply mapM_is_Some_1 in Hev.
      apply Forall_mapM_ext.
      eapply Forall_impl.
      { eapply (List.Forall_and H Hev). }
      cbn.
      intros ρ [Hev' [ιs' Hempty]].
      erewrite Hev'; eauto.
    - rewrite -Hev.
      f_equal.
      apply fmap_Some in Hev.
      destruct Hev as (ιss & Hev & _).
      apply mk_is_Some in Hev.
      apply mapM_is_Some_1 in Hev.
      apply Forall_mapM_ext.
      eapply Forall_impl.
      { eapply (List.Forall_and H Hev). }
      cbn.
      intros ρ [Hev' [ιs' Hempty]].
      erewrite Hev'; eauto.
    - done.
  Qed.

  Lemma mapM_eval_rep_emptyenv ρs ιss (se: semantic_env (Σ:=Σ)) :
    mapM (eval_rep EmptyEnv) ρs = Some ιss ->
    mapM (eval_rep se) ρs = Some ιss.
  Proof.
    intros Hemp.
    rewrite mapM_Some in Hemp.
    rewrite mapM_Some.
    eapply Forall2_impl.
    2: {
      intros.
      apply eval_rep_emptyenv.
      apply H.
    }
    done.
  Qed.

  Lemma sum_offset_emptyenv ρs i off (se: semantic_env (Σ:=Σ)) :
    sum_offset EmptyEnv ρs i = Some off ->
    sum_offset se ρs i = Some off.
  Proof.
    intros Hso.
    apply bind_Some in Hso as [ιss [Her H]].
    eapply mapM_eval_rep_emptyenv in Her.
    apply bind_Some.
    eauto.
  Qed.

  Lemma eval_kind_of_eval_rep (se: semantic_env (Σ:=Σ)) ρ ιs :
    eval_rep se ρ = Some ιs ->
    forall ξ, eval_kind se (VALTYPE ρ ξ) = Some (SVALTYPE ιs ξ).
  Proof.
    intros Heval ξ.
    unfold eval_kind.
    apply bind_Some.
    by eexists.
  Qed.

  Lemma type_skind_eval_rep (se: semantic_env (Σ:=Σ)) F ρ ιs ξ τ ιs' ξ' :
    has_kind F τ (VALTYPE ρ ξ) ->
    sem_env_interp F se ->
    eval_rep se ρ = Some ιs ->
    type_skind se τ = Some (SVALTYPE ιs' ξ') ->
    ιs = ιs' /\ ξ = ξ'.
  Proof.
    intros.
    assert (SVALTYPE ιs ξ = SVALTYPE ιs' ξ') as Heq.
    - eapply type_skind_has_kind_agree; try done.
      cbn.
      by rewrite H1.
    - by inversion Heq.
  Qed.

  Lemma type_skind_eval_rep_emptyenv (se: semantic_env (Σ:=Σ)) F ρ ιs ξ τ ιs' ξ' :
    has_kind F τ (VALTYPE ρ ξ) ->
    sem_env_interp F se ->
    eval_rep EmptyEnv ρ = Some ιs ->
    type_skind se τ = Some (SVALTYPE ιs' ξ') ->
    ιs = ιs' /\ ξ = ξ'.
  Proof.
    intros.
    eapply type_skind_eval_rep; try done.
    by apply eval_rep_emptyenv.
  Qed.

  Lemma fe_of_context_labels F f :
    fe_of_context F = fe_of_context (F <| fc_labels ::= f |>).
  Proof.
    done.
  Qed.

  Lemma fe_wlocal_offset_length F :
    fe_wlocal_offset (fe_of_context F) = length $ concat (typing.fc_locals F).
  Proof.
    unfold fe_wlocal_offset. simpl.
    apply sum_list_with_length_concat.
  Qed.

  Lemma seq_forall_leq base len :
    Forall (λ i, i < base + len) (seq base len).
  Proof.
    rewrite Forall_seq.
    intros j Hj.
    lia.
  Qed.

  Lemma map_seq_forall_localidx_leq base len :
    Forall (λ i : prelude.W.localidx, localimm i < base + len)
      (map prelude.W.Mk_localidx (seq base len)).
  Proof.
    apply Forall_map.
    apply seq_forall_leq.
  Qed.

  Lemma map_seq_forall_localidx_neq base len :
    Forall (λ i : prelude.W.localidx, localimm i ≠ base + len)
      (map prelude.W.Mk_localidx (seq base len)).
  Proof.
    eapply Forall_impl; first apply map_seq_forall_localidx_leq.
    lias.
  Qed.

  Lemma eval_rep_senv_insert_type sκ T (se: semantic_env (Σ:=Σ)) ρ :
    eval_rep (senv_insert_type sκ T se) ρ = eval_rep se ρ.
  Proof.
    induction ρ using rep_ind; cbn.
    - reflexivity.
    - f_equal. apply Forall_mapM_ext.
      eapply Forall_impl; [exact H |].
      intros ρ' IH. apply IH.
    - f_equal. apply Forall_mapM_ext.
      eapply Forall_impl; [exact H |].
      intros ρ' IH. apply IH.
    - reflexivity.
  Qed.

  Lemma eval_size_senv_insert_type sκ T (se: semantic_env (Σ:=Σ)) σ :
    eval_size (senv_insert_type sκ T se) σ = eval_size se σ.
  Proof.
    induction σ using size_ind; cbn.
    - reflexivity.
    - f_equal. apply Forall_mapM_ext.
      eapply Forall_impl; [exact H |].
      intros σ' IH. apply IH.
    - f_equal. apply Forall_mapM_ext. exact H.
    - by rewrite eval_rep_senv_insert_type.
    - reflexivity.
  Qed.

  Lemma eval_kind_senv_insert_type sκ T (se: semantic_env (Σ:=Σ)) κ :
    eval_kind (senv_insert_type sκ T se) κ = eval_kind se κ.
  Proof.
    unfold eval_kind, senv_insert_type. simpl.
    destruct κ; simpl.
    - rewrite eval_rep_senv_insert_type. reflexivity.
    - rewrite eval_size_senv_insert_type. reflexivity.
  Qed.

  Lemma eval_rep_prod_atoms (se: semantic_env (Σ:=Σ)) ηs :
    eval_rep se (ProdR (map (AtomR ∘ prim_to_arep) ηs)) = Some (map prim_to_arep ηs).
  Proof.
    induction ηs; simpl; first done.
    simpl in IHηs.
    destruct (mapM (eval_rep se) (map (AtomR ∘ prim_to_arep) ηs)) as [ιss|] eqn:Hmapм; simpl in *; last done.
    injection IHηs as IHηs.
    by rewrite IHηs.
  Qed.

End util.
