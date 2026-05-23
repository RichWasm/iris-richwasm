From Stdlib Require Export ZArith.

From stdpp Require Export base list.

Require Export RecordUpdate.RecordUpdate.

From iris.proofmode Require Export base proofmode classes.

From RichWasm.named_props Require Export named_props custom_syntax.
From RichWasm Require Export layout syntax typing util.
Require Export RichWasm.wasm.operations.
From RichWasm.compiler Require Export prelude codegen instruction module.
From RichWasm.iris Require Export autowp memory logrel logrel_properties util wp_codegen.
From RichWasm.iris.language Require Export cwp logpred.
Require Export RichWasm.iris.logrel.instr.kinding.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section common.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

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

  Lemma frame_rel_mask_trans_combine lmask1 lmask2 fr1 fr2 fr3:
    frame_rel lmask1 fr1 fr2 ->
    frame_rel lmask2 fr2 fr3 ->
    frame_rel (λ i, lmask1 i ∧ lmask2 i) fr1 fr3.
  Proof.
    intros fr12 fr23.
    eapply frame_rel_trans;
      (eapply frame_rel_mask_mono; last done; by intros i [H1 H2]).
  Qed.

  Lemma frame_f_locs_update fr fr' vs1 vs_new vs_old vs2 val_idxs :
    val_idxs = seq (length vs1) (length vs_old) ->
    frame_rel (λ i, i ∉ val_idxs) fr fr' ->
    Forall2 (λ i v, f_locs fr' !! i = Some v) val_idxs vs_new ->
    f_locs fr  = vs1 ++ vs_old ++ vs2 ->
    f_locs fr' = vs1 ++ vs_new ++ vs2.
  Proof.
    intros Hval_idxs [Hmask _] HF Hfr.
    (* First extract length vs_new = length vs_old from Forall2 *)
    have Hlen : length vs_new = length vs_old.
    { have := Forall2_length _ _ _ HF. rewrite Hval_idxs length_seq. lia. }
    (* Prove equality pointwise *)
    apply list_eq. intros i.
    destruct (decide (i ∈ val_idxs)) as [Hin | Hout].
    - (* i is in val_idxs, so fr' !! i = Some (vs_new !! ...) *)
      rewrite Hval_idxs in Hin.
      apply elem_of_seq in Hin as [Hlo Hhi].
      (* j is the position of i in val_idxs *)
      set j := i - length vs1.
      have Hj : j < length vs_old by unfold j; lia.
      have Hseq : seq (length vs1) (length vs_old) !! j = Some i.
      { rewrite lookup_seq. unfold j. split; lia. }
      rewrite <- Hval_idxs in Hseq.
      destruct (Forall2_lookup_l _ _ _ _ _ HF Hseq) as [v [Hv HP]].
      (* HP : f_locs fr' !! i = Some v *)
      rewrite HP.
      (* now show (vs1 ++ vs_new ++ vs2) !! i = Some v *)
      rewrite lookup_app_r; [|lia].
      rewrite lookup_app_l; [|rewrite Hlen; lia].
      (* vs_new !! j = Some v from Hv via HP *)
      by rewrite Hv.
    - (* i is not in val_idxs: fr and fr' agree *)
      rewrite <- Hmask; [|exact Hout].
      rewrite Hfr.
      rewrite Hval_idxs in Hout.
      have Hout' : i < length vs1 ∨ length vs1 + length vs_old ≤ i.
      { rewrite elem_of_seq in Hout.
        lia. }
      destruct Hout' as [Hlt | Hge].
      + (* i < length vs1: in the vs1 segment, both sides agree *)
        rewrite !lookup_app_l; lias.
      + (* i ≥ length vs1 + length vs_old: in the vs2 segment *)
        rewrite !lookup_app_r; [|lia..].
        f_equal. lia.
  Qed.

  Lemma frame_f_locs_update' fr fr' vs1 vs_new vs_old vs2 val_idxs val_localidxs :
    val_idxs = seq (length vs1) (length vs_old) ->
    val_localidxs = map prelude.W.Mk_localidx val_idxs ->
    frame_rel (λ i, i ∉ val_idxs) fr fr' ->
    Forall2 (λ i v, f_locs fr' !! localimm i = Some v) val_localidxs vs_new ->
    f_locs fr  = vs1 ++ vs_old ++ vs2 ->
    f_locs fr' = vs1 ++ vs_new ++ vs2.
  Proof.
    intros Hval_idxs Hval_localidxs Hframe_rel HF Hfr.
    eapply frame_f_locs_update; eauto.
    subst val_localidxs.
    rewrite Forall2_fmap_l in HF.
    eapply Forall2_impl; [exact HF|].
    done.
  Qed.

  Lemma frame_rel_Forall2_update fr fr' vs (val_idxs1 val_idxs2 : list nat) :
    frame_rel (λ i, i ∉ val_idxs1) fr fr' ->
    Forall (λ i, i ∉ val_idxs1) val_idxs2 ->
    Forall2 (λ i v, f_locs fr !! i = Some v) val_idxs2 vs ->
    Forall2 (λ i v, f_locs fr' !! i = Some v) val_idxs2 vs.
  Proof.
    intros [Hmask _] Hdisjoint Hforall.
    induction Hforall as [| i v idxs vs Hi Hrest IH].
    - constructor.
    - apply Forall_cons in Hdisjoint as [Hnotin Hdisjoint].
      constructor.
      + rewrite <- Hmask; last exact Hnotin.
        exact Hi.
      + exact (IH Hdisjoint).
  Qed.

  Lemma frame_rel_Forall2_update' fr fr' vs val_localidxs2 (val_idxs1 val_idxs2 : list nat) :
    val_localidxs2 = map prelude.W.Mk_localidx val_idxs2 ->
    frame_rel (λ i, i ∉ val_idxs1) fr fr' ->
    Forall (λ i, i ∉ val_idxs1) val_idxs2 ->
    Forall2 (λ i v, f_locs fr !! localimm i = Some v) val_localidxs2 vs ->
    Forall2 (λ i v, f_locs fr' !! localimm i = Some v) val_localidxs2 vs.
  Proof.
    intros -> Hfrel Hdisjoint Hforall.
    rewrite Forall2_fmap_l in Hforall.
    rewrite Forall2_fmap_l.
    eapply Forall2_impl.
    2: {
      intros x y Hxy.
      simpl.
      apply Hxy.
    }
    eapply frame_rel_Forall2_update; try done.
  Qed.

(* This is a copy of values_interp_cons
  Lemma values_interp_cons_inv se τ τs os :
    ⊢ values_interp rti sr se (τ :: τs) os -∗
      ∃ os1 os2,
        ⌜os = os1 ++ os2⌝ ∗
        value_interp rti sr se τ (SAtoms os1) ∗
        values_interp rti sr se τs os2.
  Proof.
    iIntros "(%vss & %Hconcat & Hval)".
    rewrite big_sepL2_cons_inv_l.
    iDestruct "Hval" as "(%vs1 & %vss2 & %Hvss & Hvs1 & Hvss2)".
    iExists vs1, (concat vss2).
    iSplit; first by rewrite Hconcat Hvss.
    iSplitL "Hvs1".
    - done.
    - iExists _.
      iSplit; done.
  Qed. *)
  Lemma atoms_interp_length os vs :
    ⊢ atoms_interp os vs -∗ ⌜length os = length vs⌝.
  Proof.
    iApply big_sepL2_length.
  Qed.

  Lemma atoms_interp_one_inv o vs :
    atoms_interp [o] vs ⊣⊢ ∃ v, ⌜vs = [v]⌝ ∗ atom_interp o v.
  Proof.
    iSplit.
    - iIntros "Hvs".
      iPoseProof (atoms_interp_cons_l with "Hvs") as (v vs' Heq) "[Hv Hnil]".
      iPoseProof (atoms_interp_nil_l with "Hnil") as "->".
      iExists v; auto.
    - iIntros "(%v & -> & Hv)".
      cbn; auto.
  Qed.

  Lemma value_interp_ref_sz se κ μ τ os :
    value_interp rti sr se (RefT κ μ τ) (SAtoms os) -∗ ⌜length os = 1⌝.
  Proof.
    iIntros "(%sκ & _ & _ & H)".
    destruct μ.
    - destruct (lookup_mem se n) eqn:Hn; cbn in Hn.
      + cbn. rewrite Hn. destruct b.
        * iDestruct "H" as "(% & % & % & %Hos & _)". by inversion Hos.
        * iDestruct "H" as "(% & % & %Hos & _)". by inversion Hos.
      + cbn. by rewrite Hn.
    - cbn. destruct b.
      + iDestruct "H" as "(% & % & % & %Hos & _)". by inversion Hos.
      + iDestruct "H" as "(% & % & %Hos & _)". by inversion Hos.
  Qed.

  (* useful lemma for proving compat lemmas for instructions erased by the compiler. *)
  Lemma sem_type_erased M F L WT WL lmask ψ τs1 τs2 :
    ψ = InstrT τs1 τs2 ->
    ⊢ (∀ se vs,
          values_interp rti sr se τs1 vs -∗
          values_interp rti sr se τs2 vs) -∗
      have_instr_type_sem rti sr mr M F L WT WL lmask [] ψ L.
  Proof.
    iIntros (->) "Hcast".
    iIntros (se inst lh Henv fr rvs vs θ) "@@@@@@@@@@@@".
    rewrite app_nil_r.
    iApply (cwp_val with "[$] [$]"); first done.
    iFrame.
    iSplit.
    - unfold frame_rel.
      iPureIntro; split.
      + unfold mask_locs_eq; eauto.
      + eauto.
    - by iApply "Hcast".
  Qed.

  Lemma sem_type_erased_nop M F L WT WL lmask ψ τs1 τs2 :
    ψ = InstrT τs1 τs2 ->
    ⊢ (∀ se fr B R os,
     "%Hse" ∷ ⌜sem_env_interp F se⌝ -∗
     "#Hinst" ∷ instance_interp rti sr mr M WT (f_inst fr) -∗
     "#Hlabels"
     ∷ labels_interp rti sr se (typing.fc_locals F) fr WL lmask 
         (fc_labels F) B -∗
     "#Hreturn" ∷ return_interp rti sr se (fc_return F) R -∗
          values_interp rti sr se τs1 os -∗
          ▷values_interp rti sr se τs2 os) -∗
      have_instr_type_sem rti sr mr M F L WT WL lmask [BI_nop] ψ L.
  Proof.
    iIntros (->) "Hcast".
    iIntros (se inst lh fr rvs vs θ Henv) "@@@@@@@@@@@@".
    iApply cwp_val_app; first done.
    iApply (cwp_nop with "[$] [$]").
    iFrame.
    iSplit.
    - unfold frame_rel, mask_locs_eq; eauto.
    - rewrite app_nil_r.
      iFrame.
      by iApply "Hcast".
  Qed.

  Lemma forall2_lookup_same {A B} (ls ls' : list A) (idxs : list B) (xs : list A) (j_excl : nat) (f: B -> nat) :
    (∀ j : B, f j ≠ j_excl → ls' !! f j = ls !! f j) ->
    Forall (λ i, f i ≠ j_excl) idxs ->
    Forall2 (λ (i : B) (v : A), ls  !! f i = Some v) idxs xs ->
    Forall2 (λ (i : B) (v : A), ls' !! f i = Some v) idxs xs.
  Proof.
    intros Hsame Hnotin Hf.
    induction Hf.
    - constructor.
    - inversion Hnotin; subst.
      constructor.
      + rewrite Hsame; auto.
      + apply IHHf; auto.
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

  Lemma sem_env_interp_extend_type F (se: semantic_env (Σ:=Σ)) κ sκ T :
    sem_env_interp F se →
    eval_kind se κ = Some sκ →
    skind_has_stype sκ T →
    sem_env_interp (F <| fc_type_vars ::= cons κ |>) (senv_insert_type sκ T se).
  Proof.
    intros [Hkind Htype] Heval Hstype.
    split.
    - (* kind_ctx_interp *)
      unfold kind_ctx_interp in *.
      destruct Hkind as (Hmem & Hrep & Hsize).
      repeat split; assumption.
    - (* type_ctx_interp *)
      unfold type_ctx_interp in *.
      simpl.
      apply Forall2_cons.
      + split.
        * rewrite eval_kind_senv_insert_type. by split.
        * eapply Forall2_impl; first done.
          intros κ0 [sκ0 T0] [Heval0 Hstype0].
          rewrite eval_kind_senv_insert_type.
          split; [exact Heval0 | exact Hstype0].
  Qed.

  Lemma lwp_wasm_empty_ctx s E es Φ:
    lenient_wp s E es Φ ∗-∗ lenient_wp_ctx s E es Φ 0 (LH_base nil nil).
  Proof.
    by iApply wp_wasm_empty_ctx.
  Qed.

  Lemma lwp_label_push s E Φ i lh n es es0 vs es':
    is_true (const_list vs) ->
    ⊢ lenient_wp_ctx s E es Φ (S i) (push_base lh n es0 vs es') -∗
      lenient_wp_ctx s E [AI_label n es0 (vs ++ es ++ es')] Φ i lh.
  Proof.
    iIntros (Hconst) "Hwp".
    change @app with @seq.cat.
    by iApply wp_label_push.
  Qed.


  Lemma append_lh_depth {i : nat} (lh : valid_holed i) e :
    lh_depth (lh_of_vh lh) = lh_depth (lh_of_vh (vh_append lh e)).
  Proof.
    induction lh; simpl; auto.
  Qed.

  Lemma wp_map_gc_ptr_duproot ι idx wt wl res wt' wl' es:
    run_codegen (memory.map_gc_ptr ι idx (memory.duproot mr)) wt wl = inr (res, wt', wl', es) ->
    res = () /\ wt' = [] /\ wl' = [].
  Proof.
    unfold memory.map_gc_ptr, memory.ite_gc_ptr; intros Hcg.
    destruct ι.
    - apply wp_ignore in Hcg.
      destruct Hcg as (-> & res' & Hcg).
      admit.
    - cbn; inv_cg_ret Hcg; done.
    - cbn; inv_cg_ret Hcg; done.
    - cbn; inv_cg_ret Hcg; done.
    - cbn; inv_cg_ret Hcg; done.
  Admitted.

  Lemma wp_map_gc_ptrs_duproot ιs idxs wt wl res wt' wl' es_gcs:
    run_codegen (memory.map_gc_ptrs ιs idxs (memory.duproot mr)) wt wl = inr (res, wt', wl', es_gcs) ->
    res = () /\ wt' = [] /\ wl' = [].
  Proof.
    unfold memory.map_gc_ptrs, util.mapM_.
    intros Hcg.
    apply wp_ignore in Hcg.
    destruct Hcg as (-> & res' & Hcg).
    remember (zip ιs idxs) as ιidxs.
    revert Heqιidxs Hcg.
    revert ιs idxs wt wl res' wt' wl' es_gcs.
    induction ιidxs as [|[ι idx] ιidxs].
    - intros.
      apply wp_mapM_nil in Hcg.
      destruct Hcg as (-> & -> & -> & ->).
      done.
    - intros.
      destruct ιs as [|ι' ιs], idxs as [|idx' idxs]; inversion Heqιidxs.
      subst ι' idx'.
      apply wp_mapM_cons in Hcg.
      destruct Hcg as (res & ?wt & ?wl & ?es & ?res & ?wt & ?wl & ?es & Hdup & Hcg & Heqs).
      destruct Heqs as (-> & -> & -> & ->).
      eapply IHιidxs in Hcg; eauto.
      destruct Hcg as (_ & -> & ->).
      split; auto.
      apply wp_map_gc_ptr_duproot in Hdup.
      destruct Hdup as (-> & -> & ->).
      done.
  Qed.

  Fixpoint replace_base {n} (vh: valid_holed n) vs :=
    match vh with
    | VH_base n _ es => VH_base n vs es
    | VH_rec n b c d vh e => VH_rec b c d (replace_base vh vs) e
    end.

  Lemma lfilled_get_replace_base {n} (vh: valid_holed n) es vs1 vs2:
    get_base_l vh = vs1 ++ vs2 ->
    lh_depth (lh_of_vh vh) = n ->
    is_true (lfilled n (lh_of_vh (replace_base vh vs1))
               (seq.cat (v_to_e_list vs2) es) (vfill vh es)).
  Proof.
    induction vh => //=.
    - intros -> <-.
      unfold lfilled, lfill => //=.
      rewrite v_to_e_is_const_list /=.
      rewrite -v_to_e_cat.
      repeat rewrite cat_app.
      repeat rewrite app_assoc.
      done.
    - intros Hbase Hdepth.
      apply eq_add_S in Hdepth.
      specialize (IHvh Hbase Hdepth).
      unfold lfilled, lfill; fold lfill.
      rewrite v_to_e_is_const_list.
      unfold lfilled in IHvh.
      destruct (lfill _ _ _) => //.
      apply b2p in IHvh as <-.
      done.
  Qed.

  Lemma atoms_interp_take os vs count :
    atoms_interp os vs -∗
    atoms_interp (take count os) (take count vs) ∗
    atoms_interp (drop count os) (drop count vs).
  Proof.
    iIntros "Hatoms".
    iDestruct (big_sepL2_length with "Hatoms") as %Hlen.
    rewrite -{1}(take_drop count os) -{1}(take_drop count vs).
    iDestruct (big_sepL2_app_inv with "Hatoms") as "[Htake Hdrop]".
    { rewrite !length_take. lia. }
    iFrame.
  Qed.

  Lemma atoms_interp_take_drop os vs off count :
    atoms_interp os vs -∗
    atoms_interp (take count (drop off os)) (take count (drop off vs)).
  Proof.
    iIntros "Hatoms".
    iDestruct (atoms_interp_take with "Hatoms") as "[_ Hdrop]".
    by iDestruct (atoms_interp_take with "Hdrop") as "[Htake_drop _]".
  Qed.

  Lemma atoms_interp_app_split_l os1 os2 vs1 vs2 :
    length os1 = length vs1 ->
    atoms_interp (os1 ++ os2) (vs1 ++ vs2) -∗
    atoms_interp os1 vs1 ∗
    atoms_interp os2 vs2.
  Proof.
    iIntros (Hlen) "Hatoms".
    iDestruct (atoms_interp_take _ _ (length os1) with "Hatoms") as "[H1 H2]".
    rewrite !take_app_length !drop_app_length Hlen !take_app_length !drop_app_length.
    iFrame.
  Qed.

  Lemma atoms_interp_app_split_r os1 os2 vs1 vs2 :
    atoms_interp os1 vs1 -∗
    atoms_interp os2 vs2 -∗
    atoms_interp (os1 ++ os2) (vs1 ++ vs2).
  Proof.
    iIntros "H1 H2".
    iApply (big_sepL2_app with "H1 H2").
  Qed.

  Lemma atoms_interp_app_l os1 os2 vs :
    atoms_interp (os1 ++ os2) vs -∗
    ∃ vs1 vs2, ⌜vs = vs1 ++ vs2⌝ ∗ atoms_interp os1 vs1 ∗ atoms_interp os2 vs2.
  Proof.
    iIntros "Hos".
    iDestruct (atoms_interp_length with "Hos") as %Hlen.
    iDestruct (atoms_interp_take _ _ (length os1) with "Hos") as "[Hos1 Hos2]".
    iEval (rewrite take_app_length) in "Hos1".
    iEval (rewrite drop_app_length) in "Hos2".
    iExists (take (length os1) vs), (drop (length os1) vs).
    iSplit.
    - iPureIntro. rewrite take_drop. reflexivity.
    - iFrame.
  Qed.

  Lemma atoms_interp_app_r (os : list atom) (vs1 vs2 : list value) :
    atoms_interp os (vs1 ++ vs2) -∗
    ∃ os1 os2 : list atom, ⌜os = os1 ++ os2⌝ ∗ atoms_interp os1 vs1 ∗ atoms_interp os2 vs2.
  Proof.
    iIntros "Hos".
    iDestruct (atoms_interp_length with "Hos") as %Hlen.
    iDestruct (atoms_interp_take _ _ (length vs1) with "Hos") as "[Hos1 Hos2]".
    iEval (rewrite take_app_length) in "Hos1".
    iEval (rewrite drop_app_length) in "Hos2".
    iExists (take (length vs1) os), (drop (length vs1) os).
    iSplit.
    - iPureIntro. rewrite take_drop. reflexivity.
    - iFrame.
  Qed.

  Definition value_to_atom (v : value) : atom :=
    match v with
    | VAL_int32 n32 => I32A n32
    | VAL_int64 n64 => I64A n64
    | VAL_float32 f32 => F32A f32
    | VAL_float64 f64 => F64A f64
    end.

  Definition values_to_atoms (vs : list value) :=
    map value_to_atom vs.

  Lemma atom_interp_value_as_atom v :
    ⊢ atom_interp (value_to_atom v) v.
  Proof.
    destruct v; simpl; by iIntros.
  Qed.

  Lemma atoms_interp_values_as_atoms vs :
   ⊢ atoms_interp (values_to_atoms vs) vs.
  Proof.
    iInduction vs as [|v vs] "IH"; first by simpl.
    rewrite /values_to_atoms map_cons.
    rewrite atoms_interp_cons.
    iFrame "#".
    iApply atom_interp_value_as_atom.
  Qed.

  Lemma has_prim_has_arep η v :
    has_prim η v ->
    has_arep (prim_to_arep η) (value_to_atom v).
  Proof.
    intros Hprim.
    destruct v, η; simpl; done.
  Qed.

  Lemma has_prims_has_areps ηs vs :
    has_prims ηs vs ->
    has_areps (map prim_to_arep ηs) (SAtoms (values_to_atoms vs)).
  Proof.
    revert ηs.
    induction vs; intros ηs Hprims.
    - inversion Hprims; subst.
      simpl.
      eexists.
      by split.
    - destruct ηs as [| η ηs]; first inversion Hprims.
      simpl.
      apply has_areps_cons.
      apply Forall2_cons in Hprims as [Hprim Hprims].
      split; first by apply IHvs.
      by apply has_prim_has_arep.
  Qed.

  Lemma values_to_atoms_norefs vs :
    Forall (forall_ptr_atom norefs_ptr_interp) (values_to_atoms vs).
  Proof.
    induction vs as [|v vs]; simpl; first done.
    apply Forall_cons.
    split.
    - by destruct v.
    - apply IHvs.
  Qed.

  Lemma locals_interp_lookup se L oss i τ_old :
    L !! i = Some τ_old →
    locals_interp rti sr se L oss -∗
    ∃ oss_pre os_mid oss_post,
    ⌜oss = oss_pre ++ [os_mid] ++ oss_post⌝ ∗
    locals_interp rti sr se (take i L) oss_pre ∗
    value_interp rti sr se τ_old (SAtoms os_mid) ∗
    locals_interp rti sr se (drop (S i) L) oss_post.
  Proof.
    iIntros (Hlookup_L) "Hval".
    iDestruct (big_sepL2_length with "Hval") as %Hoss_len.
    have Hlookup_oss_i : ∃ os_mid, oss !! i = Some os_mid.
    {
      apply lookup_lt_is_Some_2.
      rewrite -Hoss_len.
      by eapply lookup_lt_Some.
    }
    destruct Hlookup_oss_i as [os_mid Hlookup_oss_i].
    iExists (take i oss), os_mid, (drop (S i) oss).
    iSplit.
    { iPureIntro. symmetry. apply take_drop_middle. exact Hlookup_oss_i. }
    (* unfold locals_interp. *)
    have Hsplit_L := take_drop_middle L i τ_old Hlookup_L.
    have Hsplit_oss := take_drop_middle oss i os_mid Hlookup_oss_i.
    rewrite <- Hsplit_L, <- Hsplit_oss.
    iDestruct (big_sepL2_app_inv with "Hval") as "[Hval_pre Hval_rest]".
    { left. rewrite !length_take. lia. }
    rewrite Hsplit_L Hsplit_oss.
    iDestruct "Hval_rest" as "[Hval_mid Hval_post]".
    unfold locals_interp.
    iFrame.
  Qed.

  Lemma locals_interp_length se L oss :
    locals_interp rti sr se L oss -∗ ⌜length L = length oss⌝.
  Proof.
    iIntros "Hval".
    unfold locals_interp.
    iDestruct (big_sepL2_length with "Hval") as %Hlen.
    iPureIntro. exact Hlen.
  Qed.

  Lemma frame_interp_update_frame se ηss L wl1 wl2 wl vs_idxs vs_wl fr fr' :
    vs_idxs = seq ((length $ concat ηss) + length wl1) (length wl) ->
    Forall2 (λ i v, f_locs fr' !! i = Some v) vs_idxs vs_wl ->
    result_type_interp wl vs_wl ->
    frame_rel (λ i, i ∉ vs_idxs) fr fr' ->
    frame_interp rti sr se ηss L (wl1 ++ wl ++ wl2) fr -∗
    frame_interp rti sr se ηss L (wl1 ++ wl ++ wl2) fr'.
  Proof.
    intros Hvs_idxs_wl Hnew_vals Hres Hfrel.
    iIntros "Hframe".
    iDestruct "Hframe" as
      "(%oss & %vss_L & %vs_WL_old & %Hfr & %Hprims & %Hresult & Hatom & Hval)".
    apply result_type_interp_split in Hresult.
    destruct Hresult as [vs_wl1 [vs_rest [-> [Hvs_wl1 Hresult]]]].
    apply result_type_interp_split in Hresult.
    destruct Hresult as [vs_wl' [vs_wl2 [-> [Hvs_wl' Hvs_wl2]]]].
    iFrame.
    iExists (vs_wl1 ++ vs_wl ++ vs_wl2).
    iPureIntro; split; last split.
    - rewrite app_assoc.
      eapply (frame_f_locs_update); [ | done | done | by rewrite -app_assoc].
      rewrite length_app.
      apply Forall2_length in Hvs_wl' as <-.
      apply Forall2_length in Hvs_wl1 as <-.
      apply Forall2_concat in Hprims.
      apply Forall2_length in Hprims as <-.
      done.
    - done.
    - apply result_type_interp_combine; first done.
      by apply result_type_interp_combine; last done.
  Qed.

  Lemma frame_interp_update_frame' se ηss L wl1 wl2 wl vs_localidxs vs_idxs vs_wl fr fr' :
    vs_idxs = seq ((length $ concat ηss) + length wl1) (length wl) ->
    vs_localidxs = map prelude.W.Mk_localidx vs_idxs ->
    Forall2 (λ i v, f_locs fr' !! localimm i = Some v) vs_localidxs vs_wl ->
    result_type_interp wl vs_wl ->
    frame_rel (λ i, i ∉ vs_idxs) fr fr' ->
    frame_interp rti sr se ηss L (wl1 ++ wl ++ wl2) fr -∗
    frame_interp rti sr se ηss L (wl1 ++ wl ++ wl2) fr'.
  Proof.
    iIntros (Hvs_idxs Hvs_localidxs HF Hres Hframe_rel) "Hfr".
    iApply frame_interp_update_frame; eauto.
    subst vs_localidxs.
    rewrite Forall2_fmap_l in HF.
    eapply Forall2_impl; [exact HF|].
    done.
  Qed.

  Lemma frame_interp_locals_ctx_length se ηss L WL fr :
    frame_interp rti sr se ηss L WL fr -∗ ⌜length ηss = length L⌝.
  Proof.
    iIntros "Hframe".
    iDestruct "Hframe" as (oss vss_L vs_WL Hf_locs Hhas_prims Hresult) "[Hatom Hval]".
    iDestruct (locals_interp_length with "Hval") as "->".
    iDestruct (big_sepL2_length with "Hatom") as "%Hoss_len".
    iPureIntro.
    apply Forall2_length in Hhas_prims as ->.
    done.
  Qed.

  Lemma frame_interp_update_frame_label se τ_old ηs L wl vs_l vs_idxs os fe fr fr' i τ :
    let L' := <[i:=τ]> L in
    L !! i = Some τ_old ->
    wl_interp (fe_wlocal_offset fe) wl fr ->
    fe_locals fe !! i = Some ηs ->
    vs_idxs = seq (sum_list_with length (take i (fe_locals fe))) (length ηs) ->
    has_prims ηs vs_l ->
    Forall2 (λ j v, f_locs fr' !! j = Some v) vs_idxs vs_l ->
    frame_rel (λ j, j ∉ vs_idxs) fr fr' ->
    atoms_interp os vs_l -∗
    value_interp rti sr se τ (SAtoms os) -∗
    frame_interp rti sr se (fe_locals fe) L wl fr -∗
    frame_interp rti sr se (fe_locals fe) L' wl fr'.
  Proof.
    intros L' Hlookup_L Hwl_interp Hlookup Hvs_idxs Hhas_prims_new Hf2 Hfrel.
    iIntros "Hatoms_new Hvalues Hframe".

    iDestruct (frame_interp_locals_ctx_length with "Hframe") as "%HL_len".

    iDestruct "Hframe" as
      "(%oss & %vss_L & %vs_WL & %Hfr & %Hhas_prims & %Hresult & Hatoms & Hval)".
    iFrame (Hresult).

    have Hsplit := take_drop_middle (fe_locals fe) i ηs Hlookup.
    rewrite <- Hsplit in Hhas_prims.
    apply List.Forall2_app_inv_l in Hhas_prims as (vss_L_pre & vss_L_rest & Hpre & Hrest & ->).
    destruct vss_L_rest as [| vs_mid vss_L_post]; [inversion Hrest |].
    apply Forall2_cons_1 in Hrest as [Hmid Hpost].

    iDestruct (locals_interp_lookup _ _ _ _ _ Hlookup_L with "Hval") as (oss_pre os_mid oss_post Hoss_eq) "[Hval_pre [_ Hval_post]]".

    iEval (rewrite Hoss_eq) in "Hatoms".
    iDestruct (locals_interp_length with "Hval_pre") as %Hlen_pre.
    iDestruct (locals_interp_length with "Hval_post") as %Hlen_post.
    apply Forall2_length in Hpre as Hvs_pre_len.
    apply Forall2_length in Hmid as Hvs_mid_len.
    apply Forall2_length in Hpost as Hvs_post_len.

    have Hlen_oss_pre : length oss_pre = length vss_L_pre.
    { rewrite <- Hlen_pre, length_take, <- Hvs_pre_len, length_take. lia. }
    have Hlen_oss_post : length oss_post = length vss_L_post.
    { rewrite <- Hlen_post, length_drop, <- Hvs_post_len, length_drop. lia. }

    iDestruct (big_sepL2_app_inv _ _ _ _ _ with "Hatoms") as "[Hatoms_pre Hatoms_rest]"; first by left.
    (* NOTE: the atoms_interp for the middle is being thrown away, since the values are being overwritten *)
    iDestruct (big_sepL2_cons with "Hatoms_rest") as "[_ Hatoms_post]".

    iExists (oss_pre ++ [os] ++ oss_post), (vss_L_pre ++ [vs_l] ++ vss_L_post).
    iSplit.
    {
      iPureIntro.
      rewrite !concat_app.
      rewrite concat_app concat_cons in Hfr.
      rewrite -!app_assoc.
      rewrite -!app_assoc in Hfr.
      clear_nils.
      eapply frame_f_locs_update.
      4: apply Hfr.
      3: done.
      2: done.
      subst vs_idxs.
      f_equal; last done.
      rewrite -sum_list_with_length_concat.
      eapply Forall2_sum_list_with_length.
      eapply Forall2_impl; [exact Hpre |].
      intros ηs' vs' Hprims'.
      apply Forall2_length in Hprims'.
      done.
    }
    iSplit.
    {
      iPureIntro.
      rewrite <- (take_drop_middle (fe_locals fe) i ηs Hlookup).
      apply Forall2_app; [exact Hpre |].
      apply Forall2_cons; by split.
    }
    iSplitL "Hatoms_new Hatoms_pre Hatoms_post".
    - by iFrame.
    - unfold locals_interp, L'.
      rewrite insert_take_drop.
      2: { eapply lookup_lt_Some. exact Hlookup_L. }
      iApply (big_sepL2_app with "Hval_pre").
      iApply big_sepL2_cons.
      iFrame.
  Qed.

  Lemma frame_interp_update_frame_label' se τ_old ηs L wl vs_l vs_idxs vs_localidxs os fe fr fr' i τ :
    let L' := <[i:=τ]> L in
    L !! i = Some τ_old ->
    wl_interp (fe_wlocal_offset fe) wl fr ->
    fe_locals fe !! i = Some ηs ->
    vs_idxs = seq (sum_list_with length (take i (fe_locals fe))) (length ηs) ->
    vs_localidxs = map prelude.W.Mk_localidx vs_idxs ->
    has_prims ηs vs_l ->
    Forall2 (λ j v, f_locs fr' !! localimm j = Some v) vs_localidxs vs_l ->
    frame_rel (λ j, j ∉ vs_idxs) fr fr' ->
    atoms_interp os vs_l -∗
    value_interp rti sr se τ (SAtoms os) -∗
    frame_interp rti sr se (fe_locals fe) L wl fr -∗
    frame_interp rti sr se (fe_locals fe) L' wl fr'.
  Proof.
    intros L' HlookupL Hwl_interp Hlookup Hvs_idxs Hvs_localidxs Hhas_prims_new Hf2 Hfrel.
    iIntros "Hatoms Hvalues Hframe".
    iApply (frame_interp_update_frame_label with "[$] [$] [$]" ); eauto.
    subst vs_localidxs.
    rewrite Forall2_fmap_l in Hf2.
    eapply Forall2_impl; [exact Hf2|].
    done.
  Qed.

  Lemma fe_wlocal_offset_length F :
    fe_wlocal_offset (fe_of_context F) = length $ concat (typing.fc_locals F).
  Proof.
    unfold fe_wlocal_offset. simpl.
    apply sum_list_with_length_concat.
  Qed.

  Lemma atom_interp_value_type_interp (ι : atomic_rep) (o : atom) (v : value) :
    has_arep ι o →
    atom_interp o v -∗
    ⌜value_type_interp (translate_arep ι) v⌝.
  Proof.
    intros Harep.
    destruct ι, o; simpl in *; try done.
    {
      iIntros "(%n & %n32 & %Hrep & -> & _)".
      iExists _; eauto.
    }
    all: iIntros "->"; iPureIntro; exists n; done.
  Qed.

  Lemma result_type_interp_of_atoms_interp ιs os vs :
    has_areps ιs (SAtoms os) ->
    atoms_interp os vs -∗
    ⌜result_type_interp (map translate_arep ιs) vs⌝.
  Proof.
    revert os vs.
    induction ιs as [| ι ιs' IH]; intros os vs Hιs'.
    - (* ιs = [] *)
      destruct Hιs' as (os' & Heq & Hfa).
      inversion Heq; subst.
      inversion Hfa; subst.
      iIntros "Hinterp".
      iDestruct (atoms_interp_nil_l with "Hinterp") as "->".
      iPureIntro.
      constructor.
    - (* ιs = ι :: ιs' *)
      destruct os as [| o os].
      {
        destruct Hιs' as (os' & Heq & Hfa).
        inversion Heq; subst.
        inversion Hfa.
      }
      apply has_areps_cons in Hιs' as [Hιs'_tl Hιs'_hd].
      iIntros "Hinterp".
      iDestruct (atoms_interp_cons_l with "Hinterp") as
      "(%v & %vs' & -> & Hv & Hos)".
      iDestruct (IH _ _ Hιs'_tl with "Hos") as "%Htl".
      iDestruct (atom_interp_value_type_interp ι o v Hιs'_hd with "Hv") as "%Hhd".
      iPureIntro.
      simpl.
      by constructor.
  Qed.


  Lemma value_type_interp_of_default ty :
    value_type_interp ty (default_of_value_type ty).
  Proof. destruct ty; by eexists. Qed.

  Lemma result_type_interp_of_defaults tys :
    result_type_interp tys (default_of_value_types tys).
  Proof.
    induction tys as [| ty tys IH].
    - constructor.
    - constructor; last done.
      apply value_type_interp_of_default.
  Qed.

  Lemma empty_closure_interp se ϕ cl :
    closure_interp rti sr ϕ senv_empty cl -∗
    closure_interp rti sr ϕ se cl.
  Proof.
    (* This seems true? *)
    iIntros "H".
    cbn.
  Admitted.

  Definition expect_heap_ptr (o : atom) : option (base_memory * location) :=
    match o with
    | PtrA (PtrHeap μ ℓ) => Some (μ, ℓ)
    | _ => None
    end.

  Lemma atom_interp_dup o v :
    expect_heap_ptr o = None ->
    Persistent (atom_interp o v).
  Proof.
    destruct o; cbn; intros Heq; try apply bi.pure_persistent.
    repeat (apply bi.pure_persistent
    || (apply bi.exist_persistent; intros ?x)
    || apply bi.sep_persistent).
    destruct p; try congruence.
    destruct x1; cbn;
    repeat (apply bi.pure_persistent
    || (apply bi.exist_persistent; intros ?x)
    || apply bi.sep_persistent).
  Qed.

  Lemma atoms_interp_dup os vs :
    Forall (λ o, expect_heap_ptr o = None) os ->
    Persistent (atoms_interp os vs).
  Proof.
    intros Hall.
    unfold atoms_interp.
    apply big_sepL2_persistent.
    intros k o v Hok Hvk.
    apply atom_interp_dup.
    rewrite Forall_lookup in Hall.
    exact (Hall k o Hok).
  Qed.

  Global Instance atom_interp_value_to_atom_persistent v :
    Persistent (atom_interp (value_to_atom v) v).
  Proof.
    unfold Persistent.
    iIntros "H !>".
    iApply atom_interp_value_as_atom.
  Qed.

  Global Instance atoms_interp_values_to_atoms_persistent vs :
    Persistent (atoms_interp (values_to_atoms vs) vs).
  Proof.
    unfold Persistent.
    iIntros "H !>".
    iApply atoms_interp_values_as_atoms.
  Qed.

  Lemma atoms_interp_norefs_persistent (se: semantic_env (Σ:=Σ)) os vs :
    ref_flag_atoms_interp NoRefs (SAtoms os) ->
    Persistent (atoms_interp os vs).
  Proof.
    intros Href.
    unfold ref_flag_atoms_interp, forall_satoms in Href.
    apply atoms_interp_dup.
    rewrite Forall_lookup. intros k o Hok.
    rewrite Forall_lookup in Href.
    specialize (Href k o Hok).
    destruct o; simpl in *; try done.
    destruct p; simpl in *; done.
  Qed.

  Lemma skind_rec_interp_unfold sκ T (se: semantic_env (Σ:=Σ)) sv :
    skind_rec_interp sκ T se sv ≡ (▷ T (senv_insert_type sκ (skind_rec_interp sκ T se) se) sv)%I.
  Proof.
    simpl.
    set f := (λ T0 : leibnizO semantic_value -n> iPropO Σ, λne sv0 : leibnizO semantic_value, (▷ T (se.1, (sκ, T0) :: se.2) sv0)%I).
     etransitivity.
     - exact (fixpoint_unfold f sv).
     - simpl. reflexivity.
  Qed.

  Lemma rec_interp_unfold κ T (se: semantic_env (Σ:=Σ)) sv :
    rec_interp κ T se sv ≡
    match eval_kind_se se κ with
    | Some sκ => ▷ T (senv_insert_type sκ (skind_rec_interp sκ T se) se) sv
    | None => False
    end%I.
  Proof.
    unfold rec_interp. simpl.
    destruct (eval_kind se κ) as [sκ|]; simpl.
    - set f := (λ T0 : leibnizO semantic_value -n> iPropO Σ,
      λne sv0 : leibnizO semantic_value,
      (▷ T (se.1, (sκ, T0) :: se.2) sv0)%I).
      etransitivity.
      + exact (fixpoint_unfold f sv).
      + simpl. reflexivity.
    - reflexivity.
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

  Lemma value_interp_type_plug se vs ηs :
    ⌜has_prims ηs vs⌝ -∗
    value_interp rti sr se (type_plug_prim ηs) (SAtoms (values_to_atoms vs)).
  Proof.
    iIntros "%Hprims".
    rewrite value_interp_eq /add_skind_interp.
    unfold type_plug_prim, type_plug. simpl.
    set ρ := ProdR (map (AtomR ∘ prim_to_arep) ηs).
    have Heval : eval_rep se ρ = Some (map prim_to_arep ηs).
    { apply eval_rep_prod_atoms. }
    iExists (SVALTYPE (map prim_to_arep ηs) NoRefs).
    iSplit.
    - iPureIntro. unfold type_skind. simpl.
      have Heval_kind := eval_kind_of_eval_rep se ρ _ Heval NoRefs.
      rewrite -Heval_kind.
      done.
    - apply has_prims_has_areps in Hprims as Hareps.
      iSplit.
      + iPureIntro. simpl.
        split; first done.
        apply values_to_atoms_norefs.
      + iExists (map prim_to_arep ηs).
        iSplit; [iPureIntro; exact Heval |].
        done.
  Qed.

  Lemma type_interp_skind_svalue (τ : type) se sv :
    type_interp rti sr τ se sv -∗ ∃ sκ, ⌜type_skind se τ = Some sκ⌝ ∗ ⌜skind_has_svalue sκ sv⌝.
  Proof.
    iIntros "H".
    rewrite type_interp_eq.
    iDestruct "H" as (sκ) "[%Hsk [%Hsv _]]".
    iExists sκ. by iSplit; iPureIntro.
  Qed.

  (* TODO: might need to change. @Elan *)
  Lemma fold_type_interp_subst (se : semantic_env (Σ:=Σ)) (τ : type) (κ : kind) sκ sv :
    eval_kind se κ = Some sκ →
    type_interp rti sr (subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ) se sv ⊣⊢
    type_interp rti sr τ (senv_insert_type sκ (skind_rec_interp sκ (type_interp rti sr τ) se) se) sv.
  Proof. Admitted.

  Lemma fold_type_interp (se : semantic_env (Σ:=Σ)) (τ : type) (κ : kind) sκ sv :
    eval_kind se κ = Some sκ →
    type_interp rti sr (RecT κ τ) se sv ⊣⊢
    ⌜skind_has_svalue sκ sv⌝ ∗
    ▷ type_interp rti sr (subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ) se sv.
  Proof.
    intros Hκ.
    iSplit.
    - iIntros "H".
      iEval (rewrite type_interp_eq) in "H".
      iDestruct "H" as "(%sκ' & %Hκ' & %Hsv & Hrec)".
      unfold type_skind in Hκ'. simpl in Hκ'.
      rewrite Hκ in Hκ'. simplify_eq.
      iSplit; first done.
      iEval (cbn [pre_type_interp]) in "Hrec".
      iEval (rewrite (rec_interp_unfold κ (type_interp rti sr τ) se sv)) in "Hrec".
      replace (eval_kind_se se κ) with (eval_kind se κ); last done.
      iEval (rewrite Hκ) in "Hrec".
      iEval (rewrite <- (fold_type_interp_subst se τ κ sκ' sv Hκ)) in "Hrec".
      iExact "Hrec".
    - iIntros "[%Hsv Hτrec]".
      iEval (rewrite type_interp_eq).
      iExists sκ.
      iSplit. { iPureIntro. unfold type_skind. simpl. by rewrite Hκ. }
      iSplit. { iPureIntro. exact Hsv. }
      iEval (cbn [pre_type_interp]).
      iEval (rewrite (rec_interp_unfold κ (type_interp rti sr τ) se sv)).
      replace (eval_kind_se se κ) with (eval_kind se κ); last done.
      iEval (rewrite Hκ).
      iEval (rewrite (fold_type_interp_subst se τ κ sκ sv Hκ)) in "Hτrec".
      iExact "Hτrec".
  Qed.

End common.
