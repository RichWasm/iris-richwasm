Require Import RichWasm.iris.logrel.logrel_properties.
Require Import RichWasm.iris.wp_codegen.
Require Import RichWasm.iris.logrel.logrel_properties.
Require Import RichWasm.iris.logrel.env_props.
Require Import RichWasm.iris.logrel.type_eq.
Require Import RichWasm.kinding_subst.
Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section substitution.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  (** STARTING FROM HERE, we begin to have these assumptions about how substitutions and semantic envs
      relate to one another. These relations are strong enough to prove the necessary subsitution
      lemmas, and weak enough to be proven about the outermost substitution we're working on. *)

  Definition sem_env_types_well_formed (se : @semantic_env Σ) :=
    Forall (fun '(sκ, (sκ_T, T)) => subskind_of sκ_T sκ /\ skind_has_stype sκ_T T) (senv_types se).

  Definition sem_env_rel_rep_eq (se' : @semantic_env Σ) (se : @semantic_env Σ) (sub_r:nat → representation) :=
    (forall i, lookup_rep se' i = eval_rep se (sub_r i)).
  Definition sem_env_rel_size_eq (se' : @semantic_env Σ) (se : @semantic_env Σ) (sub_s:nat → Core.size) :=
    (forall i, lookup_size se' i = eval_size se (sub_s i)).
  Definition sem_env_rel_mem_eq (se' : @semantic_env Σ) (se : @semantic_env Σ) (sub_m:nat → Core.memory) :=
    (forall i, lookup_mem se' i = eval_mem se (sub_m i)).
  Definition subskind_of_option (sk: option skind) (sk': option skind) :=
    match sk, sk' with
    | Some sk, Some sk' => subskind_of sk sk'
    | None, None => True
    | _, _ => False
    end.
  Lemma subskind_of_option_refl sk :
    subskind_of_option sk sk.
  Proof.
    destruct sk; cbn; try done.
    apply subskind_of_refl.
  Qed.
  Lemma subskind_of_option_invl sk osk' :
    subskind_of_option (Some sk) osk' ->
    ∃ sk', osk' = Some sk' /\ subskind_of sk sk'.
  Proof.
    intros; destruct osk'; cbn; try done.
    cbn in H.
    eexists; done.
  Qed.

  Lemma subskind_of_option_invr osk sk' :
    subskind_of_option osk (Some sk') ->
    ∃ sk, osk = Some sk /\ subskind_of sk sk'.
  Proof.
    intros; destruct osk; cbn; try done.
    cbn in H.
    eexists; done.
  Qed.

  (* TODO at one point make subskind_of_option an inductive. not that important *)


  Definition sem_env_rel_sκ_eq (se' : @semantic_env Σ) (se : @semantic_env Σ) (sub_t:nat → type) :=
    (forall i, subskind_of_option (type_skind se (sub_t i)) (fst <$> lookup_type se' i)).
  Definition sem_env_rel_type_eq (se' : @semantic_env Σ) (se : @semantic_env Σ) (sub_t:nat → type) :=
    (forall i, default (λne _, False%I) (snd <$> (snd <$> lookup_type se' i)) ≡
                  (value_interp rti sr se (sub_t i))).
  Definition sub_t_well_formed F (sub_t : nat → type) :=
    (∀ i, refresh_kinds F (sub_t i) = sub_t i).

  Ltac unfold_sem_rels :=
    unfold
    sem_env_rel_rep_eq, sem_env_rel_size_eq,
      sem_env_rel_mem_eq, sem_env_types_well_formed, sub_t_well_formed,
      sem_env_rel_type_eq, sem_env_rel_sκ_eq in *.

  Lemma sem_well_formed_from_interp F se :
    sem_env_interp F se ->
    sem_env_types_well_formed se.
  Proof.
    intros.
    destruct H as [_ H].
    unfold sem_env_types_well_formed.
    unfold type_ctx_interp in H.

    generalize dependent (fc_type_vars F).
    generalize dependent (senv_types se).
    induction o.
    - intros.
      by apply Forall_nil.
    - intros.
      rename l into Fl.
      destruct a as [sκ [sκ_T T]].
      rename o into se_rest.
      destruct Fl as [|f Fl]; [apply Forall2_nil_cons_inv in H; done|].
      apply Forall2_cons in H as [[_ Imp] Rest].
      apply IHo in Rest.
      apply Forall_cons; done.
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
      assert (H': mapM (eval_rep se') ρs = mapM (eval_rep se) (map (subst_representation sub_r) ρs))
        by (by apply Forall_mapM_map_ext).
      by rewrite H'.
    - cbn.
      assert (H': mapM (eval_rep se') ρs = mapM (eval_rep se) (map (subst_representation sub_r) ρs))
        by (by apply Forall_mapM_map_ext).
      by rewrite H'.
    - cbn in *; done.
  Qed.

  Lemma eval_size_subst_senv_eq (se se' : semantic_env (Σ:=Σ)) sub_r sub_s σ :
    sem_env_rel_rep_eq se' se sub_r ->
    sem_env_rel_size_eq se' se sub_s ->
    eval_size se' σ =
    eval_size se (subst_size sub_r sub_s σ).
  Proof.
    intros Hsub_r Hsub_s; unfold_sem_rels.
    induction σ using size_ind.
    - cbn in *. apply Hsub_s.
    - cbn in *.
      assert (H': mapM (eval_size se') σs = mapM (eval_size se) (map (subst_size sub_r sub_s) σs))
        by (by apply Forall_mapM_map_ext).
      by rewrite H'.
    - cbn in *.
      assert (H': mapM (eval_size se') σs = mapM (eval_size se) (map (subst_size sub_r sub_s) σs))
        by (by apply Forall_mapM_map_ext).
      by rewrite H'.
    - cbn.
      by rewrite <- (eval_rep_subst_senv_eq _ _ _ _ Hsub_r).
    - by cbn.
  Qed.

  Lemma eval_mem_subst_senv_eq (se se' : semantic_env (Σ:=Σ)) sub_m m :
    sem_env_rel_mem_eq se' se sub_m ->
    eval_mem se' m =
    eval_mem se (subst_memory sub_m m).
  Proof.
    intros Hsub_m. unfold_sem_rels.

    induction m as [i | b].
    - cbn.
      by apply Hsub_m.
    - by cbn.

  Qed.

  Lemma eval_kind_subst_senv_eq (se se' : semantic_env (Σ:=Σ)) sub_r sub_s κ :
    sem_env_rel_rep_eq se' se sub_r ->
    sem_env_rel_size_eq se' se sub_s ->
    eval_kind se' κ =
    eval_kind se (subst_kind sub_r sub_s κ) .
  Proof.
    intros Hsub_r Hsub_s; unfold_sem_rels.
    induction κ as [ρ ξ | σ ξ].
    - cbn.
      by rewrite <- (eval_rep_subst_senv_eq _ _ _ _ Hsub_r).
    - cbn.
      by rewrite <- (eval_size_subst_senv_eq _ _ _ _ _ Hsub_r Hsub_s).
  Qed.

  Record sem_env_ren (ξm ξr ξs ξt : nat → nat) (se se' : semantic_env (Σ:=Σ)) : Prop :=
    { sem_env_ren_mem : ∀ i, lookup_mem se i = lookup_mem se' (ξm i);
      sem_env_ren_rep : ∀ i, lookup_rep se i = lookup_rep se' (ξr i);
      sem_env_ren_size : ∀ i, lookup_size se i = lookup_size se' (ξs i);
      sem_env_ren_type : ∀ i, lookup_type se i ≡ lookup_type se' (ξt i) }.

  Lemma sem_env_ren_insert_mem ξm ξr ξs ξt se se' μ :
    sem_env_ren ξm ξr ξs ξt se se' →
    sem_env_ren (unscoped.up_ren ξm) ξr ξs ξt (senv_insert_mem μ se) (senv_insert_mem μ se').
  Proof.
    intros [Hm Hr Hs Ht]; split; intros i; [destruct i|..]; cbn in *; auto.
  Qed.

  Lemma sem_env_ren_insert_rep ξm ξr ξs ξt se se' ιs :
    sem_env_ren ξm ξr ξs ξt se se' →
    sem_env_ren ξm (unscoped.up_ren ξr) ξs ξt (senv_insert_rep ιs se) (senv_insert_rep ιs se').
  Proof.
    intros [Hm Hr Hs Ht]; split; intros i; [|destruct i|..]; cbn in *; auto.
  Qed.

  Lemma sem_env_ren_insert_size ξm ξr ξs ξt se se' n :
    sem_env_ren ξm ξr ξs ξt se se' →
    sem_env_ren ξm ξr (unscoped.up_ren ξs) ξt (senv_insert_size n se) (senv_insert_size n se').
  Proof.
    intros [Hm Hr Hs Ht]; split; intros i; [| |destruct i|]; cbn in *; auto.
  Qed.

  Lemma sem_env_ren_insert_type ξm ξr ξs ξt se se' sκ sκ_T T :
    sem_env_ren ξm ξr ξs ξt se se' →
    sem_env_ren ξm ξr ξs (unscoped.up_ren ξt) (senv_insert_type sκ sκ_T T se) (senv_insert_type sκ sκ_T T se').
  Proof.
    intros [Hm Hr Hs Ht]; split; intros i; [| | |destruct i]; cbn in *; auto.
  Qed.

  Lemma eval_mem_ren ξm ξr ξs ξt se se' μ :
    sem_env_ren ξm ξr ξs ξt se se' →
    eval_mem se μ = eval_mem se' (ren_memory ξm μ).
  Proof.
    intros HR; destruct μ; cbn; [apply HR|done].
  Qed.

  Lemma eval_rep_ren ξm ξr ξs ξt se se' ρ :
    sem_env_ren ξm ξr ξs ξt se se' →
    eval_rep se ρ = eval_rep se' (ren_representation ξr ρ).
  Proof.
    intros HR; rewrite rinstInst'_representation.
    apply eval_rep_subst_senv_eq; intros i; cbn; apply HR.
  Qed.

  Lemma eval_size_ren ξm ξr ξs ξt se se' σ :
    sem_env_ren ξm ξr ξs ξt se se' →
    eval_size se σ = eval_size se' (ren_size ξr ξs σ).
  Proof.
    intros HR; rewrite rinstInst'_size.
    apply eval_size_subst_senv_eq; intros i; cbn; apply HR.
  Qed.

  Lemma eval_kind_ren ξm ξr ξs ξt se se' κ :
    sem_env_ren ξm ξr ξs ξt se se' →
    eval_kind se κ = eval_kind se' (ren_kind ξr ξs κ).
  Proof.
    intros HR; rewrite rinstInst'_kind.
    apply eval_kind_subst_senv_eq; intros i; cbn; apply HR.
  Qed.

  Lemma sum_offset_ren ξm ξr ξs ξt se se' ρs i :
    sem_env_ren ξm ξr ξs ξt se se' →
    sum_offset se ρs i = sum_offset se' (map (ren_representation ξr) ρs) i.
  Proof.
    intros HR; unfold sum_offset.
    rewrite firstn_map.
    f_equal.
    apply Forall_mapM_map_ext, Forall_forall; intros ρ _.
    by eapply eval_rep_ren.
  Qed.

  Lemma type_entry_equiv_skind
    (o o' : optionO (prodO (leibnizO skind) (prodO (leibnizO skind) (leibnizO semantic_value -n> iPropO Σ)))) :
    o ≡ o' → fst <$> o = fst <$> o'.
  Proof.
    intros H; inversion H as [u v Huv|]; subst; cbn; [f_equal|done].
    by destruct Huv as [Hfst _].
  Qed.

  Lemma type_skind_ren ξm ξr ξs ξt se se' τ :
    sem_env_ren ξm ξr ξs ξt se se' →
    type_skind se τ = type_skind se' (ren_type ξm ξr ξs ξt τ).
  Proof.
    intros HR; destruct τ; cbn; try by eapply eval_kind_ren.
    apply type_entry_equiv_skind, (sem_env_ren_type _ _ _ _ _ _ HR).
  Qed.

  Lemma translate_type_ren ξm ξr ξs ξt se se' τ :
    sem_env_ren ξm ξr ξs ξt se se' →
    translate_type se τ = translate_type se' (ren_type ξm ξr ξs ξt τ).
  Proof.
    intros HR; cbn -[type_skind].
    by rewrite (type_skind_ren _ _ _ _ _ _ τ HR).
  Qed.

  Lemma translate_types_ren ξm ξr ξs ξt se se' τs :
    sem_env_ren ξm ξr ξs ξt se se' →
    translate_types se τs = translate_types se' (map (ren_type ξm ξr ξs ξt) τs).
  Proof.
    intros HR; cbn -[translate_type].
    f_equal.
    apply Forall_mapM_map_ext, Forall_forall; intros τ _.
    by apply translate_type_ren.
  Qed.

  Lemma type_var_interp_ren ξm ξr ξs ξt se se' x :
    sem_env_ren ξm ξr ξs ξt se se' →
    type_var_interp x se ≡ type_var_interp (ξt x) se'.
  Proof.
    intros HR; pose proof (sem_env_ren_type _ _ _ _ _ _ HR x) as Ht.
    intros sv; cbn -[lookup_type]; revert Ht.
    generalize (lookup_type se x), (lookup_type se' (ξt x)); intros o o' Ht.
    inversion Ht as [u v Huv|]; subst; cbn; [|done].
    destruct Huv as [_ [_ HT]]; apply HT.
  Qed.

  Lemma lookup_interp_ren (Ts Ts' : list semantic_type) (se se' : semantic_env (Σ:=Σ)) (i : nat) (sv : semantic_value) :
    Forall2 (λ T T' : semantic_type, T se ≡ T' se') Ts Ts' →
    (match list_lookup i Ts as o return (o = list_lookup i Ts → iPropI Σ) with
     | Some T => λ _, T se sv
     | None => λ _, False%I
     end eq_refl) ⊣⊢
    (match list_lookup i Ts' as o return (o = list_lookup i Ts' → iPropI Σ) with
     | Some T => λ _, T se' sv
     | None => λ _, False%I
     end eq_refl).
  Proof.
    intros HF; revert i.
    induction HF as [|T T' Ts Ts' HT _ IH]; intros [|i]; cbn; [done|done|apply HT|apply IH].
  Qed.

  Lemma big_sepL2_interp_ren {B} (Ts Ts' : list (semantic_type (Σ:=Σ))) (l : list B) (g : B → semantic_value)
    (se se' : semantic_env (Σ:=Σ)) :
    Forall2 (λ T T' : semantic_type, T se ≡ T' se') Ts Ts' →
    ([∗ list] (T : semantic_type);b ∈ Ts;l, T se (g b)) ⊣⊢
    ([∗ list] (T : semantic_type);b ∈ Ts';l, T se' (g b)).
  Proof.
    intros HF; revert l.
    induction HF as [|T T' Ts Ts' HT _ IH]; intros [|b l]; cbn; [done..|].
    f_equiv; [apply HT|apply IH].
  Qed.

  Lemma type_interp_ext τ τ' se se' :
    type_skind se τ = type_skind se' τ' →
    pre_type_interp rti sr τ se ≡ pre_type_interp rti sr τ' se' →
    type_interp rti sr τ se ≡ type_interp rti sr τ' se'.
  Proof.
    intros Hsk HT sv.
    rewrite !type_interp_eq; cbn -[type_skind pre_type_interp skind_has_svalue].
    rewrite Hsk.
    f_equiv; intros sκ.
    repeat (f_equiv; try done).
  Qed.

  Lemma sum_interp_ren ξm ξr ξs ξt se se' κ Ts Ts' :
    sem_env_ren ξm ξr ξs ξt se se' →
    Forall2 (λ T T' : semantic_type, T se ≡ T' se') Ts Ts' →
    sum_interp κ Ts se ≡ sum_interp (ren_kind ξr ξs κ) Ts' se'.
  Proof.
    intros HR HF.
    destruct κ as [[|ρs|ρs|ι] ξ|σ ξ]; try done.
    intros sv; cbn.
    do 4 (f_equiv; intros ?).
    rewrite (sum_offset_ren _ _ _ _ _ _ ρs _ HR).
    rewrite map_fmap list_lookup_fmap.
    destruct (ρs !! _) as [ρ|]; cbn; [rewrite (eval_rep_ren _ _ _ _ _ _ ρ HR)|].
    all: repeat (f_equiv; try done).
    all: apply lookup_interp_ren, HF.
  Qed.

  Lemma variant_interp_ren Ts Ts' (se se' : semantic_env (Σ:=Σ)) :
    Forall2 (λ T T' : semantic_type, T se ≡ T' se') Ts Ts' →
    variant_interp Ts se ≡ variant_interp Ts' se'.
  Proof.
    intros HF sv; cbn.
    do 4 (f_equiv; intros ?).
    repeat (f_equiv; try done).
    apply lookup_interp_ren, HF.
  Qed.

  Lemma prod_interp_ren Ts Ts' (se se' : semantic_env (Σ:=Σ)) :
    Forall2 (λ T T' : semantic_type, T se ≡ T' se') Ts Ts' →
    prod_interp Ts se ≡ prod_interp Ts' se'.
  Proof.
    intros HF sv; cbn.
    f_equiv; intros oss.
    f_equiv.
    apply (big_sepL2_interp_ren _ _ _ SAtoms), HF.
  Qed.

  Lemma struct_interp_ren Ts Ts' (se se' : semantic_env (Σ:=Σ)) :
    Forall2 (λ T T' : semantic_type, T se ≡ T' se') Ts Ts' →
    struct_interp Ts se ≡ struct_interp Ts' se'.
  Proof.
    intros HF sv; cbn.
    f_equiv; intros wss.
    f_equiv.
    rewrite (big_sepL2_flip (λ _ (T : semantic_type) ws,T se (SWords ws)) Ts wss).
    rewrite (big_sepL2_flip (λ _ (T : semantic_type) ws,T se' (SWords ws)) Ts' wss).
    apply (big_sepL2_interp_ren _ _ _ SWords), HF.
  Qed.

  Lemma ref_interp_ren ξm ξr ξs ξt se se' μ β (T T' : semantic_type) :
    sem_env_ren ξm ξr ξs ξt se se' →
    T se ≡ T' se' →
    ref_interp μ β T se ≡ ref_interp (ren_memory ξm μ) β T' se'.
  Proof.
    intros HR HT.
    cbn -[ref_mm_mut_interp ref_mm_imm_interp ref_gc_mut_interp ref_gc_imm_interp].
    rewrite <- (eval_mem_ren _ _ _ _ _ _ μ HR).
    destruct (eval_mem se μ) as [[|]|], β; try done.
    all: intros sv; cbn.
    all: do 2 (f_equiv; intros ?).
    all: repeat (f_equiv; try (intros ?); try done).
  Qed.

  Lemma coderef_interp_ren (FT FT' : semantic_env -n> ClR) (se se' : semantic_env (Σ:=Σ)) :
    FT se ≡ FT' se' →
    coderef_interp sr FT se ≡ coderef_interp sr FT' se'.
  Proof.
    intros H sv; cbn.
    do 4 (f_equiv; intros ?).
    repeat (f_equiv; try done).
  Qed.

  Lemma ser_interp_ren (T T' : semantic_type) (se se' : semantic_env (Σ:=Σ)) :
    T se ≡ T' se' →
    ser_interp T se ≡ ser_interp T' se'.
  Proof.
    intros HT sv; cbn.
    f_equiv; intros os.
    repeat (f_equiv; try done).
  Qed.

  Lemma rec_interp_ren ξm ξr ξs ξt se se' κ (T T' : semantic_type) :
    sem_env_ren ξm ξr ξs ξt se se' →
    (∀ sκ sκ_T X, T (senv_insert_type sκ sκ_T X se) ≡ T' (senv_insert_type sκ sκ_T X se')) →
    rec_interp κ T se ≡ rec_interp (ren_kind ξr ξs κ) T' se'.
  Proof.
    intros HR HT.
    cbn -[skind_rec_interp].
    rewrite <- (eval_kind_ren _ _ _ _ _ _ κ HR).
    destruct (eval_kind se κ) as [sκ|]; [|done].
    cbn -[fixpoint skind_rec_interp1].
    apply fixpoint_proper; intros X sv.
    cbn -[senv_insert_type add_skind_interp_closed].
    f_equiv.
    apply HT.
  Qed.

  Lemma exists_mem_interp_ren (T T' : semantic_type) (se se' : semantic_env (Σ:=Σ)) :
    (∀ μ, T (senv_insert_mem μ se) ≡ T' (senv_insert_mem μ se')) →
    exists_mem_interp T se ≡ exists_mem_interp T' se'.
  Proof.
    intros HT sv; cbn -[senv_insert_mem].
    f_equiv; intros μ.
    apply HT.
  Qed.

  Lemma exists_rep_interp_ren (T T' : semantic_type) (se se' : semantic_env (Σ:=Σ)) :
    (∀ ιs, T (senv_insert_rep ιs se) ≡ T' (senv_insert_rep ιs se')) →
    exists_rep_interp T se ≡ exists_rep_interp T' se'.
  Proof.
    intros HT sv; cbn -[senv_insert_rep].
    f_equiv; intros ιs.
    apply HT.
  Qed.

  Lemma exists_size_interp_ren (T T' : semantic_type) (se se' : semantic_env (Σ:=Σ)) :
    (∀ n, T (senv_insert_size n se) ≡ T' (senv_insert_size n se')) →
    exists_size_interp T se ≡ exists_size_interp T' se'.
  Proof.
    intros HT sv; cbn -[senv_insert_size].
    f_equiv; intros n.
    apply HT.
  Qed.

  Lemma exists_type_interp_ren ξm ξr ξs ξt se se' κ (T T' : semantic_type) :
    sem_env_ren ξm ξr ξs ξt se se' →
    (∀ sκ sκ_T X, T (senv_insert_type sκ sκ_T X se) ≡ T' (senv_insert_type sκ sκ_T X se')) →
    exists_type_interp κ T se ≡ exists_type_interp (ren_kind ξr ξs κ) T' se'.
  Proof.
    intros HR HT sv; cbn -[senv_insert_type].
    rewrite <- (eval_kind_ren _ _ _ _ _ _ κ HR).
    f_equiv; intros X.
    f_equiv; intros sκ.
    f_equiv; intros sκ_T.
    specialize (HT sκ sκ_T X).
    repeat (f_equiv; try done).
  Qed.

  Lemma values_interp1_ren Ts Ts' (se se' : semantic_env (Σ:=Σ)) :
    Forall2 (λ T T' : semantic_type, T se ≡ T' se') Ts Ts' →
    values_interp1 Ts se ≡ values_interp1 Ts' se'.
  Proof.
    intros HF os; cbn.
    f_equiv; intros oss.
    f_equiv.
    apply (big_sepL2_interp_ren _ _ _ SAtoms), HF.
  Qed.

  Lemma cwp_wasm_equiv es (L1 L2 : label_ctxO) (R1 R2 : return_ctxO) (Φ1 Φ2 : fvs_predO) :
    L1 ≡ L2 → R1 ≡ R2 → Φ1 ≡ Φ2 →
    cwp_wasm NotStuck ⊤ es (coe_label_ctx L1) (coe_return_ctx R1) (coe_fvs_pred Φ1) ⊣⊢
    cwp_wasm NotStuck ⊤ es (coe_label_ctx L2) (coe_return_ctx R2) (coe_fvs_pred Φ2).
  Proof.
    intros HL HR HΦ.
    unfold cwp_wasm.
    apply (ne_proper (A:=logpredO) (B:=iPropO Σ) (lenient_wp _ _ _)).
    change (cwp_post_lp (coe_label_ctx L1) (coe_return_ctx R1) (coe_fvs_pred Φ1))
      with (cwp_post_lp_ne L1 R1 Φ1).
    change (cwp_post_lp (coe_label_ctx L2) (coe_return_ctx R2) (coe_fvs_pred Φ2))
      with (cwp_post_lp_ne L2 R2 Φ2).
    repeat (f_equiv; try done).
  Qed.

  Lemma mono_closure_interp_ren ξm ξr ξs ξt se se' τs1 τs2 Ts1 Ts2 Ts1' Ts2' :
    sem_env_ren ξm ξr ξs ξt se se' →
    Forall2 (λ T T' : semantic_type, T se ≡ T' se') Ts1 Ts1' →
    Forall2 (λ T T' : semantic_type, T se ≡ T' se') Ts2 Ts2' →
    mono_closure_interp rti sr τs1 τs2 Ts1 Ts2 se ≡
    mono_closure_interp rti sr (map (ren_type ξm ξr ξs ξt) τs1) (map (ren_type ξm ξr ξs ξt) τs2) Ts1' Ts2' se'.
  Proof.
    intros HR HF1 HF2 cl.
    destruct cl as [inst [ts1 ts2] tlocs es|]; [|done].
    cbn -[values_interp1 atoms_interp translate_types].
    rewrite <- !(translate_types_ren _ _ _ _ _ _ _ HR).
    pose proof (values_interp1_ren _ _ _ _ HF1) as HV1.
    pose proof (values_interp1_ren _ _ _ _ HF2) as HV2.
    pose (oΦ1 := (λne vs2, (∃ os2, atoms_interp os2 vs2 ∗ values_interp1 Ts2 se os2) ∗
                           (∃ θ', rt_token rti sr lpall θ') ∗ na_own logrel_nais ⊤)%I).
    pose (oΦ2 := (λne vs2, (∃ os2, atoms_interp os2 vs2 ∗ values_interp1 Ts2' se' os2) ∗
                           (∃ θ', rt_token rti sr lpall θ') ∗ na_own logrel_nais ⊤)%I).
    assert (HΦs : oΦ1 ≡ oΦ2).
    { intros vs2; cbn -[values_interp1 atoms_interp].
      f_equiv.
      f_equiv; intros os2.
      f_equiv.
      exact (HV2 os2). }
    assert (HΦs' : (λne _ : leibnizO frame, oΦ1) ≡ (λne _, oΦ2)) by (intros ?; exact HΦs).
    pose (oL1 := [(length ts2, λne _, oΦ1)] : label_ctxO).
    pose (oL2 := [(length ts2, λne _, oΦ2)] : label_ctxO).
    assert (HLs : oL1 ≡ oL2) by (constructor; [split; [done|exact HΦs']|constructor]).
    pose (oR1 := Some (length ts2, oΦ1) : return_ctxO).
    pose (oR2 := Some (length ts2, oΦ2) : return_ctxO).
    assert (HRs : oR1 ≡ oR2) by (constructor; split; [done|exact HΦs]).
    do 2 (f_equiv; try done).
    do 9 f_equiv.
    f_equiv; first exact (HV1 _).
    do 4 f_equiv.
    apply (cwp_wasm_equiv es oL1 oL2 oR1 oR2 (λne _, oΦ1) (λne _, oΦ2) HLs HRs HΦs').
  Qed.

  Lemma forall_type_interp_ren ξm ξr ξs ξt se se' κ (FT FT' : semantic_env -n> ClR) :
    sem_env_ren ξm ξr ξs ξt se se' →
    (∀ sκ sκ_T X, FT (senv_insert_type sκ sκ_T X se) ≡ FT' (senv_insert_type sκ sκ_T X se')) →
    forall_type_interp κ FT se ≡ forall_type_interp (ren_kind ξr ξs κ) FT' se'.
  Proof.
    intros HR HFT cl; cbn -[senv_insert_type].
    rewrite <- (eval_kind_ren _ _ _ _ _ _ κ HR).
    f_equiv.
    f_equiv; intros sκ.
    f_equiv; intros sκ_T.
    f_equiv; intros X.
    specialize (HFT sκ sκ_T X).
    repeat (f_equiv; try done).
  Qed.

  Lemma forall_mem_interp_ren (FT FT' : semantic_env -n> ClR) (se se' : semantic_env (Σ:=Σ)) :
    (∀ μ, FT (senv_insert_mem μ se) ≡ FT' (senv_insert_mem μ se')) →
    forall_mem_interp FT se ≡ forall_mem_interp FT' se'.
  Proof.
    intros H cl; cbn -[senv_insert_mem].
    f_equiv.
    f_equiv; intros μ.
    exact (H μ cl).
  Qed.

  Lemma forall_rep_interp_ren (FT FT' : semantic_env -n> ClR) (se se' : semantic_env (Σ:=Σ)) :
    (∀ ιs, FT (senv_insert_rep ιs se) ≡ FT' (senv_insert_rep ιs se')) →
    forall_rep_interp FT se ≡ forall_rep_interp FT' se'.
  Proof.
    intros H cl; cbn -[senv_insert_rep].
    f_equiv.
    f_equiv; intros ιs.
    exact (H ιs cl).
  Qed.

  Lemma forall_size_interp_ren (FT FT' : semantic_env -n> ClR) (se se' : semantic_env (Σ:=Σ)) :
    (∀ n, FT (senv_insert_size n se) ≡ FT' (senv_insert_size n se')) →
    forall_size_interp FT se ≡ forall_size_interp FT' se'.
  Proof.
    intros H cl; cbn -[senv_insert_size].
    f_equiv.
    f_equiv; intros n.
    exact (H n cl).
  Qed.

  Definition type_ren_ok (τ : type) : Prop :=
    ∀ ξm ξr ξs ξt se se',
      sem_env_ren ξm ξr ξs ξt se se' →
      type_interp rti sr τ se ≡ type_interp rti sr (ren_type ξm ξr ξs ξt τ) se'.

  Definition function_type_ren_ok (ϕ : Core.function_type) : Prop :=
    ∀ ξm ξr ξs ξt se se',
      sem_env_ren ξm ξr ξs ξt se se' →
      closure_interp rti sr ϕ se ≡ closure_interp rti sr (ren_function_type ξm ξr ξs ξt ϕ) se'.

  Definition inner_function_type_ren_ok (ϕ : inner_function_type) : Prop :=
    ∀ ξm ξr ξs ξt se se',
      sem_env_ren ξm ξr ξs ξt se se' →
      inner_closure_interp rti sr ϕ se ≡
      inner_closure_interp rti sr (ren_inner_function_type ξm ξr ξs ξt ϕ) se'.

  Lemma map_type_interp_ren τs ξm ξr ξs ξt se se' :
    sem_env_ren ξm ξr ξs ξt se se' →
    Forall type_ren_ok τs →
    Forall2 (λ T T' : semantic_type, T se ≡ T' se')
      (map (type_interp rti sr) τs) (map (type_interp rti sr) (map (ren_type ξm ξr ξs ξt) τs)).
  Proof.
    intros HR IH.
    rewrite !map_fmap.
    apply Forall2_fmap, Forall2_fmap_r, Forall_Forall2_diag.
    eapply Forall_impl; [exact IH|].
    intros τ Hτ; cbn.
    by apply Hτ.
  Qed.

  Lemma closure_interp_eq' ϕ se :
    closure_interp rti sr ϕ se ≡ closure_interp' rti sr ϕ se.
  Proof.
    intros cl; apply closure_interp_eq.
  Qed.

  Lemma inner_closure_interp_eq' ϕ se :
    inner_closure_interp rti sr ϕ se ≡ inner_closure_interp' rti sr ϕ se.
  Proof.
    intros cl; apply inner_closure_interp_eq.
  Qed.

  Ltac cbn_interp :=
    cbn -[type_var_interp sum_interp variant_interp prod_interp struct_interp
          ref_interp coderef_interp ser_interp rec_interp
          exists_mem_interp exists_rep_interp exists_size_interp exists_type_interp
          mono_closure_interp forall_type_interp forall_mem_interp forall_rep_interp forall_size_interp
          unscoped.up_ren].

  Lemma type_interp_ren :
    (∀ τ, type_ren_ok τ) ∧ (∀ ϕ, function_type_ren_ok ϕ) ∧ (∀ ϕ, inner_function_type_ren_ok ϕ).
  Proof.
    apply type_and_function_ind.
    - intros x ξm ξr ξs ξt se se' HR.
      apply type_interp_ext; [by eapply type_skind_ren|].
      cbn_interp.
      by eapply type_var_interp_ren.
    - intros κ ξm ξr ξs ξt se se' HR.
      apply type_interp_ext; [by eapply type_skind_ren|].
      by intros sv; cbn.
    - intros κ nt ξm ξr ξs ξt se se' HR.
      apply type_interp_ext; [by eapply type_skind_ren|].
      by intros sv; cbn.
    - intros κ τs IH ξm ξr ξs ξt se se' HR.
      apply type_interp_ext; [by eapply type_skind_ren|].
      cbn_interp.
      apply (sum_interp_ren _ _ _ _ _ _ _ _ _ HR), (map_type_interp_ren _ _ _ _ _ _ _ HR IH).
    - intros κ τs IH ξm ξr ξs ξt se se' HR.
      apply type_interp_ext; [by eapply type_skind_ren|].
      cbn_interp.
      apply variant_interp_ren, (map_type_interp_ren _ _ _ _ _ _ _ HR IH).
    - intros κ τs IH ξm ξr ξs ξt se se' HR.
      apply type_interp_ext; [by eapply type_skind_ren|].
      cbn_interp.
      apply prod_interp_ren, (map_type_interp_ren _ _ _ _ _ _ _ HR IH).
    - intros κ τs IH ξm ξr ξs ξt se se' HR.
      apply type_interp_ext; [by eapply type_skind_ren|].
      cbn_interp.
      apply struct_interp_ren, (map_type_interp_ren _ _ _ _ _ _ _ HR IH).
    - intros κ μ β τ IH ξm ξr ξs ξt se se' HR.
      apply type_interp_ext; [by eapply type_skind_ren|].
      cbn_interp.
      apply (ref_interp_ren _ _ _ _ _ _ _ _ _ _ HR).
      by apply IH.
    - intros κ ϕ IH ξm ξr ξs ξt se se' HR.
      apply type_interp_ext; [by eapply type_skind_ren|].
      cbn_interp.
      apply coderef_interp_ren.
      by apply IH.
    - intros κ τ IH ξm ξr ξs ξt se se' HR.
      apply type_interp_ext; [by eapply type_skind_ren|].
      cbn_interp.
      apply ser_interp_ren.
      by apply IH.
    - intros κ ρ ξm ξr ξs ξt se se' HR.
      apply type_interp_ext; [by eapply type_skind_ren|].
      by intros sv; cbn.
    - intros κ σ ξm ξr ξs ξt se se' HR.
      apply type_interp_ext; [by eapply type_skind_ren|].
      by intros sv; cbn.
    - intros κ τ IH ξm ξr ξs ξt se se' HR.
      apply type_interp_ext; [by eapply type_skind_ren|].
      cbn_interp.
      apply (rec_interp_ren _ _ _ _ _ _ _ _ _ HR).
      intros sκ sκ_T X.
      apply IH.
      by apply sem_env_ren_insert_type.
    - intros κ τ IH ξm ξr ξs ξt se se' HR.
      apply type_interp_ext; [by eapply type_skind_ren|].
      cbn_interp.
      apply exists_mem_interp_ren; intros μ.
      apply IH.
      by apply sem_env_ren_insert_mem.
    - intros κ τ IH ξm ξr ξs ξt se se' HR.
      apply type_interp_ext; [by eapply type_skind_ren|].
      cbn_interp.
      apply exists_rep_interp_ren; intros ιs.
      apply IH.
      by apply sem_env_ren_insert_rep.
    - intros κ τ IH ξm ξr ξs ξt se se' HR.
      apply type_interp_ext; [by eapply type_skind_ren|].
      cbn_interp.
      apply exists_size_interp_ren; intros n.
      apply IH.
      by apply sem_env_ren_insert_size.
    - intros κ κ0 τ IH ξm ξr ξs ξt se se' HR.
      apply type_interp_ext; [by eapply type_skind_ren|].
      cbn_interp.
      apply (exists_type_interp_ren _ _ _ _ _ _ _ _ _ HR).
      intros sκ sκ_T X.
      apply IH.
      by apply sem_env_ren_insert_type.
    - intros τs1 τs2 IH1 IH2 ξm ξr ξs ξt se se' HR.
      cbn_interp.
      apply (mono_closure_interp_ren _ _ _ _ _ _ _ _ _ _ _ _ HR);
        by apply map_type_interp_ren.
    - intros κ ϕ IH ξm ξr ξs ξt se se' HR.
      cbn_interp.
      apply (forall_type_interp_ren _ _ _ _ _ _ _ _ _ HR).
      intros sκ sκ_T X.
      apply IH.
      by apply sem_env_ren_insert_type.
    - intros ϕ IH ξm ξr ξs ξt se se' HR.
      rewrite !closure_interp_eq'; cbn_interp.
      rewrite <- !inner_closure_interp_eq'.
      by apply IH.
    - intros ϕ IH ξm ξr ξs ξt se se' HR.
      rewrite !closure_interp_eq'; cbn_interp.
      apply forall_mem_interp_ren; intros μ.
      apply IH.
      by apply sem_env_ren_insert_mem.
    - intros ϕ IH ξm ξr ξs ξt se se' HR.
      rewrite !closure_interp_eq'; cbn_interp.
      apply forall_rep_interp_ren; intros ιs.
      apply IH.
      by apply sem_env_ren_insert_rep.
    - intros ϕ IH ξm ξr ξs ξt se se' HR.
      rewrite !closure_interp_eq'; cbn_interp.
      apply forall_size_interp_ren; intros n.
      apply IH.
      by apply sem_env_ren_insert_size.
  Qed.

  Lemma type_interp_up_rep se sub_t ρ sv i :
    type_interp rti sr (sub_t i) se sv ∗-∗
    type_interp rti sr (up_representation_type sub_t i) (senv_insert_rep ρ se) sv.
  Proof.
    apply bi.equiv_wand_iff, (proj1 type_interp_ren).
    by split; intros [|j]; cbn.
  Qed.

  Lemma type_interp_up_size se sub_t n sv i :
    type_interp rti sr (sub_t i) se sv ∗-∗
    type_interp rti sr (up_size_type sub_t i) (senv_insert_size n se) sv.
  Proof.
    apply bi.equiv_wand_iff, (proj1 type_interp_ren).
    by split; intros [|j]; cbn.
  Qed.

  Lemma type_interp_up_type se sub_t sκ sκ_T T sv i :
    type_interp rti sr (sub_t i) se sv ∗-∗
    type_interp rti sr (up_type_type sub_t (S i)) (senv_insert_type sκ sκ_T T se) sv.
  Proof.
    apply bi.equiv_wand_iff, (proj1 type_interp_ren).
    by split; intros [|j]; cbn.
  Qed.

  Lemma type_interp_up_memory se sub_t μ sv i :
    type_interp rti sr (sub_t i) se sv ∗-∗
    type_interp rti sr (up_memory_type sub_t i) (senv_insert_mem μ se) sv.
  Proof.
    apply bi.equiv_wand_iff, (proj1 type_interp_ren).
    by split; intros [|j]; cbn.
  Qed.

  Lemma eq_subskind_of_option u v :
    u = v →
    subskind_of_option u v.
  Proof.
    intros H. subst u.
    apply subskind_of_option_refl.
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

  Lemma value_interp_eq_no_sv τ se :
    value_interp rti sr se τ ≡ (add_skind_interp τ $ pre_type_interp rti sr τ) se.
  Proof.
    iStartProof.
    iIntros (sv).
    rewrite value_interp_eq.
    iSplitR; iIntros; done.
  Qed.


  Lemma skind_rec_interp_unfold_no_sv :
  ∀ (sκ : skind) (T : semantic_type) (se : semantic_env),
    skind_rec_interp sκ T se
      ≡ (λne sv, (▷ T (senv_insert_type (Σ:=Σ) sκ sκ
                         (add_skind_interp_closed sκ (skind_rec_interp sκ T se)) se) sv))%I.
  Proof.
    intros.
    iIntros.
    rewrite skind_rec_interp_unfold.
    cbn.
    iSplitR; iIntros; done.
  Qed.

  (** Substitution conditions, bundled so the binder cases of the substitution lemmas
      can extend them with one lemma per binder. *)
  Record subst_rel (F F' : function_ctx) (sub_m : nat → Core.memory) (sub_r : nat → representation)
    (sub_s : nat → Core.size) (sub_t : nat → type) (se se' : semantic_env (Σ:=Σ)) : Prop :=
    { subst_rel_env' : sem_env_interp F' se';
      subst_rel_env : sem_env_interp F se;
      subst_rel_rep : sem_env_rel_rep_eq se' se sub_r;
      subst_rel_size : sem_env_rel_size_eq se' se sub_s;
      subst_rel_mem : sem_env_rel_mem_eq se' se sub_m;
      subst_rel_sκ : sem_env_rel_sκ_eq se' se sub_t;
      subst_rel_type : ∀ i, type_var_interp i se' ≡ value_interp rti sr se (sub_t i);
      subst_rel_good : sub_t_well_formed F sub_t }.

  Lemma sem_env_ren_shift_mem (se : semantic_env (Σ:=Σ)) μ :
    sem_env_ren unscoped.shift unscoped.id unscoped.id unscoped.id se (senv_insert_mem μ se).
  Proof. by split; intros [|j]; cbn. Qed.

  Lemma sem_env_ren_shift_rep (se : semantic_env (Σ:=Σ)) ιs :
    sem_env_ren unscoped.id unscoped.shift unscoped.id unscoped.id se (senv_insert_rep ιs se).
  Proof. by split; intros [|j]; cbn. Qed.

  Lemma sem_env_ren_shift_size (se : semantic_env (Σ:=Σ)) n :
    sem_env_ren unscoped.id unscoped.id unscoped.shift unscoped.id se (senv_insert_size n se).
  Proof. by split; intros [|j]; cbn. Qed.

  Lemma sem_env_ren_shift_type (se : semantic_env (Σ:=Σ)) sκ sκ_T T :
    sem_env_ren unscoped.id unscoped.id unscoped.id unscoped.shift se (senv_insert_type sκ sκ_T T se).
  Proof. by split; intros [|j]; cbn. Qed.

  Lemma value_interp_ren ξm ξr ξs ξt (se se' : semantic_env (Σ:=Σ)) τ :
    sem_env_ren ξm ξr ξs ξt se se' →
    value_interp rti sr se τ ≡ value_interp rti sr se' (ren_type ξm ξr ξs ξt τ).
  Proof.
    intros HR.
    Transparent value_interp. unfold value_interp. Opaque value_interp.
    cbn.
    by apply (proj1 type_interp_ren).
  Qed.

  Lemma value_interp_var_insert (se : semantic_env (Σ:=Σ)) sκ sκ_T T :
    subskind_of sκ_T sκ →
    skind_has_stype sκ_T T →
    T ≡ value_interp rti sr (senv_insert_type sκ sκ_T T se) (VarT 0).
  Proof.
    intros Hsub [_ HT] sv.
    rewrite value_interp_eq; cbn -[skind_has_svalue].
    iSplit.
    - iIntros "H".
      iDestruct (HT with "H") as %Hsv.
      iExists sκ; iFrame.
      iPureIntro; split; first done.
      by eapply skind_as_type_refine.
    - by iIntros "(% & _ & _ & $)".
  Qed.

  Lemma sem_env_rel_type_eq_var (se se' : semantic_env (Σ:=Σ)) sub_t :
    sem_env_rel_type_eq se' se sub_t →
    ∀ i, type_var_interp i se' ≡ value_interp rti sr se (sub_t i).
  Proof.
    intros HT i sv.
    specialize (HT i sv).
    cbn in HT |- *.
    by destruct (se'.2 !! i) as [[? [? T]]|]; cbn in HT |- *.
  Qed.

  Lemma subst_rel_insert_mem F F' sub_m sub_r sub_s sub_t se se' μ :
    subst_rel F F' sub_m sub_r sub_s sub_t se se' →
    subst_rel (F <| fc_kind_ctx ::= set kc_mem_vars S |>) (F' <| fc_kind_ctx ::= set kc_mem_vars S |>)
      (up_memory_memory sub_m) (up_memory_representation sub_r) (up_memory_size sub_s)
      (up_memory_type sub_t) (senv_insert_mem μ se) (senv_insert_mem μ se').
  Proof.
    intros [Henv' Henv Hr Hs Hm Hsκ HT Hgood]; unfold_sem_rels.
    pose proof (sem_env_ren_shift_mem se μ) as HR.
    pose proof (sem_env_ren_shift_mem se' μ) as HR'.
    split.
    - by apply sem_env_insert_mem.
    - by apply sem_env_insert_mem.
    - intros i; unfold up_memory_representation, core.funcomp.
      rewrite <- (eval_rep_ren _ _ _ _ _ _ _ HR); apply Hr.
    - intros i; unfold up_memory_size, core.funcomp.
      rewrite <- (eval_size_ren _ _ _ _ _ _ _ HR); apply Hs.
    - intros [|i]; first done.
      unfold up_memory_memory, core.funcomp; cbn [unscoped.scons].
      rewrite <- (eval_mem_ren _ _ _ _ _ _ _ HR); apply Hm.
    - intros i; unfold up_memory_type, core.funcomp.
      rewrite <- (type_skind_ren _ _ _ _ _ _ _ HR); apply Hsκ.
    - intros i; unfold up_memory_type, core.funcomp.
      etrans; first (symmetry; exact (type_var_interp_ren _ _ _ _ _ _ i HR')).
      etrans; first apply HT.
      by apply value_interp_ren.
    - intros i; unfold up_memory_type, core.funcomp.
      rewrite refresh_kinds_up_shift_mem; by rewrite Hgood.
  Qed.

  Lemma subst_rel_insert_rep F F' sub_m sub_r sub_s sub_t se se' ιs :
    subst_rel F F' sub_m sub_r sub_s sub_t se se' →
    subst_rel (add_rep_var F) (add_rep_var F')
      (up_representation_memory sub_m) (up_representation_representation sub_r)
      (up_representation_size sub_s) (up_representation_type sub_t)
      (senv_insert_rep ιs se) (senv_insert_rep ιs se').
  Proof.
    intros [Henv' Henv Hr Hs Hm Hsκ HT Hgood]; unfold_sem_rels.
    pose proof (sem_env_ren_shift_rep se ιs) as HR.
    pose proof (sem_env_ren_shift_rep se' ιs) as HR'.
    split.
    - by apply sem_env_insert_rep.
    - by apply sem_env_insert_rep.
    - intros [|i]; first done.
      unfold up_representation_representation, core.funcomp; cbn [unscoped.scons].
      rewrite <- (eval_rep_ren _ _ _ _ _ _ _ HR); apply Hr.
    - intros i; unfold up_representation_size, core.funcomp.
      rewrite <- (eval_size_ren _ _ _ _ _ _ _ HR); apply Hs.
    - intros i; unfold up_representation_memory, core.funcomp.
      rewrite <- (eval_mem_ren _ _ _ _ _ _ _ HR); apply Hm.
    - intros i; unfold up_representation_type, core.funcomp.
      rewrite <- (type_skind_ren _ _ _ _ _ _ _ HR); apply Hsκ.
    - intros i; unfold up_representation_type, core.funcomp.
      etrans; first (symmetry; exact (type_var_interp_ren _ _ _ _ _ _ i HR')).
      etrans; first apply HT.
      by apply value_interp_ren.
    - intros i; unfold up_representation_type, core.funcomp.
      rewrite refresh_kinds_up_shift_rep; by rewrite Hgood.
  Qed.

  Lemma subst_rel_insert_size F F' sub_m sub_r sub_s sub_t se se' n :
    subst_rel F F' sub_m sub_r sub_s sub_t se se' →
    subst_rel (add_size_var F) (add_size_var F')
      (up_size_memory sub_m) (up_size_representation sub_r) (up_size_size sub_s) (up_size_type sub_t)
      (senv_insert_size n se) (senv_insert_size n se').
  Proof.
    intros [Henv' Henv Hr Hs Hm Hsκ HT Hgood]; unfold_sem_rels.
    pose proof (sem_env_ren_shift_size se n) as HR.
    pose proof (sem_env_ren_shift_size se' n) as HR'.
    split.
    - by apply sem_env_insert_size.
    - by apply sem_env_insert_size.
    - intros i; unfold up_size_representation, core.funcomp.
      rewrite <- (eval_rep_ren _ _ _ _ _ _ _ HR); apply Hr.
    - intros [|i]; first done.
      unfold up_size_size, core.funcomp; cbn [unscoped.scons].
      rewrite <- (eval_size_ren _ _ _ _ _ _ _ HR); apply Hs.
    - intros i; unfold up_size_memory, core.funcomp.
      rewrite <- (eval_mem_ren _ _ _ _ _ _ _ HR); apply Hm.
    - intros i; unfold up_size_type, core.funcomp.
      rewrite <- (type_skind_ren _ _ _ _ _ _ _ HR); apply Hsκ.
    - intros i; unfold up_size_type, core.funcomp.
      etrans; first (symmetry; exact (type_var_interp_ren _ _ _ _ _ _ i HR')).
      etrans; first apply HT.
      by apply value_interp_ren.
    - intros i; unfold up_size_type, core.funcomp.
      rewrite refresh_kinds_up_shift_size; by rewrite Hgood.
  Qed.

  Lemma subst_rel_insert_type F F' sub_m sub_r sub_s sub_t se se' κ sκ sκ_T T :
    subst_rel F F' sub_m sub_r sub_s sub_t se se' →
    eval_kind se' κ = Some sκ →
    subskind_of sκ_T sκ →
    skind_has_stype sκ_T T →
    subst_rel (F <| fc_type_vars ::= cons (subst_kind sub_r sub_s κ) |>) (F' <| fc_type_vars ::= cons κ |>)
      (up_type_memory sub_m) (up_type_representation sub_r) (up_type_size sub_s) (up_type_type sub_t)
      (senv_insert_type sκ sκ_T T se) (senv_insert_type sκ sκ_T T se').
  Proof.
    intros [Henv' Henv Hr Hs Hm Hsκ HT Hgood] Hκ Hsub HsT; unfold_sem_rels.
    pose proof (sem_env_ren_shift_type se sκ sκ_T T) as HR.
    pose proof (sem_env_ren_shift_type se' sκ sκ_T T) as HR'.
    split.
    - by apply sem_env_interp_insert_type.
    - apply sem_env_interp_insert_type; try done.
      by erewrite <- eval_kind_subst_senv_eq.
    - intros i; unfold up_type_representation, core.funcomp.
      rewrite <- (eval_rep_ren _ _ _ _ _ _ _ HR); apply Hr.
    - intros i; unfold up_type_size, core.funcomp.
      rewrite <- (eval_size_ren _ _ _ _ _ _ _ HR); apply Hs.
    - intros i; unfold up_type_memory, core.funcomp.
      rewrite <- (eval_mem_ren _ _ _ _ _ _ _ HR); apply Hm.
    - intros [|i]; first (cbn; apply subskind_of_refl).
      unfold up_type_type, core.funcomp; cbn [unscoped.scons].
      rewrite <- (type_skind_ren _ _ _ _ _ _ _ HR); apply Hsκ.
    - intros [|i].
      { etrans; last by apply value_interp_var_insert.
        by intros sv; cbn. }
      unfold up_type_type, core.funcomp; cbn [unscoped.scons].
      etrans; first (symmetry; exact (type_var_interp_ren _ _ _ _ _ _ i HR')).
      etrans; first apply HT.
      by apply value_interp_ren.
    - intros [|i]; first done.
      unfold up_type_type, core.funcomp; cbn [unscoped.scons].
      rewrite refresh_kinds_up_shift_type; by rewrite Hgood.
  Qed.

  Lemma type_skind_has_kind F (se : semantic_env (Σ:=Σ)) τ κ :
    has_kind F τ κ →
    sem_env_interp F se →
    type_skind se τ = eval_kind se κ.
  Proof.
    intros Hk Henv.
    apply has_kind_inv in Hk as Hok; inversion Hok as [? ? ? _ Hκok]; subst.
    destruct (eval_kind_ok_Some _ _ _ Henv Hκok) as [sκ Hsκ].
    rewrite Hsκ.
    by eapply type_skind_has_kind_Some.
  Qed.

  Lemma has_kind_memtype_eval_size F (se : semantic_env (Σ:=Σ)) σ ξ τ :
    sem_env_interp F se →
    has_kind F τ (MEMTYPE σ ξ) →
    ∃ n, eval_size se σ = Some n ∧ type_skind se τ = Some (SMEMTYPE n ξ).
  Proof.
    intros Henv Hk.
    apply has_kind_inv in Hk as Hok; inversion Hok as [? ? ? _ Hκok]; subst.
    inversion Hκok as [|? ? ? Hσok]; subst.
    destruct (eval_size_ok_Some _ _ _ Henv Hσok) as [n Hn].
    exists n; split; first done.
    rewrite (type_skind_has_kind _ _ _ _ Hk Henv); cbn.
    by rewrite Hn.
  Qed.

  Lemma has_kind_sum_inv F κ τs κ' :
    has_kind F (SumT κ τs) κ' →
    ∃ ρs ξs, κ' = VALTYPE (SumR ρs) (ref_flag_lub ξs) ∧ κ = κ' ∧
             Forall3 (λ τ ρ ξ, has_kind F τ (VALTYPE ρ ξ)) τs ρs ξs.
  Proof. inversion 1; subst; eauto. Qed.

  Lemma has_kind_variant_inv F κ τs κ' :
    has_kind F (VariantT κ τs) κ' →
    ∃ σs ξs, κ' = MEMTYPE (SumS σs) (ref_flag_lub ξs) ∧ κ = κ' ∧
             Forall3 (λ τ σ ξ, has_kind F τ (MEMTYPE σ ξ)) τs σs ξs.
  Proof. inversion 1; subst; eauto. Qed.

  Lemma has_kind_prod_inv F κ τs κ' :
    has_kind F (ProdT κ τs) κ' →
    ∃ ρs ξs, κ' = VALTYPE (ProdR ρs) (ref_flag_lub ξs) ∧ κ = κ' ∧
             Forall3 (λ τ ρ ξ, has_kind F τ (VALTYPE ρ ξ)) τs ρs ξs.
  Proof. inversion 1; subst; eauto. Qed.

  Lemma has_kind_struct_inv F κ τs κ' :
    has_kind F (StructT κ τs) κ' →
    ∃ σs ξs, κ' = MEMTYPE (ProdS σs) (ref_flag_lub ξs) ∧ κ = κ' ∧
             Forall3 (λ τ σ ξ, has_kind F τ (MEMTYPE σ ξ)) τs σs ξs.
  Proof. inversion 1; subst; eauto. Qed.

  Lemma has_kind_ser_inv F κ τ κ' :
    has_kind F (SerT κ τ) κ' →
    ∃ ρ ξ, κ' = MEMTYPE (RepS ρ) ξ ∧ κ = κ' ∧ has_kind F τ (VALTYPE ρ ξ).
  Proof. inversion 1; subst; eauto. Qed.

  Lemma ref_flag_lub2_mono ξ1 ξ1' ξ2 ξ2' :
    ref_flag_le ξ1 ξ1' → ref_flag_le ξ2 ξ2' →
    ref_flag_le (ref_flag_lub2 ξ1 ξ2) (ref_flag_lub2 ξ1' ξ2').
  Proof. by destruct ξ1, ξ1', ξ2, ξ2'. Qed.

  Lemma ref_flag_lub_mono ξs ξs' :
    Forall2 ref_flag_le ξs ξs' → ref_flag_le (ref_flag_lub ξs) (ref_flag_lub ξs').
  Proof.
    induction 1 as [|ξ ξ' ξs ξs' Hle _ IH]; first done.
    by apply ref_flag_lub2_mono.
  Qed.

  Definition refresh_subskind (rs : type → type) F F' (se se' : semantic_env (Σ:=Σ)) (τ : type) : Prop :=
    ∀ κ κ', has_kind F' τ κ → has_kind F (rs τ) κ' →
            subskind_of_option (type_skind se (rs τ)) (type_skind se' τ).

  Lemma refresh_children_val rs F F' se se' τs ρs ξs ρs' ξs' :
    sem_env_interp F' se' → sem_env_interp F se →
    Forall (refresh_subskind rs F F' se se') τs →
    Forall3 (λ τ ρ ξ, has_kind F' τ (VALTYPE ρ ξ)) τs ρs ξs →
    Forall3 (λ τ ρ ξ, has_kind F τ (VALTYPE ρ ξ)) (map rs τs) ρs' ξs' →
    Forall2 (λ ρ ρ', eval_rep se' ρ = eval_rep se ρ') ρs ρs' ∧ Forall2 ref_flag_le ξs' ξs.
  Proof.
    intros Henv' Henv HIH; revert ρs ξs ρs' ξs'.
    induction HIH as [|τ τs IH _ IHτs]; intros ρs ξs ρs' ξs' H1 H2.
    - inversion H1; inversion H2; subst; done.
    - apply Forall3_cons_inv_l in H1 as (ρ & ρs0 & ξ & ξs0 & -> & -> & Hk & H1).
      cbn in H2.
      apply Forall3_cons_inv_l in H2 as (ρ' & ρs0' & ξ' & ξs0' & -> & -> & Hk' & H2).
      destruct (IHτs _ _ _ _ H1 H2) as [Hρ Hle].
      destruct (has_kind_valtype_eval_rep _ _ _ _ _ Henv' Hk) as (ιs & Hιs & Hsk).
      destruct (has_kind_valtype_eval_rep _ _ _ _ _ Henv Hk') as (ιs' & Hιs' & Hsk').
      specialize (IH _ _ Hk Hk'); rewrite Hsk Hsk' in IH; cbn in IH; inversion IH; subst.
      split; constructor; try done.
      by rewrite Hιs Hιs'.
  Qed.

  Lemma refresh_children_mem rs F F' se se' τs σs ξs σs' ξs' :
    sem_env_interp F' se' → sem_env_interp F se →
    Forall (refresh_subskind rs F F' se se') τs →
    Forall3 (λ τ σ ξ, has_kind F' τ (MEMTYPE σ ξ)) τs σs ξs →
    Forall3 (λ τ σ ξ, has_kind F τ (MEMTYPE σ ξ)) (map rs τs) σs' ξs' →
    Forall2 (λ σ σ', eval_size se' σ = eval_size se σ') σs σs' ∧ Forall2 ref_flag_le ξs' ξs.
  Proof.
    intros Henv' Henv HIH; revert σs ξs σs' ξs'.
    induction HIH as [|τ τs IH _ IHτs]; intros σs ξs σs' ξs' H1 H2.
    - inversion H1; inversion H2; subst; done.
    - apply Forall3_cons_inv_l in H1 as (σ & σs0 & ξ & ξs0 & -> & -> & Hk & H1).
      cbn in H2.
      apply Forall3_cons_inv_l in H2 as (σ' & σs0' & ξ' & ξs0' & -> & -> & Hk' & H2).
      destruct (IHτs _ _ _ _ H1 H2) as [Hσ Hle].
      destruct (has_kind_memtype_eval_size _ _ _ _ _ Henv' Hk) as (n & Hn & Hsk).
      destruct (has_kind_memtype_eval_size _ _ _ _ _ Henv Hk') as (n' & Hn' & Hsk').
      specialize (IH _ _ Hk Hk'); rewrite Hsk Hsk' in IH; cbn in IH; inversion IH; subst.
      split; constructor; try done.
      by rewrite Hn Hn'.
  Qed.

  Lemma type_skind_refresh_subst F F' sub_m sub_r sub_s sub_t se se' τ κ κ' :
    subst_rel F F' sub_m sub_r sub_s sub_t se se' →
    has_kind F' τ κ →
    has_kind F (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)) κ' →
    subskind_of_option
      (type_skind (Σ:=Σ) se (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)))
      (type_skind (Σ:=Σ) se' τ).
  Proof.
    intros [Henv' Henv Hr Hs Hm Hsκ HT Hgood]; unfold_sem_rels.
    revert κ κ'.
    induction τ using type_ind with (P0 := const True) (Pi := const True); try done;
      intros κa κb Hk Hk'.
    1: cbn; rewrite Hgood; apply Hsκ.
    all: rewrite (type_skind_has_kind _ _ _ _ Hk' Henv) (type_skind_has_kind _ _ _ _ Hk Henv').
    all: try by (inversion Hk'; subst; inversion Hk; subst;
                 rewrite (eval_kind_subst_senv_eq se se' sub_r sub_s); try done;
                 cbn; first [apply subskind_of_option_refl|apply subskind_of_refl]).
    - (* sum *)
      apply has_kind_sum_inv in Hk as (ρs & ξs & -> & _ & H1).
      apply has_kind_sum_inv in Hk' as (ρs' & ξs' & -> & _ & H2).
      rewrite map_map in H2.
      destruct (refresh_children_val (λ τ, refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ))
                  _ _ _ _ _ _ _ _ _ Henv' Henv H H1 H2) as [Hρ Hle].
      cbn; rewrite <- (Forall2_mapM_ext _ _ _ _ Hρ).
      destruct (mapM (eval_rep se') ρs); cbn; last done.
      constructor; by apply ref_flag_lub_mono.
    - (* variant *)
      apply has_kind_variant_inv in Hk as (σs & ξs & -> & _ & H1).
      apply has_kind_variant_inv in Hk' as (σs' & ξs' & -> & _ & H2).
      rewrite map_map in H2.
      destruct (refresh_children_mem (λ τ, refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ))
                  _ _ _ _ _ _ _ _ _ Henv' Henv H H1 H2) as [Hσ Hle].
      cbn; rewrite <- (Forall2_mapM_ext _ _ _ _ Hσ).
      destruct (mapM (eval_size se') σs); cbn; last done.
      constructor; by apply ref_flag_lub_mono.
    - (* prod *)
      apply has_kind_prod_inv in Hk as (ρs & ξs & -> & _ & H1).
      apply has_kind_prod_inv in Hk' as (ρs' & ξs' & -> & _ & H2).
      rewrite map_map in H2.
      destruct (refresh_children_val (λ τ, refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ))
                  _ _ _ _ _ _ _ _ _ Henv' Henv H H1 H2) as [Hρ Hle].
      cbn; rewrite <- (Forall2_mapM_ext _ _ _ _ Hρ).
      destruct (mapM (eval_rep se') ρs); cbn; last done.
      constructor; by apply ref_flag_lub_mono.
    - (* struct *)
      apply has_kind_struct_inv in Hk as (σs & ξs & -> & _ & H1).
      apply has_kind_struct_inv in Hk' as (σs' & ξs' & -> & _ & H2).
      rewrite map_map in H2.
      destruct (refresh_children_mem (λ τ, refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ))
                  _ _ _ _ _ _ _ _ _ Henv' Henv H H1 H2) as [Hσ Hle].
      cbn; rewrite <- (Forall2_mapM_ext _ _ _ _ Hσ).
      destruct (mapM (eval_size se') σs); cbn; last done.
      constructor; by apply ref_flag_lub_mono.
    - (* ref *)
      inversion Hk; subst; cbn in Hk'.
      + destruct (sub_m m) as [|[|]]; inversion Hk'; subst; cbn; by constructor.
      + inversion Hk'; subst; cbn; by constructor.
      + inversion Hk'; subst; cbn; by constructor.
    - (* ser *)
      apply has_kind_ser_inv in Hk as (ρ & ξ & -> & _ & Hk0).
      apply has_kind_ser_inv in Hk' as (ρ' & ξ' & -> & _ & Hk0').
      specialize (IHτ _ _ Hk0 Hk0').
      rewrite (type_skind_has_kind _ _ _ _ Hk0' Henv) (type_skind_has_kind _ _ _ _ Hk0 Henv') in IHτ.
      cbn in IHτ |- *.
      destruct (eval_rep se ρ'), (eval_rep se' ρ); cbn in IHτ |- *; try done.
      inversion IHτ; subst; by constructor.
  Qed.

  Lemma type_arep_refresh_subst F F' sub_m sub_r sub_s sub_t se se' τ κ κ' :
    subst_rel F F' sub_m sub_r sub_s sub_t se se' →
    has_kind F' τ κ →
    has_kind F (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)) κ' →
    type_arep (Σ:=Σ) se' τ =
    type_arep (Σ:=Σ) se (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)).
  Proof.
    intros HR Hk Hk'.
    pose proof (type_skind_refresh_subst _ _ _ _ _ _ _ _ _ _ _ HR Hk Hk') as Hsub.
    unfold type_arep; cbn -[type_skind].
    destruct (type_skind se' τ) as [sκ|], (type_skind se _) as [sκ'|]; cbn in Hsub |- *; try done.
    by inversion Hsub; subst.
  Qed.

  Lemma translate_type_refresh_subst F F' sub_m sub_r sub_s sub_t se se' τ κ κ' :
    subst_rel F F' sub_m sub_r sub_s sub_t se se' →
    has_kind F' τ κ →
    has_kind F (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)) κ' →
    translate_type (Σ:=Σ) se' τ =
    translate_type (Σ:=Σ) se (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)).
  Proof.
    intros HR Hk Hk'.
    unfold translate_type; cbn -[type_arep].
    by erewrite type_arep_refresh_subst.
  Qed.

  Lemma translate_types_refresh_subst F F' sub_m sub_r sub_s sub_t se se' τs κs κs' :
    subst_rel F F' sub_m sub_r sub_s sub_t se se' →
    Forall2 (has_kind F') τs κs →
    Forall2 (has_kind F) (map (refresh_kinds F) (map (subst_type sub_m sub_r sub_s sub_t) τs)) κs' →
    translate_types (Σ:=Σ) se' τs =
    translate_types (Σ:=Σ) se (map (refresh_kinds F) (map (subst_type sub_m sub_r sub_s sub_t) τs)).
  Proof.
    intros HR H1 H2.
    unfold translate_types; cbn -[translate_type].
    rewrite map_map in H2 |- *.
    f_equal.
    apply Forall_mapM_map_ext, Forall_lookup_2.
    intros i τ Hi.
    destruct (Forall2_lookup_l _ _ _ _ _ H1 Hi) as (κ & _ & Hk).
    destruct (Forall2_lookup_l _ _ _ _ _ H2 (map_lookup_helper_forwards _ _ _ _ Hi)) as (κ' & _ & Hk').
    by eapply translate_type_refresh_subst.
  Qed.

  Lemma skind_interp_same_skind τ τ' (se se' : semantic_env (Σ:=Σ)) sv :
    type_skind se τ' = type_skind se' τ →
    type_interp rti sr τ se' sv -∗
    ∃ sκ, ⌜type_skind se τ' = Some sκ ∧ skind_has_svalue sκ sv⌝.
  Proof.
    intros Heq; rewrite Heq.
    iIntros "H".
    iDestruct (type_interp_skind_svalue with "H") as (sκ) "[% %]".
    by iExists sκ.
  Qed.

  Lemma skind_has_svalue_val_tighten ιs ξ ξ' sv :
    skind_has_svalue (SVALTYPE ιs ξ) sv → ref_flag_atoms_interp ξ' sv →
    skind_has_svalue (SVALTYPE ιs ξ') sv.
  Proof. cbn; by intros [? _] ?. Qed.

  Lemma skind_has_svalue_mem_tighten n ξ ξ' sv :
    skind_has_svalue (SMEMTYPE n ξ) sv → ref_flag_words_interp ξ' sv →
    skind_has_svalue (SMEMTYPE n ξ') sv.
  Proof. cbn; by intros [? _] ?. Qed.

  Lemma ref_flag_words_interp_app ξ ws1 ws2 :
    ref_flag_words_interp ξ (SWords ws1) → ref_flag_words_interp ξ (SWords ws2) →
    ref_flag_words_interp ξ (SWords (ws1 ++ ws2)).
  Proof. unfold ref_flag_words_interp, forall_swords; intros; by apply Forall_app. Qed.

  Lemma ref_flag_words_interp_cons_int ξ n ws :
    ref_flag_words_interp ξ (SWords ws) → ref_flag_words_interp ξ (SWords (WordInt n :: ws)).
  Proof. unfold ref_flag_words_interp, forall_swords; intros; by apply Forall_cons. Qed.

  Lemma ref_flag_words_interp_concat ξs wss :
    Forall2 (λ ξ ws, ref_flag_words_interp ξ (SWords ws)) ξs wss →
    ref_flag_words_interp (ref_flag_lub ξs) (SWords (concat wss)).
  Proof.
    induction 1 as [|ξ ws ξs wss Hhd _ IH]; first by constructor.
    cbn [ref_flag_lub concat foldr].
    apply ref_flag_words_interp_app.
    - eapply ref_flag_words_refine; last exact Hhd. apply ref_flag_lub2_ub.
    - eapply ref_flag_words_refine; last exact IH. apply ref_flag_lub2_ub.
  Qed.

  Lemma ref_flag_atoms_interp_slice ξ os off count :
    ref_flag_atoms_interp NoRefs (SAtoms (take off os ++ drop (off + count) os)) →
    ref_flag_atoms_interp ξ (SAtoms (take count (drop off os))) →
    ref_flag_atoms_interp ξ (SAtoms os).
  Proof.
    intros Hpad Hmid.
    apply ref_flag_atoms_interp_app in Hpad as [Hpre Hpost].
    rewrite <- (take_drop off os), <- (take_drop count (drop off os)), drop_drop.
    apply ref_flag_atoms_interp_app; split; first by eapply (ref_flag_atoms_refine NoRefs).
    apply ref_flag_atoms_interp_app; split; first done.
    by eapply (ref_flag_atoms_refine NoRefs).
  Qed.

  Lemma big_sepL2_pure_forall2 {A B} (Φ : nat → A → B → iProp Σ) (φ : A → B → Prop)
    (l1 : list A) (l2 : list B) :
    (∀ k x y, l1 !! k = Some x → l2 !! k = Some y → Φ k x y ⊢ ⌜φ x y⌝) →
    ([∗ list] k↦x;y ∈ l1;l2, Φ k x y) ⊢ ⌜Forall2 φ l1 l2⌝.
  Proof.
    intros HΦ.
    rewrite Forall2_same_length_lookup -big_sepL2_pure.
    iIntros "H".
    iApply (big_sepL2_impl with "H").
    iIntros "!>" (k x y Hx Hy) "H".
    by iApply HΦ.
  Qed.

  Lemma forall2_flags_of_skinds_val (rs : type → type) (se : semantic_env (Σ:=Σ)) τs ιss ξs oss :
    Forall3 (λ τ ιs ξ, type_skind se τ = Some (SVALTYPE ιs ξ)) (map rs τs) ιss ξs →
    Forall2 (λ τ os, ∃ sκ, type_skind se (rs τ) = Some sκ ∧ skind_has_svalue sκ (SAtoms os)) τs oss →
    Forall2 (λ ξ os, ref_flag_atoms_interp ξ (SAtoms os)) ξs oss.
  Proof.
    intros H3 H2; revert ιss ξs H3.
    induction H2 as [|τ os τs oss (sκ & Hsκ & Hsv) _ IH]; intros ιss ξs H3.
    - inversion H3; subst; constructor.
    - change (map rs (τ :: τs)) with (rs τ :: map rs τs) in H3.
      apply Forall3_cons_inv_l in H3 as (ιs & ιss0 & ξ & ξs0 & -> & -> & Hsκ' & H3).
      rewrite Hsκ' in Hsκ; injection Hsκ as <-.
      constructor; last exact (IH _ _ H3).
      cbn in Hsv; by destruct Hsv.
  Qed.

  Lemma forall2_flags_of_skinds_mem (rs : type → type) (se : semantic_env (Σ:=Σ)) τs ns ξs wss :
    Forall3 (λ τ n ξ, type_skind se τ = Some (SMEMTYPE n ξ)) (map rs τs) ns ξs →
    Forall2 (λ τ ws, ∃ sκ, type_skind se (rs τ) = Some sκ ∧ skind_has_svalue sκ (SWords ws)) τs wss →
    Forall2 (λ ξ ws, ref_flag_words_interp ξ (SWords ws)) ξs wss.
  Proof.
    intros H3 H2; revert ns ξs H3.
    induction H2 as [|τ ws τs wss (sκ & Hsκ & Hsv) _ IH]; intros ns ξs H3.
    - inversion H3; subst; constructor.
    - change (map rs (τ :: τs)) with (rs τ :: map rs τs) in H3.
      apply Forall3_cons_inv_l in H3 as (n & ns0 & ξ & ξs0 & -> & -> & Hsκ' & H3).
      rewrite Hsκ' in Hsκ; injection Hsκ as <-.
      constructor; last exact (IH _ _ H3).
      cbn in Hsv; by destruct Hsv.
  Qed.

  Lemma has_kind_memtype_eval_size_list F (se : semantic_env (Σ:=Σ)) τs σs ξs :
    sem_env_interp F se →
    Forall3 (λ τ σ ξ, has_kind F τ (MEMTYPE σ ξ)) τs σs ξs →
    ∃ ns, mapM (eval_size se) σs = Some ns ∧
          Forall3 (λ τ n ξ, type_skind se τ = Some (SMEMTYPE n ξ)) τs ns ξs.
  Proof.
    intros Henv H1.
    induction H1 as [|τ σ ξ τs σs ξs Hk _ (ns & Hns & IH)].
    - exists []; split; [done|constructor].
    - destruct (has_kind_memtype_eval_size _ _ _ _ _ Henv Hk) as (n & Hn & Hsk).
      exists (n :: ns); split; last by constructor.
      by cbn; rewrite Hn Hns.
  Qed.

  Lemma type_var_interp_subst_skind (se se' : semantic_env (Σ:=Σ)) sub_t i sκ sv :
    (∀ i, type_var_interp i se' ≡ value_interp rti sr se (sub_t i)) →
    type_skind se (sub_t i) = Some sκ →
    type_var_interp i se' sv ⊢ ⌜skind_has_svalue sκ sv⌝.
  Proof.
    intros HT Hsκ.
    rewrite (HT i sv) value_interp_eq; cbn -[skind_has_svalue type_skind].
    iIntros "H".
    iDestruct "H" as (sκ') "(%Hsκ' & %Hsv & _)".
    rewrite Hsκ in Hsκ'; injection Hsκ' as <-.
    done.
  Qed.

  Definition skind_subst_ok (τ : type) : Prop :=
    ∀ F F' sub_m sub_r sub_s sub_t se se' κ κ' sv,
      subst_rel F F' sub_m sub_r sub_s sub_t se se' →
      has_kind F' τ κ →
      has_kind F (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)) κ' →
      type_interp rti sr τ se' sv -∗
      ∃ sκ, ⌜type_skind se (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)) = Some sκ ∧
             skind_has_svalue sκ sv⌝.

  Lemma skind_interp_chillin τ : skind_subst_ok τ.
  Proof.
    induction τ using type_ind with (P0 := const True) (Pi := const True); try done;
      intros F F' sub_m sub_r sub_s sub_t se se' κa κb sv HR Hk Hk';
      pose proof HR as [Henv' Henv Hr Hs Hm Hsκ HT Hgood]; unfold_sem_rels.
    all: try by (eapply skind_interp_same_skind;
                 rewrite (type_skind_has_kind _ _ _ _ Hk' Henv) (type_skind_has_kind _ _ _ _ Hk Henv');
                 inversion Hk'; subst; inversion Hk; subst;
                 rewrite (eval_kind_subst_senv_eq se se' sub_r sub_s); try done; cbn).
    - (* var *)
      iIntros "H".
      iEval (rewrite type_interp_eq) in "H".
      iDestruct "H" as (sκ0) "(%Hsκ0 & _ & H)".
      iEval (cbn -[type_var_interp]) in "H".
      change (type_skind se' (VarT idx)) with (fst <$> lookup_type se' idx) in Hsκ0.
      change (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t (VarT idx)))
        with (refresh_kinds F (sub_t idx)).
      rewrite Hgood.
      specialize (Hsκ idx); rewrite Hsκ0 in Hsκ.
      apply subskind_of_option_invr in Hsκ as (sκ1 & Hsκ1 & _).
      iDestruct (type_var_interp_subst_skind with "H") as %Hsv; [done|done|].
      by iExists sκ1.
    - (* sum *)
      iIntros "H".
      iDestruct (type_interp_skind_svalue with "H") as %(sκ & Hsκ0 & Hsv).
      pose proof (type_skind_refresh_subst _ _ _ _ _ _ _ _ _ _ _ HR Hk Hk') as Hsub.
      rewrite Hsκ0 in Hsub; apply subskind_of_option_invr in Hsub as (sκ' & Hsκ' & Hsub).
      apply has_kind_sum_inv in Hk as (ρs & ξs & -> & -> & H1).
      pose proof Hk' as Hk''; apply has_kind_sum_inv in Hk'' as (ρs' & ξs' & Hκb & Hann & H2).
      rewrite map_map in H2.
      destruct (has_kind_valtype_eval_rep_list _ _ _ _ _ Henv H2) as (ιss' & Hιss' & Hsk').
      pose proof Hsκ' as Hts'.
      rewrite (type_skind_has_kind _ _ _ _ Hk' Henv) Hκb in Hsκ'; cbn in Hsκ'.
      rewrite (mapM_Some_2 _ _ _ Hιss') in Hsκ'; cbn in Hsκ'; injection Hsκ' as <-.
      inversion Hsub; subst.
      iExists (SVALTYPE (I32R :: concat ιss') (ref_flag_lub ξs')).
      rewrite type_interp_eq; cbn -[skind_has_svalue].
      iDestruct "H" as (sκ0 Hsκ0' Hsv0) "(%i & %os & %off & %count & -> & %Hoff & %Hcount & %Hpad & Hi)".
      destruct (τs !! i) as [τi|] eqn:Hτi; last first.
      { iEval (change (list_lookup i (map (type_interp rti sr) τs)) with ((type_interp rti sr <$> τs) !! i);
          rewrite list_lookup_fmap Hτi) in "Hi".
        by iDestruct "Hi" as "[]". }
      iEval (change (list_lookup i (map (type_interp rti sr) τs)) with ((type_interp rti sr <$> τs) !! i);
        rewrite list_lookup_fmap Hτi; cbn) in "Hi".
      destruct (Forall3_lookup_l _ _ _ _ _ _ H1 Hτi) as (ρi & ξi & _ & Hξi & Hkτi).
      destruct (Forall3_lookup_l _ _ _ _ _ _ H2 (map_lookup_helper_forwards _ _ _ _ Hτi))
        as (ρi' & ξi' & _ & Hξi' & Hkτi').
      destruct (Forall3_lookup_l _ _ _ _ _ _ Hsk' (map_lookup_helper_forwards _ _ _ _ Hτi))
        as (ιsi & ξi'' & _ & Hξi'' & Hski).
      rewrite Hξi' in Hξi''; injection Hξi'' as <-.
      iDestruct (Forall_lookup_1 _ _ _ _ H Hτi _ _ _ _ _ _ _ _ _ _ _ HR Hkτi Hkτi' with "Hi")
        as %(sκi & Hsκi & Hsvi).
      rewrite Hski in Hsκi; injection Hsκi as <-.
      iPureIntro; split; first done.
      eapply skind_has_svalue_val_tighten; first exact Hsv.
      apply ref_flag_atoms_interp_cons; split; first done.
      eapply ref_flag_atoms_interp_slice; first exact Hpad.
      eapply ref_flag_atoms_refine; first (apply ref_flag_lub_ub; exact (list_elem_of_lookup_2 _ _ _ Hξi')).
      cbn in Hsvi; by destruct Hsvi.
    - (* variant *)
      iIntros "H".
      iDestruct (type_interp_skind_svalue with "H") as %(sκ & Hsκ0 & Hsv).
      pose proof (type_skind_refresh_subst _ _ _ _ _ _ _ _ _ _ _ HR Hk Hk') as Hsub.
      rewrite Hsκ0 in Hsub; apply subskind_of_option_invr in Hsub as (sκ' & Hsκ' & Hsub).
      apply has_kind_variant_inv in Hk as (σs & ξs & -> & _ & H1).
      pose proof Hk' as Hk''; apply has_kind_variant_inv in Hk'' as (σs' & ξs' & Hκb & Hann & H2).
      rewrite map_map in H2.
      destruct (has_kind_memtype_eval_size_list _ _ _ _ _ Henv H2) as (ns' & Hns' & Hsk').
      pose proof Hsκ' as Hts'.
      rewrite (type_skind_has_kind _ _ _ _ Hk' Henv) Hκb in Hsκ'; cbn in Hsκ'.
      rewrite Hns' in Hsκ'; cbn in Hsκ'; injection Hsκ' as <-.
      inversion Hsub; subst.
      iExists (SMEMTYPE (1 + list_max ns') (ref_flag_lub ξs')).
      rewrite type_interp_eq; cbn -[skind_has_svalue].
      iDestruct "H" as (sκ0 Hsκ0' Hsv0) "(%i & %n & %ws & %ws' & %Hrepr & -> & %Hpad & Hi)".
      destruct (τs !! i) as [τi|] eqn:Hτi; last first.
      { iEval (change (list_lookup i (map (type_interp rti sr) τs)) with ((type_interp rti sr <$> τs) !! i);
          rewrite list_lookup_fmap Hτi) in "Hi".
        by iDestruct "Hi" as "[]". }
      iEval (change (list_lookup i (map (type_interp rti sr) τs)) with ((type_interp rti sr <$> τs) !! i);
        rewrite list_lookup_fmap Hτi; cbn) in "Hi".
      destruct (Forall3_lookup_l _ _ _ _ _ _ H1 Hτi) as (σi & ξi & _ & Hξi & Hkτi).
      destruct (Forall3_lookup_l _ _ _ _ _ _ H2 (map_lookup_helper_forwards _ _ _ _ Hτi))
        as (σi' & ξi' & _ & Hξi' & Hkτi').
      destruct (Forall3_lookup_l _ _ _ _ _ _ Hsk' (map_lookup_helper_forwards _ _ _ _ Hτi))
        as (ni & ξi'' & _ & Hξi'' & Hski).
      rewrite Hξi' in Hξi''; injection Hξi'' as <-.
      iDestruct (Forall_lookup_1 _ _ _ _ H Hτi _ _ _ _ _ _ _ _ _ _ _ HR Hkτi Hkτi' with "Hi")
        as %(sκi & Hsκi & Hsvi).
      rewrite Hski in Hsκi; injection Hsκi as <-.
      iPureIntro; split; first done.
      eapply skind_has_svalue_mem_tighten; first exact Hsv.
      cbn in Hsvi; destruct Hsvi as [_ Hsvi].
      apply ref_flag_words_interp_cons_int, ref_flag_words_interp_app.
      + eapply ref_flag_words_refine; last exact Hsvi.
        apply ref_flag_lub_ub; exact (list_elem_of_lookup_2 _ _ _ Hξi').
      + by eapply (ref_flag_words_refine NoRefs).
    - (* prod *)
      iIntros "H".
      iDestruct (type_interp_skind_svalue with "H") as %(sκ & Hsκ0 & Hsv).
      pose proof (type_skind_refresh_subst _ _ _ _ _ _ _ _ _ _ _ HR Hk Hk') as Hsub.
      rewrite Hsκ0 in Hsub; apply subskind_of_option_invr in Hsub as (sκ' & Hsκ' & Hsub).
      apply has_kind_prod_inv in Hk as (ρs & ξs & -> & _ & H1).
      pose proof Hk' as Hk''; apply has_kind_prod_inv in Hk'' as (ρs' & ξs' & Hκb & Hann & H2).
      rewrite map_map in H2.
      destruct (has_kind_valtype_eval_rep_list _ _ _ _ _ Henv H2) as (ιss' & Hιss' & Hsk').
      pose proof Hsκ' as Hts'.
      rewrite (type_skind_has_kind _ _ _ _ Hk' Henv) Hκb in Hsκ'; cbn in Hsκ'.
      rewrite (mapM_Some_2 _ _ _ Hιss') in Hsκ'; cbn in Hsκ'; injection Hsκ' as <-.
      inversion Hsub; subst.
      iExists (SVALTYPE (concat ιss') (ref_flag_lub ξs')).
      rewrite type_interp_eq; cbn -[skind_has_svalue].
      iDestruct "H" as (sκ0 Hsκ0' Hsv0) "(%oss & -> & H)".
      rewrite big_sepL2_fmap_l.
      iDestruct (big_sepL2_pure_forall2 _
        (λ τ os, ∃ sκ, type_skind se (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)) = Some sκ ∧
                       skind_has_svalue sκ (SAtoms os)) with "H") as %Hall.
      { intros k τk os Hτk Hos.
        destruct (Forall3_lookup_l _ _ _ _ _ _ H1 Hτk) as (ρk & ξk & _ & _ & Hkτk).
        destruct (Forall3_lookup_l _ _ _ _ _ _ H2 (map_lookup_helper_forwards _ _ _ _ Hτk))
          as (ρk' & ξk' & _ & _ & Hkτk').
        iIntros "H".
        iDestruct (Forall_lookup_1 _ _ _ _ H Hτk _ _ _ _ _ _ _ _ _ _ _ HR Hkτk Hkτk' with "H")
          as %(sκk & ? & ?).
        iPureIntro; by exists sκk. }
      iPureIntro; split; first done.
      eapply skind_has_svalue_val_tighten; first exact Hsv.
      apply ref_flag_atoms_interp_concat.
      by eapply forall2_flags_of_skinds_val.
    - (* struct *)
      iIntros "H".
      iDestruct (type_interp_skind_svalue with "H") as %(sκ & Hsκ0 & Hsv).
      pose proof (type_skind_refresh_subst _ _ _ _ _ _ _ _ _ _ _ HR Hk Hk') as Hsub.
      rewrite Hsκ0 in Hsub; apply subskind_of_option_invr in Hsub as (sκ' & Hsκ' & Hsub).
      apply has_kind_struct_inv in Hk as (σs & ξs & -> & _ & H1).
      pose proof Hk' as Hk''; apply has_kind_struct_inv in Hk'' as (σs' & ξs' & Hκb & Hann & H2).
      rewrite map_map in H2.
      destruct (has_kind_memtype_eval_size_list _ _ _ _ _ Henv H2) as (ns' & Hns' & Hsk').
      pose proof Hsκ' as Hts'.
      rewrite (type_skind_has_kind _ _ _ _ Hk' Henv) Hκb in Hsκ'; cbn in Hsκ'.
      rewrite Hns' in Hsκ'; cbn in Hsκ'; injection Hsκ' as <-.
      inversion Hsub; subst.
      iExists (SMEMTYPE (list_sum ns') (ref_flag_lub ξs')).
      rewrite type_interp_eq; cbn -[skind_has_svalue].
      iDestruct "H" as (sκ0 Hsκ0' Hsv0) "(%wss & -> & H)".
      rewrite big_sepL2_flip big_sepL2_fmap_l.
      iDestruct (big_sepL2_pure_forall2 _
        (λ τ ws, ∃ sκ, type_skind se (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)) = Some sκ ∧
                       skind_has_svalue sκ (SWords ws)) with "H") as %Hall.
      { intros k τk ws Hτk Hws.
        destruct (Forall3_lookup_l _ _ _ _ _ _ H1 Hτk) as (σk & ξk & _ & _ & Hkτk).
        destruct (Forall3_lookup_l _ _ _ _ _ _ H2 (map_lookup_helper_forwards _ _ _ _ Hτk))
          as (σk' & ξk' & _ & _ & Hkτk').
        iIntros "H".
        iDestruct (Forall_lookup_1 _ _ _ _ H Hτk _ _ _ _ _ _ _ _ _ _ _ HR Hkτk Hkτk' with "H")
          as %(sκk & ? & ?).
        iPureIntro; by exists sκk. }
      iPureIntro; split; first done.
      eapply skind_has_svalue_mem_tighten; first exact Hsv.
      apply ref_flag_words_interp_concat.
      by eapply forall2_flags_of_skinds_mem.
    - (* ref *)
      inversion Hk; subst.
      2,3: by (eapply skind_interp_same_skind; cbn).
      cbn -[type_skind skind_has_svalue] in Hk' |- *.
      destruct (sub_m m) as [m'|[|]] eqn:Hsm.
      1,2: by (eapply skind_interp_same_skind; cbn).
      iIntros "H".
      rewrite type_interp_eq; cbn -[skind_has_svalue].
      iDestruct "H" as (sκ0 Hsκ0 Hsv0) "H".
      assert (lookup_mem se' m = Some MemGC) as Hmm by (by rewrite (Hm m) Hsm).
      change (se'.1.1.1 !! m) with (lookup_mem se' m).
      rewrite Hmm.
      iExists (SVALTYPE [PtrR] GCRefs).
      destruct β.
      + iDestruct "H" as (ℓ fs) "(-> & _)".
        iPureIntro; split; first done.
        split; [eexists; split; [done|by repeat constructor]|by repeat constructor].
      + iDestruct "H" as (ℓ fs ws) "(-> & _)".
        iPureIntro; split; first done.
        split; [eexists; split; [done|by repeat constructor]|by repeat constructor].
    - (* ser *)
      iIntros "H".
      apply has_kind_ser_inv in Hk as (ρ & ξ & -> & _ & Hk0).
      pose proof Hk' as Hk''; apply has_kind_ser_inv in Hk'' as (ρ' & ξ' & Hκb & Hann & Hk0').
      destruct (has_kind_valtype_eval_rep _ _ _ _ _ Henv Hk0') as (ιs' & Hιs' & Hsk').
      rewrite type_interp_eq; cbn -[skind_has_svalue type_skind].
      iDestruct "H" as (sκ0 Hsκ0 Hsv0) "(%os & -> & H)".
      iDestruct (IHτ _ _ _ _ _ _ _ _ _ _ _ HR Hk0 Hk0' with "H") as %(sκi & Hsκi & Hsvi).
      rewrite Hsk' in Hsκi; injection Hsκi as <-.
      cbn in Hsvi; destruct Hsvi as [Hareps Hflag].
      destruct Hareps as (os' & Heq & Hareps); injection Heq as <-.
      iPureIntro.
      eexists; split.
      { rewrite (type_skind_has_kind _ _ _ _ Hk' Henv) Hκb; cbn.
        by rewrite Hιs'. }
      split; last by apply ref_flag_serialize.
      cbn; unfold compose.
      by rewrite (has_areps_serialize_length _ _ Hareps).
  Qed.

  Lemma skind_interp_chillin_backwards F F' sub_m sub_r sub_s sub_t se se' τ κ κ' sv :
    subst_rel F F' sub_m sub_r sub_s sub_t se se' →
    has_kind F' τ κ →
    has_kind F (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)) κ' →
    type_interp rti sr (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)) se sv -∗
    ∃ sκ, ⌜type_skind se' τ = Some sκ ∧ skind_has_svalue sκ sv⌝.
  Proof.
    intros HR Hk Hk'.
    pose proof (type_skind_refresh_subst _ _ _ _ _ _ _ _ _ _ _ HR Hk Hk') as Hsub.
    iIntros "H".
    iDestruct (type_interp_skind_svalue with "H") as %(sκ' & Hsκ' & Hsv).
    rewrite Hsκ' in Hsub; apply subskind_of_option_invl in Hsub as (sκ & Hsκ & Hsub).
    iExists sκ; iPureIntro; split; first done.
    by eapply skind_as_type_refine.
  Qed.

  Lemma peel_off_add_skind_interp F F' sub_m sub_r sub_s sub_t se se' τ κ κ' sv :
    subst_rel F F' sub_m sub_r sub_s sub_t se se' →
    has_kind F' τ κ →
    has_kind F (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)) κ' →
    (pre_type_interp rti sr τ se' sv ∗-∗
     pre_type_interp rti sr (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)) se sv) →
    type_interp rti sr τ se' sv ∗-∗
    type_interp rti sr (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)) se sv.
  Proof.
    intros HR Hk Hk' Hequiv.
    iSplit; iIntros "H".
    - iDestruct (skind_interp_chillin τ _ _ _ _ _ _ _ _ _ _ sv HR Hk Hk' with "H") as %(sκ & Hsκ & Hsv).
      rewrite !type_interp_eq; cbn -[type_skind].
      iDestruct "H" as (sκ0) "(_ & _ & H)".
      iExists sκ; do 2 (iSplit; first done).
      by iApply Hequiv.
    - iDestruct (skind_interp_chillin_backwards _ _ _ _ _ _ _ _ _ _ _ sv HR Hk Hk' with "H")
        as %(sκ & Hsκ & Hsv).
      rewrite !type_interp_eq; cbn -[type_skind].
      iDestruct "H" as (sκ0) "(_ & _ & H)".
      iExists sκ; do 2 (iSplit; first done).
      by iApply Hequiv.
  Qed.

  Lemma sum_interp_equiv ρs ρs' ξ ξ' Ts Ts' (se se' : semantic_env (Σ:=Σ)) :
    Forall2 (λ ρ ρ', eval_rep se ρ = eval_rep se' ρ') ρs ρs' →
    Forall2 (λ T T' : semantic_type, T se ≡ T' se') Ts Ts' →
    sum_interp (VALTYPE (SumR ρs) ξ) Ts se ≡ sum_interp (VALTYPE (SumR ρs') ξ') Ts' se'.
  Proof.
    intros Hρ HF sv; cbn.
    f_equiv; intros i.
    do 3 (f_equiv; intros ?).
    unfold sum_offset.
    rewrite (Forall2_mapM_ext _ _ _ _ (Forall2_take _ _ _ i Hρ)).
    pose proof (proj1 (Forall2_lookup _ _ _) Hρ i) as Hl.
    inversion Hl as [ρ ρ' Hρρ' Hl1 Hl2|Hl1 Hl2]; cbn; [rewrite Hρρ'|].
    all: repeat (f_equiv; try done).
    all: apply lookup_interp_ren, HF.
  Qed.

  Lemma ref_interp_equiv μ μ' β (T T' : semantic_type) (se se' : semantic_env (Σ:=Σ)) :
    eval_mem se μ = eval_mem se' μ' →
    T se ≡ T' se' →
    ref_interp μ β T se ≡ ref_interp μ' β T' se'.
  Proof.
    intros Hμ HT.
    cbn -[ref_mm_mut_interp ref_mm_imm_interp ref_gc_mut_interp ref_gc_imm_interp].
    rewrite <- Hμ.
    destruct (eval_mem se μ) as [[|]|], β; try done.
    all: intros sv; cbn.
    all: do 2 (f_equiv; intros ?).
    all: repeat (f_equiv; try (intros ?); try done).
  Qed.

  Lemma skind_rec_interp_equiv sκ (T T' : semantic_type) (se se' : semantic_env (Σ:=Σ)) :
    (∀ X, skind_has_stype sκ X →
          T (senv_insert_type sκ sκ X se) ≡ T' (senv_insert_type sκ sκ X se')) →
    skind_has_stype sκ (add_skind_interp_closed sκ (skind_rec_interp sκ T se)) →
    skind_rec_interp sκ T se ≡ skind_rec_interp sκ T' se'.
  Proof.
    intros HT Hst.
    apply fixpoint_unique; intros sv.
    rewrite (skind_rec_interp_unfold sκ T se sv); cbn.
    f_equiv.
    by apply HT.
  Qed.

  Lemma rec_interp_equiv κ κ' (T T' : semantic_type) (se se' : semantic_env (Σ:=Σ)) :
    eval_kind se κ = eval_kind se' κ' →
    (∀ sκ X, eval_kind se κ = Some sκ → skind_has_stype sκ X →
             T (senv_insert_type sκ sκ X se) ≡ T' (senv_insert_type sκ sκ X se')) →
    (∀ sκ, eval_kind se κ = Some sκ →
           skind_has_stype sκ (add_skind_interp_closed sκ (skind_rec_interp sκ T se))) →
    rec_interp κ T se ≡ rec_interp κ' T' se'.
  Proof.
    intros Hκ HT Hst.
    cbn -[skind_rec_interp]; rewrite <- Hκ.
    destruct (eval_kind se κ) as [sκ|] eqn:Hsκ; [|done].
    apply skind_rec_interp_equiv; [intros X HX; apply (HT sκ X); [by rewrite ?Hsκ|exact HX]|apply (Hst sκ); by rewrite ?Hsκ].
  Qed.

  Lemma exists_type_interp_equiv κ κ' (T T' : semantic_type) (se se' : semantic_env (Σ:=Σ)) :
    eval_kind se κ = eval_kind se' κ' →
    (∀ sκ sκ_T X, eval_kind se κ = Some sκ → subskind_of sκ_T sκ → skind_has_stype sκ_T X →
                  T (senv_insert_type sκ sκ_T X se) ≡ T' (senv_insert_type sκ sκ_T X se')) →
    exists_type_interp κ T se ≡ exists_type_interp κ' T' se'.
  Proof.
    intros Hκ HT sv; cbn -[senv_insert_type].
    rewrite <- Hκ.
    f_equiv; intros X.
    f_equiv; intros sκ.
    f_equiv; intros sκ_T.
    iSplit; iIntros "(%H1 & %H2 & %H3 & H)"; do 3 (iSplit; first done).
    - by rewrite (HT _ _ _ H1 H2 H3 sv).
    - by rewrite <- (HT _ _ _ H1 H2 H3 sv).
  Qed.

  Lemma forall_type_interp_equiv κ κ' (FT FT' : semantic_env -n> ClR) (se se' : semantic_env (Σ:=Σ)) :
    eval_kind se κ = eval_kind se' κ' →
    (∀ sκ sκ_T X, eval_kind se κ = Some sκ → subskind_of sκ_T sκ → skind_has_stype sκ_T X →
                  FT (senv_insert_type sκ sκ_T X se) ≡ FT' (senv_insert_type sκ sκ_T X se')) →
    forall_type_interp κ FT se ≡ forall_type_interp κ' FT' se'.
  Proof.
    intros Hκ HFT cl; cbn -[senv_insert_type].
    change (eval_kind_se se κ) with (eval_kind se κ).
    change (eval_kind_se se' κ') with (eval_kind se' κ').
    rewrite <- Hκ.
    f_equiv.
    f_equiv; intros sκ.
    f_equiv; intros sκ_T.
    f_equiv; intros X.
    iSplit; iIntros "H %H1 %H2 %H3".
    - rewrite <- (HFT _ _ _ H1 H2 H3 cl); by iApply "H".
    - rewrite (HFT _ _ _ H1 H2 H3 cl); by iApply "H".
  Qed.

  Lemma mono_closure_interp_equiv τs1 τs2 τs1' τs2' Ts1 Ts2 Ts1' Ts2' (se se' : semantic_env (Σ:=Σ)) :
    translate_types se τs1 = translate_types se' τs1' →
    translate_types se τs2 = translate_types se' τs2' →
    Forall2 (λ T T' : semantic_type, T se ≡ T' se') Ts1 Ts1' →
    Forall2 (λ T T' : semantic_type, T se ≡ T' se') Ts2 Ts2' →
    mono_closure_interp rti sr τs1 τs2 Ts1 Ts2 se ≡
    mono_closure_interp rti sr τs1' τs2' Ts1' Ts2' se'.
  Proof.
    intros Ht1 Ht2 HF1 HF2 cl.
    destruct cl as [inst [ts1 ts2] tlocs es|]; [|done].
    cbn -[values_interp1 atoms_interp translate_types].
    rewrite <- Ht1, <- Ht2.
    pose proof (values_interp1_ren _ _ _ _ HF1) as HV1.
    pose proof (values_interp1_ren _ _ _ _ HF2) as HV2.
    pose (oΦ1 := (λne vs2, (∃ os2, atoms_interp os2 vs2 ∗ values_interp1 Ts2 se os2) ∗
                           (∃ θ', rt_token rti sr lpall θ') ∗ na_own logrel_nais ⊤)%I).
    pose (oΦ2 := (λne vs2, (∃ os2, atoms_interp os2 vs2 ∗ values_interp1 Ts2' se' os2) ∗
                           (∃ θ', rt_token rti sr lpall θ') ∗ na_own logrel_nais ⊤)%I).
    assert (HΦs : oΦ1 ≡ oΦ2).
    { intros vs2; cbn -[values_interp1 atoms_interp].
      f_equiv.
      f_equiv; intros os2.
      f_equiv.
      exact (HV2 os2). }
    assert (HΦs' : (λne _ : leibnizO frame, oΦ1) ≡ (λne _, oΦ2)) by (intros ?; exact HΦs).
    pose (oL1 := [(length ts2, λne _, oΦ1)] : label_ctxO).
    pose (oL2 := [(length ts2, λne _, oΦ2)] : label_ctxO).
    assert (HLs : oL1 ≡ oL2) by (constructor; [split; [done|exact HΦs']|constructor]).
    pose (oR1 := Some (length ts2, oΦ1) : return_ctxO).
    pose (oR2 := Some (length ts2, oΦ2) : return_ctxO).
    assert (HRs : oR1 ≡ oR2) by (constructor; split; [done|exact HΦs]).
    do 2 (f_equiv; try done).
    do 9 f_equiv.
    f_equiv; first exact (HV1 _).
    do 4 f_equiv.
    apply (cwp_wasm_equiv es oL1 oL2 oR1 oR2 (λne _, oΦ1) (λne _, oΦ2) HLs HRs HΦs').
  Qed.

  Lemma skind_has_stype_proper sκ (T T' : leibnizO semantic_value -n> iPropO Σ) :
    T ≡ T' →
    skind_has_stype sκ T' →
    skind_has_stype sκ T.
  Proof.
    intros Heq [Href Hval].
    split.
    - unfold ref_flag_stype_interp in *.
      destruct (skind_ref_flag sκ); try done.
      all: intros sv; by rewrite (Heq sv).
    - intros sv.
      by rewrite (Heq sv).
  Qed.

  Global Instance skind_has_stype_proper_instance sκ :
  Proper (equiv ==> flip impl) (skind_has_stype (Σ:=Σ) sκ).
  Proof.
    intros T T' Heq HT'.
    eapply skind_has_stype_proper; [exact Heq | exact HT'].
  Qed.

  Lemma rec_closed_equiv_value_interp sκ κ τ (se : semantic_env (Σ:=Σ)) :
    eval_kind se κ = Some sκ →
    add_skind_interp_closed sκ (skind_rec_interp sκ (type_interp rti sr τ) se) ≡
    value_interp rti sr se (RecT κ τ).
  Proof.
    intros Hκ sv.
    rewrite value_interp_eq; cbn -[skind_rec_interp skind_has_svalue].
    rewrite Hκ.
    iSplit.
    - iIntros "(% & H)"; iExists sκ; by iFrame.
    - iIntros "(%sκ0 & %Heq & %Hsv & H)"; injection Heq as <-; by iFrame.
  Qed.

  Lemma has_kind_rec_inv F κ τ κ' :
    has_kind F (RecT κ τ) κ' → κ' = κ ∧ has_kind (F <| fc_type_vars ::= cons κ |>) τ κ.
  Proof. by inversion 1; subst. Qed.

  Lemma has_kind_existsmem_inv F κ τ κ' :
    has_kind F (ExistsMemT κ τ) κ' →
    κ' = κ ∧ has_kind (F <| fc_kind_ctx ::= set kc_mem_vars S |>) τ κ.
  Proof. by inversion 1; subst. Qed.

  Lemma has_kind_existsrep_inv F κ τ κ' :
    has_kind F (ExistsRepT κ τ) κ' →
    κ' = κ ∧ has_kind (add_rep_var F) τ (ren_kind unscoped.shift unscoped.id κ).
  Proof. by inversion 1; subst. Qed.

  Lemma has_kind_existssize_inv F κ τ κ' :
    has_kind F (ExistsSizeT κ τ) κ' →
    κ' = κ ∧ has_kind (add_size_var F) τ (ren_kind unscoped.id unscoped.shift κ).
  Proof. by inversion 1; subst. Qed.

  Lemma has_kind_existstype_inv F κ κ0 τ κ' :
    has_kind F (ExistsTypeT κ κ0 τ) κ' →
    κ' = κ ∧ has_kind (F <| fc_type_vars ::= cons κ0 |>) τ κ.
  Proof. by inversion 1; subst. Qed.

  Lemma has_kind_coderef_inv F κ ϕ κ' :
    has_kind F (CodeRefT κ ϕ) κ' → has_kind_ft F ϕ.
  Proof. by inversion 1; subst. Qed.

  Lemma has_kind_ift_mono_inv F τs1 τs2 :
    has_kind_ift F (MonoFunT τs1 τs2) →
    ∃ κs1 κs2, Forall2 (has_kind F) τs1 κs1 ∧ Forall2 (has_kind F) τs2 κs2.
  Proof. inversion 1; subst; eauto. Qed.

  Lemma has_kind_ift_foralltype_inv F κ ϕ :
    has_kind_ift F (ForallTypeT κ ϕ) →
    kind_ok F.(fc_kind_ctx) κ ∧ has_kind_ift (F <| fc_type_vars ::= cons κ |>) ϕ.
  Proof. by inversion 1; subst. Qed.

  Lemma has_kind_ft_inner_inv F ϕ :
    has_kind_ft F (InnerFunT ϕ) → has_kind_ift F ϕ.
  Proof. by inversion 1; subst. Qed.

  Lemma has_kind_ft_forallmem_inv F ϕ :
    has_kind_ft F (ForallMemT ϕ) → has_kind_ft (F <| fc_kind_ctx ::= set kc_mem_vars S |>) ϕ.
  Proof. by inversion 1; subst. Qed.

  Lemma has_kind_ft_forallrep_inv F ϕ :
    has_kind_ft F (ForallRepT ϕ) → has_kind_ft (add_rep_var F) ϕ.
  Proof. by inversion 1; subst. Qed.

  Lemma has_kind_ft_forallsize_inv F ϕ :
    has_kind_ft F (ForallSizeT ϕ) → has_kind_ft (add_size_var F) ϕ.
  Proof. by inversion 1; subst. Qed.

  Lemma kinds_of_forall3_val F F' (rs : type → type) τs ρs ξs ρs' ξs' :
    Forall3 (λ τ ρ ξ, has_kind F' τ (VALTYPE ρ ξ)) τs ρs ξs →
    Forall3 (λ τ ρ ξ, has_kind F τ (VALTYPE ρ ξ)) (map rs τs) ρs' ξs' →
    ∀ i τ, τs !! i = Some τ → ∃ κ κ', has_kind F' τ κ ∧ has_kind F (rs τ) κ'.
  Proof.
    intros H1 H2 i τ Hi.
    destruct (Forall3_lookup_l _ _ _ _ _ _ H1 Hi) as (ρ & ξ & _ & _ & Hk).
    destruct (Forall3_lookup_l _ _ _ _ _ _ H2 (map_lookup_helper_forwards _ _ _ _ Hi))
      as (ρ' & ξ' & _ & _ & Hk').
    eauto.
  Qed.

  Lemma kinds_of_forall3_mem F F' (rs : type → type) τs σs ξs σs' ξs' :
    Forall3 (λ τ σ ξ, has_kind F' τ (MEMTYPE σ ξ)) τs σs ξs →
    Forall3 (λ τ σ ξ, has_kind F τ (MEMTYPE σ ξ)) (map rs τs) σs' ξs' →
    ∀ i τ, τs !! i = Some τ → ∃ κ κ', has_kind F' τ κ ∧ has_kind F (rs τ) κ'.
  Proof.
    intros H1 H2 i τ Hi.
    destruct (Forall3_lookup_l _ _ _ _ _ _ H1 Hi) as (σ & ξ & _ & _ & Hk).
    destruct (Forall3_lookup_l _ _ _ _ _ _ H2 (map_lookup_helper_forwards _ _ _ _ Hi))
      as (σ' & ξ' & _ & _ & Hk').
    eauto.
  Qed.

  Lemma kinds_of_forall2 F F' (rs : type → type) τs κs κs' :
    Forall2 (has_kind F') τs κs →
    Forall2 (has_kind F) (map rs τs) κs' →
    ∀ i τ, τs !! i = Some τ → ∃ κ κ', has_kind F' τ κ ∧ has_kind F (rs τ) κ'.
  Proof.
    intros H1 H2 i τ Hi.
    destruct (Forall2_lookup_l _ _ _ _ _ H1 Hi) as (κ & _ & Hk).
    destruct (Forall2_lookup_l _ _ _ _ _ H2 (map_lookup_helper_forwards _ _ _ _ Hi)) as (κ' & _ & Hk').
    eauto.
  Qed.

  Definition type_subst_ok (τ : type) : Prop :=
    ∀ F F' sub_m sub_r sub_s sub_t se se' κ κ' sv,
      subst_rel F F' sub_m sub_r sub_s sub_t se se' →
      has_kind F' τ κ →
      has_kind F (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)) κ' →
      type_interp rti sr τ se' sv ∗-∗
      type_interp rti sr (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)) se sv.

  Definition function_type_subst_ok (ϕ : Core.function_type) : Prop :=
    ∀ F F' sub_m sub_r sub_s sub_t se se' cl,
      subst_rel F F' sub_m sub_r sub_s sub_t se se' →
      has_kind_ft F' ϕ →
      has_kind_ft F (refresh_kinds_ft F (subst_function_type sub_m sub_r sub_s sub_t ϕ)) →
      closure_interp rti sr ϕ se' cl ∗-∗
      closure_interp rti sr (refresh_kinds_ft F (subst_function_type sub_m sub_r sub_s sub_t ϕ)) se cl.

  Definition inner_function_type_subst_ok (ϕ : inner_function_type) : Prop :=
    ∀ F F' sub_m sub_r sub_s sub_t se se' cl,
      subst_rel F F' sub_m sub_r sub_s sub_t se se' →
      has_kind_ift F' ϕ →
      has_kind_ift F (refresh_kinds_ift F (subst_inner_function_type sub_m sub_r sub_s sub_t ϕ)) →
      inner_closure_interp rti sr ϕ se' cl ∗-∗
      inner_closure_interp rti sr
        (refresh_kinds_ift F (subst_inner_function_type sub_m sub_r sub_s sub_t ϕ)) se cl.

  Lemma type_subst_ok_equiv τ F F' sub_m sub_r sub_s sub_t se se' κ κ' :
    type_subst_ok τ →
    subst_rel F F' sub_m sub_r sub_s sub_t se se' →
    has_kind F' τ κ →
    has_kind F (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)) κ' →
    type_interp rti sr τ se' ≡
    type_interp rti sr (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)) se.
  Proof.
    intros IH HR Hk Hk' sv; iStartProof.
    iPoseProof (IH _ _ _ _ _ _ _ _ _ _ sv HR Hk Hk') as "H"; iExact "H".
  Qed.

  Lemma function_type_subst_ok_equiv ϕ F F' sub_m sub_r sub_s sub_t se se' :
    function_type_subst_ok ϕ →
    subst_rel F F' sub_m sub_r sub_s sub_t se se' →
    has_kind_ft F' ϕ →
    has_kind_ft F (refresh_kinds_ft F (subst_function_type sub_m sub_r sub_s sub_t ϕ)) →
    closure_interp rti sr ϕ se' ≡
    closure_interp rti sr (refresh_kinds_ft F (subst_function_type sub_m sub_r sub_s sub_t ϕ)) se.
  Proof.
    intros IH HR Hk Hk' cl; iStartProof.
    iPoseProof (IH _ _ _ _ _ _ _ _ cl HR Hk Hk') as "H"; iExact "H".
  Qed.

  Lemma inner_function_type_subst_ok_equiv ϕ F F' sub_m sub_r sub_s sub_t se se' :
    inner_function_type_subst_ok ϕ →
    subst_rel F F' sub_m sub_r sub_s sub_t se se' →
    has_kind_ift F' ϕ →
    has_kind_ift F (refresh_kinds_ift F (subst_inner_function_type sub_m sub_r sub_s sub_t ϕ)) →
    inner_closure_interp rti sr ϕ se' ≡
    inner_closure_interp rti sr
      (refresh_kinds_ift F (subst_inner_function_type sub_m sub_r sub_s sub_t ϕ)) se.
  Proof.
    intros IH HR Hk Hk' cl; iStartProof.
    iPoseProof (IH _ _ _ _ _ _ _ _ cl HR Hk Hk') as "H"; iExact "H".
  Qed.

  Lemma map_type_interp_subst F F' sub_m sub_r sub_s sub_t se se' τs :
    subst_rel F F' sub_m sub_r sub_s sub_t se se' →
    Forall type_subst_ok τs →
    (∀ i τ, τs !! i = Some τ →
            ∃ κ κ', has_kind F' τ κ ∧ has_kind F (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)) κ') →
    Forall2 (λ T T' : semantic_type, T se' ≡ T' se)
      (map (type_interp rti sr) τs)
      (map (type_interp rti sr) (map (refresh_kinds F) (map (subst_type sub_m sub_r sub_s sub_t) τs))).
  Proof.
    intros HR HIH Hk.
    rewrite !map_fmap.
    apply Forall2_fmap, Forall2_fmap_r, Forall2_fmap_r, Forall_Forall2_diag, Forall_lookup_2.
    intros i τ Hi.
    destruct (Hk i τ Hi) as (κ & κ' & Hκ & Hκ').
    exact (type_subst_ok_equiv _ _ _ _ _ _ _ _ _ _ _ (Forall_lookup_1 _ _ _ _ HIH Hi) HR Hκ Hκ').
  Qed.

  Lemma refresh_subst_rec_stype F F' sub_m sub_r sub_s sub_t se se' κ τ sκ :
    subst_rel F F' sub_m sub_r sub_s sub_t se se' →
    has_kind F' (RecT κ τ) κ →
    eval_kind se' κ = Some sκ →
    skind_has_stype sκ (add_skind_interp_closed sκ (skind_rec_interp sκ (type_interp rti sr τ) se')).
  Proof.
    intros HR Hk Hsκ.
    rewrite (rec_closed_equiv_value_interp _ _ _ _ Hsκ).
    by eapply kinding_sound; [|apply HR|].
  Qed.

  Ltac subst_case_intro :=
    intros F F' sub_m sub_r sub_s sub_t se se' κ κ' sv HR Hk Hk';
    pose proof HR as [HseF' HseF Hsub_r Hsub_s Hsub_m Hsub_sκ Hsub_T Hsub_t_good]; unfold_sem_rels.

  Ltac peel := eapply peel_off_add_skind_interp; [done|done|done|]; cbn_interp; apply bi.equiv_wand_iff.

  Lemma type_interp_subst :
    (∀ τ, type_subst_ok τ) ∧ (∀ ϕ, function_type_subst_ok ϕ) ∧ (∀ ϕ, inner_function_type_subst_ok ϕ).
  Proof.
    apply type_and_function_ind.
    - (* var *)
      intros idx; subst_case_intro.
      pose proof (Hsub_T idx sv) as Hv.
      Transparent value_interp. unfold value_interp in Hv. Opaque value_interp.
      cbn -[type_var_interp] in Hv.
      iSplit; iIntros "H".
      + iEval (rewrite type_interp_eq; cbn -[type_var_interp]) in "H".
        iDestruct "H" as (sκ0) "(_ & _ & H)".
        cbn; rewrite Hsub_t_good.
        rewrite <- Hv.
        iExact "H".
      + iDestruct (skind_interp_chillin_backwards _ _ _ _ _ _ _ _ _ _ _ sv HR Hk Hk' with "H")
          as %(sκ0 & Hsκ0 & Hsv).
        cbn in Hsκ0 |- *; rewrite Hsub_t_good.
        iEval (rewrite <- Hv) in "H".
        rewrite type_interp_eq; cbn -[type_var_interp skind_has_svalue].
        iExists sκ0; iFrame.
        by iPureIntro.
    - (* i31 *)
      intros κ0; subst_case_intro.
      peel; by intros; cbn.
    - (* num *)
      intros κ0 nt; subst_case_intro.
      peel; by intros; cbn.
    - (* sum *)
      intros κ0 τs IH; subst_case_intro.
      pose proof (has_kind_sum_inv _ _ _ _ Hk) as (ρs & ξs & -> & -> & H1).
      pose proof (has_kind_sum_inv _ _ _ _ Hk') as (ρs' & ξs' & Hκ' & Hann & H2).
      rewrite map_map in H2.
      destruct (refresh_children_val (λ τ, refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ))
                  _ _ _ _ _ _ _ _ _ HseF' HseF
                  (Forall_true _ _ (λ τ κa κb, type_skind_refresh_subst _ _ _ _ _ _ _ _ τ κa κb HR)) H1 H2)
        as [Hρ _].
      peel.
      rewrite Hann Hκ'.
      exact (sum_interp_equiv _ _ _ _ _ _ _ _ Hρ
               (map_type_interp_subst _ _ _ _ _ _ _ _ _ HR IH (kinds_of_forall3_val _ _ _ _ _ _ _ _ H1 H2)) sv).
    - (* variant *)
      intros κ0 τs IH; subst_case_intro.
      pose proof (has_kind_variant_inv _ _ _ _ Hk) as (σs & ξs & -> & -> & H1).
      pose proof (has_kind_variant_inv _ _ _ _ Hk') as (σs' & ξs' & Hκ' & Hann & H2).
      rewrite map_map in H2.
      peel.
      exact (variant_interp_ren _ _ _ _
               (map_type_interp_subst _ _ _ _ _ _ _ _ _ HR IH (kinds_of_forall3_mem _ _ _ _ _ _ _ _ H1 H2)) sv).
    - (* prod *)
      intros κ0 τs IH; subst_case_intro.
      pose proof (has_kind_prod_inv _ _ _ _ Hk) as (ρs & ξs & -> & -> & H1).
      pose proof (has_kind_prod_inv _ _ _ _ Hk') as (ρs' & ξs' & Hκ' & Hann & H2).
      rewrite map_map in H2.
      peel.
      exact (prod_interp_ren _ _ _ _
               (map_type_interp_subst _ _ _ _ _ _ _ _ _ HR IH (kinds_of_forall3_val _ _ _ _ _ _ _ _ H1 H2)) sv).
    - (* struct *)
      intros κ0 τs IH; subst_case_intro.
      pose proof (has_kind_struct_inv _ _ _ _ Hk) as (σs & ξs & -> & -> & H1).
      pose proof (has_kind_struct_inv _ _ _ _ Hk') as (σs' & ξs' & Hκ' & Hann & H2).
      rewrite map_map in H2.
      peel.
      exact (struct_interp_ren _ _ _ _
               (map_type_interp_subst _ _ _ _ _ _ _ _ _ HR IH (kinds_of_forall3_mem _ _ _ _ _ _ _ _ H1 H2)) sv).
    - (* ref *)
      intros κ0 μ β τ0 IH; subst_case_intro.
      destruct (has_kind_ref_ty _ _ _ _ _ _ Hk) as (σ & ξ & Hk0).
      destruct (has_kind_ref_ty _ _ _ _ _ _ Hk') as (σ' & ξ' & Hk0').
      peel.
      exact (ref_interp_equiv _ _ _ _ _ _ _ (eval_mem_subst_senv_eq _ _ _ _ Hsub_m)
               (type_subst_ok_equiv _ _ _ _ _ _ _ _ _ _ _ IH HR Hk0 Hk0') sv).
    - (* coderef *)
      intros κ0 ϕ IH; subst_case_intro.
      apply has_kind_coderef_inv in Hk as Hkϕ.
      apply has_kind_coderef_inv in Hk' as Hkϕ'.
      peel.
      exact (coderef_interp_ren _ _ _ _ (function_type_subst_ok_equiv _ _ _ _ _ _ _ _ _ IH HR Hkϕ Hkϕ') sv).
    - (* ser *)
      intros κ0 τ0 IH; subst_case_intro.
      pose proof (has_kind_ser_inv _ _ _ _ Hk) as (ρ & ξ & -> & -> & Hk0).
      pose proof (has_kind_ser_inv _ _ _ _ Hk') as (ρ' & ξ' & Hκ' & Hann & Hk0').
      peel.
      exact (ser_interp_ren _ _ _ _ (type_subst_ok_equiv _ _ _ _ _ _ _ _ _ _ _ IH HR Hk0 Hk0') sv).
    - (* plug *)
      intros κ0 ρ; subst_case_intro.
      peel; by intros; cbn.
    - (* span *)
      intros κ0 σ; subst_case_intro.
      peel; by intros; cbn.
    - (* rec *)
      intros κ0 τ0 IH; subst_case_intro.
      pose proof (has_kind_rec_inv _ _ _ _ Hk) as [-> Hk0].
      pose proof (has_kind_rec_inv _ _ _ _ Hk') as [-> Hk0'].
      peel.
      refine (rec_interp_equiv _ _ _ _ _ _ (eval_kind_subst_senv_eq _ _ _ _ _ Hsub_r Hsub_s) _ _ sv).
      + intros sκ X Hsκ HX.
        apply (type_subst_ok_equiv _ _ _ _ _ _ _ _ _ _ _ IH
                 (subst_rel_insert_type _ _ _ _ _ _ _ _ _ _ _ _ HR Hsκ (subskind_of_refl _) HX) Hk0 Hk0').
      + intros sκ Hsκ.
        by eapply refresh_subst_rec_stype.
    - (* exists mem *)
      intros κ0 τ0 IH; subst_case_intro.
      pose proof (has_kind_existsmem_inv _ _ _ _ Hk) as [-> Hk0].
      pose proof (has_kind_existsmem_inv _ _ _ _ Hk') as [-> Hk0'].
      peel.
      refine (exists_mem_interp_ren _ _ _ _ _ sv); intros μ.
      exact (type_subst_ok_equiv _ _ _ _ _ _ _ _ _ _ _ IH (subst_rel_insert_mem _ _ _ _ _ _ _ _ μ HR) Hk0 Hk0').
    - (* exists rep *)
      intros κ0 τ0 IH; subst_case_intro.
      pose proof (has_kind_existsrep_inv _ _ _ _ Hk) as [-> Hk0].
      pose proof (has_kind_existsrep_inv _ _ _ _ Hk') as [-> Hk0'].
      peel.
      refine (exists_rep_interp_ren _ _ _ _ _ sv); intros ιs.
      exact (type_subst_ok_equiv _ _ _ _ _ _ _ _ _ _ _ IH (subst_rel_insert_rep _ _ _ _ _ _ _ _ ιs HR) Hk0 Hk0').
    - (* exists size *)
      intros κ0 τ0 IH; subst_case_intro.
      pose proof (has_kind_existssize_inv _ _ _ _ Hk) as [-> Hk0].
      pose proof (has_kind_existssize_inv _ _ _ _ Hk') as [-> Hk0'].
      peel.
      refine (exists_size_interp_ren _ _ _ _ _ sv); intros n.
      exact (type_subst_ok_equiv _ _ _ _ _ _ _ _ _ _ _ IH (subst_rel_insert_size _ _ _ _ _ _ _ _ n HR) Hk0 Hk0').
    - (* exists type *)
      intros κ0 κ1 τ0 IH; subst_case_intro.
      pose proof (has_kind_existstype_inv _ _ _ _ _ Hk) as [-> Hk0].
      pose proof (has_kind_existstype_inv _ _ _ _ _ Hk') as [-> Hk0'].
      peel.
      refine (exists_type_interp_equiv _ _ _ _ _ _ (eval_kind_subst_senv_eq _ _ _ _ _ Hsub_r Hsub_s) _ sv).
      intros sκ sκ_T X Hsκ Hsub HX.
      exact (type_subst_ok_equiv _ _ _ _ _ _ _ _ _ _ _ IH
               (subst_rel_insert_type _ _ _ _ _ _ _ _ _ _ _ _ HR Hsκ Hsub HX) Hk0 Hk0').
    - (* mono fun *)
      intros τs1 τs2 IH1 IH2 F F' sub_m sub_r sub_s sub_t se se' cl HR Hk Hk'.
      pose proof (has_kind_ift_mono_inv _ _ _ Hk) as (κs1 & κs2 & Hk1 & Hk2).
      pose proof (has_kind_ift_mono_inv _ _ _ Hk') as (κs1' & κs2' & Hk1' & Hk2').
      rewrite !inner_closure_interp_eq; cbn_interp.
      apply bi.equiv_wand_iff.
      pose proof Hk1' as Hk1m; pose proof Hk2' as Hk2m.
      rewrite !map_map in Hk1m Hk2m.
      exact (mono_closure_interp_equiv _ _ _ _ _ _ _ _ _ _
               (translate_types_refresh_subst _ _ _ _ _ _ _ _ _ _ _ HR Hk1 Hk1')
               (translate_types_refresh_subst _ _ _ _ _ _ _ _ _ _ _ HR Hk2 Hk2')
               (map_type_interp_subst _ _ _ _ _ _ _ _ _ HR IH1 (kinds_of_forall2 _ _ _ _ _ _ Hk1 Hk1m))
               (map_type_interp_subst _ _ _ _ _ _ _ _ _ HR IH2 (kinds_of_forall2 _ _ _ _ _ _ Hk2 Hk2m)) cl).
    - (* forall type *)
      intros κ0 ϕ IH F F' sub_m sub_r sub_s sub_t se se' cl HR Hk Hk'.
      pose proof HR as [HseF' HseF Hsub_r Hsub_s Hsub_m Hsub_sκ Hsub_T Hsub_t_good].
      pose proof (has_kind_ift_foralltype_inv _ _ _ Hk) as [_ Hk0].
      pose proof (has_kind_ift_foralltype_inv _ _ _ Hk') as [_ Hk0'].
      rewrite !inner_closure_interp_eq; cbn_interp.
      apply bi.equiv_wand_iff.
      refine (forall_type_interp_equiv _ _ _ _ _ _ (eval_kind_subst_senv_eq _ _ _ _ _ Hsub_r Hsub_s) _ cl).
      intros sκ sκ_T X Hsκ Hsub HX.
      exact (inner_function_type_subst_ok_equiv _ _ _ _ _ _ _ _ _ IH
               (subst_rel_insert_type _ _ _ _ _ _ _ _ _ _ _ _ HR Hsκ Hsub HX) Hk0 Hk0').
    - (* inner fun *)
      intros ϕ IH F F' sub_m sub_r sub_s sub_t se se' cl HR Hk Hk'.
      apply has_kind_ft_inner_inv in Hk as Hk0.
      apply has_kind_ft_inner_inv in Hk' as Hk0'.
      rewrite !closure_interp_eq; cbn_interp.
      rewrite <- !inner_closure_interp_eq.
      exact (IH _ _ _ _ _ _ _ _ cl HR Hk0 Hk0').
    - (* forall mem *)
      intros ϕ IH F F' sub_m sub_r sub_s sub_t se se' cl HR Hk Hk'.
      apply has_kind_ft_forallmem_inv in Hk as Hk0.
      apply has_kind_ft_forallmem_inv in Hk' as Hk0'.
      rewrite !closure_interp_eq; cbn_interp.
      apply bi.equiv_wand_iff.
      refine (forall_mem_interp_ren _ _ _ _ _ cl); intros μ.
      exact (function_type_subst_ok_equiv _ _ _ _ _ _ _ _ _ IH (subst_rel_insert_mem _ _ _ _ _ _ _ _ μ HR) Hk0 Hk0').
    - (* forall rep *)
      intros ϕ IH F F' sub_m sub_r sub_s sub_t se se' cl HR Hk Hk'.
      apply has_kind_ft_forallrep_inv in Hk as Hk0.
      apply has_kind_ft_forallrep_inv in Hk' as Hk0'.
      rewrite !closure_interp_eq; cbn_interp.
      apply bi.equiv_wand_iff.
      refine (forall_rep_interp_ren _ _ _ _ _ cl); intros ιs.
      exact (function_type_subst_ok_equiv _ _ _ _ _ _ _ _ _ IH (subst_rel_insert_rep _ _ _ _ _ _ _ _ ιs HR) Hk0 Hk0').
    - (* forall size *)
      intros ϕ IH F F' sub_m sub_r sub_s sub_t se se' cl HR Hk Hk'.
      apply has_kind_ft_forallsize_inv in Hk as Hk0.
      apply has_kind_ft_forallsize_inv in Hk' as Hk0'.
      rewrite !closure_interp_eq; cbn_interp.
      apply bi.equiv_wand_iff.
      refine (forall_size_interp_ren _ _ _ _ _ cl); intros n.
      exact (function_type_subst_ok_equiv _ _ _ _ _ _ _ _ _ IH (subst_rel_insert_size _ _ _ _ _ _ _ _ n HR) Hk0 Hk0').
  Qed.

  Lemma subst_rel_of F F' se se' sub_m sub_r sub_s sub_t :
    sem_env_interp F' se' →
    sem_env_interp F se →
    sem_env_rel_rep_eq se' se sub_r →
    sem_env_rel_size_eq se' se sub_s →
    sem_env_rel_mem_eq se' se sub_m →
    sem_env_rel_sκ_eq se' se sub_t →
    sem_env_rel_type_eq se' se sub_t →
    (∀ i, refresh_kinds F (sub_t i) = sub_t i) →
    subst_rel F F' sub_m sub_r sub_s sub_t se se'.
  Proof.
    intros; split; try done.
    by apply sem_env_rel_type_eq_var.
  Qed.

  Lemma type_interp_subst_type_BIDIRECTIONAL F F' se se' τ κ κ' sv sub_m sub_r sub_s sub_t :
    let τ' := refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ) in
    (sem_env_types_well_formed se') ->
    (sem_env_types_well_formed se) ->
    (sem_env_interp F' se') ->
    (sem_env_interp F se) ->
    (sem_env_rel_rep_eq se' se sub_r) ->
    (sem_env_rel_size_eq se' se sub_s) ->
    (sem_env_rel_mem_eq se' se sub_m) ->
    (sem_env_rel_sκ_eq se' se sub_t) ->
    (sem_env_rel_type_eq se' se sub_t) ->
    (∀ i, refresh_kinds F (sub_t i) = sub_t i) ->
    has_kind F' τ κ ->
    has_kind F τ' κ' ->
    (* type_eq_mod_kinds τ' (subst_type sub_m sub_r sub_s sub_t τ) -> *)
    type_interp rti sr τ se' sv ∗-∗
    type_interp rti sr τ' se sv.
  Proof.
    intros τ' _ _ HseF' HseF Hr Hs Hm Hsκ HT Hgood Hk Hk'.
    apply (proj1 type_interp_subst τ F F' sub_m sub_r sub_s sub_t se se' κ κ' sv); [|done|done].
    by apply subst_rel_of.
  Qed.

  Lemma closure_interp_subst_senv_eq F F' se se' ft cl sub_m sub_r sub_s sub_t :
    let ft' := refresh_kinds_ft F (subst_function_type sub_m sub_r sub_s sub_t ft) in
    (sem_env_types_well_formed se') ->
    (sem_env_types_well_formed se) ->
    (sem_env_interp F' se') ->
    (sem_env_interp F se) ->
    (sem_env_rel_rep_eq se' se sub_r) ->
    (sem_env_rel_size_eq se' se sub_s) ->
    (sem_env_rel_mem_eq se' se sub_m) ->
    (sem_env_rel_sκ_eq se' se sub_t) ->
    (sem_env_rel_type_eq se' se sub_t) ->
    (∀ i, refresh_kinds F (sub_t i) = sub_t i) ->
    has_kind_ft F' ft ->
    has_kind_ft F ft' ->
    closure_interp rti sr ft se' cl -∗
      closure_interp rti sr ft' se cl.
  Proof.
    intros ft' _ _ HseF' HseF Hr Hs Hm Hsκ HT Hgood Hk Hk'; subst ft'.
    iPoseProof (proj1 (proj2 type_interp_subst) ft _ _ _ _ _ _ _ _ cl
                  (subst_rel_of _ _ _ _ _ _ _ _ HseF' HseF Hr Hs Hm Hsκ HT Hgood) Hk Hk') as "[H _]".
    iExact "H".
  Qed.

  Lemma inner_closure_interp_subst_senv_eq F F' se se' ft cl sub_m sub_r sub_s sub_t :
    let ft' := refresh_kinds_ift F (subst_inner_function_type sub_m sub_r sub_s sub_t ft) in
    (sem_env_types_well_formed se') ->
    (sem_env_types_well_formed se) ->
    (sem_env_interp F' se') ->
    (sem_env_interp F se) ->
    (sem_env_rel_rep_eq se' se sub_r) ->
    (sem_env_rel_size_eq se' se sub_s) ->
    (sem_env_rel_mem_eq se' se sub_m) ->
    (sem_env_rel_sκ_eq se' se sub_t) ->
    (sem_env_rel_type_eq se' se sub_t) ->
    (∀ i, refresh_kinds F (sub_t i) = sub_t i) ->
    has_kind_ift F' ft ->
    has_kind_ift F ft' ->
    inner_closure_interp rti sr ft se' cl -∗
      inner_closure_interp rti sr ft' se cl.
  Proof.
    intros ft' _ _ HseF' HseF Hr Hs Hm Hsκ HT Hgood Hk Hk'; subst ft'.
    iPoseProof (proj2 (proj2 type_interp_subst) ft _ _ _ _ _ _ _ _ cl
                  (subst_rel_of _ _ _ _ _ _ _ _ HseF' HseF Hr Hs Hm Hsκ HT Hgood) Hk Hk') as "[H _]".
    iExact "H".
  Qed.

  Lemma value_interp_subst_type_BIDIRECTIONAL F F' se se' τ κ κ' sv sub_m sub_r sub_s sub_t :
    let τ' := refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ) in
    (sem_env_types_well_formed se') ->
    (sem_env_types_well_formed se) ->
    (sem_env_interp F' se') ->
    (sem_env_interp F se) ->
    (sem_env_rel_rep_eq se' se sub_r) ->
    (sem_env_rel_size_eq se' se sub_s) ->
    (sem_env_rel_mem_eq se' se sub_m) ->
    (sem_env_rel_sκ_eq se' se sub_t) ->
    (sem_env_rel_type_eq se' se sub_t) ->
    (∀ i, refresh_kinds F (sub_t i) = sub_t i) ->
    has_kind F' τ κ ->
    has_kind F τ' κ' ->
    (* type_eq_mod_kinds τ' (subst_type sub_m sub_r sub_s sub_t τ) -> *)
    value_interp rti sr se' τ sv ∗-∗
    value_interp rti sr se τ' sv.
  Proof.
    Transparent value_interp.
    unfold value_interp.
    Opaque value_interp.
    cbn.
    by apply type_interp_subst_type_BIDIRECTIONAL.
  Qed.

  Lemma values_interp_subst_type_BIDIRECTIONAL F F' se se' τs κs κs' os sub_m sub_r sub_s sub_t :
    let τs' := map (λ τ, refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)) τs in
    (sem_env_types_well_formed se') ->
    (sem_env_types_well_formed se) ->
    (sem_env_interp F' se') ->
    (sem_env_interp F se) ->
    (sem_env_rel_rep_eq se' se sub_r) ->
    (sem_env_rel_size_eq se' se sub_s) ->
    (sem_env_rel_mem_eq se' se sub_m) ->
    (sem_env_rel_sκ_eq se' se sub_t) ->
    (sem_env_rel_type_eq se' se sub_t) ->
    (∀ i, refresh_kinds F (sub_t i) = sub_t i) ->
    Forall2 (has_kind F') τs κs ->
    Forall2 (has_kind F) τs' κs' ->
    values_interp rti sr se' τs os ∗-∗
    values_interp rti sr se τs' os.
  Proof.
    intros τs' Hse' Hse HseF' HseF Hsub_r Hsub_s Hsub_m Hsub_sκ Hsub_T
      Hsub_t_good Hkind_τs Hkind_τs'.

    generalize dependent κs; generalize dependent κs'.
    generalize dependent os; generalize dependent τs.
    induction τs as [| τ τs].
    - intros * Hkind_τs' * Hkind_τs.
      iSplitR; iIntros "Hos"; destruct os; done.
    - intros τs' os_big κs_big' Hkind_τs' κs_big Hkind_τs.
      subst τs'.
      rewrite map_cons in Hkind_τs'.
      rewrite map_cons.
      apply Forall2_cons_inv_l in Hkind_τs.
      destruct Hkind_τs as (κ & κs & Hkind_τ & Hkind_τs & ->).
      apply Forall2_cons_inv_l in Hkind_τs'.
      destruct Hkind_τs' as (κ' & κs' & Hkind_τ' & Hkind_τs' & ->).

      iSplitR; iIntros "Hos".
      all: iDestruct "Hos" as "(%oss_big & %Hos_big & Hos)".
      all: destruct oss_big as [|o oss]; [done|].
      all: rewrite big_sepL2_cons.
      all: rewrite big_sepL2_fmap_l.
      all: iDestruct "Hos" as "[Hoa Hτsoss]".
      all: cbn in IHτs.
      all: setoid_rewrite big_sepL2_fmap_l in IHτs.
      all: specialize (IHτs (concat oss)).


      1: iAssert (∃ oss0, ⌜concat oss = concat oss0⌝ ∗
            ([∗ list] τ0;os ∈ τs;oss0, value_interp rti sr se' τ0 (SAtoms os)))%I with "[Hτsoss]"
          as "Hτs'".
          1: iExists oss; iSplitR; done.
      2: iAssert (∃ oss0, ⌜concat oss = concat oss0⌝ ∗
            ([∗ list] τ0;os ∈ map (λ τ0, refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ0)) τs;
             oss0,
               value_interp rti sr se τ0 (SAtoms os)))%I with "[Hτsoss]"
          as "Hτs'".
          2: iExists oss; iSplitR; done.
      all: specialize (IHτs κs' Hkind_τs' κs Hkind_τs).
      all: iPoseProof IHτs as "#IHτs".
      all: iDestruct "IHτs" as "[IH1 IH2]".
      1: iPoseProof ("IH1" with "[$Hτs']") as "Hτs''".
      2: iPoseProof ("IH2" with "[$Hτs']") as "Hτs''".
      all: iDestruct "Hτs''" as "(%oss' & %Hc & Hτoss')".
      (* note: concat oss = concat oss' does not imply oss = oss'. A bit stupid but okay. *)

      all: iExists (o :: oss'); iSplitR.
      1, 3: iPureIntro; rewrite concat_cons; rewrite concat_cons in Hos_big; by rewrite <- Hc.

      all: iApply big_sepL2_cons.
      all: rewrite !big_sepL2_fmap_l.
      all: iSplitL "Hoa"; try done.
      all: iApply (type_interp_subst_type_BIDIRECTIONAL F F' se se' τ); try done.
  Qed.


  Lemma hsub_t_base_se_VarT se :
    sem_env_types_well_formed se ->
    sem_env_rel_type_eq se se VarT.
  Proof.
    intros.
    unfold_sem_rels. unfold sem_env_types_well_formed in H.
    intros i. cbn.
    intros sv.
    iStartProof.
    iSplitR.
    - iIntros "HT".
      destruct (snd <$> se.2 !! i) eqn:HT'; rewrite HT'; [rename o into T'|done].
      cbn.
      apply fmap_Some in HT' as ((sκ & [sκ_T T]) & Hlookup & b).
      cbn in b. subst T'.

      cbn in H.
      apply (Forall_lookup_1 _ _ _ _ H) in Hlookup as HT.
      cbn in HT.
      destruct HT as [a HT].
      destruct HT as [b HT].
      iPoseProof (HT with "HT") as "%ye".

      rewrite value_interp_eq.
      cbn.
      iExists sκ; rewrite Hlookup; cbn; iFrame.
      iSplitR; iPureIntro; try done.
      eapply skind_as_type_refine; try done.
    - iIntros "HT".
      rewrite value_interp_eq.
      cbn.
      iDestruct "HT" as "(%sk & _ & _ & pls)".
      destruct (snd <$> se.2 !! i) eqn:HT'; rewrite HT'; [rename o into T'|done].
      done.
  Qed.

  Lemma type_interp_subst_type_forwards F F' se se' τ κ κ' sv sub_m sub_r sub_s sub_t :
    let τ' := refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ) in
    (sem_env_types_well_formed se') ->
    (sem_env_types_well_formed se) ->
    (sem_env_interp F' se') ->
    (sem_env_interp F se) ->
    (sem_env_rel_rep_eq se' se sub_r) ->
    (sem_env_rel_size_eq se' se sub_s) ->
    (sem_env_rel_mem_eq se' se sub_m) ->
    (sem_env_rel_sκ_eq se' se sub_t) ->
    (sem_env_rel_type_eq se' se sub_t) ->
    (∀ i, refresh_kinds F (sub_t i) = sub_t i) ->
    has_kind F' τ κ ->
    has_kind F τ' κ' ->
    (* type_eq_mod_kinds τ' (subst_type sub_m sub_r sub_s sub_t τ) -> *)
    type_interp rti sr τ se' sv -∗
    type_interp rti sr τ' se sv.
  Proof.
    intros.
    iIntros "H".
    iApply (type_interp_subst_type_BIDIRECTIONAL F F' se se' τ κ κ'); try done.
  Qed.
  Lemma type_interp_subst_type_backwards F F' se se' τ κ κ' sv sub_m sub_r sub_s sub_t :
    let τ' := refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ) in
    (sem_env_types_well_formed se') ->
    (sem_env_types_well_formed se) ->
    (sem_env_interp F' se') ->
    (sem_env_interp F se) ->
    (sem_env_rel_rep_eq se' se sub_r) ->
    (sem_env_rel_size_eq se' se sub_s) ->
    (sem_env_rel_mem_eq se' se sub_m) ->
    (sem_env_rel_sκ_eq se' se sub_t) ->
    (sem_env_rel_type_eq se' se sub_t) ->
    (∀ i, refresh_kinds F (sub_t i) = sub_t i) ->
    has_kind F' τ κ ->
    has_kind F τ' κ' ->
    type_interp rti sr τ' se sv -∗
    type_interp rti sr τ se' sv.
  Proof.
    intros.
    iIntros "H".
    iApply (type_interp_subst_type_BIDIRECTIONAL F F' se se' τ κ κ'); try done.
  Qed.


  (* Note: the implicit hell below is because rocq can't figure out the contractive
   instances. In plain text, this lemma is the following:

  eval_kind se κ = Some sκ
  → add_skind_interp_closed sκ
      (fixpoint
         (λ T0 : leibnizO semantic_value -n> iPropO Σ,
            λne sv : leibnizO semantic_value,
            (▷ type_interp rti sr τ (se.1, (sκ, (sκ, add_skind_interp_closed sκ T0)) :: se.2) sv)%I))
    ≡ value_interp rti sr se (RecT κ τ)

   *)
  Lemma add_skind_interp_closed_equiv_value_interp sκ τ κ (se: semantic_env (Σ:=Σ)):
    eval_kind se κ = Some sκ ->
    (@add_skind_interp_closed Σ sκ)
    (@fixpoint natSI (leibnizO semantic_value -n> iPropO Σ)
       (@ofe_mor_cofe natSI (leibnizO semantic_value) (iPropO Σ) (@uPred_cofe (iResUR Σ)))
       (@ofe_mor_inhabited natSI (leibnizO semantic_value) (iPropO Σ) (@bi_inhabited (iPropI Σ)))
       (λ T0 : leibnizO semantic_value -n> iPropO Σ,
          λne sv : leibnizO semantic_value,
          (▷ (@type_interp Σ logrel_na_invs0 wasmG0 richwasmG0 rti sr τ)
               (senv_insert_type sκ sκ ((@add_skind_interp_closed Σ sκ) T0) se) sv)%I)
       (@skind_rec_interp1_contractive Σ sκ
          (@type_interp Σ logrel_na_invs0 wasmG0 richwasmG0 rti sr τ) se))
    ≡ (@value_interp Σ logrel_na_invs0 wasmG0 richwasmG0 rti sr) se (RecT κ τ).
  Proof.
    intros Hκ sv.
    rewrite value_interp_eq.
    Transparent rec_interp.
    iSplitR; iIntros "Hoa".
    + cbn.
      rewrite Hκ.
      iExists sκ.
      iSplitR; first done.
      done.
    + cbn.
      rewrite Hκ.
      iDestruct "Hoa" as "(%sκ_old & %toinv & this)".
      inversion toinv; subst.
      done.
  Qed.


  Lemma invert_memok K n :
    mem_ok K (VarM n) -> n < kc_mem_vars K.
  Proof.
    intros.
    inversion H. subst. done.
  Qed.

  Lemma closure_interp_scons_insert_mem F se μ ϕ cl :
    let ϕ' := refresh_kinds_ft F
                (subst_function_type (unscoped.scons μ VarM) VarR VarS VarT ϕ) in
    has_kind_ft F ϕ' ->
    has_kind_ft (F <| fc_kind_ctx ::= set kc_mem_vars S |>) ϕ ->
    mem_ok F.(fc_kind_ctx) μ ->
    sem_env_interp F se ->
    (∀ μ', closure_interp rti sr ϕ (senv_insert_mem μ' se) cl) -∗
    closure_interp rti sr ϕ' se cl.
  Proof using mr. (* NOTE: don't know why rocq wants using mr *)
    intros ϕ' Hkind_ϕ' Hkind_ϕ Hok Hse.
    iIntros "Hcl".
    pose proof (sem_well_formed_from_interp _ _ Hse) as Hsegood.
    assert (Hse': ∀ μ', sem_env_types_well_formed (senv_insert_mem μ' se)). {
      intros. cbn. unfold sem_env_types_well_formed in *.
      cbn. done.
    }
    assert (H: ∃ b, eval_mem se μ = Some b). {
      destruct μ.
      - (* ahhhhh *)
        cbn.
        destruct Hse as [ (Hse & _ & _)  _].
        cbn in Hse.
        apply invert_memok in Hok.
        rewrite Hse in Hok.
        apply lookup_lt_is_Some_2 in Hok.
        done.
      - cbn. by eexists.
    }
    destruct H as (b & evalμ).
    unfold sem_env_types_well_formed in Hsegood.
    iApply closure_interp_subst_senv_eq; unfold_sem_rels; last done; try done.

    Unshelve.
    5: exact b.

    (* RE:Hsub_T *)
    (* this is the location that's testing whether Hsub_T is weak enough *)
    (* strong enough test is above *)
    3: {
      intros i.
      cbn.
      apply subskind_of_option_refl.
    }
    3: {
      Transparent senv_insert_mem.
      cbn.
      by apply hsub_t_base_se_VarT.
    }
    2: {
      intros.
      cbn.
      destruct i; by cbn.
    }
    - destruct Hse as ((h1 & h2 & h3) & h4).
      cbn in h1; cbn in h2; cbn in h3.
      repeat split; try done.
      + cbn.
        rewrite <- h1.
        done.
      + unfold type_ctx_interp.
        cbn.
        eapply Forall2_impl; first exact h4.
        intros *.
        destruct y.
        intros.
        change (b::se.1.1.1, se.1.1.2, se.1.2, se.2) with (senv_insert_mem b se).
        destruct p.
        rewrite <- (@eval_kind_mem_irrel_eq Σ).
        done.
  Qed.


  Lemma closure_interp_scons_insert_rep F se ρ ϕ cl :
    let ϕ' := refresh_kinds_ft F (subst_function_type VarM (unscoped.scons ρ VarR) VarS VarT ϕ) in
    has_kind_ft F ϕ' ->
    has_kind_ft (add_rep_var F) ϕ ->
    rep_ok (fc_kind_ctx F) ρ ->
    sem_env_interp F se ->
    (∀ ιs, closure_interp rti sr ϕ (senv_insert_rep ιs se) cl) -∗
    closure_interp rti sr ϕ' se cl.
  Proof using mr.
    intros ϕ' Hkind_ϕ' Hkind_ϕ Hok Hse.
    iIntros "Hcl".
    pose proof (sem_well_formed_from_interp _ _ Hse) as Hsegood.
    assert (Hse': ∀ ιs', sem_env_types_well_formed (senv_insert_rep ιs' se)). {
      Transparent senv_insert_rep.
      intros. cbn. unfold sem_env_types_well_formed in *.
      cbn. done.
    }
    destruct (eval_rep_ok_Some _ _ _ Hse Hok) as [ιs Hιs].
    iSpecialize ("Hcl" $! ιs).
    iApply closure_interp_subst_senv_eq; unfold_sem_rels; last done; try done.
    3: {
      intros i.
      cbn.
      apply subskind_of_option_refl.
    }
    3: {
      intros; cbn.
      apply hsub_t_base_se_VarT; done.
    }
    2: {
      intros.
      cbn.
      destruct i; by cbn.
    }
    apply sem_env_insert_rep; done.
  Qed.

  Lemma closure_interp_scons_insert_size F se σ ϕ cl :
    let ϕ' := refresh_kinds_ft F (subst_function_type VarM VarR (unscoped.scons σ VarS) VarT ϕ) in
    has_kind_ft F ϕ' ->
    has_kind_ft (add_size_var F) ϕ ->
    size_ok (fc_kind_ctx F) σ ->
    sem_env_interp F se ->
    (∀ n, closure_interp rti sr ϕ (senv_insert_size n se) cl) -∗
    closure_interp rti sr ϕ' se cl.
  Proof using mr.
    intros ϕ' Hkind_ϕ' Hkind_ϕ Hok Hse.
    iIntros "Hcl".
    destruct (eval_size_ok_Some _ _ _ Hse Hok) as [n Hn].
    pose proof (sem_well_formed_from_interp _ _ Hse) as Hsegood.
    assert (Hse': ∀ n', sem_env_types_well_formed (senv_insert_size n' se)). {
      intros. cbn. unfold sem_env_types_well_formed in *.
      cbn. done.
    }
    iSpecialize ("Hcl" $! n).
    iApply closure_interp_subst_senv_eq; unfold_sem_rels; last done; try done.
    3: {
      intros i.
      cbn.
      apply subskind_of_option_refl.
    }
    3: {
      intros; cbn.
      apply hsub_t_base_se_VarT; done.
    }

    Transparent senv_insert_size.
    2: {
      cbn.
      intros.
      destruct i; by cbn.
    }
    apply sem_env_insert_size; done.
  Qed.

  Lemma inner_closure_interp_scons_insert_type F se τ κ κ0 sκ ϕ cl :
    let ϕ' := refresh_kinds_ift F (subst_inner_function_type VarM VarR VarS (unscoped.scons τ VarT) ϕ) in
    has_kind_ift F ϕ' ->
    has_kind_ift (F <| fc_type_vars ::= cons κ0 |>) ϕ ->
    sem_env_interp F se ->
    has_kind F τ κ ->
    subkind_of κ κ0 ->
    eval_kind se κ0 = Some sκ ->
    (□ ∀ sκ sκ_T T,
       ⌜eval_kind se κ0 = Some sκ⌝ -∗
       ⌜subskind_of sκ_T sκ⌝ -∗
       ⌜skind_has_stype sκ_T T⌝ -∗
       inner_closure_interp rti sr ϕ (senv_insert_type sκ sκ_T T se) cl) -∗
    inner_closure_interp rti sr ϕ' se cl.
  Proof using mr.
    iIntros (ϕ' Hkind_ϕ' Hkind_ϕ Hse Hκ Hsubkind Hsκ) "Hcl".
    apply has_kind_inv in Hκ as Hok_has_κ.
    inversion Hok_has_κ as [??? Hok_τ Hok_κ].
    subst.
    clear Hok_has_κ.
    destruct (eval_kind_ok_Some _ _ _ Hse Hok_κ) as [sκ_T Hsκ_T].

    pose proof (subkind_subskind _ _ _ _ _ Hsκ_T Hsκ Hsubkind) as Hsubskind.
    pose proof (kinding_sound rti sr _ _ _ _ _ Hκ Hse Hsκ_T) as HT.
    set T := value_interp rti sr se τ.
    iSpecialize ("Hcl" $! sκ sκ_T T Hsκ Hsubskind HT).
    iApply inner_closure_interp_subst_senv_eq; last done.
    Unshelve.
    13: exact (F <| fc_type_vars ::= cons κ0 |>).
    - apply Forall_cons. by split; last eapply sem_well_formed_from_interp.
    - by eapply sem_well_formed_from_interp.
    - destruct Hse as (h1 & h2).
      destruct h1 as (h11 & h12 & h13).
      cbn in h11; cbn in h12; cbn in h13.
      repeat split; cbn; try done.
      unfold type_ctx_interp.
      cbn.
      apply Forall2_cons.
      split.
      + change (se.1, (sκ, (sκ_T, T))::se.2) with (senv_insert_type sκ sκ_T T se).
        rewrite <- (@eval_kind_type_irrel_eq Σ).
        try done.
      + unfold type_ctx_interp in h2.
        eapply Forall2_impl; first exact h2.
        intros *. cbn.
        destruct y.
        intros.
        change (se.1, (sκ, (sκ_T, T))::se.2) with (senv_insert_type sκ sκ_T T se).
        rewrite <- (@eval_kind_type_irrel_eq Σ).
        done.
    - done.
    - done.
    - done.
    - done.
    - intros i.
      destruct i.
      2: {
        cbn. apply subskind_of_option_refl.
      }
      cbn -[type_skind].
      pose proof (type_skind_has_kind_Some _ _ _ _ _ Hκ Hse Hsκ_T).
      rewrite H.
      cbn.
      done.
    - intros i.
      destruct i; first done.
      cbn.
      apply hsub_t_base_se_VarT.
      by eapply sem_well_formed_from_interp.
    - intros i.
      destruct i; cbn; try done.
      symmetry.
      destruct (refresh_kinds_id) as (this & _); try done.
      eapply this; done.
    - exact Hkind_ϕ.
    - exact Hkind_ϕ'.
  Qed.


End substitution.
