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
      - cbn. unfold unscoped.shift. lia.
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

  Lemma eval_rep_mem_irrel se ρ ιs μ :
    eval_rep se ρ = Some ιs ->
    eval_rep (senv_insert_mem (Σ:=Σ) μ se) ρ = Some ιs.
  Proof.
    (* by induction ρ using rep_ind. *)
  Admitted.

  Lemma eval_size_mem_irrel se σ n μ :
    eval_size se σ = Some n ->
    eval_size (senv_insert_mem (Σ:=Σ) μ se) σ = Some n.
  Proof.
    (* by induction σ using size_ind. *)
  Admitted.

  Lemma type_skind_mem_irrel se μ τ sκ :
    type_skind (Σ:=Σ) se τ = Some sκ ->
    type_skind (Σ:=Σ) (senv_insert_mem μ se)
      (ren_type unscoped.shift unscoped.id unscoped.id unscoped.id τ) = Some sκ.
  Proof.
    intros H.
    destruct τ.
    1: done.
    (* all: cbn; unfold eval_kind; by rewrite rinstId'_kind. *)
  Admitted.

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
    (* by asimpl'. *)
  Admitted.

  Lemma eval_rep_up_memory se sub_r ιs i μ :
    eval_rep se (sub_r i) = Some ιs ->
    eval_rep (senv_insert_mem (Σ:=Σ) μ se) (up_memory_representation sub_r i) = Some ιs.
  Proof.
    (* by asimpl'. *)
  Admitted.

  Lemma eval_size_up_memory se sub_s n i μ :
    eval_size se (sub_s i) = Some n ->
    eval_size (senv_insert_mem (Σ:=Σ) μ se) (up_memory_size sub_s i) = Some n.
  Proof.
    (* by asimpl'. *)
  Admitted.

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

  Lemma eval_rep_subst_senv (se se' : semantic_env (Σ:=Σ)) sub_r ρ ιs :
    (forall i ιs', lookup_rep se' i = Some ιs' -> eval_rep se (sub_r i) = Some ιs') ->
    eval_rep se' ρ = Some ιs ->
    eval_rep se (subst_representation sub_r ρ) = Some ιs.
  Proof.
    intros Hsub.
    generalize dependent ιs.
    induction ρ as [n|ρs IH|ρs IH|ιs'] using rep_ind.
    - intros ? H. cbn in *. by apply Hsub.
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
    (forall i ιs', lookup_rep se' i = Some ιs' -> eval_rep se (sub_r i) = Some ιs') ->
    (forall i n, lookup_size se' i = Some n -> eval_size se (sub_s i) = Some n) ->
    eval_size se' σ = Some n ->
    eval_size se (subst_size sub_r sub_s σ) = Some n.
  Proof.
    intros Hsub_r Hsub_s.
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
      apply Hsub_r.
    - done.
  Qed.

  Lemma eval_kind_subst_senv (se se' : semantic_env (Σ:=Σ)) sub_r sub_s κ sκ :
    (forall i ιs', lookup_rep se' i = Some ιs' -> eval_rep se (sub_r i) = Some ιs') ->
    (forall i n, lookup_size se' i = Some n -> eval_size se (sub_s i) = Some n) ->
    eval_kind se' κ = Some sκ ->
    eval_kind se (subst_kind sub_r sub_s κ) = Some sκ.
  Proof.
    unfold eval_kind.
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
    (forall i ιs', lookup_rep se' i = Some ιs' -> eval_rep se (sub_r i) = Some ιs') ->
    (forall i n, lookup_size se' i = Some n -> eval_size se (sub_s i) = Some n) ->
    (forall i sκ', fst <$> lookup_type se' i = Some sκ' ->
                   ∃ sκ0', type_skind se (sub_t i) = Some sκ0' /\ subskind_of sκ0' sκ') ->
    type_skind (Σ:=Σ) se' τ = Some sκ ->
    (∃ sκ0, type_skind (Σ:=Σ) se (subst_type sub_m sub_r sub_s sub_t τ) = Some sκ0
            /\ subskind_of sκ0 sκ).
  Proof.
    unfold type_skind.
    intros Hsub_r Hsub_s Hsub_t H.
    destruct τ.
    1: by apply Hsub_t.
    all: exists sκ; split; [|by apply subskind_of_refl]; by eapply eval_kind_subst_senv.
  Qed.

  Lemma type_arep_subst_senv se se' sub_m sub_r sub_s sub_t τ ιs :
    (forall i ιs', lookup_rep se' i = Some ιs' -> eval_rep se (sub_r i) = Some ιs') ->
    (forall i n, lookup_size se' i = Some n -> eval_size se (sub_s i) = Some n) ->
    (forall i sκ', fst <$> lookup_type se' i = Some sκ' ->
                   ∃ sκ0', type_skind se (sub_t i) = Some sκ0' /\ subskind_of sκ0' sκ') ->
    type_arep (Σ:=Σ) se' τ = Some ιs ->
    type_arep (Σ:=Σ) se (subst_type sub_m sub_r sub_s sub_t τ) = Some ιs.
  Proof.
    unfold type_arep.
    intros Hsub_r Hsub_s Hsub_t H.
    apply bind_Some in H as (sκ & Hsκ & Hιs).
    apply bind_Some.
    pose proof (type_skind_subst_senv se se' sub_m sub_r sub_s sub_t _ _ Hsub_r Hsub_s Hsub_t Hsκ)
      as (sκ' & Hsκ' & Hsubskind).
    exists sκ'.
    split; first done.
    by eapply skind_rep_subskinds.
  Qed.

  Lemma translate_type_subst_senv se se' sub_m sub_r sub_s sub_t τ ts :
    (forall i ιs', lookup_rep se' i = Some ιs' -> eval_rep se (sub_r i) = Some ιs') ->
    (forall i n, lookup_size se' i = Some n -> eval_size se (sub_s i) = Some n) ->
    (forall i sκ', fst <$> lookup_type se' i = Some sκ' ->
                   ∃ sκ0', type_skind se (sub_t i) = Some sκ0' /\ subskind_of sκ0' sκ') ->
    translate_type (Σ:=Σ) se' τ = Some ts ->
    translate_type (Σ:=Σ) se (subst_type sub_m sub_r sub_s sub_t τ) = Some ts.
  Proof.
    unfold translate_type.
    intros Hsub_r Hsub_s Hsub_t H.
    apply fmap_Some in H as (ιs & H & ->).
    apply fmap_Some.
    eexists.
    split; last done.
    by eapply type_arep_subst_senv.
  Qed.

  Lemma translate_types_subst_senv se se' sub_m sub_r sub_s sub_t τs ts :
    (forall i ιs', lookup_rep se' i = Some ιs' -> eval_rep se (sub_r i) = Some ιs') ->
    (forall i n, lookup_size se' i = Some n -> eval_size se (sub_s i) = Some n) ->
    (forall i sκ', fst <$> lookup_type se' i = Some sκ' ->
                   ∃ sκ0', type_skind se (sub_t i) = Some sκ0' /\ subskind_of sκ0' sκ') ->
    translate_types (Σ:=Σ) se' τs = Some ts ->
    translate_types (Σ:=Σ) se (map (subst_type sub_m sub_r sub_s sub_t) τs) = Some ts.
  Proof.
    unfold translate_types.
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

  (* As mentioned in a lower comment, this might require an additional assumption *)
  (* this is also now safe from contamination :3 *)
  Lemma values_interp0_subst_type se se' τs os sub_m sub_r sub_s sub_t :
    (forall i ιs', lookup_rep se' i = Some ιs' -> eval_rep se (sub_r i) = Some ιs') ->
    (forall i n, lookup_size se' i = Some n -> eval_size se (sub_s i) = Some n) ->
    (forall i sκ', fst <$> lookup_type se' i = Some sκ' ->
                   ∃ sκ0', type_skind se (sub_t i) = Some sκ0' /\ subskind_of sκ0' sκ') ->
    values_interp0 (value_interp rti sr) se' τs os -∗
    values_interp0 (value_interp rti sr) se (map (subst_type sub_m sub_r sub_s sub_t) τs) os.
  Proof.
    iIntros (Hsub_r Hsub_s Hsub_t) "Hos".
    generalize dependent os; generalize dependent τs.
    induction τs as [| τ τs].
    - intros os. destruct os; done.
    - intros os_big.
      cbn.
      iDestruct "Hos" as "(%oss_big & %Hos_big & Hos)".
      destruct oss_big as [|o oss]; [done|].
      iDestruct (big_sepL2_cons with "Hos") as "[Hoa Hτsoss]".
      cbn in IHτs.
      iExists (o :: oss); iSplitR; first done.
      iApply big_sepL2_cons.
      iSplitL "Hoa"; first last.
      + specialize (IHτs (concat oss)).
        (* for some reason this  v   doesn't work *)
        (* iPoseProof IHτs as "IHτs". *)
        (* but to finish this proof off, get IHτs into iris proof mode,
           then iExists oss, put IHτsoss as the hypothesis, and done. *)
        admit.
      + (* this is where the fun begins *)
        clear IHτs Hos_big os_big oss τs.
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
               (forall i ιs', lookup_rep se' i = Some ιs' -> eval_rep se (sub_r i) = Some ιs') ->
               (forall i n, lookup_size se' i = Some n -> eval_size se (sub_s i) = Some n) ->
               (forall i sκ', fst <$> lookup_type se' i = Some sκ' ->
                   ∃ sκ0', type_skind se (sub_t i) = Some sκ0' /\ subskind_of sκ0' sκ') ->
               closure_interp0 rti sr (value_interp rti sr) se' ft cl -∗
               closure_interp0 rti sr (value_interp rti sr) se
               (subst_function_type sub_m sub_r sub_s sub_t ft) cl).
        * (* I'm scared of VarT *)
          intros; cbn in *.
          iPoseProof (value_interp_eq with "Hoa") as "Hoa".
          iApply value_interp_eq.
          iEval (cbn) in "Hoa".
          iDestruct "Hoa" as "(%sκ & %Hse'skind & Hoa & Htypevar)".
          destruct sκ as [ιs ξ | n ξ]; [|iDestruct "Hoa" as "[[] _]"].
          apply Hsub_t in Hse'skind as Htypeskind.
          (* This is now using the correct Hsub_t *)
          destruct Htypeskind as (sκ' & Htypeskind & Hsubsk).
          inversion Hsubsk; subst.

          iExists (SVALTYPE ιs ξ0).
          iFrame.
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
          assert (temp: sκ' = SVALTYPE ιs ξ) by admit.
          subst sκ'.



          admit.
        * (* i31 *)
          intros; cbn.
          iPoseProof (value_interp_eq with "Hoa") as "Hoa".
          iApply value_interp_eq.
          cbn.
          iDestruct "Hoa" as "(%sk & %HEval & Hoa & _)".
          destruct sk as [ιs ξ | n ξ]; [|iDestruct "Hoa" as "[[] _]"].

          iExists (SVALTYPE ιs ξ).
          iSplitR; [iPureIntro; by eapply eval_kind_subst_senv; done|iFrame].

        * intros. cbn.
          iPoseProof (value_interp_eq with "Hoa") as "Hoa".
          iApply value_interp_eq.
          cbn.
          iDestruct "Hoa" as "(%sk & %HEval & Hoa & _)".
          destruct sk as [ιs ξ | n ξ]; [|iDestruct "Hoa" as "[[] _]"].
          iExists (SVALTYPE ιs ξ); cbn; iFrame.
          iPureIntro.
          eapply eval_kind_subst_senv; done. (* well at least numbers work *)
        * (* sums *)
          intros; cbn.
          iPoseProof (value_interp_eq with "Hoa") as "Hoa".
          iApply value_interp_eq.
          cbn.
          iDestruct "Hoa" as "(%sk & %HEval & Hoa & Hk)".
          destruct sk as [ιs ξ | n ξ]; [|iDestruct "Hoa" as "[[] _]"].
          iExists (SVALTYPE ιs ξ); cbn; iFrame.
          iSplitR; [iPureIntro; eapply eval_kind_subst_senv; done|].
          destruct κ; [|done].
          destruct r; try done.
          cbn.
          iDestruct "Hk" as "(%i & %os & %off & %count & %τi &
                              %H1 & %H2 & %H3 & %H4 & Hoa)".
          (* i and os are definitely right *)
          iExists i, os.
          (* These are likely to need to change TODO *)
          iExists off, count.
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
             by specialize (H0 sub_t sub_r sub_s sub_m se se' Hsub_r Hsub_s Hsub_t
                           (take count (drop off os))).
          -- (* this is true by H4 and some map lemma *)
             (* can't find it quickly but it's true *)
             admit.
          -- (* UNSURE about this one TODO *)
             admit.
          -- (* also unsure about this one TODO *)
             admit.
        (* what else would be interesting... *)
        (* the exists guys probably. Also exists type *)
        (* coderef to figure to test if P0 is enough *)
        (* ForallMemT to test if P0 is true *)
        * admit.
        * admit.
        * admit.
        * (* refT *)
          intros; cbn.
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

        * (* coderef case *)
          (* I think this IH for function types is what we need but we'll see *)
          intros.
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
          specialize (IHτ se se' cl sub_m sub_r sub_s sub_t Hsub_r Hsub_s Hsub_t).
          iPoseProof IHτ as "IHτ".
          iApply IHτ; auto.

        * admit.
        * admit.
        * admit.
        * admit.
        * (* exists mem *)
          intros.
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

               (* okay yes. This is true because o3 isn't changed. but
                  I can't figure out how to tell rocq that the i is indexing
                  into o3 into both cases.
                *)
               admit.
             }
             apply Hsub_r in H'.
             by apply eval_rep_up_memory.
          -- intros.
             (* okay similarly thought eval_size_up_memory *)
             (* with the variables from before, o2 doesn't change *)
             admit.
          -- intros.
             (* I think same deal *)
             admit.
        * admit.
        * admit.
        * admit.
        * (* MonoFun *)
          (* base case for P0 *)
          iIntros (??????? Hsub_r Hsub_s Hsub_t) "#Hcl".
          cbn.
          (* I'm so scared *)
          destruct cl; [|auto].
          destruct f as [τs1_trans τs2_trans] eqn:Hf.
          iDestruct "Hcl" as "(%Hτs1 & %Hτs2 & Hcl)".
          iSplitR; [iPureIntro| iSplitR; [iPureIntro|]]; fold (subst_type sub_m sub_r sub_s sub_t).
          -- by eapply translate_types_subst_senv.
          -- by eapply translate_types_subst_senv.
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
                admit. (* values_interp0 *)
        * (* ForallMemT case *)
          (* this is to test is P0 is reasonable *)
          intros.
          iIntros "Hcl".
          cbn.
          iIntros.
          iSpecialize ("Hcl" $! μ).


          


  Admitted.


  (* TODO: The lemma for values_interp0 might require adding an assumption about
     the memory substitution? *)
  Lemma closure_interp0_subst_senv se se' ϕ cl sub_m sub_r sub_s sub_t :
    (forall i ιs', lookup_rep se' i = Some ιs' -> eval_rep se (sub_r i) = Some ιs') ->
    (forall i n, lookup_size se' i = Some n -> eval_size se (sub_s i) = Some n) ->
    (forall i sκ', fst <$> lookup_type se' i = Some sκ' ->
                   ∃ sκ0', type_skind se (sub_t i) = Some sκ0' /\ subskind_of sκ0' sκ') ->
    closure_interp0 rti sr (value_interp rti sr) se' ϕ cl -∗
    let ϕ' := subst_function_type sub_m sub_r sub_s sub_t ϕ in
    closure_interp0 rti sr (value_interp rti sr) se ϕ' cl.
  Proof.
    generalize dependent sub_t.
    generalize dependent sub_s.
    generalize dependent sub_r.
    generalize dependent sub_m.
    generalize dependent se.
    generalize dependent se'.
    induction ϕ as [τs1 τs2| | | |κ] .
    - iIntros (?????? Hsub_r Hsub_s Hsub_t) "#Hcl".
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
    - iIntros (?????? Hsub_r Hsub_s Hsub_t) "#Hcl %".
      iApply IHϕ; last done.
      + intros ?? H. asimpl'. apply eval_rep_mem_irrel. by apply Hsub_r.
      + intros ?? H. asimpl'. apply eval_size_mem_irrel. by apply Hsub_s.
      + intros ?? H. asimpl'.
        apply Hsub_t in H.
        destruct H as (sκ0' & H & Hsubsk).
        exists sκ0'.
        split; [by apply type_skind_mem_irrel|done].
    - iIntros (?????? Hsub_r Hsub_s Hsub_t) "#Hcl %".
      iApply IHϕ; last done.
      + intros ?? H.
        destruct i.
        * cbn. by rewrite <- H.
        * apply eval_rep_up_rep. by apply Hsub_r.
      + intros ?? H. apply eval_size_up_rep. by apply Hsub_s.
      + intros ?? H.
        apply Hsub_t in H as (sκ0' & H & Hsubsk).
        exists sκ0'.
        split; [by apply type_skind_up_rep|done].
    - iIntros (?????? Hsub_r Hsub_s Hsub_t) "#Hcl %".
      iApply IHϕ; last done.
      + intros ?? H. apply eval_rep_up_size. admit.
      + admit.
      + admit.
    - admit.
  Admitted.

  Lemma closure_interp0_scons_insert_mem F se μ ϕ cl :
    mem_ok F.(fc_kind_ctx) μ ->
    sem_env_interp F se ->
    (∀ μ', closure_interp0 rti sr (value_interp rti sr) (senv_insert_mem μ' se) ϕ cl) -∗
    let ϕ' := subst_function_type (unscoped.scons μ VarM) VarR VarS VarT ϕ in
    closure_interp0 rti sr (value_interp rti sr) se ϕ' cl.
  Proof.
    iIntros (Hok Hse) "Hcl".
    iApply closure_interp0_subst_senv; last done; try done.
    instantiate (1:=MemMM).
    cbn.
    intros ?? H.
    exists sκ'.
    split; [done|by apply subskind_of_refl].
  Qed.

  Lemma closure_interp0_scons_insert_rep F se ρ ϕ cl :
    rep_ok (fc_kind_ctx F) ρ ->
    sem_env_interp F se ->
    (∀ ιs, closure_interp0 rti sr (value_interp rti sr) (senv_insert_rep ιs se) ϕ cl) -∗
    let ϕ' := subst_function_type VarM (unscoped.scons ρ VarR) VarS VarT ϕ in
    closure_interp0 rti sr (value_interp rti sr) se ϕ' cl.
  Proof.
    iIntros (Hok Hse) "Hcl".
    destruct (eval_rep_ok_Some _ _ _ Hse Hok) as [ιs Hιs].
    iSpecialize ("Hcl" $! ιs).
    iApply closure_interp0_subst_senv; last done.
    - intros ?? H.
      destruct i.
      + by rewrite <- H.
      + done.
    - done.
    - intros ?? H.
      exists sκ'.
      split; [done|by apply subskind_of_refl].
  Qed.

  Lemma closure_interp0_scons_insert_size F se σ ϕ cl :
    size_ok (fc_kind_ctx F) σ ->
    sem_env_interp F se ->
    (∀ n, closure_interp0 rti sr (value_interp rti sr) (senv_insert_size n se) ϕ cl) -∗
    let ϕ' := subst_function_type VarM VarR (unscoped.scons σ VarS) VarT ϕ in
    closure_interp0 rti sr (value_interp rti sr) se ϕ' cl.
  Proof.
    iIntros (Hok Hse) "Hcl".
    destruct (eval_size_ok_Some _ _ _ Hse Hok) as [n Hn].
    iSpecialize ("Hcl" $! n).
    iApply closure_interp0_subst_senv; last done.
    - done.
    - intros ?? H.
      destruct i.
      + by rewrite <- H.
      + done.
    - intros ?? H.
      exists sκ'.
      split; [done|by apply subskind_of_refl].
  Qed.

  Lemma closure_interp0_scons_insert_type F se τ κ ϕ cl :
    has_kind F τ κ ->
    sem_env_interp F se ->
    (∀ sκ T,
       ⌜eval_kind se κ = Some sκ⌝ -∗
       ⌜skind_interp sκ T⌝ -∗
       closure_interp0 rti sr (value_interp rti sr) (senv_insert_type sκ T se) ϕ cl) -∗
    let ϕ' := subst_function_type VarM VarR VarS (unscoped.scons τ VarT) ϕ in
    closure_interp0 rti sr (value_interp rti sr) se ϕ' cl.
  Proof.
    iIntros (Hok Hse) "Hcl".
    destruct (has_kind_inv _ _ _ Hok) as [F τ κ Hok_τ Hok_κ].
    destruct (eval_kind_ok_Some _ _ _ Hse Hok_κ) as [sκ Hsκ].
    pose proof (type_skind_has_kind_Some _ _ _ _ _ Hok Hse Hsκ) as (sκ' & Hskind' & Hsub).
    set T := value_interp rti sr se τ.
    iSpecialize ("Hcl" $! sκ T).
    iApply closure_interp0_subst_senv; last iApply "Hcl".
    - done.
    - done.
    - (* this is the incorrect case *)
      (* next step: change closure_interp0_subst_senv's hypothesis, then slowly
         change all of them. Hopefully nothing breaks too horribly.
       *)
      intros ?? H.
      destruct i.
      + cbn in H; inversion H; subst.
        exists sκ'.
        by split.
      + cbn in H.
        cbn.
        eexists; split; [done|by apply subskind_of_refl].
    - done.
    - iPureIntro.
      subst T.
      iIntros (sv) "H".
      rewrite value_interp_eq.
      iDestruct "H" as "(%sκ'' & %Hsκ'' & Hskind' & Htype)".
      rewrite Hskind' in Hsκ''.
      inversion Hsκ''; subst.
      iApply skind_as_type_refine; done.
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
    iApply value_interp_eq.
    iPoseProof (value_interp_eq with "Hos") as "Hos".

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

    - iApply closure_interp0_scons_insert_mem; [done|done|by inversion Hok].
    - iApply closure_interp0_scons_insert_rep; [done|done|by inversion Hok].
    - iApply closure_interp0_scons_insert_size; [done|done|by inversion Hok].
    - iApply closure_interp0_scons_insert_type; [done|done|by inversion Hok].
  Qed.

End inst.
