Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.env_props.
Require Import RichWasm.iris.logrel.instr.kinding.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section pure.

  Lemma type_eq_symmetric : Symmetric type_eq.
  Proof.
    rewrite /Symmetric.
    intros τ τ' Hteq.
    induction Hteq using type_eq_ind'; try (by constructor); try (constructor; try done; by apply Forall2_flip).
  Qed.

  Global Instance type_eq_sym : Symmetric type_eq.
  Proof.
    apply type_eq_symmetric.
  Qed.

End pure.

Section serialize.

  Lemma has_arep_serialize_length ι o :
    has_arep ι o ->
    length (serialize_atom o) = arep_size ι.
  Proof.
    intros H.
    destruct ι, o; cbn in *; done.
  Qed.

  Lemma has_areps_serialize_length ιs os :
    Forall2 has_arep ιs os ->
    length (flat_map serialize_atom os) = areps_size ιs.
  Proof.
    induction 1 as [|ι o ιs os Hao HF IH]; cbn; first done.
    rewrite length_app IH (has_arep_serialize_length _ _ Hao).
    done.
  Qed.

  Lemma ref_flag_atom_word_serialize (P : pointer -> Prop) o :
    forall_ptr_atom P o ->
    Forall (forall_ptr_word P) (serialize_atom o).
  Proof.
    intros H.
    destruct o; cbn in *; repeat constructor; done.
  Qed.

  Lemma ref_flag_serialize ξ os :
    ref_flag_atoms_interp ξ (SAtoms os) ->
    ref_flag_words_interp ξ (SWords (flat_map serialize_atom os)).
  Proof.
    unfold ref_flag_atoms_interp, ref_flag_words_interp, forall_satoms, forall_swords.
    induction 1 as [|o os Ho Hos IH]; cbn; first constructor.
    apply Forall_app.
    split; last done.
    by apply ref_flag_atom_word_serialize.
  Qed.

End serialize.

Section pure_kinds.
  Context {E : Type}.
  Context `{Env E}.
  Variable env : E.

  Lemma eval_size_RepS_ProdR ρs :
    eval_size env (RepS (ProdR ρs)) = eval_size env (ProdS (map RepS ρs)).
  Proof.
    cbn.
    unfold compose.
    induction ρs as [|ρ ρs IH]; cbn; first done.
    destruct (eval_rep env ρ) as [ιs|] eqn:Hρ; cbn; last done.
    destruct (mapM (eval_rep env) ρs) as [ιss|] eqn:Hρs;
      destruct (mapM (eval_size env) (map RepS ρs)) as [ns|] eqn:Hns;
      cbn in IH |- *; try done.
    injection IH as IH.
    f_equal.
    rewrite map_app.
    change (foldr Init.Nat.add 0 ?l) with (list_sum l).
    change (foldr Init.Nat.add 0 ?l) with (list_sum l) in IH.
    rewrite list_sum_app.
    lia.
  Qed.

  Lemma eval_kind_valtype_inv ρ ξ ρ' ξ' :
    eval_kind env (VALTYPE ρ ξ) = eval_kind env (VALTYPE ρ' ξ') ->
    eval_rep env ρ = eval_rep env ρ' /\
    (forall ιs, eval_rep env ρ = Some ιs -> ξ = ξ').
  Proof.
    cbn.
    destruct (eval_rep env ρ) as [ιs|] eqn:Hρ;
      destruct (eval_rep env ρ') as [ιs'|] eqn:Hρ'; cbn;
      intros Heq; simplify_eq; split; congruence.
  Qed.

  Lemma eval_kind_ser_prod_struct ρs ξs ρs' ξs' :
    Forall2 (fun ρξ ρξ' : representation * ref_flag =>
               eval_kind env (VALTYPE ρξ.1 ρξ.2) = eval_kind env (VALTYPE ρξ'.1 ρξ'.2))
      (zip ρs ξs) (zip ρs' ξs') ->
    length ρs = length ξs ->
    length ρs' = length ξs' ->
    length ρs = length ρs' ->
    eval_kind env (MEMTYPE (RepS (ProdR ρs)) (ref_flag_lub ξs)) =
    eval_kind env (MEMTYPE (ProdS (map RepS ρs')) (ref_flag_lub ξs')).
  Proof.
    revert ξs ρs' ξs'.
    induction ρs as [|ρ ρs IH]; intros ξs ρs' ξs' HF2 Hlen1 Hlen2 Hlen3;
      destruct ρs' as [|ρ' ρs']; try discriminate;
      destruct ξs as [|ξ ξs]; try discriminate;
      destruct ξs' as [|ξ' ξs']; try discriminate.
    - done.
    - cbn in HF2.
      apply Forall2_cons_1 in HF2 as [Hhd HF2].
      apply eval_kind_valtype_inv in Hhd as [Hrep Hflag].
      injection Hlen1 as Hlen1.
      injection Hlen2 as Hlen2.
      injection Hlen3 as Hlen3.
      specialize (IH ξs ρs' ξs' HF2 Hlen1 Hlen2 Hlen3).
      cbn in IH |- *.
      unfold compose in *.
      cbn in Hrep, Hflag.
      destruct (eval_rep env ρ) as [ιs|] eqn:Hρ; rewrite <- Hrep; cbn; last done.
      specialize (Hflag ιs eq_refl); subst ξ'.
      destruct (mapM (eval_rep env) ρs) as [ιss|] eqn:Hρs;
        destruct (mapM (eval_size env) (map RepS ρs')) as [ns|] eqn:Hns;
        cbn in IH |- *; try done; try discriminate.
      injection IH as IHn IHflag.
      unfold ref_flag_lub in IHflag.
      f_equal.
      f_equal; last congruence.
      rewrite map_app.
      change (foldr Init.Nat.add 0 ?l) with (list_sum l).
      rewrite list_sum_app.
      lia.
Qed.

  Lemma struct_fields_ser_inv F κs_ser τs' σs' ξs2 :
    Forall3 (fun τ σ ξ => has_kind F τ (MEMTYPE σ ξ)) (zip_with SerT κs_ser τs') σs' ξs2 ->
    length κs_ser = length τs' ->
    exists ρs2,
      σs' = map RepS ρs2 /\
      κs_ser = map (fun ρξ : representation * ref_flag => MEMTYPE (RepS ρξ.1) ρξ.2)
                 (zip ρs2 ξs2) /\
      Forall3 (fun τ' ρ ξ => has_kind F τ' (VALTYPE ρ ξ)) τs' ρs2 ξs2.
  Proof.
    revert τs' σs' ξs2.
    induction κs_ser as [|κ0 κs_ser IH]; intros τs' σs' ξs2 HF3 Hlen;
      destruct τs' as [|τ' τs']; try discriminate.
    - cbn in HF3.
      inversion HF3; subst.
      exists [].
      repeat split; constructor.
    - cbn in HF3.
      injection Hlen as Hlen.
      inversion HF3 as [|? σ0 ξ0 ? σs0 ξs0 Hhd HF3']; subst.
      inversion Hhd; subst.
      destruct (IH _ _ _ HF3' Hlen) as (ρs2 & -> & -> & HF3'').
      eexists (_ :: ρs2).
      repeat split.
      by constructor.
  Qed.

  Lemma eval_kind_pairs_of_kinds F τs τs' ρs ξs ρs2 ξs2 :
    Forall2 (fun τ τ' =>
               forall F κ κ',
                 has_kind F τ κ ->
                 has_kind F τ' κ' ->
                 eval_kind env κ = eval_kind env κ') τs τs' ->
    Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs ρs ξs ->
    Forall3 (fun τ' ρ ξ => has_kind F τ' (VALTYPE ρ ξ)) τs' ρs2 ξs2 ->
    Forall2 (fun ρξ ρξ' : representation * ref_flag =>
               eval_kind env (VALTYPE ρξ.1 ρξ.2) = eval_kind env (VALTYPE ρξ'.1 ρξ'.2))
      (zip ρs ξs) (zip ρs2 ξs2).
  Proof.
    intros HF2.
    revert ρs ξs ρs2 ξs2.
    induction HF2 as [|τ τ' τs τs' Hhd HF2 IH]; intros ρs ξs ρs2 ξs2 HF3 HF3'.
    - inversion HF3; subst.
      inversion HF3'; subst.
      constructor.
    - inversion HF3; subst.
      inversion HF3'; subst.
      cbn [zip zip_with].
      constructor; last by apply IH.
      cbv beta; cbn [fst snd].
      by eapply Hhd.
  Qed.

  Lemma type_eq_eval_kind_agree :
    forall τ τ',
      type_eq τ τ' ->
      forall F κ κ',
        has_kind F τ κ ->
        has_kind F τ' κ' ->
        eval_kind env κ = eval_kind env κ'.
  Proof.
    apply (type_eq_ind'
             (fun τ τ' =>
                forall F κ κ',
                  has_kind F τ κ ->
                  has_kind F τ' κ' ->
                  eval_kind env κ = eval_kind env κ')).
    - intros τ F κ κ' Hκ Hκ'.
      by rewrite (has_kind_agree _ _ _ _ Hκ Hκ').
    - intros κ0 τs τs' _ _ F κ κ' Hκ Hκ'; inversion Hκ; inversion Hκ'; subst; congruence.
    - intros κ0 τs τs' _ _ F κ κ' Hκ Hκ'; inversion Hκ; inversion Hκ'; subst; congruence.
    - intros κ0 τs τs' _ _ F κ κ' Hκ Hκ'; inversion Hκ; inversion Hκ'; subst; congruence.
    - intros κ0 τs τs' _ _ F κ κ' Hκ Hκ'; inversion Hκ; inversion Hκ'; subst; congruence.
    - intros κ0 μ β τ τ' _ _ F κ κ' Hκ Hκ'; inversion Hκ; inversion Hκ'; subst; congruence.
    - intros κ0 τ τ' _ _ F κ κ' Hκ Hκ'; inversion Hκ; inversion Hκ'; subst; congruence.
    - intros κ0 τ τ' _ _ F κ κ' Hκ Hκ'; inversion Hκ; inversion Hκ'; subst; congruence.
    - intros κ0 τ τ' _ _ F κ κ' Hκ Hκ'; inversion Hκ; inversion Hκ'; subst; congruence.
    - intros κ0 τ τ' _ _ F κ κ' Hκ Hκ'; inversion Hκ; inversion Hκ'; subst; congruence.
    - intros κ0 τ τ' _ _ F κ κ' Hκ Hκ'; inversion Hκ; inversion Hκ'; subst; congruence.
    - intros κ0 κτ τ τ' _ _ F κ κ' Hκ Hκ'; inversion Hκ; inversion Hκ'; subst; congruence.
    - intros κ_ser κ_prod κ_struct κs_ser τs τs' Hlen Heq IH F κ κ' Hκ Hκ'.
      inversion Hκ; subst.
      match goal with Hp : has_kind _ (ProdT _ _) _ |- _ => rename Hp into Hprod end.
      inversion Hprod; subst.
      match goal with Hf : Forall3 _ τs _ _ |- _ => rename Hf into HF3 end.
      inversion Hκ'; subst.
      match goal with
        Hf : Forall3 _ (zip_with SerT _ _) _ _ |- _ => rename Hf into HF3' end.
      pose proof (Forall2_length _ _ _ Heq) as Hlenττ'.
      destruct (struct_fields_ser_inv _ _ _ _ _ HF3' Hlen) as (ρs2 & -> & _ & HF3'').
      pose proof (Forall3_length_lm _ _ _ _ HF3) as Hl1.
      pose proof (Forall3_length_lr _ _ _ _ HF3) as Hl2.
      pose proof (Forall3_length_lm _ _ _ _ HF3'') as Hl3.
      pose proof (Forall3_length_lr _ _ _ _ HF3'') as Hl4.
      apply eval_kind_ser_prod_struct; try congruence.
      by eapply eval_kind_pairs_of_kinds.
    - intros κ_ser κ_prod κ_struct κs_ser τs τs' Hlen Heq IH F κ κ' Hκ Hκ'.
      inversion Hκ; subst.
      match goal with
        Hf : Forall3 _ (zip_with SerT _ _) _ _ |- _ => rename Hf into HF3' end.
      inversion Hκ'; subst.
      match goal with Hp : has_kind _ (ProdT _ _) _ |- _ => rename Hp into Hprod end.
      inversion Hprod; subst.
      match goal with Hf : Forall3 _ τs' _ _ |- _ => rename Hf into HF3 end.
      pose proof (Forall2_length _ _ _ Heq) as Hlenττ'.
      destruct (struct_fields_ser_inv _ _ _ _ _ HF3' Hlen) as (ρs2 & -> & _ & HF3'').
      pose proof (Forall3_length_lm _ _ _ _ HF3) as Hl1.
      pose proof (Forall3_length_lr _ _ _ _ HF3) as Hl2.
      pose proof (Forall3_length_lm _ _ _ _ HF3'') as Hl3.
      pose proof (Forall3_length_lr _ _ _ _ HF3'') as Hl4.
      symmetry.
      apply eval_kind_ser_prod_struct; try congruence.
      eapply eval_kind_pairs_of_kinds; [|exact HF3|exact HF3''].
      apply Forall2_flip in IH.
      eapply Forall2_impl; first exact IH.
      intros ta tb HP Fx κa κb Hka Hkb.
      symmetry.
      by eapply HP.
  Qed.

End pure_kinds.

Section type_eq_sem.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.

  Lemma has_kind_valtype_eval_rep F se ρ ξ τ :
    sem_env_interp F se ->
    has_kind F τ (VALTYPE ρ ξ) ->
    ∃ ιs, eval_rep se ρ = Some ιs /\ @type_skind Σ se τ = Some (SVALTYPE ιs ξ).
  Proof.
    intros Hsem Hk.
    pose proof (has_kind_inv _ _ _ Hk) as Hko.
    inversion Hko as [? ? ? Htok Hkok]; subst.
    inversion Hkok as [? ? ? Hrok | ]; subst.
    destruct (eval_rep_ok_Some F se ρ Hsem Hrok) as [ιs Hιs].
    exists ιs; split; first done.
    eapply type_skind_has_kind_Some; eauto.
    cbn. rewrite Hιs. done.
  Qed.

  Lemma has_kind_valtype_eval_rep_list F se τs ρs ξs :
    sem_env_interp F se ->
    Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs ρs ξs ->
    ∃ ιss,
      Forall2 (fun ρ ιs => eval_rep se ρ = Some ιs) ρs ιss /\
      Forall3 (fun τ ιs ξ => @type_skind Σ se τ = Some (SVALTYPE ιs ξ)) τs ιss ξs.
  Proof.
    intros Hsem H1.
    induction H1 as [|τ ρ ξ τs ρs ξs Hτρξ H1 IHind].
    - exists []. split; constructor.
    - destruct (has_kind_valtype_eval_rep F se ρ ξ τ Hsem Hτρξ) as (ιs & Hιs & Hsk).
      destruct IHind as (ιss & Hιss & HF3).
      exists (ιs :: ιss). split; constructor; done.
  Qed.

  Lemma ref_flag_atoms_interp_concat ξs oss :
    Forall2 (fun ξ os => ref_flag_atoms_interp ξ (SAtoms os)) ξs oss ->
    ref_flag_atoms_interp (ref_flag_lub ξs) (SAtoms (concat oss)).
  Proof.
    induction 1 as [|ξ os ξs oss Hhd Htl IH].
    - cbn. constructor.
    - cbn [ref_flag_lub concat foldr].
      apply ref_flag_atoms_interp_app.
      split.
      + eapply ref_flag_atoms_refine; last exact Hhd.
        apply ref_flag_lub2_ub.
      + eapply ref_flag_atoms_refine; last exact IH.
        apply ref_flag_lub2_ub.
  Qed.

  Lemma struct_fields_to_prod_atoms F se τs τs' ρs ξs ρs2 ξs2 wss :
    sem_env_interp F se ->
    Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs ρs ξs ->
    Forall3 (fun τ' ρ ξ => has_kind F τ' (VALTYPE ρ ξ)) τs' ρs2 ξs2 ->
    Forall2 type_eq τs τs' ->
    Forall2 (fun τ τ' => ∀ sv, type_interp rti sr τ se sv ⊣⊢ type_interp rti sr τ' se sv) τs τs' ->
    length wss = length τs' ->
    ([∗ list] ws;τ ∈ wss; zip_with SerT (map (fun ρξ => MEMTYPE (RepS ρξ.1) ρξ.2) (zip ρs2 ξs2)) τs',
       type_interp rti sr τ se (SWords ws))
    ⊢
    (∃ os, ⌜concat wss = flat_map serialize_atom os⌝ ∗
       type_interp rti sr (ProdT (VALTYPE (ProdR ρs) (ref_flag_lub ξs)) τs) se (SAtoms os)).
  Proof.
    intros Hsem H1.
    revert τs' ρs2 ξs2 wss.
    induction H1 as [|τ ρ ξ τs ρs ξs Hτρξ H1 IHind];
      intros τs' ρs2 ξs2 wss H1' Heqtyp IH Hlenwss.
    - apply Forall2_nil_inv_l in IH as ->.
      cbn in Hlenwss.
      apply nil_length_inv in Hlenwss as ->.
      cbn.
      iIntros "_".
      iExists []. cbn. iSplit; first done.
      rewrite type_interp_eq /add_skind_interp /pre_type_interp /=.
      iExists (SVALTYPE [] NoRefs).
      iSplit; first done.
      iSplit.
      { iPureIntro. split; last done. by exists []. }
      iExists []. by iSplit.
    - apply Forall2_cons_inv_l in Heqtyp as (τ' & τs'0 & Hτeq & Heqtyp & ->).
      rename τs'0 into τs'.
      apply Forall2_cons in IH as (IHhead & IH).
      apply Forall3_cons_inv_l in H1' as (ρ2 & ρs2' & ξ2 & ξs2' & -> & -> & Hτ'ρ2ξ2 & H1').
      destruct wss as [|ws wss]; first done.
      injection Hlenwss as Hlenwss.
      cbn [zip map zip_with concat].
      iIntros "H".
      iDestruct "H" as "[Hhd Htl]".
      iEval (rewrite type_interp_eq /add_skind_interp /pre_type_interp /=) in "Hhd".
      iDestruct "Hhd" as (sκser Hskser Hsvser) "Hhd".
      iDestruct "Hhd" as (os') "(%Hwseq & Hhd)".
      iDestruct (IHhead with "Hhd") as "Hhd'".
      injection Hwseq as Hwseq.
      iDestruct (IHind τs' ρs2' ξs2' wss H1' Heqtyp IH Hlenwss with "Htl") as (os_tail) "(%Htaileq & Htail)".
      iExists (os' ++ os_tail).
      iSplit.
      { iPureIntro. rewrite Hwseq Htaileq flat_map_app. done. }
      destruct (has_kind_valtype_eval_rep_list F se τs ρs ξs Hsem H1) as (ιss & Hιss & Hsκτs).
      destruct (has_kind_valtype_eval_rep F se ρ ξ τ Hsem Hτρξ) as (ιsτ & Hιsτ & Hsκτ).
      iEval (rewrite type_interp_eq /add_skind_interp) in "Hhd'".
      iDestruct "Hhd'" as (sκτ) "(%Hskτ & %Hsvτ & Hhd'')".
      rewrite Hsκτ in Hskτ. injection Hskτ as <-.
      iEval (rewrite type_interp_eq /add_skind_interp /pre_type_interp /=) in "Htail".
      iDestruct "Htail" as (sκtail) "(%Hsktail & %Hsvtail & Htail)".
      rewrite (mapM_Some_2 _ _ _ Hιss) in Hsktail.
      cbn in Hsktail.
      injection Hsktail as <-.
      iExists (SVALTYPE (ιsτ ++ concat ιss) (ref_flag_lub (ξ :: ξs))).
      iSplit.
      { iPureIntro.
        cbn. rewrite Hιsτ. cbn. erewrite mapM_Some_2; last exact Hιss. done. }
      iSplit.
      { iPureIntro.
        destruct Hsvτ as [Harepτ Hrefτ].
        destruct Hsvtail as [Hareptail Hreftail].
        split.
        - apply has_areps_app_l; done.
        - apply ref_flag_atoms_interp_app.
          split.
          + eapply ref_flag_atoms_refine; last exact Hrefτ.
            apply ref_flag_lub2_ub.
          + eapply ref_flag_atoms_refine; last exact Hreftail.
            apply ref_flag_lub2_ub. }
      iDestruct "Htail" as (oss_tail) "(%Hosstaileq & Hbig)".
      injection Hosstaileq as Hosstaileq.
      iExists (os' :: oss_tail).
      iSplit; first (iPureIntro; cbn; rewrite Hosstaileq; done).
      iApply (big_sepL2_cons with "[Hhd'' $Hbig]").
      iApply (type_interp_eq rti sr τ se (SAtoms os')).
      rewrite /add_skind_interp.
      iExists (SVALTYPE ιsτ ξ).
      iSplit; first done.
      iSplit; first done.
      iExact "Hhd''".
  Qed.

  Lemma prod_atoms_to_struct_fields F se τs τs' ρs ξs ρs2 ξs2 os :
    sem_env_interp F se ->
    Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs ρs ξs ->
    Forall3 (fun τ' ρ ξ => has_kind F τ' (VALTYPE ρ ξ)) τs' ρs2 ξs2 ->
    Forall2 type_eq τs τs' ->
    Forall2 (fun τ τ' => ∀ sv, type_interp rti sr τ se sv ⊣⊢ type_interp rti sr τ' se sv) τs τs' ->
    type_interp rti sr (ProdT (VALTYPE (ProdR ρs) (ref_flag_lub ξs)) τs) se (SAtoms os)
    ⊢
    (∃ wss, ⌜flat_map serialize_atom os = concat wss⌝ ∗
       [∗ list] ws;τ ∈ wss; zip_with SerT (map (fun ρξ => MEMTYPE (RepS ρξ.1) ρξ.2) (zip ρs2 ξs2)) τs',
         type_interp rti sr τ se (SWords ws)).
  Proof.
    intros Hsem H1.
    revert τs' ρs2 ξs2 os.
    induction H1 as [|τ ρ ξ τs ρs ξs Hτρξ H1 IHind];
      intros τs' ρs2 ξs2 os H1' Heqtyp IH.
    - apply Forall2_nil_inv_l in IH as ->.
      iIntros "H".
      iEval (rewrite type_interp_eq /add_skind_interp /pre_type_interp /=) in "H".
      iDestruct "H" as (sκ0 Hsk0 Hsv0) "H".
      iDestruct "H" as (oss) "(%Hoseq & H)".
      destruct oss as [|o oss]; last done.
      cbn in Hoseq.
      iExists []. cbn.
      injection Hoseq as ->.
      iSplit; first done.
      by rewrite zip_with_nil_r.
    - apply Forall2_cons_inv_l in Heqtyp as (τ' & τs'0 & Hτeq & Heqtyp & ->).
      rename τs'0 into τs'.
      apply Forall2_cons in IH as (IHhead & IH).
      apply Forall3_cons_inv_l in H1' as (ρ2 & ρs2' & ξ2 & ξs2' & -> & -> & Hτ'ρ2ξ2 & H1').
      cbn [zip map zip_with concat].
      iIntros "H".
      iEval (rewrite type_interp_eq /add_skind_interp /pre_type_interp /=) in "H".
      iDestruct "H" as (sκ Hsk Hsv) "H".
      iDestruct "H" as ([|o oss]) "(%Hoseq & H)"; first done.
      iEval (rewrite big_sepL2_cons) in "H".
      iDestruct "H" as "[Hhd Htl]".
      iEval (rewrite big_sepL2_fmap_l) in "Htl".
      iDestruct (big_sepL2_value_interp_skind with "Htl") as "%Hp".
      destruct (has_kind_valtype_eval_rep_list F se τs ρs ξs Hsem H1) as (ιss & Hιss & Hsκτs).
      assert (Forall2 (fun ιs_i os_i => Forall2 has_arep ιs_i os_i) ιss oss /\
              Forall2 (fun ξ_i os_i => ref_flag_atoms_interp ξ_i (SAtoms os_i)) ξs oss) as [Harepall Hrefall].
      { clear -Hp Hsκτs.
        revert oss Hp.
        induction Hsκτs as [|τ0 ιs0 ξ0 τs0 ιss0 ξs0 Hsk0' Hsκτs0 IHk]; intros oss0 Hp.
        - apply Forall2_nil_inv_l in Hp as ->. split; constructor.
        - apply Forall2_cons_inv_l in Hp as (os0h & oss0t & Hph & Hpt & ->).
          destruct Hph as (sκh & Hskh & Hsvh).
          rewrite Hsk0' in Hskh. injection Hskh as <-.
          destruct (IHk oss0t Hpt) as [IH1 IH2].
          destruct Hsvh as [Harep Href].
          destruct Harep as (os0h' & Heqh & Harep').
          injection Heqh as <-.
          split; constructor; done. }
      pose proof (Forall2_concat _ _ _ Harepall) as Harepcat.
      pose proof (ref_flag_atoms_interp_concat _ _ Hrefall) as Hrefcat.
      destruct (has_kind_valtype_eval_rep F se ρ ξ τ Hsem Hτρξ) as (ιsτ & Hιsτ & Hsκτ).
      iDestruct (type_interp_skind_svalue with "Hhd") as "%Hheadp".
      destruct Hheadp as (sκh & Hskh & Hsvh).
      rewrite Hsκτ in Hskh. injection Hskh as <-.
      destruct Hsvh as [Harepo Refo].
      destruct Harepo as (o' & Heqo & Harepo').
      injection Heqo as <-.
      pose proof (type_eq_eval_kind_agree se τ τ' Hτeq F (VALTYPE ρ ξ) (VALTYPE ρ2 ξ2) Hτρξ Hτ'ρ2ξ2) as Hagree.
      assert (eval_kind se (VALTYPE ρ ξ) = Some (SVALTYPE ιsτ ξ)) as Hek1.
      { cbn. rewrite Hιsτ. done. }
      rewrite Hek1 in Hagree.
      destruct (has_kind_valtype_eval_rep F se ρ2 ξ2 τ' Hsem Hτ'ρ2ξ2) as (ιs2 & Hιs2 & Hsκτ2).
      assert (eval_kind se (VALTYPE ρ2 ξ2) = Some (SVALTYPE ιs2 ξ2)) as Hek2.
      { cbn. rewrite Hιs2. done. }
      rewrite Hek2 in Hagree.
      injection Hagree as -> ->.
      iDestruct (IHhead with "Hhd") as "Hhd2".
      iAssert (type_interp rti sr (SerT (MEMTYPE (RepS ρ2) ξ2) τ') se (SWords (flat_map serialize_atom o)))%I
        with "[Hhd2]" as "Hheadser".
      { iApply (type_interp_eq rti sr (SerT (MEMTYPE (RepS ρ2) ξ2) τ') se (SWords (flat_map serialize_atom o))).
        rewrite /add_skind_interp.
        iExists (SMEMTYPE (length (flat_map serialize_atom o)) ξ2).
        iSplit.
        { iPureIntro. cbn. rewrite Hιs2. cbn. unfold compose.
          rewrite (has_areps_serialize_length _ _ Harepo'). done. }
        iSplit.
        { iPureIntro. split; first done. by apply ref_flag_serialize. }
        rewrite /pre_type_interp /=.
        iExists o. iSplit; first done. iExact "Hhd2". }
      iAssert (type_interp rti sr (ProdT (VALTYPE (ProdR ρs) (ref_flag_lub ξs)) τs) se (SAtoms (concat oss)))%I
        with "[Htl]" as "Htail2".
      { iApply (type_interp_eq rti sr (ProdT (VALTYPE (ProdR ρs) (ref_flag_lub ξs)) τs) se (SAtoms (concat oss))).
        rewrite /add_skind_interp.
        iExists (SVALTYPE (concat ιss) (ref_flag_lub ξs)).
        iSplit.
        { iPureIntro. cbn. unfold compose. by erewrite mapM_Some_2. }
        iSplit.
        { iPureIntro. split; last done. by exists (concat oss). }
        rewrite /pre_type_interp /=.
        iExists oss. iSplit; first done.
        rewrite big_sepL2_fmap_l. iExact "Htl". }
      iDestruct (IHind τs' ρs2' ξs2' (concat oss) H1' Heqtyp IH with "Htail2") as (wss_tail) "(%Htaileq2 & Hstructtail)".
      iExists (flat_map serialize_atom o :: wss_tail).
      iSplit.
      { iPureIntro. injection Hoseq as Hoseq. rewrite Hoseq. cbn. by rewrite flat_map_app Htaileq2. }
      iEval (rewrite big_sepL2_cons).
      iFrame.
  Qed.

  Lemma pre_type_interp_prod_ser F se τs τs' ρs ξs ρs2 ξs2 sv :
    sem_env_interp F se ->
    Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs ρs ξs ->
    Forall3 (fun τ' ρ ξ => has_kind F τ' (VALTYPE ρ ξ)) τs' ρs2 ξs2 ->
    Forall2 type_eq τs τs' ->
    Forall2 (fun τ τ' => forall sv, type_interp rti sr τ se sv ⊣⊢ type_interp rti sr τ' se sv) τs τs' ->
    pre_type_interp rti sr
      (StructT (MEMTYPE (ProdS (map RepS ρs2)) (ref_flag_lub ξs2))
         (zip_with SerT (map (fun ρξ => MEMTYPE (RepS ρξ.1) ρξ.2) (zip ρs2 ξs2)) τs')) se sv
    ⊣⊢
    pre_type_interp rti sr (SerT (MEMTYPE (RepS (ProdR ρs)) (ref_flag_lub ξs)) (ProdT (VALTYPE (ProdR ρs) (ref_flag_lub ξs)) τs)) se sv.
  Proof.
    intros Hsem H H' Heqtyp IH.
    apply Forall3_length_lm in H' as Hlen2'.
    apply Forall3_length_lr in H' as Hlen2.
    iSplit.
    - iIntros "Hstruct".
      cbn. iDestruct "Hstruct" as (wss) "(-> & Hser)".
      rewrite big_sepL2_fmap_r.
      iDestruct (big_sepL2_length with "Hser") as "%Hlenwss".
      assert (length wss = length τs') as Hlenwss'.
      { rewrite Hlenwss length_zip_with length_map length_zip. lia. }
      iDestruct (struct_fields_to_prod_atoms F se τs τs' ρs ξs ρs2 ξs2 wss
                   Hsem H H' Heqtyp IH Hlenwss' with "Hser") as (os) "(%Hoseq & Hos)".
      iExists os. rewrite -Hoseq. by iFrame.
    - iIntros "Hser".
      cbn. iDestruct "Hser" as (os) "(-> & Hprod)".
      iDestruct (prod_atoms_to_struct_fields F se τs τs' ρs ξs ρs2 ξs2 os
                   Hsem H H' Heqtyp IH with "Hprod") as (wss) "(%Hwseq & Hstruct)".
      iExists wss. rewrite Hwseq. iSplit; first done.
      rewrite big_sepL2_fmap_r. iFrame.
  Qed.

  Lemma big_sepL2_svr_transport {A : Type} (Ts Ts' : list (semantic_type (Σ:=Σ)))
      (xs : list A) (f : semantic_type -> A -> iProp Σ) :
    Forall2 (fun T T' => forall x, f T x ⊣⊢ f T' x) Ts Ts' ->
    ([∗ list] T;x ∈ Ts;xs, f T x) ⊣⊢ ([∗ list] T;x ∈ Ts';xs, f T x).
  Proof.
    intros HF2.
    revert xs.
    induction HF2 as [|T T' Ts Ts' HTT' HF2 IH]; intros xs; first done.
    destruct xs as [|x xs].
    - iSplit; iIntros "H"; iDestruct (big_sepL2_length with "H") as %Hlen; done.
    - rewrite !big_sepL2_cons HTT' IH.
      done.
  Qed.



  Lemma type_interp_type_eq :
    forall τ τ',
      type_eq τ τ' ->
      forall F κ κ' se sv,
        has_kind F τ κ ->
        has_kind F τ' κ' ->
        sem_env_interp F se ->
        type_interp rti sr τ se sv ⊣⊢ type_interp rti sr τ' se sv.
  Proof.
    apply (type_eq_ind'
             (fun τ τ' =>
                forall F κ κ' se sv,
                  has_kind F τ κ ->
                  has_kind F τ' κ' ->
                  sem_env_interp F se ->
                  type_interp rti sr τ se sv ⊣⊢ type_interp rti sr τ' se sv)).
    - done.
    - (* Sum *)
      intros κ0 τs τs' Heq IH F κ κ' se sv Hkind Hkind' Hsem.
      rewrite !type_interp_eq.
      inversion Hkind; subst.
      inversion Hkind'; subst.
      iSplit; iIntros "H".
      + iDestruct "H" as (sκ) "(%Hsk & %Hsv & Hsum)".
        iExists sκ.
        iSplit; first (iPureIntro; exact Hsk).
        iSplit; first done.
        simpl.
        iDestruct "Hsum" as (i os off count ->) "(%Hoff & %Hcount & HTi)".
        iExists i, os, off, count.
        do 3 (iSplit; first done).
        destruct (τs !! i) as [τi_raw|] eqn:Hiraw.
        * eapply (Forall2_lookup_l) in Heq as [τi_raw' [Hiraw' Heqi]]; last exact Hiraw.
          iEval (change (list_lookup i (map (type_interp rti sr) τs)) with ((type_interp rti sr <$> τs) !! i); rewrite list_lookup_fmap Hiraw; cbn) in "HTi".
          iEval (change (list_lookup i (map (type_interp rti sr) τs')) with ((type_interp rti sr <$> τs') !! i); rewrite list_lookup_fmap Hiraw'; cbn).
          eapply Forall3_lookup_l in H3, H5; try done.
          destruct H3 as (? & ? & ? & ? & ?).
          destruct H5 as (? & ? & ? & ? & ?).
          eapply Forall2_lookup_lr in IH; try done.
          iApply IH; try done.
        * iEval (change (list_lookup i (map (type_interp rti sr) τs)) with ((type_interp rti sr <$> τs) !! i); rewrite list_lookup_fmap Hiraw; cbn) in "HTi".
          iDestruct "HTi" as "[]".
      + iDestruct "H" as (sκ) "(%Hsk & %Hsv & Hsum)".
        iExists sκ.
        iSplit; first (iPureIntro; exact Hsk).
        iSplit; first done.
        simpl.
        iDestruct "Hsum" as (i os off count ->) "(%Hoff & %Hcount & HTi)".
        iExists i, os, off, count.
        do 3 (iSplit; first done).
        destruct (τs' !! i) as [τi_raw'|] eqn:Hiraw'.
        * eapply (Forall2_lookup_r) in Heq as [τi_raw [Hiraw Heqi]]; last exact Hiraw'.
          iEval (change (list_lookup i (map (type_interp rti sr) τs')) with ((type_interp rti sr <$> τs') !! i); rewrite list_lookup_fmap Hiraw'; cbn) in "HTi".
          iEval (change (list_lookup i (map (type_interp rti sr) τs)) with ((type_interp rti sr <$> τs) !! i); rewrite list_lookup_fmap Hiraw; cbn).
          eapply Forall3_lookup_l in H3, H5; try done.
          destruct H3 as (? & ? & ? & ? & ?).
          destruct H5 as (? & ? & ? & ? & ?).
          eapply Forall2_lookup_lr in IH; try done.
          iApply IH; try done.
        * iEval (change (list_lookup i (map (type_interp rti sr) τs')) with ((type_interp rti sr <$> τs') !! i); rewrite list_lookup_fmap Hiraw'; cbn) in "HTi".
          iDestruct "HTi" as "[]".
    - (* Variant *)
      intros κ0 τs τs' Heq IH F κ κ' se sv Hκ Hκ' Hsem.
      rewrite !type_interp_eq.
      inversion Hκ; subst.
      inversion Hκ'; subst.
      iSplit; iIntros "H".
      + iDestruct "H" as (sκ) "(%Hsk & %Hsv & Hvar)".
        iExists sκ.
        iSplit; first (iPureIntro; exact Hsk).
        iSplit; first done.
        simpl.
        iDestruct "Hvar" as (i n ws ws' Hrepr ->) "HTi".
        iExists i, n, ws, ws'.
        do 2 (iSplit; first done).
        destruct (τs !! i) as [τi_raw|] eqn:Hiraw.
        * eapply (Forall2_lookup_l) in Heq as [τi_raw' [Hiraw' Heqi]]; last exact Hiraw.

          iEval (change (list_lookup i (map (type_interp rti sr) τs)) with ((type_interp rti sr <$> τs) !! i); rewrite list_lookup_fmap Hiraw; cbn) in "HTi".

          iEval (change (list_lookup i (map (type_interp rti sr) τs')) with ((type_interp rti sr <$> τs') !! i); rewrite list_lookup_fmap Hiraw'; cbn).

          eapply Forall3_lookup_l in H3, H5; try done.
          destruct H3 as (? & ? & ? & ? & ?).
          destruct H5 as (? & ? & ? & ? & ?).
          eapply Forall2_lookup_lr in IH; try done.
          iApply IH; try done.

        * iEval (change (list_lookup i (map (type_interp rti sr) τs)) with ((type_interp rti sr <$> τs) !! i); rewrite list_lookup_fmap Hiraw; cbn) in "HTi".
          iDestruct "HTi" as "[]".
      + iDestruct "H" as (sκ) "(%Hsk & %Hsv & Hvar)".
        iExists sκ.
        iSplit; first (iPureIntro; exact Hsk).
        iSplit; first done.
        simpl.
        iDestruct "Hvar" as (i n ws ws' Hrepr ->) "HTi".
        iExists i, n, ws, ws'.
        do 2 (iSplit; first done).
        destruct (τs' !! i) as [τi_raw'|] eqn:Hiraw'.
        * eapply (Forall2_lookup_r) in Heq as [τi_raw [Hiraw Heqi]]; last exact Hiraw'.
          iEval (change (list_lookup i (map (type_interp rti sr) τs')) with ((type_interp rti sr <$> τs') !! i); rewrite list_lookup_fmap Hiraw'; cbn) in "HTi".
          iEval (change (list_lookup i (map (type_interp rti sr) τs)) with ((type_interp rti sr <$> τs) !! i); rewrite list_lookup_fmap Hiraw; cbn).
          eapply Forall3_lookup_l in H3, H5; try done.
          destruct H3 as (? & ? & ? & ? & ?).
          destruct H5 as (? & ? & ? & ? & ?).
          eapply Forall2_lookup_lr in IH; try done.
          iApply IH; try done.
        * iEval (change (list_lookup i (map (type_interp rti sr) τs')) with ((type_interp rti sr <$> τs') !! i); rewrite list_lookup_fmap Hiraw'; cbn) in "HTi".
          iDestruct "HTi" as "[]".
    - (* Product *)
      intros κ0 τs τs' Heq IH F κ κ' se sv Hκ Hκ' Hsem.
      rewrite !type_interp_eq.
      inversion Hκ; subst.
      inversion Hκ'; subst.
      iSplit; iIntros "H".
      + iDestruct "H" as (sκ) "(%Hsk & %Hsv & Hprod)".
        iExists sκ.
        iSplit; first (iPureIntro; exact Hsk).
        iSplit; first done.
        simpl.
        iDestruct "Hprod" as "(%oss & -> & Hbig)".
        iSimpl. iExists oss. iSplit; first done.
        iApply (big_sepL2_svr_transport _ (map (type_interp rti sr) τs') with "Hbig").
        apply Forall2_fmap_2.
        eapply Forall2_mini_impl; try done.
        apply Forall2_same_length_lookup_2.
        { exact (Forall2_length _ _ _ Heq). }
        intros i a b Hai Hbi Hpair x.
        destruct (Forall3_lookup_l _ _ _ _ _ _ H3 Hai) as (ρ & ξ & _ & _ & Hka).
        destruct (Forall3_lookup_l _ _ _ _ _ _ H5 Hbi) as (ρ' & ξ' & _ & _ & Hkb).
        by eapply Hpair.
      + iDestruct "H" as (sκ) "(%Hsk & %Hsv & Hprod)".
        iExists sκ.
        iSplit; first (iPureIntro; exact Hsk).
        iSplit; first done.
        simpl.
        iDestruct "Hprod" as "(%oss & -> & Hbig)".
        iSimpl.
        iExists oss.
        iSplit; first done.
        iApply (big_sepL2_svr_transport _ (map (type_interp rti sr) τs) with "Hbig").
        apply Forall2_fmap_2.
        apply Forall2_same_length_lookup_2.
        { exact (eq_sym (Forall2_length _ _ _ Heq)). }
        intros i b a Hbi Hai x0.
        destruct (Forall3_lookup_l _ _ _ _ _ _ H3 Hai) as (ρ & ξ & _ & _ & Hka).
        destruct (Forall3_lookup_l _ _ _ _ _ _ H5 Hbi) as (ρ' & ξ' & _ & _ & Hkb).
        eapply Forall2_lookup_lr in IH; try done.
        symmetry.
        exact (IH F _ _ se (SAtoms x0) Hka Hkb Hsem).
    - (* Struct *)
      intros κ0 τs τs' Heq IH F κ κ' se sv Hκ Hκ' Hsem.
      rewrite !type_interp_eq.
      inversion Hκ; subst.
      inversion Hκ'; subst.
      iSplit; iIntros "H".
      + iDestruct "H" as (wss) "(%Hwss & Hbig)".
        iDestruct "Hbig" as "(%Hsv & Hstruct)".
        iExists wss.
        iSplitL "". { iPureIntro. exact Hwss. }
        iSplitL "". { iPureIntro. exact Hsv. }
        simpl.
        iDestruct "Hstruct" as (wss0) "(%Hwss0 & Hbig)".
        iExists wss0. iSplit; first done.
        iEval (rewrite big_sepL2_flip) in "Hbig".
        iEval (rewrite big_sepL2_flip).
        iApply (big_sepL2_svr_transport _ (map (type_interp rti sr) τs') with "Hbig").
        apply Forall2_fmap_2.
        eapply Forall2_mini_impl; try done.
        apply Forall2_same_length_lookup_2.
        { exact (Forall2_length _ _ _ Heq). }
        intros i a b Hai Hbi Hpair ws.
        destruct (Forall3_lookup_l _ _ _ _ _ _ H3 Hai) as (σ & ξ & _ & _ & Hka).
        destruct (Forall3_lookup_l _ _ _ _ _ _ H5 Hbi) as (σ' & ξ' & _ & _ & Hkb).
        by eapply Hpair.
      + iDestruct "H" as (wss) "(%Hwss & Hbig)".
        iDestruct "Hbig" as "(%Hsv & Hstruct)".
        iExists wss.
        iSplitL "". { iPureIntro. exact Hwss. }
        iSplitL "". { iPureIntro. exact Hsv. }
        simpl.
        iDestruct "Hstruct" as (wss0) "(%Hwss0 & Hbig)".
        iExists wss0. iSplit; first done.
        iEval (rewrite big_sepL2_flip) in "Hbig".
        iEval (rewrite big_sepL2_flip).
        iApply (big_sepL2_svr_transport _ (map (type_interp rti sr) τs) with "Hbig").
        apply Forall2_fmap_2.
        apply Forall2_same_length_lookup_2.
        { exact (eq_sym (Forall2_length _ _ _ Heq)). }
        intros i b a Hbi Hai ws.
        destruct (Forall3_lookup_l _ _ _ _ _ _ H3 Hai) as (σ & ξ & _ & _ & Hka).
        destruct (Forall3_lookup_l _ _ _ _ _ _ H5 Hbi) as (σ' & ξ' & _ & _ & Hkb).
        eapply Forall2_lookup_lr in IH; try done.
        symmetry.
        exact (IH F _ _ se (SWords ws) Hka Hkb Hsem).
    - intros κ0 μ β τ τ' Heq IH F κ κ' se sv Hκ Hκ' Hsem.
      destruct (has_kind_ref_ty _ _ _ _ _ _ Hκ) as (σ & ξ & Hkτ).
      destruct (has_kind_ref_ty _ _ _ _ _ _ Hκ') as (σ' & ξ' & Hkτ').
      assert (∀ sv, type_interp rti sr τ se sv ⊣⊢ type_interp rti sr τ' se sv) as Heqτ.
      { intros sv'. exact (IH F _ _ se sv' Hkτ Hkτ' Hsem). }
      rewrite !type_interp_eq /add_skind_interp /=.
      iSplit.
      { iIntros "(%sκ & %Hsk & %Hsv & Hr)".
        iExists sκ. iSplit; first done. iSplit; first done.
        destruct (eval_mem se μ) as [bm|] eqn:Hμ; try rewrite Hμ.
        2: { iDestruct "Hr" as "[]". }
        destruct bm, β.
        { iDestruct "Hr" as "(%ℓ & %fs & %ws & %Hsveq & Hlayout & Hheap & Hτ)".
          iExists ℓ, fs, ws. iSplit; first done. iFrame.
          iEval (rewrite Heqτ) in "Hτ". iExact "Hτ". }
        { iDestruct "Hr" as "(%ℓ & %fs & %ws & %Hsveq & Hinv & Hτ)".
          iExists ℓ, fs, ws. iSplit; first done. iFrame.
          iEval (rewrite Heqτ) in "Hτ". iExact "Hτ". }
        { iDestruct "Hr" as "(%ℓ & %fs & %Hsveq & Hinv)".
          iExists ℓ, fs. iSplit; first done.
          iApply (na_inv_iff with "Hinv").
          repeat iModIntro.
          iSplitR; iIntros "Hlocal".
          + iDestruct "Hlocal" as "(%ws & Hlayout & Hheap & Hτ)".
            iExists ws. iFrame.
            iEval (rewrite Heqτ) in "Hτ". iExact "Hτ".
          + iDestruct "Hlocal" as "(%ws & Hlayout & Hheap & Hτ)".
            iExists ws. iFrame.
            iEval (rewrite -Heqτ) in "Hτ". iExact "Hτ". }
        { iDestruct "Hr" as "(%ℓ & %fs & %ws & %Hsveq & Hinv)".
          iExists ℓ, fs, ws. iSplit; first done.
          iApply (na_inv_iff with "Hinv").
          repeat iModIntro.
          iSplitR; iIntros "Hlocal".
          + iDestruct "Hlocal" as "(Hlayout & Hheap & Hτ)".
            iFrame.
            iEval (rewrite Heqτ) in "Hτ". iExact "Hτ".
          + iDestruct "Hlocal" as "(Hlayout & Hheap & Hτ)".
            iFrame.
            iEval (rewrite -Heqτ) in "Hτ". iExact "Hτ". } }
      { iIntros "(%sκ & %Hsk & %Hsv & Hr)".
        iExists sκ. iSplit; first done. iSplit; first done.
        destruct (eval_mem se μ) as [bm|] eqn:Hμ; try rewrite Hμ.
        2: { iDestruct "Hr" as "[]". }
        destruct bm, β.
        { iDestruct "Hr" as "(%ℓ & %fs & %ws & %Hsveq & Hlayout & Hheap & Hτ)".
          iExists ℓ, fs, ws. iSplit; first done. iFrame.
          iEval (rewrite -Heqτ) in "Hτ". iExact "Hτ". }
        { iDestruct "Hr" as "(%ℓ & %fs & %ws & %Hsveq & Hinv & Hτ)".
          iExists ℓ, fs, ws. iSplit; first done. iFrame.
          iEval (rewrite -Heqτ) in "Hτ". iExact "Hτ". }
        { iDestruct "Hr" as "(%ℓ & %fs & %Hsveq & Hinv)".
          iExists ℓ, fs. iSplit; first done.
          iApply (na_inv_iff with "Hinv").
          repeat iModIntro.
          iSplitR; iIntros "Hlocal".
          + iDestruct "Hlocal" as "(%ws & Hlayout & Hheap & Hτ)".
            iExists ws. iFrame.
            iEval (rewrite -Heqτ) in "Hτ". iExact "Hτ".
          + iDestruct "Hlocal" as "(%ws & Hlayout & Hheap & Hτ)".
            iExists ws. iFrame.
            iEval (rewrite Heqτ) in "Hτ". iExact "Hτ". }
        { iDestruct "Hr" as "(%ℓ & %fs & %ws & %Hsveq & Hinv)".
          iExists ℓ, fs, ws. iSplit; first done.
          iApply (na_inv_iff with "Hinv").
          repeat iModIntro.
          iSplitR; iIntros "Hlocal".
          + iDestruct "Hlocal" as "(Hlayout & Hheap & Hτ)".
            iFrame.
            iEval (rewrite -Heqτ) in "Hτ". iExact "Hτ".
          + iDestruct "Hlocal" as "(Hlayout & Hheap & Hτ)".
            iFrame.
            iEval (rewrite Heqτ) in "Hτ". iExact "Hτ". } }
    - (* Ser *)
      intros κ0 τ τ' Heq IH F κ κ' se sv Hκ Hκ' Hsem.
      inversion Hκ; subst.
      inversion Hκ'; subst.
      match goal with Hk : has_kind F τ (VALTYPE _ _) |- _ => rename Hk into Hkτ end.
      match goal with Hk : has_kind F τ' (VALTYPE _ _) |- _ => rename Hk into Hkτ' end.
      rewrite !type_interp_eq.
      iSplit.
      + iIntros "H".
        iDestruct "H" as (sκ) "(%Hsk & %Hsv & Hser)".
        iExists sκ.
        iSplit; first (iPureIntro; exact Hsk).
        iSplit; first done.
        iDestruct "Hser" as (os) "[%Hws Hτ]".
        iExists os.
        iSplit; first done.
        by iEval (rewrite (IH F _ _ se _ Hkτ Hkτ' Hsem)) in "Hτ".
      + iIntros "H".
        iDestruct "H" as (sκ) "(%Hsk & %Hsv & Hser)".
        iExists sκ.
        iSplit; first (iPureIntro; exact Hsk).
        iSplit; first done.
        iDestruct "Hser" as (os) "[%Hws Hτ]".
        iExists os.
        iSplit; first done.
        by iEval (rewrite -(IH F _ _ se _ Hkτ Hkτ' Hsem)) in "Hτ".
    - (* RecT *)
      intros κ0 τ τ' Heq IH F κ κ' se sv Hκ Hκ' Hsem.
      inversion Hκ'; subst.
      inversion Hκ; subst.
      specialize (IH (F <| fc_type_vars ::= cons κ |>) κ κ).
      assert (kind_ok (fc_kind_ctx F) κ) as Hok.
      { eapply has_kind_inv in Hκ. by inversion Hκ. }
      destruct (eval_kind_ok_Some F se κ Hsem Hok) as [sκ Heval].
      assert (∀ τ sv, type_interp rti sr (RecT κ τ) se sv ⊣⊢
                add_skind_interp_closed sκ (skind_rec_interp sκ (type_interp rti sr τ) se) sv)
      as Hrec_eq.
      {
        intros τ0 sv0.
        rewrite type_interp_eq /add_skind_interp /=.
        change (eval_kind_se se κ) with (eval_kind se κ).
        rewrite Heval.
        iSplit.
        - iIntros "(%sκ0 & %Hsk0 & %Hsv0 & H)".
          injection Hsk0 as <-.
          iFrame. done.
        - iIntros "(%Hsv0 & H)".
          iExists sκ. iSplit; first done.
          iFrame. done.
      }
      assert (∀ τ, has_kind F (RecT κ τ) κ ->
                sem_env_interp (F <| fc_type_vars ::= cons κ |>)
                  (senv_insert_type sκ sκ
                     (add_skind_interp_closed sκ (skind_rec_interp sκ (type_interp rti sr τ) se))
                     se))
      as Hself_sem.
      {
        intros τ0 Hkτ0.
        eapply sem_env_interp_insert_type; eauto.
        - apply subskind_of_refl.
        - assert (Hkt : skind_has_stype sκ (value_interp rti sr se (RecT κ τ0))).
          { eapply kinding_sound; eauto. }
          change (value_interp rti sr se (RecT κ τ0)) with (type_interp rti sr (RecT κ τ0) se) in Hkt.
          unfold skind_has_stype in *.
          destruct Hkt as [Hrf Hsv].
          split.
          + revert Hrf. unfold ref_flag_stype_interp.
            destruct (skind_ref_flag sκ); try done.
            all: intros Hp sv0; specialize (Hp sv0); by rewrite (Hrec_eq τ0 sv0) in Hp.
          + intros sv0. specialize (Hsv sv0). by rewrite (Hrec_eq τ0 sv0) in Hsv.
      }
      assert (skind_rec_interp sκ (type_interp rti sr τ) se ≡
              skind_rec_interp sκ (type_interp rti sr τ') se) as Hself_eq.
      {
        apply fixpoint_unique.
        intros sv0.
        rewrite (skind_rec_interp_unfold sκ (type_interp rti sr τ) se sv0).
        cbn.
        f_equiv.
        apply (IH _ sv0 H4 H3 (Hself_sem τ Hκ)).
      }
      rewrite (Hrec_eq τ sv) (Hrec_eq τ' sv).
      f_equiv.
      f_equiv.
      apply Hself_eq.
    - intros κ0 τ τ' Heq IH F κ κ' se sv Hκ Hκ' Hsem.
      (* TEqExMem *)
      inversion Hκ; subst. inversion Hκ'; subst.
      match goal with Hk : has_kind (F <| fc_kind_ctx; kc_mem_vars ::= S |>) τ _ |- _ =>
        rename Hk into Hkτ end.
      match goal with Hk : has_kind (F <| fc_kind_ctx; kc_mem_vars ::= S |>) τ' _ |- _ =>
        rename Hk into Hkτ' end.
      rewrite !type_interp_eq /add_skind_interp /=.
      iSplit.
      + iIntros "(%sκ & %Hsk & %Hsv & %μ & Hτ)".
        iExists sκ. iSplit; first done. iSplit; first done.
        iExists μ.
        iApply IH; [done|done|by apply sem_env_insert_mem|iExact "Hτ"].
      + iIntros "(%sκ & %Hsk & %Hsv & %μ & Hτ)".
        iExists sκ. iSplit; first done. iSplit; first done.
        iExists μ.
        iApply IH; [done|done|by apply sem_env_insert_mem|iExact "Hτ"].
    - (* ExistsRep *)
      intros κ0 τ τ' Heq IH F κ κ' se sv Hκ Hκ' Hsem.
      inversion Hκ; subst. inversion Hκ'; subst.
      rewrite !type_interp_eq /add_skind_interp /=.
      iSplit.
      + iIntros "(%sκ & %Hsk & %Hsv & %ιs & Hτ)".
        iExists sκ. iSplit; first done. iSplit; first done.
        iExists ιs.
        iApply IH; [done|done|by apply sem_env_insert_rep|iExact "Hτ"].
      + iIntros "(%sκ & %Hsk & %Hsv & %ιs & Hτ)".
        iExists sκ. iSplit; first done. iSplit; first done.
        iExists ιs.
        iApply IH; [done|done|by apply sem_env_insert_rep|iExact "Hτ"].
    - (* ExistsSize *)
      intros κ0 τ τ' Heq IH F κ κ' se sv Hκ Hκ' Hsem.
      inversion Hκ; subst. inversion Hκ'; subst.
      rewrite !type_interp_eq /add_skind_interp /=.
      iSplit.
      + iIntros "(%sκ & %Hsk & %Hsv & %n & Hτ)".
        iExists sκ. iSplit; first done. iSplit; first done.
        iExists n.
        iApply IH; [done|done|by apply sem_env_insert_size|iExact "Hτ"].
      + iIntros "(%sκ & %Hsk & %Hsv & %n & Hτ)".
        iExists sκ. iSplit; first done. iSplit; first done.
        iExists n.
        iApply IH; [done|done|by apply sem_env_insert_size|iExact "Hτ"].
    - intros κ0 κτ τ τ' Heq IH F κ κ' se sv Hκ Hκ' Hsem.
      (* TEqExType *)
      inversion Hκ; subst. inversion Hκ'; subst.
      match goal with Hk : has_kind (F <| fc_type_vars ::= cons κτ |>) τ _ |- _ =>
        rename Hk into Hkτ end.
      match goal with Hk : has_kind (F <| fc_type_vars ::= cons κτ |>) τ' _ |- _ =>
        rename Hk into Hkτ' end.
      rewrite !type_interp_eq /add_skind_interp /=.
      iSplit.
      + iIntros "(%sκ & %Hsk & %Hsv & %T' & %sκ0 & %sκ_T & %Heval & %HsT & %Hskst & Hτ)".
        iExists sκ. iSplit; first done. iSplit; first done.
        iExists T', sκ0, sκ_T. iSplit; first done. iSplit; first done. iSplit; first done.
        iApply IH; [done|done|by apply sem_env_interp_insert_type|iExact "Hτ"].
      + iIntros "(%sκ & %Hsk & %Hsv & %T' & %sκ0 & %sκ_T & %Heval & %HsT & %Hskst & Hτ)".
        iExists sκ. iSplit; first done. iSplit; first done.
        iExists T', sκ0, sκ_T. iSplit; first done. iSplit; first done. iSplit; first done.
        iApply IH; [done|done|by apply sem_env_interp_insert_type|iExact "Hτ"].
    - (* Ser Struct *)
      intros κ_ser κ_prod κ_struct κs_ser τs τs' Hlen Heq IH F κ κ' se sv Hκ Hκ' Hsem.
      assert (eval_kind se κ = eval_kind se κ') as Heval_kind.
      { eapply type_eq_eval_kind_agree; [ | done | apply Hκ']; by constructor. }
      inversion Hκ; subst.
      inversion H3; subst.
      inversion Hκ'; subst.
      destruct (struct_fields_ser_inv _ _ _ _ _ H5 Hlen) as (ρs2 & -> & Hκseq & HF3'').
      rewrite !type_interp_eq /add_skind_interp.
      assert (
        Forall2
          (λ τ τ' : type,
            ∀ (sv0 : leibnizO semantic_value),
              type_interp rti sr τ se sv0 ⊣⊢ type_interp rti sr τ' se sv0)
        τs τs'
      ) as IH'.
      {
        eapply Forall2_mini_impl; try done.
        apply Forall2_same_length_lookup_2.
        { exact (Forall2_length _ _ _ Heq). }
        intros i a b Hai Hbi Hpair sv'.
        apply lookup_lt_Some in Hbi as Hilen.
        rewrite -Hlen in Hilen.
        apply lookup_lt_is_Some in Hilen as [κ_ser Hklookup].
        assert ((zip_with SerT κs_ser τs') !! i = Some $ SerT κ_ser b) as Hzlookup.
        {
          apply lookup_zip_with_Some.
          eauto.
        }
        destruct (Forall3_lookup_l _ _ _ _ _ _ H1 Hai) as (ρ & ξ & _ & _ & Hka).
        destruct (Forall3_lookup_l _ _ _ _ _ _ H5 Hzlookup) as (ρ' & ξ' & _ & _ & Hkb).
        inversion Hkb; subst.
        eapply Hpair; try done.
      }
      clear IH.
      iSplit.
      + iIntros "(%sκ & %Hsk & %Hsv & Hser)".
        Opaque eval_kind.
        cbn in Hsk.
        Transparent eval_kind.
        rewrite Hsk in Heval_kind.
        iExists sκ.
        iSplit.
        { iPureIntro. Opaque eval_kind. cbn. Transparent eval_kind. exact (eq_sym Heval_kind). }
        iSplit; first done.
        rewrite Hκseq.
        iApply (pre_type_interp_prod_ser F se τs τs' _ _ ρs2 _ sv Hsem H1 HF3'' Heq IH' with "Hser").
      + iIntros "(%sκ & %Hsk & %Hsv & Hstruct)".
        Opaque eval_kind.
        cbn in Hsk.
        Transparent eval_kind.
        rewrite Hsk in Heval_kind.
        iExists sκ.
        iSplit.
        { iPureIntro. Opaque eval_kind. cbn. Transparent eval_kind. exact Heval_kind. }
        iSplit; first done.
        rewrite Hκseq.
        iApply (pre_type_interp_prod_ser F se τs τs' _ _ ρs2 _ sv Hsem H1 HF3'' Heq IH' with "Hstruct").
    - (* Struct Ser *)
      intros κ_ser κ_prod κ_struct κs_ser τs τs' Hlen Heq IH F κ κ' se sv Hκ Hκ' Hsem.
      assert (eval_kind se κ = eval_kind se κ') as Heval_kind.
      { eapply type_eq_eval_kind_agree; [ | done | apply Hκ']; by constructor. }
      inversion Hκ'; subst.
      inversion H3; subst.
      inversion Hκ; subst.
      destruct (struct_fields_ser_inv _ _ _ _ _ H5 Hlen) as (ρs2 & -> & Hκseq & HF3'').
      rewrite !type_interp_eq /add_skind_interp.
      assert (
        Forall2
          (λ τ τ' : type,
            ∀ (sv0 : leibnizO semantic_value),
              type_interp rti sr τ se sv0 ⊣⊢ type_interp rti sr τ' se sv0)
        τs τs'
      ) as IH'.
      {
        eapply Forall2_mini_impl; try done.
        apply Forall2_same_length_lookup_2.
        { exact (Forall2_length _ _ _ Heq). }
        intros i a b Hai Hbi Hpair sv'.
        apply lookup_lt_Some in Hai as Hilen.
        rewrite -Hlen in Hilen.
        apply lookup_lt_is_Some in Hilen as [κ_ser Hklookup].
        assert ((zip_with SerT κs_ser τs) !! i = Some $ SerT κ_ser a) as Hzlookup.
        {
          apply lookup_zip_with_Some.
          eauto.
        }
        destruct (Forall3_lookup_l _ _ _ _ _ _ H1 Hbi) as (ρ & ξ & _ & _ & Hka).
        destruct (Forall3_lookup_l _ _ _ _ _ _ H5 Hzlookup) as (ρ' & ξ' & _ & _ & Hkb).
        inversion Hkb; subst.
        eapply Hpair; try done.
      }
      clear IH.
      have Hsym :
          Symmetric
            (λ τ τ' : type,
              ∀ (sv0 : leibnizO semantic_value),
                type_interp rti sr τ se sv0 ⊣⊢
                type_interp rti sr τ' se sv0).
      {
        intros τ τ' H sv0.
        symmetry.
        apply H.
      }
      symmetry in Heq.
      symmetry in IH'.
      iSplit.
      + iIntros "(%sκ & %Hsk & %Hsv & Hser)".
        Opaque eval_kind.
        cbn in Hsk.
        Transparent eval_kind.
        rewrite Hsk in Heval_kind.
        iExists sκ.
        iSplit.
        { iPureIntro. Opaque eval_kind. cbn. Transparent eval_kind. exact (eq_sym Heval_kind). }
        iSplit; first done.
        iEval (rewrite Hκseq) in "Hser".
        iApply (pre_type_interp_prod_ser F se τs' τs _ _ ρs2 _ sv Hsem H1 HF3'' Heq IH' with "Hser").
      + iIntros "(%sκ & %Hsk & %Hsv & Hstruct)".
        Opaque eval_kind.
        cbn in Hsk.
        Transparent eval_kind.
        rewrite Hsk in Heval_kind.
        iExists sκ.
        iSplit.
        { iPureIntro. Opaque eval_kind. cbn. Transparent eval_kind. exact Heval_kind. }
        iSplit; first done.
        rewrite Hκseq.
        iApply (pre_type_interp_prod_ser F se τs' τs _ _ ρs2 _ sv Hsem H1 HF3'' Heq IH' with "Hstruct").
  Qed.

End type_eq_sem.
