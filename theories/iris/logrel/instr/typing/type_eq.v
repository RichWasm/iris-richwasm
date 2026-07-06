Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.env_props.
Require Import RichWasm.iris.logrel.instr.kinding.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

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

  Lemma flat_map_concat {A B} (f : A -> list B) (ls : list (list A)) :
    flat_map f (concat ls) = concat (map (flat_map f) ls).
  Proof.
    induction ls as [|l ls IH]; cbn; first done.
    rewrite flat_map_app IH.
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
      intros κ0 τs τs' Heq IH F κ κ' se sv Hkind Hkind' Hse.
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
      intros κ0 τs τs' Heq IH F κ κ' se sv Hκ Hκ' Hse.
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
      intros κ0 τs τs' Heq IH F κ κ' se sv Hκ Hκ' Hse.
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
        exact (IH F _ _ se (SAtoms x0) Hka Hkb Hse).
    - (* Struct *)
      intros κ0 τs τs' Heq IH F κ κ' se sv Hκ Hκ' Hse.
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
        exact (IH F _ _ se (SWords ws) Hka Hkb Hse).
    - intros κ0 μ β τ τ' Heq IH F κ κ' se sv Hκ Hκ' Hse.
      destruct (has_kind_ref_ty _ _ _ _ _ _ Hκ) as (σ & ξ & Hkτ).
      destruct (has_kind_ref_ty _ _ _ _ _ _ Hκ') as (σ' & ξ' & Hkτ').
      rewrite !type_interp_eq /add_skind_interp /=.
      iSplit.
      { iIntros "(%sκ & %Hsk & %Hsv & Hr)".
        iExists sκ. iSplit; first done. iSplit; first done.
        destruct (eval_mem se μ) as [bm|] eqn:Hμ.
        2: { iDestruct "Hr" as "[]". }
        destruct bm, β.
        { iDestruct "Hr" as "(%ℓ & %fs & %ws & %Hsveq & Hlayout & Hheap & Hτ)".
          iExists ℓ, fs, ws. iSplit; first done. iFrame.
          iEval (rewrite (IH F _ _ se _ Hkτ Hkτ' Hse)) in "Hτ". iExact "Hτ". }
        { iDestruct "Hr" as "(%ℓ & %fs & %ws & %Hsveq & Hinv & Hτ)".
          iExists ℓ, fs, ws. iSplit; first done. iFrame.
          iEval (rewrite (IH F _ _ se _ Hkτ Hkτ' Hse)) in "Hτ". iExact "Hτ". }
        { iDestruct "Hr" as "(%ℓ & %fs & %Hsveq & Hinv)".
          iExists ℓ, fs. iSplit; first done.
          iApply (na_inv_iff with "Hinv").
          repeat iModIntro.
          iSplitR; iIntros "Hlocal".
          + iDestruct "Hlocal" as "(%ws & Hlayout & Hheap & Hτ)".
            iExists ws. iFrame.
            iEval (rewrite (IH F _ _ se _ Hkτ Hkτ' Hse)) in "Hτ". iExact "Hτ".
          + iDestruct "Hlocal" as "(%ws & Hlayout & Hheap & Hτ)".
            iExists ws. iFrame.
            iEval (rewrite -(IH F _ _ se _ Hkτ Hkτ' Hse)) in "Hτ". iExact "Hτ". }
        { iDestruct "Hr" as "(%ℓ & %fs & %ws & %Hsveq & Hinv)".
          iExists ℓ, fs, ws. iSplit; first done.
          iApply (na_inv_iff with "Hinv").
          repeat iModIntro.
          iSplitR; iIntros "Hlocal".
          + iDestruct "Hlocal" as "(Hlayout & Hheap & Hτ)".
            iFrame.
            iEval (rewrite (IH F _ _ se _ Hkτ Hkτ' Hse)) in "Hτ". iExact "Hτ".
          + iDestruct "Hlocal" as "(Hlayout & Hheap & Hτ)".
            iFrame.
            iEval (rewrite -(IH F _ _ se _ Hkτ Hkτ' Hse)) in "Hτ". iExact "Hτ". } }
      { iIntros "(%sκ & %Hsk & %Hsv & Hr)".
        iExists sκ. iSplit; first done. iSplit; first done.
        destruct (eval_mem se μ) as [bm|] eqn:Hμ.
        2: { iDestruct "Hr" as "[]". }
        destruct bm, β.
        { iDestruct "Hr" as "(%ℓ & %fs & %ws & %Hsveq & Hlayout & Hheap & Hτ)".
          iExists ℓ, fs, ws. iSplit; first done. iFrame.
          iEval (rewrite -(IH F _ _ se _ Hkτ Hkτ' Hse)) in "Hτ". iExact "Hτ". }
        { iDestruct "Hr" as "(%ℓ & %fs & %ws & %Hsveq & Hinv & Hτ)".
          iExists ℓ, fs, ws. iSplit; first done. iFrame.
          iEval (rewrite -(IH F _ _ se _ Hkτ Hkτ' Hse)) in "Hτ". iExact "Hτ". }
        { iDestruct "Hr" as "(%ℓ & %fs & %Hsveq & Hinv)".
          iExists ℓ, fs. iSplit; first done.
          iApply (na_inv_iff with "Hinv").
          repeat iModIntro.
          iSplitR; iIntros "Hlocal".
          + iDestruct "Hlocal" as "(%ws & Hlayout & Hheap & Hτ)".
            iExists ws. iFrame.
            iEval (rewrite -(IH F _ _ se _ Hkτ Hkτ' Hse)) in "Hτ". iExact "Hτ".
          + iDestruct "Hlocal" as "(%ws & Hlayout & Hheap & Hτ)".
            iExists ws. iFrame.
            iEval (rewrite (IH F _ _ se _ Hkτ Hkτ' Hse)) in "Hτ". iExact "Hτ". }
        { iDestruct "Hr" as "(%ℓ & %fs & %ws & %Hsveq & Hinv)".
          iExists ℓ, fs, ws. iSplit; first done.
          iApply (na_inv_iff with "Hinv").
          repeat iModIntro.
          iSplitR; iIntros "Hlocal".
          + iDestruct "Hlocal" as "(Hlayout & Hheap & Hτ)".
            iFrame.
            iEval (rewrite -(IH F _ _ se _ Hkτ Hkτ' Hse)) in "Hτ". iExact "Hτ".
          + iDestruct "Hlocal" as "(Hlayout & Hheap & Hτ)".
            iFrame.
            iEval (rewrite (IH F _ _ se _ Hkτ Hkτ' Hse)) in "Hτ". iExact "Hτ". } }
    - (* Ser *)
      intros κ0 τ τ' Heq IH F κ κ' se sv Hκ Hκ' Hse.
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
        by iEval (rewrite (IH F _ _ se _ Hkτ Hkτ' Hse)) in "Hτ".
      + iIntros "H".
        iDestruct "H" as (sκ) "(%Hsk & %Hsv & Hser)".
        iExists sκ.
        iSplit; first (iPureIntro; exact Hsk).
        iSplit; first done.
        iDestruct "Hser" as (os) "[%Hws Hτ]".
        iExists os.
        iSplit; first done.
        by iEval (rewrite -(IH F _ _ se _ Hkτ Hkτ' Hse)) in "Hτ".
    - (* RecT *)
      intros κ0 τ τ' Heq IH F κ κ' se sv Hκ Hκ' Hse.
      iEval (rewrite !type_interp_eq /add_skind_interp).
      iSplit.
      + iIntros "(%sκ & %Htsk & %Hsksv & Hrec)".
        iExists sκ.
        iSplit; first done.
        iSplit; first done.
        rewrite /pre_type_interp.
        rewrite !rec_interp_unfold.
        destruct (eval_kind_se se κ0) eqn:H; try done.
        iNext.
        admit.
      + admit.
    - intros κ0 τ τ' Heq IH F κ κ' se sv Hκ Hκ' Hse.
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
        iApply IH; try done.
        by apply sem_env_insert_mem.
      + iIntros "(%sκ & %Hsk & %Hsv & %μ & Hτ)".
        iExists sκ. iSplit; first done. iSplit; first done.
        iExists μ.
        iApply IH; try done.
        by apply sem_env_insert_mem.
    - (* ExistsRep *)
      intros κ0 τ τ' Heq IH F κ κ' se sv Hκ Hκ' Hse.
      inversion Hκ; subst. inversion Hκ'; subst.
      rewrite !type_interp_eq /add_skind_interp /=.
      iSplit.
      + iIntros "(%sκ & %Hsk & %Hsv & %ιs & Hτ)".
        iExists sκ. iSplit; first done. iSplit; first done.
        iExists ιs.
        iApply IH; try done.
        by apply sem_env_insert_rep.
      + iIntros "(%sκ & %Hsk & %Hsv & %ιs & Hτ)".
        iExists sκ. iSplit; first done. iSplit; first done.
        iExists ιs.
        iApply IH; try done.
        by apply sem_env_insert_rep.
    - (* ExistsSize *)
      intros κ0 τ τ' Heq IH F κ κ' se sv Hκ Hκ' Hse.
      inversion Hκ; subst. inversion Hκ'; subst.
      rewrite !type_interp_eq /add_skind_interp /=.
      iSplit.
      + iIntros "(%sκ & %Hsk & %Hsv & %n & Hτ)".
        iExists sκ. iSplit; first done. iSplit; first done.
        iExists n.
        iApply IH; try done.
        by apply sem_env_insert_size.
      + iIntros "(%sκ & %Hsk & %Hsv & %n & Hτ)".
        iExists sκ. iSplit; first done. iSplit; first done.
        iExists n.
        iApply IH; try done.
        by apply sem_env_insert_size.
    - intros κ0 κτ τ τ' Heq IH F κ κ' se sv Hκ Hκ' Hse.
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
        iApply IH; try done.
        apply sem_env_interp_insert_type; try done.
      + iIntros "(%sκ & %Hsk & %Hsv & %T' & %sκ0 & %sκ_T & %Heval & %HsT & %Hskst & Hτ)".
        iExists sκ. iSplit; first done. iSplit; first done.
        iExists T', sκ0, sκ_T. iSplit; first done. iSplit; first done. iSplit; first done.
        iApply IH; try done.
        apply sem_env_interp_insert_type; try done.
    - (* Ser Struct *)
      intros κ_ser κ_prod κ_struct κs_ser τs τs' Hlen Heq IH F κ κ' se sv Hκ Hκ' Hse.
      inversion Hκ; subst. inversion Hκ'; subst.
      rewrite !type_interp_eq /add_skind_interp.
      iSplit.
      + iIntros "(%sκ & %Hsk & %Hsv & Hser)".
        iExists sκ.
        iSplit; first admit.
        iSplit; first done.
        cbn.
        iDestruct "Hser" as (os) "(-> & Hprod)".
        iExists (map serialize_atom os).
        rewrite flat_map_concat_map.
        iSplit; first done.
        rewrite big_sepL2_fmap_r big_sepL2_fmap_l.
        rewrite !type_interp_eq /add_skind_interp.
        iDestruct "Hprod" as (sκ0 Htskind Hsksv) "Hprod".
        cbn.
        iDestruct "Hprod" as (oss Hatoms_eq) "H".
        inversion Hatoms_eq.
        subst os.
        rewrite big_sepL2_fmap_l.
        rewrite big_sepL2_flip. (* The definitions should really agree on the order... *)
        (* TODO: this feels like an odd thing to prove...
           The lenght implications mean that, if this is true, then length oss = length $ concat oss *)

        admit.
      + admit.
    - (* Struct Ser *)
      intros κ_ser κ_prod κ_struct κs_ser τs τs' Hlen Heq IH F κ κ' se sv Hκ Hκ' Hse.
      admit.
  Admitted.

End type_eq_sem.
