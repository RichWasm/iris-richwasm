Require Import RichWasm.iris.logrel.instr.typing.common.
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
    - intros κ0 τs τs' Heq IH F κ κ' se sv Hκ Hκ' Hse.
      admit.
    - intros κ0 τs τs' Heq IH F κ κ' se sv Hκ Hκ' Hse.
      admit.
    - intros κ0 τs τs' Heq IH F κ κ' se sv Hκ Hκ' Hse.
      admit.
    - intros κ0 τs τs' Heq IH F κ κ' se sv Hκ Hκ' Hse.
      admit.
    - intros κ0 μ β τ τ' Heq IH F κ κ' se sv Hκ Hκ' Hse.
      admit.
    - intros κ0 τ τ' Heq IH F κ κ' se sv Hκ Hκ' Hse.
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
    - intros κ0 τ τ' Heq IH F κ κ' se sv Hκ Hκ' Hse.
      admit.
    - intros κ0 τ τ' Heq IH F κ κ' se sv Hκ Hκ' Hse.
      admit.
    - intros κ0 τ τ' Heq IH F κ κ' se sv Hκ Hκ' Hse.
      admit.
    - intros κ0 τ τ' Heq IH F κ κ' se sv Hκ Hκ' Hse.
      admit.
    - intros κ0 κτ τ τ' Heq IH F κ κ' se sv Hκ Hκ' Hse.
      admit.
    - intros κ_ser κ_prod κ_struct κs_ser τs τs' Hlen Heq IH F κ κ' se sv Hκ Hκ' Hse.
      admit.
    - intros κ_ser κ_prod κ_struct κs_ser τs τs' Hlen Heq IH F κ κ' se sv Hκ Hκ' Hse.
      admit.
  Admitted.

End type_eq_sem.
