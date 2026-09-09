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

  Lemma struct_fields_ser_inv F τs' σs' ξs2 :
    Forall3 (fun τ σ ξ => has_kind F τ (MEMTYPE σ ξ)) (map SerT τs') σs' ξs2 ->
    exists ρs2,
      σs' = map RepS ρs2 /\
      Forall3 (fun τ' ρ ξ => has_kind F τ' (VALTYPE ρ ξ)) τs' ρs2 ξs2.
  Proof.
    revert σs' ξs2.
    induction τs' as [|τ' τs' IH]; intros σs' ξs2 HF3.
    - inversion HF3; subst.
      exists [].
      split; constructor.
    - cbn in HF3.
      inversion HF3 as [|? σ0 ξ0 ? σs0 ξs0 Hhd HF3']; subst.
      inversion Hhd; subst.
      destruct (IH _ _ HF3') as (ρs2 & -> & HF3'').
      eexists (_ :: ρs2).
      split; by constructor.
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

  (* MEMTYPE analogue of [eval_kind_valtype_inv]. *)
  Lemma eval_kind_memtype_inv σ ξ σ' ξ' :
    eval_kind env (MEMTYPE σ ξ) = eval_kind env (MEMTYPE σ' ξ') ->
    eval_size env σ = eval_size env σ' /\
    (forall n, eval_size env σ = Some n -> ξ = ξ').
  Proof.
    cbn.
    destruct (eval_size env σ) as [n|] eqn:Hσ;
      destruct (eval_size env σ') as [n'|] eqn:Hσ'; cbn;
      intros Heq; simplify_eq; split; congruence.
  Qed.

  (* Pointwise VALTYPE eval_kind agreement on a zipped (rep,flag) list
     implies agreement of the whole list's [mapM eval_rep] and (whenever
     that mapM succeeds) agreement of the flag lists -- the common core
     used by [eval_kind_sum] and [eval_kind_prod] below. *)
  Lemma eval_kind_valtype_zip_agree ρs ξs ρs' ξs' :
    Forall2 (fun ρξ ρξ' : representation * ref_flag =>
               eval_kind env (VALTYPE ρξ.1 ρξ.2) = eval_kind env (VALTYPE ρξ'.1 ρξ'.2))
      (zip ρs ξs) (zip ρs' ξs') ->
    length ρs = length ξs ->
    length ρs' = length ξs' ->
    length ρs = length ρs' ->
    mapM (eval_rep env) ρs = mapM (eval_rep env) ρs' /\
    (forall ιss, mapM (eval_rep env) ρs = Some ιss -> ξs = ξs').
  Proof.
    revert ξs ρs' ξs'.
    induction ρs as [|ρ ρs IH]; intros ξs ρs' ξs' HF2 Hlen1 Hlen2 Hlen3;
      destruct ρs' as [|ρ' ρs']; try discriminate;
      destruct ξs as [|ξ ξs]; try discriminate;
      destruct ξs' as [|ξ' ξs']; try discriminate.
    - split; first done. intros ιss Heq. done.
    - cbn in HF2.
      apply Forall2_cons_1 in HF2 as [Hhd HF2].
      apply eval_kind_valtype_inv in Hhd as [Hrep Hflag].
      injection Hlen1 as Hlen1.
      injection Hlen2 as Hlen2.
      injection Hlen3 as Hlen3.
      destruct (IH ξs ρs' ξs' HF2 Hlen1 Hlen2 Hlen3) as [IHmap IHflag].
      split.
      + cbn. rewrite Hrep IHmap. done.
      + intros ιss Heq.
        apply mapM_Some_1 in Heq.
        apply Forall2_cons_inv_l in Heq as (ιs & ιss0 & Hρ & Heq0 & _).
        specialize (Hflag ιs Hρ).
        specialize (IHflag ιss0 (mapM_Some_2 _ _ _ Heq0)).
        by f_equal.
  Qed.

  (* MEMTYPE analogue of [eval_kind_valtype_zip_agree], for SumS/ProdS. *)
  Lemma eval_kind_memtype_zip_agree σs ξs σs' ξs' :
    Forall2 (fun σξ σξ' : Core.size * ref_flag =>
               eval_kind env (MEMTYPE σξ.1 σξ.2) = eval_kind env (MEMTYPE σξ'.1 σξ'.2))
      (zip σs ξs) (zip σs' ξs') ->
    length σs = length ξs ->
    length σs' = length ξs' ->
    length σs = length σs' ->
    mapM (eval_size env) σs = mapM (eval_size env) σs' /\
    (forall ns, mapM (eval_size env) σs = Some ns -> ξs = ξs').
  Proof.
    revert ξs σs' ξs'.
    induction σs as [|σ σs IH]; intros ξs σs' ξs' HF2 Hlen1 Hlen2 Hlen3;
      destruct σs' as [|σ' σs']; try discriminate;
      destruct ξs as [|ξ ξs]; try discriminate;
      destruct ξs' as [|ξ' ξs']; try discriminate.
    - split; first done. intros ns Heq. done.
    - cbn in HF2.
      apply Forall2_cons_1 in HF2 as [Hhd HF2].
      apply eval_kind_memtype_inv in Hhd as [Hsz Hflag].
      injection Hlen1 as Hlen1.
      injection Hlen2 as Hlen2.
      injection Hlen3 as Hlen3.
      destruct (IH ξs σs' ξs' HF2 Hlen1 Hlen2 Hlen3) as [IHmap IHflag].
      split.
      + cbn. rewrite Hsz IHmap. done.
      + intros ns Heq.
        apply mapM_Some_1 in Heq.
        apply Forall2_cons_inv_l in Heq as (n & ns0 & Hσ & Heq0 & _).
        specialize (Hflag n Hσ).
        specialize (IHflag ns0 (mapM_Some_2 _ _ _ Heq0)).
        by f_equal.
  Qed.

  (* Aggregate [eval_kind] congruence for [SumT]. *)
  Lemma eval_kind_sum ρs ξs ρs' ξs' :
    Forall2 (fun ρξ ρξ' : representation * ref_flag =>
               eval_kind env (VALTYPE ρξ.1 ρξ.2) = eval_kind env (VALTYPE ρξ'.1 ρξ'.2))
      (zip ρs ξs) (zip ρs' ξs') ->
    length ρs = length ξs ->
    length ρs' = length ξs' ->
    length ρs = length ρs' ->
    eval_kind env (VALTYPE (SumR ρs) (ref_flag_lub ξs)) =
    eval_kind env (VALTYPE (SumR ρs') (ref_flag_lub ξs')).
  Proof.
    intros HF2 Hlen1 Hlen2 Hlen3.
    destruct (eval_kind_valtype_zip_agree ρs ξs ρs' ξs' HF2 Hlen1 Hlen2 Hlen3) as [Hmap Hflag].
    cbn.
    destruct (mapM (eval_rep env) ρs) as [ιss|] eqn:Hρs.
    - rewrite <- Hmap.
      specialize (Hflag ιss eq_refl) as ->.
      done.
    - rewrite <- Hmap.
      done.
  Qed.

  (* Aggregate [eval_kind] congruence for [VariantT]. *)
  Lemma eval_kind_variant σs ξs σs' ξs' :
    Forall2 (fun σξ σξ' : Core.size * ref_flag =>
               eval_kind env (MEMTYPE σξ.1 σξ.2) = eval_kind env (MEMTYPE σξ'.1 σξ'.2))
      (zip σs ξs) (zip σs' ξs') ->
    length σs = length ξs ->
    length σs' = length ξs' ->
    length σs = length σs' ->
    eval_kind env (MEMTYPE (SumS σs) (ref_flag_lub ξs)) =
    eval_kind env (MEMTYPE (SumS σs') (ref_flag_lub ξs')).
  Proof.
    intros HF2 Hlen1 Hlen2 Hlen3.
    destruct (eval_kind_memtype_zip_agree σs ξs σs' ξs' HF2 Hlen1 Hlen2 Hlen3) as [Hmap Hflag].
    cbn.
    destruct (mapM (eval_size env) σs) as [ns|] eqn:Hσs.
    - rewrite <- Hmap.
      specialize (Hflag ns eq_refl) as ->.
      done.
    - rewrite <- Hmap.
      done.
  Qed.

  (* Aggregate [eval_kind] congruence for [ProdT]. *)
  Lemma eval_kind_prod ρs ξs ρs' ξs' :
    Forall2 (fun ρξ ρξ' : representation * ref_flag =>
               eval_kind env (VALTYPE ρξ.1 ρξ.2) = eval_kind env (VALTYPE ρξ'.1 ρξ'.2))
      (zip ρs ξs) (zip ρs' ξs') ->
    length ρs = length ξs ->
    length ρs' = length ξs' ->
    length ρs = length ρs' ->
    eval_kind env (VALTYPE (ProdR ρs) (ref_flag_lub ξs)) =
    eval_kind env (VALTYPE (ProdR ρs') (ref_flag_lub ξs')).
  Proof.
    intros HF2 Hlen1 Hlen2 Hlen3.
    destruct (eval_kind_valtype_zip_agree ρs ξs ρs' ξs' HF2 Hlen1 Hlen2 Hlen3) as [Hmap Hflag].
    cbn.
    destruct (mapM (eval_rep env) ρs) as [ιss|] eqn:Hρs.
    - rewrite <- Hmap.
      specialize (Hflag ιss eq_refl) as ->.
      done.
    - rewrite <- Hmap.
      done.
  Qed.

  (* Aggregate [eval_kind] congruence for [StructT]. *)
  Lemma eval_kind_struct σs ξs σs' ξs' :
    Forall2 (fun σξ σξ' : Core.size * ref_flag =>
               eval_kind env (MEMTYPE σξ.1 σξ.2) = eval_kind env (MEMTYPE σξ'.1 σξ'.2))
      (zip σs ξs) (zip σs' ξs') ->
    length σs = length ξs ->
    length σs' = length ξs' ->
    length σs = length σs' ->
    eval_kind env (MEMTYPE (ProdS σs) (ref_flag_lub ξs)) =
    eval_kind env (MEMTYPE (ProdS σs') (ref_flag_lub ξs')).
  Proof.
    intros HF2 Hlen1 Hlen2 Hlen3.
    destruct (eval_kind_memtype_zip_agree σs ξs σs' ξs' HF2 Hlen1 Hlen2 Hlen3) as [Hmap Hflag].
    cbn.
    destruct (mapM (eval_size env) σs) as [ns|] eqn:Hσs.
    - rewrite <- Hmap.
      specialize (Hflag ns eq_refl) as ->.
      done.
    - rewrite <- Hmap.
      done.
  Qed.

  (* [eval_kind] congruence for the plain [SerT] constructor: since [SerT]
     no longer carries its own kind, its (MEMTYPE) kind is derived from its
     argument's (VALTYPE) kind, so agreement has to be transported through
     that derivation rather than being definitional. *)
  Lemma eval_kind_ser_congr ρ ξ ρ' ξ' :
    eval_kind env (VALTYPE ρ ξ) = eval_kind env (VALTYPE ρ' ξ') ->
    eval_kind env (MEMTYPE (RepS ρ) ξ) = eval_kind env (MEMTYPE (RepS ρ') ξ').
  Proof.
    intros Heq.
    apply eval_kind_valtype_inv in Heq as [Hrep Hflag].
    cbn.
    destruct (eval_rep env ρ) as [ιs|] eqn:Hρ.
    - rewrite <- Hrep.
      specialize (Hflag ιs eq_refl) as ->.
      done.
    - rewrite <- Hrep.
      done.
  Qed.

  (* MEMTYPE analogue of [eval_kind_pairs_of_kinds]. *)
  Lemma eval_kind_pairs_of_kinds_mem F τs τs' σs ξs σs2 ξs2 :
    Forall2 (fun τ τ' =>
               forall F κ κ',
                 has_kind F τ κ ->
                 has_kind F τ' κ' ->
                 eval_kind env κ = eval_kind env κ') τs τs' ->
    Forall3 (fun τ σ ξ => has_kind F τ (MEMTYPE σ ξ)) τs σs ξs ->
    Forall3 (fun τ' σ ξ => has_kind F τ' (MEMTYPE σ ξ)) τs' σs2 ξs2 ->
    Forall2 (fun σξ σξ' : Core.size * ref_flag =>
               eval_kind env (MEMTYPE σξ.1 σξ.2) = eval_kind env (MEMTYPE σξ'.1 σξ'.2))
      (zip σs ξs) (zip σs2 ξs2).
  Proof.
    intros HF2.
    revert σs ξs σs2 ξs2.
    induction HF2 as [|τ τ' τs τs' Hhd HF2 IH]; intros σs ξs σs2 ξs2 HF3 HF3'.
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
    - (* Sum *)
      intros τs τs' Heq IH F κ κ' Hκ Hκ'.
      inversion Hκ; subst.
      match goal with
        H : Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs _ _ |- _ => rename H into HF3
      end.
      inversion Hκ'; subst.
      match goal with
        H : Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs' _ _ |- _ => rename H into HF3'
      end.
      pose proof (Forall3_length_lm _ _ _ _ HF3) as Hl1.
      pose proof (Forall3_length_lr _ _ _ _ HF3) as Hl2.
      pose proof (Forall3_length_lm _ _ _ _ HF3') as Hl3.
      pose proof (Forall3_length_lr _ _ _ _ HF3') as Hl4.
      pose proof (Forall2_length _ _ _ Heq) as Hlenττ'.
      apply eval_kind_sum; try congruence.
      by eapply eval_kind_pairs_of_kinds.
    - (* Variant *)
      intros τs τs' Heq IH F κ κ' Hκ Hκ'.
      inversion Hκ; subst.
      match goal with
        H : Forall3 (fun τ σ ξ => has_kind F τ (MEMTYPE σ ξ)) τs _ _ |- _ => rename H into HF3
      end.
      inversion Hκ'; subst.
      match goal with
        H : Forall3 (fun τ σ ξ => has_kind F τ (MEMTYPE σ ξ)) τs' _ _ |- _ => rename H into HF3'
      end.
      pose proof (Forall3_length_lm _ _ _ _ HF3) as Hl1.
      pose proof (Forall3_length_lr _ _ _ _ HF3) as Hl2.
      pose proof (Forall3_length_lm _ _ _ _ HF3') as Hl3.
      pose proof (Forall3_length_lr _ _ _ _ HF3') as Hl4.
      pose proof (Forall2_length _ _ _ Heq) as Hlenττ'.
      apply eval_kind_variant; try congruence.
      by eapply eval_kind_pairs_of_kinds_mem.
    - (* Prod *)
      intros τs τs' Heq IH F κ κ' Hκ Hκ'.
      inversion Hκ; subst.
      match goal with
        H : Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs _ _ |- _ => rename H into HF3
      end.
      inversion Hκ'; subst.
      match goal with
        H : Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs' _ _ |- _ => rename H into HF3'
      end.
      pose proof (Forall3_length_lm _ _ _ _ HF3) as Hl1.
      pose proof (Forall3_length_lr _ _ _ _ HF3) as Hl2.
      pose proof (Forall3_length_lm _ _ _ _ HF3') as Hl3.
      pose proof (Forall3_length_lr _ _ _ _ HF3') as Hl4.
      pose proof (Forall2_length _ _ _ Heq) as Hlenττ'.
      apply eval_kind_prod; try congruence.
      by eapply eval_kind_pairs_of_kinds.
    - (* Struct *)
      intros τs τs' Heq IH F κ κ' Hκ Hκ'.
      inversion Hκ; subst.
      match goal with
        H : Forall3 (fun τ σ ξ => has_kind F τ (MEMTYPE σ ξ)) τs _ _ |- _ => rename H into HF3
      end.
      inversion Hκ'; subst.
      match goal with
        H : Forall3 (fun τ σ ξ => has_kind F τ (MEMTYPE σ ξ)) τs' _ _ |- _ => rename H into HF3'
      end.
      pose proof (Forall3_length_lm _ _ _ _ HF3) as Hl1.
      pose proof (Forall3_length_lr _ _ _ _ HF3) as Hl2.
      pose proof (Forall3_length_lm _ _ _ _ HF3') as Hl3.
      pose proof (Forall3_length_lr _ _ _ _ HF3') as Hl4.
      pose proof (Forall2_length _ _ _ Heq) as Hlenττ'.
      apply eval_kind_struct; try congruence.
      by eapply eval_kind_pairs_of_kinds_mem.
    - (* Ref *)
      intros μ β τ τ' _ _ F κ κ' Hκ Hκ'; inversion Hκ; inversion Hκ'; subst; cbn in *; congruence.
    - (* Ser *)
      intros τ τ' _ IH F κ κ' Hκ Hκ'.
      inversion Hκ; subst.
      match goal with H : has_kind F τ (VALTYPE _ _) |- _ => rename H into Hkτ end.
      inversion Hκ'; subst.
      match goal with H : has_kind F τ' (VALTYPE _ _) |- _ => rename H into Hkτ' end.
      apply eval_kind_ser_congr.
      by eapply IH.
    - (* Rec *)
      intros κ0 τ τ' _ _ F κ κ' Hκ Hκ'; inversion Hκ; inversion Hκ'; subst; cbn in *; congruence.
    - (* ExMem *)
      intros κ0 τ τ' _ _ F κ κ' Hκ Hκ'; inversion Hκ; inversion Hκ'; subst; cbn in *; congruence.
    - (* ExRep *)
      intros κ0 τ τ' _ _ F κ κ' Hκ Hκ'; inversion Hκ; inversion Hκ'; subst; cbn in *; congruence.
    - (* ExSize *)
      intros κ0 τ τ' _ _ F κ κ' Hκ Hκ'; inversion Hκ; inversion Hκ'; subst; cbn in *; congruence.
    - (* ExType *)
      intros κ0 κτ τ τ' _ _ F κ κ' Hκ Hκ'; inversion Hκ; inversion Hκ'; subst; cbn in *; congruence.
    - (* SerProd *)
      intros τs τs' Heq IH F κ κ' Hκ Hκ'.
      inversion Hκ; subst.
      match goal with H : has_kind F (ProdT _) _ |- _ => rename H into Hprod end.
      inversion Hprod; subst.
      match goal with H : Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs _ _ |- _ => rename H into HF3 end.
      inversion Hκ'; subst.
      match goal with
        H : Forall3 _ (map SerT _) _ _ |- _ => rename H into HF3' end.
      pose proof (Forall2_length _ _ _ Heq) as Hlenττ'.
      destruct (struct_fields_ser_inv _ _ _ _ HF3') as (ρs2 & -> & HF3'').
      pose proof (Forall3_length_lm _ _ _ _ HF3) as Hl1.
      pose proof (Forall3_length_lr _ _ _ _ HF3) as Hl2.
      pose proof (Forall3_length_lm _ _ _ _ HF3'') as Hl3.
      pose proof (Forall3_length_lr _ _ _ _ HF3'') as Hl4.
      apply eval_kind_ser_prod_struct; try congruence.
      by eapply eval_kind_pairs_of_kinds.
    - (* ProdSer *)
      intros τs τs' Heq IH F κ κ' Hκ Hκ'.
      inversion Hκ; subst.
      match goal with
        H : Forall3 _ (map SerT _) _ _ |- _ => rename H into HF3' end.
      inversion Hκ'; subst.
      match goal with H : has_kind F (ProdT _) _ |- _ => rename H into Hprod end.
      inversion Hprod; subst.
      match goal with H : Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs' _ _ |- _ => rename H into HF3 end.
      pose proof (Forall2_length _ _ _ Heq) as Hlenττ'.
      destruct (struct_fields_ser_inv _ _ _ _ HF3') as (ρs2 & -> & HF3'').
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
    ([∗ list] ws;τ ∈ wss; map SerT τs',
       type_interp rti sr τ se (SWords ws))
    ⊢
    (∃ os, ⌜concat wss = flat_map serialize_atom os⌝ ∗
       type_interp rti sr (ProdT τs) se (SAtoms os)).
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
      assert (Hbridge : Forall3 (fun τ0 ρ0 ξ0 =>
                           forall sκ0, eval_kind se (VALTYPE ρ0 ξ0) = Some sκ0 -> type_skind_go se τ0 = Some sκ0)
                        τs ρs ξs).
      { eapply Forall3_impl; first exact H1.
        intros τ0 ρ0 ξ0 Hhk sκ0 Heval.
        eapply type_skind_has_kind_Some; [exact Hhk|exact Hsem|exact Heval]. }
      pose proof (forall3_mapM_type_skind_val se τs ρs ξs Hbridge ιss (mapM_Some_2 _ _ _ Hιss)) as Hmm.
      rewrite Hmm in Hsktail.
      pose proof (Forall2_length _ _ _ Hιss) as Hlen_ρs_ιss.
      pose proof (Forall3_length_lm _ _ _ _ H1) as Hlen_τs_ρs.
      pose proof (Forall3_length_lr _ _ _ _ H1) as Hlen_τs_ξs.
      assert (Hlen_ιss_ξs : length ιss = length ξs) by congruence.
      cbn in Hsktail.
      rewrite (mapM_skind_rep_zip _ _ Hlen_ιss_ξs) in Hsktail.
      cbn in Hsktail.
      rewrite (map_skind_ref_flag_zip_val _ _ Hlen_ιss_ξs) in Hsktail.
      injection Hsktail as <-.
      iExists (SVALTYPE (ιsτ ++ concat ιss) (ref_flag_lub (ξ :: ξs))).
      iSplit.
      { iPureIntro.
        pose proof Hsκτ as Hsκτ'.
        cbn in Hsκτ'.
        cbn.
        rewrite Hsκτ' Hmm.
        cbn.
        rewrite (mapM_skind_rep_zip _ _ Hlen_ιss_ξs).
        cbn.
        rewrite (map_skind_ref_flag_zip_val _ _ Hlen_ιss_ξs).
        done. }
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
    type_interp rti sr (ProdT τs) se (SAtoms os)
    ⊢
    (∃ wss, ⌜flat_map serialize_atom os = concat wss⌝ ∗
       [∗ list] ws;τ ∈ wss; map SerT τs',
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
      done.
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
      assert (Hbridge : Forall3 (fun τ0 ρ0 ξ0 =>
                           forall sκ0, eval_kind se (VALTYPE ρ0 ξ0) = Some sκ0 -> type_skind_go se τ0 = Some sκ0)
                        τs ρs ξs).
      { eapply Forall3_impl; first exact H1.
        intros τ0 ρ0 ξ0 Hhk sκ0 Heval.
        eapply type_skind_has_kind_Some; [exact Hhk|exact Hsem|exact Heval]. }
      pose proof (forall3_mapM_type_skind_val se τs ρs ξs Hbridge ιss (mapM_Some_2 _ _ _ Hιss)) as Hmm.
      pose proof (Forall2_length _ _ _ Hιss) as Hlen_ρs_ιss.
      pose proof (Forall3_length_lm _ _ _ _ H1) as Hlen_τs_ρs.
      pose proof (Forall3_length_lr _ _ _ _ H1) as Hlen_τs_ξs.
      assert (Hlen_ιss_ξs : length ιss = length ξs) by congruence.
      iAssert (type_interp rti sr (SerT τ') se (SWords (flat_map serialize_atom o)))%I
        with "[Hhd2]" as "Hheadser".
      { iApply (type_interp_eq rti sr (SerT τ') se (SWords (flat_map serialize_atom o))).
        rewrite /add_skind_interp.
        iExists (SMEMTYPE (areps_size ιs2) ξ2).
        iSplit.
        { iPureIntro. pose proof Hsκτ2 as Hsκτ2'. cbn in Hsκτ2'. cbn. rewrite Hsκτ2'. cbn. done. }
        iSplit.
        { iPureIntro. split.
          - cbn. by rewrite (has_areps_serialize_length _ _ Harepo').
          - by apply ref_flag_serialize. }
        rewrite /pre_type_interp /=.
        iExists o. iSplit; first done. iExact "Hhd2". }
      iAssert (type_interp rti sr (ProdT τs) se (SAtoms (concat oss)))%I
        with "[Htl]" as "Htail2".
      { iApply (type_interp_eq rti sr (ProdT τs) se (SAtoms (concat oss))).
        rewrite /add_skind_interp.
        iExists (SVALTYPE (concat ιss) (ref_flag_lub ξs)).
        iSplit.
        { iPureIntro.
          cbn.
          rewrite Hmm.
          cbn.
          rewrite (mapM_skind_rep_zip _ _ Hlen_ιss_ξs).
          cbn.
          by rewrite (map_skind_ref_flag_zip_val _ _ Hlen_ιss_ξs). }
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
    pre_type_interp rti sr (StructT (map SerT τs')) se sv
    ⊣⊢
    pre_type_interp rti sr (SerT (ProdT τs)) se sv.
  Proof.
    intros Hsem H1 H1' Heq IH.
    rewrite /pre_type_interp /=.
    iSplit.
    - iIntros "(%wss & -> & Hbig)".
      iEval (rewrite big_sepL2_fmap_r) in "Hbig".
      iDestruct (big_sepL2_length with "Hbig") as %Hlenwss.
      rewrite length_map in Hlenwss.
      iDestruct (struct_fields_to_prod_atoms F se τs τs' ρs ξs ρs2 ξs2 wss Hsem H1 H1' Heq IH Hlenwss with "Hbig")
        as (os) "(%Hoseq & Hprod)".
      iExists os.
      iSplit.
      { iPureIntro. by rewrite Hoseq. }
      iExact "Hprod".
    - iIntros "(%os & -> & Hprod)".
      iDestruct (prod_atoms_to_struct_fields F se τs τs' ρs ξs ρs2 ξs2 os Hsem H1 H1' Heq IH with "Hprod")
        as (wss) "(%Hwsseq & Hbig)".
      iExists wss.
      iSplit.
      { iPureIntro. by rewrite Hwsseq. }
      iEval (rewrite big_sepL2_fmap_r).
      iExact "Hbig".
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

  (* Post-refactor, an aggregate type's [type_skind] is recomputed
     bottom-up from its children rather than read off a shared cached
     kind, so [type_skind se τ] and [type_skind se τ'] are no longer
     syntactically identical for [type_eq]-related [τ]/[τ']; this bridges
     the gap via [type_eq_eval_kind_agree] (agreement at the [eval_kind]
     level, from [has_kind]) and [type_skind_has_kind_Some] (the
     [has_kind]/[eval_kind] -> [type_skind] bridge). *)
  Lemma type_skind_type_eq_agree F se τ τ' κ κ' sκ :
    type_eq τ τ' ->
    has_kind F τ κ ->
    has_kind F τ' κ' ->
    sem_env_interp F se ->
    @type_skind Σ se τ = Some sκ ->
    @type_skind Σ se τ' = Some sκ.
  Proof.
    intros Hteq Hκ Hκ' Hsem Hsk.
    pose proof (has_kind_ok_kind_ok _ _ _ (has_kind_inv _ _ _ Hκ)) as Hkindok.
    destruct (eval_kind_ok_Some F se κ Hsem Hkindok) as [sκ0 Heval0].
    pose proof (type_skind_has_kind_Some F se τ κ sκ0 Hκ Hsem Heval0) as Htsk0.
    rewrite Hsk in Htsk0.
    injection Htsk0 as <-.
    pose proof (type_eq_eval_kind_agree se τ τ' Hteq F κ κ' Hκ Hκ') as Hagree.
    rewrite Heval0 in Hagree.
    symmetry in Hagree.
    eapply type_skind_has_kind_Some; eauto.
  Qed.

  Lemma type_arep_type_eq_agree F se τ τ' κ κ' :
    type_eq τ τ' ->
    has_kind F τ κ ->
    has_kind F τ' κ' ->
    sem_env_interp F se ->
    @type_arep Σ se τ = @type_arep Σ se τ'.
  Proof.
    intros Hteq Hκ Hκ' Hsem.
    pose proof (has_kind_ok_kind_ok _ _ _ (has_kind_inv _ _ _ Hκ)) as Hkindok.
    destruct (eval_kind_ok_Some F se κ Hsem Hkindok) as [sκ0 Heval0].
    pose proof (type_skind_has_kind_Some F se τ κ sκ0 Hκ Hsem Heval0) as Htsk0.
    pose proof (type_skind_type_eq_agree F se τ τ' κ κ' sκ0 Hteq Hκ Hκ' Hsem Htsk0) as Htsk0'.
    cbn in Htsk0, Htsk0'.
    cbn [type_arep].
    unfold type_skind.
    cbn.
    rewrite Htsk0 Htsk0'.
    done.
  Qed.

  (* [sum_interp_offset]/[sum_interp_count] now recompute from [τs]/[τs']
     directly (see their own comments above), so unlike the pre-refactor
     cached-kind version, their agreement across [type_eq]-related lists
     needs an explicit argument via [type_arep_type_eq_agree]. *)
  Lemma sum_interp_offset_count_type_eq_agree F se τs τs' ρs ξs ρs' ξs' :
    Forall2 type_eq τs τs' ->
    Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs ρs ξs ->
    Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs' ρs' ξs' ->
    sem_env_interp F se ->
    forall i,
      @sum_interp_offset Σ se τs i = @sum_interp_offset Σ se τs' i /\
      @sum_interp_count Σ se τs i = @sum_interp_count Σ se τs' i.
  Proof.
    intros Heq HF3 HF3' Hsem i.
    assert (Forall2 (fun τ τ' => @type_arep Σ se τ = @type_arep Σ se τ') τs τs') as Harep.
    {
      eapply Forall2_mini_impl; try done.
      apply Forall2_same_length_lookup_2.
      { exact (Forall2_length _ _ _ Heq). }
      intros j a b Haj Hbj Hpair.
      destruct (Forall3_lookup_l _ _ _ _ _ _ HF3 Haj) as (ρ & ξ & _ & _ & Hka).
      destruct (Forall3_lookup_l _ _ _ _ _ _ HF3' Hbj) as (ρ' & ξ' & _ & _ & Hkb).
      eapply type_arep_type_eq_agree; eauto.
    }
    split.
    - unfold sum_interp_offset.
      assert (Hmm : mapM (type_arep se) (take i τs) = mapM (type_arep se) (take i τs')).
      { eapply Forall2_mapM_ext, Forall2_take, Harep. }
      by rewrite Hmm.
    - unfold sum_interp_count.
      destruct (τs !! i) as [τi|] eqn:Hτi.
      + destruct (Forall2_lookup_l _ _ _ _ _ Harep Hτi) as (ai & Hτi' & Harepi).
        rewrite Hτi'.
        cbn [mbind option_bind].
        by rewrite Harepi.
      + assert (τs' !! i = None) as Hτi'.
        { apply lookup_ge_None. apply lookup_ge_None in Hτi.
          by rewrite (Forall2_length _ _ _ Harep) in Hτi. }
        by rewrite Hτi'.
  Qed.

  Lemma sum_interp_offset_count_type_eq_agree' F se τs τs' ρs ξs ρs' ξs' :
    Forall2 type_eq τs τs' ->
    Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs ρs ξs ->
    Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs' ρs' ξs' ->
    sem_env_interp F se ->
    forall i,
      @sum_interp_offset Σ se τs' i = @sum_interp_offset Σ se τs i /\
      @sum_interp_count Σ se τs' i = @sum_interp_count Σ se τs i.
  Proof.
    intros Heq HF3 HF3' Hsem i.
    destruct (sum_interp_offset_count_type_eq_agree F se τs τs' ρs ξs ρs' ξs' Heq HF3 HF3' Hsem i)
      as [Ho Hc].
    split; symmetry; done.
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
      intros τs τs' Heq IH F κ κ' se sv Hkind Hkind' Hsem.
      rewrite !type_interp_eq.
      inversion Hkind; subst.
      match goal with H : Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs _ _ |- _ => rename H into HF3a end.
      inversion Hkind'; subst.
      match goal with H : Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs' _ _ |- _ => rename H into HF3b end.
      iSplit; iIntros "H".
      + iDestruct "H" as (sκ) "(%Hsk & %Hsv & Hsum)".
        iExists sκ.
        iSplit; first (iPureIntro; eapply type_skind_type_eq_agree; [by constructor|exact Hkind|exact Hkind'|exact Hsem|exact Hsk]).
        iSplit; first done.
        simpl.
        iDestruct "Hsum" as (i os off count ->) "(%Hoff & %Hcount & HTi)".
        iExists i, os, off, count.
        destruct (sum_interp_offset_count_type_eq_agree F se τs τs' _ _ _ _ Heq HF3a HF3b Hsem i) as [Hoffeq Hcounteq].
        iSplit; first (iPureIntro; done).
        iSplit; first (iPureIntro; rewrite -Hoffeq; exact Hoff).
        iSplit; first (iPureIntro; rewrite -Hcounteq; exact Hcount).
        destruct (τs !! i) as [τi_raw|] eqn:Hiraw.
        * eapply (Forall2_lookup_l) in Heq as [τi_raw' [Hiraw' Heqi]]; last exact Hiraw.
          iEval (change (list_lookup i (map (type_interp rti sr) τs)) with ((type_interp rti sr <$> τs) !! i); rewrite list_lookup_fmap Hiraw; cbn) in "HTi".
          iEval (change (list_lookup i (map (type_interp rti sr) τs')) with ((type_interp rti sr <$> τs') !! i); rewrite list_lookup_fmap Hiraw'; cbn).
          eapply Forall3_lookup_l in HF3a, HF3b; try done.
          destruct HF3a as (? & ? & ? & ? & ?).
          destruct HF3b as (? & ? & ? & ? & ?).
          eapply Forall2_lookup_lr in IH; try done.
          iApply IH; try done.
        * iEval (change (list_lookup i (map (type_interp rti sr) τs)) with ((type_interp rti sr <$> τs) !! i); rewrite list_lookup_fmap Hiraw; cbn) in "HTi".
          iDestruct "HTi" as "[]".
      + iDestruct "H" as (sκ) "(%Hsk & %Hsv & Hsum)".
        iExists sκ.
        iSplit; first (iPureIntro; eapply type_skind_type_eq_agree; [by (symmetry; constructor)|exact Hkind'|exact Hkind|exact Hsem|exact Hsk]).
        iSplit; first done.
        simpl.
        iDestruct "Hsum" as (i os off count ->) "(%Hoff & %Hcount & HTi)".
        iExists i, os, off, count.
        destruct (sum_interp_offset_count_type_eq_agree' F se τs τs' _ _ _ _
                    Heq HF3a HF3b Hsem i) as [Hoffeq Hcounteq].
        iSplit; first (iPureIntro; done).
        iSplit; first (iPureIntro; rewrite -Hoffeq; exact Hoff).
        iSplit; first (iPureIntro; rewrite -Hcounteq; exact Hcount).
        destruct (τs' !! i) as [τi_raw'|] eqn:Hiraw'.
        * eapply (Forall2_lookup_r) in Heq as [τi_raw [Hiraw Heqi]]; last exact Hiraw'.
          iEval (change (list_lookup i (map (type_interp rti sr) τs')) with ((type_interp rti sr <$> τs') !! i); rewrite list_lookup_fmap Hiraw'; cbn) in "HTi".
          iEval (change (list_lookup i (map (type_interp rti sr) τs)) with ((type_interp rti sr <$> τs) !! i); rewrite list_lookup_fmap Hiraw; cbn).
          eapply Forall3_lookup_l in HF3a, HF3b; try done.
          destruct HF3a as (? & ? & ? & ? & ?).
          destruct HF3b as (? & ? & ? & ? & ?).
          eapply Forall2_lookup_lr in IH; try done.
          iApply IH; try done.
        * iEval (change (list_lookup i (map (type_interp rti sr) τs')) with ((type_interp rti sr <$> τs') !! i); rewrite list_lookup_fmap Hiraw'; cbn) in "HTi".
          iDestruct "HTi" as "[]".
    - (* Variant *)
      intros τs τs' Heq IH F κ κ' se sv Hκ Hκ' Hsem.
      rewrite !type_interp_eq.
      inversion Hκ; subst.
      match goal with H : Forall3 (fun τ σ ξ => has_kind F τ (MEMTYPE σ ξ)) τs _ _ |- _ => rename H into HF3a end.
      inversion Hκ'; subst.
      match goal with H : Forall3 (fun τ σ ξ => has_kind F τ (MEMTYPE σ ξ)) τs' _ _ |- _ => rename H into HF3b end.
      iSplit; iIntros "H".
      + iDestruct "H" as (sκ) "(%Hsk & %Hsv & Hvar)".
        iExists sκ.
        iSplit; first (iPureIntro; eapply type_skind_type_eq_agree; [by constructor|exact Hκ|exact Hκ'|exact Hsem|exact Hsk]).
        iSplit; first done.
        simpl.
        iDestruct "Hvar" as (i n ws ws' Hrepr -> Hpad) "HTi".
        iExists i, n, ws, ws'.
        do 3 (iSplit; first done).
        destruct (τs !! i) as [τi_raw|] eqn:Hiraw.
        * eapply (Forall2_lookup_l) in Heq as [τi_raw' [Hiraw' Heqi]]; last exact Hiraw.

          iEval (change (list_lookup i (map (type_interp rti sr) τs)) with ((type_interp rti sr <$> τs) !! i); rewrite list_lookup_fmap Hiraw; cbn) in "HTi".

          iEval (change (list_lookup i (map (type_interp rti sr) τs')) with ((type_interp rti sr <$> τs') !! i); rewrite list_lookup_fmap Hiraw'; cbn).

          eapply Forall3_lookup_l in HF3a, HF3b; try done.
          destruct HF3a as (? & ? & ? & ? & ?).
          destruct HF3b as (? & ? & ? & ? & ?).
          eapply Forall2_lookup_lr in IH; try done.
          iApply IH; try done.

        * iEval (change (list_lookup i (map (type_interp rti sr) τs)) with ((type_interp rti sr <$> τs) !! i); rewrite list_lookup_fmap Hiraw; cbn) in "HTi".
          iDestruct "HTi" as "[]".
      + iDestruct "H" as (sκ) "(%Hsk & %Hsv & Hvar)".
        iExists sκ.
        iSplit; first (iPureIntro; eapply type_skind_type_eq_agree; [by (symmetry; constructor)|exact Hκ'|exact Hκ|exact Hsem|exact Hsk]).
        iSplit; first done.
        simpl.
        iDestruct "Hvar" as (i n ws ws' Hrepr -> Hpad) "HTi".
        iExists i, n, ws, ws'.
        do 3 (iSplit; first done).
        destruct (τs' !! i) as [τi_raw'|] eqn:Hiraw'.
        * eapply (Forall2_lookup_r) in Heq as [τi_raw [Hiraw Heqi]]; last exact Hiraw'.
          iEval (change (list_lookup i (map (type_interp rti sr) τs')) with ((type_interp rti sr <$> τs') !! i); rewrite list_lookup_fmap Hiraw'; cbn) in "HTi".
          iEval (change (list_lookup i (map (type_interp rti sr) τs)) with ((type_interp rti sr <$> τs) !! i); rewrite list_lookup_fmap Hiraw; cbn).
          eapply Forall3_lookup_l in HF3a, HF3b; try done.
          destruct HF3a as (? & ? & ? & ? & ?).
          destruct HF3b as (? & ? & ? & ? & ?).
          eapply Forall2_lookup_lr in IH; try done.
          iApply IH; try done.
        * iEval (change (list_lookup i (map (type_interp rti sr) τs')) with ((type_interp rti sr <$> τs') !! i); rewrite list_lookup_fmap Hiraw'; cbn) in "HTi".
          iDestruct "HTi" as "[]".
    - (* Product *)
      intros τs τs' Heq IH F κ κ' se sv Hκ Hκ' Hsem.
      rewrite !type_interp_eq.
      inversion Hκ; subst.
      match goal with H : Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs _ _ |- _ => rename H into HF3a end.
      inversion Hκ'; subst.
      match goal with H : Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs' _ _ |- _ => rename H into HF3b end.
      iSplit; iIntros "H".
      + iDestruct "H" as (sκ) "(%Hsk & %Hsv & Hprod)".
        iExists sκ.
        iSplit; first (iPureIntro; eapply type_skind_type_eq_agree; [by constructor|exact Hκ|exact Hκ'|exact Hsem|exact Hsk]).
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
        destruct (Forall3_lookup_l _ _ _ _ _ _ HF3a Hai) as (ρ & ξ & _ & _ & Hka).
        destruct (Forall3_lookup_l _ _ _ _ _ _ HF3b Hbi) as (ρ' & ξ' & _ & _ & Hkb).
        by eapply Hpair.
      + iDestruct "H" as (sκ) "(%Hsk & %Hsv & Hprod)".
        iExists sκ.
        iSplit; first (iPureIntro; eapply type_skind_type_eq_agree; [by (symmetry; constructor)|exact Hκ'|exact Hκ|exact Hsem|exact Hsk]).
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
        destruct (Forall3_lookup_l _ _ _ _ _ _ HF3a Hai) as (ρ & ξ & _ & _ & Hka).
        destruct (Forall3_lookup_l _ _ _ _ _ _ HF3b Hbi) as (ρ' & ξ' & _ & _ & Hkb).
        eapply Forall2_lookup_lr in IH; try done.
        symmetry.
        exact (IH F _ _ se (SAtoms x0) Hka Hkb Hsem).
    - (* Struct *)
      intros τs τs' Heq IH F κ κ' se sv Hκ Hκ' Hsem.
      rewrite !type_interp_eq.
      inversion Hκ; subst.
      match goal with H : Forall3 (fun τ σ ξ => has_kind F τ (MEMTYPE σ ξ)) τs _ _ |- _ => rename H into HF3a end.
      inversion Hκ'; subst.
      match goal with H : Forall3 (fun τ σ ξ => has_kind F τ (MEMTYPE σ ξ)) τs' _ _ |- _ => rename H into HF3b end.
      iSplit; iIntros "H".
      + iDestruct "H" as (wss) "(%Hwss & Hbig)".
        iDestruct "Hbig" as "(%Hsv & Hstruct)".
        iExists wss.
        iSplitL "". { iPureIntro. eapply type_skind_type_eq_agree; [by constructor|exact Hκ|exact Hκ'|exact Hsem|exact Hwss]. }
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
        destruct (Forall3_lookup_l _ _ _ _ _ _ HF3a Hai) as (σ & ξ & _ & _ & Hka).
        destruct (Forall3_lookup_l _ _ _ _ _ _ HF3b Hbi) as (σ' & ξ' & _ & _ & Hkb).
        by eapply Hpair.
      + iDestruct "H" as (wss) "(%Hwss & Hbig)".
        iDestruct "Hbig" as "(%Hsv & Hstruct)".
        iExists wss.
        iSplitL "". { iPureIntro. eapply type_skind_type_eq_agree; [by (symmetry; constructor)|exact Hκ'|exact Hκ|exact Hsem|exact Hwss]. }
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
        destruct (Forall3_lookup_l _ _ _ _ _ _ HF3a Hai) as (σ & ξ & _ & _ & Hka).
        destruct (Forall3_lookup_l _ _ _ _ _ _ HF3b Hbi) as (σ' & ξ' & _ & _ & Hkb).
        eapply Forall2_lookup_lr in IH; try done.
        symmetry.
        exact (IH F _ _ se (SWords ws) Hka Hkb Hsem).
    - (* Ref *)
      intros μ β τ τ' Heq IH F κ κ' se sv Hκ Hκ' Hsem.
      destruct (has_kind_ref_ty _ _ _ _ _ Hκ) as (σ & ξ & Hkτ).
      destruct (has_kind_ref_ty _ _ _ _ _ Hκ') as (σ' & ξ' & Hkτ').
      assert (∀ sv, type_interp rti sr τ se sv ⊣⊢ type_interp rti sr τ' se sv) as Heqτ.
      { intros sv'. exact (IH F _ _ se sv' Hkτ Hkτ' Hsem). }
      rewrite !type_interp_eq /add_skind_interp /=.
      iSplit.
      { iIntros "(%sκ & %Hsk & %Hsv & Hr)".
        iExists sκ.
        assert (Hsk' : type_skind se (RefT μ β τ) = Some sκ) by (cbn; exact Hsk).
        assert (Hgoal : type_skind se (RefT μ β τ') = Some sκ).
        { eapply type_skind_type_eq_agree; [by constructor|exact Hκ|exact Hκ'|exact Hsem|exact Hsk']. }
        iSplit; first (iPureIntro; exact Hgoal).
        iSplit; first done.
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
        iExists sκ.
        assert (Hsk' : type_skind se (RefT μ β τ') = Some sκ) by (cbn; exact Hsk).
        assert (Hgoal : type_skind se (RefT μ β τ) = Some sκ).
        { eapply type_skind_type_eq_agree; [by (symmetry; constructor)|exact Hκ'|exact Hκ|exact Hsem|exact Hsk']. }
        iSplit; first (iPureIntro; exact Hgoal).
        iSplit; first done.
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
      intros τ τ' Heq IH F κ κ' se sv Hκ Hκ' Hsem.
      inversion Hκ; subst.
      inversion Hκ'; subst.
      match goal with Hk : has_kind F τ (VALTYPE _ _) |- _ => rename Hk into Hkτ end.
      match goal with Hk : has_kind F τ' (VALTYPE _ _) |- _ => rename Hk into Hkτ' end.
      rewrite !type_interp_eq.
      iSplit.
      + iIntros "H".
        iDestruct "H" as (sκ) "(%Hsk & %Hsv & Hser)".
        iExists sκ.
        iSplit; first (iPureIntro; eapply type_skind_type_eq_agree; [by constructor|exact Hκ|exact Hκ'|exact Hsem|exact Hsk]).
        iSplit; first done.
        iDestruct "Hser" as (os) "[%Hws Hτ]".
        iExists os.
        iSplit; first done.
        by iEval (rewrite (IH F _ _ se _ Hkτ Hkτ' Hsem)) in "Hτ".
      + iIntros "H".
        iDestruct "H" as (sκ) "(%Hsk & %Hsv & Hser)".
        iExists sκ.
        iSplit; first (iPureIntro; eapply type_skind_type_eq_agree; [by (symmetry; constructor)|exact Hκ'|exact Hκ|exact Hsem|exact Hsk]).
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
      intros τs τs' Heq IH F κ κ' se sv Hκ Hκ' Hsem.
      inversion Hκ; subst.
      match goal with H : has_kind F (ProdT _) _ |- _ => rename H into Hprod end.
      inversion Hprod; subst.
      match goal with H : Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs _ _ |- _ => rename H into HF3 end.
      inversion Hκ'; subst.
      match goal with H : Forall3 _ (map SerT _) _ _ |- _ => rename H into HF3' end.
      destruct (struct_fields_ser_inv _ _ _ _ HF3') as (ρs2 & -> & HF3'').
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
        destruct (Forall3_lookup_l _ _ _ _ _ _ HF3 Hai) as (ρ & ξ & _ & _ & Hka).
        destruct (Forall3_lookup_l _ _ _ _ _ _ HF3'' Hbi) as (ρ' & ξ' & _ & _ & Hkb).
        eapply Hpair; try done.
      }
      clear IH.
      iSplit.
      + iIntros "(%sκ & %Hsk & %Hsv & Hser)".
        iExists sκ.
        iSplit; first (iPureIntro; eapply type_skind_type_eq_agree; [by constructor|exact Hκ|exact Hκ'|exact Hsem|exact Hsk]).
        iSplit; first done.
        iApply (pre_type_interp_prod_ser F se τs τs' _ _ ρs2 _ sv Hsem HF3 HF3'' Heq IH' with "Hser").
      + iIntros "(%sκ & %Hsk & %Hsv & Hstruct)".
        iExists sκ.
        iSplit; first (iPureIntro; eapply type_skind_type_eq_agree; [by (symmetry; constructor)|exact Hκ'|exact Hκ|exact Hsem|exact Hsk]).
        iSplit; first done.
        iApply (pre_type_interp_prod_ser F se τs τs' _ _ ρs2 _ sv Hsem HF3 HF3'' Heq IH' with "Hstruct").
    - (* Struct Ser *)
      intros τs τs' Heq IH F κ κ' se sv Hκ Hκ' Hsem.
      inversion Hκ'; subst.
      match goal with H : has_kind F (ProdT _) _ |- _ => rename H into Hprod end.
      inversion Hprod; subst.
      match goal with H : Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs' _ _ |- _ => rename H into HF3 end.
      inversion Hκ; subst.
      match goal with H : Forall3 _ (map SerT _) _ _ |- _ => rename H into HF3' end.
      destruct (struct_fields_ser_inv _ _ _ _ HF3') as (ρs2 & -> & HF3'').
      assert (Htyeq : type_eq (StructT (map SerT τs)) (SerT (ProdT τs'))) by (by constructor).
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
        destruct (Forall3_lookup_l _ _ _ _ _ _ HF3'' Hai) as (ρ & ξ & _ & _ & Hka).
        destruct (Forall3_lookup_l _ _ _ _ _ _ HF3 Hbi) as (ρ' & ξ' & _ & _ & Hkb).
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
        iExists sκ.
        iSplit; first (iPureIntro; eapply type_skind_type_eq_agree; [exact Htyeq|exact Hκ|exact Hκ'|exact Hsem|exact Hsk]).
        iSplit; first done.
        iApply (pre_type_interp_prod_ser F se τs' τs _ _ ρs2 _ sv Hsem HF3 HF3'' Heq IH' with "Hser").
      + iIntros "(%sκ & %Hsk & %Hsv & Hstruct)".
        iExists sκ.
        iSplit; first (iPureIntro; eapply type_skind_type_eq_agree; [symmetry; exact Htyeq|exact Hκ'|exact Hκ|exact Hsem|exact Hsk]).
        iSplit; first done.
        iApply (pre_type_interp_prod_ser F se τs' τs _ _ ρs2 _ sv Hsem HF3 HF3'' Heq IH' with "Hstruct").
  Qed.

End type_eq_sem.
