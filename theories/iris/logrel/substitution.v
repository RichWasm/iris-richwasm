Require Import RichWasm.iris.logrel.logrel_properties.
Require Import RichWasm.iris.wp_codegen.
Require Import RichWasm.iris.logrel.logrel_properties.
Require Import RichWasm.iris.logrel.env_props.
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


  (* NOT DONE P:L these substitution lemmas are almost certainly okay *)
  Lemma refresh_kinds_up_shift_type F κ τ :
    refresh_kinds (F <| fc_type_vars ::= cons κ |>)
      (ren_type unscoped.id unscoped.id unscoped.id unscoped.shift τ) =
      ren_type unscoped.id unscoped.id unscoped.id unscoped.shift (refresh_kinds F τ).
  Proof.
  Admitted.



  (* NOT DONE P:L PROBABLY TRUE BUT ANNOYING *)
  Lemma type_interp_up_rep se sub_t ρ sv i :
    type_interp rti sr (sub_t i) se sv ∗-∗
    type_interp rti sr (up_representation_type sub_t i) (senv_insert_rep ρ se) sv.
  Proof.
  Admitted.
  Lemma type_interp_up_size se sub_t n sv i :
    type_interp rti sr (sub_t i) se sv ∗-∗
    type_interp rti sr (up_size_type sub_t i) (senv_insert_size n se) sv.
  Proof.
  Admitted.
  Lemma type_interp_up_type se sub_t sκ sκ_T T sv i :
    True -> (* need to add a condition on sκ and T here? *)
    type_interp rti sr (sub_t i) se sv ∗-∗
    type_interp rti sr (up_type_type sub_t (S i)) (senv_insert_type sκ sκ_T T se) sv.
  Proof.
  Admitted.
  Lemma type_interp_up_memory se sub_t μ sv i :
    type_interp rti sr (sub_t i) se sv ∗-∗
    type_interp rti sr (up_memory_type sub_t i) (senv_insert_mem μ se) sv.
  Proof.
  Admitted.

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
(* NOT DONE P:H QUITE FUNDAMENTAL *)
  (* I wonder if some of of the hypotheses can be deleted *)
  (* probably, but maybe not  *)
  Lemma type_skind_refresh_subst_senv_eq F F' se se' sub_m sub_r sub_s sub_t τ κ κ' :
    let τ' := (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)) in
    has_kind F' τ κ ->
    has_kind F τ' κ' ->
    sem_env_rel_rep_eq se' se sub_r ->
    sem_env_rel_size_eq se' se sub_s ->
    sem_env_rel_sκ_eq se' se sub_t ->
    (∀ i, refresh_kinds F (sub_t i) = sub_t i) ->
    sem_env_interp F' se' ->
    sem_env_interp F se ->
    subskind_of_option
      (type_skind (Σ:=Σ) se (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)))
      (type_skind (Σ:=Σ) se' τ).
  Proof.
    unfold_sem_rels.
    intros Hkind_τ.
    generalize dependent κ'.
    pose proof Hkind_τ as Hkind_save.
    revert Hkind_save.
    induction Hkind_τ using has_kind_ind'
      with (P0:= const (const True)) (Pi:=const (const True)); try done;
      intros Hkind_τ κ' Hkind_τ' Hsub_r Hsub_s Hsub_t Hsub_t_good Hse' Hse.
    all: try by (subst κ; cbn; apply subskind_of_refl).
    7: (cbn -[type_skind]; unfold κ; cbn;
       rewrite <- (eval_rep_subst_senv_eq se se'); try done;
       apply subskind_of_option_refl).
    all: try by
      (cbn; rewrite <- (eval_kind_subst_senv_eq se se'); try done;
       apply subskind_of_option_refl).
    6: { (* sert qed, proof that IH can work *)
      subst κ.

      cbn in Hkind_τ'.
      inversion Hkind_τ'; subst.
      apply kind_of_node_good in H3 as H4.
      rewrite <- H4 in H.
      inversion Hkind_τ; subst.
      subst κ1 κ2; clear H7.
      specialize (IHHkind_τ H2 (VALTYPE ρ0 ξ0)
        ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto)).
      rewrite <- H4 in *.
      move IHHkind_τ at bottom.

      set (τ' := (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ))) in *.
      apply has_kind_inv in H3 as Hevalτ'.
      apply has_kind_inv in H2 as Hevalτ.
      inversion Hevalτ'; subst.
      inversion Hevalτ; subst.
      pose proof (eval_kind_ok_Some _ _ _ Hse H1) as (sk & Hevalτκ).
      pose proof (eval_kind_ok_Some _ _ _ Hse' H6) as (sk' & Hevalτ'κ).
      pose proof (type_skind_has_kind_Some _ _ _ _ _ H3 Hse Hevalτκ) as Htssubτ.
      pose proof (type_skind_has_kind_Some _ _ _ _ _ H2 Hse' Hevalτ'κ) as Htsτ.
      (* I'm crying *)
      clear H0 H1 H5 H6 Hevalτ' Hevalτ.
      rename sk into sk_τ'. rename sk' into sk_τ.
      rename F0 into F'. rename ρ0 into ρ'; rename ξ0 into ξ'.
      rename Htssubτ into Htsτ'.
      rename H3 into Haskind_τ'. rename H2 into Haskind_τ.
      rename Hevalτκ into Hevτ'. rename Hevalτ'κ into Hevτ.

      apply bind_Some in Hevτ' as temp.
      destruct temp as (ιs' & Heval_ρ' & toinv).
      inversion toinv; subst; clear toinv.
      apply bind_Some in Hevτ as temp.
      destruct temp as (ιs & Heval_ρ & toinv).
      inversion toinv; subst; clear toinv.

      cbn.
      fold τ'.
      rewrite <- H4.
      cbn.
      rewrite Heval_ρ' Heval_ρ; cbn.
      rewrite Htsτ' in IHHkind_τ; rewrite Htsτ in IHHkind_τ; cbn in IHHkind_τ.
      inversion IHHkind_τ; subst.
      by constructor.
    }
    7: {
      cbn -[type_skind].
      rewrite Hsub_t_good.
      apply Hsub_t.
    }
    5: {
      inversion Hkind_τ; subst.
      (* oh I can tell this will be pretty much identical to the sert case *)
      (* i think we're okay *)
      admit.
    }
    5: {
      cbn -[type_skind]; unfold κ; cbn.
      rewrite <- (eval_size_subst_senv_eq se se'); try done.
      apply subskind_of_option_refl.
    }
  (* and the rest are are just the struct like ones which are like sert/ref var
   but on steroids *)
  Admitted.

  Lemma type_arep_refresh_subst_senv_eq F F' se se' sub_m sub_r sub_s sub_t τ κ κ' :
    let τ' := (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)) in
    has_kind F' τ κ ->
    has_kind F τ' κ' ->
    sem_env_rel_rep_eq se' se sub_r ->
    sem_env_rel_size_eq se' se sub_s ->
    sem_env_rel_sκ_eq se' se sub_t ->
    (∀ i, refresh_kinds F (sub_t i) = sub_t i) ->
    sem_env_interp F' se' ->
    sem_env_interp F se ->
    type_arep (Σ:=Σ) se' τ =
    type_arep (Σ:=Σ) se (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)).
  Proof.
    unfold type_arep; unfold_sem_rels.
    intros Hkind_τ Hkind_τ' Hsub_r Hsub_s Hsub_t Hsub_t_good Hse' Hse.
    pose proof (type_skind_refresh_subst_senv_eq F F' se se' sub_m sub_r sub_s sub_t τ κ κ'
    ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ).
    destruct (type_skind se' τ) eqn:hse'τ;
      destruct (type_skind se (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ))) eqn:hsesubτ;
      try done; cbn -[type_skind]; rewrite hse'τ; rewrite hsesubτ; cbn; try done.
    cbn in H.
    inversion H; subst; try done.
  Qed.

  Lemma translate_type_refresh_subst_senv_eq F F' se se' sub_m sub_r sub_s sub_t τ κ κ' :
    let τ' := (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)) in
    has_kind F' τ κ ->
    has_kind F τ' κ' ->
    sem_env_rel_rep_eq se' se sub_r ->
    sem_env_rel_size_eq se' se sub_s ->
    sem_env_rel_sκ_eq se' se sub_t ->
    (∀ i, refresh_kinds F (sub_t i) = sub_t i) ->
    sem_env_interp F' se' ->
    sem_env_interp F se ->
    translate_type (Σ:=Σ) se' τ =
    translate_type (Σ:=Σ) se (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ)).
  Proof.
    unfold translate_type; unfold_sem_rels.
    intros Hkind_τ Hkind_τ' Hsub_r Hsub_s Hsub_t Hsub_t_good Hse' Hse.
    Opaque translate_arep. Opaque type_arep.
    cbn.
    Transparent translate_arep. Transparent type_arep.
    pose proof (type_arep_refresh_subst_senv_eq F F' se se' sub_m sub_r sub_s sub_t τ κ κ'
    ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ).
    rewrite H.
    done.
  Qed.

  Lemma translate_types_refresh_subst_senv_eq F F' se se' sub_m sub_r sub_s sub_t τs κs κs' :
    let τs' := (map (refresh_kinds F) (map (subst_type sub_m sub_r sub_s sub_t) τs))  in
    Forall2 (has_kind F') τs κs ->
    Forall2 (has_kind F) τs' κs' ->
    sem_env_rel_rep_eq se' se sub_r ->
    sem_env_rel_size_eq se' se sub_s ->
    sem_env_rel_sκ_eq se' se sub_t ->
    (∀ i, refresh_kinds F (sub_t i) = sub_t i) ->
    sem_env_interp F' se' ->
    sem_env_interp F se ->
    translate_types (Σ:=Σ) se' τs =
    translate_types (Σ:=Σ) se τs' .
  Proof.
    intros τs' Hkind_τs Hkind_τs' Hsub_r Hsub_s Hsub_t Hsub_t_good Hse' Hse.
    unfold translate_types; unfold_sem_rels.
    Opaque translate_type.
    cbn.
    Transparent translate_type.

    assert (Y: mapM (translate_type se') τs =
                 mapM (translate_type se) τs'). {
      (* okay we use Forall_mapM_ext along with translate_type_subst_senv_eq and we're done *)
      admit.
    }
    rewrite Y; done.
  Admitted.

  (* probably move elsewhere *)
  Lemma ref_flag_le_preserves_atoms_interp ξ ξ' os:
    ref_flag_le ξ ξ' -> ref_flag_atoms_interp ξ (SAtoms os) ->
    ref_flag_atoms_interp ξ' (SAtoms os).
  Proof.
    apply ref_flag_atoms_refine.
  Qed.

  Lemma struct_test sv:
    let nt32 := (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T)) in
    let nt31 := (I31T (VALTYPE (AtomR PtrR) NoRefs)) in
    let se : semantic_env := ([],[],[],
          [(SVALTYPE [PtrR] AnyRefs,
            ((SVALTYPE [PtrR] NoRefs),(value_interp rti sr senv_empty nt31)))]) in
    type_interp rti sr
      (ProdT (VALTYPE (ProdR [AtomR PtrR;AtomR I32R]) AnyRefs)
         [VarT 0; nt32]) se sv ∗-∗
    type_interp rti sr
      (ProdT (VALTYPE (ProdR [AtomR PtrR;AtomR I32R]) NoRefs)
         [nt31; nt32]) senv_empty sv.
  Proof.
    intros.
    iSplitR.
    - (* unsubted -> substed *)
      iIntros "Ht".
      rewrite !type_interp_eq.
      unfold add_skind_interp.
      (* idea for lemma
         value_interp rti sr τ se' sv -∗
         type_skind se (refresh_kinds F (subst τ)) = Some sκ' /\
         skind_has_svalue sκ' sv
       *)
      cbn.
      iDestruct "Ht" as "(%sκ & %toinv & %HAnySk & Ht)".
      inversion toinv; subst; clear toinv.
      destruct HAnySk as (HasArepsSV & AnyRefsSV).
      iExists (SVALTYPE [PtrR;I32R] NoRefs).
      iSplitR; first done.
      iDestruct "Ht" as "(%wss & -> & Ht)".
      iPoseProof (big_sepL2_cons_inv_l with "[$Ht]") as "Ht".
      iDestruct "Ht" as "(%osvar & %oss32 & -> & Htvar & Ht32)".
      iPoseProof (big_sepL2_cons_inv_l with "[$Ht32]") as "Ht32".
      iDestruct "Ht32" as "(%os32 & %ostoinv & -> & Ht32 & Hempty)".
      iPoseProof (big_sepL2_length with "[$Hempty]") as "%leninv".
      destruct ostoinv; try (inversion leninv; done); clear leninv.
      iClear "Hempty".
      Transparent type_interp.
      iEval (unfold type_interp) in "Htvar".
      iEval (unfold nt32; unfold type_interp) in "Ht32".
      Opaque type_interp.
      iEval (cbn) in "Htvar".
      iEval (cbn) in "Ht32".
      iDestruct "Htvar" as "(%sκ & %toinv & %osvarintp & Htvar)".
      inversion toinv; subst; clear toinv.
      iDestruct "Ht32" as "(%sκ & %toinv & %os32intp & _)".
      inversion toinv; subst; clear toinv.
      (* to get that osvar has norefs we have to look at htvar *)
      (* this extra step is new *)
      (* this is the key: *)
      iAssert (⌜ref_flag_atoms_interp NoRefs (SAtoms (concat [osvar;os32]) )⌝%I)
        with "[Htvar]"as "%yes". {
        rewrite value_interp_eq.
        iEval (cbn) in "Htvar".
        iDestruct "Htvar" as "(%sκ & %toinv & %osvarintptrue & _)".
        inversion toinv; subst; clear toinv.
        cbn. clear_nils.
        destruct osvarintptrue as (Harepvar & HvarNoRef).
        destruct os32intp as (Harep32 & H32NoRef).
        cbn in *.
        iPureIntro.
        apply Forall_app; try done.
      }

      iSplitR; first done.
      iExists ([osvar;os32]).
      iSplitR; first done.
      iFrame.
      cbn.
      iSplitR; last done.
      unfold nt32.
      rewrite type_interp_eq.
      cbn.
      iExists (SVALTYPE [I32R] NoRefs).
      iSplitR; first done.
      iSplitR; first done.
      done.
  Admitted.

  (* the big scary one P:H *)
  Lemma skind_interp_chillin :
    ∀ τ F F' κ κ' (se:semantic_env (Σ:=Σ)) se' sub_m sub_r sub_s sub_t sv,
    let τ' := refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ) in
    (* conditions for substitutions and types *)
    (sem_env_rel_rep_eq se' se sub_r) ->
    (sem_env_rel_size_eq se' se sub_s) ->
    (sem_env_rel_mem_eq se' se sub_m) -> (* necessary *)
    (sem_env_rel_sκ_eq se' se sub_t) ->
    (sem_env_rel_type_eq se' se sub_t) ->
    (∀ i, refresh_kinds F (sub_t i) = sub_t i) -> (* necessary *)
    sem_env_interp F' se' ->
    sem_env_interp F se ->
    has_kind F' τ κ ->  (* necessary *)
    has_kind F τ' κ' -> (* can prove: κ' ≤ κ *) (* necessary *)
    (* the skind interp thingy *)
    type_interp rti sr τ se' sv -∗
     ∃ sκ, ⌜type_skind se τ' = Some sκ /\ skind_has_svalue sκ sv⌝.
  Proof.
    induction τ using type_ind with (P0 := const True) (Pi := const True);
      try (intros * Hsub_r Hsub_s Hsub_m Hsub_sκ Hsub_T Hsub_t_good Hse' Hse Hkind_τ Hkind_τ'); try done;
      unfold_sem_rels.
    1: { (* var, qed *)
      iIntros "Ht".
      rewrite type_interp_eq.
      cbn in τ'.
      subst τ'.
      rewrite Hsub_t_good in Hkind_τ'.
      rewrite Hsub_t_good.
      iDestruct "Ht" as "(%sκ_big & %one & %two & Ht)".
      cbn -[lookup_type] in one.
      specialize (Hsub_sκ idx).
      rewrite one in Hsub_sκ.
      apply subskind_of_option_invr in Hsub_sκ as (sκ_small & jo & subsk).
      iExists sκ_small.
      rewrite jo.
      iEval (cbn) in "Ht".
      specialize (Hsub_T idx sv).
      cbn in Hsub_T.
      apply fmap_Some in one as ([sκ [sκ_T T]] & lookp & ->).
      cbn in lookp.
      rewrite lookp in Hsub_T; rewrite lookp.
      cbn -[skind_has_svalue]; cbn in Hsub_T.
      rewrite Hsub_T.
      rewrite value_interp_eq.
      unfold add_skind_interp.
      iDestruct "Ht" as "(%sκfake & %ah & %no & _)".
      rewrite jo in ah; inversion ah; subst.
      iPureIntro; done.
    }
    5: { (* prodt, convinced it's okay now *)
      iIntros "Ht".
      pose proof (type_skind_refresh_subst_senv_eq F F' se se' sub_m sub_r sub_s
                    sub_t (ProdT κ τs) κ0 κ') as Hsubk.
      do 8 (specialize (Hsubk ltac:(auto))).
      cbn in τ'.
      inversion Hkind_τ; subst; subst κ1.
      inversion Hkind_τ'; subst.
      rename H4 into Hkind3_τ.
      rename H6 into Hkind3_τ'.
      rename H3 into Hrefs_τ'.

      (* kinding time..... need to get type_skind into from Hkind_τ *)
      apply has_kind_inv in Hkind_τ as temp.
      inversion temp; subst.
      clear H0; rename H1 into kind_ok_τ.
      pose proof (eval_kind_ok_Some _ _ _ Hse' kind_ok_τ) as (sκ_τ & Hevalτ).
      pose proof (type_skind_has_kind_Some _ _ _ _ _ Hkind_τ Hse' Hevalτ) as Htsτ.
      rewrite Htsτ in Hsubk.
      apply subskind_of_option_invr in Hsubk as (sκ_τ' & Htsτ' & Hsubk).
      pose proof Htsτ as copy.
      cbn in copy.
      apply bind_Some in copy as (ιs & Hevalρs & toinv).
      inversion toinv; subst; clear toinv.
      pose proof Htsτ' as copy.
      cbn in copy.
      apply bind_Some in copy as (ιs' & Hevalρs' & toinv).
      rewrite <- Hrefs_τ' in toinv.
      inversion toinv; subst; clear toinv.
      inversion Hsubk; subst.
      (* yay okay now we have that ρs and ρs' eval to same ιs *)
      assert (ξs0 = (map kind_ref_flag
         (map (kind_of_node F)
            (map (refresh_kinds F) (map (subst_type sub_m sub_r sub_s sub_t) τs))))). {
        (* this is just by Hkind3_τ', not even subkinding stuff *)
        admit.
      }

      rewrite <- H0 in *. clear Hrefs_τ'; rename H0 into Hrefs_τ'.
      rename H1 into subsk_ref_flags.

      (* how it's time to actually do stuff *)
      rewrite type_interp_eq.
      iEval (cbn) in "Ht".
      (* we need to throw away a good bit of this info I believe... *)
      assert (Hnew:
      Forall (λ τ, ∀ sv, type_interp rti sr τ se' sv -∗
            ∃ sκ, ⌜ type_skind se (refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ))
                    = Some sκ /\ skind_has_svalue sκ sv ⌝
        ) τs
             ). {
        apply Forall_lookup_2.
        intros i τ Hiτ sv0.
        pose proof (Forall_lookup_1 _ τs i τ H Hiτ).
        (* now i need to get Forall3_τ info out *)
        pose proof (Forall3_lookup_l _ τs ρs ξs i τ Hkind3_τ Hiτ).
        destruct H1 as (ρ & ξ & Hρ & Hξ & Hτ_kind).
        specialize (H0 F F' (VALTYPE ρ ξ)).
        pose proof Hiτ as Himapτ.
        pose proof (map_lookup_helper_forwards
                      (subst_type sub_m sub_r sub_s sub_t) τs i τ Himapτ).
        pose proof (map_lookup_helper_forwards
                      (refresh_kinds F) _ i _ H1).
        pose proof (Forall3_lookup_l _ _ _ ξs0 i _ Hkind3_τ' H2).
        destruct H3 as (ρ' & ξ' & Hρ' & Hξ' & Hτ'_kind).
        specialize (H0 (VALTYPE ρ' ξ') se se' sub_m sub_r sub_s sub_t sv0).
        apply H0; try done.
      }
      (* okay yay now we won't need to deal with weird things in IH *)
      iDestruct "Ht" as "(%sκ_old & %Htypeskindold & %Hsvold & (%oss' & -> & Ht))".
      iPoseProof (big_sepL2_fmap_l (type_interp rti sr) with "Ht") as "Ht".
      cbn.
      rewrite Hevalρs in Htypeskindold. cbn in Htypeskindold.
      inversion Htypeskindold; subst sκ_old.
      rewrite Hevalρs'.
      rewrite <- Hrefs_τ'.
      cbn.
      iExists (SVALTYPE ιs (ref_flag_lub ξs0)).
      iSplitR; first done.
      destruct Hsvold as (areps & Hsvold).
      iSplitR; first done.

      (* okay and now this will be combining Hnew and Ht *)
      (* I'm now convinced this is fine *)
      admit.
    }
    7: { (* coderef, qed *)
      iIntros "Ht".
      rewrite type_interp_eq.
      cbn in τ'.
      subst τ'.
      cbn.
      inversion Hkind_τ; subst.
      subst κ1.
      iDestruct "Ht" as "(%sκ & %one & %two & _)".
      iExists sκ.
      iPureIntro; done.
    }
    6: { (* ref, qed *)
      iIntros "Ht".
      rewrite type_interp_eq.
      inversion Hkind_τ; subst.
      - (* var mem *)
        iEval (cbn) in "Ht".
        iDestruct "Ht" as "(%sκ & %toinv & %SVAnyInterp & Ht)".
        inversion toinv; subst; clear toinv.
        cbn in τ'.
        assert (se'.1.1.1 !! m = eval_mem se (sub_m m)) by (apply Hsub_m; done).
        (* NOTE: EVAL SUBM M IS EITHER GC OR MM *)
        (* BUT SUBM M IS VAR, GC, OR MM *)
        (* IN THE VAR CASE, IT'S TRUE BY VAR BEING ANY *)
        (* IN THE OTHERS, THEY'RE JUST EQUAL *)
        destruct (se'.1.1.1 !! m) eqn:TheEval; rewrite TheEval; try done.
        destruct b, β.
        + (* eval to memm, and mut *)
          iEval (cbn) in "Ht".
          destruct (sub_m m) eqn:TheSubM.
          * (* var case *)
            unfold τ'.
            cbn.
            iExists (SVALTYPE [PtrR] AnyRefs).
            iSplitR; first done; done.
          * destruct b; cbn in H; try done.
            unfold τ'; cbn.
            iExists (SVALTYPE [PtrR] AnyRefs).
            iSplitR; first done; done.
        + (* eval to memm and imm *)
          iEval (cbn) in "Ht".
          destruct (sub_m m) eqn:TheSubM.
          * (* var case *)
            unfold τ'.
            cbn.
            iExists (SVALTYPE [PtrR] AnyRefs).
            iSplitR; first done; done.
          * destruct b; cbn in H; try done.
            unfold τ'; cbn.
            iExists (SVALTYPE [PtrR] AnyRefs).
            iSplitR; first done; done.
        + (* eval to gc and mut *)
          iEval (cbn) in "Ht".
          destruct (sub_m m) eqn:TheSubM.
          * (* var case *)
            unfold τ'.
            cbn.
            iExists (SVALTYPE [PtrR] AnyRefs).
            iSplitR; first done; done.
          * destruct b; cbn in H; try done.
            (* THIS IS THE INTERESTING CASE I THINK *)
            unfold τ'; cbn.
            iExists (SVALTYPE [PtrR] GCRefs).
            (* finally interesting: we do NOT yet have a ref interp for GCRefs *)
            iSplitR; first done.
            (* this is where we have to dig into Ht to get what sv actually is *)
            iDestruct "Ht" as "(%ℓ & %fs & -> & Ht)".
            cbn.
            iPureIntro.
            destruct SVAnyInterp as (arep & useless).
            split; first done.
            constructor; last done.
            cbn. done.
        + (* eval to gc and imm *)
          iEval (cbn) in "Ht".
          destruct (sub_m m) eqn:TheSubM.
          * (* var case *)
            unfold τ'.
            cbn.
            iExists (SVALTYPE [PtrR] AnyRefs).
            iSplitR; first done; done.
          * destruct b; cbn in H; try done.
            (* THIS IS THE INTERESTING CASE I THINK *)
            unfold τ'; cbn.
            iExists (SVALTYPE [PtrR] GCRefs).
            (* finally interesting: we do NOT yet have a ref interp for GCRefs *)
            iSplitR; first done.
            (* this is where we have to dig into Ht to get what sv actually is *)
            iDestruct "Ht" as "(%ℓ & %fs & %ws & -> & Ht)".
            cbn.
            iPureIntro.
            destruct SVAnyInterp as (arep & useless).
            split; first done.
            constructor; last done.
            cbn. done.
      - (* mm *)
        cbn in τ'.
        unfold τ'.
        cbn.
        iExists (SVALTYPE [PtrR] AnyRefs).
        iSplitR; first done.
        iDestruct "Ht" as "(%sκ & %toinv & %thefacts & _)".
        inversion toinv; subst; clear toinv.
        done.
      - (* gc *)
        cbn in τ'.
        unfold τ'.
        cbn.
        iExists (SVALTYPE [PtrR] GCRefs).
        iSplitR; first done.
        iDestruct "Ht" as "(%sκ & %toinv & %thefacts & _)".
        inversion toinv; subst; clear toinv.
        done.
    }
    13: { (* exists type, qed *)
      iIntros "Ht".
      rewrite type_interp_eq.
      iEval (cbn) in "Ht".
      inversion Hkind_τ; subst.
      (* we'll need to use the inductive hyp here *)
      (* but uhm... on what..... *)
      cbn in τ'.
      subst τ'.
      cbn.
      inversion Hkind_τ'; subst.

      (* hm Im scared the F being extended with subst_kind... *)
      iDestruct "Ht" as "(%sκ & %Hevalκ & %SVskterp &
      (%T' & %sκ0 & %sκ_T & %Hevalsκ' & %subskind & %skindhasstype & Ht))".
      iPoseProof (IHτ with "[$Ht]") as "pls".
      9: exact H6.
      9: exact H9.
      Unshelve.
      10: exact (senv_insert_type sκ0 sκ_T T' se).
      1-6: intros.
      1-3: cbn.
      - change (se'.1.1.2 !! i) with (lookup_rep se' i); rewrite Hsub_r.
        apply eval_rep_up_type_eq.
      - change (se'.1.2 !! i) with (lookup_size se' i); rewrite Hsub_s.
        apply eval_size_up_type_eq.
      - change (se'.1.1.1 !! i) with (lookup_mem se' i); rewrite Hsub_m.
        apply eval_mem_up_type_eq.
      - destruct i; try by (cbn; apply subskind_of_refl).
        rewrite <- type_skind_up_type_eq.
        move Hsub_sκ at bottom.
        specialize (Hsub_sκ i).
        assert (fst <$> lookup_type se' i = fst <$> lookup_type (se'.1, (sκ0, (sκ_T, T'))::se'.2) (S i)) by by cbn.
        rewrite H in Hsub_sκ.
        done.
      - cbn.
        destruct i; cbn; try done.
        + rewrite value_interp_eq_no_sv.
          Opaque skind_has_svalue.
          cbn.
          unfold skind_has_stype in skindhasstype.
          iIntros (sv').
          iSplitR; iIntros "Ht".
          * iExists sκ0.
            iSplitR; first done.
            destruct skindhasstype as (no & yes).
            iPoseProof (yes with "[$Ht]") as "%skindsv'".
            iFrame.
            iPureIntro.
            eapply skind_as_type_refine; try done.
          * cbn.
            iDestruct "Ht" as "(%sκ' & _ & _ & yes)".
            iFrame.
        + change (snd <$> se'.2 !! i) with (snd <$> lookup_type se' i).
          rewrite Hsub_T.
          iIntros (sv').
          iApply type_interp_up_type. (* THIS IS A COMPLETELY ADMITTED LEMMA THAT'S PROBABLY FINE *)
          (* NOTE: there may be other conditions here *)
          done.
      - cbn.
        destruct i; try (cbn; done). (* gets rid of the i=0 case, which is what we're putting in *)
        asimpl'; cbn; unfold core.funcomp.
        rewrite <- Hsub_t_good at 2.
        apply refresh_kinds_up_shift_type.
      - eapply sem_env_interp_insert_type; try done.
      - eapply sem_env_interp_insert_type; try done; try (by apply subskind_of_refl).
        erewrite <- eval_kind_subst_senv_eq; try done.
      - iDestruct "pls" as "(%sκ1 & %typeskind & %skindhassvalue)".
        erewrite <- eval_kind_subst_senv_eq; try done.
        iExists sκ.
        iSplitR; try done.
    }
    9: { (* rec, qed *)
      iIntros "Ht".
      cbn in τ'.
      rewrite type_interp_eq.
      Opaque rec_interp.
      iEval (cbn) in "Ht".
      Transparent rec_interp.
      inversion Hkind_τ; subst.
      inversion Hkind_τ'; subst.

      iDestruct "Ht" as "(%sκ & %Hevalκ & %SVskterp & Ht)".
      rewrite rec_interp_unfold.
      change (eval_kind_se se' κ0) with (eval_kind se' κ0).
      rewrite Hevalκ.

      erewrite eval_kind_subst_senv_eq in Hevalκ; try done.
      unfold τ'.
      cbn.
      iExists sκ.
      iPureIntro; done.
    }

  Admitted.

  Lemma skind_interp_chillin_backwards :
    ∀ τ F F' κ κ' (se:semantic_env (Σ:=Σ)) se' sub_m sub_r sub_s sub_t sv,
    let τ' := refresh_kinds F (subst_type sub_m sub_r sub_s sub_t τ) in
    (sem_env_rel_rep_eq se' se sub_r) ->
    (sem_env_rel_size_eq se' se sub_s) ->
    (sem_env_rel_mem_eq se' se sub_m) ->
    (sem_env_rel_sκ_eq se' se sub_t) ->
    (sem_env_rel_type_eq se' se sub_t) ->
    (∀ i, refresh_kinds F (sub_t i) = sub_t i) ->
    sem_env_interp F' se' ->
    sem_env_interp F se ->
    has_kind F' τ κ ->
    has_kind F τ' κ' ->
    type_interp rti sr τ' se sv -∗
    ∃ sκ, ⌜type_skind se' τ = Some sκ /\ skind_has_svalue sκ sv⌝.
  Proof.
    intros * Hsub_r Hsub_s Hsub_m Hsub_sκ Hsub_T Hsub_t_good Hse' Hse Hkind_τ Hkind_τ'.
    iIntros "Ht".
    pose proof (type_skind_refresh_subst_senv_eq F F' se se' sub_m sub_r sub_s
                  sub_t τ κ κ') as Hsubk.
    do 8 (specialize (Hsubk ltac:(auto))).
    rewrite type_interp_eq.
    iDestruct "Ht" as "(%sκ' & %Htsτ' & %Hsksv & _)".
    iPureIntro.
    rewrite Htsτ' in Hsubk.
    apply subskind_of_option_invl in Hsubk as (sκ & Htsτ & Hsubsk).
    exists sκ; split; try done.
    eapply skind_as_type_refine; try done.
  Qed.

  Lemma peel_off_add_skind_interp F F' se se' τ κ κ' sv sub_m sub_r sub_s sub_t :
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
    (pre_type_interp rti sr τ se' sv ∗-∗ pre_type_interp rti sr τ' se sv) ->
    (* type_eq_mod_kinds τ' (subst_type sub_m sub_r sub_s sub_t τ) -> *)
    type_interp rti sr τ se' sv ∗-∗
    type_interp rti sr τ' se sv.
  Proof.
    intros τ' Hse' Hse HseF' HseF Hsub_r Hsub_s Hsub_m Hsub_sκ Hsub_T
      Hsub_t_good Hkind_τ Hkind_τ'.
    intros Hequiv.
    iSplitR; iIntros "Ht".
    - iPoseProof (skind_interp_chillin with "[$Ht]") as "%Ht"; try done.
      rewrite !type_interp_eq.
      cbn -[type_skind].
      iDestruct "Ht" as "(%sκ_no & %no1 & %no2 & Ht)".
      destruct Ht as (sk & yes1 & yes2).
      iExists sk.
      iSplitR; first done; iSplitR; first done.
      by iApply Hequiv.
    - iPoseProof (skind_interp_chillin_backwards with "[$Ht]") as "%Ht"; try done.
      rewrite !type_interp_eq.
      cbn -[type_skind].
      iDestruct "Ht" as "(%sκ_no & %no1 & %no2 & Ht)".
      destruct Ht as (sk & yes1 & yes2).
      iExists sk.
      iSplitR; first done; iSplitR; first done.
      by iApply Hequiv.
  Qed.


  (* NOT DONE P:H THIS IS THE MAIN LEMMA *)
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
    iIntros (τ' Hse' Hse HseF' HseF Hsub_r Hsub_s Hsub_m Hsub_sκ Hsub_T
               Hsub_t_good Hkind_τ Hkind_τ').
    (* pose proof (rel_type_implies_rel_sκ se' se sub_t Hsub_T) as Hsub_t. *)
    (* comment/uncomment if you want/don't want to see them *)
    unfold_sem_rels.
    unfold sem_env_types_well_formed in *.
    (* note that this generalization is necessary for the exists_ types *)
    generalize dependent sv.
    generalize dependent se'.
    generalize dependent se.
    generalize dependent sub_m.
    generalize dependent sub_s.
    generalize dependent sub_r.
    generalize dependent sub_t.
    generalize dependent F.
    generalize dependent F'.
    generalize dependent κ.
    generalize dependent κ'.
    generalize dependent τ.
    induction τ using type_ind with
      (P0 := λ ft, ∀ F F' se se' cl sub_m sub_r sub_s sub_t,
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
           closure_interp rti sr ft se' cl ∗-∗
              closure_interp rti sr ft' se cl)
      (Pi := λ ft, ∀ F F' se se' cl sub_m sub_r sub_s sub_t,
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
           inner_closure_interp rti sr ft se' cl ∗-∗
              inner_closure_interp rti sr ft' se cl).
    * (** vart, qed *)
      intros.
      iSplitR.
      (* RE:Hsub_T *)
      (* note: this is The Test if Hsub_T is strong enough *)
      (* the test if it's weak enough is lower down *)
      {
        iIntros "Hoa".
        iPoseProof (skind_interp_chillin with "[$Hoa]") as "%Ey"; try done.
        rewrite type_interp_eq.
        iDestruct "Hoa" as "(%sk & %HEval & %Hoa & VarInterp)".
        iEval (cbn) in "VarInterp".

        specialize (Hsub_T idx).
        cbn in Hsub_T.
        specialize (Hsub_T sv).
        iPoseProof (Hsub_T) as "Hsub_T".
        iDestruct "Hsub_T" as "(Hsub_T & _)".
        iPoseProof ("Hsub_T" with "[VarInterp]") as "VarInterp". {
          destruct (snd <$> se'.2 !! idx) eqn:HT'; [rename o into T'|rewrite HT'; done].
          rewrite HT'. cbn. done.
        }

        rewrite type_interp_eq.
        unfold add_skind_interp.
        destruct Ey as (thesκ & htypeskind & sksv).
        cbn -[type_skind] in htypeskind.
        iExists thesκ.
        iSplitR; first done; iSplitR; first done.
        cbn.
        rewrite Hsub_t_good.
        rewrite value_interp_eq.
        iDestruct "VarInterp" as "(%i & %hate & %it & here)".
        done.
      }
      {
        iIntros "Hoa".
        iPoseProof (skind_interp_chillin_backwards with "[$Hoa]") as "%Ey"; try done.
        destruct Ey as (thesκ & htypeskind & sksv).
        cbn.
        rewrite Hsub_t_good.
        Transparent value_interp.
        unfold value_interp in Hsub_T.
        Opaque value_interp.
        cbn in Hsub_T.
        specialize (Hsub_T idx sv).
        rewrite <- Hsub_T.

        rewrite type_interp_eq.
        iExists thesκ.
        iSplitR; first done; iSplitR; first done.
        cbn.
        destruct (snd <$> se'.2 !! idx) eqn:HT'; [rename o into T'|rewrite HT'; done].
        rewrite HT'. cbn. done.
      }
    * (* i31, qed *)
      intros.
      inversion Hkind_τ; subst.
      cbn in τ'; subst τ'.
      inversion Hkind_τ'; subst.
      subst κ1; subst κ.
      iSplitR.
      all: iIntros "Hoa";
        rewrite !type_interp_eq;
        iDestruct "Hoa" as "(%sk & %HEval & %Hoa & _)";
        iExists sk.
      all: iSplitR; [iPureIntro | iSplitR; [iPureIntro; done | done]];
        rewrite <- HEval.
      1: symmetry.
      all: cbn; done.
    * (* numt, qed *)
      intros.
      assert (κ0 = κ) by (inversion Hkind_τ; subst; done).
      subst κ0.
      iSplitR; iIntros "Hoa".
      {
        rewrite !type_interp_eq.
        iDestruct "Hoa" as "(%sk & %HEval & %Hoa & _)".
        iExists sk; iSplitR; [iPureIntro | iSplitR; [iPureIntro; done | done]].
        rewrite <- HEval.
        symmetry.
        cbn.
        cbn in τ'; subst τ'.
        cbn in HEval.
        rewrite HEval.
        inversion Hkind_τ; inversion Hkind_τ'; subst; try subst κ0 κ1; cbn in *; done.
      }
      {
        rewrite !type_interp_eq.
        iDestruct "Hoa" as "(%sk & %HEval & %Hoa & _)".
        iExists sk; iSplitR; [iPureIntro | iSplitR; [iPureIntro; done | done]].
        rewrite <- HEval.
        cbn; inversion Hkind_τ; subst; done.
      }
    * (* sum, half done, fine *)
      intros.
      inversion Hkind_τ; subst.

      iSplitR; iIntros "Hoa".
      {
        iPoseProof (skind_interp_chillin with "[$Hoa]") as "%Ey"; try done.
        destruct Ey as (thesκ & thetypeskind & thesksv).
        rewrite type_interp_eq.
        iDestruct "Hoa" as "(%sk & %HEval & %Hoa & Hsuminterp)".
        unfold pre_type_interp.
        rewrite type_interp_eq.
        iExists thesκ.
        iSplitR; first done; iSplitR; first done.
        cbn in τ'.
        unfold τ'.
        unfold pre_type_interp.
        subst κ1.
        subst τ'.
        inversion Hkind_τ'; subst.
        cbn in HEval.
        apply bind_Some in HEval as (ιs & Hea & toinvert);
          inversion toinvert; subst; cbn in Hoa; clear toinvert.
        set (ρs0 := (get_all_lefts
         (map get_rep_or_size
            (map (kind_of_node F)
               (map (refresh_kinds F) (map (subst_type sub_m sub_r sub_s sub_t) τs)))))
                ) in *.
        iDestruct "Hsuminterp" as "(%i & %os & %off & %count &
                              %H67 & %H7 & %H8 & Hoa)".
        destruct (list_lookup i (map (type_interp rti sr) τs)) eqn:Hτi_interp; try done.
        rename o into τi_interp.

        (* idk how to work with these maps but lemme get some of this out *)
        assert (H': ∃ τi, τs !! i = Some τi /\ τi_interp = type_interp rti sr τi). {
          (* obvious by Hτi_interp *)

          admit.
        }
        destruct H' as (τi & Hτi_lookup & Hτi).
        subst τi_interp.

        cbn.
        iExists i, os, off, count.

      (* There's gonna have to be a LOT of refresh_kinds lemmas
         But it does seem okay, staring at it for a while.
        iSplitR; [done |
                   iSplitR; [iPureIntro |
                              iSplitR; [iPureIntro |]]]; last first.
        -- pose proof (Forall_lookup_1 _ _ i τi H Hτi_lookup) as IH_τi.
           specialize (IH_τi sub_t sub_r sub_s sub_m se Hse se' Hse'
                         Hsub_r Hsub_s Hsub_m Hsub_sκ Hsub_T
                         (SAtoms (take count (drop off os)))).

           assert (H': list_lookup i (map (type_interp rti sr)
                      (map (subst_type sub_m sub_r sub_s sub_t) τs)) =
                         Some (type_interp rti sr (subst_type sub_m sub_r sub_s sub_t τi))).
           {
             (* this by τs !! i = Some τi *)

             admit.
           }
           rewrite H'.
           by iApply IH_τi.
        -- apply fmap_Some.
           apply fmap_Some in H3 as (ιs_ρ & Hy & Hah).
           exists ιs_ρ.
           split; [|done].
           apply bind_Some.
           apply bind_Some in Hy as (ρ & Hz & Hbh).
           cbn in Hbh.
           exists (subst_representation sub_r ρ).
           split.
           ++ by apply map_lookup_helper_forwards.
           ++ rewrite <- Hbh.
              symmetry.
              eapply eval_rep_subst_senv_eq; done.
        -- unfold sum_offset in *.
           apply bind_Some in H2 as (ιss & Hy & Hah).
           apply bind_Some.
           (* hopefully *)
           exists ιss. split; [|done].
           (* Okay this is true by a combo of mapM lemmas and
                eval_rep_subst_senv_eq:
                Hsub_r -> eval_rep se' ρ =
                eval_rep se (subst_representation sub_r ρ)
            *)

           apply mapM_Some.
           apply mapM_Some in Hy.
           (* seems a bit annoying to prove but definitely true:
                - take i ρs and take i (map (..) ρs) operate on the same things
                - On those things, use eval_rep_subst_senv, and you're good
            *)
           admit. *)
        admit.
      }
      {
        cbn.
        admit.
      }
    * (* variant *)
      intros.
      eapply peel_off_add_skind_interp; try done.
      cbn.
      (* intros. *)
      (* rewrite !type_interp_eq. *)
      (* cbn. *)
      (* pose proof (eval_kind_subst_senv_eq se se' sub_r sub_s κ *)
      (*               Hsub_r Hsub_s) as Hevalκ. *)
      (* rewrite !Hevalκ. *)

      (* iSplitR. *)
      (* all: iIntros "Hoa". *)
      (* all: iDestruct "Hoa" as "(%sκ & #Hsκ & #Hsv & Htypeinterp)". *)
      (* all: iExists sκ; iFrame "#". *)
      (* all: iDestruct "Htypeinterp" as "(%i & %n & %ws & %ws' & #hin & #hsv & Htypeinterp)". *)
      (* all: iExists i, n, ws, ws'; iFrame "#". *)
      (* - destruct (list_lookup i (map (type_interp rti sr) τs)) as [τi|] eqn:Hτi; *)
      (*     rewrite Hτi; try done. *)
      (*   admit. *)
      (* - admit. *)
      admit.
    * (* prod *)
      (* intros. *)
      (* rewrite !type_interp_eq. *)
      (* cbn. *)
      (* pose proof (eval_kind_subst_senv_eq se se' sub_r sub_s κ *)
      (*               Hsub_r Hsub_s) as Hevalκ. *)
      (* rewrite !Hevalκ. *)

      (* iSplitR. *)
      (* all: iIntros "Hoa". *)
      (* all: iDestruct "Hoa" as "(%sκ & #Hsκ & #Hsv & Htypeinterp)". *)
      (* all: iExists sκ; iFrame "#". *)
      (* all: iDestruct "Htypeinterp" as "(%oss & #Hoss & Htypeinterp)". *)
      (* all: iExists oss; iFrame "#". *)
      (* all: cbn. *)
      (* all: do 2 (setoid_rewrite big_sepL2_fmap_l). *)
      (* all: iApply big_sepL2_mono; [|done]. *)
      (* all: intros i τ os Hτ Hos. *)
      (* all: cbn. *)
      (* all: pose proof (Forall_lookup_1 _ _ _ _ H Hτ) as IH. *)
      (* all: specialize (IH sub_t sub_r sub_s sub_m se Hse se' Hse'). *)
      (* all: specialize (IH Hsub_r Hsub_s Hsub_m Hsub_sκ Hsub_T). *)
      (* all: specialize (IH (SAtoms os)). *)
      (* all: iIntros "H". *)
      (* all: by iApply IH. *)
      admit.
    * (* struct *)
      (* intros. *)
      (* rewrite !type_interp_eq. *)
      (* cbn. *)
      (* pose proof (eval_kind_subst_senv_eq se se' sub_r sub_s κ *)
      (*               Hsub_r Hsub_s) as Hevalκ. *)
      (* rewrite !Hevalκ. *)

      (* iSplitR. *)
      (* all: iIntros "Hoa". *)
      (* all: iDestruct "Hoa" as "(%sκ & #Hsκ & #Hsv & Htypeinterp)". *)
      (* all: iExists sκ; iFrame "#". *)
      (* all: iDestruct "Htypeinterp" as "(%oss & #Hoss & Htypeinterp)". *)
      (* all: iExists oss; iFrame "#". *)
      (* all: cbn. *)
      (* all: rewrite !map_fmap. *)
      (* all: do 2 (setoid_rewrite big_sepL2_fmap_r). *)
      (* all: iApply big_sepL2_mono; [|done]. *)
      (* all: intros i ws τ Hos Hτ. *)
      (* all: cbn. *)
      (* all: pose proof (Forall_lookup_1 _ _ _ _ H Hτ) as IH. *)
      (* all: specialize (IH sub_t sub_r sub_s sub_m se Hse se' Hse'). *)
      (* all: specialize (IH Hsub_r Hsub_s Hsub_m Hsub_sκ Hsub_T). *)
      (* all: specialize (IH (SWords ws)). *)
      (* all: iIntros "H". *)
      (* all: by iApply IH. *)
      admit.
    * (* reft, qed *)
      intros.
      (* idk if this looses too much *)
      eapply peel_off_add_skind_interp; try done.
      cbn.
      rewrite <- (eval_mem_subst_senv_eq se se'); [|done].
      destruct (eval_mem se' μ) eqn:Hevalμ.
      2: cbn; iSplitR; try done.

      destruct b; destruct β.
      -- cbn.
         iSplitR.
         all: iIntros "(%ℓ & %fs & %ws & yes1 & yes2 & yes3 & Ht)".
         all: iExists ℓ, fs, ws; iFrame.
         all: iModIntro.
         all: inversion Hkind_τ; subst; inversion Hkind_τ'; subst.
         all: iApply IHτ; last done; try done.
      -- cbn.
         iSplitR.
         all: iIntros "(%ℓ & %fs & %ws & yes1 & yes2 & Ht)".
         all: iExists ℓ, fs, ws; iFrame.
         all: iModIntro.
         all: inversion Hkind_τ; subst; inversion Hkind_τ'; subst.
         all: iApply IHτ; last done; try done.
      -- cbn.
         iSplitR.
         all: iIntros "(%ℓ & %fs & yes1 & Ht)".
         all: iExists ℓ, fs; iFrame.
         all: iApply (na_inv_iff with "[$Ht]").
         all: repeat iModIntro.
         all: iSplitR; iIntros "(%ws & yes1 & yes2 & Ht)".
         all: iExists ws; iFrame.
         all: iModIntro.
         all: inversion Hkind_τ; subst; inversion Hkind_τ'; subst.
         all: iApply IHτ; last done; try done.
      -- cbn.
         iSplitR.
         all: iIntros "(%ℓ & %fs & %ws & yes1 & Ht)".
         all: iExists ℓ, fs, ws; iFrame.
         all: iApply (na_inv_iff with "[$Ht]").
         all: repeat iModIntro.
         all: iSplitR; iIntros "(yes1 & yes2 & Ht)".
         all: iFrame.
         all: iModIntro.
         all: inversion Hkind_τ; subst; inversion Hkind_τ'; subst.
         all: iApply IHτ; last done; try done.
    * (* coderef, qed *)
      intros.
      eapply peel_off_add_skind_interp; try done.
      cbn.
      inversion Hkind_τ; subst.
      inversion Hkind_τ'; subst.
      iSplit.
      all: iIntros "(%i & %i32 & %j & %cl & nrepr & nsv & Hcl & inv1 & inv2)".
      all: iExists i, i32, j, cl.
      all: iFrame "∗".
      all: specialize (IHτ F F' se se' cl sub_m sub_r sub_s sub_t).
      all: iApply IHτ; try done.
    * (* sert, qed  *)
      intros.
      eapply peel_off_add_skind_interp; try done.
      cbn.
      inversion Hkind_τ; subst.
      rename H3 into Hkind_τ_inner.
      inversion Hkind_τ'; subst.
      apply kind_of_node_good in H3 as kindnode.
      rewrite <- kindnode in *. subst κ; clear H.
      rename H3 into Hkind_τ'_inner.
      iSplit.
      all: iIntros "(%os & nsv & Ht)".
      all: iExists os.
      all: iFrame "∗".
      all: iApply IHτ; last done; try done.
    * (* plug, qed *)
      intros.
      eapply peel_off_add_skind_interp; try done.
      cbn.
      iSplitR; done.
    * (* span, qed *)
      intros.
      eapply peel_off_add_skind_interp; try done.
      cbn.
      iSplitR; done.
    * (* rec *)
      intros.

      iSplitR.
      {
        iIntros "Hoa".
        iPoseProof (skind_interp_chillin with "[$Hoa]") as "%Ey"; try done.
        destruct Ey as (thesκ & thetypeskind & thesksv).
        cbn in τ'.
        unfold τ'.
        rewrite !type_interp_eq.
        Opaque rec_interp.
        cbn.
        iExists thesκ.
        iSplitR; first done. iSplitR; first done.
        iDestruct "Hoa" as "(%sκ & %sκeval & %sκsv & Hoa)".
        rewrite !rec_interp_unfold.
        unfold eval_kind_se.
        (* I can prove sκ = thesκ *)
        Opaque skind_rec_interp.
        cbn.
        rewrite sκeval.
        cbn in thetypeskind.
        rewrite thetypeskind.
        erewrite eval_kind_subst_senv_eq in sκeval; try done.
        rewrite thetypeskind in sκeval; inversion sκeval; subst.
        iModIntro.
        inversion Hkind_τ; subst.
        inversion Hkind_τ'; subst.
        specialize (IHτ (subst_kind sub_r sub_s κ0) κ0 (F' <| fc_type_vars ::= cons κ0 |>)).
        specialize (IHτ H3).
        specialize (IHτ (F <| fc_type_vars ::= cons (subst_kind sub_r sub_s κ0) |>)).
        specialize (IHτ (up_type_type sub_t)).
        (* is this enough for good evars *)

        iApply IHτ; last done; try done. (* okay yay *)
        - admit.
        - (* RYAN: this is a tricky one *)
          cbn.
          apply Forall_cons.
          split; last done.
          unfold skind_has_stype.
          unfold ref_flag_stype_interp.
          (* this is where the weird persistence comes in *)
          (* if this was instead a value_interp, or something equivalent,
           then we can use kinding soundness*)
          admit.
        - admit.
        - (* same as above *)
          admit.
        - admit.
        - cbn.
          intros.
          change (se'.1.1.2 !! i) with (lookup_rep se' i).
          rewrite (Hsub_r i).
          apply eval_rep_up_type_eq.
        - cbn.
          intros.
          change (se'.1.2 !! i) with (lookup_size se' i).
          rewrite (Hsub_s i).
          apply eval_size_up_type_eq.
        - cbn.
          intros.
          change (se'.1.1.1 !! i) with (lookup_mem se' i).
          rewrite (Hsub_m i).
          apply eval_mem_up_type_eq.
        - Opaque skind_rec_interp.
          Opaque type_skind.
          cbn.
          intros.
          destruct i.
          + cbn.
            unfold unscoped.var_zero.
            Transparent type_skind.
            unfold type_skind.
            cbn.
            Opaque type_skind.
            apply subskind_of_refl.
          + change (se'.2 !! i) with (lookup_type se' i).
            move Hsub_sκ at bottom.
            change ((se.1, (?x, (?y,?z))::se.2)) with (senv_insert_type x y z se).
            erewrite <- type_skind_up_type_eq.
            cbn.
            cbn in Hsub_sκ.
            apply Hsub_sκ.

          Transparent type_skind.
          Opaque skind_rec_interp.
        - (* RYAN: this is where skindrecinterp needs to be equiv to val interp *)
          cbn.
          intros.
          destruct i.
          + cbn.
            rewrite !value_interp_eq_no_sv.
            (* Right here *)
            admit.
          + change (se'.2 !! i) with (lookup_type se' i).
            rewrite (Hsub_T i).
            cbn.
            (* iApply type_interp_up_type. *)
            admit.
      }
      {
        admit.
      }
    * (* exists mem, nearly qed with that one big lemma and two boring *)
      intros.
      eapply peel_off_add_skind_interp; try done.
      cbn -[senv_insert_mem].
      inversion Hkind_τ; subst.
      rename H4 into Hkind_τ_inner.
      inversion Hkind_τ'; subst.
      rename H5 into Hkind_τ'_inner.
      (* carefully specialize IHτ now *)
      specialize (IHτ (subst_kind sub_r sub_s κ0) κ0 (F' <| fc_kind_ctx; kc_mem_vars ::= S |>) Hkind_τ_inner).
      specialize (IHτ (F <| fc_kind_ctx; kc_mem_vars ::= S |>)).
      (* I think the rest will be possible to iApply *)
      iSplitR; iIntros "(%μ & Ht)"; iExists μ.
      all: iApply IHτ; last done; try done.
      (* I think I literally end up proving these in the skind chillin *)
      (* TODO: make the exists mem/rep/size/type expansion thingies actual lemmas *)
      (* then probably a tactic that just shreds them *)

      (* these should mostly work, but they're incomplete *)
      (* all: iApply IHτ; try done. *)
      (* (* these lemmas are half done with only the value_interp ones being scary *) *)
      (* (* make these hypotheses/asserts so it's easy  *) *)
      (* (* i'll make them asserts/lemmas later *) *)
      (* (* the exists rep and all that have some of these by default already *) *)
      (* (* mem just hasn't had them yet *) *)
      (* 1, 6: intros; cbn; *)
      (*       change ((senv_insert_mem μ se').1.1.2 !! i) with (lookup_rep se' i); *)
      (*       rewrite (Hsub_r i); *)
      (*       apply eval_rep_up_memory_eq. *)
      (* 1, 5: intros; cbn; *)
      (*       change ((senv_insert_mem μ se').1.2 !! i) with (lookup_size se' i); *)
      (*       rewrite (Hsub_s i); *)
      (*       apply eval_size_up_memory_eq. *)
      (* 1, 4: intros; cbn; *)
      (*       destruct i; cbn; try done; *)
      (*       change ((senv_insert_mem μ se').1.1.1 !! S i) with (lookup_mem se' i); *)
      (*       rewrite (Hsub_m i); *)
      (*       unfold core.funcomp; *)
      (*       cbn; *)
      (*       apply eval_mem_up_shift_mem_eq. *)
      (* 1, 3: intros; *)
      (*       change (fst <$> lookup_type (senv_insert_mem μ se') i) with *)
      (*          (fst <$> lookup_type se' i); *)
      (*       rewrite (Hsub_sκ i); *)
      (*       apply type_skind_up_memory_eq. *)
      (* 1, 2: intros; *)
      (*       change (snd <$> lookup_type (senv_insert_mem μ se') i) with *)
      (*          (snd <$> lookup_type se' i); *)
      (*       rewrite (Hsub_T i); *)
      (*       iIntros; *)
      (*       iApply type_interp_up_memory. *)
      all: admit.
    * (* exists rep *)
      admit.
    * (* exists size *)
      admit.
    * (* exists type *)
      admit.
    * (* mono fun *)
      intros.
      setoid_rewrite inner_closure_interp_eq.
      asimpl'.
      unfold inner_closure_interp'.
      rename H into IHτs1. rename H0 into IHτs2.
      rename H1 into Hse'. rename H2 into Hse.
      rename H3 into HseF'. rename H4 into HseF.
      rename H5 into Hsub_r. rename H6 into Hsub_s.
      rename H7 into Hsub_m. rename H8 into Hsub_sκ.
      rename H9 into Hsub_T.
      rename H10 into Hsub_t_good.
      rename H11 into Hkind_ft. rename H12 into Hkind_ft'.
      inversion Hkind_ft; subst.
      inversion Hkind_ft'; subst.
      rename H2 into Hkindτs1; rename H3 into Hkindτs2.
      rename H4 into Hkindτs1'; rename H5 into Hkindτs2'.
      rename κs0 into κs1'; rename κs3 into κs2'.
      (* argh imma need this sort of stuff for refresh_kinds *)
      pose proof (translate_types_refresh_subst_senv_eq
                    F F' se se' sub_m sub_r sub_s sub_t τs1 κs1 κs1'
                    ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto)  ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ) as Htranslate1.
      pose proof (translate_types_refresh_subst_senv_eq
                    F F' se se' sub_m sub_r sub_s sub_t τs2 κs2 κs2'
                    ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto)  ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ) as Htranslate2.
      unfold mono_closure_interp.
      Opaque atoms_interp.
      Opaque translate_types.
      cbn.
      rewrite !Htranslate1.
      rewrite !Htranslate2.
      destruct cl as [inst f tlocs es | a b]; [|cbn; iSplitR; done].
      destruct f as [ts1 ts2].

      iAssert (∀ oss : leibnizO (list (list atom)),
        (([∗ list] '(τ : semantic_env -n> leibnizO semantic_value -n> iPropO Σ);os ∈ map (type_interp rti sr)
                    (map (refresh_kinds F)
                        (map (subst_type sub_m sub_r sub_s sub_t) τs1));oss,
            τ se (SAtoms os))%I ∗-∗
          ([∗ list] '(τ : semantic_env -n> leibnizO semantic_value -n> iPropO Σ);os ∈
                          map (type_interp rti sr) τs1;oss,
              τ se' (SAtoms os))%I)%I
              )%I with "[]" as "FlipSepL2τs1". {
        iIntros (oss).
        rewrite !map_fmap.
        repeat rewrite big_sepL2_fmap_l.
        iSplitR; iIntros "Hoa".
        all: iApply (big_sepL2_mono with "[$Hoa]").
        all: intros i τ os Hτ Hos.
        all: cbn.
        all: pose proof (Forall_lookup_1 _ _ _ _ IHτs1 Hτ) as IH.
        all: pose proof (Forall2_lookup_l _ _ _ _ _ Hkindτs1 Hτ) as (κ_τ & Hκ & Haskind_τ).
        all: pose proof Hτ as temp.
        all: pose proof (map_lookup_helper_forwards
                           (subst_type sub_m sub_r sub_s sub_t) τs1 i τ temp).
        all: pose proof (map_lookup_helper_forwards
                           (refresh_kinds F) _ i _ H) as Himapτ.
        all: pose proof (Forall2_lookup_l _ _ _ _ _ Hkindτs1' Himapτ) as
          (κ_τ' & Hκ' & Haskind_τ').
        all: iIntros "H".
        all: iApply IH; last done; try done.
      }
      iAssert (∀ oss : leibnizO (list (list atom)),
        (([∗ list] '(τ : semantic_env -n> leibnizO semantic_value -n> iPropO Σ);os ∈ map (type_interp rti sr)
            (map (refresh_kinds F)
                (map (subst_type sub_m sub_r sub_s sub_t) τs2));oss,
            τ se (SAtoms os))%I ∗-∗
        ([∗ list] '(τ : semantic_env -n> leibnizO semantic_value -n> iPropO Σ);os ∈
                  map (type_interp rti sr) τs2;oss,
            τ se' (SAtoms os))%I)%I
              )%I with "[]" as "FlipSepL2τs2". {
        iIntros (oss).
        rewrite !map_fmap.
        repeat rewrite big_sepL2_fmap_l.
        iSplitR; iIntros "Hoa".
        all: iApply (big_sepL2_mono with "[$Hoa]").
        all: intros i τ os Hτ Hos.
        all: cbn.
        all: pose proof (Forall_lookup_1 _ _ _ _ IHτs2 Hτ) as IH.
        all: pose proof (Forall2_lookup_l _ _ _ _ _ Hkindτs2 Hτ) as (κ_τ & Hκ & Haskind_τ).
        all: pose proof Hτ as temp.
        all: pose proof (map_lookup_helper_forwards
                           (subst_type sub_m sub_r sub_s sub_t) τs2 i τ temp).
        all: pose proof (map_lookup_helper_forwards
                           (refresh_kinds F) _ i _ H) as Himapτ.
        all: pose proof (Forall2_lookup_l _ _ _ _ _ Hkindτs2' Himapτ) as
          (κ_τ' & Hκ' & Haskind_τ').
        all: iIntros "H".
        all: iApply IH; last done; try done.
      }
      (* unfold mono_closure_interp. *)
      (* I hate mono closure interp so much *)
      (* I think this is as far as I get without splitting *)
      iSplitR.
      {
        iIntros "Hoa".
        iDestruct "Hoa" as "(#ts1trans & #ts2trans & #Hoa)".
        iSplitR; [done| iSplitR; [done|]].
        do 2 iModIntro.
        iIntros (vs1 os1 θ) "Hos Htypes Hrt Hown Hfr Hrun".
        iSpecialize ("Hoa" $! vs1 os1 θ).

        iClear "ts1trans ts2trans".

        iSpecialize ("Hoa" with "[$Hos] [Htypes] [$Hrt] [$Hown] [$Hfr] [$Hrun]").
        {
          iDestruct "Htypes" as "(%oss & rest)".
          iDestruct "rest" as "(#Hoss & Htypes)".
          iExists oss; iFrame "#".
          iApply "FlipSepL2τs1"; done.
        }

        iApply (cwp_label_wand with "[-]").
        - iApply (cwp_return_wand with "[-]").
          + iApply (cwp_wand with "[-]").
            * done.
            * iIntros (f v) "H".
              iDestruct "H" as "(H & $ & $)".
              iDestruct "H" as "(%os2 & $ & (%oss & $ & H))".
              iApply "FlipSepL2τs2"; done.
          + cbn.
            unfold return_wand.
            iSplitR; [iPureIntro; by cbn|].
            iIntros (vs Hvs) "H".
            iDestruct "H" as "(H & $ & $)".
            iDestruct "H" as "(%os2 & $ & (%oss & $ & H))".
            iApply "FlipSepL2τs2"; done.
        - unfold label_ctx_wand.
          iSplitR; [iPureIntro; by cbn|].
          cbn. iSplitR; [|done].
          unfold label_wand.
          iSplitR; [iPureIntro; by cbn|].
          iIntros (f vs Hvs) "H".
          iDestruct "H" as "(H & $ & $)".
          iDestruct "H" as "(%os2 & $ & (%oss & $ & H))".
          iApply "FlipSepL2τs2"; done.
      }
      {
        iIntros "Hoa".
        iDestruct "Hoa" as "(#ts1trans & #ts2trans & #Hoa)".
        iSplitR; [done| iSplitR; [done|]].
        do 2 iModIntro.
        iIntros (vs1 os1 θ) "Hos Htypes Hrt Hown Hfr Hrun".
        iSpecialize ("Hoa" $! vs1 os1 θ).

        iClear "ts1trans ts2trans".

        iSpecialize ("Hoa" with "[$Hos] [Htypes] [$Hrt] [$Hown] [$Hfr] [$Hrun]").
        {
          iDestruct "Htypes" as "(%oss & rest)".
          iDestruct "rest" as "(#Hoss & Htypes)".
          iExists oss; iFrame "#".
          iApply "FlipSepL2τs1"; done.
        }

        iApply (cwp_label_wand with "[-]").
        - iApply (cwp_return_wand with "[-]").
          + iApply (cwp_wand with "[-]").
            * done.
            * iIntros (f v) "H".
              iDestruct "H" as "(H & $ & $)".
              iDestruct "H" as "(%os2 & $ & (%oss & $ & H))".
              iApply "FlipSepL2τs2"; done.
          + cbn.
            unfold return_wand.
            iSplitR; [iPureIntro; by cbn|].
            iIntros (vs Hvs) "H".
            iDestruct "H" as "(H & $ & $)".
            iDestruct "H" as "(%os2 & $ & (%oss & $ & H))".
            iApply "FlipSepL2τs2"; done.
        - unfold label_ctx_wand.
          iSplitR; [iPureIntro; by cbn|].
          cbn. iSplitR; [|done].
          unfold label_wand.
          iSplitR; [iPureIntro; by cbn|].
          iIntros (f vs Hvs) "H".
          iDestruct "H" as "(H & $ & $)".
          iDestruct "H" as "(%os2 & $ & (%oss & $ & H))".
          iApply "FlipSepL2τs2"; done.
      }
    * (* foralltype, should finish a bit more *)
      intros.
      rename H into Hse'. rename H0 into Hse.
      rename H1 into Hsub_r. rename H2 into Hsub_s.
      rename H3 into Hsub_m. rename H4 into Hsub_sκ.
      rename H5 into Hsub_T.

      rewrite !inner_closure_interp_eq.
      cbn.
      (* pose proof (eval_kind_subst_senv_eq se se' sub_r sub_s κ *)
      (*               Hsub_r Hsub_s) as Hevalκ. *)
      (* rewrite !Hevalκ. *)

      (* iSplitR. *)
      (* all: iIntros "#Hoa". *)
      (* all: iModIntro. *)
      (* all: iIntros (sκ sκ_T T hsk sksk sktype). *)
      (* all: iSpecialize ("Hoa" $! sκ sκ_T T hsk sksk sktype). *)
      admit.

    * (* forall inner *)
      intros.
      rewrite !closure_interp_eq; cbn.
      rewrite <- !inner_closure_interp_eq; cbn.
      iApply IHτ; try done.
      -- inversion H9. done.
      -- cbn in ft'.
         subst ft'.
         inversion H10; done.

    * (* forallmem *)
      (* intros. *)
      (* rename H into Hse'. rename H0 into Hse. *)
      (* rename H1 into Hsub_r. rename H2 into Hsub_s. *)
      (* rename H3 into Hsub_m. rename H4 into Hsub_sκ. *)
      (* rename H5 into Hsub_T. *)

      (* rewrite !closure_interp_eq. *)
      (* cbn. *)

      (* iSplitR. *)
      (* all: iIntros "#Hoa". *)
      (* all: iModIntro. *)
      (* all: iIntros (μ); iSpecialize ("Hoa" $! μ). *)
      (* all: specialize (IHτ (senv_insert_mem μ se) (senv_insert_mem μ se')). *)
      (* all: iApply IHτ; last done. *)
      (* okay and then these are literally identical to the future lemma things in existsmem!
         just need to lemma-ify them and then this will be easier.
       *)

      admit.
    * (* forallrep *)
      admit.
    * (* forallsize *)
      admit.

  Admitted.


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


  (* BIG NOTE: THIS IS WHAT I'M USING FOR TESTING RELATION SATISFIABILITY *)
  (* NOT DONE P:H COPY PASTE FROM MAIN TYPE_INTERP BIDIRECTIONAL PROOF *)
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
  Admitted.

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
  Admitted.

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
