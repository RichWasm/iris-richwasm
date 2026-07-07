Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.substitution.
Require Import RichWasm.iris.logrel.logrel_properties.
Require Import RichWasm.iris.logrel.env_props.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section inst.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Ltac unfold_sem_rels :=
    unfold
    sem_env_rel_rep_eq, sem_env_rel_size_eq,
      sem_env_rel_mem_eq, sem_env_types_well_formed, sub_t_well_formed,
      sem_env_rel_type_eq, sem_env_rel_sκ_eq in *.

  Lemma stupid K n :
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
        apply stupid in Hok.
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

  (* SEM ENV INTERPS - TO MOVE TO LOGREL_PROPERTIES? *)

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
    1: exact mr.
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

  (* NOT DONE P:L TO MOVE TO LOGREL/UTIL.V? *)
  Lemma has_kind_ft_function_type_eq_mod_kinds:
    (∀ τ F κ subm subr subs subt,
        let substed := subst_type subm subr subs subt τ in
        has_kind F τ κ ->
        type_eq_mod_kinds τ substed ->
        τ = refresh_kinds F substed
    ) /\
    (∀ ϕ' F ϕ subm subr subs subt, let substed :=
      (subst_function_type subm subr subs subt ϕ) in
    has_kind_ft F ϕ' ->
    function_type_eq_mod_kinds ϕ' substed ->
    ϕ' = refresh_kinds_ft F substed) /\
    (∀ ϕ' F ϕ subm subr subs subt, let substed :=
      (subst_inner_function_type subm subr subs subt ϕ) in
    has_kind_ift F ϕ' ->
    inner_function_type_eq_mod_kinds ϕ' substed ->
    ϕ' = refresh_kinds_ift F substed).
  Proof.
    Opaque type_eq_mod_kinds.
    Opaque function_type_eq_mod_kinds.
    apply type_and_function_ind; intros * Hkind Heqmod; cbn in *;
      try (inversion Hkind; subst; done).
    Transparent type_eq_mod_kinds.
    Transparent function_type_eq_mod_kinds.
    1: {
      cbn in *.
      subst substed.
      destruct (subt idx) eqn:Hs; try done.
      subst; done.
    }
    6: {
      rename Hkind into IHkind; rename Heqmod into F.
      intros * Hkind Heqmod.
      inversion Hkind; subst.
      cbn in Heqmod.
      eapply IHkind in H3; try done.
      rewrite <- H3.
      subst κ1; done.
    }
    7: {
      cbn in *.
      rewrite <- Heqmod.
      inversion Hkind; subst; done.
    }
    16: {
      rename Hkind into IHkind; rename Heqmod into F.
      intros * Hkind Heqmod.
      cbn in *.
      inversion Hkind; subst.
      destruct (subst_function_type subm subr subs subt ϕ) eqn:hs;
        try done.
      assert (∃ f', ϕ = ForallMemT f'). {
        destruct ϕ; cbn in hs; inversion hs; try done.
        exists ϕ; done.
      }
      destruct H as (f' & ->).
      cbn in hs.
      inversion hs.
      subst f.
      eapply IHkind in H1; try done.
      rewrite H1.
      cbn.
      done.
    }
    14: {
      rename Hkind into IHkind; rename Heqmod into F.
      intros * Hkind Heqmod.
      cbn in *.
      inversion Hkind; subst.
      destruct (subst_inner_function_type subm subr subs subt ϕ) eqn:hs;
        try done.
      destruct Heqmod as (-> & Heqmod).
      assert (∃ κ' f', ϕ = ForallTypeT κ' f'). {
        destruct ϕ; cbn in hs; inversion hs; try done.
        eexists _, _; try done.
      }
      destruct H as (f' & κ' & ->).
      cbn in hs.
      inversion hs.
      subst i k.
      eapply IHkind in H3; try done.
      rewrite H3.
      cbn.
      done.
    }
    13: {
      rename Hkind into IHkind1; rename Heqmod into IHkind2.
      intros * Hkind Heqmod.
      cbn in *.
      destruct (subst_inner_function_type subm subr subs subt ϕ) eqn:hs;
        try done.
      (* okay yup this looks fine *)
      cbn.
      (* it looks annoying but fine to combine everything *)
      admit.
    }
  Admitted.

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
    setoid_rewrite value_interp_eq.

    (* mini kinding quarantine *)
    assert (Hkind_first: has_kind F (CodeRefT κ ϕ) κ). {
        inversion Hok.
        inversion H1; subst.
        inversion H3; subst. clear H8.
        inversion H7; subst.
        destruct H5 as (pls & hlp).
        inversion pls; subst.
        inversion H5; subst.
        constructor. done.
    }
    assert (Hkind: has_kind F (CodeRefT κ ϕ') κ). {
        inversion Hok.
        inversion H1; subst.
        inversion H4; subst. clear H8.
        inversion H7; subst.
        destruct H5 as (pls & hlp).
        inversion pls; subst.
        inversion H5; subst.
        constructor. done.
    }
    inversion Hkind; subst. rename H3 into Hkind_ft.
    (* now we need to use the key hypothesis: Hfinst *)
    destruct Hfinst.

    1: destruct H1.
    1: assert (Hϕ': ϕ' = refresh_kinds_ift F
            (subst_inner_function_type VarM VarR VarS (unscoped.scons τ VarT) ϕ)) by
        (pose proof (has_kind_ft_function_type_eq_mod_kinds) as (_ & H10);
         eapply H10; try done; inversion Hkind_ft; subst; done).
    1: rewrite Hϕ'.
    2-4: unfold ϕ'.
    (* dig into all at once down to closure interp *)

    all: iDestruct "Hos" as "(%sκ & %toinvert & HKindInterp & Rest)".
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

    - rewrite !closure_interp_eq.
      Opaque senv_insert_type.
      cbn.
      Transparent senv_insert_type.
      rewrite <- inner_closure_interp_eq.
      assert (∃ x, eval_kind se κ0 = Some x). {
        inversion Hkind_first; subst.
        inversion H6; subst.
        inversion H7; subst.
        pose proof (eval_kind_ok_Some _ _ _ H H9).
        inversion H4.
        eexists; exact H5.
      }
      destruct H4 as (x & hevalx).
      inversion Hkind_first; subst.
      inversion Hkind_ft; subst; inversion H6; subst.
      inversion H8; subst.
      iApply inner_closure_interp_scons_insert_type; try done.
    - pose proof (refresh_kinds_id) as (_ & Hid); try done.
      apply Hid in Hkind_ft as Htorewrite.
      fold ϕ'; rewrite Htorewrite; unfold ϕ'.
      inversion Hkind_first; subst. inversion H4; subst.
      rewrite Htorewrite in Hkind_ft.
      by iApply closure_interp_scons_insert_mem.
    - pose proof (refresh_kinds_id) as (_ & Hid); try done.
      apply Hid in Hkind_ft as Htorewrite.
      fold ϕ'; rewrite Htorewrite; unfold ϕ'.
      inversion Hkind_first; subst. inversion H4; subst.
      rewrite Htorewrite in Hkind_ft.
      by iApply closure_interp_scons_insert_rep.
    - pose proof (refresh_kinds_id) as (_ & Hid); try done.
      apply Hid in Hkind_ft as Htorewrite.
      fold ϕ'; rewrite Htorewrite; unfold ϕ'.
      inversion Hkind_first; subst. inversion H4; subst.
      rewrite Htorewrite in Hkind_ft.
      by iApply closure_interp_scons_insert_size.
  Qed.

End inst.
