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

  Lemma eval_rep_mem_irrel se ρ ιs μ :
    eval_rep se ρ = Some ιs ->
    eval_rep (senv_insert_mem (Σ:=Σ) μ se) ρ = Some ιs.
  Proof.
    by induction ρ using rep_ind.
  Qed.

  Lemma eval_size_mem_irrel se σ n μ :
    eval_size se σ = Some n ->
    eval_size (senv_insert_mem (Σ:=Σ) μ se) σ = Some n.
  Proof.
    by induction σ using size_ind.
  Qed.

  (* TODO: Is the assumption too strong? We only care about the free variables in ρ. *)
  Lemma eval_rep_subst_senv (se se' : semantic_env (Σ:=Σ)) sub_r ρ ιs :
    (forall i ιs', se' !! i = Some ιs' -> eval_rep se (sub_r i) = Some ιs') ->
    eval_rep se' ρ = Some ιs ->
    eval_rep se (subst_representation sub_r ρ) = Some ιs.
  Proof.
    intros Hsub.
    generalize dependent ιs.
    induction ρ as [n|ρs IH|ρs IH|ιs' IH] using rep_ind.
    - intros ? H. cbn in *. by apply Hsub.
    - intros ? H.
      cbn in *.
      apply fmap_Some in H as (ιss & Hρs & ->).
      apply fmap_Some.
      eexists.
      split; last done.
      apply mapM_Some in Hρs.
      apply mapM_Some.
      rewrite <- (list_fmap_id ιss).
      rewrite map_fmap.
      apply Forall2_fmap.
      eapply Forall2_impl; first done.
      intros ρ ιs H.
      cbn in H.
  Admitted.

  Lemma eval_size_subst_env (se se' : semantic_env (Σ:=Σ)) sub_r sub_s σ n :
    (forall i ιs', se' !! i = Some ιs' -> eval_rep se (sub_r i) = Some ιs') ->
    (forall i n, se' !! i = Some n -> eval_size se (sub_s i) = Some n) ->
    eval_size se' σ = Some n ->
    eval_size se (subst_size sub_r sub_s σ) = Some n.
  Proof.
    intros Hsub_r Hsub_s.
    generalize dependent n.
    induction σ using size_ind.
    - intros ? H. cbn in *. by apply Hsub_s.
    - admit.
    - admit.
    - intros ??.
      cbn in *.
      apply fmap_Some in H as (ιss & Hρ & ->).
      apply fmap_Some.
      eexists.
      split; last done.
      eapply eval_rep_subst_senv; last done.
      apply Hsub_r.
    - done.
  Admitted.

  Lemma eval_kind_subst_senv (se se' : semantic_env (Σ:=Σ)) sub_r sub_s κ sκ :
    (forall i ιs', se' !! i = Some ιs' -> eval_rep se (sub_r i) = Some ιs') ->
    (forall i n, se' !! i = Some n -> eval_size se (sub_s i) = Some n) ->
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

  Lemma type_skind_subst_senv se se' sub_m sub_r sub_s sub_t τ sκ :
    (forall i ιs', se' !! i = Some ιs' -> eval_rep se (sub_r i) = Some ιs') ->
    (forall i n, se' !! i = Some n -> eval_size se (sub_s i) = Some n) ->
    (forall i sκ', se' !! i = Some sκ' -> type_skind se (sub_t i) = Some sκ') ->
    type_skind (Σ:=Σ) se' τ = Some sκ ->
    type_skind (Σ:=Σ) se (subst_type sub_m sub_r sub_s sub_t τ) = Some sκ.
  Proof.
    unfold type_skind.
    intros Hsub_r Hsub_s Hsub_t H.
    destruct τ.
    1: by apply Hsub_t.
    all: by eapply eval_kind_subst_senv.
  Qed.

  Lemma type_arep_subst_senv se se' sub_m sub_r sub_s sub_t τ ιs :
    (forall i ιs', se' !! i = Some ιs' -> eval_rep se (sub_r i) = Some ιs') ->
    (forall i n, se' !! i = Some n -> eval_size se (sub_s i) = Some n) ->
    (forall i sκ', se' !! i = Some sκ' -> type_skind se (sub_t i) = Some sκ') ->
    type_arep (Σ:=Σ) se' τ = Some ιs ->
    type_arep (Σ:=Σ) se (subst_type sub_m sub_r sub_s sub_t τ) = Some ιs.
  Proof.
    unfold type_arep.
    intros Hsub_r Hsub_s Hsub_t H.
    apply bind_Some in H as (sκ & Hsκ & Hιs).
    apply bind_Some.
    eexists.
    split; last done.
    by eapply type_skind_subst_senv.
  Qed.

  Lemma translate_type_subst_senv se se' sub_m sub_r sub_s sub_t τ ts :
    (forall i ιs', se' !! i = Some ιs' -> eval_rep se (sub_r i) = Some ιs') ->
    (forall i n, se' !! i = Some n -> eval_size se (sub_s i) = Some n) ->
    (forall i sκ', se' !! i = Some sκ' -> type_skind se (sub_t i) = Some sκ') ->
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
    (forall i ιs', se' !! i = Some ιs' -> eval_rep se (sub_r i) = Some ιs') ->
    (forall i n, se' !! i = Some n -> eval_size se (sub_s i) = Some n) ->
    (forall i sκ', se' !! i = Some sκ' -> type_skind se (sub_t i) = Some sκ') ->
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

  Lemma closure_interp0_subst_senv se se' ϕ cl sub_m sub_r sub_s sub_t :
    (forall i ιs', se' !! i = Some ιs' -> eval_rep se (sub_r i) = Some ιs') ->
    (forall i n, se' !! i = Some n -> eval_size se (sub_s i) = Some n) ->
    (forall i sκ', se' !! i = Some sκ' -> type_skind se (sub_t i) = Some sκ') ->
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
      + intros ?? H. asimpl'. admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  (* TODO: Might need to be simultaneous in all sorts. *)
  Lemma closure_interp0_subst_senv_mem se se' ϕ cl sub_m sub_r sub_s sub_t :
    (forall i, mem_ok_se se (sub_m i) -> i < length (senv_mems se')) ->
    closure_interp0 rti sr (value_interp rti sr) se' ϕ cl -∗
    let ϕ' := subst_function_type sub_m sub_r sub_s sub_t ϕ in
    closure_interp0 rti sr (value_interp rti sr) se ϕ' cl.
  Proof.
    intros Hok.
    generalize dependent sub_t.
    generalize dependent sub_s.
    generalize dependent sub_r.
    generalize dependent sub_m.
    generalize dependent se.
    generalize dependent se'.
    induction ϕ as [τs1 τs2| | | |κ] .
    - iIntros (???????) "#Hcl".
      destruct cl; [|auto].
      destruct f as [τs1_trans τs2_trans] eqn:Hf.
      iDestruct "Hcl" as "(%Hτs1 & %Hτs2 & Hcl)".
      iSplitR; [iPureIntro| iSplitR; [iPureIntro|]]; fold (subst_type sub_m sub_r sub_s sub_t).
      + admit. (* translate_types *)
      + admit. (* translate_types *)
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
    - iIntros (???????) "Hcl %".
      iApply IHϕ; last done.
      intros ? Hok'.
      destruct i.
      + instantiate (1 := MemMM). cbn. lia.
      + apply mem_ok_se_up_mem in Hok'. apply Hok in Hok'. cbn. lia.
    - iIntros (???????) "Hcl %".
      iApply IHϕ; last done.
      intros ? Hok'.
      apply Hok.
      by rewrite mem_ok_se_up_rep.
    - iIntros (???????) "Hcl %".
      iApply IHϕ; last done.
      intros ? Hok'.
      apply Hok.
      by rewrite mem_ok_se_up_size.
    - iIntros (???????) "Hcl % % %Hsκ %HT".
      iApply IHϕ; last iApply "Hcl"; last done.
      + intros i Hok'. apply Hok. by rewrite mem_ok_se_up_type.
      + iPureIntro. admit. (* eval_kind *)
  Admitted.

  Lemma closure_interp0_scons_insert_mem F se μ ϕ cl :
    mem_ok F.(fc_kind_ctx) μ ->
    sem_env_interp F se ->
    (∀ μ', closure_interp0 rti sr (value_interp rti sr) (senv_insert_mem μ' se) ϕ cl) -∗
    let ϕ' := subst_function_type (unscoped.scons μ VarM) VarR VarS VarT ϕ in
    closure_interp0 rti sr (value_interp rti sr) se ϕ' cl.
  Proof.
    iIntros (Hok Hse) "Hcl".
    iApply closure_interp0_subst_senv_mem; last done.
    intros i Hok_se.
    destruct i.
    - cbn. lia.
    - instantiate (1:=MemMM). cbn in *. lia.
  Qed.

  Lemma closure_interp0_scons_insert_rep F se ρ ϕ cl :
    rep_ok (fc_kind_ctx F) ρ ->
    sem_env_interp F se ->
    (∀ ι, closure_interp0 rti sr (value_interp rti sr) (senv_insert_rep ι se) ϕ cl) -∗
    let ϕ' := subst_function_type VarM (unscoped.scons ρ VarR) VarS VarT ϕ in
    closure_interp0 rti sr (value_interp rti sr) se ϕ' cl.
  Proof.
    iIntros (Hok Hse) "Hcl".
  Admitted.

  Lemma closure_interp0_scons_insert_size F se σ ϕ cl :
    size_ok (fc_kind_ctx F) σ ->
    sem_env_interp F se ->
    (∀ n, closure_interp0 rti sr (value_interp rti sr) (senv_insert_size n se) ϕ cl) -∗
    let ϕ' := subst_function_type VarM VarR (unscoped.scons σ VarS) VarT ϕ in
    closure_interp0 rti sr (value_interp rti sr) se ϕ' cl.
  Proof.
    iIntros (Hok Hse) "Hcl".
  Admitted.

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
