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

  Lemma mem_ok_se_up μ se sub_m i :
    mem_ok_se se (sub_m i) <->
    mem_ok_se (senv_insert_mem μ se) (up_memory_memory sub_m (S i)).
  Proof.
    unfold mem_ok_se.
    split.
    {
      intros H.
      assert (Hope: (ren_memory unscoped.shift) (sub_m i) = up_memory_memory sub_m (S i)). {
        substify. done.
      }
      rewrite <- Hope.
      cbn.
      destruct (sub_m i) eqn:Hsubi.
      - cbn.
        unfold unscoped.shift.
        lia.
      - cbn. auto.
    }
    {
      intros H.
      assert (Hope: (ren_memory unscoped.shift) (sub_m i) = up_memory_memory sub_m (S i)). {
        substify. done.
      }
      rewrite <- Hope in H.

      cbn in *.
      destruct (sub_m i) eqn:Hsubi.
      - cbn in H. unfold unscoped.shift in H. lia.
      - auto.
    }
  Qed.

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
    induction ϕ.
    - iIntros (???????) "Hcl".
      rename l into τs1; rename l0 into τs2.

      unfold closure_interp0.
      iEval (cbn).
      iEval (cbn) in "Hcl".
      destruct cl; [|auto].
      destruct f as [τs1_trans τs2_trans] eqn:Hf.
      iDestruct "Hcl" as "(%Hτs1 & %Hτs2 & Hcl)".

      iSplitR; [iPureIntro| iSplitR; [iPureIntro|]].
      + admit.
      + admit.
      + admit.
    - iIntros (???????) "Hcl".
      cbn.
      iIntros (?).
      iApply IHϕ; last done.
      intros ? Hok'.

      destruct i.
      + instantiate (1:= MemMM).
        cbn. lia.
      + apply mem_ok_se_up in Hok'.
        apply Hok in Hok'.
        cbn. lia.

    - admit.
    - admit.
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
    iApply closure_interp0_subst_senv_mem; last done.
    intros i Hok_se.
    destruct i.
    - cbn. lia.
    - instantiate (1:=MemMM).
      cbn in *.
      lia.
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
