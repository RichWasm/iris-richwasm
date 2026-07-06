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
        (pose proof (has_kind_ft_function_type_eq_mod_kinds rti sr mr) as (_ & H10);
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
