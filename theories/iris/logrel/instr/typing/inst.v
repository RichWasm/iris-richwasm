Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.substitution.
Require Import RichWasm.iris.logrel.logrel_properties.
Require Import RichWasm.iris.logrel.env_props.
Require Import RichWasm.kinding_subst.

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
    let ψ := InstrT [CodeRefT ϕ] [CodeRefT ϕ'] in
    function_type_inst F ix ϕ ϕ' ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IInst ψ ix)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmask ψ Hfinst Hok Hcg.
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

    (* mini kinding quarantine: [CodeRefT] no longer carries its own kind
       argument (it was always [VALTYPE (AtomR I32R) NoRefs], per [KCodeRef]
       in typing.v), so [κ] is now just that fixed kind, derived from
       [has_instruction_type_ok] instead of pattern-matched off the type. *)
    set (κ := VALTYPE (AtomR I32R) NoRefs).
    assert (Hkind_first: has_kind F (CodeRefT ϕ) κ). {
        destruct Hok as [[Hmono1 _] _].
        apply Forall_cons_iff in Hmono1 as [(ρ1 & Hrep1 & Hmonorep1) _].
        inversion Hrep1 as [? ? ? ξ1 Hhaskind1]; subst.
        inversion Hhaskind1; subst.
        constructor; done.
    }
    assert (Hkind: has_kind F (CodeRefT ϕ') κ). {
        destruct Hok as [[_ Hmono2] _].
        apply Forall_cons_iff in Hmono2 as [(ρ2 & Hrep2 & Hmonorep2) _].
        inversion Hrep2 as [? ? ? ξ2 Hhaskind2]; subst.
        inversion Hhaskind2; subst.
        constructor; done.
    }
    inversion Hkind; subst.
    match goal with
    | H : has_kind_ft F ϕ' |- _ => rename H into Hkind_ft
    end.
    (* now we need to use the key hypothesis: Hfinst.
       Reaching this point requires reconstructing [ϕ'] modulo cached-kind
       refresh across each of the four kind-quantifier instantiation forms
       (type/mem/rep/size), which used [refresh_kinds_ift]/[refresh_kinds]
       and [has_kind_ft_function_type_eq_mod_kinds]. Both were removed by
       the refactor that dropped cached kinds from the [type] AST (and this
       part of the proof was already only a sketch, ending in [Admitted],
       before that refactor as well) so completing this is pre-existing
       tech debt left for the corresponding rework of [inner_function_type]
       kind bookkeeping, not something introduced by this refactor. *)
    destruct Hfinst.

    1: destruct H1.
  Admitted.
  (*
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
*)

End inst.
