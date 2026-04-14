Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section untag.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_untag M F L wt wt' wtf wl wl' wlf es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [type_i31] [type_i32] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IUntag ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmask ψ Hok Hcg.

    cbn in Hcg; inversion Hcg; subst; clear Hcg.

    iIntros (??????????) "@@@@@@@@@@".
    iEval (rewrite values_interp_one_eq) in "Hos".
    iPoseProof (value_interp_i31 with "Hos") as "[%p %Hos]".
    subst os.
    iEval (rewrite atoms_interp_one_inv) in "Hvs".
    iDestruct "Hvs" as "[%v [-> Hvs]]".
    iEval (cbn) in "Hvs".
    iDestruct "Hvs" as "(%n & %n32 & %Hn & -> & %rp & %Hrp & Hrpinterp)".

    (* need to show evs is a number *)
    apply has_values_to_consts_inv in H0.
    cbn in H0. subst evs.
    change ([?x]++[?y;?z]) with ([x;y;z]).

    iApply (cwp_binop with "[$Hfr] [$Hrun]").
    - by cbn.
    - iFrame. iModIntro.
      iSplitR; auto.
      iExists [I32A (Wasm_int.Int32.ishr_u n32 (Wasm_int.Int32.repr 1))].
      iSplitL.
      + iApply values_interp_one_eq.
        iApply value_interp_eq.
        iExists (SVALTYPE [I32R] NoRefs).
        iPureIntro.
        repeat split; auto.
        * eexists; split; auto.
          apply Forall2_cons; split; [|by apply Forall2_nil].
          by cbn.
        * eexists; split; auto.
          apply Forall_cons; split; [|by apply Forall_nil].
          by cbn.
      + cbn.
        iSplit; auto.
  Qed.

End untag.
