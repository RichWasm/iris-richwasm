Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section num_const.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_num_const M F L wt wt' wtf wl wl' wlf n ν es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [] [num_type_type ν] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (INumConst ψ n)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmask ψ Hok Hcg.
    destruct ν; cbn in Hcg; inversion Hcg; subst; clear Hcg.

    all: iIntros (??????????) "@@@@@@@@@@".
    all: iPoseProof (values_interp_nil_l with "Hos") as "->".
    all: iPoseProof (atoms_interp_nil_l with "Hvs") as "->".
    all: apply has_values_to_consts_inv in H0; subst evs.
    all: change (to_consts []) with ([]:(list basic_instruction)).
    all: clear_nils.

    all: iApply (cwp_val with "[$Hfr] [$Hrun]").
    1: instantiate (1 := ([value_of_Z (translate_num_type (IntT i)) n])%I).
    3: instantiate (1 := ([value_of_Z (translate_num_type (FloatT f)) n])%I).

    1,3: apply has_values_iff_to_consts; auto.

    all: iFrame.
    all: iSplitR; auto.
    1: destruct i.
    3: destruct f.
    all: iEval (cbn).
    1: iExists [I32A (Wasm_int.Int32.repr n)].
    2: iExists [I64A (Wasm_int.Int64.repr n)].
    3: iExists [F32A (Wasm_float.FloatSize32.of_bits (Integers.Int.repr n))].
    4: iExists [F64A (Wasm_float.FloatSize64.of_bits (Integers.Int64.repr n))].
    all: iEval (cbn).
    all: iSplitL; try iSplitL; auto.
    1: iExists [[I32A (Wasm_int.Int32.repr n)]].
    2: iExists [[I64A (Wasm_int.Int64.repr n)]].
    3: iExists [[F32A (Wasm_float.FloatSize32.of_bits (Integers.Int.repr n))]].
    4: iExists [[F64A (Wasm_float.FloatSize64.of_bits (Integers.Int64.repr n))]].
    all: iEval (cbn); iSplitR; auto; iSplitL; auto.
    all: iApply value_interp_eq; iEval (cbn).
    all: iExists _.
    all: iSplitR; auto; iSplitL; auto; iEval (cbn).
    all: iPureIntro.
    all: split;
      [ eexists; split; auto; apply Forall2_cons; split;[|by apply Forall2_nil]; by cbn
      | eexists; split; auto; apply Forall_cons; split;[|by apply Forall_nil]; by cbn].

  Qed.

End num_const.
