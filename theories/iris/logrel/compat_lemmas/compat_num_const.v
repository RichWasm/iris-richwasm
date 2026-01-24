Require Import RecordUpdate.RecordUpdate.
From stdpp Require Import base list.

From iris.proofmode Require Import base tactics classes.
From Wasm Require Import operations.

From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import prelude codegen instruction module.
From RichWasm.iris Require Import autowp memory util wp_codegen.
From RichWasm.iris.language Require Import lenient_wp lwp_pure lwp_structural lwp_resources logpred.
From RichWasm.iris.logrel Require Import relations fundamental_kinding.

Require Export shared.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Fundamental.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_num_const M F L n_skip wt wt' wtf wl wl' wlf n ν es' :
    let fe := fe_of_context F <| fe_br_skip := n_skip |> in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [] [num_type_type ν] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (INumConst ψ n)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Proof.
    intros fe WT WL ψ Hok Hcompile. cbn in Hcompile.
    (* Immediately, we must destruct ν *)
    destruct ν; cbn in Hcompile; inversion Hcompile.
    (* From here on out, we have an integer case and a float case (until we split
       further into 32/64 *)

    (* Some basic intros, unfolds, proving empty lists empty *)
    all: unfold have_instruction_type_sem.
    all: iIntros (? ? ? ? ? ? ?) "Henv Hinst Hctx Hrvs Hvs Hfr Hrt Hf Hrun".
    all: iEval (cbn) in "Hrvs"; iEval (cbn) in "Hvs".
    all: iDestruct "Hvs" as "(%rvss & %Hconcat & Hrvss)".
    all: iPoseProof (big_sepL2_length with "[$Hrvss]") as "%Hlens_rvss";
      iPoseProof (big_sepL2_length with "[$Hrvs]") as "%Hlens_rvs_vs".
    all: cbn in Hlens_rvss; destruct rvss, os; cbn in Hconcat, Hlens_rvss;
      try congruence.
    all: cbn in Hlens_rvs_vs; destruct vs; cbn in Hlens_rvs_vs; try congruence.

    (* Now it's time to apply lenient_wp *)
    all: iApply lenient_wp_value.
    (* In int case, instantiate value with int value. Float in float case *)
    (* Automatics don't work great here *)
    1: by instantiate (1 := (immV [(value_of_Z (translate_num_type (IntT i)) n)])%I).
    2: by instantiate (1 := (immV [(value_of_Z (translate_num_type (FloatT f)) n)])%I).

    all: unfold denote_logpred; iFrame; iEval (cbn).
    (* Split into 32/64 cases *)
    1: destruct i.
    3: destruct f.
    all: iEval (cbn).
    (* automatic exists don't work well here unfortunately *)
    1: iExists [I32A (Wasm_int.Int32.repr n)].
    2: iExists [I64A (Wasm_int.Int64.repr n)].
    3: iExists [F32A (Wasm_float.FloatSize32.of_bits (Integers.Int.repr n))].
    4: iExists [F64A (Wasm_float.FloatSize64.of_bits (Integers.Int64.repr n))].
    all: iEval (cbn).
    all: iSplitL; try iSplitL; auto.
    (* once again, automatic exists don't work great *)
    1: iExists [[I32A (Wasm_int.Int32.repr n)]].
    2: iExists [[I64A (Wasm_int.Int64.repr n)]].
    3: iExists [[F32A (Wasm_float.FloatSize32.of_bits (Integers.Int.repr n))]].
    4: iExists [[F64A (Wasm_float.FloatSize64.of_bits (Integers.Int64.repr n))]].
    all: iEval (cbn); iSplitR; auto; iSplitL; auto.
    (* Dig into value interp a bit, then smooth sailing *)
    all: iApply value_interp_eq; iEval (cbn).
    all: iExists _.
    all: iSplitR; auto; iSplitL; auto; iEval (cbn).
    all: iPureIntro.
    all: eexists; split; auto.
    all: apply Forall2_cons_iff.
    all: split; try (by apply Forall2_nill).
    all: done.
  Qed.

End Fundamental.
