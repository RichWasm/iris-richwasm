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

  Lemma compat_nop M F L n_skip wt wt' wtf wl wl' wlf es' :
    let fe := fe_of_context F <| fe_br_skip := n_skip |> in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [] [] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (INop ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Proof.
    (* This is currently following the compat_copy lemma very closely *)
    intros fe WT WL ψ Hok Hcompile.
    inv_cg_emit Hcompile; subst.
    unfold have_instruction_type_sem.
    destruct ψ eqn:Hψ.
    inversion Hψ; subst l l0.
    iIntros (? ? ? ? ? ? ? ?) "Hinst Hctx Hrvs Hvs Hframe Hrt Hf Hrun".
    unfold expr_interp.
    iEval (cbn) in "Hrvs"; iEval (cbn) in "Hvs".
    iDestruct "Hvs" as "(%rvss & %Hconcat & Hrvss)".
    iPoseProof (big_sepL2_length with "[$Hrvss]") as "%Hlens_rvss".
    iPoseProof (big_sepL2_length with "[$Hrvs]") as "%Hlens_rvs_vs".
    cbn in Hlens_rvss.
    destruct rvss, os; cbn in Hconcat, Hlens_rvss; try congruence.
    cbn in Hlens_rvs_vs. destruct vs; cbn in Hlens_rvs_vs; try congruence.
    iApply (lenient_wp_nop with "[$] [$] [Hframe Hrt] []").
    - iModIntro.
      iFrame.
      iExists []; cbn.
      iSplitR; [|done].
      iExists []; auto.
    - done.
  Qed.

End Fundamental.
