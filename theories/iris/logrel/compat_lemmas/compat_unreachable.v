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

  Lemma compat_unreachable M F L L' wt wt' wtf wl wl' wlf ψ es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (IUnreachable ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L'.
  Proof.
    intros fe WT WL Hok Hcompile.
    inv_cg_emit Hcompile; subst.
    unfold have_instruction_type_sem.
    destruct ψ eqn:Hψ.
    iIntros (? ? ? ? ? ? ? ?) "Hinst Hctx Hrvs Hvs Hframe Hrt Hf Hrun".
    unfold expr_interp.
    iApply wp_mono.
    2: {
      iApply wp_val_app_trap_post'.
      iFrame "Hf".
      iIntros "Hf".
      iApply wp_mono.
      2: iApply (wp_unreachable with "[$] [$]").
      - iIntros (?) "[[Hv Hbail] Hframe]".
        iFrame.
        instantiate (1 := λ _, ↪[BAIL]).
        iFrame.
        auto.
      - done.
    }
    iIntros (?) "[Hbail [-> Hframe]]".
    unfold denote_logpred. simpl.
    iFrame.
  Qed.

End Fundamental.
