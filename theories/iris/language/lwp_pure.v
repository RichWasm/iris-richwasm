From RichWasm.iris.rules Require Import iris_rules_pure iris_rules_trap.
From RichWasm.iris.language Require Import iris_wp_def logpred lenient_wp.
Import iris.algebra.list.
From iris.proofmode Require Import base tactics classes.
Set Bullet Behavior "Strict Subproofs".

Section lwp_pure.
  Context `{!wasmG Σ}.
  Open Scope bi_scope.
  
  Lemma lwp_binop s E Φ op t v1 v2 v (f: datatypes.frame) :
    app_binop op v1 v2 = Some v →
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) [v] ∗
    Φ.(lp_fr) f
    ⊢ lenient_wp s E [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] (lp_run Φ).
  Proof.
    iIntros (Happ) "(Hf & Hrun & Hval & Hfr)".
    iApply (wp_wand with "[Hf Hrun Hval]").
    - iApply (wp_binop with "[$] [$]").
      eauto.
      by instantiate (1:= lp_noframe Φ).
    - iIntros (w) "[[Hnofr Hrun] Hf]".
      unfold lp_run.
      rewrite -lp_with_sep.
      iFrame.
  Qed.

  Lemma lwp_relop s E Φ op t v1 v2 b (f: datatypes.frame) :
    app_relop op v1 v2 = b →
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) [VAL_int32 (wasm_bool b)] ∗
    Φ.(lp_fr) f
    ⊢ lenient_wp s E [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_relop t op)] (lp_run Φ).
  Proof.
    iIntros (Happ) "(Hf & Hrun & Hval & Hfr)".
    iApply (wp_wand with "[Hf Hrun Hval]").
    - iApply (wp_relop with "[$] [$]").
      eauto.
      by instantiate (1:= lp_noframe Φ).
    - iIntros (w) "[[Hnofr Hrun] Hf]".
      unfold lp_run.
      rewrite -lp_with_sep.
      iFrame.
  Qed.

End lwp_pure.
