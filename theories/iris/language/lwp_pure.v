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
    Φ.(lp_fr) f ∗
    Φ.(lp_fr_inv) f
    ⊢ lenient_wp s E [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] Φ.
  Proof.
    iIntros (Happ) "(Hf & Hrun & Hval & Hfr & Hfrinv)".
    iApply (wp_wand with "[Hf Hfr Hrun Hval]").
    - iApply (wp_binop with "[$] [$]").
      eauto.
      instantiate (1:= λ v, ↪[RUN] -∗ lp_noframe Φ f v).
      iFrame.
      by iIntros "!> ?".
    - iIntros (w) "[[Hnofr Hrun] Hf]".
      iSpecialize ("Hnofr" with "Hrun").
      iFrame.
  Qed.

  Lemma lwp_relop s E Φ op t v1 v2 b (f: datatypes.frame) :
    app_relop op v1 v2 = b →
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) [VAL_int32 (wasm_bool b)] ∗
    Φ.(lp_fr) f ∗
    Φ.(lp_fr_inv) f
    ⊢ lenient_wp s E [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_relop t op)] Φ.
  Proof.
    iIntros (Happ) "(Hf & Hrun & Hval & Hfr & Hfrinv)".
    iApply (wp_wand with "[Hf Hrun Hval Hfr]").
    - iApply (wp_relop with "[$] [$]").
      eauto.
      instantiate (1:= λ v, ↪[RUN] -∗ lp_noframe Φ f v).
      iFrame.
      by iIntros "!> ?".
    - iIntros (w) "[[Hnofr Hrun] Hf]".
      iSpecialize ("Hnofr" with "Hrun").
      iFrame.
  Qed.

  Lemma lenient_wp_nop s E Φ f :
    ⊢ ↪[RUN] -∗
      ↪[frame] f -∗
      ▷ Φ.(lp_fr) f -∗
      Φ.(lp_fr_inv) f -∗
      ▷ Φ.(lp_val) [] -∗
      lenient_wp s E [AI_basic BI_nop] Φ.
  Proof.
    iIntros "HR Hf Hfr Hfrinv HΦ".
    iApply (wp_wand with "[HR HΦ Hf Hfr]").
    iApply (wp_nop with "[$] [$]").
    - instantiate (1 := λ v, ↪[RUN] -∗ lp_noframe Φ f v).
      iFrame.
      by iIntros "!> ?".
    - iIntros (w) "[[Hnof HR] Hf]".
      iSpecialize ("Hnof" with "HR").
      iFrame.
  Qed.

End lwp_pure.
