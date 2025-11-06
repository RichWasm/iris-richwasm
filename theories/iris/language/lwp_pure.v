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
    ▷ Φ.(lp_val) f [v] ∗
    Φ.(lp_fr_inv) f
    ⊢ lenient_wp s E [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] Φ.
  Proof.
    iIntros (Happ) "(Hf & Hrun & Hval & Hfrinv)".
    iApply (wp_wand with "[Hf Hrun Hval]").
    - iApply (wp_binop with "[$] [$]").
      eauto.
      instantiate (1:= λ v, ↪[RUN] -∗ lp_noframe Φ f v).
      iFrame.
      by iIntros "!> ?".
    - iIntros (w) "[[Hnofr Hrun] Hf]".
      iSpecialize ("Hnofr" with "Hrun").
      iFrame.
  Qed.

  Lemma lwp_unop s E Φ op t v1 v (f: datatypes.frame) :
    app_unop op v1 = v →
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) f [v] ∗
    Φ.(lp_fr_inv) f
    ⊢ lenient_wp s E [AI_basic (BI_const v1); AI_basic (BI_unop t op)] Φ.
  Proof.
    iIntros (Happ) "(Hf & Hrun & Hval & Hfrinv)".
    iApply (wp_wand with "[Hf Hrun Hval]").
    - iApply (wp_unop with "[$] [$]"); eauto.
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
    ▷ Φ.(lp_val) f [VAL_int32 (wasm_bool b)] ∗
    Φ.(lp_fr_inv) f
    ⊢ lenient_wp s E [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_relop t op)] Φ.
  Proof.
    iIntros (Happ) "(Hf & Hrun & Hval & Hfrinv)".
    iApply (wp_wand with "[Hf Hrun Hval]").
    - iApply (wp_relop with "[$] [$]").
      eauto.
      instantiate (1:= λ v, ↪[RUN] -∗ lp_noframe Φ f v).
      iFrame.
      by iIntros "!> ?".
    - iIntros (w) "[[Hnofr Hrun] Hf]".
      iSpecialize ("Hnofr" with "Hrun").
      iFrame.
  Qed.

  Lemma lwp_testop_i32 s E Φ op v b (f: datatypes.frame) :
    app_testop_i (e:=i32t) op v = b →
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) f [VAL_int32 (wasm_bool b)] ∗
    Φ.(lp_fr_inv) f
    ⊢ lenient_wp s E [AI_basic (BI_const (VAL_int32 v)); AI_basic (BI_testop T_i32 op)] Φ.
  Proof.
    iIntros (Happ) "(Hf & Hrun & Hval & Hfrinv)".
    iApply (wp_wand with "[Hf Hrun Hval]").
    - iApply (wp_testop_i32 with "[$] [$]").
      eauto.
      instantiate (1:= λ v, ↪[RUN] -∗ lp_noframe Φ f v).
      iFrame.
      by iIntros "!> ?".
    - iIntros (w) "[[Hnofr Hrun] Hf]".
      iSpecialize ("Hnofr" with "Hrun").
      iFrame.
  Qed.

  Lemma lwp_testop_i64 s E Φ op v b (f: datatypes.frame) :
    app_testop_i (e:=i64t) op v = b →
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) f [VAL_int32 (wasm_bool b)] ∗
    Φ.(lp_fr_inv) f
    ⊢ lenient_wp s E [AI_basic (BI_const (VAL_int64 v)); AI_basic (BI_testop T_i64 op)] Φ.
  Proof.
    iIntros (Happ) "(Hf & Hrun & Hval & Hfrinv)".
    iApply (wp_wand with "[Hf Hrun Hval]").
    - iApply (wp_testop_i64 with "[$] [$]").
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
      ▷ Φ.(lp_val) f [] -∗
      Φ.(lp_fr_inv) f -∗
      lenient_wp s E [AI_basic BI_nop] Φ.
  Proof.
    iIntros "HR Hf HΦ Hfrinv".
    iApply (wp_wand with "[HR HΦ Hf]").
    iApply (wp_nop with "[$] [$]").
    - instantiate (1 := λ v, ↪[RUN] -∗ lp_noframe Φ f v).
      iFrame.
      by iIntros "!> ?".
    - iIntros (w) "[[Hnof HR] Hf]".
      iSpecialize ("Hnof" with "HR").
      iFrame.
  Qed.

End lwp_pure.
