From RichWasm.iris.rules Require Import iris_rules_trap.
From RichWasm.iris.language Require Import iris_wp_def logpred lenient_wp.
Import iris.algebra.list.
From iris.proofmode Require Import base tactics classes.
Set Bullet Behavior "Strict Subproofs".

Section lwp_trap.
  Context `{!wasmG Σ}.
  Open Scope bi_scope.

  Lemma lwp_trap s E vs es Φ f: 
    is_true (const_list vs) ->
    ⊢ Φ.(lp_trap) -∗
      Φ.(lp_fr_inv) f -∗
      ↪[frame] f -∗
      ↪[BAIL] -∗
      lenient_wp s E (vs ++ [AI_trap] ++ es) Φ.
  Proof.
    iIntros (Hvs) "Htrap Hfr Hf Hbail".
    iApply (wp_wand with "[Htrap Hf Hbail]").
    - iApply (wp_trap_frame with "[Htrap Hbail] [$]"); auto.
      instantiate (1:= lp_noframe Φ).
      iFrame.
    - iIntros (w) "(Hnof & Hf)".
      iFrame.
  Qed.

End lwp_trap.
