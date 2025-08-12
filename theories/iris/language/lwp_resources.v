From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
Import iris.algebra.list.
From RWasm.iris.rules Require Import iris_rules_resources.
From RWasm.iris.language Require Import iris_wp_def logpred lenient_wp.

Set Bullet Behavior "Strict Subproofs".

Section lwp_resources.
  Context `{!wasmG Σ}.
  Open Scope bi_scope.

Locate Wasm.iris.language.iris.iris.val.
Locate iris.val.
Locate Wasm.iris.language.iris.iris.val.

  Lemma lenient_wp_get_local s E (v: value) i Φ f :
    (f_locs f) !! i = Some v ->
    ▷Φ.(lp_val) [v] ∗
    ▷Φ.(lp_fr) f ∗
    ↪[frame] f ∗
    ↪[RUN]
    ⊢ lenient_wp s E [AI_basic (BI_get_local i)] Φ.
  Proof.
    iIntros "%Hi (Hval & Hfr & Hf & Hrun)".
    unfold lenient_wp.
    iApply (wp_wand with "[Hfr Hf Hrun Hval]").
    iApply (wp_get_local with "[Hfr Hval] [$] [$]").
    - by apply Hi.
    - instantiate (1:=(fun v: iris.val => (lp_noframe Φ v ∗ lp_fr Φ f)%I)).
      iFrame.
    - iIntros (v0) "[[Hq Hrun] Hf]".
      unfold denote_logpred.
      iFrame.
  Qed.

End lwp_resources.
