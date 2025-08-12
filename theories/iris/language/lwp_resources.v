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

  Check wp_set_local.

  Definition lp_fr_set f i v (Φ : @logpred Σ) : logpred :=
    {|
      lp_fr := λ f', ⌜f' = {| f_locs := seq.set_nth v (f_locs f) i v; f_inst := f_inst f |}⌝;
      lp_val := lp_val Φ;
      lp_trap := lp_trap Φ;
      lp_br := lp_br Φ;
      lp_ret := lp_ret Φ;
      lp_host := lp_host Φ;
    |}.

  Definition lp_run Φ :=
    {|
      lp_fr := lp_fr Φ;
      lp_val := λ vs, lp_val Φ vs ∗ ↪[RUN];
      lp_trap := lp_trap Φ;
      lp_br := λ x, lp_br Φ x ∗ ↪[RUN];
      lp_ret := λ x, lp_ret Φ x ∗ ↪[RUN];
      lp_host := λ ft hf vs lh, lp_host Φ ft hf vs lh ∗ ↪[RUN];
    |}.

  Lemma lp_run_sep Φ w :
    denote_logpred Φ w ∗ ↪[RUN] ⊢ denote_logpred (lp_run Φ) w.
  Proof.
    unfold lp_run, denote_logpred.
    cbn.
    destruct w; cbn; iIntros "[HΦ Hrun]"; iFrame.
  Qed.

  Lemma lenient_wp_set_local s E i Φ v (f: datatypes.frame) :
    i < length f.(f_locs) ->
    ▷ Φ.(lp_val) [] ∗
    ↪[frame] f ∗
    ↪[RUN]
    ⊢ lenient_wp s E [AI_basic (BI_const v); AI_basic (BI_set_local i)] (lp_run (lp_fr_set f i v Φ)).
  Proof.
    iIntros (Hlen) "(Hval & Hf & Hrun)".
    iApply (wp_wand with "[Hval Hf Hrun]").
    iApply (wp_set_local with "[Hval] [$Hf] [$Hrun]").
    - assumption.
    - instantiate (1:= lp_noframe (lp_fr_set f i v Φ)).
      by cbn.
    - iIntros (w) "((Hpred & Hrun) & Hf)".
      iApply lp_run_sep.
      by iFrame.
  Qed.

End lwp_resources.
