From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
Import iris.algebra.list.
From RWasm.iris.rules Require Import iris_rules_resources.
From RWasm.iris.language Require Import iris_wp_def logpred lenient_wp.

Set Bullet Behavior "Strict Subproofs".

Section lwp_resources.
  Context `{!wasmG Σ}.
  Open Scope bi_scope.

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
      iApply lp_with_sep.
      by iFrame.
  Qed.

  Theorem lenient_wp_tee_local s E i Φ v (f: datatypes.frame) :
    i < length f.(f_locs) ->
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ (↪[frame] f -∗
        ↪[RUN] -∗
        lenient_wp s E [AI_basic (BI_const v); AI_basic (BI_const v); AI_basic (BI_set_local i)] Φ)
    ⊢ lenient_wp s E [AI_basic (BI_const v); AI_basic (BI_tee_local i)] Φ.
  Proof.
    iIntros (Hlocs) "(Hf & Hr & Hwp)".
    iApply (wp_tee_local with "[$] [$] [$]").
  Qed.

  Theorem lenient_wp_load Φ s E t v off a k n f i : 
    let R := N.of_nat n ↦[wms][Wasm_int.N_of_uint i32m k + off] bits v in
    is_true (types_agree t v) ->
    inst_memory (f_inst f) !! i = Some n ->
    R ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) [v] ∗
    Φ.(lp_fr) f ∗
    ↪[frame] f
    ⊢ lenient_wp s E [AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_load i t None a off)]
                     (lp_with (R ∗ ↪[RUN]) Φ).
  Proof.
    iIntros (R Hag Hmem) "(Hwp & Hrun & Hval & Hfr & Hf)".
    iApply (wp_wand with "[Hwp Hrun Hval Hfr Hf]").
    iApply wp_load; eauto.
    - iFrame.
      instantiate (1:=(fun v: iris.val => (lp_noframe Φ v ∗ lp_fr Φ f)%I)).
      iFrame.
    - iIntros (v0) "[[[Hnoframe Hfr] [HR Hrun]] Hf]".
      rewrite -lp_with_sep.
      iFrame.
  Qed.

  Theorem lenient_wp_store Φ s E t bs v off a k n f i :
    is_true (types_agree t v) ->
    length bs = length_t t ->
    inst_memory (f_inst f) !! i = Some n ->
    N.of_nat n↦[wms][Wasm_int.N_of_uint i32m k + off] bs ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) [] ∗
    Φ.(lp_fr) f ∗
    ↪[frame] f
    ⊢ lenient_wp s E [AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_const v); AI_basic (BI_store i t None a off)]
                     (lp_with (N.of_nat n↦[wms][Wasm_int.N_of_uint i32m k + off]bits v ∗ ↪[RUN]) Φ).
  Proof.
    iIntros (Hag Hlen Hmem) "(Hptr & Hrun & Hval & Hfr & Hf)".
    iApply (wp_wand with "[Hptr Hrun Hval Hf]").
    - iFrame.
      iApply wp_store; eauto.
      instantiate (1:=(fun v: iris.val => lp_noframe Φ v)).
      iFrame.
    - iIntros (v0) "[[Hnofram [Hptr Hrun]] Hf]".
      rewrite -lp_with_sep.
      iFrame.
  Qed.

End lwp_resources.
