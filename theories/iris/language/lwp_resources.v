From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
Import iris.algebra.list.
From RichWasm.iris.rules Require Import iris_rules_resources.
From RichWasm.iris.language Require Import iris_wp_def logpred lenient_wp.

Set Bullet Behavior "Strict Subproofs".

Section lwp_resources.
  Context `{!wasmG Σ}.
  Open Scope bi_scope.

  Lemma lenient_wp_get_local s E (v: value) i Φ f :
    (f_locs f) !! i = Some v ->
    ▷ Φ.(lp_val) f [v] ∗
    Φ.(lp_fr_inv) f ∗
    ↪[frame] f ∗
    ↪[RUN]
    ⊢ lenient_wp s E [AI_basic (BI_get_local i)] Φ.
  Proof.
    iIntros "%Hi (Hval & Hfrinv & Hf & Hrun)".
    unfold lenient_wp.
    iApply (wp_wand with "[Hf Hrun Hval]").
    iApply (wp_get_local with "[Hval] [$] [$]").
    - by apply Hi.
    - instantiate (1:= (λ v, ↪[RUN] -∗ lp_noframe Φ f v)).
      iIntros "!> ?"; iFrame.
    - iIntros (v0) "[[Hq Hrun] Hf]".
      unfold denote_logpred.
      iFrame.
      by iApply "Hq".
  Qed.

  Lemma lenient_wp_set_local s E i Φ v (f: datatypes.frame) :
    let f' := {| f_locs := seq.set_nth v (f_locs f) i v; f_inst := f_inst f |} in
    i < length f.(f_locs) ->
    ▷ Φ.(lp_val) f' [] ∗
    Φ.(lp_fr_inv) f' ∗
    ↪[frame] f ∗
    ↪[RUN]
    ⊢ lenient_wp s E [AI_basic (BI_const v); AI_basic (BI_set_local i)] Φ.
  Proof.
    iIntros (f' Hlen) "(Hval & Hfrinv & Hf & Hrun)".
    iApply (wp_wand with "[Hval Hf Hrun]").
    iApply (wp_set_local with "[Hval] [$Hf] [$Hrun]").
    - assumption.
    - instantiate (1:= (λ v, ↪[RUN] -∗ lp_noframe Φ f' v)).
      iIntros "!> ?"; iFrame.
    - iIntros (w) "((Hpred & Hrun) & Hf)".
      iSpecialize ("Hpred" with "Hrun").
      iFrame.
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
    ↪[RUN] ∗
    R ∗
    ▷ (R -∗ Φ.(lp_val) f [v]) ∗
    Φ.(lp_fr_inv) f ∗
    ↪[frame] f
    ⊢ lenient_wp s E [AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_load i t None a off)]
                     Φ.
  Proof.
    iIntros (R Hag Hmem) "(Hrun & HR & Hval & Hfrinv & Hf)".
    iApply (wp_wand with "[Hrun HR Hval Hf]").
    iApply wp_load; eauto.
    - iFrame.
      instantiate (1:= (λ v, ↪[RUN] -∗ R -∗ lp_noframe Φ f v)).
      cbn.
      iIntros "!> ?"; iFrame.
    - iIntros (v0) "[(Hnoframe & HR & Hrun) Hf]".
      iSpecialize ("Hnoframe" with "Hrun").
      iFrame.
      by iApply "Hnoframe".
  Qed.

  Theorem lenient_wp_store Φ s E t bs v off a k n f i :
    let R := N.of_nat n↦[wms][Wasm_int.N_of_uint i32m k + off] bs in
    let R' := N.of_nat n↦[wms][Wasm_int.N_of_uint i32m k + off]bits v in
    is_true (types_agree t v) ->
    length bs = length_t t ->
    inst_memory (f_inst f) !! i = Some n ->
    R ∗
    ↪[RUN] ∗
    ▷ (R' -∗ Φ.(lp_val) f []) ∗
    Φ.(lp_fr_inv) f ∗
    ↪[frame] f
    ⊢ lenient_wp s E [AI_basic (BI_const (VAL_int32 k));
                      AI_basic (BI_const v);
                      AI_basic (BI_store i t None a off)]
                     Φ.
  Proof.
    iIntros (R R' Hag Hlen Hmem) "(HR & Hrun & Hval & Hfrinv & Hf)".
    iApply (wp_wand with "[HR Hrun Hval Hf]").
    - iApply wp_store; eauto.
      iFrame.
      instantiate (1:= (λ v, ↪[RUN] -∗ R' -∗ lp_noframe Φ f v)).
      cbn.
      iIntros "!> ?"; iFrame.
    - iIntros (v0) "[[Hnoframe [Hptr Hrun]] Hf]".
      iFrame.
      iApply ("Hnoframe" with "[$] [$]").
  Qed.

End lwp_resources.
