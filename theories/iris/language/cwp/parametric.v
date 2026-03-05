Require Import iris.proofmode.tactics.

Require Import RichWasm.iris.language.iris_wp_def.
Require Import RichWasm.iris.language.cwp.def.
Require Import RichWasm.iris.rules.iris_rules_pure.

Set Bullet Behavior "Strict Subproofs".

Section parametric.

  Context `{!wasmG Σ}.

  Lemma cwp_drop s E (f : frame) v L R Φ :
    ↪[frame] f -∗
    ↪[RUN] -∗
    ▷ Φ f [] -∗
    CWP [BI_const v; BI_drop] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros "Hf Hrun HΦ".
    iApply (wp_wand with "[HΦ Hf Hrun]").
    - iApply (wp_drop with "[$] [$]").
      instantiate (1 := fun v => (⌜v = immV []⌝ ∗ Φ f [])%I).
      by iFrame.
    - iIntros (v') "[[[-> HΦ] Hrun] Hf]". iFrame.
  Qed.

  Lemma cwp_select_nonzero s E (f : frame) v1 v2 c L R Φ :
    c <> Wasm_int.int_zero i32m ->
    ↪[frame] f -∗
    ↪[RUN] -∗
    ▷ Φ f [v1] -∗
    CWP [BI_const v1; BI_const v2; BI_const (VAL_int32 c); BI_select] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hc) "Hf Hrun HΦ".
    iApply (wp_wand with "[HΦ Hf Hrun]").
    - iApply (wp_select_true with "[$] [$]"); first done.
      instantiate (1 := fun v => (⌜v = immV [v1]⌝ ∗ Φ f [v1])%I).
      by iFrame.
    - iIntros (v') "[[[-> HΦ] Hrun] Hf]". iFrame.
  Qed.

  Lemma cwp_select_zero s E (f : frame) v1 v2 c L R Φ :
    c = Wasm_int.int_zero i32m ->
    ↪[frame] f -∗
    ↪[RUN] -∗
    ▷ Φ f [v2] -∗
    CWP [BI_const v1; BI_const v2; BI_const (VAL_int32 c); BI_select] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hc) "Hf Hrun HΦ".
    iApply (wp_wand with "[HΦ Hf Hrun]").
    - iApply (wp_select_false with "[$] [$]"); first done.
      instantiate (1 := fun v => (⌜v = immV [v2]⌝ ∗ Φ f [v2])%I).
      by iFrame.
    - iIntros (v') "[[[-> HΦ] Hrun] Hf]". iFrame.
  Qed.

End parametric.
