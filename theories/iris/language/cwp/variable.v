Require Import RecordUpdate.RecordUpdate.

Require Import iris.proofmode.tactics.

Require Import RichWasm.iris.language.lwp_resources.
Require Import RichWasm.iris.language.cwp.def.
Require Import RichWasm.iris.rules.iris_rules_resources.

Set Bullet Behavior "Strict Subproofs".

Section variable.

  Context `{!wasmG Σ}.

  Lemma cwp_local_get s E (f : frame) v i L R Φ :
    f.(f_locs) !! i = Some v ->
    ▷ Φ f [v] -∗
    ↪[frame] f -∗
    ↪[RUN] -∗
    CWP [BI_get_local i] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hi) "HΦ Hf Hrun".
    iApply lenient_wp_get_local; first done.
    iFrame.
  Qed.

  Lemma cwp_local_set s E (f : frame) i v L R Φ :
    i < length f.(f_locs) ->
    let f' := Build_frame (<[ i := v ]> f.(f_locs)) f.(f_inst) in
    ▷ Φ f' [] -∗
    ↪[frame] f -∗
    ↪[RUN] -∗
    CWP [BI_const v; BI_set_local i] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hi f') "HΦ Hf Hrun".
    iApply lenient_wp_set_local; first done.
    rewrite <- fmap_insert_set_nth; last done.
    iFrame.
  Qed.

  Lemma cwp_local_tee s E (f : frame) i v L R Φ :
    i < length f.(f_locs) ->
    ↪[frame] f -∗
    ↪[RUN] -∗
    ▷ (↪[frame] f -∗ ↪[RUN] -∗
       CWP [BI_const v; BI_const v; BI_set_local i] @ s; E UNDER L; R {{ Φ }}) -∗
    CWP [BI_const v; BI_tee_local i] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hi) "Hf Hrun Hset".
    iApply lenient_wp_tee_local; first done.
    iFrame.
  Qed.

  Lemma cwp_global_get s E (f : frame) i j v g L R Φ :
    f.(f_inst).(inst_globs) !! i = Some j ->
    g.(g_val) = v ->
    N.of_nat j ↦[wg] g -∗
    ▷ Φ f [v] -∗
    ↪[frame] f -∗
    ↪[RUN] -∗
    CWP [BI_get_global i] @ s; E UNDER L; R {{ f; v, Φ f v ∗ N.of_nat j ↦[wg] g }}.
  Proof.
    iIntros (Hi Hv) "Hj HΦ Hf Hrun".
    iApply (wp_wand with "[Hj HΦ Hf Hrun]").
    - iApply (wp_get_global with "[HΦ] [$] [$] [$]").
      1, 2: done.
      instantiate (1 := fun v' => (⌜v' = immV [v]⌝ ∗ Φ f [v])%I).
      by iFrame.
    - iIntros (v') "([-> HΦ] & Hj & Hrun & Hf)".
      iFrame.
  Qed.

  Lemma cwp_global_set s E (f : frame) g i j v L R Φ :
    f.(f_inst).(inst_globs) !! i = Some j ->
    N.of_nat j ↦[wg] g -∗
    ▷ Φ f [] -∗
    ↪[frame] f -∗
    ↪[RUN] -∗
    CWP [BI_const v; BI_set_global i] @ s; E UNDER L; R
        {{ f; v', Φ f v' ∗ N.of_nat j ↦[wg] Build_global g.(g_mut) v }}.
  Proof.
    iIntros (Hi) "Hj HΦ Hf Hrun".
    iApply (wp_wand with "[Hj HΦ Hf Hrun]").
    - iApply (wp_set_global with "[HΦ] [$] [$] [$]"); first done.
      instantiate (1 := fun v => (⌜v = immV []⌝ ∗ Φ f [])%I).
      by iFrame.
    - iIntros (v') "([-> HΦ] & Hj & Hrun & Hf)".
      iFrame.
  Qed.

End variable.
