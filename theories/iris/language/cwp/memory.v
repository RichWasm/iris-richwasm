Require Import iris.proofmode.tactics.

From RichWasm.iris.language Require Import iris_wp_def lwp_resources.
Require Import RichWasm.iris.language.cwp.def.

Set Bullet Behavior "Strict Subproofs".

Section memory.

  Context `{!wasmG Σ}.

  Lemma cwp_load s E (f : frame) v k n i t a off L R Φ :
    types_agree t v ->
    f.(f_inst).(inst_memory) !! i = Some n ->
    N.of_nat n ↦[wms][N.add (Wasm_int.N_of_uint i32m k) off] bits v -∗
    ▷ Φ f [v] -∗
    ↪[frame] f -∗
    ↪[RUN] -∗
    CWP [BI_const (VAL_int32 k); BI_load i t None a off]
        @ s; E UNDER L; R
        {{ f; vs, Φ f vs ∗ N.of_nat n ↦[wms][N.add (Wasm_int.N_of_uint i32m k) off] bits v }}.
  Proof.
    iIntros (Htv Hi) "Hn HΦ Hf Hrun".
    iApply lenient_wp_load.
    { by apply Is_true_true. }
    { done. }
    iFrame.
    by iIntros "!> Hn".
  Qed.

  Lemma cwp_store s E (f : frame) bs v k n i t a off L R Φ :
    types_agree t v ->
    length bs = length_t t ->
    f.(f_inst).(inst_memory) !! i = Some n ->
    N.of_nat n ↦[wms][N.add (Wasm_int.N_of_uint i32m k) off] bs -∗
    ▷ Φ f [] -∗
    ↪[frame] f -∗
    ↪[RUN] -∗
    CWP [BI_const (VAL_int32 k); BI_const v; BI_store i t None a off]
        @ s; E UNDER L; R
        {{ f; vs, Φ f vs ∗ N.of_nat n ↦[wms][Wasm_int.N_of_uint i32m k + off] bits v }}.
  Proof.
    iIntros (Htv Hlen Hi) "Hn HΦ Hf Hrun".
    iApply lenient_wp_store.
    { by apply Is_true_true. }
    { done. }
    { done. }
    iFrame.
    by iIntros "!> Hn".
  Qed.

End memory.
