Require Import iris.proofmode.tactics.

From RichWasm Require Import numerics.
From RichWasm.iris.language Require Import iris_wp_def lwp_resources.
Require Import RichWasm.iris.language.cwp.def.

Set Bullet Behavior "Strict Subproofs".

Section memory.

  Context `{!wasmG Σ}.

  Lemma cwp_load s E f v k32 k n nN i t a off L R Φ :
    types_agree t v ->
    N_i32_repr k k32 ->
    N_nat_repr n nN ->
    f.(f_inst).(inst_memory) !! i = Some n ->
    nN ↦[wms][k + off] bits v -∗
    ▷ (nN ↦[wms][k + off] bits v -∗ Φ f [v]) -∗
    ↪[frame] f -∗
    ↪[RUN] -∗
    CWP [BI_const (VAL_int32 k32); BI_load i t None a off]
        @ s; E UNDER L; R
        {{ f; vs, Φ f vs }}.
  Proof.
    iIntros (Htv Hrep Hn Hi) "Hn HΦ Hf Hrun".
    iApply lenient_wp_load.
    { by apply Is_true_true. }
    { done. }
    erewrite N_i32_repr_N_of_uint by eauto.
    rewrite Hn.
    iFrame.
  Qed.

  Lemma cwp_store s E f bs v k k32 nN n i t a off L R Φ :
    types_agree t v ->
    N_i32_repr k k32 ->
    N_nat_repr n nN ->
    length bs = length_t t ->
    f.(f_inst).(inst_memory) !! i = Some n ->
    nN ↦[wms][k + off] bs -∗
    ▷ (nN ↦[wms][k + off] bits v -∗ Φ f []) -∗
    ↪[frame] f -∗
    ↪[RUN] -∗
    CWP [BI_const (VAL_int32 k32); BI_const v; BI_store i t None a off]
        @ s; E UNDER L; R
        {{ f; vs, Φ f vs }}.
  Proof.
    iIntros (Htv Hrep Hn Hlen Hi) "Hn HΦ Hf Hrun".
    iApply lenient_wp_store.
    { by apply Is_true_true. }
    { done. }
    { done. }
    erewrite N_i32_repr_N_of_uint by eauto.
    rewrite Hn.
    iFrame.
  Qed.

End memory.
