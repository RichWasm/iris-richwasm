Require Import RichWasm.iris.memory.
Require Import RichWasm.iris.logrel.
Require Import RichWasm.iris.util.
Require Import RichWasm.util.
From iris.proofmode Require Import base proofmode classes.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".


Section rt_token.
  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.

  Lemma rt_token_getheap lmask θ :
    rt_token rti sr lmask θ -∗
    ∃ hm,
      rt_token_phys sr θ hm ∗
      rt_token_nophys rti sr lmask θ hm.
  Proof.
    iIntros "Hrt".
    open_rt "Hrt".
    by iFrame.
  Qed.

  Lemma rt_token_putheap lmask θ hm :
    rt_token_nophys rti sr lmask θ hm -∗
    rt_token_phys sr θ hm -∗
    rt_token rti sr lmask θ.
  Proof.
    iIntros "Hnph Hph".
    iDestruct "Hnph" as "(%rm & %lm & Hnoheap)".
    iDestruct "Hph" as "(? & ? & ?)".
    iExists rm, lm, hm.
    by iFrame.
  Qed.
End rt_token.
