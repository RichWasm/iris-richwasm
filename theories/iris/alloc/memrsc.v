From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From Wasm.iris.logrel Require Export iris_fundamental.
From Wasm.iris.rules Require Export proofmode.
Require Import RichWasm.iris.util.

Section memrsc.
Context `{!wasmG Σ}. 

Definition own_vec (memidx: N) (base_addr: N) (sz: N) : iProp Σ :=
  ∃ bs: bytes, ⌜N.of_nat (length bs) = sz⌝ ∗ memidx ↦[wms][base_addr] bs.

Lemma own_vec_split memidx ℓ sz1 sz2 :
  own_vec memidx ℓ (sz1 + sz2) ⊣⊢ own_vec memidx ℓ sz1 ∗ own_vec memidx (ℓ + sz1) sz2.
Proof.
  unfold own_vec.
  iSplit.
  - iIntros "(%bs & %Hlen & Hbs)".
    pose proof (take_drop (N.to_nat sz1) bs) as Hsplit.
    rewrite <- Hsplit.
    rewrite wms_app; [|eauto; lia].
    iDestruct "Hbs" as "(Hbs1 & Hbs2)".
    iSplitL "Hbs1".
    + iExists _; iFrame.
      iPureIntro.
      rewrite length_take_le; lia.
    + rewrite length_take_le; [|lia].
      rewrite N2Nat.id.
      iExists _; iFrame.
      iPureIntro.
      rewrite length_drop.
      lia.
  - iIntros "((%bs1 & (%Hlen1 & Hbs1)) & (%bs2 & (%Hlen2 & Hbs2)))".
    iExists (bs1 ++ bs2).
    erewrite (wms_app _ _ _ (sz1:=sz1)); [| lia].
    iFrame.
    iPureIntro.
    rewrite length_app.
    lia.
Qed.

Lemma repeat_own_vec (memidx: N) (addr: N) b (k: N) :
  memidx ↦[wms][addr] (repeat b (N.to_nat k)) ⊢
  own_vec memidx addr k.
Proof.
  iIntros.
  iExists (repeat b (N.to_nat k)).
  iFrame.
  iPureIntro.
  by rewrite length_repeat N2Nat.id.
Qed.

Class allocG Σ := {
  (* maps locs returned by malloc to their size *)
  allocG_shapeG :: ghost_mapG Σ N N;
  allocG_shape : gname
}.

End memrsc.

(* Authoritative shape map *)
Notation "↪[toks] m" := (ghost_map_auth allocG_shape 1%Qp m)%I
  (at level 20, format "↪[toks] m") : bi_scope.

(* Atomic fragments of the shape map *)
Notation "n ↦[tok]{ dq } sz" := (n ↪[allocG_shape]{dq} sz)%I
  (at level 20, format "n ↦[tok]{ dq } sz") : bi_scope.
Notation "n ↦[tok] sz" := (n ↪[allocG_shape]{(DfracOwn 1)} sz)%I
  (at level 20, format "n ↦[tok] sz") : bi_scope.
