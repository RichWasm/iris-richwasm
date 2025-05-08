From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From Wasm.iris.logrel Require Export iris_fundamental.
From Wasm.iris.rules Require Export proofmode.

Definition mem_block_at_pos_frac `{!wasmG Σ} (q: dfrac) (n: N) (l:bytes) k : iProp Σ :=
  ([∗ list] i ↦ b ∈ l, n ↦[wm]{q} [ (N.of_nat (N.to_nat k+i)) ] b)%I.
Locate "↦[wms][".

Notation "n ↦[wms]{ q } [ i ] l" := (mem_block_at_pos_frac q n l i)                    
                                      (at level 20, q at level 5, format "n ↦[wms]{ q } [ i ] l"): bi_scope.

Section memrsc.
Context `{!wasmG Σ}. 

Lemma mem_block_at_frac_one n i l :
  n ↦[wms]{DfracOwn 1}[i] l ⊢ n ↦[wms][i] l.
Proof.
  iIntros.
  iFrame.
Qed.
    

Lemma mem_block_at_frac_combine n p q i l l' :
  n ↦[wms]{p}[i] l ∗ n ↦[wms]{q}[i] l' ⊢ n ↦[wms]{p ⋅ q}[i] l ∗ ⌜l = l'⌝.
Proof.
Admitted.

Lemma mem_block_at_frac_split n p q i l :
  n ↦[wms]{p ⋅ q}[i] l ⊢
  n ↦[wms]{p}[i] l ∗ n ↦[wms]{q}[i] l.
Proof.
Admitted.

Lemma mem_block_at_frac_halve n i l :
  n ↦[wms][i] l ⊢
  n ↦[wms]{DfracOwn (1/2)}[i] l ∗ n ↦[wms]{DfracOwn (1/2)}[i] l.
Proof.
  iIntros "H".
  iApply mem_block_at_frac_split.
  rewrite dfrac_op_own.
  rewrite Qp.half_half.
  iFrame.
Qed.


Definition own_vec (memidx: N) (base_addr: N) (sz: N) : iProp Σ :=
  ∃ bs: bytes, ⌜N.of_nat (length bs) = sz⌝ ∗ memidx ↦[wms][base_addr] bs.

Definition own_half_vec (memidx: N) (base_addr: N) (sz: N) : iProp Σ :=
  ∃ bs: bytes, ⌜N.of_nat (length bs) = sz⌝ ∗ memidx ↦[wms]{DfracOwn (1/2)}[base_addr] bs.

Lemma own_half_vec_split memidx base_addr sz:
  own_half_vec memidx base_addr sz ∗ own_half_vec memidx base_addr sz ⊣⊢ own_vec memidx base_addr sz.
Proof.
  iSplit.
  - iIntros "[[%b [%len H]] [%b' [%len' H']]]".
    iPoseProof (mem_block_at_frac_combine with "[$]") as "[Hcomb %Hbeq]".
    subst b'.
    rewrite dfrac_op_own.
    rewrite Qp.half_half.
    iExists b.
    by iFrame.
  - iIntros "(%b & %bsz & H)".
    iPoseProof (mem_block_at_frac_halve with "[$]") as "[Hp Hq]".
    by iFrame.
Qed.
End memrsc.
