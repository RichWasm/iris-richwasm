From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From Wasm.iris.logrel Require Export iris_fundamental.
From Wasm.iris.rules Require Export proofmode.
From RichWasm.iris.alloc Require Export util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Section misc.

  Context `{!wasmG Σ}.

  Lemma wp_label_push_emp
    (s : stuckness) (E : coPset) (Φ : val → iProp Σ)
    (es : language.expr iris_wp_def.wasm_lang)
    (i : nat) (lh : lholed) (n : nat)
    (es' : seq.seq administrative_instruction) :
    WP es @ s; E CTX S i; push_base lh n es' [] [] {{ v, Φ v }} ⊢ WP [AI_label n es' es] @ s; E CTX i; lh {{ v, Φ v }}.
  Proof.
    replace [AI_label n es' es]
       with [AI_label n es' ([] ++ es ++ [])]
      by (rewrite cats0; auto).
    eapply wp_label_push; auto.
  Qed.

  Lemma wp_label_push_cons
    (s : stuckness) (E : coPset) (Φ : val → iProp Σ)
    (e : administrative_instruction)
    (es : language.expr iris_wp_def.wasm_lang)
    (i : nat) (lh : lholed) (n : nat)
    (es' : seq.seq administrative_instruction) :
    WP [e] @ s; E CTX S i; push_base lh n es' [] es {{ v, Φ v }} ⊢ WP [AI_label n es' (e::es)] @ s; E CTX i; lh {{ v, Φ v }}.
  Proof.
    replace [AI_label n es' (e::es)]
       with [AI_label n es' ([] ++ [e] ++ es)]
      by (simpl; auto).
    eapply wp_label_push; auto.
  Qed.

  Lemma bimp_bient (P Q: iProp Σ) :
    (⊢ P ∗-∗ Q)
    <->
    (P ⊣⊢ Q).
  Proof.
    intros; split.
    - intros Hwand.
      iSplit.
      + iIntros.
        iApply Hwand.
        iFrame.
      + iIntros.
        iApply Hwand.
        iFrame.
    - intros Hent.
      iSplit; rewrite Hent; auto.
  Qed.

  Lemma wms_app n bs1 :
    forall ℓ sz1 bs2,
    sz1 = N.of_nat (length bs1) ->
    n ↦[wms][ℓ] (bs1 ++ bs2) ⊣⊢ n ↦[wms][ℓ] bs1 ∗ n ↦[wms][ℓ + sz1] bs2.
  Proof.
    unfold mem_block_at_pos.
    intros.
    rewrite big_opL_app.
    repeat (f_equiv; try lia).
  Qed.

End misc.

Ltac wp_chomp := take_drop_app_rewrite.
Ltac wp_chomp2 := take_drop_app_rewrite_twice.
Ltac fill_imm_pred :=
  match goal with
  | |- context [?g (immV ?v)] => instantiate (1:= λ w, ⌜w = immV v⌝%I) =>//
  end.
