From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From RichWasm.iris.rules Require Export proofmode.
From RichWasm.iris.alloc.functions Require Export util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Record store_runtime :=
  { sr_mem_mm : memaddr;
    sr_mem_gc : memaddr;
    sr_func_mmalloc : funcaddr;
    sr_func_gcalloc : funcaddr;
    sr_func_free : funcaddr;
    sr_func_setflag : funcaddr;
    sr_func_registerroot : funcaddr;
    sr_func_unregisterroot : funcaddr;
    sr_table : tableaddr;
    sr_gc_heap_off : N }.

(* beware:
   The i32 type is a record {intval: Z; proof: -1 < z < 2^32}.
   This means that N_repr is not a functional relation
   (unless you assume propositional extensionality).
*)
Definition N_repr (n : N) (n32 : i32) : Prop :=
  (-1 < Z.of_N n < Wasm_int.Int32.modulus)%Z /\
    n = Wasm_int.N_of_uint i32m n32.

Lemma N_repr_uint :
  forall n n32,
    N_repr n n32 ->
    n = Wasm_int.N_of_uint i32m n32.
Proof.
  unfold N_repr.
  tauto.
Qed.

Lemma N_repr_i32repr :
  forall (n : N) (z : Z),
    (-1 < Z.of_N n < Wasm_int.Int32.modulus)%Z ->
    z = Z.of_N n ->
    N_repr n (Wasm_int.Int32.repr z).
Proof.
  intros.
  unfold Wasm_int.Int32.repr, N_repr, Wasm_int.N_of_uint; cbn.
  split.
  - assumption.
  - rewrite Wasm_int.Int32.Z_mod_modulus_id.
    + subst. by rewrite N2Z.id.
    + lia.
Qed.

Definition serialize_Z_i32 : Z -> bytes := serialise_i32 ∘ Wasm_int.int_of_Z i32m.

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
