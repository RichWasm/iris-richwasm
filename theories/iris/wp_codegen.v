Require Import iris.proofmode.tactics.

Require Import Wasm.iris.rules.iris_rules.

Require Import RichWasm.term.
Require Import RichWasm.iris.logrel.relations.
From RichWasm.compiler Require Import codegen instrs util.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section CodeGen.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.

  Variable sr : store_runtime.
  Variable me : module_env.
  Variable fe : function_env.

  Lemma wp_if_c {A B} s E i tf (c1 : codegen A) (c2 : codegen B) wl wl' es x y Φ f :
    run_codegen (if_c tf c1 c2) wl = inr (x, y, wl', es) ->
    exists wl1 es1 es2,
    run_codegen c1 wl = inr (x, wl1, es1) /\
    run_codegen c2 wl1 = inr (y, wl', es2) /\
    ⊢ ↪[frame] f -∗
      ((⌜i <> Wasm_int.int_zero i32m⌝ ∧
        ▷ (↪[frame] f -∗ WP [AI_basic (BI_block tf es1)] @ s; E {{ w, Φ w }})) ∨
       (⌜i = Wasm_int.int_zero i32m⌝ ∧
        ▷ (↪[frame] f -∗ WP [AI_basic (BI_block tf es2)] @ s; E {{ w, Φ w }}))) -∗
      WP to_e_list (BI_const (VAL_int32 i) :: es) @ s; E {{ w, Φ w }}.
  Proof.
    intros Hcomp.
    unfold if_c in Hcomp.

    apply run_codegen_bind_dist in Hcomp.
    destruct Hcomp as (x1 & wl1 & es1 & es2 & Hcomp1 & Hcomp2 & Hes).
    destruct x1 as [x' es1'].
    subst es.
    apply run_codegen_capture in Hcomp1.
    destruct Hcomp1 as [Hcomp1 ->].

    apply run_codegen_bind_dist in Hcomp2.
    destruct Hcomp2 as (x2 & wl2 & es3 & es4 & Hcomp2 & Hcomp3 & Hes).
    destruct x2 as [y' es2'].
    subst es2.

    apply run_codegen_capture in Hcomp2.
    destruct Hcomp2 as [Hcomp2 ->].

    cbn in Hcomp3.
    inversion Hcomp3.
    subst x' y' wl2 es4.
    clear Hcomp3.
    rename es1' into es1, es2' into es2.

    exists wl1, es1, es2.
    split; first assumption.
    split; first assumption.

    iIntros "Hfr Hbl".
    iSimpl.
    iDestruct "Hbl" as "[[%Hi Hbl] | [%Hi Hbl]]".
    - by iApply (wp_if_true with "Hfr"); first assumption.
    - by iApply (wp_if_false with "Hfr"); first assumption.
  Qed.

  (* TODO *)
  Lemma wp_if_gc_bit {A B} s E cap ptr ht tf (gc : codegen B) (mm : codegen A) wl wl' es x y i Φ f :
    run_codegen (if_gc_bit tf gc mm) wl = inr (y, x, wl', es) ->
    exists wl1 es1 es2,
    run_codegen mm wl = inr (y, wl1, es1) /\
    run_codegen gc wl1 = inr (x, wl', es2) /\
    ⊢ ↪[frame] f -∗
      interp_val sr [RefT cap (LocP ptr GCMem) ht] (immV [VAL_int32 i]) ∨
      interp_val sr [RefT cap (LocP ptr LinMem) ht] (immV [VAL_int32 i]) -∗
      ▷ (↪[frame] f -∗
         (interp_val sr [RefT cap (LocP ptr GCMem) ht] (immV [VAL_int32 i]) -∗
          WP [AI_basic (BI_block tf es2)] @ s; E {{ w, Φ w }}) ∨
         (interp_val sr [RefT cap (LocP ptr LinMem) ht] (immV [VAL_int32 i]) -∗
          WP [AI_basic (BI_block tf es1)] @ s; E {{ w, Φ w }})) -∗
      WP to_e_list (BI_const (VAL_int32 i) :: es) @ s; E {{ w, Φ w }}.
  Proof.
    intros Hcomp.
    unfold if_gc_bit in Hcomp.

    apply run_codegen_bind_dist in Hcomp.
    destruct Hcomp as (x1 & wl1 & es1 & es2 & Hcomp1 & Hcomp2 & Hes).
    cbn in Hcomp1.
    inversion Hcomp1.
    subst x1 wl1 es es1.
    clear Hcomp1.

    apply run_codegen_bind_dist in Hcomp2.
    destruct Hcomp2 as (x2 & wl2 & es3 & es4 & Hcomp2 & Hcomp3 & Hes2).
    cbn in Hcomp2.
    inversion Hcomp2.
    subst x2 wl2 es2 es3.
    clear Hcomp2.

    apply run_codegen_bind_dist in Hcomp3.
    destruct Hcomp3 as (x3 & wl3 & es5 & es6 & Hcomp3 & Hcomp4 & Hes4).
    cbn in Hcomp3.
    inversion Hcomp3.
    subst x3 wl3 es4 es5.
    clear Hcomp3.
    rename Hcomp4 into Hcomp.

    apply wp_if_c with (s := s) (E := E) (i := i) (Φ := Φ) (f := f) in Hcomp.
    destruct Hcomp as (wl1 & es1 & es2 & Hcomp1 & Hcomp2 & Hif).

    exists wl1, es1, es2.
    split; first assumption.
    split; first assumption.

    iIntros "Hfr Href Hif".
  Abort.

  (* TODO *)
  Lemma wp_load_value_tagged s E get_offset ty wl wl' es :
    run_codegen (load_value_tagged me fe get_offset ty) wl = inr (tt, wl', es) ->
    ⊢ True -∗
      WP to_e_list es @ s; E {{ w, ⌜w = immV []⌝ }}.
  Proof.
    intros Hcomp.
    iIntros (HTrue).
    unfold load_value_tagged in Hcomp.

    apply run_codegen_bind_dist in Hcomp.
    destruct Hcomp as (x1 & wl1 & es1 & es2 & Hcomp1 & Hcomp2 & Hes).
    cbn in Hcomp1.
    inversion Hcomp1.
    subst x1 wl1 es es1.
    clear Hcomp1.

    apply run_codegen_bind_dist in Hcomp2.
    destruct Hcomp2 as (x2 & wl2 & es3 & es4 & Hcomp2 & Hcomp3 & Hes2).
    cbn in Hcomp2.
    inversion Hcomp2.
    subst x2 wl2 es2 es3.
    clear Hcomp2.

    apply run_codegen_bind_dist in Hcomp3.
    destruct Hcomp3 as (x3 & wl3 & es5 & es6 & Hcomp3 & Hcomp4 & Hes4).
    cbn in Hcomp3.
    inversion Hcomp3.
    subst x3 wl3 es4 es5.
    clear Hcomp3.

    iSimpl.
  Abort.

End CodeGen.
