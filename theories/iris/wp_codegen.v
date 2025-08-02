Require Import iris.proofmode.tactics.

Require Import Wasm.iris.rules.iris_rules.

From RichWasm Require Import term typing.
Require Import RichWasm.iris.gc.
From RichWasm.iris.logrel Require Import relations util.
From RichWasm.compiler Require Import codegen instrs types util.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section CodeGen.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!rwasm_gcG Σ}.

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
        ▷ (↪[frame] f -∗ WP [AI_basic (BI_block tf es1)] @ s; E {{ v, Φ v }})) ∨
       (⌜i = Wasm_int.int_zero i32m⌝ ∧
        ▷ (↪[frame] f -∗ WP [AI_basic (BI_block tf es2)] @ s; E {{ v, Φ v }}))) -∗
      WP to_e_list (BI_const (VAL_int32 i) :: es) @ s; E {{ v, Φ v }}.
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
         interp_val sr [RefT cap (LocP ptr GCMem) ht] (immV [VAL_int32 i]) -∗
         WP [AI_basic (BI_block tf es2)] @ s; E {{ v, Φ v }}) ∧
      ▷ (↪[frame] f -∗
         interp_val sr [RefT cap (LocP ptr LinMem) ht] (immV [VAL_int32 i]) -∗
         WP [AI_basic (BI_block tf es1)] @ s; E {{ v, Φ v }}) -∗
      WP to_e_list (BI_const (VAL_int32 i) :: es) @ s; E {{ v, Φ v }}.
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

    iIntros "Hfr [Href | Href] Hif".
  Admitted.

  (* TODO *)
  Lemma wp_load_value_tagged_struct s E cap ptr szs tys offset sz_off n_off ty wl wl' es idx a f :
    tys !! idx = Some ty ->
    struct_field_offset szs idx = inr sz_off ->
    (* TODO: Are the sizes closed?
             If so, how is it related to the Wasm args that get_offset uses? *)
    eval_closed_size sz_off = Some (Wasm_int.nat_of_uint i32m n_off) ->
    f.(f_locs) !! (localimm offset) = Some (VAL_int32 n_off) ->
    run_codegen (load_value_tagged me fe offset ty) wl = inr (tt, wl', es) ->
    ⊢ ↪[frame] f -∗
      interp_val sr [RefT cap (LocP ptr GCMem) (StructType (zip tys szs))] (immV [VAL_int32 a]) ∨
      interp_val sr [RefT cap (LocP ptr LinMem) (StructType (zip tys szs))] (immV [VAL_int32 a]) -∗
      WP to_e_list es @ s; E {{ v, interp_val sr [ty] v }}.
  Proof.
    intros Hty Hsz_off Hn_off Hoffset Hcomp.
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

    apply run_codegen_bind_dist in Hcomp4.
    destruct Hcomp4 as ([[] []] & wl4 & es7 & es8 & Hcomp4 & Hcomp5 & Hes6).
    cbn in Hcomp5.
    inversion Hcomp5.
    subst es6 es8 wl4.
    clear Hcomp5.

    apply wp_if_gc_bit with (s := s) (E := E) (cap := cap) (ptr := ptr) (i := a) (f := f)
                            (ht := StructType (zip tys szs)) (Φ := interp_val sr [ty])
      in Hcomp4.
    destruct Hcomp4 as (wl5 & es9 & es10 & Hcomp5 & Hcomp6 & Hwp).

    iIntros "Hf Href".
  Abort.

End CodeGen.
