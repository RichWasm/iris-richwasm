Require Import iris.proofmode.tactics.

Require Import Wasm.iris.rules.iris_rules.

From RichWasm Require Import syntax typing.
From RichWasm.compiler Require Import codegen instrs modules types util.
From RichWasm.iris Require Import autowp gc.
From RichWasm.iris.logrel Require Import relations util.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section CodeGen.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!rwasm_gcG Σ}.

  Variable sr : store_runtime.
  Variable me : module_env.
  Variable F : function_ctx.
  Variable L : local_ctx.
  Variable WL : wlocal_ctx.

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

End CodeGen.
