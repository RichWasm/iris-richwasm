From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From Wasm.iris.rules Require Export iris_rules proofmode.
From Wasm.iris.rules Require Export iris_example_helper. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Notation "{{{{ P }}}} es {{{{ v , Q }}}}" :=
  (□ ∀ Φ, P -∗ (∀ v : iris.val, Q -∗ Φ v) -∗ WP (es : iris.expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).   
   
Notation "{{{{ P }}}} es @ E {{{{ v , Q }}}}" :=
  (□ ∀ Φ, P -∗ (∀ v : iris.val, Q -∗ Φ v) -∗ (WP (es : iris.expr) @ NotStuck ; E {{ v, Φ v }}))%I (at level 50).


Definition i32const (n:Z) := BI_const (VAL_int32 (Wasm_int.int_of_Z i32m n)).
Definition value_of_int (n:Z) := VAL_int32 (Wasm_int.int_of_Z i32m n).

Definition u32const (n:N) := BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N n))).
Definition value_of_uint (n:N) := VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N n)).

(* Some useful constants *)
Definition two14 := 16384%N.
Definition two16 := 65536%N.
Definition two32 := 4294967296%N.
Definition ffff0000 := 4294901760%N.


Definition points_to_i32 `{!wasmG Σ} n i v :=
  (∃ a b c d, n ↦[wm][ i ] a ∗ n ↦[wm][N.add i 1] b ∗
                n ↦[wm][N.add i 2] c ∗ n ↦[wm][N.add i 3] d ∗
                ⌜ serialise_i32 v = [a ; b ; c ; d] ⌝)%I.

Notation "n ↦[i32][ k ] v" := (points_to_i32 n k v) (at level 50).
