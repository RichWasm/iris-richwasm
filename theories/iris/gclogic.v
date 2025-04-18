From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.algebra Require Import list.
From iris.prelude Require Import options.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From Wasm Require Import stdpp_aux.
From Wasm.iris.helpers Require Import iris_properties.
From Wasm.iris.language Require Export iris_atomicity iris_wp.
From Wasm.iris.language.iris Require Export iris_locations iris.
From Wasm.iris.rules Require Export iris_rules.

Import uPred.

Set Default Proof Using "Type".

Close Scope byte_scope.

Definition expr := iris.expr.
Definition val := iris.val.
Definition to_val := iris.to_val.

Definition loc := N.

Definition ptr := N.

Definition word := (byte * byte * byte * byte)%type.

Record logptr := LogPtr { head : loc; offset : Z }.

Inductive logval :=
  | logptrV : logptr -> logval
  | wordV : word -> logval
.

Definition logheap := gmap (loc * N) logval.

(*Definition table := gmap loc (ptr * positive).*)
Definition table := gmap loc ptr.

Definition phyv (T : table) (v : logval) : word.
Admitted.

Definition word_to_bytes (w : word) : list byte :=
  let '(b1, b2, b3, b4) := w in [b1; b2; b3; b4].

Class gcwasmG Σ := GcwasmG {
  gcmem_gen_hsG :: gen_heapGS (loc * N) logval Σ;
  table_gen_hsG :: ghost_mapG Σ unit table;
  tableGName :: gname;
}.

Section defs.

Context `{!wasmG Σ, !gcwasmG Σ, !logrel_na_invs Σ}.

Definition gcmem := N.of_nat 0.

Notation "l ↦[gc] v" := (pointsto (L:=loc*N) (V:=logval) l (DfracOwn 1) v% V)
  (at level 20, format "l ↦[gc] v") : bi_scope.

Notation " ↪[table] v" := (ghost_map_elem tableGName tt (DfracOwn 1) v%V)
  (at level 20, format " ↪[table] v").

Definition gc_inv : iProp Σ :=
  ∃ (T : table),
  ↪[table] T ∗
  [∗ map] l↦p ∈ T, ∀ v, (l, N.of_nat 0) ↦[gc] v ∗-∗ gcmem ↦[wms][ p ] (word_to_bytes (phyv T v)).

End defs.
