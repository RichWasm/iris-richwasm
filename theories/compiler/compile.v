From Coq Require Import List NArith.BinNat.
From stdpp Require Import base option strings list pretty gmap gmultiset fin_sets decidable.
From Wasm Require datatypes.
From RWasm Require term.
From RWasm Require Import exn state.
From RWasm.compiler Require Import numbers layout monads ir.

Definition compile_typ (typ : rwasm.Typ) : M (list wasm.value_type) :=
  shape ← RWasmToLayout.compile_typ typ;
  mret $ shape_to_wasm_types shape.

Section Mod.
  Variable (mod_idx : nat).

  Definition compile_module (module : rwasm.module rwasm.ArrowType) : M wasm.module :=
    layout_module ← RWasmToLayout.compile_module module;
    wasm ← LayoutToWasm.compile_module mod_idx layout_module;
    mret $ wasm.
End Mod.
