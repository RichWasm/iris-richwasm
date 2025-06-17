From Coq Require Import List NArith.BinNat Lists.List.
From stdpp Require Import base option strings list pretty.
From Wasm Require datatypes.
From RWasm Require term annotated_term.
From RWasm.compiler Require Import numbers monads.

Section Layout.

Inductive LayoutShape :=
| LS_int32
| LS_int64
| LS_float32
| LS_float64
| LS_tuple (fields : list LayoutShape).

Inductive LayoutValue :=
| LV_int32 (i : nat)
| LV_int64 (i : nat)
| LV_float32 (f : nat)
| LV_float64 (f : nat)
| LV_tuple (fields : list LayoutValue).

Fixpoint layout_value_to_shape (lv : LayoutValue) : LayoutShape :=
  match lv with
  | LV_int32 i => LS_int32
  | LV_int64 i => LS_int64
  | LV_float32 f => LS_float32
  | LV_float64 f => LS_float64
  | LV_tuple fields => LS_tuple (map layout_value_to_shape fields)
  end.

End Layout.

(* TODO: *)
Definition loc_to_layout (ℓ : rwasm.Loc) : LayoutValue.
Admitted.

Fixpoint value_to_layout (value : rwasm.Value) : option LayoutValue :=
  match value with
  | rwasm.NumConst (rwasm.Int _ rwasm.i32) num => mret $ LV_int32 num
  | rwasm.NumConst (rwasm.Int _ rwasm.i64) num => mret $ LV_int64 num
  | rwasm.NumConst (rwasm.Float rwasm.f32) num => mret $ LV_float32 num
  | rwasm.NumConst (rwasm.Float rwasm.f64) num => mret $ LV_float64 num
  | rwasm.Tt => None
  | rwasm.Coderef module_idx table_idx concrete =>
      mret $ LV_tuple [LV_int32 module_idx; LV_int32 table_idx] (* TODO: confirm this is ok *)
  | rwasm.Fold v => value_to_layout v
  | rwasm.Prod v__s => mret $ LV_tuple (omap value_to_layout v__s)
  | rwasm.Ref ℓ => mret $ loc_to_layout ℓ
  | rwasm.PtrV ℓ => mret $ loc_to_layout ℓ
  | rwasm.Cap
  | rwasm.Own => None
  | rwasm.Mempack ℓ v => value_to_layout v
  end.


Fixpoint compile_value (value : rwasm.Value) : M (list wasm.value) :=
  match value with
  | rwasm.NumConst num_type num => mret [(compile_num num_type num)]
  | rwasm.Tt => mthrow (err "todo")
  | rwasm.Coderef module_idx table_idx idxs => mthrow (err "todo")
  | rwasm.Fold val => mthrow (err "todo")
  | rwasm.Prod vals => mthrow (err "todo")
  | rwasm.Ref loc => mthrow (err "todo")
  | rwasm.PtrV loc => mthrow (err "todo")
  | rwasm.Cap
  | rwasm.Own => mret []
  | rwasm.Mempack loc val => mthrow (err "todo")
  end.
