From stdpp Require Import gmap.

From mathcomp Require Import eqtype.

From iris.proofmode Require Import base tactics classes.

From RichWasm Require Import syntax util.
From RichWasm.iris.rules Require Import iris_rules proofmode.

Definition location := N.

Definition address := N.

Definition address_map : Type := gmap location address.

Inductive pointer :=
| PtrInt (n : Z)
| PtrMM (a : address)
| PtrGC (ℓ : location)
| PtrRoot (a : address).

Inductive word :=
| WordInt (n : Z)
| WordPtr (p : pointer).

Inductive word_kind :=
| IntWord
| PtrWord.

Inductive rep_value :=
| PtrV (i : i32)
| I32V (i : i32)
| I64V (i : i64)
| F32V (f : f32)
| F64V (f : f64).

Definition to_rep_value (ι : primitive_rep) (v : value) : option rep_value :=
  match ι, v with
  | PtrR, VAL_int32 i => Some (PtrV i)
  | I32R, VAL_int32 i => Some (I32V i)
  | I64R, VAL_int64 i => Some (I64V i)
  | F32R, VAL_float32 f => Some (F32V f)
  | F64R, VAL_float64 f => Some (F64V f)
  | _, _ => None
  end.

Definition to_rep_values (ιs : list primitive_rep) (vs : list value) : option (list rep_value) :=
  mapM (fun '(ι, v) => to_rep_value ι v) (zip ιs vs).

Definition word_has_kind (k : word_kind) (w : word) : bool :=
  match k, w with
  | IntWord, WordInt _ => true
  | PtrWord, WordPtr _ => true
  | _, _ => false
  end.

Definition index_address (i : nat) : N := N.of_nat (4 * i).

Section Repr.

  Variable gc_heap_off : N.

  Inductive repr_pointer : address_map -> pointer -> Z -> Prop :=
  | ReprPtrInt θ n :
    n `mod` 2 = 0 ->
    repr_pointer θ (PtrInt n) (2 * n)
  | ReprPtrMM θ a :
    (a `mod` 4 = 0)%N ->
    repr_pointer θ (PtrMM a) (Z.of_N a - 3)
  | ReprPtrGC θ ℓ a :
    θ !! ℓ = Some a ->
    (a `mod` 4 = 0)%N ->
    (a >= gc_heap_off)%N ->
    repr_pointer θ (PtrGC ℓ) (Z.of_N a - 1)
  | ReprPtrRoot θ a :
    (a `mod` 4 = 0)%N ->
    (a < gc_heap_off)%N ->
    repr_pointer θ (PtrRoot a) (Z.of_N a - 1).

  Inductive repr_word : address_map -> word -> Z -> Prop :=
  | ReprWordInt θ n :
    repr_word θ (WordInt n) n
  | ReprWordPtr θ p n :
    repr_pointer θ p n ->
    repr_word θ (WordPtr p) n.

  Inductive repr_double_word : address_map -> word -> word -> Z -> Prop :=
  | ReprDoubleWordInt θ n1 n2 m :
    repr_word θ (WordInt n1) n1 ->
    repr_word θ (WordInt n2) n2 ->
    (Wasm_int.Int32.Z_mod_modulus n1 + n2 ≪ 32)%Z = m ->
    repr_double_word θ (WordInt n1) (WordInt n2) m.

  Definition repr_list_word (θ : address_map) (ws : list word) (ns : list Z) : Prop :=
    Forall2 (repr_word θ) ws ns.

  Inductive repr_location_index : address_map -> location -> nat -> Z -> Prop :=
  | ReprLocElem θ ℓ i a0 a :
    θ !! ℓ = Some a0 ->
    a = Z.of_N (a0 + index_address i) ->
    repr_location_index θ ℓ i a.

  Definition repr_location (θ : address_map) (ℓ : location) (a : Z) : Prop :=
    repr_location_index θ ℓ 0 a.

  Inductive ser_value : rep_value -> list word -> Prop :=
  | SerPtr i p n :
    i = Wasm_int.int_of_Z i32m n ->
    repr_pointer ∅ p n ->
    ser_value (PtrV i) [WordPtr p]
  | SerI32 i n :
    i = Wasm_int.int_of_Z i32m n ->
    ser_value (I32V i) [WordInt n]
  | SerI64 i n w1 w2 :
    i = Wasm_int.int_of_Z i64m n ->
    repr_double_word ∅ w1 w2 n ->
    ser_value (I64V i) [w1; w2]
  | SerF32 i f n :
    ser_value (I32V i) [WordInt n] ->
    serialise_i32 i = serialise_f32 f ->
    ser_value (F32V f) [WordInt n]
  | SerF64 i f n1 n2 :
    ser_value (I64V i) [WordInt n1; WordInt n2] ->
    serialise_i64 i = serialise_f64 f ->
    ser_value (F64V f) [WordInt n1; WordInt n2].

End Repr.
