From stdpp Require Import pmap.
Require Import BinNat.
From mathcomp Require Import seq.
From Wasm Require Import bytes.
From Wasm Require datatypes.
From Wasm Require Import numerics.
From iris.algebra Require Import ofe.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition var : Type := nat.
Definition ptr : Type := N.
(** * Types **)

(** ** Qualifiers and sizes*)
Inductive cap := R | W.

Inductive heapable :=
| Heapable
| NotHeapable.

Inductive qual :=
| Unr
| Aff.

Inductive loc :=
| LocV: var -> loc
| LocP : ptr -> qual -> loc.

Inductive size :=
| size_var : var -> size
| size_const : nat -> size
| size_plus : size -> size -> size.

(** ** Numeric types *)
Inductive num_type : Type :=
  | T_i32
  | T_i64
  | T_f32
  | T_f64.

(** ** Function types *)
Inductive pre_type : Type :=
| Num      : num_type -> pre_type
(*| TVar     : var -> pre_type*)
| Unit     : pre_type
(*| ProdT    : list Typ -> pre_type*)
| CoderefT : function_type -> pre_type
(*| Rec      : Qual -> Typ -> pre_type (* binding site *) *)
(* | PtrT     : loc -> pre_type *)
| ExLoc    : value_type -> pre_type (* binding site *)
(* | OwnR     : loc -> pre_type *)
(* | CapT     : cap -> loc -> heap_type -> pre_type *)
| RefT     : cap -> size -> heap_type -> pre_type

with value_type : Type := 
| QualT: pre_type -> qual -> value_type

with heap_type : Type :=
| VariantType : list value_type -> heap_type
| StructType  : list (value_type * size) -> heap_type
| ArrayType   : value_type -> heap_type
(*| Ex          : Size -> Qual -> Typ -> HeapType (* binding site *)*)

with function_type := (* tf *)
  | Tf : list value_type -> list value_type -> function_type.

Definition result_type := list value_type.

Definition value := Wasm.datatypes.value.

Fixpoint eval_size (sz : size) : option nat :=
  match sz with
  | size_var _ => None
  | size_const n => Some n
  | size_plus sz1 sz2 =>
    match eval_size sz1, eval_size sz2 with
    | Some n1, Some n2 => Some (n1 + n2)
    | _, _ => None
    end
  end.

(* TODO *)
Definition size_of (τ : value_type) : nat :=
  0.

(* TODO: PtrT, OwnR, CapT not defined yet. *)
Definition subst_type_loc (ℓ : loc) (τ : value_type) : value_type :=
  τ.

(* TODO *)
Definition lower_type (τ : value_type) : Wasm.datatypes.value_type :=
  Wasm.datatypes.T_i32.

(* TODO *)
Definition lower_locals (L : list (value_type * size)) : list Wasm.datatypes.value_type :=
  cons Wasm.datatypes.T_i32 nil.

Class Read := {
  read_value : value_type -> bytes -> list value;
  read_tag : bytes -> nat;
}.

(* Typing contexts *)
Definition mem_type : Type := Pmap heap_type.
Record store_typing := {
    lin_mem_type: mem_type;
    unr_mem_type: mem_type;
}.

Definition locals_type : Type :=
  list (value_type * size).

Definition locals_typeO : ofe :=
  discreteO locals_type.

Definition labels_type : Type :=
  list (result_type * list (value_type * size)).

Definition labels_typeO : ofe :=
  discreteO (list (result_type * list (value_type * size))).

Definition ret_type : Type :=
  option result_type.

Definition ret_typeO : ofe :=
  optionO (discreteO result_type).

Definition module_typing : Type := unit (* TODO *).
Record function_typing := {
    fn_label_type: labels_type;
    fn_ret_type: ret_type;
}.
