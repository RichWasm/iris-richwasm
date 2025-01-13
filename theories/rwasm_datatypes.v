Require Import BinNat.

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
| PtrT     : loc -> pre_type
| ExLoc    : value_type -> pre_type (* binding site *)
| OwnR     : loc -> pre_type
| CapT     : cap -> loc -> heap_type -> pre_type
| RefT     : cap -> loc -> heap_type -> pre_type

with value_type : Type := 
| QualT: pre_type -> qual -> value_type
                             
with heap_type : Type :=
(*| VariantType : list Typ -> HeapType*)
| StructType  : list (value_type * size) -> heap_type
(*| ArrayType   : Typ -> HeapType*)
(*| Ex          : Size -> Qual -> Typ -> HeapType (* binding site *)*)

with function_type := (* tf *)
  | Tf : list value_type -> list value_type -> function_type.

Definition result_type := list value_type.
