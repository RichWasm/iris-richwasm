From Coq Require Import List.
Import ListNotations.

Require Import mathcomp.ssreflect.seq.

From stdpp Require Import list_numbers.

From ExtLib.Data Require Import List.
From ExtLib.Structures Require Import Functor Monads Traversable.

From Wasm Require datatypes operations.

Require Import RichWasm.syntax.
Require Import RichWasm.util.stdpp_extlib.
Require Import RichWasm.compiler.util.

Module W. Include datatypes <+ operations. End W.

Definition translate_prim_rep (ι : primitive_rep) : W.value_type :=
  match ι with
  | PtrR => W.T_i32
  | I32R => W.T_i32
  | I64R => W.T_i64
  | F32R => W.T_f32
  | F64R => W.T_f64
  end.

Definition translate_sum_rep (ρs : list representation) : option (list W.value_type).
Admitted.

Fixpoint translate_rep (ρ : representation) : option (list W.value_type) :=
  match ρ with
  | VarR _ => None
  | SumR ρs => translate_sum_rep ρs
  | ProdR ρs => flatten <$> mapM translate_rep ρs
  | PrimR ι => Some [translate_prim_rep ι]
  end.

Definition kind_rep (κ : kind) : option representation :=
  match κ with
  | VALTYPE ρ _ => Some ρ
  | MEMTYPE _ _ _ => None
  end.

Definition type_rep (κs : list kind) (τ : type) : option representation :=
  match τ with
  | VarT t => κs !! t ≫= kind_rep
  | NumT κ _
  | SumT κ _
  | ProdT κ _
  | ArrT κ _
  | RefT κ _ _
  | GCPtrT κ _
  | CodeRefT κ _
  | RepT κ _ _
  | PadT κ _ _
  | SerT κ _
  | RecT κ _
  | ExMemT κ _
  | ExRepT κ _
  | ExSizeT κ _
  | ExTypeT κ _ _ => kind_rep κ
  end.

Definition translate_type (κs : list kind) (τ : type) : option (list W.value_type) :=
  type_rep κs τ ≫= translate_rep.
