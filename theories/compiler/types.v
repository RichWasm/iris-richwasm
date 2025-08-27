From Coq Require Import List.
Import ListNotations.

Require Import mathcomp.ssreflect.seq.

From stdpp Require Import list_numbers.

From ExtLib.Data Require Import List.
From ExtLib.Structures Require Import Functor Monads Traversable.

From Wasm Require datatypes operations.

Require RichWasm.syntax.
Require Import RichWasm.util.stdpp_extlib.
Require Import RichWasm.compiler.util.

Module R := RichWasm.syntax.
Module W. Include datatypes <+ operations. End W.

Definition translate_prim_rep (ι : R.primitive_rep) : W.value_type :=
  match ι with
  | R.PtrR => W.T_i32
  | R.I32R => W.T_i32
  | R.I64R => W.T_i64
  | R.F32R => W.T_f32
  | R.F64R => W.T_f64
  end.

Definition translate_sum_rep (ρs : list R.representation) : option (list W.value_type).
Admitted.

Fixpoint translate_rep (ρ : R.representation) : option (list W.value_type) :=
  match ρ with
  | R.VarR _ => None
  | R.SumR ρs => translate_sum_rep ρs
  | R.ProdR ρs => flatten <$> mapM translate_rep ρs
  | R.PrimR ι => Some [translate_prim_rep ι]
  end.
