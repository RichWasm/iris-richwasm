From Stdlib Require Import List.
Import ListNotations.

From RichWasm.syntax Require Export module rw.

Definition primitive_rep_eq_dec (ι1 ι2 : primitive_rep) : {ι1 = ι2} + {ι1 <> ι2}.
  decide equality.
Defined.

Fixpoint flatten_func_type (ϕ : function_type) : list kind * list type * list type :=
  match ϕ with
  | MonoFunT τs1 τs2 => ([], τs1, τs2)
  | ForallMemT ϕ'
  | ForallRepT ϕ'
  | ForallSizeT ϕ' => flatten_func_type ϕ'
  | ForallTypeT κ ϕ' => let '(κs, τs1, τs2) := flatten_func_type ϕ' in (κ :: κs, τs1, τs2)
  end.
