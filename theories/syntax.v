From Stdlib Require Import List.
Import ListNotations.

Require Import RecordUpdate.RecordUpdate.

From RichWasm.syntax Require Export module rw.

Record flat_function_type :=
  { fft_mem_vars : nat;
    fft_rep_vars : nat;
    fft_size_vars : nat;
    fft_type_vars : list kind;
    fft_in : list type;
    fft_out : list type }.

Fixpoint flatten_function_type (ϕ : function_type) : flat_function_type :=
  match ϕ with
  | MonoFunT τs1 τs2 => Build_flat_function_type 0 0 0 [] τs1 τs2
  | ForallMemT ϕ' => flatten_function_type ϕ' <| fft_mem_vars ::= S |>
  | ForallRepT ϕ' => flatten_function_type ϕ' <| fft_rep_vars ::= S |>
  | ForallSizeT ϕ' => flatten_function_type ϕ' <| fft_size_vars ::= S |>
  | ForallTypeT κ ϕ' => flatten_function_type ϕ' <| fft_type_vars ::= app [κ] |>
  end.
