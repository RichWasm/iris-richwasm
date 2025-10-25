From Stdlib Require Import List.
Import ListNotations.

Require Import RecordUpdate.RecordUpdate.

From RichWasm.syntax Require Export module rw.

Definition path := list nat.

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

Definition proj_instr_ty (e : instruction) : instruction_type :=
  match e with
  | INop ψ
  | IUnreachable ψ
  | ICopy ψ
  | IDrop ψ
  | INum ψ _
  | INumConst ψ _
  | IBlock ψ _ _
  | ILoop ψ _
  | IIte ψ _ _ _
  | IBr ψ _
  | IReturn ψ
  | ILocalGet ψ _
  | ILocalSet ψ _
  | ICodeRef ψ _
  | IInst ψ _
  | ICall ψ _ _
  | ICallIndirect ψ
  | IInject ψ _
  | ICase ψ _ _
  | IGroup ψ
  | IUngroup ψ
  | IFold ψ
  | IUnfold ψ
  | IPack ψ
  | IUnpack ψ _ _
  | ITag ψ
  | IUntag ψ
  | ICast ψ
  | INew ψ
  | ILoad ψ _ _
  | IStore ψ _
  | ISwap ψ _ => ψ
  end.
