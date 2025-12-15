From Stdlib Require Import List.
Import ListNotations.

Require Import RecordUpdate.RecordUpdate.

From RichWasm.syntax Require Export module rw.

Inductive primitive :=
| I32P
| I64P
| F32P
| F64P.

Definition path : Type := list nat.

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

Definition arep_to_prim (ι : atomic_rep) : primitive :=
  match ι with
  | PtrR => I32P
  | I32R => I32P
  | I64R => I64P
  | F32R => F32P
  | F64R => F64P
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
  | IInjectNew ψ _
  | ICase ψ _ _
  | ICaseLoad ψ _ _ _
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

Inductive skind :=
| SVALTYPE : list atomic_rep -> copyability -> dropability -> skind
| SMEMTYPE : nat -> dropability -> skind.

Section RepInd.

  Variables (P : representation -> Prop)
            (HVarR : forall idx, P (VarR idx))
            (HSumR : forall ρs, Forall P ρs -> P (SumR ρs))
            (HProdR : forall ρs, Forall P ρs -> P (ProdR ρs))
            (HAtomR : forall ι, P (AtomR ι)).

  Fixpoint rep_ind (ρ: representation) : P ρ :=
    let fix reps_ind ρs : Forall P ρs :=
      match ρs with
      | [] => ListDef.Forall_nil _
      | ρ :: ρs => ListDef.Forall_cons _ (rep_ind ρ) (reps_ind ρs)
      end
    in
    match ρ with
    | VarR idx => HVarR idx
    | SumR ρs => HSumR ρs (reps_ind ρs)
    | ProdR ρs => HProdR ρs (reps_ind ρs)
    | AtomR ι => HAtomR ι
    end.

End RepInd.

Section SizeInd.

  Variables (P : size -> Prop)
            (HVarS : forall idx, P (VarS idx))
            (HSumS : forall σs, Forall P σs -> P (SumS σs))
            (HProdS : forall σs, Forall P σs -> P (ProdS σs))
            (HRepS : forall ρ, P (RepS ρ))
            (HConstS : forall n, P (ConstS n)).

  Fixpoint size_ind (σ: size) : P σ :=
    let fix sizes_ind σs : Forall P σs :=
      match σs with
      | [] => ListDef.Forall_nil _
      | s :: ss => ListDef.Forall_cons _ (size_ind s) (sizes_ind ss)
      end
    in
    match σ with
    | VarS idx => HVarS idx
    | SumS σs => HSumS σs (sizes_ind σs)
    | ProdS σs => HProdS σs (sizes_ind σs)
    | RepS ρ => HRepS ρ
    | ConstS n => HConstS n
    end.

End SizeInd.
