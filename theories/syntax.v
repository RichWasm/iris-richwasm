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

Section TypeInd.

  Variables
    (P : type -> Prop)
    (P0: function_type -> Prop)
    (HVarT : forall idx, P (VarT idx))
    (HI31T : forall κ, P (I31T κ))
    (HNumT : forall κ nt, P (NumT κ nt))
    (HSumT : forall κ τs, Forall P τs -> P (SumT κ τs) )
    (HVariantT : forall κ τs, Forall P τs -> P (VariantT κ τs) )
    (HProdT : forall κ τs, Forall P τs -> P (ProdT κ τs) )
    (HStructT : forall κ τs, Forall P τs -> P (StructT κ τs) )
    (HRefT : forall κ m t, P t -> P (RefT κ m t))
    (HCodeRefT : forall κ ft, P0 ft -> P (CodeRefT κ ft) )
    (*coderef might be wrong*)
    (HSerT : forall κ t, P t -> P (SerT κ t))
    (HPlugT : forall κ rep, P (PlugT κ rep))
    (HSpanT : forall κ s, P (SpanT κ s))
    (HRecT : forall κ t, P t -> P (RecT κ t))
    (HExistsMemT : forall κ t, P t -> P (ExistsMemT κ t))
    (HExistsRepT : forall κ t, P t -> P (ExistsRepT κ t))
    (HExistsSizeT : forall κ t, P t -> P (ExistsSizeT κ t))
    (HExistsTypeT : forall κ1 κ2 t, P t -> P (ExistsTypeT κ1 κ2 t))

    (HOKMonoFunT : forall τs1 τs2,
        Forall P τs1 -> Forall P τs2 -> P0 (MonoFunT τs1 τs2))
    (HOKForallMemT : forall ft, P0 ft -> P0 (ForallMemT ft))
    (HOKForallRepT : forall ft, P0 ft -> P0 (ForallRepT ft))
    (HOKForallSizeT : forall ft, P0 ft -> P0 (ForallSizeT ft))
    (HOKForallTypeT : forall κ ft, P0 ft -> P0 (ForallTypeT κ ft))
  .

  Fixpoint type_ind (t:type) : P t :=
    let fix types_ind ts : Forall P ts :=
      match ts with
      | [] => ListDef.Forall_nil _
      | b :: bs => ListDef.Forall_cons _ (type_ind b) (types_ind bs)
      end
    in
    match t with
    | VarT idx => HVarT idx
    | I31T κ => HI31T κ
    | NumT κ nt => HNumT κ nt
    | SumT κ ts => HSumT κ ts (types_ind ts)
    | VariantT κ ts => HVariantT κ ts (types_ind ts)
    | ProdT κ ts => HProdT κ ts (types_ind ts)
    | StructT κ ts => HStructT κ ts (types_ind ts)
    | RefT κ m t => HRefT κ m t (type_ind t)
    | CodeRefT κ ft => HCodeRefT κ ft (function_type_ind ft)
    | SerT κ t => HSerT κ t (type_ind t)
    | PlugT κ ρ => HPlugT κ ρ
    | SpanT κ σ => HSpanT κ σ
    | RecT κ t => HRecT κ t (type_ind t)
    | ExistsMemT κ t => HExistsMemT κ t (type_ind t)
    | ExistsRepT κ t => HExistsRepT κ t (type_ind t)
    | ExistsSizeT κ t => HExistsSizeT κ t (type_ind t)
    | ExistsTypeT κ1 κ2 t => HExistsTypeT κ1 κ2 t (type_ind t)
    end
  with function_type_ind (ft: function_type) : P0 ft :=
      let fix types_ind ts : Forall P ts :=
      match ts with
      | [] => ListDef.Forall_nil _
      | b :: bs => ListDef.Forall_cons _ (type_ind b) (types_ind bs)
      end
    in
         match ft with
         | MonoFunT τs1 τs2 => HOKMonoFunT τs1 τs2 (types_ind τs1) (types_ind τs2)
         | ForallMemT ft => HOKForallMemT ft (function_type_ind ft)
         | ForallRepT ft => HOKForallRepT ft (function_type_ind ft)
         | ForallSizeT ft => HOKForallSizeT ft (function_type_ind ft)
         | ForallTypeT κ ft => HOKForallTypeT κ ft (function_type_ind ft)
         end.

  Lemma type_and_function_ind : (forall t, P t) /\ (forall ft, P0 ft).
  Proof.
    split; intros; [apply type_ind|apply function_type_ind]; assumption.
  Qed.

End TypeInd.
