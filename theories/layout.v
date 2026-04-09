From stdpp Require Import base list.

Require Import RichWasm.syntax.

Definition kind_rep (κ : kind) : option representation :=
  match κ with
  | VALTYPE ρ _ => Some ρ
  | MEMTYPE _ _ => None
  end.

Definition kind_size (κ : kind) : option size :=
  match κ with
  | VALTYPE _ _ => None
  | MEMTYPE σ _ => Some σ
  end.

Definition type_kind (κs : list kind) (τ : type) : option kind :=
  match τ with
  | VarT t => κs !! t
  | NumT κ _
  | SumT κ _
  | VariantT κ _
  | ProdT κ _
  | StructT κ _
  | RefT κ _ _
  | I31T κ
  | CodeRefT κ _
  | SerT κ _
  | PlugT κ _
  | SpanT κ _
  | RecT κ _
  | ExistsMemT κ _
  | ExistsRepT κ _
  | ExistsSizeT κ _
  | ExistsTypeT κ _ _ => Some κ
  end.

Definition int_type_arep (νi : int_type) : atomic_rep :=
  match νi with
  | I32T => I32R
  | I64T => I64R
  end.

Definition int_type_type (νi : int_type) : type :=
  let ι := int_type_arep νi in
  NumT (VALTYPE (AtomR ι) NoRefs) (IntT νi).

Definition float_type_arep (νf : float_type) : atomic_rep :=
  match νf with
  | F32T => F32R
  | F64T => F64R
  end.

Definition float_type_type (νf : float_type) : type :=
  let ι := float_type_arep νf in
  NumT (VALTYPE (AtomR ι) NoRefs) (FloatT νf).

Definition num_type_type (ν : num_type) : type :=
  match ν with
  | IntT νi => int_type_type νi
  | FloatT νf => float_type_type νf
  end.

Definition type_i31 : type := I31T (VALTYPE (AtomR PtrR) NoRefs).
Definition type_i32 : type := int_type_type I32T.
Definition type_i64 : type := int_type_type I64T.
Definition type_f32 : type := float_type_type F32T.
Definition type_f64 : type := float_type_type F64T.
Definition type_plug (ρ : representation) : type := PlugT (VALTYPE ρ NoRefs) ρ.
Definition type_span (σ : size) : type := SpanT (MEMTYPE σ NoRefs) σ.

(* Fact: If |- NumT ν : κ, then Some [num_type_rep ν] = type_rep (NumT ν). *)
Definition num_type_arep (ν : num_type) : atomic_rep :=
  match ν with
  | IntT νi => int_type_arep νi
  | FloatT νf => float_type_arep νf
  end.

Definition prim_to_arep (η : primitive) : atomic_rep :=
  match η with
  | I32P => I32R
  | I64P => I64R
  | F32P => F32R
  | F64P => F64R
  end.

Definition type_plug_prim (ηs : list primitive) : type :=
  type_plug (ProdR (map (AtomR ∘ prim_to_arep) ηs)).

Definition type_rep (κs : list kind) (τ : type) : option representation :=
  type_kind κs τ ≫= kind_rep.

Definition type_size (κs : list kind) (τ : type) : option size :=
  type_kind κs τ ≫= kind_size.

Definition arep_size (ι : atomic_rep) : nat :=
  match ι with
  | PtrR => 1
  | I32R => 1
  | I64R => 2
  | F32R => 1
  | F64R => 2
  end.

Definition areps_size : list atomic_rep -> nat :=
  list_sum ∘ map arep_size.

Section Eval.

  Context `{Lookup nat base_memory Env}.
  Context `{Lookup nat (list atomic_rep) Env}.
  Context `{Lookup nat nat Env}.
  Variable env : Env.

  Definition eval_mem (μ : memory) : option base_memory :=
    match μ with
    | VarM x => env !! x
    | BaseM bm => mret bm
    end.

  Fixpoint eval_rep (ρ : representation) : option (list atomic_rep) :=
    match ρ with
    | VarR x => env !! x
    | SumR ρs => cons I32R ∘ @concat _ <$> mapM eval_rep ρs
    | ProdR ρs => @concat _ <$> mapM eval_rep ρs
    | AtomR ι => Some [ι]
    end.

  Definition eval_rep_prim (ρ : representation) : option (list primitive) :=
    map arep_to_prim <$> eval_rep ρ.

  Definition eval_rep_size (ρ : representation) : option nat :=
    areps_size <$> eval_rep ρ.

  Fixpoint eval_size (σ : size) : option nat :=
    match σ with
    | VarS x => env !! x
    | SumS σs =>
        ns ← mapM eval_size σs;
        Some (1 + list_max ns)
    | ProdS σs => list_sum <$> mapM eval_size σs
    | RepS ρ => list_sum ∘ map arep_size <$> eval_rep ρ
    | ConstS n => Some n
    end.

  Definition eval_kind (κ : kind) : option skind :=
    match κ with
    | VALTYPE ρ ξ =>
        sρ ← eval_rep ρ;
        mret $ SVALTYPE sρ ξ
    | MEMTYPE σ ξ =>
        n ← eval_size σ;
        mret $ SMEMTYPE n ξ
    end.

  Definition sum_offset (ρs : list representation) (i : nat) : option nat :=
    ιss ← mapM eval_rep (take i ρs);
    Some (length (concat ιss)).

End Eval.

(* empty_env is a type of environments that are always empty. It is
   useful for evaluating _closed_ things. *)
Inductive empty_env : Type := EmptyEnv.

Instance empty_env_lookup {K A} : Lookup K A empty_env := λ k m, None.

(* Resolve type classes here, rather than manually in the OCaml code: *)
Definition eval_rep_prim_empty (ρ : representation) : option (list primitive) :=
  eval_rep_prim EmptyEnv ρ.
