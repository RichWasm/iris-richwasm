
Require Import stdpp.base stdpp.list.

From RichWasm Require Import syntax.

Record arep_dist :=
  { ad_ptr : nat;
    ad_i32 : nat;
    ad_i64 : nat;
    ad_f32 : nat;
    ad_f64 : nat }.

Definition ad_empty : arep_dist :=
  {| ad_ptr := 0; ad_i32 := 0; ad_i64 := 0; ad_f32 := 0; ad_f64 := 0 |}.

Definition ad_singleton (ι : atomic_rep) : arep_dist :=
  match ι with
  | PtrR => {| ad_ptr := 1; ad_i32 := 0; ad_i64 := 0; ad_f32 := 0; ad_f64 := 0 |}
  | I32R => {| ad_ptr := 0; ad_i32 := 1; ad_i64 := 0; ad_f32 := 0; ad_f64 := 0 |}
  | I64R => {| ad_ptr := 0; ad_i32 := 0; ad_i64 := 1; ad_f32 := 0; ad_f64 := 0 |}
  | F32R => {| ad_ptr := 0; ad_i32 := 0; ad_i64 := 0; ad_f32 := 1; ad_f64 := 0 |}
  | F64R => {| ad_ptr := 0; ad_i32 := 0; ad_i64 := 0; ad_f32 := 0; ad_f64 := 1 |}
  end.

Definition ad_plus (ad1 ad2 : arep_dist) : arep_dist :=
  {| ad_ptr := ad1.(ad_ptr) + ad2.(ad_ptr);
     ad_i32 := ad1.(ad_i32) + ad2.(ad_i32);
     ad_i64 := ad1.(ad_i64) + ad2.(ad_i64);
     ad_f32 := ad1.(ad_f32) + ad2.(ad_f32);
     ad_f64 := ad1.(ad_f64) + ad2.(ad_f64) |}.

Definition ad_max (ad1 ad2 : arep_dist) : arep_dist :=
  {| ad_ptr := max ad1.(ad_ptr) ad2.(ad_ptr);
     ad_i32 := max ad1.(ad_i32) ad2.(ad_i32);
     ad_i64 := max ad1.(ad_i64) ad2.(ad_i64);
     ad_f32 := max ad1.(ad_f32) ad2.(ad_f32);
     ad_f64 := max ad1.(ad_f64) ad2.(ad_f64) |}.

Definition ad_le (ad1 ad2 : arep_dist) : bool :=
  (ad1.(ad_ptr) <=? ad2.(ad_ptr)) &&
    (ad1.(ad_i32) <=? ad2.(ad_i32)) &&
    (ad1.(ad_i64) <=? ad2.(ad_i64)) &&
    (ad1.(ad_f32) <=? ad2.(ad_f32)) &&
    (ad1.(ad_f64) <=? ad2.(ad_f64)).

Definition count_areps (ιs : list atomic_rep) : arep_dist :=
  fold_left ad_plus (map ad_singleton ιs) ad_empty.

Definition max_areps (ιss : list (list atomic_rep)) : arep_dist :=
  fold_left ad_max (map count_areps ιss) ad_empty.

Definition inject_arep (slots : arep_dist) (used : arep_dist) (ι : atomic_rep) : nat :=
  match ι with
  | PtrR => used.(ad_ptr)
  | I32R => slots.(ad_ptr) + used.(ad_i32)
  | I64R => slots.(ad_ptr) + slots.(ad_i32) + used.(ad_i64)
  | F32R => slots.(ad_ptr) + slots.(ad_i32) + slots.(ad_i64) + used.(ad_f32)
  | F64R => slots.(ad_ptr) + slots.(ad_i32) + slots.(ad_i64) + slots.(ad_f32) + used.(ad_f64)
  end.

Definition inject_areps (slots : arep_dist) (ιs : list atomic_rep) : option (list nat) :=
  let fix go used ιs :=
    match ιs with
    | [] => Some []
    | ι :: ιs' =>
        let ix := inject_arep slots used ι in
        let used' := ad_plus used (ad_singleton ι) in
        guard (ad_le used' slots);;
        cons ix <$> go used' ιs'
    end
  in
  go ad_empty ιs.

Definition kind_rep (κ : kind) : option representation :=
  match κ with
  | VALTYPE ρ _ _ => Some ρ
  | MEMTYPE _ _ => None
  end.

Definition kind_size (κ : kind) : option size :=
  match κ with
  | VALTYPE _ _ _ => None
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
  NumT (VALTYPE (AtomR ι) ImCopy ImDrop) (IntT νi).

Definition float_type_arep (νf : float_type) : atomic_rep :=
  match νf with
  | F32T => F32R
  | F64T => F64R
  end.

Definition float_type_type (νf : float_type) : type :=
  let ι := float_type_arep νf in
  NumT (VALTYPE (AtomR ι) ImCopy ImDrop) (FloatT νf).

Definition num_type_type (ν : num_type) : type :=
  match ν with
  | IntT νi => int_type_type νi
  | FloatT νf => float_type_type νf
  end.

Definition type_i31 : type := I31T (VALTYPE (AtomR PtrR) ImCopy ImDrop).
Definition type_i32 : type := int_type_type I32T.
Definition type_i64 : type := int_type_type I64T.
Definition type_f32 : type := float_type_type F32T.
Definition type_f64 : type := float_type_type F64T.
Definition type_plug (ρ : representation) : type := PlugT (VALTYPE ρ ImCopy ImDrop) ρ.
Definition type_span (σ : size) : type := SpanT (MEMTYPE σ ImDrop) σ.

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
  Variable (env : Env).

  Definition eval_mem (μ : memory) : option base_memory :=
    match μ with
    | VarM x => env !! x
    | BaseM bm => mret bm
    end.

  Fixpoint eval_rep (ρ : representation) : option (list atomic_rep) :=
    match ρ with
    | VarR x => env !! x
    | SumR ρs =>
        slots ← max_areps <$> mapM eval_rep ρs;
        mret $ I32R ::
          repeat PtrR slots.(ad_ptr) ++
          repeat I32R slots.(ad_i32) ++
          repeat I64R slots.(ad_i64) ++
          repeat F32R slots.(ad_f32) ++
          repeat F64R slots.(ad_f64)
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
    | ProdS σs =>
        list_sum <$> mapM eval_size σs
    | RepS ρ =>
        ιs ← eval_rep ρ;
        Some (list_sum (map arep_size ιs))
    | ConstS n => Some n
    end.

  Definition eval_kind (κ : kind) : option skind :=
    match κ with
    | VALTYPE ρ χ δ => 
        sρ ← eval_rep ρ;
        mret $ SVALTYPE sρ χ δ 
    | MEMTYPE σ δ =>
        n ← eval_size σ;
        mret $ SMEMTYPE n δ
    end.

  Definition inject_sum_arep (ιs : list atomic_rep) (ιs0 : list atomic_rep) : option (list nat) :=
    let slots := count_areps ιs in
    inject_areps slots ιs0.

  Definition inject_sum_rep (ρs : list representation) (ρ : representation) : option (list nat) :=
    ιs ← tail <$> eval_rep (SumR ρs);
    ιs0 ← eval_rep ρ;
    inject_sum_arep ιs ιs0.

End Eval.

(* empty_env is a type of environments that are always empty. It is
   useful for evaluating _closed_ things. *)
Inductive empty_env : Type := EmptyEnv.

Instance empty_env_lookup {K A} : Lookup K A empty_env := λ k m, None.

(* Resolve type classes here, rather than manually in the OCaml code: *)
Definition eval_rep_prim_empty (ρ : representation) : option (list primitive) :=
  eval_rep_prim EmptyEnv ρ.
