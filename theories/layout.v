From Stdlib Require Import List.

Require Import stdpp.list.

From RichWasm Require Import syntax.

Record primitive_dist :=
  { pd_n__ptr : nat;
    pd_n__i32 : nat;
    pd_n__i64 : nat;
    pd_n__f32 : nat;
    pd_n__f64 : nat }.

Definition pd_empty : primitive_dist :=
  {| pd_n__ptr := 0; pd_n__i32 := 0; pd_n__i64 := 0; pd_n__f32 := 0; pd_n__f64 := 0 |}.

Definition pd_singleton (ι : primitive_rep) : primitive_dist :=
  match ι with
  | PtrR => {| pd_n__ptr := 1; pd_n__i32 := 0; pd_n__i64 := 0; pd_n__f32 := 0; pd_n__f64 := 0 |}
  | I32R => {| pd_n__ptr := 0; pd_n__i32 := 1; pd_n__i64 := 0; pd_n__f32 := 0; pd_n__f64 := 0 |}
  | I64R => {| pd_n__ptr := 0; pd_n__i32 := 0; pd_n__i64 := 1; pd_n__f32 := 0; pd_n__f64 := 0 |}
  | F32R => {| pd_n__ptr := 0; pd_n__i32 := 0; pd_n__i64 := 0; pd_n__f32 := 1; pd_n__f64 := 0 |}
  | F64R => {| pd_n__ptr := 0; pd_n__i32 := 0; pd_n__i64 := 0; pd_n__f32 := 0; pd_n__f64 := 1 |}
  end.

Definition pd_plus (pd1 pd2 : primitive_dist) : primitive_dist :=
  {| pd_n__ptr := pd1.(pd_n__ptr) + pd2.(pd_n__ptr);
     pd_n__i32 := pd1.(pd_n__i32) + pd2.(pd_n__i32);
     pd_n__i64 := pd1.(pd_n__i64) + pd2.(pd_n__i64);
     pd_n__f32 := pd1.(pd_n__f32) + pd2.(pd_n__f32);
     pd_n__f64 := pd1.(pd_n__f64) + pd2.(pd_n__f64) |}.

Definition pd_max (pd1 pd2 : primitive_dist) : primitive_dist :=
  {| pd_n__ptr := max pd1.(pd_n__ptr) pd2.(pd_n__ptr);
     pd_n__i32 := max pd1.(pd_n__i32) pd2.(pd_n__i32);
     pd_n__i64 := max pd1.(pd_n__i64) pd2.(pd_n__i64);
     pd_n__f32 := max pd1.(pd_n__f32) pd2.(pd_n__f32);
     pd_n__f64 := max pd1.(pd_n__f64) pd2.(pd_n__f64) |}.

Definition pd_le (pd1 pd2 : primitive_dist) : bool :=
  (pd1.(pd_n__ptr) <=? pd2.(pd_n__ptr)) &&
    (pd1.(pd_n__i32) <=? pd2.(pd_n__i32)) &&
    (pd1.(pd_n__i64) <=? pd2.(pd_n__i64)) &&
    (pd1.(pd_n__f32) <=? pd2.(pd_n__f32)) &&
    (pd1.(pd_n__f64) <=? pd2.(pd_n__f64)).

Definition count_primitives (ιs : list primitive_rep) : primitive_dist :=
  fold_left pd_plus (map pd_singleton ιs) pd_empty.

Definition max_primitives (ιss : list (list primitive_rep)) : primitive_dist :=
  fold_left pd_max (map count_primitives ιss) pd_empty.

Definition inject_primitive (slots : primitive_dist) (used : primitive_dist) (ι : primitive_rep) : nat :=
  match ι with
  | PtrR => used.(pd_n__ptr)
  | I32R => slots.(pd_n__ptr) + used.(pd_n__i32)
  | I64R => slots.(pd_n__ptr) + slots.(pd_n__i32) + used.(pd_n__i64)
  | F32R => slots.(pd_n__ptr) + slots.(pd_n__i32) + slots.(pd_n__i64) + used.(pd_n__f32)
  | F64R => slots.(pd_n__ptr) + slots.(pd_n__i32) + slots.(pd_n__i64) + slots.(pd_n__f32) + used.(pd_n__f64)
  end.

Definition inject_primitives (slots : primitive_dist) (ιs : list primitive_rep) : option (list nat) :=
  let fix go used ιs :=
    match ιs with
    | [] => Some []
    | ι :: ιs' =>
        let ix := inject_primitive slots used ι in
        let used' := pd_plus used (pd_singleton ι) in
        guard (pd_le used' slots);;
        cons ix <$> go used' ιs'
    end
  in
  go pd_empty ιs.

Fixpoint eval_rep (ρ : representation) : option (list primitive_rep) :=
  match ρ with
  | VarR _ => None
  | SumR ρs =>
      ιss ← mapM eval_rep ρs;
      let slots := max_primitives ιss in
      Some (I32R ::
              repeat PtrR slots.(pd_n__ptr) ++
              repeat I32R slots.(pd_n__i32) ++
              repeat I64R slots.(pd_n__i64) ++
              repeat F32R slots.(pd_n__f32) ++
              repeat F64R slots.(pd_n__f64))
  | ProdR ρs => @concat _ <$> mapM eval_rep ρs
  | PrimR ι => Some [ι]
  end.

Definition inject_sum_rep (ρs : list representation) (ρ : representation) : option (list nat) :=
  ιs ← tail <$> eval_rep (SumR ρs);
  let slots := count_primitives ιs in
  ιs0 ← eval_rep ρ;
  inject_primitives slots ιs0.

Definition kind_rep (κ : kind) : option representation :=
  match κ with
  | VALTYPE ρ _ _ => Some ρ
  | MEMTYPE _ _ => None
  end.

Definition kind_size (κ : kind) : option size :=
  match κ with
  | VALTYPE _ _ _
  | MEMTYPE Unsized _ => None
  | MEMTYPE (Sized σ) _ => Some σ
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
  | UninitT κ _
  | RecT κ _
  | ExistsMemT κ _
  | ExistsRepT κ _
  | ExistsSizeT κ _
  | ExistsTypeT κ _ _ => Some κ
  end.

Definition int_type_rep (νi : int_type) : primitive_rep :=
  match νi with
  | I32T => I32R
  | I64T => I64R
  end.

Definition int_type_type (νi : int_type) : type :=
  let ι := int_type_rep νi in
  NumT (VALTYPE (PrimR ι) ImCopy ImDrop) (IntT νi).

Definition float_type_rep (νf : float_type) : primitive_rep :=
  match νf with
  | F32T => F32R
  | F64T => F64R
  end.

Definition float_type_type (νf : float_type) : type :=
  let ι := float_type_rep νf in
  NumT (VALTYPE (PrimR ι) ImCopy ImDrop) (FloatT νf).

Definition num_type_type (ν : num_type) : type :=
  match ν with
  | IntT νi => int_type_type νi
  | FloatT νf => float_type_type νf
  end.

Definition type_i31 : type := I31T (VALTYPE (PrimR PtrR) ImCopy ImDrop).
Definition type_i32 : type := int_type_type I32T.
Definition type_i64 : type := int_type_type I64T.
Definition type_f32 : type := float_type_type F32T.
Definition type_f64 : type := float_type_type F64T.
Definition type_uninit (σ : size) : type := UninitT (MEMTYPE (Sized σ) ImDrop) σ.

(* Fact: If |- NumT ν : κ, then Some [num_type_rep ν] = type_rep (NumT ν). *)
Definition num_type_rep (ν : num_type) : primitive_rep :=
  match ν with
  | IntT νi => int_type_rep νi
  | FloatT νf => float_type_rep νf
  end.

Definition type_rep (κs : list kind) (τ : type) : option representation :=
  type_kind κs τ ≫= kind_rep.

Definition type_size (κs : list kind) (τ : type) : option size :=
  type_kind κs τ ≫= kind_size.

Definition primitive_size (ι : primitive_rep) : nat :=
  match ι with
  | PtrR => 1
  | I32R => 1
  | I64R => 2
  | F32R => 1
  | F64R => 2
  end.

Definition primitives_size : list primitive_rep -> nat :=
  list_sum ∘ map primitive_size.

Fixpoint eval_size (σ : size) : option nat :=
  match σ with
  | VarS _ => None
  | SumS σs =>
      ns ← mapM eval_size σs;
      Some (1 + list_max ns)
  | ProdS σs =>
      ns ← mapM eval_size σs;
      Some (list_sum ns)
  | RepS ρ =>
      ιs ← eval_rep ρ;
      Some (list_sum (map primitive_size ιs))
  | ConstS n => Some n
  end.
