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
  | MEMTYPE _ _ _ => None
  end.

Definition type_kind (κs : list kind) (τ : type) : option kind :=
  match τ with
  | VarT t => κs !! t
  | NumT κ _
  | SumT κ _
  | ProdT κ _
  | RefT κ _ _
  | GCPtrT κ _
  | CodeRefT κ _
  | RepT κ _ _
  | PadT κ _ _
  | SerT κ _
  | RecT κ _
  | ExistsMemT κ _
  | ExistsRepT κ _
  | ExistsSizeT κ _
  | ExistsTypeT κ _ _ => Some κ
  end.

(* Fact: If |- NumT ν : κ, then Some [num_type_rep ν] = type_rep (NumT ν). *)
Definition num_type_rep (ν : num_type) : primitive_rep :=
  match ν with
  | IntT I32T => I32R
  | IntT I64T => I64R
  | FloatT F32T => F32R
  | FloatT F64T => F64R
  end.

Definition type_rep (κs : list kind) (τ : type) : option representation :=
  type_kind κs τ ≫= kind_rep.

Definition primitive_size (ι : primitive_rep) : nat :=
  match ι with
  | PtrR => 1
  | I32R => 1
  | I64R => 2
  | F32R => 1
  | F64R => 2
  end.

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
