Require Import stdpp.list.

Require Import RecordUpdate.RecordUpdate.

From RichWasm Require Import syntax layout.

Record module_ctx :=
  { mc_functions : list function_type;
    mc_table : list function_type;
    mc_globals : list (mutability * type) }.

Arguments module_ctx : clear implicits.

Definition local_ctx := list type.

Record kind_ctx :=
  { kc_mem_vars : nat;
    kc_rep_vars : nat;
    kc_size_vars : nat }.

Definition kc_empty : kind_ctx :=
  {| kc_mem_vars := 0;
     kc_rep_vars := 0;
     kc_size_vars := 0 |}.

Record function_ctx :=
  { fc_return : list type;
    fc_locals : list (list primitive_rep);
    fc_labels : list (list type * local_ctx);
    fc_kind_ctx : kind_ctx;
    fc_type_vars : list kind }.

Arguments function_ctx : clear implicits.

Definition fc_empty : function_ctx :=
  {| fc_return := [];
     fc_locals := [];
     fc_labels := [];
     fc_kind_ctx := kc_empty;
     fc_type_vars := [] |}.

Definition subst_function_ctx
  (s__mem : nat -> memory) (s__rep : nat -> representation) (s__size : nat -> size) (s__type : nat -> type)
  (F : function_ctx) :
  function_ctx :=
  {| fc_return := map (subst_type s__mem s__rep s__size s__type) F.(fc_return);
     fc_locals := F.(fc_locals);
     fc_labels :=
       map
         (fun '(τs, L) =>
            (map (subst_type s__mem s__rep s__size s__type) τs, map (subst_type s__mem s__rep s__size s__type) L))
         F.(fc_labels);
     fc_kind_ctx := F.(fc_kind_ctx);
     fc_type_vars := map (subst_kind s__mem s__rep s__size) F.(fc_type_vars) |}.

Global Instance eta_function_ctx : Settable function_ctx :=
  settable! Build_function_ctx <fc_return; fc_locals; fc_labels; fc_kind_ctx; fc_type_vars>.

Inductive mem_ok : kind_ctx -> memory -> Prop :=
| OKVarM K m :
  m < K.(kc_mem_vars) ->
  mem_ok K (VarM m)
| OKConstM K cm :
  mem_ok K (ConstM cm).

Inductive rep_ok : kind_ctx -> representation -> Prop :=
| OKVarR K r :
  r < K.(kc_rep_vars) ->
  rep_ok K (VarR r)
| OKSumR K ρs :
  Forall (rep_ok K) ρs ->
  rep_ok K (SumR ρs)
| OKProdR K ρs :
  Forall (rep_ok K) ρs ->
  rep_ok K (ProdR ρs)
| OKPrimR K ι :
  rep_ok K (PrimR ι).

Inductive size_ok : kind_ctx -> size -> Prop :=
| OKVarS K s :
  s < K.(kc_size_vars) ->
  size_ok K (VarS s)
| OKSumS K σs :
  Forall (size_ok K) σs ->
  size_ok K (SumS σs)
| OKProdS K σs :
  Forall (size_ok K) σs ->
  size_ok K (ProdS σs)
| OKRepS K ρ :
  rep_ok K ρ ->
  size_ok K (RepS ρ)
| OKConstS K n :
  size_ok K (ConstS n).

Inductive sizity_ok : kind_ctx -> sizity -> Prop :=
| OKSized K σ :
  size_ok K σ ->
  sizity_ok K (Sized σ)
| OKUnsized K :
  sizity_ok K Unsized.

Inductive kind_ok : kind_ctx -> kind -> Prop :=
| OKVALTYPE K ρ χ δ :
  rep_ok K ρ ->
  kind_ok K (VALTYPE ρ χ δ)
| OKMEMTYPE K ζ μ δ :
  sizity_ok K ζ ->
  mem_ok K μ ->
  kind_ok K (MEMTYPE ζ μ δ).

Inductive type_ok : function_ctx -> type -> Prop :=
| OKVarT F t κ :
  F.(fc_type_vars) !! t = Some κ ->
  kind_ok F.(fc_kind_ctx) κ ->
  type_ok F (VarT t)
| OKI31T F κ :
  kind_ok F.(fc_kind_ctx) κ ->
  type_ok F (I31T κ)
| OKNumT F κ ν :
  kind_ok F.(fc_kind_ctx) κ ->
  type_ok F (NumT κ ν)
| OKSumT F κ τs :
  kind_ok F.(fc_kind_ctx) κ ->
  Forall (type_ok F) τs ->
  type_ok F (SumT κ τs)
| OKProdT F κ τs :
  kind_ok F.(fc_kind_ctx) κ ->
  Forall (type_ok F) τs ->
  type_ok F (ProdT κ τs)
| OKRefT F κ μ τ :
  kind_ok F.(fc_kind_ctx) κ ->
  mem_ok F.(fc_kind_ctx) μ ->
  type_ok F τ ->
  type_ok F (RefT κ μ τ)
| OKGCPtr F κ τ :
  kind_ok F.(fc_kind_ctx) κ ->
  type_ok F τ ->
  type_ok F (GCPtrT κ τ)
| OKCodeRefT F κ ϕ :
  kind_ok F.(fc_kind_ctx) κ ->
  function_type_ok F ϕ ->
  type_ok F (CodeRefT κ ϕ)
| OKRepT F κ ρ τ :
  kind_ok F.(fc_kind_ctx) κ ->
  rep_ok F.(fc_kind_ctx) ρ ->
  type_ok F τ ->
  type_ok F (RepT κ ρ τ)
| OKPadT F κ σ τ :
  kind_ok F.(fc_kind_ctx) κ ->
  size_ok F.(fc_kind_ctx) σ ->
  type_ok F τ ->
  type_ok F (PadT κ σ τ)
| OKSerT F κ τ :
  kind_ok F.(fc_kind_ctx) κ ->
  type_ok F τ ->
  type_ok F (SerT κ τ)
| OKRecT F κ τ :
  kind_ok F.(fc_kind_ctx) κ ->
  type_ok (F <| fc_type_vars ::= cons κ |>) τ ->
  type_ok F (RecT κ τ)
| OKExistsMemT F κ τ :
  kind_ok F.(fc_kind_ctx) κ ->
  type_ok (F <| fc_kind_ctx ::= set kc_mem_vars S |>) τ ->
  type_ok F (ExistsMemT κ τ)
| OKExistsRepT F κ τ :
  kind_ok F.(fc_kind_ctx) κ ->
  type_ok (F <| fc_kind_ctx ::= set kc_rep_vars S |>) τ ->
  type_ok F (ExistsRepT κ τ)
| OKExistsSizeT F κ τ :
  kind_ok F.(fc_kind_ctx) κ ->
  type_ok (F <| fc_kind_ctx ::= set kc_size_vars S |>) τ ->
  type_ok F (ExistsSizeT κ τ)
| OKExistsType F κ κ0 τ :
  kind_ok F.(fc_kind_ctx) κ ->
  kind_ok F.(fc_kind_ctx) κ0 ->
  type_ok (F <| fc_type_vars ::= cons κ0 |>) τ ->
  type_ok F (ExistsTypeT κ κ0 τ)

with function_type_ok : function_ctx -> function_type -> Prop :=
| OKMonoFunT F τs1 τs2 :
  Forall (type_ok F) τs1 ->
  Forall (type_ok F) τs2 ->
  function_type_ok F (MonoFunT τs1 τs2)
| OKForallMemT F ϕ :
  function_type_ok (F <| fc_kind_ctx ::= set kc_mem_vars S |>) ϕ ->
  function_type_ok F (ForallMemT ϕ)
| OKForallRepT F ϕ :
  function_type_ok (F <| fc_kind_ctx ::= set kc_rep_vars S |>) ϕ ->
  function_type_ok F (ForallRepT ϕ)
| OKForallSizeT F ϕ :
  function_type_ok (F <| fc_kind_ctx ::= set kc_size_vars S |>) ϕ ->
  function_type_ok F (ForallSizeT ϕ)
| OKForallTypeT F κ ϕ :
  kind_ok F.(fc_kind_ctx) κ ->
  function_type_ok (F <| fc_type_vars ::= cons κ |>) ϕ ->
  function_type_ok F (ForallTypeT κ ϕ).

Definition mono_mem (μ : memory) : Prop := exists cm, μ = ConstM cm.

Inductive subkind_of : kind -> kind -> Prop :=
| KSubValExCopy ρ δ :
  subkind_of (VALTYPE ρ ImCopy δ) (VALTYPE ρ ExCopy δ)
| KSubValNoCopy ρ δ :
  subkind_of (VALTYPE ρ ExCopy δ) (VALTYPE ρ NoCopy δ)
| KSubValExDrop ρ χ :
  subkind_of (VALTYPE ρ χ ImDrop) (VALTYPE ρ χ ExDrop)
| KSubValNoDrop ρ χ :
  subkind_of (VALTYPE ρ χ ExDrop) (VALTYPE ρ χ NoDrop)
| SubMemExDrop ζ μ :
  subkind_of (MEMTYPE ζ μ ImDrop) (MEMTYPE ζ μ ExDrop)
| SubMemNoDrop ζ μ :
  subkind_of (MEMTYPE ζ μ ExDrop) (MEMTYPE ζ μ NoDrop)
| KSubSizity σ μ δ :
  subkind_of (MEMTYPE (Sized σ) μ δ) (MEMTYPE Unsized μ δ).

Inductive has_kind_ok : function_ctx -> type -> kind -> Prop :=
| OKHasKind F τ κ :
  type_ok F τ ->
  kind_ok F.(fc_kind_ctx) κ ->
  has_kind_ok F τ κ.

Inductive has_kind : function_ctx -> type -> kind -> Prop :=
| KSub F τ κ κ' :
  subkind_of κ κ' ->
  has_kind F τ κ ->
  has_kind F τ κ'
| KVar F t κ :
  F.(fc_type_vars) !! t = Some κ ->
  kind_ok F.(fc_kind_ctx) κ ->
  has_kind F (VarT t) κ
| KI31 F :
  let κ := VALTYPE (PrimR PtrR) ImCopy ImDrop in
  has_kind F (I31T κ) κ
| KI32 F :
  let κ := VALTYPE (PrimR I32R) ImCopy ImDrop in
  has_kind F (NumT κ (IntT I32T)) κ
| KI64 F :
  let κ := VALTYPE (PrimR I64R) ImCopy ImDrop in
  has_kind F (NumT κ (IntT I64T)) κ
| KF32 F :
  let κ := VALTYPE (PrimR F32R) ImCopy ImDrop in
  has_kind F (NumT κ (FloatT F32T)) κ
| KF64 F :
  let κ := VALTYPE (PrimR F64R) ImCopy ImDrop in
  has_kind F (NumT κ (FloatT F64T)) κ
| KSumVal F τs ρs χ δ :
  Forall2 (fun τ ρ => has_kind F τ (VALTYPE ρ χ δ)) τs ρs ->
  let κ := VALTYPE (SumR ρs) χ δ in
  has_kind F (SumT κ τs) κ
| KSumMem F τs ζs μ δ :
  mem_ok F.(fc_kind_ctx) μ ->
  Forall2 (fun τ ζ => has_kind F τ (MEMTYPE ζ μ δ)) τs ζs ->
  let κ := MEMTYPE Unsized μ δ in
  has_kind F (SumT κ τs) κ
| KSumMemSized F τs σs μ δ :
  mem_ok F.(fc_kind_ctx) μ ->
  Forall2 (fun τ σ => has_kind F τ (MEMTYPE (Sized σ) μ δ)) τs σs ->
  let κ := MEMTYPE (Sized (SumS σs)) μ δ in
  has_kind F (SumT κ τs) κ
| KProdVal F τs ρs χ δ :
  Forall2 (fun τ ρ => has_kind F τ (VALTYPE ρ χ δ)) τs ρs ->
  let κ := VALTYPE (ProdR ρs) χ δ in
  has_kind F (ProdT κ τs) κ
| KProdMem F τs ζs μ δ :
  mem_ok F.(fc_kind_ctx) μ ->
  Forall2 (fun τ ζ => has_kind F τ (MEMTYPE ζ μ δ)) τs ζs ->
  let κ := MEMTYPE Unsized μ δ in
  has_kind F (ProdT κ τs) κ
| KProdMemSized F τs σs μ δ :
  mem_ok F.(fc_kind_ctx) μ ->
  Forall2 (fun τ σ => has_kind F τ (MEMTYPE (Sized σ) μ δ)) τs σs ->
  let κ := MEMTYPE (Sized (ProdS σs)) μ δ in
  has_kind F (ProdT κ τs) κ
| KRef F τ ζ μ δ :
  has_kind F τ (MEMTYPE ζ μ δ) ->
  let κ := VALTYPE (PrimR PtrR) NoCopy NoDrop in
  has_kind F (RefT κ μ τ) κ
| KRefMMDrop F τ ζ :
  has_kind F τ (MEMTYPE ζ (ConstM MemMM) ImDrop) ->
  let κ := VALTYPE (PrimR PtrR) NoCopy ExDrop in
  has_kind F (RefT κ (ConstM MemMM) τ) κ
| KRefGC F τ ζ δ :
  has_kind F τ (MEMTYPE ζ (ConstM MemGC) δ) ->
  let κ := VALTYPE (PrimR PtrR) ExCopy ExDrop in
  has_kind F (RefT κ (ConstM MemGC) τ) κ
| KGCPtr F τ ζ δ :
  has_kind F τ (MEMTYPE ζ (ConstM MemGC) δ) ->
  let κ := MEMTYPE (Sized (ConstS 1)) (ConstM MemGC) ImDrop in
  has_kind F (GCPtrT κ τ) κ
| KCodeRef F ϕ :
  function_type_ok F ϕ ->
  let κ := VALTYPE (PrimR I32R) ImCopy ImDrop in
  has_kind F (CodeRefT κ ϕ) κ
| KRep F ρ0 ρ τ χ δ :
  has_kind F τ (VALTYPE ρ0 χ δ) ->
  rep_ok F.(fc_kind_ctx) ρ ->
  let κ := VALTYPE ρ χ δ in
  has_kind F (RepT κ ρ τ) κ
| KPad F σ0 σ τ μ δ :
  has_kind F τ (MEMTYPE (Sized σ0) μ δ) ->
  size_ok F.(fc_kind_ctx) σ ->
  let κ := MEMTYPE (Sized σ) μ δ in
  has_kind F (PadT κ σ τ) κ
| KSer F τ ρ μ χ δ :
  mem_ok F.(fc_kind_ctx) μ ->
  has_kind F τ (VALTYPE ρ χ δ) ->
  let κ := MEMTYPE (Sized (RepS ρ)) μ δ in
  has_kind F (SerT κ τ) κ
| KRec F τ κ :
  has_kind (F <| fc_type_vars ::= cons κ |>) τ κ ->
  has_kind F (RecT κ τ) κ
| KExistsMem F τ κ :
  has_kind (F <| fc_kind_ctx ::= set kc_mem_vars S |>) τ κ ->
  kind_ok F.(fc_kind_ctx) κ ->
  has_kind F (ExistsMemT κ τ) κ
| KExistsRep F τ κ :
  has_kind (F <| fc_kind_ctx ::= set kc_rep_vars S |>) τ κ ->
  kind_ok F.(fc_kind_ctx) κ ->
  has_kind F (ExistsRepT κ τ) κ
| KExistsSize F τ κ :
  has_kind (F <| fc_kind_ctx ::= set kc_size_vars S |>) τ κ ->
  kind_ok F.(fc_kind_ctx) κ ->
  has_kind F (ExistsSizeT κ τ) κ
| KExistsType F τ κ0 κ :
  kind_ok F.(fc_kind_ctx) κ0 ->
  kind_ok F.(fc_kind_ctx) κ ->
  has_kind (F <| fc_type_vars ::= cons κ0 |>) τ κ ->
  has_kind F (ExistsTypeT κ κ0 τ) κ.

Section HasKindInd.

  Variable P : function_ctx -> type -> kind -> Prop.

  Hypotheses
    (HSub : forall F τ κ κ', subkind_of κ κ' -> P F τ κ -> P F τ κ')
      (HVar : forall F t κ, F.(fc_type_vars) !! t = Some κ ->
                       kind_ok F.(fc_kind_ctx) κ ->
                       P F (VarT t) κ)
      (HI31 : forall F, let κ := VALTYPE (PrimR PtrR) ImCopy ImDrop in
                   P F (I31T κ) κ)
      (HI32 : forall F, let κ := VALTYPE (PrimR I32R) ImCopy ImDrop in
                   P F (NumT κ (IntT I32T)) κ)
      (HI64 : forall F, let κ := VALTYPE (PrimR I64R) ImCopy ImDrop in
                   P F (NumT κ (IntT I64T)) κ)
      (HF32 : forall F, let κ := VALTYPE (PrimR F32R) ImCopy ImDrop in
                   P F (NumT κ (FloatT F32T)) κ)
      (HF64 : forall F, let κ := VALTYPE (PrimR F64R) ImCopy ImDrop in
                   P F (NumT κ (FloatT F64T)) κ)
      (HSumVal : forall F τs ρs χ δ, Forall2 (fun τ ρ => P F τ (VALTYPE ρ χ δ)) τs ρs ->
                                let κ := VALTYPE (SumR ρs) χ δ in
                                P F (SumT κ τs) κ)
      (HSumMem : forall F τs ζs μ δ, mem_ok F.(fc_kind_ctx) μ ->
                                Forall2 (fun τ ζ => P F τ (MEMTYPE ζ μ δ)) τs ζs ->
                                let κ := MEMTYPE Unsized μ δ in P F (SumT κ τs) κ)
      (HSumMemSized : forall F τs σs μ δ,
          mem_ok F.(fc_kind_ctx) μ ->
          Forall2 (fun τ σ => P F τ (MEMTYPE (Sized σ) μ δ)) τs σs ->
          let κ := MEMTYPE (Sized (SumS σs)) μ δ in P F (SumT κ τs) κ)
      (HProdVal : forall F τs ρs χ δ, Forall2 (fun τ ρ => P F τ (VALTYPE ρ χ δ)) τs ρs ->
                                 let κ := VALTYPE (ProdR ρs) χ δ in
                                 P F (ProdT κ τs) κ)
      (HProdMem : forall F τs ζs μ δ, mem_ok F.(fc_kind_ctx) μ ->
                                 Forall2 (fun τ ζ => P F τ (MEMTYPE ζ μ δ)) τs ζs ->
                                 let κ := MEMTYPE Unsized μ δ in
                                 P F (ProdT κ τs) κ)
      (HProdMemSized : forall F τs σs μ δ, mem_ok F.(fc_kind_ctx) μ ->
                                      Forall2 (fun τ σ => P F τ (MEMTYPE (Sized σ) μ δ)) τs σs ->
                                      let κ := MEMTYPE (Sized (ProdS σs)) μ δ in
                                      P F (ProdT κ τs) κ)
      (HRef : forall F τ ζ μ δ, P F τ (MEMTYPE ζ μ δ) ->
                           let κ := VALTYPE (PrimR PtrR) NoCopy NoDrop in
                           P F (RefT κ μ τ) κ)
      (HRefMMDrop : forall F τ ζ, P F τ (MEMTYPE ζ (ConstM MemMM) ImDrop) ->
                             let κ := VALTYPE (PrimR PtrR) NoCopy ExDrop in
                             P F (RefT κ (ConstM MemMM) τ) κ)
      (HRefGC : forall F τ ζ δ, P F τ (MEMTYPE ζ (ConstM MemGC) δ) ->
                           let κ := VALTYPE (PrimR PtrR) ExCopy ExDrop in
                           P F (RefT κ (ConstM MemGC) τ) κ)
      (HGCPtr : forall F τ ζ δ, P F τ (MEMTYPE ζ (ConstM MemGC) δ) ->
                           let κ := MEMTYPE (Sized (ConstS 1)) (ConstM MemGC) ImDrop in
                           P F (GCPtrT κ τ) κ)
      (HCodeRef : forall F ϕ, function_type_ok F ϕ ->
                         let κ := VALTYPE (PrimR I32R) ImCopy ImDrop in
                         P F (CodeRefT κ ϕ) κ)
      (HRep : forall F ρ0 ρ τ χ δ, P F τ (VALTYPE ρ0 χ δ) ->
                              rep_ok F.(fc_kind_ctx) ρ ->
                              let κ := VALTYPE ρ χ δ in
                              P F (RepT κ ρ τ) κ)
      (HPad : forall F σ0 σ τ μ δ, P F τ (MEMTYPE (Sized σ0) μ δ) ->
                              size_ok F.(fc_kind_ctx) σ ->
                              let κ := MEMTYPE (Sized σ) μ δ in
                              P F (PadT κ σ τ) κ)
      (HSer : forall F τ ρ μ χ δ, mem_ok F.(fc_kind_ctx) μ ->
                             P F τ (VALTYPE ρ χ δ) ->
                             let κ := MEMTYPE (Sized (RepS ρ)) μ δ in
                             P F (SerT κ τ) κ)
      (HRec : forall F τ κ, P (F <| fc_type_vars ::= cons κ |>) τ κ ->
                       P F (RecT κ τ) κ)
      (HExistsMem : forall F τ κ, P (F <| fc_kind_ctx ::= set kc_mem_vars S |>) τ κ ->
                             kind_ok F.(fc_kind_ctx) κ ->
                             P F (ExistsMemT κ τ) κ)
      (HExistsRep : forall F τ κ, P (F <| fc_kind_ctx ::= set kc_rep_vars S |>) τ κ ->
                             kind_ok F.(fc_kind_ctx) κ ->
                             P F (ExistsRepT κ τ) κ)
      (HExistsSize : forall F τ κ, P (F <| fc_kind_ctx ::= set kc_size_vars S |>) τ κ ->
                              kind_ok F.(fc_kind_ctx) κ ->
                              P F (ExistsSizeT κ τ) κ)
      (HExistsType : forall F τ κ0 κ, kind_ok F.(fc_kind_ctx) κ0 ->
                                 kind_ok F.(fc_kind_ctx) κ ->
                                 P (F <| fc_type_vars ::= cons κ0 |>) τ κ ->
                                 P F (ExistsTypeT κ κ0 τ) κ).

  Fixpoint has_kind_ind' (F : function_ctx) (τ : type) (κ : kind) (H : has_kind F τ κ) : P F τ κ :=
    match H with
    | KSub F τ κ κ' H1 H2 => HSub F τ κ κ' H1 (has_kind_ind' F τ κ H2)
    | KVar F t κ H1 H2 => HVar F t κ H1 H2
    | KI31 F => HI31 F
    | KI32 F => HI32 F
    | KI64 F => HI64 F
    | KF32 F => HF32 F
    | KF64 F => HF64 F
    | KSumVal F τs ρs χ δ H1 =>
        HSumVal F τs ρs χ δ (Forall2_impl _ _ _ _ H1 (fun τ ρ => has_kind_ind' _ _ _))
    | KSumMem F τs ζs μ δ H1 H2 =>
        HSumMem F τs ζs μ δ H1 (Forall2_impl _ _ _ _ H2 (fun τ ζ => has_kind_ind' _ _ _))
    | KSumMemSized F τs σs μ δ H1 H2 =>
        HSumMemSized F τs σs μ δ H1 (Forall2_impl _ _ _ _ H2 (fun τ σ => has_kind_ind' _ _ _))
    | KProdVal F τs ρs χ δ H1 H2 =>
        HProdVal F τs ρs χ δ (Forall2_impl _ _ _ _ H1 (fun τ ρ => has_kind_ind' _ _ _))
    | KProdMem F τs ζs μ δ H1 H2 =>
        HProdMem F τs ζs μ δ H1 (Forall2_impl _ _ _ _ H2 (fun τ ζ => has_kind_ind' _ _ _))
    | KProdMemSized F τs σs μ δ H1 H2 =>
        HProdMemSized F τs σs μ δ H1 (Forall2_impl _ _ _ _ H2 (fun τ σ => has_kind_ind' _ _ _))
    | KRef F τ ζ μ δ H1 => HRef F τ ζ μ δ (has_kind_ind' _ _ _ H1)
    | KRefMMDrop F τ ζ H1 => HRefMMDrop F τ ζ (has_kind_ind' _ _ _ H1)
    | KRefGC F τ ζ δ H1 => HRefGC F τ ζ δ (has_kind_ind' _ _ _ H1)
    | KGCPtr F τ ζ δ H1 => HGCPtr F τ ζ δ (has_kind_ind' _ _ _ H1)
    | KCodeRef F ϕ H1 => HCodeRef F ϕ H1
    | KRep F ρ0 ρ τ χ δ H1 H2 => HRep F ρ0 ρ τ χ δ (has_kind_ind' _ _ _ H1) H2
    | KPad F σ0 σ τ μ δ H1 H2 => HPad F σ0 σ τ μ δ (has_kind_ind' _ _ _ H1) H2
    | KSer F τ ρ μ χ δ H1 H2 => HSer F τ ρ μ χ δ H1 (has_kind_ind' _ _ _ H2)
    | KRec F τ κ H1 => HRec F τ κ (has_kind_ind' _ _ _ H1)
    | KExistsMem F τ κ H1 H2 => HExistsMem F τ κ (has_kind_ind' _ _ _ H1) H2
    | KExistsRep F τ κ H1 H2 => HExistsRep F τ κ (has_kind_ind' _ _ _ H1) H2
    | KExistsSize F τ κ H1 H2 => HExistsSize F τ κ (has_kind_ind' _ _ _ H1) H2
    | KExistsType F τ κ0 κ H1 H2 H3 => HExistsType F τ κ0 κ H1 H2 (has_kind_ind' _ _ _ H3)
    end.

End HasKindInd.

Inductive has_rep : function_ctx -> type -> representation -> Prop :=
| RepVALTYPE F τ ρ χ δ :
  has_kind F τ (VALTYPE ρ χ δ) ->
  has_rep F τ ρ.

Inductive has_mono_rep : function_ctx -> type -> Prop :=
| MonoRep F τ ρ ιs :
  has_rep F τ ρ ->
  eval_rep ρ = Some ιs ->
  has_mono_rep F τ.

Definition has_mono_rep_instr (F : function_ctx) '(InstrT τs1 τs2 : instruction_type) : Prop :=
  Forall (has_mono_rep F) τs1 /\ Forall (has_mono_rep F) τs2.

Definition has_size (F : function_ctx) (τ : type) (σ : size) : Prop :=
  exists χ δ, has_kind F τ (MEMTYPE (Sized σ) χ δ).

Inductive mono_size : function_ctx -> type -> Prop :=
| MonoSizeVALTYPE F τ ρ ιs :
  has_rep F τ ρ ->
  eval_rep ρ = Some ιs ->
  mono_size F τ
| MonoSizeMEMTYPE F τ σ μ δ n :
  has_kind F τ (MEMTYPE (Sized σ) μ δ) ->
  eval_size σ = Some n ->
  mono_size F τ.

Definition mono_rep (ρ : representation) : Prop :=
  exists ιs, eval_rep ρ = Some ιs.

Definition type_rep_eval (F : function_ctx) (τ : type) (ιs : list primitive_rep) : Prop :=
  exists ρ, has_rep F τ ρ /\ eval_rep ρ = Some ιs.

Inductive size_eq : size -> size -> Prop :=
| SizeEq σ1 σ2 n :
  eval_size σ1 = Some n ->
  eval_size σ2 = Some n ->
  size_eq σ1 σ2.

Definition type_size_eq (F : function_ctx) (τ1 τ2 : type) : Prop :=
  exists σ1 σ2, has_size F τ1 σ1 /\ has_size F τ2 σ2 /\ size_eq σ1 σ2.

Inductive has_copyability : function_ctx -> type -> copyability -> Prop :=
| CopyVALTYPE F τ ρ χ δ :
  has_kind F τ (VALTYPE ρ χ δ) ->
  has_copyability F τ χ.

Inductive has_dropability : function_ctx -> type -> dropability -> Prop :=
| DropVALTYPE F τ ρ χ δ :
  has_kind F τ (VALTYPE ρ χ δ) ->
  has_dropability F τ δ
| DropMEMTYPE F τ ζ μ δ :
  has_kind F τ (MEMTYPE ζ μ δ) ->
  has_dropability F τ δ.

Definition convertible_to (ιs1 ιs2 : list primitive_rep) : Prop :=
  let eq_dec := primitive_rep_eq_dec in
  count_occ eq_dec ιs1 PtrR <= count_occ eq_dec ιs2 PtrR /\
    primitives_size (remove eq_dec PtrR ιs1) <= primitives_size (remove eq_dec PtrR ιs2).

Record path_result :=
  { pr_prefix : list type;
    pr_target : type;
    pr_replaced : type }.

Inductive resolve_path : type -> path -> option type -> path_result -> Prop :=
| PathNilNone τ :
  resolve_path τ [] None (Build_path_result [] τ τ)
| PathNilSome τ τ' :
  resolve_path τ [] (Some τ') (Build_path_result [] τ τ')
| PathProd pr i π τ__π τs0 τ τs' κ :
  length τs0 = i ->
  resolve_path τ π τ__π pr ->
  let pr' :=
    {| pr_prefix := τs0 ++ pr.(pr_prefix);
       pr_target := pr.(pr_target);
       pr_replaced := ProdT κ (τs0 ++ pr.(pr_replaced) :: τs') |}
  in
  resolve_path (ProdT κ (τs0 ++ τ :: τs')) (PCProj i :: π) τ__π pr'
| PathRep pr π τ τ__π κ ρ :
  resolve_path τ π τ__π pr ->
  resolve_path (RepT κ ρ τ) (PCUnwrap :: π) τ__π pr
| PathPad pr π τ τ__π κ σ :
  resolve_path τ π τ__π pr ->
  resolve_path (PadT κ σ τ) (PCUnwrap :: π) τ__π pr
| PathSer pr π τ τ__π κ :
  resolve_path τ π τ__π pr ->
  resolve_path (SerT κ τ) (PCUnwrap :: π) τ__π pr
| PathExistsMem pr π τ τ__π κ :
  resolve_path τ π τ__π pr ->
  resolve_path (ExistsMemT κ τ) (PCUnwrap :: π) τ__π pr
| PathRec pr π τ τ__π κ :
  resolve_path τ π τ__π pr ->
  resolve_path (RecT κ τ) (PCUnwrap :: π) τ__π pr
| PathExistsRep pr π τ τ__π κ :
  resolve_path τ π τ__π pr ->
  resolve_path (ExistsRepT κ τ) (PCUnwrap :: π) τ__π pr
| PathExistsSize pr π τ τ__π κ :
  resolve_path τ π τ__π pr ->
  resolve_path (ExistsSizeT κ τ) (PCUnwrap :: π) τ__π pr
| PathExistsType pr π τ τ__π κ κ0 :
  resolve_path τ π τ__π pr ->
  resolve_path (ExistsTypeT κ κ0 τ) (PCUnwrap :: π) τ__π pr.

Inductive stores_as : function_ctx -> type -> type -> Prop :=
| SASer F κ τ :
  stores_as F τ (SerT κ τ)
| SAPad F κ τ τ' ρ ιs σ n :
  has_rep F τ ρ ->
  eval_rep ρ = Some ιs ->
  eval_size σ = Some n ->
  list_sum (map primitive_size ιs) <= n ->
  stores_as F τ τ' ->
  stores_as F τ (PadT κ σ τ')
| SAProd F κ τs τs' :
  Forall2 (stores_as F) τs τs' ->
  stores_as F (ProdT κ τs) (ProdT κ τs').

Definition loads_as (F : function_ctx) (τ τ' : type) := stores_as F τ' τ.

Inductive function_type_inst : function_ctx -> index -> function_type -> function_type -> Prop :=
| FTInstMem F ϕ μ :
  let ϕ' := subst_function_type (unscoped.scons μ VarM) VarR VarS VarT ϕ in
  function_type_inst F (MemI μ) (ForallMemT ϕ) ϕ'
| FTInstRep F ϕ ρ :
  let ϕ' := subst_function_type VarM (unscoped.scons ρ VarR) VarS VarT ϕ in
  function_type_inst F (RepI ρ) (ForallRepT ϕ) ϕ'
| FTInstSize F ϕ σ :
  let ϕ' := subst_function_type VarM VarR (unscoped.scons σ VarS) VarT ϕ in
  function_type_inst F (SizeI σ) (ForallSizeT ϕ) ϕ'
| FTInstType F ϕ τ κ :
  has_kind F τ κ ->
  let ϕ' := subst_function_type VarM VarR VarS (unscoped.scons τ VarT) ϕ in
  function_type_inst F (TypeI τ) (ForallTypeT κ ϕ) ϕ'.

Inductive function_type_insts : function_ctx -> list index -> function_type -> function_type -> Prop :=
| FTNil F ϕ :
  function_type_insts F [] ϕ ϕ
| FTCons F ϕ ϕ' ϕ'' ix ixs :
  function_type_inst F ix ϕ ϕ' ->
  function_type_insts F ixs ϕ' ϕ'' ->
  function_type_insts F (ix :: ixs) ϕ ϕ''.

Inductive packed_existential : function_ctx -> type -> type -> Prop :=
| PackMem F μ τ' κ' :
  has_kind F τ' κ' ->
  let τ0 := subst_type (unscoped.scons μ VarM) VarR VarS VarT τ' in
  packed_existential F τ0 (ExistsMemT κ' τ')
| PackRep F ρ τ' κ' :
  has_kind F τ' κ' ->
  let τ0 := subst_type VarM (unscoped.scons ρ VarR) VarS VarT τ' in
  packed_existential F τ0 (ExistsRepT κ' τ')
| PackSize F σ τ' κ' :
  has_kind F τ' κ' ->
  let τ0 := subst_type VarM VarR (unscoped.scons σ VarS) VarT τ' in
  packed_existential F τ0 (ExistsSizeT κ' τ')
| PackType F τ τ' κ κ' :
  has_kind F τ κ ->
  has_kind F τ' κ' ->
  let τ0 := subst_type VarM VarR VarS (unscoped.scons τ VarT) τ' in
  packed_existential F τ0 (ExistsTypeT κ' κ τ').

Inductive unpacked_existential :
  function_ctx -> local_ctx -> list instruction -> instruction_type -> local_ctx ->
  function_ctx -> local_ctx -> list instruction -> instruction_type -> local_ctx ->
  Prop :=
| UnpackMem F L L' es τs1 κ τ τs2 :
  let F0 := subst_function_ctx (up_memory VarM) VarR VarS VarT F
              <| fc_kind_ctx ::= set kc_mem_vars S |> in
  let es0 := map (subst_instruction (up_memory VarM) VarR VarS VarT) es in
  let up := map (subst_type (up_memory VarM) VarR VarS VarT) in
  unpacked_existential
    F L es (InstrT (τs1 ++ [ExistsMemT κ τ]) τs2) L'
    F0 (up L) es0 (InstrT (up τs1 ++ [τ]) (up τs2)) (up L')
| UnpackRep F L L' es τs1 κ τ τs2 :
  let F0 := subst_function_ctx VarM (up_representation VarR) VarS VarT F
              <| fc_kind_ctx ::= set kc_rep_vars S |> in
  let es0 := map (subst_instruction VarM (up_representation VarR) VarS VarT) es in
  let up := map (subst_type VarM (up_representation VarR) VarS VarT) in
  unpacked_existential
    F L es (InstrT (τs1 ++ [ExistsRepT κ τ]) τs2) L'
    F0 (up L) es0 (InstrT (up τs1 ++ [τ]) (up τs2)) (up L')
| UnpackSize F L L' es τs1 κ τ τs2 :
  let F0 := subst_function_ctx VarM VarR (up_size VarS) VarT F
              <| fc_kind_ctx ::= set kc_size_vars S |> in
  let es0 := map (subst_instruction VarM VarR (up_size VarS) VarT) es in
  let up := map (subst_type VarM VarR (up_size VarS) VarT) in
  unpacked_existential
    F L es (InstrT (τs1 ++ [ExistsSizeT κ τ]) τs2) L'
    F0 (up L) es0 (InstrT (up τs1 ++ [τ]) (up τs2)) (up L')
| UnpackType F L L' es τs1 κ κ0 τ τs2 :
  let F0 := subst_function_ctx VarM VarR VarS (up_type VarT) F <| fc_type_vars ::= cons κ0 |> in
  let es0 := map (subst_instruction VarM VarR VarS (up_type VarT)) es in
  let up := map (subst_type VarM VarR VarS (up_type VarT)) in
  unpacked_existential
    F L es (InstrT (τs1 ++ [ExistsTypeT κ κ0 τ]) τs2) L'
    F0 (up L) es0 (InstrT (up τs1 ++ [τ]) (up τs2)) (up L').

Definition local_ctx_ok (F : function_ctx) (L : local_ctx) : Prop :=
  Forall2 (type_rep_eval F) L F.(fc_locals).

Inductive has_instruction_type_ok : function_ctx -> instruction_type -> local_ctx -> Prop :=
| OKHasInstructionType F ψ L' :
  has_mono_rep_instr F ψ ->
  local_ctx_ok F L' ->
  has_instruction_type_ok F ψ L'.

Inductive has_instruction_type_cvt : conversion_op -> instruction_type -> Prop :=
| TWrapC :
  has_instruction_type_cvt CWrap (InstrT [type_i64] [type_i32])
| TExtend s :
  has_instruction_type_cvt (CExtend s) (InstrT [type_i32] [type_i64])
| TTrunc νf νi s :
  has_instruction_type_cvt (CTrunc νf νi s) (InstrT [float_type_type νf] [int_type_type νi])
| TDemote :
  has_instruction_type_cvt CDemote (InstrT [type_f64] [type_f32])
| TPromote :
  has_instruction_type_cvt CPromote (InstrT [type_f32] [type_f64])
| TConvert νi νf s :
  has_instruction_type_cvt (CConvert νi νf s) (InstrT [int_type_type νi] [float_type_type νf])
| TReinterpretI32 :
  has_instruction_type_cvt (CReinterpret (IntT I32T)) (InstrT [type_i32] [type_f32])
| TReinterpretI64 :
  has_instruction_type_cvt (CReinterpret (IntT I64T)) (InstrT [type_i64] [type_f64])
| TReinterpretF32 :
  has_instruction_type_cvt (CReinterpret (FloatT F32T)) (InstrT [type_f32] [type_i32])
| TReinterpretF64 :
  has_instruction_type_cvt (CReinterpret (FloatT F64T)) (InstrT [type_f64] [type_i64]).

Inductive has_instruction_type_num : num_instruction -> instruction_type -> Prop :=
| TInt1 νi op :
  let τ := int_type_type νi in
  has_instruction_type_num (IInt1 νi op) (InstrT [τ] [τ])
| TInt2 νi op :
  let τ := int_type_type νi in
  has_instruction_type_num (IInt2 νi op) (InstrT [τ; τ] [τ])
| TIntTest νi op :
  let τ := int_type_type νi in
  has_instruction_type_num (IIntTest νi op) (InstrT [τ] [type_i32])
| TIntRel νi op :
  let τ := int_type_type νi in
  has_instruction_type_num (IIntRel νi op) (InstrT [τ; τ] [type_i32])
| IFloat1 νf op :
  let τ := float_type_type νf in
  has_instruction_type_num (IFloat1 νf op) (InstrT [τ] [τ])
| IFloat2 νf op :
  let τ := float_type_type νf in
  has_instruction_type_num (IFloat2 νf op) (InstrT [τ; τ] [τ])
| IFloatRel νf op :
  let τ := float_type_type νf in
  has_instruction_type_num (IFloatRel νf op) (InstrT [τ; τ] [type_i32])
| ICvt op ψ :
  has_instruction_type_cvt op ψ ->
  has_instruction_type_num (ICvt op) ψ.

Inductive has_instruction_type :
  module_ctx -> function_ctx -> local_ctx -> instruction -> instruction_type -> local_ctx -> Prop :=
| TNop M F L :
  let ψ := InstrT [] [] in
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (INop ψ) ψ L
| TUnreachable M F L L' ψ :
  has_instruction_type_ok F ψ L' ->
  has_instruction_type M F L (IUnreachable ψ) ψ L'
| TCopy M F L τ :
  let ψ := InstrT [τ] [τ; τ] in
  has_copyability F τ ExCopy ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (ICopy ψ) ψ L
| TDrop M F L τ :
  let ψ := InstrT [τ] [] in
  has_dropability F τ ExDrop ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IDrop ψ) ψ L
| TNum M F L e ψ :
  has_instruction_type_num e ψ ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (INum ψ e) ψ L
| TNumConst M F L κ ν n :
  let ψ := InstrT [] [NumT κ ν] in
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (INumConst ψ n) ψ L
| TBlock M F L L' τs1 τs2 es :
  let F' := F <| fc_labels ::= cons (τs2, L') |> in
  let ψ := InstrT τs1 τs2 in
  have_instruction_type M F' L es ψ L' ->
  has_instruction_type_ok F ψ L' ->
  has_instruction_type M F L (IBlock ψ L' es) ψ L'
| TLoop M F L τs1 τs2 es :
  let F' := F <| fc_labels ::= cons (τs1, L) |> in
  let ψ := InstrT τs1 τs2 in
  have_instruction_type M F' L es ψ L ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (ILoop ψ es) ψ L
| TIte M F L L' τs1 τs2 es1 es2 :
  have_instruction_type M F L es1 (InstrT τs1 τs2) L' ->
  have_instruction_type M F L es2 (InstrT τs1 τs2) L' ->
  let ψ := InstrT (τs1 ++ [type_i32]) τs2 in
  has_instruction_type_ok F ψ L' ->
  has_instruction_type M F L (IIte ψ L' es1 es2) ψ L'
| TBr M F L L' i τs τs1 τs2 :
  let ψ := InstrT (τs1 ++ τs) τs2 in
  F.(fc_labels) !! i = Some (τs, L) ->
  Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
  has_instruction_type_ok F ψ L' ->
  has_instruction_type M F L (IBr ψ i) ψ L'
| TReturn M F L L' τs τs1 τs2 :
  let ψ := InstrT (τs1 ++ τs) τs2 in
  F.(fc_return) = τs ->
  Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
  has_instruction_type_ok F ψ L' ->
  has_instruction_type M F L (IReturn ψ) ψ L'
| TLocalGet M F L i τ ιs :
  let ψ := InstrT [] [τ] in
  let ρ := ProdR (map PrimR ιs) in
  let τ' := RepT (VALTYPE ρ ImCopy ImDrop) ρ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []) in
  let L' := <[ i := τ' ]> L in
  F.(fc_locals) !! i = Some ιs ->
  L !! i = Some τ ->
  has_instruction_type_ok F ψ L' ->
  has_instruction_type M F L (ILocalGet ψ i) ψ L'
| TLocalGetCopy M F L i τ :
  let ψ := InstrT [] [τ] in
  L !! i = Some τ ->
  has_copyability F τ ImCopy ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (ILocalGet ψ i) ψ L
| TLocalSet M F L i τ τ' ιs :
  let ψ := InstrT [τ'] [] in
  let L' := <[ i := τ' ]> L in
  L !! i = Some τ ->
  has_dropability F τ ImDrop ->
  F.(fc_locals) !! i = Some ιs ->
  type_rep_eval F τ' ιs ->
  has_instruction_type_ok F ψ L' ->
  has_instruction_type M F L (ILocalSet ψ i) ψ L'
| TGlobalGet M F L i ω τ :
  let ψ := InstrT [] [τ] in
  M.(mc_globals) !! i = Some (ω, τ) ->
  has_copyability F τ ImCopy ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IGlobalGet ψ i) ψ L
| TGlobalSet M F L i τ :
  let ψ := InstrT [τ] [] in
  M.(mc_globals) !! i = Some (Mut, τ) ->
  has_dropability F τ ImDrop ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IGlobalSet ψ i) ψ L
| TGlobalSwap M F L i τ :
  let ψ := InstrT [τ] [τ] in
  M.(mc_globals) !! i = Some (Mut, τ) ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IGlobalSwap ψ i) ψ L
| TCodeRef M F L i ϕ :
  let τ := CodeRefT (VALTYPE (PrimR I32R) ImCopy ImDrop) ϕ in
  let ψ := InstrT [] [τ] in
  M.(mc_table) !! i = Some ϕ ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (ICodeRef ψ i) ψ L
| TInst M F L ix ϕ ϕ' :
  let κ := VALTYPE (PrimR I32R) ImCopy ImDrop in
  let ψ := InstrT [CodeRefT κ ϕ] [CodeRefT κ ϕ'] in
  function_type_inst F ix ϕ ϕ' ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IInst ψ ix) ψ L
| TCall M F L i ixs ϕ τs1 τs2 :
  let ψ := InstrT τs1 τs2 in
  M.(mc_functions) !! i = Some ϕ ->
  function_type_insts F ixs ϕ (MonoFunT τs1 τs2) ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (ICall ψ i ixs) ψ L
| TCallIndirect M F L τs1 τs2 :
  let κ := VALTYPE (PrimR I32R) ImCopy ImDrop in
  let ψ := InstrT (τs1 ++ [CodeRefT κ (MonoFunT τs1 τs2)]) τs2 in
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (ICallIndirect ψ) ψ L
| TInject M F L i τ τs κ :
  let ψ := InstrT [τ] [SumT κ τs] in
  τs !! i = Some τ ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IInject ψ i) ψ L
| TCase M F L L' κ τ' τs ess :
  let ψ := InstrT [SumT κ τs] [τ'] in
  Forall2 (fun τ es => have_instruction_type M F L es (InstrT [τ] [τ']) L') τs ess ->
  has_instruction_type_ok F ψ L' ->
  has_instruction_type M F L (ICase ψ L' ess) ψ L'
| TGroup M F L τs κ :
  let ψ := InstrT τs [ProdT κ τs] in
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IGroup ψ) ψ L
| TUngroup M F L τs κ :
  let ψ := InstrT [ProdT κ τs] τs in
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IUngroup ψ) ψ L
| TFold M F L τ κ :
  let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
  let ψ := InstrT [τ0] [RecT κ τ] in
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IFold ψ) ψ L
| TUnfold M F L τ κ :
  let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
  let ψ := InstrT [RecT κ τ] [τ0] in
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IUnfold ψ) ψ L
| TPack M F L τ τ' :
  let ψ := InstrT [τ] [τ'] in
  packed_existential F τ τ' ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IPack ψ) ψ L
| TUnpack M F F0 L L' L0 L0' es es0 ψ ψ0 :
  unpacked_existential F L es ψ L' F0 L0 es0 ψ0 L0' ->
  have_instruction_type M F0 L0 es0 ψ0 L0' ->
  has_instruction_type_ok F ψ L' ->
  has_instruction_type M F L (IUnpack ψ L' es) ψ L'
| TWrap M F L ρ ιs0 ιs τ0 κ :
  let ψ := InstrT [τ0] [RepT κ ρ τ0] in
  type_rep_eval F τ0 ιs0 ->
  eval_rep ρ = Some ιs ->
  convertible_to ιs0 ιs ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IWrap ψ) ψ L
| TUnwrap M F L ρ ιs0 ιs τ0 κ :
  let ψ := InstrT [RepT κ ρ τ0] [τ0] in
  type_rep_eval F τ0 ιs0 ->
  eval_rep ρ = Some ιs ->
  convertible_to ιs0 ιs ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IUnwrap ψ) ψ L
| TTag M F L :
  let ψ := InstrT [type_i32] [type_i31] in
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (ITag ψ) ψ L
| TUntag M F L :
  let ψ := InstrT [type_i31] [type_i32] in
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IUntag ψ) ψ L
| TRefNew M F L μ τ τ' κ :
  let ψ := InstrT [τ] [RefT κ μ τ'] in
  mono_mem μ ->
  stores_as F τ τ' ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IRefNew ψ) ψ L
| TRefLoad M F L π μ τ τval pr κ :
  let ψ := InstrT [RefT κ μ τ] [RefT κ μ τ; τval] in
  resolve_path τ π None pr ->
  has_copyability F pr.(pr_target) ImCopy ->
  loads_as F pr.(pr_target) τval ->
  Forall (mono_size F) pr.(pr_prefix) ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IRefLoad ψ π) ψ L
| TRefStore M F L π μ τ τval pr κ :
  let ψ := InstrT [RefT κ μ τ; τval] [τ] in
  resolve_path τ π None pr ->
  has_dropability F pr.(pr_target) ImDrop ->
  stores_as F τval pr.(pr_target) ->
  Forall (mono_size F) pr.(pr_prefix) ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IRefStore ψ π) ψ L
| TRefMMStore M F L π τ τval τmem pr κ κ' :
  let ψ := InstrT [RefT κ (ConstM MemMM) τ; τval] [RefT κ' (ConstM MemMM) pr.(pr_replaced)] in
  stores_as F τval τmem ->
  resolve_path τ π (Some τmem) pr ->
  has_dropability F pr.(pr_target) ImDrop ->
  type_size_eq F pr.(pr_target) τmem ->
  Forall (mono_size F) pr.(pr_prefix) ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IRefStore ψ π) ψ L
| TRefSwap M F L π τ τval pr κ μ :
  let ψ := InstrT [RefT κ μ τ; τval] [RefT κ μ τ; τval] in
  resolve_path τ π None pr ->
  Forall (mono_size F) pr.(pr_prefix) ->
  loads_as F τval pr.(pr_target) ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IRefSwap ψ π) ψ L
| TRefMMSwap M F L π τ τval τval' τmem κ κ' pr :
  let ψ := InstrT [RefT κ (ConstM MemMM) τ; τval'] [RefT κ' (ConstM MemMM) pr.(pr_replaced); τval] in
  stores_as F τval τmem ->
  resolve_path τ π (Some τmem) pr ->
  Forall (mono_size F) pr.(pr_prefix) ->
  loads_as F pr.(pr_target) τval ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IRefSwap ψ π) ψ L

with have_instruction_type :
  module_ctx -> function_ctx -> local_ctx -> list instruction -> instruction_type -> local_ctx -> Prop :=
| TNil M F L :
  local_ctx_ok F L ->
  have_instruction_type M F L [] (InstrT [] []) L
| TCons M F L1 L2 L3 e es τs1 τs2 τs3 :
  has_instruction_type M F L1 e (InstrT τs1 τs2) L2 ->
  have_instruction_type M F L2 es (InstrT τs2 τs3) L3 ->
  have_instruction_type M F L1 (e :: es) (InstrT τs1 τs3) L3
| TFrame M F L L' es τ τs1 τs2 :
  has_mono_rep F τ ->
  have_instruction_type M F L es (InstrT τs1 τs2) L' ->
  have_instruction_type M F L es (InstrT (τ :: τs1) (τ :: τs2)) L'.

Section HasHaveInstructionTypeMind.

  Variables
    (P1 : module_ctx -> function_ctx -> local_ctx -> instruction -> instruction_type -> local_ctx -> Prop)
      (P2 : module_ctx -> function_ctx -> local_ctx -> list instruction -> instruction_type -> local_ctx ->
            Prop).

  Hypotheses
    (HNop : forall M F L,
        let ψ := InstrT [] [] in
        has_instruction_type_ok F ψ L ->
        P1 M F L (INop ψ) ψ L)
      (HUnreachable : forall M F L L' ψ,
          has_instruction_type_ok F ψ L' ->
          P1 M F L (IUnreachable ψ) ψ L')
      (HCopy : forall M F L τ,
          let ψ := InstrT [τ] [τ; τ] in
          has_copyability F τ ExCopy ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (ICopy ψ) ψ L)
      (HDrop : forall M F L τ,
          let ψ := InstrT [τ] [] in
          has_dropability F τ ExDrop ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (IDrop ψ) ψ L)
      (HNum : forall M F L e ψ,
          has_instruction_type_num e ψ ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (INum ψ e) ψ L)
      (HNumConst : forall M F L κ ν n,
          let ψ := InstrT [] [NumT κ ν] in
          has_instruction_type_ok F ψ L ->
          P1 M F L (INumConst ψ n) ψ L)
      (HBlock : forall M F L L' τs1 τs2 es,
          let F' := F <| fc_labels ::= cons (τs2, L') |> in
          let ψ := InstrT τs1 τs2 in
          P2 M F' L es ψ L' ->
          has_instruction_type_ok F ψ L' ->
          P1 M F L (IBlock ψ L' es) ψ L')
      (HLoop : forall M F L τs1 τs2 es,
          let F' := F <| fc_labels ::= cons (τs1, L) |> in
          let ψ := InstrT τs1 τs2 in
          P2 M F' L es ψ L ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (ILoop ψ es) ψ L)
      (HIte : forall M F L L' τs1 τs2 es1 es2,
          P2 M F L es1 (InstrT τs1 τs2) L' ->
          P2 M F L es2 (InstrT τs1 τs2) L' ->
          let ψ := InstrT (τs1 ++ [type_i32]) τs2 in
          has_instruction_type_ok F ψ L' ->
          P1 M F L (IIte ψ L' es1 es2) ψ L')
      (HBr : forall M F L L' i τs τs1 τs2,
          let ψ := InstrT (τs1 ++ τs) τs2 in
          F.(fc_labels) !! i = Some (τs, L) ->
          Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
          has_instruction_type_ok F ψ L' ->
          P1 M F L (IBr ψ i) ψ L')
      (HReturn : forall M F L L' τs τs1 τs2,
          let ψ := InstrT (τs1 ++ τs) τs2 in
          F.(fc_return) = τs ->
          Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
          has_instruction_type_ok F ψ L' ->
          P1 M F L (IReturn ψ) ψ L')
      (HLocalGet : forall M F L i τ ιs,
          let ψ := InstrT [] [τ] in
          let ρ := ProdR (map PrimR ιs) in
          let τ' := RepT (VALTYPE ρ ImCopy ImDrop) ρ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []) in
          let L' := <[ i := τ' ]> L in
          F.(fc_locals) !! i = Some ιs ->
          L !! i = Some τ ->
          has_instruction_type_ok F ψ L' ->
          P1 M F L (ILocalGet ψ i) ψ L')
      (HLocalGetCopy : forall M F L i τ,
          let ψ := InstrT [] [τ] in
          L !! i = Some τ ->
          has_copyability F τ ImCopy ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (ILocalGet ψ i) ψ L)
      (HLocalSet : forall M F L i τ τ' ιs,
          let ψ := InstrT [τ'] [] in
          let L' := <[ i := τ' ]> L in
          L !! i = Some τ ->
          has_dropability F τ ImDrop ->
          F.(fc_locals) !! i = Some ιs ->
          type_rep_eval F τ' ιs ->
          has_instruction_type_ok F ψ L' ->
          P1 M F L (ILocalSet ψ i) ψ L')
      (HGlobalGet : forall M F L i ω τ,
          let ψ := InstrT [] [τ] in
          M.(mc_globals) !! i = Some (ω, τ) ->
          has_copyability F τ ImCopy ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (IGlobalGet ψ i) ψ L)
      (HGlobalSet : forall M F L i τ,
          let ψ := InstrT [τ] [] in
          M.(mc_globals) !! i = Some (Mut, τ) ->
          has_dropability F τ ImDrop ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (IGlobalSet ψ i) ψ L)
      (HGlobalSwap : forall M F L i τ,
          let ψ := InstrT [τ] [τ] in
          M.(mc_globals) !! i = Some (Mut, τ) ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (IGlobalSwap ψ i) ψ L)
      (HCodeRef : forall M F L i ϕ,
          let τ := CodeRefT (VALTYPE (PrimR I32R) ImCopy ImDrop) ϕ in
          let ψ := InstrT [] [τ] in
          M.(mc_table) !! i = Some ϕ ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (ICodeRef ψ i) ψ L)
      (HInst : forall M F L ix ϕ ϕ',
          let κ := VALTYPE (PrimR I32R) ImCopy ImDrop in
          let ψ := InstrT [CodeRefT κ ϕ] [CodeRefT κ ϕ'] in
          function_type_inst F ix ϕ ϕ' ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (IInst ψ ix) ψ L)
      (HCall : forall M F L i ixs ϕ τs1 τs2,
          let ψ := InstrT τs1 τs2 in
          M.(mc_functions) !! i = Some ϕ ->
          function_type_insts F ixs ϕ (MonoFunT τs1 τs2) ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (ICall ψ i ixs) ψ L)
      (HCallIndirect : forall M F L τs1 τs2,
          let κ := VALTYPE (PrimR I32R) ImCopy ImDrop in
          let ψ := InstrT (τs1 ++ [CodeRefT κ (MonoFunT τs1 τs2)]) τs2 in
          has_instruction_type_ok F ψ L ->
          P1 M F L (ICallIndirect ψ) ψ L)
      (HInject : forall M F L i τ τs κ,
          let ψ := InstrT [τ] [SumT κ τs] in
          τs !! i = Some τ ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (IInject ψ i) ψ L)
      (HCase : forall M F L L' κ τ' τs ess,
          let ψ := InstrT [SumT κ τs] [τ'] in
          Forall2 (fun τ es => P2 M F L es (InstrT [τ] [τ']) L') τs ess ->
          has_instruction_type_ok F ψ L' ->
          P1 M F L (ICase ψ L' ess) ψ L')
      (HGroup : forall M F L τs κ,
          let ψ := InstrT τs [ProdT κ τs] in
          has_instruction_type_ok F ψ L ->
          P1 M F L (IGroup ψ) ψ L)
      (HUngroup : forall M F L τs κ,
          let ψ := InstrT [ProdT κ τs] τs in
          has_instruction_type_ok F ψ L ->
          P1 M F L (IUngroup ψ) ψ L)
      (HFold : forall M F L τ κ,
          let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
          let ψ := InstrT [τ0] [RecT κ τ] in
          has_instruction_type_ok F ψ L ->
          P1 M F L (IFold ψ) ψ L)
      (HUnfold : forall M F L τ κ,
          let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
          let ψ := InstrT [RecT κ τ] [τ0] in
          has_instruction_type_ok F ψ L ->
          P1 M F L (IUnfold ψ) ψ L)
      (HPack : forall M F L τ τ',
          let ψ := InstrT [τ] [τ'] in
          packed_existential F τ τ' ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (IPack ψ) ψ L)
      (HUnpack : forall M F F0 L L' L0 L0' es es0 ψ ψ0,
          unpacked_existential F L es ψ L' F0 L0 es0 ψ0 L0' ->
          P2 M F0 L0 es0 ψ0 L0' ->
          has_instruction_type_ok F ψ L' ->
          P1 M F L (IUnpack ψ L' es) ψ L')
      (HWrap : forall M F L ρ ιs0 ιs τ0 κ,
          let ψ := InstrT [τ0] [RepT κ ρ τ0] in
          type_rep_eval F τ0 ιs0 ->
          eval_rep ρ = Some ιs ->
          convertible_to ιs0 ιs ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (IWrap ψ) ψ L)
      (HUnwrap : forall M F L ρ ιs0 ιs τ0 κ,
          let ψ := InstrT [RepT κ ρ τ0] [τ0] in
          type_rep_eval F τ0 ιs0 ->
          eval_rep ρ = Some ιs ->
          convertible_to ιs0 ιs ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (IUnwrap ψ) ψ L)
      (HTag : forall M F L,
          let ψ := InstrT [type_i32] [type_i31] in
          has_instruction_type_ok F ψ L ->
          P1 M F L (ITag ψ) ψ L)
      (HUntag : forall M F L,
          let ψ := InstrT [type_i31] [type_i32] in
          has_instruction_type_ok F ψ L ->
          P1 M F L (IUntag ψ) ψ L)
      (HRefNew : forall M F L μ τ τ' κ,
          let ψ := InstrT [τ] [RefT κ μ τ'] in
          mono_mem μ ->
          stores_as F τ τ' ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (IRefNew ψ) ψ L)
      (HRefLoad : forall M F L π μ τ τval pr κ,
          let ψ := InstrT [RefT κ μ τ] [RefT κ μ τ; τval] in
          resolve_path τ π None pr ->
          has_copyability F pr.(pr_target) ImCopy ->
          loads_as F pr.(pr_target) τval ->
          Forall (mono_size F) pr.(pr_prefix) ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (IRefLoad ψ π) ψ L)
      (HRefStore : forall M F L π μ τ τval pr κ,
          let ψ := InstrT [RefT κ μ τ; τval] [τ] in
          resolve_path τ π None pr ->
          has_dropability F pr.(pr_target) ImDrop ->
          stores_as F τval pr.(pr_target) ->
          Forall (mono_size F) pr.(pr_prefix) ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (IRefStore ψ π) ψ L)
      (HRefMMStore : forall M F L π τ τval τmem pr κ κ',
          let ψ := InstrT [RefT κ (ConstM MemMM) τ; τval] [RefT κ' (ConstM MemMM) pr.(pr_replaced)] in
          stores_as F τval τmem ->
          resolve_path τ π (Some τmem) pr ->
          has_dropability F pr.(pr_target) ImDrop ->
          type_size_eq F pr.(pr_target) τmem ->
          Forall (mono_size F) pr.(pr_prefix) ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (IRefStore ψ π) ψ L)
      (HRefSwap : forall M F L π τ τval pr κ μ,
          let ψ := InstrT [RefT κ μ τ; τval] [RefT κ μ τ; τval] in
          resolve_path τ π None pr ->
          Forall (mono_size F) pr.(pr_prefix) ->
          loads_as F τval pr.(pr_target) ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (IRefSwap ψ π) ψ L)
      (HRefMMSwap : forall M F L π τ τval τval' τmem κ κ' pr,
          let ψ :=
            InstrT [RefT κ (ConstM MemMM) τ; τval'] [RefT κ' (ConstM MemMM) pr.(pr_replaced); τval]
          in
          stores_as F τval τmem ->
          resolve_path τ π (Some τmem) pr ->
          Forall (mono_size F) pr.(pr_prefix) ->
          loads_as F pr.(pr_target) τval ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (IRefSwap ψ π) ψ L)
      (HNil : forall M F L,
          local_ctx_ok F L ->
          P2 M F L [] (InstrT [] []) L)
      (HCons : forall M F L1 L2 L3 e es τs1 τs2 τs3,
          P1 M F L1 e (InstrT τs1 τs2) L2 ->
          P2 M F L2 es (InstrT τs2 τs3) L3 ->
          P2 M F L1 (e :: es) (InstrT τs1 τs3) L3)
      (HFrame : forall M F L L' es τ τs1 τs2,
          has_mono_rep F τ ->
          P2 M F L es (InstrT τs1 τs2) L' ->
          P2 M F L es (InstrT (τ :: τs1) (τ :: τs2)) L').

  Fixpoint has_instruction_type_mind
    (M : module_ctx) (F : function_ctx) (L : local_ctx)
    (e : instruction)
    (ψ : instruction_type) (L' : local_ctx)
    (H : has_instruction_type M F L e ψ L') :
    P1 M F L e ψ L' :=
    match H with
    | TNop M F L H1 => HNop M F L H1
    | TUnreachable M F L L' ψ H1 => HUnreachable M F L L' ψ H1
    | TCopy M F L τ H1 H2 => HCopy M F L τ H1 H2
    | TDrop M F L τ H1 H2 => HDrop M F L τ H1 H2
    | TNum M F L e ψ H1 H2 => HNum M F L e ψ H1 H2
    | TNumConst M F L κ ν n H1 => HNumConst M F L κ ν n H1
    | TBlock M F L L' τs1 τs2 es H1 H2 =>
        HBlock M F L L' τs1 τs2 es (have_instruction_type_mind _ _ _ _ _ _ H1) H2
    | TLoop M F L τs1 τs2 es H1 H2 =>
        HLoop M F L τs1 τs2 es (have_instruction_type_mind _ _ _ _ _ _ H1) H2
    | TIte M F L L' τs1 τs2 es1 es2 H1 H2 H3 =>
        HIte M F L L' τs1 τs2 es1 es2
          (have_instruction_type_mind _ _ _ _ _ _ H1)
          (have_instruction_type_mind _ _ _ _ _ _ H2)
          H3
    | TBr M F L L' i τs τs1 τs2 H1 H2 H3 => HBr M F L L' i τs τs1 τs2 H1 H2 H3
    | TReturn M F L L' τs τs1 τs2 H1 H2 H3 => HReturn M F L L' τs τs1 τs2 H1 H2 H3
    | TLocalGet M F L i τ ιs H1 H2 H3 => HLocalGet M F L i τ ιs H1 H2 H3
    | TLocalGetCopy M F L i τ H1 H2 H3 => HLocalGetCopy M F L i τ H1 H2 H3
    | TLocalSet M F L i τ τ' ιs H1 H2 H3 H4 H5 => HLocalSet M F L i τ τ' ιs H1 H2 H3 H4 H5
    | TGlobalGet M F L i ω τ H1 H2 H3 => HGlobalGet M F L i ω τ H1 H2 H3
    | TGlobalSet M F L i τ H1 H2 H3 => HGlobalSet M F L i τ H1 H2 H3
    | TGlobalSwap M F L i τ H1 H2 => HGlobalSwap M F L i τ H1 H2
    | TCodeRef M F L i ϕ H1 H2 => HCodeRef M F L i ϕ H1 H2
    | TInst M F L ix ϕ ϕ' H1 H2 => HInst M F L ix ϕ ϕ' H1 H2
    | TCall M F L i ixs ϕ τs1 τs2 H1 H2 H3 => HCall M F L i ixs ϕ τs1 τs2 H1 H2 H3
    | TCallIndirect M F L τs1 τs2 H1 => HCallIndirect M F L τs1 τs2 H1
    | TInject M F L i τ τs κ H1 H2 => HInject M F L i τ τs κ H1 H2
    | TCase M F L L' κ τ' τs ess H1 H2 =>
        HCase M F L L' κ τ' τs ess
          (Forall2_impl _ _ _ _ H1 (fun τ es => have_instruction_type_mind _ _ _ _ _ _))
          H2
    | TGroup M F L τs κ H1 => HGroup M F L τs κ H1
    | TUngroup M F L τs κ H1 => HUngroup M F L τs κ H1
    | TFold M F L τs κ H1 => HFold M F L τs κ H1
    | TUnfold M F L τ κ H1 => HUnfold M F L τ κ H1
    | TPack M F L τ τ' H1 H2 => HPack M F L τ τ' H1 H2
    | TUnpack M F F0 L L' L0 L0' es es0 ψ ψ0 H1 H2 H3 =>
        HUnpack M F F0 L L' L0 L0' es es0 ψ ψ0 H1 (have_instruction_type_mind _ _ _ _ _ _ H2) H3
    | TWrap M F L ρ ιs0 ιs τ0 κ H1 H2 H3 H4 => HWrap M F L ρ ιs0 ιs τ0 κ H1 H2 H3 H4
    | TUnwrap M F L ρ ιs0 ιs τ0 κ H1 H2 H3 H4 => HUnwrap M F L ρ ιs0 ιs τ0 κ H1 H2 H3 H4
    | TTag M F L H1 => HTag M F L H1
    | TUntag M F L H1 => HUntag M F L H1
    | TRefNew M F L μ τ τ' κ H1 H2 H3 => HRefNew M F L μ τ τ' κ H1 H2 H3
    | TRefLoad M F L π μ τ τval pr κ H1 H2 H3 H4 H5 => HRefLoad M F L π μ τ τval pr κ H1 H2 H3 H4 H5
    | TRefStore M F L π μ τ τval pr κ H1 H2 H3 H4 H5 => HRefStore M F L π μ τ τval pr κ H1 H2 H3 H4 H5
    | TRefMMStore M F L π τ τval τmem pr κ κ' H1 H2 H3 H4 H5 H6 =>
        HRefMMStore M F L π τ τval τmem pr κ κ' H1 H2 H3 H4 H5 H6
    | TRefSwap M F L π τ τval pr κ μ H1 H2 H3 H4 => HRefSwap M F L π τ τval pr κ μ H1 H2 H3 H4
    | TRefMMSwap M F L π τ τval τval' τmem κ κ' pr H1 H2 H3 H4 H5 =>
        HRefMMSwap M F L π τ τval τval' τmem κ κ' pr H1 H2 H3 H4 H5
    end

  with have_instruction_type_mind
    (M : module_ctx) (F : function_ctx) (L : local_ctx)
    (es : list instruction)
    (ψ : instruction_type) (L' : local_ctx)
    (H : have_instruction_type M F L es ψ L') :
    P2 M F L es ψ L' :=
    match H with
    | TNil M F L H1 => HNil M F L H1
    | TCons M F L1 L2 L3 e es τs1 τs2 τs3 H1 H2 =>
        HCons M F L1 L2 L3 e es τs1 τs2 τs3
          (has_instruction_type_mind _ _ _ _ _ _ H1)
          (have_instruction_type_mind _ _ _ _ _ _ H2)
    | TFrame M F L L' es τ τs1 τs2 H1 H2 =>
       HFrame M F L L' es τ τs1 τs2 H1 (have_instruction_type_mind _ _ _ _ _ _ H2)
    end.

End HasHaveInstructionTypeMind.

Lemma kind_ok_subkind_of F κ κ' : kind_ok F κ -> subkind_of κ κ' -> kind_ok F κ'.
Proof.
  intros H1 H2.
  induction H2; repeat constructor; by inversion H1.
Qed.

Lemma has_kind_inv F τ κ : has_kind F τ κ -> has_kind_ok F τ κ.
Proof.
  intros H.
  induction H using has_kind_ind'.
  { destruct IHhas_kind as [F τ κ H1 H2].
    by apply (kind_ok_subkind_of _ _ _ H2) in H. }
  { constructor; last done. by apply OKVarT with (κ := κ). }
  all: repeat constructor.
  all: try inversion IHhas_kind.
  all: try done.
  all: try by inversion H0.
  all: try by inversion H1.
  - eapply Forall2_Forall_r in H; first exact H. apply Forall_forall.
    intros. inversion H1. by inversion H3.
  - eapply Forall2_Forall_l in H; first exact H. apply Forall_forall.
    intros. inversion H1. by inversion H3.
  - eapply Forall2_Forall_r in H; first exact H. apply Forall_forall.
    intros. inversion H1. by inversion H3.
  - eapply Forall2_Forall_l in H0; first exact H0. apply Forall_forall.
    intros. by inversion H2.
  - eapply Forall2_Forall_r in H0; first exact H0. apply Forall_forall.
    intros. inversion H2. inversion H4. by inversion H11.
  - eapply Forall2_Forall_l in H0; first exact H0. apply Forall_forall.
    intros. by inversion H2.
  - eapply Forall2_Forall_r in H0; first exact H0. apply Forall_forall.
    intros. inversion H2. inversion H4. by inversion H11.
  - eapply Forall2_Forall_r in H; first exact H. apply Forall_forall.
    intros. inversion H1. by inversion H3.
  - eapply Forall2_Forall_l in H; first exact H. apply Forall_forall.
    intros. by inversion H1.
  - eapply Forall2_Forall_r in H; first exact H. apply Forall_forall.
    intros. inversion H1. by inversion H3.
  - eapply Forall2_Forall_l in H0; first exact H0. apply Forall_forall.
    intros. by inversion H2.
  - eapply Forall2_Forall_r in H0; first exact H0. apply Forall_forall.
    intros. inversion H2. inversion H4. by inversion H11.
  - eapply Forall2_Forall_l in H0; first exact H0. apply Forall_forall.
    intros. by inversion H2.
  - eapply Forall2_Forall_r in H0; first exact H0. apply Forall_forall.
    intros. inversion H2. inversion H4. by inversion H11.
Qed.

Lemma have_instruction_type_inv M F L e ψ L' :
  have_instruction_type M F L e ψ L' -> has_instruction_type_ok F ψ L'.
Proof.
  intros H.
  induction H using have_instruction_type_mind with
    (P1 := fun _ F _ _ ψ L' => has_instruction_type_ok F ψ L');
    try assumption; repeat constructor; try assumption.
  - inversion IHhave_instruction_type. by inversion H.
  - inversion IHhave_instruction_type0. by inversion H.
  - by inversion IHhave_instruction_type0.
  - inversion IHhave_instruction_type. by inversion H0.
  - inversion IHhave_instruction_type. by inversion H0.
  - by inversion IHhave_instruction_type.
Qed.
