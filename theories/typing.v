From Stdlib Require Import List.
Import ListNotations.

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
    fc_locals : list representation;
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
     fc_locals := map (subst_representation s__rep) F.(fc_locals);
     fc_labels :=
       map
         (fun '(τs, L) =>
            (map (subst_type s__mem s__rep s__size s__type) τs, map (subst_type s__mem s__rep s__size s__type) L))
         F.(fc_labels);
     fc_kind_ctx := F.(fc_kind_ctx);
     fc_type_vars := map (subst_kind s__mem s__rep s__size) F.(fc_type_vars) |}.

Global Instance eta_function_ctx : Settable _ :=
  settable! Build_function_ctx
  <fc_return; fc_locals; fc_labels; fc_kind_ctx; fc_type_vars>.

Definition update_locals (ξ : local_fx) (L : local_ctx) : local_ctx :=
  let 'LocalFx l := ξ in
  fold_left (fun acc '(i, τ) => <[ i := τ ]> acc) l L.

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

with instruction_type_ok : function_ctx -> instruction_type -> Prop :=
| OKInstrT F τs1 τs2 :
  Forall (type_ok F) τs1 ->
  Forall (type_ok F) τs2 ->
  instruction_type_ok F (InstrT τs1 τs2)

with function_type_ok : function_ctx -> function_type -> Prop :=
| OKMonoFunT F ψ :
  instruction_type_ok F ψ ->
  function_type_ok F (MonoFunT ψ)
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

Inductive rep_eq : representation -> representation -> Prop :=
| RepEq ρ1 ρ2 ιs :
  eval_rep ρ1 = Some ιs ->
  eval_rep ρ2 = Some ιs ->
  rep_eq ρ1 ρ2.

Definition type_rep_eq (F : function_ctx) (τ : type) (ρ : representation) : Prop :=
  exists ρ', has_rep F τ ρ' /\ rep_eq ρ ρ'.

Inductive size_eq : size -> size -> Prop :=
| SizeEq σ1 σ2 n :
  eval_size σ1 = Some n ->
  eval_size σ2 = Some n ->
  size_eq σ1 σ2.

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

Inductive convertible_to : list primitive_rep -> list primitive_rep -> Prop :=
| ConvertPad ιs2 :
  convertible_to [] ιs2
| ConvertNoPtrs ιs1 ιs1' ιs2 ιs2' :
  PtrR ∉ ιs1 ->
  list_sum (map primitive_size ιs1) = list_sum (map primitive_size ιs2) ->
  convertible_to ιs1' ιs2' ->
  convertible_to (ιs1 ++ ιs1') (ιs2 ++ ιs2')
| ConvertPtr ιs1 ιs2 :
  convertible_to (PtrR :: ιs1) (PtrR :: ιs2).

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
| UnpackMem F L es τs1 κ τ τs2 L' :
  let F0 := subst_function_ctx (up_memory VarM) VarR VarS VarT F
              <| fc_kind_ctx ::= set kc_mem_vars S |> in
  let es0 := map (subst_instruction (up_memory VarM) VarR VarS VarT) es in
  let up := map (subst_type (up_memory VarM) VarR VarS VarT) in
  unpacked_existential
    F L es (InstrT (τs1 ++ [ExistsMemT κ τ]) τs2) L'
    F0 (up L) es0 (InstrT (up τs1 ++ [τ]) (up τs2)) (up L')
| UnpackRep F L es τs1 κ τ τs2 L' :
  let F0 := subst_function_ctx VarM (up_representation VarR) VarS VarT F
              <| fc_kind_ctx ::= set kc_rep_vars S |> in
  let es0 := map (subst_instruction VarM (up_representation VarR) VarS VarT) es in
  let up := map (subst_type VarM (up_representation VarR) VarS VarT) in
  unpacked_existential
    F L es (InstrT (τs1 ++ [ExistsRepT κ τ]) τs2) L'
    F0 (up L) es0 (InstrT (up τs1 ++ [τ]) (up τs2)) (up L')
| UnpackSize F L es τs1 κ τ τs2 L' :
  let F0 := subst_function_ctx VarM VarR (up_size VarS) VarT F
              <| fc_kind_ctx ::= set kc_size_vars S |> in
  let es0 := map (subst_instruction VarM VarR (up_size VarS) VarT) es in
  let up := map (subst_type VarM VarR (up_size VarS) VarT) in
  unpacked_existential
    F L es (InstrT (τs1 ++ [ExistsSizeT κ τ]) τs2) L'
    F0 (up L) es0 (InstrT (up τs1 ++ [τ]) (up τs2)) (up L')
| UnpackType F L es τs1 κ κ0 τ τs2 L' :
  let F0 := subst_function_ctx VarM VarR VarS (up_type VarT) F <| fc_type_vars ::= cons κ0 |> in
  let es0 := map (subst_instruction VarM VarR VarS (up_type VarT)) es in
  let up := map (subst_type VarM VarR VarS (up_type VarT)) in
  unpacked_existential
    F L es (InstrT (τs1 ++ [ExistsTypeT κ κ0 τ]) τs2) L'
    F0 (up L) es0 (InstrT (up τs1 ++ [τ]) (up τs2)) (up L').

Definition local_ctx_ok (F : function_ctx) (L : local_ctx) : Prop :=
  Forall2 (type_rep_eq F) L F.(fc_locals).

Definition local_fx_ok (F : function_ctx) '(LocalFx ξ : local_fx) : Prop :=
  Forall (fun '(i, τ) => exists ρ, F.(fc_locals) !! i = Some ρ /\ type_rep_eq F τ ρ) ξ.

Inductive has_instruction_type_ok : function_ctx -> local_ctx -> instruction_type -> local_ctx -> Prop :=
| OKHasInstructionType F L ψ L' :
  local_ctx_ok F L ->
  local_ctx_ok F L' ->
  has_mono_rep_instr F ψ ->
  has_instruction_type_ok F L ψ L'.

Inductive has_instruction_type_num : num_instruction -> instruction_type -> Prop :=
| TInt1 νi op :
  let τ := int_type_type νi in
  has_instruction_type_num (IInt1 νi op) (InstrT [τ] [τ])
| TInt2 νi op :
  let τ := int_type_type νi in
  has_instruction_type_num (IInt2 νi op) (InstrT [τ; τ] [τ])
| TIntTest νi op :
  let τ := int_type_type νi in
  let τ_i32 := int_type_type I32T in
  has_instruction_type_num (IIntTest νi op) (InstrT [τ] [τ_i32])
| TIntRel νi op :
  let τ := int_type_type νi in
  let τ_i32 := int_type_type I32T in
  has_instruction_type_num (IIntRel νi op) (InstrT [τ; τ] [τ_i32])
| IFloat1 νf op :
  let τ := float_type_type νf in
  has_instruction_type_num (IFloat1 νf op) (InstrT [τ] [τ])
| IFloat2 νf op :
  let τ := float_type_type νf in
  has_instruction_type_num (IFloat2 νf op) (InstrT [τ; τ] [τ])
| IFloatRel νf op :
  let τ := float_type_type νf in
  let τ_i32 := int_type_type I32T in
  has_instruction_type_num (IFloatRel νf op) (InstrT [τ; τ] [τ_i32]).

Inductive has_instruction_type :
  module_ctx -> function_ctx -> local_ctx -> instruction -> instruction_type -> local_ctx -> Prop :=
| TNop M F L :
  local_ctx_ok F L ->
  let ψ := InstrT [] [] in
  has_instruction_type M F L (INop ψ) ψ L
| TUnreachable M F L ψ L' :
  has_instruction_type_ok F L ψ L' ->
  has_instruction_type M F L (IUnreachable ψ) ψ L'
| TCopy M F L τ :
  local_ctx_ok F L ->
  has_copyability F τ ExCopy ->
  has_mono_rep F τ ->
  let ψ := InstrT [τ] [τ; τ] in
  has_instruction_type M F L (ICopy ψ) ψ L
| TDrop M F L τ :
  local_ctx_ok F L ->
  has_dropability F τ ExDrop ->
  has_mono_rep F τ ->
  let ψ := InstrT [τ] [] in
  has_instruction_type M F L (IDrop ψ) ψ L
| TNum M F L e ψ :
  local_ctx_ok F L ->
  has_instruction_type_num e ψ ->
  has_instruction_type M F L (INum ψ e) ψ L
| TNumConst M F L κ ν n :
  local_ctx_ok F L ->
  has_kind F (NumT κ ν) κ ->
  let ψ := InstrT [] [NumT κ ν] in
  has_instruction_type M F L (INumConst ψ n) ψ L
| TBlock M F L τs1 τs2 ξ es :
  local_ctx_ok F L ->
  local_fx_ok F ξ ->
  let L' := update_locals ξ L in
  let F' := F <| fc_labels ::= cons (τs2, L') |> in
  let ψ := InstrT τs1 τs2 in
  has_mono_rep_instr F ψ ->
  have_instruction_type M F' L es ψ L' ->
  has_instruction_type M F L (IBlock ψ ξ es) ψ L'
| TLoop M F L τs1 τs2 es :
  local_ctx_ok F L ->
  let F' := F <| fc_labels ::= cons (τs1, L) |> in
  let ψ := InstrT τs1 τs2 in
  has_mono_rep_instr F ψ ->
  have_instruction_type M F' L es ψ L ->
  has_instruction_type M F L (ILoop ψ es) ψ L
| TIte M F L ψ ξ es1 es2 :
  local_ctx_ok F L ->
  local_fx_ok F ξ ->
  has_mono_rep_instr F ψ ->
  let L' := update_locals ξ L in
  have_instruction_type M F L es1 ψ L' ->
  have_instruction_type M F L es2 ψ L' ->
  has_instruction_type M F L (IIte ψ ξ es1 es2) ψ L'
| TBr M F L n τs τs1 τs2 L' :
  local_ctx_ok F L ->
  local_ctx_ok F L' ->
  F.(fc_labels) !! n = Some (τs, L) ->
  Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
  let ψ := InstrT (τs1 ++ τs) τs2 in
  has_mono_rep_instr F ψ ->
  has_instruction_type M F L (IBr ψ n) ψ L'
| TReturn M F L L' τs τs1 τs2 :
  local_ctx_ok F L ->
  local_ctx_ok F L' ->
  F.(fc_return) = τs ->
  Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
  let ψ := InstrT (τs1 ++ τs) τs2 in
  has_mono_rep_instr F ψ ->
  has_instruction_type M F L (IReturn ψ) ψ L'
| TLocalGet M F L n τ ρ :
  local_ctx_ok F L ->
  F.(fc_locals) !! n = Some ρ ->
  mono_rep ρ ->
  L !! n = Some τ ->
  let τ' := RepT (VALTYPE ρ ImCopy ImDrop) ρ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []) in
  let L' := <[ n := τ' ]> L in
  let ψ := InstrT [] [τ] in
  has_instruction_type M F L (ILocalGet ψ n) ψ L'
| TLocalGetCopy M F L n τ :
  local_ctx_ok F L ->
  L !! n = Some τ ->
  has_copyability F τ ImCopy ->
  let ψ := InstrT [] [τ] in
  has_instruction_type M F L (ILocalGet ψ n) ψ L
| TLocalSet M F L n τ τ' ρ :
  local_ctx_ok F L ->
  F.(fc_locals) !! n = Some ρ ->
  L !! n = Some τ ->
  has_dropability F τ ImDrop ->
  type_rep_eq F τ' ρ ->
  let L' := <[ n := τ' ]> L in
  let ψ := InstrT [τ'] [] in
  has_instruction_type M F L (ILocalSet ψ n) ψ L'
| TGlobalGet M F L n m τ :
  local_ctx_ok F L ->
  M.(mc_globals) !! n = Some (m, τ) ->
  has_mono_rep F τ ->
  has_copyability F τ ImCopy ->
  let ψ := InstrT [] [τ] in
  has_instruction_type M F L (IGlobalGet ψ n) ψ L
| TGlobalSet M F L n τ :
  local_ctx_ok F L ->
  M.(mc_globals) !! n = Some (Mut, τ) ->
  has_mono_rep F τ ->
  has_dropability F τ ImDrop ->
  let ψ := InstrT [τ] [] in
  has_instruction_type M F L (IGlobalSet ψ n) ψ L
| TGlobalSwap M F L n τ :
  local_ctx_ok F L ->
  M.(mc_globals) !! n = Some (Mut, τ) ->
  has_mono_rep F τ ->
  let ψ := InstrT [τ] [τ] in
  has_instruction_type M F L (IGlobalSwap ψ n) ψ L
| TCodeRef M F L i ϕ :
  local_ctx_ok F L ->
  M.(mc_table) !! i = Some ϕ ->
  function_type_ok F ϕ ->
  let τ := CodeRefT (VALTYPE (PrimR I32R) ImCopy ImDrop) ϕ in
  let ψ := InstrT [] [τ] in
  has_instruction_type M F L (ICodeRef ψ i) ψ L
| TInst M F L ix ϕ ϕ' :
  local_ctx_ok F L ->
  function_type_ok F ϕ ->
  function_type_inst F ix ϕ ϕ' ->
  let κ := VALTYPE (PrimR I32R) ImCopy ImDrop in
  let ψ := InstrT [CodeRefT κ ϕ] [CodeRefT κ ϕ'] in
  has_instruction_type M F L (IInst ψ ix) ψ L
| TCall M F L i ixs ϕ τs1 τs2 :
  local_ctx_ok F L ->
  M.(mc_functions) !! i = Some ϕ ->
  let ψ := InstrT τs1 τs2 in
  has_mono_rep_instr F ψ ->
  function_type_insts F ixs ϕ (MonoFunT ψ) ->
  has_instruction_type M F L (ICall ψ i ixs) ψ L
| TCallIndirect M F L τs1 τs2 :
  local_ctx_ok F L ->
  Forall (has_mono_rep F) τs1 ->
  Forall (has_mono_rep F) τs2 ->
  let κ := VALTYPE (PrimR I32R) ImCopy ImDrop in
  let ψ := InstrT (τs1 ++ [CodeRefT κ (MonoFunT (InstrT τs1 τs2))]) τs2 in
  has_instruction_type M F L (ICallIndirect ψ) ψ L
| TInject M F L i τ τs κ :
  local_ctx_ok F L ->
  τs !! i = Some τ ->
  has_kind F (SumT κ τs) κ ->
  Forall (has_mono_rep F) τs ->
  let ψ := InstrT [τ] [SumT κ τs] in
  has_instruction_type M F L (IInject ψ i) ψ L
| TCase M F L ξ κ τ' τs ess :
  let L' := update_locals ξ L in
  Forall2 (fun τ es => have_instruction_type M F L es (InstrT [τ] [τ']) L') τs ess ->
  let ψ := InstrT [SumT κ τs] [τ'] in
  has_instruction_type M F L (ICase ψ ξ ess) ψ L'
| TGroup M F L τs ρs χ δ :
  Forall2 (λ τ ρ, has_kind F τ (VALTYPE ρ χ δ)) τs ρs ->
  let τ := ProdT (VALTYPE (ProdR ρs) χ δ) τs in
  let ψ := InstrT τs [τ] in
  has_instruction_type M F L (IGroup ψ) ψ L
| TUngroup M F L τs κ :
  let τ := ProdT κ τs in
  let ψ := InstrT [τ] τs in
  has_instruction_type M F L (IUngroup ψ) ψ L
| TFold M F L τ κ :
  has_kind F (RecT κ τ) κ ->
  let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
  let ψ := InstrT [τ0] [RecT κ τ] in
  has_instruction_type M F L (IFold ψ) ψ L
| TUnfold M F L τ κ :
  has_kind F (RecT κ τ) κ ->
  let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
  let ψ := InstrT [RecT κ τ] [τ0] in
  has_instruction_type M F L (IUnfold ψ) ψ L
| TPack M F L τ τ' :
  packed_existential F τ τ' ->
  let ψ := InstrT [τ] [τ'] in
  has_instruction_type M F L (IPack ψ) ψ L
| TUnpack M F F0 L L0 ξ es es0 ψ ψ0 L0' :
  let L' := update_locals ξ L in
  unpacked_existential F L es ψ L'
                       F0 L0 es0 ψ0 L0' ->
  have_instruction_type M F0 L0 es0 ψ0 L0' ->
  has_instruction_type M F L (IUnpack ψ ξ es) ψ L'
| TWrap M F L ρ0 ρ ιs0 ιs τ0 χ δ :
  has_kind F τ0 (VALTYPE ρ0 χ δ) ->
  eval_rep ρ0 = Some ιs0 ->
  eval_rep ρ = Some ιs ->
  convertible_to ιs0 ιs ->
  let τ := RepT (VALTYPE ρ χ δ) ρ τ0 in
  let ψ := InstrT [τ0] [τ] in
  has_instruction_type M F L (IWrap ψ) ψ L
| TUnwrap M F L ρ0 ρ ιs0 ιs τ0 χ δ :
  has_kind F τ0 (VALTYPE ρ0 χ δ) ->
  eval_rep ρ0 = Some ιs0 ->
  eval_rep ρ = Some ιs ->
  convertible_to ιs0 ιs ->
  let τ := RepT (VALTYPE ρ χ δ) ρ τ0 in
  let ψ := InstrT [τ] [τ0] in
  has_instruction_type M F L (IUnwrap ψ) ψ L
| TRefNew M F L μ τ τ' κ :
  mono_mem μ ->
  stores_as F τ τ' ->
  let τ_ref := RefT κ μ τ' in
  has_kind F τ κ ->
  let ψ := InstrT [τ] [τ_ref] in
  has_instruction_type M F L (IRefNew ψ) ψ L
| TRefLoad M F L π μ τ τ_val pr ρ δ κ :
  resolve_path τ π None pr ->
  Forall (mono_size F) pr.(pr_prefix) ->
  has_kind F pr.(pr_target) (VALTYPE ρ ImCopy δ) ->
  loads_as F pr.(pr_target) τ_val ->
  rep_ok kc_empty ρ ->
  let τ_ref := RefT κ μ τ in
  has_kind F τ_ref κ ->
  let ψ := InstrT [τ_ref] [τ_ref; τ_val] in
  has_instruction_type M F L (IRefLoad ψ π) ψ L
| TRefStore M F L π μ τ τ_val pr κ :
  resolve_path τ π None pr ->
  Forall (mono_size F) pr.(pr_prefix) ->
  has_dropability F pr.(pr_target) ImDrop ->
  stores_as F τ_val pr.(pr_target) ->
  let τ_ref := RefT κ μ τ in
  let ψ := InstrT [τ_ref; τ_val] [τ] in
  has_instruction_type M F L (IRefStore ψ π) ψ L
| TRefMMStore M F L π τ τ_val τ_val' pr κ κ' σ σ' δ :
  resolve_path τ π (Some τ_val') pr ->
  Forall (mono_size F) pr.(pr_prefix) ->
  stores_as F τ_val τ_val' ->
  has_kind F pr.(pr_target) (MEMTYPE (Sized σ) (ConstM MemMM) ImDrop) ->
  has_kind F τ_val' (MEMTYPE (Sized σ') (ConstM MemMM) δ) ->
  size_eq σ σ' ->
  let τ_ref := RefT κ (ConstM MemMM) τ in
  let τ_ref' := RefT κ' (ConstM MemMM) pr.(pr_replaced) in
  has_kind F τ_ref κ ->
  has_kind F τ_ref' κ' ->
  let ψ := InstrT [τ_ref; τ_val] [τ_ref'] in
  has_instruction_type M F L (IRefStore ψ π) ψ L
| TRefSwap M F L π τ τ_val pr κ μ :
  resolve_path τ π None pr ->
  Forall (mono_size F) pr.(pr_prefix) ->
  loads_as F τ_val pr.(pr_target) ->
  let τ_ref := RefT κ μ τ in
  let ψ := InstrT [τ_ref; τ_val] [τ_ref; τ_val] in
  has_instruction_type M F L (IRefSwap ψ π) ψ L
| TRefMMSwap M F L π τ τ_val τ_val' τ__π κ κ' pr :
  resolve_path τ π (Some τ_val') pr ->
  Forall (mono_size F) pr.(pr_prefix) ->
  stores_as F τ_val τ_val' ->
  loads_as F pr.(pr_target) τ__π ->
  has_mono_rep F τ__π ->
  let τ_ref := RefT κ (ConstM MemMM) τ in
  let τ_ref' := RefT κ' (ConstM MemMM) pr.(pr_replaced) in
  has_kind F τ_ref κ ->
  has_kind F τ_ref' κ' ->
  let ψ := InstrT [τ_ref; τ_val] [τ_ref'; τ__π] in
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
  have_instruction_type M F L es (InstrT τs1 τs2) L' ->
  has_mono_rep F τ ->
  have_instruction_type M F L es (InstrT (τ :: τs1) (τ :: τs2)) L'.

Scheme has_instruction_type_mind := Induction for has_instruction_type Sort Prop
with have_instruction_type_mind := Induction for have_instruction_type Sort Prop.

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

Lemma int_type_type_mono_rep F νi : has_mono_rep F (int_type_type νi).
Proof.
  unfold int_type_type.
  destruct νi; (econstructor; [econstructor; constructor | reflexivity]).
Qed.

Lemma float_type_type_mono_rep F νf : has_mono_rep F (float_type_type νf).
Proof.
  unfold float_type_type.
  destruct νf; (econstructor; [econstructor; constructor | reflexivity]).
Qed.

Lemma has_instruction_type_num_inv F L e ψ :
  local_ctx_ok F L ->
  has_instruction_type_num e ψ ->
  has_instruction_type_ok F L ψ L.
Proof.
  intros H1 H2.
  inversion H2;
    constructor;
    try assumption;
    repeat constructor;
    try apply int_type_type_mono_rep;
    apply float_type_type_mono_rep.
Qed.

Lemma has_mono_rep_num F κ ν : has_kind F (NumT κ ν) κ -> has_mono_rep F (NumT κ ν).
Admitted.

Lemma update_local_ctx_ok F L i ρ τ :
  F.(fc_locals) !! i = Some ρ ->
  type_rep_eq F τ ρ ->
  local_ctx_ok F L ->
  local_ctx_ok F (<[ i := τ ]> L).
Admitted.

Lemma update_locals_ctx_ok F L ξ :
  local_ctx_ok F L ->
  local_fx_ok F ξ ->
  local_ctx_ok F (update_locals ξ L).
Admitted.

Lemma has_mono_rep_if_type_rep_eq F τ ρ : type_rep_eq F τ ρ -> has_mono_rep F τ.
Admitted.

Lemma mono_rep_ok K ρ : mono_rep ρ -> rep_ok K ρ.
Admitted.

Lemma mono_rep_type_ok F τ : has_mono_rep F τ -> type_ok F τ.
Admitted.

Lemma mono_rep_iff_eq_refl ρ : mono_rep ρ <-> rep_eq ρ ρ.
Admitted.

Lemma function_type_inst_ok  F ix ϕ ϕ' :
  function_type_ok F ϕ ->
  function_type_inst F ix ϕ ϕ' ->
  function_type_ok F ϕ'.
Admitted.

Lemma mono_rep_sum F κ τs :
  Forall (has_mono_rep F) τs ->
  has_kind F (SumT κ τs) κ ->
  has_mono_rep F (SumT κ τs).
Admitted.

Lemma have_instruction_type_inv M F L e ψ L' :
  have_instruction_type M F L e ψ L' -> has_instruction_type_ok F L ψ L'.
Proof.
  intros H.
  induction H using have_instruction_type_mind with
    (P := fun _ F L _ ψ L' _ => has_instruction_type_ok F L ψ L').
  - constructor.
    + assumption.
    + assumption.
    + constructor; constructor.
  - assumption.
  - constructor.
    + assumption.
    + assumption.
    + constructor.
      * constructor; last constructor. assumption.
      * constructor; last constructor; last constructor; assumption.
  - constructor.
    + assumption.
    + assumption.
    + constructor.
      * constructor; last constructor. assumption.
      * constructor.
  - by apply has_instruction_type_num_inv with (e := e).
  - constructor.
    + assumption.
    + assumption.
    + constructor.
      * constructor.
      * constructor; last constructor.
        by apply has_mono_rep_num.
  - constructor.
    + assumption.
    + by apply update_locals_ctx_ok.
    + assumption.
  - constructor.
    + assumption.
    + assumption.
    + assumption.
  - constructor.
    + assumption.
    + by apply update_locals_ctx_ok.
    + assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor.
    + assumption.
    + apply update_local_ctx_ok with (ρ := ρ).
      * assumption.
      * exists ρ. split.
        -- apply RepVALTYPE with (χ := ImCopy) (δ := ImDrop).
           apply KRep with (ρ0 := ProdR []); first repeat constructor.
           by apply mono_rep_ok.
        -- by apply mono_rep_iff_eq_refl.
      * assumption.
    + constructor; first constructor. constructor; last constructor.
      apply has_mono_rep_if_type_rep_eq with (ρ := ρ).
      apply Forall2_lookup_lr with (l := L) (k := F.(fc_locals)) (i := n); assumption.
  - constructor.
    + assumption.
    + assumption.
    + constructor; first constructor. constructor; last constructor.
      destruct (Forall2_lookup_l _ _ _ _ _ l e) as (ρ & Hρ & Hτ).
      by apply has_mono_rep_if_type_rep_eq with (ρ := ρ).
  - constructor.
    + assumption.
    + apply update_local_ctx_ok with (ρ := ρ); assumption.
    + constructor; last constructor. constructor; last constructor.
      by apply has_mono_rep_if_type_rep_eq with (ρ := ρ).
  - constructor.
    + assumption.
    + assumption.
    + constructor; first constructor. constructor; last constructor. assumption.
  - constructor.
    + assumption.
    + assumption.
    + constructor; last constructor. constructor; last constructor. assumption.
  - constructor.
    + assumption.
    + assumption.
    + constructor.
      * constructor; last constructor. assumption.
      * constructor; last constructor. assumption.
  - constructor.
    + assumption.
    + assumption.
    + constructor; first constructor. constructor; last constructor.
      apply MonoRep with (ρ := PrimR I32R) (ιs := [I32R]).
      * apply RepVALTYPE with (χ := ImCopy) (δ := ImDrop). constructor. assumption.
      * reflexivity.
  - constructor.
    + assumption.
    + assumption.
    + constructor.
      * constructor; last constructor.
        apply MonoRep with (ρ := PrimR I32R) (ιs := [I32R]).
        -- apply RepVALTYPE with (χ := ImCopy) (δ := ImDrop). constructor. assumption.
        -- reflexivity.
      * constructor; last constructor.
        apply MonoRep with (ρ := PrimR I32R) (ιs := [I32R]).
        -- apply RepVALTYPE with (χ := ImCopy) (δ := ImDrop). constructor.
           by eapply function_type_inst_ok.
        -- reflexivity.
  - constructor; assumption.
  - constructor.
    + assumption.
    + assumption.
    + constructor.
      * apply Forall_app. split.
        -- assumption.
        -- constructor; last constructor.
           apply MonoRep with (ρ := PrimR I32R) (ιs := [I32R]).
           ++ apply RepVALTYPE with (χ := ImCopy) (δ := ImDrop). repeat constructor.
              ** eapply Forall_impl; first exact f. intros τ H.
                 by apply mono_rep_type_ok.
              ** eapply Forall_impl; first exact f0. intros τ H.
                 by apply mono_rep_type_ok.
           ++ reflexivity.
      * assumption.
  - constructor.
    + assumption.
    + assumption.
    + constructor.
      * constructor; last constructor.
        by apply Forall_lookup_1 with (l := τs) (i := i).
      * constructor; last constructor.
        by apply mono_rep_sum.
Abort.
