From Coq Require Import List.
Import ListNotations.

Require Import RecordUpdate.RecordUpdate.

Require Import RichWasm.syntax.

Record function_context :=
  { fc_loc_vars : nat;
    fc_rep_vars : nat;
    fc_type_vars : list kind }.

Global Instance eta_function_context : Settable _ :=
  settable! Build_function_context <fc_loc_vars; fc_rep_vars; fc_type_vars>.

Inductive rep_ok : function_context -> representation -> Prop :=
| VarR_OK (F : function_context) (ϱ : variable) :
  ϱ < F.(fc_rep_vars) -> rep_ok F (VarR ϱ)
| SumR_OK (F : function_context) (rs : list representation) :
  Forall (rep_ok F) rs -> rep_ok F (SumR rs)
| ProdR_OK (F : function_context) (rs : list representation) :
  Forall (rep_ok F) rs -> rep_ok F (ProdR rs)
| PrimR_OK (F : function_context) (p : primitive_rep) :
  rep_ok F (PrimR p)
| DynR_OK (F : function_context) :
  rep_ok F DynR.

Inductive kind_ok : function_context -> kind -> Prop :=
| TYPE_OK (F : function_context) (r : representation) (l : linearity) (h : heapability) :
  rep_ok F r -> kind_ok F (TYPE r l h)
| CONSTRAINT_OK (F : function_context) (r : representation) :
  rep_ok F r -> kind_ok F (CONSTRAINT r).

Inductive has_mono_size : representation -> nat -> Prop :=
| SizeSumR (rs : list representation) (szs : list nat) :
  Forall2 has_mono_size rs szs ->
  (* TODO: Use the efficient packing size. *)
  has_mono_size (SumR rs) (list_sum szs)
| SizeProdR (rs : list representation) (szs : list nat) :
  Forall2 has_mono_size rs szs ->
  has_mono_size (ProdR rs) (list_sum szs)
| SizePtrR :
  has_mono_size (PrimR PtrR) 1
| SizeI32R :
  has_mono_size (PrimR I32R) 1
| SizeI64R :
  has_mono_size (PrimR I64R) 2
| SizeF32R :
  has_mono_size (PrimR F32R) 1
| SizeF64R :
  has_mono_size (PrimR F64R) 2.

Inductive has_kind : function_context -> type -> kind -> Prop :=
| KVar (F : function_context) (α : variable) (κ : kind) :
  nth_error F.(fc_type_vars) α = Some κ ->
  kind_ok F κ ->
  has_kind F (VarT α) κ
| KI32 (F : function_context) :
  has_kind F (NumT (IntT I32T)) (TYPE (PrimR I32R) Unr Heapable)
| KI64 (F : function_context) :
  has_kind F (NumT (IntT I64T)) (TYPE (PrimR I64R) Unr Heapable)
| KF32 (F : function_context) :
  has_kind F (NumT (FloatT F32T)) (TYPE (PrimR F32R) Unr Heapable)
| KF64 (F : function_context) :
  has_kind F (NumT (FloatT F64T)) (TYPE (PrimR F64R) Unr Heapable)
| KSum
    (F : function_context) (τs : list type) (rs : list representation) (l : linearity)
    (h : heapability) :
  Forall2 (fun τ r => has_kind F τ (TYPE r l h)) τs rs ->
  has_kind F (SumT τs) (TYPE (SumR rs) l h)
| KProd
    (F : function_context) (τs : list type) (rs : list representation) (l : linearity)
    (h : heapability) :
  Forall2 (fun τ r => has_kind F τ (TYPE r l h)) τs rs ->
  has_kind F (ProdT τs) (TYPE (ProdR rs) l h)
| KArray (F : function_context) (τ : type) (r : representation) :
  has_kind F τ (TYPE r Unr Heapable) ->
  has_kind F (ArrayT τ) (TYPE DynR Unr Heapable)
| KExLoc (F : function_context) (τ : type) (κ : kind) :
  has_kind (set fc_loc_vars S F) τ κ ->
  has_kind F (ExT ELoc τ) κ
| KExType (F : function_context) (τ : type) (κ0 κ : kind) :
  has_kind (set fc_type_vars (cons κ0) F) τ κ ->
  has_kind F (ExT (EType κ0) τ) κ
| KRec (F : function_context) (τ : type) (κ : kind) :
  (* TODO: Unfold. *)
  has_kind F τ κ ->
  has_kind F (RecT τ) κ
| KPtr (F : function_context) (ℓ : location) :
  has_kind F (PtrT ℓ) (TYPE (PrimR PtrR) Unr Heapable)
| KCap (F : function_context) (ℓ : location) (τ : type) :
  has_kind F (CapT ℓ τ) (TYPE (ProdR []) Lin Unheapable)
| KBoxUniq (F : function_context) (ℓ : location) (τ : type) :
  has_kind F (BoxT OwnUniq ℓ τ) (TYPE (PrimR PtrR) Lin Heapable)
| KBoxGC (F : function_context) (ℓ : location) (τ : type) :
  has_kind F (BoxT OwnGC ℓ τ) (TYPE (PrimR PtrR) Unr Heapable)
| KCoderef (F : function_context) (χ : function_type) :
  has_kind F (CoderefT χ) (TYPE (PrimR I32R) Unr Heapable)
| KRepT
    (F : function_context) (r0 r : representation) (sz0 sz : nat) (τ : type) (l : linearity)
    (h : heapability) :
  sz0 <= sz ->
  has_mono_size r0 sz0 ->
  has_mono_size r sz ->
  has_kind F τ (TYPE r0 l h) ->
  has_kind F (RepT r τ) (TYPE r l h)
| KSized (F : function_context) (r : representation) :
  has_kind F (SizedT r) (CONSTRAINT (PrimR I32R)).
