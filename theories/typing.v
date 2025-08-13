From Coq Require Import List.
Import ListNotations.

Require Import RichWasm.syntax.

Record function_context :=
  { fc_loc_vars : nat;
    fc_size_vars : list (list size * list size);
    fc_rep_vars : list (option size);
    fc_type_vars : list kind }.

Inductive size_ok : function_context -> size -> Prop :=
| SizeVarOK (F : function_context) (σ : variable) :
  σ < length F.(fc_size_vars) -> size_ok F (SizeVar σ)
| SizePlusOK (F : function_context) (sz1 sz2 : size) :
  size_ok F sz1 -> size_ok F sz2 -> size_ok F (SizePlus sz1 sz2)
| SizeConstOK (F : function_context) (c : nat) :
  size_ok F (SizeConst c).

Inductive rep_ok : function_context -> representation -> Prop :=
| VarR_OK (F : function_context) (ϱ : variable) :
  ϱ < length F.(fc_rep_vars) -> rep_ok F (VarR ϱ)
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
  rep_ok F r -> kind_ok F (TYPE r l h).

Inductive has_kind : function_context -> type -> kind -> Prop :=
| KUnit (F : function_context) :
  has_kind F UnitT (TYPE (ProdR []) Unr Heapable)
| KVar (F : function_context) (α : variable) (κ : kind) :
  nth_error F.(fc_type_vars) α = Some κ -> kind_ok F κ -> has_kind F (VarT α) κ
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
  has_kind F (ArrayT τ) (TYPE DynR Unr Heapable).
