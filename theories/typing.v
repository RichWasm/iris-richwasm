From Coq Require Import List.
Import ListNotations.

Require Import RichWasm.syntax.

Record function_context :=
  { fc_loc_vars : nat;
    fc_size_vars : list (list size * list size);
    fc_acuity_vars : nat;
    fc_rep_vars : list (option size);
    fc_type_vars : list kind }.

Inductive acu_ok : function_context -> acuity -> Prop :=
| AcuVarOK (F : function_context) (ℵ : variable) :
  ℵ < F.(fc_acuity_vars) -> acu_ok F (AcuVar ℵ)
| SharpOK (F : function_context) :
  acu_ok F Sharp
| DullOK (F : function_context) :
  acu_ok F Dull.

Inductive size_ok : function_context -> size -> Prop :=
| SizeVarOK (F : function_context) (σ : variable) :
  σ < length F.(fc_size_vars) -> size_ok F (SizeVar σ)
| SizePlusOK (F : function_context) (sz1 sz2 : size) :
  size_ok F sz1 -> size_ok F sz2 -> size_ok F (SizePlus sz1 sz2)
| SizeConstOK (F : function_context) (c : nat) :
  size_ok F (SizeConst c).

Inductive base_rep_ok : function_context -> base_representation -> Prop :=
| I32R_OK (F : function_context) (a : acuity) :
  acu_ok F a -> base_rep_ok F (I32R a)
| I64R_OK (F : function_context) :
  base_rep_ok F I64R
| F32R_OK (F : function_context) :
  base_rep_ok F F32R
| F64R_OK (F : function_context) :
  base_rep_ok F F64R.

Inductive rep_ok : function_context -> representation -> Prop :=
| RepVarOK (F : function_context) (ϱ : variable) :
  ϱ < length F.(fc_rep_vars) -> rep_ok F (RepVar ϱ)
| RepListOK (F : function_context) (bs : list base_representation) :
  Forall (base_rep_ok F) bs -> rep_ok F (RepList bs)
| RepPadOK (F : function_context) (sz : size) (r : representation) :
  size_ok F sz -> rep_ok F r -> rep_ok F (RepPad sz r)
| RepDynOK (F : function_context) :
  rep_ok F RepDyn.

Inductive kind_ok : function_context -> kind -> Prop :=
| TYPE_OK (F : function_context) (r : representation) (l : linearity) (h : heapability) :
  rep_ok F r -> kind_ok F (TYPE r l h).

Inductive has_kind : function_context -> type -> kind -> Prop :=
| KUnit (F : function_context) :
  has_kind F UnitT (TYPE (RepList []) Unr Heapable)
| KVar (F : function_context) (α : variable) (κ : kind) :
  nth_error F.(fc_type_vars) α = Some κ -> kind_ok F κ -> has_kind F (VarT α) κ
| KI32 (F : function_context) :
  has_kind F (NumT (IntT I32T)) (TYPE (RepList [I32R Dull]) Unr Heapable)
| KI64 (F : function_context) :
  has_kind F (NumT (IntT I64T)) (TYPE (RepList [I64R]) Unr Heapable)
| KF32 (F : function_context) :
  has_kind F (NumT (FloatT F32T)) (TYPE (RepList [F32R]) Unr Heapable)
| KF64 (F : function_context) :
  has_kind F (NumT (FloatT F64T)) (TYPE (RepList [F64R]) Unr Heapable).
