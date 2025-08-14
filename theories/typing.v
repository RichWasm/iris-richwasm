From Coq Require Import List.
Import ListNotations.

Require Import stdpp.list.

Require Import RecordUpdate.RecordUpdate.

Require Import RichWasm.syntax.

Definition local_context := list type.

Record function_context :=
  { fc_result_type : list type;
    fc_labels : list (list type * local_context);
    fc_location_vars : nat;
    fc_rep_vars : nat;
    fc_type_vars : list kind }.

Global Instance eta_function_context : Settable _ :=
  settable! Build_function_context
  <fc_result_type; fc_labels; fc_location_vars; fc_rep_vars; fc_type_vars>.

Definition update_locals (le : local_effect) (L : local_context) : local_context :=
  fold_left (fun acc '(i, τ) => <[ i := τ ]> acc) le L.

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
| KSubLin (F : function_context) (τ : type) (r : representation) (h : heapability) :
  has_kind F τ (TYPE r Unr h) ->
  has_kind F τ (TYPE r Lin h)
| KSubHeap (F : function_context) (τ : type) (r : representation) (l : linearity) :
  has_kind F τ (TYPE r l Heapable) ->
  has_kind F τ (TYPE r l Unheapable)
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
  has_kind (set fc_location_vars S F) τ κ ->
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

Inductive is_unrestricted : function_context -> type -> Prop :=
| UnrTYPE (F : function_context) (τ : type) (r : representation) (h : heapability) :
  has_kind F τ (TYPE r Unr h) ->
  is_unrestricted F τ
| UnrCONSTRAINT (F : function_context) (τ : type) (r : representation) :
  has_kind F τ (CONSTRAINT r) ->
  is_unrestricted F τ.

(* TODO *)
Inductive num_instr_has_type : num_instr -> arrow_type -> Prop :=.

Inductive instr_has_type {A : Type} :
  function_context -> local_context -> instr A -> arrow_type -> local_context -> Prop :=
| TNop (F : function_context) (L : local_context) (ann : A) :
  instr_has_type F L (INop ann) (ArrowT [] []) L
| TDrop (F : function_context) (L : local_context) (ann : A) (τ : type) :
  is_unrestricted F τ ->
  instr_has_type F L (IDrop ann) (ArrowT [τ] []) L
| TUnreachable
    (F : function_context) (L L' : local_context) (ann : A) (τs1 τs2 : list type) (le : local_effect) :
  L' = update_locals le L ->
  instr_has_type F L (IUnreachable ann) (ArrowT τs1 τs2) L
| TNum (F : function_context) (L : local_context) (ann : A) (en : num_instr) (τa : arrow_type) :
  num_instr_has_type en τa ->
  instr_has_type F L (INum ann en) τa L
| TNumConst (F : function_context) (L : local_context) (ann : A) (τn : num_type) (n : nat) :
  instr_has_type F L (INumConst ann τn n) (ArrowT [] [NumT τn]) L
| TBlock
    (F F' : function_context) (L L' : local_context) (ann : A) (τs1 τs2 : list type)
    (le : local_effect) (es : expr A) :
  F' = set fc_labels (cons (τs2, L')) F ->
  L' = update_locals le L ->
  expr_has_type F L es (ArrowT τs1 τs2) L' ->
  instr_has_type F L (IBlock ann (ArrowT τs1 τs2) le es) (ArrowT τs1 τs2) L'
| TLoop
    (F F' : function_context) (L : local_context) (ann : A) (τs1 τs2 : list type) (es : expr A) :
  F' = set fc_labels (cons (τs1, L)) F ->
  expr_has_type F L es (ArrowT τs1 τs2) L ->
  instr_has_type F L (ILoop ann (ArrowT τs1 τs2) es) (ArrowT τs1 τs2) L
| TIte
    (F : function_context) (L L' : local_context) (ann : A) (τa : arrow_type) (le : local_effect)
    (es1 es2 : expr A) :
  L' = update_locals le L ->
  expr_has_type F L es1 τa L' ->
  expr_has_type F L es2 τa L' ->
  instr_has_type F L (IIte ann τa le es1 es2) τa L'
| TBr
    (F : function_context) (L L' : local_context) (ann : A) (n : nat) (τs τs1 τs2 : list type)
    (le : local_effect) :
  L' = update_locals le L ->
  nth_error F.(fc_labels) n = Some (τs, L) ->
  Forall (is_unrestricted F) τs1 ->
  instr_has_type F L (IBr ann n) (ArrowT (τs1 ++ τs) τs2) L'
| TBrIf (F : function_context) (L : local_context) (ann : A) (n : nat) (τs : list type) :
  nth_error F.(fc_labels) n = Some (τs, L) ->
  instr_has_type F L (IBrIf ann n) (ArrowT (τs ++ [NumT (IntT I32T)]) τs) L
| TBrTable
    (F : function_context) (L L' : local_context) (ann : A) (ns : list nat) (n : nat)
    (τs τs1 τs2 : list type) :
  Forall (fun i => nth_error F.(fc_labels) i = Some (τs, L)) (n :: ns) ->
  Forall (is_unrestricted F) τs1 ->
  instr_has_type F L (IBrTable ann ns n) (ArrowT (τs1 ++ τs ++ [NumT (IntT I32T)]) τs2) L'
| TReturn
    (F : function_context) (L L' : local_context) (ann : A) (le : local_effect)
    (τs τs1 τs2 : list type) :
  F.(fc_result_type) = τs ->
  L' = update_locals le L ->
  Forall (is_unrestricted F) τs1 ->
  instr_has_type F L (IReturn ann) (ArrowT (τs1 ++ τs) τs2) L'

with expr_has_type {A : Type} :
  function_context -> local_context -> expr A -> arrow_type -> local_context -> Prop :=
| TNil (F : function_context) (L : local_context) :
  expr_has_type F L [] (ArrowT [] []) L
| TCons
    (F : function_context) (L1 L2 L3 : local_context) (e : instr A) (es : expr A)
    (τs1 τs2 τs3 : list type) :
  instr_has_type F L1 e (ArrowT τs1 τs2) L2 ->
  expr_has_type F L2 es (ArrowT τs2 τs3) L3 ->
  expr_has_type F L1 (e :: es) (ArrowT τs1 τs3) L3.
