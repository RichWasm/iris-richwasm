From Coq Require Import List.
Import ListNotations.

Require Import stdpp.list.

Require Import RecordUpdate.RecordUpdate.

Require Import RichWasm.syntax.

Record module_ctx :=
  { mc_globals : list global_type }.

Definition local_ctx := list type.

Record function_ctx :=
  { fc_result_type : list type;
    fc_labels : list (list type * local_ctx);
    fc_location_vars : nat;
    fc_rep_vars : nat;
    fc_type_vars : list kind }.

Definition fc_empty : function_ctx :=
  {| fc_result_type := [];
     fc_labels := [];
     fc_location_vars := 0;
     fc_rep_vars := 0;
     fc_type_vars := [] |}.

Global Instance eta_function_ctx : Settable _ :=
  settable! Build_function_ctx
  <fc_result_type; fc_labels; fc_location_vars; fc_rep_vars; fc_type_vars>.

Definition update_locals (le : local_effect) (L : local_ctx) : local_ctx :=
  fold_left (fun acc '(i, τ) => <[ i := τ ]> acc) le L.

Inductive rep_ok : function_ctx -> representation -> Prop :=
| VarR_OK (F : function_ctx) (ϱ : variable) :
  ϱ < F.(fc_rep_vars) -> rep_ok F (VarR ϱ)
| SumR_OK (F : function_ctx) (rs : list representation) :
  Forall (rep_ok F) rs -> rep_ok F (SumR rs)
| ProdR_OK (F : function_ctx) (rs : list representation) :
  Forall (rep_ok F) rs -> rep_ok F (ProdR rs)
| PrimR_OK (F : function_ctx) (p : primitive_rep) :
  rep_ok F (PrimR p).

Inductive kind_ok : function_ctx -> kind -> Prop :=
| TYPE_OK (F : function_ctx) (r : representation) (l : linearity) (h : heapability) :
  rep_ok F r -> kind_ok F (TYPE r l h).

Inductive mono_rep : representation -> list primitive_rep -> Prop :=
| MonoSumR (rs : list representation) (pss : list (list primitive_rep)) :
  Forall2 mono_rep rs pss ->
  (* TODO: Use an efficient packing. *)
  mono_rep (SumR rs) (concat pss)
| MonoProdR (rs : list representation) (pss : list (list primitive_rep)) :
  Forall2 mono_rep rs pss ->
  mono_rep (ProdR rs) (concat pss)
| MonoPtrR :
  mono_rep (PrimR PtrR) [PtrR]
| MonoI32R :
  mono_rep (PrimR I32R) [I32R]
| MonoI64R :
  mono_rep (PrimR I64R) [I64R]
| MonoF32R :
  mono_rep (PrimR F32R) [F32R]
| MonoF64R :
  mono_rep (PrimR F64R) [F64R].

Definition primitive_size (p : primitive_rep) : nat :=
  match p with
  | PtrR => 1
  | I32R => 1
  | I64R => 2
  | F32R => 1
  | F64R => 2
  end.

Inductive has_mono_size : representation -> nat -> Prop :=
| MonoSize (r : representation) (ps : list primitive_rep) :
  mono_rep r ps ->
  has_mono_size r (list_sum (map primitive_size ps)).

Inductive has_kind : function_ctx -> type -> kind -> Prop :=
| KSubLin (F : function_ctx) (τ : type) (r : representation) (h : heapability) :
  has_kind F τ (TYPE r Unr h) ->
  has_kind F τ (TYPE r Lin h)
| KSubHeap (F : function_ctx) (τ : type) (r : representation) (l : linearity) :
  has_kind F τ (TYPE r l Heapable) ->
  has_kind F τ (TYPE r l Unheapable)
| KVar (F : function_ctx) (α : variable) (κ : kind) :
  F.(fc_type_vars) !! α = Some κ ->
  kind_ok F κ ->
  has_kind F (VarT α) κ
| KI32 (F : function_ctx) :
  has_kind F (NumT (IntT I32T)) (TYPE (PrimR I32R) Unr Heapable)
| KI64 (F : function_ctx) :
  has_kind F (NumT (IntT I64T)) (TYPE (PrimR I64R) Unr Heapable)
| KF32 (F : function_ctx) :
  has_kind F (NumT (FloatT F32T)) (TYPE (PrimR F32R) Unr Heapable)
| KF64 (F : function_ctx) :
  has_kind F (NumT (FloatT F64T)) (TYPE (PrimR F64R) Unr Heapable)
| KSum
    (F : function_ctx) (τs : list type) (rs : list representation) (l : linearity)
    (h : heapability) :
  Forall2 (fun τ r => has_kind F τ (TYPE r l h)) τs rs ->
  has_kind F (SumT τs) (TYPE (SumR rs) l h)
| KProd
    (F : function_ctx) (τs : list type) (rs : list representation) (l : linearity)
    (h : heapability) :
  Forall2 (fun τ r => has_kind F τ (TYPE r l h)) τs rs ->
  has_kind F (ProdT τs) (TYPE (ProdR rs) l h)
| KExLoc (F : function_ctx) (τ : type) (κ : kind) :
  has_kind (set fc_location_vars S F) τ κ ->
  has_kind F (ExT ELoc τ) κ
| KExType (F : function_ctx) (τ : type) (κ0 κ : kind) :
  has_kind (set fc_type_vars (cons κ0) F) τ κ ->
  has_kind F (ExT (EType κ0) τ) κ
| KRec (F : function_ctx) (τ : type) (κ : kind) :
  (* TODO: Unfold. *)
  has_kind F τ κ ->
  has_kind F (RecT τ) κ
| KPtr (F : function_ctx) (ℓ : location) :
  has_kind F (PtrT ℓ) (TYPE (PrimR PtrR) Unr Heapable)
| KCap (F : function_ctx) (ℓ : location) (τ : type) :
  has_kind F (CapT ℓ τ) (TYPE (ProdR []) Lin Unheapable)
| KBoxUniq (F : function_ctx) (ℓ : location) (ψ : boxed_type) :
  has_kind F (BoxT OwnUniq ℓ ψ) (TYPE (PrimR PtrR) Lin Heapable)
| KBoxGC (F : function_ctx) (ℓ : location) (ψ : boxed_type) :
  has_kind F (BoxT OwnGC ℓ ψ) (TYPE (PrimR PtrR) Unr Heapable)
| KCoderef (F : function_ctx) (χ : function_type) :
  has_kind F (CoderefT χ) (TYPE (PrimR I32R) Unr Heapable)
| KRepT
    (F : function_ctx) (r0 r : representation) (sz0 sz : nat) (τ : type) (l : linearity)
    (h : heapability) :
  sz0 <= sz ->
  has_mono_size r0 sz0 ->
  has_mono_size r sz ->
  has_kind F τ (TYPE r0 l h) ->
  has_kind F (RepT r τ) (TYPE r l h)
| KSize (F : function_ctx) (r : representation) :
  has_kind F (SizeT r) (TYPE (PrimR I32R) Unr Heapable).

Inductive has_rep : function_ctx -> type -> representation -> Prop :=
| RepTYPE (F : function_ctx) (τ : type) (r : representation) (l : linearity) (h : heapability) :
  has_kind F τ (TYPE r l h) ->
  has_rep F τ r.

Inductive is_unrestricted : function_ctx -> type -> Prop :=
| UnrTYPE (F : function_ctx) (τ : type) (r : representation) (h : heapability) :
  has_kind F τ (TYPE r Unr h) ->
  is_unrestricted F τ.

Inductive module_ctx_ok : module_ctx -> Prop :=
| MC_OK (τgs : list global_type) :
  Forall (fun '(GlobalT _ τ) => is_unrestricted fc_empty τ) τgs ->
  module_ctx_ok {| mc_globals := τgs |}.

(* TODO *)
Inductive num_instr_has_type : num_instr -> arrow_type -> Prop :=.

Inductive instr_has_type {A : Type} :
  module_ctx -> function_ctx -> local_ctx -> instr A -> arrow_type -> local_ctx -> Prop :=
| TNop M F L ann :
  instr_has_type M F L (INop ann) (ArrowT [] []) L
| TDrop M F L ann τ :
  is_unrestricted F τ ->
  instr_has_type M F L (IDrop ann) (ArrowT [τ] []) L
| TUnreachable M F L L' ann τs1 τs2 le :
  L' = update_locals le L ->
  instr_has_type M F L (IUnreachable ann) (ArrowT τs1 τs2) L
| TNum M F L ann en τa :
  num_instr_has_type en τa ->
  instr_has_type M F L (INum ann en) τa L
| TNumConst M F L ann τn n :
  instr_has_type M F L (INumConst ann τn n) (ArrowT [] [NumT τn]) L
| TBlock M F F' L L' ann τs1 τs2 le es :
  F' = set fc_labels (cons (τs2, L')) F ->
  L' = update_locals le L ->
  expr_has_type M F L es (ArrowT τs1 τs2) L' ->
  instr_has_type M F L (IBlock ann (ArrowT τs1 τs2) le es) (ArrowT τs1 τs2) L'
| TLoop M F F' L ann τs1 τs2 es :
  F' = set fc_labels (cons (τs1, L)) F ->
  expr_has_type M F L es (ArrowT τs1 τs2) L ->
  instr_has_type M F L (ILoop ann (ArrowT τs1 τs2) es) (ArrowT τs1 τs2) L
| TIte M F L L' ann τa le es1 es2 :
  L' = update_locals le L ->
  expr_has_type M F L es1 τa L' ->
  expr_has_type M F L es2 τa L' ->
  instr_has_type M F L (IIte ann τa le es1 es2) τa L'
| TBr M F L L' ann n τs τs1 τs2 le :
  L' = update_locals le L ->
  F.(fc_labels) !! n = Some (τs, L) ->
  Forall (is_unrestricted F) τs1 ->
  instr_has_type M F L (IBr ann n) (ArrowT (τs1 ++ τs) τs2) L'
| TBrIf M F L ann n τs :
  F.(fc_labels) !! n = Some (τs, L) ->
  instr_has_type M F L (IBrIf ann n) (ArrowT (τs ++ [NumT (IntT I32T)]) τs) L
| TBrTable M F L L' ann ns n τs τs1 τs2 :
  Forall (fun i => F.(fc_labels) !! i = Some (τs, L)) (n :: ns) ->
  Forall (is_unrestricted F) τs1 ->
  instr_has_type M F L (IBrTable ann ns n) (ArrowT (τs1 ++ τs ++ [NumT (IntT I32T)]) τs2) L'
| TReturn M F L L' ann le τs τs1 τs2 :
  F.(fc_result_type) = τs ->
  L' = update_locals le L ->
  Forall (is_unrestricted F) τs1 ->
  instr_has_type M F L (IReturn ann) (ArrowT (τs1 ++ τs) τs2) L'
| TLocalGet M F L L' ann n τ r :
  L !! n = Some τ ->
  has_rep F τ r ->
  L' = <[ n := RepT r (ProdT []) ]> L ->
  instr_has_type M F L (ILocalGet ann n) (ArrowT [] [τ]) L'
| TLocalGetUnr M F L ann n τ :
  L !! n = Some τ ->
  is_unrestricted F τ ->
  instr_has_type M F L (ILocalGet ann n) (ArrowT [] [τ]) L
| TLocalSet M F L L' ann n τ τ' r :
  L' = <[ n := τ' ]> L ->
  L !! n = Some τ ->
  is_unrestricted F τ ->
  has_rep F τ r ->
  has_rep F τ' r ->
  instr_has_type M F L (ILocalSet ann n) (ArrowT [τ'] []) L'
| TGlobalGet M F L ann n m τ :
  M.(mc_globals) !! n = Some (GlobalT m τ) ->
  instr_has_type M F L (IGlobalGet ann n) (ArrowT [] [τ]) L
| TGlobalSet M F L ann n m τ :
  M.(mc_globals) !! n = Some (GlobalT m τ) ->
  instr_has_type M F L (IGlobalSet ann n) (ArrowT [τ] []) L

with expr_has_type {A : Type} :
  module_ctx -> function_ctx -> local_ctx -> expr A -> arrow_type -> local_ctx -> Prop :=
| TNil M F L :
  expr_has_type M F L [] (ArrowT [] []) L
| TCons M F L1 L2 L3 e es τs1 τs2 τs3 :
  instr_has_type M F L1 e (ArrowT τs1 τs2) L2 ->
  expr_has_type M F L2 es (ArrowT τs2 τs3) L3 ->
  expr_has_type M F L1 (e :: es) (ArrowT τs1 τs3) L3.
