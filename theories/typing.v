From Coq Require Import List.
Import ListNotations.

Require Import stdpp.list.

Require Import RecordUpdate.RecordUpdate.

Require Import RichWasm.syntax.

Record module_ctx :=
  { mc_globals : list (mutability * type) }.

Definition local_ctx := list type.

Record function_ctx :=
  { fc_result_type : list type;
    fc_labels : list (list type * local_ctx);
    fc_location_vars : nat;
    fc_own_vars : nat;
    fc_rep_vars : nat;
    fc_size_vars : nat;
    fc_type_vars : list kind }.

Definition fc_empty : function_ctx :=
  {| fc_result_type := [];
     fc_labels := [];
     fc_location_vars := 0;
     fc_own_vars := 0;
     fc_rep_vars := 0;
     fc_size_vars := 0;
     fc_type_vars := [] |}.

Global Instance eta_function_ctx : Settable _ :=
  settable! Build_function_ctx
  <fc_result_type; fc_labels; fc_location_vars; fc_own_vars; fc_rep_vars; fc_size_vars;
   fc_type_vars>.

Definition update_locals (le : local_effect) (L : local_ctx) : local_ctx :=
  fold_left (fun acc '(i, τ) => <[ i := τ ]> acc) le L.

Inductive rep_ok : function_ctx -> representation -> Prop :=
| VarR_OK (F : function_ctx) (r : variable) :
  r < F.(fc_rep_vars) -> rep_ok F (VarR r)
| SumR_OK (F : function_ctx) (ρs : list representation) :
  Forall (rep_ok F) ρs -> rep_ok F (SumR ρs)
| ProdR_OK (F : function_ctx) (ρs : list representation) :
  Forall (rep_ok F) ρs -> rep_ok F (ProdR ρs)
| PrimR_OK (F : function_ctx) (ι : primitive_rep) :
  rep_ok F (PrimR ι).

Inductive kind_ok : function_ctx -> kind -> Prop :=
| VALTYPE_OK (F : function_ctx) (ρ : representation) (η : heapability) (γ : linearity) :
  rep_ok F ρ -> kind_ok F (VALTYPE ρ η γ)
| MEMTYPE_OK (F : function_ctx) (ζ : sizity) :
  kind_ok F (MEMTYPE ζ).

Inductive mono_rep : representation -> list primitive_rep -> Prop :=
| MonoSumR (ρs : list representation) (ιss : list (list primitive_rep)) :
  Forall2 mono_rep ρs ιss ->
  (* TODO: Use an efficient packing. *)
  mono_rep (SumR ρs) (concat ιss)
| MonoProdR (ρs : list representation) (ιss : list (list primitive_rep)) :
  Forall2 mono_rep ρs ιss ->
  mono_rep (ProdR ρs) (concat ιss)
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

Definition primitive_size (ι : primitive_rep) : nat :=
  match ι with
  | PtrR => 1
  | I32R => 1
  | I64R => 2
  | F32R => 1
  | F64R => 2
  end.

Inductive has_mono_size : representation -> nat -> Prop :=
| MonoSize (ρ : representation) (ιs : list primitive_rep) :
  mono_rep ρ ιs ->
  has_mono_size ρ (list_sum (map primitive_size ιs)).

Inductive has_kind : function_ctx -> type -> kind -> Prop :=
| KSubLin F τ ρ η :
  has_kind F τ (VALTYPE ρ η Unr) ->
  has_kind F τ (VALTYPE ρ η Lin)
| KSubUnheapable F τ ρ γ :
  has_kind F τ (VALTYPE ρ Heapable γ) ->
  has_kind F τ (VALTYPE ρ Unheapable γ)
| KSubUnsized F τ σ :
  has_kind F τ (MEMTYPE (Sized σ)) ->
  has_kind F τ (MEMTYPE Unsized)
| KVar F t κ :
  F.(fc_type_vars) !! t = Some κ ->
  kind_ok F κ ->
  has_kind F (VarT t) κ
| KI32 F :
  has_kind F (NumT (IntT I32T)) (VALTYPE (PrimR I32R) Heapable Unr)
| KI64 F :
  has_kind F (NumT (IntT I64T)) (VALTYPE (PrimR I64R) Heapable Unr)
| KF32 F :
  has_kind F (NumT (FloatT F32T)) (VALTYPE (PrimR F32R) Heapable Unr)
| KF64 F :
  has_kind F (NumT (FloatT F64T)) (VALTYPE (PrimR F64R) Heapable Unr)
| KSumVal F τs ρs η γ :
  Forall2 (fun τ ρ => has_kind F τ (VALTYPE ρ η γ)) τs ρs ->
  has_kind F (SumT τs) (VALTYPE (SumR ρs) η γ)
| KSumMem F τs ζs :
  Forall2 (fun τ ζ => has_kind F τ (MEMTYPE ζ)) τs ζs ->
  has_kind F (SumT τs) (MEMTYPE Unsized)
| KSumMemSized F τs σs :
  Forall2 (fun τ σ => has_kind F τ (MEMTYPE (Sized σ))) τs σs ->
  has_kind F (SumT τs) (MEMTYPE (Sized (SumS σs)))
| KProdVal F τs ρs η γ :
  Forall2 (fun τ ρ => has_kind F τ (VALTYPE ρ η γ)) τs ρs ->
  has_kind F (ProdT τs) (VALTYPE (ProdR ρs) η γ)
| KProdMem F τs τn σs ζ :
  Forall2 (fun τ σ => has_kind F τ (MEMTYPE (Sized σ))) τs σs ->
  has_kind F τn (MEMTYPE ζ) ->
  has_kind F (ProdT (τs ++ [τn])) (MEMTYPE Unsized)
| KProdMemSized F τs σs :
  Forall2 (fun τ σ => has_kind F τ (MEMTYPE (Sized σ))) τs σs ->
  has_kind F (ProdT τs) (MEMTYPE (Sized (ProdS σs)))
| KArray F τ σ :
  has_kind F τ (MEMTYPE (Sized σ)) ->
  has_kind F (ArrayT τ) (MEMTYPE Unsized)
| KExLoc F τ κ :
  has_kind (set fc_location_vars S F) τ κ ->
  has_kind F (ExT QLoc τ) κ
| KExOwn F τ κ :
  has_kind (set fc_own_vars S F) τ κ ->
  has_kind F (ExT QOwn τ) κ
| KExRep F τ κ :
  has_kind (set fc_rep_vars S F) τ κ ->
  has_kind F (ExT QRep τ) κ
| KExSize F τ κ :
  has_kind (set fc_size_vars S F) τ κ ->
  has_kind F (ExT QSize τ) κ
| KExType F τ κ0 κ :
  has_kind (set fc_type_vars (cons κ0) F) τ κ ->
  has_kind F (ExT (QType κ0) τ) κ
| KRec F τ κ :
  (* TODO: Unfold. *)
  has_kind F τ κ ->
  has_kind F (RecT τ) κ
| KPtr F ℓ :
  has_kind F (PtrT ℓ) (VALTYPE (PrimR PtrR) Heapable Unr)
| KCap F ℓ τ :
  has_kind F (CapT ℓ τ) (VALTYPE (ProdR []) Unheapable Lin)
| KRef F ℓ ω τ ζ :
  has_kind F τ (MEMTYPE ζ) ->
  has_kind F (RefT ω ℓ τ) (VALTYPE (PrimR PtrR) Heapable Lin)
| KRefGC F ℓ τ ζ :
  has_kind F τ (MEMTYPE ζ) ->
  has_kind F (RefT OwnGC ℓ τ) (VALTYPE (PrimR PtrR) Heapable Unr)
| KCodeRef F ϕ :
  has_kind F (CodeRefT ϕ) (VALTYPE (PrimR I32R) Heapable Unr)
| KRep F ρ0 ρ τ η γ :
  has_kind F τ (VALTYPE ρ0 η γ) ->
  has_kind F (RepT ρ τ) (VALTYPE ρ η γ)
| KPad F σ0 σ τ :
  has_kind F τ (MEMTYPE (Sized σ0)) ->
  has_kind F (PadT σ τ) (MEMTYPE (Sized σ))
| KSer F τ ρ γ :
  has_kind F τ (VALTYPE ρ Heapable γ) ->
  has_kind F (SerT τ) (MEMTYPE (Sized (RepS ρ))).

Inductive has_rep : function_ctx -> type -> representation -> Prop :=
| RepVALTYPE (F : function_ctx) (τ : type) (ρ : representation) (η : heapability) (γ : linearity) :
  has_kind F τ (VALTYPE ρ η γ) ->
  has_rep F τ ρ.

Inductive is_unrestricted : function_ctx -> type -> Prop :=
| UnrVALTYPE (F : function_ctx) (τ : type) (ρ : representation) (η : heapability) :
  has_kind F τ (VALTYPE ρ η Unr) ->
  is_unrestricted F τ.

Inductive module_ctx_ok : module_ctx -> Prop :=
| MC_OK (gs : list (mutability * type)) :
  Forall (fun '(_, τ) => is_unrestricted fc_empty τ) gs ->
  module_ctx_ok {| mc_globals := gs |}.

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
| TNum M F L ann en χ :
  num_instr_has_type en χ ->
  instr_has_type M F L (INum ann en) χ L
| TNumConst M F L ann ν n :
  instr_has_type M F L (INumConst ann ν n) (ArrowT [] [NumT ν]) L
| TBlock M F F' L L' ann τs1 τs2 le es :
  F' = set fc_labels (cons (τs2, L')) F ->
  L' = update_locals le L ->
  expr_has_type M F L es (ArrowT τs1 τs2) L' ->
  instr_has_type M F L (IBlock ann (ArrowT τs1 τs2) le es) (ArrowT τs1 τs2) L'
| TLoop M F F' L ann τs1 τs2 es :
  F' = set fc_labels (cons (τs1, L)) F ->
  expr_has_type M F L es (ArrowT τs1 τs2) L ->
  instr_has_type M F L (ILoop ann (ArrowT τs1 τs2) es) (ArrowT τs1 τs2) L
| TIte M F L L' ann χ le es1 es2 :
  L' = update_locals le L ->
  expr_has_type M F L es1 χ L' ->
  expr_has_type M F L es2 χ L' ->
  instr_has_type M F L (IIte ann χ le es1 es2) χ L'
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
| TLocalGet M F L L' ann n τ ρ :
  L !! n = Some τ ->
  has_rep F τ ρ ->
  L' = <[ n := RepT ρ (ProdT []) ]> L ->
  instr_has_type M F L (ILocalGet ann n) (ArrowT [] [τ]) L'
| TLocalGetUnr M F L ann n τ :
  L !! n = Some τ ->
  is_unrestricted F τ ->
  instr_has_type M F L (ILocalGet ann n) (ArrowT [] [τ]) L
| TLocalSet M F L L' ann n τ τ' ρ :
  L' = <[ n := τ' ]> L ->
  L !! n = Some τ ->
  is_unrestricted F τ ->
  has_rep F τ ρ ->
  has_rep F τ' ρ ->
  instr_has_type M F L (ILocalSet ann n) (ArrowT [τ'] []) L'
| TGlobalGet M F L ann n m τ :
  M.(mc_globals) !! n = Some (m, τ) ->
  instr_has_type M F L (IGlobalGet ann n) (ArrowT [] [τ]) L
| TGlobalSet M F L ann n m τ :
  M.(mc_globals) !! n = Some (m, τ) ->
  instr_has_type M F L (IGlobalSet ann n) (ArrowT [τ] []) L

with expr_has_type {A : Type} :
  module_ctx -> function_ctx -> local_ctx -> expr A -> arrow_type -> local_ctx -> Prop :=
| TNil M F L :
  expr_has_type M F L [] (ArrowT [] []) L
| TCons M F L1 L2 L3 e es τs1 τs2 τs3 :
  instr_has_type M F L1 e (ArrowT τs1 τs2) L2 ->
  expr_has_type M F L2 es (ArrowT τs2 τs3) L3 ->
  expr_has_type M F L1 (e :: es) (ArrowT τs1 τs3) L3.
