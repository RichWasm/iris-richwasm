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
| VarROK (F : function_ctx) (r : variable) :
  r < F.(fc_rep_vars) -> rep_ok F (VarR r)
| SumROK (F : function_ctx) (ρs : list representation) :
  Forall (rep_ok F) ρs -> rep_ok F (SumR ρs)
| ProdROK (F : function_ctx) (ρs : list representation) :
  Forall (rep_ok F) ρs -> rep_ok F (ProdR ρs)
| PrimROK (F : function_ctx) (ι : primitive_rep) :
  rep_ok F (PrimR ι).

Inductive kind_ok : function_ctx -> kind -> Prop :=
| VALTYPEOK (F : function_ctx) (ρ : representation) (η : heapability) (γ : linearity) :
  rep_ok F ρ -> kind_ok F (VALTYPE ρ η γ)
| MEMTYPEOK (F : function_ctx) (ζ : sizity) (γ : linearity) :
  kind_ok F (MEMTYPE ζ γ).

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

Inductive has_kind : function_ctx -> type -> kind -> Prop :=
| KSubValLin F τ ρ η :
  has_kind F τ (VALTYPE ρ η Unr) ->
  has_kind F τ (VALTYPE ρ η Lin)
| KSubMemLin F τ ζ :
  has_kind F τ (MEMTYPE ζ Unr) ->
  has_kind F τ (MEMTYPE ζ Lin)
| KSubUnheapable F τ ρ γ :
  has_kind F τ (VALTYPE ρ Heapable γ) ->
  has_kind F τ (VALTYPE ρ Unheapable γ)
| KSubUnsized F τ σ γ :
  has_kind F τ (MEMTYPE (Sized σ) γ) ->
  has_kind F τ (MEMTYPE Unsized γ)
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
| KSumMem F τs ζs γ :
  Forall2 (fun τ ζ => has_kind F τ (MEMTYPE ζ γ)) τs ζs ->
  has_kind F (SumT τs) (MEMTYPE Unsized γ)
| KSumMemSized F τs σs γ :
  Forall2 (fun τ σ => has_kind F τ (MEMTYPE (Sized σ) γ)) τs σs ->
  has_kind F (SumT τs) (MEMTYPE (Sized (SumS σs)) γ)
| KProdVal F τs ρs η γ :
  Forall2 (fun τ ρ => has_kind F τ (VALTYPE ρ η γ)) τs ρs ->
  has_kind F (ProdT τs) (VALTYPE (ProdR ρs) η γ)
| KProdMem F τs τn σs ζ γ :
  Forall2 (fun τ σ => has_kind F τ (MEMTYPE (Sized σ) γ)) τs σs ->
  has_kind F τn (MEMTYPE ζ γ) ->
  has_kind F (ProdT (τs ++ [τn])) (MEMTYPE Unsized γ)
| KProdMemSized F τs σs γ :
  Forall2 (fun τ σ => has_kind F τ (MEMTYPE (Sized σ) γ)) τs σs ->
  has_kind F (ProdT τs) (MEMTYPE (Sized (ProdS σs)) γ)
| KArray F τ σ :
  has_kind F τ (MEMTYPE (Sized σ) Unr) ->
  has_kind F (ArrayT τ) (MEMTYPE Unsized Unr)
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
| KCap F ω ℓ τ :
  has_kind F (CapT ω ℓ τ) (VALTYPE (ProdR []) Unheapable Lin)
| KRef F ℓ ω τ ζ γ :
  has_kind F τ (MEMTYPE ζ γ) ->
  has_kind F (RefT ω ℓ τ) (VALTYPE (PrimR PtrR) Heapable Lin)
| KCodeRef F ϕ :
  has_kind F (CodeRefT ϕ) (VALTYPE (PrimR I32R) Heapable Unr)
| KRep F ρ0 ρ τ η γ :
  has_kind F τ (VALTYPE ρ0 η γ) ->
  has_kind F (RepT ρ τ) (VALTYPE ρ η γ)
| KPad F σ0 σ τ γ :
  has_kind F τ (MEMTYPE (Sized σ0) γ) ->
  has_kind F (PadT σ τ) (MEMTYPE (Sized σ) γ)
| KSer F τ ρ γ :
  has_kind F τ (VALTYPE ρ Heapable γ) ->
  has_kind F (SerT τ) (MEMTYPE (Sized (RepS ρ)) γ).

Inductive has_rep : function_ctx -> type -> representation -> Prop :=
| RepVALTYPE (F : function_ctx) (τ : type) (ρ : representation) (η : heapability) (γ : linearity) :
  has_kind F τ (VALTYPE ρ η γ) ->
  has_rep F τ ρ.

Inductive mono_sized : function_ctx -> type -> Prop :=
| MonoSized (F : function_ctx) (τ : type) (ρ : representation) (ιs : list primitive_rep) :
  has_rep F τ ρ ->
  mono_rep ρ ιs ->
  mono_sized F τ.

Inductive is_unrestricted : function_ctx -> type -> Prop :=
| UnrVALTYPE (F : function_ctx) (τ : type) (ρ : representation) (η : heapability) :
  has_kind F τ (VALTYPE ρ η Unr) ->
  is_unrestricted F τ
| UnrMEMTYPE (F : function_ctx) (τ : type) (ζ : sizity) :
  has_kind F τ (MEMTYPE ζ Unr) ->
  is_unrestricted F τ.

Inductive is_heapable : function_ctx -> type -> Prop :=
| IsHeapable (F : function_ctx) (τ : type) (ρ : representation) (γ : linearity) :
  has_kind F τ (VALTYPE ρ Heapable γ) ->
  is_heapable F τ.

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

Inductive path_to : path -> type -> list type -> type -> Prop :=
| PathToNil τ :
  path_to [] τ [] τ
| PathToRep π ρ τ τs τ' :
  path_to π τ τs τ' ->
  path_to (PCUnwrap :: π) (RepT ρ τ) τs τ'
| PathToPad π σ τ τs τ' :
  path_to (PCUnwrap :: π) τ τs τ' ->
  path_to π (PadT σ τ) τs τ'
| PathToSer π τ τs τ' :
  path_to π τ τs τ' ->
  path_to (PCUnwrap :: π) (SerT τ) τs τ'
| PathToEx π δ τ τs τ' :
  path_to π τ τs τ' ->
  path_to (PCUnwrap :: π) (ExT δ τ) τs τ'
| PathToRec π τ τs τ' :
  path_to π τ τs τ' ->
  path_to (PCUnwrap :: π) (RecT τ) τs τ'
| PathToProd n π τs τs0 τs' τ τ0 :
  length τs0 = n ->
  path_to π τ0 τs τ ->
  path_to (PCProj n :: π) (ProdT (τs0 ++ τ0 :: τs')) (τs0 ++ τs) τ.

Inductive update_at : path -> type -> type -> type -> type -> Prop :=
| UpdateAtNil τ τ' :
  update_at [] τ τ τ' τ'
| UpdateAtRep π ρ τ τ' τ__π τ__π' :
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCUnwrap :: π) (RepT ρ τ) τ__π (RepT ρ τ') τ__π'
| UpdateAtPad π σ τ τ' τ__π τ__π' :
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCUnwrap :: π) (PadT σ τ) τ__π (PadT σ τ') τ__π'
| UpdateAtSer π τ τ' τ__π τ__π' :
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCUnwrap :: π) (SerT τ) τ__π (SerT τ') τ__π'
| UpdateAtEx π δ τ τ' τ__π τ__π'  :
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCUnwrap :: π) (ExT δ τ) τ__π (ExT δ τ') τ__π'
| UpdateAtRec π τ τ' τ__π τ__π' :
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCUnwrap :: π) (RecT τ) τ__π (RecT τ') τ__π'
| UpdateAtProd π τ τ' τ__π τ__π' τs τs' n :
  length τs = n ->
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCProj n :: π) (ProdT (τs ++ τ :: τs')) τ__π (ProdT (τs ++ τ' :: τs')) τ__π'.

Inductive mono_size : size -> nat -> Prop :=
| MonoSizeSum σs ns :
  Forall2 mono_size σs ns ->
  mono_size (SumS σs) (S (list_max ns))
| MonoSizeProd σs ns :
  Forall2 mono_size σs ns ->
  mono_size (ProdS σs) (list_sum ns)
| MonoSizeRep ρ ιs :
  mono_rep ρ ιs ->
  mono_size (RepS ρ) (list_sum (map primitive_size ιs))
| MonoSizeConst n :
  mono_size (ConstS n) n.

Inductive stores_as : function_ctx -> type -> type -> Prop :=
| SASer F τ :
  stores_as F τ (SerT τ)
| SAPad F τ τ' ρ ιs σ n :
  has_rep F τ ρ ->
  mono_rep ρ ιs ->
  mono_size σ n ->
  list_sum (map primitive_size ιs) <= n ->
  stores_as F τ τ' ->
  stores_as F τ (PadT σ τ')
| SAProd F τs τs' :
  Forall2 (stores_as F) τs τs' ->
  stores_as F (ProdT τs) (ProdT τs').

(* Handy name for the converse of stores_as. *)
Definition loads_as F τ τ' := stores_as F τ' τ.

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
| TWrap M F L ann ρ0 ρ ιs0 ιs τ :
  mono_rep ρ0 ιs0 ->
  mono_rep ρ ιs ->
  convertible_to ιs0 ιs ->
  instr_has_type M F L (IWrap ann) (ArrowT [τ] [RepT ρ τ]) L
| TUnwrap M F L ann ρ0 ρ ιs0 ιs τ :
  mono_rep ρ0 ιs0 ->
  mono_rep ρ ιs ->
  convertible_to ιs0 ιs ->
  instr_has_type M F L (IUnwrap ann) (ArrowT [RepT ρ τ] [τ]) L
| TRefNew M F L ann ω τ τ' :
  is_heapable F τ ->
  stores_as F τ τ' ->
  (* TODO: weaken τ' *)
  instr_has_type M F L (IRefNew ann ω) (ArrowT [τ] [ExT QLoc (RefT ω (LocVar 0) τ')]) L
| TRefFree M F L ann ℓ τ :
  is_unrestricted F τ ->
  instr_has_type M F L (IRefFree ann) (ArrowT [RefT OwnUniq ℓ τ] []) L
| TRefDup M F L ann ℓ τ :
  instr_has_type M F L (IRefDup ann) (ArrowT [RefT OwnGC ℓ τ] [RefT OwnGC ℓ τ; RefT OwnGC ℓ τ]) L
| TRefDrop M F L ann ℓ τ :
  instr_has_type M F L (IRefDrop ann) (ArrowT [RefT OwnGC ℓ τ] []) L
| TRefLoad M F L ann π ω ℓ τ τs__off τ' ρ ιs :
  path_to π τ τs__off τ' ->
  Forall (mono_sized F) τs__off ->
  has_kind F τ' (VALTYPE ρ Heapable Unr) ->
  mono_rep ρ ιs ->
  instr_has_type M F L (IRefLoad ann π) (ArrowT [RefT ω ℓ τ] [RefT ω ℓ τ; τ']) L
| TRefStore M F L ann π ω ℓ τ τs τᵥ τ__π :
  path_to π τ τs τ__π ->
  stores_as F τᵥ τ__π ->
  instr_has_type M F L (IRefStore ann π) (ArrowT [RefT ω ℓ τ; τᵥ] [RefT ω ℓ τ]) L
| TRefStoreUniq M F L ann π ℓ τ τ' τᵥ τᵥ' τₘ τₘ' σ σ' γ n :
  is_heapable F τᵥ' ->
  stores_as F τᵥ τₘ' ->
  update_at π τ τₘ τ' τₘ' ->
  has_kind F τₘ (MEMTYPE (Sized σ) Unr) ->
  has_kind F τₘ' (MEMTYPE (Sized σ') γ) ->
  mono_size σ n ->
  mono_size σ' n ->
  instr_has_type M F L (IRefStore ann π) (ArrowT [RefT OwnUniq ℓ τ; τᵥ'] [RefT OwnUniq ℓ τ']) L
| TRefSwap M F L ann π ℓ γ ρ ιs τ τ' τᵥ τᵥ' τₘ τₘ' σ σ' τs__off :
  is_heapable F τᵥ' ->
  has_kind F τᵥ (VALTYPE ρ Heapable γ) ->
  mono_rep ρ ιs ->
  has_kind F τₘ (MEMTYPE (Sized σ) Unr) ->
  has_kind F τₘ' (MEMTYPE (Sized σ') γ) ->
  loads_as F τᵥ τₘ ->
  stores_as F τᵥ' τₘ' ->
  update_at π τ τₘ τ' τₘ' ->
  path_to π τ' τs__off τₘ ->
  Forall (mono_sized F) τs__off ->
  instr_has_type M F L (IRefSwap ann π) (ArrowT [RefT OwnUniq ℓ τ; τᵥ'] [RefT OwnUniq ℓ τ'; τᵥ]) L
| TRefSplit M F L ann ω ℓ τ ζ γ :
  has_kind F τ (MEMTYPE ζ γ) ->
  instr_has_type M F L (IRefSplit ann) (ArrowT [RefT ω ℓ τ] [ProdT [PtrT ℓ; CapT ω ℓ τ]]) L
| TRefJoin M F L ann ω ℓ τ ζ γ :
  has_kind F τ (MEMTYPE ζ γ) ->
  instr_has_type M F L (IRefSplit ann) (ArrowT [ProdT [PtrT ℓ; CapT ω ℓ τ]] [RefT ω ℓ τ]) L

with expr_has_type {A : Type} :
  module_ctx -> function_ctx -> local_ctx -> expr A -> arrow_type -> local_ctx -> Prop :=
| TNil M F L :
  expr_has_type M F L [] (ArrowT [] []) L
| TCons M F L1 L2 L3 e es τs1 τs2 τs3 :
  instr_has_type M F L1 e (ArrowT τs1 τs2) L2 ->
  expr_has_type M F L2 es (ArrowT τs2 τs3) L3 ->
  expr_has_type M F L1 (e :: es) (ArrowT τs1 τs3) L3.
