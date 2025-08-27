From Coq Require Import List.
Import ListNotations.

Require Import stdpp.list.

Require Import RecordUpdate.RecordUpdate.

Require Import RichWasm.syntax.

Record module_ctx {K : Type} :=
  { mc_globals : list (mutability * type K);
    mc_table : list (function_type K) }.

Arguments module_ctx : clear implicits.

Definition local_ctx (K : Type) := list (type K).

Record function_ctx {K : Type} :=
  { fc_result_type : list (type K);
    fc_labels : list (list (type K) * local_ctx K);
    fc_location_vars : nat;
    fc_own_vars : nat;
    fc_rep_vars : nat;
    fc_size_vars : nat;
    fc_type_vars : list kind }.

Arguments function_ctx : clear implicits.

Definition fc_empty {K : Type} : function_ctx K :=
  {| fc_result_type := [];
     fc_labels := [];
     fc_location_vars := 0;
     fc_own_vars := 0;
     fc_rep_vars := 0;
     fc_size_vars := 0;
     fc_type_vars := [] |}.

Global Instance eta_function_ctx {K : Type} : Settable _ :=
  settable! (@Build_function_ctx K)
  <fc_result_type; fc_labels; fc_location_vars; fc_own_vars; fc_rep_vars; fc_size_vars;
   fc_type_vars>.

Definition update_locals {K : Type} (le : local_effect K) (L : local_ctx K) : local_ctx K :=
  fold_left (fun acc '(i, τ) => <[ i := τ ]> acc) le L.

Inductive rep_ok {K : Type} : function_ctx K -> representation -> Prop :=
| VarROK (F : function_ctx K) (r : variable) :
  r < F.(fc_rep_vars) -> rep_ok F (VarR r)
| SumROK (F : function_ctx K) (ρs : list representation) :
  Forall (rep_ok F) ρs -> rep_ok F (SumR ρs)
| ProdROK (F : function_ctx K) (ρs : list representation) :
  Forall (rep_ok F) ρs -> rep_ok F (ProdR ρs)
| PrimROK (F : function_ctx K) (ι : primitive_rep) :
  rep_ok F (PrimR ι).

Inductive kind_ok {K : Type} : function_ctx K -> kind -> Prop :=
| VALTYPEOK (F : function_ctx K) (ρ : representation) (γ : linearity) :
  rep_ok F ρ -> kind_ok F (VALTYPE ρ γ)
| MEMTYPEOK (F : function_ctx K) (ζ : sizity) (μ : memory) (γ : linearity) :
  kind_ok F (MEMTYPE ζ μ γ).

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

Inductive has_kind : function_ctx kind -> type kind -> kind -> Prop :=
| KSubValLin F τ ρ :
  has_kind F τ (VALTYPE ρ Unr) ->
  has_kind F τ (VALTYPE ρ Lin)
| KSubMemLin F τ ζ μ :
  has_kind F τ (MEMTYPE ζ μ Unr) ->
  has_kind F τ (MEMTYPE ζ μ Lin)
| KSubUnsized F τ σ μ γ :
  has_kind F τ (MEMTYPE (Sized σ) μ γ) ->
  has_kind F τ (MEMTYPE Unsized μ γ)
| KVar F t κ :
  F.(fc_type_vars) !! t = Some κ ->
  kind_ok F κ ->
  has_kind F (VarT κ t) κ
| KI32 F :
  let κ := VALTYPE (PrimR I32R) Unr in
  has_kind F (NumT κ (IntT I32T)) κ
| KI64 F :
  let κ := VALTYPE (PrimR I64R) Unr in
  has_kind F (NumT κ (IntT I64T)) κ
| KF32 F :
  let κ := VALTYPE (PrimR F32R) Unr in
  has_kind F (NumT κ (FloatT F32T)) κ
| KF64 F :
  let κ := VALTYPE (PrimR F64R) Unr in
  has_kind F (NumT κ (FloatT F64T)) κ
| KSumVal F τs ρs γ :
  Forall2 (fun τ ρ => has_kind F τ (VALTYPE ρ γ)) τs ρs ->
  let κ := VALTYPE (SumR ρs) γ in
  has_kind F (SumT κ τs) κ
| KSumMem F τs ζs μ γ :
  Forall2 (fun τ ζ => has_kind F τ (MEMTYPE ζ μ γ)) τs ζs ->
  let κ := MEMTYPE Unsized μ γ in
  has_kind F (SumT κ τs) κ
| KSumMemSized F τs σs μ γ :
  Forall2 (fun τ σ => has_kind F τ (MEMTYPE (Sized σ) μ γ)) τs σs ->
  let κ := MEMTYPE (Sized (SumS σs)) μ γ in
  has_kind F (SumT κ τs) κ
| KProdVal F τs ρs γ :
  Forall2 (fun τ ρ => has_kind F τ (VALTYPE ρ γ)) τs ρs ->
  let κ := VALTYPE (ProdR ρs) γ in
  has_kind F (ProdT κ τs) κ
| KProdMem F τs τn σs ζ μ γ :
  (* TODO: Maybe the requirement that all preceding components are sized should be in the typing
           rule for load instead. *)
  Forall2 (fun τ σ => has_kind F τ (MEMTYPE (Sized σ) μ γ)) τs σs ->
  has_kind F τn (MEMTYPE ζ μ γ) ->
  let κ := MEMTYPE Unsized μ γ in
  has_kind F (ProdT κ (τs ++ [τn])) κ
| KProdMemSized F τs σs μ γ :
  Forall2 (fun τ σ => has_kind F τ (MEMTYPE (Sized σ) μ γ)) τs σs ->
  let κ := MEMTYPE (Sized (ProdS σs)) μ γ in
  has_kind F (ProdT κ τs) κ
| KArray F τ σ μ :
  has_kind F τ (MEMTYPE (Sized σ) μ Unr) ->
  let κ := MEMTYPE Unsized μ Unr in
  has_kind F (ArrayT κ τ) κ
| KExMem F τ κ :
  has_kind (set fc_own_vars S F) τ κ ->
  has_kind F (ExT κ QMem τ) κ
| KExRep F τ κ :
  has_kind (set fc_rep_vars S F) τ κ ->
  has_kind F (ExT κ QRep τ) κ
| KExSize F τ κ :
  has_kind (set fc_size_vars S F) τ κ ->
  has_kind F (ExT κ QSize τ) κ
| KExType F τ κ0 κ :
  has_kind (set fc_type_vars (cons κ0) F) τ κ ->
  has_kind F (ExT κ (QType κ0) τ) κ
| KRec F τ κ :
  (* TODO: Unfold. *)
  has_kind F τ κ ->
  has_kind F (RecT κ τ) κ
| KRef F ω τ ζ μ γ :
  has_kind F τ (MEMTYPE ζ μ γ) ->
  let κ := VALTYPE (PrimR PtrR) Lin in
  has_kind F (RefT κ ω τ) κ
| KCodeRef F ϕ :
  let κ := VALTYPE (PrimR I32R) Unr in
  has_kind F (CodeRefT κ ϕ) κ
| KRep F ρ0 ρ τ γ :
  has_kind F τ (VALTYPE ρ0 γ) ->
  let κ := VALTYPE ρ γ in
  has_kind F (RepT κ ρ τ) κ
| KPad F σ0 σ τ μ γ :
  has_kind F τ (MEMTYPE (Sized σ0) μ γ) ->
  let κ := MEMTYPE (Sized σ) μ γ in
  has_kind F (PadT κ σ τ) κ
| KSer F τ ρ μ γ :
  has_kind F τ (VALTYPE ρ γ) ->
  let κ := MEMTYPE (Sized (RepS ρ)) μ γ in
  has_kind F (SerT κ τ) κ.

Inductive has_rep : function_ctx kind -> type kind -> representation -> Prop :=
| RepVALTYPE (F : function_ctx kind) (τ : type kind) (ρ : representation) (γ : linearity) :
  has_kind F τ (VALTYPE ρ γ) ->
  has_rep F τ ρ.

Inductive mono_sized : function_ctx kind -> type kind -> Prop :=
| MonoSized (F : function_ctx kind) (τ : type kind) (ρ : representation) (ιs : list primitive_rep) :
  has_rep F τ ρ ->
  mono_rep ρ ιs ->
  mono_sized F τ.

Inductive is_unrestricted : function_ctx kind -> type kind -> Prop :=
| UnrVALTYPE (F : function_ctx kind) (τ : type kind) (ρ : representation) :
  has_kind F τ (VALTYPE ρ Unr) ->
  is_unrestricted F τ
| UnrMEMTYPE (F : function_ctx kind) (τ : type kind) (ζ : sizity) (μ : memory) :
  has_kind F τ (MEMTYPE ζ μ Unr) ->
  is_unrestricted F τ.

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

Inductive path_to {K : Type} : path -> type K -> list (type K) -> type K -> Prop :=
| PathToNil τ :
  path_to [] τ [] τ
| PathToRep ann π ρ τ τs τ' :
  path_to π τ τs τ' ->
  path_to (PCUnwrap :: π) (RepT ann ρ τ) τs τ'
| PathToPad ann π σ τ τs τ' :
  path_to (PCUnwrap :: π) τ τs τ' ->
  path_to π (PadT ann σ τ) τs τ'
| PathToSer ann π τ τs τ' :
  path_to π τ τs τ' ->
  path_to (PCUnwrap :: π) (SerT ann τ) τs τ'
| PathToEx ann π δ τ τs τ' :
  path_to π τ τs τ' ->
  path_to (PCUnwrap :: π) (ExT ann δ τ) τs τ'
| PathToRec ann π τ τs τ' :
  path_to π τ τs τ' ->
  path_to (PCUnwrap :: π) (RecT ann τ) τs τ'
| PathToProd ann n π τs τs0 τs' τ τ0 :
  length τs0 = n ->
  path_to π τ0 τs τ ->
  path_to (PCProj n :: π) (ProdT ann (τs0 ++ τ0 :: τs')) (τs0 ++ τs) τ.

Inductive update_at {K : Type} : path -> type K -> type K -> type K -> type K -> Prop :=
| UpdateAtNil τ τ' :
  update_at [] τ τ τ' τ'
| UpdateAtRep ann π ρ τ τ' τ__π τ__π' :
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCUnwrap :: π) (RepT ann ρ τ) τ__π (RepT ann ρ τ') τ__π'
| UpdateAtPad ann π σ τ τ' τ__π τ__π' :
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCUnwrap :: π) (PadT ann σ τ) τ__π (PadT ann σ τ') τ__π'
| UpdateAtSer ann π τ τ' τ__π τ__π' :
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCUnwrap :: π) (SerT ann τ) τ__π (SerT ann τ') τ__π'
| UpdateAtEx ann π δ τ τ' τ__π τ__π'  :
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCUnwrap :: π) (ExT ann δ τ) τ__π (ExT ann δ τ') τ__π'
| UpdateAtRec ann π τ τ' τ__π τ__π' :
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCUnwrap :: π) (RecT ann τ) τ__π (RecT ann τ') τ__π'
| UpdateAtProd ann π τ τ' τ__π τ__π' τs τs' n :
  length τs = n ->
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCProj n :: π) (ProdT ann (τs ++ τ :: τs')) τ__π (ProdT ann (τs ++ τ' :: τs')) τ__π'.

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

Inductive stores_as : function_ctx kind -> type kind -> type kind -> Prop :=
| SASer F κ τ :
  stores_as F τ (SerT κ τ)
| SAPad F κ τ τ' ρ ιs σ n :
  has_rep F τ ρ ->
  mono_rep ρ ιs ->
  mono_size σ n ->
  list_sum (map primitive_size ιs) <= n ->
  stores_as F τ τ' ->
  stores_as F τ (PadT κ σ τ')
| SAProd F κ τs τs' :
  Forall2 (stores_as F) τs τs' ->
  stores_as F (ProdT κ τs) (ProdT κ τs').

(* Handy name for the converse of stores_as. *)
Definition loads_as F τ τ' := stores_as F τ' τ.

Inductive module_ctx_ok : module_ctx kind -> Prop :=
| MC_OK (gs : list (mutability * type kind)) ts :
  Forall (fun '(_, τ) => is_unrestricted fc_empty τ) gs ->
  module_ctx_ok {| mc_globals := gs; mc_table := ts |}.

(* TODO *)
Inductive num_instr_has_type : num_instr -> arrow_type kind -> Prop :=.

Inductive instr_has_type :
  module_ctx kind ->
  function_ctx kind ->
  local_ctx kind ->
  instr (arrow_type kind) kind ->
  arrow_type kind ->
  local_ctx kind ->
  Prop :=
| TNop M F L :
  let χ := ArrowT [] [] in
  instr_has_type M F L (INop χ) χ L
| TDrop M F L τ :
  is_unrestricted F τ ->
  let χ := ArrowT [τ] [] in
  instr_has_type M F L (IDrop χ) χ L
| TUnreachable M F L τs1 τs2 le :
  let L' := update_locals le L in
  let χ := ArrowT τs1 τs2 in
  instr_has_type M F L (IUnreachable χ) χ L'
| TNum M F L en χ :
  num_instr_has_type en χ ->
  instr_has_type M F L (INum χ en) χ L
| TNumConst M F L κ ν n :
  has_kind F (NumT κ ν) κ ->
  let χ := ArrowT [] [NumT κ ν] in
  instr_has_type M F L (INumConst χ ν n) χ L
| TBlock M F L τs1 τs2 le es :
  let L' := update_locals le L in
  let F' := set fc_labels (cons (τs2, L')) F in
  let χ := ArrowT τs1 τs2 in
  expr_has_type M F' L es χ L' ->
  instr_has_type M F L (IBlock χ (ArrowT τs1 τs2) le es) χ L'
| TLoop M F L τs1 τs2 es :
  let F' := set fc_labels (cons (τs1, L)) F in
  let χ := ArrowT τs1 τs2 in
  expr_has_type M F' L es χ L ->
  instr_has_type M F L (ILoop χ χ es) χ L
| TIte M F L χ le es1 es2 :
  let L' := update_locals le L in
  expr_has_type M F L es1 χ L' ->
  expr_has_type M F L es2 χ L' ->
  instr_has_type M F L (IIte χ χ le es1 es2) χ L'
| TBr M F L n τs τs1 τs2 le :
  F.(fc_labels) !! n = Some (τs, L) ->
  Forall (is_unrestricted F) τs1 ->
  let χ := ArrowT (τs1 ++ τs) τs2 in
  let L' := update_locals le L in
  instr_has_type M F L (IBr χ n) χ L'
| TBrIf M F L n τs κ :
  F.(fc_labels) !! n = Some (τs, L) ->
  let τ := NumT κ (IntT I32T) in
  has_kind F τ κ ->
  let χ := ArrowT (τs ++ [τ]) τs in
  instr_has_type M F L (IBrIf χ n) χ L
| TBrTable M F L L' ns n τs τs1 τs2 κ :
  Forall (fun i => F.(fc_labels) !! i = Some (τs, L)) (n :: ns) ->
  Forall (is_unrestricted F) τs1 ->
  let τ := NumT κ (IntT I32T) in
  has_kind F τ κ ->
  let χ := ArrowT (τs1 ++ τs ++ [τ]) τs2 in
  instr_has_type M F L (IBrTable χ ns n) χ L'
| TReturn M F L le τs τs1 τs2 :
  F.(fc_result_type) = τs ->
  Forall (is_unrestricted F) τs1 ->
  let L' := update_locals le L in
  let χ := ArrowT (τs1 ++ τs) τs2 in
  instr_has_type M F L (IReturn χ) χ L'
| TLocalGet M F L n τ ρ κ0 κ :
  L !! n = Some τ ->
  has_rep F τ ρ ->
  let τ' := RepT κ ρ (ProdT κ0 []) in
  has_kind F τ' κ ->
  let L' := <[ n := τ' ]> L in
  let χ := ArrowT [] [τ] in
  instr_has_type M F L (ILocalGet χ n) χ L'
| TLocalGetUnr M F L n τ :
  L !! n = Some τ ->
  is_unrestricted F τ ->
  let χ := ArrowT [] [τ] in
  instr_has_type M F L (ILocalGet χ n) χ L
| TLocalSet M F L n τ τ' ρ :
  L !! n = Some τ ->
  is_unrestricted F τ ->
  has_rep F τ ρ ->
  has_rep F τ' ρ ->
  let L' := <[ n := τ' ]> L in
  let χ := ArrowT [τ'] [] in
  instr_has_type M F L (ILocalSet χ n) χ L'
| TGlobalGet M F L n m τ :
  M.(mc_globals) !! n = Some (m, τ) ->
  let χ := ArrowT [] [τ] in
  instr_has_type M F L (IGlobalGet χ n) χ L
| TGlobalSet M F L n m τ :
  M.(mc_globals) !! n = Some (m, τ) ->
  let χ := ArrowT [τ] [] in
  instr_has_type M F L (IGlobalSet χ n) χ L
| TCodeRef M F L n ϕ κ :
  (mc_table M) !! n = Some ϕ ->
  let τ := CodeRefT κ ϕ in
  has_kind F τ κ ->
  let χ := ArrowT [] [τ] in
  instr_has_type M F L (ICodeRef χ n) χ L
(*
| TCall M F L ann n ixs :
  instr_has_type M F L (ICall ann n ixs) (ArrowT [] []) L
| TCallIndirect M F L ann ixs :
  instr_has_type M F L (ICallIndirect ann ixs) (ArrowT [] []) L
*)
| TGroup M F L n κ τs ρs γ :
  length τs = n ->
  Forall2 (λ τ ρ, has_kind F τ (VALTYPE ρ γ)) τs ρs ->
  let τ := ProdT κ τs in
  has_kind F τ κ ->
  let χ := ArrowT τs [τ] in
  instr_has_type M F L (IGroup χ n) χ L
| TUngroup M F L τs ρ γ :
  let κ := VALTYPE ρ γ in
  let τ := ProdT κ τs in
  has_kind F τ κ ->
  let χ := ArrowT [τ] τs in
  instr_has_type M F L (IUngroup χ) χ L
(* These require setting up substitution.
| TFold M F L ann τ :
  instr_has_type M F L (IFold ann τ) (ArrowT [] []) L
| TUnfold M F L ann :
  instr_has_type M F L (IUnfold ann) (ArrowT [] []) L
| TPack M F L ann κ ix :
  instr_has_type M F L (IPack ann κ ix) (ArrowT [] []) L
| TUnpack M F L ann χ le es :
  instr_has_type M F L (IUnpack ann χ le es) (ArrowT [] []) L
*)
| TWrap M F L ρ0 ρ ιs0 ιs τ0 κ :
  mono_rep ρ0 ιs0 ->
  mono_rep ρ ιs ->
  convertible_to ιs0 ιs ->
  let τ := RepT κ ρ τ0 in
  has_kind F τ κ ->
  let χ := ArrowT [τ0] [τ] in
  instr_has_type M F L (IWrap χ) χ L
| TUnwrap M F L ρ0 ρ ιs0 ιs τ0 κ :
  mono_rep ρ0 ιs0 ->
  mono_rep ρ ιs ->
  convertible_to ιs0 ιs ->
  let τ := RepT κ ρ τ0 in
  has_kind F τ κ ->
  let χ := ArrowT [τ] [τ0] in
  instr_has_type M F L (IUnwrap χ) χ L
| TRefNew M F L μ τ0 τ0' κ :
  stores_as F τ0 τ0' ->
  let τ := RefT κ μ τ0' in
  has_kind F τ κ ->
  let χ := ArrowT [τ0] [τ] in
  instr_has_type M F L (IRefNew χ μ) χ L
| TRefFree M F L τ0 κ :
  is_unrestricted F τ0 ->
  let τ := RefT κ MemMM τ0 in
  has_kind F τ κ ->
  let χ := ArrowT [τ] [] in
  instr_has_type M F L (IRefFree χ) χ L
| TRefDup M F L τ0 κ :
  let τ := RefT κ MemGC τ0 in
  has_kind F τ κ ->
  let χ := ArrowT [τ] [τ; τ] in
  instr_has_type M F L (IRefDup χ) χ L
| TRefDrop M F L τ0 κ :
  let τ := RefT κ MemGC τ0 in
  has_kind F τ κ ->
  let χ := ArrowT [τ] [] in
  instr_has_type M F L (IRefDrop χ) χ L
| TRefLoad M F L π μ τ0 τs__off τ0' ρ ιs κ :
  path_to π τ0 τs__off τ0' ->
  Forall (mono_sized F) τs__off ->
  has_kind F τ0' (VALTYPE ρ Unr) ->
  mono_rep ρ ιs ->
  let τ := RefT κ μ τ0 in
  has_kind F τ κ ->
  let χ := ArrowT [τ] [τ; τ0'] in
  instr_has_type M F L (IRefLoad χ π) χ L
| TRefStore M F L π μ τ0 τs τᵥ τ__π κ :
  path_to π τ0 τs τ__π ->
  stores_as F τᵥ τ__π ->
  is_unrestricted F τ__π ->
  let τ := RefT κ μ τ0 in
  has_kind F τ κ ->
  let χ := ArrowT [τ; τᵥ] [τ] in
  instr_has_type M F L (IRefStore χ π) χ L
| TRefStoreUniq M F L ann π μ τ0 τ0' τᵥ τᵥ' τₘ τₘ' κ κ' σ σ' γ n :
  stores_as F τᵥ τₘ' ->
  update_at π τ0 τₘ τ0' τₘ' ->
  has_kind F τₘ (MEMTYPE (Sized σ) μ Unr) ->
  has_kind F τₘ' (MEMTYPE (Sized σ') μ γ) ->
  mono_size σ n ->
  mono_size σ' n ->
  let τ := RefT κ MemMM τ0 in
  let τ' := RefT κ' MemMM τ0' in
  has_kind F τ κ ->
  has_kind F τ' κ' ->
  instr_has_type M F L (IRefStore ann π) (ArrowT [τ; τᵥ'] [τ']) L
| TRefSwap M F L π γ ρ ιs μ τ0 τᵥ τₘ τs__off κ :
  has_kind F τᵥ (VALTYPE ρ γ) ->
  mono_rep ρ ιs ->
  path_to π τ0 τs__off τₘ ->
  loads_as F τᵥ τₘ ->
  Forall (mono_sized F) τs__off ->
  let τ := RefT κ μ τ0 in
  has_kind F τ κ ->
  let χ := ArrowT [τ; τᵥ] [τ; τᵥ] in
  instr_has_type M F L (IRefSwap χ π) χ L
| TRefSwapUniq M F L π γ ρ ιs τ0 τ0' τᵥ τᵥ' τₘ τₘ' τs__off κ κ' :
  has_kind F τᵥ (VALTYPE ρ γ) ->
  mono_rep ρ ιs ->
  path_to π τ0 τs__off τₘ ->
  loads_as F τᵥ τₘ ->
  stores_as F τᵥ' τₘ' ->
  update_at π τ0 τₘ τ0' τₘ' ->
  Forall (mono_sized F) τs__off ->
  let τ := RefT κ MemMM τ0 in
  let τ' := RefT κ' MemMM τ0' in
  has_kind F τ κ ->
  has_kind F τ' κ' ->
  let χ := ArrowT [τ; τᵥ'] [τ'; τᵥ] in
  instr_has_type M F L (IRefSwap χ π) χ L

with expr_has_type :
  module_ctx kind ->
  function_ctx kind ->
  local_ctx kind ->
  expr (arrow_type kind) kind ->
  arrow_type kind ->
  local_ctx kind ->
  Prop :=
| TNil M F L :
  expr_has_type M F L [] (ArrowT [] []) L
| TCons M F L1 L2 L3 e es τs1 τs2 τs3 :
  instr_has_type M F L1 e (ArrowT τs1 τs2) L2 ->
  expr_has_type M F L2 es (ArrowT τs2 τs3) L3 ->
  expr_has_type M F L1 (e :: es) (ArrowT τs1 τs3) L3.
