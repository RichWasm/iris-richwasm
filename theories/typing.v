From Stdlib Require Import List.
Import ListNotations.

Require Import stdpp.list.

Require Import RecordUpdate.RecordUpdate.

Require Import RichWasm.syntax.

Record module_ctx :=
  { mc_globals : list (mutability * type);
    mc_table : list function_type }.

Arguments module_ctx : clear implicits.

Definition local_ctx := list type.

Record function_ctx :=
  { fc_return_type : list type;
    fc_labels : list (list type * local_ctx);
    fc_mem_vars : nat;
    fc_rep_vars : nat;
    fc_size_vars : nat;
    fc_type_vars : list kind }.

Arguments function_ctx : clear implicits.

Definition fc_empty : function_ctx :=
  {| fc_return_type := [];
     fc_labels := [];
     fc_mem_vars := 0;
     fc_rep_vars := 0;
     fc_size_vars := 0;
     fc_type_vars := [] |}.

Global Instance eta_function_ctx : Settable _ :=
  settable! Build_function_ctx
  <fc_return_type; fc_labels; fc_mem_vars; fc_rep_vars; fc_size_vars; fc_type_vars>.

Definition update_locals (ξ : local_fx) (L : local_ctx) : local_ctx :=
  let 'LocalFx l := ξ in
  fold_left (fun acc '(i, τ) => <[ i := τ ]> acc) l L.

Inductive rep_ok : function_ctx -> representation -> Prop :=
| VarROK (F : function_ctx) (r : nat) :
  r < F.(fc_rep_vars) -> rep_ok F (VarR r)
| SumROK (F : function_ctx) (ρs : list representation) :
  Forall (rep_ok F) ρs -> rep_ok F (SumR ρs)
| ProdROK (F : function_ctx) (ρs : list representation) :
  Forall (rep_ok F) ρs -> rep_ok F (ProdR ρs)
| PrimROK (F : function_ctx) (ι : primitive_rep) :
  rep_ok F (PrimR ι).

Inductive kind_ok : function_ctx -> kind -> Prop :=
| VALTYPEOK (F : function_ctx) (ρ : representation) (γ : copyability) (δ : dropability) :
  rep_ok F ρ -> kind_ok F (VALTYPE ρ γ δ)
| MEMTYPEOK (F : function_ctx) (ζ : sizity) (μ : memory) (δ : dropability) :
  kind_ok F (MEMTYPE ζ μ δ).

Inductive mono_mem : memory -> Prop :=
| MonoMemMM MemMM : mono_mem MemMM
| MonoMemGC MemGC : mono_mem MemGC.

Inductive mono_rep : representation -> list primitive_rep -> Prop :=
| MonoSumR (ρs : list representation) (ιss : list (list primitive_rep)) :
  Forall2 mono_rep ρs ιss ->
  (* TODO: Use an efficient packing. *)
  mono_rep (SumR ρs) (concat ιss)
| MonoProdR (ρs : list representation) (ιss : list (list primitive_rep)) :
  Forall2 mono_rep ρs ιss ->
  mono_rep (ProdR ρs) (concat ιss)
| MonoPrim :
  mono_rep (PrimR ι) [ι].

Definition primitive_size (ι : primitive_rep) : nat :=
  match ι with
  | PtrR => 1
  | I32R => 1
  | I64R => 2
  | F32R => 1
  | F64R => 2
  end.

Inductive has_kind : function_ctx -> type -> kind -> Prop :=
| KSubValCopy F τ ρ δ :
  has_kind F τ (VALTYPE ρ ImCopy δ) ->
  has_kind F τ (VALTYPE ρ ExCopy δ)
| KSubValDrop F τ ρ γ :
  has_kind F τ (VALTYPE ρ γ ImDrop) ->
  has_kind F τ (VALTYPE ρ γ ExDrop)
| KSubMemDrop F τ ζ μ :
  has_kind F τ (MEMTYPE ζ μ ImDrop) ->
  has_kind F τ (MEMTYPE ζ μ ExDrop)
| KSubSizity F τ σ μ γ :
  has_kind F τ (MEMTYPE (Sized σ) μ γ) ->
  has_kind F τ (MEMTYPE Unsized μ γ)
| KVar F t κ :
  F.(fc_type_vars) !! t = Some κ ->
  kind_ok F κ ->
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
| KSumVal F τs ρs γ δ :
  Forall2 (fun τ ρ => has_kind F τ (VALTYPE ρ γ δ)) τs ρs ->
  let κ := VALTYPE (SumR ρs) γ δ in
  has_kind F (SumT κ τs) κ
| KSumMem F τs ζs μ δ :
  Forall2 (fun τ ζ => has_kind F τ (MEMTYPE ζ μ δ)) τs ζs ->
  let κ := MEMTYPE Unsized μ δ in
  has_kind F (SumT κ τs) κ
| KSumMemSized F τs σs μ δ :
  Forall2 (fun τ σ => has_kind F τ (MEMTYPE (Sized σ) μ δ)) τs σs ->
  let κ := MEMTYPE (Sized (SumS σs)) μ δ in
  has_kind F (SumT κ τs) κ
| KProdVal F τs ρs γ δ :
  Forall2 (fun τ ρ => has_kind F τ (VALTYPE ρ γ δ)) τs ρs ->
  let κ := VALTYPE (ProdR ρs) γ δ in
  has_kind F (ProdT κ τs) κ
| KProdMem F τs τn σs ζ μ δ :
  (* TODO: Maybe the requirement that all preceding components are sized should be in the typing
           rule for load instead. *)
  Forall2 (fun τ σ => has_kind F τ (MEMTYPE (Sized σ) μ δ)) τs σs ->
  has_kind F τn (MEMTYPE ζ μ δ) ->
  let κ := MEMTYPE Unsized μ δ in
  has_kind F (ProdT κ (τs ++ [τn])) κ
| KProdMemSized F τs σs μ δ :
  Forall2 (fun τ σ => has_kind F τ (MEMTYPE (Sized σ) μ δ)) τs σs ->
  let κ := MEMTYPE (Sized (ProdS σs)) μ δ in
  has_kind F (ProdT κ τs) κ
| KArr F τ σ μ δ :
  has_kind F τ (MEMTYPE (Sized σ) μ δ) ->
  let κ := MEMTYPE Unsized μ δ in
  has_kind F (ArrT κ τ) κ
| KExMem F τ κ :
  has_kind (set fc_mem_vars S F) τ κ ->
  has_kind F (ExMemT κ τ) κ
| KExRep F τ κ :
  has_kind (set fc_rep_vars S F) τ κ ->
  has_kind F (ExRepT κ τ) κ
| KExSize F τ κ :
  has_kind (set fc_size_vars S F) τ κ ->
  has_kind F (ExSizeT κ τ) κ
| KExType F τ κ0 κ :
  has_kind (set fc_type_vars (cons κ0) F) τ κ ->
  has_kind F (ExTypeT κ κ0 τ) κ
| KRec F τ κ :
  (* TODO: Unfold. *)
  has_kind F τ κ ->
  has_kind F (RecT κ τ) κ
| KRef F (μ : memory) τ ζ μ δ :
  has_kind F τ (MEMTYPE ζ μ δ) ->
  let κ := VALTYPE (PrimR PtrR) NoCopy NoDrop in
  has_kind F (RefT κ μ τ) κ
| KRefMMDrop F τ ζ :
  has_kind F τ (MEMTYPE ζ MemMM ImDrop) ->
  let κ := VALTYPE (PrimR PtrR) NoCopy ExDrop in
  has_kind F (RefT κ MemMM τ) κ
| KRefGC F τ ζ δ :
  has_kind F τ (MEMTYPE ζ MemGC δ) ->
  let κ := VALTYPE (PrimR PtrR) ExCopy ExDrop in
  has_kind F (RefT κ MemGC τ) κ
| KGCPtr F τ ζ δ :
  has_kind F τ (MEMTYPE ζ MemGC δ) ->
  let κ := MEMTYPE (Sized (ConstS 1)) MemGC ImDrop in
  has_kind F (GCPtrT κ τ) κ
| KCodeRef F ϕ :
  let κ := VALTYPE (PrimR I32R) ImCopy ImDrop in
  has_kind F (CodeRefT κ ϕ) κ
| KRep F ρ0 ρ τ γ δ :
  has_kind F τ (VALTYPE ρ0 γ δ) ->
  let κ := VALTYPE ρ γ δ in
  has_kind F (RepT κ ρ τ) κ
| KPad F σ0 σ τ μ δ :
  has_kind F τ (MEMTYPE (Sized σ0) μ δ) ->
  let κ := MEMTYPE (Sized σ) μ δ in
  has_kind F (PadT κ σ τ) κ
| KSer F τ ρ μ γ δ :
  has_kind F τ (VALTYPE ρ γ δ) ->
  let κ := MEMTYPE (Sized (RepS ρ)) μ δ in
  has_kind F (SerT κ τ) κ.

Inductive has_rep : function_ctx -> type -> representation -> Prop :=
| RepVALTYPE F τ ρ γ δ :
  has_kind F τ (VALTYPE ρ γ δ) ->
  has_rep F τ ρ.

Inductive mono_sized : function_ctx -> type -> Prop :=
| MonoSized (F : function_ctx) (τ : type) (ρ : representation) (ιs : list primitive_rep) :
  has_rep F τ ρ ->
  mono_rep ρ ιs ->
  mono_sized F τ.

Inductive has_copyability : function_ctx -> type -> copyability -> Prop :=
| CopyVALTYPE F τ ρ γ δ :
  has_kind F τ (VALTYPE ρ γ δ) ->
  has_copyability F τ γ.

Inductive has_dropability : function_ctx -> type -> dropability -> Prop :=
| DropVALTYPE F τ ρ γ δ :
  has_kind F τ (VALTYPE ρ γ δ) ->
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

Inductive path_to : path -> type -> list type -> type -> Prop :=
| PathToNil τ :
  path_to [] τ [] τ
| PathToRep κ π ρ τ τs τ' :
  path_to π τ τs τ' ->
  path_to (PCUnwrap :: π) (RepT κ ρ τ) τs τ'
| PathToPad κ π σ τ τs τ' :
  path_to (PCUnwrap :: π) τ τs τ' ->
  path_to π (PadT κ σ τ) τs τ'
| PathToSer κ π τ τs τ' :
  path_to π τ τs τ' ->
  path_to (PCUnwrap :: π) (SerT κ τ) τs τ'
| PathToExMem π κ τ τs τ' :
  path_to π τ τs τ' ->
  path_to (PCUnwrap :: π) (ExMemT κ τ) τs τ'
| PathToExRep π κ τ τs τ' :
  path_to π τ τs τ' ->
  path_to (PCUnwrap :: π) (ExRepT κ τ) τs τ'
| PathToExSize π κ τ τs τ' :
  path_to π τ τs τ' ->
  path_to (PCUnwrap :: π) (ExSizeT κ τ) τs τ'
| PathToExType π κ κ0 τ τs τ' :
  path_to π τ τs τ' ->
  path_to (PCUnwrap :: π) (ExTypeT κ κ0 τ) τs τ'
| PathToRec ann π τ τs τ' :
  path_to π τ τs τ' ->
  path_to (PCUnwrap :: π) (RecT ann τ) τs τ'
| PathToProd ann n π τs τs0 τs' τ τ0 :
  length τs0 = n ->
  path_to π τ0 τs τ ->
  path_to (PCProj n :: π) (ProdT ann (τs0 ++ τ0 :: τs')) (τs0 ++ τs) τ.

(* TODO: Merge this with path_to. *)
Inductive update_at : path -> type -> type -> type -> type -> Prop :=
| UpdateAtNil τ τ' :
  update_at [] τ τ τ' τ'
| UpdateAtRep κ π ρ τ τ' τ__π τ__π' :
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCUnwrap :: π) (RepT κ ρ τ) τ__π (RepT κ ρ τ') τ__π'
| UpdateAtPad κ π σ τ τ' τ__π τ__π' :
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCUnwrap :: π) (PadT κ σ τ) τ__π (PadT κ σ τ') τ__π'
| UpdateAtSer κ π τ τ' τ__π τ__π' :
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCUnwrap :: π) (SerT κ τ) τ__π (SerT κ τ') τ__π'
| UpdateAtExMem κ π τ τ' τ__π τ__π'  :
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCUnwrap :: π) (ExMemT κ τ) τ__π (ExMemT κ τ') τ__π'
| UpdateAtExRep κ π τ τ' τ__π τ__π'  :
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCUnwrap :: π) (ExRepT κ τ) τ__π (ExRepT κ τ') τ__π'
| UpdateAtExSize κ π τ τ' τ__π τ__π'  :
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCUnwrap :: π) (ExSizeT κ τ) τ__π (ExSizeT κ τ') τ__π'
| UpdateAtExType κ κ0 π τ τ' τ__π τ__π'  :
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCUnwrap :: π) (ExTypeT κ κ0 τ) τ__π (ExTypeT κ κ0 τ') τ__π'
| UpdateAtRec κ π τ τ' τ__π τ__π' :
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCUnwrap :: π) (RecT κ τ) τ__π (RecT κ τ') τ__π'
| UpdateAtProd κ π τ τ' τ__π τ__π' τs τs' n :
  length τs = n ->
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCProj n :: π) (ProdT κ (τs ++ τ :: τs')) τ__π (ProdT κ (τs ++ τ' :: τs')) τ__π'.

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

Inductive module_ctx_ok : module_ctx -> Prop :=
| MC_OK (gs : list (mutability * type)) ts :
  Forall (fun '(_, τ) => exists ρ γ, has_kind fc_empty τ (VALTYPE ρ γ ImDrop)) gs ->
  module_ctx_ok {| mc_globals := gs; mc_table := ts |}.

(* TODO *)
Inductive num_instr_has_type : num_instruction -> arrow_type -> Prop :=.

Inductive instr_has_type :
  module_ctx -> function_ctx -> local_ctx -> instruction -> arrow_type -> local_ctx -> Prop :=
| TNop M F L :
  let χ := ArrowT [] [] in
  instr_has_type M F L (INop χ) χ L
| TUnreachable M F L L' τs1 τs2 :
  let χ := ArrowT τs1 τs2 in
  instr_has_type M F L (IUnreachable χ) χ L'
| TCopy M F L τ :
  has_copyability F τ ExCopy ->
  let χ := ArrowT [τ] [τ; τ] in
  instr_has_type M F L (ICopy χ) χ L
| TDrop M F L τ :
  has_dropability F τ ExDrop ->
  let χ := ArrowT [τ] [] in
  instr_has_type M F L (IDrop χ) χ L
| TNum M F L eₙ χ :
  num_instr_has_type eₙ χ ->
  instr_has_type M F L (INum χ eₙ) χ L
| TNumConst M F L κ ν n :
  has_kind F (NumT κ ν) κ ->
  let χ := ArrowT [] [NumT κ ν] in
  instr_has_type M F L (INumConst χ n) χ L
| TBlock M F L τs1 τs2 ξ es :
  let L' := update_locals ξ L in
  let F' := set fc_labels (cons (τs2, L')) F in
  let χ := ArrowT τs1 τs2 in
  instrs_have_type M F' L es χ L' ->
  instr_has_type M F L (IBlock χ ξ es) χ L'
| TLoop M F L τs1 τs2 es :
  let F' := set fc_labels (cons (τs1, L)) F in
  let χ := ArrowT τs1 τs2 in
  instrs_have_type M F' L es χ L ->
  instr_has_type M F L (ILoop χ es) χ L
| TIte M F L χ ξ es1 es2 :
  let L' := update_locals ξ L in
  instrs_have_type M F L es1 χ L' ->
  instrs_have_type M F L es2 χ L' ->
  instr_has_type M F L (IIte χ ξ es1 es2) χ L'
| TBr M F L n τs τs1 τs2 ξ :
  F.(fc_labels) !! n = Some (τs, L) ->
  Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
  let χ := ArrowT (τs1 ++ τs) τs2 in
  let L' := update_locals ξ L in
  instr_has_type M F L (IBr χ n) χ L'
| TBrIf M F L n τs κ :
  F.(fc_labels) !! n = Some (τs, L) ->
  let τ := NumT κ (IntT I32T) in
  has_kind F τ κ ->
  let χ := ArrowT (τs ++ [τ]) τs in
  instr_has_type M F L (IBrIf χ n) χ L
| TBrTable M F L L' ns n τs τs1 τs2 κ :
  Forall (fun i => F.(fc_labels) !! i = Some (τs, L)) (n :: ns) ->
  Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
  let τ := NumT κ (IntT I32T) in
  has_kind F τ κ ->
  let χ := ArrowT (τs1 ++ τs ++ [τ]) τs2 in
  instr_has_type M F L (IBrTable χ ns n) χ L'
| TReturn M F L L' τs τs1 τs2 :
  F.(fc_return_type) = τs ->
  Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
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
| TLocalGetCopy M F L n τ :
  L !! n = Some τ ->
  has_copyability F τ ImCopy ->
  let χ := ArrowT [] [τ] in
  instr_has_type M F L (ILocalGet χ n) χ L
| TLocalSet M F L n τ τ' ρ :
  L !! n = Some τ ->
  has_dropability F τ ImDrop ->
  has_rep F τ ρ ->
  has_rep F τ' ρ ->
  let L' := <[ n := τ' ]> L in
  let χ := ArrowT [τ'] [] in
  instr_has_type M F L (ILocalSet χ n) χ L'
| TGlobalGet M F L n m τ :
  M.(mc_globals) !! n = Some (m, τ) ->
  has_copyability F τ ImCopy ->
  let χ := ArrowT [] [τ] in
  instr_has_type M F L (IGlobalGet χ n) χ L
| TGlobalSet M F L n τ :
  M.(mc_globals) !! n = Some (Mut, τ) ->
  let χ := ArrowT [τ] [] in
  instr_has_type M F L (IGlobalSet χ n) χ L
| TGlobalSwap M F L n τ :
  M.(mc_globals) !! n = Some (Mut, τ) ->
  let χ := ArrowT [τ] [τ] in
  instr_has_type M F L (IGlobalSwap χ n) χ L
| TCodeRef M F L n ϕ κ :
  M.(mc_table) !! n = Some ϕ ->
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
| TGroup M F L κ τs ρs γ δ :
  Forall2 (λ τ ρ, has_kind F τ (VALTYPE ρ γ δ)) τs ρs ->
  let τ := ProdT κ τs in
  has_kind F τ κ ->
  let χ := ArrowT τs [τ] in
  instr_has_type M F L (IGroup χ) χ L
| TUngroup M F L τs ρ γ δ :
  let κ := VALTYPE ρ γ δ in
  let τ := ProdT κ τs in
  has_kind F τ κ ->
  let χ := ArrowT [τ] τs in
  instr_has_type M F L (IUngroup χ) χ L
| TFold M F L τ κ :
  has_kind F τ κ ->
  let τ0 := subst_type MemVar VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
  let χ := ArrowT [τ0] [RecT κ τ] in
  instr_has_type M F L (IFold χ) χ L
| TUnfold M F L τ κ :
  let τ0 := subst_type MemVar VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
  let χ := ArrowT [RecT κ τ] [τ0] in
  instr_has_type M F L (IUnfold χ) χ L
(* These require setting up substitution.
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
  mono_mem μ ->
  stores_as F τ0 τ0' ->
  let τ := RefT κ μ τ0' in
  has_kind F τ κ ->
  let χ := ArrowT [τ0] [τ] in
  instr_has_type M F L (IRefNew χ) χ L
| TRefLoad M F L π μ τ0 τs__off τ0' ρ ιs δ κ :
  path_to π τ0 τs__off τ0' ->
  Forall (mono_sized F) τs__off ->
  has_kind F τ0' (VALTYPE ρ ImCopy δ) ->
  mono_rep ρ ιs ->
  let τ := RefT κ μ τ0 in
  has_kind F τ κ ->
  let χ := ArrowT [τ] [τ; τ0'] in
  instr_has_type M F L (IRefLoad χ π) χ L
| TRefStore M F L π μ τ0 τs τᵥ τ__π κ :
  path_to π τ0 τs τ__π ->
  stores_as F τᵥ τ__π ->
  has_dropability F τ__π ImDrop ->
  let τ := RefT κ μ τ0 in
  has_kind F τ κ ->
  let χ := ArrowT [τ; τᵥ] [τ] in
  instr_has_type M F L (IRefStore χ π) χ L
| TRefMMStore M F L ann π τ0 τ0' τᵥ τᵥ' τₘ τₘ' κ κ' σ δ n :
  stores_as F τᵥ τₘ' ->
  update_at π τ0 τₘ τ0' τₘ' ->
  has_kind F τₘ (MEMTYPE (Sized σ) MemMM ImDrop) ->
  has_kind F τₘ' (MEMTYPE (Sized σ) MemMM δ) ->
  mono_size σ n ->
  let τ := RefT κ MemMM τ0 in
  let τ' := RefT κ' MemMM τ0' in
  has_kind F τ κ ->
  has_kind F τ' κ' ->
  instr_has_type M F L (IRefStore ann π) (ArrowT [τ; τᵥ'] [τ']) L
| TRefSwap M F L π ρ ιs μ τ0 τᵥ τₘ τs__prefix κ :
  mono_rep ρ ιs ->
  path_to π τ0 τs__prefix τₘ ->
  loads_as F τᵥ τₘ ->
  Forall (mono_sized F) τs__prefix ->
  let τ := RefT κ μ τ0 in
  has_kind F τ κ ->
  let χ := ArrowT [τ; τᵥ] [τ; τᵥ] in
  instr_has_type M F L (IRefSwap χ π) χ L
| TRefMMSwap M F L π ρ ιs τ0 τ0' τᵥ τᵥ' τₘ τₘ' τs__prefix κ κ' :
  mono_rep ρ ιs ->
  path_to π τ0 τs__prefix τₘ ->
  loads_as F τᵥ τₘ ->
  stores_as F τᵥ' τₘ' ->
  update_at π τ0 τₘ τ0' τₘ' ->
  Forall (mono_sized F) τs__prefix ->
  let τ := RefT κ MemMM τ0 in
  let τ' := RefT κ' MemMM τ0' in
  has_kind F τ κ ->
  has_kind F τ' κ' ->
  let χ := ArrowT [τ; τᵥ'] [τ'; τᵥ] in
  instr_has_type M F L (IRefSwap χ π) χ L

with instrs_have_type :
  module_ctx -> function_ctx -> local_ctx -> list instruction -> arrow_type -> local_ctx -> Prop :=
| TNil M F L :
  instrs_have_type M F L [] (ArrowT [] []) L
| TCons M F L1 L2 L3 e es τs1 τs2 τs3 :
  instr_has_type M F L1 e (ArrowT τs1 τs2) L2 ->
  instrs_have_type M F L2 es (ArrowT τs2 τs3) L3 ->
  instrs_have_type M F L1 (e :: es) (ArrowT τs1 τs3) L3.

Scheme instr_has_type_mind := Induction for instr_has_type Sort Prop
with instrs_have_type_mind := Induction for instrs_have_type Sort Prop.
