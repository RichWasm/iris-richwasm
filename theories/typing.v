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
    fc_locals : list representation;
    fc_labels : list (list type * local_ctx);
    fc_mem_vars : nat;
    fc_rep_vars : nat;
    fc_size_vars : nat;
    fc_type_vars : list kind }.

Arguments function_ctx : clear implicits.

Definition fc_empty : function_ctx :=
  {| fc_return_type := [];
     fc_locals := [];
     fc_labels := [];
     fc_mem_vars := 0;
     fc_rep_vars := 0;
     fc_size_vars := 0;
     fc_type_vars := [] |}.

Definition subst_function_ctx
  (s__mem : nat -> memory) (s__rep : nat -> representation) (s__size : nat -> size) (s__type : nat -> type)
  (F : function_ctx) :
  function_ctx :=
  {| fc_return_type := map (subst_type s__mem s__rep s__size s__type) F.(fc_return_type);
     fc_locals := map (subst_representation s__rep) F.(fc_locals);
     fc_labels :=
       map
         (fun '(τs, L) =>
            (map (subst_type s__mem s__rep s__size s__type) τs, map (subst_type s__mem s__rep s__size s__type) L))
         F.(fc_labels);
     fc_mem_vars := F.(fc_mem_vars);
     fc_rep_vars := F.(fc_rep_vars);
     fc_size_vars := F.(fc_size_vars);
     fc_type_vars := map (subst_kind s__mem s__rep s__size) F.(fc_type_vars) |}.

Global Instance eta_function_ctx : Settable _ :=
  settable! Build_function_ctx
  <fc_return_type; fc_locals; fc_labels; fc_mem_vars; fc_rep_vars; fc_size_vars; fc_type_vars>.

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
| VALTYPEOK (F : function_ctx) (ρ : representation) (χ : copyability) (δ : dropability) :
  rep_ok F ρ -> kind_ok F (VALTYPE ρ χ δ)
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
| MonoPrim : forall ι,
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
| KSubValExCopy F τ ρ δ :
  has_kind F τ (VALTYPE ρ ImCopy δ) ->
  has_kind F τ (VALTYPE ρ ExCopy δ)
| KSubValNoCopy F τ ρ δ :
  has_kind F τ (VALTYPE ρ ExCopy δ) ->
  has_kind F τ (VALTYPE ρ NoCopy δ)
| KSubValExDrop F τ ρ χ :
  has_kind F τ (VALTYPE ρ χ ImDrop) ->
  has_kind F τ (VALTYPE ρ χ ExDrop)
| KSubValNoDrop F τ ρ χ :
  has_kind F τ (VALTYPE ρ χ ExDrop) ->
  has_kind F τ (VALTYPE ρ χ NoDrop)
| KSubMemExDrop F τ ζ μ :
  has_kind F τ (MEMTYPE ζ μ ImDrop) ->
  has_kind F τ (MEMTYPE ζ μ ExDrop)
| KSubMemNoDrop F τ ζ μ :
  has_kind F τ (MEMTYPE ζ μ ExDrop) ->
  has_kind F τ (MEMTYPE ζ μ NoDrop)
| KSubSizity F τ σ μ δ :
  has_kind F τ (MEMTYPE (Sized σ) μ δ) ->
  has_kind F τ (MEMTYPE Unsized μ δ)
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
| KSumVal F τs ρs χ δ :
  Forall2 (fun τ ρ => has_kind F τ (VALTYPE ρ χ δ)) τs ρs ->
  let κ := VALTYPE (SumR ρs) χ δ in
  has_kind F (SumT κ τs) κ
| KSumMem F τs ζs μ δ :
  Forall2 (fun τ ζ => has_kind F τ (MEMTYPE ζ μ δ)) τs ζs ->
  let κ := MEMTYPE Unsized μ δ in
  has_kind F (SumT κ τs) κ
| KSumMemSized F τs σs μ δ :
  Forall2 (fun τ σ => has_kind F τ (MEMTYPE (Sized σ) μ δ)) τs σs ->
  let κ := MEMTYPE (Sized (SumS σs)) μ δ in
  has_kind F (SumT κ τs) κ
| KProdVal F τs ρs χ δ :
  Forall2 (fun τ ρ => has_kind F τ (VALTYPE ρ χ δ)) τs ρs ->
  let κ := VALTYPE (ProdR ρs) χ δ in
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
| KExixstsMem F τ κ :
  has_kind (set fc_mem_vars S F) τ κ ->
  has_kind F (ExistsMemT κ τ) κ
| KExistsRep F τ κ :
  has_kind (set fc_rep_vars S F) τ κ ->
  has_kind F (ExistsRepT κ τ) κ
| KExistsSize F τ κ :
  has_kind (set fc_size_vars S F) τ κ ->
  has_kind F (ExistsSizeT κ τ) κ
| KExistsType F τ κ0 κ :
  has_kind (set fc_type_vars (cons κ0) F) τ κ ->
  has_kind F (ExistsTypeT κ κ0 τ) κ
| KRec F τ κ :
  (* TODO: Unfold. *)
  has_kind F τ κ ->
  has_kind F (RecT κ τ) κ
| KRef F (μ : memory) τ ζ μ δ :
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
  let κ := VALTYPE (PrimR I32R) ImCopy ImDrop in
  has_kind F (CodeRefT κ ϕ) κ
| KRep F ρ0 ρ τ χ δ :
  has_kind F τ (VALTYPE ρ0 χ δ) ->
  let κ := VALTYPE ρ χ δ in
  has_kind F (RepT κ ρ τ) κ
| KPad F σ0 σ τ μ δ :
  has_kind F τ (MEMTYPE (Sized σ0) μ δ) ->
  let κ := MEMTYPE (Sized σ) μ δ in
  has_kind F (PadT κ σ τ) κ
| KSer F τ ρ μ χ δ :
  has_kind F τ (VALTYPE ρ χ δ) ->
  let κ := MEMTYPE (Sized (RepS ρ)) μ δ in
  has_kind F (SerT κ τ) κ.

Inductive has_rep : function_ctx -> type -> representation -> Prop :=
| RepVALTYPE F τ ρ χ δ :
  has_kind F τ (VALTYPE ρ χ δ) ->
  has_rep F τ ρ.

Inductive mono_sized : function_ctx -> type -> Prop :=
| MonoSized (F : function_ctx) (τ : type) (ρ : representation) (ιs : list primitive_rep) :
  has_rep F τ ρ ->
  mono_rep ρ ιs ->
  mono_sized F τ.

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
| PathToExistsMem π κ τ τs τ' :
  path_to π τ τs τ' ->
  path_to (PCUnwrap :: π) (ExistsMemT κ τ) τs τ'
| PathToExistsRep π κ τ τs τ' :
  path_to π τ τs τ' ->
  path_to (PCUnwrap :: π) (ExistsRepT κ τ) τs τ'
| PathToExistsSize π κ τ τs τ' :
  path_to π τ τs τ' ->
  path_to (PCUnwrap :: π) (ExistsSizeT κ τ) τs τ'
| PathToExstsType π κ κ0 τ τs τ' :
  path_to π τ τs τ' ->
  path_to (PCUnwrap :: π) (ExistsTypeT κ κ0 τ) τs τ'
| PathToRec κ π τ τs τ' :
  path_to π τ τs τ' ->
  path_to (PCUnwrap :: π) (RecT κ τ) τs τ'
| PathToProd κ n π τs τs0 τs' τ τ0 :
  length τs0 = n ->
  path_to π τ0 τs τ ->
  path_to (PCProj n :: π) (ProdT κ (τs0 ++ τ0 :: τs')) (τs0 ++ τs) τ.

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
| UpdateAtExistsMem κ π τ τ' τ__π τ__π'  :
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCUnwrap :: π) (ExistsMemT κ τ) τ__π (ExistsMemT κ τ') τ__π'
| UpdateAtExistsRep κ π τ τ' τ__π τ__π'  :
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCUnwrap :: π) (ExistsRepT κ τ) τ__π (ExistsRepT κ τ') τ__π'
| UpdateAtExistsSize κ π τ τ' τ__π τ__π'  :
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCUnwrap :: π) (ExistsSizeT κ τ) τ__π (ExistsSizeT κ τ') τ__π'
| UpdateAtExistsType κ κ0 π τ τ' τ__π τ__π'  :
  update_at π τ τ__π τ' τ__π' ->
  update_at (PCUnwrap :: π) (ExistsTypeT κ κ0 τ) τ__π (ExistsTypeT κ κ0 τ') τ__π'
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
  Forall (fun '(_, τ) => exists ρ χ, has_kind fc_empty τ (VALTYPE ρ χ ImDrop)) gs ->
  module_ctx_ok {| mc_globals := gs; mc_table := ts |}.

Inductive inst_function_type : function_ctx -> index -> function_type -> function_type -> Prop :=
| FTInstMem F ϕ μ :
  let ϕ' := subst_function_type (unscoped.scons μ VarM) VarR VarS VarT ϕ in
  inst_function_type F (MemI μ) (ForallMemT ϕ) ϕ'
| FTInstRep F ϕ ρ :
  let ϕ' := subst_function_type VarM (unscoped.scons ρ VarR) VarS VarT ϕ in
  inst_function_type F (RepI ρ) (ForallRepT ϕ) ϕ'
| FTInstSize F ϕ σ :
  let ϕ' := subst_function_type VarM VarR (unscoped.scons σ VarS) VarT ϕ in
  inst_function_type F (SizeI σ) (ForallSizeT ϕ) ϕ'
| FTInstType F ϕ τ κ :
  has_kind F τ κ ->
  let ϕ' := subst_function_type VarM VarR VarS (unscoped.scons τ VarT) ϕ in
  inst_function_type F (TypeI τ) (ForallTypeT κ ϕ) ϕ'.

Inductive list_inst_function_type : function_ctx -> list index -> function_type -> function_type -> Prop :=
| FTNil F ϕ :
  list_inst_function_type F [] ϕ ϕ
| FTCons F ϕ ϕ' ϕ'' ix ixs :
  inst_function_type F ix ϕ ϕ' ->
  list_inst_function_type F ixs ϕ' ϕ'' ->
  list_inst_function_type F (ix :: ixs) ϕ ϕ''.

Inductive pack_existential_type : function_ctx -> type -> type -> Prop :=
| PackMem F μ τ' κ' :
  has_kind F τ' κ' ->
  let τ0 := subst_type (unscoped.scons μ VarM) VarR VarS VarT τ' in
  pack_existential_type F τ0 (ExistsMemT κ' τ')
| PackRep F ρ τ' κ' :
  has_kind F τ' κ' ->
  let τ0 := subst_type VarM (unscoped.scons ρ VarR) VarS VarT τ' in
  pack_existential_type F τ0 (ExistsRepT κ' τ')
| PackSize F σ τ' κ' :
  has_kind F τ' κ' ->
  let τ0 := subst_type VarM VarR (unscoped.scons σ VarS) VarT τ' in
  pack_existential_type F τ0 (ExistsSizeT κ' τ')
| PackType F τ τ' κ κ' :
  has_kind F τ κ ->
  has_kind F τ' κ' ->
  let τ0 := subst_type VarM VarR VarS (unscoped.scons τ VarT) τ' in
  pack_existential_type F τ0 (ExistsTypeT κ' κ τ').

(* TODO *)
Inductive num_instr_has_type : num_instruction -> instruction_type -> Prop :=.

Inductive instr_has_type :
  module_ctx -> function_ctx -> local_ctx -> instruction -> instruction_type -> local_ctx -> Prop :=
| TNop M F L :
  let ψ := InstrT [] [] in
  instr_has_type M F L (INop ψ) ψ L
| TUnreachable M F L L' τs1 τs2 :
  let ψ := InstrT τs1 τs2 in
  instr_has_type M F L (IUnreachable ψ) ψ L'
| TCopy M F L τ :
  has_copyability F τ ExCopy ->
  let ψ := InstrT [τ] [τ; τ] in
  instr_has_type M F L (ICopy ψ) ψ L
| TDrop M F L τ :
  has_dropability F τ ExDrop ->
  let ψ := InstrT [τ] [] in
  instr_has_type M F L (IDrop ψ) ψ L
| TNum M F L eₙ ψ :
  num_instr_has_type eₙ ψ ->
  instr_has_type M F L (INum ψ eₙ) ψ L
| TNumConst M F L κ ν n :
  has_kind F (NumT κ ν) κ ->
  let ψ := InstrT [] [NumT κ ν] in
  instr_has_type M F L (INumConst ψ n) ψ L
| TBlock M F L τs1 τs2 ξ es :
  let L' := update_locals ξ L in
  let F' := set fc_labels (cons (τs2, L')) F in
  let ψ := InstrT τs1 τs2 in
  instrs_have_type M F' L es ψ L' ->
  instr_has_type M F L (IBlock ψ ξ es) ψ L'
| TLoop M F L τs1 τs2 es :
  let F' := set fc_labels (cons (τs1, L)) F in
  let ψ := InstrT τs1 τs2 in
  instrs_have_type M F' L es ψ L ->
  instr_has_type M F L (ILoop ψ es) ψ L
| TIte M F L ψ ξ es1 es2 :
  let L' := update_locals ξ L in
  instrs_have_type M F L es1 ψ L' ->
  instrs_have_type M F L es2 ψ L' ->
  instr_has_type M F L (IIte ψ ξ es1 es2) ψ L'
| TBr M F L n τs τs1 τs2 ξ :
  F.(fc_labels) !! n = Some (τs, L) ->
  Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
  let ψ := InstrT (τs1 ++ τs) τs2 in
  let L' := update_locals ξ L in
  instr_has_type M F L (IBr ψ n) ψ L'
| TBrIf M F L n τs κ :
  F.(fc_labels) !! n = Some (τs, L) ->
  let τ := NumT κ (IntT I32T) in
  has_kind F τ κ ->
  let ψ := InstrT (τs ++ [τ]) τs in
  instr_has_type M F L (IBrIf ψ n) ψ L
| TBrTable M F L L' ns n τs τs1 τs2 κ :
  Forall (fun i => F.(fc_labels) !! i = Some (τs, L)) (n :: ns) ->
  Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
  let τ := NumT κ (IntT I32T) in
  has_kind F τ κ ->
  let ψ := InstrT (τs1 ++ τs ++ [τ]) τs2 in
  instr_has_type M F L (IBrTable ψ ns n) ψ L'
| TReturn M F L L' τs τs1 τs2 :
  F.(fc_return_type) = τs ->
  Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
  let ψ := InstrT (τs1 ++ τs) τs2 in
  instr_has_type M F L (IReturn ψ) ψ L'
| TLocalGet M F L n τ ρ κ0 κ :
  L !! n = Some τ ->
  has_rep F τ ρ ->
  let τ' := RepT κ ρ (ProdT κ0 []) in
  has_kind F τ' κ ->
  let L' := <[ n := τ' ]> L in
  let ψ := InstrT [] [τ] in
  instr_has_type M F L (ILocalGet ψ n) ψ L'
| TLocalGetCopy M F L n τ :
  L !! n = Some τ ->
  has_copyability F τ ImCopy ->
  let ψ := InstrT [] [τ] in
  instr_has_type M F L (ILocalGet ψ n) ψ L
| TLocalSet M F L n τ τ' ρ :
  L !! n = Some τ ->
  has_dropability F τ ImDrop ->
  has_rep F τ ρ ->
  has_rep F τ' ρ ->
  let L' := <[ n := τ' ]> L in
  let ψ := InstrT [τ'] [] in
  instr_has_type M F L (ILocalSet ψ n) ψ L'
| TGlobalGet M F L n m τ :
  M.(mc_globals) !! n = Some (m, τ) ->
  has_copyability F τ ImCopy ->
  let ψ := InstrT [] [τ] in
  instr_has_type M F L (IGlobalGet ψ n) ψ L
| TGlobalSet M F L n τ :
  M.(mc_globals) !! n = Some (Mut, τ) ->
  has_dropability F τ ImDrop ->
  let ψ := InstrT [τ] [] in
  instr_has_type M F L (IGlobalSet ψ n) ψ L
| TGlobalSwap M F L n τ :
  M.(mc_globals) !! n = Some (Mut, τ) ->
  let ψ := InstrT [τ] [τ] in
  instr_has_type M F L (IGlobalSwap ψ n) ψ L
| TCodeRef M F L i ϕ κ :
  M.(mc_table) !! i = Some ϕ ->
  let τ := CodeRefT κ ϕ in
  has_kind F τ κ ->
  let ψ := InstrT [] [τ] in
  instr_has_type M F L (ICodeRef ψ i) ψ L
| TInst M F L ix ϕ ϕ' κ :
  inst_function_type F ix ϕ ϕ' ->
  let ψ := InstrT [CodeRefT κ ϕ] [CodeRefT κ ϕ'] in
  instr_has_type M F L (IInst ψ ix) ψ L
| TCall M F L i ixs ϕ τs1 τs2 :
  M.(mc_table) !! i = Some ϕ ->
  let ψ := InstrT τs1 τs2 in
  list_inst_function_type F ixs ϕ (MonoFunT ψ) ->
  instr_has_type M F L (ICall ψ i ixs) ψ L
| TCallIndirect M F L τs1 τs2 κ :
  let ψ := InstrT (τs1 ++ [CodeRefT κ (MonoFunT (InstrT τs1 τs2))]) τs2 in
  instr_has_type M F L (ICallIndirect ψ) ψ L
| TInject M F L i τ τs κ :
  τs !! i = Some τ ->
  let ψ := InstrT [τ] [SumT κ τs] in
  instr_has_type M F L (IInject ψ i) ψ L
| TCase M F L ξ κ τ' τs ess :
  let L' := update_locals ξ L in
  Forall2 (fun τ es => instrs_have_type M F L es (InstrT [τ] [τ']) L') τs ess ->
  let ψ := InstrT [SumT κ τs] [τ'] in
  instr_has_type M F L (ICase ψ ξ ess) ψ L'
| TGroup M F L τs κ ρs χ δ :
  Forall2 (λ τ ρ, has_kind F τ (VALTYPE ρ χ δ)) τs ρs ->
  let τ := ProdT κ τs in
  has_kind F τ κ ->
  let ψ := InstrT τs [τ] in
  instr_has_type M F L (IGroup ψ) ψ L
| TUngroup M F L τs ρ χ δ :
  let κ := VALTYPE ρ χ δ in
  let τ := ProdT κ τs in
  has_kind F τ κ ->
  let ψ := InstrT [τ] τs in
  instr_has_type M F L (IUngroup ψ) ψ L
| TFold M F L τ κ :
  has_kind F τ κ ->
  let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
  let ψ := InstrT [τ0] [RecT κ τ] in
  instr_has_type M F L (IFold ψ) ψ L
| TUnfold M F L τ κ :
  let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
  let ψ := InstrT [RecT κ τ] [τ0] in
  instr_has_type M F L (IUnfold ψ) ψ L
| TPack M F L τ τ' :
  pack_existential_type F τ τ' ->
  let ψ := InstrT [τ] [τ'] in
  instr_has_type M F L (IPack ψ) ψ L
| TUnpackMem M F L κ τ τs1 τs2 ξ es :
  let F' := set fc_mem_vars S (subst_function_ctx (up_memory VarM) VarR VarS VarT F) in
  let L' := update_locals ξ L in
  let weak := map (subst_type (up_memory VarM) VarR VarS VarT) in
  instrs_have_type M F' (weak L) es (InstrT (weak τs1 ++ [τ]) (weak τs2)) (weak L') ->
  let ψ := InstrT (τs1 ++ [ExistsMemT κ τ]) τs2 in
  instr_has_type M F L (IUnpack ψ ξ es) ψ L'
| TUnpackRep M F L κ τ τs1 τs2 ξ es :
  let F' := set fc_rep_vars S (subst_function_ctx VarM (up_representation VarR) VarS VarT F) in
  let L' := update_locals ξ L in
  let weak := map (subst_type VarM (up_representation VarR) VarS VarT) in
  instrs_have_type M F' (weak L) es (InstrT (weak τs1 ++ [τ]) (weak τs2)) (weak L') ->
  let ψ := InstrT (τs1 ++ [ExistsRepT κ τ]) τs2 in
  instr_has_type M F L (IUnpack ψ ξ es) ψ L'
| TUnpackSize M F L κ τ τs1 τs2 ξ es :
  let F' := set fc_size_vars S (subst_function_ctx VarM VarR (up_size VarS) VarT F) in
  let L' := update_locals ξ L in
  let weak := map (subst_type VarM VarR (up_size VarS) VarT) in
  instrs_have_type M F' (weak L) es (InstrT (weak τs1 ++ [τ]) (weak τs2)) (weak L') ->
  let ψ := InstrT (τs1 ++ [ExistsRepT κ τ]) τs2 in
  instr_has_type M F L (IUnpack ψ ξ es) ψ L'
| TUnpackType M F L κ0 κ τ τs1 τs2 ξ es :
  let F' := set fc_type_vars (cons κ0) (subst_function_ctx VarM VarR VarS (up_type VarT) F) in
  let L' := update_locals ξ L in
  let weak := map (subst_type VarM VarR VarS (up_type VarT)) in
  instrs_have_type M F' (weak L) es (InstrT (weak τs1 ++ [τ]) (weak τs2)) (weak L') ->
  let ψ := InstrT (τs1 ++ [ExistsTypeT κ κ0 τ]) τs2 in
  instr_has_type M F L (IUnpack ψ ξ es) ψ L'
| TWrap M F L ρ0 ρ ιs0 ιs τ0 κ :
  mono_rep ρ0 ιs0 ->
  mono_rep ρ ιs ->
  convertible_to ιs0 ιs ->
  let τ := RepT κ ρ τ0 in
  has_kind F τ κ ->
  let ψ := InstrT [τ0] [τ] in
  instr_has_type M F L (IWrap ψ) ψ L
| TUnwrap M F L ρ0 ρ ιs0 ιs τ0 κ :
  mono_rep ρ0 ιs0 ->
  mono_rep ρ ιs ->
  convertible_to ιs0 ιs ->
  let τ := RepT κ ρ τ0 in
  has_kind F τ κ ->
  let ψ := InstrT [τ] [τ0] in
  instr_has_type M F L (IUnwrap ψ) ψ L
| TRefNew M F L μ τ0 τ0' κ :
  mono_mem μ ->
  stores_as F τ0 τ0' ->
  let τ := RefT κ μ τ0' in
  has_kind F τ κ ->
  let ψ := InstrT [τ0] [τ] in
  instr_has_type M F L (IRefNew ψ) ψ L
| TRefLoad M F L π μ τ0 τs__off τ0' ρ ιs δ κ :
  path_to π τ0 τs__off τ0' ->
  Forall (mono_sized F) τs__off ->
  has_kind F τ0' (VALTYPE ρ ImCopy δ) ->
  mono_rep ρ ιs ->
  let τ := RefT κ μ τ0 in
  has_kind F τ κ ->
  let ψ := InstrT [τ] [τ; τ0'] in
  instr_has_type M F L (IRefLoad ψ π) ψ L
| TRefStore M F L π μ τ0 τs τᵥ τ__π κ :
  path_to π τ0 τs τ__π ->
  stores_as F τᵥ τ__π ->
  has_dropability F τ__π ImDrop ->
  let τ := RefT κ μ τ0 in
  has_kind F τ κ ->
  let ψ := InstrT [τ; τᵥ] [τ] in
  instr_has_type M F L (IRefStore ψ π) ψ L
| TRefMMStore M F L π τ0 τ0' τᵥ τᵥ' τₘ τₘ' κ κ' σ δ n :
  stores_as F τᵥ τₘ' ->
  update_at π τ0 τₘ τ0' τₘ' ->
  has_kind F τₘ (MEMTYPE (Sized σ) (ConstM MemMM) ImDrop) ->
  has_kind F τₘ' (MEMTYPE (Sized σ) (ConstM MemMM) δ) ->
  mono_size σ n ->
  let τ := RefT κ (ConstM MemMM) τ0 in
  let τ' := RefT κ' (ConstM MemMM) τ0' in
  has_kind F τ κ ->
  has_kind F τ' κ' ->
  let ψ := InstrT [τ; τᵥ'] [τ'] in
  instr_has_type M F L (IRefStore ψ π) ψ L
| TRefSwap M F L π ρ ιs μ τ0 τᵥ τₘ τs__prefix κ :
  mono_rep ρ ιs ->
  path_to π τ0 τs__prefix τₘ ->
  loads_as F τᵥ τₘ ->
  Forall (mono_sized F) τs__prefix ->
  let τ := RefT κ μ τ0 in
  has_kind F τ κ ->
  let ψ := InstrT [τ; τᵥ] [τ; τᵥ] in
  instr_has_type M F L (IRefSwap ψ π) ψ L
| TRefMMSwap M F L π ρ ιs τ0 τ0' τᵥ τᵥ' τₘ τₘ' τs__prefix κ κ' :
  mono_rep ρ ιs ->
  path_to π τ0 τs__prefix τₘ ->
  loads_as F τᵥ τₘ ->
  stores_as F τᵥ' τₘ' ->
  update_at π τ0 τₘ τ0' τₘ' ->
  Forall (mono_sized F) τs__prefix ->
  let τ := RefT κ (ConstM MemMM) τ0 in
  let τ' := RefT κ' (ConstM MemMM) τ0' in
  has_kind F τ κ ->
  has_kind F τ' κ' ->
  let ψ := InstrT [τ; τᵥ'] [τ'; τᵥ] in
  instr_has_type M F L (IRefSwap ψ π) ψ L

with instrs_have_type :
  module_ctx -> function_ctx -> local_ctx -> list instruction -> instruction_type -> local_ctx -> Prop :=
| TNil M F L :
  instrs_have_type M F L [] (InstrT [] []) L
| TCons M F L1 L2 L3 e es τs1 τs2 τs3 :
  instr_has_type M F L1 e (InstrT τs1 τs2) L2 ->
  instrs_have_type M F L2 es (InstrT τs2 τs3) L3 ->
  instrs_have_type M F L1 (e :: es) (InstrT τs1 τs3) L3.

Scheme instr_has_type_mind := Induction for instr_has_type Sort Prop
with instrs_have_type_mind := Induction for instrs_have_type Sort Prop.
