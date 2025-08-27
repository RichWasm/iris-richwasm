From stdpp Require Import base decidable numbers list.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Strings.String.

Definition variable := nat.

#[global]
Instance Eq_variable : EqDecision variable := ltac:(solve_decision).

Inductive sign := SignU | SignS.

#[global]
Instance Eq_sign : EqDecision sign := ltac:(solve_decision).

Inductive mutability := Mut | Imm.

#[global]
Instance Eq_mutability : EqDecision mutability := ltac:(solve_decision).

Inductive linearity := Lin | Unr.

#[global]
Instance Eq_linearity : EqDecision linearity := ltac:(solve_decision).

Inductive memory :=
| MemVar (m : variable)
| MemMM
| MemGC.

#[global]
Instance Eq_memory : EqDecision memory := ltac:(solve_decision).

Inductive ownership :=
| OwnVar (o : variable)
| OwnUniq
| OwnGC.

#[global]
Instance Eq_ownership : EqDecision ownership := ltac:(solve_decision).

Inductive location :=
| LocVar (l : variable)
| LocConst (n : N).

#[global]
Instance Eq_location : EqDecision location := ltac:(solve_decision).

Inductive primitive_rep :=
| PtrR
| I32R
| I64R
| F32R
| F64R.

#[global]
Instance Eq_primitive_rep : EqDecision primitive_rep := ltac:(solve_decision).

Inductive representation :=
| VarR (r : variable)
| SumR (ρs : list representation)
| ProdR (ρs : list representation)
| PrimR (ι : primitive_rep).

#[global]
Instance Eq_representation : EqDecision representation.
unfold EqDecision, Decision.
Eval cbv in Eq_primitive_rep.
refine (fix eqr r1 r2 := 
          match r1, r2 with
          | VarR v1, VarR v2 => cast_if (decide (v1 = v2))
          | SumR ρs1, SumR ρs2 => cast_if (@list_eq_dec _ eqr ρs1 ρs2)
          | ProdR ρs1, ProdR ρs2 => cast_if (@list_eq_dec _ eqr ρs1 ρs2)
          | PrimR ι1, PrimR ι2 => cast_if (decide (ι1 = ι2))
          | _, _ => right _
          end); congruence.
Defined.

Inductive size :=
| VarS (s : variable)
| SumS (σs : list size)
| ProdS (σs : list size)
| RepS (ρ : representation)
| ConstS (n : nat).

#[global]
Instance Eq_size : EqDecision size.
refine (fix eqs σ1 σ2 :=
          match σ1, σ2 with
          | VarS s1, VarS s2 => cast_if (decide (s1 = s2))
          | SumS σs1, SumS σs2 => cast_if (@list_eq_dec _ eqs σs1 σs2)
          | ProdS σs1, ProdS σs2 => cast_if (@list_eq_dec _ eqs σs1 σs2)
          | RepS ρ1, RepS ρ2 => cast_if (decide (ρ1 = ρ2))
          | ConstS n1, ConstS n2 => cast_if (decide (n1 = n2))
          | _, _ => right _
          end); congruence.
Defined.

Inductive sizity :=
| Sized (σ : size)
| Unsized.

#[global]
Instance Eq_sizity : EqDecision sizity := ltac:(solve_decision).

Inductive kind :=
| VALTYPE (ρ : representation) (γ : linearity)
| MEMTYPE (ζ : sizity) (μ : memory) (γ : linearity).

#[global]
Instance Eq_kind : EqDecision kind := ltac:(solve_decision).

Inductive quantifier :=
| QMem
| QRep
| QSize
| QType (κ : kind).

#[global]
Instance Eq_quantifier : EqDecision quantifier := ltac:(solve_decision).

Inductive int_type := I32T | I64T.

Inductive float_type := F32T | F64T.

Inductive num_type :=
| IntT (ν__i : int_type)
| FloatT (ν__f : float_type).

Inductive type :=
| VarT (t : variable)
| NumT (ν : num_type)
| SumT (τs : list type)
| ProdT (τs : list type)
| ArrayT (τ : type)
| RefT (μ : memory) (τ : type)
| GCPtrT (τ : type)
| CodeRefT (ϕ : function_type)
| RepT (ρ : representation) (τ : type)
| PadT (σ : size) (τ : type)
| SerT (τ : type)
| ExT (δ : quantifier) (τ : type)
| RecT (τ : type)

with arrow_type :=
| ArrowT (τs1 : list type) (τs2 : list type)

with function_type :=
| FunT (δs : list quantifier) (χ : arrow_type).

Definition local_effect := list (nat * type).

Inductive index :=
| MemI (μ : memory)
| RepI (ρ : representation)
| SizeI (σ : size)
| TypeI (τ : type).

Inductive path_component :=
| PCProj (n : nat)
| PCUnwrap.

Definition path := list path_component.

Inductive int_unop := ClzI | CtzI | PopcntI.

Inductive int_binop :=
| AddI
| SubI
| MulI
| DivI (s : sign)
| RemI (s : sign)
| AndI
| OrI
| XorI
| ShlI
| ShrI (s : sign)
| RotlI
| RotrI.

Inductive int_testop := EqzI.

Inductive int_relop :=
| EqI
| NeI
| LtI (s : sign)
| GtI (s : sign)
| LeI (s : sign)
| GeI (s : sign).

Inductive float_unop := NegF | AbsF | CeilF | FloorF | TruncF | NearestF | SqrtF.

Inductive float_binop := AddF | SubF | MulF | DivF | MinF | MaxF | CopySignF.

Inductive float_relop := EqF | NeF | LtF | GtF | LeF | GeF.

Inductive cvtop :=
| CWrap
| CExtend (s : sign)
| CTrunc (ν__i : int_type) (ν__f : float_type) (s : sign)
| CTruncSat (ν__i : int_type) (ν__f : float_type) (s : sign)
| CDemote
| CPromote
| CConvert (ν__f : float_type) (ν__i : int_type) (s : sign)
| CReinterpretFI (ν__f : float_type) (ν__i : int_type)
| CReinterpretIF (ν__i : int_type) (ν__f : float_type)
| CReinterpretII (ν__i : int_type) (s1 s2 : sign).

Inductive num_instr :=
| IInt1 (ν__i : int_type) (op : int_unop)
| IInt2 (ν__i : int_type) (op : int_binop)
| IIntTest (ν__i : int_type) (op : int_testop)
| IIntRel (ν__i : int_type) (op : int_relop)
| IFloat1 (ν__f : float_type) (op : float_unop)
| IFloat2 (ν__f : float_type) (op : float_binop)
| IFloatRel (ν__f : float_type) (op : float_relop)
| ICvt (op : cvtop).

Inductive instr {A : Type} :=
| INop (ann : A)
| IDrop (ann : A)
| IUnreachable (ann : A)
| INum (ann : A) (en : num_instr)
| INumConst (ann : A) (ν : num_type) (n : nat)
| IBlock (ann : A) (χ : arrow_type) (le : local_effect) (es : list instr)
| ILoop (ann : A) (χ : arrow_type) (es : list instr)
| IIte (ann : A) (χ : arrow_type) (le : local_effect) (es1 es2 : list instr)
| IBr (ann : A) (n : nat)
| IBrIf (ann : A) (n : nat)
| IBrTable (ann : A) (ns : list nat) (n : nat)
| IReturn (ann : A)
| ILocalGet (ann : A) (n : nat)
| ILocalSet (ann : A) (n : nat)
| IGlobalGet (ann : A) (n : nat)
| IGlobalSet (ann : A) (n : nat)
| ICodeRef (ann : A) (n : nat)
| ICall (ann : A) (n : nat) (ixs : list index)
| ICallIndirect (ann : A) (ixs : list index)
| IGroup (ann : A) (n : nat)
| IUngroup (ann : A)
| IFold (ann : A) (τ : type)
| IUnfold (ann : A)
| IPack (ann : A) (κ : kind) (ix : index)
| IUnpack (ann : A) (χ : arrow_type) (le : local_effect) (es : list instr)
| IWrap (ann : A)
| IUnwrap (ann : A)
| IRefNew (ann : A) (μ : memory)
| IRefFree (ann : A)
| IRefDup (ann : A)
| IRefDrop (ann : A)
| IRefLoad (ann : A) (π : path)
| IRefStore (ann : A) (π : path)
| IRefSwap (ann : A) (π : path)
| IVariantNew (ann : A) (n : nat) (τs : list type) (μ : memory)
| IVariantCase
    (ann : A) (γ : linearity) (χ : arrow_type) (le : local_effect) (ess : list (list instr))
| IArrayNew (ann : A) (μ : memory)
| IArrayFree (ann : A)
| IArrayGet (ann : A)
| IArraySet (ann : A).

Arguments instr : clear implicits.

Definition expr A := list (instr A).

Record module_function {A : Type} :=
  { mf_type : function_type;
    mf_body : list (instr A) }.

Arguments module_function : clear implicits.

Record module_global {A : Type} :=
  { mg_type : type;
    mg_init : list (instr A) }.

Arguments module_global : clear implicits.

Inductive module_import_desc :=
| ImFunction (ϕ : function_type)
| ImGlobal (ω : mutability) (τ : type).

Record module_import :=
  { mi_name : string;
    mi_desc : module_import_desc }.

Inductive module_export_desc :=
| ExFunction (n : nat)
| ExGlobal (n : nat).

Record module_export :=
  { me_name : string;
    me_desc : module_export_desc }.

Record module {A : Type} :=
  { m_imports : list module_import;
    m_funcs : list (module_function A);
    m_globals : list (module_global A);
    m_table : list nat;
    m_exports : list module_export }.

Arguments module : clear implicits.

Section InductionPrinciples.
  
  Section RepInd.
    Variables
      (P: representation -> Prop)
      (HVarR: ∀ r, P (VarR r))
      (HSumR: ∀ ρs, Forall P ρs -> P (SumR ρs))
      (HProdR: ∀ ρs, Forall P ρs -> P (ProdR ρs))
      (HPrimR: ∀ ι, P (PrimR ι)).

    Fixpoint representation_ind' (ρ: representation) : P ρ :=
      let fix reps_ind (ρs: list representation) : Forall P ρs :=
        match ρs as ρs return Forall P ρs with
        | [] => List.Forall_nil _
        | ρ :: ρs => List.Forall_cons _ _ _ (representation_ind' ρ) (reps_ind ρs)
        end
      in
      match ρ as ρ return P ρ with
      | VarR r => HVarR r
      | SumR ρs => HSumR _ (reps_ind ρs)
      | ProdR ρs => HProdR _ (reps_ind ρs)
      | PrimR ι => HPrimR ι
      end.

  End RepInd.

  Section SizeInd.
    Variables
      (P : size -> Prop)
      (HVarS : ∀ s, P (VarS s))
      (HSumS : ∀ σs, Forall P σs -> P (SumS σs))
      (HProdS : ∀ σs, Forall P σs -> P (ProdS σs))
      (HRepS : ∀ ρ, P (RepS ρ))
      (HConstS : ∀ n, P (ConstS n)).
    
    Fixpoint size_ind' (σ: size) : P σ :=
      let fix sizes_ind (σs: list size) : Forall P σs :=
        match σs as σs return Forall P σs with
        | [] => List.Forall_nil _
        | σ :: σs => List.Forall_cons _ _ _ (size_ind' σ) (sizes_ind σs)
        end
      in
      match σ as σ return P σ with
      | VarS s => HVarS s
      | SumS σs => HSumS σs (sizes_ind σs)
      | ProdS σs => HProdS σs (sizes_ind σs)
      | RepS ρ => HRepS ρ
      | ConstS n => HConstS n
      end.

  End SizeInd.

  Section TypeInd.
    Variables
      (P_type : type -> Prop)
      (P_arrow_type : arrow_type -> Prop)
      (P_function_type : function_type -> Prop)
      (HVarT: ∀ t, P_type (VarT t))
      (HNumT: ∀ ν, P_type (NumT ν))
      (HSumT: ∀ τs, Forall P_type τs -> P_type (SumT τs))
      (HProdT: ∀ τs, Forall P_type τs -> P_type (ProdT τs))
      (HArrayT: ∀ τ, P_type τ -> P_type (ArrayT τ))
      (HRefT: ∀ μ τ, P_type τ -> P_type (RefT μ τ))
      (HGCPtrT: ∀ τ, P_type τ -> P_type (GCPtrT τ))
      (HCodeRefT: ∀ ϕ, P_function_type ϕ -> P_type (CodeRefT ϕ))
      (HRepT: ∀ ρ τ, P_type τ -> P_type (RepT ρ τ))
      (HPadT: ∀ σ τ, P_type τ -> P_type (PadT σ τ))
      (HSerT: ∀ τ, P_type τ -> P_type (SerT τ))
      (HExT: ∀ δ τ, P_type τ -> P_type (ExT δ τ))
      (HRecT: ∀ τ, P_type τ -> P_type (RecT τ))
      (HArrowT: ∀ τs1 τs2,
          Forall P_type τs1 ->
          Forall P_type τs2 ->
          P_arrow_type (ArrowT τs1 τs2))
      (HFunT: ∀ δs χ,
          P_arrow_type χ ->
          P_function_type (FunT δs χ)).

    Fixpoint type_ind' (τ: type) {struct τ} : P_type τ :=
      let fix types_ind' (τs: list type) {struct τs} : Forall P_type τs :=
        match τs as τs return Forall P_type τs with
        | [] => List.Forall_nil _
        | τ :: τs => List.Forall_cons _ _ _ (type_ind' τ) (types_ind' τs)
        end
      in
      match τ as τ return P_type τ with
      | VarT t => HVarT t
      | NumT ν => HNumT ν
      | SumT τs => HSumT τs (types_ind' τs)
      | ProdT τs => HProdT τs (types_ind' τs)
      | ArrayT τ => HArrayT τ (type_ind' τ)
      | RefT μ τ => HRefT μ τ (type_ind' τ)
      | GCPtrT τ => HGCPtrT τ (type_ind' τ)
      | CodeRefT ϕ => HCodeRefT ϕ (function_type_ind' ϕ)
      | RepT ρ τ => HRepT ρ τ (type_ind' τ)
      | PadT σ τ => HPadT σ τ (type_ind' τ)
      | SerT τ => HSerT τ (type_ind' τ)
      | ExT δ τ => HExT δ τ (type_ind' τ)
      | RecT τ => HRecT τ (type_ind' τ)
      end
    with arrow_type_ind' (χ: arrow_type) {struct χ} : P_arrow_type χ :=
      let fix types_ind' (τs: list type) {struct τs} : Forall P_type τs :=
        match τs as τs return Forall P_type τs with
        | [] => List.Forall_nil _
        | τ :: τs => List.Forall_cons _ _ _ (type_ind' τ) (types_ind' τs)
        end
      in
      match χ as χ return P_arrow_type χ with
      | ArrowT τs1 τs2 => HArrowT _ _ (types_ind' τs1) (types_ind' τs2)
      end
    with function_type_ind' (ϕ: function_type) {struct ϕ} : P_function_type ϕ :=
      match ϕ as ϕ return P_function_type ϕ with
      | FunT δs χ => HFunT _ _ (arrow_type_ind' χ)
      end.
    
    Definition type_arr_fun_ind :
      (∀ τ, P_type τ) /\ (∀ χ, P_arrow_type χ) /\ (∀ ϕ, P_function_type ϕ) :=
      conj type_ind' (conj arrow_type_ind' function_type_ind').

  End TypeInd.
  
  Section InstrInd.
    Context {A: Type}.
    Variables
        (P: instr A -> Prop)
        (HNop: forall ann, P (INop ann))
        (HDrop: forall ann, P (IDrop ann))
        (HUnreachable: forall ann, P (IUnreachable ann))
        (HNum: forall ann en, P (INum ann en))
        (HNumConst: forall ann ν n, P (INumConst ann ν n))
        (HBlock: forall ann χ le es, 
            Forall P es ->
            P (IBlock ann χ le es))
        (HLoop: forall ann χ es,
            Forall P es ->
            P (ILoop ann χ es))
        (HIte: forall ann χ le es1 es2,
            Forall P es1 ->
            Forall P es2 ->
            P (IIte ann χ le es1 es2))
        (HBr : forall ann n, P (IBr ann n))
        (HBrIf : forall ann n, P (IBrIf ann n))
        (HBrTable : forall ann ns n, P (IBrTable ann ns n))
        (HReturn : forall ann, P (IReturn ann))
        (HLocalGet: forall ann n, P (ILocalGet ann n))
        (HLocalSet : forall ann n, P (ILocalSet ann n))
        (HGlobalGet: forall ann n, P (IGlobalGet ann n))
        (HGlobalSet: forall ann n, P (IGlobalSet ann n))
        (HCodeRef: forall ann n, P (ICodeRef ann n))
        (HCall: forall ann n ixs, P (ICall ann n ixs))
        (HCallIndirect: forall ann ixs, P (ICallIndirect ann ixs))
        (HGroup: forall ann n, P (IGroup ann n))
        (HUngroup: forall ann, P (IUngroup ann))
        (HFold: forall ann τ, P (IFold ann τ))
        (HUnfold: forall ann, P (IUnfold ann))
        (HPack: forall ann κ ix, P (IPack ann κ ix))
        (HUnpack: forall ann χ le es, Forall P es -> P (IUnpack ann χ le es))
        (HWrap: forall ann, P (IWrap ann))
        (HUnwrap:  forall ann, P (IUnwrap ann))
        (HRefNew : forall ann μ, P (IRefNew ann μ))
        (HRefFree: forall ann, P (IRefFree ann))
        (HRefDup: forall ann, P (IRefDup ann))
        (HRefDrop: forall ann, P (IRefDrop ann))
        (HRefLoad: forall ann π, P (IRefLoad ann π))
        (HRefStore: forall ann π, P (IRefStore ann π))
        (HRefSwap: forall ann π, P (IRefSwap ann π))
        (HVariantNew: forall ann n τs μ, P (IVariantNew ann n τs μ))
        (HVariantCase: forall ann γ χ le ess, 
            Forall (Forall P) ess ->
            P (IVariantCase ann γ χ le ess))
        (HArrayNew: forall ann μ, P (IArrayNew ann μ))
        (HArrayFree: forall ann, P (IArrayFree ann))
        (HArrayGet: forall ann, P (IArrayGet ann))
        (HArraySet: forall ann, P (IArraySet ann)).
    
    Fixpoint instr_ind' (i: instr A) : P i :=
      let fix instrs_ind (i: list (instr A)) : Forall P i :=
        match i with
        | [] => List.Forall_nil _
        | ins :: i => List.Forall_cons _ _ _ (instr_ind' ins) (instrs_ind i)
        end 
      in
      let fix instrss_ind (i: list (list (instr A))) : Forall (Forall P) i :=
        match i with
        | [] => List.Forall_nil _
        | i :: i' => List.Forall_cons _ _ _ (instrs_ind i) (instrss_ind i')
        end 
      in
      match i with
      | INop ann => HNop ann
      | IDrop ann => HDrop ann
      | IUnreachable ann => HUnreachable ann
      | INum ann en => HNum ann en
      | INumConst ann ν n => HNumConst ann ν n
      | IBlock ann χ le es => HBlock ann χ le es (instrs_ind es)
      | ILoop ann χ es => HLoop ann χ es (instrs_ind es)
      | IIte ann χ le es1 es2 => HIte ann χ le es1 es2 (instrs_ind es1) (instrs_ind es2)
      | IBr ann n => HBr ann n
      | IBrIf ann n => HBrIf ann n
      | IBrTable ann ns n => HBrTable ann ns n
      | IReturn ann => HReturn ann
      | ILocalGet ann n => HLocalGet ann n
      | ILocalSet ann n => HLocalSet ann n
      | IGlobalGet ann n => HGlobalGet ann n
      | IGlobalSet ann n => HGlobalSet ann n
      | ICodeRef ann n => HCodeRef ann n
      | ICall ann n ixs => HCall ann n ixs
      | ICallIndirect ann ixs => HCallIndirect ann ixs
      | IGroup ann n => HGroup ann n
      | IUngroup ann => HUngroup ann
      | IFold ann τ => HFold ann τ
      | IUnfold ann => HUnfold ann
      | IPack ann κ ix => HPack ann κ ix
      | IUnpack ann χ le es => HUnpack ann χ le es (instrs_ind es)
      | IWrap ann => HWrap ann
      | IUnwrap ann => HUnwrap ann
      | IRefNew ann μ => HRefNew ann μ
      | IRefFree ann => HRefFree ann
      | IRefDup ann => HRefDup ann
      | IRefDrop ann => HRefDrop ann
      | IRefLoad ann π => HRefLoad ann π
      | IRefStore ann π => HRefStore ann π
      | IRefSwap ann π => HRefSwap ann π
      | IVariantNew ann n τs μ => HVariantNew ann n τs μ
      | IVariantCase ann γ χ le ess => HVariantCase ann γ χ le ess (instrss_ind ess)
      | IArrayNew ann μ => HArrayNew ann μ
      | IArrayFree ann => HArrayFree ann
      | IArrayGet ann => HArrayGet ann
      | IArraySet ann => HArraySet ann
      end.
    
  End InstrInd.

End InductionPrinciples.
