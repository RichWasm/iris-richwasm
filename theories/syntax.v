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
