From Coq Require Import List.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Strings.String.

Definition variable := nat.

Inductive sign := SignU | SignS.

Inductive mutability := Mut | Imm.

Inductive heapability := Heapable | Unheapable.

Inductive linearity := Lin | Unr.

Inductive ownership :=
| OwnVar (o : variable)
| OwnUniq
| OwnGC.

Inductive location :=
| LocVar (l : variable)
| LocConst (n : N).

Inductive primitive_rep :=
| PtrR
| I32R
| I64R
| F32R
| F64R.

Inductive representation :=
| VarR (r : variable)
| SumR (ρs : list representation)
| ProdR (ρs : list representation)
| PrimR (ι : primitive_rep).

Inductive size :=
| VarS (s : variable)
| SumS (σs : list size)
| ProdS (σs : list size)
| RepS (ρ : representation)
| ConstS (n : nat).

Inductive sizity :=
| Sized (σ : size)
| Unsized.

Inductive kind :=
| VALTYPE (ρ : representation) (η : heapability) (γ : linearity)
| MEMTYPE (ζ : sizity) (γ : linearity).

Inductive quantifier :=
| QLoc
| QOwn
| QRep
| QSize
| QType (κ : kind).

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
| RefT (ω : ownership) (ℓ : location) (τ : type)
| CapT (ω : ownership) (ℓ : location) (τ : type)
| PtrT (ℓ : location)
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
| LocI (ℓ : location)
| OwnI (ω : ownership)
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
| ICoderef (ann : A) (n : nat)
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
| IRefNew (ann : A) (ω : ownership)
| IRefFree (ann : A)
| IRefDup (ann : A)
| IRefDrop (ann : A)
| IRefSplit (ann : A)
| IRefJoin (ann : A)
| IRefLoad (ann : A) (π : path)
| IRefStore (ann : A) (π : path)
| IRefSwap (ann : A) (π : path)
| IVariantNew (ann : A) (n : nat) (τs : list type) (ω : ownership)
| IVariantCase
    (ann : A) (γ : linearity) (χ : arrow_type) (le : local_effect) (ess : list (list instr))
| IArrayNew (ann : A) (ω : ownership)
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
| ImGlobal (μ : mutability) (τ : type)
| ImTable.

Record module_import :=
  { mi_name : string;
    mi_desc : module_import_desc }.

Inductive module_export_desc :=
| ExFunction (n : nat)
| ExGlobal (n : nat)
| ExTable.

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
