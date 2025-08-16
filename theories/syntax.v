From Coq Require Import List.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Strings.String.

Definition variable := nat.

Inductive sign := SignU | SignS.

Inductive ownership := OwnUniq | OwnGC.

Inductive mutability := Mut | Imm.

Inductive heapability := Heapable | Unheapable.

Inductive linearity := Lin | Unr.

Inductive location :=
| LocVar (ρ : variable)
| LocConst (c : N).

Inductive primitive_rep :=
| PtrR
| I32R
| I64R
| F32R
| F64R.

Inductive representation :=
| VarR (ϱ : variable)
| SumR (rs : list representation)
| ProdR (rs : list representation)
| PrimR (p : primitive_rep).

Inductive size :=
| VarS (σ : variable)
| RepS (r : representation)
| SumS (szs : list size)
| ProdS (szs : list size)
| ConstS (c : nat).

Inductive sizity :=
| Sized (sz : size)
| Unsized.

Inductive kind :=
| VALTYPE (r : representation) (l : linearity) (h : heapability)
| MEMTYPE (sy : sizity).

Inductive ubinder :=
| ULoc
| URep
| USizity
| USize
| UType (κ : kind).

Inductive ebinder :=
| ELoc
| EType (κ : kind).

Inductive int_type := I32T | I64T.

Inductive float_type := F32T | F64T.

Inductive num_type :=
| IntT (τI : int_type)
| FloatT (τF : float_type).

Inductive type :=
| VarT (α : variable)
| NumT (τn : num_type)
| SumT (τs : list type)
| ProdT (τs : list type)
| ArrayT (τ : type)
| ExT (b : ebinder) (τ : type)
| RecT (τ : type)
| PtrT (ℓ : location)
| CapT (ℓ : location) (τ : type)
| RefT (ω : ownership) (ℓ : location) (τ : type)
| CodeRefT (χ : function_type)
| RepT (r : representation) (τ : type)
| PadT (sz : size) (τ : type)
| SerT (τ : type)

with arrow_type :=
| ArrowT (τs1 : list type) (τs2 : list type)

with function_type :=
| FunT (bs : list ubinder) (τa : arrow_type).

Inductive global_type :=
| GlobalT (m : mutability) (τ : type).

Definition local_effect := list (nat * type).

Inductive index :=
| LocI (ℓ : location)
| RepI (r : representation)
| TypeI (τ : type).

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
| CTrunc (τI : int_type) (τF : float_type) (s : sign)
| CTruncSat (τI : int_type) (τF : float_type) (s : sign)
| CDemote
| CPromote
| CConvert (τF : float_type) (τI : int_type) (s : sign)
| CReinterpretFI (τF : float_type) (τI : int_type)
| CReinterpretIF (τI : int_type) (τF : float_type)
| CReinterpretII (τI : int_type) (s1 s2 : sign).

Inductive num_instr :=
| IInt1 (τI : int_type) (op : int_unop)
| IInt2 (τI : int_type) (op : int_binop)
| IIntTest (τI : int_type) (op : int_testop)
| IIntRel (τI : int_type) (op : int_relop)
| IFloat1 (τF : float_type) (op : float_unop)
| IFloat2 (τF : float_type) (op : float_binop)
| IFloatRel (τF : float_type) (op : float_relop)
| ICvt (op : cvtop).

Inductive instr {A : Type} :=
| INop (ann : A)
| IDrop (ann : A)
| IUnreachable (ann : A)
| INum (ann : A) (en : num_instr)
| INumConst (ann : A) (τn : num_type) (n : nat)
| IBlock (ann : A) (τa : arrow_type) (le : local_effect) (es : list instr)
| ILoop (ann : A) (τa : arrow_type) (es : list instr)
| IIte (ann : A) (τa : arrow_type) (le : local_effect) (es1 es2 : list instr)
| IBr (ann : A) (n : nat)
| IBrIf (ann : A) (n : nat)
| IBrTable (ann : A) (ns : list nat) (n : nat)
| IReturn (ann : A)
| ILocalGet (ann : A) (n : nat)
| ILocalSet (ann : A) (n : nat)
| IGlobalGet (ann : A) (n : nat)
| IGlobalSet (ann : A) (n : nat)
| ICoderef (ann : A) (n : nat)
| ICall (ann : A) (n : nat) (idxs : list index)
| ICallIndirect (ann : A) (idxs : list index)
| IGroup (ann : A) (n : nat)
| IUngroup (ann : A)
| IFold (ann : A) (τ : type)
| IUnfold (ann : A)
| IPack (ann : A) (κ : kind) (idx : index)
| IUnpack (ann : A) (τa : arrow_type) (le : local_effect) (es : list instr)
| IStructNew (ann : A) (o : ownership)
| IStructFree (ann : A)
| IStructGet (ann : A) (n : nat)
| IStructSet (ann : A) (n : nat)
| IStructSwap (ann : A) (n : nat)
| IVariantNew (ann : A) (n : nat) (τs : list type) (o : ownership)
| IVariantCase
    (ann : A) (l : linearity) (τa : arrow_type) (le : local_effect) (ess : list (list instr))
| IArrayNew (ann : A) (o : ownership)
| IArrayFree (ann : A)
| IArrayGet (ann : A)
| IArraySet (ann : A)
| IRefSplit (ann : A)
| IRefJoin (ann : A).

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
| ImFunction (τf : function_type)
| ImGlobal (τg : global_type)
| ImTable.

Record module_import :=
  { mi_name : string;
    mi_desc : module_import_desc }.

Inductive module_export_desc :=
| ExFunction (i : nat)
| ExGlobal (i : nat)
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
