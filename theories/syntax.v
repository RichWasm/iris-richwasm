From Coq Require Import List.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Strings.String.

Definition var := nat.

Inductive sign := SignU | SignS.

Inductive privilege := PrivRW | PrivR.

Inductive ownership := OwnUniq | OwnGC.

Inductive mutability := Mut | Imm.

Inductive heapability := Heapable | Unheapable.

Inductive linearity := Lin | Unr.

Inductive acuity :=
| AcuVar (ℵ : var)
| Sharp
| Dull.

Inductive location :=
| LocVar (ρ : var)
| LocConst (c : N).

Inductive size :=
| SizeVar (σ : var)
| SizePlus (sz1 : size) (sz2 : size)
| SizeConst (c : nat).

Inductive base_representation :=
| I32R (a : acuity)
| I64R
| F32R
| F64R.

Inductive representation :=
| RepVar (ϱ : var)
| RepList (bs : list base_representation).

Inductive kind :=
| TYPE (r : representation) (l : linearity) (h : heapability)
| SIZE
| REP
| ACU
| LOC.

Inductive constraint :=
| SizeAtLeastC (sz__min : size)
| SizeAtMostC (sz__max : size)
| RepAtMostC (sz__max : size).

Inductive int_type := I32T | I64T.

Inductive float_type := F32T | F64T.

Inductive num_type :=
| IntT (τI : int_type)
| FloatT (τF : float_type).

Inductive type :=
| UnitT
| NumT (τn : num_type)
| VarT (α : var)
| ProdT (τs : list type)
| CoderefT (χ : function_type)
| RecT (τ : type)
| PtrT (ℓ : location)
| ExT (κ : kind) (τ : type)
| OwnT (ℓ : location)
| CapT (π : privilege) (ℓ : location) (ψ : heap_type)
| RefT (o : ownership) (π : privilege) (ℓ : location) (ψ : heap_type)

with heap_type :=
| VariantT (τs : list type)
| StructT (fs : list (type * size))
| ArrayT (τ : type)

with arrow_type :=
| ArrowT (τs1 : list type) (τs2 : list type)

with function_type :=
| FunT (κs : list kind) (cs : list constraint) (τa : arrow_type).

Inductive global_type :=
| GlobalT (m : mutability) (τ : type).

Definition local_effects := list (nat * type).

Inductive index :=
| TypeI (τ : type)
| SizeI (sz : size)
| RepI (r : representation)
| AcuI (a : acuity)
| LocI (ℓ : location).

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
| IUnit (ann : A)
| IDrop (ann : A)
| IUnreachable (ann : A)
| INum (ann : A) (en : num_instr)
| INumConst (ann : A) (τn : num_type) (n : nat)
| IBlock (ann : A) (τa : arrow_type) (effs : local_effects) (es : list instr)
| ILoop (ann : A) (τa : arrow_type) (es : list instr)
| IIte (ann : A) (τa : arrow_type) (effs : local_effects) (es1 : list instr) (es2 : list instr)
| IBr (ann : A) (n : nat)
| IBrIf (ann : A) (n : nat)
| IBrTable (ann : A) (ns : list nat) (n : nat)
| IRet (ann : A)
| ILocalGet (ann : A) (i : nat) (l : linearity)
| ILocalSet (ann : A) (i : nat)
| IGlobalGet (ann : A) (i : nat)
| IGlobalSet (ann : A) (i : nat)
| ICoderef (ann : A) (i : nat)
| ICall (ann : A) (i : nat) (idxs : list index)
| ICallIndirect (ann : A) (idxs : list index)
| IFold (ann : A) (τ : type)
| IUnfold (ann : A)
| IGroup (ann : A) (n : nat)
| IUngroup (ann : A)
| ICapSplit (ann : A)
| ICapJoin (ann : A)
| IPack (ann : A) (κ : kind) (idx : index)
| IUnpack (ann : A) (τa : arrow_type) (effs : local_effects) (es : list instr)
| IStructNew (ann : A) (szs : list size) (o : ownership)
| IStructFree (ann : A)
| IStructGet (ann : A) (n : nat)
| IStructSet (ann : A) (n : nat)
| IStructSwap (ann : A) (n : nat)
| IVariantNew (ann : A) (i : nat) (τs : list type) (o : ownership)
| IVariantCase
    (ann : A) (l : linearity) (τa : arrow_type) (effs : local_effects) (ess : list (list instr))
| IArrayNew (ann : A) (o : ownership)
| IArrayFree (ann : A)
| IArrayGet (ann : A)
| IArraySet (ann : A)
| IRefSplit (ann : A)
| IRefJoin (ann : A)
| IRefDemote (ann : A).

Arguments instr : clear implicits.

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
| ImGlobal (τ : type)
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
  { m_funcs : list (module_function A);
    m_globals : list (module_global A);
    m_table : list nat;
    m_imports : list module_import;
    m_exports : list module_export }.

Arguments module : clear implicits.

Section TypeInd.

  Context (P : type -> Prop)
    (F : function_type -> Prop)
    (H : heap_type -> Prop)
    (A : arrow_type -> Prop)
    (HUnit : P UnitT)
    (HNum : forall τn : num_type, P (NumT τn))
    (HVar : forall α : var, P (VarT α))
    (HProd : forall τs : list type, Forall P τs -> P (ProdT τs))
    (HCoderef : forall χ : function_type, F χ -> P (CoderefT χ))
    (HRec : forall τ : type, P τ -> P (RecT τ))
    (HPtr : forall ℓ : location, P (PtrT ℓ))
    (HEx : forall (κ : kind) (τ : type), P τ -> P (ExT κ τ))
    (HOwn : forall ℓ : location, P (OwnT ℓ))
    (HCap : forall (π : privilege) (ℓ : location) (Ψ : heap_type), H Ψ -> P (CapT π ℓ Ψ))
    (HRef : forall (o : ownership) (π : privilege) (ℓ : location) (Ψ : heap_type), H Ψ -> P (RefT o π ℓ Ψ))
    (HVariant : forall τs : list type, Forall P τs -> H (VariantT τs))
    (HStruct : forall fs : list (type * size), Forall (fun '(τ, sz) => P τ) fs -> H (StructT fs))
    (HArray : forall τ : type, P τ -> H (ArrayT τ))
    (HArrow : forall τs1 τs2 : list type, Forall P τs1 -> Forall P τs2 -> A (ArrowT τs1 τs2))
    (HFun : forall (κs : list kind) (cs : list constraint) (τa : arrow_type), A τa -> F (FunT κs cs τa)).

  Fixpoint type_ind' (τ : type) {struct τ} : P τ
  with function_type_ind' (τf : function_type) {struct τf} : F τf
  with arrow_type_ind' (τa : arrow_type) {struct τa} : A τa
  with heap_type_ind' (Ψ : heap_type) {struct Ψ} : H Ψ.
  Proof.
    - destruct τ.
      + exact HUnit.
      + apply HNum.
      + apply HVar.
      + apply HProd. induction τs; constructor.
        * apply type_ind'.
        * exact IHτs.
      + apply HCoderef, function_type_ind'.
      + apply HRec, type_ind'.
      + apply HPtr.
      + apply HEx, type_ind'.
      + apply HOwn.
      + apply HCap, heap_type_ind'.
      + apply HRef, heap_type_ind'.
    - destruct τf. apply HFun, arrow_type_ind'.
    - destruct τa as [τs1 τs2]. apply HArrow; (induction τs1 + induction τs2); constructor.
      1, 3: apply type_ind'.
      + exact IHτs1.
      + exact IHτs2.
    - destruct Ψ.
      + apply HVariant. induction τs; constructor.
        * apply type_ind'.
        * exact IHτs.
      + apply HStruct. induction fs; constructor.
        * destruct a. apply type_ind'.
        * exact IHfs.
      + apply HArray, type_ind'.
  Defined.

  Corollary type_function_arrow_heap_ind : (forall τ, P τ) /\ (forall τf, F τf) /\ (forall τa, A τa) /\ (forall Ψ, H Ψ).
  Proof.
    repeat split;
      (apply type_ind' || apply function_type_ind' || apply arrow_type_ind' || apply heap_type_ind').
  Qed.

End TypeInd.
