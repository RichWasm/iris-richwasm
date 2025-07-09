Set Universe Polymorphism.
From stdpp Require Import base list list_numbers.
From Coq Require Import Numbers.BinNums List NArith.

Import ListNotations.

Definition var := nat.

(* Types and term for the RichWasm language *)

(** ** Types *)

Inductive cap := R | W.

Inductive Sign := U | S.

Definition Ptr := N.

Inductive HeapableConstant :=
| Heapable
| NotHeapable.

Inductive QualConstant :=
| Unrestricted
| Linear.

Definition qualconstr_eq_dec (r1 r2 : QualConstant) : {r1 = r2} + {r1 <> r2}.
Proof.
  destruct r1, r2; try (right; congruence); eauto.
Defined.

Inductive MemConstant := GCMem | LinMem.

Definition mem_const_eq_dec: forall x y: MemConstant, {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Inductive Loc :=
| LocV   : var -> Loc
| LocP   : Ptr -> MemConstant -> Loc.

Inductive Qual :=
| QualVar (δ : var)
| QualJoin (q__s : list Qual)
| QualConst (c : QualConstant).

Coercion QualConst : QualConstant >-> Qual.

Inductive Size :=
| SizeVar (σ : var)
| SizePlus (sz1 : Size) (sz2 : Size)
| SizeConst (c : nat).

(* Numeric Types *)

Inductive IntType := i32 | i64.

Inductive FloatType := f32 | f64.

Inductive NumType :=
| Int (s : Sign) (i : IntType)
| Float (f : FloatType).

Inductive KindVar := (* Binding sites for kind variables *)
| LOC (q : Qual)
| QUAL (q__upper : list Qual) (q__lower : list Qual)
| SIZE (sz__upper : list Size) (sz__lower : list Size)
| TYPE (sz : Size) (q : Qual) (hc : HeapableConstant).

Inductive Typ :=
| Num (nτ : NumType)
| TVar (α : var)
| Unit
| ProdT (τ__s : list Typ)
| CoderefT (χ : FunType)
| Rec (q : Qual) (τ : Typ) (* binding site *)
| PtrT (ℓ : Loc)
| ExLoc (q : Qual) (τ : Typ) (* binding site *)
| OwnR (ℓ : Loc)
| CapT (cap : cap) (ℓ : Loc) (ψ : HeapType)
| RefT (cap : cap) (ℓ : Loc) (ψ : HeapType)

with HeapType :=
| VariantType (τ__s : list Typ)
| StructType (fields : list (Typ * Size))
| ArrayType (τ : Typ)
| Ex (sz : Size) (q : Qual) (τ : Typ) (* binding site *)

with ArrowType :=
| Arrow (τ__s1 : list Typ) (τ__s2 : list Typ)

with FunType :=
| FunT (κ : list KindVar) (tf : ArrowType).

Definition qual_ctx := list Qual.
Definition mem_qual (mem: MemConstant) : Qual :=
  match mem with
  | GCMem => Unrestricted
  | LinMem => Linear
  end.

Definition loc_qual (loc_quals: qual_ctx) (loc: Loc) : option Qual :=
  match loc with
  | LocV ρ => loc_quals !! ρ
  | LocP ℓ mem => mret $ mem_qual mem
  end.

Definition Mut := bool.

Inductive GlobalType :=
| GT : Mut -> Typ -> GlobalType.

Definition Table := list nat.

Definition LocalEffect := list (nat * Typ).

Inductive Index :=
| LocI (ℓ : Loc)
| SizeI (sz : Size)
| QualI (q : Qual)
| TypI (τ : Typ).

Coercion LocI  : Loc >-> Index.
Coercion SizeI : Size >-> Index.
Coercion QualI : Qual >-> Index.
Coercion TypI  : Typ >-> Index.

(** ** Terms *)

Inductive IUnOp :=
| clz | ctz | popcnt.

Inductive IBinOp :=
| add | sub | mul | div (s : Sign) | rem (s : Sign)
| and | or | xor | shl | shr (s : Sign) | rotl | rotr.

Inductive FUnOp :=
| neg | abs | ceil | floor | trunc | nearest | sqrt.

Inductive FBinOp :=
| addf | subf | mulf | divf | min | max | copysign.

Inductive ITestOp := eqz.

Inductive IRelOp :=
| eq | ne
| lt (s : Sign) | gt (s : Sign)
| le (s : Sign) | ge (s : Sign).

Inductive FRelOp :=
| eqf | nef
| ltf | gtf
| lef | gef.

Inductive CvtOp :=
| Wrap        (i : IntType)
| Extend      (i : IntType)   (s : Sign)
| Trunc       (f : FloatType) (s : Sign)
| TruncSat    (f : FloatType) (s : Sign)
| Convert     (i : IntType)   (s : Sign)
| Demote      (f : FloatType)
| Promote     (f : FloatType)
| Reinterpret (i : IntType).
(* FIXME: you can reinterpret floats too *)

Inductive NumInstr :=
| Iu   (i : IntType)   (op : IUnOp)
| Ib   (i : IntType)   (op : IBinOp)
| Fu   (f : FloatType) (op : FUnOp)
| Fb   (f : FloatType) (op : FBinOp)
| It   (i : IntType)   (op : ITestOp)
| Ir   (i : IntType)   (op : IRelOp)
| Fr   (f : FloatType) (op : FRelOp)
| CvtI (i : IntType)   (op : CvtOp)
| CvtF (f : FloatType) (op : CvtOp).

(* exports *)
Definition ex := positive.
(* imports *)
Definition im := positive.

Inductive instr {A} :=
  | INumConst (ann : A) (nt : NumType) (n : nat)
  | IUnit (ann : A)
  | INum (ann : A) (ni : NumInstr)
  | IUnreachable (ann : A)
  | INop (ann : A)
  | IDrop (ann : A)
  | ISelect (ann : A)
  | IBlock (ann : A) (ta : ArrowType) (tl : LocalEffect) (es : list instr)
  | ILoop (ann : A) (ta : ArrowType) (es : list instr)
  | IIte (ann : A) (ta : ArrowType) (tl : LocalEffect) (es1 : list instr) (es2 : list instr)
  | IBr (ann : A) (n : nat)
  | IBrIf (ann : A) (n : nat)
  | IBrTable (ann : A) (ns : list nat) (n : nat)
  | IRet (ann : A)
  | IGetLocal (ann : A) (i : nat) (q : Qual)
  | ISetLocal (ann : A) (i : nat)
  | ITeeLocal (ann : A) (i : nat)
  | IGetGlobal (ann : A) (i : nat)
  | ISetGlobal (ann : A) (i : nat)
  | ICoderef (ann : A) (i : nat)
  | ICallIndirect (ann : A) (idxs : list Index)
  | ICall (ann : A) (i : nat) (idxs : list Index)
  | IRecFold (ann : A) (ty : Typ)
  | IRecUnfold (ann : A)
  | IGroup (ann : A) (n : nat)
  | IUngroup (ann : A)
  | ICapSplit (ann : A)
  | ICapJoin (ann : A)
  | IRefDemote (ann : A)
  | IMemPack (ann : A) (l : Loc) (* XXX Loc or not? *)
  | IMemUnpack (ann : A) (ta : ArrowType) (tl : LocalEffect) (es : list instr)
  | IStructMalloc (ann : A) (szs : list Size) (q : Qual)
  | IStructFree (ann : A)
  | IStructGet (ann : A) (n : nat)
  | IStructSet (ann : A) (n : nat)
  | IStructSwap (ann : A) (n : nat)
  | IVariantMalloc (ann : A) (i : nat) (ts : list Typ) (q : Qual)
  | IVariantCase (ann : A) (q : Qual) (th : HeapType) (ta : ArrowType) (tl : LocalEffect) (es : list (list instr))
  | IArrayMalloc (ann : A) (q : Qual)
  | IArrayGet (ann : A)
  | IArraySet (ann : A)
  | IArrayFree (ann : A)
  | IExistPack (ann : A) (t : Typ) (th : HeapType) (q : Qual)
  | IExistUnpack (ann : A) (q : Qual) (th : HeapType) (ta : ArrowType) (tl : LocalEffect) (es : list instr)
  | IRefSplit (ann : A)
  | IRefJoin (ann : A)
  | IQualify (ann : A) (q : Qual).

Arguments instr : clear implicits.

Inductive Func A :=
  | Fun (exs : list ex) (ft : FunType) (szs : list Size) (es : list (instr A)).

Arguments Fun {_} _ _ _ _.

Inductive Closure A :=
  | Clo : nat -> Func A -> Closure A.

Arguments Clo {_} _ _.

Inductive Glob A :=
| GlobMut(τ : Typ) (i__s : list (instr A))
| GlobEx (ex__s : list ex) (τ : Typ) (i__s : list (instr A))
| GlobIm (ex__s : list ex) (τ : Typ) (im : im).

Arguments GlobMut {_} _ _.
Arguments GlobEx {_} _ _ _.
Arguments GlobIm {_} _ _ _.

Definition module A :=
  (list (Func A) *
   list (Glob A) *
   Table)%type.

(** Useful properties *)

Inductive Forall_type {A : Type} (P : A -> Type) : list A -> Type :=
| Forall_type_nil : Forall_type P []
| Forall_type_cons : forall (x : A) (l : list A),
    P x -> Forall_type P l -> Forall_type P (x :: l).

Section TypeInd.

  Context
    (P : Typ -> Prop)
    (F : FunType -> Prop)
    (H : HeapType -> Prop)
    (A : ArrowType -> Prop)
    (HNum : forall n : NumType, P (Num n))
    (HVar : forall v : var, P (TVar v))
    (HUnit : P Unit)
    (HProd : forall l : list Typ, Forall P l -> P (ProdT l))
    (HCoderef : forall f : FunType, F f -> P (CoderefT f))
    (HRec : forall q (t : Typ), P t -> P (Rec q t))
    (HPtr : forall l : Loc, P (PtrT l))
    (HExLoc : forall q (t : Typ), P t -> P (ExLoc q t))
    (HOwn : forall l : Loc, P (OwnR l))
    (HCap : forall (c : cap) (l : Loc) (h : HeapType), H h -> P (CapT c l h))
    (HRef : forall (c : cap) (l : Loc) (h : HeapType), H h -> P (RefT c l h))
    (HFun : forall (l : list KindVar) (a : ArrowType), A a -> F (FunT l a))
    (HArrow : forall (l1 l2 : list Typ), Forall P l1 -> Forall P l2 -> A (Arrow l1 l2))
    (HVariant : forall l : list Typ, Forall P l -> H (VariantType l))
    (HStruct : forall l : list (Typ * Size), Forall (fun '(t, s) => P t) l -> H (StructType l))
    (HArray : forall t : Typ, P t -> H (ArrayType t))
    (HEx : forall (s : Size) q (t : Typ), P t -> H (Ex s q t)).

  Fixpoint Typ_ind' (t : Typ) {struct t} : P t
  with FunType_ind' (f : FunType) {struct f} : F f
  with ArrowType_ind' (a : ArrowType) {struct a} : A a
  with HeapType_ind' (h : HeapType) {struct h} : H h.
  Proof.
    - destruct t.
      + apply HNum.
      + apply HVar.
      + apply HUnit.
      + apply HProd.
        induction τ__s; [constructor|constructor].
        * apply Typ_ind'.
        * apply IHτ__s.
      + apply HCoderef, FunType_ind'.
      + apply HRec, Typ_ind'.
      + apply HPtr.
      + apply HExLoc, Typ_ind'.
      + apply HOwn.
      + apply HCap, HeapType_ind'.
      + apply HRef, HeapType_ind'.
    - destruct f. apply HFun, ArrowType_ind'.
    - destruct a as [l1 l2].
      apply HArrow; ((induction l1 + induction l2); constructor;
                     [apply Typ_ind'|apply IHl1+apply IHl2]).
    - destruct h.
      + apply HVariant. induction τ__s; constructor; [apply Typ_ind'|apply IHτ__s].
      + apply HStruct. induction fields; constructor; [destruct a; apply Typ_ind'|apply IHfields].
      + apply HArray, Typ_ind'.
      + apply HEx, Typ_ind'.
  Defined.

  Corollary Typ_Fun_Arrow_Heap_ind :
    (forall p, P p) /\ (forall f, F f) /\ (forall a, A a) /\ (forall h, H h).
  Proof.
    repeat split;
      (apply Typ_ind'||apply FunType_ind'||apply ArrowType_ind'||apply HeapType_ind').
  Qed.

End TypeInd.

Section TypeRect.

  Context
    (P : Typ -> Type)
    (F : FunType -> Type)
    (H : HeapType -> Type)
    (A : ArrowType -> Type)
    (HNum : forall n : NumType, P (Num n))
    (HVar : forall v : var, P (TVar v))
    (HUnit : P Unit)
    (HProd : forall l : list Typ, Forall_type P l -> P (ProdT l))
    (HCoderef : forall f : FunType, F f -> P (CoderefT f))
    (HRec : forall q (t : Typ), P t -> P (Rec q t))
    (HPtr : forall l : Loc, P (PtrT l))
    (HExLoc : forall q (t : Typ), P t -> P (ExLoc q t))
    (HOwn : forall l : Loc, P (OwnR l))
    (HCap : forall (c : cap) (l : Loc) (h : HeapType), H h -> P (CapT c l h))
    (HRef : forall (c : cap) (l : Loc) (h : HeapType), H h -> P (RefT c l h))
    (HFun : forall (l : list KindVar) (a : ArrowType), A a -> F (FunT l a))
    (HArrow : forall (l1 l2 : list Typ), Forall_type P l1 -> Forall_type P l2 -> A (Arrow l1 l2))
    (HVariant : forall l : list Typ, Forall_type P l -> H (VariantType l))
    (HStruct : forall l : list (Typ * Size), Forall_type (fun '(t, s) => P t) l -> H (StructType l))
    (HArray : forall t : Typ, P t -> H (ArrayType t))
    (HEx : forall (s : Size) q (t : Typ), P t -> H (Ex s q t)).

  Fixpoint Typ_rect' (t : Typ) {struct t} : P t
  with FunType_rect' (f : FunType) {struct f} : F f
  with ArrowType_rect' (a : ArrowType) {struct a} : A a
  with HeapType_rect' (h : HeapType) {struct h} : H h.
  Proof.
    - destruct t.
      + apply HNum.
      + apply HVar.
      + apply HUnit.
      + apply HProd.
        induction τ__s; [constructor|constructor].
        * apply Typ_rect'.
        * apply IHτ__s.
      + apply HCoderef, FunType_rect'.
      + apply HRec, Typ_rect'.
      + apply HPtr.
      + apply HExLoc, Typ_rect'.
      + apply HOwn.
      + apply HCap, HeapType_rect'.
      + apply HRef, HeapType_rect'.
    - destruct f. apply HFun, ArrowType_rect'.
    - destruct a as [l1 l2].
      apply HArrow; ((induction l1 + induction l2); constructor;
                     [apply Typ_rect'|apply IHl1+apply IHl2]).
    - destruct h.
      + apply HVariant. induction τ__s; constructor; [apply Typ_rect'|apply IHτ__s].
      + apply HStruct. induction fields; constructor; [destruct a; apply Typ_rect'|apply IHfields].
      + apply HArray, Typ_rect'.
      + apply HEx, Typ_rect'.
  Defined.

  Corollary Typ_Fun_Arrow_Heap_rect :
    (forall p, P p) * (forall f, F f) * (forall a, A a) * (forall h, H h).
  Proof.
    repeat split;
      (apply Typ_rect'||apply FunType_rect'
       ||apply ArrowType_rect'||apply HeapType_rect').
  Qed.
  
End TypeRect.
