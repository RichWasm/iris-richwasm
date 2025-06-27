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
| QualVar : var -> Qual
| QualJoin : list Qual -> Qual
| QualConst : QualConstant -> Qual.

Coercion QualConst : QualConstant >-> Qual.

Inductive Size :=
| SizeVar : var -> Size
| SizePlus : Size -> Size -> Size
| SizeConst : nat -> Size.

(* Numeric Types *)

Inductive IntType := i32 | i64.

Inductive FloatType := f32 | f64.

Inductive NumType :=
| Int : Sign -> IntType -> NumType
| Float : FloatType -> NumType.

Inductive KindVar := (* Binding sites for kind variables *)
| LOC  : Qual -> KindVar
| QUAL : list Qual -> list Qual -> KindVar
| SIZE : list Size -> list Size -> KindVar
| TYPE : Size -> Qual -> HeapableConstant -> KindVar.

Inductive Typ :=
| Num      : NumType -> Typ
| TVar     : var -> Typ
| Unit     : Typ
| ProdT    : list Typ -> Typ
| CoderefT : FunType -> Typ
| Rec      : Qual -> Typ -> Typ (* binding site *)
| PtrT     : Loc -> Typ
| ExLoc    : Qual -> Typ -> Typ (* binding site *)
| OwnR     : Loc -> Typ
| CapT     : cap -> Loc -> HeapType -> Typ
| RefT     : cap -> Loc -> HeapType -> Typ

with HeapType :=
| VariantType : list Typ -> HeapType
| StructType  : list (Typ * Size) -> HeapType
| ArrayType   : Typ -> HeapType
| Ex          : Size -> Qual -> Typ -> HeapType (* binding site *)

with ArrowType :=
| Arrow : list Typ -> list Typ -> ArrowType

with FunType :=
| FunT : list KindVar -> ArrowType -> FunType.

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
| LocI  : Loc -> Index
| SizeI : Size -> Index
| QualI : Qual -> Index
| TypI  : Typ -> Index.

Coercion LocI  : Loc >-> Index.
Coercion SizeI : Size >-> Index.
Coercion QualI : Qual >-> Index.
Coercion TypI  : Typ >-> Index.

(** ** Terms *)

Inductive IUnOp :=
| clz | ctz | popcnt.

Inductive IBinOp :=
| add | sub | mul | div : Sign -> IBinOp | rem : Sign -> IBinOp
| and | or | xor | shl | shr : Sign -> IBinOp | rotl | rotr.

Inductive FUnOp :=
| neg | abs | ceil | floor | trunc | nearest | sqrt.

Inductive FBinOp :=
| addf | subf | mulf | divf | min | max | copysign.

Inductive ITestOp := eqz.

Inductive IRelOp :=
| eq | ne
| lt : Sign -> IRelOp | gt : Sign -> IRelOp
| le : Sign -> IRelOp | ge : Sign -> IRelOp.

Inductive FRelOp :=
| eqf | nef
| ltf | gtf
| lef | gef.

Inductive CvtOp :=
| Wrap        : IntType -> CvtOp
| Extend      : IntType -> Sign -> CvtOp
| Trunc       : FloatType -> Sign -> CvtOp
| TruncSat    : FloatType -> Sign -> CvtOp
| Convert     : IntType -> Sign -> CvtOp
| Demote      : FloatType -> CvtOp
| Promote     : FloatType -> CvtOp
| Reinterpret : IntType -> CvtOp.

Inductive NumInstr :=
| Iu   : IntType -> IUnOp -> NumInstr
| Ib   : IntType -> IBinOp -> NumInstr
| Fu   : FloatType -> FUnOp -> NumInstr
| Fb   : FloatType -> FBinOp -> NumInstr
| It   : IntType -> ITestOp -> NumInstr
| Ir   : IntType -> IRelOp -> NumInstr
| Fr   : FloatType -> FRelOp -> NumInstr
| CvtI : IntType -> CvtOp -> NumInstr
| CvtF : FloatType -> CvtOp -> NumInstr.

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
  | IIte (ann : A) (ta : ArrowType) (tl : LocalEffect) (es1 : list instr) (es1 : list instr)
  | IBr (ann : A) (n : nat)
  | IBrIf (ann : A) (n : nat)
  | IBrTable (ann : A) (ns : list nat) (n : nat)
  | IRet (ann : A)
  | IGetLocal (ann : A) (n : nat) (q : Qual)
  | ISetLocal (ann : A) (n : nat)
  | ITeeLocal (ann : A) (n : nat)
  | IGetGlobal (ann : A) (n : nat)
  | ISetGlobal (ann : A) (n : nat)
  | ICoderef (ann : A) (n : nat)
  | IInst (ann : A) (idxs : list Index)
  | ICallIndirect (ann : A)
  | ICall (ann : A) (n : nat) (idxs : list Index)
  | IRecFold (ann : A) (ty : Typ)
  | IRecUnfold (ann : A)
  | IGroup (ann : A) (n : nat) (q : Qual)
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
  | IVariantMalloc (ann : A) (n : nat) (ts : list Typ) (q : Qual)
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
  | Fun : list ex -> FunType -> list Size -> list (instr A) -> Func A.

Arguments Fun {_} _ _ _ _.

Inductive Closure A :=
  | Clo : nat -> Func A -> Closure A.

Arguments Clo {_} _ _.

Inductive Glob A :=
| GlobMut : Typ -> list (instr A) -> Glob A
| GlobEx : list ex -> Typ -> list (instr A) -> Glob A
| GlobIm : list ex -> Typ -> im -> Glob A.

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
        induction l; [constructor|constructor].
        * apply Typ_ind'.
        * apply IHl.
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
      + apply HVariant. induction l; constructor; [apply Typ_ind'|apply IHl].
      + apply HStruct. induction l; constructor; [destruct a; apply Typ_ind'|apply IHl].
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
        induction l; [constructor|constructor].
        * apply Typ_rect'.
        * apply IHl.
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
      + apply HVariant. induction l; constructor; [apply Typ_rect'|apply IHl].
      + apply HStruct. induction l; constructor; [destruct a; apply Typ_rect'|apply IHl].
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
