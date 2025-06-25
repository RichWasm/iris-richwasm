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

Inductive Value :=
| NumConst  : NumType -> nat -> Value
| Tt        : Value (* Unit value *)
| Coderef   : nat(* module index *) -> nat (* table index *) -> list Index -> Value
| Fold      : Value -> Value
| Prod      : list Value -> Value
| Ref       : Loc -> Value
| PtrV      : Loc -> Value
| Cap       : Value
| Own       : Value
| Mempack   : Loc -> Value -> Value.

Inductive HeapValue :=
| Variant : nat -> Value -> HeapValue
| Struct  : list Value -> HeapValue
| Array   : nat -> list Value -> HeapValue
| Pack    : Typ -> Value ->  HeapType -> HeapValue.

(* Size of a value in words. *)
Fixpoint size_val (v : Value) : nat :=
  match v with
  | NumConst (Int _ i32) _ => 1
  | NumConst (Int _ i64) _ => 2
  | NumConst (Float f32) _ => 1
  | NumConst (Float f64) _ => 2
  | Tt => 1
  | Coderef _ _ _ => 2
  | Fold v => size_val v
  | Prod vs => sum_list_with size_val vs
  | Ref _ => 1
  | PtrV _ => 1
  | Cap => 0
  | Own => 0
  | Mempack _ v => size_val v
  end.

Definition size (hv : HeapValue) : nat :=
  match hv with
  | Variant n v => 1 + size_val v
  | Struct vs => sum_list_with size_val vs
  | Array i vs => sum_list_with size_val vs
  | Pack p v ht => 1 + size_val v
  end.

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

Inductive basic_instr A :=
  | Val : A -> Value -> basic_instr A
  | Ne : A -> NumInstr -> basic_instr A
  | Unreachable : A -> basic_instr A
  | Nop : A -> basic_instr A
  | Drop : A -> basic_instr A
  | Select : A -> basic_instr A
  | Block : A -> ArrowType -> LocalEffect -> list (basic_instr A) -> basic_instr A
  | Loop : A -> ArrowType -> list (basic_instr A) -> basic_instr A
  | ITE : A -> ArrowType -> LocalEffect -> list (basic_instr A) -> list (basic_instr A) -> basic_instr A
  | Br : A -> nat -> basic_instr A
  | Br_if : A -> nat -> basic_instr A
  | Br_table : A -> list nat -> nat -> basic_instr A
  | Ret : A -> basic_instr A
  | Get_local : A -> nat -> Qual -> basic_instr A
  | Set_local : A -> nat -> basic_instr A
  | Tee_local : A -> nat -> basic_instr A
  | Get_global : A -> nat -> basic_instr A
  | Set_global : A -> nat -> basic_instr A
  | CoderefI : A -> nat -> basic_instr A
  | Inst : A -> list Index -> basic_instr A
  | Call_indirect : A -> basic_instr A
  | Call : A -> nat -> list Index -> basic_instr A
  | RecFold : A -> Typ -> basic_instr A
  | RecUnfold : A -> basic_instr A
  | Group : A -> nat -> Qual -> basic_instr A
  | Ungroup : A -> basic_instr A
  | CapSplit : A -> basic_instr A
  | CapJoin : A -> basic_instr A
  | RefDemote : A -> basic_instr A
  | MemPack : A -> Loc -> basic_instr A (* XXX Loc or not? *)
  | MemUnpack : A -> ArrowType -> LocalEffect -> list (basic_instr A) -> basic_instr A (* binding site *)
  | StructMalloc : A -> list Size -> Qual -> basic_instr A
  | StructFree : A -> basic_instr A
  | StructGet : A -> nat -> basic_instr A
  | StructSet: A -> nat -> basic_instr A
  | StructSwap : A -> nat -> basic_instr A
  | VariantMalloc : A -> nat -> list Typ -> Qual -> basic_instr A
  | VariantCase : A -> Qual -> HeapType -> ArrowType -> LocalEffect -> list (list (basic_instr A)) -> basic_instr A
  | ArrayMalloc : A -> Qual -> basic_instr A
  | ArrayGet : A -> basic_instr A
  | ArraySet : A -> basic_instr A
  | ArrayFree : A -> basic_instr A
  | ExistPack : A -> Typ -> HeapType -> Qual -> basic_instr A
  | ExistUnpack : A -> Qual -> HeapType -> ArrowType -> LocalEffect -> list (basic_instr A) -> basic_instr A (* binding site *)
  | RefSplit : A -> basic_instr A
  | RefJoin : A -> basic_instr A
  | Qualify : A -> Qual -> basic_instr A.

Arguments Val {_} _ _.
Arguments Ne {_} _ _.
Arguments Unreachable {_} _.
Arguments Nop {_} _.
Arguments Drop {_} _.
Arguments Select {_} _.
Arguments Block {_} _ _ _ _.
Arguments Loop {_} _ _ _.
Arguments ITE {_} _ _ _ _.
Arguments Br {_} _ _.
Arguments Br_if {_} _ _.
Arguments Br_table {_} _ _ _.
Arguments Ret {_} _.
Arguments Get_local {_} _ _ _.
Arguments Set_local {_} _ _.
Arguments Tee_local {_} _ _.
Arguments Get_global {_} _ _.
Arguments Set_global {_} _ _.
Arguments CoderefI {_} _ _.
Arguments Inst {_} _ _.
Arguments Call_indirect {_} _.
Arguments Call {_} _ _ _.
Arguments RecFold {_} _ _.
Arguments RecUnfold {_} _.
Arguments Group {_} _ _ _.
Arguments Ungroup {_} _.
Arguments CapSplit {_} _.
Arguments CapJoin {_} _.
Arguments RefDemote {_} _.
Arguments MemPack {_} _ _.
Arguments MemUnpack {_} _ _ _ _.
Arguments StructMalloc {_} _ _ _.
Arguments StructFree {_} _.
Arguments StructGet {_} _ _.
Arguments StructSet {_} _ _.
Arguments StructSwap {_} _ _.
Arguments VariantMalloc {_} _ _ _ _.
Arguments VariantCase {_} _ _ _ _ _ _.
Arguments ArrayMalloc {_} _ _.
Arguments ArrayGet {_} _.
Arguments ArraySet {_} _.
Arguments ArrayFree {_} _.
Arguments ExistPack {_} _ _ _ _.
Arguments ExistUnpack {_} _ _ _ _ _ _.
Arguments RefSplit {_} _.
Arguments RefJoin {_} _.
Arguments Qualify {_} _ _.

Inductive Func A :=
  | Fun : list ex -> FunType -> list Size -> list (basic_instr A) -> Func A.

Arguments Fun {_} _ _ _ _.

Inductive Closure A :=
  | Clo : nat -> Func A -> Closure A.

Arguments Clo {_} _ _.

Inductive admin_instr A :=
  | Basic : basic_instr A -> admin_instr A
  | Trap
  | CallAdm : Closure A -> list Index -> admin_instr A
  | Label : nat -> ArrowType -> list (admin_instr A) -> list (admin_instr A) -> admin_instr A
  | Local : nat -> nat -> list Value -> list nat (* sizes of local slots (args + locals) *) -> list (admin_instr A) -> admin_instr A
  | Malloc : Size -> HeapValue -> Qual -> admin_instr A
  | Free.

Arguments Basic {_} _.
Arguments Trap {_}.
Arguments CallAdm {_} _ _.
Arguments Label {_} _ _ _ _.
Arguments Local {_} _ _ _ _ _.
Arguments Malloc {_} _ _ _.
Arguments Free {_}.

Inductive Glob A :=
| GlobMut : Typ -> list (basic_instr A) -> Glob A
| GlobEx : list ex -> Typ -> list (basic_instr A) -> Glob A
| GlobIm : list ex -> Typ -> im -> Glob A.

Arguments GlobMut {_} _ _.
Arguments GlobEx {_} _ _ _.
Arguments GlobIm {_} _ _ _.

Definition module A :=
  (list (Func A) *
   list (Glob A) *
   Table)%type.

Record MInst A :=
  { func : list (Closure A);
    glob : list (Mut * Value);
    tab  : list (Closure A);
  }.

Arguments Build_MInst {_} _ _ _.

(** Useful properties *)

Lemma Value_ind' :
  forall P : Value -> Prop,
    (forall (n : NumType) (n0 : nat), P (NumConst n n0)) ->
    P Tt ->
    (forall (n n0 : nat) (l : list Index), P (Coderef n n0 l)) ->
    (forall v : Value, P v -> P (Fold v)) ->
    (forall l : list Value, Forall P l -> P (Prod l)) ->
    (forall l : Loc, P (Ref l)) ->
    (forall l : Loc, P (PtrV l)) ->
    P Cap ->
    P Own ->
    (forall (l : Loc) (v : Value), P v -> P (Mempack l v)) ->
    forall v : Value, P v.
Proof.
  intros P H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
  fix IHv 1. induction v; try (now clear IHv; eauto).
  eapply H5.
  induction l.
  - now constructor.
  - constructor. eapply IHv. eassumption.
Qed.

Inductive Forall_type {A : Type} (P : A -> Type) : list A -> Type :=
| Forall_type_nil : Forall_type P []
| Forall_type_cons : forall (x : A) (l : list A),
    P x -> Forall_type P l -> Forall_type P (x :: l).

Lemma Value_rect' :
  forall P : Value -> Type,
    (forall (n : NumType) (n0 : nat), P (NumConst n n0)) ->
    P Tt ->
    (forall (n n0 : nat) (l : list Index), P (Coderef n n0 l)) ->
    (forall v : Value, P v -> P (Fold v)) ->
    (forall l : list Value, Forall_type P l -> P (Prod l)) ->
    (forall l : Loc, P (Ref l)) ->
    (forall l : Loc, P (PtrV l)) ->
    P Cap ->
    P Own ->
    (forall (l : Loc) (v : Value), P v -> P (Mempack l v)) ->
    forall v : Value, P v.
Proof.
  intros P H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
  fix IHv 1. induction v; try (now clear IHv; eauto).
  eapply H5.
  induction l.
  - now constructor.
  - constructor. eapply IHv. eassumption.
Qed.

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

Section InstructionInd.
  Context
    (A : Type)
    (I : basic_instr A -> Prop)
    (F : Func A -> Prop)
    (C : Closure A -> Prop).

  Context
    (HVal : forall x v, I (Val x v))
    (HNe : forall x ninstr, I (Ne x ninstr))
    (HUnreachable : forall x, I (Unreachable x))
    (HNop : forall x, I (Nop x))
    (HDrop : forall x, I (Drop x))
    (HSelect : forall x, I (Select x))
    (HBlock : forall x arty leff insns, Forall I insns -> I (Block x arty leff insns))
    (HLoop : forall x arty insns, Forall I insns -> I (Loop x arty insns))
    (HITE : forall x arty leff insns1 insns2,
        Forall I insns1 ->
        Forall I insns2 ->
        I (ITE x arty leff insns1 insns2))
    (HBr : forall x n, I (Br x n))
    (HBr_if : forall x n, I (Br_if x n))
    (HBr_table : forall x ns n, I (Br_table x ns n))
    (HRet : forall x, I (Ret x))
    (HGet_local : forall x n qual, I (Get_local x n qual))
    (HSet_local : forall x n, I (Set_local x n))
    (HTee_local : forall x n, I (Tee_local x n))
    (HGet_global : forall x n, I (Get_global x n))
    (HSet_global : forall x n, I (Set_global x n))
    (HCoderefI : forall x n, I (CoderefI x n))
    (HInst : forall x ixs, I (Inst x ixs))
    (HCall_indirect : forall x, I (Call_indirect x))
    (HCall : forall x n ixs, I (Call x n ixs))
    (HRecFold : forall x pt, I (RecFold x pt))
    (HRecUnfold : forall x, I (RecUnfold x))
    (HGroup : forall x n qual, I (Group x n qual))
    (HUngroup : forall x, I (Ungroup x))
    (HCapSplit : forall x, I (CapSplit x))
    (HCapJoin : forall x, I (CapJoin x))
    (HRefDemote  : forall x, I (RefDemote x))
    (HMemPack   : forall x l, I (MemPack x l))
    (HMemUnpack : forall x arty leff insns, Forall I insns -> I (MemUnpack x arty leff insns))
    (HStructMalloc : forall x szs qual, I (StructMalloc x szs qual))
    (HStructFree : forall x, I (StructFree x))
    (HStructGet : forall x n, I (StructGet x n))
    (HStructSet : forall x n, I (StructSet x n))
    (HStructSwap : forall x n, I (StructSwap x n))
    (HVariantMalloc : forall x n typs qual, I (VariantMalloc x n typs qual))
    (HVariantCase : forall x qual arty leff insnss tausv,
        Forall (Forall I) insnss ->
        I (VariantCase x qual tausv arty leff insnss))
    (HArrayMalloc : forall x qual, I (ArrayMalloc x qual))
    (HArrayGet : forall x, I (ArrayGet x))
    (HArraySet : forall x, I (ArraySet x))
    (HArrayFree : forall x, I (ArrayFree x))
    (HExistPack : forall x pt ht qual, I (ExistPack x pt ht qual))
    (HExistUnpack : forall x qual arty leff insns ex , Forall I insns -> I (ExistUnpack x qual ex arty leff insns))
    (HRefSplit : forall x, I (RefSplit x))
    (HRefJoin : forall x, I (RefJoin x))
    (HQualify : forall x qual, I (Qualify x qual)).

  Context (HFun : forall exs fty szs insns, Forall I insns -> F (Fun exs fty szs insns)).

  Context (HClo : forall n func, F func -> C (Clo n func)).

  Local Ltac clear_ihs :=
    try match goal with
    | HI : forall x, I x, HF : forall x, F x, HC : forall x, C x |- _ => clear HI HF HC
    end.

  Local Ltac list_ind :=
    match goal with
    | IH : forall _, ?P _ |- Forall (Forall ?P) ?l =>
      clear - IH; induction l; constructor; try assumption; list_ind
    | IH : forall _, ?P _ |- Forall ?P ?l =>
      clear - IH; induction l; constructor; auto
    end.

End InstructionInd.
