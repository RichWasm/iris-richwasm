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
| QUAL : list Qual -> list Qual -> KindVar
| SIZE : list Size -> list Size -> KindVar
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
| NumConst (nτ : NumType) (val : nat)
| Tt (* Unit value *)
| Coderef (module_index : nat) (table_index : nat) (z__s : list Index)
| Fold (v : Value)
| Prod (v__s : list Value)
| Ref (ℓ : Loc)
| PtrV (ℓ : Loc)
| Cap
| Own
| Mempack (ℓ : Loc) (v : Value).

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

Inductive Instruction :=
(* Values are instructions *)
| Val (v : Value)

| Ne (ni : NumInstr)
| Unreachable
| Nop
| Drop
| Select
| Block (tf : ArrowType) (le : LocalEffect) (e__s : list Instruction)
| Loop (tf : ArrowType) (e : list Instruction)
| ITE (tf : ArrowType) (le : LocalEffect) (e__thn : list Instruction) (e__els : list Instruction)
| Br (i : nat)
| Br_if (i : nat)
| Br_table (i__s : list nat) (j : nat)
| Ret
| Get_local (i : nat) (q : Qual)
| Set_local (i : nat)
| Tee_local (i : nat)
| Get_global (i : nat)
| Set_global (i : nat)
| CoderefI (i : nat)
| Inst (z__s : list Index)
| Call_indirect
| Call (i : nat) (z__s : list Index)
(* Rec *)
| RecFold (τ : Typ)
| RecUnfold
(* Seq *)
| Group (i : nat) (q : Qual)
| Ungroup
(* Cap Instructions *)
| CapSplit
| CapJoin
| RefDemote
| MemPack (ℓ : Loc) (* XXX Loc or not? *)
| MemUnpack (tf : ArrowType) (le : LocalEffect) (e__s : list Instruction) (* binding site *)
(* Struct Instructions *)
| StructMalloc (sz__s : list Size) (q : Qual)
| StructFree
| StructGet (i : nat)
| StructSet (i : nat)
| StructSwap (i : nat)
(* Variant Instructions *)
| VariantMalloc (i : nat) (τ__s : list Typ) (q : Qual)
| VariantCase (q : Qual) (ψ : HeapType) (tf : ArrowType) (le : LocalEffect) (e__ss : list (list Instruction))
(* Array Instructions *)
| ArrayMalloc (q : Qual)
| ArrayGet
| ArraySet
| ArrayFree
(* Existsential Instructions *)
| ExistPack (τ : Typ) (ψ : HeapType) (q : Qual)
| ExistUnpack (q : Qual) (ψ : HeapType) (tf : ArrowType) (le : LocalEffect) (e__s : list Instruction)
(* Ref operations *)
| RefSplit
| RefJoin
| Qualify (q : Qual)
(* Administrative Instructions *)
| Trap
| CallAdm :  Closure -> list Index -> Instruction
| Label : nat -> ArrowType -> list Instruction -> list Instruction -> Instruction
| Local : nat -> nat -> list Value -> list nat (* sizes of local slots (args + locals) *) -> list Instruction -> Instruction
| Malloc : Size -> HeapValue -> Qual -> Instruction
| Free

with Func :=
| Fun : list ex -> FunType -> list Size -> list Instruction -> Func

with Closure :=
| Clo : nat -> Func -> Closure.


Coercion Val : Value >-> Instruction.

Inductive Glob :=
| GlobMut(τ : Typ) (i__s : list Instruction)
| GlobEx (ex__s : list ex) (τ : Typ) (i__s : list Instruction)
| GlobIm (ex__s : list ex) (τ : Typ) (im : im).

Definition module :=
  (list Func *
   list Glob *
   Table)%type.

Record MInst :=
  { func : list Closure;
    glob : list (Mut * Value);
    tab  : list Closure;
  }.

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
  induction v__s.
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
  induction v__s.
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

Section InstructionInd.
  Context
    (I : Instruction -> Prop)
    (F : Func -> Prop)
    (C : Closure -> Prop).

  Context
    (HVal : forall v, I (Val v))
    (HNe : forall ninstr, I (Ne ninstr))
    (HUnreachable : I Unreachable)
    (HNop : I Nop)
    (HDrop : I Drop)
    (HSelect : I Select)
    (HBlock : forall arty leff insns, Forall I insns -> I (Block arty leff insns))
    (HLoop  : forall arty insns, Forall I insns -> I (Loop arty insns))
    (HITE   : forall arty leff insns1 insns2,
        Forall I insns1 ->
        Forall I insns2 ->
        I (ITE arty leff insns1 insns2))
    (HBr    : forall n, I (Br n))
    (HBr_if : forall n, I (Br_if n))
    (HBr_table : forall ns n, I (Br_table ns n))
    (HRet : I Ret)
    (HGet_local  : forall n qual, I (Get_local n qual))
    (HSet_local  : forall n, I (Set_local n))
    (HTee_local  : forall n, I (Tee_local n))
    (HGet_global : forall n, I (Get_global n))
    (HSet_global : forall n, I (Set_global n))
    (HCoderefI   : forall n, I (CoderefI n))
    (HInst       : forall ixs, I (Inst ixs))
    (HCall_indirect : I Call_indirect)
    (HCall : forall n ixs, I (Call n ixs))
    (HRecFold : forall pt, I (RecFold pt))
    (HRecUnfold : I RecUnfold)
    (HGroup : forall n qual, I (Group n qual))
    (HUngroup : I Ungroup)
    (HCapSplit : I CapSplit)
    (HCapJoin : I CapJoin)
    (HRefDemote  : I RefDemote)
    (HMemPack   : forall l, I (MemPack l))
    (HMemUnpack : forall arty leff insns, Forall I insns -> I (MemUnpack arty leff insns))
    (HStructMalloc : forall szs qual, I (StructMalloc szs qual))
    (HStructFree : I StructFree)
    (HStructGet : forall n, I (StructGet n))
    (HStructSet : forall n, I (StructSet n))
    (HStructSwap : forall n, I (StructSwap n))
    (HVariantMalloc : forall n typs qual, I (VariantMalloc n typs qual))
    (HVariantCase   : forall qual arty leff insnss tausv,
        Forall (Forall I) insnss ->
        I (VariantCase qual tausv arty leff insnss))
    (HArrayMalloc : forall qual, I (ArrayMalloc qual))
    (HArrayGet : I ArrayGet)
    (HArraySet : I ArraySet)
    (HArrayFree : I ArrayFree)
    (HExistPack   : forall pt ht qual, I (ExistPack pt ht qual))
    (HExistUnpack : forall qual arty leff insns ex , Forall I insns -> I (ExistUnpack qual ex arty leff insns))
    (HRefSplit  : I RefSplit)
    (HRefJoin : I RefJoin)
    (HQualify : forall qual, I (Qualify qual))
    (HTrap : I Trap)
    (HCallAdm : forall clo ixs, C clo -> I (CallAdm clo ixs))
    (HLabel : forall n arty insns1 insns2,
        Forall I insns1 ->
        Forall I insns2 ->
        I (Label n arty insns1 insns2))
    (HLocal : forall n1 n2 vs ns insns, Forall I insns -> I (Local n1 n2 vs ns insns))
    (HMalloc : forall sz hv qual, I (Malloc sz hv qual))
    (HFree : I Free).

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
  
  Fixpoint Instruction_ind' (insn : Instruction) {struct insn} : I insn
  with Func_ind' (func : Func) {struct func} : F func
  with Closure_ind' (clo : Closure) {struct clo} : C clo.
  Proof.
    - destruct insn;
      multimatch goal with
      | HI : forall x, I x, HF : forall x, F x, HC : forall x, C x, H : _ |- _ => apply H
      end; solve [list_ind|clear_ihs; eauto|eauto].
    - destruct func; apply HFun; list_ind.
    - destruct clo; apply HClo; apply Func_ind'.
  Qed.

  Corollary Instruction_Func_Closure_ind :
    (forall i, I i) /\ (forall f, F f) /\ (forall c, C c).
  Proof. repeat split; (apply Instruction_ind'||apply Func_ind'||apply Closure_ind'). Qed.
  
End InstructionInd.
