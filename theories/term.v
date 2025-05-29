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

Fixpoint typ_qual (loc_quals: qual_ctx) (ty_quals: qual_ctx) (ty: Typ) : option Qual :=
  match ty with
  | Num _
  | Unit
  | CoderefT _
  | PtrT _ => mret (Unrestricted: Qual)
  | TVar α => ty_quals !! α
  | ProdT tys => quals ← (mapM (typ_qual loc_quals ty_quals) tys); mret (QualJoin quals)
  | Rec q ty => mret q
  | ExLoc q ty => typ_qual (q :: loc_quals) ty_quals ty
  | OwnR loc => loc_qual loc_quals loc
  | CapT _ loc _ 
  | RefT _ loc _ => loc_qual loc_quals loc
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

Inductive Instruction :=
(* Values are instructions *)
| Val : Value -> Instruction

| Ne : NumInstr -> Instruction
| Unreachable
| Nop
| Drop
| Select
| Block : ArrowType -> LocalEffect -> list Instruction -> Instruction
| Loop  : ArrowType -> list Instruction -> Instruction
| ITE   : ArrowType -> LocalEffect -> list Instruction -> list Instruction -> Instruction
| Br    : nat -> Instruction
| Br_if : nat -> Instruction
| Br_table : list nat -> nat -> Instruction
| Ret
| Get_local  : nat -> Qual -> Instruction
| Set_local  : nat -> Instruction
| Tee_local  : nat -> Instruction
| Get_global : nat -> Instruction
| Set_global : nat -> Instruction
| CoderefI   : nat -> Instruction
| Inst       : list Index -> Instruction
| Call_indirect
| Call : nat -> list Index -> Instruction
(* Rec *)
| RecFold : Typ -> Instruction
| RecUnfold
(* Seq *)
| Group : nat -> Qual -> Instruction
| Ungroup : Instruction
(* Cap Instructions *)
| CapSplit
| CapJoin
| RefDemote
| MemPack   : Loc -> Instruction (* XXX Loc or not? *)
| MemUnpack : ArrowType -> LocalEffect -> list Instruction -> Instruction (* binding site *)
(* Struct Instructions *)
| StructMalloc : list Size -> Qual -> Instruction
| StructFree
| StructGet : nat -> Instruction
| StructSet : nat -> Instruction
| StructSwap : nat -> Instruction
(* Variant Instructions *)
| VariantMalloc : nat -> list Typ -> Qual -> Instruction
| VariantCase   : Qual -> HeapType -> ArrowType -> LocalEffect -> list (list Instruction) -> Instruction
(* Array Instructions *)
| ArrayMalloc : Qual -> Instruction
| ArrayGet
| ArraySet
| ArrayFree
(* Existsential Instructions *)
| ExistPack   : Typ -> HeapType -> Qual -> Instruction
| ExistUnpack : Qual -> HeapType -> ArrowType -> LocalEffect -> list Instruction -> Instruction (* binding site *)
(* Ref operations *)
| RefSplit
| RefJoin
| Qualify : Qual -> Instruction
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
| GlobMut : Typ -> list Instruction -> Glob
| GlobEx : list ex -> Typ -> list Instruction -> Glob
| GlobIm : list ex -> Typ -> im -> Glob.

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
