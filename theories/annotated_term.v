Set Universe Polymorphism.
Require Export term.

Inductive Instruction :=
| Instr (pre : PreInstruction) (tf : ArrowType)
with PreInstruction :=
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
| CallAdm : Closure -> list Index -> PreInstruction
| Label : nat -> ArrowType -> list Instruction -> list Instruction -> PreInstruction
| Local : nat -> nat -> list Value -> list nat (* sizes of local slots (args + locals) *) -> list Instruction -> PreInstruction
| Malloc : Size -> HeapValue -> Qual -> PreInstruction
| Free
with Func :=
| Fun (ex__s : list ex) (χ : FunType) (sz__s : list Size) (e__s : list Instruction)
with Closure :=
| Clo (i : nat) (f : Func).
