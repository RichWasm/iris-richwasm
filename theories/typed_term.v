Require Export term.

Inductive Instruction :=
| Instr : PreInstruction -> ArrowType -> Instruction
with PreInstruction :=
(* Values are instructions *)
| Val : Value -> PreInstruction
| Ne : NumInstr -> PreInstruction
| Unreachable
| Nop
| Drop
| Select
| Block : ArrowType -> LocalEffect -> list Instruction -> PreInstruction
| Loop  : ArrowType -> list Instruction -> PreInstruction
| ITE   : ArrowType -> LocalEffect -> list Instruction -> list Instruction -> PreInstruction
| Br    : nat -> PreInstruction
| Br_if : nat -> PreInstruction
| Br_table : list nat -> nat -> PreInstruction
| Ret
| Get_local  : nat -> Qual -> PreInstruction
| Set_local  : nat -> PreInstruction
| Tee_local  : nat -> PreInstruction
| Get_global : nat -> PreInstruction
| Set_global : nat -> PreInstruction
| CoderefI   : nat -> PreInstruction
| Inst       : list Index -> PreInstruction
| Call_indirect
| Call : nat -> list Index -> PreInstruction
(* Rec *)
| RecFold : Typ -> PreInstruction
| RecUnfold
(* Seq *)
| Group : nat -> Qual -> PreInstruction
| Ungroup
(* Cap Instructions *)
| CapSplit
| CapJoin
| RefDemote
| MemPack   : Loc -> PreInstruction (* XXX Loc or not? *)
| MemUnpack : ArrowType -> LocalEffect -> list Instruction -> PreInstruction (* binding site *)
(* Struct Instructions *)
| StructMalloc : list Size -> Qual -> PreInstruction
| StructFree
| StructGet : nat -> PreInstruction
| StructSet : nat -> PreInstruction
| StructSwap : nat -> PreInstruction
(* Variant Instructions *)
| VariantMalloc : nat -> list Typ -> Qual -> PreInstruction
| VariantCase   : Qual -> HeapType -> ArrowType -> LocalEffect -> list (list Instruction) -> PreInstruction
(* Array Instructions *)
| ArrayMalloc : Qual -> PreInstruction
| ArrayGet
| ArraySet
| ArrayFree
(* Existsential Instructions *)
| ExistPack   : Typ -> HeapType -> Qual -> PreInstruction
| ExistUnpack : Qual -> HeapType -> ArrowType -> LocalEffect -> list Instruction -> PreInstruction (* binding site *)
(* Ref operations *)
| RefSplit
| RefJoin
| Qualify : Qual -> PreInstruction
(* Administrative Instructions *)
| Trap
| CallAdm :  Closure -> list Index -> PreInstruction
| Label : nat -> ArrowType -> list Instruction -> list Instruction -> PreInstruction
| Local : nat -> nat -> list Value -> list nat (* sizes of local slots (args + locals) *) -> list Instruction -> PreInstruction
| Malloc : Size -> HeapValue -> Qual -> PreInstruction
| Free
with Func :=
| Fun : list ex -> FunType -> list Size -> list Instruction -> Func
with Closure :=
| Clo : nat -> Func -> Closure.
