From Coq Require Import List NArith.BinNat Lists.List.
From stdpp Require Import base option strings list pretty.
From Wasm Require datatypes.
From RWasm Require term annotated_term.
From RWasm.compiler Require Import numbers monads.


Module BoxPolymorphicIR.

  Inductive Typ :=
  | Num (nτ : rwasm.NumType)
  | BoxedT (τ : Typ)
  | TVar (α : rwasm.var) (* must be boxed *)
  | Unit
  | ProdT (τ__s : list Typ)
  | CoderefT (χ : FunType)
  | Rec (q : rwasm.Qual) (τ : Typ) (* binding site *)
  | PtrT (ℓ : rwasm.Loc)
  | ExLoc (q : rwasm.Qual) (τ : Typ) (* binding site *)
  | OwnR (ℓ : rwasm.Loc)
  | CapT (cap : rwasm.cap) (ℓ : rwasm.Loc) (ψ : HeapType)
  | RefT (cap : rwasm.cap) (ℓ : rwasm.Loc) (ψ : HeapType)

  with HeapType :=
  | VariantType (τ__s : list Typ)
  | StructType (fields : list (Typ * rwasm.Size))
  | ArrayType (τ : Typ)
  | Ex (sz : rwasm.Size) (q : rwasm.Qual) (τ : Typ) (* binding site *)

  with ArrowType :=
  | Arrow (τ__s1 : list Typ) (τ__s2 : list Typ)

  with FunType :=
  | FunT (κ : list rwasm.KindVar) (tf : ArrowType).

  Definition LocalEffect := list (nat * Typ).

  Inductive Value :=
  | NumConst (nτ : rwasm.NumType) (val : nat)
  | Tt (* Unit value *)
  | Coderef (module_index : nat) (table_index : nat) (z__s : list rwasm.Index)
  | Fold (v : Value)
  | Prod (v__s : list Value)
  | Ref (ℓ : rwasm.Loc)
  | PtrV (ℓ : rwasm.Loc)
  | Cap
  | Own
  | Mempack (ℓ : rwasm.Loc) (v : Value)
  (* boxed polymorphic value *)
  | Boxed (v : Value).


  Inductive Instruction :=
  | Instr (pre : PreInstruction) (tf : ArrowType)
  with PreInstruction :=
  (* Values are instructions *)
  | Val (v : Value)
  | Ne (ni : rwasm.NumInstr)
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
  | Get_local (i : nat) (q : rwasm.Qual)
  | Set_local (i : nat)
  | Tee_local (i : nat)
  | Get_global (i : nat)
  | Set_global (i : nat)
  | CoderefI (i : nat)
  | Inst (z__s : list rwasm.Index)
  | Call_indirect
  | Call (i : nat) (z__s : list rwasm.Index)
  (* Rec *)
  | RecFold (τ : Typ)
  | RecUnfold
  (* Seq *)
  | Group (i : nat) (q : rwasm.Qual)
  | Ungroup
  (* Cap Instructions *)
  | CapSplit
  | CapJoin
  | RefDemote
  | MemPack (ℓ : rwasm.Loc) (* XXX Loc or not? *)
  | MemUnpack (tf : ArrowType) (le : LocalEffect) (e__s : list Instruction) (* binding site *)
  (* Struct Instructions *)
  | StructMalloc (sz__s : list rwasm.Size) (q : rwasm.Qual)
  | StructFree
  | StructGet (i : nat)
  | StructSet (i : nat)
  | StructSwap (i : nat)
  (* Variant Instructions *)
  | VariantMalloc (i : nat) (τ__s : list Typ) (q : rwasm.Qual)
  | VariantCase (q : rwasm.Qual) (ψ : HeapType) (tf : ArrowType) (le : LocalEffect) (e__ss : list (list Instruction))
  (* Array Instructions *)
  | ArrayMalloc (q : rwasm.Qual)
  | ArrayGet
  | ArraySet
  | ArrayFree
  (* Existsential Instructions *)
  | ExistPack (τ : Typ) (ψ : HeapType) (q : rwasm.Qual)
  | ExistUnpack (q : rwasm.Qual) (ψ : HeapType) (tf : ArrowType) (le : LocalEffect) (e__s : list Instruction)
  (* Ref operations *)
  | RefSplit
  | RefJoin
  | Qualify (q : rwasm.Qual).
  (* Administrative Instructions *)
  (* | Trap *)
  (* | CallAdm : Closure -> list rwasm.Index -> PreInstruction *)
  (* | Label : nat -> ArrowType -> list Instruction -> list Instruction -> PreInstruction *)
  (* | Local : nat -> nat -> list Value -> list nat (* sizes of local slots (args + locals) *) -> list Instruction -> PreInstruction *)
  (* | Malloc : Size -> HeapValue -> Qual -> PreInstruction *)
  (* | Free *)
  (* withFunc := *)
  (* | Fun : list wasm.ex -> FunType -> list Size -> list Instruction -> Func *)
  (* with Closure := *)
  (* | Clo : nat -> Func -> Closure. *)

  Fixpoint compile_val (val : rwasm.Value) : Value :=
   match val with
   | rwasm.NumConst nτ val => NumConst nτ val
   | rwasm.Tt => Tt
   | rwasm.Coderef module_index table_index z__s => Coderef module_index table_index z__s
   | rwasm.Fold v => Fold (compile_val v)
   | rwasm.Prod v__s => Prod (map compile_val v__s)
   | rwasm.Ref ℓ => Ref ℓ
   | rwasm.PtrV ℓ => PtrV ℓ
   | rwasm.Cap => Cap
   | rwasm.Own => Own
   | rwasm.Mempack ℓ v => Mempack ℓ (compile_val v)
   end.

  Fixpoint compile_arrow (tf : rwasm.ArrowType) : M ArrowType :=
   match tf with
   | rwasm.Arrow τ__s1 τ__s2 => mthrow (err "TODO")
   end.

  Fixpoint compile_instruction (instr : AR.Instruction) : M Instruction :=
    match instr with
    | AR.Instr pre tf =>
        pre' ← compile_pre_instruction pre;
        tf' ← compile_arrow tf;
        mret $ Instr pre' tf'
    end
  with compile_pre_instruction (pre : AR.PreInstruction) : M PreInstruction :=
    match pre with
    | AR.Val v => mthrow (err "TODO")
    | AR.Ne ni => mthrow (err "TODO")
    | AR.Unreachable => mthrow (err "TODO")
    | AR.Nop => mthrow (err "TODO")
    | AR.Drop => mthrow (err "TODO")
    | AR.Select => mthrow (err "TODO")
    | AR.Block tf le e__s => mthrow (err "TODO")
    | AR.Loop tf e => mthrow (err "TODO")
    | AR.ITE tf le e__thn e__els => mthrow (err "TODO")
    | AR.Br i => mthrow (err "TODO")
    | AR.Br_if i => mthrow (err "TODO")
    | AR.Br_table i__s j => mthrow (err "TODO")
    | AR.Ret => mthrow (err "TODO")
    | AR.Get_local i q => mthrow (err "TODO")
    | AR.Set_local i => mthrow (err "TODO")
    | AR.Tee_local i => mthrow (err "TODO")
    | AR.Get_global i => mthrow (err "TODO")
    | AR.Set_global i => mthrow (err "TODO")
    | AR.CoderefI i => mthrow (err "TODO")
    | AR.Inst z__s => mthrow (err "TODO")
    | AR.Call_indirect => mthrow (err "TODO")
    | AR.Call i z__s => mthrow (err "TODO")
    | AR.RecFold τ => mthrow (err "TODO")
    | AR.RecUnfold => mthrow (err "TODO")
    | AR.Group i q => mthrow (err "TODO")
    | AR.Ungroup => mthrow (err "TODO")
    | AR.CapSplit => mthrow (err "TODO")
    | AR.CapJoin => mthrow (err "TODO")
    | AR.RefDemote => mthrow (err "TODO")
    | AR.MemPack ℓ => mthrow (err "TODO")
    | AR.MemUnpack tf le e__s => mthrow (err "TODO")
    | AR.StructMalloc sz__s q => mthrow (err "TODO")
    | AR.StructFree => mthrow (err "TODO")
    | AR.StructGet i => mthrow (err "TODO")
    | AR.StructSet i => mthrow (err "TODO")
    | AR.StructSwap i => mthrow (err "TODO")
    | AR.VariantMalloc i τ__s q => mthrow (err "TODO")
    | AR.VariantCase q ψ tf le e__ss => mthrow (err "TODO")
    | AR.ArrayMalloc q => mthrow (err "TODO")
    | AR.ArrayGet => mthrow (err "TODO")
    | AR.ArraySet => mthrow (err "TODO")
    | AR.ArrayFree => mthrow (err "TODO")
    | AR.ExistPack τ ψ q => mthrow (err "TODO")
    | AR.ExistUnpack q ψ tf le e__s => mthrow (err "TODO")
    | AR.RefSplit => mthrow (err "TODO")
    | AR.RefJoin => mthrow (err "TODO")
    | AR.Qualify q => mthrow (err "TODO")
    | AR.Trap
    | AR.CallAdm _ _
    | AR.Label _ _ _ _
    | AR.Local _ _ _ _ _
    | AR.Malloc _ _ _
    | AR.Free => mthrow (err "unexpected admin instr")
    end.
End BoxPolymorphicIR.
