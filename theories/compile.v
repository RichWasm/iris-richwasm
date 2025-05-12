From Coq Require Import List.
Require Import stdpp.base.
Require Import stdpp.option.
Import ListNotations.
From RWasm Require term.
From Wasm Require datatypes.
Require Import Wasm.numerics.
Require Import BinNat.

Module rwasm := term.
Module wasm := datatypes.
Print wasm.function_type .
Print wasm.result_type .
Require Import stdpp.list.
Search (list (_ _) -> _ (list _)).

Fixpoint compile_typ (typ: rwasm.Typ) : option wasm.value_type :=
  match typ with
  | rwasm.Num x => None
  | rwasm.TVar x => None
  | rwasm.Unit => None
  | rwasm.ProdT x => None
  | rwasm.CoderefT x => None
  | rwasm.Rec _ typ => compile_typ typ
  | rwasm.PtrT x => None
  | rwasm.ExLoc x => None
  | rwasm.OwnR x => None
  | rwasm.CapT x x0 x1 => None
  | rwasm.RefT x x0 x1 => None
  end
with compile_heap_type (typ: rwasm.HeapType) : option unit :=
       match typ with
       | rwasm.VariantType typs => None
       | rwasm.StructType fields => None
       | rwasm.ArrayType elt_typ => None
       | rwasm.Ex sz qual typ => None
       end
with compile_arrow_type (typ: rwasm.ArrowType) : option wasm.function_type :=
       match typ with
       | rwasm.Arrow tys1 tys2 =>
           tys1' ← mapM compile_typ tys1;
           tys2' ← mapM compile_typ tys2;
           mret (wasm.Tf tys1' tys2')
       end
with compile_fun_type (typ: rwasm.FunType) : option unit := None. (* What to do about generics? *)

Definition compile_num (num_type : rwasm.NumType) (num : nat) : option wasm.value :=
  match (num_type, num) with
  | (rwasm.Int rwasm.S rwasm.i32, n) => (* numerics.int *) None
  | (rwasm.Int rwasm.S rwasm.i64, n) => None
  | (rwasm.Int rwasm.U int_type, n) => None
  | (rwasm.Float float_type, n) => None
  end.
  
Fixpoint compile_value (value : rwasm.Value) : option wasm.value :=
  match value with 
  | rwasm.NumConst num_type num => compile_num num_type num
  | rwasm.Tt => None
  | rwasm.Coderef module_idx table_idx idxs => None
  | rwasm.Fold val => None
  | rwasm.Prod vals => None
  | rwasm.Ref loc => None
  | rwasm.PtrV loc => None
  | rwasm.Cap => None
  | rwasm.Own => None
  | rwasm.Mempack loc val => None
  end.

Fixpoint compile_instr (instr: rwasm.Instruction) : option (list wasm.basic_instruction) :=
  match instr with
  | rwasm.Val x => None
  | rwasm.Ne x => None
  | rwasm.Unreachable => None
  | rwasm.Nop => None
  | rwasm.Drop => None
  | rwasm.Select => None
  | rwasm.Block x x0 x1 => None
  | rwasm.Loop x x0 => None
  | rwasm.ITE x x0 x1 x2 => None
  | rwasm.Br x => None
  | rwasm.Br_if x => None
  | rwasm.Br_table x x0 => None
  | rwasm.Ret => None
  | rwasm.Get_local x x0 => None
  | rwasm.Set_local x => None
  | rwasm.Tee_local x => None
  | rwasm.Get_global x => None
  | rwasm.Set_global x => None
  | rwasm.CoderefI x => None
  | rwasm.Inst x => None
  | rwasm.Call_indirect => None
  | rwasm.Call x x0 => None
  | rwasm.RecFold x => None
  | rwasm.RecUnfold => None
  | rwasm.Group x x0 => None
  | rwasm.Ungroup => None
  | rwasm.CapSplit => None
  | rwasm.CapJoin => None
  | rwasm.RefDemote => None
  | rwasm.MemPack x => None
  | rwasm.MemUnpack x x0 x1 => None
  | rwasm.StructMalloc x x0 => None
  | rwasm.StructFree => None
  | rwasm.StructGet x => None
  | rwasm.StructSet x => None
  | rwasm.StructSwap x => None
  | rwasm.VariantMalloc x x0 x1 => None
  | rwasm.VariantCase x x0 x1 x2 x3 => None
  | rwasm.ArrayMalloc x => None
  | rwasm.ArrayGet => None
  | rwasm.ArraySet => None
  | rwasm.ArrayFree => None
  | rwasm.ExistPack x x0 x1 => None
  | rwasm.ExistUnpack x x0 x1 x2 x3 => None
  | rwasm.RefSplit => None
  | rwasm.RefJoin => None
  | rwasm.Qualify x => None
  | rwasm.Trap => None
  | rwasm.CallAdm x x0 => None
  | rwasm.Label x x0 x1 x2 => None
  | rwasm.Local x x0 x1 x2 x3 => None
  | rwasm.Malloc x x0 x1 => None
  | rwasm.Free => None
  end.
(* ... *)


Definition compile_fun_type_idx (fun_type : rwasm.FunType) : wasm.typeidx.
Admitted.


Fixpoint compile_module (module : rwasm.module) : option wasm.module :=
  let '(funcs, globs, table) := module return option wasm.module in
  Some {|
    wasm.mod_types := []; (* TODO *)
    wasm.mod_funcs := []; (* TODO *)
    wasm.mod_tables := []; (* TODO *)
    wasm.mod_mems := []; (* TODO *)
    wasm.mod_globals := []; (* TODO *)
    wasm.mod_elem := []; (* TODO *)
    wasm.mod_data := []; (* TODO *)
    wasm.mod_start := None; (* TODO *)
    wasm.mod_imports := []; (* TODO *)
    wasm.mod_exports := [] (* TODO *)
  |}

(* TODO: modfunc_type expects a typeidx while rwasm does this inline *)
with compile_func (func : rwasm.Func) : option wasm.module_func := 
  match func with 
  | rwasm.Fun exports fun_type sizes intrs =>
    Some {|
      wasm.modfunc_type := compile_fun_type_idx fun_type;
      wasm.modfunc_locals := []; (* TODO *)
      wasm.modfunc_body := []; (* TODO *)
    |}
  end

with compile_glob (glob : rwasm.Glob) : option wasm.module_glob
with compile_table (table : rwasm.Table) : option wasm.module_table.
Admitted.
