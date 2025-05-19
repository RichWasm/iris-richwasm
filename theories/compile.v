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
Require Import stdpp.list.

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

Definition compile_num (num_type : rwasm.NumType) (num : nat) : wasm.value :=
  match num_type with
  | rwasm.Int _ rwasm.i32 => 
    wasm.VAL_int32 (Wasm_int.int_of_Z numerics.i32m (Z.of_nat num))
  | rwasm.Int _ rwasm.i64 => 
    wasm.VAL_int64 (Wasm_int.int_of_Z numerics.i64m (Z.of_nat num))
  (* is the signed converter the right thing to use here? *)
  | rwasm.Float rwasm.f32 =>
    wasm.VAL_float32 
      ((Wasm_float.float_convert_si32
        numerics.f32m (Wasm_int.int_of_Z numerics.i32m (Z.of_nat num))))
  | rwasm.Float rwasm.f64 =>
    wasm.VAL_float64
      ((Wasm_float.float_convert_si64
        numerics.f64m (Wasm_int.int_of_Z numerics.i64m (Z.of_nat num))))
  end.

Fixpoint compile_value (value : rwasm.Value) : option wasm.value :=
  match value with 
  | rwasm.NumConst num_type num => Some (compile_num num_type num)
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


Fixpoint option_of_list {A} (l : list (option A)) : option (list A) :=
  match l with
  | [] => Some []
  | None :: _ => None
  | Some x :: xs =>
    rest ← option_of_list xs;
    mret (x :: rest)
  end.

Fixpoint list_flatten {A} (l : list (list A)) : list A :=
  match l with
  | [] => []
  | x :: xs => x ++ (list_flatten xs)
  end.

Fixpoint compile_instr (instr: rwasm.Instruction) : option (list wasm.basic_instruction) :=
  match instr with
  | rwasm.Val x => option_map (fun y => [wasm.BI_const y]) (compile_value x)
  | rwasm.Ne x => None
  | rwasm.Unreachable => Some [wasm.BI_unreachable]
  | rwasm.Nop => Some [wasm.BI_nop]
  | rwasm.Drop => Some [wasm.BI_drop]
  | rwasm.Select => Some [wasm.BI_select]
  | rwasm.Block arrow _ i =>
      ft ← compile_arrow_type arrow;
      i' ← option_of_list (map compile_instr i);
      mret [wasm.BI_block ft (list_flatten i')]
  | rwasm.Loop arrow i =>
      ft ← compile_arrow_type arrow;
      i' ← option_of_list (map compile_instr i);
      mret [wasm.BI_block ft (list_flatten i')]
  | rwasm.ITE arrow _ t e =>
    ft ← compile_arrow_type arrow;
    t' ← option_of_list (map compile_instr t);
    e' ← option_of_list (map compile_instr e);
    mret [wasm.BI_if ft (list_flatten t') (list_flatten e')]
  | rwasm.Br x => Some [wasm.BI_br x]
  | rwasm.Br_if x => Some [wasm.BI_br_if x]
  | rwasm.Br_table x x0 => Some [wasm.BI_br_table x x0]
  | rwasm.Ret => Some [wasm.BI_return]
  | rwasm.Get_local x x0 => Some [wasm.BI_get_local x]
  | rwasm.Set_local x => Some [wasm.BI_set_local x]
  | rwasm.Tee_local x => Some [wasm.BI_tee_local x]
  | rwasm.Get_global x => Some [wasm.BI_get_global x]
  | rwasm.Set_global x => Some [wasm.BI_set_global x]
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
