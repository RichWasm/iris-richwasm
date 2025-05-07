From Coq Require Import List.
Import ListNotations.
From RWasm Require term.
From Wasm Require datatypes.
Require Import BinNat.

Module rwasm := term.
Module wasm := datatypes.

Fixpoint compile_num (num_type : rwasm.NumType) (num : nat) : wasm.value.
  (* match (num_type, num) with
  | () => VAL_int32 (Z.of_nat )
  end. *)
Admitted.
  
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

(* ... *)


Definition compile_fun_type (fun_type : rwasm.FunType) : wasm.typeidx.
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
      wasm.modfunc_type := compile_fun_type fun_type;
      wasm.modfunc_locals := []; (* TODO *)
      wasm.modfunc_body := []; (* TODO *)
    |}
  end

with compile_glob (glob : rwasm.Glob) : option wasm.module_glob
with compile_table (table : rwasm.Table) : option wasm.module_table.

