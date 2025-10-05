From Stdlib Require Import String.
Require Import Stdlib.ZArith.BinInt.

Require Import mathcomp.ssreflect.seq.

Require Import stdpp.list.

Require Import RecordUpdate.RecordUpdate.

Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Structures.Monads.

Require Wasm.datatypes.
Require Import Wasm.numerics.

From RichWasm Require Import layout syntax typing util.
From RichWasm.compiler Require Import prelude codegen instruction.

Module W := Wasm.datatypes.

Definition modgen := stateT W.module (sum error).

Existing Instance Monad_stateT.

Definition get_id_global (imd : W.import_desc) : option W.global_type :=
  match imd with
  | W.ID_global tg => Some tg
  | _ => None
  end.

Definition get_id_func (imd : W.import_desc) : option nat :=
  match imd with
  | W.ID_func i => Some i
  | _ => None
  end.

Definition count_global_imports (m : W.module) : nat :=
  length (pmap (get_id_global ∘ W.imp_desc) m.(W.mod_imports)).

Definition count_func_imports (m : W.module) : nat :=
  length (pmap (get_id_func ∘ W.imp_desc) m.(W.mod_imports)).

Definition add_type (tf : W.function_type) : modgen W.typeidx :=
  m ← get;
  put (m <| W.mod_types ::= flip app [tf] |>);;
  ret (W.Mk_typeidx (length m.(W.mod_types))).

Definition add_import (imp : W.module_import) : modgen unit :=
  m ← get;
  put (m <| W.mod_imports ::= flip app [imp] |>).

Definition rt_import (name : string) (id : W.import_desc) : W.module_import :=
  {| W.imp_module := String.list_byte_of_string "richwasm";
     W.imp_name := String.list_byte_of_string name;
     W.imp_desc := id |}.

Definition add_rt_mem_import (name : string) (tm : W.memory_type) : modgen W.memidx :=
  m ← get;
  add_import (rt_import name (W.ID_mem tm));;
  ret (W.Mk_memidx (length m.(W.mod_mems))).

Definition add_rt_global_import (name : string) (tg : W.global_type) : modgen W.globalidx :=
  m ← get;
  add_import (rt_import name (W.ID_global tg));;
  ret (W.Mk_globalidx (count_global_imports m)).

Definition add_global_import (tg : W.global_type) : modgen W.globalidx :=
  m ← get;
  add_import (W.Build_module_import [] [] (W.ID_global tg));;
  ret (W.Mk_globalidx (count_global_imports m)).

Definition add_global (mg : W.module_glob) : modgen W.globalidx :=
  m ← get;
  put (m <| W.mod_globals ::= flip app [mg] |>);;
  ret (W.Mk_globalidx (count_global_imports m + length m.(W.mod_globals))).

Definition add_rt_func_import (name : string) (tf : W.function_type) : modgen W.funcidx :=
  m ← get;
  tid ← add_type tf;
  add_import (rt_import name (W.ID_func (typeimm tid)));;
  ret (W.Mk_funcidx (count_func_imports m)).

Definition add_func_import (tf : W.function_type) : modgen W.funcidx :=
  m ← get;
  tid ← add_type tf;
  add_import (W.Build_module_import [] [] (W.ID_func (typeimm tid)));;
  ret (W.Mk_funcidx (count_func_imports m)).

Definition add_func (mf : W.module_func) : modgen W.funcidx :=
  m ← get;
  put (m <| W.mod_funcs ::= flip app [mf] |>);;
  ret (W.Mk_funcidx (count_func_imports m + length m.(W.mod_funcs))).

Definition add_rt_table_import (name : string) (tt : W.table_type) : modgen W.tableidx :=
  m ← get;
  add_import (rt_import name (W.ID_table tt));;
  ret (W.Mk_tableidx (length m.(W.mod_tables))).

Definition set_start (ms : option W.module_start) : modgen unit :=
  m ← get;
  put (m <| W.mod_start := ms |>).

Definition table_alloc (gid_table_next gid_table_off : W.globalidx) (n : nat) : W.expr :=
  [
    (* Save the next index. *)
    W.BI_get_global (globalimm gid_table_next);
    W.BI_set_global (globalimm gid_table_off);
    (* Increment the next index. *)
    W.BI_get_global (globalimm gid_table_off);
    W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat n)));
    W.BI_binop W.T_i32 (W.Binop_i W.BOI_add);
    W.BI_set_global (globalimm gid_table_next)
  ].

Definition call_table_set (gid_table_off : W.globalidx) (fid_table_set : W.funcidx) (ix fid : nat) :
  W.expr :=
  [
    W.BI_get_global (globalimm gid_table_off);
    W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat ix)));
    W.BI_binop W.T_i32 (W.Binop_i W.BOI_add);
    W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat fid)));
    W.BI_call (funcimm fid_table_set)
  ].

Definition compile_func_import (ϕ : function_type) : modgen W.funcidx :=
  try_option EFail (translate_func_type [] ϕ) ≫= add_func_import.

Definition compile_func (me : module_env) (mf : module_function) : modgen W.funcidx :=
  tf ← try_option EFail (translate_func_type [] mf.(mf_type));
  tid ← add_type tf;
  fe ← try_option EFail (fe_of_module_func mf);
  '((), wl, body) ← lift (run_codegen (compile_instrs me fe mf.(mf_body)) []);
  locals ← try_option EFail (mapM eval_rep mf.(mf_locals));
  let locals' := flat_map (map translate_prim_rep) locals ++ wl in
  add_func (W.Build_module_func tid locals' body).

Definition compile_table
  (gid_table_next gid_table_off : W.globalidx) (fid_table_set : W.funcidx) (tab : list nat) :
  modgen W.funcidx :=
  tid ← add_type (W.Tf [] []);
  let body :=
    table_alloc gid_table_next gid_table_off (length tab) ++
      flatten (imap (call_table_set gid_table_off fid_table_set) tab)
  in
  add_func (W.Build_module_func tid [] body).

Definition compile_module (m : module) : modgen unit :=
  (* Runtime Imports *)
  mid_mem_mm ← add_rt_mem_import "mem_mm" (W.Build_limits 0 None);
  mid_mem_gc ← add_rt_mem_import "mem_gc" (W.Build_limits 0 None);
  gid_table_next ← add_rt_global_import "table_next" (W.Build_global_type W.MUT_mut W.T_i32);
  fid_table_set ← add_rt_func_import "table_set" (W.Tf [W.T_i32; W.T_i32] []);
  fid_alloc_mm ← add_rt_func_import "alloc_mm" (W.Tf [W.T_i32] [W.T_i32]);
  fid_alloc_gc ← add_rt_func_import "alloc_gc" (W.Tf [W.T_i32; W.T_i64] [W.T_i32]);
  fid_free ← add_rt_func_import "free" (W.Tf [W.T_i32] []);
  fid_registerroot ← add_rt_func_import "registerroot" (W.Tf [W.T_i32] [W.T_i32]);
  fid_unregisterroot ← add_rt_func_import "unregisterroot" (W.Tf [W.T_i32] []);
  tid_table ← add_rt_table_import "table" (W.Build_table_type (W.Build_limits 0 None) W.ELT_funcref);

  (* User Imports *)
  mapM_ compile_func_import m.(m_funcs_import);;
  (* TODO: globals_import *)

  (* Runtime Definitions *)
  let mg_table_off :=
    {| W.modglob_type := W.Build_global_type W.MUT_mut W.T_i32;
       W.modglob_init := [W.BI_const (W.VAL_int32 (Wasm_int.int_zero i32m))] |}
  in
  gid_table_off ← add_global mg_table_off;
  fid_table_init ← compile_table gid_table_next gid_table_off fid_table_set m.(m_table);
  set_start (Some (W.Build_module_start fid_table_init));;

  (* User Definitions *)
  (* TODO: globals *)
  let mr :=
    {| mr_mem_mm := mid_mem_mm;
       mr_mem_gc := mid_mem_gc;
       mr_func_alloc_mm := fid_alloc_mm;
       mr_func_alloc_gc := fid_alloc_gc;
       mr_func_free := fid_free;
       mr_func_registerroot := fid_registerroot;
       mr_func_unregisterroot := fid_unregisterroot;
       mr_func_user := W.Mk_funcidx 0; (* TODO *)
       mr_table := tid_table;
       mr_global_table_off := gid_table_off;
       mr_global_user := W.Mk_globalidx 0 (* TODO *) |}
  in
  let me := me_of_module m mr in
  mapM_ (compile_func me) m.(m_funcs);;

  (* TODO: exports *)
  ret tt.
