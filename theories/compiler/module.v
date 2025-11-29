From Stdlib Require Import String.
Require Import Stdlib.ZArith.BinInt.

Require Import mathcomp.boot.seq.

Require Import stdpp.list.

Require Import RecordUpdate.RecordUpdate.

From ExtLib.Structures Require Import MonadTrans Monoid.

Require Wasm.datatypes.
Require Import Wasm.numerics.

From RichWasm Require Import layout syntax typing util.
From RichWasm.compiler Require Import prelude accum codegen instruction.

Module W := Wasm.datatypes.

Definition modgen : Type -> Type := accumT W.module (sum error).

Definition run_modgen {A : Type} : modgen A -> W.module -> error + A * W.module :=
  runAccumT.

Definition mod_empty : W.module :=
  {| W.mod_types := [];
     W.mod_funcs := [];
     W.mod_tables := [];
     W.mod_mems := [];
     W.mod_globals := [];
     W.mod_elem := [];
     W.mod_data := [];
     W.mod_start := None;
     W.mod_imports := [];
     W.mod_exports := [] |}.

Definition mod_app (m1 m2 : W.module) : W.module :=
  {| W.mod_types := monoid_plus m1.(W.mod_types) m2.(W.mod_types);
     W.mod_funcs := monoid_plus m1.(W.mod_funcs) m2.(W.mod_funcs);
     W.mod_tables := monoid_plus m1.(W.mod_tables) m2.(W.mod_tables);
     W.mod_mems := monoid_plus m1.(W.mod_mems) m2.(W.mod_mems);
     W.mod_globals := monoid_plus m1.(W.mod_globals) m2.(W.mod_globals);
     W.mod_elem := monoid_plus m1.(W.mod_elem) m2.(W.mod_elem);
     W.mod_data := monoid_plus m1.(W.mod_data) m2.(W.mod_data);
     W.mod_start := option_last m1.(W.mod_start) m2.(W.mod_start);
     W.mod_imports := monoid_plus m1.(W.mod_imports) m2.(W.mod_imports);
     W.mod_exports := monoid_plus m1.(W.mod_exports) m2.(W.mod_exports) |}.

Instance Monoid_module : Monoid W.module :=
  {| monoid_unit := mod_empty;
     monoid_plus := mod_app |}.

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

Definition next_memidx_import : modgen W.memidx :=
  gets (W.Mk_memidx ∘ length ∘ W.mod_mems).

Definition next_globalidx_import : modgen W.globalidx :=
  gets (W.Mk_globalidx ∘ count_global_imports).

Definition next_globalidx : modgen W.globalidx :=
  gets (fun m => W.Mk_globalidx (count_global_imports m + length m.(W.mod_globals))).

Definition next_funcidx_import : modgen W.funcidx :=
  gets (W.Mk_funcidx ∘ count_func_imports).

Definition next_funcidx : modgen W.funcidx :=
  gets (fun m => W.Mk_funcidx (count_func_imports m + length m.(W.mod_funcs))).

Definition next_tableidx_import : modgen W.tableidx :=
  gets (W.Mk_tableidx ∘ length ∘ W.mod_tables).

Definition add_type (tf : W.function_type) : modgen W.typeidx :=
  tfs ← gets W.mod_types;
  match list_find (W.function_type_eqb tf) tfs with
  | Some (i, _) => mret (W.Mk_typeidx i)
  | None => acc (mod_empty <| W.mod_types := [tf] |>);;
           mret (W.Mk_typeidx (length tfs))
  end.

Definition add_types : list W.function_type -> modgen unit := mapM_ add_type.

Definition add_import (imp : W.module_import) : modgen unit :=
  acc (mod_empty <| W.mod_imports := [imp] |>).

Definition rt_import (name : string) (id : W.import_desc) : W.module_import :=
  {| W.imp_module := String.list_byte_of_string "richwasm";
     W.imp_name := String.list_byte_of_string name;
     W.imp_desc := id |}.

Definition add_rt_mem_import (name : string) (tm : W.memory_type) : modgen W.memidx :=
  mid ← next_memidx_import;
  add_import (rt_import name (W.ID_mem tm));;
  mret mid.

Definition add_rt_global_import (name : string) (tg : W.global_type) : modgen W.globalidx :=
  gid ← next_globalidx_import;
  add_import (rt_import name (W.ID_global tg));;
  mret gid.

Definition add_global (mg : W.module_glob) : modgen W.globalidx :=
  gid ← next_globalidx;
  acc (mod_empty <| W.mod_globals := [mg] |>);;
  mret gid.

Definition add_rt_func_import (name : string) (tf : W.function_type) : modgen W.funcidx :=
  tid ← add_type tf;
  fid ← next_funcidx_import;
  add_import (rt_import name (W.ID_func (typeimm tid)));;
  mret fid.

Definition add_func_import (tf : W.function_type) : modgen W.funcidx :=
  tid ← add_type tf;
  fid ← next_funcidx_import;
  add_import (W.Build_module_import [] [] (W.ID_func (typeimm tid)));;
  mret fid.

Definition add_func (mf : W.module_func) : modgen W.funcidx :=
  fid ← next_funcidx;
  acc (mod_empty <| W.mod_funcs := [mf] |>);;
  mret fid.

Definition add_rt_table_import (name : string) (tt : W.table_type) : modgen W.tableidx :=
  tid ← next_tableidx_import;
  add_import (rt_import name (W.ID_table tt));;
  mret tid.

Definition set_start (ms : W.module_start) : modgen unit :=
  acc (mod_empty <| W.mod_start := Some ms |>).

Definition add_export (ex : W.module_export) : modgen unit :=
  acc (mod_empty <| W.mod_exports := [ex] |>).

Definition table_alloc (gid_tablenext gid_table_off : W.globalidx) (n : nat) : W.expr :=
  [
    (* Save the next index. *)
    W.BI_get_global (globalimm gid_tablenext);
    W.BI_set_global (globalimm gid_table_off);
    (* Increment the next index. *)
    W.BI_get_global (globalimm gid_table_off);
    W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat n)));
    W.BI_binop W.T_i32 (W.Binop_i W.BOI_add);
    W.BI_set_global (globalimm gid_tablenext)
  ].

Definition call_table_set (gid_table_off : W.globalidx) (fid_tableset : W.funcidx) (ix fid : nat) :
  W.expr :=
  [
    W.BI_get_global (globalimm gid_table_off);
    W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat ix)));
    W.BI_binop W.T_i32 (W.Binop_i W.BOI_add);
    W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat fid)));
    W.BI_call (funcimm fid_tableset)
  ].

Definition compile_func_import (ϕ : function_type) : modgen W.funcidx :=
  try_option EFail (translate_func_type [] ϕ) ≫= add_func_import.

Definition compile_func (mr : module_runtime) (mf : module_function) : modgen W.funcidx :=
  tf ← try_option EFail (translate_func_type [] mf.(mf_type));
  tid ← add_type tf;
  fe ← try_option EFail (fe_of_module_func mf);
  wt ← gets W.mod_types;
  '((), wt', wl, body) ← lift (run_codegen (compile_instrs mr fe mf.(mf_body)) wt []);
  add_types wt';;
  ls ← try_option EFail (mapM (eval_rep EmptyEnv) mf.(mf_locals));
  let ls' := flat_map (map translate_arep) ls ++ wl in
  add_func (W.Build_module_func tid ls' body).

Definition compile_table
  (gid_tablenext gid_table_off : W.globalidx) (fid_user fid_tableset : W.funcidx) (tab : list nat) :
  modgen W.funcidx :=
  tid ← add_type (W.Tf [] []);
  let es1 := table_alloc gid_tablenext gid_table_off (length tab) in
  let table_set i fid := call_table_set gid_table_off fid_tableset i (funcimm fid_user + fid) in
  let es2 := flatten (imap table_set tab) in
  add_func (W.Build_module_func tid [] (es1 ++ es2)).

Definition compile_export (gid_user : W.globalidx) (fid_user : W.funcidx) (export : module_export) : modgen unit :=
  let ed := W.MED_func (W.Mk_funcidx (funcimm fid_user + (me_desc export))) in
  let name := list_byte_of_string (me_name export) in
  add_export (W.Build_module_export name ed).

Definition compile_module (m : module) : modgen unit :=
  (* Runtime Imports *)
  mid_mmmem ← add_rt_mem_import "mmmem" (W.Build_limits 0 None);
  mid_gcmem ← add_rt_mem_import "gcmem" (W.Build_limits 0 None);
  gid_tablenext ← add_rt_global_import "tablenext" (W.Build_global_type W.MUT_mut W.T_i32);
  fid_tableset ← add_rt_func_import "tableset" (W.Tf [W.T_i32; W.T_i32] []);
  fid_mmalloc ← add_rt_func_import "mmalloc" (W.Tf [W.T_i32] [W.T_i32]);
  fid_gcalloc ← add_rt_func_import "gcalloc" (W.Tf [W.T_i32] [W.T_i32]);
  fid_setflag ← add_rt_func_import "setflag" (W.Tf [W.T_i32; W.T_i32; W.T_i32] []);
  fid_free ← add_rt_func_import "free" (W.Tf [W.T_i32] []);
  fid_registerroot ← add_rt_func_import "registerroot" (W.Tf [W.T_i32] [W.T_i32]);
  fid_unregisterroot ← add_rt_func_import "unregisterroot" (W.Tf [W.T_i32] []);
  tid_table ← add_rt_table_import "table" (W.Build_table_type (W.Build_limits 0 None) W.ELT_funcref);

  (* Save the offsets of user imports and definitions. After this point:
     - No more runtime imports.
     - Runtime function definitions only after all user functions (imports and definitions).
     This creates a "sandwich," with runtime imports at the beginning, user imports and definitions
     in the middle, and runtime definitions at the end. *)
  gid_user ← next_globalidx_import;
  fid_user ← next_funcidx_import;

  (* User Imports *)
  mapM_ compile_func_import m.(m_imports);;

  (* Runtime Global Defs *)
  let mg_table_off :=
    {| W.modglob_type := W.Build_global_type W.MUT_mut W.T_i32;
       W.modglob_init := [W.BI_const (W.VAL_int32 (Wasm_int.int_zero i32m))] |}
  in
  gid_table_off ← add_global mg_table_off;

  (* User Function Defs *)
  let mr :=
    {| mr_mmmem := mid_mmmem;
       mr_gcmem := mid_gcmem;
       mr_func_mmalloc := fid_mmalloc;
       mr_func_gcalloc := fid_gcalloc;
       mr_func_setflag := fid_setflag;
       mr_func_free := fid_free;
       mr_func_registerroot := fid_registerroot;
       mr_func_unregisterroot := fid_unregisterroot;
       mr_func_user := fid_user;
       mr_table := tid_table;
       mr_global_table_off := gid_table_off;
       mr_global_user := gid_user |}
  in
  mapM_ (compile_func mr) m.(m_functions);;

  (* User Exports *)
  mapM_ (compile_export gid_user fid_user) m.(m_exports);;

  (* Runtime Function Defs *)
  fid_table_init ← compile_table gid_tablenext gid_table_off fid_user fid_tableset m.(m_table);
  set_start (W.Build_module_start fid_table_init).
