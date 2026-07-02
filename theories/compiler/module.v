From Stdlib Require Import String.

Require Import stdpp.list.

Require Import RichWasm.wasm.numerics.

From RichWasm Require Import layout syntax util.
From RichWasm.compiler Require Import prelude codegen instruction.

Definition rt_types : list W.function_type :=
  [
    W.Tf [W.T_i32; W.T_i32] [];
    W.Tf [W.T_i32] [W.T_i32];
    W.Tf [W.T_i32; W.T_i32; W.T_i32] [];
    W.Tf [W.T_i32] [];
    W.Tf [] []
  ].

Definition rt_import (name : string) (id : W.import_desc) : W.module_import :=
  {| W.imp_module := String.list_byte_of_string "richwasm";
     W.imp_name := String.list_byte_of_string name;
     W.imp_desc := id |}.

Definition rt_imports : list W.module_import :=
  [
    rt_import "mmmem" (W.ID_mem (W.Build_limits 0 None));
    rt_import "gcmem" (W.ID_mem (W.Build_limits 0 None));
    rt_import "tablenext" (W.ID_global (W.Build_global_type W.MUT_mut W.T_i32));
    rt_import "tableset" (W.ID_func 0);
    rt_import "mmalloc" (W.ID_func 1);
    rt_import "gcalloc" (W.ID_func 1);
    rt_import "setflag" (W.ID_func 2);
    rt_import "free" (W.ID_func 3);
    rt_import "registerroot" (W.ID_func 1);
    rt_import "unregisterroot" (W.ID_func 3);
    rt_import "table" (W.ID_table (W.Build_table_type (W.Build_limits 0 None) W.ELT_funcref))
  ].

Definition rt_globals : list W.module_glob :=
  [
    {|
      W.modglob_type := W.Build_global_type W.MUT_mut W.T_i32;
      W.modglob_init := [W.BI_const (W.VAL_int32 (Wasm_int.int_zero i32m))]
    |}
  ].

Definition mr : module_runtime :=
  {|
    mr_mmmem := W.Mk_memidx 0;
    mr_gcmem := W.Mk_memidx 1;
    mr_func_mmalloc := W.Mk_funcidx 1;
    mr_func_gcalloc := W.Mk_funcidx 2;
    mr_func_setflag := W.Mk_funcidx 3;
    mr_func_free := W.Mk_funcidx 4;
    mr_func_registerroot := W.Mk_funcidx 5;
    mr_func_unregisterroot := W.Mk_funcidx 6;
    mr_func_user := W.Mk_funcidx 7;
    mr_global_table_off := W.Mk_globalidx 1
  |}.

Definition insert_type (wt : list W.function_type) (tf : W.function_type) :
  option W.function_type * nat :=
  match list_find (W.function_type_eqb tf) wt with
  | Some (i, _) => (None, i)
  | None => (Some tf, length wt)
  end.

Definition user_import (wt : list W.function_type) (ϕ : function_type) :
  option (option W.function_type * W.module_import) :=
  tf ← translate_func_type [] ϕ;
  let '(wt', i) := insert_type wt tf in
  Some (wt', {| W.imp_module := []; W.imp_name := []; W.imp_desc := W.ID_func i |}).

Definition user_imports (wt : list W.function_type) (ϕs : list function_type) :
  option (list W.function_type * list W.module_import) :=
  let f '(wt', imps) ϕ :=
    '(wt'', imp) ← user_import (wt ++ wt') ϕ;
    Some (wt' ++ option_list wt'', imps ++ [imp])
  in
  foldlM f ([], []) ϕs.

Definition user_export (func_user : nat) (exp : module_export) : W.module_export :=
  {|
    W.modexp_name := list_byte_of_string exp.(me_name);
    W.modexp_desc := W.MED_func (W.Mk_funcidx (func_user + exp.(me_desc)))
  |}.

Definition compile_function (wt : list W.function_type) (mf : module_function) :
  error + list W.function_type * W.module_func :=
  tf ← try_option EFail (translate_func_type [] mf.(mf_type));
  let '(wt', tid) := insert_type wt tf in
  fe ← try_option EFail (fe_of_module_func mf);
  ls ← try_option EFail (mapM (eval_rep EmptyEnv) mf.(mf_locals));
  '((), wt'', wl, es) ← run_codegen (compile_instrs mr fe mf.(mf_body)) (wt ++ option_list wt') [];
  let ls' := flat_map (map translate_arep) ls ++ wl in
  inr (option_list wt' ++ wt'', W.Build_module_func (W.Mk_typeidx tid) ls' es).

Definition compile_functions (wt : list W.function_type) (mfs : list module_function) :
  error + list W.function_type * list W.module_func :=
  let f '(wt', defs) mf :=
    '(wt'', def) ← compile_function (wt ++ wt') mf;
    inr (wt' ++ wt'', defs ++ [def])
  in
  foldlM f ([], []) mfs.

Definition table_alloc (tablenext table_off : W.globalidx) (n : nat) : W.expr :=
  [
    (* Save the next index. *)
    W.BI_get_global (globalimm tablenext);
    W.BI_set_global (globalimm table_off);
    (* Increment the next index. *)
    W.BI_get_global (globalimm table_off);
    W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat n)));
    W.BI_binop W.T_i32 (W.Binop_i W.BOI_add);
    W.BI_set_global (globalimm tablenext)
  ].

Definition table_set (table_off : W.globalidx) (tableset : W.funcidx) (i fid : nat) : W.expr :=
  [
    W.BI_get_global (globalimm table_off);
    W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat i)));
    W.BI_binop W.T_i32 (W.Binop_i W.BOI_add);
    W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat fid)));
    W.BI_call (funcimm tableset)
  ].

(* HACK: Since we can't use ref.func, we must export our functions for the host to add to the table.
 *)
Definition table_export (i : nat) : W.module_export :=
  let idx := funcimm mr.(mr_func_user) + i in
  let name := list_byte_of_string ("__rw_table_func_" ++ pretty.pretty idx) in
  W.Build_module_export name (W.MED_func (W.Mk_funcidx idx)).

Definition table_start (tab : list nat) : W.module_func :=
  let es1 := table_alloc (W.Mk_globalidx 0) mr.(mr_global_table_off) (length tab) in
  let table_set i fid :=
    table_set mr.(mr_global_table_off) (W.Mk_funcidx 0) i (funcimm mr.(mr_func_user) + fid)
  in
  let es2 := concat (imap table_set tab) in
  W.Build_module_func (W.Mk_typeidx 4) [] (es1 ++ es2).

Definition compile_module (m : module) : error + W.module :=
  '(imp_types, imps) ← try_option EFail (user_imports rt_types m.(m_imports));
  '(def_types, defs) ← compile_functions (rt_types ++ imp_types) m.(m_functions);
  let user_exps := map (user_export (funcimm mr.(mr_func_user))) m.(m_exports) in
  let table_exps := map table_export m.(m_table) in
  let start_func := table_start m.(m_table) in
  let start_idx := W.Mk_funcidx (funcimm mr.(mr_func_user) + length imps + length defs) in
  inr {|
      W.mod_types := rt_types ++ imp_types ++ def_types;
      W.mod_funcs := defs ++ [start_func];
      W.mod_tables := [];
      W.mod_mems := [];
      W.mod_globals := rt_globals;
      W.mod_elem := [];
      W.mod_data := [];
      W.mod_start := Some (W.Build_module_start start_idx);
      W.mod_imports := rt_imports ++ imps;
      W.mod_exports := user_exps ++ table_exps
    |}.
