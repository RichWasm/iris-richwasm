Require Wasm.datatypes.

Require Import RichWasm.syntax.

Module W := Wasm.datatypes.

Inductive error :=
  | EWrongTypeAnn
  | ECaseNotOnVariant
  | EIndexOutOfBounds (index : nat)
  | EUnboundQual
  | ETodo.

Record store_runtime :=
  { sr_mem_gc : W.memaddr;
    sr_mem_mm : W.memaddr }.

Record module_runtime :=
  { mr_mem_gc : W.memidx;
    mr_mem_mm : W.memidx;
    mr_func_alloc_mm : W.funcidx;
    mr_func_alloc_gc : W.funcidx;
    mr_func_free : W.funcidx;
    mr_func_registerroot : W.funcidx;
    mr_func_duproot : W.funcidx;
    mr_func_unregisterroot : W.funcidx;
    mr_global_table_offset : W.globalidx;
    mr_table : W.tableidx }.

Record module_env :=
  { me_globals : list type;
    me_runtime : module_runtime }.

Record function_env :=
  { fe_return_type : list type;
    fe_wlocal_offset : nat }.

Inductive VarScope :=
  | VSGlobal
  | VSLocal.

Definition funcimm (ix : W.funcidx) : W.immediate :=
  let '(W.Mk_funcidx i) := ix in i.

Definition tableimm (ix : W.tableidx) : W.immediate :=
  let '(W.Mk_tableidx i) := ix in i.

Definition memimm (ix : W.memidx) : W.immediate :=
  let '(W.Mk_memidx i) := ix in i.

Definition localimm (ix : W.localidx) : W.immediate :=
  let '(W.Mk_localidx i) := ix in i.

Definition globalimm (ix : W.globalidx) : W.immediate :=
  let '(W.Mk_globalidx i) := ix in i.

Definition scope_get_set (scope : VarScope) :
  (W.immediate -> W.basic_instruction) *
  (W.immediate -> W.basic_instruction) :=
  match scope with
  | VSGlobal => (W.BI_get_global, W.BI_set_global)
  | VSLocal => (W.BI_get_local, W.BI_set_local)
  end.
