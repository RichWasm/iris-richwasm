Require Wasm.datatypes.

Require RichWasm.term.

Module R := RichWasm.term.
Module W := Wasm.datatypes.

Inductive error :=
  | EWrongTypeAnn
  | ECaseNotOnVariant
  | EIndexOutOfBounds (index : nat)
  | ETodo.

Record store_runtime :=
  { sr_mem_gc : W.memaddr;
    sr_mem_mm : W.memaddr }.

Record module_runtime :=
  { mr_mem_gc : W.memidx;
    mr_mem_mm : W.memidx;
    mr_func_alloc : W.funcidx;
    mr_func_free : W.funcidx;
    mr_func_registerroot : W.funcidx;
    mr_func_duproot : W.funcidx;
    mr_func_unregisterroot : W.funcidx;
    mr_global_table_offset : W.globalidx;
    mr_table : W.tableidx }.

Record module_env :=
  { me_globals : list R.GlobalType;
    me_runtime : module_runtime }.

Record function_env :=
  { fe_return_type : option (list R.Typ);
    fe_size_bounds : list (list R.Size * list R.Size);
    fe_size_locals : list W.localidx;
    fe_wlocal_offset : nat }.

Inductive VarScope :=
  | VSGlobal
  | VSLocal.

Definition funcimm (idx : W.funcidx) : W.immediate :=
  let '(W.Mk_funcidx i) := idx in i.

Definition tableimm (idx : W.tableidx) : W.immediate :=
  let '(W.Mk_tableidx i) := idx in i.

Definition memimm (idx : W.memidx) : W.immediate :=
  let '(W.Mk_memidx i) := idx in i.

Definition localimm (idx : W.localidx) : W.immediate :=
  let '(W.Mk_localidx i) := idx in i.

Definition globalimm (idx : W.globalidx) : W.immediate :=
  let '(W.Mk_globalidx i) := idx in i.

Definition scope_get_set (scope : VarScope) :
  (W.immediate -> W.basic_instruction) *
  (W.immediate -> W.basic_instruction) :=
  match scope with
  | VSGlobal => (W.BI_get_global, W.BI_set_global)
  | VSLocal => (W.BI_get_local, W.BI_set_local)
  end.
