Require Import Stdlib.Numbers.BinNums.

Require Import stdpp.list_numbers.

Require Wasm.datatypes.

From RichWasm Require Import syntax layout.

Module W := Wasm.datatypes.

Inductive error :=
  | EWrongTypeAnn
  | ECaseNotOnVariant
  | EIndexOutOfBounds (index : nat)
  | EUnboundQual
  | EUnboundTypeVar
  | ERepNotMono
  | EUnboundLocal
  | ETodo.

Record store_runtime :=
  { sr_mem_gc : W.memaddr;
    sr_mem_mm : W.memaddr;
    sr_gc_heap_start : N }.

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
    fe_type_vars : list kind;
    fe_local_reprs : list representation }.

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

Definition option_sum {A E : Type} (e : E) (x : option A) : E + A :=
  match x with
  | None => inl e
  | Some x' => inr x'
  end.

Definition translate_prim_rep (ι : primitive_rep) : W.value_type :=
  match ι with
  | PtrR => W.T_i32
  | I32R => W.T_i32
  | I64R => W.T_i64
  | F32R => W.T_f32
  | F64R => W.T_f64
  end.

Definition translate_rep (ρ : representation) : option (list W.value_type) :=
  map translate_prim_rep <$> eval_rep ρ.

Definition translate_type (κs : list kind) (τ : type) : option (list W.value_type) :=
  type_rep κs τ ≫= translate_rep.

Definition translate_types (κs : list kind) (τs : list type) : option (list W.value_type) :=
  @concat _ <$> mapM (translate_type κs) τs.

Definition translate_num_type (ν : num_type) : W.value_type :=
  translate_prim_rep (num_type_rep ν).

Definition translate_arrow_type (κs : list kind) (χ : arrow_type) : option W.function_type :=
  let 'ArrowT τs1 τs2 := χ in
  tys1 ← translate_types κs τs1;
  tys2 ← translate_types κs τs2;
  mret (W.Tf tys1 tys2).

Definition fe_wlocal_offset (fe : function_env) : nat :=
  default 0 (sum_list_with length <$> mapM translate_rep fe.(fe_local_reprs)).
