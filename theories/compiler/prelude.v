Require Import Stdlib.Numbers.BinNums.

Require Import stdpp.list_numbers.

Require Wasm.datatypes.
Require Import Wasm.numerics.

From RichWasm Require Import layout syntax typing.

Module W := Wasm.datatypes.

Inductive error :=
| EFail
| ETodo.

Record module_runtime :=
  { mr_mem_mm : W.memidx;
    mr_mem_gc : W.memidx;
    mr_func_mmalloc : W.funcidx;
    mr_func_gcalloc : W.funcidx;
    mr_func_setflag : W.funcidx;
    mr_func_free : W.funcidx;
    mr_func_registerroot : W.funcidx;
    mr_func_unregisterroot : W.funcidx;
    mr_func_user : W.funcidx;
    mr_table : W.tableidx;
    mr_global_table_off : W.globalidx;
    mr_global_user : W.globalidx }.

Record function_env :=
  { fe_type_vars : list kind;
    fe_return : list type;
    fe_locals : list (list primitive);
    fe_br_skip : nat }.

Definition fe_of_module_func (mf : module_function) : option function_env :=
  let ϕ := flatten_function_type mf.(mf_type) in
  Some (Build_function_env ϕ.(fft_type_vars) ϕ.(fft_out) mf.(mf_locals) 0).

Definition fe_of_context (F : function_ctx) : function_env :=
  {| fe_type_vars := F.(fc_type_vars);
     fe_return := F.(fc_return);
     fe_locals := F.(fc_locals);
     fe_br_skip := 0 |}.

Definition fe_wlocal_offset (fe : function_env) : nat :=
  sum_list_with length fe.(fe_locals).

Definition offset_mm : W.static_offset := 3%N.
Definition offset_gc : W.static_offset := 1%N.
Definition align_word : W.alignment_exponent := 2%N.

Definition typeimm (ix : W.typeidx) : W.immediate :=
  let '(W.Mk_typeidx i) := ix in i.

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

Definition option_sum {A E : Type} (e : E) (x : option A) : E + A :=
  match x with
  | None => inl e
  | Some x' => inr x'
  end.

Definition translate_prim (η : primitive) : W.value_type :=
  match η with
  | I32P => W.T_i32
  | I64P => W.T_i64
  | F32P => W.T_f32
  | F64P => W.T_f64
  end.

Definition translate_arep : atomic_rep -> W.value_type :=
  translate_prim ∘ arep_to_prim.

Definition translate_rep : representation -> option (list W.value_type) :=
  fmap (map translate_arep) ∘ eval_rep EmptyEnv.

Definition translate_type (κs : list kind) (τ : type) : option (list W.value_type) :=
  type_rep κs τ ≫= translate_rep.

Definition translate_types (κs : list kind) (τs : list type) : option (list W.value_type) :=
  @concat _ <$> mapM (translate_type κs) τs.

Definition translate_num_type : num_type -> W.value_type :=
  translate_prim ∘ arep_to_prim ∘ num_type_arep.

Definition translate_instr_type (κs : list kind) (ψ : instruction_type) : option W.function_type :=
  let 'InstrT τs1 τs2 := ψ in
  tys1 ← translate_types κs τs1;
  tys2 ← translate_types κs τs2;
  Some (W.Tf tys1 tys2).

Fixpoint translate_func_type (κs : list kind) (ϕ : function_type) : option W.function_type :=
  match ϕ with
  | MonoFunT τs1 τs2 => translate_instr_type κs (InstrT τs1 τs2)
  | ForallMemT ϕ'
  | ForallRepT ϕ'
  | ForallSizeT ϕ' => translate_func_type κs ϕ'
  | ForallTypeT κ ϕ' => translate_func_type (κ :: κs) ϕ'
  end.

Definition translate_sign (s : sign) : W.sx :=
  match s with
  | SignU => W.SX_U
  | SignS => W.SX_S
  end.

Definition translate_int_type (νi : int_type) : W.value_type :=
  match νi with
  | I32T => W.T_i32
  | I64T => W.T_i64
  end.

Definition translate_float_type (νf : float_type) : W.value_type :=
  match νf with
  | F32T => W.T_f32
  | F64T => W.T_f64
  end.

Definition translate_int_unop (op : int_unop) : W.unop_i :=
  match op with
  | ClzI => W.UOI_clz
  | CtzI => W.UOI_ctz
  | PopcntI => W.UOI_popcnt
  end.

Definition translate_int_binop (op : int_binop) : W.binop_i :=
  match op with
  | AddI => W.BOI_add
  | SubI => W.BOI_sub
  | MulI => W.BOI_mul
  | DivI s => W.BOI_div (translate_sign s)
  | RemI s => W.BOI_rem (translate_sign s)
  | AndI => W.BOI_and
  | OrI => W.BOI_or
  | XorI => W.BOI_xor
  | ShlI => W.BOI_shl
  | ShrI s => W.BOI_shr (translate_sign s)
  | RotlI => W.BOI_rotl
  | RotrI => W.BOI_rotr
  end.

Definition translate_int_testop (op : int_testop) : W.testop :=
  match op with
  | EqzI => W.TO_eqz
  end.

Definition translate_int_relop (op : int_relop) : W.relop_i :=
  match op with
  | EqI => W.ROI_eq
  | NeI => W.ROI_ne
  | LtI s => W.ROI_lt (translate_sign s)
  | GtI s => W.ROI_gt (translate_sign s)
  | LeI s => W.ROI_le (translate_sign s)
  | GeI s => W.ROI_ge (translate_sign s)
  end.

Definition translate_float_unop (op : float_unop) : W.unop_f :=
  match op with
  | NegF => W.UOF_neg
  | AbsF => W.UOF_abs
  | CeilF => W.UOF_ceil
  | FloorF => W.UOF_floor
  | TruncF => W.UOF_trunc
  | NearestF => W.UOF_nearest
  | SqrtF => W.UOF_sqrt
  end.

Definition translate_float_binop (op : float_binop) : W.binop_f :=
  match op with
  | AddF => W.BOF_add
  | SubF => W.BOF_sub
  | MulF => W.BOF_mul
  | DivF => W.BOF_div
  | MinF => W.BOF_min
  | MaxF => W.BOF_max
  | CopySignF => W.BOF_copysign
  end.

Definition translate_float_relop (op : float_relop) : W.relop_f :=
  match op with
  | EqF => W.ROF_eq
  | NeF => W.ROF_ne
  | LtF => W.ROF_lt
  | GtF => W.ROF_gt
  | LeF => W.ROF_le
  | GeF => W.ROF_ge
  end.

Definition translate_cvt_op (op : conversion_op) : W.basic_instruction :=
  match op with
  | CWrap => W.BI_cvtop W.T_i32 W.CVO_convert W.T_i64 None
  | CExtend s =>
      let s' := translate_sign s in
      W.BI_cvtop W.T_i64 W.CVO_convert W.T_i32 (Some s')
  | CTrunc νf νi s =>
      let νf' := translate_float_type νf in
      let νi' := translate_int_type νi in
      let s' := translate_sign s in
      W.BI_cvtop νi' W.CVO_convert νf' (Some s')
  | CDemote => W.BI_cvtop W.T_f64 W.CVO_convert W.T_f32 None
  | CPromote => W.BI_cvtop W.T_f32 W.CVO_convert W.T_f64 None
  | CConvert νi νf s =>
      let νi' := translate_int_type νi in
      let νf' := translate_float_type νf in
      let s' := translate_sign s in
      W.BI_cvtop νf' W.CVO_convert νi' (Some s')
  | CReinterpret (IntT I32T) => W.BI_cvtop W.T_f32 W.CVO_reinterpret W.T_i32 None
  | CReinterpret (IntT I64T) => W.BI_cvtop W.T_f64 W.CVO_reinterpret W.T_i64 None
  | CReinterpret (FloatT F32T) => W.BI_cvtop W.T_i32 W.CVO_reinterpret W.T_f32 None
  | CReinterpret (FloatT F64T) => W.BI_cvtop W.T_i64 W.CVO_reinterpret W.T_f64 None
  end.

Definition value_of_Z (ty : W.value_type) : Z -> W.value :=
  match ty with
  | W.T_i32 => W.VAL_int32 ∘ Wasm_int.int_of_Z i32m
  | W.T_i64 => W.VAL_int64 ∘ Wasm_int.int_of_Z i64m
  | W.T_f32 => W.VAL_float32 ∘ Wasm_float.FloatSize32.of_bits ∘ Integers.Int.repr
  | W.T_f64 => W.VAL_float64 ∘ Wasm_float.FloatSize64.of_bits ∘ Integers.Int64.repr
  end.
