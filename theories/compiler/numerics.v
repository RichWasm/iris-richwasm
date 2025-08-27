From Coq Require Import List NArith.BinNat.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinInt.

From Wasm Require datatypes.
From Wasm Require Import numerics.

From RichWasm Require syntax.
From RichWasm.compiler Require Import types.

Module R := RichWasm.syntax.
Module W := Wasm.datatypes.

Definition translate_sign (s : R.sign) : W.sx :=
  match s with
  | R.SignU => W.SX_U
  | R.SignS => W.SX_S
  end.

Definition translate_int_type (νᵢ : R.int_type) : W.value_type :=
  match νᵢ with
  | R.I32T => W.T_i32
  | R.I64T => W.T_i64
  end.

Definition translate_float_type (ν__f : R.float_type) : W.value_type :=
  match ν__f with
  | R.F32T => W.T_f32
  | R.F64T => W.T_f64
  end.

Definition compile_Z (ty : W.value_type) (n : Z) : W.value :=
  match ty with
  | W.T_i32 => W.VAL_int32 (Wasm_int.int_of_Z i32m n)
  | W.T_i64 => W.VAL_int64 (Wasm_int.int_of_Z i64m n)
  (* TODO: is the signed converter the right thing to use here? *)
  | W.T_f32 =>
    let i := Wasm_int.int_of_Z i32m n in
    W.VAL_float32 (Wasm_float.float_convert_si32 f32m i)
  | W.T_f64 =>
    let i := Wasm_int.int_of_Z i64m n in
    W.VAL_float64 (Wasm_float.float_convert_si64 f64m i)
  end.

Definition compile_cvt_op (op : R.cvtop) : W.basic_instruction :=
  match op with
  | R.CWrap =>
      W.BI_cvtop W.T_i32 W.CVO_convert W.T_i64 None
  | R.CExtend s =>
      W.BI_cvtop W.T_i64 W.CVO_convert W.T_i32 (Some (translate_sign s))
  | R.CTrunc i f s =>
      let wi := translate_int_type i in
      let wf := translate_float_type f in
      W.BI_cvtop wi W.CVO_convert wf (Some (translate_sign s))
  | R.CTruncSat i f s =>
      (* XXX this case shouldn't be the same as the Trunc case, but I
         don't see what else it could be in the wasmcert syntax. Is
         this a Wasm 1.0 vs current day Wasm issue ? *)
      let wi := translate_int_type i in
      let wf := translate_float_type f in
      W.BI_cvtop wi W.CVO_convert wf (Some (translate_sign s))
  | R.CDemote =>
      W.BI_cvtop W.T_f64 W.CVO_convert W.T_f32 None 
  | R.CPromote =>
      W.BI_cvtop W.T_f32 W.CVO_convert W.T_f64 None
  | R.CConvert f i s =>
      let wi := translate_int_type i in
      let wf := translate_float_type f in
      W.BI_cvtop wf W.CVO_convert wf (Some (translate_sign s))
  | R.CReinterpretFI f i =>
      let wi := translate_int_type i in
      let wf := translate_float_type f in
      W.BI_cvtop wf W.CVO_reinterpret wi None
  | R.CReinterpretIF i f =>
      let wi := translate_int_type i in
      let wf := translate_float_type f in
      W.BI_cvtop wi W.CVO_reinterpret wf None
  | R.CReinterpretII i s s' => W.BI_nop
  end.

Definition compile_num_instr (e : R.num_instr) : W.basic_instruction :=
  match e with
  | R.IInt1 νᵢ op =>
    let νᵢ' := translate_int_type νᵢ in
    let op' :=
      match op with
      | R.ClzI => W.UOI_clz
      | R.CtzI => W.UOI_ctz
      | R.PopcntI => W.UOI_popcnt
      end
    in
    W.BI_unop νᵢ' (W.Unop_i op')
  | R.IInt2 νᵢ op =>
    let νᵢ' := translate_int_type νᵢ in
    let op' :=
      match op with
      | R.AddI => W.BOI_add
      | R.SubI => W.BOI_sub
      | R.MulI => W.BOI_mul
      | R.DivI s => W.BOI_div (translate_sign s)
      | R.RemI s => W.BOI_rem (translate_sign s)
      | R.AndI => W.BOI_and
      | R.OrI => W.BOI_or
      | R.XorI => W.BOI_xor
      | R.ShlI => W.BOI_shl
      | R.ShrI s => W.BOI_shr (translate_sign s)
      | R.RotlI => W.BOI_rotl
      | R.RotrI => W.BOI_rotr
      end
    in
    W.BI_binop νᵢ' (W.Binop_i op')
  | R.IIntTest νᵢ op =>
    let νᵢ' := translate_int_type νᵢ in
    let op' :=
      match op with
      | R.EqzI => W.TO_eqz
      end
    in
    W.BI_testop νᵢ' op'
  | R.IIntRel νᵢ op =>
    let νᵢ' := translate_int_type νᵢ in
    let op' :=
      match op with
      | R.EqI => W.ROI_eq
      | R.NeI => W.ROI_ne
      | R.LtI s => W.ROI_lt (translate_sign s)
      | R.GtI s => W.ROI_gt (translate_sign s)
      | R.LeI s => W.ROI_le (translate_sign s)
      | R.GeI s => W.ROI_ge (translate_sign s)
      end
    in
    W.BI_relop νᵢ' (W.Relop_i op')
  | R.IFloat1 ν__f op =>
    let ν__f' := translate_float_type ν__f in
    let op' :=
      match op with
      | R.NegF => W.UOF_neg
      | R.AbsF => W.UOF_abs
      | R.CeilF => W.UOF_ceil
      | R.FloorF => W.UOF_floor
      | R.TruncF => W.UOF_trunc
      | R.NearestF => W.UOF_nearest
      | R.SqrtF => W.UOF_sqrt
      end
    in
    W.BI_unop ν__f' (W.Unop_f op')
  | R.IFloat2 ν__f op =>
    let ν__f' := translate_float_type ν__f in
    let op' :=
      match op with
      | R.AddF => W.BOF_add
      | R.SubF => W.BOF_sub
      | R.MulF => W.BOF_mul
      | R.DivF => W.BOF_div
      | R.MinF => W.BOF_min
      | R.MaxF => W.BOF_max
      | R.CopySignF => W.BOF_copysign
      end
    in
    W.BI_binop ν__f' (W.Binop_f op')
  | R.IFloatRel ν__f op =>
    let ν__f' := translate_float_type ν__f in
    let op' :=
      match op with
      | R.EqF => W.ROF_eq
      | R.NeF => W.ROF_ne
      | R.LtF => W.ROF_lt
      | R.GtF => W.ROF_gt
      | R.LeF => W.ROF_le
      | R.GeF => W.ROF_ge
      end
    in
    W.BI_relop ν__f' (W.Relop_f op')
  | R.ICvt op => compile_cvt_op op
  end.
