From Stdlib Require Import List NArith.BinNat.
Require Import Stdlib.Strings.String.
Require Import Stdlib.ZArith.BinInt.

Require Wasm.datatypes.
Require Import Wasm.numerics.

Require Import RichWasm.syntax.
Require Import RichWasm.compiler.util.

Module W := Wasm.datatypes.

Definition translate_sign (s : sign) : W.sx :=
  match s with
  | SignU => W.SX_U
  | SignS => W.SX_S
  end.

Definition translate_int_type (νᵢ : int_type) : W.value_type :=
  match νᵢ with
  | I32T => W.T_i32
  | I64T => W.T_i64
  end.

Definition translate_float_type (ν__f : float_type) : W.value_type :=
  match ν__f with
  | F32T => W.T_f32
  | F64T => W.T_f64
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

Definition compile_cvt_op (op : conversion_op) : W.basic_instruction :=
  match op with
  | CWrap => W.BI_cvtop W.T_i32 W.CVO_convert W.T_i64 None
  | CExtend s => W.BI_cvtop W.T_i64 W.CVO_convert W.T_i32 (Some (translate_sign s))
  | CTrunc i f s =>
      let wi := translate_int_type i in
      let wf := translate_float_type f in
      W.BI_cvtop wi W.CVO_convert wf (Some (translate_sign s))
  | CTruncSat i f s =>
      (* XXX this case shouldn't be the same as the Trunc case, but I
         don't see what else it could be in the wasmcert syntax. Is
         this a Wasm 1.0 vs current day Wasm issue ? *)
      let wi := translate_int_type i in
      let wf := translate_float_type f in
      W.BI_cvtop wi W.CVO_convert wf (Some (translate_sign s))
  | CDemote => W.BI_cvtop W.T_f64 W.CVO_convert W.T_f32 None
  | CPromote => W.BI_cvtop W.T_f32 W.CVO_convert W.T_f64 None
  | CConvert f i s =>
      let wi := translate_int_type i in
      let wf := translate_float_type f in
      W.BI_cvtop wf W.CVO_convert wf (Some (translate_sign s))
  | CReinterpretFI f i =>
      let wi := translate_int_type i in
      let wf := translate_float_type f in
      W.BI_cvtop wf W.CVO_reinterpret wi None
  | CReinterpretIF i f =>
      let wi := translate_int_type i in
      let wf := translate_float_type f in
      W.BI_cvtop wi W.CVO_reinterpret wf None
  | CReinterpretII i s s' => W.BI_nop
  end.

Definition compile_num_instr (e : num_instruction) : W.basic_instruction :=
  match e with
  | IInt1 νᵢ op =>
      let νᵢ' := translate_int_type νᵢ in
      let op' :=
        match op with
        | ClzI => W.UOI_clz
        | CtzI => W.UOI_ctz
        | PopcntI => W.UOI_popcnt
        end
      in
      W.BI_unop νᵢ' (W.Unop_i op')
  | IInt2 νᵢ op =>
      let νᵢ' := translate_int_type νᵢ in
      let op' :=
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
        end
      in
      W.BI_binop νᵢ' (W.Binop_i op')
  | IIntTest νᵢ op =>
      let νᵢ' := translate_int_type νᵢ in
      let op' :=
        match op with
        | EqzI => W.TO_eqz
        end
      in
      W.BI_testop νᵢ' op'
  | IIntRel νᵢ op =>
      let νᵢ' := translate_int_type νᵢ in
      let op' :=
        match op with
        | EqI => W.ROI_eq
        | NeI => W.ROI_ne
        | LtI s => W.ROI_lt (translate_sign s)
        | GtI s => W.ROI_gt (translate_sign s)
        | LeI s => W.ROI_le (translate_sign s)
        | GeI s => W.ROI_ge (translate_sign s)
        end
      in
      W.BI_relop νᵢ' (W.Relop_i op')
  | IFloat1 ν__f op =>
      let ν__f' := translate_float_type ν__f in
      let op' :=
        match op with
        | NegF => W.UOF_neg
        | AbsF => W.UOF_abs
        | CeilF => W.UOF_ceil
        | FloorF => W.UOF_floor
        | TruncF => W.UOF_trunc
        | NearestF => W.UOF_nearest
        | SqrtF => W.UOF_sqrt
        end
      in
      W.BI_unop ν__f' (W.Unop_f op')
  | IFloat2 ν__f op =>
      let ν__f' := translate_float_type ν__f in
      let op' :=
        match op with
        | AddF => W.BOF_add
        | SubF => W.BOF_sub
        | MulF => W.BOF_mul
        | DivF => W.BOF_div
        | MinF => W.BOF_min
        | MaxF => W.BOF_max
        | CopySignF => W.BOF_copysign
      end
      in
      W.BI_binop ν__f' (W.Binop_f op')
  | IFloatRel ν__f op =>
      let ν__f' := translate_float_type ν__f in
      let op' :=
        match op with
        | EqF => W.ROF_eq
        | NeF => W.ROF_ne
        | LtF => W.ROF_lt
        | GtF => W.ROF_gt
        | LeF => W.ROF_le
        | GeF => W.ROF_ge
        end
      in
      W.BI_relop ν__f' (W.Relop_f op')
  | ICvt op => compile_cvt_op op
  end.
