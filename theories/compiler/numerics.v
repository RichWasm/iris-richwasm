From Stdlib Require Import List NArith.BinNat.
Require Import Stdlib.Strings.String.
Require Import Stdlib.ZArith.BinInt.
Require Import Stdlib.Program.Basics.
Local Open Scope program_scope.

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

Definition compile_Z (ty : W.value_type) : Z -> W.value :=
  match ty with
  | W.T_i32 => W.VAL_int32 ∘ Wasm_int.int_of_Z i32m
  | W.T_i64 => W.VAL_int64 ∘ Wasm_int.int_of_Z i64m
  | W.T_f32 => W.VAL_float32 ∘ Wasm_float.FloatSize32.of_bits ∘ Integers.Int.repr
  | W.T_f64 => W.VAL_float64 ∘ Wasm_float.FloatSize64.of_bits ∘ Integers.Int64.repr
  end.

Definition compile_cvt_op (op : conversion_op) : W.basic_instruction :=
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

Definition compile_num_instr (e : num_instruction) : W.basic_instruction :=
  match e with
  | IInt1 νi op =>
      let νi' := translate_int_type νi in
      let op' :=
        match op with
        | ClzI => W.UOI_clz
        | CtzI => W.UOI_ctz
        | PopcntI => W.UOI_popcnt
        end
      in
      W.BI_unop νi' (W.Unop_i op')
  | IInt2 νi op =>
      let νi' := translate_int_type νi in
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
      W.BI_binop νi' (W.Binop_i op')
  | IIntTest νi op =>
      let νi' := translate_int_type νi in
      let op' :=
        match op with
        | EqzI => W.TO_eqz
        end
      in
      W.BI_testop νi' op'
  | IIntRel νi op =>
      let νi' := translate_int_type νi in
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
      W.BI_relop νi' (W.Relop_i op')
  | IFloat1 νf op =>
      let νf' := translate_float_type νf in
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
      W.BI_unop νf' (W.Unop_f op')
  | IFloat2 νf op =>
      let νf' := translate_float_type νf in
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
      W.BI_binop νf' (W.Binop_f op')
  | IFloatRel νf op =>
      let νf' := translate_float_type νf in
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
      W.BI_relop νf' (W.Relop_f op')
  | ICvt op => compile_cvt_op op
  end.
