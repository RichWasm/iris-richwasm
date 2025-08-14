From Coq Require Import List NArith.BinNat.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinInt.

From Wasm Require datatypes.
From Wasm Require Import numerics.

From RichWasm Require term.
From RichWasm.compiler Require Import types.

Module R := RichWasm.term.
Module W := Wasm.datatypes.

Definition translate_sign (s : R.Sign) : W.sx :=
  match s with
  | R.U => W.SX_U
  | R.S => W.SX_S
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

Definition compile_cvt_op (op : R.CvtOp) : W.basic_instruction :=
  match op with
  | R.Wrap =>
      W.BI_cvtop W.T_i32 W.CVO_convert W.T_i64 None
  | R.Extend s =>
      W.BI_cvtop W.T_i64 W.CVO_convert W.T_i32 (Some (translate_sign s))
  | R.Trunc i f s =>
      let wi := translate_int_type i in
      let wf := translate_float_type f in
      W.BI_cvtop wi W.CVO_convert wf (Some (translate_sign s))
  | R.TruncSat i f s =>
      (* XXX this case shouldn't be the same as the Trunc case, but I
         don't see what else it could be in the wasmcert syntax. Is
         this a Wasm 1.0 vs current day Wasm issue ? *)
      let wi := translate_int_type i in
      let wf := translate_float_type f in
      W.BI_cvtop wi W.CVO_convert wf (Some (translate_sign s))
  | R.Demote =>
      W.BI_cvtop W.T_f64 W.CVO_convert W.T_f32 None 
  | R.Promote =>
      W.BI_cvtop W.T_f32 W.CVO_convert W.T_f64 None
  | R.Convert f i s =>
      let wi := translate_int_type i in
      let wf := translate_float_type f in
      W.BI_cvtop wf W.CVO_convert wf (Some (translate_sign s))
  | R.ReinterpretFI f i =>
      let wi := translate_int_type i in
      let wf := translate_float_type f in
      W.BI_cvtop wf W.CVO_reinterpret wi None
  | R.ReinterpretIF i f =>
      let wi := translate_int_type i in
      let wf := translate_float_type f in
      W.BI_cvtop wi W.CVO_reinterpret wf None
  | R.ReinterpretII i s s' => W.BI_nop
  end.

Definition compile_num_instr (e : R.NumInstr) : W.basic_instruction :=
  match e with
  | R.Iu ty op =>
    let ty' := translate_int_type ty in
    let op' :=
      match op with
      | R.clz => W.UOI_clz
      | R.ctz => W.UOI_ctz
      | R.popcnt => W.UOI_popcnt
      end
    in
    W.BI_unop ty' (W.Unop_i op')
  | R.Ib ty op =>
    let ty' := translate_int_type ty in
    let op' :=
      match op with
      | R.add => W.BOI_add
      | R.sub => W.BOI_sub
      | R.mul => W.BOI_mul
      | R.div s => W.BOI_div (translate_sign s)
      | R.rem s => W.BOI_rem (translate_sign s)
      | R.and => W.BOI_and
      | R.or => W.BOI_or
      | R.xor => W.BOI_xor
      | R.shl => W.BOI_shl
      | R.shr s => W.BOI_shr (translate_sign s)
      | R.rotl => W.BOI_rotl
      | R.rotr => W.BOI_rotr
      end
    in
    W.BI_binop ty' (W.Binop_i op')
  | R.Fu ty op =>
    let ty' := translate_float_type ty in
    let op' :=
      match op with
      | R.neg => W.UOF_neg
      | R.abs => W.UOF_abs
      | R.ceil => W.UOF_ceil
      | R.floor => W.UOF_floor
      | R.trunc => W.UOF_trunc
      | R.nearest => W.UOF_nearest
      | R.sqrt => W.UOF_sqrt
      end
    in
    W.BI_unop ty' (W.Unop_f op')
  | R.Fb ty op =>
    let ty' := translate_float_type ty in
    let op' :=
      match op with
      | R.addf => W.BOF_add
      | R.subf => W.BOF_sub
      | R.mulf => W.BOF_mul
      | R.divf => W.BOF_div
      | R.min => W.BOF_min
      | R.max => W.BOF_max
      | R.copysign => W.BOF_copysign
      end
    in
    W.BI_binop ty' (W.Binop_f op')
  | R.It ty op =>
    let ty' := translate_int_type ty in
    let op' :=
      match op with
      | R.eqz => W.TO_eqz
      end
    in
    W.BI_testop ty' op'
  | R.Ir ty op =>
    let ty' := translate_int_type ty in
    let op' :=
      match op with
      | R.eq => W.ROI_eq
      | R.ne => W.ROI_ne
      | R.lt s => W.ROI_lt (translate_sign s)
      | R.gt s => W.ROI_gt (translate_sign s)
      | R.le s => W.ROI_le (translate_sign s)
      | R.ge s => W.ROI_ge (translate_sign s)
      end
    in
    W.BI_relop ty' (W.Relop_i op')
  | R.Fr ty op =>
    let ty' := translate_float_type ty in
    let op' :=
      match op with
      | R.eqf => W.ROF_eq
      | R.nef => W.ROF_ne
      | R.ltf => W.ROF_lt
      | R.gtf => W.ROF_gt
      | R.lef => W.ROF_le
      | R.gef => W.ROF_ge
      end
    in
    W.BI_relop ty' (W.Relop_f op')
  | R.Cvt op => compile_cvt_op op
  end.
