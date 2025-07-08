From Coq Require Import List NArith.BinNat.
From stdpp Require Import base option strings list pretty.
From RWasm Require term.
From Wasm Require datatypes numerics.
From RWasm.compiler Require Import monads.

(* TODO: this is a pretty bad place to declare this *)
Module R := term.
Module W := datatypes.

Definition compile_sign (s : R.Sign) : W.sx :=
  match s with
  | R.U => W.SX_U
  | R.S => W.SX_S
  end.

Definition compile_num_from_Z (num_type : W.value_type) (num : Z) : W.value :=
  match num_type with
  | W.T_i32 => W.VAL_int32 (numerics.Wasm_int.int_of_Z numerics.i32m num)
  | W.T_i64 => W.VAL_int64 (numerics.Wasm_int.int_of_Z numerics.i64m num)
  (* TODO: is the signed converter the right thing to use here? *)
  | W.T_f32 =>
    let i := numerics.Wasm_int.int_of_Z numerics.i32m num in
    W.VAL_float32 (numerics.Wasm_float.float_convert_si32 numerics.f32m i)
  | W.T_f64 =>
    let i := numerics.Wasm_int.int_of_Z numerics.i64m num in
    W.VAL_float64 (numerics.Wasm_float.float_convert_si64 numerics.f64m i)
  end.

Definition compile_num (num_type : R.NumType) (num : nat) : W.value :=
  match num_type with
  | R.Int _ R.i32 => compile_num_from_Z W.T_i32 (Z.of_nat num)
  | R.Int _ R.i64 => compile_num_from_Z W.T_i64 (Z.of_nat num)
  | R.Float R.f32 => compile_num_from_Z W.T_f32 (Z.of_nat num)
  | R.Float R.f64 => compile_num_from_Z W.T_f64 (Z.of_nat num)
  end.

Definition compile_int_type (typ : R.IntType) : W.value_type :=
  match typ with
  | R.i32 => W.T_i32
  | R.i64 => W.T_i64
  end.

Definition compile_float_type (typ : R.FloatType) : W.value_type :=
  match typ with
  | R.f32 => W.T_f32
  | R.f64 => W.T_f64
  end.

Definition throw_missing (instr_name : string) : exn err W.basic_instruction :=
  mthrow (Err ("missing iris-wasm " ++ instr_name ++ " wrap instruction")).

Definition compile_num_instr (ni : R.NumInstr) : exn err W.basic_instruction :=
  match ni with
  | R.Iu typ op =>
    let typ' := compile_int_type typ in
    let op' := W.Unop_i match op with
    | R.clz => W.UOI_clz
    | R.ctz => W.UOI_ctz
    | R.popcnt => W.UOI_popcnt
    end in
    mret $ W.BI_unop typ' op'
  | R.Ib typ op =>
    let typ' := compile_int_type typ in
    let op' := W.Binop_i match op with
    | R.add => W.BOI_add
    | R.sub => W.BOI_sub
    | R.mul => W.BOI_mul
    | R.div s => W.BOI_div (compile_sign s)
    | R.rem s => W.BOI_rem (compile_sign s)
    | R.and => W.BOI_and
    | R.or => W.BOI_or
    | R.xor => W.BOI_xor
    | R.shl => W.BOI_shl
    | R.shr s => W.BOI_shr (compile_sign s)
    | R.rotl => W.BOI_rotl
    | R.rotr => W.BOI_rotr
    end in
    mret $ W.BI_binop typ' op'
  | R.Fu typ op =>
    let typ' := compile_float_type typ in
    let op' := W.Unop_f match op with
    | R.neg => W.UOF_neg
    | R.abs => W.UOF_abs
    | R.ceil => W.UOF_ceil
    | R.floor => W.UOF_floor
    | R.trunc => W.UOF_trunc
    | R.nearest => W.UOF_nearest
    | R.sqrt => W.UOF_sqrt
    end in
    mret $ W.BI_unop typ' op'
  | R.Fb typ op =>
    let typ' := compile_float_type typ in
    let op' := W.Binop_f match op with
    | R.addf => W.BOF_add
    | R.subf => W.BOF_sub
    | R.mulf => W.BOF_mul
    | R.divf => W.BOF_div
    | R.min => W.BOF_min
    | R.max => W.BOF_max
    | R.copysign => W.BOF_copysign
    end in
    mret $ W.BI_binop typ' op'
  | R.It typ op =>
    let typ' := compile_int_type typ in
    let op' := match op with
    | R.eqz => W.TO_eqz
    end in
    mret $ W.BI_testop typ' op'
  | R.Ir typ op =>
    let typ' := compile_int_type typ in
    let op' := W.Relop_i match op with
    | R.eq => W.ROI_eq
    | R.ne => W.ROI_ne
    | R.lt s => W.ROI_lt (compile_sign s)
    | R.gt s => W.ROI_gt (compile_sign s)
    | R.le s => W.ROI_le (compile_sign s)
    | R.ge s => W.ROI_ge (compile_sign s)
    end in
    mret $ W.BI_relop typ' op'
  | R.Fr typ op =>
    let typ' := compile_float_type typ in
    let op' := W.Relop_f match op with
    | R.eqf => W.ROF_eq
    | R.nef => W.ROF_ne
    | R.ltf => W.ROF_lt
    | R.gtf => W.ROF_gt
    | R.lef => W.ROF_le
    | R.gef => W.ROF_ge
    end in
    mret $ W.BI_relop typ' op'
  | R.CvtI typ op =>
    let typ' := compile_int_type typ in
    match op with
    (* FIXME: missing wasm types *)
    | R.Wrap typ2 => throw_missing "wrap"
    | R.Extend typ2 s => throw_missing "extend"
    | R.Trunc typ2 s => throw_missing "trunc"
    | R.TruncSat typ2 s => throw_missing "trunc_sat"
    | R.Convert typ2 s =>
        let typ2' := compile_int_type typ2 in
        let s' := compile_sign s in
        mret $ W.BI_cvtop typ' W.CVO_convert typ2' (Some s')
    | R.Demote typ2 => throw_missing "demote"
    | R.Promote typ2 => throw_missing "promote"
    | R.Reinterpret typ2 =>
        let typ2' := compile_int_type typ2 in
        mret $ W.BI_cvtop typ' W.CVO_convert typ2' None
    end
  | R.CvtF typ op =>
    let typ' := compile_float_type typ in
    match op with
    (* FIXME: missing wasm types *)
    | R.Wrap typ2 => throw_missing "wrap"
    | R.Extend typ2 s => throw_missing "extend"
    | R.Trunc typ2 s => throw_missing "trunc"
    | R.TruncSat typ2 s => throw_missing "trunc_sat"
    | R.Convert typ2 s =>
        let typ2' := compile_int_type typ2 in
        let s' := compile_sign s in
        mret $ W.BI_cvtop typ' W.CVO_convert typ2' (Some s')
    | R.Demote typ2 => throw_missing "demote"
    | R.Promote typ2 => throw_missing "promote"
    | R.Reinterpret typ2 =>
        let typ2' := compile_int_type typ2 in
        mret $ W.BI_cvtop typ' W.CVO_convert typ2' None
    end
  end.
