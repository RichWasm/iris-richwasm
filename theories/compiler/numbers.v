From Coq Require Import List NArith.BinNat.
From stdpp Require Import base option strings list pretty.
From RWasm Require term.
From Wasm Require datatypes numerics.
From RWasm.compiler Require Import monads.

(* TODO: this is a pretty bad place to declare this *)
Module rwasm := term.
Module wasm := datatypes.

Definition compile_sign (s : rwasm.Sign) : wasm.sx :=
  match s with
  | rwasm.U => wasm.SX_U
  | rwasm.S => wasm.SX_S
  end.

Definition compile_num_from_Z (num_type : wasm.value_type) (num : Z) : wasm.value :=
  match num_type with
  | wasm.T_i32 => wasm.VAL_int32 (numerics.Wasm_int.int_of_Z numerics.i32m num)
  | wasm.T_i64 => wasm.VAL_int64 (numerics.Wasm_int.int_of_Z numerics.i64m num)
  (* TODO: is the signed converter the right thing to use here? *)
  | wasm.T_f32 =>
    let i := numerics.Wasm_int.int_of_Z numerics.i32m num in
    wasm.VAL_float32 (numerics.Wasm_float.float_convert_si32 numerics.f32m i)
  | wasm.T_f64 =>
    let i := numerics.Wasm_int.int_of_Z numerics.i64m num in
    wasm.VAL_float64 (numerics.Wasm_float.float_convert_si64 numerics.f64m i)
  end.

Definition compile_num (num_type : rwasm.NumType) (num : nat) : wasm.value :=
  match num_type with
  | rwasm.Int _ rwasm.i32 => compile_num_from_Z wasm.T_i32 (Z.of_nat num)
  | rwasm.Int _ rwasm.i64 => compile_num_from_Z wasm.T_i64 (Z.of_nat num)
  | rwasm.Float rwasm.f32 => compile_num_from_Z wasm.T_f32 (Z.of_nat num)
  | rwasm.Float rwasm.f64 => compile_num_from_Z wasm.T_f64 (Z.of_nat num)
  end.

Definition compile_int_type (typ : rwasm.IntType) : wasm.value_type :=
  match typ with
  | rwasm.i32 => wasm.T_i32
  | rwasm.i64 => wasm.T_i64
  end.

Definition compile_float_type (typ : rwasm.FloatType) : wasm.value_type :=
  match typ with
  | rwasm.f32 => wasm.T_f32
  | rwasm.f64 => wasm.T_f64
  end.

Definition throw_missing (instr_name : string) : exn err wasm.basic_instruction :=
  mthrow (Err ("missing iris-wasm " ++ instr_name ++ " wrap instruction")).

Definition compile_num_instr (ni : rwasm.NumInstr) : exn err wasm.basic_instruction :=
  match ni with
  | rwasm.Iu typ op =>
    let typ' := compile_int_type typ in
    let op' := wasm.Unop_i match op with
    | rwasm.clz => wasm.UOI_clz
    | rwasm.ctz => wasm.UOI_ctz
    | rwasm.popcnt => wasm.UOI_popcnt
    end in
    mret $ wasm.BI_unop typ' op'
  | rwasm.Ib typ op =>
    let typ' := compile_int_type typ in
    let op' := wasm.Binop_i match op with
    | rwasm.add => wasm.BOI_add
    | rwasm.sub => wasm.BOI_sub
    | rwasm.mul => wasm.BOI_mul
    | rwasm.div s => wasm.BOI_div (compile_sign s)
    | rwasm.rem s => wasm.BOI_rem (compile_sign s)
    | rwasm.and => wasm.BOI_and
    | rwasm.or => wasm.BOI_or
    | rwasm.xor => wasm.BOI_xor
    | rwasm.shl => wasm.BOI_shl
    | rwasm.shr s => wasm.BOI_shr (compile_sign s)
    | rwasm.rotl => wasm.BOI_rotl
    | rwasm.rotr => wasm.BOI_rotr
    end in
    mret $ wasm.BI_binop typ' op'
  | rwasm.Fu typ op =>
    let typ' := compile_float_type typ in
    let op' := wasm.Unop_f match op with
    | rwasm.neg => wasm.UOF_neg
    | rwasm.abs => wasm.UOF_abs
    | rwasm.ceil => wasm.UOF_ceil
    | rwasm.floor => wasm.UOF_floor
    | rwasm.trunc => wasm.UOF_trunc
    | rwasm.nearest => wasm.UOF_nearest
    | rwasm.sqrt => wasm.UOF_sqrt
    end in
    mret $ wasm.BI_unop typ' op'
  | rwasm.Fb typ op =>
    let typ' := compile_float_type typ in
    let op' := wasm.Binop_f match op with
    | rwasm.addf => wasm.BOF_add
    | rwasm.subf => wasm.BOF_sub
    | rwasm.mulf => wasm.BOF_mul
    | rwasm.divf => wasm.BOF_div
    | rwasm.min => wasm.BOF_min
    | rwasm.max => wasm.BOF_max
    | rwasm.copysign => wasm.BOF_copysign
    end in
    mret $ wasm.BI_binop typ' op'
  | rwasm.It typ op =>
    let typ' := compile_int_type typ in
    let op' := match op with
    | rwasm.eqz => wasm.TO_eqz
    end in
    mret $ wasm.BI_testop typ' op'
  | rwasm.Ir typ op =>
    let typ' := compile_int_type typ in
    let op' := wasm.Relop_i match op with
    | rwasm.eq => wasm.ROI_eq
    | rwasm.ne => wasm.ROI_ne
    | rwasm.lt s => wasm.ROI_lt (compile_sign s)
    | rwasm.gt s => wasm.ROI_gt (compile_sign s)
    | rwasm.le s => wasm.ROI_le (compile_sign s)
    | rwasm.ge s => wasm.ROI_ge (compile_sign s)
    end in
    mret $ wasm.BI_relop typ' op'
  | rwasm.Fr typ op =>
    let typ' := compile_float_type typ in
    let op' := wasm.Relop_f match op with
    | rwasm.eqf => wasm.ROF_eq
    | rwasm.nef => wasm.ROF_ne
    | rwasm.ltf => wasm.ROF_lt
    | rwasm.gtf => wasm.ROF_gt
    | rwasm.lef => wasm.ROF_le
    | rwasm.gef => wasm.ROF_ge
    end in
    mret $ wasm.BI_relop typ' op'
  | rwasm.CvtI typ op =>
    let typ' := compile_int_type typ in
    match op with
    (* FIXME: missing wasm types *)
    | rwasm.Wrap typ2 => throw_missing "wrap"
    | rwasm.Extend typ2 s => throw_missing "extend"
    | rwasm.Trunc typ2 s => throw_missing "trunc"
    | rwasm.TruncSat typ2 s => throw_missing "trunc_sat"
    | rwasm.Convert typ2 s =>
        let typ2' := compile_int_type typ2 in
        let s' := compile_sign s in
        mret $ wasm.BI_cvtop typ' wasm.CVO_convert typ2' (Some s')
    | rwasm.Demote typ2 => throw_missing "demote"
    | rwasm.Promote typ2 => throw_missing "promote"
    | rwasm.Reinterpret typ2 =>
        let typ2' := compile_int_type typ2 in
        mret $ wasm.BI_cvtop typ' wasm.CVO_convert typ2' None
    end
  | rwasm.CvtF typ op =>
    let typ' := compile_float_type typ in
    match op with
    (* FIXME: missing wasm types *)
    | rwasm.Wrap typ2 => throw_missing "wrap"
    | rwasm.Extend typ2 s => throw_missing "extend"
    | rwasm.Trunc typ2 s => throw_missing "trunc"
    | rwasm.TruncSat typ2 s => throw_missing "trunc_sat"
    | rwasm.Convert typ2 s =>
        let typ2' := compile_int_type typ2 in
        let s' := compile_sign s in
        mret $ wasm.BI_cvtop typ' wasm.CVO_convert typ2' (Some s')
    | rwasm.Demote typ2 => throw_missing "demote"
    | rwasm.Promote typ2 => throw_missing "promote"
    | rwasm.Reinterpret typ2 =>
        let typ2' := compile_int_type typ2 in
        mret $ wasm.BI_cvtop typ' wasm.CVO_convert typ2' None
    end
  end.
