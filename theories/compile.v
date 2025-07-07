From Coq Require Import List.
Require Import mathcomp.ssreflect.seq.
Require Import stdpp.base.
Require Import stdpp.strings.
Require Import stdpp.pretty.
Require Import stdpp.list.
Import ListNotations.
From RWasm Require term.
From Wasm Require datatypes.
Require Import Wasm.numerics.
Require Import BinNat.
Require Import compiler.monads.

Module rwasm := term.
Module wasm := datatypes.
Require Import stdpp.list.

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

Definition compile_numtyp (typ: rwasm.NumType) : wasm.value_type :=
  match typ with
  | rwasm.Int _ inttyp => compile_int_type inttyp
  | rwasm.Float floattyp => compile_float_type floattyp
  end.

Definition compile_kindvar (κ: rwasm.KindVar) : list wasm.value_type :=
  match κ with
  | rwasm.SIZE _ _ => [wasm.T_i32]
  | _ => []
  end.

Definition compile_kindvars (κs: list rwasm.KindVar) : list wasm.value_type :=
  flat_map compile_kindvar κs.

Fixpoint compile_typ (typ: rwasm.Typ) : exn err (list wasm.value_type) :=
  match typ with
  | rwasm.Num ntyp => mret [compile_numtyp ntyp]
  | rwasm.TVar _ => mret [wasm.T_i32]
  | rwasm.Unit => mret []
  | rwasm.ProdT typs => flatten <$> mapM compile_typ typs
  | rwasm.CoderefT _ => mthrow Todo
  | rwasm.Rec _ typ => compile_typ typ
  | rwasm.PtrT _ => mret [wasm.T_i32]
  | rwasm.ExLoc q typ => compile_typ typ
  | rwasm.OwnR _ => mret []
  | rwasm.CapT _ _ _ => mret []
  | rwasm.RefT _ _ _  => mret [wasm.T_i32]
  end
with compile_heap_type (typ: rwasm.HeapType) : exn err unit :=
  match typ with
  | rwasm.VariantType typs => mthrow Todo
  | rwasm.StructType fields => mthrow Todo
  | rwasm.ArrayType elt_typ => mthrow Todo
  | rwasm.Ex sz qual typ => mthrow Todo
  end
with compile_arrow_type (typ: rwasm.ArrowType) : exn err wasm.function_type :=
  match typ with
  | rwasm.Arrow tys1 tys2 =>
    tys1' ← mapM compile_typ tys1;
    tys2' ← mapM compile_typ tys2;
    mret (wasm.Tf (flatten tys1') (flatten tys2'))
  end
with compile_fun_type (ft: rwasm.FunType) : exn err wasm.function_type :=
  match ft with
  | rwasm.FunT κs (rwasm.Arrow tys1 tys2) =>
    let κvs := compile_kindvars κs in
    tys1' ← flatten <$> mapM compile_typ tys1;
    tys2' ← flatten <$> mapM compile_typ tys2;
    mret (wasm.Tf (κvs ++ tys1') tys2')
  end.

Definition compile_sign (s : rwasm.Sign) : wasm.sx :=
  match s with
  | rwasm.U => wasm.SX_U
  | rwasm.S => wasm.SX_S
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

Definition compile_num (num_type : rwasm.NumType) (num : nat) : wasm.value :=
  match num_type with
  | rwasm.Int _ rwasm.i32 => 
    wasm.VAL_int32 (Wasm_int.int_of_Z numerics.i32m (Z.of_nat num))
  | rwasm.Int _ rwasm.i64 => 
    wasm.VAL_int64 (Wasm_int.int_of_Z numerics.i64m (Z.of_nat num))
  (* is the signed converter the right thing to use here? *)
  | rwasm.Float rwasm.f32 =>
    wasm.VAL_float32 
      ((Wasm_float.float_convert_si32
        numerics.f32m (Wasm_int.int_of_Z numerics.i32m (Z.of_nat num))))
  | rwasm.Float rwasm.f64 =>
    wasm.VAL_float64
      ((Wasm_float.float_convert_si64
        numerics.f64m (Wasm_int.int_of_Z numerics.i64m (Z.of_nat num))))
  end.

Definition compile_num_intr (ni : rwasm.NumInstr) : exn err wasm.basic_instruction :=
  match ni with
  | rwasm.Iu typ op =>
    let typ' := compile_int_type typ in
    let op' := wasm.Unop_i match op with
    | rwasm.clz => wasm.UOI_clz
    | rwasm.ctz => wasm.UOI_ctz
    | rwasm.popcnt => wasm.UOI_popcnt
    end in
    mret (wasm.BI_unop typ' op')
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
    mret (wasm.BI_binop typ' op')
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
    mret (wasm.BI_unop typ' op')
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
    mret (wasm.BI_binop typ' op')
  | rwasm.It typ op =>
    let typ' := compile_int_type typ in
    let op' := match op with
    | rwasm.eqz => wasm.TO_eqz
    end in
    mret (wasm.BI_testop typ' op')
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
    mret (wasm.BI_relop typ' op')
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
    mret (wasm.BI_relop typ' op')
  | rwasm.CvtI typ op =>
    let typ' := compile_int_type typ in
    match op with
    (* FIXME: missing wasm types *)
    | rwasm.Wrap typ2 => mthrow Todo
    | rwasm.Extend typ2 s => mthrow Todo
    | rwasm.Trunc typ2 s => mthrow Todo
    | rwasm.TruncSat typ2 s => mthrow Todo
    | rwasm.Convert typ2 s =>
        let typ2' := compile_int_type typ2 in
        let s' := compile_sign s in
        mret (wasm.BI_cvtop typ' wasm.CVO_convert typ2' (Some s'))
    | rwasm.Demote typ2 => mthrow Todo
    | rwasm.Promote typ2 => mthrow Todo
    | rwasm.Reinterpret typ2 =>
        let typ2' := compile_int_type typ2 in
        mret (wasm.BI_cvtop typ' wasm.CVO_convert typ2' None)
    end
  | rwasm.CvtF typ op =>
    let typ' := compile_float_type typ in
    match op with
    (* FIXME: missing wasm types *)
    | rwasm.Wrap typ2 => mthrow Todo
    | rwasm.Extend typ2 s => mthrow Todo
    | rwasm.Trunc typ2 s => mthrow Todo
    | rwasm.TruncSat typ2 s => mthrow Todo
    | rwasm.Convert typ2 s =>
        let typ2' := compile_int_type typ2 in
        let s' := compile_sign s in
        mret (wasm.BI_cvtop typ' wasm.CVO_convert typ2' (Some s'))
    | rwasm.Demote typ2 => mthrow Todo
    | rwasm.Promote typ2 => mthrow Todo
    | rwasm.Reinterpret typ2 =>
        let typ2' := compile_int_type typ2 in
        mret (wasm.BI_cvtop typ' wasm.CVO_convert typ2' None)
    end
  end.

Definition expect_concrete_size (sz: rwasm.Size) : exn err nat :=
  match sz with
  | rwasm.SizeConst c => mret c
  | _ => mthrow (Err "expected concrete size")
  end.

(* Mapping from size variables to indices of locals of type i32 *)
Definition size_ctx := 
  list wasm.immediate.
Section compile_instr.
Variable (sz_locs: size_ctx).
(* i32 local for hanging on to linear references during stores/loads *)
Variable (ref_tmp: wasm.immediate).
Variable (GC_MEM: wasm.immediate).
Variable (LIN_MEM: wasm.immediate).

Fixpoint struct_field_offset (fields: list (rwasm.Typ * rwasm.Size)) (idx: nat) : exn err rwasm.Size :=
  match idx with
  | 0 => mret $ rwasm.SizeConst 0
  | S idx' =>
      match fields with
      | (_, sz) :: fields' => rwasm.SizePlus sz <$> (struct_field_offset fields' idx')
      | [] => mthrow Todo
      end
  end.

Fixpoint compile_sz (sz : rwasm.Size) : exn err (list wasm.basic_instruction) :=
  match sz with
  | rwasm.SizeVar σ =>
    local_idx ← err_opt (sz_locs !! σ) ("sz " ++ (pretty σ) ++ " not found in sz_local_map");
    mret [wasm.BI_get_local local_idx]
  | rwasm.SizePlus sz1 sz2 =>
    e1 ← compile_sz sz1;
    e2 ← compile_sz sz2;
    mret $ e1 ++ e2 ++ [wasm.BI_binop wasm.T_i32 (wasm.Binop_i wasm.BOI_add)]
  | rwasm.SizeConst c =>
    mret [wasm.BI_const (wasm.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat c)))]
  end.

Definition get_struct_field_types (targs : list rwasm.Typ) (idx : nat) : exn err (list (rwasm.Typ * rwasm.Size)) :=
  match targs !! idx with
  | Some (rwasm.RefT _ _ (rwasm.StructType fields)) => mret fields
  | _ => mthrow (Err ("struct instruction expected type-args to be a ref to a struct at index " ++ pretty idx))
  end.

  Definition get_array_elem_type (targs : list rwasm.Typ) (idx : nat) : exn err rwasm.Typ :=
    match targs !! idx with
    | Some (rwasm.RefT _ _ (rwasm.ArrayType typ)) => mret typ
    | _ => mthrow (Err ("array instruction expected a ref to an array type at index " ++ pretty idx))
    end.

Definition if_gc_bit_set ref_tmp ins outs gc_branch lin_branch :=
  [wasm.BI_get_local ref_tmp;
   wasm.BI_const (wasm.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 1%Z));
   wasm.BI_binop wasm.T_i32 (wasm.Binop_i wasm.BOI_and);
   wasm.BI_testop wasm.T_i32 wasm.TO_eqz;
   wasm.BI_if (wasm.Tf ins outs) lin_branch gc_branch].

Definition unset_gc_bit :=
  [wasm.BI_const (wasm.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 1%Z));
   wasm.BI_binop wasm.T_i32 (wasm.Binop_i wasm.BOI_sub)].

Definition tagged_load ref_tmp offset_instrs :=
  if_gc_bit_set ref_tmp [] [wasm.T_i32 (* loaded value *)]
  ([wasm.BI_get_local ref_tmp] ++
   unset_gc_bit ++
   offset_instrs ++ 
   [wasm.BI_binop wasm.T_i32 (wasm.Binop_i wasm.BOI_add);
    wasm.BI_load GC_MEM wasm.T_i32 None 0%N 0%N])
  ([wasm.BI_get_local ref_tmp] ++
   offset_instrs ++ 
   [wasm.BI_binop wasm.T_i32 (wasm.Binop_i wasm.BOI_add);
    wasm.BI_load LIN_MEM wasm.T_i32 None 0%N 0%N]).

Fixpoint compile_instr (instr: rwasm.instr rwasm.ArrowType) : exn err (list wasm.basic_instruction) :=
  match instr with
  | rwasm.INumConst _ num_type num => mret [wasm.BI_const $ compile_num num_type num]
  | rwasm.IUnit _ => mret []
  | rwasm.INum (rwasm.Arrow targs trets) num_instr =>
      e ← compile_num_instr num_instr; mret [e]
  | rwasm.IUnreachable (rwasm.Arrow targs trets) => mret [wasm.BI_unreachable]
  | rwasm.INop (rwasm.Arrow targs trets) => mret [wasm.BI_nop]
  | rwasm.IDrop (rwasm.Arrow targs  trets) =>
      match targs with
      | (t_drop :: targs) =>
        wasm_typ ← compile_typ t_drop;
        mret $ map (const wasm.BI_drop) wasm_typ
      | [] => 
        mthrow (Err "rwasm.IDrop should have a nonempty stack type annotation")
      end
  | rwasm.ISelect (rwasm.Arrow targs trets) => mret [wasm.BI_select]
  | rwasm.IBlock (rwasm.Arrow targs trets) arrow _ i =>
    ft ← compile_arrow_type arrow;
    i' ← mapM compile_instr i;
    mret [wasm.BI_block ft (flatten i')]
  | rwasm.ILoop (rwasm.Arrow targs trets) arrow i =>
    ft ← compile_arrow_type arrow;
    i' ← mapM compile_instr i;
    mret [wasm.BI_block ft (flatten i')]
  | rwasm.IIte (rwasm.Arrow targs trets) arrow _ t e =>
    ft ← compile_arrow_type arrow;
    t' ← mapM compile_instr t;
    e' ← mapM compile_instr e;
    mret [wasm.BI_if ft (flatten t') (flatten e')]
  | rwasm.IBr (rwasm.Arrow targs trets) x => mret [wasm.BI_br x]
  | rwasm.IBrIf (rwasm.Arrow targs trets) x => mret [wasm.BI_br_if x]
  | rwasm.IBrTable (rwasm.Arrow targs trets) x x0 => mret [wasm.BI_br_table x x0]
  | rwasm.IRet (rwasm.Arrow targs trets) => mret [wasm.BI_return]
  | rwasm.IGetLocal (rwasm.Arrow targs trets) x x0 => mret [wasm.BI_get_local x]
  | rwasm.ISetLocal (rwasm.Arrow targs trets) x => mret [wasm.BI_set_local x]
  | rwasm.ITeeLocal (rwasm.Arrow targs trets) x => mret [wasm.BI_tee_local x]
  | rwasm.IGetGlobal (rwasm.Arrow targs trets) x => mret [wasm.BI_get_global x]
  | rwasm.ISetGlobal (rwasm.Arrow targs trets) x => mret [wasm.BI_set_global x]
  | rwasm.ICoderef (rwasm.Arrow targs trets) x => mthrow Todo
  | rwasm.IInst (rwasm.Arrow targs trets) x => mthrow Todo
  | rwasm.ICallIndirect (rwasm.Arrow targs trets) => mthrow Todo (* TODO: why doesn't rwasm take an immediate? *)
  | rwasm.ICall (rwasm.Arrow targs trets) x x0 => mthrow Todo     (* TODO: what to do with list of indexes? *)
  | rwasm.IRecFold (rwasm.Arrow targs trets) x => mthrow Todo
  | rwasm.IRecUnfold (rwasm.Arrow targs trets) => mthrow Todo
  | rwasm.IGroup (rwasm.Arrow targs trets) x x0 => mthrow Todo
  | rwasm.IUngroup (rwasm.Arrow targs trets) => mthrow Todo
  | rwasm.ICapSplit (rwasm.Arrow targs trets) => mthrow Todo
  | rwasm.ICapJoin (rwasm.Arrow targs trets) => mthrow Todo
  | rwasm.IRefDemote (rwasm.Arrow targs trets) => mthrow Todo
  | rwasm.IMemPack (rwasm.Arrow targs trets) x => mthrow Todo
  | rwasm.IMemUnpack (rwasm.Arrow targs trets) x x0 x1 => mthrow Todo
  | rwasm.IStructMalloc (rwasm.Arrow targs trets) x x0 => mthrow Todo
  | rwasm.IStructFree (rwasm.Arrow targs trets) => mthrow Todo
  | rwasm.IStructGet (rwasm.Arrow targs trets) idx =>
      (* Save the argument *)
      (* typ should be [ref l (structtype fields)] -> [ref l (structtype fields); tau_field] *)
      fields ← match targs with
                | [rwasm.RefT _ _ (rwasm.StructType fields)] => mret fields
                | _ => mthrow Todo
                end;
      off_sz ← struct_field_offset fields idx;
      off_instrs ← compile_sz off_sz;
      mret $ wasm.BI_tee_local ref_tmp ::
             tagged_load ref_tmp off_instrs
  | rwasm.IStructSet (rwasm.Arrow targs trets) x => mthrow Todo
  | rwasm.IStructSwap (rwasm.Arrow targs trets) x => mthrow Todo
  | rwasm.IVariantMalloc (rwasm.Arrow targs trets) x x0 x1 => mthrow Todo
  | rwasm.IVariantCase (rwasm.Arrow targs trets) x x0 x1 x2 x3 => mthrow Todo
  | rwasm.IArrayMalloc (rwasm.Arrow targs trets) x => mthrow Todo
  | rwasm.IArrayGet (rwasm.Arrow targs trets) => mthrow Todo
  | rwasm.IArraySet (rwasm.Arrow targs trets) => mthrow Todo
  | rwasm.IArrayFree (rwasm.Arrow targs trets) => mthrow Todo
  | rwasm.IExistPack (rwasm.Arrow targs trets) x x0 x1 => mthrow Todo
  | rwasm.IExistUnpack (rwasm.Arrow targs trets) x x0 x1 x2 x3 => mthrow Todo
  | rwasm.IRefSplit (rwasm.Arrow targs trets) => mthrow Todo
  | rwasm.IRefJoin (rwasm.Arrow targs trets) => mthrow Todo
  | rwasm.IQualify (rwasm.Arrow targs trets) x => mthrow Todo
  end.

Definition compile_instrs instrs := flatten <$> mapM compile_instr instrs.

End compile_instr.

Definition compile_fun_type_idx (fun_type : rwasm.FunType) : wasm.typeidx.
Admitted.

Fixpoint compile_module (module : rwasm.module rwasm.ArrowType) : exn err wasm.module :=
  let '(funcs, globs, table) := module return exn err wasm.module in
  mret {|
    wasm.mod_types := []; (* TODO *)
    wasm.mod_funcs := []; (* TODO *)
    wasm.mod_tables := []; (* TODO *)
    wasm.mod_mems := []; (* TODO *)
    wasm.mod_globals := []; (* TODO *)
    wasm.mod_elem := []; (* TODO *)
    wasm.mod_data := []; (* TODO *)
    wasm.mod_start := None; (* TODO *)
    wasm.mod_imports := []; (* TODO *)
    wasm.mod_exports := [] (* TODO *)
  |}

(* TODO: modfunc_type expects a typeidx while rwasm does this inline *)
with compile_func (func : rwasm.Func rwasm.ArrowType) : option wasm.module_func := 
  match func with 
  | rwasm.Fun exports fun_type sizes intrs =>
    Some {|
      wasm.modfunc_type := compile_fun_type_idx fun_type;
      wasm.modfunc_locals := []; (* TODO *)
      wasm.modfunc_body := []; (* TODO *)
    |}
  end

with compile_glob (glob : rwasm.Glob rwasm.ArrowType) : exn err wasm.module_glob
with compile_table (table : rwasm.Table) : exn err wasm.module_table.
Admitted.
