From Coq Require Import List.
Require Import mathcomp.ssreflect.seq.
Require Import stdpp.base.
Require Import stdpp.list.
Require Import stdpp.option.
Import ListNotations.
From RWasm Require term.
From Wasm Require datatypes.
Require Import Wasm.numerics.
Require Import BinNat.

Module rwasm := term.
Module wasm := datatypes.
Require Import stdpp.list.

Definition compile_numtyp (typ: rwasm.NumType) : option (wasm.value_type) :=
  match typ with
  | rwasm.Int _ rwasm.i32 => Some wasm.T_i32
  | rwasm.Int _ rwasm.i64 => Some wasm.T_i64
  | rwasm.Float rwasm.f32 => Some wasm.T_f32
  | rwasm.Float rwasm.f64 => Some wasm.T_f64
  end.

Definition compile_kindvar (κ: rwasm.KindVar) : list wasm.value_type :=
  match κ with
  | rwasm.SIZE _ _ => [wasm.T_i32]
  | _ => []
  end.

Definition compile_kindvars (κs: list rwasm.KindVar) : list wasm.value_type :=
  list_flatten (map compile_kindvar κs).

Fixpoint compile_typ (typ: rwasm.Typ) : option (list wasm.value_type) :=
  match typ with
  | rwasm.Num ntyp => wty ← compile_numtyp ntyp; mret [wty]
  | rwasm.TVar _ => mret [wasm.T_i32]
  | rwasm.Unit => mret []
  | rwasm.ProdT typs => list_flatten <$> mapM compile_typ typs
  | rwasm.CoderefT _ => None
  | rwasm.Rec _ typ => compile_typ typ
  | rwasm.PtrT _ => mret [wasm.T_i32]
  | rwasm.ExLoc q typ => compile_typ typ
  | rwasm.OwnR _ => mret []
  | rwasm.CapT _ _ _ => mret []
  | rwasm.RefT _ _ _  => mret [wasm.T_i32]
  end
with compile_heap_type (typ: rwasm.HeapType) : option unit :=
  match typ with
  | rwasm.VariantType typs => None
  | rwasm.StructType fields => None
  | rwasm.ArrayType elt_typ => None
  | rwasm.Ex sz qual typ => None
  end
with compile_arrow_type (typ: rwasm.ArrowType) : option wasm.function_type :=
  match typ with
  | rwasm.Arrow tys1 tys2 =>
    tys1' ← mapM compile_typ tys1;
    tys2' ← mapM compile_typ tys2;
    mret (wasm.Tf (flatten tys1') (flatten tys2'))
  end
with compile_fun_type (ft: rwasm.FunType) : option wasm.function_type :=
  match ft with
  | rwasm.FunT κs (rwasm.Arrow tys1 tys2) =>
    let κvs := compile_kindvars κs in
    tys1' ← list_flatten <$> mapM compile_typ tys1;
    tys2' ← list_flatten <$> mapM compile_typ tys2;
    mret (wasm.Tf (κvs ++ tys1') tys2')
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

Fixpoint compile_value (value : rwasm.Value) : option (list wasm.value) :=
  match value with 
  | rwasm.NumConst num_type num => Some [compile_num num_type num]
  | rwasm.Tt => None
  | rwasm.Coderef module_idx table_idx idxs => None
  | rwasm.Fold val => None
  | rwasm.Prod vals => flatten <$> mapM compile_value vals
  | rwasm.Ref loc => None
  | rwasm.PtrV loc => None
  | rwasm.Cap => None
  | rwasm.Own => None
  | rwasm.Mempack loc val => None
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

Definition compile_sign (s : rwasm.Sign) : wasm.sx :=
  match s with
  | rwasm.U => wasm.SX_U
  | rwasm.S => wasm.SX_S
  end.

Definition compile_num_intr (ni : rwasm.NumInstr) : option wasm.basic_instruction :=
  match ni with
  | rwasm.Iu typ op =>
    let typ' := compile_int_type typ in
    let op' := wasm.Unop_i match op with
    | rwasm.clz => wasm.UOI_clz
    | rwasm.ctz => wasm.UOI_ctz
    | rwasm.popcnt => wasm.UOI_popcnt
    end in
    Some (wasm.BI_unop typ' op')
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
    Some (wasm.BI_binop typ' op')
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
    Some (wasm.BI_unop typ' op')
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
    Some (wasm.BI_binop typ' op')
  | rwasm.It typ op =>
    let typ' := compile_int_type typ in
    let op' := match op with
    | rwasm.eqz => wasm.TO_eqz
    end in
    Some (wasm.BI_testop typ' op')
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
    Some (wasm.BI_relop typ' op')
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
    Some (wasm.BI_relop typ' op')
  | rwasm.CvtI typ op =>
    let typ' := compile_int_type typ in
    match op with
    (* FIXME: missing wasm types *)
    | rwasm.Wrap typ2 => None
    | rwasm.Extend typ2 s => None
    | rwasm.Trunc typ2 s => None
    | rwasm.TruncSat typ2 s => None
    | rwasm.Convert typ2 s =>
        let typ2' := compile_int_type typ2 in
        let s' := compile_sign s in
        Some (wasm.BI_cvtop typ' wasm.CVO_convert typ2' (Some s'))
    | rwasm.Demote typ2 => None
    | rwasm.Promote typ2 => None
    | rwasm.Reinterpret typ2 =>
        let typ2' := compile_int_type typ2 in
        Some (wasm.BI_cvtop typ' wasm.CVO_convert typ2' None)
    end
  | rwasm.CvtF typ op =>
    let typ' := compile_float_type typ in
    match op with
    (* FIXME: missing wasm types *)
    | rwasm.Wrap typ2 => None
    | rwasm.Extend typ2 s => None
    | rwasm.Trunc typ2 s => None
    | rwasm.TruncSat typ2 s => None
    | rwasm.Convert typ2 s =>
        let typ2' := compile_int_type typ2 in
        let s' := compile_sign s in
        Some (wasm.BI_cvtop typ' wasm.CVO_convert typ2' (Some s'))
    | rwasm.Demote typ2 => None
    | rwasm.Promote typ2 => None
    | rwasm.Reinterpret typ2 =>
        let typ2' := compile_int_type typ2 in
        Some (wasm.BI_cvtop typ' wasm.CVO_convert typ2' None)
    end
  end.

Definition expect_concrete_size (sz: rwasm.Size) : option nat :=
  match sz with
  | rwasm.SizeConst c => mret c
  | _ => None
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

(* n.b. this is polymorphic :( *)
Fixpoint struct_field_offset (fields: list (rwasm.Typ * rwasm.Size)) (idx: nat) : option rwasm.Size :=
  match idx with
  | 0 => mret $ rwasm.SizeConst 0
  | S idx' =>
      match fields with
      | (_, sz) :: fields' => rwasm.SizePlus sz <$> (struct_field_offset fields' idx')
      | [] => None
      end
  end.

(* Produces code that given a frame with sizes according to size_ctx
   computes one i32, which is the concrete value of sz at run time. *)
Fixpoint compile_size_expr (sz: rwasm.Size) : option (list wasm.basic_instruction) :=
  match sz with
  | rwasm.SizeVar σ =>
      l_idx ← sz_locs !! σ;
      mret [wasm.BI_get_local l_idx]
  | rwasm.SizePlus sz sz' =>
      e ← compile_size_expr sz;
      e' ← compile_size_expr sz';
      mret (e ++ e' ++ [wasm.BI_binop wasm.T_i32 (wasm.Binop_i wasm.BOI_add)])
  | rwasm.SizeConst n =>
      mret [wasm.BI_const (wasm.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat n)))]
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

Fixpoint compile_instr (instr: rwasm.basic_instr rwasm.ArrowType) : option (list wasm.basic_instruction) :=
  match instr with
  | rwasm.Val (rwasm.Arrow targs trets) x => option_map (map (fun y => wasm.BI_const y)) (compile_value x)
  | rwasm.Ne (rwasm.Arrow targs trets) x => None
  | rwasm.Unreachable (rwasm.Arrow targs trets) => Some [wasm.BI_unreachable]
  | rwasm.Nop (rwasm.Arrow targs trets) => Some [wasm.BI_nop]
  | rwasm.Drop (rwasm.Arrow targs trets) => Some [wasm.BI_drop]
  | rwasm.Select (rwasm.Arrow targs trets) => Some [wasm.BI_select]
  | rwasm.Block (rwasm.Arrow targs trets) arrow _ i =>
    ft ← compile_arrow_type arrow;
    i' ← mapM compile_instr i;
    mret [wasm.BI_block ft (flatten i')]
  | rwasm.Loop (rwasm.Arrow targs trets) arrow i =>
    ft ← compile_arrow_type arrow;
    i' ← mapM compile_instr i;
    mret [wasm.BI_block ft (flatten i')]
  | rwasm.ITE (rwasm.Arrow targs trets) arrow _ t e =>
    ft ← compile_arrow_type arrow;
    t' ← mapM compile_instr t;
    e' ← mapM compile_instr e;
    mret [wasm.BI_if ft (flatten t') (flatten e')]
  | rwasm.Br (rwasm.Arrow targs trets) x => Some [wasm.BI_br x]
  | rwasm.Br_if (rwasm.Arrow targs trets) x => Some [wasm.BI_br_if x]
  | rwasm.Br_table (rwasm.Arrow targs trets) x x0 => Some [wasm.BI_br_table x x0]
  | rwasm.Ret (rwasm.Arrow targs trets) => Some [wasm.BI_return]
  | rwasm.Get_local (rwasm.Arrow targs trets) x x0 => Some [wasm.BI_get_local x]
  | rwasm.Set_local (rwasm.Arrow targs trets) x => Some [wasm.BI_set_local x]
  | rwasm.Tee_local (rwasm.Arrow targs trets) x => Some [wasm.BI_tee_local x]
  | rwasm.Get_global (rwasm.Arrow targs trets) x => Some [wasm.BI_get_global x]
  | rwasm.Set_global (rwasm.Arrow targs trets) x => Some [wasm.BI_set_global x]
  | rwasm.CoderefI (rwasm.Arrow targs trets) x => None
  | rwasm.Inst (rwasm.Arrow targs trets) x => None
  | rwasm.Call_indirect (rwasm.Arrow targs trets) => None (* TODO: why doesn't rwasm take an immediate? *)
  | rwasm.Call (rwasm.Arrow targs trets) x x0 => None     (* TODO: what to do with list of indexes? *)
  | rwasm.RecFold (rwasm.Arrow targs trets) x => None
  | rwasm.RecUnfold (rwasm.Arrow targs trets) => None
  | rwasm.Group (rwasm.Arrow targs trets) x x0 => None
  | rwasm.Ungroup (rwasm.Arrow targs trets) => None
  | rwasm.CapSplit (rwasm.Arrow targs trets) => None
  | rwasm.CapJoin (rwasm.Arrow targs trets) => None
  | rwasm.RefDemote (rwasm.Arrow targs trets) => None
  | rwasm.MemPack (rwasm.Arrow targs trets) x => None
  | rwasm.MemUnpack (rwasm.Arrow targs trets) x x0 x1 => None
  | rwasm.StructMalloc (rwasm.Arrow targs trets) x x0 => None
  | rwasm.StructFree (rwasm.Arrow targs trets) => None
  | rwasm.StructGet (rwasm.Arrow targs trets) idx =>
      (* Save the argument *)
      (* typ should be [ref l (structtype fields)] -> [ref l (structtype fields); tau_field] *)
      fields ← match targs with
                | [rwasm.RefT _ _ (rwasm.StructType fields)] => Some fields
                | _ => None
                end;
      off_sz ← struct_field_offset fields idx;
      off_instrs ← compile_size_expr off_sz;
      mret $ wasm.BI_tee_local ref_tmp ::
             tagged_load ref_tmp off_instrs
  | rwasm.StructSet (rwasm.Arrow targs trets) x => None
  | rwasm.StructSwap (rwasm.Arrow targs trets) x => None
  | rwasm.VariantMalloc (rwasm.Arrow targs trets) x x0 x1 => None
  | rwasm.VariantCase (rwasm.Arrow targs trets) x x0 x1 x2 x3 => None
  | rwasm.ArrayMalloc (rwasm.Arrow targs trets) x => None
  | rwasm.ArrayGet (rwasm.Arrow targs trets) => None
  | rwasm.ArraySet (rwasm.Arrow targs trets) => None
  | rwasm.ArrayFree (rwasm.Arrow targs trets) => None
  | rwasm.ExistPack (rwasm.Arrow targs trets) x x0 x1 => None
  | rwasm.ExistUnpack (rwasm.Arrow targs trets) x x0 x1 x2 x3 => None
  | rwasm.RefSplit (rwasm.Arrow targs trets) => None
  | rwasm.RefJoin (rwasm.Arrow targs trets) => None
  | rwasm.Qualify (rwasm.Arrow targs trets) x => None
  end.
(* ... *)

End compile_instr.

Definition compile_fun_type_idx (fun_type : rwasm.FunType) : wasm.typeidx.
Admitted.

Fixpoint compile_module (module : rwasm.module rwasm.ArrowType) : option wasm.module :=
  let '(funcs, globs, table) := module return option wasm.module in
  Some {|
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

with compile_glob (glob : rwasm.Glob rwasm.ArrowType) : option wasm.module_glob
with compile_table (table : rwasm.Table) : option wasm.module_table.
Admitted.
