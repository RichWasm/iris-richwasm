From Coq Require Import List NArith.BinNat.
From stdpp Require Import base option strings list pretty gmap gmultiset fin_sets.
From RWasm Require term annotated_term.
From RWasm Require Import exn state.
From Wasm Require datatypes.
From Wasm Require Import datatypes numerics.


(* ExtLib has its own state monad but it doens't play nicely with stdpp *)
Definition state (S A : Type) : Type := S -> (S * A).

(* Not great but ok for now *)
Inductive Err :=
| err (msg: string).

(* The compiler monad. *)
Definition M := exn Err.

Definition mlookup_with_msg {A} (idx: nat) (lst: list A) (msg: string) : M A :=
  match list_lookup idx lst with
  | Some x => mret x
  | None => mthrow (err msg)
  end.

Module rwasm := term.
Module AR := annotated_term.
Module wasm := datatypes.

Fixpoint compile_numtyp (typ: rwasm.NumType) : M (wasm.value_type) :=
  match typ with
  | rwasm.Int _ rwasm.i32 => mret wasm.T_i32
  | rwasm.Int _ rwasm.i64 => mret wasm.T_i64
  | rwasm.Float rwasm.f32 => mret wasm.T_f32
  | rwasm.Float rwasm.f64 => mret wasm.T_f64
  end.

Fixpoint compile_typ (typ: rwasm.Typ) : M (list wasm.value_type) :=
  match typ with
  | rwasm.Num ntyp => wty ← compile_numtyp ntyp; mret [wty]
  | rwasm.TVar x => mthrow (err "todo")
  | rwasm.ProdT typs =>
      typs' ← mapM (fun x => compile_typ x) typs;
      mret (concat typs')
  | rwasm.PtrT _
  | rwasm.RefT _ _ _
  | rwasm.CoderefT _ => mret [wasm.T_i32]
  | rwasm.Rec _ typ => compile_typ typ
  | rwasm.ExLoc q x => mthrow (err "todo")
  | rwasm.Unit
  | rwasm.OwnR _
  | rwasm.CapT _ _ _ => mret []
  end
with compile_heap_type (typ: rwasm.HeapType) : M unit :=
  match typ with
  | rwasm.VariantType typs => mthrow (err "todo")
  | rwasm.StructType fields => mthrow (err "todo")
  | rwasm.ArrayType elt_typ => mthrow (err "todo")
  | rwasm.Ex sz qual typ => mthrow (err "todo")
  end
with compile_arrow_type (typ: rwasm.ArrowType) : M wasm.function_type :=
  match typ with
  | rwasm.Arrow tys1 tys2 =>
    tys1' ← mapM compile_typ tys1;
    tys2' ← mapM compile_typ tys2;
    mret (wasm.Tf (mjoin tys1') (mjoin tys2'))
  end
with compile_fun_type (typ: rwasm.FunType) : M wasm.function_type :=
 match typ with
 | rwasm.FunT kinds arrow => mthrow (err "todo")
 end. (* What to do about generics? *)

Definition compile_num_from_Z (num_type : wasm.value_type) (num : Z) : wasm.value :=
  match num_type with
  | wasm.T_i32 => wasm.VAL_int32 (Wasm_int.int_of_Z numerics.i32m num)
  | wasm.T_i64 => wasm.VAL_int64 (Wasm_int.int_of_Z numerics.i64m num)
  (* TODO: is the signed converter the right thing to use here? *)
  | wasm.T_f32 =>
    let i := Wasm_int.int_of_Z numerics.i32m num in
    wasm.VAL_float32 (Wasm_float.float_convert_si32 numerics.f32m i)
  | wasm.T_f64 =>
    let i := Wasm_int.int_of_Z numerics.i64m num in
    wasm.VAL_float64 (Wasm_float.float_convert_si64 numerics.f64m i)
  end.

Definition compile_num (num_type : rwasm.NumType) (num : nat) : wasm.value :=
  match num_type with
  (* TODO?: signs *)
  | rwasm.Int _ rwasm.i32 => compile_num_from_Z wasm.T_i32 (Z.of_nat num)
  | rwasm.Int _ rwasm.i64 => compile_num_from_Z wasm.T_i64 (Z.of_nat num)
  | rwasm.Float rwasm.f32 => compile_num_from_Z wasm.T_f32 (Z.of_nat num)
  | rwasm.Float rwasm.f64 => compile_num_from_Z wasm.T_f64 (Z.of_nat num)
  end.

Fixpoint compile_value (value : rwasm.Value) : M (list wasm.value) :=
  match value with 
  | rwasm.NumConst num_type num => mret [(compile_num num_type num)]
  | rwasm.Tt => mthrow (err "todo")
  | rwasm.Coderef module_idx table_idx idxs => mthrow (err "todo")
  | rwasm.Fold val => mthrow (err "todo")
  | rwasm.Prod vals => mthrow (err "todo")
  | rwasm.Ref loc => mthrow (err "todo")
  | rwasm.PtrV loc => mthrow (err "todo")
  | rwasm.Cap
  | rwasm.Own => mret []
  | rwasm.Mempack loc val => mthrow (err "todo")
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

Definition compile_num_intr (ni : rwasm.NumInstr) : M wasm.basic_instruction :=
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
    | rwasm.Wrap typ2 => mthrow (err "todo")
    | rwasm.Extend typ2 s => mthrow (err "todo")
    | rwasm.Trunc typ2 s => mthrow (err "todo")
    | rwasm.TruncSat typ2 s => mthrow (err "todo")
    | rwasm.Convert typ2 s =>
        let typ2' := compile_int_type typ2 in
        let s' := compile_sign s in
        mret $ wasm.BI_cvtop typ' wasm.CVO_convert typ2' (Some s')
    | rwasm.Demote typ2 => mthrow (err "todo")
    | rwasm.Promote typ2 => mthrow (err "todo")
    | rwasm.Reinterpret typ2 =>
        let typ2' := compile_int_type typ2 in
        mret $ wasm.BI_cvtop typ' wasm.CVO_convert typ2' None
    end
  | rwasm.CvtF typ op =>
    let typ' := compile_float_type typ in
    match op with
    (* FIXME: missing wasm types *)
    | rwasm.Wrap typ2 => mthrow (err "todo")
    | rwasm.Extend typ2 s => mthrow (err "todo")
    | rwasm.Trunc typ2 s => mthrow (err "todo")
    | rwasm.TruncSat typ2 s => mthrow (err "todo")
    | rwasm.Convert typ2 s =>
        let typ2' := compile_int_type typ2 in
        let s' := compile_sign s in
        mret $ wasm.BI_cvtop typ' wasm.CVO_convert typ2' (Some s')
    | rwasm.Demote typ2 => mthrow (err "todo")
    | rwasm.Promote typ2 => mthrow (err "todo")
    | rwasm.Reinterpret typ2 =>
        let typ2' := compile_int_type typ2 in
        mret $ wasm.BI_cvtop typ' wasm.CVO_convert typ2' None
    end
  end.

Definition expect_concrete_size (sz: rwasm.Size) : M nat :=
  match sz with
  | rwasm.SizeConst c => mret c
  | _ => mthrow (err "todo")
  end.

(* Mapping from size variables to indices of locals of type i32 *)
Definition size_ctx := 
  list wasm.immediate.
Section compile_instr.
Definition modify_st (f : TempLocals → TempLocals)  : InstM unit := mmodify f.
Definition lift_M {A} (m : M A) : InstM A :=
  λ st,
    x ← m;
    mret (st, x).
Definition fresh_local (ty : wasm.value_type) : InstM wasm.immediate :=
  st ← get_st;
  match elements (tl_free st) with
  | i :: _ =>
    let st' :=
      {| tl_start := tl_start st;
         tl_next  := tl_next st;
         tl_types := <[ i := ty ]> (tl_types st);
         tl_free  := tl_free st ∖ {[ i ]} |} in
    put_st st';;
    mret i
  | [] =>
    let i := tl_next st in
    let st' :=
      {| tl_start := tl_start st;
         tl_next  := S i;
         tl_types := <[ i := ty ]> (tl_types st);
         tl_free  := tl_free st |} in
    put_st st';;
    mret i
  end.
Definition free_local (i : wasm.immediate) : InstM unit :=
  modify_st (λ st, {| tl_start := tl_start st;
                      tl_next  := tl_next  st;
                      tl_types := tl_types st;
                      tl_free  := tl_free  st ∪ {[ i ]} |}).

Variable (sz_locs: size_ctx).
(* i32 local for hanging on to linear references during stores/loads *)
Variable (GC_MEM: wasm.immediate).
Variable (LIN_MEM: wasm.immediate).

Definition size_of_wasm_typ_offset (typ : wasm.value_type) : Z :=
  match typ with
  | wasm.T_i32 => 32%Z
  | wasm.T_i64 => 64%Z
  | wasm.T_f32 => 32%Z
  | wasm.T_f64 => 64%Z
  end.

(* n.b. this is polymorphic :( *)
Fixpoint struct_field_offset (fields: list (rwasm.Typ * rwasm.Size)) (idx: nat) : InstM rwasm.Size :=
  match idx with
  | 0 => mret $ rwasm.SizeConst 0
  | S idx' =>
      match fields with
      | (_, sz) :: fields' => rwasm.SizePlus sz <$> (struct_field_offset fields' idx')
      | [] => mthrow (err ("not enough fields in struct type to find field offset of index " ++ pretty idx))
      end
  end.

(* Produces code that given a frame with sizes according to size_ctx
   computes one i32, which is the concrete value of sz at run time. *)
Fixpoint compile_size_expr (sz: rwasm.Size) : InstM (list wasm.basic_instruction) :=
  match sz with
  | rwasm.SizeVar σ =>
      l_idx ← lift_M (guard_opt (err "sz not found in sz_locs") $ sz_locs !! σ);
      mret [wasm.BI_get_local l_idx]
  | rwasm.SizePlus sz sz' =>
      e ← compile_size_expr sz;
      e' ← compile_size_expr sz';
      mret (e ++ e' ++ [wasm.BI_binop wasm.T_i32 (wasm.Binop_i wasm.BOI_add)])
  | rwasm.SizeConst n =>
      mret [wasm.BI_const (compile_num_from_Z wasm.T_i32 (Z.of_nat n))]
  end.

Definition if_gc_bit_set ref_tmp ins outs gc_branch lin_branch :=
  [wasm.BI_get_local ref_tmp;
   wasm.BI_const (compile_num_from_Z wasm.T_i32 1%Z);
   wasm.BI_binop wasm.T_i32 (wasm.Binop_i wasm.BOI_and);
   wasm.BI_testop wasm.T_i32 wasm.TO_eqz;
   wasm.BI_if (wasm.Tf ins outs) lin_branch gc_branch].

Definition unset_gc_bit :=
  [wasm.BI_const (compile_num_from_Z wasm.T_i32 1%Z);
   wasm.BI_binop wasm.T_i32 (wasm.Binop_i wasm.BOI_sub)].

Definition get_struct_field_types (targs : list rwasm.Typ) (idx : nat) : M (list (rwasm.Typ * rwasm.Size)) :=
  match (list_lookup idx targs) with
  | Some (rwasm.RefT _ _ (rwasm.StructType fields)) => mret fields
  | _ => mthrow (err ("struct instruction expected type-args to be a ref to a struct at index " ++ pretty idx))
  end.

(* TODO: validate ordering *)
Fixpoint tagged_load_all (memory : nat) (wasm_typs : list wasm.value_type) (scratch : wasm.immediate) : list wasm.basic_instruction :=
  match wasm_typs with
  | [] => []
  | typ :: rst =>
    let typ_size := size_of_wasm_typ_offset typ in
    [wasm.BI_get_local scratch;
     wasm.BI_load memory typ None 0%N 0%N;

     (* update scratch reg *)
     wasm.BI_const (compile_num_from_Z typ typ_size);
     wasm.BI_get_local scratch;
     wasm.BI_binop typ (wasm.Binop_i wasm.BOI_add);
     wasm.BI_set_local scratch] ++ (tagged_load_all memory rst scratch)
  end.
Definition struct_setup_gc_scratch ref_tmp scratch : (list wasm.basic_instruction) :=
  [wasm.BI_get_local ref_tmp] ++
    unset_gc_bit ++
    [wasm.BI_binop wasm.T_i32 (wasm.Binop_i wasm.BOI_add);
     wasm.BI_tee_local scratch].

Definition struct_setup_lin_scratch ref_tmp scratch : (list wasm.basic_instruction) :=
  [wasm.BI_get_local ref_tmp;
  wasm.BI_binop wasm.T_i32 (wasm.Binop_i wasm.BOI_add);
  wasm.BI_tee_local scratch].

Print struct_setup_lin_scratch.

Definition tagged_load (offset_instrs : list wasm.basic_instruction) field_typ (ref_tmp : wasm.immediate) : InstM (list wasm.basic_instruction) :=
  wasm_field_typ ← lift_M (compile_typ field_typ);
  scratch ← fresh_local wasm.T_i32;
  instrs ← mret $ offset_instrs ++
    [wasm.BI_get_local ref_tmp] ++
    if_gc_bit_set ref_tmp [wasm.T_i32 (* offset *)] wasm_field_typ
      (struct_setup_gc_scratch ref_tmp scratch ++ tagged_load_all GC_MEM wasm_field_typ scratch)
      (struct_setup_lin_scratch ref_tmp scratch ++ tagged_load_all LIN_MEM wasm_field_typ scratch);
  free_local scratch;;

  mret instrs.

Definition get_struct_ctx (targs : list rwasm.Typ) (targ_idx : nat) (idx : nat) : InstM _ :=
  fields ← lift_M $ get_struct_field_types targs targ_idx;
  off_sz ← struct_field_offset fields idx;
  off_instrs ← compile_size_expr off_sz;
  '(field_typ, _) ← lift_M $ mlookup_with_msg targ_idx fields "cannot get field type";
  mret (fields, off_sz, off_instrs, field_typ).

Fixpoint compile_instr (instr: AR.Instruction) : InstM (list wasm.basic_instruction) :=
  match instr with
  | AR.Instr instr' (rwasm.Arrow targs trets) => compile_pre_instr instr' targs trets
  end
with compile_pre_instr (instr: AR.PreInstruction) (targs trets: list rwasm.Typ) : InstM (list wasm.basic_instruction) :=
  match instr with
  | AR.Val v =>
    vals ← lift_M (compile_value v);
    mret (map (fun x => wasm.BI_const x) vals)
  | AR.Ne ni => (fun x => [x]) <$> (lift_M $ compile_num_intr ni)
  | AR.Unreachable => mret [wasm.BI_unreachable]
  | AR.Nop => mret [wasm.BI_nop]
  | AR.Drop => mret [wasm.BI_drop]
  | AR.Select => mret [wasm.BI_select]
  | AR.Block arrow _ i =>
    ft ← lift_M $ compile_arrow_type arrow;
    i' ← mapM compile_instr i;
    mret [wasm.BI_block ft (mjoin i')]
  | AR.Loop arrow i =>
    ft ← lift_M $ compile_arrow_type arrow;
    i' ← mapM compile_instr i;
    mret [wasm.BI_block ft (mjoin i')]
  | AR.ITE arrow _ t e =>
    ft ← lift_M $ compile_arrow_type arrow;
    t' ← mapM compile_instr t;
    e' ← mapM compile_instr e;
    mret [wasm.BI_if ft (mjoin t') (mjoin e')]
  | AR.Br i => mret [wasm.BI_br i]
  | AR.Br_if i => mret [wasm.BI_br_if i]
  | AR.Br_table i j => mret [wasm.BI_br_table i j]
  | AR.Ret => mret [wasm.BI_return]
  | AR.Get_local x x0 => mret [wasm.BI_get_local x] (* TODO: fix *)
  | AR.Set_local x => mret [wasm.BI_set_local x] (* TODO: fix *)
  | AR.Tee_local x => mret [wasm.BI_tee_local x] (* TODO: fix *)
  | AR.Get_global x => mret [wasm.BI_get_global x] (* TODO: fix *)
  | AR.Set_global x => mret [wasm.BI_set_global x] (* TODO: fix *)
  | AR.CoderefI x => mthrow (err "todo msg")
  | AR.Inst _ => mret []
  | AR.Call_indirect => mthrow (err "todo msg")
  | AR.Call x x0 => mthrow (err "todo msg")
  | AR.RecFold _
  | AR.RecUnfold
  | AR.Group _ _
  | AR.Ungroup
  | AR.CapSplit
  | AR.CapJoin
  | AR.RefDemote
  | AR.MemPack _ => mret []
  | AR.MemUnpack bt _ body => mthrow (err "todo msg")
  | AR.StructMalloc x x0 => mthrow (err "todo msg")
  | AR.StructFree => mthrow (err "todo msg")
  | AR.StructGet idx =>
      (* Save the argument *)
      (* typ should be [ref l (structtype fields)] -> [ref l (structtype fields); tau_field] *)
      ref_tmp ← fresh_local wasm.T_i32;
      '(fields, off_sz, off_instrs, field_typ) ← get_struct_ctx targs 0 idx;
      load_instrs ← tagged_load off_instrs field_typ ref_tmp;
      instrs ← mret $ wasm.BI_tee_local ref_tmp :: load_instrs;
      free_local ref_tmp;;
      mret instrs
  | AR.StructSet idx => mthrow (err "todo")
  | AR.StructSwap x => mthrow (err "todo msg")
  | AR.VariantMalloc x x0 x1 => mthrow (err "todo msg")
  | AR.VariantCase x x0 x1 x2 x3 => mthrow (err "todo msg")
  | AR.ArrayMalloc x => mthrow (err "todo msg")
  | AR.ArrayGet => mthrow (err "todo msg")
  | AR.ArraySet => mthrow (err "todo msg")
  | AR.ArrayFree => mthrow (err "todo msg")
  | AR.ExistPack x x0 x1 => mthrow (err "todo msg")
  | AR.ExistUnpack x x0 x1 x2 x3 => mthrow (err "todo msg")
  | AR.RefSplit
  | AR.RefJoin
  | AR.Qualify _ => mret []
  | AR.Trap => mthrow (err "todo msg")
  | AR.CallAdm x x0 => mthrow (err "todo msg")
  | AR.Label x x0 x1 x2 => mthrow (err "todo msg")
  | AR.Local x x0 x1 x2 x3 => mthrow (err "todo msg")
  | AR.Malloc x x0 x1 => mthrow (err "todo msg")
  | AR.Free => mthrow (err "todo msg")
  end.
(* ... *)
  
End compile_instr.

Definition compile_fun_type_idx (fun_type : rwasm.FunType) : wasm.typeidx.
Admitted.

Fixpoint compile_module (module : rwasm.module) : M wasm.module :=
  let '(funcs, globs, table) := module in
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
with compile_func (func : rwasm.Func) : M wasm.module_func := 
  match func with 
  | rwasm.Fun exports fun_type sizes intrs =>
    mret {|
      wasm.modfunc_type := compile_fun_type_idx fun_type;
      wasm.modfunc_locals := []; (* TODO *)
      wasm.modfunc_body := []; (* TODO *)
    |}
  end

with compile_glob (glob : rwasm.Glob) : M wasm.module_glob
with compile_table (table : rwasm.Table) : M wasm.module_table.
Admitted.
