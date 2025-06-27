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

Definition compile_kindvar (κ: rwasm.KindVar) : list wasm.value_type :=
  match κ with
  | rwasm.SIZE _ _ => [wasm.T_i32]
  | _ => []
  end.

Definition compile_kindvars (κs: list rwasm.KindVar) : list wasm.value_type :=
  flatten (map compile_kindvar κs).

Fixpoint compile_typ (typ: rwasm.Typ) : option (list wasm.value_type) :=
  match typ with
  | rwasm.Num ntyp => wty ← compile_numtyp ntyp; mret [wty]
  | rwasm.TVar _ => mret [wasm.T_i32]
  | rwasm.Unit => mret []
  | rwasm.ProdT typs => flatten <$> mapM compile_typ typs
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
    tys1' ← flatten <$> mapM compile_typ tys1;
    tys2' ← flatten <$> mapM compile_typ tys2;
    mret (wasm.Tf (κvs ++ tys1') tys2')
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

Fixpoint compile_instr (instr: rwasm.instr rwasm.ArrowType) : option (list wasm.basic_instruction) :=
  match instr with
  | rwasm.INumConst _ num_type num => Some [wasm.BI_const $ compile_num num_type num]
  | rwasm.IUnit _ => None
  | rwasm.INum (rwasm.Arrow targs trets) x => None
  | rwasm.IUnreachable (rwasm.Arrow targs trets) => Some [wasm.BI_unreachable]
  | rwasm.INop (rwasm.Arrow targs trets) => Some [wasm.BI_nop]
  | rwasm.IDrop (rwasm.Arrow targs trets) => Some [wasm.BI_drop]
  | rwasm.ISelect (rwasm.Arrow targs trets) => Some [wasm.BI_select]
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
  | rwasm.IBr (rwasm.Arrow targs trets) x => Some [wasm.BI_br x]
  | rwasm.IBrIf (rwasm.Arrow targs trets) x => Some [wasm.BI_br_if x]
  | rwasm.IBrTable (rwasm.Arrow targs trets) x x0 => Some [wasm.BI_br_table x x0]
  | rwasm.IRet (rwasm.Arrow targs trets) => Some [wasm.BI_return]
  | rwasm.IGetLocal (rwasm.Arrow targs trets) x x0 => Some [wasm.BI_get_local x]
  | rwasm.ISetLocal (rwasm.Arrow targs trets) x => Some [wasm.BI_set_local x]
  | rwasm.ITeeLocal (rwasm.Arrow targs trets) x => Some [wasm.BI_tee_local x]
  | rwasm.IGetGlobal (rwasm.Arrow targs trets) x => Some [wasm.BI_get_global x]
  | rwasm.ISetGlobal (rwasm.Arrow targs trets) x => Some [wasm.BI_set_global x]
  | rwasm.ICoderef (rwasm.Arrow targs trets) x => None
  | rwasm.IInst (rwasm.Arrow targs trets) x => None
  | rwasm.ICallIndirect (rwasm.Arrow targs trets) => None (* TODO: why doesn't rwasm take an immediate? *)
  | rwasm.ICall (rwasm.Arrow targs trets) x x0 => None
  | rwasm.IRecFold (rwasm.Arrow targs trets) x => None
  | rwasm.IRecUnfold (rwasm.Arrow targs trets) => None
  | rwasm.IGroup (rwasm.Arrow targs trets) x x0 => None
  | rwasm.IUngroup (rwasm.Arrow targs trets) => None
  | rwasm.ICapSplit (rwasm.Arrow targs trets) => None
  | rwasm.ICapJoin (rwasm.Arrow targs trets) => None
  | rwasm.IRefDemote (rwasm.Arrow targs trets) => None
  | rwasm.IMemPack (rwasm.Arrow targs trets) x => None
  | rwasm.IMemUnpack (rwasm.Arrow targs trets) x x0 x1 => None
  | rwasm.IStructMalloc (rwasm.Arrow targs trets) x x0 => None
  | rwasm.IStructFree (rwasm.Arrow targs trets) => None
  | rwasm.IStructGet (rwasm.Arrow targs trets) idx =>
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
  | rwasm.IStructSet (rwasm.Arrow targs trets) x => None
  | rwasm.IStructSwap (rwasm.Arrow targs trets) x => None
  | rwasm.IVariantMalloc (rwasm.Arrow targs trets) x x0 x1 => None
  | rwasm.IVariantCase (rwasm.Arrow targs trets) x x0 x1 x2 x3 => None
  | rwasm.IArrayMalloc (rwasm.Arrow targs trets) x => None
  | rwasm.IArrayGet (rwasm.Arrow targs trets) => None
  | rwasm.IArraySet (rwasm.Arrow targs trets) => None
  | rwasm.IArrayFree (rwasm.Arrow targs trets) => None
  | rwasm.IExistPack (rwasm.Arrow targs trets) x x0 x1 => None
  | rwasm.IExistUnpack (rwasm.Arrow targs trets) x x0 x1 x2 x3 => None
  | rwasm.IRefSplit (rwasm.Arrow targs trets) => None
  | rwasm.IRefJoin (rwasm.Arrow targs trets) => None
  | rwasm.IQualify (rwasm.Arrow targs trets) x => None
  end.

Definition compile_instrs instrs := flatten <$> mapM compile_instr instrs.

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
