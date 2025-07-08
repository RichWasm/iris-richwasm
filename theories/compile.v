From Coq Require Import List.
Require Import mathcomp.ssreflect.seq.
From stdpp Require Import list list_numbers.
Require Import stdpp.base.
Require Import stdpp.strings.
Require Import stdpp.pretty.
Require Import stdpp.list_numbers.
Import ListNotations.
From RWasm Require term.
From RWasm Require Import typing.
From Wasm Require datatypes operations.
Require Import Wasm.numerics.
Require Import BinNat.
Require Import compiler.monads.
Require Import compiler.numbers.

Module R := term.
Module W := datatypes.
Require Import stdpp.list.

(* locals exclusive to webassembly (compiler-generated temporaries, etc) *)
Definition wlocal_ctx := seq.seq W.value_type.

Record wlayout :=
  { w_offset: nat;
    w_ctx: wlocal_ctx }.

Definition wextend (w: wlayout) (t: W.value_type) :=
  {| w_offset := w.(w_offset);
     w_ctx := w.(w_ctx) ++ [t]; |}.

Definition next_idx (w: wlayout) : W.immediate :=
  w.(w_offset) + length w.(w_ctx).

Definition wst (A: Type) : Type := stateT wlayout (exn err) A.

Definition walloc (t: W.value_type) : wst W.immediate :=
  λ w, OK (wextend w t, next_idx w).

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

Definition compile_numtyp (typ: R.NumType) : W.value_type :=
  match typ with
  | R.Int _ inttyp => compile_int_type inttyp
  | R.Float floattyp => compile_float_type floattyp
  end.

Definition compile_kindvar (κ: R.KindVar) : list W.value_type :=
  match κ with
  | R.SIZE _ _ => [W.T_i32]
  | _ => []
  end.

Definition compile_kindvars (κs: list R.KindVar) : list W.value_type :=
  flat_map compile_kindvar κs.

Fixpoint compile_typ (typ: R.Typ) : exn err (list W.value_type) :=
  match typ with
  | R.Num ntyp => mret [compile_numtyp ntyp]
  | R.TVar _ => mret [W.T_i32]
  | R.Unit => mret []
  | R.ProdT typs => flatten <$> mapM compile_typ typs
  | R.CoderefT _ => mthrow Todo
  | R.Rec _ typ => compile_typ typ
  | R.PtrT _ => mret [W.T_i32]
  | R.ExLoc q typ => compile_typ typ
  | R.OwnR _ => mret []
  | R.CapT _ _ _ => mret []
  | R.RefT _ _ _  => mret [W.T_i32]
  end.
    (*
with compile_heap_type (typ: rwasm.HeapType) : exn err unit :=
  match typ with
  | rwasm.VariantType typs => mthrow Todo
  | rwasm.StructType fields => mthrow Todo
  | rwasm.ArrayType elt_typ => mthrow Todo
  | rwasm.Ex sz qual typ => mthrow Todo
  end
*)
Definition compile_arrow_type (typ: R.ArrowType) : exn err W.function_type :=
  match typ with
  | R.Arrow tys1 tys2 =>
    tys1' ← mapM compile_typ tys1;
    tys2' ← mapM compile_typ tys2;
    mret (W.Tf (flatten tys1') (flatten tys2'))
  end.
Definition compile_fun_type (ft: R.FunType) : exn err W.function_type :=
  match ft with
  | R.FunT κs (R.Arrow tys1 tys2) =>
    let κvs := compile_kindvars κs in
    tys1' ← flatten <$> mapM compile_typ tys1;
    tys2' ← flatten <$> mapM compile_typ tys2;
    mret (W.Tf (κvs ++ tys1') tys2')
  end.

Definition words_typ (typ: R.Typ) : exn err nat :=
  sum_list_with operations.words_t <$> compile_typ typ.

Definition throw_missing (instr_name : string) : exn err W.basic_instruction :=
  mthrow (Err ("missing iris-wasm " ++ instr_name ++ " wrap instruction")).

Definition compile_num (num_type : R.NumType) (num : nat) : W.value :=
  match num_type with
  | R.Int _ R.i32 =>
    W.VAL_int32 (Wasm_int.int_of_Z numerics.i32m (Z.of_nat num))
  | R.Int _ R.i64 =>
    W.VAL_int64 (Wasm_int.int_of_Z numerics.i64m (Z.of_nat num))
  (* is the signed converter the right thing to use here? *)
  | R.Float R.f32 =>
    W.VAL_float32
      ((Wasm_float.float_convert_si32
        numerics.f32m (Wasm_int.int_of_Z numerics.i32m (Z.of_nat num))))
  | R.Float R.f64 =>
    W.VAL_float64
      ((Wasm_float.float_convert_si64
        numerics.f64m (Wasm_int.int_of_Z numerics.i64m (Z.of_nat num))))
  end.

Fixpoint expect_concrete_size (sz: R.Size) : exn err nat :=
  match sz with
  | R.SizeConst c => mret c
  | R.SizePlus sz1 sz2 =>
      c1 ← expect_concrete_size sz1;
      c2 ← expect_concrete_size sz2;
      mret (c1 + c2)
  | _ => mthrow (Err "expected concrete size")
  end.

(* Mapping from size variables to indices of locals of type i32 *)
Definition size_ctx := 
  list W.immediate.

Section compile_instr.
Variable (sz_locs: size_ctx).
(* i32 local for hanging on to linear references during stores/loads *)
Variable (GC_MEM: W.immediate).
Variable (LIN_MEM: W.immediate).

Fixpoint struct_field_offset (fields: list (R.Typ * R.Size)) (idx: nat) : exn err R.Size :=
  match idx with
  | 0 => mret $ R.SizeConst 0
  | S idx' =>
      match fields with
      | (_, sz) :: fields' => R.SizePlus sz <$> (struct_field_offset fields' idx')
      | [] => mthrow Todo
      end
  end.

Definition get_struct_field_types (targs : list R.Typ) (idx : nat) : exn err (list (R.Typ * R.Size)) :=
  match targs !! idx with
  | Some (R.RefT _ _ (R.StructType fields)) => mret fields
  | _ => mthrow (Err ("struct instruction expected type-args to be a ref to a struct at index " ++ pretty idx))
  end.

Definition get_array_elem_type (targs : list R.Typ) (idx : nat) : exn err R.Typ :=
  match targs !! idx with
  | Some (R.RefT _ _ (R.ArrayType typ)) => mret typ
  | _ => mthrow (Err ("array instruction expected a ref to an array type at index " ++ pretty idx))
  end.

Fixpoint compile_sz (sz : R.Size) : exn err (list W.basic_instruction) :=
  match sz with
  | R.SizeVar σ =>
    local_idx ← err_opt (sz_locs !! σ) ("sz " ++ (pretty σ) ++ " not found in sz_local_map");
    mret [W.BI_get_local local_idx]
  | R.SizePlus sz1 sz2 =>
    e1 ← compile_sz sz1;
    e2 ← compile_sz sz2;
    mret $ e1 ++ e2 ++ [W.BI_binop W.T_i32 (W.Binop_i W.BOI_add)]
  | R.SizeConst c =>
    mret [W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat c)))]
  end.

Definition if_gc_bit_set ref_tmp ins outs gc_branch lin_branch :=
  [W.BI_get_local ref_tmp;
   W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 1%Z));
   W.BI_binop W.T_i32 (W.Binop_i W.BOI_and);
   W.BI_testop W.T_i32 W.TO_eqz;
   W.BI_if (W.Tf ins outs) lin_branch gc_branch].

Definition unset_gc_bit :=
  [W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 1%Z));
   W.BI_binop W.T_i32 (W.Binop_i W.BOI_sub)].

Fixpoint loads'
  (mem: W.immediate)
  (base_ptr_var: W.immediate)
  (off: W.static_offset)
  (tys: list W.value_type) :=
  match tys with
  | [] => []
  | ty :: tys =>
      W.BI_get_local base_ptr_var ::
      W.BI_load mem ty None 0%N off ::
      loads' base_ptr_var mem (off + N.of_nat (operations.length_t ty))%N tys
  end.

Definition loads mem base_ptr_var tys :=
  loads' mem base_ptr_var 0%N tys.

Definition gc_loads
  (ref_var: W.immediate)
  (offset_instrs: list W.basic_instruction)
  (tys: list W.value_type) :=
  base_ptr_var ← walloc W.T_i32;
  mret $ W.BI_get_local ref_var ::
         unset_gc_bit ++ 
         offset_instrs ++
         W.BI_set_local base_ptr_var ::
         loads GC_MEM base_ptr_var tys.

Definition lin_loads
  (ref_var: W.immediate)
  (offset_instrs: list W.basic_instruction)
  (tys: list W.value_type) :=
  base_ptr_var ← walloc W.T_i32;
  mret $ W.BI_get_local ref_var ::
         offset_instrs ++
         W.BI_set_local base_ptr_var ::
         loads LIN_MEM base_ptr_var tys.

Definition tagged_loads
  (base_ptr: W.immediate)
  (offset_instrs: list W.basic_instruction)
  (tys: list W.value_type) :=
  gc_instrs ← gc_loads base_ptr offset_instrs tys;
  lin_instrs ← lin_loads base_ptr offset_instrs tys;
  mret $ if_gc_bit_set base_ptr [] tys gc_instrs lin_instrs.

Definition tagged_load
  (base_ptr: W.immediate)
  (offset_instrs: list W.basic_instruction)
  (ty: R.Typ)
  : wst (list W.basic_instruction) :=
  tys ← liftM $ compile_typ ty;
  tagged_loads base_ptr offset_instrs tys.

Fixpoint loc_stores'
  (base_ptr_var: W.immediate)
  (mem: W.immediate)
  (off: W.static_offset)
  (val_var_tys: list (W.immediate * W.value_type)) :=
  match val_var_tys with
  | [] => []
  | (val_var, ty) :: val_var_tys =>
      W.BI_get_local base_ptr_var ::
      W.BI_get_local val_var ::
      W.BI_store mem ty None 0%N off ::
      loc_stores' base_ptr_var mem (off + N.of_nat (operations.length_t ty))%N val_var_tys
  end.

Definition loc_stores base_ptr_var mem val_var_tys : list W.basic_instruction :=
  loc_stores' base_ptr_var mem 0%N val_var_tys.

Definition stores base_ptr_var mem (val_vars: list W.immediate) (tys: list W.value_type)
  : list W.basic_instruction :=
  loc_stores base_ptr_var mem (zip val_vars tys).

Definition wallocs (tys: list W.value_type) : wst (list W.immediate) :=
  mapM walloc tys.

Definition walloc_args (tys: list W.value_type)
  : wst (list W.immediate *
         list W.basic_instruction) :=
  vars ← wallocs tys;
  mret $ (vars, map W.BI_set_local vars).

Definition tagged_store
  (offset_instrs: list W.basic_instruction)
  (ty: R.Typ)
  : wst (list W.basic_instruction) :=
  tys ← liftM $ compile_typ ty;
  '(arg_vars, save_args) ← walloc_args tys;
  base_ptr_var ← walloc W.T_i32;
  mret $
    save_args ++
    W.BI_tee_local base_ptr_var ::
    if_gc_bit_set base_ptr_var [] []
        (W.BI_get_local base_ptr_var ::
         unset_gc_bit ++
         offset_instrs ++
         W.BI_set_local base_ptr_var ::
         stores base_ptr_var GC_MEM arg_vars tys)
        (W.BI_get_local base_ptr_var ::
         offset_instrs ++
         stores base_ptr_var LIN_MEM arg_vars tys).

Fixpoint local_layout (L: Local_Ctx) (base: nat) (i: nat) : exn err (nat * R.Typ) :=
  match L, i with
  | (τ, sz) :: L, 0 =>
      mret (base, τ)
  | (τ, sz) :: L, S i =>
      sz_const ← expect_concrete_size sz;
      local_layout L (base + sz_const) i
  | [], _ => mthrow (Err "local_layout given out of bounds index")
  end.

Definition get_i64_local loc :=
      [W.BI_get_local loc;
       W.BI_cvtop W.T_i32 W.CVO_reinterpret W.T_i64 None;
       W.BI_const (W.VAL_int64 (Wasm_int.int_of_Z i64m 32%Z));
       W.BI_binop W.T_i64 (W.Binop_i W.BOI_rotl);
       W.BI_get_local (loc + 1);
       W.BI_cvtop W.T_i32 W.CVO_reinterpret W.T_i64 None;
       W.BI_binop W.T_i64 (W.Binop_i W.BOI_or)].

Fixpoint numtyp_gets (nτ: R.NumType) (loc: nat) : list W.basic_instruction :=
  match nτ with
  | R.Int s R.i32 =>
      [W.BI_get_local loc]
  | R.Float R.f32 =>
      [W.BI_get_local loc;
       W.BI_cvtop W.T_i32 W.CVO_reinterpret W.T_f32 None]
  | R.Int s R.i64 =>
      get_i64_local loc
  | R.Float R.f64 =>
      get_i64_local loc ++ 
      [W.BI_cvtop W.T_i64 W.CVO_reinterpret W.T_f64 None]
  end.

Fixpoint local_gets (τ: R.Typ) (loc: nat) : exn err (list W.basic_instruction) :=
  match τ with
  | R.Num nτ =>
      mret (numtyp_gets nτ loc)
  | R.TVar α =>
      mret [W.BI_get_local loc]
  | R.Unit =>
      mret []
  | R.ProdT τs =>
      let fix loop τs0 sz :=
        match τs0 with
        | τ0 :: τs0' =>
            sz ← words_typ τ0;
            es ← local_gets τ0 loc;
            es' ← loop τs0' (loc + sz);
            mret $ es ++ es'
        | [] => mret []
        end in
      loop τs loc
  | R.CoderefT χ => mthrow Todo
  | R.Rec q τ =>
      local_gets τ loc
  | R.PtrT ℓ =>
      mret [W.BI_get_local loc]
  | R.ExLoc q τ =>
      local_gets τ loc
  | R.OwnR ℓ =>
      mret []
  | R.CapT cap ℓ ψ =>
      mret []
  | R.RefT cap ℓ ψ =>
      mret [W.BI_get_local loc]
  end.

Fixpoint local_sets (τ: R.Typ) (loc: nat) : exn err (list W.basic_instruction) :=
  match τ with
  | R.Num nτ =>
      mret (numtyp_gets nτ loc)
  | R.TVar α =>
      mret [W.BI_set_local loc]
  | R.Unit =>
      mret []
  | R.ProdT τs =>
      let fix loop τs0 sz :=
        match τs0 with
        | τ0 :: τs0' =>
            sz ← words_typ τ0;
            es ← local_gets τ0 loc;
            es' ← loop τs0' (loc + sz);
            mret $ es ++ es'
        | [] => mret []
        end in
      loop τs loc
  | R.CoderefT χ => mthrow Todo
  | R.Rec q τ =>
      local_gets τ loc
  | R.PtrT ℓ =>
      mret [W.BI_set_local loc]
  | R.ExLoc q τ =>
      local_gets τ loc
  | R.OwnR ℓ =>
      mret []
  | R.CapT cap ℓ ψ =>
      mret []
  | R.RefT cap ℓ ψ =>
      mret [W.BI_set_local loc]
  end.

Fixpoint compile_instr (instr: R.instr TyAnn) : wst (list W.basic_instruction) :=
  match instr with
  | R.INumConst _ num_type num =>
      mret [W.BI_const $ compile_num num_type num]
  | R.IUnit _ =>
      mret []
  | R.INum ann ni =>
      instr ← liftM $ compile_num_instr ni;
      mret [instr]
  | R.IUnreachable (R.Arrow targs trets, _) =>
      mret [W.BI_unreachable]
  | R.INop (R.Arrow targs trets, _) =>
      mret [W.BI_nop]
  | R.IDrop (R.Arrow targs trets, _) =>
      match targs with
      | (t_drop :: targs) =>
        wasm_typ ← liftM $ compile_typ t_drop;
        mret $ map (const W.BI_drop) wasm_typ
      | [] => 
        mthrow (Err "rwasm.IDrop should have a nonempty stack type annotation")
      end
  | R.ISelect (R.Arrow targs trets, _) =>
      mret [W.BI_select]
  | R.IBlock (R.Arrow targs trets, _) ta _ i =>
    ta' ← liftM $ compile_arrow_type ta;
    i' ← mapM compile_instr i;
    mret [W.BI_block ta' (flatten i')]
  | R.ILoop (R.Arrow targs trets, _) arrow i =>
    ft ← liftM $ compile_arrow_type arrow;
    i' ← mapM compile_instr i;
    mret [W.BI_block ft (flatten i')]
  | R.IIte (R.Arrow targs trets, _) arrow _ t e =>
    ft ← liftM $ compile_arrow_type arrow;
    t' ← mapM compile_instr t;
    e' ← mapM compile_instr e;
    mret [W.BI_if ft (flatten t') (flatten e')]
  | R.IBr (R.Arrow targs trets, _) x => mret [W.BI_br x]
  | R.IBrIf (R.Arrow targs trets, _) x => mret [W.BI_br_if x]
  | R.IBrTable (R.Arrow targs trets, _) x x0 => mret [W.BI_br_table x x0]
  | R.IRet (R.Arrow targs trets, _) => mret [W.BI_return]
  | R.IGetLocal (R.Arrow targs trets, LSig L _) idx _ =>
      '(base, τ) ← liftM $ local_layout L 0 idx;
      liftM $ local_gets τ base
  | R.ISetLocal (R.Arrow targs trets, LSig L _) idx =>
      '(base, τ) ← liftM $ local_layout L 0 idx;
      liftM $ local_sets τ base
  | R.ITeeLocal (R.Arrow targs trets, LSig L _) idx =>
      '(base, τ) ← liftM $ local_layout L 0 idx;
      sets ← liftM $ local_sets τ base;
      gets ← liftM $ local_gets τ base;
      mret $ sets ++ gets
  | R.IGetGlobal (R.Arrow targs trets, _) x => mret [W.BI_get_global x]
  | R.ISetGlobal (R.Arrow targs trets, _) x => mret [W.BI_set_global x]
  | R.ICoderef (R.Arrow targs trets, _) x => mthrow Todo
  | R.IInst (R.Arrow targs trets, _) x => mthrow Todo
  | R.ICallIndirect (R.Arrow targs trets, _) => mthrow Todo (* TODO: why doesn't rwasm take an immediate? *)
  | R.ICall (R.Arrow targs trets, _) x x0 => mthrow Todo     (* TODO: what to do with list of indexes? *)
  | R.IMemUnpack _ ta tl es =>
      ta' ← liftM $ compile_arrow_type ta;
      e__s' ← flatten <$> mapM compile_instr es;
      mret [W.BI_block ta' e__s']
  | R.IStructMalloc (R.Arrow targs trets, _) szs q =>
      mthrow Todo
  | R.IStructFree (R.Arrow targs trets, _) =>
      mthrow Todo
             (* mret $ [wasm.BI_call Σ.(me_free)]*)
  | R.IStructGet (R.Arrow from to, _) n =>
      base_ref ← walloc W.T_i32;
      fields ← liftM $ get_struct_field_types from 0;
      field_typ ← liftM $ err_opt (list_lookup 0 to) "struct.get: cannot find output val type";
      offset_sz ← liftM $ struct_field_offset fields n;
      offset_instrs ← liftM $ compile_sz offset_sz;
      load_instrs ← tagged_load base_ref offset_instrs field_typ;
      mret $ W.BI_tee_local base_ref :: load_instrs
  | R.IStructSet (R.Arrow from to, _) n =>
      fields ← liftM $ get_struct_field_types from 1;
      val_typ ← liftM $ err_opt (list_lookup 0 from) "struct.set: cannot find input val type";
      offset_sz ← liftM $ struct_field_offset fields n;
      offset_e ← liftM $ compile_sz offset_sz;
      tagged_store offset_e val_typ
  | R.IStructSwap (R.Arrow from to, _) n =>
      fields ← liftM $ get_struct_field_types from 1;
      field_typ ← liftM $ err_opt (list_lookup 0 from) "struct.swap: cannot find input val type";
      field_shape ← liftM $ compile_typ field_typ;
      offset_sz ← liftM $ struct_field_offset fields n;
      offset_e ← liftM $ compile_sz offset_sz;
      mthrow Todo
(*
      mret $ [layout.Swap] ++                (* [ptr; val] → [val; ptr]*)
             offset_e ++                     (* [] → [offset] *)
             [layout.SwapOffset field_shape; (* [ptr; offset; val__new] → [ptr; offset; val__old] *)
              layout.Swap;                   (* [offset; val] → [val; offset] *)
              layout.Drop]                   (* [offset] → [] *)
*)
  | R.IVariantMalloc (R.Arrow from to, _) sz tys q =>
      typ ← liftM $ err_opt (list_lookup 0 from) "variant.malloc: cannot find val type";
      shape ← liftM $ compile_typ  typ;
      (* memory layout is [ind, τ*] so we just add prepend *)
      (*let full_shape := LS_tuple [LS_int32; shape] in*)
      mthrow Todo (*
      mret $ [
        layout.Val $ LV_int32 (shape_size_words full_shape);
        layout.Malloc;                                       (* [i32] → [ptr] *)
        layout.Val $ LV_int32 (shape_size_words full_shape); (* [] → [offset__end] *)
        layout.Pluck 3;          (* [val; ptr; offset] → [ptr; offset; val] *)
        layout.StoreOffset;      (* [ptr; offset; val] → [ptr; offset] *)
        layout.Val $ LV_int32 i; (* [] → [val] *)
        layout.StoreOffset;      (* [ptr; offset; val] → [ptr; offset] *)
        layout.Drop]             (* [ptr; offset] → [ptr] *)
    *)
    | R.IVariantCase ann q th ta tl es => mthrow Todo
    (* [val__init; len] → [ptr] *)
    (* [τ      ; i32] → [i32] *)
    | R.IArrayMalloc (R.Arrow from to, _) q =>
      arr_init_typ ← liftM $ err_opt (list_lookup 1 from) "array.malloc: cannot find val type";
      shape ← liftM $ compile_typ arr_init_typ;
      mthrow Todo
             (*
      mret [
        layout.Dup;             (* [len] → [len; len] *)
        layout.Val $ LV_int32 (shape_size_words shape);
        layout.Ne $ rwasm.Ib rwasm.i32 rwasm.mul; (* [len; i32] → [size] *)
        layout.Malloc;                            (* [size] → [ptr] *)
        layout.RepeatInit shape]                  (* [val; len; ptr] → [ptr] *)
*)
    (* [ptr; idx] → [ptr; val] *)
    (* [i32; i32] → [i32; τ  ] *)
    | R.IArrayGet (R.Arrow from to, _) =>
      elem_typ ← liftM $ get_array_elem_type from 1;
      elem_shape ← liftM $ compile_typ elem_typ;
      (*  ex: i64[i]
         | idx | offset |
         |-----|--------|
         | 0   | 0      |
         | 1   | 1 * 2  |
         ...
         | i   | i * 2  | *)
      mthrow Todo
(*
      mret [
        layout.Val $ LV_int32 (shape_size_words elem_shape);
        layout.Ne $ rwasm.Ib rwasm.i32 rwasm.mul; (* [idx; sz] → [offset] *)
        layout.LoadOffset elem_shape; (* [ptr; offset] → [ptr; offset; val] *)
        layout.Swap;                  (* [offset; val] → [val; offset]*)
        layout.Drop]                  (* [offset]; → [] *)
    (* [ptr; idx; val] → [ptr] *)
    (* [i32; i32; τ  ] → [i32] *)
*)
    | R.IArraySet (R.Arrow from to, _) =>
      elem_typ ← liftM $ get_array_elem_type from 2;
      elem_shape ← liftM $ compile_typ elem_typ;
      (*  ex: [i]
         | idx | offset      |
         |-----|-------------|
         | 0   | 2           |
         | 1   | 2 * 2       |
         ...
         | i   | (i + 1) * 2 | *)
      mthrow Todo
             (*
      mret [
        layout.Val $ LV_int32 1;
        layout.Ne $ rwasm.Ib rwasm.i32 rwasm.add;
        layout.Val $ LV_int32 (shape_size_words elem_shape);
        layout.Ne $ rwasm.Ib rwasm.i32 rwasm.mul; (* [idx; sz] → [offset] *)
        layout.LoadOffset elem_shape; (* [ptr; offset] → [ptr; offset; val] *)
        layout.Swap;                  (* [offset; val] → [val; offset]*)
        layout.Drop]                  (* [offset]; → [] *)
*)
    (* [ptr] → [] *)
    (* [i32] → [] *)
  | R.IArrayFree ann => mthrow Todo (*mret $ [wasm.BI_call Σ.(me_free)]*)
  | R.IExistPack (R.Arrow targs trets, _) x x0 x1 => mthrow Todo
  | R.IExistUnpack (R.Arrow targs trets, _) x x0 x1 x2 x3 => mthrow Todo
  | R.IRefSplit _
  | R.IRefJoin _
  | R.IRecFold _ _
  | R.IRecUnfold  _
  | R.IGroup _ _ _
  | R.IUngroup _
  | R.ICapSplit _
  | R.ICapJoin _
  | R.IRefDemote _
  | R.IMemPack _ _
  | R.IQualify _ _ => mret []
  end.

Definition compile_instrs instrs := flatten <$> mapM compile_instr instrs.

End compile_instr.

Definition compile_fun_type_idx (fun_type : R.FunType) : W.typeidx.
Admitted.

Definition funcidx_table_write : W.immediate.
Admitted.

Definition typeidx_start : W.immediate.
Admitted.

Definition typeidx_table_write : W.immediate.
Admitted.

Definition globidx_table_offset : W.immediate.
Admitted.

Definition compile_table_elem (start : W.immediate) (i funcidx : nat) : W.expr :=
  [ W.BI_get_local start;
    W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat i)));
    W.BI_binop W.T_i32 (W.Binop_i W.BOI_add);
    W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat funcidx)));
    W.BI_call funcidx_table_write ].

Definition compile_start (table : R.Table) : W.module_func :=
  {| W.modfunc_type := W.Mk_typeidx typeidx_start;
     W.modfunc_locals := [ W.T_i32 ];
     W.modfunc_body :=
       [ (* Save the beginning table offset. *)
         W.BI_get_global globidx_table_offset;
         W.BI_set_local 0;
         (* Increment the index for the next module to use the table. *)
         W.BI_get_local 0;
         W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (length table))));
         W.BI_binop W.T_i32 (W.Binop_i W.BOI_add);
         W.BI_set_global globidx_table_offset ] ++
       flatten (imap (compile_table_elem 0) table) |}.

Fixpoint compile_module (module : R.module TyAnn) : exn err W.module :=
  let '(funcs, globs, table) := module return exn err W.module in
  mret {|
    W.mod_types := []; (* TODO *)
    W.mod_funcs := []; (* TODO *)
    W.mod_tables := []; (* TODO *)
    W.mod_mems := []; (* TODO *)
    W.mod_globals := []; (* TODO *)
    W.mod_elem := []; (* TODO *)
    W.mod_data := []; (* TODO *)
    W.mod_start := Some (W.Build_module_start (W.Mk_funcidx 0)); (* TODO *)
    W.mod_imports := (* TODO *)
      [ W.Build_module_import
          (String.list_byte_of_string "RichWasm")
          (String.list_byte_of_string "modify_table")
          (W.ID_func typeidx_table_write) ];
    W.mod_exports := [] (* TODO *)
  |}

(* TODO: modfunc_type expects a typeidx while rwasm does this inline *)
with compile_func (func : R.Func TyAnn) : option W.module_func :=
  match func with
  | R.Fun exports fun_type sizes intrs =>
    Some {|
      W.modfunc_type := compile_fun_type_idx fun_type;
      W.modfunc_locals := []; (* TODO *)
      W.modfunc_body := []; (* TODO *)
    |}
  end

with compile_glob (glob : R.Glob TyAnn) : exn err W.module_glob
with compile_table (table : R.Table) : exn err W.module_table.
Admitted.
