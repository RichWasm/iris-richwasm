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

Module rwasm := term.
Module wasm := datatypes.
Require Import stdpp.list.

(* locals exclusive to webassembly (compiler-generated temporaries, etc) *)
Definition wlocal_ctx := seq.seq wasm.value_type.

Record wlayout :=
  { w_offset: nat;
    w_ctx: wlocal_ctx }.

Definition wextend (w: wlayout) (t: wasm.value_type) :=
  {| w_offset := w.(w_offset);
     w_ctx := w.(w_ctx) ++ [t]; |}.

Definition next_idx (w: wlayout) : wasm.immediate :=
  w.(w_offset) + length w.(w_ctx).

Definition wst (A: Type) : Type := stateT wlayout (exn err) A.

Definition walloc (t: wasm.value_type) : wst wasm.immediate :=
  λ w, OK (wextend w t, next_idx w).

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
Definition compile_arrow_type (typ: rwasm.ArrowType) : exn err wasm.function_type :=
  match typ with
  | rwasm.Arrow tys1 tys2 =>
    tys1' ← mapM compile_typ tys1;
    tys2' ← mapM compile_typ tys2;
    mret (wasm.Tf (flatten tys1') (flatten tys2'))
  end.
Definition compile_fun_type (ft: rwasm.FunType) : exn err wasm.function_type :=
  match ft with
  | rwasm.FunT κs (rwasm.Arrow tys1 tys2) =>
    let κvs := compile_kindvars κs in
    tys1' ← flatten <$> mapM compile_typ tys1;
    tys2' ← flatten <$> mapM compile_typ tys2;
    mret (wasm.Tf (κvs ++ tys1') tys2')
  end.

Definition words_typ (typ: rwasm.Typ) : exn err nat :=
  sum_list_with operations.words_t <$> compile_typ typ.

Definition throw_missing (instr_name : string) : exn err wasm.basic_instruction :=
  mthrow (Err ("missing iris-wasm " ++ instr_name ++ " wrap instruction")).

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

Fixpoint expect_concrete_size (sz: rwasm.Size) : exn err nat :=
  match sz with
  | rwasm.SizeConst c => mret c
  | rwasm.SizePlus sz1 sz2 =>
      c1 ← expect_concrete_size sz1;
      c2 ← expect_concrete_size sz2;
      mret (c1 + c2)
  | _ => mthrow (Err "expected concrete size")
  end.

(* Mapping from size variables to indices of locals of type i32 *)
Definition size_ctx := 
  list wasm.immediate.

Section compile_instr.
Variable (sz_locs: size_ctx).
(* i32 local for hanging on to linear references during stores/loads *)
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

Definition if_gc_bit_set ref_tmp ins outs gc_branch lin_branch :=
  [wasm.BI_get_local ref_tmp;
   wasm.BI_const (wasm.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 1%Z));
   wasm.BI_binop wasm.T_i32 (wasm.Binop_i wasm.BOI_and);
   wasm.BI_testop wasm.T_i32 wasm.TO_eqz;
   wasm.BI_if (wasm.Tf ins outs) lin_branch gc_branch].

Definition unset_gc_bit :=
  [wasm.BI_const (wasm.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 1%Z));
   wasm.BI_binop wasm.T_i32 (wasm.Binop_i wasm.BOI_sub)].

Fixpoint loads'
  (mem: wasm.immediate)
  (base_ptr_var: wasm.immediate)
  (off: wasm.static_offset)
  (tys: list wasm.value_type) :=
  match tys with
  | [] => []
  | ty :: tys =>
      wasm.BI_get_local base_ptr_var ::
      wasm.BI_load mem ty None 0%N off ::
      loads' base_ptr_var mem (off + N.of_nat (operations.length_t ty))%N tys
  end.

Definition loads mem base_ptr_var tys :=
  loads' mem base_ptr_var 0%N tys.

Definition gc_loads
  (ref_var: wasm.immediate)
  (offset_instrs: list wasm.basic_instruction) 
  (tys: list wasm.value_type) :=
  base_ptr_var ← walloc wasm.T_i32;
  mret $ wasm.BI_get_local ref_var ::
         unset_gc_bit ++ 
         offset_instrs ++
         wasm.BI_set_local base_ptr_var ::
         loads GC_MEM base_ptr_var tys.
        
Definition lin_loads
  (ref_var: wasm.immediate)
  (offset_instrs: list wasm.basic_instruction) 
  (tys: list wasm.value_type) :=
  base_ptr_var ← walloc wasm.T_i32;
  mret $ wasm.BI_get_local ref_var ::
         offset_instrs ++
         wasm.BI_set_local base_ptr_var ::
         loads LIN_MEM base_ptr_var tys.

Definition tagged_loads
  (base_ptr: wasm.immediate)
  (offset_instrs: list wasm.basic_instruction) 
  (tys: list wasm.value_type) :=
  gc_instrs ← gc_loads base_ptr offset_instrs tys;
  lin_instrs ← lin_loads base_ptr offset_instrs tys;
  mret $ if_gc_bit_set base_ptr [] tys gc_instrs lin_instrs.

Definition tagged_load
  (base_ptr: wasm.immediate)
  (offset_instrs: list wasm.basic_instruction) 
  (ty: rwasm.Typ) 
  : wst (list wasm.basic_instruction) :=
  tys ← liftM $ compile_typ ty;
  tagged_loads base_ptr offset_instrs tys.

Fixpoint loc_stores'
  (base_ptr_var: wasm.immediate)
  (mem: wasm.immediate)
  (off: wasm.static_offset)
  (val_var_tys: list (wasm.immediate * wasm.value_type)) :=
  match val_var_tys with
  | [] => []
  | (val_var, ty) :: val_var_tys =>
      wasm.BI_get_local base_ptr_var ::
      wasm.BI_get_local val_var ::
      wasm.BI_store mem ty None 0%N off ::
      loc_stores' base_ptr_var mem (off + N.of_nat (operations.length_t ty))%N val_var_tys
  end.

Definition loc_stores base_ptr_var mem val_var_tys : list wasm.basic_instruction :=
  loc_stores' base_ptr_var mem 0%N val_var_tys.

Definition stores base_ptr_var mem (val_vars: list wasm.immediate) (tys: list wasm.value_type) 
  : list wasm.basic_instruction :=
  loc_stores base_ptr_var mem (zip val_vars tys).

Definition wallocs (tys: list wasm.value_type) : wst (list wasm.immediate) :=
  mapM walloc tys.

Definition walloc_args (tys: list wasm.value_type) 
  : wst (list wasm.immediate * 
         list wasm.basic_instruction) :=
  vars ← wallocs tys;
  mret $ (vars, map wasm.BI_set_local vars).

Definition tagged_store
  (offset_instrs: list wasm.basic_instruction) 
  (ty: rwasm.Typ) 
  : wst (list wasm.basic_instruction) :=
  tys ← liftM $ compile_typ ty;
  '(arg_vars, save_args) ← walloc_args tys;
  base_ptr_var ← walloc wasm.T_i32;
  mret $
    save_args ++
    wasm.BI_tee_local base_ptr_var ::
    if_gc_bit_set base_ptr_var [] []
        (wasm.BI_get_local base_ptr_var ::
         unset_gc_bit ++
         offset_instrs ++
         wasm.BI_set_local base_ptr_var ::
         stores base_ptr_var GC_MEM arg_vars tys)
        (wasm.BI_get_local base_ptr_var ::
         offset_instrs ++
         stores base_ptr_var LIN_MEM arg_vars tys).

Fixpoint local_layout (L: Local_Ctx) (base: nat) (i: nat) : exn err (nat * rwasm.Typ) :=
  match L, i with
  | (τ, sz) :: L, 0 =>
      mret (base, τ)
  | (τ, sz) :: L, S i =>
      sz_const ← expect_concrete_size sz;
      local_layout L (base + sz_const) i
  | [], _ => mthrow (Err "local_layout given out of bounds index")
  end.

Print wasm.BI_cvtop.

Definition get_i64_local loc :=
      [wasm.BI_get_local loc;
       wasm.BI_cvtop wasm.T_i32 wasm.CVO_reinterpret wasm.T_i64 None;
       wasm.BI_const (wasm.VAL_int64 (Wasm_int.int_of_Z i64m 32%Z));
       wasm.BI_binop wasm.T_i64 (wasm.Binop_i wasm.BOI_rotl);
       wasm.BI_get_local (loc + 1);
       wasm.BI_cvtop wasm.T_i32 wasm.CVO_reinterpret wasm.T_i64 None;
       wasm.BI_binop wasm.T_i64 (wasm.Binop_i wasm.BOI_or)].

Fixpoint numtyp_gets (nτ: rwasm.NumType) (loc: nat) : list wasm.basic_instruction :=
  match nτ with
  | rwasm.Int s rwasm.i32 =>
      [wasm.BI_get_local loc]
  | rwasm.Float rwasm.f32 =>
      [wasm.BI_get_local loc;
       wasm.BI_cvtop wasm.T_i32 wasm.CVO_reinterpret wasm.T_f32 None]
  | rwasm.Int s rwasm.i64 =>
      get_i64_local loc
  | rwasm.Float rwasm.f64 =>
      get_i64_local loc ++ 
      [wasm.BI_cvtop wasm.T_i64 wasm.CVO_reinterpret wasm.T_f64 None]
  end.
  
Fixpoint local_gets (τ: rwasm.Typ) (loc: nat) : exn err (list wasm.basic_instruction) :=
  match τ with
  | rwasm.Num nτ =>
      mret (numtyp_gets nτ loc)
  | rwasm.TVar α =>
      mret [wasm.BI_get_local loc]
  | rwasm.Unit =>
      mret []
  | rwasm.ProdT τs =>
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
  | rwasm.CoderefT χ => mthrow Todo
  | rwasm.Rec q τ =>
      local_gets τ loc
  | rwasm.PtrT ℓ =>
      mret [wasm.BI_get_local loc]
  | rwasm.ExLoc q τ =>
      local_gets τ loc
  | rwasm.OwnR ℓ =>
      mret []
  | rwasm.CapT cap ℓ ψ =>
      mret []
  | rwasm.RefT cap ℓ ψ =>
      mret [wasm.BI_get_local loc]
  end.

Fixpoint compile_instr (instr: rwasm.instr TyAnn) : wst (list wasm.basic_instruction) :=
  match instr with
  | rwasm.INumConst _ num_type num =>
      mret [wasm.BI_const $ compile_num num_type num]
  | rwasm.IUnit _ =>
      mret []
  | rwasm.INum ann ni =>
      instr ← liftM $ compile_num_instr ni;
      mret [instr]
  | rwasm.IUnreachable (rwasm.Arrow targs trets, _) =>
      mret [wasm.BI_unreachable]
  | rwasm.INop (rwasm.Arrow targs trets, _) =>
      mret [wasm.BI_nop]
  | rwasm.IDrop (rwasm.Arrow targs trets, _) =>
      match targs with
      | (t_drop :: targs) =>
        wasm_typ ← liftM $ compile_typ t_drop;
        mret $ map (const wasm.BI_drop) wasm_typ
      | [] => 
        mthrow (Err "rwasm.IDrop should have a nonempty stack type annotation")
      end
  | rwasm.ISelect (rwasm.Arrow targs trets, _) =>
      mret [wasm.BI_select]
  | rwasm.IBlock (rwasm.Arrow targs trets, _) ta _ i =>
    ta' ← liftM $ compile_arrow_type ta;
    i' ← mapM compile_instr i;
    mret [wasm.BI_block ta' (flatten i')]
  | rwasm.ILoop (rwasm.Arrow targs trets, _) arrow i =>
    ft ← liftM $ compile_arrow_type arrow;
    i' ← mapM compile_instr i;
    mret [wasm.BI_block ft (flatten i')]
  | rwasm.IIte (rwasm.Arrow targs trets, _) arrow _ t e =>
    ft ← liftM $ compile_arrow_type arrow;
    t' ← mapM compile_instr t;
    e' ← mapM compile_instr e;
    mret [wasm.BI_if ft (flatten t') (flatten e')]
  | rwasm.IBr (rwasm.Arrow targs trets, _) x => mret [wasm.BI_br x]
  | rwasm.IBrIf (rwasm.Arrow targs trets, _) x => mret [wasm.BI_br_if x]
  | rwasm.IBrTable (rwasm.Arrow targs trets, _) x x0 => mret [wasm.BI_br_table x x0]
  | rwasm.IRet (rwasm.Arrow targs trets, _) => mret [wasm.BI_return]
  | rwasm.IGetLocal (rwasm.Arrow targs trets, LSig L _) idx _ =>
      '(base, τ) ← liftM $ local_layout L 0 idx;
      liftM $ local_gets τ base
  | rwasm.ISetLocal (rwasm.Arrow targs trets, _) x =>
    mret [wasm.BI_set_local x]
  | rwasm.ITeeLocal (rwasm.Arrow targs trets, _) x => mret [wasm.BI_tee_local x]
  | rwasm.IGetGlobal (rwasm.Arrow targs trets, _) x => mret [wasm.BI_get_global x]
  | rwasm.ISetGlobal (rwasm.Arrow targs trets, _) x => mret [wasm.BI_set_global x]
  | rwasm.ICoderef (rwasm.Arrow targs trets, _) x => mthrow Todo
  | rwasm.IInst (rwasm.Arrow targs trets, _) x => mthrow Todo
  | rwasm.ICallIndirect (rwasm.Arrow targs trets, _) => mthrow Todo (* TODO: why doesn't rwasm take an immediate? *)
  | rwasm.ICall (rwasm.Arrow targs trets, _) x x0 => mthrow Todo     (* TODO: what to do with list of indexes? *)
  | rwasm.IMemUnpack _ ta tl es =>
      ta' ← liftM $ compile_arrow_type ta;
      e__s' ← flatten <$> mapM compile_instr es;
      mret [wasm.BI_block ta' e__s']
  | rwasm.IStructMalloc (rwasm.Arrow targs trets, _) szs q =>
      mthrow Todo
  | rwasm.IStructFree (rwasm.Arrow targs trets, _) =>
      mthrow Todo
             (* mret $ [wasm.BI_call Σ.(me_free)]*)
  | rwasm.IStructGet (rwasm.Arrow from to, _) n =>
      base_ref ← walloc wasm.T_i32;
      fields ← liftM $ get_struct_field_types from 0;
      field_typ ← liftM $ err_opt (list_lookup 0 to) "struct.get: cannot find output val type";
      offset_sz ← liftM $ struct_field_offset fields n;
      offset_instrs ← liftM $ compile_sz offset_sz;
      load_instrs ← tagged_load base_ref offset_instrs field_typ;
      mret $ wasm.BI_tee_local base_ref :: load_instrs
  | rwasm.IStructSet (rwasm.Arrow from to, _) n =>
      fields ← liftM $ get_struct_field_types from 1;
      val_typ ← liftM $ err_opt (list_lookup 0 from) "struct.set: cannot find input val type";
      offset_sz ← liftM $ struct_field_offset fields n;
      offset_e ← liftM $ compile_sz offset_sz;
      tagged_store offset_e val_typ
  | rwasm.IStructSwap (rwasm.Arrow from to, _) n =>
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
  | rwasm.IVariantMalloc (rwasm.Arrow from to, _) sz tys q =>
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
    | rwasm.IVariantCase ann q th ta tl es => mthrow Todo
    (* [val__init; len] → [ptr] *)
    (* [τ      ; i32] → [i32] *)
    | rwasm.IArrayMalloc (rwasm.Arrow from to, _) q =>
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
    | rwasm.IArrayGet (rwasm.Arrow from to, _) =>
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
    | rwasm.IArraySet (rwasm.Arrow from to, _) =>
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
  | rwasm.IArrayFree ann => mthrow Todo (*mret $ [wasm.BI_call Σ.(me_free)]*)
  | rwasm.IExistPack (rwasm.Arrow targs trets, _) x x0 x1 => mthrow Todo
  | rwasm.IExistUnpack (rwasm.Arrow targs trets, _) x x0 x1 x2 x3 => mthrow Todo
  | rwasm.IRefSplit _ 
  | rwasm.IRefJoin _ 
  | rwasm.IRecFold _ _
  | rwasm.IRecUnfold  _
  | rwasm.IGroup _ _ _ 
  | rwasm.IUngroup _
  | rwasm.ICapSplit _
  | rwasm.ICapJoin _
  | rwasm.IRefDemote _
  | rwasm.IMemPack _ _
  | rwasm.IQualify _ _ => mret []
  end.

Definition compile_instrs instrs := flatten <$> mapM compile_instr instrs.

End compile_instr.

Definition compile_fun_type_idx (fun_type : rwasm.FunType) : wasm.typeidx.
Admitted.

Fixpoint compile_module (module : rwasm.module TyAnn) : exn err wasm.module :=
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
with compile_func (func : rwasm.Func TyAnn) : option wasm.module_func := 
  match func with 
  | rwasm.Fun exports fun_type sizes intrs =>
    Some {|
      wasm.modfunc_type := compile_fun_type_idx fun_type;
      wasm.modfunc_locals := []; (* TODO *)
      wasm.modfunc_body := []; (* TODO *)
    |}
  end

with compile_glob (glob : rwasm.Glob TyAnn) : exn err wasm.module_glob
with compile_table (table : rwasm.Table) : exn err wasm.module_table.
Admitted.
