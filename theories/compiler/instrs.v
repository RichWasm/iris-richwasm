From Coq Require Import List.
Import Coq.Lists.List.ListNotations.
Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinInt.
Local Open Scope program_scope.

From ExtLib.Data Require Import List.
From ExtLib.Data.Monads Require Import EitherMonad StateMonad WriterMonad.
From ExtLib.Structures Require Import Functor Monads Reducible Traversable.

From stdpp Require Import list_numbers.

From Wasm Require datatypes operations.
Require Import Wasm.numerics.

From RichWasm Require term typing.
From RichWasm.compiler Require Import codegen numerics types util.
Require Import RichWasm.util.stdpp_extlib.

Module R. Include term <+ typing. End R.
Module W. Include datatypes <+ operations. End W.

Section Instrs.

  Variable me : module_env.
  Variable fe : function_env.

  Definition wlalloc (ty : W.value_type) : codegen W.localidx :=
    wl ← get;
    put (wl ++ [ty]);;
    ret (W.Mk_localidx (fe.(fe_wlocal_offset) + length wl)).

  Definition get_local_i64 (x : W.localidx) : codegen unit :=
    emit (W.BI_get_local (localimm x));;
    emit (W.BI_cvtop W.T_i32 W.CVO_reinterpret W.T_i64 None);;
    emit (W.BI_get_local (localimm x + 1));;
    emit (W.BI_const (W.VAL_int64 (Wasm_int.int_of_Z i64m 32)));;
    emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_rotl));;
    emit (W.BI_cvtop W.T_i32 W.CVO_reinterpret W.T_i64 None);;
    emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_or)).

  Definition set_local_i64 (x : W.localidx) : codegen unit :=
    y ← wlalloc W.T_i64;
    emit (W.BI_tee_local (localimm y));;
    emit (W.BI_const (W.VAL_int64 (wasm_extend_u int32_minus_one)));;
    emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_and));;
    emit (W.BI_cvtop W.T_i64 W.CVO_convert W.T_i32 None);;
    emit (W.BI_set_local (localimm x));;
    emit (W.BI_get_local (localimm y));;
    emit (W.BI_const (W.VAL_int64 (Wasm_int.int_of_Z i64m 32)));;
    emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_rotr));;
    emit (W.BI_set_local (localimm x + 1)).

  Definition get_local_w (x : W.localidx) (ty : W.value_type) : codegen unit :=
    match ty with
    | W.T_i32 => emit (W.BI_get_local (localimm x))
    | W.T_i64 => get_local_i64 x
    | W.T_f32 =>
        emit (W.BI_get_local (localimm x));;
        emit (W.BI_cvtop W.T_i32 W.CVO_reinterpret W.T_f32 None)
    | W.T_f64 =>
        get_local_i64 x;;
        emit (W.BI_cvtop W.T_i64 W.CVO_reinterpret W.T_f64 None)
    end.

  Definition get_locals_w (x : W.localidx) : W.result_type -> codegen unit :=
    ignore ∘ foldM
      (fun ty x =>
        get_local_w (W.Mk_localidx x) ty;;
        ret (x + W.words_t ty))
      (ret (localimm x)).

  Definition set_local_w (x : W.localidx) (ty : W.value_type) : codegen unit :=
    match ty with
    | W.T_i32 => emit (W.BI_set_local (localimm x))
    | W.T_i64 => set_local_i64 x
    | W.T_f32 =>
        emit (W.BI_cvtop W.T_f32 W.CVO_reinterpret W.T_i32 None);;
        emit (W.BI_set_local (localimm x))
    | W.T_f64 =>
        emit (W.BI_cvtop W.T_f64 W.CVO_reinterpret W.T_i64 None);;
        set_local_i64 x
    end.

  Definition set_locals_w (x : W.localidx) : W.result_type -> codegen unit :=
    ignore ∘ foldM
      (fun ty x =>
        set_local_w (W.Mk_localidx x) ty;;
        ret (x + W.words_t ty))
      (ret (localimm x)).

  Definition get_local (x : W.localidx) : R.Typ -> codegen unit :=
    get_locals_w x ∘ translate_type.

  Definition set_local (x : W.localidx) : R.Typ -> codegen unit :=
    set_locals_w x ∘ translate_type.

  Definition save_stack_w (ty : W.result_type) : codegen W.localidx :=
    xs ← forT ty wlalloc;
    ret (ssrfun.Option.default (W.Mk_localidx 0) (head xs)).

  Definition save_stack : list R.Typ -> codegen W.localidx :=
    save_stack_w ∘ flat_map translate_type.

  Definition restore_stack_w (x : W.localidx) (ty : W.result_type) : codegen unit :=
    ignore (forT (seq (localimm x) (length ty)) (emit ∘ W.BI_get_local)).

  Definition restore_stack (x : W.localidx) : list R.Typ -> codegen unit :=
    restore_stack_w x ∘ flat_map translate_type.

  Definition if_gc_bit {A B} (tf : W.function_type) (gc : codegen B) (mm : codegen A) : codegen (A * B) :=
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 1%Z)));;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_and));;
    emit (W.BI_testop W.T_i32 W.TO_eqz);;
    if_c tf mm gc.

  Definition clear_gc_bit : codegen unit :=
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 1%Z)));;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_sub)).

  Definition load_values_w (mem : W.memidx) (ptr : W.localidx) (off : W.static_offset)
    : W.result_type -> codegen unit :=
    ignore ∘ foldM
      (fun ty off =>
        emit (W.BI_get_local (localimm ptr));;
        emit (W.BI_load (memimm mem) ty None 0%N off);;
        ret (off + N.of_nat (W.length_t ty))%N)
      (ret off).

  Definition load_value (mem : W.memidx) (ptr : W.localidx) (off : W.static_offset)
    : R.Typ -> codegen unit :=
    load_values_w mem ptr off ∘ translate_type.

  Definition load_value_tagged_w (get_offset : codegen unit) (ty : W.value_type) : codegen unit :=
    ptr ← wlalloc W.T_i32;
    emit (W.BI_tee_local (localimm ptr));;
    emit (W.BI_get_local (localimm ptr));;
    if_gc_bit (W.Tf [] [])
      (clear_gc_bit;;
       get_offset;;
       emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add));;
       emit (W.BI_load (memimm me.(me_runtime).(mr_mem_gc)) ty None 0%N 0%N))
      (get_offset;;
       emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add));;
       emit (W.BI_load (memimm me.(me_runtime).(mr_mem_mm)) ty None 0%N 0%N));;
    ret tt.

  Definition set_offset (ptr : W.localidx) (get_offset : codegen unit) : codegen unit :=
    get_offset;;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add));;
    emit (W.BI_set_local (localimm ptr)).

  Definition load_value_tagged (get_offset : codegen unit) (ty : R.Typ) : codegen unit :=
    ptr ← wlalloc W.T_i32;
    emit (W.BI_tee_local (localimm ptr));;
    emit (W.BI_get_local (localimm ptr));;
    if_gc_bit (W.Tf [] [])
      (clear_gc_bit;;
       set_offset ptr get_offset;;
       load_value me.(me_runtime).(mr_mem_gc) ptr 0%N ty)
      (set_offset ptr get_offset;;
       load_value me.(me_runtime).(mr_mem_mm) ptr 0%N ty);;
    ret tt.

  Definition store_value_w
    (mem : W.memidx) (ptr : W.localidx) (off : W.static_offset)
    (val : W.localidx) (ty : W.value_type)
    : codegen unit :=
    emit (W.BI_get_local (localimm ptr));;
    emit (W.BI_get_local (localimm val));;
    emit (W.BI_store (memimm mem) ty None 0%N off).

  Definition store_values_w (mem : W.memidx) (ptr : W.localidx) (off : W.static_offset)
    : list (W.localidx * W.value_type) -> codegen unit :=
    ignore ∘ foldM
      (fun '(val, ty) off =>
        store_value_w mem ptr off val ty;;
        ret (off + N.of_nat (W.length_t ty))%N)
      (ret off).

  Definition store_value (mem : W.memidx) (ptr : W.localidx) (off : W.static_offset) (val : W.localidx) (ty : R.Typ)
    : codegen unit :=
    let ty' := translate_type ty in
    let vals := zip (map W.Mk_localidx (seq (localimm val) (length ty'))) ty' in
    store_values_w mem ptr off vals.

  Definition store_value_tagged (get_offset : codegen unit) (ty : R.Typ) : codegen unit :=
    val ← save_stack [ty];
    ptr ← wlalloc W.T_i32;
    emit (W.BI_tee_local (localimm ptr));;
    emit (W.BI_get_local (localimm ptr));;
    if_gc_bit (W.Tf [] [])
      (clear_gc_bit;;
       set_offset ptr get_offset;;
       store_value me.(me_runtime).(mr_mem_gc) ptr 0%N val ty)
      (set_offset ptr get_offset;;
       store_value me.(me_runtime).(mr_mem_mm) ptr 0%N val ty);;
    ret tt.

  Definition foreach_when_gc_bit (scope : VarScope) (refs : list W.immediate) (c : codegen unit)
    : codegen unit :=
    iterM
      (fun var =>
        let '(get, set) := scope_get_set scope in
        emit (get var);;
        if_gc_bit (W.Tf [W.T_i32] [W.T_i32]) c (ret tt);;
        emit (set var))
      refs.

  Definition lookup_local (L : R.Local_Ctx) (idx : nat) : error + (W.localidx * R.Typ) :=
    let fix go L i j :=
      match L, j with
      | (ty, sz) :: _, 0 => inr (W.Mk_localidx i, ty)
      | (ty, sz) :: L', S j' =>
          real_sz ← size_upper_bound fe.(fe_size_bounds) sz;
          go L' (i + real_sz) j'
      | [], _ => inl (EIndexOutOfBounds idx)
      end
    in
    go L 0 idx.

  Definition lookup_global (idx : nat) : option (W.globalidx * R.Typ) :=
    let fix go globals idx :=
      match globals, idx with
      | R.GT _ ty :: _, 0 => Some (W.Mk_globalidx 0, ty)
      | R.GT _ ty :: globals', S idx' =>
          let width := length (translate_type ty) in
          go globals' (width + idx')
      | [], _ => None
      end
    in
    go me.(me_globals) idx.

  Fixpoint compile_size (sz : R.Size) : codegen unit :=
    match sz with
    | R.SizeVar σ =>
        x ← try_option (EIndexOutOfBounds σ) (lookup σ fe.(fe_size_locals));
        emit (W.BI_get_local (localimm x))
    | R.SizePlus sz1 sz2 =>
        compile_size sz1;;
        compile_size sz2;;
        emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add))
    | R.SizeConst c =>
        emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat c))))
    end.

  Definition compile_index (idx: R.Index) : codegen unit :=
    match idx with
    | R.SizeI sz => compile_size sz
    | R.LocI _
    | R.QualI _
    | R.TypI _ => ret tt
    end.

  Definition if_index_in_bounds {A} (tf : W.function_type) (idx : W.localidx) (c : codegen A)
    : codegen A :=
    load_value_tagged_w
      (emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat 0)))))
      (W.T_i32);;
    emit (W.BI_get_local (localimm idx));;
    emit (W.BI_relop W.T_i32 (W.Relop_i (W.ROI_lt (W.SX_U))));;
    fst <$> if_c tf c (emit W.BI_unreachable).

  Definition get_elem_offset (idx : W.localidx) (size : nat) : codegen unit :=
    emit (W.BI_get_local (localimm idx));;
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat size))));;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_mul));;
    (* Skip 4 bytes for the array length. *)
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat 4))));;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add)).

  Definition compile_drop (ty : R.Typ) : codegen unit :=
    val ← save_stack [ty];
    let refs := map (fun i => localimm val + i) (find_refs LMNative ty) in
    foreach_when_gc_bit VSLocal refs
      (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot))));;
    restore_stack val [ty];;
    let tys := translate_type ty in
    forT tys (const (emit W.BI_drop));;
    ret tt.

  Definition compile_return (ty : list R.Typ) : codegen unit :=
    let return_ty := ssrfun.Option.default [] fe.(fe_return_type) in
    let drop_ty := take (length ty - length return_ty) ty in
    r ← save_stack return_ty;
    d ← save_stack drop_ty;
    let refs := map (fun i => localimm d + i) (flat_map (find_refs LMNative) drop_ty) in
    foreach_when_gc_bit VSLocal refs
      (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot))));;
    restore_stack r return_ty;;
    emit W.BI_return.

  Definition compile_get_local (L : R.Local_Ctx) (x : nat) : codegen unit :=
    '(x', ty) ← lift_error (lookup_local L x);
    get_local x' ty;;
    val ← save_stack [ty];
    let refs := map (fun i => localimm val + i) (find_refs LMNative ty) in
    foreach_when_gc_bit VSLocal refs
      (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_duproot))));;
    restore_stack val [ty].

  Definition compile_set_local (L : R.Local_Ctx) (x : nat) : codegen unit :=
    '(x', ty) ← lift_error (lookup_local L x);
    let refs := map (fun i => localimm x' + i) (find_refs LMWords ty) in
    foreach_when_gc_bit VSLocal refs
      (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot))));;
    set_local x' ty.

  Definition compile_get_global (x : nat) : codegen unit :=
    '(x', ty) ← try_option (EIndexOutOfBounds x) (lookup_global x);
    forT (imap (fun i _ => globalimm x' + i) (translate_type ty))
      (emit ∘ W.BI_get_global);;
    val ← save_stack [ty];
    let refs := map (fun i => localimm val + i) (find_refs LMNative ty) in
    foreach_when_gc_bit VSLocal refs
      (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_duproot))));;
    restore_stack val [ty].

  Definition compile_set_global (x : nat) : codegen unit :=
    '(x', ty) ← try_option (EIndexOutOfBounds x) (lookup_global x);
    let refs := map (fun i => globalimm x' + i) (find_refs LMNative ty) in
    foreach_when_gc_bit VSGlobal refs
      (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot))));;
    forT (imap (fun i _ => globalimm x' + i) (translate_type ty))
      (emit ∘ W.BI_set_global);;
    ret tt.

  Definition compile_coderef (x : nat) : codegen unit :=
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat x))));;
    emit (W.BI_get_global (globalimm me.(me_runtime).(mr_global_table_offset)));;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add)).

  Definition compile_call_indirect (arg_ty : list R.Typ) (idxs : list R.Index) : codegen unit :=
    arg ← save_stack arg_ty;
    forT idxs compile_index;;
    restore_stack arg arg_ty;;
    emit (W.BI_call_indirect (tableimm me.(me_runtime).(mr_table))).

  Definition compile_call (arg_ty : list R.Typ) (x : nat) (idxs : list R.Index) : codegen unit :=
    arg ← save_stack arg_ty;
    forT idxs compile_index;;
    restore_stack arg arg_ty;;
    (* TODO: Translate function index. *)
    emit (W.BI_call x).

  Definition compile_struct_get (tys : list R.Typ) (sizes : list R.Size) (i : nat) : codegen unit :=
    field_ty ← try_option EWrongTypeAnn (tys !! i);
    offset ← lift_error (struct_field_offset sizes i);
    ref ← wlalloc W.T_i32;
    load_value_tagged (compile_size offset) field_ty;;
    val ← save_stack [field_ty];
    let refs := map (fun i => localimm val + i) (find_refs LMNative field_ty) in
    emit (W.BI_get_local (localimm ref));;
    if_gc_bit (W.Tf [] [])
      (foreach_when_gc_bit VSLocal refs
         (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_registerroot)))))
      (foreach_when_gc_bit VSLocal refs
         (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_duproot)))));;
    restore_stack val [field_ty].

  Definition compile_struct_set (tys : list R.Typ) (sizes : list R.Size) (val_ty : R.Typ) (i : nat) : codegen unit :=
    field_ty ← try_option EWrongTypeAnn (tys !! i);
    offset ← lift_error (struct_field_offset sizes i);

    val ← save_stack [val_ty];
    ptr ← wlalloc W.T_i32;
    emit (W.BI_tee_local (localimm ptr));;
    if_gc_bit (W.Tf [] [])
      (let refs := map (fun i => localimm val + i) (find_refs LMNative val_ty) in
       foreach_when_gc_bit VSLocal refs
         (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot)))))
      (emit (W.BI_get_local (localimm ptr));;
       ptr' ← wlalloc W.T_i32;
       set_offset ptr' (compile_size offset);;
       load_value me.(me_runtime).(mr_mem_mm) ptr' 0%N field_ty;;
       old_val ← save_stack [field_ty];
       let refs := map (fun i => localimm val + i) (find_refs LMNative field_ty) in
       foreach_when_gc_bit VSLocal refs
         (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot)))));;

    emit (W.BI_get_local (localimm ptr));;
    store_value_tagged (compile_size offset) val_ty.

  Definition compile_array_get (elem_ty : R.Typ) : codegen unit :=
    (* TODO: registerroot if GC array; duproot if MM array. *)
    idx ← wlalloc W.T_i32;
    ptr ← wlalloc W.T_i32;
    emit (W.BI_set_local (localimm idx));;
    emit (W.BI_tee_local (localimm ptr));;
    let elem_tys := translate_type elem_ty in
    if_index_in_bounds (W.Tf [] elem_tys) idx
      (emit (W.BI_get_local (localimm ptr));;
       load_value_tagged (get_elem_offset idx (type_words elem_ty)) elem_ty).

  Definition compile_array_set (elem_ty : R.Typ) : codegen unit :=
    (* TODO: unregisterroot if GC array; duproot a bunch of times if MM array. *)
    val ← save_stack [elem_ty];
    idx ← wlalloc W.T_i32;
    ptr ← wlalloc W.T_i32;
    emit (W.BI_set_local (localimm idx));;
    emit (W.BI_tee_local (localimm ptr));;
    if_index_in_bounds (W.Tf [] []) idx
      (emit (W.BI_get_local (localimm ptr));;
       restore_stack val [elem_ty];;
       store_value_tagged (get_elem_offset idx (type_words elem_ty)) elem_ty).

  Fixpoint compile_instr (e : R.instr R.TyAnn) : codegen unit :=
    match e with
    | R.INumConst _ ty n => emit (W.BI_const (compile_Z (translate_num_type ty) (Z.of_nat n)))
    | R.IUnit _ => ret tt
    | R.INum _ e' => emit (compile_num_instr e')
    | R.IUnreachable _ => emit (W.BI_unreachable)
    | R.INop _ => emit W.BI_nop
    | R.IDrop (R.Arrow ty _, _) => try_option EWrongTypeAnn (head ty) ≫= compile_drop
    | R.IBlock _ ty _ es => ignore (block_c (translate_arrow_type ty) (forT es compile_instr))
    | R.ILoop _ ty es => ignore (loop_c (translate_arrow_type ty) (forT es compile_instr))
    | R.IIte _ ty _ es1 es2 =>
        ignore (if_c (translate_arrow_type ty) (forT es1 compile_instr) (forT es2 compile_instr))
    | R.IBr _ l => emit (W.BI_br l)
    | R.IBrIf _ l => emit (W.BI_br_if l)
    | R.IBrTable _ ls l => emit (W.BI_br_table ls l)
    | R.IRet (R.Arrow ty _, _) => compile_return ty
    | R.IGetLocal (_, R.LSig L _) x _ => compile_get_local L x
    | R.ISetLocal (_, R.LSig L _) x => compile_set_local L x
    | R.IGetGlobal _ x => compile_get_global x
    | R.ISetGlobal _ x => compile_set_global x
    | R.ICoderef _ x => compile_coderef x
    | R.ICallIndirect (R.Arrow arg_ty _, _) idxs => compile_call_indirect arg_ty idxs
    | R.ICall (R.Arrow arg_ty _, _) x idxs => compile_call arg_ty x idxs
    | R.IMemUnpack _ ty _ es => ignore (block_c (translate_arrow_type ty) (forT es compile_instr))
    | R.IStructMalloc _ _ _ =>
        (* TODO: registerroot on the new address;
                 unregisterroot if any field is GC ref being put into GC struct. *)
        (* compute size for malloc *)
        (* call malloc and save result *)
        (* load args into locals *)
        (* do an IStructSet on each arg *)
        (* return the base pointer *)
        raise ETodo
    | R.IStructFree _ =>
        (* TODO: unregisterroot fields that may be refs to GC if this struct is MM. *)
        emit (W.BI_call (funcimm me.(me_runtime).(mr_func_free)))
    | R.IStructGet (R.Arrow in_ty _, _) i =>
        fields ← try_option EWrongTypeAnn (head in_ty ≫= struct_fields);
        let (tys, sizes) := split fields in
        compile_struct_get tys sizes i
    | R.IStructSet (R.Arrow in_ty _, _) i =>
        fields ← try_option EWrongTypeAnn (head in_ty ≫= struct_fields);
        val_ty ← try_option EWrongTypeAnn (lookup 1 in_ty);
        let (tys, sizes) := split fields in
        compile_struct_set tys sizes val_ty i
    | R.IStructSwap _ _ =>
        (* TODO: registerroot if GC struct *)
        raise ETodo
    | R.IVariantMalloc _ _ _ _ =>
        (* TODO: registerroot on the new address;
                 unregisterroot if payload is GC ref being put into GC variant *)
        raise ETodo
    | R.IVariantCase _ _ _ _ _ _ =>
        (* TODO: duproot if unrestricted *)
        raise ETodo
    | R.IArrayMalloc _ _ =>
        (* TODO: unregisterroot the initial value if GC array;
                 duproot a bunch of times if MM array *)
        raise ETodo
    | R.IArrayGet (R.Arrow in_ty _, _) =>
        try_option EWrongTypeAnn (head in_ty ≫= array_elem) ≫= compile_array_get
    | R.IArraySet (R.Arrow in_ty _, _) =>
        try_option EWrongTypeAnn (head in_ty ≫= array_elem) ≫= compile_array_set
    | R.IArrayFree ann =>
        (* TODO: unregisterroot a bunch of times, since this is an MM array *)
        emit (W.BI_call (funcimm me.(me_runtime).(mr_func_free)))
    | R.IExistPack (R.Arrow targs trets, _) t th q =>
        (* TODO: unregisterroot if GC package *)
        raise ETodo
    | R.IExistUnpack (R.Arrow targs trets, _) q th ta tl es =>
        (* TODO: registerroot if GC package *)
        raise ETodo
    | R.IRefSplit _
    | R.IRefJoin _
    | R.IRecFold _ _
    | R.IRecUnfold  _
    | R.IGroup _ _
    | R.IUngroup _
    | R.ICapSplit _
    | R.ICapJoin _
    | R.IRefDemote _
    | R.IMemPack _ _
    | R.IQualify _ _ => ret tt
    end.

  Definition compile_instrs : list (R.instr R.TyAnn) -> codegen unit :=
    iterM compile_instr.

End Instrs.
