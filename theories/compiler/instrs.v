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

From RichWasm Require Import prelude syntax typing.
From RichWasm.compiler Require Import codegen numerics types util.
Require Import RichWasm.util.stdpp_extlib.

Module W. Include datatypes <+ operations. End W.

Section Instrs.

  Variable me : module_env.
  Variable fe : function_env.

  Definition translate_type : type -> option (list W.value_type) :=
    translate_type fe.(fe_type_vars).

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

  Definition get_local (x : W.localidx) (τ : type) : codegen unit :=
    ty ← try_option EWrongTypeAnn (translate_type τ);
    get_locals_w x ty.

  Definition set_local (x : W.localidx) (τ : type) : codegen unit :=
    ty ← try_option EWrongTypeAnn (translate_type τ);
    set_locals_w x ty.

  Definition save_stack_w (ty : W.result_type) : codegen W.localidx :=
    xs ← forT ty wlalloc;
    forT (reverse xs) (emit ∘ W.BI_set_local ∘ localimm);;
    ret (ssrfun.Option.default (W.Mk_localidx 0) (head xs)).

  Definition save_stack (τs : list type) : codegen W.localidx :=
    tys ← try_option EWrongTypeAnn (mapM translate_type τs);
    save_stack_w (concat tys).

  Definition restore_stack_w (x : W.localidx) (ty : W.result_type) : codegen unit :=
    ignore (forT (seq (localimm x) (length ty)) (emit ∘ W.BI_get_local)).

  Definition restore_stack (x : W.localidx) (τs : list type) : codegen unit :=
    tys ← try_option EWrongTypeAnn (mapM translate_type τs);
    restore_stack_w x (concat tys).

  Definition if_gc_bit {A B} (tf : W.function_type) (gc : codegen B) (mm : codegen A) : codegen (A * B) :=
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 1%Z)));;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_and));;
    emit (W.BI_testop W.T_i32 W.TO_eqz);;
    if_c tf mm gc.

  Definition clear_gc_bit : codegen unit :=
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 1%Z)));;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_sub)).

  Definition load_values_w (mem : W.memidx) (ptr : W.localidx) (off : W.static_offset) :
    W.result_type -> codegen unit :=
    ignore ∘ foldM
      (fun ty off =>
        emit (W.BI_get_local (localimm ptr));;
        emit (W.BI_load (memimm mem) ty None 0%N off);;
        ret (off + N.of_nat (W.length_t ty))%N)
      (ret off).

  Definition load_value (mem : W.memidx) (ptr : W.localidx) (off : W.static_offset) (τ : type) :
    codegen unit :=
    tys ← try_option EWrongTypeAnn (translate_type τ);
    load_values_w mem ptr off tys.

  Definition load_value_tagged_w (ty : W.value_type) : codegen unit :=
    ptr ← wlalloc W.T_i32;
    emit (W.BI_tee_local (localimm ptr));;
    emit (W.BI_get_local (localimm ptr));;
    if_gc_bit (W.Tf [] [])
      (clear_gc_bit;;
       emit (W.BI_load (memimm me.(me_runtime).(mr_mem_gc)) ty None 0%N 0%N))
      (emit (W.BI_load (memimm me.(me_runtime).(mr_mem_mm)) ty None 0%N 0%N));;
    ret tt.

  Definition load_value_tagged (offset : W.localidx) (τ : type) : codegen unit :=
    ptr ← wlalloc W.T_i32;
    emit (W.BI_tee_local (localimm ptr));;
    emit (W.BI_get_local (localimm ptr));;
    if_gc_bit (W.Tf [] [])
      (clear_gc_bit;;
       emit (W.BI_get_local (localimm offset));;
       emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add));;
       emit (W.BI_set_local (localimm ptr));;
       load_value me.(me_runtime).(mr_mem_gc) ptr 0%N τ)
      (emit (W.BI_get_local (localimm offset));;
       emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add));;
       emit (W.BI_set_local (localimm ptr));;
       load_value me.(me_runtime).(mr_mem_mm) ptr 0%N τ);;
    ret tt.

  Definition store_value_w
    (mem : W.memidx) (ptr : W.localidx) (off : W.static_offset)
    (val : W.localidx) (ty : W.value_type) :
    codegen unit :=
    emit (W.BI_get_local (localimm ptr));;
    emit (W.BI_get_local (localimm val));;
    emit (W.BI_store (memimm mem) ty None 0%N off).

  Definition store_values_w (mem : W.memidx) (ptr : W.localidx) (off : W.static_offset) :
    list (W.localidx * W.value_type) -> codegen unit :=
    ignore ∘ foldM
      (fun '(val, ty) off =>
        store_value_w mem ptr off val ty;;
        ret (off + N.of_nat (W.length_t ty))%N)
      (ret off).

  Definition store_value
    (mem : W.memidx) (ptr : W.localidx) (off : W.static_offset) (val : W.localidx) (τ : type) :
    codegen unit :=
    ty ← try_option EWrongTypeAnn (translate_type τ);
    let vals := zip (map W.Mk_localidx (seq (localimm val) (length ty))) ty in
    store_values_w mem ptr off vals.

  Definition store_value_tagged (offset : W.localidx) (τ : type) : codegen unit :=
    val ← save_stack [τ];
    ptr ← wlalloc W.T_i32;
    emit (W.BI_tee_local (localimm ptr));;
    emit (W.BI_get_local (localimm ptr));;
    if_gc_bit (W.Tf [] [])
      (clear_gc_bit;;
       emit (W.BI_get_local (localimm offset));;
       emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add));;
       emit (W.BI_set_local (localimm ptr));;
       store_value me.(me_runtime).(mr_mem_gc) ptr 0%N val τ)
      (emit (W.BI_get_local (localimm offset));;
       emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add));;
       emit (W.BI_set_local (localimm ptr));;
       store_value me.(me_runtime).(mr_mem_mm) ptr 0%N val τ);;
    ret tt.

  Definition foreach_when_gc_bit (scope : VarScope) (refs : list W.immediate) (c : codegen unit) :
    codegen unit :=
    iterM
      (fun var =>
        let '(get, set) := scope_get_set scope in
        emit (get var);;
        if_gc_bit (W.Tf [W.T_i32] [W.T_i32]) c (ret tt);;
        emit (set var))
      refs.

  Definition lookup_local (L : local_ctx) (x : nat) : error + (W.localidx * type) :=
    let fix go L i j :=
      match L, j with
      | τ :: _, 0 => inr (W.Mk_localidx i, τ)
      | τ :: L', S j' =>
          ty ← option_sum EWrongTypeAnn (translate_type τ);
          go L' (i + length ty) j'
      | [], _ => inl (EIndexOutOfBounds x)
      end
    in
    go L 0 x.

  Definition lookup_global (x : nat) : option (W.globalidx * type) :=
    let fix go globals i :=
      match globals, i with
      | τ :: _, 0 => Some (W.Mk_globalidx 0, τ)
      | τ :: globals', S i' =>
          ty ← translate_type τ;
          let width := length ty in
          go globals' (width + i')
      | [], _ => None
      end
    in
    go me.(me_globals) x.

  Definition trap_if_index_out_of_bounds (idx : W.localidx) : codegen unit :=
    load_value_tagged_w W.T_i32;;
    emit (W.BI_get_local (localimm idx));;
    emit (W.BI_relop W.T_i32 (W.Relop_i (W.ROI_lt (W.SX_U))));;
    fst <$> if_c (W.Tf [] []) (ret tt) (emit W.BI_unreachable).

  Definition get_elem_offset (size : nat) : codegen unit :=
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat size))));;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_mul));;
    (* Skip 4 bytes for the array length. *)
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat 4))));;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add)).

  Definition compile_drop (τ : type) : codegen unit :=
    (* TODO:
    val ← save_stack [ty];
    let refs := map (fun i => localimm val + i) (find_refs LMNative ty) in
    foreach_when_gc_bit VSLocal refs
      (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot))));;
    restore_stack val [ty];;
    let tys := translate_type ty in
    forT tys (const (emit W.BI_drop));;
    *)
    ret tt.

  Definition compile_return (τs : list type) : codegen unit :=
    (* TODO:
    let return_ty := ssrfun.Option.default [] fe.(fe_return_type) in
    let drop_ty := take (length ty - length return_ty) ty in
    r ← save_stack return_ty;
    d ← save_stack drop_ty;
    let refs := map (fun i => localimm d + i) (flat_map (find_refs LMNative) drop_ty) in
    foreach_when_gc_bit VSLocal refs
      (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot))));;
    restore_stack r return_ty;;
    *)
    emit W.BI_return.

  Definition compile_get_local (L : local_ctx) (x : nat) : codegen unit :=
    (* TODO:
    '(x', ty) ← lift_error (lookup_local L x);
    get_local x' ty;;
    val ← save_stack [ty];
    let refs := map (fun i => localimm val + i) (find_refs LMNative ty) in
    foreach_when_gc_bit VSLocal refs
      (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_duproot))));;
    restore_stack val [ty]
    *)
    ret tt.

  Definition compile_set_local (L : local_ctx) (x : nat) : codegen unit :=
    (* TODO:
    '(x', ty) ← lift_error (lookup_local L x);
    let refs := map (fun i => localimm x' + i) (find_refs LMWords ty) in
    foreach_when_gc_bit VSLocal refs
      (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot))));;
    set_local x' ty
    *)
    ret tt.

  Definition compile_get_global (x : nat) : codegen unit :=
    (* TODO:
    '(x', ty) ← try_option (EIndexOutOfBounds x) (lookup_global x);
    forT (imap (fun i _ => globalimm x' + i) (translate_type ty))
      (emit ∘ W.BI_get_global);;
    val ← save_stack [ty];
    let refs := map (fun i => localimm val + i) (find_refs LMNative ty) in
    foreach_when_gc_bit VSLocal refs
      (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_duproot))));;
    restore_stack val [ty]
    *)
    ret tt.

  Definition compile_set_global (x : nat) : codegen unit :=
    (* TODO:
    '(x', ty) ← try_option (EIndexOutOfBounds x) (lookup_global x);
    let refs := map (fun i => globalimm x' + i) (find_refs LMNative ty) in
    foreach_when_gc_bit VSGlobal refs
      (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot))));;
    forT (imap (fun i _ => globalimm x' + i) (translate_type ty))
      (emit ∘ W.BI_set_global);;
    *)
    ret tt.

  Definition compile_coderef (x : nat) : codegen unit :=
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat x))));;
    emit (W.BI_get_global (globalimm me.(me_runtime).(mr_global_table_offset)));;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add)).

  Definition compile_call_indirect (τs : list type) : codegen unit :=
    (* TODO:
    arg ← save_stack arg_ty;
    forT idxs compile_index;;
    restore_stack arg arg_ty;;
    emit (W.BI_call_indirect (tableimm me.(me_runtime).(mr_table)))
    *)
    ret tt.

  Definition compile_call (τs : list type) (x : nat) (ixs : list index) : codegen unit :=
    (* TODO:
    arg ← save_stack arg_ty;
    forT idxs compile_index;;
    restore_stack arg arg_ty;;
    (* TODO: Translate function index. *)
    emit (W.BI_call x).
    *)
    ret tt.

  (* TODO: Struct replaced by product type.
  Definition compile_struct_get (tys : list R.Typ) (sizes : list R.Size) (i : nat) : codegen unit :=
    ptr ← wlalloc W.T_i32;
    emit (W.BI_tee_local (localimm ptr));;

    offset_sz ← lift_error (struct_field_offset sizes i);
    compile_size offset_sz;;
    offset ← wlalloc W.T_i32;
    emit (W.BI_set_local (localimm offset));;

    field_ty ← try_option EWrongTypeAnn (tys !! i);
    load_value_tagged offset field_ty;;

    val ← save_stack [field_ty];
    let refs := map (fun i => localimm val + i) (find_refs LMNative field_ty) in
    emit (W.BI_get_local (localimm ptr));;
    if_gc_bit (W.Tf [] [])
      (foreach_when_gc_bit VSLocal refs
         (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_registerroot)))))
      (foreach_when_gc_bit VSLocal refs
         (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_duproot)))));;
    restore_stack val [field_ty].
  *)

  (* TODO: Struct replaced by product type.
  Definition compile_struct_set (tys : list R.Typ) (sizes : list R.Size) (val_ty : R.Typ) (i : nat) :
    codegen unit :=
    offset_sz ← lift_error (struct_field_offset sizes i);
    compile_size offset_sz;;
    offset ← wlalloc W.T_i32;
    emit (W.BI_set_local (localimm offset));;

    val ← save_stack [val_ty];
    ptr ← wlalloc W.T_i32;
    emit (W.BI_tee_local (localimm ptr));;
    if_gc_bit (W.Tf [] [])
      (let refs := map (fun i => localimm val + i) (find_refs LMNative val_ty) in
       foreach_when_gc_bit VSLocal refs
         (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot)))))
      (emit (W.BI_get_local (localimm ptr));;
       ptr' ← wlalloc W.T_i32;
       emit (W.BI_get_local (localimm offset));;
       emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add));;
       emit (W.BI_set_local (localimm ptr'));;

       field_ty ← try_option EWrongTypeAnn (tys !! i);
       load_value me.(me_runtime).(mr_mem_mm) ptr' 0%N field_ty;;
       old_val ← save_stack [field_ty];
       let refs := map (fun i => localimm val + i) (find_refs LMNative field_ty) in
       foreach_when_gc_bit VSLocal refs
         (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot)))));;

    emit (W.BI_get_local (localimm ptr));;
    store_value_tagged offset val_ty.
  *)

  (* TODO: Struct replaced by product type.
  Definition compile_struct_swap
    (ptr : W.localidx)
    (tys : list R.Typ)
    (sizes : list R.Size)
    (val_ty : R.Typ)
    (i : nat)
  : codegen unit :=
    field_ty ← try_option EWrongTypeAnn (tys !! i);
    emit (W.BI_get_local (localimm ptr));;
    compile_struct_get tys sizes i;;
    old ← save_stack [field_ty];
    compile_struct_set tys sizes val_ty i;;
    restore_stack old [field_ty].
  *)

  Definition compile_array_get (π : path) (τ : type) : codegen unit :=
    (* TODO: registerroot if GC array; duproot if MM array. *)
    (* TODO:
    idx ← wlalloc W.T_i32;
    emit (W.BI_tee_local (localimm idx));;
    get_elem_offset (type_words elem_ty);;
    offset ← wlalloc W.T_i32;
    emit (W.BI_set_local (localimm offset));;
    ptr ← wlalloc W.T_i32;
    emit (W.BI_tee_local (localimm ptr));;
    emit (W.BI_get_local (localimm ptr));;
    trap_if_index_out_of_bounds idx;;
    load_value_tagged offset elem_ty
    *)
    ret tt.

  Definition compile_array_set (π : path) (τ : type) : codegen unit :=
    (* TODO: unregisterroot if GC array; duproot a bunch of times if MM array. *)
    (* TODO:
    val ← save_stack [elem_ty];
    idx ← wlalloc W.T_i32;
    emit (W.BI_tee_local (localimm idx));;
    get_elem_offset (type_words elem_ty);;
    offset ← wlalloc W.T_i32;
    emit (W.BI_set_local (localimm offset));;
    ptr ← wlalloc W.T_i32;
    emit (W.BI_tee_local (localimm ptr));;
    trap_if_index_out_of_bounds idx;;
    emit (W.BI_get_local (localimm ptr));;
    restore_stack val [elem_ty];;
    store_value_tagged offset elem_ty.
    *)
    ret tt.

  Fixpoint compile_variant_case
    (ptr : W.localidx) (n : nat) (i : nat) (tf : W.function_type) (cases : list (type * W.expr)) :
    codegen unit :=
    (* TODO:
    match cases with
    | [] =>
        block_c tf
          (offset ← wlalloc W.T_i32;
           emit (W.BI_const (compile_Z W.T_i32 (Z.of_nat 0)));;
           emit (W.BI_set_local (localimm offset));;
           emit (W.BI_get_local (localimm ptr));;
           load_value_tagged offset (R.Num (R.Int R.S R.i32));;
           emit (W.BI_br_table (seq 0 n) 0)) (* default value should never happen *)
    | (ty, es) :: cases' =>
        block_c tf
          (compile_variant_case ptr n (i + 1) tf cases';;
           offset ← wlalloc W.T_i32;
           emit (W.BI_const (compile_Z W.T_i32 (Z.of_nat 4)));; (* skip length *)
           emit (W.BI_set_local (localimm offset));;
           load_value_tagged offset ty;;
           emit_all es;;
           emit (W.BI_br (n - i + 1))) (* TODO: make sure this is right *)
    end
    *)
    ret tt.

  (* Produces code that consumes a size on the top of the stack and returns a ref *) 
  Definition compile_malloc (μ : memory) : codegen unit :=
    (* TODO:
    compile_qual q;;
    emit (W.BI_if (W.Tf [W.T_i32] [W.T_i32])
            [W.BI_call (funcimm me.(me_runtime).(mr_func_lin_alloc))]
            [W.BI_call (funcimm me.(me_runtime).(mr_func_gc_alloc))])
    *)
    ret tt.

  Fixpoint compile_instr (e : instruction) : codegen unit :=
    match e with
    | INop _ => emit W.BI_nop
    | IDrop (ArrowT τs _) => try_option EWrongTypeAnn (head τs) ≫= compile_drop
    | IUnreachable _ => emit (W.BI_unreachable)
    | INum _ e' => emit (compile_num_instr e')
    | INumConst _ ν n =>
        (* TODO: emit (W.BI_const (compile_Z (translate_num_type ty) (Z.of_nat n))) *)
        raise ETodo
    | IBlock _ _ _ =>
        (* TODO: ignore (block_c (translate_arrow_type ty) (forT es compile_instr)) *)
        raise ETodo
    | ILoop _ _ =>
        (* TODO: ignore (loop_c (translate_arrow_type ty) (forT es compile_instr)) *)
        raise ETodo
    | IIte _ _ _ _ =>
        (* TODO: ignore (if_c (translate_arrow_type ty) (forT es1 compile_instr) (forT es2 compile_instr)) *)
        raise ETodo
    | IBr _ n => emit (W.BI_br n)
    | IBrIf _ n => emit (W.BI_br_if n)
    | IBrTable _ ns n => emit (W.BI_br_table ns n)
    | IReturn (ArrowT τs _) => compile_return τs
    | ILocalGet _ _ =>
        (* TODO: compile_get_local L x *)
        raise ETodo
    | ILocalSet _ x =>
        (* TODO: compile_set_local L x *)
        raise ETodo
    | IGlobalGet _ x => compile_get_global x
    | IGlobalSet _ x => compile_set_global x
    | ICodeRef _ x => compile_coderef x
    | IInst _ _ => raise ETodo
    | ICall (ArrowT τs _) x ixs => compile_call τs x ixs
    | ICallIndirect (ArrowT τs _) => compile_call_indirect τs
    | IInject _ _ =>
        (* TODO: registerroot on the new address;
                 unregisterroot if payload is GC ref being put into GC variant *)
        raise ETodo
    | ICase _ _ _ => raise ETodo
    | IGroup _ _ => raise ETodo
    | IUngroup _ => raise ETodo
    | IFold _ _ => raise ETodo
    | IUnfold  _ => raise ETodo
    | IPack _ _ _ =>
        (* TODO:
        contents_idx ← save_stack [tau];
        (* TODO: unregisterroot if GC package *)
        let hsz_bytes := 4 * type_words htau in
        emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat hsz_bytes))));;
        compile_malloc q;;
        (* save the tagged pointer returned by malloc *)
        ptr_idx ← wlalloc W.T_i32;
        emit (W.BI_set_local (localimm ptr_idx));;
        (* set up a local for the offset (it's zero...) *)
        zero_idx ← wlalloc W.T_i32;
        emit (W.BI_const (compile_Z W.T_i32 0%Z));;
        (* do the tagged store to initialize the newly allocated region *)
        emit (W.BI_get_local (localimm ptr_idx));;
        restore_stack contents_idx [tau];;
        store_value_tagged zero_idx t;;
        (* put the tagged pointer on the top of the stack *)
        emit (W.BI_get_local (localimm ptr_idx))
        *)
        raise ETodo
    | IUnpack _ _ _ =>
        (* TODO: registerroot if GC package *)
        (* TODO: ignore (block_c (translate_arrow_type ty) (forT es compile_instr)) *)
        raise ETodo
    | IWrap _ => raise ETodo
    | IUnwrap _ => raise ETodo
    | IRefNew _ _ => raise ETodo
    | IRefFree _ => raise ETodo
    | IRefDup _ => raise ETodo
    | IRefDrop _ => raise ETodo
    | IRefLoad _ _ => raise ETodo
    | IRefStore _ _ => raise ETodo
    | IRefSwap _ _ => raise ETodo
    | IArrayNew _ _ =>
        (* TODO: unregisterroot the initial value if GC array;
                 duproot a bunch of times if MM array *)
        raise ETodo
    | IArrayFree _ =>
        (* TODO: unregisterroot a bunch of times, since this is an MM array *)
        emit (W.BI_call (funcimm me.(me_runtime).(mr_func_free)))
    | IArrayGet _ =>
        (* TODO: try_option EWrongTypeAnn (head in_ty ≫= array_elem) ≫= compile_array_get *)
        raise ETodo
    | IArraySet _ =>
        (* TODO: try_option EWrongTypeAnn (head in_ty ≫= array_elem) ≫= compile_array_set *)
        raise ETodo
    end.

  Definition compile_instrs : list instruction -> codegen unit := iterM compile_instr.

End Instrs.
