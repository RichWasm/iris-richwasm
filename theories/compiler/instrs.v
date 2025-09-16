From Stdlib Require Import List.
Import Stdlib.Lists.List.ListNotations.
Require Import Stdlib.Program.Basics.
Require Import Stdlib.Strings.String.
Require Import Stdlib.NArith.BinNat.
Require Import Stdlib.ZArith.BinInt.
Local Open Scope program_scope.

From ExtLib.Data Require Import List.
From ExtLib.Data.Monads Require Import EitherMonad StateMonad WriterMonad.
From ExtLib.Structures Require Import Functor Monads Reducible Traversable.

From stdpp Require Import list_numbers.

From Wasm Require datatypes operations.
Require Import Wasm.numerics.

From RichWasm Require Import prelude syntax layout.
From RichWasm.compiler Require Import codegen numerics util.
Require Import RichWasm.util.

Module W. Include datatypes <+ operations. End W.

Section Instrs.

  Variable me : module_env.
  Variable fe : function_env.

  Definition translate_type : type -> option (list W.value_type) :=
    translate_type fe.(fe_type_vars).

  (** Operations on PtrR values. *)

(* Remember the pointer encoding is
   x0 31-bit number, not actually a pointer
   01 word-aligned ptr to manually managed memory
   11 word-aligned ptr to gc memory
*)
  Definition ptr_case {A B C}
    (tf : W.function_type)
    (idx: W.localidx) 
    (num : codegen A)
    (mm : codegen B) 
    (gc : codegen C)
     : codegen (A * (B * C)) :=
    emit (W.BI_get_local $ localimm idx);;
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 1%Z)));;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_and));;
    emit (W.BI_testop W.T_i32 W.TO_eqz);;
    if_c tf num (
        emit (W.BI_get_local $ localimm idx);;
        emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 2%Z)));;
        emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_and));;
        emit (W.BI_testop W.T_i32 W.TO_eqz);;
        if_c tf mm gc).

  Definition ptr_case_global {A B C}
    (tf : W.function_type)
    (idx: W.globalidx) 
    (num : codegen A)
    (mm : codegen B) 
    (gc : codegen C)
     : codegen (A * (B * C)) :=
    emit (W.BI_get_global $ globalimm idx);;
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 1%Z)));;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_and));;
    emit (W.BI_testop W.T_i32 W.TO_eqz);;
    if_c tf num (
        emit (W.BI_get_global $ globalimm idx);;
        emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 2%Z)));;
        emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_and));;
        emit (W.BI_testop W.T_i32 W.TO_eqz);;
        if_c tf mm gc).

  Definition clear_gc_bit : codegen unit :=
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 3%Z)));;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_sub)).

  (** Root management. *)
  Fixpoint foreach_gc_ptr (idx: W.localidx) (ρ: representation) (op: codegen unit) : codegen unit :=
    let fix do_prod (idx: W.localidx) ρs : codegen unit :=
      let 'W.Mk_localidx idx_nat := idx in
      match ρs with
      | [] => mret ()
      | ρ :: ρs =>
          foreach_gc_ptr idx ρ op;;
          do_prod (W.Mk_localidx (S idx_nat)) ρs
      end
    in
    match ρ with
    | VarR v => raise ERepNotMono
    | SumR ρs => raise ETodo
    | ProdR ρs => do_prod idx ρs
    | PrimR PtrR =>
        ignore $ ptr_case (W.Tf [] []) idx (mret ()) (mret ())
          (emit $ W.BI_get_local (localimm idx);;
           clear_gc_bit;;
           op)
    | PrimR _ => mret ()
    end.

  Fixpoint foreach_gc_ptr_global (idx: W.globalidx) (ρ: representation) (op: codegen unit) : codegen unit :=
    let fix do_prod (idx: W.globalidx) ρs : codegen unit :=
      let 'W.Mk_globalidx idx_nat := idx in
      match ρs with
      | [] => mret ()
      | ρ :: ρs =>
          foreach_gc_ptr_global idx ρ op;;
          do_prod (W.Mk_globalidx (S idx_nat)) ρs
      end
    in
    match ρ with
    | VarR v => raise ERepNotMono
    | SumR ρs => raise ETodo
    | ProdR ρs => do_prod idx ρs
    | PrimR PtrR =>
        ignore $ ptr_case_global (W.Tf [] []) idx (mret ()) (mret ())
          (emit $ W.BI_get_global (globalimm idx);;
           clear_gc_bit;;
           op)
    | PrimR _ => mret ()
    end.

  Definition dup_roots_local (idx: W.localidx) (ρ: representation) : codegen unit :=
    foreach_gc_ptr idx ρ $ 
      emit (W.BI_call (funcimm me.(me_runtime).(mr_func_duproot))).

  Definition dup_roots_global (idx: W.globalidx) (ρ: representation) : codegen unit :=
    foreach_gc_ptr_global idx ρ $ 
      emit (W.BI_call (funcimm me.(me_runtime).(mr_func_duproot))).

  Definition unregister_roots_local (idx: W.localidx) (ρ: representation) : codegen unit :=
    foreach_gc_ptr idx ρ $ 
      emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot))).

  Definition unregister_roots_global (idx: W.globalidx) (ρ: representation) : codegen unit :=
    foreach_gc_ptr_global idx ρ $ 
      emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot))).

  Definition wlalloc (ty : W.value_type) : codegen W.localidx :=
    wl ← get;
    put (wl ++ [ty]);;
    ret (W.Mk_localidx (fe_wlocal_offset fe + length wl)).

  (** Saving and restoring the stack. *)
  Definition save_stack_w (ty : W.result_type) : codegen W.localidx :=
    xs ← mapM wlalloc ty;
    mapM (emit ∘ W.BI_set_local ∘ localimm) (reverse xs);;
    ret (ssrfun.Option.default (W.Mk_localidx 0) (head xs)).

  Definition save_stack_r (ρ : representation) : codegen W.localidx :=
    try_option EWrongTypeAnn (translate_rep ρ) ≫= save_stack_w.

  Definition save_stack (τs : list type) : codegen W.localidx :=
    tys ← try_option EWrongTypeAnn (mapM translate_type τs);
    save_stack_w (concat tys).

  Definition restore_stack_w (x : W.localidx) (ty : W.result_type) : codegen unit :=
    ignore (mapM (emit ∘ W.BI_get_local) (seq (localimm x) (length ty)) ).
  
  Definition restore_stack_r (x: W.localidx) (ρ: representation) : codegen unit :=
    tys ← try_option EWrongTypeAnn (translate_rep ρ);
    restore_stack_w x tys.

  Definition restore_stack (x : W.localidx) (τs : list type) : codegen unit :=
    tys ← try_option EWrongTypeAnn (mapM translate_type τs);
    restore_stack_w x (concat tys).

  (** Operations on locals. *)
  Fixpoint get_locals_w (base_idx : W.localidx) (count : nat) : codegen unit :=
    match count with
    | 0 => mret ()
    | S count =>
        emit (W.BI_get_local $ localimm base_idx);;
        get_locals_w base_idx count
    end.
        
  Fixpoint set_locals_w (base_idx : W.localidx) (count : nat) : codegen unit :=
    match count with
    | 0 => mret ()
    | S count =>
        emit (W.BI_set_local $ localimm base_idx);;
        set_locals_w base_idx count
    end.

  Definition get_local (x : W.localidx) (ρ : representation) : codegen unit :=
    tys ← try_option EWrongTypeAnn (translate_rep ρ);
    get_locals_w x (length tys).

  Definition set_local (x : W.localidx) (ρ: representation) : codegen unit :=
    tys ← try_option EWrongTypeAnn (translate_rep ρ);
    set_locals_w x (length tys).

  Definition local_index (x: nat) (ρs: list representation) : option W.localidx :=
    ts ← mapM translate_rep ρs;
    mret $ W.Mk_localidx $ sum_list_with length (take x ts).

  Definition lookup_local (x: nat) : option (W.localidx * representation) :=
    idx ← local_index x fe.(fe_local_reprs);
    ρ ← fe.(fe_local_reprs) !! x;
    mret (idx, ρ).

  Definition compile_get_local (idx : nat) : codegen unit :=
    '(idx', ρ) ← try_option EUnboundLocal (lookup_local idx);
    dup_roots_local idx' ρ;;
    get_local idx' ρ.

  Definition compile_set_local (x : nat) : codegen unit :=
    '(x', ρ) ← try_option EUnboundLocal (lookup_local x);
    unregister_roots_local x' ρ;;
    set_local x' ρ.

  (** Operations on globals. *)
  Fixpoint get_globals_w (base_idx : W.globalidx) (count : nat) : codegen unit :=
    match count with
    | 0 => mret ()
    | S count =>
        emit (W.BI_get_global $ globalimm base_idx);;
        get_globals_w base_idx count
    end.
        
  Fixpoint set_globals_w (base_idx : W.globalidx) (count : nat) : codegen unit :=
    match count with
    | 0 => mret ()
    | S count =>
        emit (W.BI_set_global $ globalimm base_idx);;
        set_globals_w base_idx count
    end.

  Definition get_global (x : W.globalidx) (ρ : representation) : codegen unit :=
    tys ← try_option EWrongTypeAnn (translate_rep ρ);
    get_globals_w x (length tys).

  Definition set_global (idx : W.globalidx) (ρ: representation) : codegen unit :=
    tys ← try_option EWrongTypeAnn (translate_rep ρ);
    set_globals_w idx (length tys).

  Definition global_index (x: nat) (ρs: list representation) : option W.globalidx :=
    ts ← mapM translate_rep ρs;
    mret $ W.Mk_globalidx $ sum_list_with length (take x ts).

  Definition lookup_global (x: nat) : option (W.globalidx * representation) :=
    ρs ← mapM (type_rep fe.(fe_type_vars)) me.(me_globals);
    idx ← global_index x ρs;
    ρ ← ρs !! x;
    mret (idx, ρ).

  Definition compile_get_global (idx : nat) : codegen unit :=
    '(idx', ρ) ← try_option EUnboundGlobal (lookup_global idx);
    dup_roots_global idx' ρ;;
    get_global idx' ρ.

  Definition compile_set_global (idx : nat) : codegen unit :=
    '(idx', ρ) ← try_option EUnboundGlobal (lookup_global idx);
    unregister_roots_global idx' ρ;;
    set_global idx' ρ.
  
  Definition compile_swap_global (idx: nat) : codegen unit :=
    '(idx', ρ) ← try_option EUnboundGlobal (lookup_global idx);
    get_global idx' ρ;;
    idx_old ← save_stack_r ρ;
    set_global idx' ρ;;
    restore_stack_r idx_old ρ.

  (** Operations on memory. *)
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

  (*
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

*)
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

  (*
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
*)

  (*
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
*)

  (** Dropping values from the stack. *)
  Definition compile_drop_prim_rep (ι : primitive_rep) : codegen unit :=
    match ι with
    | PtrR =>
        idx ← save_stack_w [W.T_i32];
        ignore $ ptr_case
                   (W.Tf [] [])
                   idx
                   (emit W.BI_drop)
                   (emit W.BI_drop)
                   (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot))))
    | _ => emit W.BI_drop
    end.

  Fixpoint compile_drop_rep (ρ : representation) : codegen unit :=
    match ρ with
    | VarR r => raise ERepNotMono
    | SumR ρs => raise ETodo
    | ProdR ρs => ignore $ mapM compile_drop_rep ρs
    | PrimR ι => compile_drop_prim_rep ι
    end.

  Definition compile_drop (τ : type) : codegen unit :=
    ρ ← try_option EUnboundTypeVar (type_rep fe.(fe_type_vars) τ);
    compile_drop_rep ρ.

  Definition compile_drops (τs : list type) : codegen unit :=
    ignore $ mapM compile_drop τs.
  
  (** Control flow: return *)
  Definition compile_return (τs : list type) : codegen unit :=
    let return_ty := fe.(fe_return_type) in
    let drop_ty := take (length τs - length return_ty) τs in
    r ← save_stack return_ty;
    compile_drops drop_ty;;
    restore_stack r return_ty;;
    emit W.BI_return.

  Definition compile_coderef (x : nat) : codegen unit :=
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat x))));;
    emit (W.BI_get_global (globalimm me.(me_runtime).(mr_global_table_offset)));;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add)).

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

  Definition compile_variant_case
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

  (** Operatiosn on mono representations *)
  (* This is the computational analogue of mono_rep *)
  Fixpoint flatten_rep (ρ : representation) : option (list primitive_rep) :=
    match ρ with
    | VarR _ => None
    | SumR ρs => seq.flatten <$> mapM flatten_rep ρs
    | ProdR ρs => seq.flatten <$> mapM flatten_rep ρs
    | PrimR ι => mret [ι]
    end.

  (** Conversions between types of the same size and ptr layout *)
  Definition to_words_i64 : codegen unit :=
    idx ← save_stack_r (PrimR I64R);
    (* low half *)
    restore_stack_r idx (PrimR I64R);;
    emit (W.BI_const (W.VAL_int64 (wasm_extend_u int32_minus_one)));;
    emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_and));;
    emit (W.BI_cvtop W.T_i64 W.CVO_convert W.T_i32 None);;
    (* high half *)
    restore_stack_r idx (PrimR I64R);;
    emit (W.BI_const (W.VAL_int64 (Wasm_int.int_of_Z i64m 32)));;
    emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_rotr));;
    emit (W.BI_cvtop W.T_i64 W.CVO_convert W.T_i32 None).

  Definition to_words_one (ι : primitive_rep) : codegen unit :=
    match ι with
    | PtrR => mret tt (* no op *)
    | I32R => mret tt (* no op *)
    | I64R => to_words_i64
    | F32R =>
        emit (W.BI_cvtop W.T_f32 W.CVO_reinterpret W.T_i32 None)
    | F64R =>
        emit (W.BI_cvtop W.T_f64 W.CVO_reinterpret W.T_i64 None);;
        to_words_i64
    end.

  Definition to_words (ιs : list primitive_rep) : codegen unit :=
    ignore $ mapM to_words_one ιs.

  Definition from_words_i64 : codegen unit :=
    idx ← save_stack_w [W.T_i32; W.T_i32];
    let idx_hi := localimm idx + 1 in 
    let idx_lo := localimm idx + 1 in 
    emit (W.BI_get_local idx_hi);;
    emit (W.BI_cvtop W.T_i32 W.CVO_reinterpret W.T_i64 None);;
    emit (W.BI_const (W.VAL_int64 (Wasm_int.int_of_Z i64m 32)));;
    emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_rotl));;
    emit (W.BI_get_local idx_lo);;
    emit (W.BI_cvtop W.T_i32 W.CVO_reinterpret W.T_i64 None);;
    emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_or)).

  Definition from_words_one (ι : primitive_rep) : codegen unit :=
    match ι with
    | PtrR => mret tt (* no op *)
    | I32R => mret tt (* no op *)
    | I64R => from_words_i64
    | F32R =>
        emit (W.BI_cvtop W.T_i32 W.CVO_reinterpret W.T_f32 None)
    | F64R =>
        from_words_i64;;
        emit (W.BI_cvtop W.T_i64 W.CVO_reinterpret W.T_f64 None)
    end.

  Definition from_words (ιs : list primitive_rep) : codegen unit :=
    ignore $ mapM from_words_one ιs.

  Definition conv_rep (ρ ρ' : representation) : codegen unit :=
    ιs ← try_option ERepNotMono $ flatten_rep ρ;
    ιs' ← try_option ERepNotMono $ flatten_rep ρ';
    to_words ιs;;
    from_words ιs'.

  Definition erased_in_wasm : codegen unit := mret tt.
  
  Fixpoint compile_instr (e : instruction) : codegen unit :=
    match e with
    | INop _ => emit W.BI_nop
    | IUnreachable _ => emit (W.BI_unreachable)
    | ICopy (ArrowT [τ] [_; _]) =>
        ρ ← try_option EUnboundTypeVar (type_rep fe.(fe_type_vars) τ);
        idx ← save_stack_r ρ;
        dup_roots_local idx ρ;;
        restore_stack_r idx ρ;;
        restore_stack_r idx ρ
    | ICopy _ => raise EWrongTypeAnn
    | IDrop (ArrowT τs _) => try_option EWrongTypeAnn (head τs) ≫= compile_drop
    | INum _ e' => emit (compile_num_instr e')
    | INumConst (ArrowT [] [NumT _ nt]) n =>
        emit (W.BI_const (compile_Z (translate_num_type nt) (Z.of_nat n)))
    | INumConst _ _ => raise EWrongTypeAnn
    | IBlock ψ _ es =>
        tf ← try_option EUnboundTypeVar (translate_arrow_type fe.(fe_type_vars) ψ);
        ignore (block_c tf (mapM compile_instr es))
    | ILoop ψ es =>
        tf ← try_option EUnboundTypeVar (translate_arrow_type fe.(fe_type_vars) ψ);
        ignore (loop_c tf (mapM compile_instr es))
    | IIte ψ _ es1 es2 =>
        tf ← try_option EUnboundTypeVar (translate_arrow_type fe.(fe_type_vars) ψ);
        ignore (if_c tf (mapM compile_instr es1) (mapM compile_instr es2))
    | IBr _ n => emit (W.BI_br n)
    | IBrIf _ n => emit (W.BI_br_if n)
    | IBrTable _ ns n => emit (W.BI_br_table ns n)
    | IReturn (ArrowT τs _) => compile_return τs
    | ILocalGet _ idx => compile_get_local idx
    | ILocalSet _ idx => compile_set_local idx
    | IGlobalGet _ idx => compile_get_global idx
    | IGlobalSet _ idx => compile_set_global idx
    | IGlobalSwap _ idx => compile_swap_global idx
    | ICodeRef _ x => compile_coderef x
    | IInst _ _ => erased_in_wasm
    | ICall _ fidx _ => emit (W.BI_call fidx)
    | ICallIndirect _ => emit (W.BI_call_indirect (tableimm me.(me_runtime).(mr_table)))
    | IInject _ k =>
        (* TODO: registerroot on the new address;
                 unregisterroot if payload is GC ref being put into GC variant *)
        raise ETodo
    | ICase _ _ _ => raise ETodo

    | IGroup _ => erased_in_wasm
    | IUngroup _ => erased_in_wasm
    | IFold _ => erased_in_wasm
    | IUnfold  _ => erased_in_wasm

    | IPack _ _ _ => erased_in_wasm
    | IUnpack ψ _ es =>
        tys ← try_option EUnboundTypeVar (translate_arrow_type fe.(fe_type_vars) ψ);
        (* bug? fe.(fe_type_vars) needs to be extended *)
        ignore $ block_c tys $ mapM compile_instr es

    | IWrap (ArrowT [τ0] [RepT κ ρ τ0']) =>
        ρ0 ← try_option EUnboundTypeVar $ type_rep fe.(fe_type_vars) τ0;
        conv_rep ρ0 ρ
    | IWrap _ => raise EWrongTypeAnn
    | IUnwrap (ArrowT [RepT κ ρ τ0'] [τ0]) =>
        ρ0 ← try_option EUnboundTypeVar $ type_rep fe.(fe_type_vars) τ0;
        conv_rep ρ ρ0
    | IUnwrap _ => raise EWrongTypeAnn

    | IRefNew (ArrowT [τ] [RefT κ MemMM τ']) => raise ETodo
    | IRefNew (ArrowT [τ] [RefT κ MemGC τ']) => raise ETodo
    | IRefNew _ => raise ETodo
    | IRefLoad _ _ => raise ETodo
    | IRefStore _ _ => raise ETodo
    | IRefSwap _ _ => raise ETodo

    | IArrayNew _ =>
        (* TODO: unregisterroot the initial value if GC array;
                 duproot a bunch of times if MM array *)
        raise ETodo
    | IArrayGet _ =>
        (* TODO: try_option EWrongTypeAnn (head in_ty ≫= array_elem) ≫= compile_array_get *)
        raise ETodo
    | IArraySet _ =>
        (* TODO: try_option EWrongTypeAnn (head in_ty ≫= array_elem) ≫= compile_array_set *)
        raise ETodo
    end.

  Definition compile_instrs : list instruction -> codegen unit := iterM compile_instr.

End Instrs.
