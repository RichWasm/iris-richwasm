From Stdlib Require Import List.
Import Stdlib.Lists.List.ListNotations.
Require Import Stdlib.Program.Basics.
Require Import Stdlib.Strings.String.
Require Import Stdlib.NArith.BinNat.
Require Import Stdlib.ZArith.BinInt.
Local Open Scope program_scope.

Require Import RecordUpdate.RecordUpdate.

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
  Definition foreach_gc_ptr (idx : W.localidx) (ιs : list primitive_rep) (op : codegen unit) :
    codegen unit :=
    ignore $ forT (zip (seq (localimm idx) (length ιs)) ιs)
      (fun '(i, ι) =>
         match ι with
          | PtrR =>
              ignore $ ptr_case (W.Tf [] []) idx (mret ()) (mret ())
                (emit $ W.BI_get_local i;;
                 clear_gc_bit;;
                 op)
         | _ => mret tt
         end).

  Definition foreach_gc_ptr_global (idx : W.globalidx) (ιs : list primitive_rep) (op : codegen unit) :
    codegen unit :=
    ignore $ forT (zip (seq (globalimm idx) (length ιs)) ιs)
      (fun '(i, ι) =>
         match ι with
          | PtrR =>
              ignore $ ptr_case_global (W.Tf [] []) idx (mret ()) (mret ())
                (emit $ W.BI_get_global i;;
                 clear_gc_bit;;
                 op)
         | _ => mret tt
         end).

  Definition dup_root : codegen unit :=
    emit (W.BI_load (memimm me.(me_runtime).(mr_mem_gc)) W.T_i32 None 0%N 0%N);;
    emit (W.BI_call (funcimm me.(me_runtime).(mr_func_registerroot))).

  Definition dup_roots_local (idx : W.localidx) (ιs : list primitive_rep) : codegen unit :=
    foreach_gc_ptr idx ιs dup_root.

  Definition dup_roots_global (idx : W.globalidx) (ιs : list primitive_rep) : codegen unit :=
    foreach_gc_ptr_global idx ιs dup_root.

  Definition unregister_roots_local (idx: W.localidx) (ιs : list primitive_rep) : codegen unit :=
    foreach_gc_ptr idx ιs $ 
      emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot))).

  Definition unregister_roots_global (idx : W.globalidx) (ιs : list primitive_rep) : codegen unit :=
    foreach_gc_ptr_global idx ιs $ 
      emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot))).

  Definition wlalloc (fe : function_env) (ty : W.value_type) : codegen W.localidx :=
    wl ← get;
    put (wl ++ [ty]);;
    ret (W.Mk_localidx (fe_wlocal_offset fe + length wl)).

  (** Saving and restoring the stack. *)
  Definition save_stack1 (fe : function_env) (ty : W.value_type) : codegen W.localidx :=
    idx ← wlalloc fe ty;
    emit (W.BI_set_local (localimm idx));;
    mret idx.

  Definition save_stack_w (fe : function_env) (tys : W.result_type) : codegen (list W.localidx) :=
    idxs ← mapM (wlalloc fe) tys;
    mapM (emit ∘ W.BI_set_local ∘ localimm) (rev idxs);;
    mret idxs.

  Definition save_stack_r (fe : function_env) (ιs : list primitive_rep) : codegen (list W.localidx) :=
    save_stack_w fe (map translate_prim_rep ιs).

  Definition save_stack (fe : function_env) (τs : list type) : codegen (list W.localidx) :=
    tys ← try_option EWrongTypeAnn (mapM (translate_type fe.(fe_type_vars)) τs);
    save_stack_w fe (concat tys).

  Definition restore_stack_w (idxs : list W.localidx) (ty : W.result_type) : codegen unit :=
    ignore (mapM (emit ∘ W.BI_get_local ∘ localimm) idxs).

  Definition restore_stack_r (idxs : list W.localidx) (ιs : list primitive_rep) : codegen unit :=
    restore_stack_w idxs (map translate_prim_rep ιs).

  Definition restore_stack (fe : function_env) (idxs : list W.localidx) (τs : list type) :
    codegen unit :=
    tys ← try_option EWrongTypeAnn (mapM (translate_type fe.(fe_type_vars)) τs);
    restore_stack_w idxs (concat tys).

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

  Definition get_local (x : W.localidx) (ιs : list primitive_rep) : codegen unit :=
    get_locals_w x (length ιs).

  Definition set_local (x : W.localidx) (ιs : list primitive_rep) : codegen unit :=
    set_locals_w x (length ιs).

  Definition local_index (x : nat) (ιs : list (list primitive_rep)) : option W.localidx :=
    mret $ W.Mk_localidx $ sum_list_with length (take x ιs).

  Definition lookup_local (fe : function_env) (x : nat) : option (W.localidx * list primitive_rep) :=
    idx ← local_index x fe.(fe_local_reps);
    ρ ← fe.(fe_local_reps) !! x;
    mret (idx, ρ).

  Definition compile_get_local (fe : function_env) (idx : nat) : codegen unit :=
    '(idx', ιs) ← try_option EUnboundLocal (lookup_local fe idx);
    (* TODO: local.get should never do anything with the retrieved value. *)
    dup_roots_local idx' ιs;;
    get_local idx' ιs.

  Definition compile_set_local (fe : function_env) (x : nat) : codegen unit :=
    '(x', ιs) ← try_option EUnboundLocal (lookup_local fe x);
    (* TODO: local.set should never do anything with the old value. *)
    unregister_roots_local x' ιs;;
    set_local x' ιs.

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

  Definition get_global (x : W.globalidx) (ιs : list primitive_rep) : codegen unit :=
    get_globals_w x (length ιs).

  Definition set_global (idx : W.globalidx) (ιs : list primitive_rep) : codegen unit :=
    set_globals_w idx (length ιs).

  Definition global_index (x : nat) (ιss: list (list primitive_rep)) : W.globalidx :=
    W.Mk_globalidx $ sum_list_with length (take x ιss).

  Definition lookup_global (x : nat) : option (W.globalidx * list primitive_rep) :=
    ρs ← mapM (type_rep []) me.(me_globals);
    ιss ← mapM eval_rep ρs;
    let idx := global_index x ιss in
    ιs ← ιss !! x;
    mret (idx, ιs).

  Definition compile_get_global (idx : nat) : codegen unit :=
    '(idx', ιs) ← try_option EUnboundGlobal (lookup_global idx);
    (* TODO: global.get should never do anything with the retrieved value. *)
    dup_roots_global idx' ιs;;
    get_global idx' ιs.

  Definition compile_set_global (idx : nat) : codegen unit :=
    '(idx', ιs) ← try_option EUnboundGlobal (lookup_global idx);
    (* TODO: global.set should never do anything with the previous value. *)
    unregister_roots_global idx' ιs;;
    set_global idx' ιs.

  Definition compile_swap_global (fe : function_env) (idx : nat) : codegen unit :=
    '(idx', ιs) ← try_option EUnboundGlobal (lookup_global idx);
    get_global idx' ιs;;
    idx_old ← save_stack_r fe ιs;
    set_global idx' ιs;;
    restore_stack_r idx_old ιs.

  (** Operations on memory. *)
  Definition load_values_w (mem : W.memidx) (ptr : W.localidx) (off : W.static_offset) :
    W.result_type -> codegen unit :=
    ignore ∘ foldM
      (fun ty off =>
        emit (W.BI_get_local (localimm ptr));;
        emit (W.BI_load (memimm mem) ty None 0%N off);;
        ret (off + N.of_nat (W.length_t ty))%N)
      (ret off).

  Definition load_value
    (fe : function_env) (mem : W.memidx) (ptr : W.localidx) (off : W.static_offset) (τ : type) :
    codegen unit :=
    tys ← try_option EWrongTypeAnn (translate_type fe.(fe_type_vars) τ);
    load_values_w mem ptr off tys.

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
    (fe : function_env) (mem : W.memidx) (ptr : W.localidx) (off : W.static_offset)
    (val : W.localidx) (τ : type) :
    codegen unit :=
    ty ← try_option EWrongTypeAnn (translate_type fe.(fe_type_vars) τ);
    let vals := zip (map W.Mk_localidx (seq (localimm val) (length ty))) ty in
    store_values_w mem ptr off vals.

  (** Dropping values from the stack. *)
  Definition compile_drop_prim_rep (fe : function_env) (ι : primitive_rep) : codegen unit :=
    match ι with
    | PtrR =>
        (* TODO: Drop also needs to free MM refs. *)
        idx ← save_stack1 fe W.T_i32;
        ignore $ ptr_case
                   (W.Tf [] [])
                   idx
                   (emit W.BI_drop)
                   (emit W.BI_drop)
                   (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot))))
    | _ => emit W.BI_drop
    end.

  Definition compile_drop (fe : function_env) (τ : type) : codegen unit :=
    ρ ← try_option EUnboundTypeVar (type_rep fe.(fe_type_vars) τ);
    ιs ← try_option EUnboundTypeVar (eval_rep ρ);
    ignore $ mapM (compile_drop_prim_rep fe) ιs.

  Definition compile_drops (fe : function_env) (τs : list type) : codegen unit :=
    ignore $ mapM (compile_drop fe) τs.

  Definition compile_coderef (x : nat) : codegen unit :=
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat x))));;
    emit (W.BI_get_global (globalimm me.(me_runtime).(mr_global_table_offset)));;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add)).

  (* Produces code that consumes a size on the top of the stack and returns a ref *)
  Definition compile_malloc (μ : memory) : codegen unit :=
    (* TODO *)
    ret tt.

  (** Conversions between types of the same size and ptr layout *)
  Definition to_words_i64 (fe : function_env) : codegen unit :=
    idx ← save_stack_r fe [I64R];
    (* low half *)
    restore_stack_r idx [I64R];;
    emit (W.BI_const (W.VAL_int64 (wasm_extend_u int32_minus_one)));;
    emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_and));;
    emit (W.BI_cvtop W.T_i64 W.CVO_convert W.T_i32 None);;
    (* high half *)
    restore_stack_r idx [I64R];;
    emit (W.BI_const (W.VAL_int64 (Wasm_int.int_of_Z i64m 32)));;
    emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_rotr));;
    emit (W.BI_cvtop W.T_i64 W.CVO_convert W.T_i32 None).

  Definition to_words_one (fe : function_env) (ι : primitive_rep) : codegen unit :=
    match ι with
    | PtrR => mret tt (* no op *)
    | I32R => mret tt (* no op *)
    | I64R => to_words_i64 fe
    | F32R =>
        emit (W.BI_cvtop W.T_f32 W.CVO_reinterpret W.T_i32 None)
    | F64R =>
        emit (W.BI_cvtop W.T_f64 W.CVO_reinterpret W.T_i64 None);;
        to_words_i64 fe
    end.

  Definition to_words (fe : function_env) (ιs : list primitive_rep) : codegen unit :=
    ignore $ mapM (to_words_one fe) ιs.

  Definition from_words_i64 (fe : function_env) : codegen unit :=
    idx_lo ← save_stack1 fe W.T_i32;
    idx_hi ← save_stack1 fe W.T_i32;
    emit (W.BI_get_local (localimm idx_hi));;
    emit (W.BI_cvtop W.T_i32 W.CVO_reinterpret W.T_i64 None);;
    emit (W.BI_const (W.VAL_int64 (Wasm_int.int_of_Z i64m 32)));;
    emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_rotl));;
    emit (W.BI_get_local (localimm idx_lo));;
    emit (W.BI_cvtop W.T_i32 W.CVO_reinterpret W.T_i64 None);;
    emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_or)).

  Definition from_words_one (fe : function_env) (ι : primitive_rep) : codegen unit :=
    match ι with
    | PtrR => mret tt (* no op *)
    | I32R => mret tt (* no op *)
    | I64R => from_words_i64 fe
    | F32R =>
        emit (W.BI_cvtop W.T_i32 W.CVO_reinterpret W.T_f32 None)
    | F64R =>
        from_words_i64 fe;;
        emit (W.BI_cvtop W.T_i64 W.CVO_reinterpret W.T_f64 None)
    end.

  Definition from_words (fe : function_env) (ιs : list primitive_rep) : codegen unit :=
    ignore $ mapM (from_words_one fe) ιs.

  Definition conv_rep (fe : function_env) (ρ ρ' : representation) : codegen unit :=
    (* TODO: Pointer reps must be preserved. *)
    ιs ← try_option ERepNotMono $ eval_rep ρ;
    ιs' ← try_option ERepNotMono $ eval_rep ρ';
    to_words fe ιs;;
    from_words fe ιs'.

  Definition erased_in_wasm : codegen unit := mret tt.

  Fixpoint compile_instr (fe : function_env) (e : instruction) : codegen unit :=
    match e with
    | INop _ => emit W.BI_nop
    | IUnreachable _ => emit W.BI_unreachable
    | ICopy (InstrT [τ] _) =>
        ρ ← try_option EUnboundTypeVar (type_rep fe.(fe_type_vars) τ);
        ιs ← try_option EUnboundTypeVar (eval_rep ρ);
        idxs ← save_stack_r fe ιs;
        raise ETodo
    | ICopy _ => raise EWrongTypeAnn
    | IDrop (InstrT τs _) => try_option EWrongTypeAnn (head τs) ≫= compile_drop fe
    | INum _ e' => emit (compile_num_instr e')
    | INumConst (InstrT _ [NumT _ ν]) n =>
        emit (W.BI_const (compile_Z (translate_num_type ν) (Z.of_nat n)))
    | INumConst _ _ => raise EWrongTypeAnn
    | IBlock ψ _ es =>
        tf ← try_option EUnboundTypeVar (translate_instr_type fe.(fe_type_vars) ψ);
        ignore (block_c tf (mapM (compile_instr fe) es))
    | ILoop ψ es =>
        tf ← try_option EUnboundTypeVar (translate_instr_type fe.(fe_type_vars) ψ);
        ignore (loop_c tf (mapM (compile_instr fe) es))
    | IIte ψ _ es1 es2 =>
        tf ← try_option EUnboundTypeVar (translate_instr_type fe.(fe_type_vars) ψ);
        ignore (if_c tf (mapM (compile_instr fe) es1) (mapM (compile_instr fe) es2))
    | IBr _ i => emit (W.BI_br i)
    | IReturn _ => emit W.BI_return
    | ILocalGet _ idx => compile_get_local fe idx
    | ILocalSet _ idx => compile_set_local fe idx
    | IGlobalGet _ idx => compile_get_global idx
    | IGlobalSet _ idx => compile_set_global idx
    | IGlobalSwap _ idx => compile_swap_global fe idx
    | ICodeRef _ x => compile_coderef x
    | IInst _ _ => erased_in_wasm
    | ICall _ fidx _ => emit (W.BI_call fidx) (* TODO: Add offset for imported runtime functions. *)
    | ICallIndirect _ => emit (W.BI_call_indirect (tableimm me.(me_runtime).(mr_table)))
    | IInject _ k => raise ETodo
    | ICase _ _ _ => raise ETodo
    | IGroup _ => erased_in_wasm
    | IUngroup _ => erased_in_wasm
    | IFold _ => erased_in_wasm
    | IUnfold  _ => erased_in_wasm
    | IPack _ => erased_in_wasm
    | IUnpack (InstrT τs1 τs2) _ es =>
        τ ← try_option EWrongTypeAnn (last τs1);
        let fe' :=
          match τ with
          | ExistsTypeT _ κ0 _ => fe <| fe_type_vars ::= cons κ0 |>
          | _ => fe
          end
        in
        tys ← try_option EUnboundTypeVar (translate_instr_type fe.(fe_type_vars) (InstrT τs1 τs2));
        ignore $ block_c tys $ mapM (compile_instr fe') es
    | IWrap (InstrT [τ0] [RepT κ ρ τ0']) =>
        ρ0 ← try_option EUnboundTypeVar $ type_rep fe.(fe_type_vars) τ0;
        conv_rep fe ρ0 ρ
    | IWrap _ => raise EWrongTypeAnn
    | IUnwrap (InstrT [RepT κ ρ τ0'] [τ0]) =>
        ρ0 ← try_option EUnboundTypeVar $ type_rep fe.(fe_type_vars) τ0;
        conv_rep fe ρ ρ0
    | IUnwrap _ => raise EWrongTypeAnn
    | ITag _ => raise ETodo
    | IUntag _ => raise ETodo
    | IRefNew (InstrT [τ] [RefT κ (ConstM MemMM) τ']) => raise ETodo
    | IRefNew (InstrT [τ] [RefT κ (ConstM MemGC) τ']) => raise ETodo
    | IRefNew _ => raise ETodo
    | IRefLoad _ _ => raise ETodo
    | IRefStore _ _ => raise ETodo
    | IRefSwap _ _ => raise ETodo
    end.

  Definition compile_instrs (fe : function_env) : list instruction -> codegen unit :=
    iterM (compile_instr fe).

End Instrs.
