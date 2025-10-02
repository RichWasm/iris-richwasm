Require Import RecordUpdate.RecordUpdate.

From ExtLib.Structures Require Import Monads Reducible.

From stdpp Require Import numbers list.

From Wasm Require datatypes operations.
Require Import Wasm.numerics.

From RichWasm Require Import prelude syntax layout.
From RichWasm.compiler Require Import codegen numerics util.

Module W. Include datatypes <+ operations. End W.

Section Instrs.

  Variable me : module_env.

  Definition offset_mm : N := 3.
  Definition offset_gc : N := 1.

  Definition get_locals_w : list W.localidx -> codegen unit :=
    mapM_ (emit ∘ W.BI_get_local ∘ localimm).

  Definition set_locals_w : list W.localidx -> codegen unit :=
    mapM_ (emit ∘ W.BI_set_local ∘ localimm) ∘ @rev _.

  Definition get_globals_w : list W.globalidx -> codegen unit :=
    mapM_ (emit ∘ W.BI_get_global ∘ globalimm).

  Definition set_globals_w : list W.globalidx -> codegen unit :=
    mapM_ (emit ∘ W.BI_set_global ∘ globalimm) ∘ @rev _.

  Definition wlalloc (fe : function_env) (ty : W.value_type) : codegen W.localidx :=
    wl ← get;
    put (wl ++ [ty]);;
    ret (W.Mk_localidx (fe_wlocal_offset fe + length wl)).

  Definition save_stack1 (fe : function_env) (ty : W.value_type) : codegen W.localidx :=
    i ← wlalloc fe ty;
    emit (W.BI_set_local (localimm i));;
    ret i.

  Definition save_stack_w (fe : function_env) (tys : W.result_type) : codegen (list W.localidx) :=
    ixs ← mapM (wlalloc fe) tys;
    set_locals_w ixs;;
    ret ixs.

  Definition save_stack (fe : function_env) (ιs : list primitive_rep) : codegen (list W.localidx) :=
    save_stack_w fe (map translate_prim_rep ιs).

  Definition restore_stack : list W.localidx -> codegen unit := get_locals_w.

  Definition case_ptr {A B C : Type}
    (tf : W.function_type) (i : W.localidx) (num : codegen A) (mm : codegen B) (gc : codegen C) :
    codegen (A * (B * C)) :=
    emit (W.BI_get_local (localimm i));;
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m 1)));;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_and));;
    emit (W.BI_testop W.T_i32 W.TO_eqz);;
    if_c tf
      num
      (emit (W.BI_get_local (localimm i));;
       emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 2)));;
       emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_and));;
       emit (W.BI_testop W.T_i32 W.TO_eqz);;
       if_c tf mm gc).

  Definition update_gc_ref (i : W.localidx) (ι : primitive_rep) (c : codegen unit) : codegen unit :=
    match ι with
    | PtrR =>
        ignore $ case_ptr (W.Tf [] []) i
          (ret tt)
          (ret tt)
          (emit (W.BI_get_local (localimm i));;
           c;;
           emit (W.BI_set_local (localimm i)))
    | _ => ret tt
    end.

  Definition update_gc_refs (ixs : list W.localidx) (ιs : list primitive_rep) (c : codegen unit) :
    codegen unit :=
    mapM_ (fun '(i, ι) => update_gc_ref i ι c) (zip ixs ιs).

  Definition free : codegen unit :=
    emit (W.BI_call (funcimm me.(me_runtime).(mr_func_free))).

  Definition duproot : codegen unit :=
    emit (W.BI_load (memimm me.(me_runtime).(mr_mem_gc)) W.T_i32 None 0%N offset_gc);;
    emit (W.BI_call (funcimm me.(me_runtime).(mr_func_registerroot))).

  Definition unregisterroot : codegen unit :=
    emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot))).

  Definition drop_primitive (fe : function_env) (ι : primitive_rep) : codegen unit :=
    match ι with
    | PtrR =>
        i ← save_stack1 fe W.T_i32;
        ignore (case_ptr (W.Tf [] []) i (emit W.BI_drop) free unregisterroot)
    | _ => emit W.BI_drop
    end.

  Definition local_indices (fe : function_env) (i : nat) : option (list W.localidx) :=
    let i' := sum_list_with length (take i fe.(fe_local_reps)) in
    ιs ← fe.(fe_local_reps) !! i;
    Some (map W.Mk_localidx (seq i' (length ιs))).

  Definition global_indices (i : nat) : option (list W.globalidx * list primitive_rep) :=
    ρs ← mapM (type_rep []) me.(me_globals);
    ιss ← mapM eval_rep ρs;
    let i' := sum_list_with length (take i ιss) in
    ιs ← ιss !! i;
    Some (map W.Mk_globalidx (seq i' (length ιs)), ιs).

  Definition fe_extend_unpack (fe : function_env) (τ : type) : function_env :=
    match τ with
    | ExistsTypeT _ κ _ => fe <| fe_type_vars ::= cons κ |>
    | _ => fe
    end.

  Definition compile_copy (fe : function_env) (τ : type) : codegen unit :=
    ρ ← try_option EUnboundTypeVar (type_rep fe.(fe_type_vars) τ);
    ιs ← try_option EUnboundTypeVar (eval_rep ρ);
    ixs ← save_stack fe ιs;
    restore_stack ixs;;
    update_gc_refs ixs ιs duproot;;
    restore_stack ixs.

  Definition compile_drop (fe : function_env) (τ : type) : codegen unit :=
    ρ ← try_option EUnboundTypeVar (type_rep fe.(fe_type_vars) τ);
    ιs ← try_option EUnboundTypeVar (eval_rep ρ);
    mapM_ (drop_primitive fe) (rev ιs).

  Definition compile_num_const (ν : num_type) (n : nat) : codegen unit :=
    emit (W.BI_const (compile_Z (translate_num_type ν) (Z.of_nat n))).

  Definition compile_block (fe : function_env) (ψ : instruction_type) (c : codegen (list unit)) :
    codegen unit :=
    tf ← try_option EUnboundTypeVar (translate_instr_type fe.(fe_type_vars) ψ);
    block_c tf (ignore c).

  Definition compile_loop (fe : function_env) (ψ : instruction_type) (c : codegen (list unit)) :
    codegen unit :=
    tf ← try_option EUnboundTypeVar (translate_instr_type fe.(fe_type_vars) ψ);
    loop_c tf (ignore c).

  Definition compile_ite (fe : function_env) (ψ : instruction_type) (c1 c2 : codegen (list unit)) :
    codegen unit :=
    tf ← try_option EUnboundTypeVar (translate_instr_type fe.(fe_type_vars) ψ);
    ignore (if_c tf c1 c2).

  Definition compile_local_get (fe : function_env) (i : nat) : codegen unit :=
    try_option EUnboundLocal (local_indices fe i) ≫= get_locals_w.

  Definition compile_local_set (fe : function_env) (i : nat) : codegen unit :=
    try_option EUnboundLocal (local_indices fe i) ≫= set_locals_w.

  Definition compile_global_get (i : nat) : codegen unit :=
    try_option EUnboundGlobal (global_indices i) ≫= get_globals_w ∘ fst.

  Definition compile_global_set (i : nat) : codegen unit :=
    try_option EUnboundGlobal (global_indices i) ≫= set_globals_w ∘ fst.

  Definition compile_global_swap (fe : function_env) (i : nat) : codegen unit :=
    '(ixs, ιs) ← try_option EUnboundGlobal (global_indices i);
    get_globals_w ixs;;
    old ← save_stack fe ιs;
    set_globals_w ixs;;
    restore_stack old.

  Definition compile_coderef (i : nat) : codegen unit :=
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat i))));;
    emit (W.BI_get_global (globalimm me.(me_runtime).(mr_global_table_offset)));;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add)).

  Definition compile_call (i : nat) : codegen unit :=
    let i' := i + funcimm me.(me_runtime).(mr_func_user) in
    emit (W.BI_call i').

  Definition compile_unpack
    (fe : function_env) '(InstrT τs1 τs2 : instruction_type) (c : function_env -> codegen unit) :
    codegen unit :=
    τ ← try_option EWrongTypeAnn (last τs1);
    let fe' := fe_extend_unpack fe τ in
    tys ← try_option EUnboundTypeVar (translate_instr_type fe.(fe_type_vars) (InstrT τs1 τs2));
    ignore $ block_c tys (c fe').

  Definition erased_in_wasm : codegen unit := ret tt.

  Fixpoint compile_instr (fe : function_env) (e : instruction) : codegen unit :=
    match e with
    | INop _ => emit W.BI_nop
    | IUnreachable _ => emit W.BI_unreachable
    | ICopy (InstrT [τ] _) => compile_copy fe τ
    | ICopy _ => raise EWrongTypeAnn
    | IDrop (InstrT [τ] _) => compile_drop fe τ
    | IDrop _ => raise EWrongTypeAnn
    | INum _ e' => emit (compile_num_instr e')
    | INumConst (InstrT _ [NumT _ ν]) n => compile_num_const ν n
    | INumConst _ _ => raise EWrongTypeAnn
    | IBlock ψ _ es => compile_block fe ψ (mapM (compile_instr fe) es)
    | ILoop ψ es => compile_loop fe ψ (mapM (compile_instr fe) es)
    | IIte ψ _ es1 es2 => compile_ite fe ψ (mapM (compile_instr fe) es1) (mapM (compile_instr fe) es2)
    | IBr _ i => emit (W.BI_br i)
    | IReturn _ => emit W.BI_return
    | ILocalGet _ i => compile_local_get fe i
    | ILocalSet _ i => compile_local_set fe i
    | IGlobalGet _ i => compile_global_get i
    | IGlobalSet _ i => compile_global_set i
    | IGlobalSwap _ i => compile_global_swap fe i
    | ICodeRef _ i => compile_coderef i
    | IInst _ _ => erased_in_wasm
    | ICall _ i _ => compile_call i
    | ICallIndirect _ => emit (W.BI_call_indirect (tableimm me.(me_runtime).(mr_table)))
    | IInject _ _ => raise ETodo
    | ICase _ _ _ => raise ETodo
    | IGroup _ => erased_in_wasm
    | IUngroup _ => erased_in_wasm
    | IFold _ => erased_in_wasm
    | IUnfold  _ => erased_in_wasm
    | IPack _ => erased_in_wasm
    | IUnpack ψ _ es => compile_unpack fe ψ (fun fe' => mapM_ (compile_instr fe') es)
    | IWrap _ => raise ETodo
    | IUnwrap _ => raise ETodo
    | ITag _ => raise ETodo
    | IUntag _ => raise ETodo
    | IRefNew _ => raise ETodo
    | IRefLoad _ _ => raise ETodo
    | IRefStore _ _ => raise ETodo
    | IRefSwap _ _ => raise ETodo
    end.

  Definition compile_instrs (fe : function_env) : list instruction -> codegen unit :=
    iterM (compile_instr fe).

End Instrs.
