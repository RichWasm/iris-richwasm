Require Import RecordUpdate.RecordUpdate.

From ExtLib.Structures Require Import Monads.

Require Import stdpp.list.

From Wasm Require datatypes operations.
Require Import Wasm.numerics.

From RichWasm Require Import prelude layout syntax.
From RichWasm.compiler Require Import prelude codegen convert memory util.

Module W. Include Wasm.datatypes <+ Wasm.operations. End W.

Section Compiler.

  Variable me : module_env.

  Definition drop_primitive (fe : function_env) (ι : primitive_rep) : codegen unit :=
    match ι with
    | PtrR =>
        i ← save_stack1 fe W.T_i32;
        ignore (case_ptr (W.Tf [] []) i (emit W.BI_drop) (free me) (unregisterroot me))
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
    update_gc_refs ixs ιs (duproot me);;
    restore_stack ixs.

  Definition compile_drop (fe : function_env) (τ : type) : codegen unit :=
    ρ ← try_option EUnboundTypeVar (type_rep fe.(fe_type_vars) τ);
    ιs ← try_option EUnboundTypeVar (eval_rep ρ);
    mapM_ (drop_primitive fe) (rev ιs).

  Definition compile_num (e : num_instruction) : codegen unit :=
    match e with
    | IInt1 νi op => emit (W.BI_unop (translate_int_type νi) (W.Unop_i (translate_int_unop op)))
    | IInt2 νi op => emit (W.BI_binop (translate_int_type νi) (W.Binop_i (translate_int_binop op)))
    | IIntTest νi op => emit (W.BI_testop (translate_int_type νi) (translate_int_testop op))
    | IIntRel νi op => emit (W.BI_relop (translate_int_type νi) (W.Relop_i (translate_int_relop op)))
    | IFloat1 νf op => emit (W.BI_unop (translate_float_type νf) (W.Unop_f (translate_float_unop op)))
    | IFloat2 νf op =>
        emit (W.BI_binop (translate_float_type νf) (W.Binop_f (translate_float_binop op)))
    | IFloatRel νf op =>
        emit (W.BI_relop (translate_float_type νf) (W.Relop_f (translate_float_relop op)))
    | ICvt op => emit (translate_cvt_op op)
    end.

  Definition compile_num_const (ν : num_type) (n : nat) : codegen unit :=
    emit (W.BI_const (value_of_Z (translate_num_type ν) (Z.of_nat n))).

  Definition compile_block (fe : function_env) (ψ : instruction_type) (c : codegen unit) :
    codegen unit :=
    tf ← try_option EUnboundTypeVar (translate_instr_type fe.(fe_type_vars) ψ);
    block_c tf c.

  Definition compile_loop (fe : function_env) (ψ : instruction_type) (c : codegen unit) :
    codegen unit :=
    tf ← try_option EUnboundTypeVar (translate_instr_type fe.(fe_type_vars) ψ);
    loop_c tf c.

  Definition compile_ite (fe : function_env) (ψ : instruction_type) (c1 c2 : codegen unit) :
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

  Definition compile_inject (fe : function_env) (ρs : list representation) (τ : type) (i : nat) :
    codegen unit :=
    ιs_sum ← try_option EWrongTypeAnn (eval_rep (SumR ρs));
    ixs_sum ← mapM (wlalloc fe) (map translate_prim_rep (tail ιs_sum));
    ρ ← try_option EWrongTypeAnn (type_rep fe.(fe_type_vars) τ);
    ixs ← try_option EWrongTypeAnn (inject_sum_rep ρs ρ);
    ixs' ← mapM (try_option EWrongTypeAnn ∘ nth_error ixs_sum) ixs;
    mapM (emit ∘ W.BI_set_local ∘ localimm) (rev ixs');;
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat i))));;
    restore_stack ixs_sum.

  Definition compile_case
    (fe : function_env) (ρs : list representation) (τs : list type) (cases : list (codegen unit)) :
    codegen unit :=
    result ← try_option EWrongTypeAnn (translate_types fe.(fe_type_vars) τs);
    ιs ← try_option EWrongTypeAnn (eval_rep (SumR ρs));
    ixs ← save_stack fe (tail ιs);
    let cases' := map (fun c ixs => get_locals_w ixs;; c) cases in
    case_blocks ρs ixs result cases'.

  Definition compile_unpack
    (fe : function_env) '(InstrT τs1 τs2 : instruction_type) (c : function_env -> codegen unit) :
    codegen unit :=
    τ ← try_option EWrongTypeAnn (last τs1);
    let fe' := fe_extend_unpack fe τ in
    tys ← try_option EUnboundTypeVar (translate_instr_type fe.(fe_type_vars) (InstrT τs1 τs2));
    ignore $ block_c tys (c fe').

  Definition compile_wrap (fe : function_env) (ρ : representation) (τ : type) : codegen unit :=
    ρ0 ← try_option EWrongTypeAnn (type_rep fe.(fe_type_vars) τ);
    ιs0 ← try_option EWrongTypeAnn (eval_rep ρ0);
    ιs ← try_option EWrongTypeAnn (eval_rep ρ);
    wz ← to_words fe ιs0;
    from_words fe wz ιs.

  Definition compile_unwrap (fe : function_env) (ρ : representation) (τ : type) : codegen unit :=
    ρ0 ← try_option EWrongTypeAnn (type_rep fe.(fe_type_vars) τ);
    ιs0 ← try_option EWrongTypeAnn (eval_rep ρ0);
    ιs ← try_option EWrongTypeAnn (eval_rep ρ);
    wz ← to_words fe ιs;
    from_words fe wz ιs0.

  Definition compile_tag : codegen unit :=
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m 1)));;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_shl)).

  Definition compile_untag : codegen unit :=
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m 1)));;
    emit (W.BI_binop W.T_i32 (W.Binop_i (W.BOI_shr W.SX_U))).

  Definition compile_ref_new (fe : function_env) (cm : concrete_memory) (τ τ' : type) :
    codegen unit :=
    ρ ← try_option EWrongTypeAnn (type_rep fe.(fe_type_vars) τ);
    ιs ← try_option EWrongTypeAnn (eval_rep ρ);
    σ ← try_option EWrongTypeAnn (type_size fe.(fe_type_vars) τ');
    n ← try_option EWrongTypeAnn (eval_size σ);
    vs ← save_stack fe ιs;
    alloc me cm n;;
    a ← wlalloc fe W.T_i32;
    emit (W.BI_set_local (localimm a));;
    store_as me fe cm a 0%N ρ τ' vs.

  Definition compile_ref_store (fe : function_env) (τ τ' : type) (π : path) : codegen unit :=
    ρ ← try_option EWrongTypeAnn (type_rep fe.(fe_type_vars) τ);
    ιs ← try_option EWrongTypeAnn (eval_rep ρ);
    '(off, τ'') ← try_option EWrongTypeAnn (resolve_path fe τ' π);
    vs ← save_stack fe ιs;
    a ← wlalloc fe W.T_i32;
    emit (W.BI_set_local (localimm a));;
    ignore $ case_ptr (W.Tf [] []) a
      (emit W.BI_unreachable)
      (store_as me fe MemMM a off ρ τ'' vs)
      (store_as me fe MemGC a off ρ τ'' vs).

  Definition erased_in_wasm : codegen unit := ret tt.

  Fixpoint compile_instr (fe : function_env) (e : instruction) : codegen unit :=
    let compile_instrs fe := mapM_ (compile_instr fe) in
    match e with
    | INop _ => emit W.BI_nop
    | IUnreachable _ => emit W.BI_unreachable
    | ICopy (InstrT [τ] _) => compile_copy fe τ
    | ICopy _ => raise EWrongTypeAnn
    | IDrop (InstrT [τ] _) => compile_drop fe τ
    | IDrop _ => raise EWrongTypeAnn
    | INum _ e' => compile_num e'
    | INumConst (InstrT _ [NumT _ ν]) n => compile_num_const ν n
    | INumConst _ _ => raise EWrongTypeAnn
    | IBlock ψ _ es => compile_block fe ψ (compile_instrs fe es)
    | ILoop ψ es => compile_loop fe ψ (compile_instrs fe es)
    | IIte ψ _ es1 es2 => compile_ite fe ψ (compile_instrs fe es1) (compile_instrs fe es2)
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
    | IInject (InstrT [τ] [SumT (VALTYPE (SumR ρs) _ _) _]) i => compile_inject fe ρs τ i
    | IInject _ _ => raise EWrongTypeAnn
    | ICase (InstrT [SumT (VALTYPE (SumR ρs) _ _) _] τs) _ ess =>
        compile_case fe ρs τs (map (compile_instrs fe) ess)
    | ICase _ _ _ => raise EWrongTypeAnn
    | IGroup _ => erased_in_wasm
    | IUngroup _ => erased_in_wasm
    | IFold _ => erased_in_wasm
    | IUnfold  _ => erased_in_wasm
    | IPack _ => erased_in_wasm
    | IUnpack ψ _ es => compile_unpack fe ψ (flip compile_instrs es)
    | IWrap (InstrT _ [RepT _ ρ τ]) => compile_wrap fe ρ τ
    | IWrap _ => raise EWrongTypeAnn
    | IUnwrap (InstrT [RepT _ ρ τ] _) => compile_unwrap fe ρ τ
    | IUnwrap _ => raise EWrongTypeAnn
    | ITag _ => compile_tag
    | IUntag _ => compile_untag
    | IRefNew (InstrT [τ] [RefT _ (ConstM cm) τ']) => compile_ref_new fe cm τ τ'
    | IRefNew _ => raise EWrongTypeAnn
    | IRefLoad _ _ => raise ETodo
    | IRefStore (InstrT [RefT _ _ τ'; τ] _) π => compile_ref_store fe τ τ' π
    | IRefStore _ _ => raise EWrongTypeAnn
    | IRefSwap _ _ => raise ETodo
    end.

  Definition compile_instrs (fe : function_env) : list instruction -> codegen unit :=
    mapM_ (compile_instr fe).

End Compiler.
