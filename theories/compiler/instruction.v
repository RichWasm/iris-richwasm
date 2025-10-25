Require Import RecordUpdate.RecordUpdate.

From ExtLib.Structures Require Import Monads.

Require Import stdpp.list.

From Wasm Require datatypes operations.
Require Import Wasm.numerics.

From RichWasm Require Import prelude layout syntax util.
From RichWasm.compiler Require Import prelude codegen memory util.

Module W. Include Wasm.datatypes <+ Wasm.operations. End W.

Section Compiler.

  Variable mr : module_runtime.

  Definition drop_primitive (fe : function_env) (ι : primitive_rep) : codegen unit :=
    match ι with
    | PtrR =>
        i ← save_stack1 fe W.T_i32;
        ignore $ case_ptr i (W.Tf [] [])
          (ret tt)
          (fun μ => emit (W.BI_get_local (localimm i));; drop_ptr mr μ)
    | _ => emit W.BI_drop
    end.

  Definition local_indices (fe : function_env) (i : nat) : option (list W.localidx) :=
    let i' := sum_list_with length (take i fe.(fe_locals)) in
    ιs ← fe.(fe_locals) !! i;
    Some (map W.Mk_localidx (seq i' (length ιs))).

  Definition fe_extend_unpack (fe : function_env) (τ : type) : function_env :=
    match τ with
    | ExistsTypeT _ κ _ => fe <| fe_type_vars ::= cons κ |>
    | _ => fe
    end.

  Definition compile_copy (fe : function_env) (τ : type) : codegen unit :=
    ρ ← try_option EFail (type_rep fe.(fe_type_vars) τ);
    ιs ← try_option EFail (eval_rep ρ);
    ixs ← save_stack fe ιs;
    restore_stack ixs;;
    map_gc_ptrs ιs ixs (duproot mr);;
    restore_stack ixs.

  Definition compile_drop (fe : function_env) (τ : type) : codegen unit :=
    ρ ← try_option EFail (type_rep fe.(fe_type_vars) τ);
    ιs ← try_option EFail (eval_rep ρ);
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
    tf ← try_option EFail (translate_instr_type fe.(fe_type_vars) ψ);
    block_c tf c.

  Definition compile_loop (fe : function_env) (ψ : instruction_type) (c : codegen unit) :
    codegen unit :=
    tf ← try_option EFail (translate_instr_type fe.(fe_type_vars) ψ);
    loop_c tf c.

  Definition compile_ite
    (fe : function_env) '(InstrT τs1 τs2 : instruction_type) (c1 c2 : codegen unit) : codegen unit :=
    ts1 ← try_option EFail (translate_types fe.(fe_type_vars) (removelast τs1));
    ts2 ← try_option EFail (translate_types fe.(fe_type_vars) τs2);
    ignore (if_c (W.Tf ts1 ts2) c1 c2).

  Definition compile_local_get (fe : function_env) (i : nat) : codegen unit :=
    try_option EFail (local_indices fe i) ≫= get_locals_w.

  Definition compile_local_set (fe : function_env) (i : nat) : codegen unit :=
    try_option EFail (local_indices fe i) ≫= set_locals_w.

  Definition compile_coderef (i : nat) : codegen unit :=
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat i))));;
    emit (W.BI_get_global (globalimm mr.(mr_global_table_off)));;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add)).

  Definition compile_call (i : nat) : codegen unit :=
    let i' := i + funcimm mr.(mr_func_user) in
    emit (W.BI_call i').

  Definition compile_inject_sum (fe : function_env) (ρs : list representation) (τ : type) (i : nat) :
    codegen unit :=
    ιs_sum ← try_option EFail (eval_rep (SumR ρs));
    ixs_sum ← mapM (wlalloc fe) (map translate_prim_rep (tail ιs_sum));
    ρ ← try_option EFail (type_rep fe.(fe_type_vars) τ);
    ixs ← try_option EFail (inject_sum_rep ρs ρ);
    ixs' ← mapM (try_option EFail ∘ nth_error ixs_sum) ixs;
    mapM (emit ∘ W.BI_set_local ∘ localimm) (rev ixs');;
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat i))));;
    restore_stack ixs_sum.

  Definition compile_inject_variant
    (fe : function_env) (μ : concrete_memory) (i : nat) (τ : type) (σ : size) : codegen unit :=
    ρ ← try_option EFail (type_rep fe.(fe_type_vars) τ);
    ιs ← try_option EFail (eval_rep ρ);
    n ← try_option EFail (eval_size σ);
    vs ← save_stack fe ιs;
    alloc mr μ n;;
    a ← wlalloc fe W.T_i32;
    emit (W.BI_set_local (localimm a));;
    set_pointer_flags mr a 0 (I32R :: ιs);;
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat i))));;
    t ← wlalloc fe W.T_i32;
    emit (W.BI_set_local (localimm t));;
    store_primitive mr μ a 0%N t I32R;;
    store_primitives mr μ a 4%N vs ιs;;
    emit (W.BI_get_local (localimm a));;
    match μ with
    | MemMM => ret tt
    | MemGC => registerroot mr
    end.

  (* TODO: br inside a case should bypass all but the outermost block. *)
  Definition compile_case_sum
    (fe : function_env) (ρs : list representation) (τ' : type) (cases : list (codegen unit)) :
    codegen unit :=
    res ← try_option EFail (translate_type fe.(fe_type_vars) τ');
    ιs ← try_option EFail (eval_rep (SumR ρs));
    ixs ← save_stack fe (tail ιs);
    let do_case c i :=
      ρ ← try_option EFail (ρs !! i);
      ixs' ← try_option EFail (inject_sum_rep ρs ρ);
      try_option EFail (nths_error ixs ixs') ≫= get_locals_w;;
      c
    in
    case_blocks res (map do_case cases).

  (* TODO: br inside a case should bypass all but the outermost block. *)
  (* TODO: Handle NoCopy data in GC variants? *)
  Definition compile_case_variant
    (fe : function_env) (τs : list type) (τ' : type) (cases : list (codegen unit)) : codegen unit :=
    res ← try_option EFail (translate_type fe.(fe_type_vars) τ');
    a ← wlalloc fe W.T_i32;
    emit (W.BI_set_local (localimm a));;
    ignore $ case_ptr a (W.Tf [] res)
      (emit W.BI_unreachable)
      (fun μ =>
         let do_case c i :=
           τ ← try_option EFail (τs !! i);
           ρ ← try_option EFail (type_rep fe.(fe_type_vars) τ);
           ιs ← try_option EFail (eval_rep ρ);
           load_primitives mr fe μ a 4%N ιs;;
           c
         in
         load_primitive mr fe μ a 0%N I32R;;
         case_blocks res (map do_case cases);;
         emit (W.BI_get_local (localimm a));;
         drop_ptr mr μ).

  Definition compile_unpack
    (fe : function_env) '(InstrT τs1 τs2 : instruction_type) (c : function_env -> codegen unit) :
    codegen unit :=
    τ ← try_option EFail (last τs1);
    let fe' := fe_extend_unpack fe τ in
    tys ← try_option EFail (translate_instr_type fe.(fe_type_vars) (InstrT τs1 τs2));
    ignore $ block_c tys (c fe').

  Definition compile_tag : codegen unit :=
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m 1)));;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_shl)).

  Definition compile_untag : codegen unit :=
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m 1)));;
    emit (W.BI_binop W.T_i32 (W.Binop_i (W.BOI_shr W.SX_U))).

  Definition compile_new (fe : function_env) (μ : concrete_memory) (τ : type) : codegen unit :=
    ρ ← try_option EFail (type_rep fe.(fe_type_vars) τ);
    ιs ← try_option EFail (eval_rep ρ);
    let n := list_sum (map primitive_size ιs) in
    vs ← save_stack fe ιs;
    alloc mr μ n;;
    a ← wlalloc fe W.T_i32;
    emit (W.BI_set_local (localimm a));;
    set_pointer_flags mr a 0 ιs;;
    store_primitives mr μ a 0%N vs ιs;;
    emit (W.BI_get_local (localimm a));;
    match μ with
    | MemMM => ret tt
    | MemGC => registerroot mr
    end.

  Definition compile_load (fe : function_env) (τ τval : type) (π : path) : codegen unit :=
    (* TODO: Set pointer flags if destructive load. *)
    off ← try_option EFail (path_offset fe τ π);
    ρ ← try_option EFail (type_rep fe.(fe_type_vars) τval);
    ιs ← try_option EFail (eval_rep ρ);
    a ← wlalloc fe W.T_i32;
    emit (W.BI_set_local (localimm a));;
    ignore $ case_ptr a (W.Tf [] (map translate_prim_rep ιs))
      (emit W.BI_unreachable)
      (fun μ => load_primitives mr fe μ a off ιs).

  Definition compile_store (fe : function_env) (τ τval : type) (π : path) : codegen unit :=
    (* TODO: Set pointer flags if strong update. *)
    ρ ← try_option EFail (type_rep fe.(fe_type_vars) τval);
    ιs ← try_option EFail (eval_rep ρ);
    off ← try_option EFail (path_offset fe τ π);
    vs ← save_stack fe ιs;
    a ← wlalloc fe W.T_i32;
    emit (W.BI_tee_local (localimm a));;
    ignore $ case_ptr a (W.Tf [] [])
      (emit W.BI_unreachable)
      (fun μ => store_primitives mr μ a off vs ιs).

  Definition compile_swap (fe : function_env) (τ τval : type) (π : path) : codegen unit :=
    ρ ← try_option EFail (type_rep fe.(fe_type_vars) τval);
    ιs ← try_option EFail (eval_rep ρ);
    off ← try_option EFail (path_offset fe τ π);
    vs ← save_stack fe ιs;
    a ← wlalloc fe W.T_i32;
    emit (W.BI_set_local (localimm a));;
    ignore $ case_ptr a (W.Tf [] (map translate_prim_rep ιs))
      (emit W.BI_unreachable)
      (fun μ => load_primitives mr fe μ a off ιs;; store_primitives mr μ a off vs ιs).

  Definition erased_in_wasm : codegen unit := ret tt.

  (* Some instructions that are erased should still take a step due to
     funny business involving the later modality. *)
  Definition erased_in_wasm_nop : codegen unit := emit W.BI_nop.

  Fixpoint compile_instr (fe : function_env) (e : instruction) : codegen unit :=
    let compile_instrs fe := mapM_ (compile_instr fe) in
    match e with
    | INop _ => emit W.BI_nop
    | IUnreachable _ => emit W.BI_unreachable
    | ICopy (InstrT [τ] _) => compile_copy fe τ
    | ICopy _ => raise EFail
    | IDrop (InstrT [τ] _) => compile_drop fe τ
    | IDrop _ => raise EFail
    | INum _ e' => compile_num e'
    | INumConst (InstrT _ [NumT _ ν]) n => compile_num_const ν n
    | INumConst _ _ => raise EFail
    | IBlock ψ _ es => compile_block fe ψ (compile_instrs fe es)
    | ILoop ψ es => compile_loop fe ψ (compile_instrs fe es)
    | IIte ψ _ es1 es2 => compile_ite fe ψ (compile_instrs fe es1) (compile_instrs fe es2)
    | IBr _ i => emit (W.BI_br i)
    | IReturn _ => emit W.BI_return
    | ILocalGet _ i => compile_local_get fe i
    | ILocalSet _ i => compile_local_set fe i
    | ICodeRef _ i => compile_coderef i
    | IInst _ _ => erased_in_wasm
    | ICall _ i _ => compile_call i
    | ICallIndirect _ => emit (W.BI_call_indirect 0) (* TODO: Type index. *)
    | IInject (InstrT [τ] [SumT (VALTYPE (SumR ρs) _ _) _]) i => compile_inject_sum fe ρs τ i
    | IInject (InstrT [τ] [RefT _ (ConstM μ) (VariantT (MEMTYPE σ _) _)]) i =>
        compile_inject_variant fe μ i τ σ
    | IInject _ _ => raise EFail
    | ICase (InstrT [SumT (VALTYPE (SumR ρs) _ _) _] [τ']) _ ess =>
        compile_case_sum fe ρs τ' (map (compile_instrs fe) ess)
    | ICase (InstrT [RefT _ _ (VariantT _ τs)] [τ']) _ ess =>
        compile_case_variant fe τs τ' (map (compile_instrs fe) ess)
    | ICase _ _ _ => raise EFail
    | IGroup _ => erased_in_wasm_nop
    | IUngroup _ => erased_in_wasm_nop
    | IFold _ => erased_in_wasm
    | IUnfold  _ => erased_in_wasm
    | IPack _ => erased_in_wasm
    | IUnpack ψ _ es => compile_unpack fe ψ (flip compile_instrs es)
    | ITag _ => compile_tag
    | IUntag _ => compile_untag
    | ICast _ => erased_in_wasm
    | INew (InstrT [τ] [RefT _ (ConstM μ) _]) => compile_new fe μ τ
    | INew _ => raise EFail
    | ILoad (InstrT [RefT _ _ τ] [_; τval]) π => compile_load fe τ τval π
    | ILoad _ _ => raise EFail
    | IStore (InstrT [RefT _ _ τ; τval] _) π => compile_store fe τ τval π
    | IStore _ _ => raise EFail
    | ISwap (InstrT [RefT _ _ τ; τval] _) π => compile_swap fe τ τval π
    | ISwap _ _ => raise EFail
    end.

  Definition compile_instrs (fe : function_env) : list instruction -> codegen unit :=
    mapM_ (compile_instr fe).

End Compiler.
