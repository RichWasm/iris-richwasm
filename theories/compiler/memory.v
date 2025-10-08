From ExtLib.Structures Require Import Monads Reducible.

Require Import stdpp.list.

From Wasm Require datatypes operations.
Require Import Wasm.numerics.

From RichWasm Require Import prelude layout syntax util.
From RichWasm.compiler Require Import prelude codegen util.

Module W. Include Wasm.datatypes <+ Wasm.operations. End W.

Section Compiler.

  Variable mr : module_runtime.

  Definition alloc (cm : concrete_memory) (n : nat) : codegen unit :=
    match cm with
    | MemMM =>
        emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat n))));;
        emit (W.BI_call (funcimm mr.(mr_func_alloc_mm)))
    | MemGC =>
        emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat n))));;
        (* TODO: Pointer map. *)
        emit (W.BI_const (W.VAL_int64 (Wasm_int.int_zero i64m)));;
        emit (W.BI_call (funcimm mr.(mr_func_alloc_gc)))
    end.

  Definition free : codegen unit :=
    emit (W.BI_call (funcimm mr.(mr_func_free))).

  Definition duproot : codegen unit :=
    emit (W.BI_load (memimm mr.(mr_mem_gc)) W.T_i32 None align_word offset_gc);;
    emit (W.BI_call (funcimm mr.(mr_func_registerroot))).

  Definition registerroot : codegen unit :=
    emit (W.BI_call (funcimm mr.(mr_func_registerroot))).

  Definition unregisterroot : codegen unit :=
    emit (W.BI_call (funcimm mr.(mr_func_unregisterroot))).

  Definition primitive_offset (ι : primitive_rep) : W.static_offset :=
    (4 * N.of_nat (primitive_size ι))%N.

  Fixpoint resolve_path (fe : function_env) (τ : type) (π : path) :
    option (W.static_offset * type) :=
    match τ, π with
    | _, [] => Some (0%N, τ)
    | ProdT _ τs, PCProj i :: π' =>
        σs ← mapM (type_size fe.(fe_type_vars)) (take i τs);
        ns ← mapM eval_size σs;
        τ' ← τs !! i;
        '(n, τ'') ← resolve_path fe τ' π';
        Some (N.of_nat (list_sum ns) + n, τ'')%N
    | PadT _ _ τ', PCSkip :: π' => resolve_path fe τ' π'
    | _, _ => None
    end.

  Definition case_ptr {A B : Type}
    (tf : W.function_type) (i : W.localidx)
    (do_int : codegen A) (do_ptr : concrete_memory -> codegen B) :
    codegen (A * (B * B)) :=
    emit (W.BI_get_local (localimm i));;
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m 1)));;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_and));;
    emit (W.BI_testop W.T_i32 W.TO_eqz);;
    if_c tf
      do_int
      (emit (W.BI_get_local (localimm i));;
       emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 2)));;
       emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_and));;
       emit (W.BI_testop W.T_i32 W.TO_eqz);;
       if_c tf (do_ptr MemMM) (do_ptr MemGC)).

  Definition update_gc_ref (i : W.localidx) (ι : primitive_rep) (c : codegen unit) : codegen unit :=
    match ι with
    | PtrR =>
        ignore $ case_ptr (W.Tf [] []) i
          (ret tt)
          (fun cm =>
             match cm with
             | MemMM => ret tt
             | MemGC => emit (W.BI_get_local (localimm i));; c;; emit (W.BI_set_local (localimm i))
             end)
    | _ => ret tt
    end.

  Definition update_gc_refs (ixs : list W.localidx) (ιs : list primitive_rep) (c : codegen unit) :
    codegen unit :=
    mapM_ (fun '(i, ι) => update_gc_ref i ι c) (zip ixs ιs).

  Definition store_as_primitive
    (cm : concrete_memory) (a : W.localidx) (off : W.static_offset) (ι : primitive_rep)
    (v : W.localidx) :
    codegen unit :=
    emit (W.BI_get_local (localimm a));;
    emit (W.BI_get_local (localimm v));;
    let ty := translate_prim_rep ι in
    match cm with
    | MemMM =>
        emit (W.BI_store (memimm mr.(mr_mem_mm)) ty None align_word (offset_mm + off)%N)
    | MemGC =>
        emit (W.BI_store (memimm mr.(mr_mem_gc)) ty None align_word (offset_gc + off)%N)
    end.

  Definition store_as_ser
    (cm : concrete_memory) (a : W.localidx) (off : W.static_offset) (vs : list W.localidx)
    (ιs : list primitive_rep) :
    codegen unit :=
    ignore $ foldM
      (fun '(ι, v) off => store_as_primitive cm a off ι v;; ret (off + primitive_offset ι)%N)
      (ret off)
      (zip ιs vs).

  Definition store_as_gcptr (a : W.localidx) (off : W.static_offset) (v : W.localidx) :
    codegen unit :=
    emit (W.BI_get_local (localimm a));;
    emit (W.BI_get_local (localimm v));;
    unregisterroot;;
    emit (W.BI_store (memimm mr.(mr_mem_gc)) W.T_i32 None align_word (offset_gc + off)%N).

  Fixpoint store_as
    (fe : function_env) (cm : concrete_memory) (a : W.localidx) (off : W.static_offset)
    (ρ : representation) (τ : type) (vs : list W.localidx) {struct τ} :
    codegen unit :=
    match ρ, τ with
    | SumR ρs, SumT _ τs =>
        (* TODO: ref.store on a GC ref with a sum type can change pointer positions. *)
        let fix store_cons_as ρs τs {struct τs} :=
          match ρs, τs with
          | ρ :: ρs', τ :: τs' =>
              let store_case ixs :=
                try_option EFail (nths_error (tail vs) ixs) ≫=
                  store_as fe cm a (off + 1)%N ρ τ
              in
              store_case :: store_cons_as ρs' τs'
          | _, _ => []
          end
        in
        v ← try_option EFail (head vs);
        store_as_primitive cm a off I32R v;;
        emit (W.BI_get_local (localimm v));;
        case_blocks ρs [] (store_cons_as ρs τs)
    | ProdR ρs, ProdT _ τs =>
        let fix store_items_as off vs ρs τs {struct τs} :=
          match ρs, τs with
          | ρ :: ρs', τ :: τs' =>
              ιs ← try_option EFail (eval_rep ρ);
              σ ← try_option EFail (type_size fe.(fe_type_vars) τ);
              n ← try_option EFail (eval_size σ);
              store_as fe cm a off ρ τ (take (length ιs) vs);;
              store_items_as (off + N.of_nat n)%N (drop (length ιs) vs) ρs' τs'
          | _, _ => ret tt
          end
        in
        store_items_as off vs ρs τs
    | _, SerT _ _ => try_option EFail (eval_rep ρ) ≫= store_as_ser cm a off vs
    | _, GCPtrT _ _ => try_option EFail (head vs) ≫= store_as_gcptr a off
    | _, PadT _ _ τ'
    | _, ExistsMemT _ τ'
    | _, ExistsRepT _ τ'
    | _, ExistsSizeT _ τ'
    | _, ExistsTypeT _ _ τ' => store_as fe cm a off ρ τ' vs
    | _, _ => raise EFail
    end.

  Definition load_from_primitive
    (cm : concrete_memory) (a : W.localidx) (off : W.static_offset) (ι : primitive_rep) :
    codegen unit :=
    emit (W.BI_get_local (localimm a));;
    let ty := translate_prim_rep ι in
    match cm with
    | MemMM =>
        emit (W.BI_load (memimm mr.(mr_mem_mm)) ty None align_word (offset_mm + off)%N)
    | MemGC =>
        emit (W.BI_load (memimm mr.(mr_mem_gc)) ty None align_word (offset_gc + off)%N)
    end.

  Definition load_from_ser
    (cm : concrete_memory) (a : W.localidx) (off : W.static_offset) (ιs : list primitive_rep) :
    codegen unit :=
    ignore $ foldM
      (fun ι off => load_from_primitive cm a off ι;; ret (off + primitive_offset ι)%N)
      (ret off)
      ιs.

  Definition load_from_gcptr (a : W.localidx) (off : W.static_offset) : codegen unit :=
    emit (W.BI_get_local (localimm a));;
    emit (W.BI_load (memimm mr.(mr_mem_gc)) W.T_i32 None align_word (offset_gc + off)%N);;
    registerroot.

  Fixpoint load_from
    (fe : function_env) (cm : concrete_memory) (a : W.localidx) (off : W.static_offset) (τ : type) :
    codegen unit :=
    match τ with
    | SumT _ τs =>
        ρs ← try_option EFail (mapM (type_rep fe.(fe_type_vars)) τs);
        ιs ← try_option EFail (eval_rep (SumR ρs));
        vs ← mapM (wlalloc fe) (map translate_prim_rep ιs);
        tag ← try_option EFail (head vs);
        let load_case τ ixs :=
          ixs' ← try_option EFail (nths_error (tail vs) ixs);
          load_from fe cm a (off + 1)%N τ;;
          set_locals_w ixs'
        in
        load_from_primitive cm a off I32R;;
        emit (W.BI_tee_local (localimm tag));;
        case_blocks ρs [] (map load_case τs);;
        restore_stack vs
    | ProdT _ τs =>
        ignore $ foldM
          (fun τ' off =>
             σ ← try_option EFail (type_size fe.(fe_type_vars) τ');
             n ← try_option EFail (eval_size σ);
             load_from fe cm a off τ';;
             ret (off + N.of_nat n)%N)
          (ret off)
          τs
    | SerT _ τ' =>
        ρ ← try_option EFail (type_rep fe.(fe_type_vars) τ');
        try_option EFail (eval_rep ρ) ≫= load_from_ser cm a off
    | GCPtrT _ _ => load_from_gcptr a off
    | PadT _ _ τ'
    | ExistsMemT _ τ'
    | ExistsRepT _ τ'
    | ExistsSizeT _ τ'
    | ExistsTypeT _ _ τ' => load_from fe cm a off τ'
    | _ => raise EFail
    end.

End Compiler.
