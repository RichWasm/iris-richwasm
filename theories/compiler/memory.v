From ExtLib.Structures Require Import Monads Reducible.

Require Import stdpp.list.

From Wasm Require datatypes operations.
Require Import Wasm.numerics.

From RichWasm Require Import prelude layout syntax util.
From RichWasm.compiler Require Import prelude codegen util.

Module W. Include Wasm.datatypes <+ Wasm.operations. End W.

Section Compiler.

  Variable mr : module_runtime.

  Definition load (μ : concrete_memory) (t : W.value_type) (off : W.static_offset) : codegen unit :=
    match μ with
    | MemMM => emit (W.BI_load (memimm mr.(mr_mem_mm)) t None align_word (offset_mm + off)%N)
    | MemGC => emit (W.BI_load (memimm mr.(mr_mem_gc)) t None align_word (offset_gc + off)%N)
    end.

  Definition store (μ : concrete_memory) (t : W.value_type) (off : W.static_offset) : codegen unit :=
    match μ with
    | MemMM => emit (W.BI_store (memimm mr.(mr_mem_mm)) t None align_word (offset_mm + off)%N)
    | MemGC => emit (W.BI_store (memimm mr.(mr_mem_gc)) t None align_word (offset_gc + off)%N)
    end.

  Definition primitive_offset (ι : primitive_rep) : W.static_offset :=
    (4 * N.of_nat (primitive_size ι))%N.

  Definition alloc (μ : concrete_memory) (n : nat) : codegen unit :=
    match μ with
    | MemMM =>
        emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat n))));;
        emit (W.BI_call (funcimm mr.(mr_func_mmalloc)))
    | MemGC =>
        emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat n))));;
        emit (W.BI_call (funcimm mr.(mr_func_gcalloc)))
    end.

  Definition free : codegen unit :=
    emit (W.BI_call (funcimm mr.(mr_func_free))).

  Definition registerroot : codegen unit :=
    emit (W.BI_call (funcimm mr.(mr_func_registerroot))).

  Definition loadroot : codegen unit :=
    emit (W.BI_load (memimm mr.(mr_mem_gc)) W.T_i32 None align_word offset_gc).

  Definition duproot : codegen unit := loadroot;; registerroot.

  Definition unregisterroot : codegen unit :=
    emit (W.BI_call (funcimm mr.(mr_func_unregisterroot))).

  Definition drop_ptr (μ : concrete_memory) : codegen unit :=
    match μ with
    | MemMM => free
    | MemGC => unregisterroot
    end.

  Fixpoint resolve_path
    (fe : function_env) (τ : type) (π : path) : option (W.static_offset * type) :=
    match τ, π with
    | SerT _ τ', [] => Some (0%N, τ')
    | StructT _ τs, PCProj i :: π' =>
        σs ← mapM (type_size fe.(fe_type_vars)) (take i τs);
        ns ← mapM eval_size σs;
        τ' ← τs !! i;
        '(n, τ'') ← resolve_path fe τ' π';
        Some (N.of_nat (list_sum ns) + n, τ'')%N
    | _, _ => None
    end.

  Definition case_ptr {A B : Type}
    (i : W.localidx) (tf : W.function_type)
    (do_int : codegen A) (do_heap : concrete_memory -> codegen B) :
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
       if_c tf (do_heap MemMM) (do_heap MemGC)).

  Definition ite_gc_ptr
    (ι : primitive_rep) (i : W.localidx) (tf : W.function_type)
    (do_gc : codegen unit) (do_nongc : codegen unit) : codegen unit :=
    match ι with
    | PtrR =>
        ignore $ case_ptr i tf
          do_nongc
          (fun μ => match μ with MemMM => do_nongc | MemGC => do_gc end)
    | _ => do_nongc
    end.

  Definition map_gc_ptr (ι : primitive_rep) (i : W.localidx) (c : codegen unit) : codegen unit :=
    ite_gc_ptr ι i (W.Tf [] [])
      (emit (W.BI_get_local (localimm i));; c;; emit (W.BI_set_local (localimm i)))
      (ret tt).

  Definition map_gc_ptrs
    (ιs : list primitive_rep) (ixs : list W.localidx) (c : codegen unit) : codegen unit :=
    mapM_ (fun '(ι, i) => map_gc_ptr ι i c) (zip ιs ixs).

  Definition load_primitive
    (fe : function_env) (μ : concrete_memory) (a : W.localidx) (off : W.static_offset)
    (ι : primitive_rep) :
    codegen unit :=
    emit (W.BI_get_local (localimm a));;
    let t := translate_prim_rep ι in
    load μ t off;;
    v ← wlalloc fe t;
    emit (W.BI_tee_local (localimm v));;
    ite_gc_ptr ι v (W.Tf [W.T_i32] [W.T_i32]) registerroot (ret tt).

  Definition load_primitives
    (fe : function_env) (μ : concrete_memory) (a : W.localidx) (off : W.static_offset)
    (ιs : list primitive_rep) :
    codegen unit :=
    ignore $ foldM
      (fun ι off => load_primitive fe μ a off ι;; ret (off + primitive_offset ι)%N)
      (ret off)
      ιs.

  Definition store_primitive
    (μ : concrete_memory) (a : W.localidx) (off : W.static_offset)
    (v : W.localidx) (ι : primitive_rep) :
    codegen unit :=
    emit (W.BI_get_local (localimm a));;
    emit (W.BI_get_local (localimm v));;
    let t := translate_prim_rep ι in
    ite_gc_ptr ι v (W.Tf [t] [])
      (loadroot;; store μ t off;; emit (W.BI_get_local (localimm v));; unregisterroot)
      (store μ t off).

  Definition store_primitives
    (μ : concrete_memory) (a : W.localidx) (off : W.static_offset)
    (vs : list W.localidx) (ιs : list primitive_rep) :
    codegen unit :=
    ignore $ foldM
      (fun '(v, ι) off => store_primitive μ a off v ι;; ret (off + primitive_offset ι)%N)
      (ret off)
      (zip vs ιs).

End Compiler.
