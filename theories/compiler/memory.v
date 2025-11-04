From ExtLib.Structures Require Import Monads Reducible.

Require Import stdpp.list.

From Wasm Require datatypes operations.
Require Import Wasm.numerics.

From RichWasm Require Import prelude layout syntax util.
From RichWasm.compiler Require Import prelude codegen.

Module W. Include Wasm.datatypes <+ Wasm.operations. End W.

Section Compiler.

  Variable mr : module_runtime.

  Definition byte_offset (μ : smemory) (off : nat) : W.static_offset :=
    match μ with
    | MemMM => offset_mm + 4 * N.of_nat off
    | MemGC => offset_gc + 4 * N.of_nat off
    end%N.

  Definition load (μ : smemory) (t : W.value_type) (off : nat) : codegen unit :=
    let off' := byte_offset μ off in
    match μ with
    | MemMM => emit (W.BI_load (memimm mr.(mr_mem_mm)) t None align_word off')
    | MemGC => emit (W.BI_load (memimm mr.(mr_mem_gc)) t None align_word off')
    end.

  Definition store (μ : smemory) (t : W.value_type) (off : nat) : codegen unit :=
    let off' := byte_offset μ off in
    match μ with
    | MemMM => emit (W.BI_store (memimm mr.(mr_mem_mm)) t None align_word off')
    | MemGC => emit (W.BI_store (memimm mr.(mr_mem_gc)) t None align_word off')
    end.

  Definition alloc (μ : smemory) (n : nat) : codegen unit :=
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat n))));;
    match μ with
    | MemMM => emit (W.BI_call (funcimm mr.(mr_func_mmalloc)))
    | MemGC => emit (W.BI_call (funcimm mr.(mr_func_gcalloc)))
    end.

  Definition free : codegen unit := emit (W.BI_call (funcimm mr.(mr_func_free))).

  Definition setflag (i : nat) (f : pointer_flag) : codegen unit :=
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat i))));;
    emit (W.BI_const (W.VAL_int32 (i32_of_flag f)));;
    emit (W.BI_call (funcimm mr.(mr_func_setflag))).

  Definition registerroot : codegen unit :=
    emit (W.BI_call (funcimm mr.(mr_func_registerroot))).

  Definition loadroot : codegen unit :=
    emit (W.BI_load (memimm mr.(mr_mem_gc)) W.T_i32 None align_word offset_gc).

  Definition duproot : codegen unit := loadroot;; registerroot.

  Definition unregisterroot : codegen unit :=
    emit (W.BI_call (funcimm mr.(mr_func_unregisterroot))).

  Definition set_pointer_flags (a : W.localidx) (i : nat) (fs : list pointer_flag) : codegen unit :=
    mapM_
      (fun '(i, f) => emit (W.BI_get_local (localimm a));; setflag i f)
      (zip (seq i (length fs)) fs).

  Definition drop_ptr (μ : smemory) : codegen unit :=
    match μ with
    | MemMM => free
    | MemGC => unregisterroot
    end.

  Fixpoint path_offset (fe : function_env) (τ : type) (π : path) : option nat :=
    match τ, π with
    | _, [] => Some 0
    | StructT _ τs, i :: π' =>
        σs ← mapM (type_size fe.(fe_type_vars)) (take i τs);
        ns ← mapM (eval_size EmptyEnv) σs;
        τ' ← τs !! i;
        n ← path_offset fe τ' π';
        Some (list_sum ns + n)
    | _, _ => None
    end.

  Definition case_ptr {A B : Type}
    (i : W.localidx) (tf : W.function_type)
    (do_int : codegen A)
    (do_heap : smemory -> codegen B)
    : codegen (A * (B * B)) :=
    emit_all [W.BI_get_local (localimm i);
              W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m 1));
              W.BI_binop W.T_i32 (W.Binop_i W.BOI_and);
              W.BI_testop W.T_i32 W.TO_eqz];;
    if_c tf
      do_int
      (emit_all [W.BI_get_local (localimm i);
                 W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 2));
                 W.BI_binop W.T_i32 (W.Binop_i W.BOI_and);
                 W.BI_testop W.T_i32 W.TO_eqz];;
       if_c tf (do_heap MemMM) (do_heap MemGC)).

  Definition ite_gc_ptr
    (ι : primitive_rep) (i : W.localidx) (tf : W.function_type)
    (do_gc : codegen unit) (do_nongc : codegen unit) :
    codegen unit :=
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
    (fe : function_env) (μ : smemory) (con : consumption)
    (a : W.localidx) (off : nat) (ι : primitive_rep) :
    codegen unit :=
    emit (W.BI_get_local (localimm a));;
    let t := translate_prim_rep ι in
    load μ t off;;
    v ← wlalloc fe t;
    emit (W.BI_tee_local (localimm v));;
    let prep_root :=
      match μ, con with
      | MemMM, Move => ret tt
      | MemMM, Copy => duproot
      | MemGC, _ => registerroot
      end
    in
    ite_gc_ptr ι v (W.Tf [W.T_i32] [W.T_i32]) prep_root (ret tt).

  Definition load_primitives
    (fe : function_env) (μ : smemory) (con : consumption)
    (a : W.localidx) (off : nat) (ιs : list primitive_rep) :
    codegen unit :=
    ignore $ foldM
      (fun ι off => load_primitive fe μ con a off ι;; ret (off + primitive_size ι))
      (ret off)
      ιs.

  Definition store_primitive
    (μ : smemory) (a : W.localidx) (off : nat) (v : W.localidx) (ι : primitive_rep) :
    codegen unit :=
    emit (W.BI_get_local (localimm a));;
    emit (W.BI_get_local (localimm v));;
    let t := translate_prim_rep ι in
    match μ with
    | MemMM => store μ t off
    | MemGC =>
        ite_gc_ptr ι v (W.Tf [t] [])
          (loadroot;; store μ t off;; emit (W.BI_get_local (localimm v));; unregisterroot)
          (store μ t off)
    end.

  Definition store_primitives
    (μ : smemory) (a : W.localidx) (off : nat)
    (vs : list W.localidx) (ιs : list primitive_rep) :
    codegen unit :=
    ignore $ foldM
      (fun '(v, ι) off => store_primitive μ a off v ι;; ret (off + primitive_size ι))
      (ret off)
      (zip vs ιs).

End Compiler.
