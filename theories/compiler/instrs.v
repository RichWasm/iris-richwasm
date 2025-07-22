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
Import FunctorNotation.
Import MonadNotation.
Local Open Scope monad.

From stdpp Require Import -(notations) list_numbers.

From Wasm Require datatypes operations.
Require Import Wasm.numerics.

From RichWasm Require term typing.
From RichWasm.compiler Require Import numerics types util.
Require Import RichWasm.util.dlist.
Import RichWasm.util.dlist.Notation.

Module R. Include term <+ typing. End R.
Module W. Include datatypes <+ operations. End W.

(* locals exclusive to webassembly (compiler-generated temporaries, etc) *)
Notation wlocal_ctx := (list W.value_type) (only parsing).

Notation dexpr := (dlist W.basic_instruction).

Record codegen (A : Type) :=
  { uncodegen : stateT wlocal_ctx
                       (writerT (@DList.Monoid_dlist W.basic_instruction)
                                (sum error))
                       A }.

Arguments Build_codegen {A} _.
Arguments uncodegen {A} _.

Existing Instance Monad_stateT.

Global Instance Monad_codegen : Monad codegen :=
  { ret := fun _ => Build_codegen ∘ ret;
    bind := fun _ _ c f => Build_codegen (uncodegen c >>= uncodegen ∘ f) }.

Global Instance MonadExc_codegen : MonadExc error codegen :=
  { raise := fun _ => Build_codegen ∘ raise;
    catch := fun _ b h => Build_codegen (catch (uncodegen b) (uncodegen ∘ h)) }.

Global Instance MonadState_codegen : MonadState wlocal_ctx codegen :=
  { get := Build_codegen get;
    put := Build_codegen ∘ put }.

Global Instance MonadWriter_codegen : MonadWriter (@DList.Monoid_dlist W.basic_instruction) codegen :=
  { tell := Build_codegen ∘ tell;
    listen := fun _ => Build_codegen ∘ listen ∘ uncodegen;
    (* Work around broken implementation of `pass` in ExtLib.
       https://github.com/rocq-community/coq-ext-lib/issues/153 *)
    pass := fun _ c => Build_codegen (mkStateT (fun s =>
      pass ('(x, f, s) <- runStateT (uncodegen c) s;;
            ret (x, s, f)))) }.

Definition lift_error {A} (c : error + A) : codegen A :=
  Build_codegen (lift (lift c)).

Definition try_option {A} (e : error) (x : option A) : codegen A :=
  match x with
  | None => raise e
  | Some x' => ret x'
  end.

Definition run_codegen (c : codegen unit) (wl : wlocal_ctx) : error + wlocal_ctx * W.expr :=
  match runWriterT (runStateT (uncodegen c) wl) with
  | inl e => inl e
  | inr x => inr (snd (PPair.pfst x), DList.to_list (PPair.psnd x))
  end.

Definition emit (e : W.basic_instruction) : codegen unit :=
  tell (DList.singleton e).

Definition capture {A} (c : codegen A) : codegen (A * dexpr) :=
  censor (const []%DL) (listen c).

Definition block_c {A} (tf : W.function_type) (c : codegen A) : codegen A :=
  '(x, es) <- capture c;;
  emit (W.BI_block tf (DList.to_list es));;
  ret x.

Definition loop_c {A} (tf : W.function_type) (c : codegen A) : codegen A :=
  '(x, es) <- capture c;;
  emit (W.BI_loop tf (DList.to_list es));;
  ret x.

Definition if_c {A B} (tf : W.function_type) (thn : codegen A) (els : codegen B) : codegen (A * B) :=
  '(x1, es1) <- capture thn;;
  '(x2, es2) <- capture els;;
  emit (W.BI_if tf (DList.to_list es1) (DList.to_list es2));;
  ret (x1, x2).

Definition if_gc_bit_set {A B} (tf : W.function_type) (gc : codegen B) (mm : codegen A)
  : codegen (A * B) :=
  emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 1%Z)));;
  emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_and));;
  emit (W.BI_testop W.T_i32 W.TO_eqz);;
  if_c tf mm gc.

Definition unset_gc_bit : codegen unit :=
  emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 1%Z)));;
  emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_sub)).

Fixpoint loads'
  (mem : W.memidx)
  (base_ptr_var : W.localidx)
  (off : W.static_offset)
  (tys : list W.value_type)
  : codegen unit :=
  match tys with
  | [] => ret tt
  | ty :: tys =>
      emit (W.BI_get_local (localimm base_ptr_var));;
      emit (W.BI_load (memimm mem) ty None 0%N off);;
      loads' mem base_ptr_var (off + N.of_nat (W.length_t ty))%N tys
  end.

Definition loads mem base_ptr_var tys : codegen unit :=
  loads' mem base_ptr_var 0%N tys.

Fixpoint loc_stores'
  (base_ptr_var : W.localidx)
  (mem : W.memidx)
  (off : W.static_offset)
  (val_var_tys : list (W.localidx * W.value_type))
  : codegen unit :=
  match val_var_tys with
  | [] => ret tt
  | (val_var, ty) :: val_var_tys =>
      emit (W.BI_get_local (localimm base_ptr_var));;
      emit (W.BI_get_local (localimm val_var));;
      emit (W.BI_store (memimm mem) ty None 0%N off);;
      loc_stores' base_ptr_var mem (off + N.of_nat (W.length_t ty))%N val_var_tys
  end.

Definition loc_stores base_ptr_var mem val_var_tys : codegen unit :=
  loc_stores' base_ptr_var mem 0%N val_var_tys.

Definition stores base_ptr_var mem (val_vars : list W.localidx) (tys : list W.value_type)
  : codegen unit :=
  loc_stores base_ptr_var mem (zip val_vars tys).

Inductive VarScope :=
  | VSGlobal
  | VSLocal.

Definition scope_get_set (scope : VarScope) :
  (W.immediate -> W.basic_instruction) *
  (W.immediate -> W.basic_instruction) :=
  match scope with
  | VSGlobal => (W.BI_get_global, W.BI_set_global)
  | VSLocal => (W.BI_get_local, W.BI_set_local)
  end.

Definition for_gc_ref_vars (scope : VarScope) (vars : list W.immediate) (m : codegen unit) : codegen unit :=
  iterM
    (fun var =>
       let '(get, set) := scope_get_set scope in
       emit (get var);;
       if_gc_bit_set (W.Tf [W.T_i32] [W.T_i32]) m (ret tt);;
       emit (set var))
    vars.

Fixpoint global_layout (globs : list R.GlobalType) (idx : nat) : option (W.globalidx * R.Typ) :=
  match globs, idx with
  | [R.GT _ ty], 0 => Some (W.Mk_globalidx 0, ty)
  | R.GT _ ty :: globs', S idx' => global_layout globs' (length (translate_type ty) + idx')
  | _, _ => None
  end.

Section Instrs.

  Variable me : module_env.
  Variable fe : function_env.

  Definition wnext : codegen W.localidx :=
    temps <- get;;
    ret (W.Mk_localidx (fe.(fe_wlocal_offset) + length temps)).

  Definition walloc (t : W.value_type) : codegen W.localidx :=
    temps <- get;;
    put (temps ++ [t]);;
    ret (W.Mk_localidx (fe.(fe_wlocal_offset) + length temps)).

  Definition wallocs (tys : list W.value_type) : codegen (list W.localidx) :=
    mapT walloc tys.

  Definition walloc_args (tys : list W.value_type) : codegen (list W.localidx) :=
    vars <- wallocs tys;;
    @forT list _ _ _ _ _ vars (fun var => emit (W.BI_set_local (localimm var)));;
    ret vars.

  Definition walloc_rvalue (ty : R.Typ) : codegen W.localidx :=
    i <- wnext;;
    forT (translate_type ty) walloc;;
    ret i.

  Definition walloc_rvalues (tys : list R.Typ) : codegen W.localidx :=
    i <- wnext;;
    forT tys walloc_rvalue;;
    ret i.

  Definition tagged_store
    (base_ptr : W.localidx)
    (arg_vars : list W.localidx)
    (get_offset : codegen unit)
    (ty : R.Typ)
    : codegen unit :=
    emit (W.BI_tee_local (localimm base_ptr));;
    emit (W.BI_get_local (localimm base_ptr));;
    let tys := translate_type ty in
    if_gc_bit_set (W.Tf [] [])
      (emit (W.BI_get_local (localimm base_ptr));;
       unset_gc_bit;;
       get_offset;;
       emit (W.BI_set_local (localimm base_ptr));;
       stores base_ptr me.(me_runtime).(mr_mem_gc) arg_vars tys)
      (emit (W.BI_get_local (localimm base_ptr));;
       get_offset;;
       stores base_ptr me.(me_runtime).(mr_mem_mm) arg_vars tys);;
    ret tt.

  Definition local_layout (L : R.Local_Ctx) (idx : nat) : error + (W.localidx * R.Typ) :=
    let fix go L base i :=
      match L, i with
      | (τ, sz) :: L, 0 => inr (W.Mk_localidx base, τ)
      | (τ, sz) :: L, S i =>
          sz_const <- size_upper_bound fe.(fe_size_bounds) sz;;
          go L (base + sz_const) i
      | [], _ => inl (EIndexOutOfBounds idx)
      end
    in
    go L 0 idx.

  Definition gc_loads
    (ref_var : W.localidx)
    (get_offset : codegen unit)
    (tys : list W.value_type)
    : codegen unit :=
    base_ptr_var <- walloc W.T_i32;;
    emit (W.BI_get_local (localimm ref_var));;
    unset_gc_bit;;
    get_offset;;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add));;
    emit (W.BI_set_local (localimm base_ptr_var));;
    loads me.(me_runtime).(mr_mem_gc) base_ptr_var tys.

  Definition lin_loads
    (ref_var : W.localidx)
    (get_offset : codegen unit)
    (tys : list W.value_type)
    : codegen unit :=
    base_ptr_var <- walloc W.T_i32;;
    emit (W.BI_get_local (localimm ref_var));;
    get_offset;;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add));;
    emit (W.BI_set_local (localimm base_ptr_var));;
    loads me.(me_runtime).(mr_mem_mm) base_ptr_var tys.

  Definition tagged_loads
    (base_ptr: W.localidx)
    (get_offset: codegen unit)
    (tys: list W.value_type)
    : codegen unit :=
    emit (W.BI_get_local (localimm base_ptr));;
    if_gc_bit_set (W.Tf [] tys)
      (gc_loads base_ptr get_offset tys)
      (lin_loads base_ptr get_offset tys);;
    ret tt.

  Definition tagged_load
    (base_ptr : W.localidx)
    (get_offset : codegen unit)
    (ty : R.Typ)
    : codegen unit :=
    let tys := translate_type ty in
    tagged_loads base_ptr get_offset tys.

  Definition tagged_store' (get_offset : codegen unit) (ty : R.Typ) : codegen unit :=
    let tys := translate_type ty in
    arg_vars <- walloc_args tys;;
    base_ptr_var <- walloc W.T_i32;;
    tagged_store base_ptr_var arg_vars get_offset ty.

  Definition get_i64_local (loc : W.localidx) : codegen unit :=
    emit (W.BI_get_local (localimm loc));;
    emit (W.BI_cvtop W.T_i32 W.CVO_reinterpret W.T_i64 None);;
    emit (W.BI_get_local (localimm loc + 1));;
    emit (W.BI_const (W.VAL_int64 (Wasm_int.int_of_Z i64m 32)));;
    emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_rotl));;
    emit (W.BI_cvtop W.T_i32 W.CVO_reinterpret W.T_i64 None);;
    emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_or)).

  Definition set_i64_local (loc : W.localidx) : codegen unit :=
    tmp <- walloc W.T_i64;;
    emit (W.BI_tee_local (localimm tmp));;
    emit (W.BI_const (W.VAL_int64 (wasm_extend_u int32_minus_one)));;
    emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_and));;
    emit (W.BI_cvtop W.T_i64 W.CVO_convert W.T_i32 None);;
    emit (W.BI_set_local (localimm loc));;
    emit (W.BI_get_local (localimm tmp));;
    emit (W.BI_const (W.VAL_int64 (Wasm_int.int_of_Z i64m 32)));;
    emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_rotr));;
    emit (W.BI_set_local (localimm loc + 1)).

  Definition numtyp_gets (ty : R.NumType) (loc : W.localidx) : codegen unit :=
    match ty with
    | R.Int s R.i32 => emit (W.BI_get_local (localimm loc))
    | R.Float R.f32 =>
        emit (W.BI_get_local (localimm loc));;
        emit (W.BI_cvtop W.T_i32 W.CVO_reinterpret W.T_f32 None)
    | R.Int s R.i64 => get_i64_local loc
    | R.Float R.f64 =>
        get_i64_local loc;;
        emit (W.BI_cvtop W.T_i64 W.CVO_reinterpret W.T_f64 None)
    end.

  Definition numtyp_sets (ty : R.NumType) (loc : W.localidx) : codegen unit :=
    match ty with
    | R.Int s R.i32 => emit (W.BI_set_local (localimm loc))
    | R.Float R.f32 =>
        emit (W.BI_cvtop W.T_f32 W.CVO_reinterpret W.T_i32 None);;
        emit (W.BI_set_local (localimm loc))
    | R.Int s R.i64 => set_i64_local loc
    | R.Float R.f64 =>
        emit (W.BI_cvtop W.T_f64 W.CVO_reinterpret W.T_i64 None);;
        set_i64_local loc
    end.

  Fixpoint local_gets (ty : R.Typ) (loc : W.localidx) : codegen unit :=
    match ty with
    | R.Num nτ => numtyp_gets nτ loc
    | R.TVar α => emit (W.BI_get_local (localimm loc))
    | R.Unit => ret tt
    | R.ProdT τs =>
        let fix loop τs0 sz :=
          match τs0 with
          | τ0 :: τs0' =>
              let sz := type_words τ0 in
              local_gets τ0 loc;;
              loop τs0' (localimm loc + sz)
          | [] => ret tt
          end in
        loop τs (localimm loc)
    | R.CoderefT χ => emit (W.BI_get_local (localimm loc))
    | R.Rec q τ => local_gets τ loc
    | R.PtrT ℓ => emit (W.BI_get_local (localimm loc))
    | R.ExLoc q τ => local_gets τ loc
    | R.OwnR ℓ => ret tt
    | R.CapT cap ℓ ψ => ret tt
    | R.RefT cap ℓ ψ => emit (W.BI_get_local (localimm loc))
    end.

  Fixpoint local_sets (ty : R.Typ) (loc : W.localidx) : codegen unit :=
    match ty with
    | R.Num nτ =>
        numtyp_sets nτ loc
    | R.TVar α =>
        emit (W.BI_set_local (localimm loc))
    | R.Unit =>
        ret tt
    | R.ProdT τs =>
        let fix loop τs0 sz :=
          match τs0 with
          | τ0 :: τs0' =>
              let sz := type_words τ0 in
              local_sets τ0 loc;;
              loop τs0' (localimm loc + sz)
          | [] => ret tt
          end in
        loop τs (localimm loc)
    | R.CoderefT χ =>
        emit (W.BI_set_local (localimm loc))
    | R.Rec q τ =>
        local_sets τ loc
    | R.PtrT ℓ =>
        emit (W.BI_set_local (localimm loc))
    | R.ExLoc q τ =>
        local_sets τ loc
    | R.OwnR ℓ =>
        ret tt
    | R.CapT cap ℓ ψ =>
        ret tt
    | R.RefT cap ℓ ψ =>
        emit (W.BI_set_local (localimm loc))
    end.

  Definition save_stack (tys : list R.Typ) : codegen W.localidx :=
    idx <- walloc_rvalues tys;;
    local_sets (R.ProdT tys) idx;;
    ret idx.

  Definition restore_stack (tys : list R.Typ) (idx : W.localidx) : codegen unit :=
    local_gets (R.ProdT tys) idx.

  Fixpoint compile_sz (sz : R.Size) : codegen unit :=
    match sz with
    | R.SizeVar σ =>
      local_idx <- try_option (EIndexOutOfBounds σ) (lookup σ fe.(fe_size_locals));;
      emit (W.BI_get_local (localimm local_idx))
    | R.SizePlus sz1 sz2 =>
      compile_sz sz1;;
      compile_sz sz2;;
      emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add))
    | R.SizeConst c =>
      emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat c))))
    end.

  Definition compile_ind (ind: R.Index) : codegen unit :=
    match ind with
    | R.SizeI sz => compile_sz sz
    | R.LocI _
    | R.QualI _
    | R.TypI _ => ret tt
    end.

  Definition array_bounds_check (base idx : W.localidx) : codegen unit :=
    tagged_load
      base
      (emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat 0)))))
      (R.Num (R.Int R.U R.i32));;
    emit (W.BI_get_local (localimm idx));;
    emit (W.BI_relop W.T_i32 (W.Relop_i (W.ROI_lt (W.SX_U)))).

  Definition array_offset (idx : W.localidx) (size : nat) : codegen unit :=
    emit (W.BI_get_local (localimm idx));;
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat size))));;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_mul));;
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat 4))));; (* skip header length word *)
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add)).

  Fixpoint compile_instr (e : R.instr R.TyAnn) : codegen unit :=
    match e with
    | R.INumConst _ ty n =>
        let ty' := translate_num_type ty in
        emit (W.BI_const (compile_Z ty' (Z.of_nat n)))
    | R.IUnit _ => ret tt
    | R.INum _ e' => emit (compile_num_instr e')
    | R.IUnreachable _ => emit (W.BI_unreachable)
    | R.INop _ => emit W.BI_nop
    | R.IDrop (R.Arrow in_ty _, _) =>
        ty <- try_option EWrongTypeAnn (head in_ty);;
        let tys := translate_type ty in
        val <- save_stack [ty];;
        let refs := map (fun i => localimm val + i) (find_refs LMNative ty) in
        for_gc_ref_vars VSLocal refs
          (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot))));;
        restore_stack [ty] val;;
        forT tys (const (emit W.BI_drop));;
        ret tt
    | R.IBlock _ ty _ es =>
        block_c (translate_arrow_type ty) (forT es compile_instr);;
        ret tt
    | R.ILoop _ ty es =>
        loop_c (translate_arrow_type ty) (forT es compile_instr);;
        ret tt
    | R.IIte _ ty _ es1 es2 =>
        let ty' := translate_arrow_type ty in
        if_c ty' (forT es1 compile_instr) (forT es2 compile_instr);;
        ret tt
    | R.IBr _ l => emit (W.BI_br l)
    | R.IBrIf _ l => emit (W.BI_br_if l)
    | R.IBrTable _ ls l => emit (W.BI_br_table ls l)
    | R.IRet (R.Arrow in_ty _, _) =>
        let return_ty := ssrfun.Option.default [] fe.(fe_return_type) in
        let drop_ty := take (length in_ty - length return_ty) in_ty in
        r <- save_stack return_ty;;
        d <- save_stack drop_ty;;
        let refs := map (fun i => localimm d + i) (flat_map (find_refs LMNative) drop_ty) in
        for_gc_ref_vars VSLocal refs
          (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot))));;
        restore_stack return_ty r;;
        emit W.BI_return
    | R.IGetLocal (_, R.LSig L _) x _ =>
        '(x', ty) <- lift_error (local_layout L x);;
        local_gets ty x';;
        val <- save_stack [ty];;
        let refs := map (fun i => localimm val + i) (find_refs LMNative ty) in
        for_gc_ref_vars VSLocal refs
          (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_duproot))));;
        restore_stack [ty] val
    | R.ISetLocal (_, R.LSig L _) x =>
        '(x', ty) <- lift_error (local_layout L x);;
        let refs := map (fun i => localimm x' + i) (find_refs LMWords ty) in
        for_gc_ref_vars VSLocal refs
          (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot))));;
        local_sets ty x'
    | R.IGetGlobal _ x =>
        '(x', ty) <- try_option (EIndexOutOfBounds x) (global_layout me.(me_globals) x);;
        forT (imap (fun i _ => globalimm x' + i) (translate_type ty))
          (emit ∘ W.BI_get_global);;
        val <- save_stack [ty];;
        let refs := map (fun i => localimm val + i) (find_refs LMNative ty) in
        for_gc_ref_vars VSLocal refs
          (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_duproot))));;
        restore_stack [ty] val
    | R.ISetGlobal _ x =>
        '(x', ty) <- try_option (EIndexOutOfBounds x) (global_layout me.(me_globals) x);;
        let refs := map (fun i => globalimm x' + i) (find_refs LMNative ty) in
        for_gc_ref_vars VSGlobal refs
          (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot))));;
        forT (imap (fun i _ => globalimm x' + i) (translate_type ty))
          (emit ∘ W.BI_set_global);;
        ret tt
    | R.ICoderef _ x =>
        emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat x))));;
        emit (W.BI_get_global (globalimm me.(me_runtime).(mr_global_table_offset)));;
        emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add))
    | R.ICallIndirect (R.Arrow in_ty _, _) idxs =>
        args <- save_stack in_ty;;
        forT idxs compile_ind;;
        restore_stack in_ty args;;
        emit (W.BI_call_indirect (tableimm me.(me_runtime).(mr_table)))
    | R.ICall (R.Arrow in_ty _, _) x idxs =>
        args <- save_stack in_ty;;
        forT idxs compile_ind;;
        restore_stack in_ty args;;
        (* TODO: Translate function index. *)
        emit (W.BI_call x)
    | R.IMemUnpack _ ty _ es =>
        block_c (translate_arrow_type ty) (forT es compile_instr);;
        ret tt
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
        ref <- walloc W.T_i32;;
        fields <- try_option EWrongTypeAnn (head in_ty >>= struct_fields);;
        field_ty <- try_option EWrongTypeAnn (fst <$> lookup i fields);;
        offset <- lift_error (struct_field_offset fields i);;
        emit (W.BI_tee_local (localimm ref));;
        tagged_load ref (compile_sz offset) field_ty;;
        val <- save_stack [field_ty];;
        emit (W.BI_get_local (localimm ref));;
        let refs := map (fun i => localimm val + i) (find_refs LMNative field_ty) in
        if_gc_bit_set (W.Tf [] [])
          (for_gc_ref_vars VSLocal refs
             (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_registerroot)))))
          (for_gc_ref_vars VSLocal refs
             (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_duproot)))));;
        restore_stack [field_ty] val
    | R.IStructSet (R.Arrow in_ty _, _) i =>
        ref <- walloc W.T_i32;;
        fields <- try_option EWrongTypeAnn (head in_ty >>= struct_fields);;
        field_ty <- try_option EWrongTypeAnn (fst <$> lookup i fields);;
        val_ty <- try_option EWrongTypeAnn (lookup 1 in_ty);;
        offset <- lift_error (struct_field_offset fields i);;

        emit (W.BI_tee_local (localimm ref));;
        if_gc_bit_set (W.Tf [] [])
          (ret tt)
          (let tys := translate_type field_ty in
           gc_loads ref (compile_sz offset) tys;;
           val <- save_stack [field_ty];;
           let refs := map (fun i => localimm val + i) (find_refs LMNative field_ty) in
           for_gc_ref_vars VSLocal refs
             (emit (W.BI_call (funcimm me.(me_runtime).(mr_func_unregisterroot)))));;

        emit (W.BI_get_local (localimm ref));;
        if_gc_bit_set (W.Tf [] [])
          (val <- save_stack [val_ty];;
           let refs := map (fun i => localimm val + i) (find_refs LMNative val_ty) in
           for_gc_ref_vars VSLocal refs
             (emit (W.BI_load (memimm me.(me_runtime).(mr_mem_gc)) W.T_i32 None 0%N 0%N));;
           restore_stack [val_ty] val)
          (ret tt);;

        emit (W.BI_get_local (localimm ref));;
        tagged_store' (compile_sz offset) val_ty
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
        (* TODO: registerroot if GC array;
                 duproot if MM array *)
        idx <- walloc W.T_i32;;
        ref <- walloc W.T_i32;;
        emit (W.BI_set_local (localimm idx));;
        emit (W.BI_set_local (localimm ref));;

        tagged_load
          ref
          (emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m 0))))
          (R.Num (R.Int R.U R.i32));;

        emit (W.BI_get_local (localimm idx));;
        emit (W.BI_relop W.T_i32 (W.Relop_i (W.ROI_lt (W.SX_U))));;

        elem_ty <- try_option EWrongTypeAnn (head in_ty >>= array_elem);;
        let get_offset :=
          emit (W.BI_get_local (localimm idx));;
          let words := type_words elem_ty in
          emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat words))));;
          emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_mul));;
          emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m 4)));; (* skip header length word *)
          emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add))
        in
        let elem_tys := translate_type elem_ty in
        if_c (W.Tf [] elem_tys)
          (tagged_load ref get_offset elem_ty)
          (emit W.BI_unreachable);;
        ret tt
    | R.IArraySet (R.Arrow in_ty _, _) =>
        (* TODO: unregisterroot if GC array;
                 duproot a bunch of times if MM array *)
        elem_ty <- try_option EWrongTypeAnn (head in_ty >>= array_elem);;
        val <- save_stack [elem_ty];;
        idx <- walloc W.T_i32;;
        ref <- walloc W.T_i32;;
        emit (W.BI_set_local (localimm idx));;
        emit (W.BI_tee_local (localimm ref));;
        array_bounds_check ref idx;;
        if_c (W.Tf [] [])
          (emit (W.BI_get_local (localimm ref));;
           restore_stack [elem_ty] val;;
           let words := type_words elem_ty in
           tagged_store' (array_offset idx words) elem_ty)
          (emit W.BI_unreachable);;
        ret tt
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
