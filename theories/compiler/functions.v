From Coq Require Import List.
Import Coq.Lists.List.ListNotations.
Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinInt.
Local Open Scope program_scope.

From ExtLib.Data Require Import List.
From ExtLib.Data.Monads Require Import EitherMonad StateMonad WriterMonad.
From ExtLib.Structures Require Import Monads Reducible Traversable.
Import MonadNotation.
Local Open Scope monad.

From stdpp Require Import -(notations) list_numbers.

From Wasm Require datatypes operations.
Require Import Wasm.numerics.

From RichWasm Require term typing.
From RichWasm.compiler Require Import error numerics types.
Require Import RichWasm.util.dlist.
Import RichWasm.util.dlist.Notation.

Module R. Include term <+ typing. End R.
Module W. Include datatypes <+ operations. End W.

(* locals exclusive to webassembly (compiler-generated temporaries, etc) *)
Notation wlocal_ctx := (list W.value_type).

Notation instr_list := (dlist W.basic_instruction).

Record wst (A : Type) :=
  { un_wst : stateT
               wlocal_ctx
               (writerT
                  (@DList.Monoid_dlist W.basic_instruction)
                  (sum error))
               A }.

Arguments Build_wst {A} _.
Arguments un_wst {A} _.

Existing Instance Monad_stateT.

Global Instance Monad_wst : Monad wst :=
  { ret := fun _ x => Build_wst (ret x);
    bind := fun _ _ c f => Build_wst (bind (un_wst c) (fun x => un_wst (f x))) }.

Global Instance MonadExc_wst : MonadExc error wst :=
  { raise := fun _ e => Build_wst (raise e);
    catch := fun _ body hnd => Build_wst (catch (un_wst body) (fun e => un_wst (hnd e))) }.

Global Instance MonadState_wst : MonadState wlocal_ctx wst :=
  { get := Build_wst get;
    put := fun x => Build_wst (put x) }.

Global Instance MonadWriter_wst : MonadWriter (@DList.Monoid_dlist W.basic_instruction) wst :=
  { tell := fun x => Build_wst (tell x);
    listen := fun _ c => Build_wst (listen (un_wst c));
    (* Work around broken implementation of `pass` in ExtLib.
       https://github.com/rocq-community/coq-ext-lib/issues/153 *)
    pass := fun _ c => Build_wst (mkStateT (fun s =>
      pass ('(a, t, s) <- runStateT (un_wst c) s;;
            ret (a, s, t)))) }.

Record compiler_mod_ctx :=
  { mem_gc : W.immediate;
    mem_lin : W.immediate;
    free : W.immediate;
    alloc : W.immediate;
    registerroot : W.immediate;
    unregisterroot : W.immediate;
    duproot : W.immediate;
    coderef_offset : W.immediate;
    fn_tab : W.immediate }.

Definition lift_error {A} (c : error + A) : wst A :=
  Build_wst (lift (lift c)).

Definition try_option {A} (e : error) (x : option A) : wst A :=
  match x with
  | None => raise e
  | Some x' => ret x'
  end.

Definition run_compiler (c : wst unit) (wl : wlocal_ctx) : error + wlocal_ctx * list W.basic_instruction :=
  match runWriterT (runStateT (un_wst c) wl) with
  | inl e => inl e
  | inr x => inr (snd (PPair.pfst x), DList.to_list (PPair.psnd x))
  end.

Definition emit (e : W.basic_instruction) : wst unit :=
  tell (DList.singleton e).

Definition capture {A} (c : wst A) : wst (A * instr_list) :=
  censor (const []%DL) (listen c).

Definition block_c {A} (tf : W.function_type) (c : wst A) : wst A :=
  '(x, es) <- capture c;;
  emit (W.BI_block tf (DList.to_list es));;
  ret x.

Definition loop_c {A} (tf : W.function_type) (c : wst A) : wst A :=
  '(x, es) <- capture c;;
  emit (W.BI_loop tf (DList.to_list es));;
  ret x.

Definition if_c {A B} (tf : W.function_type) (thn : wst A) (els : wst B) : wst (A * B) :=
  '(x1, es1) <- capture thn;;
  '(x2, es2) <- capture els;;
  emit (W.BI_if tf (DList.to_list es1) (DList.to_list es2));;
  ret (x1, x2).

(* Mapping from size variables to indices of locals of type i32 *)
Definition size_ctx := list W.immediate.

Definition if_gc_bit_set {A} {B}
  (tf : W.function_type)
  (gc_branch : wst B)
  (lin_branch : wst A)
: wst (A * B) :=
  emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 1%Z)));;
  emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_and));;
  emit (W.BI_testop W.T_i32 W.TO_eqz);;
  if_c tf lin_branch gc_branch.

Definition unset_gc_bit : wst unit :=
  emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 1%Z)));;
  emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_sub)).

Fixpoint loads'
  (mem: W.immediate)
  (base_ptr_var: W.immediate)
  (off: W.static_offset)
  (tys: list W.value_type)
: wst unit :=
  match tys with
  | [] => ret tt
  | ty :: tys =>
      emit (W.BI_get_local base_ptr_var);;
      emit (W.BI_load mem ty None 0%N off);;
      loads' base_ptr_var mem (off + N.of_nat (W.length_t ty))%N tys
  end.

Definition loads mem base_ptr_var tys : wst unit :=
  loads' mem base_ptr_var 0%N tys.

Fixpoint loc_stores'
  (base_ptr_var: W.immediate)
  (mem: W.immediate)
  (off: W.static_offset)
  (val_var_tys: list (W.immediate * W.value_type))
: wst unit :=
  match val_var_tys with
  | [] => ret tt
  | (val_var, ty) :: val_var_tys =>
      emit (W.BI_get_local base_ptr_var);;
      emit (W.BI_get_local val_var);;
      emit (W.BI_store mem ty None 0%N off);;
      loc_stores' base_ptr_var mem (off + N.of_nat (W.length_t ty))%N val_var_tys
  end.

Definition loc_stores base_ptr_var mem val_var_tys : wst unit :=
  loc_stores' base_ptr_var mem 0%N val_var_tys.

Definition stores base_ptr_var mem (val_vars: list W.immediate) (tys: list W.value_type)
  : wst unit :=
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

Definition for_gc_ref_vars (scope : VarScope) (vars : list W.immediate) (m : wst unit) : wst unit :=
  iterM
    (fun var =>
       let '(get, set) := scope_get_set scope in
       emit (get var);;
       if_gc_bit_set (W.Tf [W.T_i32] [W.T_i32]) m (ret tt);;
       emit (set var))
    vars.

Fixpoint global_layout (globs : list R.GlobalType) (idx : nat) : option (nat * R.Typ) :=
  match globs, idx with
  | [R.GT _ ty], 0 => Some (0, ty)
  | R.GT _ ty :: globs', S idx' => global_layout globs' (length (compile_typ ty) + idx')
  | _, _ => None
  end.

Section Functions.

  (* TODO: should these be combined? *)
  Variable mctx : compiler_mod_ctx.
  Variable C : R.Module_Ctx.
  Variable sz_locs: size_ctx.
  Variable F : R.Function_Ctx.
  Variable temps_off : nat.

  Definition wnext : wst W.immediate :=
    temps <- get;;
    ret (temps_off + length temps).

  Definition walloc (t: W.value_type) : wst W.immediate :=
    temps <- get;;
    put (temps ++ [t]);;
    ret (temps_off + length temps).

  Definition wallocs (tys: list W.value_type) : wst (list W.immediate) :=
    mapT walloc tys.

  Definition walloc_args (tys: list W.value_type) : wst (list W.immediate) :=
    vars <- wallocs tys;;
    @forT list _ _ _ _ _ vars (fun var => emit (W.BI_set_local var));;
    ret vars.

  Definition walloc_rvalue (ty : R.Typ) : wst W.immediate :=
    i <- wnext;;
    forT (compile_typ ty) walloc;;
    ret i.

  Definition walloc_rvalues (tys : list R.Typ) : wst W.immediate :=
    i <- wnext;;
    forT tys walloc_rvalue;;
    ret i.

  Definition tagged_store
    (base_ptr: W.immediate)
    (arg_vars: list W.immediate)
    (get_offset: wst unit)
    (ty: R.Typ)
    : wst unit :=
    emit (W.BI_tee_local base_ptr);;
    emit (W.BI_get_local base_ptr);;
    let tys := compile_typ ty in
    if_gc_bit_set (W.Tf [] [])
      (emit (W.BI_get_local base_ptr);;
       unset_gc_bit;;
       get_offset;;
       emit (W.BI_set_local base_ptr);;
       stores base_ptr mctx.(mem_gc) arg_vars tys)
      (emit (W.BI_get_local base_ptr);;
       get_offset;;
       stores base_ptr mctx.(mem_lin) arg_vars tys);;
    ret tt.

  Definition local_layout (L : R.Local_Ctx) (idx : nat) : error + (nat * R.Typ) :=
    let fix go L base i :=
      match L, i with
      | (τ, sz) :: L, 0 => inr (base, τ)
      | (τ, sz) :: L, S i =>
          sz_const <- size_upper_bound F.(R.size) sz;;
          go L (base + sz_const) i
      | [], _ => inl (ELocalIndexOutOfBounds idx)
      end
    in
    go L 0 idx.

  Definition gc_loads
    (ref_var: W.immediate)
    (get_offset: wst unit)
    (tys: list W.value_type)
  : wst unit :=
    base_ptr_var <- walloc W.T_i32;;
    emit (W.BI_get_local ref_var);;
    unset_gc_bit;;
    get_offset;;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add));;
    emit (W.BI_set_local base_ptr_var);;
    loads mctx.(mem_gc) base_ptr_var tys.

  Definition lin_loads
    (ref_var: W.immediate)
    (get_offset: wst unit)
    (tys: list W.value_type)
  : wst unit :=
    base_ptr_var <- walloc W.T_i32;;
    emit (W.BI_get_local ref_var);;
    get_offset;;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add));;
    emit (W.BI_set_local base_ptr_var);;
    loads mctx.(mem_lin) base_ptr_var tys.

  Definition tagged_loads
    (base_ptr: W.immediate)
    (get_offset: wst unit)
    (tys: list W.value_type)
    : wst unit :=
    emit (W.BI_get_local base_ptr);;
    if_gc_bit_set (W.Tf [] tys)
      (gc_loads base_ptr get_offset tys)
      (lin_loads base_ptr get_offset tys);;
    ret tt.

  Definition tagged_load
    (base_ptr: W.immediate)
    (get_offset: wst unit)
    (ty: R.Typ)
  : wst unit :=
    let tys := compile_typ ty in
    tagged_loads base_ptr get_offset tys.

  Definition tagged_store' (get_offset : wst unit) (ty : R.Typ) : wst unit :=
    let tys := compile_typ ty in
    arg_vars <- walloc_args tys;;
    base_ptr_var <- walloc W.T_i32;;
    tagged_store base_ptr_var arg_vars get_offset ty.

  Definition get_i64_local (loc : W.immediate) : wst unit :=
    emit (W.BI_get_local loc);;
    emit (W.BI_cvtop W.T_i32 W.CVO_reinterpret W.T_i64 None);;
    emit (W.BI_get_local (loc + 1));;
    emit (W.BI_const (W.VAL_int64 (Wasm_int.int_of_Z i64m 32)));;
    emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_rotl));;
    emit (W.BI_cvtop W.T_i32 W.CVO_reinterpret W.T_i64 None);;
    emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_or)).

  Definition set_i64_local (loc : W.immediate) : wst unit :=
    tmp <- walloc W.T_i64;;
    emit (W.BI_tee_local tmp);;
    emit (W.BI_const (W.VAL_int64 (wasm_extend_u int32_minus_one)));;
    emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_and));;
    emit (W.BI_cvtop W.T_i64 W.CVO_convert W.T_i32 None);;
    emit (W.BI_set_local loc);;
    emit (W.BI_get_local tmp);;
    emit (W.BI_const (W.VAL_int64 (Wasm_int.int_of_Z i64m 32)));;
    emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_rotr));;
    emit (W.BI_set_local (loc + 1)).

  Definition numtyp_gets (nτ: R.NumType) (loc: nat) : wst unit :=
    match nτ with
    | R.Int s R.i32 => emit (W.BI_get_local loc)
    | R.Float R.f32 =>
        emit (W.BI_get_local loc);;
        emit (W.BI_cvtop W.T_i32 W.CVO_reinterpret W.T_f32 None)
    | R.Int s R.i64 => get_i64_local loc
    | R.Float R.f64 =>
        get_i64_local loc;;
        emit (W.BI_cvtop W.T_i64 W.CVO_reinterpret W.T_f64 None)
    end.

  Definition numtyp_sets (nτ: R.NumType) (loc: nat) : wst unit :=
    match nτ with
    | R.Int s R.i32 => emit (W.BI_set_local loc)
    | R.Float R.f32 =>
        emit (W.BI_cvtop W.T_f32 W.CVO_reinterpret W.T_i32 None);;
        emit (W.BI_set_local loc)
    | R.Int s R.i64 => set_i64_local loc
    | R.Float R.f64 =>
        emit (W.BI_cvtop W.T_f64 W.CVO_reinterpret W.T_i64 None);;
        set_i64_local loc
    end.

  Fixpoint local_gets (τ: R.Typ) (loc: nat) : wst unit :=
    match τ with
    | R.Num nτ => numtyp_gets nτ loc
    | R.TVar α => emit (W.BI_get_local loc)
    | R.Unit => ret tt
    | R.ProdT τs =>
        let fix loop τs0 sz :=
          match τs0 with
          | τ0 :: τs0' =>
              let sz := words_typ τ0 in
              local_gets τ0 loc;;
              loop τs0' (loc + sz)
          | [] => ret tt
          end in
        loop τs loc
    | R.CoderefT χ => emit (W.BI_get_local loc)
    | R.Rec q τ => local_gets τ loc
    | R.PtrT ℓ => emit (W.BI_get_local loc)
    | R.ExLoc q τ => local_gets τ loc
    | R.OwnR ℓ => ret tt
    | R.CapT cap ℓ ψ => ret tt
    | R.RefT cap ℓ ψ => emit (W.BI_get_local loc)
    end.

  Fixpoint local_sets (τ: R.Typ) (loc: nat) : wst unit :=
    match τ with
    | R.Num nτ =>
        numtyp_sets nτ loc
    | R.TVar α =>
        emit (W.BI_set_local loc)
    | R.Unit =>
        ret tt
    | R.ProdT τs =>
        let fix loop τs0 sz :=
          match τs0 with
          | τ0 :: τs0' =>
              let sz := words_typ τ0 in
              local_sets τ0 loc;;
              loop τs0' (loc + sz)
          | [] => ret tt
          end in
        loop τs loc
    | R.CoderefT χ =>
        emit (W.BI_set_local loc)
    | R.Rec q τ =>
        local_sets τ loc
    | R.PtrT ℓ =>
        emit (W.BI_set_local loc)
    | R.ExLoc q τ =>
        local_sets τ loc
    | R.OwnR ℓ =>
        ret tt
    | R.CapT cap ℓ ψ =>
        ret tt
    | R.RefT cap ℓ ψ =>
        emit (W.BI_set_local loc)
    end.

  Definition save_stack (tys : list R.Typ) : wst W.immediate :=
    idx <- walloc_rvalues tys;;
    local_sets (R.ProdT tys) idx;;
    ret idx.

  Definition restore_stack (tys : list R.Typ) (idx : W.immediate) : wst unit :=
    local_gets (R.ProdT tys) idx.

  Fixpoint compile_sz (sz : R.Size) : wst unit :=
    match sz with
    | R.SizeVar σ =>
      local_idx <- try_option (ESizeIndexOutOfBounds σ) (lookup σ sz_locs);;
      emit (W.BI_get_local local_idx)
    | R.SizePlus sz1 sz2 =>
      compile_sz sz1;;
      compile_sz sz2;;
      emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add))
    | R.SizeConst c =>
      emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat c))))
    end.

  Definition compile_ind (ind: R.Index) : wst unit :=
    match ind with
    | R.SizeI sz => compile_sz sz
    | R.LocI _
    | R.QualI _
    | R.TypI _ => ret tt
    end.

  Definition array_bounds_check (base idx : W.immediate) : wst unit :=
    tagged_load
      base
      (emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat 0)))))
      (R.Num (R.Int R.U R.i32));;
    emit (W.BI_get_local idx);;
    emit (W.BI_relop W.T_i32 (W.Relop_i (W.ROI_lt (W.SX_U)))).

  Definition array_offset (idx : W.immediate) (size : nat) : wst unit :=
    emit (W.BI_get_local idx);;
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat size))));;
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_mul));;
    emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat 4))));; (* skip header length word *)
    emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add)).

  Fixpoint compile_instr (instr: R.instr R.TyAnn) : wst unit :=
    match instr with
    | R.INumConst _ num_type num => emit (W.BI_const (compile_num num_type num))
    | R.IUnit _ => ret tt
    | R.INum ann ni => emit (compile_num_instr ni)
    | R.IUnreachable (R.Arrow targs trets, _) => emit (W.BI_unreachable)
    | R.INop (R.Arrow targs trets, _) => emit (W.BI_nop)
    | R.IDrop (R.Arrow targs trets, R.LSig L _) =>
        match targs with
        | [t_drop] =>
            let wasm_typ := compile_typ t_drop in
            base <- save_stack [t_drop];;
            let ref_vars := map (Nat.add base) (ref_indices LMNative t_drop) in
            for_gc_ref_vars VSLocal ref_vars (emit (W.BI_call mctx.(unregisterroot)));;
            restore_stack [t_drop] base;;
            forT wasm_typ (const (emit W.BI_drop));;
            ret tt
        | _ => raise EWrongTypeAnn
        end
    | R.IBlock (R.Arrow targs trets, _) ta _ es =>
        block_c (compile_arrow_type ta) (forT es compile_instr);;
        ret tt
    | R.ILoop (R.Arrow targs trets, _) arrow es =>
        loop_c (compile_arrow_type arrow) (forT es compile_instr);;
        ret tt
    | R.IIte (R.Arrow targs trets, _) arrow _ ets efs =>
        let tf := compile_arrow_type arrow in
        if_c tf (forT ets compile_instr) (forT efs compile_instr);;
        ret tt
    | R.IBr (R.Arrow targs trets, _) x => emit (W.BI_br x)
    | R.IBrIf (R.Arrow targs trets, _) x => emit (W.BI_br_if x)
    | R.IBrTable (R.Arrow targs trets, _) x x0 => emit (W.BI_br_table x x0)
    | R.IRet (R.Arrow targs trets, _) =>
        let ret_ty' := ssrfun.Option.default [] F.(R.rettyp) in
        let rdropped := take (length targs - length ret_ty') targs in
        let wdropped := flat_map compile_typ rdropped in
        idx_ret <- save_stack ret_ty';;
        idx_dropped <- save_stack rdropped;;
        let ref_vars := map (Nat.add idx_dropped) (flat_map (ref_indices LMNative) rdropped) in
        for_gc_ref_vars VSLocal ref_vars (emit (W.BI_call mctx.(unregisterroot)));;
        restore_stack ret_ty' idx_ret;;
        emit W.BI_return
    | R.IGetLocal (R.Arrow targs trets, R.LSig L _) idx _ =>
        '(base, τ) <- lift_error (local_layout L idx);;
        local_gets τ base;;
        'i <- save_stack [τ];;
        let ref_vars := map (Nat.add i) (ref_indices LMNative τ) in
        for_gc_ref_vars VSLocal ref_vars (emit (W.BI_call mctx.(duproot)));;
        restore_stack [τ] i
    | R.ISetLocal (R.Arrow targs trets, R.LSig L _) idx =>
        '(base, τ) <- lift_error (local_layout L idx);;
        let ref_vars := map (Nat.add base) (ref_indices LMWords τ) in
        for_gc_ref_vars VSLocal ref_vars (emit (W.BI_call mctx.(unregisterroot)));;
        local_sets τ base
    | R.IGetGlobal _ i =>
        '(i', ty) <- try_option (EGlobalIndexOutOfBounds i) (global_layout C.(R.global) i);;
        forT (imap (fun j _ => i' + j) (compile_typ ty)) (emit ∘ W.BI_get_global);;
        j <- save_stack [ty];;
        let ref_vars := map (Nat.add j) (ref_indices LMNative ty) in
        for_gc_ref_vars VSLocal ref_vars (emit (W.BI_call mctx.(duproot)));;
        restore_stack [ty] i
    | R.ISetGlobal _ i =>
        '(i', ty) <- try_option (EGlobalIndexOutOfBounds i) (global_layout C.(R.global) i);;
        let ref_vars := map (Nat.add i') (ref_indices LMNative ty) in
        for_gc_ref_vars VSGlobal ref_vars (emit (W.BI_call mctx.(unregisterroot)));;
        forT (imap (fun j _ => i' + j) (compile_typ ty)) (emit ∘ W.BI_set_global);;
        ret tt
    | R.ICoderef (R.Arrow targs trets, _) idx =>
        emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat idx))));;
        emit (W.BI_get_global mctx.(coderef_offset));;
        emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add))
    | R.ICallIndirect (R.Arrow targs trets, _) inds =>
        stk <- save_stack targs;;
        forT inds compile_ind;;
        restore_stack targs stk;;
        emit (W.BI_call_indirect mctx.(fn_tab))
    | R.ICall (R.Arrow targs trets, _) fidx inds =>
        stk <- save_stack targs;;
        forT inds compile_ind;;
        restore_stack targs stk;;
        emit (W.BI_call fidx)
    | R.IMemUnpack _ ta tl es =>
        block_c (compile_arrow_type ta) (forT es compile_instr);;
        ret tt
    | R.IStructMalloc (R.Arrow targs trets, _) szs q =>
        (* TODO: registerroot on the new address;
                 unregisterroot if any field is GC ref being put into GC struct *)
        (* compute size for malloc *)
        (* call malloc and save result *)
        (* load args into locals *)
        (* do an IStructSet on each arg *)
        (* return the base pointer *)
        raise ETodo
    | R.IStructFree (R.Arrow targs trets, _) =>
        (* TODO: unregisterroot fields that may be refs to GC if this struct is MM *)
        emit (W.BI_call mctx.(free))
    | R.IStructGet (R.Arrow from to, _) n =>
        base_ref <- walloc W.T_i32;;
        fields <- lift_error (get_struct_field_types from 0);;
        field_typ <- try_option EWrongTypeAnn (lookup 0 to);;
        offset_sz <- lift_error (struct_field_offset fields n);;
        emit (W.BI_tee_local base_ref);;
        tagged_load base_ref (compile_sz offset_sz) field_typ;;
        stk <- save_stack [field_typ];;
        emit (W.BI_get_local base_ref);;
        let ref_vars := map (Nat.add stk) (ref_indices LMNative field_typ) in
        if_gc_bit_set (W.Tf [] [])
          (for_gc_ref_vars VSLocal ref_vars (emit (W.BI_call mctx.(registerroot))))
          (for_gc_ref_vars VSLocal ref_vars (emit (W.BI_call mctx.(duproot))));;
        restore_stack [field_typ] stk
    | R.IStructSet (R.Arrow from to, _) n =>
        base_ref <- walloc W.T_i32;;
        fields <- lift_error (get_struct_field_types from 1);;
        field_typ <- try_option EWrongTypeAnn (lookup 0 to);;
        val_typ <- try_option EWrongTypeAnn (lookup 0 from);;
        offset_sz <- lift_error (struct_field_offset fields n);;

        emit (W.BI_tee_local base_ref);;
        if_gc_bit_set (W.Tf [] [])
          (ret tt)
          (let tys := compile_typ field_typ in
           gc_loads base_ref (compile_sz offset_sz) tys;;
           old_stk_var <- save_stack [field_typ];;
           let old_ref_vars := map (Nat.add old_stk_var) (ref_indices LMNative field_typ) in
           for_gc_ref_vars VSLocal old_ref_vars
             (emit (W.BI_call mctx.(unregisterroot))));;

        emit (W.BI_get_local base_ref);;
        if_gc_bit_set (W.Tf [] [])
          (new_stk_var <- save_stack [val_typ];;
           let new_ref_vars := map (Nat.add new_stk_var) (ref_indices LMNative val_typ) in
           for_gc_ref_vars VSLocal new_ref_vars
             (emit (W.BI_load mctx.(mem_gc) W.T_i32 None 0%N 0%N));;
           restore_stack [val_typ] new_stk_var)
          (ret tt);;

        emit (W.BI_get_local base_ref);;
        tagged_store' (compile_sz offset_sz) val_typ
    | R.IStructSwap (R.Arrow from to, _) n =>
        (* TODO: registerroot if GC struct *)
        raise ETodo
    | R.IVariantMalloc (R.Arrow from to, _) sz tys q =>
        (* TODO: registerroot on the new address;
                 unregisterroot if payload is GC ref being put into GC variant *)
        typ <- try_option EWrongTypeAnn (lookup 0 from);;
        let shape := compile_typ typ in
        (* memory layout is [ind, τ*] so we just add prepend *)
        (*let full_shape := LS_tuple [LS_int32; shape] in*)
        raise ETodo (*
        mret $ [
          layout.Val $ LV_int32 (shape_size_words full_shape);
          layout.Malloc;                                       (* [i32] → [ptr] *)
          layout.Val $ LV_int32 (shape_size_words full_shape); (* [] → [offset__end] *)
          layout.Pluck 3;          (* [val; ptr; offset] → [ptr; offset; val] *)
          layout.StoreOffset;      (* [ptr; offset; val] → [ptr; offset] *)
          layout.Val $ LV_int32 i; (* [] → [val] *)
          layout.StoreOffset;      (* [ptr; offset; val] → [ptr; offset] *)
          layout.Drop]             (* [ptr; offset] → [ptr] *)
      *)
    | R.IVariantCase ann q th ta tl es =>
        (* TODO: duproot if unrestricted *)
        raise ETodo
        (* [val__init; len] → [ptr] *)
        (* [τ      ; i32] → [i32] *)
    | R.IArrayMalloc (R.Arrow from to, _) q =>
        (* TODO: unregisterroot the initial value if GC array;
                 duproot a bunch of times if MM array *)
        arr_init_typ <- try_option EWrongTypeAnn (list_lookup 1 from);;
        let shape := compile_typ arr_init_typ in
        raise ETodo
               (*
        mret [
          layout.Dup;             (* [len] → [len; len] *)
          layout.Val $ LV_int32 (shape_size_words shape);
          layout.Ne $ rwasm.Ib rwasm.i32 rwasm.mul; (* [len; i32] → [size] *)
          layout.Malloc;                            (* [size] → [ptr] *)
          layout.RepeatInit shape]                  (* [val; len; ptr] → [ptr] *)
  *)
      (* [ptr; idx] → [ptr; val] *)
      (* [i32; i32] → [i32; τ  ] *)
    | R.IArrayGet (R.Arrow from to, _) =>
        (* TODO: registerroot if GC array;
                 duproot if MM array *)
        (*  ex: i64[i]
          | idx | offset |
          |-----|--------|
          | 0   | 0      |
          | 1   | 1 * 2  |
          ...
          | i   | i * 2  | *)
        elem_typ <- lift_error (get_array_elem_type from 1);;
        let elem_shape := compile_typ elem_typ in
        idx_local <- walloc W.T_i32;;
        base_local <- walloc W.T_i32;;
        let words := words_typ elem_typ in
        emit (W.BI_set_local idx_local);;
        emit (W.BI_set_local base_local);;
        tagged_load
          base_local
          (emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m 0))))
          (R.Num (R.Int R.U R.i32));;
        emit (W.BI_get_local idx_local);;
        emit (W.BI_relop W.T_i32 (W.Relop_i (W.ROI_lt (W.SX_U))));;
        let get_offset :=
          emit (W.BI_get_local idx_local);;
          emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat words))));;
          emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_mul));;
          emit (W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m 4)));; (* skip header length word *)
          emit (W.BI_binop W.T_i32 (W.Binop_i W.BOI_add))
        in
        if_c (W.Tf [] elem_shape)
          (tagged_load base_local get_offset elem_typ)
          (emit W.BI_unreachable);;
        ret tt
    | R.IArraySet (R.Arrow from to, _) =>
        (* TODO: unregisterroot if GC array;
                 duproot a bunch of times if MM array *)
        (*  ex: [i]
           | idx | offset      |
           |-----|-------------|
           | 0   | 2           |
           | 1   | 2 * 2       |
           ...
           | i   | (i + 1) * 2 | *)
        elem_typ <- lift_error (get_array_elem_type from 2);;
        let elem_shape := compile_typ elem_typ in
        idx_local <- walloc W.T_i32;;
        base_local <- walloc W.T_i32;;
        val_save_idx <- save_stack [elem_typ];;
        emit (W.BI_set_local idx_local);;
        emit (W.BI_tee_local base_local);;
        array_bounds_check base_local idx_local;;
        if_c (W.Tf [] [])
          (emit (W.BI_get_local base_local);;
           let words := words_typ elem_typ in
           let compute_offset := array_offset idx_local words in
           tagged_store' compute_offset elem_typ)
          (emit W.BI_unreachable);;
        ret tt
    | R.IArrayFree ann =>
        (* TODO: unregisterroot a bunch of times, since this is an MM array *)
        raise ETodo (*mret $ [wasm.BI_call Σ.(me_free)]*)
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

    Definition compile_instrs : list (R.instr R.TyAnn) -> wst unit :=
      iterM compile_instr.

End Functions.
