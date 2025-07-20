From Coq Require Import List.
Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Import Coq.Lists.List.ListNotations.
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinInt.
Local Open Scope program_scope.

Require Import mathcomp.ssreflect.seq.

From stdpp Require Import -(notations) list_numbers pretty.

From ExtLib.Structures Require Import Functor Monads Reducible Traversable.
Import FunctorNotation.
Import MonadNotation.
Local Open Scope monad.
From ExtLib.Data Require Import List.
From ExtLib.Data.Monads Require Import EitherMonad StateMonad WriterMonad.

From Wasm Require datatypes operations.
Require Import Wasm.numerics.

From RichWasm Require term.
From RichWasm Require Import typing.
Require Import RichWasm.util.dlist.
Import RichWasm.util.dlist.Notation.
From RichWasm.compiler Require Import numerics util.

Module R := term.
Module W := datatypes.

(* Mapping from size variables to indices of locals of type i32 *)
Definition size_ctx := list W.immediate.

(* locals exclusive to webassembly (compiler-generated temporaries, etc) *)
Definition wlocal_ctx := list W.value_type.

Notation instr_list := (dlist W.basic_instruction).

Record wst (A : Type) :=
  { un_wst : stateT wlocal_ctx (writerT (@DList.Monoid_dlist W.basic_instruction) (sum err)) A }.

Arguments Build_wst {A} _.
Arguments un_wst {A} _.

Existing Instance Monad_stateT.

Global Instance Monad_wst : Monad wst :=
  { ret := fun _ x => Build_wst (ret x);
    bind := fun _ _ c f => Build_wst (bind (un_wst c) (fun x => un_wst (f x))) }.

Global Instance MonadExc_wst : MonadExc err wst :=
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

Definition lift_err {A} (c : err + A) : wst A :=
  Build_wst (lift (lift c)).

Definition run_compiler (c : wst unit) (wl : wlocal_ctx) : err + wlocal_ctx * list W.basic_instruction :=
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

Record compiler_mod_ctx := {
  mem_gc : W.immediate;
  mem_lin : W.immediate;
  free : W.immediate;
  alloc : W.immediate;
  registerroot : W.immediate;
  unregisterroot : W.immediate;
  duproot : W.immediate;
  coderef_offset : W.immediate;
  fn_tab : W.immediate;
}.

Definition compile_int_type (typ : R.IntType) : W.value_type :=
  match typ with
  | R.i32 => W.T_i32
  | R.i64 => W.T_i64
  end.

Definition compile_float_type (typ : R.FloatType) : W.value_type :=
  match typ with
  | R.f32 => W.T_f32
  | R.f64 => W.T_f64
  end.

Definition compile_numtyp (typ: R.NumType) : W.value_type :=
  match typ with
  | R.Int _ inttyp => compile_int_type inttyp
  | R.Float floattyp => compile_float_type floattyp
  end.

Definition compile_kindvar (κ: R.KindVar) : list W.value_type :=
  match κ with
  | R.SIZE _ _ => [W.T_i32]
  | _ => []
  end.

Definition compile_kindvars (κs: list R.KindVar) : list W.value_type :=
  flat_map compile_kindvar κs.

Fixpoint compile_typ (typ: R.Typ) : list W.value_type :=
  match typ with
  | R.Num ntyp => [compile_numtyp ntyp]
  | R.TVar _ => [W.T_i32]
  | R.Unit => []
  | R.ProdT typs => flatten (map compile_typ typs)
  | R.CoderefT _ => [W.T_i32]
  | R.Rec _ typ => compile_typ typ
  | R.PtrT _ => [W.T_i32]
  | R.ExLoc q typ => compile_typ typ
  | R.OwnR _ => []
  | R.CapT _ _ _ => []
  | R.RefT _ _ _  => [W.T_i32]
  end.

Definition compile_arrow_type (typ: R.ArrowType) : W.function_type :=
  match typ with
  | R.Arrow tys1 tys2 =>
    let tys1' := mapT compile_typ tys1 in
    let tys2' := mapT compile_typ tys2 in
    W.Tf (flatten tys1') (flatten tys2')
  end.

Definition compile_fun_type (ft: R.FunType) : W.function_type :=
  match ft with
  | R.FunT κs (R.Arrow tys1 tys2) =>
    let κvs := compile_kindvars κs in
    let tys1' := flatten (mapT compile_typ tys1) in
    let tys2' := flatten (mapT compile_typ tys2) in
    W.Tf (κvs ++ tys1') tys2'
  end.

Definition words_typ (typ: R.Typ) : nat :=
  sum_list_with operations.words_t (compile_typ typ).

Definition throw_missing (instr_name : string) : err + W.basic_instruction :=
  inl (Err ("missing iris-wasm " ++ instr_name ++ " wrap instruction")).

Definition compile_num (num_type : R.NumType) (num : nat) : W.value :=
  match num_type with
  | R.Int _ R.i32 =>
    W.VAL_int32 (Wasm_int.int_of_Z numerics.i32m (Z.of_nat num))
  | R.Int _ R.i64 =>
    W.VAL_int64 (Wasm_int.int_of_Z numerics.i64m (Z.of_nat num))
  (* is the signed converter the right thing to use here? *)
  | R.Float R.f32 =>
    W.VAL_float32
      (Wasm_float.float_convert_si32
         numerics.f32m (Wasm_int.int_of_Z numerics.i32m (Z.of_nat num)))
  | R.Float R.f64 =>
    W.VAL_float64
      (Wasm_float.float_convert_si64
         numerics.f64m (Wasm_int.int_of_Z numerics.i64m (Z.of_nat num)))
  end.

Fixpoint expect_concrete_size (sz: R.Size) : err + nat :=
  match sz with
  | R.SizeConst c => inr c
  | R.SizePlus sz1 sz2 =>
      c1 <- expect_concrete_size sz1;;
      c2 <- expect_concrete_size sz2;;
      inr (c1 + c2)
  | _ => inl (Err "expected concrete size")
  end.

Fixpoint struct_field_offset (fields: list (R.Typ * R.Size)) (idx: nat) : err + R.Size :=
  match idx with
  | 0 => inr (R.SizeConst 0)
  | S idx' =>
      match fields with
      | (_, sz) :: fields' => R.SizePlus sz <$> struct_field_offset fields' idx'
      | [] => inl Todo
      end
  end.

Definition get_struct_field_types (targs : list R.Typ) (idx : nat) : err + list (R.Typ * R.Size) :=
  match lookup idx targs with
  | Some (R.RefT _ _ (R.StructType fields)) => inr fields
  | _ => inl (Err ("struct instruction expected type-args to be a ref to a struct at index " ++ pretty idx))
  end.

Definition get_array_elem_type (targs : list R.Typ) (idx : nat) : err + R.Typ :=
  match lookup idx targs with
  | Some (R.RefT _ _ (R.ArrayType typ)) => inr typ
  | _ => inl (Err ("array instruction expected a ref to an array type at index " ++ pretty idx))
  end.

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
      loads' base_ptr_var mem (off + N.of_nat (operations.length_t ty))%N tys
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
      loc_stores' base_ptr_var mem (off + N.of_nat (operations.length_t ty))%N val_var_tys
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

Inductive LayoutMode :=
  | LMWords
  | LMNative.

Definition layout_ty_length (layout : LayoutMode) (ty : R.Typ) :=
  match layout with
  | LMWords => words_typ ty
  | LMNative => length (compile_typ ty)
  end.

Definition ref_indices (layout : LayoutMode) (ty : R.Typ) : list W.immediate :=
  let fix go ty i :=
    match ty with
    | R.Num _
    | R.Unit
    | R.CoderefT _
    | R.PtrT _
    | R.OwnR _
    | R.CapT _ _ _ => []
    | R.ProdT tys =>
        snd (foldl (fun '(j, is) ty' => (j + layout_ty_length layout ty', is ++ go ty' j))
                   (i, [])
                   tys)
    | R.Rec _ ty'
    | R.ExLoc _ ty' => go ty' i
    | R.TVar _
    | R.RefT _ _ _ => [i]
    end in
  go ty 0.

Definition for_gc_ref_vars (scope : VarScope) (vars : list W.immediate) (m : wst unit) : wst unit :=
  iterM
    (fun var =>
       let '(get, set) := scope_get_set scope in
       emit (get var);;
       if_gc_bit_set (W.Tf [W.T_i32] [W.T_i32]) m (ret tt);;
       emit (set var))
    vars.

Section Mod.

  (* TODO: should these be combined? *)
  Variable mctx : compiler_mod_ctx.
  Variable C : Module_Ctx.

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

  Fixpoint global_layout (globs : list R.GlobalType) (idx : nat) : option (nat * R.Typ) :=
    match globs, idx with
    | [R.GT _ ty], 0 => Some (0, ty)
    | R.GT _ ty :: globs', S idx' => global_layout globs' (length (compile_typ ty) + idx')
    | _, _ => None
    end.

  Section Fun.

    Variable (sz_locs: size_ctx).
    Variable (F : Function_Ctx).
    Variable (temps_off : nat).

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

    Fixpoint local_layout (L: Local_Ctx) (base: nat) (i: nat) : err + (nat * R.Typ) :=
      match L, i with
      | (τ, sz) :: L, 0 => inr (base, τ)
      | (τ, sz) :: L, S i =>
          sz_const <- expect_concrete_size sz;;
          local_layout L (base + sz_const) i
      | [], _ => inl (Err "local_layout given out of bounds index")
      end.

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
        local_idx <- lift_err (err_opt (lookup σ sz_locs)
                                       ("sz " ++ pretty σ ++ " not found in sz_local_map"));;
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

    Fixpoint compile_instr (instr: R.instr TyAnn) : wst unit :=
      match instr with
      | R.INumConst _ num_type num => emit (W.BI_const (compile_num num_type num))
      | R.IUnit _ => ret tt
      | R.INum ann ni => lift_err (compile_num_instr ni) >>= emit
      | R.IUnreachable (R.Arrow targs trets, _) => emit (W.BI_unreachable)
      | R.INop (R.Arrow targs trets, _) => emit (W.BI_nop)
      | R.IDrop (R.Arrow targs trets, LSig L _) =>
          match targs with
          | [t_drop] =>
              let wasm_typ := compile_typ t_drop in
              base <- save_stack [t_drop];;
              let ref_vars := map (Nat.add base) (ref_indices LMNative t_drop) in
              for_gc_ref_vars VSLocal ref_vars (emit (W.BI_call mctx.(unregisterroot)));;
              restore_stack [t_drop] base;;
              forT wasm_typ (const (emit W.BI_drop));;
              ret tt
          | _ => raise (Err "drop should consume exactly one value")
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
          let ret_ty' := ssrfun.Option.default [] F.(rettyp) in
          let rdropped := take (length targs - length ret_ty') targs in
          let wdropped := flat_map compile_typ rdropped in
          idx_ret <- save_stack ret_ty';;
          idx_dropped <- save_stack rdropped;;
          let ref_vars := map (Nat.add idx_dropped) (flat_map (ref_indices LMNative) rdropped) in
          for_gc_ref_vars VSLocal ref_vars (emit (W.BI_call mctx.(unregisterroot)));;
          restore_stack ret_ty' idx_ret;;
          emit W.BI_return
      | R.IGetLocal (R.Arrow targs trets, LSig L _) idx _ =>
          '(base, τ) <- lift_err (local_layout L 0 idx);;
          local_gets τ base;;
          'i <- save_stack [τ];;
          let ref_vars := map (Nat.add i) (ref_indices LMNative τ) in
          for_gc_ref_vars VSLocal ref_vars (emit (W.BI_call mctx.(duproot)));;
          restore_stack [τ] i
      | R.ISetLocal (R.Arrow targs trets, LSig L _) idx =>
          '(base, τ) <- lift_err (local_layout L 0 idx);;
          let ref_vars := map (Nat.add base) (ref_indices LMWords τ) in
          for_gc_ref_vars VSLocal ref_vars (emit (W.BI_call mctx.(unregisterroot)));;
          local_sets τ base
      | R.IGetGlobal _ i =>
          '(i', ty) <- lift_err (err_opt (global_layout C.(global) i) "invalid global index");;
          forT (imap (fun j _ => i' + j) (compile_typ ty)) (emit ∘ W.BI_get_global);;
          j <- save_stack [ty];;
          let ref_vars := map (Nat.add j) (ref_indices LMNative ty) in
          for_gc_ref_vars VSLocal ref_vars (emit (W.BI_call mctx.(duproot)));;
          restore_stack [ty] i
      | R.ISetGlobal _ i =>
          '(i', ty) <- lift_err (err_opt (global_layout C.(global) i) "invalid global index");;
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
          raise Todo
      | R.IStructFree (R.Arrow targs trets, _) =>
          (* TODO: unregisterroot fields that may be refs to GC if this struct is MM *)
          emit (W.BI_call mctx.(free))
      | R.IStructGet (R.Arrow from to, _) n =>
          base_ref <- walloc W.T_i32;;
          fields <- lift_err (get_struct_field_types from 0);;
          field_typ <- lift_err (err_opt (list_lookup 0 to) "struct.get: cannot find output val type");;
          offset_sz <- lift_err (struct_field_offset fields n);;
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
          fields <- lift_err (get_struct_field_types from 1);;
          field_typ <- lift_err (err_opt (list_lookup 0 to) "struct.set: cannot find output val type");;
          val_typ <- lift_err (err_opt (list_lookup 0 from) "struct.set: cannot find input val type");;
          offset_sz <- lift_err (struct_field_offset fields n);;

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
          fields <- lift_err (get_struct_field_types from 1);;
          field_typ <- lift_err (err_opt (list_lookup 0 from) "struct.swap: cannot find input val type");;
          let field_shape := compile_typ field_typ in
          offset_sz <- lift_err (struct_field_offset fields n);;
          offset_e <- compile_sz offset_sz;;
          raise Todo
    (*
          mret $ [layout.Swap] ++                (* [ptr; val] → [val; ptr]*)
                 offset_e ++                     (* [] → [offset] *)
                 [layout.SwapOffset field_shape; (* [ptr; offset; val__new] → [ptr; offset; val__old] *)
                  layout.Swap;                   (* [offset; val] → [val; offset] *)
                  layout.Drop]                   (* [offset] → [] *)
    *)
      | R.IVariantMalloc (R.Arrow from to, _) sz tys q =>
          (* TODO: registerroot on the new address;
                   unregisterroot if payload is GC ref being put into GC variant *)
          typ <- lift_err (err_opt (list_lookup 0 from) "variant.malloc: cannot find val type");;
          let shape := compile_typ typ in
          (* memory layout is [ind, τ*] so we just add prepend *)
          (*let full_shape := LS_tuple [LS_int32; shape] in*)
          raise Todo (*
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
          raise Todo
          (* [val__init; len] → [ptr] *)
          (* [τ      ; i32] → [i32] *)
      | R.IArrayMalloc (R.Arrow from to, _) q =>
          (* TODO: unregisterroot the initial value if GC array;
                   duproot a bunch of times if MM array *)
          arr_init_typ <- lift_err (err_opt (list_lookup 1 from) "array.malloc: cannot find val type");;
          let shape := compile_typ arr_init_typ in
          raise Todo
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
          elem_typ <- lift_err (get_array_elem_type from 1);;
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
          elem_typ <- lift_err (get_array_elem_type from 2);;
          let elem_shape := compile_typ elem_typ in
          (*  ex: [i]
             | idx | offset      |
             |-----|-------------|
             | 0   | 2           |
             | 1   | 2 * 2       |
             ...
             | i   | (i + 1) * 2 | *)
          raise Todo
                 (*
          mret [
            layout.Val $ LV_int32 1;
            layout.Ne $ rwasm.Ib rwasm.i32 rwasm.add;
            layout.Val $ LV_int32 (shape_size_words elem_shape);
            layout.Ne $ rwasm.Ib rwasm.i32 rwasm.mul; (* [idx; sz] → [offset] *)
            layout.LoadOffset elem_shape; (* [ptr; offset] → [ptr; offset; val] *)
            layout.Swap;                  (* [offset; val] → [val; offset]*)
            layout.Drop]                  (* [offset]; → [] *)
    *)
        (* [ptr] → [] *)
        (* [i32] → [] *)
      | R.IArrayFree ann =>
          (* TODO: unregisterroot a bunch of times, since this is an MM array *)
          raise Todo (*mret $ [wasm.BI_call Σ.(me_free)]*)
      | R.IExistPack (R.Arrow targs trets, _) t th q =>
          (* TODO: unregisterroot if GC package *)
          raise Todo
      | R.IExistUnpack (R.Arrow targs trets, _) q th ta tl es =>
          (* TODO: registerroot if GC package *)
          raise Todo
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

      Definition compile_instrs : list (R.instr TyAnn) -> wst unit :=
        iterM compile_instr.

  End Fun.

End Mod.

Definition compile_fun_type_idx (fun_type : R.FunType) : W.typeidx.
Admitted.

Definition funcidx_table_write : W.immediate := 0.

Definition typeidx_start : W.immediate := 0.

Definition typeidx_table_write : W.immediate := 1.

Definition globidx_table_next : W.immediate := 0.

Definition globidx_table_offset : W.immediate := 1.

Definition compile_table_elem (start : W.immediate) (i funcidx : nat) : W.expr :=
  [ W.BI_get_local start;
    W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat i)));
    W.BI_binop W.T_i32 (W.Binop_i W.BOI_add);
    W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat funcidx)));
    W.BI_call funcidx_table_write ].

Definition compile_start (table : R.Table) : W.module_func :=
  {| W.modfunc_type := W.Mk_typeidx typeidx_start;
     W.modfunc_locals := [];
     W.modfunc_body :=
       [ (* Remember the starting index of our section in the table. *)
         W.BI_get_global globidx_table_next;
         W.BI_set_global globidx_table_offset;
         (* Increment the index for the next module to use the table. *)
         W.BI_get_global globidx_table_offset;
         W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (length table))));
         W.BI_binop W.T_i32 (W.Binop_i W.BOI_add);
         W.BI_set_global globidx_table_next ] ++
       flatten (imap (compile_table_elem 0) table) |}.

Fixpoint compile_module (module : R.module TyAnn) : err + W.module :=
  let '(funcs, globs, table) := module return err + W.module in
  let mctx := {|
    mem_gc := 0;
    mem_lin := 1;
    free := 1;
    alloc := 2;
    registerroot := 3;
    unregisterroot := 4;
    duproot := 5;
    coderef_offset := 0;
    fn_tab := 0;
  |} in
  inr {|
    W.mod_types := []; (* TODO *)
    W.mod_funcs := []; (* TODO *)
    W.mod_tables := []; (* TODO *)
    W.mod_mems := []; (* TODO *)
    W.mod_globals := (* TODO *)
      [ W.Build_module_glob
          (W.Build_global_type W.MUT_mut W.T_i32)
          [ W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m 0)) ] ];
    W.mod_elem := []; (* TODO *)
    W.mod_data := []; (* TODO *)
    W.mod_start := Some (W.Build_module_start (W.Mk_funcidx 0)); (* TODO *)
    W.mod_imports := (* TODO *)
      [ W.Build_module_import
          (String.list_byte_of_string "RichWasm")
          (String.list_byte_of_string "modify_table")
          (W.ID_func typeidx_table_write) ];
    W.mod_exports := [] (* TODO *)
  |}

(* TODO: modfunc_type expects a typeidx while rwasm does this inline *)
with compile_func (func : R.Func TyAnn) : option W.module_func :=
  match func with
  | R.Fun exports fun_type sizes intrs =>
    Some {|
      W.modfunc_type := compile_fun_type_idx fun_type;
      W.modfunc_locals := []; (* TODO *)
      W.modfunc_body := []; (* TODO *)
    |}
  end

with compile_glob (glob : R.Glob TyAnn) : err + W.module_glob
with compile_table (table : R.Table) : err + W.module_table.
Admitted.
