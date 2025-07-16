From Coq Require Import List.
Require Import mathcomp.ssreflect.seq.
From stdpp Require Import list list_numbers.
Require Import stdpp.base.
Require Import stdpp.strings.
Require Import stdpp.pretty.
Require Import stdpp.list_numbers.
Import ListNotations.
From RWasm Require term.
From RWasm Require Import typing.
From Wasm Require datatypes operations.
Require Import Wasm.numerics.
Require Import BinNat.
Require Import compiler.monads.
Require Import compiler.numbers.

Module R := term.
Module W := datatypes.
Require Import stdpp.list.

(* locals exclusive to webassembly (compiler-generated temporaries, etc) *)
Definition wlocal_ctx := seq.seq W.value_type.

Record wlayout :=
  { w_offset: nat;
    w_ctx: wlocal_ctx }.

Definition wextend (w: wlayout) (t: W.value_type) :=
  {| w_offset := w.(w_offset);
     w_ctx := w.(w_ctx) ++ [t]; |}.

Definition next_idx (w: wlayout) : W.immediate :=
  w.(w_offset) + length w.(w_ctx).

Definition wst (A: Type) : Type := stateT wlayout (exn err) A.

Definition walloc (t: W.value_type) : wst W.immediate :=
  λ w, OK (wextend w t, next_idx w).

Definition wnext_idx : wst W.immediate :=
  λ w, OK (w, next_idx w).

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
  | R.ProdT typs => flatten $ map compile_typ typs
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
    let tys1' := mapM compile_typ tys1 in
    let tys2' := mapM compile_typ tys2 in
    W.Tf (flatten tys1') (flatten tys2')
  end.
Definition compile_fun_type (ft: R.FunType) : W.function_type :=
  match ft with
  | R.FunT κs (R.Arrow tys1 tys2) =>
    let κvs := compile_kindvars κs in
    let tys1' := flatten $ mapM compile_typ tys1 in
    let tys2' := flatten $ mapM compile_typ tys2 in
    W.Tf (κvs ++ tys1') tys2'
  end.

Definition words_typ (typ: R.Typ) : nat :=
  sum_list_with operations.words_t $ compile_typ typ.

Definition throw_missing (instr_name : string) : exn err W.basic_instruction :=
  mthrow (Err ("missing iris-wasm " ++ instr_name ++ " wrap instruction")).

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

Fixpoint expect_concrete_size (sz: R.Size) : exn err nat :=
  match sz with
  | R.SizeConst c => mret c
  | R.SizePlus sz1 sz2 =>
      c1 ← expect_concrete_size sz1;
      c2 ← expect_concrete_size sz2;
      mret (c1 + c2)
  | _ => mthrow (Err "expected concrete size")
  end.

(* Mapping from size variables to indices of locals of type i32 *)
Definition size_ctx := 
  list W.immediate.

Section Mod.

Record compiler_mod_ctx := {
  mem_gc : W.immediate;
  mem_lin : W.immediate;
  free : W.immediate;
  alloc : W.immediate;
  coderef_offset : W.immediate;
}.

(* TODO: should these be combined? *)
Variable mctx : compiler_mod_ctx.
Variable (C : Module_Ctx).

Fixpoint struct_field_offset (fields: list (R.Typ * R.Size)) (idx: nat) : exn err R.Size :=
  match idx with
  | 0 => mret $ R.SizeConst 0
  | S idx' =>
      match fields with
      | (_, sz) :: fields' => R.SizePlus sz <$> (struct_field_offset fields' idx')
      | [] => mthrow Todo
      end
  end.

Definition get_struct_field_types (targs : list R.Typ) (idx : nat) : exn err (list (R.Typ * R.Size)) :=
  match targs !! idx with
  | Some (R.RefT _ _ (R.StructType fields)) => mret fields
  | _ => mthrow (Err ("struct instruction expected type-args to be a ref to a struct at index " ++ pretty idx))
  end.

Definition get_array_elem_type (targs : list R.Typ) (idx : nat) : exn err R.Typ :=
  match targs !! idx with
  | Some (R.RefT _ _ (R.ArrayType typ)) => mret typ
  | _ => mthrow (Err ("array instruction expected a ref to an array type at index " ++ pretty idx))
  end.

Definition if_gc_bit_set ins outs gc_branch lin_branch :=
  [W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 1%Z));
   W.BI_binop W.T_i32 (W.Binop_i W.BOI_and);
   W.BI_testop W.T_i32 W.TO_eqz;
   W.BI_if (W.Tf ins outs) lin_branch gc_branch].

Definition unset_gc_bit :=
  [W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z numerics.i32m 1%Z));
   W.BI_binop W.T_i32 (W.Binop_i W.BOI_sub)].

Fixpoint loads'
  (mem: W.immediate)
  (base_ptr_var: W.immediate)
  (off: W.static_offset)
  (tys: list W.value_type) :=
  match tys with
  | [] => []
  | ty :: tys =>
      W.BI_get_local base_ptr_var ::
      W.BI_load mem ty None 0%N off ::
      loads' base_ptr_var mem (off + N.of_nat (operations.length_t ty))%N tys
  end.

Definition loads mem base_ptr_var tys :=
  loads' mem base_ptr_var 0%N tys.

Definition gc_loads
  (ref_var: W.immediate)
  (offset_instrs: list W.basic_instruction)
  (tys: list W.value_type) :=
  base_ptr_var ← walloc W.T_i32;
  mret $ W.BI_get_local ref_var ::
         unset_gc_bit ++
         offset_instrs ++
         W.BI_binop W.T_i32 (W.Binop_i W.BOI_add) ::
         W.BI_set_local base_ptr_var ::
         loads mctx.(mem_gc) base_ptr_var tys.

Definition lin_loads
  (ref_var: W.immediate)
  (offset_instrs: list W.basic_instruction)
  (tys: list W.value_type) :=
  base_ptr_var ← walloc W.T_i32;
  mret $ W.BI_get_local ref_var ::
         offset_instrs ++
         W.BI_binop W.T_i32 (W.Binop_i W.BOI_add) ::
         W.BI_set_local base_ptr_var ::
         loads mctx.(mem_lin) base_ptr_var tys.

Definition tagged_loads
  (base_ptr: W.immediate)
  (offset_instrs: list W.basic_instruction)
  (tys: list W.value_type) :=
  gc_instrs ← gc_loads base_ptr offset_instrs tys;
  lin_instrs ← lin_loads base_ptr offset_instrs tys;
  mret $ W.BI_get_local base_ptr ::
         if_gc_bit_set [] tys gc_instrs lin_instrs.

Definition tagged_load
  (base_ptr: W.immediate)
  (offset_instrs: list W.basic_instruction)
  (ty: R.Typ)
  : wst (list W.basic_instruction) :=
  let tys := compile_typ ty in
  tagged_loads base_ptr offset_instrs tys.

Fixpoint loc_stores'
  (base_ptr_var: W.immediate)
  (mem: W.immediate)
  (off: W.static_offset)
  (val_var_tys: list (W.immediate * W.value_type)) :=
  match val_var_tys with
  | [] => []
  | (val_var, ty) :: val_var_tys =>
      W.BI_get_local base_ptr_var ::
      W.BI_get_local val_var ::
      W.BI_store mem ty None 0%N off ::
      loc_stores' base_ptr_var mem (off + N.of_nat (operations.length_t ty))%N val_var_tys
  end.

Definition loc_stores base_ptr_var mem val_var_tys : list W.basic_instruction :=
  loc_stores' base_ptr_var mem 0%N val_var_tys.

Definition stores base_ptr_var mem (val_vars: list W.immediate) (tys: list W.value_type)
  : list W.basic_instruction :=
  loc_stores base_ptr_var mem (zip val_vars tys).

Definition wallocs (tys: list W.value_type) : wst (list W.immediate) :=
  mapM walloc tys.

Definition walloc_args (tys: list W.value_type)
  : wst (list W.immediate *
         list W.basic_instruction) :=
  vars ← wallocs tys;
  mret $ (vars, map W.BI_set_local vars).

Definition walloc_rvalue (ty : R.Typ) : wst W.immediate :=
  next_idx ← wnext_idx;
  _ ← mapM walloc $ compile_typ ty;
  mret next_idx.

Definition walloc_rvalues (tys : list R.Typ) : wst W.immediate :=
  next_idx ← wnext_idx;
  _ ← mapM walloc_rvalue tys;
  mret next_idx.

Definition tagged_store
  (offset_instrs: list W.basic_instruction)
  (ty: R.Typ)
  : wst (list W.basic_instruction) :=
  let tys := compile_typ ty in
  '(arg_vars, save_args) ← walloc_args tys;
  base_ptr_var ← walloc W.T_i32;
  mret $
    save_args ++
    W.BI_tee_local base_ptr_var ::
    W.BI_get_local base_ptr_var ::
    if_gc_bit_set [] []
        (W.BI_get_local base_ptr_var ::
         unset_gc_bit ++
         offset_instrs ++
         W.BI_set_local base_ptr_var ::
         stores base_ptr_var mctx.(mem_gc) arg_vars tys)
        (W.BI_get_local base_ptr_var ::
         offset_instrs ++
         stores base_ptr_var mctx.(mem_lin) arg_vars tys).

Fixpoint local_layout (L: Local_Ctx) (base: nat) (i: nat) : exn err (nat * R.Typ) :=
  match L, i with
  | (τ, sz) :: L, 0 =>
      mret (base, τ)
  | (τ, sz) :: L, S i =>
      sz_const ← expect_concrete_size sz;
      local_layout L (base + sz_const) i
  | [], _ => mthrow (Err "local_layout given out of bounds index")
  end.

Fixpoint global_layout (globs : list R.GlobalType) (idx : nat) : option (nat * R.Typ) :=
  match globs, idx with
  | [R.GT _ ty], 0 => Some (0, ty)
  | R.GT _ ty :: globs', S idx' => global_layout globs' (length (compile_typ ty) + idx')
  | _, _ => None
  end.

Definition get_i64_local (loc : W.immediate) : list W.basic_instruction :=
  [ W.BI_get_local loc;
    W.BI_cvtop W.T_i32 W.CVO_reinterpret W.T_i64 None;
    W.BI_get_local (loc + 1);
    W.BI_const (W.VAL_int64 (Wasm_int.int_of_Z i64m 32));
    W.BI_binop W.T_i64 (W.Binop_i W.BOI_rotl);
    W.BI_cvtop W.T_i32 W.CVO_reinterpret W.T_i64 None;
    W.BI_binop W.T_i64 (W.Binop_i W.BOI_or) ].

Definition set_i64_local (loc : W.immediate) : wst (list W.basic_instruction) :=
  tmp ← walloc W.T_i64;
  mret [ W.BI_tee_local tmp;
         W.BI_const (W.VAL_int64 (wasm_extend_u int32_minus_one));
         W.BI_binop W.T_i64 (W.Binop_i W.BOI_and);
         W.BI_cvtop W.T_i64 W.CVO_convert W.T_i32 None;
         W.BI_set_local loc;
         W.BI_get_local tmp;
         W.BI_const (W.VAL_int64 (Wasm_int.int_of_Z i64m 32));
         W.BI_binop W.T_i64 (W.Binop_i W.BOI_rotr);
         W.BI_set_local (loc + 1) ].

Definition numtyp_gets (nτ: R.NumType) (loc: nat) : list W.basic_instruction :=
  match nτ with
  | R.Int s R.i32 => [ W.BI_get_local loc ]
  | R.Float R.f32 =>
      [ W.BI_get_local loc;
        W.BI_cvtop W.T_i32 W.CVO_reinterpret W.T_f32 None ]
  | R.Int s R.i64 => get_i64_local loc
  | R.Float R.f64 =>
      get_i64_local loc ++
      [ W.BI_cvtop W.T_i64 W.CVO_reinterpret W.T_f64 None ]
  end.

Definition numtyp_sets (nτ: R.NumType) (loc: nat) : wst (list W.basic_instruction) :=
  match nτ with
  | R.Int s R.i32 => mret [ W.BI_set_local loc ]
  | R.Float R.f32 =>
      mret [ W.BI_cvtop W.T_f32 W.CVO_reinterpret W.T_i32 None;
             W.BI_set_local loc ]
  | R.Int s R.i64 => set_i64_local loc
  | R.Float R.f64 =>
      es ← set_i64_local loc;
      mret $ W.BI_cvtop W.T_f64 W.CVO_reinterpret W.T_i64 None :: es
  end.

Fixpoint local_gets (τ: R.Typ) (loc: nat) : list W.basic_instruction :=
  match τ with
  | R.Num nτ =>
      numtyp_gets nτ loc
  | R.TVar α =>
      [W.BI_get_local loc]
  | R.Unit =>
      []
  | R.ProdT τs =>
      let fix loop τs0 sz :=
        match τs0 with
        | τ0 :: τs0' =>
            let sz := words_typ τ0 in
            let es := local_gets τ0 loc in
            let es' := loop τs0' (loc + sz) in
            es ++ es'
        | [] => []
        end in
      loop τs loc
  | R.CoderefT χ =>
    [W.BI_get_local loc]
  | R.Rec q τ =>
      local_gets τ loc
  | R.PtrT ℓ =>
      [W.BI_get_local loc]
  | R.ExLoc q τ =>
      local_gets τ loc
  | R.OwnR ℓ =>
      []
  | R.CapT cap ℓ ψ =>
      []
  | R.RefT cap ℓ ψ =>
      [W.BI_get_local loc]
  end.

Fixpoint local_sets (τ: R.Typ) (loc: nat) : wst (list W.basic_instruction) :=
  match τ with
  | R.Num nτ =>
      numtyp_sets nτ loc
  | R.TVar α =>
      mret [W.BI_set_local loc]
  | R.Unit =>
      mret []
  | R.ProdT τs =>
      let fix loop τs0 sz :=
        match τs0 with
        | τ0 :: τs0' =>
            let sz := words_typ τ0 in
            es ← local_sets τ0 loc;
            es' ← loop τs0' (loc + sz);
            mret $ es ++ es'
        | [] => mret []
        end in
      loop τs loc
  | R.CoderefT χ =>
      mret [W.BI_set_local loc]
  | R.Rec q τ =>
      local_sets τ loc
  | R.PtrT ℓ =>
      mret [W.BI_set_local loc]
  | R.ExLoc q τ =>
      local_sets τ loc
  | R.OwnR ℓ =>
      mret []
  | R.CapT cap ℓ ψ =>
      mret []
  | R.RefT cap ℓ ψ =>
      mret [W.BI_set_local loc]
  end.

Definition save_stack (tys : list R.Typ) : wst (W.immediate * list W.basic_instruction) :=
  idx ← walloc_rvalues tys;
  es ← local_sets (R.ProdT tys) idx;
  mret (idx, es).

Definition restore_stack (tys : list R.Typ) (idx : W.immediate) : list W.basic_instruction :=
  local_gets (R.ProdT tys) idx.

Definition funcidx_registerroot : W.immediate.
Admitted.

Definition funcidx_duproot : W.immediate.
Admitted.

Definition funcidx_unregisterroot : W.immediate.
Admitted.

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
  | LMNative => length $ compile_typ ty
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
        snd $ foldl
          (fun '(j, is) ty' => (j + layout_ty_length layout ty', is ++ go ty' j))
          (i, [])
          tys
    | R.Rec _ ty'
    | R.ExLoc _ ty' => go ty' i
    | R.TVar _
    | R.RefT _ _ _ => [i]
    end in
  go ty 0.

Definition map_gc_ref_vars (scope : VarScope) (es : list W.basic_instruction)
  : list W.immediate -> list W.basic_instruction :=
  flat_map (fun i =>
    let '(get, set) := scope_get_set scope in
    get i ::
    if_gc_bit_set [W.T_i32] [W.T_i32] es [] ++
    [set i]).

Section Fun.

Variable (sz_locs: size_ctx).
Variable (F : Function_Ctx).

Fixpoint compile_sz (sz : R.Size) : exn err (list W.basic_instruction) :=
  match sz with
  | R.SizeVar σ =>
    local_idx ← err_opt (sz_locs !! σ) ("sz " ++ (pretty σ) ++ " not found in sz_local_map");
    mret [W.BI_get_local local_idx]
  | R.SizePlus sz1 sz2 =>
    e1 ← compile_sz sz1;
    e2 ← compile_sz sz2;
    mret $ e1 ++ e2 ++ [W.BI_binop W.T_i32 (W.Binop_i W.BOI_add)]
  | R.SizeConst c =>
    mret [W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat c)))]
  end.

Definition compile_ind (ind: R.Index) : exn err (list W.basic_instruction) :=
  match ind with
  | R.SizeI sz => compile_sz sz
  | R.LocI _
  | R.QualI _
  | R.TypI _ => mret []
  end.

Definition compile_inds (inds: list R.Index) : exn err (list W.basic_instruction) :=
  flatten <$> mapM compile_ind inds.

Fixpoint compile_instr (instr: R.instr TyAnn) : wst (list W.basic_instruction) :=
  match instr with
  | R.INumConst _ num_type num =>
      mret [W.BI_const $ compile_num num_type num]
  | R.IUnit _ =>
      mret []
  | R.INum ann ni =>
      instr ← liftM $ compile_num_instr ni;
      mret [instr]
  | R.IUnreachable (R.Arrow targs trets, _) =>
      mret [W.BI_unreachable]
  | R.INop (R.Arrow targs trets, _) =>
      mret [W.BI_nop]
  | R.IDrop (R.Arrow targs trets, LSig L _) =>
      match targs with
      | [t_drop] =>
          let wasm_typ := compile_typ t_drop in
          '(base, es) ← save_stack [t_drop];
          let ref_vars := map (Nat.add base) $ ref_indices LMNative t_drop in
          mret $ map_gc_ref_vars VSLocal [W.BI_call funcidx_unregisterroot] ref_vars ++
                 restore_stack [t_drop] base ++
                 map (const W.BI_drop) wasm_typ
      | _ => mthrow (Err "drop should consume exactly one value")
      end
  | R.IBlock (R.Arrow targs trets, _) ta _ i =>
    let ta' := compile_arrow_type ta in
    i' ← mapM compile_instr i;
    mret [W.BI_block ta' (flatten i')]
  | R.ILoop (R.Arrow targs trets, _) arrow i =>
    let ft := compile_arrow_type arrow in
    i' ← mapM compile_instr i;
    mret [W.BI_block ft (flatten i')]
  | R.IIte (R.Arrow targs trets, _) arrow _ t e =>
    let ft := compile_arrow_type arrow in
    t' ← mapM compile_instr t;
    e' ← mapM compile_instr e;
    mret [W.BI_if ft (flatten t') (flatten e')]
  | R.IBr (R.Arrow targs trets, _) x => mret [W.BI_br x]
  | R.IBrIf (R.Arrow targs trets, _) x => mret [W.BI_br_if x]
  | R.IBrTable (R.Arrow targs trets, _) x x0 => mret [W.BI_br_table x x0]
  | R.IRet (R.Arrow targs trets, _) =>
      let ret_ty' := ssrfun.Option.default [] F.(ret) in
      let rdropped := take (length targs - length ret_ty') targs in
      let wdropped := flat_map compile_typ rdropped in
      '(idx_ret, ret_set_es) ← save_stack ret_ty';
      '(idx_dropped, dropped_es) ← save_stack rdropped;
      let ref_vars := map (Nat.add idx_dropped) $ flat_map (ref_indices LMNative) rdropped in
      mret $ ret_set_es ++
             dropped_es ++
             map_gc_ref_vars VSLocal [W.BI_call funcidx_unregisterroot] ref_vars ++
             restore_stack ret_ty' idx_ret ++
             [W.BI_return]
  | R.IGetLocal (R.Arrow targs trets, LSig L _) idx _ =>
      '(base, τ) ← liftM $ local_layout L 0 idx;
      let es1 := local_gets τ base in
      '(i, es2) ← save_stack [τ];
      let ref_vars := map (Nat.add i) $ ref_indices LMNative τ in
      let es3 := map_gc_ref_vars VSLocal [W.BI_call funcidx_duproot] ref_vars in
      let es4 := restore_stack [τ] i in
      mret $ es1 ++ es2 ++ es3 ++ es4
  | R.ISetLocal (R.Arrow targs trets, LSig L _) idx =>
      '(base, τ) ← liftM $ local_layout L 0 idx;
      let ref_vars := map (Nat.add base) $ ref_indices LMWords τ in
      let es1 := map_gc_ref_vars VSLocal [W.BI_call funcidx_unregisterroot] ref_vars in
      es2 ← local_sets τ base;
      mret $ es1 ++ es2
  | R.IGetGlobal _ i =>
      '(i', ty) ← liftM $ guard_opt (Err "invalid global index") $ global_layout C.(global) i;
      let es1 := imap (fun j _ => W.BI_get_global $ i' + j) $ compile_typ ty in
      '(j, es2) ← save_stack [ty];
      let ref_vars := map (Nat.add j) $ ref_indices LMNative ty in
      let es3 := map_gc_ref_vars VSLocal [W.BI_call funcidx_duproot] ref_vars in
      let es4 := restore_stack [ty] i in
      mret $ es1 ++ es2 ++ es3 ++ es4
  | R.ISetGlobal _ i =>
      '(i', ty) ← liftM $ guard_opt (Err "invalid global index") $ global_layout C.(global) i;
      let ref_vars := map (Nat.add i') $ ref_indices LMNative ty in
      let es1 := map_gc_ref_vars VSGlobal [W.BI_call funcidx_unregisterroot] ref_vars in
      let es2 := imap (fun j _ => W.BI_set_global (i' + j)) $ compile_typ ty in
      mret $ es1 ++ es2
  | R.ICoderef (R.Arrow targs trets, _) idx =>
    mret [W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat idx)));
          W.BI_get_global mctx.(coderef_offset);
          W.BI_binop W.T_i32 (W.Binop_i W.BOI_add)]
  | R.ICallIndirect (R.Arrow targs trets, _) inds => 
      '(stk, save_args) ← save_stack targs;
      sz_args ← liftM $ compile_inds inds;
      mret $ save_args ++ sz_args ++ restore_stack targs stk ++ [W.BI_call_indirect mctx.fn_tab]
  | R.ICall (R.Arrow targs trets, _) fidx inds => 
      '(stk, save_args) ← save_stack targs;
      sz_args ← liftM $ compile_inds inds;
      mret $ save_args ++ sz_args ++ restore_stack targs stk ++ [W.BI_call fidx]
  | R.IMemUnpack _ ta tl es =>
      let ta' := compile_arrow_type ta in
      e__s' ← flatten <$> mapM compile_instr es;
      mret [W.BI_block ta' e__s']
  | R.IStructMalloc (R.Arrow targs trets, _) szs q =>
      (* TODO: registerroot on the new address;
               unregisterroot if any field is GC ref being put into GC struct *)
      mthrow Todo
  | R.IStructFree (R.Arrow targs trets, _) =>
      (* TODO: unregisterroot fields that may be refs to GC if this struct is MM *)
      mthrow Todo
             (* mret $ [wasm.BI_call Σ.(me_free)]*)
  | R.IStructGet (R.Arrow from to, _) n =>
      base_ref ← walloc W.T_i32;
      fields ← liftM $ get_struct_field_types from 0;
      field_typ ← liftM $ err_opt (list_lookup 0 to) "struct.get: cannot find output val type";
      offset_sz ← liftM $ struct_field_offset fields n;
      offset_es ← liftM $ compile_sz offset_sz;
      load_es ← tagged_load base_ref offset_es field_typ;
      '(stk, save_es) ← save_stack [field_typ];
      let ref_vars := map (Nat.add stk) $ ref_indices LMNative field_typ in
      mret $ W.BI_tee_local base_ref ::
             load_es ++
             save_es ++
             W.BI_get_local base_ref ::
             if_gc_bit_set [] []
               (map_gc_ref_vars VSLocal [W.BI_call funcidx_registerroot] ref_vars)
               (map_gc_ref_vars VSLocal [W.BI_call funcidx_duproot] ref_vars) ++
             restore_stack [field_typ] stk
  | R.IStructSet (R.Arrow from to, _) n =>
      base_ref ← walloc W.T_i32;
      fields ← liftM $ get_struct_field_types from 1;
      field_typ ← liftM $ err_opt (list_lookup 0 to) "struct.get: cannot find output val type";
      val_typ ← liftM $ err_opt (list_lookup 0 from) "struct.set: cannot find input val type";
      offset_sz ← liftM $ struct_field_offset fields n;
      offset_es ← liftM $ compile_sz offset_sz;
      let tys := compile_typ field_typ in
      load_es ← gc_loads base_ref offset_es tys;
      store_es ← tagged_store offset_es val_typ;
      '(old_stk_var, old_save_es) ← save_stack [field_typ];
      '(new_stk_var, new_save_es) ← save_stack [val_typ];
      let old_ref_vars := map (Nat.add old_stk_var) $ ref_indices LMNative field_typ in
      let new_ref_vars := map (Nat.add new_stk_var) $ ref_indices LMNative val_typ in
      let unreg_es :=
        if_gc_bit_set [] []
          []
          (load_es ++
           new_save_es ++
           map_gc_ref_vars VSLocal [W.BI_call funcidx_unregisterroot] old_ref_vars) in
      let loadroot_es :=
        if_gc_bit_set [] []
          (new_save_es ++
           map_gc_ref_vars VSLocal [W.BI_load mctx.(mem_gc) W.T_i32 None 0%N 0%N] new_ref_vars ++
           restore_stack [val_typ] new_stk_var)
          [] in
      mret $ W.BI_tee_local base_ref ::
             unreg_es ++
             W.BI_get_local base_ref ::
             loadroot_es ++
             W.BI_get_local base_ref ::
             store_es
  | R.IStructSwap (R.Arrow from to, _) n =>
      (* TODO: registerroot if GC struct *)
      fields ← liftM $ get_struct_field_types from 1;
      field_typ ← liftM $ err_opt (list_lookup 0 from) "struct.swap: cannot find input val type";
      let field_shape := compile_typ field_typ in
      offset_sz ← liftM $ struct_field_offset fields n;
      offset_e ← liftM $ compile_sz offset_sz;
      mthrow Todo
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
      typ ← liftM $ err_opt (list_lookup 0 from) "variant.malloc: cannot find val type";
      let shape := compile_typ typ in
      (* memory layout is [ind, τ*] so we just add prepend *)
      (*let full_shape := LS_tuple [LS_int32; shape] in*)
      mthrow Todo (*
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
        mthrow Todo
    (* [val__init; len] → [ptr] *)
    (* [τ      ; i32] → [i32] *)
    | R.IArrayMalloc (R.Arrow from to, _) q =>
      (* TODO: unregisterroot the initial value if GC array;
               duproot a bunch of times if MM array *)
      arr_init_typ ← liftM $ err_opt (list_lookup 1 from) "array.malloc: cannot find val type";
      let shape := compile_typ arr_init_typ in
      mthrow Todo
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
      elem_typ ← liftM $ get_array_elem_type from 1;
      let elem_shape := compile_typ elem_typ in
      (*  ex: i64[i]
         | idx | offset |
         |-----|--------|
         | 0   | 0      |
         | 1   | 1 * 2  |
         ...
         | i   | i * 2  | *)
      mthrow Todo
(*
      mret [
        layout.Val $ LV_int32 (shape_size_words elem_shape);
        layout.Ne $ rwasm.Ib rwasm.i32 rwasm.mul; (* [idx; sz] → [offset] *)
        layout.LoadOffset elem_shape; (* [ptr; offset] → [ptr; offset; val] *)
        layout.Swap;                  (* [offset; val] → [val; offset]*)
        layout.Drop]                  (* [offset]; → [] *)
    (* [ptr; idx; val] → [ptr] *)
    (* [i32; i32; τ  ] → [i32] *)
*)
    | R.IArraySet (R.Arrow from to, _) =>
      (* TODO: unregisterroot if GC array;
               duproot a bunch of times if MM array *)
      elem_typ ← liftM $ get_array_elem_type from 2;
      let elem_shape := compile_typ elem_typ in
      (*  ex: [i]
         | idx | offset      |
         |-----|-------------|
         | 0   | 2           |
         | 1   | 2 * 2       |
         ...
         | i   | (i + 1) * 2 | *)
      mthrow Todo
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
      mthrow Todo (*mret $ [wasm.BI_call Σ.(me_free)]*)
  | R.IExistPack (R.Arrow targs trets, _) t th q =>
      (* TODO: unregisterroot if GC package *)
      mthrow Todo
  | R.IExistUnpack (R.Arrow targs trets, _) q th ta tl es =>
      (* TODO: registerroot if GC package *)
      mthrow Todo
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
  | R.IQualify _ _ => mret []
  end.

Definition compile_instrs instrs := flatten <$> mapM compile_instr instrs.

End Fun.

End Mod.

Definition compile_fun_type_idx (fun_type : R.FunType) : W.typeidx.
Admitted.

Definition funcidx_table_write : W.immediate.
Admitted.

Definition typeidx_start : W.immediate.
Admitted.

Definition typeidx_table_write : W.immediate.
Admitted.

Definition globidx_table_next : W.immediate.
Admitted.

Definition globidx_table_offset : W.immediate.
Admitted.

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


Fixpoint compile_module (module : R.module TyAnn) : exn err W.module :=
  let '(funcs, globs, table) := module return exn err W.module in
  let mctx := {|
    mem_gc := 0;
    mem_lin := 1;
    free := 0;
    alloc := 1;
    coderef_offset := 0;
  |} in
  mret {|
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

with compile_glob (glob : R.Glob TyAnn) : exn err W.module_glob
with compile_table (table : R.Table) : exn err W.module_table.
Admitted.
