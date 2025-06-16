From Coq Require Import List NArith.BinNat.
From stdpp Require Import base option strings list pretty gmap gmultiset fin_sets decidable.
From RWasm Require term annotated_term.
From RWasm Require Import exn state.
From Wasm Require datatypes.
From Wasm Require Import datatypes numerics .
From RWasm.compiler Require Import numbers monads.


Module rwasm := term.
Module AR := annotated_term.
Module wasm := datatypes.

Fixpoint compile_numtyp (typ: rwasm.NumType) : M (wasm.value_type) :=
  match typ with
  | rwasm.Int _ rwasm.i32 => mret wasm.T_i32
  | rwasm.Int _ rwasm.i64 => mret wasm.T_i64
  | rwasm.Float rwasm.f32 => mret wasm.T_f32
  | rwasm.Float rwasm.f64 => mret wasm.T_f64
  end.

Fixpoint compile_typ (typ: rwasm.Typ) : M (list wasm.value_type) :=
  match typ with
  | rwasm.Num ntyp => wty ← compile_numtyp ntyp; mret [wty]
  | rwasm.TVar x => mthrow (err "todo")
  | rwasm.ProdT typs =>
      typs' ← mapM (fun x => compile_typ x) typs;
      mret (concat typs')
  | rwasm.PtrT _
  | rwasm.RefT _ _ _
  | rwasm.CoderefT _ => mret [wasm.T_i32]
  | rwasm.Rec _ typ => compile_typ typ
  | rwasm.ExLoc q x => mthrow (err "todo")
  | rwasm.Unit
  | rwasm.OwnR _
  | rwasm.CapT _ _ _ => mret []
  end
with compile_heap_type (typ: rwasm.HeapType) : M unit :=
  match typ with
  | rwasm.VariantType typs => mthrow (err "todo")
  | rwasm.StructType fields => mthrow (err "todo")
  | rwasm.ArrayType elt_typ => mthrow (err "todo")
  | rwasm.Ex sz qual typ => mthrow (err "todo")
  end
with compile_arrow_type (typ: rwasm.ArrowType) : M wasm.function_type :=
  match typ with
  | rwasm.Arrow tys1 tys2 =>
    tys1' ← mapM compile_typ tys1;
    tys2' ← mapM compile_typ tys2;
    mret (wasm.Tf (mjoin tys1') (mjoin tys2'))
  end
with compile_fun_type (typ: rwasm.FunType) : M wasm.function_type :=
 match typ with
 | rwasm.FunT kinds arrow => mthrow (err "todo")
 end. (* What to do about generics? *)



Definition expect_concrete_size (sz: rwasm.Size) : M nat :=
  match sz with
  | rwasm.SizeConst c => mret c
  | _ => mthrow (err "todo")
  end.

(* Mapping from size variables to indices of locals of type i32 *)
Definition size_ctx :=
  list wasm.immediate.

(* FIXME: *)
Unset Guard Checking.
Section compile_instr.

Variable (sz_locs: size_ctx).
(* i32 local for hanging on to linear references during stores/loads *)
Variable (GC_MEM: wasm.immediate).
Variable (LIN_MEM: wasm.immediate).
Variable (MALLOC_FUNC: wasm.immediate).
Variable (FREE_FUNC: wasm.immediate).

Definition size_of_wasm_typ_offset (typ : wasm.value_type) : Z :=
  match typ with
  | wasm.T_i32 => 32%Z
  | wasm.T_i64 => 64%Z
  | wasm.T_f32 => 32%Z
  | wasm.T_f64 => 64%Z
  end.

Fixpoint fold_sizes (sizes : list rwasm.Size) : rwasm.Size :=
  match sizes with
  | [] => rwasm.SizeConst 0
  | sz :: rst => rwasm.SizePlus sz (fold_sizes rst)
  end.

(* n.b. this is polymorphic :( *)
Fixpoint struct_field_offset (fields: list (rwasm.Typ * rwasm.Size)) (idx: nat) : InstM rwasm.Size :=
  match idx with
  | 0 => mret $ rwasm.SizeConst 0
  | S idx' =>
      match fields with
      | (_, sz) :: fields' => rwasm.SizePlus sz <$> (struct_field_offset fields' idx')
      | [] => mthrow (err ("not enough fields in struct type to find field offset of index " ++ pretty idx))
      end
  end.

(* Produces code that given a frame with sizes according to size_ctx
   computes one i32, which is the concrete value of sz at run time. *)
Fixpoint compile_size_expr (sz: rwasm.Size) : InstM (list wasm.basic_instruction) :=
  match sz with
  | rwasm.SizeVar σ =>
      l_idx ← lift_M (guard_opt (err "sz not found in sz_locs") $ sz_locs !! σ);
      mret [wasm.BI_get_local l_idx]
  | rwasm.SizePlus sz sz' =>
      e ← compile_size_expr sz;
      e' ← compile_size_expr sz';
      mret (e ++ e' ++ [wasm.BI_binop wasm.T_i32 (wasm.Binop_i wasm.BOI_add)])
  | rwasm.SizeConst n =>
      mret [wasm.BI_const (compile_num_from_Z wasm.T_i32 (Z.of_nat n))]
  end.

Definition if_gc_bit_set ref_tmp ins outs gc_branch lin_branch :=
  [wasm.BI_get_local ref_tmp;
   wasm.BI_const (compile_num_from_Z wasm.T_i32 1%Z);
   wasm.BI_binop wasm.T_i32 (wasm.Binop_i wasm.BOI_and);
   wasm.BI_testop wasm.T_i32 wasm.TO_eqz;
   wasm.BI_if (wasm.Tf ins outs) lin_branch gc_branch].

Definition unset_gc_bit :=
  [wasm.BI_const (compile_num_from_Z wasm.T_i32 1%Z);
   wasm.BI_binop wasm.T_i32 (wasm.Binop_i wasm.BOI_sub)].

Definition get_struct_field_types (targs : list rwasm.Typ) (idx : nat) : M (list (rwasm.Typ * rwasm.Size)) :=
  match (list_lookup idx targs) with
  | Some (rwasm.RefT _ _ (rwasm.StructType fields)) => mret fields
  | _ => mthrow (err ("struct instruction expected type-args to be a ref to a struct at index " ++ pretty idx))
  end.

(* TODO: validate ordering *)
Fixpoint tagged_load_all (memory : nat) (wasm_typs : list wasm.value_type) (scratch : wasm.immediate) : list wasm.basic_instruction :=
  match wasm_typs with
  | [] => []
  | typ :: rst =>
    let typ_size := size_of_wasm_typ_offset typ in
    [wasm.BI_get_local scratch;
     wasm.BI_load memory typ None 0%N 0%N;

     (* update scratch reg *)
     wasm.BI_const (compile_num_from_Z typ typ_size);
     wasm.BI_get_local scratch;
     wasm.BI_binop typ (wasm.Binop_i wasm.BOI_add);
     wasm.BI_set_local scratch] ++ (tagged_load_all memory rst scratch)
  end.
Definition struct_setup_gc_scratch ref_tmp scratch : (list wasm.basic_instruction) :=
  [wasm.BI_get_local ref_tmp] ++
    unset_gc_bit ++
    [wasm.BI_binop wasm.T_i32 (wasm.Binop_i wasm.BOI_add);
     wasm.BI_tee_local scratch].

Definition struct_setup_lin_scratch ref_tmp scratch : (list wasm.basic_instruction) :=
  [wasm.BI_get_local ref_tmp;
  wasm.BI_binop wasm.T_i32 (wasm.Binop_i wasm.BOI_add);
  wasm.BI_tee_local scratch].

Definition tagged_load (offset_instrs : list wasm.basic_instruction) field_typ (ref_tmp : wasm.immediate) : InstM (list wasm.basic_instruction) :=
  wasm_field_typ ← lift_M (compile_typ field_typ);
  scratch ← fresh_local wasm.T_i32;
  instrs ← mret $ offset_instrs ++
    [wasm.BI_get_local ref_tmp] ++
    if_gc_bit_set ref_tmp [wasm.T_i32 (* offset *)] wasm_field_typ
      (struct_setup_gc_scratch ref_tmp scratch ++ tagged_load_all GC_MEM wasm_field_typ scratch)
      (struct_setup_lin_scratch ref_tmp scratch ++ tagged_load_all LIN_MEM wasm_field_typ scratch);
  free_local scratch;;

  mret instrs.

Definition get_struct_ctx (targs : list rwasm.Typ) (targ_idx : nat) (idx : nat) : InstM _ :=
  fields ← lift_M $ get_struct_field_types targs targ_idx;
  off_sz ← struct_field_offset fields idx;
  off_instrs ← compile_size_expr off_sz;
  '(field_typ, _) ← lift_M $ mlookup_with_msg targ_idx fields "cannot get field type";
  mret (fields, off_sz, off_instrs, field_typ).



Definition reduce_to_admin (instr: AR.PreInstruction) (targs trets: list rwasm.Typ) : InstM AR.PreInstruction :=
  match instr with
  | AR.Val _
  | AR.Ne _
  | AR.Unreachable
  | AR.Nop
  | AR.Drop
  | AR.Select
  | AR.Block _ _ _
  | AR.Loop _ _
  | AR.ITE _ _ _ _
  | AR.Br _
  | AR.Br_if _
  | AR.Br_table _ _
  | AR.Ret => mret instr
  | AR.Get_local x x0 => mret instr
  | AR.Set_local x => mret instr
  | AR.Tee_local x => mret instr
  | AR.Get_global x => mret instr
  | AR.Set_global x => mret instr
  | AR.CoderefI x => mret instr
  | AR.Inst x => mret instr
  | AR.Call_indirect => mret instr
  | AR.Call x x0 => mret instr
  | AR.RecFold _
  | AR.RecUnfold
  | AR.Group _ _
  | AR.Ungroup
  | AR.CapSplit
  | AR.CapJoin
  | AR.RefDemote
  | AR.MemPack _
  | AR.MemUnpack _ _ _ => mret instr
  (* | AR.StructMalloc field_szs qual => mret AR.Malloc (fold_sizes field_szs) rwasm.Struct *)
  | AR.StructMalloc field_szs qual => mthrow (err "how do get HeapVal?")
  | AR.StructFree => mret AR.Free
  | AR.StructGet x => mret instr
  | AR.StructSet x => mret instr
  | AR.StructSwap x => mret instr
  | AR.VariantMalloc x x0 x1 => mret instr
  | AR.VariantCase x x0 x1 x2 x3 => mret instr
  | AR.ArrayMalloc x => mret instr
  | AR.ArrayGet => mret instr
  | AR.ArraySet => mret instr
  | AR.ArrayFree => mret AR.Free
  | AR.ExistPack x x0 x1 => mret instr
  | AR.ExistUnpack x x0 x1 x2 x3 => mret instr
  | AR.RefSplit => mret instr
  | AR.RefJoin => mret instr
  | AR.Qualify x => mret instr

  | AR.Trap
  | AR.CallAdm _ _
  | AR.Label _ _ _ _
  | AR.Local _ _ _ _ _
  | AR.Malloc _ _ _
  | AR.Free => mthrow (err "unexpected admin instr in reduce_to_admin")
  end.
Fixpoint compile_instr (instr: AR.Instruction) {struct instr} : InstM (list wasm.basic_instruction) :=
  match instr with
  | AR.Instr instr' (rwasm.Arrow targs trets) =>
    reduced ← reduce_to_admin instr' targs trets;
    compile_pre_instr reduced targs trets
  end
with compile_pre_instr (instr: AR.PreInstruction) (targs trets: list rwasm.Typ) {struct instr} : InstM (list wasm.basic_instruction) :=
  match instr with
  | AR.Val v =>
    vals ← lift_M (compile_value v);
    mret (map (fun x => wasm.BI_const x) vals)
  | AR.Ne ni => (fun x => [x]) <$> (lift_M $ compile_num_intr ni)
  | AR.Unreachable => mret [wasm.BI_unreachable]
  | AR.Nop => mret [wasm.BI_nop]
  | AR.Drop => mret [wasm.BI_drop]
  | AR.Select => mret [wasm.BI_select]
  | AR.Block arrow _ i =>
    ft ← lift_M $ compile_arrow_type arrow;
    i' ← mapM compile_instr i;
    mret [wasm.BI_block ft (mjoin i')]
  | AR.Loop arrow i =>
    ft ← lift_M $ compile_arrow_type arrow;
    i' ← mapM compile_instr i;
    mret [wasm.BI_block ft (mjoin i')]
  | AR.ITE arrow _ t e =>
    ft ← lift_M $ compile_arrow_type arrow;
    t' ← mapM compile_instr t;
    e' ← mapM compile_instr e;
    mret [wasm.BI_if ft (mjoin t') (mjoin e')]
  | AR.Br i => mret [wasm.BI_br i]
  | AR.Br_if i => mret [wasm.BI_br_if i]
  | AR.Br_table i j => mret [wasm.BI_br_table i j]
  | AR.Ret => mret [wasm.BI_return]
  (* these depend on the size of the type *)
  | AR.Get_local x x0 => mret [wasm.BI_get_local x] (* TODO: fix *)
  | AR.Set_local x => mret [wasm.BI_set_local x] (* TODO: fix *)
  | AR.Tee_local x => mret [wasm.BI_tee_local x] (* TODO: fix *)
  | AR.Get_global x => mret [wasm.BI_get_global x] (* TODO: fix *)
  | AR.Set_global x => mret [wasm.BI_set_global x] (* TODO: fix *)
  | AR.CoderefI x => mthrow (err "todo msg")
  | AR.Inst _ => mret []
  | AR.Call_indirect => mthrow (err "todo msg")
  | AR.Call x x0 => mthrow (err "todo msg")
  | AR.RecFold _
  | AR.RecUnfold
  | AR.Group _ _
  | AR.Ungroup
  | AR.CapSplit
  | AR.CapJoin
  | AR.RefDemote
  | AR.MemPack _ => mret []
  | AR.MemUnpack bt _ body => mthrow (err "todo msg")
  | AR.StructMalloc _ _
  | AR.StructFree => mthrow (err "became admin")
  | AR.StructGet idx =>
      (* Save the argument *)
      (* typ should be [ref l (structtype fields)] -> [ref l (structtype fields); tau_field] *)
      ref_tmp ← fresh_local wasm.T_i32;
      '(fields, off_sz, off_instrs, field_typ) ← get_struct_ctx targs 0 idx;
      load_instrs ← tagged_load off_instrs field_typ ref_tmp;
      instrs ← mret $ wasm.BI_tee_local ref_tmp :: load_instrs;
      free_local ref_tmp;;
      mret instrs
  | AR.StructSet idx => mthrow (err "todo")
  | AR.StructSwap x => mthrow (err "todo msg")
  | AR.VariantMalloc _ _ _ => mthrow (err "became admin")
  | AR.VariantCase x x0 x1 x2 x3 => mthrow (err "todo msg") (* FIXME: is it possible to rewrite in term of AR?*)
  | AR.ArrayGet => mthrow (err "todo msg")
  | AR.ArraySet => mthrow (err "todo msg")
  | AR.ArrayMalloc _
  | AR.ArrayFree => mthrow (err "became admin")
  | AR.ExistPack x x0 x1 => mthrow (err "todo msg")
  | AR.ExistUnpack x x0 x1 x2 x3 => mthrow (err "todo msg")
  | AR.RefSplit
  | AR.RefJoin
  | AR.Qualify _ => mret []
  | AR.Trap => mret [wasm.BI_unreachable]
  | AR.CallAdm x x0 => mthrow (err "todo msg")
  | AR.Label x x0 x1 x2 => mthrow (err "todo msg")
  | AR.Local x x0 x1 x2 x3 => mthrow (err "todo msg")
  | AR.Malloc sz hv qual => mret [wasm.BI_call MALLOC_FUNC]
  | AR.Free => mret [wasm.BI_call FREE_FUNC]
  end.
End compile_instr.
Set Guard Checking.

Definition annotate_instr (instr : rwasm.Instruction) : AR.Instruction.
Admitted.

Definition compile_func (idx : nat) (func : rwasm.Func) : M _ :=
  match func with
  | rwasm.Fun exports fun_type sizes instrs =>
    let sz_locs := [] in (* FIXME: deal with sizes *)
    let GC_MEM := 0 in
    let LIN_MEM := 1 in
    let ann_instrs := map annotate_instr instrs in
    (* TODO: do exports need to be propogated out? *)
    let instrs' := mapM (compile_instr sz_locs GC_MEM LIN_MEM 0 1) ann_instrs in
    let init_tl := new_tl 0 in
    '(st, instrs_ll) ← instrs' init_tl;
    let locals := map snd (map_to_list (tl_types st)) in
    let body   := concat instrs_ll in
    wasm_func ← mret {|
      wasm.modfunc_type := wasm.Mk_typeidx idx;
      wasm.modfunc_locals := locals;
      wasm.modfunc_body := body;
    |};
    fun_type' ← compile_fun_type fun_type;
    mret (wasm_func, fun_type')
  end.

Fixpoint compile_module (module : rwasm.module) : M wasm.module :=
  let '(funcs, globs, table) := module in

  '(fns, _) ← foldlM (fun func '(acc, idx) => func' ← compile_func idx func; mret (func' :: acc, S idx)) ([], 0) funcs;
  '(wasm_funcs, wasm_func_types) ← mret $ split fns;

  mret {|
    wasm.mod_types := wasm_func_types;
    wasm.mod_funcs := wasm_funcs;
    wasm.mod_tables := []; (* TODO *)
    wasm.mod_mems := []; (* TODO *)
    wasm.mod_globals := []; (* TODO *)
    wasm.mod_elem := []; (* TODO *)
    wasm.mod_data := []; (* TODO *)
    wasm.mod_start := None; (* TODO *)
    wasm.mod_imports := []; (* TODO *)
    wasm.mod_exports := [] (* TODO *)
  |}
with compile_glob (glob : rwasm.Glob) : M wasm.module_glob
with compile_table (table : rwasm.Table) : M wasm.module_table.
Admitted.
