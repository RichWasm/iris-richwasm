From Coq Require Import List NArith.BinNat Lists.List FSets.FMapInterface.
From stdpp Require Import base option strings list pretty decidable gmap.
From Wasm Require datatypes.
From RWasm Require term.
From RWasm.compiler Require Import numbers monads utils layout.

Module LayoutIR.
  Import layout.
  Definition shape := LayoutShape.
  Definition value := LayoutValue.

  Inductive ArrowShape :=
  | Arrow (shapes1 : list shape) (shapes2 : list shape).

  Definition LocalEffect := list (nat * shape).

  (* TODO: need to see if this is actually enough to stop worrying about annotated types *)
  Inductive Instruction :=
  | Val (v : value)
  | Ne (ni : rwasm.NumInstr)

  | Unreachable
  | Nop
  | Drop
  | Select
  | Block (tf : ArrowShape) (le : LocalEffect) (e__s : list Instruction)
  | Loop (tf : ArrowShape) (e : list Instruction)
  | ITE (tf : ArrowShape) (le : LocalEffect) (e__thn : list Instruction) (e__els : list Instruction)
  | Br (i : nat)
  | BrIf (i : nat)
  | BrTable (i__s : list nat) (j : nat)
  | Ret

  | NewTmp (name : string) (shape : shape)
  | SetTmp (name : string)
  | TeeTmp (name : string)
  | GetTmp (name : string)
  | FreeTmp (name : string)

  | GetLocal (i : nat)
  | SetLocal (i : nat)
  | TeeLocal (i : nat)
  | GetGlobal (i : nat)
  | SetGlobal (i : nat)

  | CallIndirect (tf : ArrowShape)        (* TODO: is this correct? *)
  | Call (i : nat)

  | Init (shape : list shape)              (* [val; ptr] → [ptr] *) (* FIXME: is this really needed? surely we can just use store-offset*)
  | RepeatInit (shape : shape)        (* [val; len; ptr] → [ptr] *)  (* FIXME: improve stack shape *)
  | LoadOffset (shape : shape)          (* [ptr; offset] → [ptr; offset; val] *)
  | StoreOffset (shape : shape)    (* [ptr; offset; val] → [ptr; offset] *)
  | SwapOffset (shape : shape)  (* [ptr; offset; val__new] → [ptr; offset; val__old] *)
  | Malloc                                    (* [words] → [ptr] *)
  | Free                                        (* [ptr] → [] *)
  with Func :=
  | Fun (ex__s : list rwasm.ex) (ta : ArrowShape) (locals : list shape) (e__s : list Instruction).

  Inductive Glob :=
  | GlobMut (shape : shape) (i__s : list Instruction)
  | GlobEx (ex__s : list rwasm.ex) (shape : shape) (i__s : list Instruction)
  | GlobIm (ex__s : list rwasm.ex) (shape : shape) (im : rwasm.im).

  Record module := {
    functions : list Func;
    globals : list Glob;
    table : rwasm.Table
  }.
End LayoutIR.

Module RWasmToLayout.
  Import layout.
  Import List Lists.List ListNotations FSets.FMapInterface.
  Module layout := LayoutIR.

  Section Typ.

  Variable env : gmap rwasm.var LayoutShape.

  (* TODO: deal with boxing and unboxing, does tvar need to be touched?? *)
  Fixpoint compile_typ (τ : rwasm.Typ) : M LayoutShape := (* TODO: function ctx *)
    match τ with
    | rwasm.Num nτ =>
      mret $ match nτ with
      | rwasm.Int _ rwasm.i32 => LS_int32
      | rwasm.Int _ rwasm.i64 => LS_int64
      | rwasm.Float rwasm.f32 => LS_float32
      | rwasm.Float rwasm.f64 => LS_float64
      end
    | rwasm.TVar α => mret LS_int32
    | rwasm.Unit => mret LS_empty
    | rwasm.ProdT τ__s =>
      shapes ← (mapM compile_typ τ__s);
      mret $ LS_tuple shapes
    | rwasm.CoderefT χ => mthrow todo
    | rwasm.Rec q τ => compile_typ τ
    | rwasm.PtrT ℓ => mret LS_int32
    | rwasm.ExLoc q τ => mthrow todo
    | rwasm.OwnR _
    | rwasm.CapT _ _ _ => mret LS_empty
    | rwasm.RefT cap ℓ ψ => mret LS_int32
    end.

  Fixpoint compile_ta (ta : rwasm.ArrowType) : M layout.ArrowShape :=
    let 'rwasm.Arrow τ__s1 τ__s2 := ta in
    τ__s1' ← mapM compile_typ τ__s1;
    τ__s2' ← mapM compile_typ τ__s2;
    mret $ layout.Arrow τ__s1' τ__s2'.

  End Typ.

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

  Section Instrs.

  Variable sz_local_map : gmap nat nat.
  Variable transform_local_idx : nat → nat.

  Fixpoint compile_tl (* (env : gmap rwasm.var LayoutShape) *) (tl : rwasm.LocalEffect) : M layout.LocalEffect :=
     mapM (fun '(i, τ) =>
            shape ← compile_typ (* env *) τ;
            mret (transform_local_idx i, shape)) tl.

  Fixpoint compile_sz (sz : rwasm.Size) : M (list layout.Instruction) :=
    match sz with
    | rwasm.SizeVar σ =>
      local_idx ← lift_optionM (sz_local_map !! σ) ("sz " ++ (pretty σ) ++ " not found in sz_local_map");
      mret [layout.GetLocal local_idx]
    | rwasm.SizePlus sz1 sz2 =>
      e1 ← compile_sz sz1;
      e2 ← compile_sz sz2;
      mret $ e1 ++ e2 ++ [layout.Ne $ rwasm.Ib rwasm.i32 rwasm.add]
    | rwasm.SizeConst c => mret [layout.Val $ LV_int32 c]
    end.

  Fixpoint compile_instr (* (env : gmap rwasm.var LayoutShape) *) (instr : rwasm.instr rwasm.ArrowType) : M (list layout.Instruction) :=
    match instr with
    | rwasm.INumConst ann nt n =>
      mret [layout.Val $ match nt with
      | rwasm.Int _ rwasm.i32 => LV_int32
      | rwasm.Int _ rwasm.i64 => LV_int64
      | rwasm.Float rwasm.f32 => LV_float32
      | rwasm.Float rwasm.f64 => LV_float64
      end n]
    | rwasm.IUnit ann => mret [layout.Val LV_unit]
    | rwasm.INum ann ni => mret [layout.Ne ni]
    | rwasm.IUnreachable ann => mret [layout.Unreachable]
    | rwasm.INop ann => mret [layout.Nop]
    | rwasm.IDrop ann => mret [layout.Drop]
    | rwasm.ISelect ann => mret [layout.Select]
    | rwasm.IBlock ann ta tl es =>
      ta' ← compile_ta (* env *) ta;
      tl' ← compile_tl (* env *) tl;
      e__s' ← flat_mapM (compile_instr (* env *)) es;
      mret [layout.Block ta' tl' e__s']
    | rwasm.ILoop ann ta es =>
      ta' ← compile_ta (* env *) ta;
      e__s' ← flat_mapM (compile_instr (* env *)) es;
      mret [layout.Loop ta' e__s']
    | rwasm.IIte ann ta tl es1 es2 =>
      ta' ← compile_ta (* env *) ta;
      tl' ← compile_tl (* env *) tl;
      e__thn' ← flat_mapM (compile_instr (* env *)) es1;
      e__els' ← flat_mapM (compile_instr (* env *)) es2;
      mret [layout.ITE ta' tl' e__thn' e__els']
    | rwasm.IBr ann i => mret [layout.Br i]
    | rwasm.IBrIf ann i => mret [layout.BrIf i]
    | rwasm.IBrTable ann ns i => mret [layout.BrTable ns i]
    | rwasm.IRet ann => mret [layout.Ret]
    | rwasm.IGetLocal ann i q => mret [layout.GetLocal (transform_local_idx i)]
    | rwasm.ISetLocal ann i => mret [layout.SetLocal (transform_local_idx i)]
    | rwasm.ITeeLocal ann i => mret [layout.TeeLocal (transform_local_idx i)]
    | rwasm.IGetGlobal ann i => mret [layout.GetGlobal i]
    | rwasm.ISetGlobal ann i => mret [layout.SetGlobal i]

    | rwasm.ICoderef ann i => mret [layout.Val $ LV_int32 i]      (* TODO: need to confirm this is correct, this is how the rust compiler does it *)
    | rwasm.IInst ann idxs => mret []
    | rwasm.ICallIndirect ann => mthrow (err "TODO: likely will need to change RWasm to explicitly pass sizes")
    | rwasm.ICall ann i idxs =>
      (* FIXME: Box and unbox *)

      z__sizes ← mret $ omap (fun idx => match idx with
                                    | rwasm.SizeI sz => Some sz
                                    | rwasm.LocI _ | rwasm.QualI _ | rwasm.TypI _ => None end) idxs;
      size_instrs ← flat_mapM compile_sz z__sizes;
      mret $ size_instrs ++ [layout.Call i]

    | rwasm.IRecFold _ _
    | rwasm.IRecUnfold _
    | rwasm.IGroup _ _ _
    | rwasm.IUngroup _
    | rwasm.ICapSplit _
    | rwasm.ICapJoin _
    | rwasm.IRefDemote _
    | rwasm.IMemPack _ _ => mret []
    | rwasm.IMemUnpack _ ta tl es =>
      ta' ← compile_ta (* env *) ta;
      tl' ← compile_tl (* env *) tl;
      e__s' ← flat_mapM (compile_instr (* env *)) es;
      mret [layout.Block ta' tl' e__s']

    (* [init_val1 ... init_val__n] → [ptr] *)
    (* [τ1        ... τ__n       ] → [i32] *)
    (* where n is known by the number of szs *)
    | rwasm.IStructMalloc ann szs q =>
      flat_sz ← mret $ fold_sizes szs;

      (* field_shapes ← *)
      mthrow todo

    (* [ptr] → [] *)
    (* [i32] → [] *)
    | rwasm.IStructFree ann => mret [layout.Free]

    (* [ptr] → [ptr; val] *)
    (* [i32] → [i32; τ  ] *)
    | rwasm.IStructGet ann n => mthrow todo

    (* [ptr; val] → [ptr] *)
    (* [i32; τ  ] → [i32] *)
    | rwasm.IStructSet ann n => mthrow todo

    (* [ptr; val__new] → [ptr; val__old] *)
    (* [i32; τ     ] → [i32; τ     ] *)
    | rwasm.IStructSwap ann n => mthrow todo

    (* [val__init] → [ptr] *)
    (* [τ      ] → [i32] *)
    | rwasm.IVariantMalloc ann i ts q =>
      typ ← lift_optionM (list_lookup i ts) ("invalid variant malloc, no type corresponds with index " ++ (pretty i));
      shape ← compile_typ (* env *) typ;
      (* memory layout is [ind, τ*] so we just add prepend *)
      let full_shape := LS_tuple [LS_int32; shape] in
      mret $ [
        layout.NewTmp "init" shape;
        layout.SetTmp "init";

        layout.Val $ LV_int32 (shape_size_words full_shape);
        layout.Malloc;          (* [i32] → [ptr] *)

        layout.Val $ LV_int32 i;
        layout.Val $ LV_int32 0;
        layout.StoreOffset LS_int32; (* [ptr; offset; val] → [ptr; offset] *)
        layout.GetTmp "init";
        layout.FreeTmp "init";
        layout.StoreOffset shape; (* [ptr; offset; val] → [ptr; offset] *)
        layout.Drop]

    | rwasm.IVariantCase ann q th ta tl es => mthrow todo

    (* [val__init; len] → [ptr] *)
    (* [τ      ; i32] → [i32] *)
    | rwasm.IArrayMalloc ann q => mthrow todo

    (* [ptr; idx] → [ptr; val] *)
    (* [i32; i32] → [i32; τ  ] *)
    | rwasm.IArrayGet ann => mthrow todo

    (* [ptr; idx; val] → [ptr] *)
    (* [i32; i32; τ  ] → [i32] *)
    | rwasm.IArraySet ann => mthrow todo

    (* [ptr] → [] *)
    (* [i32] → [] *)
    | rwasm.IArrayFree ann => mret [layout.Free]

    (* TODO: *)
    (* [ ] → [   ] *)
    (* [τ] → [i32] *)
    | rwasm.IExistPack ann t th q => mthrow todo

    (* TODO: *)
    (* GC: *)
    (*   [      ] → [   ;  ] *)
    (*   [τ; i32] → [i32; τ] *)
    (* LIN: *)
    (*   [      ] → [   ] *)
    (*   [τ; i32] → [i32] *)
    | rwasm.IExistUnpack ann q th ta tl es => mthrow todo

    | rwasm.IRefSplit _
    | rwasm.IRefJoin _
    | rwasm.IQualify _ _ => mret []
    end.
  End Instrs.

  Definition resolve_locals_layout_shape (sz__s : list rwasm.Size) (instrs : list (rwasm.instr rwasm.ArrowType)) : M (list LayoutShape) :=
    (* TODO: need to see what type the first local.store is, and use that. otherwise fallback to a sequence of i64s *)
    mthrow todo.

  Definition compile_func (func : rwasm.Func rwasm.ArrowType) : M layout.Func :=
    let 'rwasm.Fun ex__s χ sz__s e__s := func in
    let 'rwasm.FunT κ ta := χ in
    (* let 'rwasm.Arrow τ__from τ__to := tf in  *)
    '(layout.Arrow shape__from shape__to) ← compile_ta (* ∅ *) ta;      (* FIXME: previous stage should ensure this doesn't contain TVar *)
    let loc_params := omap (fun k => match k with
      | rwasm.SIZE sz__upper sz__lower => Some LS_int32
      | rwasm.LOC _ | rwasm.QUAL _ _ | rwasm.TYPE _ _ _ => None end) κ in

    locals ← resolve_locals_layout_shape sz__s e__s;
    let num_rwasm_params := length shape__from in

    let sz_locals := map_seq num_rwasm_params (seq 0 num_rwasm_params) in
    let idx_transformer i := if Nat.ltb i num_rwasm_params then i + num_rwasm_params else i in

    e__s' ← flat_mapM (compile_instr sz_locals idx_transformer (* ∅ *)) e__s;

    mret $ layout.Fun ex__s (layout.Arrow (shape__from ++ loc_params) shape__to) locals e__s'.

  Definition compile_global (global : rwasm.Glob rwasm.ArrowType) : M (option layout.Glob).
  Admitted.                     (* FIXME: what to do about 0 sized types? *)
    (* match global with *)
    (* | boxed.GlobMut τ i__s => mret $ layout.GlobMut (boxed_type_to_shape τ) (compile_instr i__s) *)
    (* | boxed.GlobEx ex__s τ i__s => mret $ layout.GlobEx ex__s (boxed_type_to_shape τ) (compile_instr i__s) *)
    (* | boxed.GlobIm ex__s τ im =>  mret $ layout.GlobEx ex__s (boxed_type_to_shape τ) im  *)
    (* end. *)

  Definition compile_module (module : rwasm.module rwasm.ArrowType) : M layout.module :=
    let '(functions, globals, table) := module in
    mthrow todo.

End RWasmToLayout.

Module LayoutToWasm.
  Import LayoutIR.
  Import numbers monads.

  Inductive LocalShape :=
  | LS_orig (shape : shape)
  | LS_updated (orignal_shape : shape) (expected_shape : shape).

  Definition effective_current_local_shape (local_shape : LocalShape) :=
    match local_shape with
    | LS_orig shape => shape
    | LS_updated orignal_shape expected_shape => expected_shape
    end.

  Record TypeEnv := {
    te_locals  : gmap nat LocalShape;
    te_globals : gmap nat (shape * bool); (* TODO: this assumes that globals can't get strong updates, is this correct? *)
    (* TODO: this might need to keep track of tables too *)
    te_stack   : list shape
  }.

  Definition te_push (s : LayoutShape) (Γ : TypeEnv) : TypeEnv :=
    {| te_locals := Γ.(te_locals);
       te_globals := Γ.(te_globals);
       te_stack := s :: Γ.(te_stack) |}.

  Definition te_pop (Γ : TypeEnv) : option (LayoutShape * TypeEnv) :=
    match Γ.(te_stack) with
    | [] => None
    | s :: stk' =>
      Some (s, {| te_locals := Γ.(te_locals);
                  te_globals := Γ.(te_globals);
                  te_stack := stk' |})
    end.

  Definition te_peek (Γ : TypeEnv) : option LayoutShape :=
    match Γ.(te_stack) with
    | [] => None
    | s :: stk' => Some s
    end.

  Definition te_pop_i32 (prefix : string) (Γ : TypeEnv) : M TypeEnv :=
    '(shape, Γ') ← lift_optionM (te_pop Γ) (prefix ++ "expected non-empty stack");
    _ ← match shape with
    | LS_int32 => mret ()
    | _ => mthrow (err (prefix ++ "expected i32 at TOS but got " ++ (pretty shape)))
    end;
    mret Γ'.

  Definition te_set_local (idx : nat) (shape : shape) (Γ : TypeEnv) : M TypeEnv :=
    local ← lift_optionM (Γ.(te_locals) !! idx) ("ICE: cannot find local with index " ++ (pretty idx));
    let '(needs_update, orig) := match local with
    | LS_orig orig_shape => ((compatible_shapes shape orig_shape), orig_shape)
    | LS_updated orig_shape _ => (true, orig_shape)
    end in
    let new_local := if needs_update then
       LS_updated orig shape
    else
       LS_orig orig in
    mret {| te_locals := <[idx := new_local]> Γ.(te_locals);
            te_globals := Γ.(te_globals);
            te_stack := Γ.(te_stack) |}.

  Definition either_layout_num (sz : LayoutPrimSize) (lt : LayoutPrimType) :=
    match lt with
    | LT_int => layout_int_from_sz sz
    | LT_float => layout_float_from_sz sz
    end.

  Definition either_single (sz : LayoutPrimSize) (l : list LayoutPrimType) :=
    map (either_layout_num sz) l.

  Definition either_n (sz : LayoutPrimSize) (ls : (list LayoutPrimType) * (list LayoutPrimType))
        : (list LayoutShape) * (list LayoutShape) :=
    let '(l1, l2) := ls in
    ((map (either_layout_num sz) l1), (map (either_layout_num sz) l2)).

  Definition rwasm_i_to_layout_prim (i : rwasm.IntType) :=
    match i with
    | rwasm.i32 => LS_int32
    | rwasm.i64 => LS_int64
    end.
  Definition rwasm_f_to_layout_prim (f : rwasm.FloatType) :=
    match f with
    | rwasm.f32 => LS_float32
    | rwasm.f64 => LS_float64
    end.

  Definition apply_ta (ta : ArrowShape) (Γ : TypeEnv) : M TypeEnv :=
    let 'Arrow shapes__in shapes__out := ta in
    Γ1 ← foldlM (fun (shape : LayoutShape) (acc : TypeEnv) =>
          '(shape', acc') ← lift_optionM (te_pop acc) "expected non-empty stack when applying arrow shape";
          match decide (shape = shape') with
          | left _ => mret acc'
          | right _ => mthrow (err ("Based on arrow shape, expected " ++ (pretty shape) ++ " but got " ++ (pretty shape') ++ " at TOS."))
          end) Γ shapes__in;
    Γ2 ← mret $ foldl' te_push Γ1 shapes__out;
    mret Γ2.

  Definition apply_tl (tl : LocalEffect) (Γ : TypeEnv) : M TypeEnv :=
    Γ' ← foldlM (fun '(idx, shape) (acc : TypeEnv) => te_set_local idx shape acc) Γ tl;
    mret Γ'.

  Fixpoint type_instr (instr : Instruction) (Γ : TypeEnv) : M TypeEnv :=
    match instr with
    | Val v => mret $ te_push (layout_value_to_shape v) Γ
    | Ne ni =>
      let szi := layout_size_of_int in
      let szf := layout_size_of_float in
      let lsi := rwasm_i_to_layout_prim in
      let lsf := rwasm_f_to_layout_prim in
      let '(tin, tout) := match ni with
      | rwasm.Iu i _ => either_n (szi i) ([LT_int], [LT_int])
      | rwasm.Ib i _ => either_n (szi i) ([LT_int; LT_int], [LT_int])
      | rwasm.Fu f _ => either_n (szf f) ([LT_float], [LT_float])
      | rwasm.Fb f _ => either_n (szf f) ([LT_float; LT_float], [LT_float])
      | rwasm.It i _ => either_n (szi i) ([LT_int], [LT_int])
      | rwasm.Ir i _ => (either_single (szi i) [LT_int; LT_int], [LS_int32])
      | rwasm.Fr f _ => (either_single (szf f) [LT_float; LT_float], [LS_int32])
      | rwasm.CvtI i1 op =>
        match op with
        | rwasm.Wrap i2 => ([lsi i2], [lsi i1])
        | rwasm.Extend i2 _ => ([lsi i2], [lsi i1])
        | rwasm.Trunc f2 _ => ([lsf f2], [lsi i1])
        | rwasm.TruncSat f2 _ =>([lsf f2], [lsi i1])
        | rwasm.Convert i2 _ => ([lsi i2], [lsi i1])
        | rwasm.Demote f2 => ([lsf f2], [lsi i1])
        | rwasm.Promote f2 => ([lsf f2], [lsi i1])
        | rwasm.Reinterpret i2 => ([lsi i2], [lsi i1])
        (* FIXME: missing reinterpret for floats *)
        end
      | rwasm.CvtF f1 op =>
        match op with
        | rwasm.Wrap i2 => ([lsi i2], [lsf f1])
        | rwasm.Extend i2 _ => ([lsi i2], [lsf f1])
        | rwasm.Trunc f2 _ => ([lsf f2], [lsf f1])
        | rwasm.TruncSat f2 _ =>([lsf f2], [lsf f1])
        | rwasm.Convert i2 _ => ([lsi i2], [lsf f1])
        | rwasm.Demote f2 => ([lsf f2], [lsf f1])
        | rwasm.Promote f2 => ([lsf f2], [lsf f1])
        | rwasm.Reinterpret i2 => ([lsi i2], [lsf f1])
        end
      end in

      Γ1 ← foldlM (fun (shape : LayoutShape) (acc : TypeEnv) =>
             '(shape', acc') ← lift_optionM (te_pop acc) "expected non-empty stack";
             match decide (shape = shape') with
             | left _ => mret acc'
             | right _ => mthrow (err ("Expected " ++ (pretty shape) ++ " but got " ++ (pretty shape') ++ " at TOS."))
             end) Γ tin;
      Γ2 ← mret $ foldl' te_push Γ1 tout;
      mret Γ2
    | Unreachable => mret Γ
    | Nop => mret Γ
    | Drop =>
      '(shape, Γ') ← lift_optionM (te_pop Γ) "Drop: expected non-empty stack";
      mret Γ'
    | Select =>
      Γ1 ← te_pop_i32 "Select1: " Γ;
      '(shape2, Γ2) ← lift_optionM (te_pop Γ1) "Select: expected non-empty stack 2";
      '(shape3, Γ3) ← lift_optionM (te_pop Γ2) "Select: expected non-empty stack 3";
      Γ4 ← match decide (shape2 = shape3) with
      | left _ => mret (te_push shape2 Γ3)
      | right _ => mthrow (err ("Expected equal shapes for select but got " ++ (pretty shape2) ++ " and " ++ (pretty shape3) ++ "."))
      end;
      mret Γ3
    | Block ta tl e__s =>
      (* TODO: validate that ta and tl are correct? *)
      Γ__arrow ← apply_ta ta Γ;
      Γ__locals ← apply_tl tl Γ__arrow;
      mret Γ__locals
    | Loop ta e__s =>
      (* TODO: validate that tf is correct? *)
      Γ' ← apply_ta ta Γ;
      mret Γ'
    | ITE ta tl e__thn e__els =>
      (* TODO: validate that tf and le are correct? *)
      Γ__arrow ← apply_ta ta Γ;
      Γ__locals ← apply_tl tl Γ__arrow;
      mret Γ__locals
    | Br i=> mthrow (err "TODO: deal with labels")
    | BrIf i=> mthrow (err "TODO: deal with labels")
    | BrTable i__s j => mthrow (err "TODO: deal with labels")
    | Ret => mthrow todo
    | GetLocal i =>
      local ← lift_optionM (Γ.(te_locals) !! i) ("expected rwasn local at index " ++ (pretty i));
      shape ← mret $ effective_current_local_shape local;
      Γ' ← mret $ te_push shape Γ;
      mret Γ'
    | SetLocal i =>
      '(shape, Γ1) ← lift_optionM (te_pop Γ) ("cannot set local with nothing on TOS");
      Γ2 ← te_set_local i shape Γ1;
      mret Γ2
    | TeeLocal i =>
      shape ← lift_optionM (te_peek Γ) "cannot tee local with nothing on TOS";
      Γ' ← te_set_local i shape Γ;
      mret Γ'
    | GetGlobal i =>
      '(shape, mut) ← lift_optionM (Γ.(te_globals) !! i) ("expected global at index " ++ (pretty i));
      Γ' ← mret $ te_push shape Γ;
      mret Γ'
    (* | SetGlobal i => _ *)
    (* | CallIndirect tf => _ *)
    (* | Call i => _ *)
    (* | LoadOffset shape => _ *)
    (* | StoreOffset shape => *)

    (* | SwapOffset offset => _ *)
    | Malloc =>
      Γ1 ← te_pop_i32 "Malloc: " Γ;
      Γ2 ← mret $ te_push LS_int32 Γ1;
      mret Γ2
    | Free =>
      Γ' ← te_pop_i32 "Free: " Γ;
      mret Γ'
    | _ => mthrow todo
    end.

  (* FIXME: why can't you both export and be mutable? the RWASM paper implies you can *)
  Definition shape_of_glob (glob : Glob) : (shape * bool) :=
    match glob with
    | GlobMut shape i__s => (shape, true)
    | GlobEx ex__s shape i__s => (shape, false)
    | GlobIm ex__s shape im => (shape, false)
    end.

  Definition translate_function_type (tf : ArrowShape) : wasm.function_type :=
    match tf with
    | Arrow s1 s2 =>
       let s1' := flat_map shape_to_wasm_types s1 in
       let s2' := flat_map shape_to_wasm_types s2 in
       wasm.Tf s1' s2'
    end.

  Section Instrs.
    Variable (MEM_GC: wasm.immediate).
    Variable (MEM_LIN: wasm.immediate).
    Variable (FUNC_MALLOC: wasm.immediate).
    Variable (FUNC_FREE: wasm.immediate).

    Variable function_types : list wasm.function_type.

    Fixpoint compile_val (value : LayoutValue) : list wasm.value :=
      match value with
      | LV_unit => []
      | LV_int32 i => [compile_num_from_Z wasm.T_i32 (Z.of_nat i)]
      | LV_int64 i => [compile_num_from_Z wasm.T_i64 (Z.of_nat i)]
      | LV_float32 f => [compile_num_from_Z wasm.T_f32 (Z.of_nat f)]
      | LV_float64 f => [compile_num_from_Z wasm.T_f64 (Z.of_nat f)]
      | LV_tuple fields => flat_map compile_val fields
      end.

    Definition lift_peek (Γ : TypeEnv) (msg : string) : InstM shape :=
      liftM $ lift_optionM (te_peek Γ) msg.

    Definition peek_ensure_i32 (Γ : TypeEnv) (prefix : string) : InstM shape :=
      shape ← lift_peek Γ (prefix ++ "expected i32 to be on stack but is typed as empty");
      _ ← match shape with
      | LS_int32 => mret ()
      | _ => mthrow (err (prefix ++  "expected i32 at TOS but got " ++ (pretty shape)))
      end;
      mret shape.

    Definition compile_instr (instr : Instruction) (Γ : TypeEnv) : InstM (list wasm.basic_instruction) :=
      match instr with
      | Val v =>
        let wasm_vals := compile_val v in
        mret $ map wasm.BI_const wasm_vals
      | Ne ni =>
        instr ← liftM (compile_num_intr ni);
        mret [instr]
      | Unreachable => mret [wasm.BI_unreachable]
      | Nop => mret [wasm.BI_nop]
      | Drop =>
        shape ← lift_peek Γ "expected element to drop";
        wasm_stack ← mret $ shape_to_wasm_stack shape;
        mret $ map (fun _ => wasm.BI_drop) wasm_stack
      | Select =>
        shape ← lift_peek Γ "expected element to select";

        mthrow todo
      | Block ta le e__s => mthrow todo
      | Loop ta e => mthrow todo
      | ITE tf le e__thn e__els => mthrow todo
      | Br i => mthrow todo
      | BrIf i => mthrow todo
      | BrTable i__s j => mthrow todo
      | Ret => mret [wasm.BI_return]
      | GetLocal i => mthrow todo
      | SetLocal i => mthrow todo
      | TeeLocal i => mthrow todo
      | GetGlobal i => mthrow todo
      | SetGlobal i => mthrow todo
      | CallIndirect ta => mret [wasm.BI_call_indirect 0] (* FIXME: what immediate is supposed to go here? is it the index of the ta?*)
      | Call i => mret [wasm.BI_call i]
      | LoadOffset offset => mthrow todo
      | StoreOffset offset => mthrow todo
      | SwapOffset offset => mthrow todo
      | Malloc =>
        _ ← peek_ensure_i32 Γ "Malloc: ";
        mret $ [wasm.BI_call FUNC_MALLOC]
      | Free =>
        _ ← peek_ensure_i32 Γ "Free: ";
        mret $ [wasm.BI_call FUNC_FREE]
      | _ => mthrow todo
      end.


    Definition compile_function_types (tf : ArrowShape) (function_types : list wasm.function_type)
      : list wasm.function_type :=

    let function_type := translate_function_type tf in
    add_if_not_in function_type function_types.

    Definition collect_function_types (function : Func) (function_types : list wasm.function_type) :=
      let '(Fun ex__s tf locals e__s) := function in
      compile_function_types tf function_types.


    Record FunctionContext := {
      fc_function_types : gmap wasm.function_type nat;
      fc_globals : gmap nat (shape * bool);
      fc_globals_layout : gmap nat nat; (* from rwasm idx to first wasm idx *)
      fc_module_idx : nat;
    }.

    Definition compile_function (ctx : FunctionContext) (function : Func) : M wasm.module_func :=
      match function with
      | Fun ex__s tf locals e__s =>
        let tf' := translate_function_type tf in
        typ_idx ← lift_optionM (ctx.(fc_function_types) !! tf') "ICE: not corresponding ft index";
        let Γ__orig := {|
          te_locals  := ∅; (* FIXME: compile locals *)
          te_globals := ctx.(fc_globals);
          te_stack := []
        |} in
        let instrs_m := foldlM (fun instr '(instrs, Γ) =>
            Γ' ← liftM $ type_instr instr Γ;
            instrs' ← compile_instr instr Γ;     (* NOTE: we use the previous type env *)
            mret (instrs ++ instrs', Γ')) ([], Γ__orig) e__s in
        let init_tl := new_tl 0 in
        '(tl, (body, _)) ← instrs_m init_tl;
        let locals := map snd (map_to_list (tl_types tl)) in

        mret {|
          wasm.modfunc_type := wasm.Mk_typeidx typ_idx;
          wasm.modfunc_locals := locals;
          wasm.modfunc_body := body
        |}
      end.

  End Instrs.

  (* TODO: deal with exports *)
  (* Definition compile_glob (glob : Glob) : wasm.global :=  *)
  (*   let '(mutable, ) match glob with *)
  (*   | GlobMut shape i__s => _ *)
  (*   | GlobEx ex__s shape i__s => _ *)
  (*   | GlobIm ex__s shape im => _ *)
  (*   end  *)

  Section Mod.

    Variable (mod_idx : nat).

    Definition compile_module (module : module) : M wasm.module :=
      let 'Build_module functions globals table := module in
      let function_types := foldl' collect_function_types [] functions in
      let ctx := {|
        fc_function_types := invert_map (map_seq 0 function_types);
        fc_globals := map_seq 0 (map shape_of_glob globals);
        fc_globals_layout := ∅;         (* FIXME *)
        fc_module_idx := mod_idx;
      |} in

      let func_malloc := 0 in
      let func_free := 1 in

      functions' ← mapM (compile_function func_malloc func_free ctx) functions;

      mret {|
        wasm.mod_types := function_types;
        wasm.mod_funcs := functions';
        wasm.mod_tables := []; (* TODO *)
        wasm.mod_mems := [
          {| wasm.lim_min := 0%N; wasm.lim_max := None |}; (* gc mem *)
          {| wasm.lim_min := 0%N; wasm.lim_max := None |}  (* lin mem *)
        ];
        wasm.mod_globals := []; (* TODO *)
        wasm.mod_elem := []; (* TODO *)
        wasm.mod_data := []; (* TODO *)
        wasm.mod_start := None;
        wasm.mod_imports := []; (* TODO *)
        wasm.mod_exports := [] (* TODO *)
      |}.

  End Mod.

End LayoutToWasm.
