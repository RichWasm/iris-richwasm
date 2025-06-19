From Coq Require Import List NArith.BinNat Lists.List.
From stdpp Require Import base option strings list pretty decidable gmap.
From Wasm Require datatypes.
From RWasm Require term annotated_term.
From RWasm.compiler Require Import numbers monads.

Module BoxPolymorphicIR.

  Inductive Typ :=
  | Num (nτ : rwasm.NumType)
  | BoxedT (τ : Typ)
  | TVar (α : rwasm.var) (* must be boxed *)
  | Unit
  | ProdT (τ__s : list Typ)
  | CoderefT (χ : FunType)
  | Rec (q : rwasm.Qual) (τ : Typ) (* binding site *)
  | PtrT (ℓ : rwasm.Loc)
  | ExLoc (q : rwasm.Qual) (τ : Typ) (* binding site *)
  | OwnR (ℓ : rwasm.Loc)
  | CapT (cap : rwasm.cap) (ℓ : rwasm.Loc) (ψ : HeapType)
  | RefT (cap : rwasm.cap) (ℓ : rwasm.Loc) (ψ : HeapType)

  with HeapType :=
  | VariantType (τ__s : list Typ)
  | StructType (fields : list (Typ * rwasm.Size))
  | ArrayType (τ : Typ)
  | Ex (sz : rwasm.Size) (q : rwasm.Qual) (τ : Typ) (* binding site *)

  with ArrowType :=
  | Arrow (τ__s1 : list Typ) (τ__s2 : list Typ)

  with FunType :=
  | FunT (κ : list rwasm.KindVar) (tf : ArrowType).

  Definition LocalEffect := list (nat * Typ).

  Inductive Value :=
  | NumConst (nτ : rwasm.NumType) (val : nat)
  | Tt (* Unit value *)
  | Coderef (module_index : nat) (table_index : nat) (z__s : list rwasm.Index)
  | Fold (v : Value)
  | Prod (v__s : list Value)
  | Ref (ℓ : rwasm.Loc)
  | PtrV (ℓ : rwasm.Loc)
  | Cap
  | Own
  | Mempack (ℓ : rwasm.Loc) (v : Value)
  (* boxed polymorphic value *)
  | Boxed (v : Value).


  Inductive Instruction :=
  | Instr (pre : PreInstruction) (tf : ArrowType)
  with PreInstruction :=
  (* Values are instructions *)
  | Val (v : Value)
  | Ne (ni : rwasm.NumInstr)
  | Unreachable
  | Nop
  | Drop
  | Select
  | Block (tf : ArrowType) (le : LocalEffect) (e__s : list Instruction)
  | Loop (tf : ArrowType) (e__s : list Instruction)
  | ITE (tf : ArrowType) (le : LocalEffect) (e__thn : list Instruction) (e__els : list Instruction)
  | Br (i : nat)
  | Br_if (i : nat)
  | Br_table (i__s : list nat) (j : nat)
  | Ret
  | Get_local (i : nat) (q : rwasm.Qual)
  | Set_local (i : nat)
  | Tee_local (i : nat)
  | Get_global (i : nat)
  | Set_global (i : nat)
  | CoderefI (i : nat)
  | Inst (z__s : list rwasm.Index)
  | Call_indirect
  | Call (i : nat) (z__s : list rwasm.Index)
  (* Rec *)
  | RecFold (τ : Typ)
  | RecUnfold
  (* Seq *)
  | Group (i : nat) (q : rwasm.Qual)
  | Ungroup
  (* Cap Instructions *)
  | CapSplit
  | CapJoin
  | RefDemote
  | MemPack (ℓ : rwasm.Loc) (* XXX Loc or not? *)
  | MemUnpack (tf : ArrowType) (le : LocalEffect) (e__s : list Instruction) (* binding site *)
  (* Struct Instructions *)
  | StructMalloc (sz__s : list rwasm.Size) (q : rwasm.Qual)
  | StructFree
  | StructGet (i : nat)
  | StructSet (i : nat)
  | StructSwap (i : nat)
  (* Variant Instructions *)
  | VariantMalloc (i : nat) (τ__s : list Typ) (q : rwasm.Qual)
  | VariantCase (q : rwasm.Qual) (ψ : HeapType) (tf : ArrowType) (le : LocalEffect) (e__ss : list (list Instruction))
  (* Array Instructions *)
  | ArrayMalloc (q : rwasm.Qual)
  | ArrayGet
  | ArraySet
  | ArrayFree
  (* Existsential Instructions *)
  | ExistPack (τ : Typ) (ψ : HeapType) (q : rwasm.Qual)
  | ExistUnpack (q : rwasm.Qual) (ψ : HeapType) (tf : ArrowType) (le : LocalEffect) (e__s : list Instruction)
  (* Ref operations *)
  | RefSplit
  | RefJoin
  | Qualify (q : rwasm.Qual).
  (* Administrative Instructions *)
  (* | Trap *)
  (* | CallAdm : Closure -> list rwasm.Index -> PreInstruction *)
  (* | Label : nat -> ArrowType -> list Instruction -> list Instruction -> PreInstruction *)
  (* | Local : nat -> nat -> list Value -> list nat (* sizes of local slots (args + locals) *) -> list Instruction -> PreInstruction *)
  (* | Malloc : Size -> HeapValue -> Qual -> PreInstruction *)
  (* | Free *)
  (* withFunc := *)
  (* | Fun : list wasm.ex -> FunType -> list Size -> list Instruction -> Func *)
  (* with Closure := *)
  (* | Clo : nat -> Func -> Closure. *)

  Fixpoint compile_val (val : rwasm.Value) : Value :=
   match val with
   | rwasm.NumConst nτ val => NumConst nτ val
   | rwasm.Tt => Tt
   | rwasm.Coderef module_index table_index z__s => Coderef module_index table_index z__s
   | rwasm.Fold v => Fold (compile_val v)
   | rwasm.Prod v__s => Prod (map compile_val v__s)
   | rwasm.Ref ℓ => Ref ℓ
   | rwasm.PtrV ℓ => PtrV ℓ
   | rwasm.Cap => Cap
   | rwasm.Own => Own
   | rwasm.Mempack ℓ v => Mempack ℓ (compile_val v)
   end.

  Fixpoint compile_arrow (tf : rwasm.ArrowType) : M ArrowType :=
   match tf with
   | rwasm.Arrow τ__s1 τ__s2 => mthrow (err "TODO")
   end.

  Fixpoint compile_instruction (instr : AR.Instruction) : M Instruction :=
    match instr with
    | AR.Instr pre tf =>
        pre' ← compile_pre_instruction pre;
        tf' ← compile_arrow tf;
        mret $ Instr pre' tf'
    end
  with compile_pre_instruction (pre : AR.PreInstruction) : M PreInstruction :=
    match pre with
    | AR.Val v => mthrow (err "TODO")
    | AR.Ne ni => mthrow (err "TODO")
    | AR.Unreachable => mthrow (err "TODO")
    | AR.Nop => mthrow (err "TODO")
    | AR.Drop => mthrow (err "TODO")
    | AR.Select => mthrow (err "TODO")
    | AR.Block tf le e__s => mthrow (err "TODO")
    | AR.Loop tf e => mthrow (err "TODO")
    | AR.ITE tf le e__thn e__els => mthrow (err "TODO")
    | AR.Br i => mthrow (err "TODO")
    | AR.Br_if i => mthrow (err "TODO")
    | AR.Br_table i__s j => mthrow (err "TODO")
    | AR.Ret => mthrow (err "TODO")
    | AR.Get_local i q => mthrow (err "TODO")
    | AR.Set_local i => mthrow (err "TODO")
    | AR.Tee_local i => mthrow (err "TODO")
    | AR.Get_global i => mthrow (err "TODO")
    | AR.Set_global i => mthrow (err "TODO")
    | AR.CoderefI i => mthrow (err "TODO")
    | AR.Inst z__s => mthrow (err "TODO")
    | AR.Call_indirect => mthrow (err "TODO")
    | AR.Call i z__s => mthrow (err "TODO")
    | AR.RecFold τ => mthrow (err "TODO")
    | AR.RecUnfold => mthrow (err "TODO")
    | AR.Group i q => mthrow (err "TODO")
    | AR.Ungroup => mthrow (err "TODO")
    | AR.CapSplit => mthrow (err "TODO")
    | AR.CapJoin => mthrow (err "TODO")
    | AR.RefDemote => mthrow (err "TODO")
    | AR.MemPack ℓ => mthrow (err "TODO")
    | AR.MemUnpack tf le e__s => mthrow (err "TODO")
    | AR.StructMalloc sz__s q => mthrow (err "TODO")
    | AR.StructFree => mthrow (err "TODO")
    | AR.StructGet i => mthrow (err "TODO")
    | AR.StructSet i => mthrow (err "TODO")
    | AR.StructSwap i => mthrow (err "TODO")
    | AR.VariantMalloc i τ__s q => mthrow (err "TODO")
    | AR.VariantCase q ψ tf le e__ss => mthrow (err "TODO")
    | AR.ArrayMalloc q => mthrow (err "TODO")
    | AR.ArrayGet => mthrow (err "TODO")
    | AR.ArraySet => mthrow (err "TODO")
    | AR.ArrayFree => mthrow (err "TODO")
    | AR.ExistPack τ ψ q => mthrow (err "TODO")
    | AR.ExistUnpack q ψ tf le e__s => mthrow (err "TODO")
    | AR.RefSplit => mthrow (err "TODO")
    | AR.RefJoin => mthrow (err "TODO")
    | AR.Qualify q => mthrow (err "TODO")
    | AR.Trap
    | AR.CallAdm _ _
    | AR.Label _ _ _ _
    | AR.Local _ _ _ _ _
    | AR.Malloc _ _ _
    | AR.Free => mthrow (err "unexpected admin instr")
    end.
End BoxPolymorphicIR.

Module LayoutIR.

  From RWasm.compiler Require Export layout.
  Definition shape := LayoutShape.
  Definition value := LayoutValue.

  Inductive ArrowShape :=
  | Arrow (shapes1 : list shape) (shapes2 : list shape).

  Definition LocalEffect := list (nat * shape).

  (* TODO: need to see if this is actually enough to stop worrying about annotated types *)
  Inductive Instruction :=
  | Const (v : value)
  | Ne (ni : rwasm.NumInstr)

  | Unreachable
  | Nop
  | Drop
  | Select
  | Block (tf : ArrowShape) (le : LocalEffect) (e__s : list Instruction)
  | Loop (tf : ArrowShape) (e : list Instruction)
  | ITE (tf : ArrowShape) (le : LocalEffect) (e__thn : list Instruction) (e__els : list Instruction)
  | Br (i : nat)
  | Br_if (i : nat)
  | Br_table (i__s : list nat) (j : nat)
  | Ret

  | GetLocal (i : nat)
  | SetLocal (i : nat)
  | TeeLocal (i : nat)
  | GetGlobal (i : nat)
  | SetGlobal (i : nat)

  | CallIndirect (tf : ArrowShape)        (* TODO: is this correct? *)
  | Call (i : nat)

  | LoadOffset (offset : nat)
  | StoreOffset (offset : nat) (* takes ptr from tos, then loads shape from below it *)
  | SwapOffset (offset : nat)
  | Malloc (shape : shape)
  | Free

  | VariantCase (q : rwasm.Qual) (ψ : rwasm.HeapType) (tf : ArrowShape) (le : LocalEffect) (e__ss : list (list Instruction)) (* FIXME *)
  with Func :=
  | Fun (ex__s : list rwasm.ex) (tf : ArrowShape) (e__s : list Instruction).

  Inductive Glob :=
  | GlobMut (shape : shape) (i__s : list Instruction)
  | GlobEx (ex__s : list rwasm.ex) (shape : shape) (i__s : list Instruction)
  | GlobIm (ex__s : list rwasm.ex) (shape : shape) (im : rwasm.im).

  Record module := {
    functions : list Func;
    globals : list Glob;
    table : rwasm.Table
  }.

  Record TypeEnv := {
    te_locals  : gmap nat shape;
    te_globals : gmap nat (bool * shape);
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

  Definition apply_tf (tf : ArrowShape) (Γ : TypeEnv) : M TypeEnv :=
    let 'Arrow shapes__in shapes__out := tf in
    Γ1 ← foldlM (fun (shape : LayoutShape) (acc : TypeEnv) =>
          '(shape', acc') ← lift_optionM (te_pop acc) "expected non-empty stack when applying arrow shape";
          match decide (shape = shape') with
          | left _ => mret acc'
          | right _ => mthrow (err ("Based on arrow shape, expected " ++ (pretty shape) ++ " but got " ++ (pretty shape') ++ " at TOS."))
          end) Γ shapes__in;
    Γ2 ← mret $ foldl' te_push Γ1 shapes__out;
    mret Γ2.

  Fixpoint type_instr (instr : Instruction) (Γ : TypeEnv) : M TypeEnv :=
    match instr with
    | Const v => mret $ te_push (layout_value_to_shape v) Γ
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
      '(shape1, Γ1) ← lift_optionM (te_pop Γ) "Select: expected non-empty stack 1";
      '(shape2, Γ2) ← lift_optionM (te_pop Γ1) "Select: expected non-empty stack 2";
      '(shape3, Γ3) ← lift_optionM (te_pop Γ2) "Select: expected non-empty stack 3";
      _ ← match shape1 with
      | LS_int32 => mret ()
      | _ => mthrow (err ("Select expected i32 at TOS but got " ++ (pretty shape1)))
      end;
      Γ4 ← match decide (shape2 = shape3) with
      | left _ => mret (te_push shape2 Γ3)
      | right _ => mthrow (err ("Expected equal shapes for select but got " ++ (pretty shape2) ++ " and " ++ (pretty shape3) ++ "."))
      end;
      mret Γ3
    | Block tf le e__s =>
      (* TODO: validate that tf and le are correct? *)
      Γ__arrow ← apply_tf tf Γ;
      Γ__locals ← apply_le le Γ__arrow;
      mret Γ__locals
    | Loop tf e__s =>
      (* TODO: validate that tf is correct? *)
      Γ' ← apply_tf tf Γ;
      mret Γ'
    | ITE tf le e__thn e__els =>
      (* TODO: validate that tf and le are correct? *)
      Γ__arrow ← apply_tf tf Γ;
      Γ__locals ← apply_le le Γ__arrow;
      mret Γ__locals
    | Br i
    | Br_if i
    | Br_table i__s j => mthrow (err "TODO: deal with labels")
    | Ret => mthrow (err "TODO:")
    (* | GetLocal i => _ *)
    (* | SetLocal i => _ *)
    (* | TeeLocal i => _ *)
    (* | GetGlobal i => _ *)
    (* | SetGlobal i => _ *)
    (* | CallIndirect tf => _ *)
    (* | Call i => _ *)
    (* | LoadOffset offset => _ *)
    (* | StoreOffset offset => _ *)
    (* | SwapOffset offset => _ *)
    (* | Malloc shape => _ *)
    (* | Free => _ *)
    | VariantCase q ψ tf le e__ss => mthrow (err "NEEDED?")
    | _ => mthrow (err "TODO")   (*  *)
   end.


End LayoutIR.

Section AddIfNotIn.
  Context `{EqDecision A}.

  Fixpoint add_if_not_in (x : A) (l : list A) : list A :=
    if bool_decide (x ∈ l) then l else x :: l.
End AddIfNotIn.

Module LayoutToWasm.
  Import LayoutIR.
  From RWasm.compiler Require Import numbers monads.

  Definition translate_function_type (tf : ArrowShape) : wasm.function_type :=
    match tf with
    | Arrow s1 s2 =>
       let s1' := flat_map shape_to_wasm_types s1 in
       let s2' := flat_map shape_to_wasm_types s2 in
       wasm.Tf s1' s2'
    end.

  Section Instrs.

    Variable function_types : list wasm.function_type.

    Fixpoint compile_val (value : LayoutValue) : list wasm.value :=
      match value with
      | LV_int32 i => [compile_num_from_Z wasm.T_i32 (Z.of_nat i)]
      | LV_int64 i => [compile_num_from_Z wasm.T_i64 (Z.of_nat i)]
      | LV_float32 f => [compile_num_from_Z wasm.T_f32 (Z.of_nat f)]
      | LV_float64 f => [compile_num_from_Z wasm.T_f64 (Z.of_nat f)]
      | LV_tuple fields => flat_map compile_val fields
      end.

    Definition compile_instr (instr : Instruction) (Γ : TypeEnv) : InstM (list wasm.basic_instruction) :=
      match instr with
      | Const v =>
          let wasm_vals := compile_val v in
          mret $ map wasm.BI_const wasm_vals
      | Ne ni =>
          instr ← liftM (compile_num_intr ni);
          mret [instr]
      | Unreachable => mret [wasm.BI_unreachable]
      | Nop => mret [wasm.BI_nop]
      (* | Drop => _ *)
      (* | Select => _ *)
      (* | Block tf le e__s => _ *)
      (* | Loop tf e => _ *)
      (* | ITE tf le e__thn e__els => _ *)
      (* | Br i => _ *)
      (* | Br_if i => _ *)
      (* | Br_table i__s j => _ *)
      (* | Ret => _ *)
      (* | GetLocal i => _ *)
      (* | SetLocal i => _ *)
      (* | TeeLocal i => _ *)
      (* | GetGlobal i => _ *)
      (* | SetGlobal i => _ *)
      (* | CallIndirect tf => _ *)
      (* | Call i => _ *)
      (* | LoadOffset offset => _ *)
      (* | StoreOffset offset => _ *)
      (* | SwapOffset offset => _ *)
      (* | Malloc shape => _ *)
      (* | Free => _ *)
      | VariantCase q ψ tf le e__ss => mthrow (err "TODO: is this needed?")
      | _ => mthrow (err "TODO")
      end.





  End Instrs.


  Definition compile_function_types (tf : ArrowShape) (function_types : list wasm.function_type)
    : list wasm.function_type :=

   let function_type := translate_function_type tf in
   add_if_not_in function_type function_types.

  (* NOTE: could probably turn acculuation of function types into a monad but likely not worth it. *)
  Definition compile_function (function : Func) (function_types : list wasm.function_type)
    : M (list wasm.module_func * wasm.function_type).
  Admitted.

  Definition layout_compile_module (module : module) : M wasm.module :=
    let 'Build_module functions globals table := module in
    '(functions, function_types) ← foldlM ;

    mret {|
        wasm.mod_types := [];
        wasm.mod_funcs := [];
        wasm.mod_tables := []; (* TODO *)
        wasm.mod_mems := []; (* TODO *)
        wasm.mod_globals := []; (* TODO *)
        wasm.mod_elem := []; (* TODO *)
        wasm.mod_data := []; (* TODO *)
        wasm.mod_start := None; (* TODO *)
        wasm.mod_imports := []; (* TODO *)
        wasm.mod_exports := [] (* TODO *)
    |}.

End LayoutToWasm.
