From Coq Require Import List NArith.BinNat Lists.List FSets.FMapInterface.
From stdpp Require Import base option strings list pretty decidable gmap.
From Wasm Require datatypes.
From RWasm Require term annotated_term.
From RWasm.compiler Require Import numbers monads utils layout.

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
  (* IR-specific instructions: box and unbox the i-th value from the top of the stack *)
  | Box (i : nat)
  | Unbox (i : nat)
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
  | Qualify (q : rwasm.Qual)
  (* Administrative Instructions *)
  (* | Trap *)
  (* | CallAdm : Closure -> list rwasm.Index -> PreInstruction *)
  (* | Label : nat -> ArrowType -> list Instruction -> list Instruction -> PreInstruction *)
  (* | Local : nat -> nat -> list Value -> list nat (* sizes of local slots (args + locals) *) -> list Instruction -> PreInstruction *)
  (* | Malloc : Size -> HeapValue -> Qual -> PreInstruction *)
  (* | Free *)
  with Func :=
  | Fun (ex__s : list rwasm.ex) (χ : FunType) (sz__s : list rwasm.Size) (e__s : list Instruction).
  (* with Closure := *)
  (* | Clo : nat -> Func -> Closure. *)

  Inductive Glob :=
  | GlobMut (τ : Typ) (i__s : list Instruction)
  | GlobEx (ex__s : list rwasm.ex) (τ : Typ) (i__s : list Instruction)
  | GlobIm (ex__s : list rwasm.ex) (τ : Typ) (im : rwasm.im).

  Record module := {
    functions : list Func;
    globals : list Glob;
    table : rwasm.Table
  }.

End BoxPolymorphicIR.

Module AnnotatedToBoxed.

  Module ann := AR.
  Module box := BoxPolymorphicIR.

  Import box.

  Fixpoint compile_val (val : rwasm.Value) : box.Value :=
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

  Fixpoint compile_type (should_box : bool) (t : rwasm.Typ) : Typ :=
    match t with
    | rwasm.Num nτ => Num nτ
    | rwasm.TVar α => if should_box then BoxedT (TVar α) else TVar α
    | rwasm.Unit => Unit
    | rwasm.ProdT τ__s => ProdT (map (compile_type should_box) τ__s)
    | rwasm.CoderefT χ => CoderefT (compile_fun should_box χ)
    | rwasm.Rec q τ => Rec q (compile_type should_box τ)
    | rwasm.PtrT ℓ => PtrT ℓ
    | rwasm.ExLoc q τ => ExLoc q (compile_type should_box τ)
    | rwasm.OwnR ℓ => OwnR ℓ
    | rwasm.CapT cap ℓ ψ => CapT cap ℓ (compile_heap should_box ψ)
    | rwasm.RefT cap ℓ ψ => RefT cap ℓ (compile_heap should_box ψ)
    end
  with compile_fun (should_box : bool) (t : rwasm.FunType) : FunType :=
    match t with
    | rwasm.FunT vs arrow => FunT vs (compile_arrow should_box arrow)
    end
  with compile_heap (should_box : bool) (t : rwasm.HeapType) : HeapType :=
    match t with
    | rwasm.VariantType ts => VariantType (map (compile_type should_box) ts)
    | rwasm.StructType ts => StructType (map (fun '(t, s) => (compile_type should_box t, s)) ts)
    | rwasm.ArrayType t => ArrayType (compile_type should_box t)
    | rwasm.Ex sz q t => Ex sz q (compile_type should_box t)
    end
  with compile_arrow (should_box : bool) (tf : rwasm.ArrowType) : ArrowType :=
   match tf with
   | rwasm.Arrow τ__s1 τ__s2 => Arrow (map (compile_type should_box) τ__s1) (map (compile_type should_box) τ__s2)
   end.

  Fixpoint mapi' {A B : Type} (f : A → nat → B) (l : list A) (n : nat) : (list B) :=
    match l with
    | [] => []
    | x :: xs => f x n :: mapi' f xs (S n)
    end.

  Definition mapi {A B : Type} (f : A → nat → B) (l : list A) : list B :=
    mapi' f l 0.

  Fixpoint foldli' {A B : Type} (f : B → A → nat → B) (base : B) (l : list A) (n : nat) : B :=
    match l with
    | [] => base
    | x :: xs => foldli' f (f base x n) xs (S n)
    end.

  Definition foldli {A B : Type} (f : B → A → nat → B) (base : B) (l : list A) : B :=
    foldli' f base l 0.

  Print Instruction.

  Fixpoint compile_instruction (instr : AR.Instruction) : M (list Instruction) :=
    let compile_le := fun '(n, t) => (n, compile_type true t) in
    match instr with
    | AR.Instr pre tf =>
      let tf' := compile_arrow true tf in
      match pre with
      | AR.Val v => mret $ [Instr (Val V) tf']
      | AR.Ne ni => mret $ [Instr (Ne ni) tf']
      | AR.Unreachable => mret $ [Instr (Unreachable) tf']
      | AR.Nop => mret $ [Instr (Nop) tf']
      | AR.Drop => mret $ [Instr (Drop) tf']
      | AR.Select => mret $ [Instr (Select) tf']
      | AR.Block tf le e__s => 
        e__s' ← mapM compile_instruction e__S;
        mret $ [Instr (Block (compile_type true tf) (map compile_le le) e__s') tf']
      | AR.Loop tf e => Loop (compile_type true tf) e
      | AR.ITE tf le e__thn e__els =>
        e__thn' ← mapM compile_instruction e__thn;
        e__els' ← mapM compile_instruction e__els;
        mret $ [Instr (ITE (compile_type true tf) (map compile_le le)) tf']
      | AR.Br i => mret $ [Instr (Br i) tf']
      | AR.Br_if i => mret $ [Instr (Br_if i) tf']
      | AR.Br_table i__s j => mret $ [Instr (Br_table i__s j) tf']
      | AR.Ret => mret $ [Instr (Ret) tf']
      | AR.Get_local i q => mret $ [Instr (Get_local i q) tf']
      | AR.Set_local i => mret $ [Instr (Set_local i) tf']
      | AR.Tee_local i => mret $ [Instr (Tee_local i) tf']
      | AR.Get_global i => mret $ [Instr (Get_global i) tf']
      | AR.Set_global i => mret $ [Instr (Set_global i) tf']
      | AR.CoderefI i => mret $ [Instr (CoderefI i) tf']
      | AR.Inst z__s => mret $ [Instr (Inst z__s) tf']
      | AR.Call_indirect => mthrow (err "TODO")
      | AR.Call i z__s =>
          let for_boxes f :=
            foldli (fun acc t i =>
            match t with
            | BoxedT _ => f i :: acc
            | _ => acc
            end) []
          in
          let type_box pre :=
            match pre with
            (* a, b, ..., i => a, b, ..., BoxedT i *)
            | Box i => mthrow (err "TODO")
            | _ => mthrow (err "expected Box pre-instr")
            end
          in
          let type_unbox pre :=
            match pre with
            | Unbox i => mthrow (err "TODO")
            | _ => mthrow (err "expected Unbox pre-instr")
            end
          in
          match tf' with
          | Arrow from to =>
            let boxes := for_boxes Box from in
            let unboxes := for_boxes Unbox to in
            boxes' ← mapM type_box boxes;
            unboxes' ← mapM type_unbox unboxes;
            mret $ [
              (* notably not tf' here *)
              Instr (Block (compile_type false tf) [] (boxes' ++ [Call i z__s] ++ unboxes'))
            ]
          end
      | AR.RecFold τ => mret $ [Instr (RecFold τ) tf']
      | AR.RecUnfold => mret $ [Instr (RecUnfold) tf']
      | AR.Group i q => mret $ [Instr (Group i q) tf']
      | AR.Ungroup => mret $ [Instr (Ungroup) tf']
      | AR.CapSplit => mret $ [Instr (CapSplit) tf']
      | AR.CapJoin => mret $ [Instr (CapJoin) tf']
      | AR.RefDemote => mret $ [Instr (RefDemote) tf']
      | AR.MemPack ℓ => mret $ [Instr (MemPack ℓ) tf']
      | AR.MemUnpack tf le e__s =>      
        e__s' ← mapM compile_instruction e__S;
        mret $ [Instr (MemUnpack (compile_type false tf) (map compile_le le) e__s') tf']
      | AR.StructMalloc sz__s q => mret $ [Instr (StructMalloc sz__s q) tf']
      | AR.StructFree => mret $ [Instr (StructFree) tf']
      | AR.StructGet i => mret $ [Instr (StructGet i) tf']
      | AR.StructSet i => mret $ [Instr (StructSet i) tf']
      | AR.StructSwap i => mret $ [Instr (StructSwap i) tf']
      | AR.VariantMalloc i τ__s q => mret $ [Instr (VariantMalloc i (map (compile_type true) τ__s) q) tf']
      | AR.VariantCase q ψ tf le e__ss =>
        let ψ' := compile_heap true ψ in
        let tf' := compile_arrow true tf in
        let le' := map compile_le le in
        let e__ss' := mapM (mapM compile_instruction) e__ss in
        mret $ [Instr (VariantCase q ψ' tf' le' e__ss') tf']
      | AR.ArrayMalloc q => mret $ [Instr (ArrayMalloc q) tf']
      | AR.ArrayGet => mret $ [Instr (ArrayGet) tf']
      | AR.ArraySet => mret $ [Instr (ArraySet) tf']
      | AR.ArrayFree => mret $ [Instr (ArrayFree) tf']
      | AR.ExistPack τ ψ q => mret $ [Instr (ExistPack (compile_type true τ) (compile_heap true ψ) q) tf']
      | AR.ExistUnpack q ψ tf le e__s =>
        let ψ' := compile_heap true ψ in
        let tf'' := compile_arrow true tf in
        let le' := map compile_le true le in
        let e__s' := map compile_instruction e__s in
        mret $ [Instr (ExistUnpack q ψ' tf'' le' e__s') tf']
      | AR.RefSplit => mret $ [Instr (RefSplit) tf']
      | AR.RefJoin => mret $ [Instr (RefJoin) tf']
      | AR.Qualify q => mret $ [Instr (Qualify q) tf']
      | AR.Trap
      | AR.CallAdm _ _
      | AR.Label _ _ _ _
      | AR.Local _ _ _ _ _
      | AR.Malloc _ _ _
      | AR.Free => mthrow (err "unexpected admin instr")
      end
    end.

  (* TODO: compile module *)

End AnnotatedToBoxed.

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
  | Br_if (i : nat)
  | Br_table (i__s : list nat) (j : nat)
  | Ret

  | NewTmp (name : string)
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

  | Init (shape : list shape)        (* [val; ptr] → ptr *)
  | RepeatInit (shape : shape)  (* [val; len; ptr] → ptr *)
  | LoadOffset (offset : nat)
  | StoreOffset (offset : nat) (* takes ptr from tos, then loads shape from below it *)
  | SwapOffset (offset : nat)
  | Malloc (shape : list shape)
  | Free
  with Func :=
  | Fun (ex__s : list rwasm.ex) (tf : ArrowShape) (locals : list shape) (e__s : list Instruction).

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

Module BoxPolymorphicToLayout.
  Import layout.
  Import List Lists.List ListNotations FSets.FMapInterface.
  Module boxed := BoxPolymorphicIR.
  Module layout := LayoutIR.

  (* FIXME: this is duplicated from layout.v *)
  Fixpoint compile_val (value : boxed.Value) : option LayoutValue :=
    match value with
    | boxed.NumConst (rwasm.Int _ rwasm.i32) num => mret $ LV_int32 num
    | boxed.NumConst (rwasm.Int _ rwasm.i64) num => mret $ LV_int64 num
    | boxed.NumConst (rwasm.Float rwasm.f32) num => mret $ LV_float32 num
    | boxed.NumConst (rwasm.Float rwasm.f64) num => mret $ LV_float64 num
    | boxed.Tt => None
    | boxed.Coderef module_idx table_idx concrete =>
        mret $ LV_tuple [LV_int32 module_idx; LV_int32 table_idx] (* TODO: confirm this is ok *)
    | boxed.Fold v => compile_val v
    | boxed.Prod v__s => mret $ LV_tuple (omap compile_val v__s)
    | boxed.Ref ℓ => mret $ loc_to_layout ℓ
    | boxed.PtrV ℓ => mret $ loc_to_layout ℓ
    | boxed.Cap
    | boxed.Own => None
    | boxed.Mempack ℓ v => compile_val v
    | boxed.Boxed v => None      (* FIXME: this is wrong, but need to finalize IR first *)
    end.

  Section Typ.

  Variable env : gmap rwasm.var LayoutShape.

  Fixpoint compile_typ (τ : boxed.Typ) : M (option LayoutShape) := (* TODO: function ctx *)
    match τ with
    | boxed.Num nτ =>
      mret $ Some (match nτ with
      | rwasm.Int _ rwasm.i32 => LS_int32
      | rwasm.Int _ rwasm.i64 => LS_int64
      | rwasm.Float rwasm.f32 => LS_float32
      | rwasm.Float rwasm.f64 => LS_float64
      end)
    | boxed.BoxedT τ => mret $ Some LS_int32
    | boxed.TVar α =>
      typ ← lift_optionM (env !! α) ("cannot find type var with index " ++ (pretty α));  (* FIXME: this is unboxed, is that correct? *)
      mret $ Some typ
    | boxed.Unit => mret None
    | boxed.ProdT τ__s =>
      opt_shapes ← (mapM compile_typ τ__s);
      let shapes := omap id opt_shapes in
      mret $ Some $ LS_tuple shapes
    | boxed.CoderefT χ => mthrow (err "TODO")
    | boxed.Rec q τ => compile_typ τ
    | boxed.PtrT ℓ => mret $ Some LS_int32
    | boxed.ExLoc q τ => mthrow (err "TODO")
    | boxed.OwnR _
    | boxed.CapT _ _ _ => mret None
    | boxed.RefT cap ℓ ψ => mret $ Some LS_int32
    end.

  Fixpoint compile_tf (tf : boxed.ArrowType) : M layout.ArrowShape :=
    let 'boxed.Arrow τ__s1 τ__s2 := tf in
    τ__s1' ← mapM compile_typ τ__s1;
    τ__s2' ← mapM compile_typ τ__s2;
    mret $ layout.Arrow (omap id τ__s1') (omap id τ__s2'). (* use omap to filter zero sized *)


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

  Fixpoint compile_le (env : gmap rwasm.var LayoutShape) (le : boxed.LocalEffect) : M layout.LocalEffect :=
    opt_shapes ← mapM (fun '(i, τ) =>
                        shape ← compile_typ env τ;
                        mret (transform_local_idx i, shape)) le;
    mret $ omap (fun '(i, shape) => match shape with | Some x => Some (i, x) | None => None end) opt_shapes.

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

  Fixpoint compile_instr (env : gmap rwasm.var LayoutShape) (instr : boxed.Instruction) : M (list layout.Instruction) :=
    match instr with
    | boxed.Instr pre tf => compile_pre_instr env pre tf
    end
  with compile_pre_instr (env : gmap rwasm.var LayoutShape )(pre : boxed.PreInstruction) tf : M (list layout.Instruction) := (* TODO: function ctx *)
    let '(boxed.Arrow tf__from tf__to) := tf in
    match pre with
    | boxed.Box _
    | boxed.Unbox _ => mthrow (err "TODO: add some sort of IR form to modify ith stack element")

    | boxed.Val v =>
      mret $ match compile_val v with
      | Some v' => [layout.Val v']
      | None => []
      end
    | boxed.Ne ni => mret [layout.Ne ni]
    | boxed.Unreachable => mret [layout.Unreachable]
    | boxed.Nop => mret [layout.Nop]
    | boxed.Drop => mret [layout.Drop]
    | boxed.Select => mret [layout.Select]
    | boxed.Block tf le e__s =>
      tf' ← compile_tf env tf;
      le' ← compile_le env le;
      e__s' ← flat_mapM (compile_instr env) e__s;
      mret [layout.Block tf' le' e__s']
    | boxed.Loop tf e__s =>
      tf' ← compile_tf env tf;
      e__s' ← flat_mapM (compile_instr env) e__s;
      mret [layout.Loop tf' e__s']
    | boxed.ITE tf le e__thn e__els =>
      tf' ← compile_tf env tf;
      le' ← compile_le env le;
      e__thn' ← flat_mapM (compile_instr env) e__thn;
      e__els' ← flat_mapM (compile_instr env) e__els;
      mret [layout.ITE tf' le' e__thn' e__els']
    | boxed.Br i => mret [layout.Br i]
    | boxed.Br_if i => mret [layout.Br_if i]
    | boxed.Br_table i__s j => mret [layout.Br_table i__s j]
    | boxed.Ret => mret [layout.Ret]
    | boxed.Get_local i _ => mret [layout.GetLocal (transform_local_idx i)]
    | boxed.Set_local i => mret [layout.SetLocal (transform_local_idx i)]
    | boxed.Tee_local i => mret [layout.TeeLocal (transform_local_idx i)]
    | boxed.Get_global i => mret [layout.GetGlobal (transform_local_idx i)]
    | boxed.Set_global i => mret [layout.SetGlobal (transform_local_idx i)]
    | boxed.CoderefI i => mret [layout.Val $ LV_int32 i]      (* TODO: need to confirm this is correct, this is how the rust compiler does it *)
    | boxed.Inst z__s => mret []
    | boxed.Call_indirect => mthrow (err "TODO:")
    | boxed.Call i z__s =>
      z__sizes ← mret $ omap (fun idx => match idx with
                                    | rwasm.SizeI sz => Some sz
                                    | rwasm.LocI _ | rwasm.QualI _ | rwasm.TypI _ => None end) z__s;
      size_instrs ← flat_mapM compile_sz z__sizes;
      mret $ size_instrs ++ [layout.Call i]
    | boxed.RecFold _
    | boxed.RecUnfold
    | boxed.Group _ _
    | boxed.Ungroup
    | boxed.CapSplit
    | boxed.CapJoin
    | boxed.RefDemote
    | boxed.MemPack _ => mret []

    | boxed.MemUnpack tf le e__s =>
      tf' ← compile_tf env tf;
      le' ← compile_le env le;
      e__s' ← flat_mapM (compile_instr env) e__s;
      mret [layout.Block tf' le' e__s']

    (* [f1 ... f__n init] → [ptr]
       [τ1 ... τ__n     ] → [i32] *)
    | boxed.StructMalloc sz__s q =>
      flat_sz ← mret $ fold_sizes sz__s;

      (* field_shapes ← *)
      mthrow (err "TODO:")

    (* [ptr] → []
       [i32] → [] *)
    | boxed.StructFree => mret [layout.Free]
    | boxed.StructGet i => mthrow (err "TODO:")
    | boxed.StructSet i => mthrow (err "TODO:")
    | boxed.StructSwap i => mthrow (err "TODO:")
    | boxed.VariantMalloc i τ__s q =>
      (* FIXME: needs init and correct vals on stack before malloc *)

      typ ← lift_optionM (list_lookup i τ__s) ("invalid variant malloc, no type corresponds with index " ++ (pretty i));
      opt_shape ← compile_typ env typ;
      (* memory layout is [ind, τ*] so we just add prepend *)
      let full_shape := LS_int32 :: match opt_shape with
      | Some s => [s]
      | None => []
      end in
      mret [layout.Malloc full_shape]
    | boxed.VariantCase q ψ tf le e__ss => mthrow (err "TODO:")

    (* [init val; len] → [ptr]
       [τ       ; i32] → [i32] *)
    | boxed.ArrayMalloc q =>
      let arr_init_typ_opt := head tf__from in (* XXX: clarify order of tf *)
      arr_init_typ ← lift_optionM arr_init_typ_opt "empty tffrom";
      shape_opt ← compile_typ env arr_init_typ;
      shape ← lift_optionM shape_opt "cannot make an array of size zero";
      mret [
        layout.NewTmp "len";
        layout.TeeTmp "len"; (* exisitng length at TOS, consumed by Malloc, but also needed for repeat Init *)
        layout.Malloc [shape];
        layout.GetTmp "len";
        layout.FreeTmp "len";
        layout.RepeatInit shape]

    | boxed.ArrayGet => mthrow (err "TODO:")
    | boxed.ArraySet => mthrow (err "TODO:")
    | boxed.ArrayFree => mret [layout.Free]
    | boxed.ExistPack τ ψ q => mthrow (err "TODO:")
    | boxed.ExistUnpack q ψ tf le e__s => mthrow (err "TODO:")
    | boxed.RefSplit
    | boxed.RefJoin
    | boxed.Qualify _ => mret []
    end.
  End Instrs.

  Print compile_instr.

  Definition resolve_locals_layout_shape (sz__s : list rwasm.Size) (instrs : list boxed.Instruction) : M (list LayoutShape) :=
    (* TODO: need to see what type the first local.store is, and use that. otherwise fallback to a sequence of i64s *)
    mthrow (err "TODO").

  Definition compile_func (func : boxed.Func) : M layout.Func :=
    let 'boxed.Fun ex__s χ sz__s e__s := func in
    let 'boxed.FunT κ tf := χ in
    (* let 'boxed.Arrow τ__from τ__to := tf in  *)
    '(layout.Arrow shape__from shape__to) ← compile_tf ∅ tf;      (* FIXME: previous stage should ensure this doesn't contain TVar *)
    let loc_params := omap (fun k => match k with
      | rwasm.SIZE sz__upper sz__lower => Some LS_int32
      | rwasm.LOC _ | rwasm.QUAL _ _ | rwasm.TYPE _ _ _ => None end) κ in

    locals ← resolve_locals_layout_shape sz__s e__s;
    let num_rwasm_params := length shape__from in

    let sz_locals := map_seq num_rwasm_params (seq 0 num_rwasm_params) in
    let idx_transformer i := if Nat.ltb i num_rwasm_params then i + num_rwasm_params else i in

    e__s' ← flat_mapM (compile_instr sz_locals idx_transformer ∅) e__s;

    mret $ layout.Fun ex__s (layout.Arrow (shape__from ++ loc_params) shape__to) locals e__s'.

  Definition compile_global (global : boxed.Glob) : M (option layout.Glob).
  Admitted.                     (* FIXME: what to do about 0 sized types? *)
    (* match global with *)
    (* | boxed.GlobMut τ i__s => mret $ layout.GlobMut (boxed_type_to_shape τ) (compile_instr i__s) *)
    (* | boxed.GlobEx ex__s τ i__s => mret $ layout.GlobEx ex__s (boxed_type_to_shape τ) (compile_instr i__s) *)
    (* | boxed.GlobIm ex__s τ im =>  mret $ layout.GlobEx ex__s (boxed_type_to_shape τ) im  *)
    (* end. *)

  Definition compile_module (module : boxed.module) : M layout.module :=
    let 'boxed.Build_module functions globals table := module in
    mthrow (err "TODO").

End BoxPolymorphicToLayout.

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

  Definition apply_le (le : LocalEffect) (Γ : TypeEnv) : M TypeEnv :=
    Γ' ← foldlM (fun '(idx, shape) (acc : TypeEnv) => te_set_local idx shape acc) Γ le;
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
    | Br i=> mthrow (err "TODO: deal with labels")
    | Br_if i=> mthrow (err "TODO: deal with labels")
    | Br_table i__s j => mthrow (err "TODO: deal with labels")
    | Ret => mthrow (err "TODO:")
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
    (* | LoadOffset offset => _ *)
    (* | StoreOffset offset => _ *)
    (* | SwapOffset offset => _ *)
    (* | Malloc shapes => *)

    | Free =>
      '(shape, Γ') ← lift_optionM (te_pop Γ) "Free: expected non-empty stack";
      _ ← match shape with
      | LS_int32 => mret ()
      | _ => mthrow (err ("Free expected i32 at TOS but got " ++ (pretty shape)))
      end;
      mret Γ'
    | _ => mthrow (err "TODO")   (*  *)
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
    Variable (GC_MEM: wasm.immediate).
    Variable (LIN_MEM: wasm.immediate).

    Variable function_types : list wasm.function_type.

    Fixpoint compile_val (value : LayoutValue) : list wasm.value :=
      match value with
      | LV_int32 i => [compile_num_from_Z wasm.T_i32 (Z.of_nat i)]
      | LV_int64 i => [compile_num_from_Z wasm.T_i64 (Z.of_nat i)]
      | LV_float32 f => [compile_num_from_Z wasm.T_f32 (Z.of_nat f)]
      | LV_float64 f => [compile_num_from_Z wasm.T_f64 (Z.of_nat f)]
      | LV_tuple fields => flat_map compile_val fields
      end.

    Definition lift_peek (Γ : TypeEnv) (msg : string) : InstM shape :=
      liftM $ lift_optionM (te_peek Γ) msg.

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

        mthrow (err "TODO")
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
      | _ => mthrow (err "TODO")
      end.

  End Instrs.


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

  (* TODO: deal with exports *)
  (* Definition compile_glob (glob : Glob) : wasm.global :=  *)
  (*   let '(mutable, ) match glob with *)
  (*   | GlobMut shape i__s => _ *)
  (*   | GlobEx ex__s shape i__s => _ *)
  (*   | GlobIm ex__s shape im => _ *)
  (*   end  *)


  Section Mod.

    Variable (mod_idx : nat).
    Variable (build_limit_min : N).
    Variable (build_limit_max : option N).

    Definition layout_compile_module (module : module) : M wasm.module :=
      let 'Build_module functions globals table := module in
      let function_types := foldl' collect_function_types [] functions in
      let ctx := {|
        fc_function_types := invert_map (map_seq 0 function_types);
        fc_globals := map_seq 0 (map shape_of_glob globals);
        fc_globals_layout := ∅;         (* FIXME *)
        fc_module_idx := mod_idx;
      |} in
      functions' ← mapM (compile_function ctx) functions;

      mret {|
        wasm.mod_types := function_types;
        wasm.mod_funcs := functions';
        wasm.mod_tables := []; (* TODO *)
        wasm.mod_mems := [
          {| wasm.lim_min := build_limit_min; wasm.lim_max := build_limit_max |}; (* gc mem *)
          {| wasm.lim_min := build_limit_min; wasm.lim_max := build_limit_max |}  (* lin mem *)
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
