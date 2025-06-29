From Coq Require Import List NArith.BinNat Lists.List.
From stdpp Require Import base option strings list pretty decidable gmap countable numbers options.
From Wasm Require datatypes.
From RWasm Require term.
From RWasm.compiler Require Import numbers monads utils.

Set Bullet Behavior "Strict Subproofs".

Section Layout.
  Inductive LayoutPrimType :=
  | LT_int
  | LT_float.

  Inductive LayoutPrimSize :=
  | LS32
  | LS64.

  Inductive LayoutShape :=
  | LS_empty
  | LS_int32
  | LS_int64
  | LS_float32
  | LS_float64
  | LS_tuple (fields : list LayoutShape).

  Inductive LayoutValue :=
  | LV_unit
  | LV_int32 (i : nat)
  | LV_int64 (i : nat)
  | LV_float32 (f : nat)
  | LV_float64 (f : nat)
  | LV_tuple (fields : list LayoutValue).

  Global Instance layout_prim_type_eq_dec : EqDecision LayoutPrimType.
  Proof. solve_decision. Defined.

  Global Instance layout_prim_size_eq_dec : EqDecision LayoutPrimSize.
  Proof. solve_decision. Defined.

  Fixpoint layout_shape_eq_dec (x y : LayoutShape) : {x = y} + {x ≠ y}.
  Proof. decide equality; solve_decision. Defined.

  Global Instance layout_shape_eq_dec_inst : EqDecision LayoutShape := layout_shape_eq_dec.

  Fixpoint layout_value_eq_dec (x y : LayoutValue) : {x = y} + {x ≠ y}.
  Proof. decide equality; solve_decision. Defined.

  Global Instance layout_value_eq_dec_inst : EqDecision LayoutValue := layout_value_eq_dec.

  Global Instance pretty_layout_shape : Pretty LayoutShape :=
    fix go (sh : LayoutShape) : string :=
      match sh with
      | LS_empty => "unit"
      | LS_int32 => "i32"
      | LS_int64 => "i64"
      | LS_float32 => "f32"
      | LS_float64 => "f64"
      | LS_tuple fields =>
          String.app (String.app "(" (String.concat ", " (map go fields))) ")"
      end.

  Fixpoint LayoutShape_to_tree (ls : LayoutShape) : gen_tree nat :=
    match ls with
    | LS_empty => GenLeaf 0
    | LS_int32 => GenLeaf 1
    | LS_int64 => GenLeaf 2
    | LS_float32 => GenLeaf 3
    | LS_float64 => GenLeaf 4
    | LS_tuple fields => GenNode 5 (map LayoutShape_to_tree fields)
    end.

  Fixpoint tree_to_LayoutShape (t : gen_tree nat) : option LayoutShape :=
    match t with
    | GenLeaf 0 => Some LS_empty
    | GenLeaf 1 => Some LS_int32
    | GenLeaf 2 => Some LS_int64
    | GenLeaf 3 => Some LS_float32
    | GenLeaf 4 => Some LS_float64
    | GenNode 5 trees =>
      match mapM tree_to_LayoutShape trees with
      | Some fields => Some (LS_tuple fields)
      | None => None
      end  | _ => None
    end.

  Lemma LayoutShape_ind_strong :
    forall P : LayoutShape -> Prop,
    P LS_empty ->
    P LS_int32 ->
    P LS_int64 ->
    P LS_float32 ->
    P LS_float64 ->
    (forall fields, Forall P fields -> P (LS_tuple fields)) ->
    forall ls, P ls.
  Proof.
    intros P H0 H1 H2 H3 H4 Htuple.
    fix IH 1.
    destruct ls.
    - exact H0.
    - exact H1.
    - exact H2.
    - exact H3.
    - exact H4.
    - apply Htuple.
      induction fields.
      + constructor.
      + constructor; [apply IH | assumption].
  Qed.

  Lemma tree_to_LayoutShape_to_tree (ls : LayoutShape) :
    tree_to_LayoutShape (LayoutShape_to_tree ls) = Some ls.
  Proof.
    induction ls using LayoutShape_ind_strong; try reflexivity.
    cbn.
    rewrite mapM_fmap_Forall_Some.
    - reflexivity.
    - exact H.
  Qed.

  Global Instance LayoutShape_countable : Countable LayoutShape.
  Proof.
    apply (inj_countable LayoutShape_to_tree tree_to_LayoutShape).
    - apply tree_to_LayoutShape_to_tree.
  Qed.

  Global Instance SlotType_layout_shape : SlotType := {
    slot_typ := LayoutShape;
    slot_eq_dec := _;
    slot_countable := _
  }.

  Coercion LayoutShape_to_slot_typ (ls : LayoutShape) : @slot_typ SlotType_layout_shape := ls.

  Definition layout_prim_size (ls : LayoutShape) : option LayoutPrimSize :=
    match ls with
    | LS_empty => None
    | LS_int32 => Some LS32
    | LS_int64 => Some LS64
    | LS_float32 => Some LS32
    | LS_float64 => Some LS64
    | LS_tuple _ => None
    end.

  Definition layout_size_of_int (int : term.IntType) : LayoutPrimSize :=
    match int with
    | term.i32 => LS32
    | term.i64 => LS64
    end.
  Definition layout_size_of_float (float : term.FloatType) : LayoutPrimSize :=
    match float with
    | term.f32 => LS32
    | term.f64 => LS64
    end.
  Definition layout_int_from_sz (sz : LayoutPrimSize) : LayoutShape :=
    match sz with
    | LS32 => LS_int32
    | LS64 => LS_int64
    end .
  Definition layout_float_from_sz (sz : LayoutPrimSize) : LayoutShape :=
    match sz with
    | LS32 => LS_float32
    | LS64 => LS_float64
    end.

  Fixpoint layout_value_to_shape (lv : LayoutValue) : LayoutShape :=
    match lv with
    | LV_unit => LS_empty
    | LV_int32 i => LS_int32
    | LV_int64 i => LS_int64
    | LV_float32 f => LS_float32
    | LV_float64 f => LS_float64
    | LV_tuple fields => LS_tuple (map layout_value_to_shape fields)
    end.

  Fixpoint shape_size_words (sh : LayoutShape) : nat :=
    match sh with
    | LS_empty => 0
    | LS_int32 | LS_float32 => 1
    | LS_int64 | LS_float64 => 2
    | LS_tuple fields => foldr (fun s n => shape_size_words s + n) 0 fields
    end.

  (* bottom to top *)
  Fixpoint shape_to_wasm_types (ls : LayoutShape) : list wasm.value_type :=
    match ls with
    | LS_empty => []
    | LS_int32 => [wasm.T_i32]
    | LS_int64 => [wasm.T_i64]
    | LS_float32 => [wasm.T_f32]
    | LS_float64 => [wasm.T_f64]
    | LS_tuple fields => concat (map shape_to_wasm_types fields)
    end.

  (* top to bottom *)
  Definition shape_to_wasm_stack (ls : LayoutShape) : list wasm.value_type :=
    reverse (shape_to_wasm_types ls).

  (* ls1 can fit into ls2 without any additional caluclations, ls2 can be larger than ls1 *)
  (* TODO: this needs to be fixed *)
  Fixpoint compatible_shapes (ls1 : LayoutShape) (ls2 : LayoutShape) : bool :=
    match (ls1, ls2) with
    | (LS_empty, _) | (_, LS_empty) => true
    | (LS_int32, LS_int32) => true
    | (LS_int64, LS_int64) => true
    | (LS_float32, LS_float32) => true
    | (LS_float64, LS_float64) => true
    | (LS_tuple fields1, LS_tuple fields2) => list_prefix compatible_shapes fields1 fields2
    | _ => false
    end.
End Layout.
