From mathcomp Require Import ssreflect ssrbool eqtype seq.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import list.
From iris.prelude Require Import options.

From Wasm.iris.helpers Require Export iris_properties.
From Wasm.iris.language Require Export iris_atomicity.
From Wasm.iris.rules Require Export iris_rules.
From Wasm Require rwasm_datatypes.

Import uPred.

Section logrel.
  
  Context `{!wasmG Σ, !logrel_na_invs Σ}.
  Context `{R : rwasm_datatypes.Read}.

  Record stack := Stack { stack_values : list value }.
  Canonical Structure stackO := leibnizO stack.

  Notation VR := ((leibnizO val) -n> iPropO Σ).
  Notation WR := ((leibnizO value) -n> iPropO Σ).
  Notation WsR := (stackO -n> iPropO Σ).
  Notation HR := ((leibnizO bytes) -n> iPropO Σ).

  (* --------------------------------------------------------------------------------------- *)
  (* ---------------------------------- VALUE RELATION ------------------------------------- *)
  (* --------------------------------------------------------------------------------------- *)

  Definition interp_heap_value_struct
    (fs : list (rwasm_datatypes.value_type * rwasm_datatypes.size))
    (iv : rwasm_datatypes.value_type -> WsR)
  : HR :=
    λne (bs : leibnizO bytes), (
      ∃ (bss : list bytes), ∃ (bs' : bytes),
        ⌜bs = flatten bss ++ bs'⌝ ∗
        [∗ list] f;bs'' ∈ fs;bss,
          let '(τ, sz) := f in
          ⌜rwasm_datatypes.eval_size sz = Some (length bs'')⌝ ∧
          ∃ ws, ⌜rwasm_datatypes.read τ bs'' = ws⌝ ∗ iv τ (Stack ws)
    )%I.

  Definition interp_heap_value (Ψ : rwasm_datatypes.heap_type) (iv : rwasm_datatypes.value_type -> WsR) : HR :=
    match Ψ with
    | rwasm_datatypes.StructType fields => interp_heap_value_struct fields iv
    end.

  Definition interp_pre_value_unit : WsR := λne ws, ⌜∃ z, stack_values ws = [VAL_int32 z]⌝%I.

  Definition interp_pre_value_num (np : rwasm_datatypes.num_type) : WsR :=
    λne ws,
      match np with
      | rwasm_datatypes.T_i32 => ⌜∃ z, stack_values ws = [VAL_int32 z]⌝%I
      | rwasm_datatypes.T_i64 => ⌜∃ z, stack_values ws = [VAL_int64 z]⌝%I
      | rwasm_datatypes.T_f32 => ⌜∃ z, stack_values ws = [VAL_float32 z]⌝%I
      | rwasm_datatypes.T_f64 => ⌜∃ z, stack_values ws = [VAL_float64 z]⌝%I
      end.

  (* TODO *)
  Definition interp_pre_value_coderef (Χ : rwasm_datatypes.function_type) : WsR :=
    λne ws, ⌜false⌝%I.

  (* TODO *)
  Definition interp_pre_value_exloc (τ : rwasm_datatypes.value_type) : WsR :=
    λne ws, ⌜false⌝%I.

  (* TODO: Check r/rw privilege. *)
  Definition interp_pre_value_ref
    (π : rwasm_datatypes.cap)
    (sz : rwasm_datatypes.size)
    (ψ : rwasm_datatypes.heap_type)
    (iv : rwasm_datatypes.value_type -> WsR)
  : WsR :=
    λne ws, (
      ∃ bs, ∃ z,
      ⌜stack_values ws = [VAL_int32 z]⌝ ∗
      ⌜rwasm_datatypes.eval_size sz = Some (length bs)⌝ ∗
      ([∗ list] k ↦ b ∈ bs,
        let n := Z.to_N (Wasm_int.Int32.unsigned z) in
        (N.add n (N.of_nat k)) ↦[wm][ N.of_nat 0 ] b) ∗
      interp_heap_value ψ iv bs
    )%I.

  Definition interp_pre_value (p : rwasm_datatypes.pre_type) (iv : rwasm_datatypes.value_type -> WsR) : WsR :=
    match p with
    | rwasm_datatypes.Num np => interp_pre_value_num np
    | rwasm_datatypes.Unit => interp_pre_value_unit
    | rwasm_datatypes.CoderefT Χ => interp_pre_value_coderef Χ
    | rwasm_datatypes.ExLoc τ' => interp_pre_value_exloc τ'
    | rwasm_datatypes.RefT π sz ψ => interp_pre_value_ref π sz ψ iv
    end.

  (* TODO: Check qualifier. *)
  Definition interp_value_0 (iv : leibnizO rwasm_datatypes.value_type -n> WsR) : (leibnizO rwasm_datatypes.value_type -n> WsR) :=
    λne (τ : leibnizO rwasm_datatypes.value_type),
      match τ with
      | rwasm_datatypes.QualT p q => interp_pre_value p iv
      end.

  (* TODO *)
  Global Instance interp_value_contractive : Contractive interp_value_0.
  Proof.
    solve_proper_prepare.
  Admitted.

  Definition interp_value : (leibnizO rwasm_datatypes.value_type -n> WsR) := fixpoint interp_value_0.

  (* TODO: Read the sequence of concrete values. *)
  Definition interp_val (τs : rwasm_datatypes.result_type) : VR :=
    λne (v : leibnizO val), (
      ⌜v = trapV⌝ ∨
      ∃ ws, ⌜v = immV ws⌝ ∗ [∗ list] τ;w ∈ τs;ws, interp_value τ (Stack [w])
    )%I.

End logrel.
