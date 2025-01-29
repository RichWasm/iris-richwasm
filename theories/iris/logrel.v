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

From RWasm Require datatypes.
Module R := RWasm.datatypes.

Import uPred.

Set Bullet Behavior "Strict Subproofs".

Section logrel.
  
  Context `{!wasmG Σ, !logrel_na_invs Σ}.
  Context `{Re : R.Read}.

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
    (fs : list (R.value_type * R.size))
    (iv : leibnizO R.value_type -n> WsR)
  : HR :=
    λne (bs : leibnizO bytes), (
      ∃ (bss : list bytes), ∃ (bs' : bytes),
        ⌜bs = flatten bss ++ bs'⌝ ∗
        [∗ list] f;bs'' ∈ fs;bss,
          let '(τ, sz) := f in
          ⌜R.eval_size sz = Some (length bs'')⌝ ∧
          ∃ ws, ⌜R.read τ bs'' = ws⌝ ∗ ▷ iv τ (Stack ws)
    )%I.

  Definition interp_heap_value (Ψ : R.heap_type) (iv : leibnizO R.value_type -n> WsR) : HR :=
    match Ψ with
    | R.StructType fields => interp_heap_value_struct fields iv
    end.

  Definition interp_pre_value_unit : WsR := λne ws, ⌜∃ z, stack_values ws = [VAL_int32 z]⌝%I.

  Definition interp_pre_value_num (np : R.num_type) : WsR :=
    λne ws,
      match np with
      | R.T_i32 => ⌜∃ z, stack_values ws = [VAL_int32 z]⌝%I
      | R.T_i64 => ⌜∃ z, stack_values ws = [VAL_int64 z]⌝%I
      | R.T_f32 => ⌜∃ z, stack_values ws = [VAL_float32 z]⌝%I
      | R.T_f64 => ⌜∃ z, stack_values ws = [VAL_float64 z]⌝%I
      end.

  (* TODO *)
  Definition interp_pre_value_coderef (Χ : R.function_type) : WsR :=
    λne ws, ⌜false⌝%I.

  (* TODO *)
  Definition interp_pre_value_exloc (τ : R.value_type) : WsR :=
    λne ws, ⌜false⌝%I.

  (* TODO: Check r/rw privilege. *)
  Definition interp_pre_value_ref
    (π : R.cap)
    (sz : R.size)
    (ψ : R.heap_type)
    (iv : leibnizO R.value_type -n> WsR)
  : WsR :=
    λne ws, (
      ∃ bs, ∃ z,
      ⌜stack_values ws = [VAL_int32 z]⌝ ∗
      ⌜R.eval_size sz = Some (length bs)⌝ ∗
      ([∗ list] k ↦ b ∈ bs,
        let n := Z.to_N (Wasm_int.Int32.unsigned z) in
        (N.add n (N.of_nat k)) ↦[wm][ N.of_nat 0 ] b) ∗
      interp_heap_value ψ iv bs
    )%I.

  Definition interp_pre_value (p : R.pre_type) (iv : leibnizO R.value_type -n> WsR) : WsR :=
    match p with
    | R.Num np => interp_pre_value_num np
    | R.Unit => interp_pre_value_unit
    | R.CoderefT Χ => interp_pre_value_coderef Χ
    | R.ExLoc τ' => interp_pre_value_exloc τ'
    | R.RefT π sz ψ => interp_pre_value_ref π sz ψ iv
    end.

  (* TODO: Check qualifier. *)
  Definition interp_value_0 (iv : leibnizO R.value_type -n> WsR) : leibnizO R.value_type -n> WsR :=
    λne (τ : leibnizO R.value_type),
      match τ with
      | R.QualT p q => interp_pre_value p iv
      end.

  (* TODO *)
  Global Instance interp_value_contractive : Contractive interp_value_0.
  Proof.
    solve_proper_prepare.
    destruct x0.
    unfold interp_pre_value.
    destruct p; repeat (apply exist_ne +
                apply intuitionistically_ne +
                apply or_ne +
                apply sep_ne +
                apply and_ne +
                apply wp_ne +
                auto +
                (rewrite /pointwise_relation; intros) +
                apply forall_ne + apply wand_ne).
    unfold interp_heap_value.
    destruct h.
    unfold interp_heap_value_struct.
    repeat (apply exist_ne +
                apply intuitionistically_ne +
                apply or_ne +
                apply sep_ne +
                apply and_ne +
                apply wp_ne +
                auto +
                (rewrite /pointwise_relation; intros) +
                apply forall_ne + apply wand_ne).
    generalize dependent a1.
    induction l.
    - destruct a1; last done.
      simpl.
      done.
    - intro a3.
      destruct a3.
      + done.
      + simpl.
        apply sep_ne.
        * destruct a1.
          repeat (apply exist_ne +
            apply intuitionistically_ne +
            apply or_ne +
            apply sep_ne +
            apply and_ne +
            apply wp_ne +
            auto +
            (rewrite /pointwise_relation; intros) +
            apply forall_ne + apply wand_ne).
          f_contractive.
          solve_contractive.
        * apply IHl.
  Qed.

  Definition interp_value : (leibnizO R.value_type -n> WsR) := fixpoint interp_value_0.

  (* TODO: Read the sequence of concrete values. *)
  Definition interp_val (τs : R.result_type) : VR :=
    λne (v : leibnizO val), (
      ⌜v = trapV⌝ ∨
      ∃ ws, ⌜v = immV ws⌝ ∗ [∗ list] τ;w ∈ τs;ws, interp_value τ (Stack [w])
    )%I.

End logrel.
