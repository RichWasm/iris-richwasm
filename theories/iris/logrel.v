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

Definition rf : string := "rfN".
Definition rt : string := "rtN".
Definition rm : string := "rmN".
Definition rg : string := "rgN".
Definition rfN (a : N) : namespace := nroot .@ rf .@ a.
Definition rtN (a b: N) : namespace := nroot .@ rt .@ a .@ b.
Definition rmN (a: N) : namespace := nroot .@ rm .@ a.
Definition rgN (a: N) : namespace := nroot .@ rg .@ a.

Section logrel.

Context `{!wasmG Σ, !logrel_na_invs Σ, !R.Read}.

Fixpoint points_to_bytes_n n bs :=
  match bs with
  | [] => emp%I
  | b :: bs' => (n ↦[wm][ N.of_nat 0 ] b ∗ points_to_bytes_n (n + 1)%N bs')%I
  end.

Definition points_to_bytes_i n bs :=
  points_to_bytes_n (Z.to_N (Wasm_int.Int32.unsigned n)) bs.

Notation "n ↦[rm] bs" := (points_to_bytes_i n bs)
  (at level 20, format "n ↦[rm] bs").

Record stack := Stack { stack_values : list value }.
Canonical Structure stackO := leibnizO stack.

Notation VR := ((leibnizO val) -n> iPropO Σ).
Notation WR := ((leibnizO value) -n> iPropO Σ).
Notation WsR := (stackO -n> iPropO Σ).
Notation HR := ((leibnizO bytes) -n> iPropO Σ).
Notation ClR := ((leibnizO function_closure) -n> iPropO Σ).

(* --------------------------------------------------------------------------------------- *)
(* ---------------------------------- VALUE RELATION ------------------------------------- *)
(* --------------------------------------------------------------------------------------- *)

Definition interp_heap_value_struct
  (fs : list (R.value_type * R.size))
  (iv : leibnizO R.value_type -n> WsR)
: HR :=
  λne (bs : leibnizO bytes), (
    ∃ (bss : list bytes), ∃ (bs_rest : bytes),
      ⌜bs = flatten bss ++ bs_rest⌝ ∗
      [∗ list] f;fbs ∈ fs;bss,
        let '(τ, sz) := f in
        ⌜R.eval_size sz = Some (length fbs)⌝ ∧
        ∃ ws, ⌜R.read τ fbs = ws⌝ ∗ ▷ iv τ (Stack ws)
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
Definition interp_closure (tf : R.function_type) : ClR :=
  λne (cl : leibnizO function_closure),
  ⌜false⌝%I.

Definition interp_pre_value_coderef (tf : R.function_type) : WsR :=
  λne ws, (
    ∃ (n : i32) cl,
    let n' := (Z.to_N (Wasm_int.Int32.unsigned n)) in
    na_inv logrel_nais (rfN n') (
      ⌜stack_values ws = [VAL_int32 n]⌝ ∗
      n' ↦[wf] cl ∗
      interp_closure tf cl
    )
  )%I.

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
    z ↦[rm] bs ∗
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

(* TODO *)
Definition interp_expr
  (τs : R.result_type)
  (labels : list (R.result_type * list (R.value_type * R.size)))
  (rets : option R.result_type)
  (locals1 : list (R.value_type * R.size))
  (locals2 : list (R.value_type * R.size))
  (inst : instance)
  (lh : lholed) (* TODO: update lholed type for RichWasm? *)
  (es : list administrative_instruction) (* TODO: update admin instr type for RichWasm? *)
: iProp Σ :=
  ⌜false⌝.

End logrel.
