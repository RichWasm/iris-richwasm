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

Record relations := mkRelations {
  interp_value : leibnizO R.value_type -n> WsR;
  interp_values : leibnizO (list R.value_type) -n> WsR;
  interp_frame : leibnizO (list (R.value_type * R.size)) -n> WsR;
  interp_expr :
    leibnizO R.result_type -n>
    leibnizO (list (R.result_type * list (R.value_type * R.size))) -n>
    optionO (leibnizO R.result_type) -n>
    leibnizO (list (R.value_type * R.size)) -n>
    leibnizO instance -n>
    leibnizO (lholed * list administrative_instruction) -n>
    iPropO Σ;
}.

Canonical Structure relationsO := leibnizO relations.

Global Instance relations_inhabited : Inhabited relationsO.
Proof.
  apply populate.
  exact {| interp_value := λne _ _, ⌜true⌝%I;
           interp_values := λne _ _, ⌜true⌝%I;
           interp_frame := λne _ _, ⌜true⌝%I;
           interp_expr := λne _ _ _ _ _ _, ⌜true⌝%I |}.
Qed.

Definition interp_heap_value_struct
  (rs : relations)
  (fs : list (R.value_type * R.size))
: HR :=
  λne (bs : leibnizO bytes), (
    ∃ (bss : list bytes), ∃ (bs_rest : bytes),
      ⌜bs = flatten bss ++ bs_rest⌝ ∗
      [∗ list] f;fbs ∈ fs;bss,
        let '(τ, sz) := f in
        ⌜R.eval_size sz = Some (length fbs)⌝ ∧
        ∃ ws, ⌜R.read τ fbs = ws⌝ ∗ ▷ rs.(interp_value) τ (Stack ws)
  )%I.

Definition interp_heap_value (rs : relations) (Ψ : R.heap_type) : HR :=
  match Ψ with
  | R.StructType fields => interp_heap_value_struct rs fields
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

Definition interp_closure (rs : relations) (tf : R.function_type) : ClR :=
  let '(R.Tf t1 t2) := tf in
  λne (cl : leibnizO function_closure),
  match cl with
  | FC_func_native inst (Tf wt1 wt2) tlocs es => (<pers>
    ⌜seq.map R.lower_type t1 = wt1⌝ ∗
    ⌜seq.map R.lower_type t2 = wt2⌝ ∗
    ∀ ws F, ∃ L,
    rs.(interp_values) t1 ws ∗ rs.(interp_frame) L F ∗ ⌜R.lower_locals L = tlocs⌝ -∗
    ∃ L',
    rs.(interp_expr) t2 [] None L' inst (
      LH_base [] [],
      [AI_local
        (length t2)
        (Build_frame ((stack_values ws) ++ (n_zeros tlocs)) inst)
        [AI_label (length t2) [] (seq.map AI_basic es)]]
    )
  )%I
  | FC_func_host _ _ => ⌜false⌝%I
  end.

Definition interp_pre_value_coderef (rs : relations) (tf : R.function_type) : WsR :=
  λne ws, (
    ∃ (n : i32) cl,
    let n' := (Z.to_N (Wasm_int.Int32.unsigned n)) in
    na_inv logrel_nais (rfN n') (
      ⌜stack_values ws = [VAL_int32 n]⌝ ∗
      n' ↦[wf] cl ∗
      interp_closure rs tf cl
    )
  )%I.

Definition interp_pre_value_exloc (rs : relations) (τ : R.value_type) : WsR :=
  λne ws, (∃ ℓ, rs.(interp_value) (R.subst_type_loc ℓ τ) ws)%I.

Definition interp_pre_value_ref_own
  (rs : relations)
  (sz : R.size)
  (ψ : R.heap_type)
  (z : i32)
: iPropO Σ :=
  (
    ∃ bs,
    ⌜R.eval_size sz = Some (length bs)⌝ ∗
    z ↦[rm] bs ∗
    interp_heap_value rs ψ bs
  )%I.

Definition interp_pre_value_ref
  (rs : relations)
  (π : R.cap)
  (sz : R.size)
  (ψ : R.heap_type)
: WsR :=
  λne ws, (
    ∃ z, ⌜stack_values ws = [VAL_int32 z]⌝ ∗
    match π with
    | R.R =>
      let n := Z.to_N (Wasm_int.Int32.unsigned z) in
      na_inv logrel_nais (rmN n) (interp_pre_value_ref_own rs sz ψ z)
    | R.W => interp_pre_value_ref_own rs sz ψ z
    end
  )%I.

Definition interp_pre_value (rs : relations) (p : R.pre_type) : WsR :=
  match p with
  | R.Num np => interp_pre_value_num np
  | R.Unit => interp_pre_value_unit
  | R.CoderefT Χ => interp_pre_value_coderef rs Χ
  | R.ExLoc τ' => interp_pre_value_exloc rs τ'
  | R.RefT π sz ψ => interp_pre_value_ref rs π sz ψ
  end.

(* TODO: Check qualifier. *)
Definition interp_value_0 (rs : relations) : leibnizO R.value_type -n> WsR :=
  λne (τ : leibnizO R.value_type),
    match τ with
    | R.QualT p q => interp_pre_value rs p
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
  (* unfold interp_heap_value.
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
      * apply IHl. *)
Admitted.

Definition interp_values_0 (rs : relations) : leibnizO (list R.value_type) -n> WsR :=
  λne (τs : leibnizO (list R.value_type)) ws, (∃ wss ws_rest,
    ⌜stack_values ws = flatten wss ++ ws_rest⌝ ∗
    [∗ list] τ;ws ∈ τs;wss, rs.(interp_value) τ (Stack ws)
  )%I.

(* TODO *)
Definition interp_frame_0 (rs : relations) : leibnizO (list (R.value_type * R.size)) -n> WsR :=
  λne _, λne _, ⌜false⌝%I.

(* TODO *)
Definition interp_expr_0 (rs : relations) :
  leibnizO R.result_type -n>
  leibnizO (list (R.result_type * list (R.value_type * R.size))) -n>
  optionO (leibnizO R.result_type) -n>
  leibnizO (list (R.value_type * R.size)) -n>
  leibnizO instance -n>
  leibnizO (lholed * list administrative_instruction) -n>
  iPropO Σ
:=
  λne _ _ _ _ _ _, ⌜false⌝%I.

Definition rels_0 (rs : relations) : relations :=
  {|
    interp_value := interp_value_0 rs;
    interp_values := interp_values_0 rs;
    interp_frame := interp_frame_0 rs;
    interp_expr := interp_expr_0 rs;
  |}.

Global Instance rels_contractive : Contractive rels_0.
Admitted.

Definition rels : relations := fixpoint rels_0.

Definition interp_val (τs : R.result_type) : VR :=
  λne (v : leibnizO val), (
    ⌜v = trapV⌝ ∨
    ∃ ws, ⌜v = immV ws⌝ ∗ rels.(interp_values) τs (Stack ws)
  )%I.

End logrel.
