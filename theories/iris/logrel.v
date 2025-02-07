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

Definition relations : Type := 
  (* interp_value *)
  (leibnizO R.value_type -n> WsR) *
  (* interp_frame *)
  (leibnizO (list (R.value_type * R.size)) -n> WsR) * 
  (* interp_expr *)
  (leibnizO R.result_type -n>
  leibnizO (list (R.result_type * list (R.value_type * R.size))) -n>
  optionO (leibnizO R.result_type) -n>
  leibnizO (list (R.value_type * R.size)) -n>
  leibnizO instance -n>
  leibnizO (lholed * list administrative_instruction) -n>
  iPropO Σ).

Definition interp_value (r: relations) : leibnizO R.value_type -n> WsR :=
  fst (fst r).

Definition interp_frame (r: relations) : leibnizO (list (R.value_type * R.size)) -n> WsR :=
  snd (fst r).

Definition interp_expr (r: relations) : _ :=
  snd r.

Canonical Structure relationsO : ofe := Ofe relations prod_ofe_mixin.

Global Instance relations_inhabited : Inhabited relationsO.
Proof.
  apply populate.
  exact (λne _ _, ⌜true⌝%I,
         λne _ _, ⌜true⌝%I,
         λne _ _ _ _ _ _, ⌜true⌝%I).
Qed.

Definition interp_heap_value_variant (rs : relations) (τs : list R.value_type) : HR :=
  λne (bs : leibnizO bytes), (
    ∃ bs_tag bs_payload bs_rest,
    ⌜bs = bs_tag ++ bs_payload ++ bs_rest⌝ ∗
    let tag := R.read_tag bs_tag in
    ∃ τ,
    ⌜τs !! tag = Some τ⌝ ∗
    let ws := R.read_value τ bs_payload in
    interp_value rs τ (Stack ws)
  )%I.

Definition interp_heap_value_struct
  (rs : relations)
  (fs : list (R.value_type * R.size))
: HR :=
  λne (bs : leibnizO bytes), (
    ∃ (bss : list bytes) (bs_rest : bytes),
      ⌜bs = flatten bss ++ bs_rest⌝ ∗
      [∗ list] f;fbs ∈ fs;bss,
        let '(τ, sz) := f in
        ⌜R.eval_size sz = Some (length fbs)⌝ ∗
        let ws := R.read_value τ fbs in
        interp_value rs τ (Stack ws)
  )%I.

Definition interp_heap_value_array (rs : relations) (τ : R.value_type) : HR :=
  λne (bs : leibnizO bytes), (∃ bss bs_rest,
    ⌜bs = flatten bss ++ bs_rest⌝ ∗
    [∗ list] ebs ∈ bss,
      ⌜length ebs = R.size_of τ⌝ ∗
      let ws := R.read_value τ ebs in
      interp_value rs τ (Stack ws)
  )%I.

Definition interp_heap_value (rs : relations) (Ψ : R.heap_type) : HR :=
  match Ψ with
  | R.VariantType τs => interp_heap_value_variant rs τs
  | R.StructType fields => interp_heap_value_struct rs fields
  | R.ArrayType τ => interp_heap_value_array rs τ
  end.

Definition interp_pre_value_unit : WsR := λne ws, ⌜∃ z, head (stack_values ws) = Some (VAL_int32 z)⌝%I.

Definition interp_values (rs : relations) : leibnizO (list R.value_type) -n> WsR :=
  λne (τs : leibnizO (list R.value_type)) ws, (∃ wss ws_rest,
    ⌜stack_values ws = flatten wss ++ ws_rest⌝ ∗
    [∗ list] τ;ws ∈ τs;wss, interp_value rs τ (Stack ws)
  )%I.

Definition interp_pre_value_num (np : R.num_type) : WsR :=
  λne ws,
    match np with
    | R.T_i32 => ⌜∃ z, head (stack_values ws) = Some (VAL_int32 z)⌝%I
    | R.T_i64 => ⌜∃ z, head (stack_values ws) = Some (VAL_int64 z)⌝%I
    | R.T_f32 => ⌜∃ z, head (stack_values ws) = Some (VAL_float32 z)⌝%I
    | R.T_f64 => ⌜∃ z, head (stack_values ws) = Some (VAL_float64 z)⌝%I
    end.

Definition interp_closure (rs : relations) (tf : R.function_type) : ClR :=
  let '(R.Tf t1 t2) := tf in
  λne (cl : leibnizO function_closure),
  match cl with
  | FC_func_native inst (Tf wt1 wt2) tlocs es => (<pers>
    ⌜seq.map R.lower_type t1 = wt1⌝ ∗
    ⌜seq.map R.lower_type t2 = wt2⌝ ∗
    ∀ ws F, ∃ L,
    interp_values rs t1 ws ∗ interp_frame rs L F ∗ ⌜R.lower_locals L = tlocs⌝ -∗
    ∃ L',
    interp_expr rs t2 [] None L' inst (
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
      ⌜head (stack_values ws) = Some (VAL_int32 n)⌝ ∗
      n' ↦[wf] cl ∗
      ▷ interp_closure rs tf cl
    )
  )%I.

Definition interp_pre_value_exloc (rs : relations) (τ : R.value_type) : WsR :=
  λne ws, (∃ ℓ, ▷ interp_value rs (R.subst_type_loc ℓ τ) ws)%I.

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
    ▷interp_heap_value rs ψ bs
  )%I.

Definition interp_pre_value_ref
  (rs : relations)
  (π : R.cap)
  (sz : R.size)
  (ψ : R.heap_type)
: WsR :=
  λne ws, (
    ∃ z, ⌜head (stack_values ws) = Some (VAL_int32 z)⌝ ∗
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

Ltac solve_iprop_ne :=
 repeat (apply exist_ne +
              apply intuitionistically_ne +
              apply or_ne +
              apply sep_ne +
              apply and_ne +
              apply wp_ne +
              apply inv_ne +
              auto +
              (rewrite /pointwise_relation; intros) +
              apply forall_ne + apply wand_ne).

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
  (interp_value_0 rs,
   interp_frame_0 rs,
   interp_expr_0 rs).

Lemma interp_closure_ne :
  forall n x y ty,
    x ≡{n}≡ y ->
    interp_closure x ty ≡{n}≡ interp_closure y ty.
Proof.
  intros.
  destruct ty.
  cbn.
  intros cl; cbn.
  destruct cl; destruct f;
  solve_iprop_ne.
  - eapply big_sepL2_ne.
    intros.
    apply H0.
  - apply H0.
  - apply H0.
Qed.

Lemma interp_heap_value_ne :
  forall n x y hty,
    x ≡{n}≡ y ->
    interp_heap_value x hty ≡{n}≡ interp_heap_value y hty.
Proof.
  intros.
  intros bs.
  destruct hty; solve_iprop_ne; cbn.
  - apply H0.
  - apply big_sepL2_ne; intros.
    destruct y1.
    solve_iprop_ne.
    apply H0.
  - apply big_opL_ne; intros.
    solve_iprop_ne.
    apply H0.
Qed.

Lemma interp_value_0_contractive :
  forall n x y,
    dist_later n x y ->
    interp_value_0 x ≡{n}≡ interp_value_0 y.
Proof.
  intros.
  intros [pty] vs.
  destruct pty; cbn; try reflexivity.
  - solve_iprop_ne.
    apply later_contractive.
    constructor; intros m Hmn.
    pose proof (dist_later_lt _ _ _ H0 _ Hmn) as Heqm.
    apply interp_closure_ne; auto.
  - solve_iprop_ne.
    apply later_contractive.
    constructor.
    intros m Hmn.
    pose proof (dist_later_lt _ _ _ H0 _ Hmn) as Heqm.
    apply Heqm.
  - solve_iprop_ne.
    destruct c.
    + solve_iprop_ne.
      apply later_contractive.
      constructor; intros m Hmn.
      pose proof (dist_later_lt _ _ _ H0 _ Hmn) as Heqm.
      now apply interp_heap_value_ne.
    + solve_iprop_ne.
      apply later_contractive.
      constructor; intros m Hmn.
      pose proof (dist_later_lt _ _ _ H0 _ Hmn) as Heqm.
      now apply interp_heap_value_ne.
Qed.

(*
Lemma interp_values_0_contractive :
  forall n x y,
    dist_later n x y ->
    interp_values x ≡{n}≡ interp_values y.
Proof.
  intros.
  intros tys.
  unfold interp_values.
  intros τs; cbn.
  solve_iprop_ne.
  apply big_sepL2_ne.
  intros.
  apply interp_value_0_ne.
Admitted.
*)

Lemma interp_frame_0_contractive :
  forall n x y,
    dist_later n x y ->
    interp_frame_0 x ≡{n}≡ interp_frame_0 y.
Proof.
  unfold interp_frame_0.
  reflexivity.
Qed.

Lemma interp_expr_0_contractive :
  forall n x y,
    dist_later n x y ->
    interp_expr_0 x ≡{n}≡ interp_expr_0 y.
Proof.
  reflexivity.
Qed.

Global Instance rels_contractive : Contractive rels_0.
Proof.
  solve_proper_prepare.
  rewrite !pair_dist.
  split; [split|].
  - by apply interp_value_0_contractive.
  - by apply interp_frame_0_contractive.
  - by apply interp_expr_0_contractive.
Qed.

Definition rels : relations := fixpoint rels_0.

Definition interp_val (τs : R.result_type) : VR :=
  λne (v : leibnizO val), (
    ⌜v = trapV⌝ ∨
    ∃ ws, ⌜v = immV ws⌝ ∗ interp_values rels τs (Stack ws)
  )%I.

End logrel.
