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
Local Obligation Tactic := try solve_proper.

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
  (R.locals_typeO -n> WsR) * 
  (* interp_expr *)
  (leibnizO R.result_type -n>
   R.labels_typeO -n>
   R.ret_typeO -n>
   R.locals_typeO -n>
   leibnizO instance -n>
   leibnizO (lholed * list administrative_instruction) -n>
   iPropO Σ).

Canonical Structure relationsO : ofe := Ofe relations (@prod_ofe_mixin (prodO _ _) _ : OfeMixin relations).

Program Definition rels_value : relationsO -n> _ :=
  λne (r: relationsO), r.1.1.

Program Definition rels_frame : relationsO -n> _ :=
  λne (r: relationsO), r.1.2.

Definition rels_expr :
  relationsO -n>
  leibnizO R.result_type -n>
  R.labels_typeO -n>
  R.ret_typeO -n>
  R.locals_typeO -n>
  leibnizO instance -n>
  leibnizO (lholed * list administrative_instruction) -n>
  iPropO Σ :=
  λne (r: relationsO), snd r.

Global Instance relations_inhabited : Inhabited relationsO.
Proof.
  apply populate.
  exact (λne _ _, ⌜true⌝%I,
         λne _ _, ⌜true⌝%I,
         λne _ _ _ _ _ _, ⌜true⌝%I).
Qed.

Program Definition interp_heap_value_variant : relationsO -n> leibnizO (list R.value_type) -n> HR :=
  λne (rs : relationsO) (τs : leibnizO (list R.value_type)) (bs : leibnizO bytes), (
    ∃ bs_tag bs_payload bs_rest,
    ⌜bs = bs_tag ++ bs_payload ++ bs_rest⌝ ∗
    let tag := R.read_tag bs_tag in
    ∃ τ,
    ⌜τs !! tag = Some τ⌝ ∗
    let ws := R.read_value τ bs_payload in
    rels_value rs τ (Stack ws)
  )%I.

Program Definition interp_heap_value_struct : relationsO -n> leibnizO (list (R.value_type * R.size)) -n> HR :=
  λne (rs : relationsO) (fs : leibnizO (list (R.value_type * R.size))) (bs : leibnizO bytes), (
    ∃ (bss : list bytes) (bs_rest : bytes),
      ⌜bs = flatten bss ++ bs_rest⌝ ∗
      [∗ list] f;fbs ∈ fs;bss,
        let '(τ, sz) := f in
        ⌜R.eval_size sz = Some (length fbs)⌝ ∗
        let ws := R.read_value τ fbs in
        rels_value rs τ (Stack ws)
  )%I.
Next Obligation.
  solve_proper_prepare.
  solve_iprop_ne.
  apply big_sepL2_ne; intros.
  destruct y1.
  solve_iprop_ne.
  apply H0.
Qed.
Opaque interp_heap_value_struct.

Program Definition interp_heap_value_array : relationsO -n> leibnizO R.value_type -n> HR :=
  λne (rs : relationsO) (τ : leibnizO R.value_type) (bs : leibnizO bytes), (∃ bss bs_rest,
    ⌜bs = flatten bss ++ bs_rest⌝ ∗
    [∗ list] ebs ∈ bss,
      ⌜length ebs = R.size_of τ⌝ ∗
      let ws := R.read_value τ ebs in
      rels_value rs τ (Stack ws)
  )%I.

Opaque interp_heap_value_array.
Definition interp_heap_value : relationsO -> leibnizO R.heap_type -n> HR :=
  λ (rs: relationsO), λne (Ψ : leibnizO R.heap_type),
  match Ψ with
  | R.VariantType τs => interp_heap_value_variant rs τs
  | R.StructType fields => interp_heap_value_struct rs fields
  | R.ArrayType τ => interp_heap_value_array rs τ
  end.
Instance interp_heap_value_ne : NonExpansive interp_heap_value.
Proof.
  intros n rs rs' Hrs Ψ bs.
  destruct Ψ; solve_proper.
Qed.

Definition interp_pre_value_unit : WsR := λne ws, ⌜∃ z, head (stack_values ws) = Some (VAL_int32 z)⌝%I.

Definition interp_values (rs : relations) : leibnizO (list R.value_type) -n> WsR :=
  λne (τs : leibnizO (list R.value_type)) ws, (∃ wss ws_rest,
    ⌜stack_values ws = flatten wss ++ ws_rest⌝ ∗
    [∗ list] τ;ws ∈ τs;wss, rels_value rs τ (Stack ws)
  )%I.

Definition interp_pre_value_num : leibnizO R.num_type -n> WsR :=
  λne (np : leibnizO R.num_type) ws,
    match np with
    | R.T_i32 => ⌜∃ z, head (stack_values ws) = Some (VAL_int32 z)⌝%I
    | R.T_i64 => ⌜∃ z, head (stack_values ws) = Some (VAL_int64 z)⌝%I
    | R.T_f32 => ⌜∃ z, head (stack_values ws) = Some (VAL_float32 z)⌝%I
    | R.T_f64 => ⌜∃ z, head (stack_values ws) = Some (VAL_float64 z)⌝%I
    end.

Definition function_type_args : leibnizO R.function_type -> leibnizO (seq.seq R.value_type) :=
  λ tf,
    match tf with
    | R.Tf ts _ => ts
    end.
Instance function_type_args_ne :  NonExpansive function_type_args.
Proof. solve_proper. Qed.

Definition function_type_rets : leibnizO R.function_type -> leibnizO (seq.seq R.value_type) :=
  λ tf,
    match tf with
    | R.Tf _ ts => ts
    end.
Instance function_type_rets_ne :  NonExpansive function_type_rets.
Proof. solve_proper. Qed.

Definition interp_closure : relationsO -> leibnizO R.function_type -n> ClR :=
  λ rs,
    λne (tf: leibnizO R.function_type) (cl: leibnizO function_closure),
    let t1 := function_type_args tf in
    let t2 := function_type_rets tf in
    match cl with
    | FC_func_native inst (Tf wt1 wt2) tlocs es => (<pers>
        ⌜seq.map R.lower_type t1 = wt1⌝ ∗
        ⌜seq.map R.lower_type t2 = wt2⌝ ∗
        ∀ ws F, ∃ L,
        interp_values rs t1 ws ∗ rels_frame rs L F ∗ ⌜R.lower_locals L = tlocs⌝ -∗
        ∃ L',
        rels_expr rs t2 [] None L' inst (
        LH_base [] [],
        [AI_local
            (length t2)
            (Build_frame ((stack_values ws) ++ (n_zeros tlocs)) inst)
            [AI_label (length t2) [] (seq.map AI_basic es)]]
        )
    )%I
    | FC_func_host _ _ => ⌜false⌝%I
    end.
Instance interp_closure_rels_ne: NonExpansive (interp_closure) := ltac:(solve_proper).

Definition interp_pre_value_coderef (rs : relationsO) : leibnizO R.function_type -n> WsR :=
  λne tf ws, (
    ∃ (n : i32) cl,
    let n' := (Z.to_N (Wasm_int.Int32.unsigned n)) in
    na_inv logrel_nais (rfN n') (
      ⌜head (stack_values ws) = Some (VAL_int32 n)⌝ ∗
      n' ↦[wf] cl ∗
      ▷ interp_closure rs tf cl
    )
  )%I.
Instance interp_pre_value_coderef_contractive: Contractive interp_pre_value_coderef :=
  ltac:(solve_contractive).

Definition interp_pre_value_exloc (rs : relationsO) : leibnizO R.value_type -n> WsR :=
  λne (τ : leibnizO R.value_type) ws, (∃ ℓ, ▷ rels_value rs (R.subst_type_loc ℓ τ) ws)%I.
Instance interp_pre_value_exloc_contractive: Contractive interp_pre_value_exloc.
Proof.
  solve_proper_prepare.
  solve_iprop_ne.
  f_contractive.
  apply H0.
Qed.

Definition interp_pre_value_ref_own
  (rs : relationsO)
: _ -n> _ -n> _ -n> iPropO Σ :=
  λne (sz : leibnizO R.size) (ψ : leibnizO R.heap_type) (z : leibnizO i32),
  (
    ∃ bs,
    ⌜R.eval_size sz = Some (length bs)⌝ ∗
    z ↦[rm] bs ∗
    ▷ interp_heap_value rs ψ bs
  )%I.
Instance interp_pre_value_ref_own_contractive: Contractive interp_pre_value_ref_own.
Proof.
  Opaque interp_heap_value.
  solve_contractive.
  Transparent interp_heap_value.
Qed.

Definition interp_pre_value_ref
  (rs : relationsO)
: _ -n> _ -n> _ -n> WsR :=
  λne (π : leibnizO R.cap) (sz : leibnizO R.size) (ψ : leibnizO R.heap_type) ws, (
    ∃ z, ⌜head (stack_values ws) = Some (VAL_int32 z)⌝ ∗
    match π with
    | R.R =>
      let n := Z.to_N (Wasm_int.Int32.unsigned z) in
      na_inv logrel_nais (rmN n) (interp_pre_value_ref_own rs sz ψ z)
    | R.W => interp_pre_value_ref_own rs sz ψ z
    end
  )%I.
Instance interp_pre_value_ref_contractive: Contractive interp_pre_value_ref.
Proof.
  Opaque interp_pre_value_ref_own.
  Opaque interp_heap_value.
  solve_proper_prepare.
  solve_iprop_ne.
  solve_contractive.
  Transparent interp_pre_value_ref_own.
  Transparent interp_heap_value.
Qed.

Definition interp_pre_value (rs : relationsO) : leibnizO R.pre_type -n> WsR :=
  λne (p : leibnizO R.pre_type),
    match p with
    | R.Num np => interp_pre_value_num np
    | R.Unit => interp_pre_value_unit
    | R.CoderefT Χ => interp_pre_value_coderef rs Χ
    | R.ExLoc τ' => interp_pre_value_exloc rs τ'
    | R.RefT π sz ψ => interp_pre_value_ref rs π sz ψ
    end.
Instance interp_pre_value_contractive : Contractive interp_pre_value.
Proof.
  Opaque interp_pre_value_num.
  Opaque interp_pre_value_unit.
  Opaque interp_pre_value_coderef.
  Opaque interp_pre_value_exloc.
  Opaque interp_pre_value_ref.
  intros n rels rels' Hrels pty.
  destruct pty; solve_contractive.
  Transparent interp_pre_value_num.
  Transparent interp_pre_value_unit.
  Transparent interp_pre_value_coderef.
  Transparent interp_pre_value_exloc.
  Transparent interp_pre_value_ref.
Qed.

(* TODO: Check qualifier. *)
Definition interp_value_0 (rs : relations) : leibnizO R.value_type -n> WsR :=
  λne (τ : leibnizO R.value_type),
    match τ with
    | R.QualT p q => interp_pre_value rs p
    end.

(* TODO *)
Definition interp_frame_0 (rs : relations) : R.locals_typeO -n> WsR :=
  λne _, λne _, ⌜false⌝%I.

(* TODO *)
Definition interp_expr_0 (rs : relations) :
  leibnizO R.result_type -n>
  R.labels_typeO -n>
  R.ret_typeO -n>
  R.locals_typeO -n>
  leibnizO instance -n>
  leibnizO (lholed * list administrative_instruction) -n>
  iPropO Σ :=
  λne _ _ _ _ _ _, ⌜false⌝%I.

Definition rels_0 (rs : relations) : relations :=
  (interp_value_0 rs,
   interp_frame_0 rs,
   interp_expr_0 rs).

Instance interp_value_0_contractive :
  Contractive interp_value_0.
Proof.
  Opaque interp_pre_value.
  intros n rels rels' Hrels ty.
  destruct ty.
  solve_contractive.
Qed.

Instance interp_frame_0_contractive :
    Contractive interp_frame_0.
Proof.
  solve_contractive.
Qed.

Instance interp_expr_0_contractive :
  Contractive interp_expr_0.
Proof.
  solve_contractive.
Qed.

Instance rels_contractive : Contractive rels_0.
Proof.
  solve_contractive.
Qed.

Definition rels : relations := fixpoint rels_0.

Definition interp_value := rels_value rels.
Definition interp_frame := rels_frame rels.
Definition interp_expr := rels_expr rels.

Definition interp_val (τs : R.result_type) : VR :=
  λne (v : leibnizO val), (
    ⌜v = trapV⌝ ∨
    ∃ ws, ⌜v = immV ws⌝ ∗ interp_values rels τs (Stack ws)
  )%I.

Definition interp_inst
  (S: R.store_typing) 
  (M: R.module_typing) 
  (inst: instance)
  : iProp Σ :=
  ⌜true⌝%I.

Definition interp_ctx
  (L L': R.locals_type) 
  (F: R.function_typing) 
  (inst: instance)
  (lh: lholed)
  : iProp Σ :=
  ⌜true⌝%I.

Definition semantic_typing 
  (S: R.store_typing) 
  (M: R.module_typing) 
  (F: R.function_typing) 
  (L: R.locals_type) 
  (es: list administrative_instruction) 
  (τs1 τs2 : list R.value_type) 
  (L': R.locals_type) 
  : iProp Σ :=
  ∀ inst lh,
    interp_inst S M inst ∗ interp_ctx L L' F inst lh -∗
    ∀ vls vs,
      interp_val τs1 vs ∗ 
      (* frame points to F ∗ *)
      interp_frame L vls ∗
      interp_expr τs2 F.(R.fn_label_type) F.(R.fn_ret_type) L' inst (lh, (of_val vs ++ es)).

End logrel.
