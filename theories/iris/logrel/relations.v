From mathcomp Require Import eqtype seq.

Require Import iris.proofmode.tactics.

Require Wasm.iris.logrel.iris_logrel.

From RichWasm.compiler Require Import codegen types util.
From RichWasm.iris Require Import gc num_reprs util.
Require Import RichWasm.iris.logrel.util.
Require Import RichWasm.util.debruijn.
Require Import RichWasm.iris.language.lenient_wp.
Require Import RichWasm.iris.language.logpred.
Import uPred.
From RichWasm Require Import syntax typing.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Relations.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!RichWasmGCG Σ}.

  Variable sr : store_runtime.

  Definition ns_func (x : N) : namespace := nroot .@ "rwf" .@ x.
  Definition ns_ref (x : N) : namespace := nroot .@ "rwr" .@ x.

  Inductive semantic_value :=
  | SValues (vs : list value)
  | SWords (ws : list word).

  Notation SVR := (leibnizO semantic_value -n> iPropO Σ).
  Notation LVR := (leibnizO val -n> iPropO Σ).
  Notation FrR := (leibnizO frame -n> iPropO Σ).
  Notation ClR := (leibnizO function_closure -n> iPropO Σ).
  Notation ER := (leibnizO (lholed * list administrative_instruction) -n> iPropO Σ).

  Implicit Type L : leibnizO local_ctx.
  Implicit Type WL : leibnizO wlocal_ctx.

  Implicit Type sv : leibnizO semantic_value.
  Implicit Type lv : leibnizO val.
  Implicit Type vs : leibnizO (list value).
  Implicit Type ws : leibnizO (list word).
  Implicit Type bs : leibnizO bytes.
  Implicit Type fr : leibnizO frame.
  Implicit Type cl : leibnizO function_closure.
  Implicit Type lh_es : leibnizO (lholed * list administrative_instruction).

  Implicit Type τ : leibnizO type.
  Implicit Type τs : leibnizO (list type).
  Implicit Type ϕ : leibnizO function_type.
  Implicit Type χ : leibnizO arrow_type.

  Definition relation_bundle : Type :=
    (* Value *)
    (leibnizO type -n> SVR) *
    (* Frame *)
    (leibnizO local_ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FrR) *
    (* Expression *)
    (leibnizO (list type) -n> leibnizO function_ctx -n> leibnizO local_ctx -n>
       leibnizO wlocal_ctx -n> leibnizO instance -n> ER).

  Definition relations_value : relation_bundle -> leibnizO type -n> SVR :=
    fst ∘ fst.

  Definition relations_frame :
    relation_bundle ->
    leibnizO local_ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FrR :=
    snd ∘ fst.

  Definition relations_expr :
    relation_bundle ->
    leibnizO (list type) -n> leibnizO function_ctx -n> leibnizO local_ctx -n>
      leibnizO wlocal_ctx -n> leibnizO instance -n> ER :=
    snd.

  Definition semantic_type : Type := semantic_value -> iProp Σ.

  Definition semantic_kind : Type := semantic_type -> iProp Σ.

  Definition primitive_rep_interp (ι : primitive_rep) (v : value) : Prop :=
    match ι with
    | PtrR => exists n, v = VAL_int32 n
    | I32R => exists n, v = VAL_int32 n
    | I64R => exists n, v = VAL_int64 n
    | F32R => exists n, v = VAL_float32 n
    | F64R => exists n, v = VAL_float64 n
    end.

  (* TODO: Returns (Some ιs) for closed representations, None for open representations. *)
  Definition eval_representation (ρ : representation) : option (list primitive_rep).
  Admitted.

  (* TODO: Returns (Some n) for closed sizes, None for open sizes. *)
  Definition eval_size (σ : size) : option nat.
  Admitted.

  Definition representation_interp0 (ρ : representation) (vs : list value) : Prop :=
    exists ιs, eval_representation ρ = Some ιs /\ Forall2 primitive_rep_interp ιs vs.

  Definition representation_interp (ρ : representation) : semantic_type :=
    fun sv => (∃ vs, ⌜sv = SValues vs⌝ ∗ ⌜representation_interp0 ρ vs⌝)%I.

  Definition linearity_interp (γ : linearity) (T : semantic_type) : Prop :=
    γ = Unr -> forall sv, Persistent (T sv).

  Definition size_interp (σ : size) (ws : list word) : Prop :=
    eval_size σ = Some (length ws).

  Definition sizity_interp (ζ : sizity) : semantic_type :=
    fun sv => (∃ ws, ⌜sv = SWords ws⌝ ∗ ∀ σ, ⌜ζ = Sized σ⌝ -∗ ⌜size_interp σ ws⌝)%I.

  (* S refines T, written S ⊑ T. *)
  Definition semantic_type_le (S T : semantic_type) : Prop :=
    forall sv, S sv -∗ T sv.

  Instance SqSubsetEq_semantic_type : SqSubsetEq semantic_type :=
    semantic_type_le.

  Definition kind_interp (κ : kind) : semantic_kind :=
    match κ with
    | VALTYPE ρ γ => fun T => (⌜T ⊑ representation_interp ρ⌝ ∗ ⌜linearity_interp γ T⌝)%I
    | MEMTYPE ζ _ γ => fun T => (⌜T ⊑ sizity_interp ζ⌝ ∗ ⌜linearity_interp γ T⌝)%I
    end.

  Definition frame_interp0 :
    relation_bundle ->
    leibnizO local_ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FrR.
  Admitted.

  Definition expr_interp0 :
    relation_bundle ->
    leibnizO (list type) -n> leibnizO function_ctx -n> leibnizO local_ctx -n> leibnizO wlocal_ctx -n>
      leibnizO instance -n> ER.
  Admitted.

  Definition relations0 : relation_bundle -> relation_bundle.
  Admitted.

  Instance Contractive_relations0 : Contractive relations0.
  Admitted.

  Definition relations : relation_bundle := fixpoint relations0.

  Definition value_interp : leibnizO type -n> SVR := relations_value relations.

  Definition frame_interp :
    leibnizO local_ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FrR :=
    relations_frame relations.

  Definition expr_interp :
    leibnizO (list type) -n> leibnizO function_ctx -n> leibnizO local_ctx -n> leibnizO wlocal_ctx -n>
      leibnizO instance -n> ER :=
    relations_expr relations.

  Lemma relations_eq : relations ≡ relations0 relations.
  Proof. apply fixpoint_unfold. Qed.

  Definition stack_interp (τs : list type) : LVR.
  Admitted.

  Definition instance_interp (M : module_ctx) (inst : instance) : iProp Σ :=
    True.

  Definition context_interp (L L' : local_ctx) (F : function_ctx) (inst : instance) (lh : lholed) :
    iProp Σ :=
    True.

  Definition has_type_semantic
    (M : module_ctx) (F : function_ctx) (L : local_ctx) (WL : wlocal_ctx)
    (es : list administrative_instruction)
    (χ : arrow_type) (L' : local_ctx) :
    iProp Σ :=
    let '(ArrowT τs1 τs2) := χ in
    ∀ inst lh,
    instance_interp M inst ∗ context_interp L L' F inst lh -∗
    ∀ fr lv,
    stack_interp τs1 lv ∗ frame_interp L WL inst fr ∗ ↪[frame] fr -∗
    expr_interp τs2 F L' WL inst (lh, of_val lv ++ es).

End Relations.
