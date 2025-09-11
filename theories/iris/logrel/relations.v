From mathcomp Require Import eqtype seq.

Require Import iris.proofmode.tactics.

Require Wasm.iris.logrel.iris_logrel.

From RichWasm.compiler Require Import codegen types util.
From RichWasm.iris Require Import gc num_reprs util.
Require Import RichWasm.iris.logrel.util.
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

  Definition rb_value : relation_bundle -> leibnizO type -n> SVR :=
    fst ∘ fst.

  Definition rb_frame :
    relation_bundle ->
    leibnizO local_ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FrR :=
    snd ∘ fst.

  Definition rb_expr :
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

  Definition project_sum_value (τs : list type) (τ : type) (vs : list value) : list value.
  Admitted.

  Definition representation_interp0 (ρ : representation) (vs : list value) : Prop :=
    exists ιs, eval_representation ρ = Some ιs /\ Forall2 primitive_rep_interp ιs vs.

  Definition representation_interp (ρ : representation) : semantic_type :=
    fun sv => (∃ vs, ⌜sv = SValues vs⌝ ∗ ⌜representation_interp0 ρ vs⌝)%I.

  Definition copyability_interp (γ : copyability) (T : semantic_type) : Prop :=
    γ = ImCopy -> forall sv, Persistent (T sv).

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
    | VALTYPE ρ γ _ => fun T => (⌜T ⊑ representation_interp ρ⌝ ∗ ⌜copyability_interp γ T⌝)%I
    | MEMTYPE ζ _ _ => fun T => ⌜T ⊑ sizity_interp ζ⌝%I
    end.

  Definition value_interp0 (rb : relation_bundle) : leibnizO type -n> SVR :=
    λne τ sv,
      match τ with
      | VarT _ => False
      | NumT _ (IntT I32T) => ∃ n, ⌜sv = SValues [VAL_int32 n]⌝
      | NumT _ (IntT I64T) => ∃ n, ⌜sv = SValues [VAL_int64 n]⌝
      | NumT _ (FloatT F32T) => ∃ n, ⌜sv = SValues [VAL_float32 n]⌝
      | NumT _ (FloatT F64T) => ∃ n, ⌜sv = SValues [VAL_float64 n]⌝
      | SumT (VALTYPE ρ _ _) τs =>
          ∃ i vs vs0 τ,
            ⌜sv = SValues (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat i)) :: vs)⌝ ∗
              ⌜τs !! i = Some τ⌝ ∗
              ⌜project_sum_value τs τ vs = vs0⌝ ∗
              rb_value rb τ (SValues vs0)
      | SumT (MEMTYPE _ _ _) τs =>
          ∃ wᵢ ws bsᵢ i τ,
            ⌜sv = SWords (wᵢ :: ws)⌝ ∗
              ⌜bsᵢ = serialize_Z_i32 (Z.of_nat i)⌝ ∗
              ⌜repr_word sr.(sr_gc_heap_start) ∅ wᵢ i⌝ ∗
              ⌜τs !! i = Some τ⌝ ∗
              rb_value rb τ (SWords ws)
      | ProdT (VALTYPE _ _ _) τs =>
          ∃ vss, ⌜sv = SValues (concat vss)⌝ ∗ [∗ list] vs; τ ∈ vss; τs, rb_value rb τ (SValues vs)
      | ProdT (MEMTYPE _ _ _) τs =>
          ∃ wss, ⌜sv = SWords (concat wss)⌝ ∗ [∗ list] ws; τ ∈ wss; τs, rb_value rb τ (SWords ws)
      | ArrT _ τ =>
          ∃ wₙ wss bsₙ n,
            ⌜sv = SWords (wₙ :: concat wss)⌝ ∗
              ⌜bsₙ = serialize_Z_i32 n⌝ ∗
              ⌜repr_word sr.(sr_gc_heap_start) ∅ wₙ n⌝ ∗
              [∗ list] ws ∈ wss, rb_value rb τ (SWords ws)
      | RefT _ (MemVar _) _ => False
      | RefT _ MemMM τ =>
          ∃ a ws ns bs,
            ⌜sv = SValues [VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N a))]⌝ ∗
              N.of_nat sr.(sr_mem_mm) ↦[wms][a] bs ∗
              ⌜repr_list_word sr.(sr_gc_heap_start) ∅ ws ns⌝ ∗
              ⌜bs = flat_map serialize_Z_i32 ns⌝ ∗
              rb_value rb τ (SWords ws)
      | RefT _ MemGC τ =>
          ∃ a ℓ,
            ⌜sv = SValues [VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N a))]⌝ ∗
              a ↦gcr ℓ ∗
              na_inv logrel_nais (ns_ref ℓ) (∃ ws, ℓ ↦gco ws ∗ rb_value rb τ (SWords ws))
      | GCPtrT _ τ =>
          ∃ ℓ,
            ⌜sv = SWords [WordPtr (PtrGC ℓ)]⌝ ∗
              na_inv logrel_nais (ns_ref ℓ) (∃ ws, ℓ ↦gco ws ∗ rb_value rb τ (SWords ws))
      | CodeRefT _ ϕ => True (* TODO *)
      | RepT _ ρ τ => True (* TODO *)
      | PadT _ σ τ => True (* TODO *)
      | SerT _ τ => True (* TODO *)
      | RecT _ τ => True (* TODO *)
      | ExMemT _ τ => True (* TODO *)
      | ExRepT _ τ => True (* TODO *)
      | ExSizeT _ τ => True (* TODO *)
      | ExTypeT _ κ τ => True (* TODO *)
      end%I.

  Definition frame_interp0 :
    relation_bundle ->
    leibnizO local_ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FrR.
  Admitted.

  Definition expr_interp0 :
    relation_bundle ->
    leibnizO (list type) -n> leibnizO function_ctx -n> leibnizO local_ctx -n> leibnizO wlocal_ctx -n>
      leibnizO instance -n> ER.
  Admitted.

  Definition relations0 (rb : relation_bundle) : relation_bundle :=
    (value_interp0 rb, frame_interp0 rb, expr_interp0 rb).

  Instance Contractive_relations0 : Contractive relations0.
  Admitted.

  Definition relations : relation_bundle := fixpoint relations0.

  Definition value_interp : leibnizO type -n> SVR := rb_value relations.

  Definition frame_interp :
    leibnizO local_ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FrR :=
    rb_frame relations.

  Definition expr_interp :
    leibnizO (list type) -n> leibnizO function_ctx -n> leibnizO local_ctx -n> leibnizO wlocal_ctx -n>
      leibnizO instance -n> ER :=
    rb_expr relations.

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
