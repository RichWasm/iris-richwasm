Require Import iris.proofmode.tactics.

From RichWasm.compiler Require Import codegen util.
From RichWasm.iris Require Import gc memory.
From RichWasm.iris.language Require Import iris_wp_def lenient_wp logpred.
From RichWasm Require Import syntax typing layout util.

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
  | SWords (cm : concrete_memory) (ws : list word).

  Notation SVR := (leibnizO semantic_value -n> iPropO Σ).
  Notation LVR := (leibnizO val -n> iPropO Σ).
  Notation VsR := (leibnizO (list value) -n> iPropO Σ).
  Notation FrR := (leibnizO frame -n> iPropO Σ).
  Notation ClR := (leibnizO function_closure -n> iPropO Σ).
  Notation ER := (leibnizO (list administrative_instruction) -n> iPropO Σ).

  Implicit Type L : leibnizO local_ctx.
  Implicit Type WL : leibnizO wlocal_ctx.

  Implicit Type es : leibnizO (list administrative_instruction).
  Implicit Type sv : leibnizO semantic_value.
  Implicit Type lv : leibnizO val.
  Implicit Type vs : leibnizO (list value).
  Implicit Type ws : leibnizO (list word).
  Implicit Type bs : leibnizO bytes.
  Implicit Type fr : leibnizO frame.
  Implicit Type cl : leibnizO function_closure.
  Implicit Type inst : leibnizO instance.

  Implicit Type τ : leibnizO type.
  Implicit Type τs : leibnizO (list type).
  Implicit Type ϕ : leibnizO function_type.
  Implicit Type ψ : leibnizO instruction_type.

  Definition relation_bundle : Type :=
    (* Value *)
    (leibnizO type -n> SVR) *
    (* Frame *)
    (leibnizO local_ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FrR) *
    (* Expression *)
    (leibnizO (list type) -n> leibnizO function_ctx -n> leibnizO local_ctx -n>
       leibnizO wlocal_ctx -n> leibnizO instance -n> leibnizO lholed -n> ER).

  Definition rb_value : relation_bundle -> leibnizO type -n> SVR :=
    fst ∘ fst.

  Definition rb_frame :
    relation_bundle ->
    leibnizO local_ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FrR :=
    snd ∘ fst.

  Definition rb_expr :
    relation_bundle ->
    leibnizO (list type) -n> leibnizO function_ctx -n> leibnizO local_ctx -n>
      leibnizO wlocal_ctx -n> leibnizO instance -n> leibnizO lholed -n> ER :=
    snd.

  Definition semantic_type : Type := semantic_value -> iProp Σ.

  Definition semantic_kind : Type := semantic_type -> iProp Σ.

  Definition value_type_interp (ty : W.value_type) (v : value) : Prop :=
    match ty with
    | T_i32 => exists n, v = VAL_int32 n
    | T_i64 => exists n, v = VAL_int64 n
    | T_f32 => exists n, v = VAL_float32 n
    | T_f64 => exists n, v = VAL_float64 n
    end.

  Definition result_type_interp (tys : W.result_type) (vs : list value) : Prop :=
    Forall2 value_type_interp tys vs.

  Definition primitive_rep_interp (ι : primitive_rep) (v : value) : Prop :=
    match ι with
    | PtrR => exists n, v = VAL_int32 n
    | I32R => exists n, v = VAL_int32 n
    | I64R => exists n, v = VAL_int64 n
    | F32R => exists n, v = VAL_float32 n
    | F64R => exists n, v = VAL_float64 n
    end.

  Definition representation_interp0 (ρ : representation) (vs : list value) : Prop :=
    exists ιs, eval_rep ρ = Some ιs /\ Forall2 primitive_rep_interp ιs vs.

  Definition representation_interp (ρ : representation) : semantic_type :=
    fun sv => (∃ vs, ⌜sv = SValues vs⌝ ∗ ⌜representation_interp0 ρ vs⌝)%I.

  Definition copyability_interp (χ : copyability) (T : semantic_type) : Prop :=
    match χ with
    | NoCopy => True
    | ExCopy => False (* TODO *)
    | ImCopy => forall sv, Persistent (T sv)
    end.

  Definition size_interp (σ : size) (ws : list word) : Prop :=
    eval_size σ = Some (length ws).

  Definition sizity_interp (ζ : sizity) : semantic_type :=
    fun sv => (∃ μ ws, ⌜sv = SWords μ ws⌝ ∗ ∀ σ, ⌜ζ = Sized σ⌝ -∗ ⌜size_interp σ ws⌝)%I.

  Definition memory_interp (μ : memory) : semantic_type :=
    fun sv => (∃ cm ws, ⌜μ = ConstM cm⌝ ∗ ⌜sv = SWords cm ws⌝)%I.

  (* S refines T, written S ⊑ T. *)
  Definition semantic_type_le (S T : semantic_type) : Prop :=
    forall sv, S sv -∗ T sv.

  Instance SqSubsetEq_semantic_type : SqSubsetEq semantic_type :=
    semantic_type_le.

  Definition kind_interp (κ : kind) : semantic_kind :=
    match κ with
    | VALTYPE ρ χ _ => fun T => (⌜T ⊑ representation_interp ρ⌝ ∗ ⌜copyability_interp χ T⌝)%I
    | MEMTYPE ζ μ _ => fun T => (⌜T ⊑ sizity_interp ζ⌝ ∗ ⌜T ⊑ memory_interp μ⌝)%I
    end.

  Definition values_interp0 (rb : relation_bundle) : leibnizO (list type) -n> VsR :=
    λne τs vs,
      (∃ vss, ⌜vs = concat vss⌝ ∗ [∗ list] τ; vs ∈ τs; vss, rb_value rb τ (SValues vs))%I.

  Definition mono_closure_interp0 (rb : relation_bundle) : leibnizO instruction_type -n> ClR :=
    λne ψ cl,
      let 'InstrT τs1 τs2 := ψ in
      match cl with
      | FC_func_native inst (Tf tfs1 tfs2) tlocs es =>
          ⌜translate_types [] τs1 = Some tfs1⌝ ∗
          ⌜translate_types [] τs2 = Some tfs2⌝ ∗
          ∀ vs1 fr,
            values_interp0 rb τs1 vs1 -∗
            ↪[frame] fr -∗
            lenient_wp NotStuck top
              [AI_local (length tfs2) (Build_frame (vs1 ++ n_zeros tlocs) inst) (to_e_list es)]
              {| lp_fr := fun fr' => ⌜fr = fr'⌝;
                 lp_val := fun vs2 => values_interp0 rb τs2 vs2 ∗ ↪[RUN];
                 lp_trap := True;
                 lp_br := fun _ => False;
                 lp_ret := fun _ => False;
                 lp_host := fun _ _ _ _ => False |}
        | FC_func_host _ _ => False
        end%I.

  Definition closure_interp0 (rb : relation_bundle) : leibnizO function_type -n> ClR :=
    λne ϕ cl,
      match ϕ with
      | MonoFunT ψ => mono_closure_interp0 rb ψ cl
      | ForallMemT ϕ' => True (* TODO *)
      | ForallRepT ϕ' => True (* TODO *)
      | ForallSizeT ϕ' => True (* TODO *)
      | ForallTypeT κ ϕ' => True (* TODO *)
      end%I.

  (* Fact: If |- τ : κ, then kind_interp κ (value_interp τ).
     TODO: Some of the definitions in value_interp0 may be too permissive.
           Incorpoate kind_interp into this definition? *)
  Definition value_interp0 (rb : relation_bundle) : leibnizO type -n> SVR :=
    λne τ sv,
      match τ with
      | VarT _ => False
      | NumT _ _ => True
      | SumT (VALTYPE ρ _ _) τs =>
          ∃ i vs vs0 τ0 ρs ρ0 ixs,
            ⌜sv = SValues (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat i)) :: vs)⌝ ∗
              ⌜ρ = SumR ρs⌝ ∗
              ⌜τs !! i = Some τ⌝ ∗
              ⌜type_rep [] τ0 = Some ρ0⌝ ∗
              ⌜inject_sum_rep ρs ρ = Some ixs⌝ ∗
              ⌜nths_error vs ixs = Some vs0⌝ ∗
              ▷ rb_value rb τ0 (SValues vs0)
      | SumT (MEMTYPE _ (VarM _) _) _ => False
      | SumT (MEMTYPE _ (ConstM cm) _) τs =>
          ∃ wᵢ ws ws' bsᵢ i τ,
            ⌜sv = SWords cm (wᵢ :: ws ++ ws')⌝ ∗
              ⌜bsᵢ = serialize_Z_i32 (Z.of_nat i)⌝ ∗
              ⌜repr_word sr.(sr_gc_heap_start) ∅ wᵢ i⌝ ∗
              ⌜τs !! i = Some τ⌝ ∗
              ▷ rb_value rb τ (SWords cm ws)
      | ProdT (VALTYPE _ _ _) τs =>
          ∃ vss, ⌜sv = SValues (concat vss)⌝ ∗ [∗ list] vs; τ ∈ vss; τs, ▷ rb_value rb τ (SValues vs)
      | ProdT (MEMTYPE _ (VarM _) _) _ => False
      | ProdT (MEMTYPE _ (ConstM cm) _) τs =>
          ∃ wss,
            ⌜sv = SWords cm (concat wss)⌝ ∗ [∗ list] ws; τ ∈ wss; τs, ▷ rb_value rb τ (SWords cm ws)
      | RefT _ (VarM _) _ => False
      | RefT _ (ConstM MemMM) τ =>
          ∃ a ws ns bs,
            ⌜sv = SValues [VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N a))]⌝ ∗
              N.of_nat sr.(sr_mem_mm) ↦[wms][a] bs ∗
              ⌜repr_list_word sr.(sr_gc_heap_start) ∅ ws ns⌝ ∗
              ⌜bs = flat_map serialize_Z_i32 ns⌝ ∗
              ▷ rb_value rb τ (SWords MemMM ws)
      | RefT _ (ConstM MemGC) τ =>
          ∃ a ℓ,
            ⌜sv = SValues [VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N a))]⌝ ∗
              a ↦gcr ℓ ∗
              na_inv logrel_nais (ns_ref ℓ) (∃ ws, ℓ ↦gco ws ∗ ▷ rb_value rb τ (SWords MemGC ws))
      | GCPtrT _ τ =>
          ∃ ℓ,
            ⌜sv = SWords MemGC [WordPtr (PtrGC ℓ)]⌝ ∗
              na_inv logrel_nais (ns_ref ℓ) (∃ ws, ℓ ↦gco ws ∗ ▷ rb_value rb τ (SWords MemGC ws))
      | CodeRefT _ ϕ =>
          ∃ n cl,
            ⌜sv = SValues [VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N n))]⌝ ∗
              ▷ closure_interp0 rb ϕ cl ∗
              na_inv logrel_nais (ns_func n) (n ↦[wf] cl)
      | RepT _ ρ' τ =>
          ∃ ρ ιs ιs' vs vs' rvs rvs' wss wss' ws,
            ⌜sv = SValues vs'⌝ ∗
              ⌜type_rep [] τ = Some ρ⌝ ∗
              ⌜eval_rep ρ = Some ιs⌝ ∗
              ⌜eval_rep ρ' = Some ιs'⌝ ∗
              ⌜to_rep_values ιs vs = Some rvs⌝ ∗
              ⌜to_rep_values ιs' vs' = Some rvs'⌝ ∗
              ⌜Forall2 (ser_value sr.(sr_gc_heap_start)) rvs wss⌝ ∗
              ⌜Forall2 (ser_value sr.(sr_gc_heap_start)) rvs' wss'⌝ ∗
              ⌜concat wss ++ ws = concat wss'⌝ ∗
              ▷ rb_value rb τ (SValues vs)
      | PadT (VALTYPE _ _ _) _ _ => False
      | PadT (MEMTYPE _ (VarM _) _) _ _ => False
      | PadT (MEMTYPE _ (ConstM cm) _) _ τ =>
          ∃ ws wsₚ, ⌜sv = SWords cm (ws ++ wsₚ)⌝ ∗ ▷ rb_value rb τ (SWords cm ws)
      | SerT (VALTYPE _ _ _) _ => False
      | SerT (MEMTYPE _ (VarM _) _) _ => False
      | SerT (MEMTYPE _ (ConstM cm) _) τ =>
          ∃ ρ ιs vs rvs ws wss,
            ⌜sv = SWords cm ws⌝ ∗
              ⌜type_rep [] τ = Some ρ⌝ ∗
              ⌜eval_rep ρ = Some ιs⌝ ∗
              ⌜to_rep_values ιs vs = Some rvs⌝ ∗
              ⌜Forall2 (ser_value sr.(sr_gc_heap_start)) rvs wss⌝ ∗
              ⌜ws = concat wss⌝ ∗
              ▷ rb_value rb τ (SValues vs)
      | RecT κ τ =>
          let τ' := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
          ▷ rb_value rb τ' sv
      | ExistsMemT _ τ =>
          ∃ μ,
            let τ' := subst_type (unscoped.scons μ VarM) VarR VarS VarT τ in
            ▷ rb_value rb τ' sv
      | ExistsRepT _ τ =>
          ∃ ρ,
            let τ' := subst_type VarM (unscoped.scons ρ VarR) VarS VarT τ in
            ▷ rb_value rb τ' sv
      | ExistsSizeT _ τ =>
          ∃ σ,
            let τ' := subst_type VarM VarR (unscoped.scons σ VarS) VarT τ in
            ▷ rb_value rb τ' sv
      | ExistsTypeT _ κ τ =>
          ∃ τ0,
            ▷ kind_interp κ (rb_value rb τ0) ∗
            let τ' := subst_type VarM VarR VarS (unscoped.scons τ0 VarT) τ in
            ▷ rb_value rb τ' sv
      end%I.

  Definition frame_interp0 (rb : relation_bundle) :
    leibnizO local_ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FrR :=
    λne L WL inst fr,
      (∃ vs__L vs__WL,
         ⌜fr = Build_frame (vs__L ++ vs__WL) inst⌝ ∗
           values_interp0 rb L vs__L ∗
           ⌜result_type_interp WL vs__WL⌝ ∗
           na_own logrel_nais ⊤)%I.

  Definition expr_interp0 (rb : relation_bundle) :
    leibnizO (list type) -n> leibnizO function_ctx -n> leibnizO local_ctx -n> leibnizO wlocal_ctx -n>
      leibnizO instance -n> leibnizO lholed -n> ER :=
    λne τs F L WL inst lh es,
      lenient_wp NotStuck top es
                 {| lp_fr := frame_interp0 rb L WL inst;
                    lp_val := fun vs => values_interp0 rb τs vs ∗ ↪[RUN];
                    lp_trap := True;
                    lp_br := fun _ => True; (* TODO *)
                    lp_ret := fun _ => True; (* TODO *)
                    lp_host := fun _ _ _ _ => True (* TODO *) |}%I.

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
      leibnizO instance -n> leibnizO lholed -n> ER :=
    rb_expr relations.

  Lemma relations_eq : relations ≡ relations0 relations.
  Proof. apply fixpoint_unfold. Qed.

  Definition logical_value_interp : leibnizO (list type) -n> LVR.
  Admitted.

  Definition instance_interp (M : module_ctx) (inst : instance) : iProp Σ :=
    True.

  Definition context_interp (F : function_ctx) (L L' : local_ctx) (inst : instance) (lh : lholed) :
    iProp Σ :=
    True.

  Definition has_type_semantic
    (M : module_ctx) (F : function_ctx) (L : local_ctx) (WL : wlocal_ctx)
    (es : list administrative_instruction)
    '(InstrT τs1 τs2 : instruction_type) (L' : local_ctx) :
    iProp Σ :=
    (∀ inst lh,
       instance_interp M inst ∗ context_interp F L L' inst lh -∗
       ∀ fr lv,
         logical_value_interp τs1 lv ∗ frame_interp L WL inst fr ∗ ↪[frame] fr -∗
         expr_interp τs2 F L' WL inst lh (of_val lv ++ es))%I.

End Relations.
