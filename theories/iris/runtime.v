From RichWasm.iris.language Require Import lenient_wp logpred.
From RichWasm.iris Require Import gc memory util.
From iris.proofmode Require Import base tactics classes.
From RichWasm.iris.rules Require Import iris_rules proofmode.

Section Runtime.

  Context `{wasmG Σ}.
  Context `{RichWasmGCG Σ}.

  Variable sr : store_runtime.
  Variable gci : gc_invariant Σ.

  Definition spec_alloc_mm (cl : function_closure) : Prop :=
    (* TODO *)
    True.

  Definition spec_alloc_gc (cl : function_closure) : Prop :=
    forall θ sz pm fr,
      let ks := kinds_of_pointer_map pm (Wasm_int.nat_of_uint i32m sz) in
      gc_token sr gci θ -∗
      N.of_nat sr.(sr_func_alloc_gc) ↦[wf] cl -∗
      ↪[frame] fr -∗
      ↪[RUN] -∗
      lenient_wp NotStuck top
        [AI_basic (BI_const (VAL_int32 sz));
         AI_basic (BI_const (VAL_int64 pm));
         AI_invoke sr.(sr_func_alloc_gc)]
        {| lp_fr := fun fr' => ⌜fr = fr'⌝ ∗ ↪[frame] fr';
           lp_val :=
             fun vs =>
               ↪[RUN] ∗
                 N.of_nat sr.(sr_func_alloc_gc) ↦[wf] cl ∗
                 ∃ θ' ℓ a ws,
                   ⌜vs = [VAL_int32 (Wasm_int.int_of_Z i32m a)]⌝ ∗
                     ⌜repr_location θ' ℓ a⌝ ∗
                     gc_token sr gci θ' ∗
                     ℓ ↦gcl ks ∗
                     ℓ ↦gco ws;
           lp_trap := True;
           lp_br := fun _ => False;
           lp_ret := fun _ => False;
           lp_host := fun _ _ _ _ => False |}.

  Definition spec_free (cl : function_closure) : Prop :=
    (* TODO *)
    True.

  Definition spec_registerroot (cl : function_closure) : Prop :=
    forall θ ℓ a fr,
      repr_location θ ℓ (Wasm_int.Z_of_uint i32m a) ->
      gc_token sr gci θ -∗
      N.of_nat sr.(sr_func_registerroot) ↦[wf] cl -∗
      ↪[RUN] -∗
      ↪[frame] fr -∗
      lenient_wp NotStuck top
        [AI_basic (BI_const (VAL_int32 a)); AI_invoke sr.(sr_func_registerroot)]
        {| lp_fr := fun fr' => ⌜fr = fr'⌝ ∗ ↪[frame] fr';
           lp_val :=
             fun vs =>
               ↪[RUN] ∗
                 N.of_nat sr.(sr_func_registerroot) ↦[wf] cl ∗
                 gc_token sr gci θ ∗
                 ∃ a', ⌜vs = [VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N a'))]⌝ ∗ a' ↦gcr ℓ;
           lp_trap := True;
           lp_br := fun _ => False;
           lp_ret := fun _ => False;
           lp_host := fun _ _ _ _ => False |}.

  Definition spec_unregisterroot (cl : function_closure) : Prop :=
    forall θ ℓ a fr,
      gc_token sr gci θ -∗
      Wasm_int.N_of_uint i32m a ↦gcr ℓ -∗
      N.of_nat sr.(sr_func_unregisterroot) ↦[wf] cl -∗
      ↪[RUN] -∗
      ↪[frame] fr -∗
      lenient_wp NotStuck top
        [AI_basic (BI_const (VAL_int32 a)); AI_invoke sr.(sr_func_unregisterroot)]
        {| lp_fr := fun fr' => ⌜fr = fr' ⌝ ∗ ↪[frame] fr';
           lp_val :=
             fun vs =>
               ↪[RUN] ∗
                 N.of_nat sr.(sr_func_unregisterroot) ↦[wf] cl ∗
                 gc_token sr gci θ ∗
                 ∃ a', ⌜vs = [VAL_int32 (Wasm_int.int_of_Z i32m a')]⌝ ∗ ⌜repr_location θ ℓ a'⌝;
           lp_trap := True;
           lp_br := fun _ => False;
           lp_ret := fun _ => False;
           lp_host := fun _ _ _ _ => False |}.

End Runtime.
