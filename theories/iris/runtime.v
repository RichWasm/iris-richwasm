Require Import RecordUpdate.RecordUpdate.

From RichWasm Require Import syntax util.
From RichWasm.iris Require Import memory util.
From RichWasm.iris.language Require Import lenient_wp logpred.

Section Runtime.

  Context `{wasmG Σ}.
  Context `{richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.

  Definition spec_mmalloc (cl : function_closure) : Prop :=
    forall fr θ sz,
      let sz' := Wasm_int.nat_of_uint i32m sz in
      rt_token rti sr θ -∗
      N.of_nat sr.(sr_func_mmalloc) ↦[wf] cl -∗
      ↪[frame] fr -∗
      ↪[RUN] -∗
      lenient_wp NotStuck top
        [AI_basic (BI_const (VAL_int32 sz)); AI_invoke sr.(sr_func_mmalloc)]
        {| lp_fr := fun _ => True;
           lp_fr_inv := fun fr' => ⌜fr = fr'⌝;
           lp_val :=
            fun vs =>
              ↪[RUN] ∗
                N.of_nat sr.(sr_func_mmalloc) ↦[wf] cl ∗
                ∃ θ' ℓ a ws,
                  ⌜vs = [VAL_int32 (Wasm_int.int_of_Z i32m (tag_address MemMM a))]⌝ ∗
                    ⌜repr_root_pointer (RootHeap MemMM a) (tag_address MemMM a)⌝ ∗
                    rt_token rti sr θ' ∗
                    ℓ ↦addr (MemMM, a) ∗
                    ℓ ↦layout repeat FlagInt sz' ∗
                    ℓ ↦heap ws;
           lp_trap := True;
           lp_br := fun _ _ => False;
           lp_ret := fun _ => False;
           lp_host := fun _ _ _ _ => False |}.

  Definition spec_gcalloc (cl : function_closure) : Prop :=
    forall fr θ sz,
      let sz' := Wasm_int.nat_of_uint i32m sz in
      rt_token rti sr θ -∗
      N.of_nat sr.(sr_func_gcalloc) ↦[wf] cl -∗
      ↪[frame] fr -∗
      ↪[RUN] -∗
      lenient_wp NotStuck top
        [AI_basic (BI_const (VAL_int32 sz)); AI_invoke sr.(sr_func_gcalloc)]
        {| lp_fr := fun _ => True;
           lp_fr_inv := fun fr' => ⌜fr = fr'⌝;
           lp_val :=
             fun vs =>
               ↪[RUN] ∗
                 N.of_nat sr.(sr_func_gcalloc) ↦[wf] cl ∗
                 ∃ θ' ℓ ta ws,
                   ⌜vs = [VAL_int32 (Wasm_int.int_of_Z i32m ta)]⌝ ∗
                     ⌜repr_pointer θ' (PtrHeap MemGC ℓ) ta⌝ ∗
                     rt_token rti sr θ' ∗
                     ℓ ↦layout repeat FlagInt sz' ∗
                     ℓ ↦heap ws;
           lp_trap := True;
           lp_br := fun _ _ => False;
           lp_ret := fun _ => False;
           lp_host := fun _ _ _ _ => False |}.

  Definition spec_free (cl : function_closure) : Prop :=
    forall fr θ ℓ a ta,
      ta = Wasm_int.int_of_Z i32m (tag_address MemMM a) ->
      repr_root_pointer (RootHeap MemMM a) (tag_address MemMM a) ->
      rt_token rti sr θ -∗
      N.of_nat sr.(sr_func_mmalloc) ↦[wf] cl -∗
      ℓ ↦addr (MemMM, a) -∗
      ↪[frame] fr -∗
      ↪[RUN] -∗
      lenient_wp NotStuck top
        [AI_basic (BI_const (VAL_int32 ta)); AI_invoke sr.(sr_func_free)]
        {| lp_fr := fun _ => True;
           lp_fr_inv := fun fr' => ⌜fr = fr'⌝;
           lp_val :=
             fun vs =>
               ⌜vs = []⌝ ∗ ↪[RUN] ∗ N.of_nat sr.(sr_func_free) ↦[wf] cl ∗ ∃ θ', rt_token rti sr θ';
           lp_trap := True;
           lp_br := fun _ _ => False;
           lp_ret := fun _ => False;
           lp_host := fun _ _ _ _ => False |}.

  Definition spec_setflag (cl : function_closure) : Prop :=
    forall fr θ ℓ fs μ ta i f,
      let ta' := Wasm_int.Z_of_uint i32m ta in
      let i' := Wasm_int.nat_of_uint i32m i in
      repr_pointer θ (PtrHeap μ ℓ) ta' ->
      rt_token rti sr θ -∗
      ℓ ↦layout fs -∗
      N.of_nat sr.(sr_func_setflag) ↦[wf] cl ∗
      ↪[frame] fr -∗
      ↪[RUN] -∗
      lenient_wp NotStuck top
        [AI_basic (BI_const (VAL_int32 ta));
         AI_basic (BI_const (VAL_int32 i));
         AI_basic (BI_const (VAL_int32 f));
         AI_invoke sr.(sr_func_setflag)]
        {| lp_fr := fun _ => True;
           lp_fr_inv := fun fr' => ⌜fr = fr'⌝;
           lp_val :=
             fun vs =>
               ⌜vs = []⌝ ∗
                 ↪[RUN] ∗
                 N.of_nat sr.(sr_func_setflag) ↦[wf] cl ∗
                 ℓ ↦layout <[ i' := flag_of_i32 f ]> fs ∗
                 ∃ θ', rt_token rti sr θ';
           lp_trap := True;
           lp_br := fun _ _ => False;
           lp_ret := fun _ => False;
           lp_host := fun _ _ _ _ => False |}.

  Definition spec_registerroot (cl : function_closure) : Prop :=
    forall fr θ ℓ tah,
      let tah' := Wasm_int.Z_of_uint i32m tah in
      repr_pointer θ (PtrHeap MemGC ℓ) tah' ->
      rt_token rti sr θ -∗
      N.of_nat sr.(sr_func_registerroot) ↦[wf] cl -∗
      ↪[frame] fr -∗
      ↪[RUN] -∗
      lenient_wp NotStuck top
        [AI_basic (BI_const (VAL_int32 tah)); AI_invoke sr.(sr_func_registerroot)]
        {| lp_fr := fun _ => True;
           lp_fr_inv := fun fr' => ⌜fr = fr'⌝;
           lp_val :=
             fun vs =>
               ↪[RUN] ∗
                 N.of_nat sr.(sr_func_registerroot) ↦[wf] cl ∗
                 ∃ θ' ar,
                   ⌜vs = [VAL_int32 (Wasm_int.int_of_Z i32m (tag_address MemGC ar))]⌝ ∗
                     ⌜repr_root_pointer (RootHeap MemGC ar) (tag_address MemGC ar)⌝ ∗
                     ar ↦root ℓ ∗
                     rt_token rti sr θ';
           lp_trap := True;
           lp_br := fun _ _ => False;
           lp_ret := fun _ => False;
           lp_host := fun _ _ _ _ => False |}.

  Definition spec_unregisterroot (cl : function_closure) : Prop :=
    forall fr θ ℓ ar tar,
      let tar' := Wasm_int.Z_of_uint i32m tar in
      repr_root_pointer (RootHeap MemGC ar) tar' ->
      rt_token rti sr θ -∗
      ar ↦root ℓ -∗
      N.of_nat sr.(sr_func_unregisterroot) ↦[wf] cl -∗
      ↪[frame] fr -∗
      ↪[RUN] -∗
      lenient_wp NotStuck top
        [AI_basic (BI_const (VAL_int32 tar)); AI_invoke sr.(sr_func_unregisterroot)]
        {| lp_fr := fun _ => True;
           lp_fr_inv := fun fr' => ⌜fr = fr'⌝;
           lp_val :=
             fun vs =>
               ⌜vs = []⌝ ∗
                 ↪[RUN] ∗
                 N.of_nat sr.(sr_func_unregisterroot) ↦[wf] cl ∗
                 ∃ θ', rt_token rti sr θ';
           lp_trap := True;
           lp_br := fun _ _ => False;
           lp_ret := fun _ => False;
           lp_host := fun _ _ _ _ => False |}.

End Runtime.
