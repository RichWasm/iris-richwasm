Require Import RecordUpdate.RecordUpdate.

From RichWasm Require Import syntax util.
From RichWasm.iris Require Import memory util numerics.
From RichWasm.iris.language Require Import cwp logpred.

Section Runtime.

  Context `{wasmG Σ}.
  Context `{richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.

  Definition spec_mmalloc (cl : function_closure) : Prop :=
    forall s E B R fr θ sz i,
      let sz' := Wasm_int.nat_of_uint i32m sz in
      rt_token rti sr θ -∗
      N.of_nat sr.(sr_func_mmalloc) ↦[wf] cl -∗
      ↪[frame] fr -∗
      ↪[RUN] -∗
      ⌜inst_funcs (f_inst fr) !! i = Some sr.(sr_func_mmalloc)⌝ -∗
      CWP [BI_const (VAL_int32 sz); BI_call i ] @ s; E UNDER B; R
          {{ fr'; vs,
               ⌜fr' = fr⌝ ∗
               N.of_nat sr.(sr_func_mmalloc) ↦[wf] cl ∗
               ∃ θ' ℓ a ws,
                 ⌜vs = [VAL_int32 (Wasm_int.int_of_Z i32m (tag_address MemMM a))]⌝ ∗
                 ⌜repr_root_pointer (RootHeap MemMM a) (tag_address MemMM a)⌝ ∗
                 rt_token rti sr θ' ∗
                 ℓ ↦addr (MemMM, a) ∗
                 ℓ ↦layout repeat FlagInt sz' ∗
                 ℓ ↦heap ws }}.

  Definition spec_gcalloc (cl : function_closure) : Prop :=
    forall s E B R fr θ sz i,
      let sz' := Wasm_int.nat_of_uint i32m sz in
      rt_token rti sr θ -∗
      N.of_nat sr.(sr_func_gcalloc) ↦[wf] cl -∗
      ↪[frame] fr -∗
      ↪[RUN] -∗
      ⌜inst_funcs (f_inst fr) !! i = Some sr.(sr_func_gcalloc)⌝ -∗
      CWP [BI_const (VAL_int32 sz); BI_call i] @ s; E UNDER B; R
        {{ fr'; vs,
             ⌜fr = fr'⌝ ∗
             N.of_nat sr.(sr_func_gcalloc) ↦[wf] cl ∗
             ∃ θ' ℓ ta ws,
               ⌜vs = [VAL_int32 (Wasm_int.int_of_Z i32m ta)]⌝ ∗
                 ⌜repr_pointer θ' (PtrHeap MemGC ℓ) ta⌝ ∗
                 rt_token rti sr θ' ∗
                 ℓ ↦layout repeat FlagInt sz' ∗
                 ℓ ↦heap ws }}.

  Definition spec_free (cl : function_closure) : Prop :=
    forall s E B R fr i θ ℓ a ta,
      ta = Wasm_int.int_of_Z i32m (tag_address MemMM a) ->
      repr_root_pointer (RootHeap MemMM a) (tag_address MemMM a) ->
      rt_token rti sr θ -∗
      N.of_nat sr.(sr_func_mmalloc) ↦[wf] cl -∗
      ℓ ↦addr (MemMM, a) -∗
      ↪[frame] fr -∗
      ↪[RUN] -∗
      ⌜inst_funcs (f_inst fr) !! i = Some sr.(sr_func_free)⌝ -∗
      CWP
        [BI_const (VAL_int32 ta); BI_call i]
        @ s; E UNDER B; R
        {{ fr'; vs, ⌜fr = fr'⌝ ∗
             ⌜vs = []⌝ ∗ N.of_nat sr.(sr_func_free) ↦[wf] cl ∗ ∃ θ', rt_token rti sr θ' }}.

  Definition spec_setflag (cl : function_closure) : Prop :=
    forall s E B R fr idx θ ℓ fs μ ta i f,
      let ta' := Wasm_int.Z_of_uint i32m ta in
      let i' := Wasm_int.nat_of_uint i32m i in
      repr_pointer θ (PtrHeap μ ℓ) ta' ->
      rt_token rti sr θ -∗
      ℓ ↦layout fs -∗
      N.of_nat sr.(sr_func_setflag) ↦[wf] cl ∗
      ↪[frame] fr -∗
      ↪[RUN] -∗
      ⌜inst_funcs (f_inst fr) !! idx = Some sr.(sr_func_setflag)⌝ -∗
      CWP
        [BI_const (VAL_int32 ta);
         BI_const (VAL_int32 i);
         BI_const (VAL_int32 f);
         BI_call idx]
        @ s; E UNDER B; R
        {{ fr'; vs, ⌜fr = fr'⌝ ∗
             ⌜vs = []⌝ ∗
             N.of_nat sr.(sr_func_setflag) ↦[wf] cl ∗
             ℓ ↦layout <[ i' := flag_of_i32 f ]> fs ∗
             ∃ θ', rt_token rti sr θ' }}.

  Definition spec_registerroot (cl : function_closure) : Prop :=
    forall s E B R fr idx θ ℓ tah,
      let tah' := Wasm_int.Z_of_uint i32m tah in
      repr_pointer θ (PtrHeap MemGC ℓ) tah' ->
      rt_token rti sr θ -∗
      N.of_nat sr.(sr_func_registerroot) ↦[wf] cl -∗
      ↪[frame] fr -∗
      ↪[RUN] -∗
      ⌜inst_funcs (f_inst fr) !! idx = Some sr.(sr_func_registerroot)⌝ -∗
      CWP [BI_const (VAL_int32 tah); BI_call idx]
          @ s; E UNDER B; R
          {{ fr'; vs, ⌜fr = fr'⌝ ∗
               N.of_nat sr.(sr_func_registerroot) ↦[wf] cl ∗
               ∃ θ' ar,
                 ⌜vs = [VAL_int32 (Wasm_int.int_of_Z i32m (tag_address MemGC ar))]⌝ ∗
                 ⌜repr_root_pointer (RootHeap MemGC ar) (tag_address MemGC ar)⌝ ∗
                 ar ↦root ℓ ∗
                 rt_token rti sr θ' }}.

  Definition spec_unregisterroot (cl : function_closure) : Prop :=
    forall s E B R fr idx θ ℓ ar tar,
      let tar' := Wasm_int.Z_of_uint i32m tar in
      repr_root_pointer (RootHeap MemGC ar) tar' ->
      rt_token rti sr θ -∗
      ar ↦root ℓ -∗
      N.of_nat sr.(sr_func_unregisterroot) ↦[wf] cl -∗
      ↪[frame] fr -∗
      ↪[RUN] -∗
      ⌜inst_funcs (f_inst fr) !! idx = Some sr.(sr_func_unregisterroot)⌝ -∗
      CWP [BI_const (VAL_int32 tar); BI_call sr.(sr_func_unregisterroot)]
        @ s; E UNDER B; R
        {{ fr'; vs,
             ⌜fr = fr'⌝ ∗
             ⌜vs = []⌝ ∗
             N.of_nat sr.(sr_func_unregisterroot) ↦[wf] cl ∗
             ∃ θ', rt_token rti sr θ' }}.

End Runtime.
