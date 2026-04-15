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
    forall s E B R f θ sz sz32 i,
      nat_i32_repr sz sz32 ->
      f.(f_inst).(inst_funcs) !! i = Some sr.(sr_func_mmalloc) ->
      N.of_nat sr.(sr_func_mmalloc) ↦[wf] cl -∗
      rt_token rti sr θ -∗
      ↪[frame] f -∗
      ↪[RUN] -∗
      CWP [BI_const (VAL_int32 sz32); BI_call i] @ s; E UNDER B; R
          {{ f'; vs,
             ⌜f' = f⌝ ∗ N.of_nat sr.(sr_func_mmalloc) ↦[wf] cl ∗ (∃ θ', rt_token rti sr θ') ∗
               ∃ ℓ a ta ta32 ws,
                 ⌜vs = [VAL_int32 ta32]⌝ ∗
                   ⌜N_i32_repr ta ta32⌝ ∗
                   ⌜repr_root_pointer (RootHeap MemMM a) ta⌝ ∗
                   ℓ ↦addr (MemMM, a) ∗
                   ℓ ↦layout repeat FlagInt sz ∗
                   ℓ ↦heap ws }}.

  Definition spec_gcalloc (cl : function_closure) : Prop :=
    forall s E B R f θ sz sz32 i,
      nat_i32_repr sz sz32 ->
      f.(f_inst).(inst_funcs) !! i = Some sr.(sr_func_gcalloc) ->
      N.of_nat sr.(sr_func_gcalloc) ↦[wf] cl -∗
      rt_token rti sr θ -∗
      ↪[frame] f -∗
      ↪[RUN] -∗
      CWP [BI_const (VAL_int32 sz32); BI_call i] @ s; E UNDER B; R
          {{ f'; vs,
             ⌜f = f'⌝ ∗ N.of_nat sr.(sr_func_gcalloc) ↦[wf] cl ∗
               ∃ θ' ℓ ta ta32 ws,
                 ⌜vs = [VAL_int32 ta32]⌝ ∗
                   ⌜N_i32_repr ta ta32⌝ ∗
                   ⌜repr_pointer θ' (PtrHeap MemGC ℓ) ta⌝ ∗
                   rt_token rti sr θ' ∗
                   ℓ ↦layout repeat FlagInt sz ∗
                   ℓ ↦heap ws }}.

  Definition spec_free (cl : function_closure) : Prop :=
    forall s E B R f i θ ℓ a ta ta32,
      N_i32_repr ta ta32 ->
      repr_root_pointer (RootHeap MemMM a) ta ->
      f.(f_inst).(inst_funcs) !! i = Some sr.(sr_func_free) ->
      ℓ ↦addr (MemMM, a) -∗
      N.of_nat sr.(sr_func_mmalloc) ↦[wf] cl -∗
      rt_token rti sr θ -∗
      ↪[frame] f -∗
      ↪[RUN] -∗
      CWP [BI_const (VAL_int32 ta32); BI_call i] @ s; E UNDER B; R
          {{ f'; vs, ⌜f = f'⌝ ∗ ⌜vs = []⌝ ∗ N.of_nat sr.(sr_func_free) ↦[wf] cl ∗
                     (∃ θ', rt_token rti sr θ') }}.

  Definition spec_setflag (cl : function_closure) : Prop :=
    forall s E B R f i θ ℓ fs μ ta ta32 j j32 fl,
      nat_i32_repr j j32 ->
      N_i32_repr ta ta32 ->
      repr_pointer θ (PtrHeap μ ℓ) ta ->
      f.(f_inst).(inst_funcs) !! i = Some sr.(sr_func_setflag) ->
      ℓ ↦layout fs -∗
      N.of_nat sr.(sr_func_setflag) ↦[wf] cl ∗
      rt_token rti sr θ -∗
      ↪[frame] f -∗
      ↪[RUN] -∗
      CWP [BI_const (VAL_int32 ta32); BI_const (VAL_int32 j32); BI_const (VAL_int32 fl); BI_call i]
        @ s; E UNDER B; R
        {{ f'; vs,
           ⌜f = f'⌝ ∗ ⌜vs = []⌝ ∗
             ℓ ↦layout <[ j := flag_of_i32 fl ]> fs ∗
             N.of_nat sr.(sr_func_setflag) ↦[wf] cl ∗ (∃ θ', rt_token rti sr θ') }}.

  Definition spec_registerroot (cl : function_closure) : Prop :=
    forall s E B R f i θ ℓ tah tah32,
      N_i32_repr tah tah32 ->
      repr_pointer θ (PtrHeap MemGC ℓ) tah ->
      f.(f_inst).(inst_funcs) !! i = Some sr.(sr_func_registerroot) ->
      N.of_nat sr.(sr_func_registerroot) ↦[wf] cl -∗
      rt_token rti sr θ -∗
      ↪[frame] f -∗
      ↪[RUN] -∗
      CWP [BI_const (VAL_int32 tah32); BI_call i] @ s; E UNDER B; R
          {{ f'; vs,
             ⌜f = f'⌝ ∗ N.of_nat sr.(sr_func_registerroot) ↦[wf] cl ∗ (∃ θ', rt_token rti sr θ') ∗
               ∃ ar tar tar32,
                 ⌜vs = [VAL_int32 tar32]⌝ ∗
                   ⌜N_i32_repr tar tar32⌝ ∗
                   ⌜repr_root_pointer (RootHeap MemGC ar) tar⌝ ∗
                   ar ↦root ℓ }}.

  Definition spec_unregisterroot (cl : function_closure) : Prop :=
    forall s E B R f i θ ℓ ar tar tar32,
      N_i32_repr tar tar32 ->
      repr_root_pointer (RootHeap MemGC ar) tar ->
      f.(f_inst).(inst_funcs) !! i = Some sr.(sr_func_unregisterroot) ->
      ar ↦root ℓ -∗
      N.of_nat sr.(sr_func_unregisterroot) ↦[wf] cl -∗
      rt_token rti sr θ -∗
      ↪[frame] f -∗
      ↪[RUN] -∗
      CWP [BI_const (VAL_int32 tar32); BI_call i] @ s; E UNDER B; R
          {{ f'; vs,
             ⌜f = f'⌝ ∗ ⌜vs = []⌝ ∗
               N.of_nat sr.(sr_func_unregisterroot) ↦[wf] cl ∗ (∃ θ', rt_token rti sr θ') }}.

End Runtime.
