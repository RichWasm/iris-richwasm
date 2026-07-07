Require Import Stdlib.ZArith.ZArith.

Require Import stdpp.base.

From iris.proofmode Require Import base classes proofmode.

From RichWasm.named_props Require Import named_props custom_syntax.
Require Import RichWasm.wasm.datatypes.
From RichWasm.iris Require Import language.cwp logrel memory runtime util.
Require Import RichWasm.syntax.

Set Bullet Behavior "Strict Subproofs".

Section swap.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.

  Variable mem_id : N.
  Variable alloc_id : nat.

  Definition swap_type : function_type :=
    InnerFunT (ForallTypeT (VALTYPE (AtomR I32R) AnyRefs)
                 (ForallTypeT (VALTYPE (AtomR I32R) AnyRefs)
                    (MonoFunT [VarT 1; VarT 0] [VarT 0; VarT 1]))).

  Definition alloc_spec (cl : function_closure) : Prop :=
    forall s E B R f i v,
      f.(f_inst).(inst_funcs) !! i = Some alloc_id ->
      N.of_nat alloc_id ↦[wf] cl -∗
      ↪[frame] f -∗
      ↪[RUN] -∗
      CWP [BI_const (VAL_int32 v); BI_call i] @ s; E UNDER B; R
          {{ f'; vs, ⌜f = f'⌝ ∗ N.of_nat alloc_id ↦[wf] cl ∗
                     ∃ a, ⌜vs = [VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N a))]⌝ ∗
                          mem_id ↦[wms][a] serialise_i32 v }}.

  Definition alloc_import (i : nat) (spec : function_closure -> Prop) (inst : instance) : iProp Σ :=
    ∃ cl,
      ⌜inst.(inst_funcs) !! i = Some alloc_id⌝ ∗
      ⌜alloc_spec cl⌝ ∗
      na_inv logrel_nais (ns_fun (N.of_nat alloc_id)) (N.of_nat alloc_id ↦[wf] cl).

  Definition instance_import (i : nat) (ϕ : function_type) (inst : instance) : iProp Σ :=
    ∃ j cl,
      ⌜inst.(inst_funcs) !! i = Some j⌝ ∗
      closure_interp rti sr ϕ senv_empty cl ∗
      na_inv logrel_nais (ns_fun (N.of_nat j)) (N.of_nat j ↦[wf] cl).

  Definition instance_ok (inst : instance) : iProp Σ :=
    "#Halloc" ∷ alloc_import 0 alloc_spec inst ∗
    "#Hswap" ∷ instance_import 1 swap_type inst.

  Definition body : list basic_instruction :=
    [
      BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat 7)));
      BI_call 0; (* alloc *)
      BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat 42)));
      BI_call 0; (* alloc *)
      BI_call 1; (* swap *)
      BI_drop;
      BI_drop
    ].

  Definition example inst : function_closure := FC_func_native inst (Tf [] []) [] body.

  Theorem example_swap_safe inst :
    instance_ok inst ⊢ closure_interp rti sr (InnerFunT (MonoFunT [] [])) senv_empty (example inst).
  Proof.
    iIntros "@".
    rewrite closure_interp_eq.
    iSplitR; first done.
    iSplitR; first done.
    iIntros "!> !> %%% Hvs1 Hos1 Hrt Hown Hfr Hrun".
  Abort.

End swap.
