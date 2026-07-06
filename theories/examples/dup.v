Require Import Stdlib.ZArith.ZArith.

Require Import stdpp.base.

From iris.proofmode Require Import base classes proofmode.

From RichWasm.named_props Require Import named_props custom_syntax.
Require Import RichWasm.wasm.datatypes.
From RichWasm.iris Require Import language.cwp logrel memory runtime util.
Require Import RichWasm.syntax.

Set Bullet Behavior "Strict Subproofs".

Section dup.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.

  Definition dup_type : function_type :=
    InnerFunT (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                 (MonoFunT
                    [VarT 0]
                    [RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                       (StructT (MEMTYPE (ProdS [RepS (AtomR PtrR); RepS (AtomR PtrR)]) GCRefs)
                          [SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0);
                           SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0)])])).

  Definition instance_import (i : nat) (ϕ : function_type) (inst : instance) : iProp Σ :=
    ∃ j cl,
      ⌜inst.(inst_funcs) !! i = Some j⌝ ∗
        closure_interp rti sr ϕ senv_empty cl ∗
        na_inv logrel_nais (ns_fun (N.of_nat j)) (N.of_nat j ↦[wf] cl).

  Definition instance_ok (inst : instance) : iProp Σ :=
    "%Hgcmem" ∷ ⌜inst.(inst_memory) !! 0 = Some sr.(sr_mem_gc)⌝ ∗
    "#Hgcalloc" ∷
      instance_rt_func_interp (Mk_funcidx 0) sr.(sr_func_gcalloc) (spec_gcalloc rti sr) inst ∗
    "#Hregisterroot" ∷
      instance_rt_func_interp (Mk_funcidx 1) sr.(sr_func_registerroot) (spec_registerroot rti sr) inst ∗
    "#Hdup" ∷ instance_import 2 dup_type inst.

  Definition body : list basic_instruction :=
    [
      BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat 1)));
      BI_call 0; (* gcalloc *)
      BI_tee_local 0; (* ref *)
      BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat 20))); (* 10 << 1 *)
      BI_store 0 T_i32 None 0%N 0%N; (* gcmem *)
      BI_get_local 0; (* ref *)
      BI_call 1; (* registerroot *)
      BI_call 2; (* dup *)
      BI_drop
    ].

  Definition example inst : function_closure := FC_func_native inst (Tf [] []) [T_i32] body.

  Theorem example_dup_safe inst :
    instance_ok inst ⊢ closure_interp rti sr (InnerFunT (MonoFunT [] [])) senv_empty (example inst).
  Proof.
    iIntros "@".
    rewrite closure_interp_eq.
    iSplitR; first done.
    iSplitR; first done.
    iIntros "!> !> %%% Hvs1 Hos1 Hrt Hown Hfr Hrun".
    cwp_chomp 2.
    iApply (cwp_seq with "[Hown Hrt Hfr Hrun]").
    {
      iDestruct "Hgcalloc" as "(%cl & %Hgcalloc_spec & %Hgcalloc_idx & Hgcalloc)".
      iApply fupd_cwp.
      iMod (na_inv_acc with "Hgcalloc Hown") as "(>Hgcalloc_cl & Hown & Hclose)".
      1, 2: done.
      iApply (cwp_wand with "[-]"); first iApply (Hgcalloc_spec with "Hgcalloc_cl Hrt Hfr Hrun").
      1, 2: done.
      iIntros "!> %% H".
      admit.
    }
    admit.
  Abort.

End dup.
