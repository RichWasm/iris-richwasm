From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From Wasm.iris.logrel Require Export iris_fundamental.
From Wasm.iris.rules Require Export proofmode.
From RichWasm.iris.alloc Require Export util memrsc reprs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Definition malloc_typ := Tf [T_i32] [T_i32].
Definition free_typ := Tf [T_i32] [].

Section spec.

  Context `{!wasmG Σ} `{!allocG Σ}.
  Parameter (memidx: N).

  Definition funspec :=
    nat ->
    instance ->
    seq.seq value_type ->
    seq.seq basic_instruction ->
    iProp Σ.

  Definition spec_malloc
    (alloc_tok: N -> N -> iProp Σ)
    (alloc_inv: N -> iProp Σ) E : funspec :=
    λ (fid: nat)
      (inst: instance)
      (local_typs: seq.seq value_type)
      (body: seq.seq basic_instruction),
      (∀ (f: frame) (reqd_sz: N) (reqd_sz32: i32),
        {{{{ N.of_nat fid ↦[wf] FC_func_native inst free_typ local_typs body ∗
             ↪[frame] f ∗
             alloc_inv memidx ∗
             ⌜N_repr reqd_sz reqd_sz32⌝ }}}}
          [AI_basic (BI_const (VAL_int32 reqd_sz32)); AI_invoke fid] @ E
          {{{{ w, ↪[frame] f ∗
                  alloc_inv memidx ∗
                    ∃ data_addr data_addr32,
                      ⌜w = immV [VAL_int32 data_addr32]⌝ ∗
                      ⌜N_repr data_addr data_addr32⌝ ∗
                      alloc_tok data_addr reqd_sz ∗
                      own_vec memidx data_addr reqd_sz
      }}}})%I.

  Definition spec_free
    (alloc_tok: N -> N -> iProp Σ)
    (alloc_inv: N -> iProp Σ) E : funspec :=
    λ (fid: nat)
      (inst: instance)
      (local_typs: seq.seq value_type)
      (body: seq.seq basic_instruction),
      (∀ (f: frame) (data_addr: N) (data_addr32: i32) (sz: N),
        {{{{ N.of_nat fid ↦[wf] FC_func_native inst free_typ local_typs body ∗
             ↪[frame] f ∗
             alloc_inv memidx ∗
             alloc_tok data_addr sz ∗
             own_vec memidx data_addr sz ∗
             ⌜N_repr data_addr data_addr32⌝ }}}}
          [AI_basic (BI_const (VAL_int32 data_addr32)); AI_invoke fid] @ E
        {{{{ w, ⌜w = immV []⌝ ∗ ↪[frame] f ∗ alloc_inv memidx }}}})%I.

End spec.
