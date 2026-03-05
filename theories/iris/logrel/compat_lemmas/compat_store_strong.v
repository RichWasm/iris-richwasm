Require Import RecordUpdate.RecordUpdate.
From stdpp Require Import base list.

From iris.proofmode Require Import base tactics classes.
From Wasm Require Import operations.

From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import prelude codegen instruction module.
From RichWasm.iris Require Import autowp memory util wp_codegen.
From RichWasm.iris.language Require Import lenient_wp lwp_pure lwp_structural lwp_resources logpred.
From RichWasm.iris.logrel Require Import relations fundamental_kinding.

Require Export shared.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Fundamental.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_store_strong M F L wt wt' wtf wl wl' wlf es' κ κ' κser σ ρ τ τval π pr :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [RefT κ (BaseM MemMM) τ; τval] [RefT κ' (BaseM MemMM) (pr_replaced pr)] in
    resolves_path τ π (Some (SerT κser τval)) pr ->
    has_dropability F pr.(pr_target) ImDrop ->
    has_size F pr.(pr_target) σ ->
    has_rep F τval ρ ->
    eval_size EmptyEnv σ = eval_rep_size EmptyEnv ρ ->
    Forall (has_mono_size F) (pr_prefix pr) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IStore ψ π)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Proof.
    intros fe WT WL ψ Hresolves Hdrop Hsize Hrep Henv Hmonosize Htype Hcompile.
    unfold WT, WL; clear WT WL.
    (* If the WT := or WL := become necessary, undo the unfold/clear*)
    cbn in Hcompile.

    (* Mechanically get through some of the first few things in compile_swap *)
    inv_cg_bind Hcompile ρ_inner ?wt ?wt ?wl ?wl es_off ?es_rest Hρ_inner Hcompile.
    inv_cg_bind Hcompile ιs ?wt ?wt ?wl ?wl es_ρ ?es_rest Hιs Hcompile.
    inv_cg_bind Hcompile off ?wt ?wt ?wl ?wl  es_fail ?es_rest Hoff Hcompile.
    inv_cg_try_option Hρ_inner; rename Heq_some into Hρ_inner.
    inv_cg_try_option Hιs; rename Heq_some into Hιs.
    inv_cg_try_option Hoff; rename Heq_some into Hoff.
    inv_cg_bind Hcompile vs ?wt ?wt ?wl ?wl  es_save ?es_rest Hsave Hcompile.
    inv_cg_bind Hcompile a ?wt ?wt ?wl ?wl  es_a ?es_rest Ha Hcompile.
    cbn in Ha; inversion Ha; subst; clear Ha.
    inv_cg_bind Hcompile res_emit ?wt ?wt ?wl ?wl  es_emit ?es_rest Hemit Hcompile.
    inv_cg_emit Hemit.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_case_ptr es_ptr_flags Hcompile Hptr_flags.

    (* Some clean up *)
    subst.
    clear_nils.

    (* The next step is a case_ptr, for which a lemma is currently being proven about *)

  Admitted.

End Fundamental.
