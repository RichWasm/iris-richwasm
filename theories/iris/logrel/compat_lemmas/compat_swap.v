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

  Lemma compat_swap M F L n_skip wt wt' wtf wl wl' wlf es' κ κser μ τ τval π pr :
     let fe := fe_of_context F <| fe_br_skip := n_skip |> in
     let WT := wt ++ wt' ++ wtf in
     let WL := wl ++ wl' ++ wlf in
     let ψ := InstrT [RefT κ μ τ; τval] [RefT κ μ τ; τval] in
     resolves_path τ π None pr ->
     Forall (has_mono_size F) (pr_prefix pr) ->
     pr.(pr_target) = SerT κser τval ->
     has_instruction_type_ok F ψ L ->
     run_codegen (compile_instr mr fe (ISwap ψ π)) wt wl = inr ((), wt', wl', es') ->
     ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Proof.
    intros fe WT WL ψ Hresolves Hmonosize Hser Htype Hcompile. unfold WT, WL; clear WT WL.
    (* If the WT := or WL := become necessary, undo the unfold/clear*)
    cbn in Hcompile.

    (* Mechanically get through some of the first few things in compile_swap *)
    inv_cg_bind Hcompile ρ ?wt ?wt ?wl ?wl es_off ?es_rest Hρ Hcompile.
    inv_cg_bind Hcompile ιs ?wt ?wt ?wl ?wl es_ρ ?es_rest Hιs Hcompile.
    inv_cg_bind Hcompile off ?wt ?wt ?wl ?wl  es_fail ?es_rest Hoff Hcompile.
    inv_cg_try_option Hρ; rename Heq_some into Hρ.
    inv_cg_try_option Hιs; rename Heq_some into Hιs.
    inv_cg_try_option Hoff; rename Heq_some into Hoff.
    inv_cg_bind Hcompile vs ?wt ?wt ?wl ?wl  es_save ?es_rest Hsave Hcompile.
    inv_cg_bind Hcompile a ?wt ?wt ?wl ?wl  es_a ?es_rest Ha Hcompile.
    cbn in Ha; inversion Ha; subst; clear Ha.
    inv_cg_bind Hcompile res_emit ?wt ?wt ?wl ?wl  es_emit ?es_rest Hemit Hcompile.
    inv_cg_emit Hemit.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl  es_case_ptr ?es_rest Hcompile Hignore.
    cbn in Hignore; inversion Hignore; subst; clear Hignore.

    (* Some clean up *)
    assert (Hu: u = ()). { admit. }
    assert (Hp: p = ((),())). { admit. }
    subst.
    clear_nils.

    (* The next step is a case_ptr, for which a lemma is currently being proven about *)

  Admitted.

End Fundamental.
