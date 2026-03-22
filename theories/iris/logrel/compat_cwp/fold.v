Require Import RecordUpdate.RecordUpdate.
From stdpp Require Import base list.

From iris.proofmode Require Import base proofmode classes.
From RichWasm.wasm Require Import operations.

From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import prelude codegen instruction module.
From RichWasm.iris Require Import autowp memory util wp_codegen.
From RichWasm.iris.language Require Import cwp logpred.
From RichWasm.iris.logrel Require Import relations_cwp fundamental_kinding.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Fundamental.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_fold M F L wt wt' wtf wl wl' wlf es' τ κ :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
    let ψ := InstrT [τ0] [RecT κ τ] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IFold ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL es' ψ L.
  Proof.
    (* intros fe WT WL τrec ψ Hok Hcg. *)
    (* cbn in Hcg; inversion Hcg; subst wt' wl' es'; clear Hcg. *)
    (* simpl to_e_list. *)
    (* iApply sem_type_erased; first done. *)
    (* iIntros (se vs) "Hrec". *)
    (* do 2 rewrite values_interp_one_eq value_interp_eq. *)
    (* iEval (cbn). *)
    (* admit. *)
  Admitted.

End Fundamental.
