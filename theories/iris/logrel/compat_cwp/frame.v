Require Import RecordUpdate.RecordUpdate.
From stdpp Require Import base list.

From iris.proofmode Require Import base tactics classes.
From Wasm Require Import operations.

From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import prelude codegen instruction module.
From RichWasm.iris Require Import autowp memory util wp_codegen.
From RichWasm.iris.language Require Import cwp logpred.
From RichWasm.iris.logrel Require Import relations_cwp fundamental_kinding.
Require Import RichWasm.iris.logrel.compat_cwp.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Fundamental.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_frame M F L L' wt wt' wtf wl wl' wlf es es' τ τs1 τs2 :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    has_mono_rep F τ ->
    (forall wt wt' wtf wl wl' wlf es',
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        run_codegen (compile_instrs mr fe es) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instr_type_sem rti sr mr M F L WT WL es' (InstrT τs1 τs2) L') ->
    run_codegen (compile_instrs mr fe es) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL es' (InstrT (τ :: τs1) (τ :: τs2)) L'.
  Proof.
    intros fe WT WL Hmono IH Hcg.
    eapply (IH _ _ _ _ _ wlf) in Hcg.
    iIntros (se inst fr os vs θ B R Hse) "HIinst HIB HIR HIvs HIos HIfr Hrt Hfr Hrun".
    (* Need to split up values_interp and atoms_interp now *)
    rewrite separate1.
    iPoseProof (values_interp_app with "[$HIos]") as "(%os1 & %os2 & -> & Hvalτ & Hvalτs1)"; auto.
    iPoseProof (atoms_interp_app with "[$HIvs]") as "(%vs1 & %vs2 & -> & Hatomτ & Hatomτs1)".
    (* Apply IH with os2 τs2 *)
    iPoseProof (Hcg $! se inst fr os2 vs2 θ B R Hse with
                 "HIinst HIB HIR Hatomτs1 Hvalτs1 HIfr Hrt Hfr Hrun") as "Hff".
    rewrite map_app. rewrite <- app_assoc.
    iApply cwp_val_app; first apply has_values_consts.
    (* Now it's time to rebuild it *)
    iApply (cwp_wand with "[$Hff]"). clear os2 vs2 θ.
    iIntros (f vs2) "(Hfr & (%os2 & %θ & Hvalτs1 & Hosτs1 & Hrt))".
    unfold fvs_combine. iFrame.
    iExists (os1 ++ os2).
    iSplitL "Hvalτ Hvalτs1".
    - simpl. iEval (rewrite separate1).
      iDestruct "Hvalτ" as "(%oss1 & -> & Hvalτ)".
      iDestruct "Hvalτs1" as "(%oss2 & -> & Hvalτs2)".
      iExists (oss1 ++ oss2). iFrame.
      iPureIntro; rewrite concat_app; auto.
    - iFrame.
  Qed.

End Fundamental.
