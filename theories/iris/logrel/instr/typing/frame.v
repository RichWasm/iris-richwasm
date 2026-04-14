Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section frame.

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
    let lmask := wlmask fe wl in
    has_mono_rep F τ ->
    (forall wt wt' wtf wl wl' wlf es',
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        let lmask := wlmask fe wl in
        run_codegen (compile_instrs mr fe es) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' (InstrT τs1 τs2) L') ->
    run_codegen (compile_instrs mr fe es) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' (InstrT (τ :: τs1) (τ :: τs2)) L'.
  Proof.
    intros fe WT WL lmask Hmono IH Hcg.
    eapply (IH _ _ _ _ _ wlf) in Hcg.
    iIntros (????????) "@@@@@@@@@@@@".
    (* Need to split up values_interp and atoms_interp now *)
    rewrite separate1.
    iPoseProof (values_interp_app_l with "[$]") as "(%os1 & %os2 & -> & Hvalτ & Hvalτs1)"; auto.
    iPoseProof (atoms_interp_app_l with "[$]") as "(%vs1 & %vs2 & -> & Hatomτ & Hatomτs1)".
    apply has_values_app_inv in Hevs as (evs1 & evs2 & -> & Hevs1 & Hevs2).
    (* Apply IH with os2 τs2 *)
    iPoseProof (Hcg $! se fr os2 vs2 evs2 θ B R Hse Hevs2 with
                 "Hinst Hlabels Hreturn Hatomτs1 Hvalτs1 Hframe Hrt Hown Hfr Hrun") as "Hff".
    rewrite <- app_assoc.
    iApply cwp_val_app; first done.
    (* Now it's time to rebuild it *)
    iApply (cwp_wand with "[$Hff]"). clear Hevs2 os2 evs2 vs2 θ.
    iIntros (f vs2) "(%Hfrel & Hfr & (%os2 & Hvalτs1 & Hosτs1) & [%θ Hrt] & Hown)".
    unfold fvs_combine.
    iFrame.
    iFrame "%".
    iExists (os1 ++ os2).
    iSplitL "Hvalτ Hvalτs1".
    - simpl. iEval (rewrite separate1).
      iDestruct "Hvalτ" as "(%oss1 & -> & Hvalτ)".
      iDestruct "Hvalτs1" as "(%oss2 & -> & Hvalτs2)".
      iExists (oss1 ++ oss2). iFrame.
      iPureIntro; rewrite concat_app; auto.
    - iFrame.
  Qed.

End frame.
