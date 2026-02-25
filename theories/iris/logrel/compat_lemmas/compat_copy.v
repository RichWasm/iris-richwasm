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


  Lemma compat_copy M F L n_skip wt wt' wtf wl wl' wlf τ es' :
    let fe := fe_of_context F <| fe_br_skip := n_skip |> in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [τ] [τ; τ] in
    has_copyability F τ ExCopy ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ICopy ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Proof.
    intros fe WT WL ψ Hcopy Hok Hcompile.
    unfold compile_instr in Hcompile.
    inv_cg_bind Hcompile ρ wt1 wt1' wl1 wl1' es_nil es1 Htype_rep Hcompile.
    inv_cg_bind Hcompile ιs wt2 wt2' wl2 wl2' es_nil' es2 Heval_rep Hcompile.
    inv_cg_bind Hcompile idxs ?wt ?wt ?wl ?wl es_save ?es Hsave Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_restore1 ?es Hrestore1 Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_gcs es_restore2 Hgcs Hrestore2.
    inv_cg_try_option Htype_rep.
    inv_cg_try_option Heval_rep.
    subst.
    unfold WT, WL.
    repeat rewrite <- ?app_assoc, -> ?app_nil_l, -> ?app_nil_r in *.
    unfold have_instruction_type_sem.
    unfold ψ.
    iIntros (se inst lh fr rvs vs θ) "%Henv #Hinst #Hlh Hrvs Hvs Hframe Hrt Hfr Hrun".
    unfold expr_interp.
    inversion Hcopy as [F' τ' ρ' χ ? Hhas_kind HF' Hτ' Hχ].
    subst F' τ'.
    assert (ρ' = ρ).
    {
      apply type_rep_has_kind_agree in Hhas_kind.
      rewrite Heq_some in Hhas_kind.
      congruence.
    }
    subst ρ'.
    assert (Heval: eval_kind se (VALTYPE ρ ExCopy δ) = Some (SVALTYPE ιs ExCopy δ)).
    {
      unfold eval_kind.
      by erewrite eval_rep_emptyenv.
    }
    pose proof (kinding_sound rti sr mr F se _ _ _ Hhas_kind ltac:(eauto) Heval) as Hskind.
    destruct Hskind as [Hrefine Hcopyable].
    cbn in Hcopyable.
    iDestruct "Hvs" as "(%vss & %Hconcat & Hvs)".
    iPoseProof (big_sepL2_length with "[$Hvs]") as "%Hlens".
    destruct vss as [|vs' [|vs'' vss]]; cbn in Hlens, Hconcat; try congruence.
    rewrite app_nil_r in Hconcat; subst vs'; clear Hlens.
    rewrite big_sepL2_singleton.
    iEval (cbn -[return_interp br_interp values_interp atoms_interp frame_interp]).
    rewrite to_e_list_app.
    rewrite (app_assoc (v_to_e_list _)).
    iPoseProof (frame_interp_wl_interp with "Hframe") as "%Hwl"; first done.
    set (Φ := {| lp_fr_inv _ := True;
                 lp_val f vs' :=
                   ⌜∀ i, i ∉ idxs -> f_locs f !! localimm i = f_locs fr !! localimm i⌝ ∗
                   ⌜Forall2 (fun i v => f_locs f !! localimm i = Some v) idxs vs⌝ ∗
                   ⌜vs' = []⌝;
                 lp_trap := False;
                 lp_br _ _ _ := False;
                 lp_ret _ := False;
                 lp_host _ _ _ _ := False |}%I : @logpred Σ).
    iApply (lenient_wp_seq with "[Hfr Hrun]").
    {
      eapply (lwp_save_stack_w _ Φ) in Hsave; eauto.
      + destruct Hsave as (-> & -> & -> & Hsave).
        iApply (Hsave with "[$] [$]").
        iIntros (f' [Hfsame Hfchanged]).
        done.
      + apply Hwl.
      + admit. (* easy pure conseqeunce of value_interp and
      rep_values_interp, should be proved above the first wp_seq
      rule *)
    }
    { by iIntros (fr') "Htrap". }
    iIntros (w fr_saved) "Hnotrap Hfr _".
    rewrite to_e_list_app.
    rewrite (app_assoc (of_val _)).
    set (Φ2 := {| lp_fr_inv _ := True;
                  lp_val f vs' :=
                    ⌜∀ i, i ∉ idxs -> f_locs f !! localimm i = f_locs fr !! localimm i⌝ ∗
                    ⌜Forall2 (fun i v => f_locs f !! localimm i = Some v) idxs vs⌝ ∗
                    ⌜vs' = vs⌝;
                  lp_trap := False;
                  lp_br _ _ _ := False;
                  lp_ret _ := False;
                  lp_host _ _ _ _ := False |}%I : @logpred Σ).
    destruct w; iEval (cbn) in "Hnotrap"; try done;
      try (iDestruct "Hnotrap" as "[? ?]"; done).
    iDestruct "Hnotrap" as "(Hrun & %Hsame & %Hsaved & ->)".
    eapply lwp_restore_stack_w in Hrestore1; eauto using Forall2_length.
    destruct Hrestore1 as (? & -> & -> & Hrestore1).
    iApply (lenient_wp_seq with "[Hfr Hrun]").
    {
      iEval (cbn).
      iApply (Hrestore1 with "[$] [$] [//]").
    }
    { by iIntros (w) "Htrap". }
    clear Hrestore1.
    iIntros (w fr_saved') "HΦ2 Hf _".
    destruct w; iEval (cbn) in "HΦ2"; try done;
      try (iDestruct "HΦ2" as "[? ?]"; done).
    iDestruct "HΦ2" as "(Hrun & -> & ->)".
    admit.
  Admitted.

End Fundamental.
