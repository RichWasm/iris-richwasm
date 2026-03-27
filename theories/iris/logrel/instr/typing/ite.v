Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section ite.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_ite M F L L' wt wt' wtf wl wl' wlf es1 es2 es' τs1 τs2 :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let F' := F <| fc_labels ::= cons (τs2, L') |> in
    let ψ := InstrT (τs1 ++ [type_i32]) τs2 in
    has_instruction_type_ok F ψ L' ->
    (forall wt wt' wtf wl wl' wlf es',
        let fe := fe_of_context F' in
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        let lmask := wlmask fe wl in
        run_codegen (compile_instrs mr fe es1) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instr_type_sem rti sr mr M F' L WT WL lmask es' (InstrT τs1 τs2) L') ->
    (forall wt wt' wtf wl wl' wlf es',
        let fe := fe_of_context F' in
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        let lmask := wlmask fe wl in
        run_codegen (compile_instrs mr fe es2) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instr_type_sem rti sr mr M F' L WT WL lmask es' (InstrT τs1 τs2) L') ->
    run_codegen (compile_instr mr fe (IIte ψ L' es1 es2)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L'.
  Proof.
    iIntros (?????? Hok IH1 IH2 Hcg ????????) "@@@@@@@@@@@".
    inv_cg_bind Hcg res1 wt1 wt2 wl1 wl2 es1' es2' Hcg1 Hcg2.
    inv_cg_bind Hcg2 res2 wt3 wt4 wl3 wl4 es3' es4' Hcg2 Hcg3.
    apply wp_ignore in Hcg3 as (_ & [] & Hcg3).
    destruct u, u0.
    inv_cg_try_option Hcg1.
    inv_cg_try_option Hcg2.
    subst wt1 wl1 es1' wt3 wl3 es3' wt2 wl2 es2' wt' wl' es' WT WL.
    clear_nils.
    iDestruct (values_interp_app_l with "Hos") as "(%os1 & %os2 & -> & Hos1 & Hos2)"; first done.
    iDestruct (atoms_interp_app_l with "Hvs") as "(%vs1 & %vs2 & -> & Hvs1 & Hvs2)".
    apply has_values_to_consts_inv in Hevs.
    subst evs.
    unfold to_consts.
    rewrite map_app.
    rewrite <- app_assoc.
    iDestruct (values_interp_cons_l with "Hos2") as "(%os1a & %os1b & -> & Hos1a & Hos1b)".
    iDestruct (atoms_interp_app_l with "Hvs2") as "(%vs1a & %vs1b & -> & Hvs1a & Hvs1b)".
    iDestruct (values_interp_nil_l with "Hos1b") as "->".
    iClear "Hos1b".
    iDestruct (big_sepL2_nil_inv_l with "Hvs1b") as "->".
    iClear "Hvs1b".
    rewrite app_nil_r.
    iDestruct (value_interp_i32 with "Hos1a") as "(%n & ->)".
    iClear "Hos1a".
    iDestruct (atoms_interp_cons_l with "Hvs1a") as "(%v & %vs' & -> & Hv & Hvs1a')".
    iDestruct (atoms_interp_nil_l with "Hvs1a'") as "->".
    iClear "Hvs1a'".
    change (map BI_const [v]) with [BI_const v].
    iDestruct "Hv" as "->".
    rewrite removelast_last in Heq_some.
    iDestruct (translate_types_comp_interp_length with "Hos1") as "%Hlen_res".
    1, 2, 3: done.
    iDestruct (big_sepL2_length with "Hvs1") as "%Hlen_vs1".
    eapply cwp_if_c in Hcg3 as (wt5 & wt6 & wl5 & wl6 & es5 & es6 & Hes1 & Hes2 & -> & -> & Hite).
    - do 2 rewrite <- app_assoc.
      destruct (value_eq_dec (VAL_int32 n) (VAL_int32 (Wasm_int.int_zero i32m))) as [Hvn|Hvn].
      + iApply (Hite with "[$] [$]").
        clear Hite.
        inversion Hvn as [Hn]. subst n. clear Hvn Hes1 IH1.
        iRight. iSplitR; first done.
        iIntros "!> Hfr Hrun".
        rewrite (app_assoc wt wt5).
        rewrite (app_assoc wl wl5).
        iApply (cwp_wand with "[-]");
          first iApply (IH2 with "[] [] [$] [Hlabels] [$] [$] [$] [$] [$] [$] [$]").
        1, 2: done.
        * iPureIntro. apply has_values_to_consts.
        * iApply labels_interp_cons.
          1, 2, 3: done.
          -- iModIntro.
             iIntros (??) "(%Hfrel & Hframe & Hvalues & Hrt)".
             iFrame.
             iPureIntro.
             eapply frame_rel_wlmask_mono; last done.
             rewrite length_app.
             lia.
          -- iApply labels_interp_mono.
             1, 3: done.
             apply wlmask_mono.
             rewrite length_app.
             lia.
        * iIntros (??) "[%Hrel H]".
          iFrame.
          iPureIntro.
          eapply frame_rel_mask_mono; last done.
          apply wlmask_mono.
          rewrite length_app.
          lia.
      + iApply (Hite with "[$] [$]").
        clear Hite.
        assert (n <> Wasm_int.int_zero i32m).
        { intros Hcontra. apply Hvn. by rewrite Hcontra. }
        clear Hvn Hes2 IH2.
        iLeft. iSplitR; first done.
        iIntros "!> Hfr Hrun".
        iApply (IH1 with "[] [] [$] [Hlabels] [$] [$] [$] [$] [$] [$] [$]").
        1, 2: done.
        { iPureIntro. apply has_values_to_consts. }
        iApply labels_interp_cons.
        4: by iIntros (fr' vs') "!> H".
        all: done.
    - apply is_consts_to_consts.
    - rewrite length_map. by rewrite <- Hlen_res.
  Qed.

End ite.
