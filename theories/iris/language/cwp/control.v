Require Import iris.proofmode.tactics.

Require Import RichWasm.iris.helpers.prelude.iris_wasm_lang_properties.
From RichWasm.iris.language Require Import iris_wp_def lenient_wp logpred lwp_pure lwp_structural lwp_trap.
From RichWasm.iris.language.cwp Require Import base def util.
From RichWasm.iris.rules Require Import
  iris_rules_bind iris_rules_calls iris_rules_pure iris_rules_trap iris_rules_control.

Set Bullet Behavior "Strict Subproofs".

Section control.

  Context `{!wasmG Σ}.

  Lemma wp_label_vfill_br s E n i (vh : valid_holed i) es esk :
    lh_depth (lh_of_vh vh) < i ->
    es = vfill vh [AI_basic (BI_br i)] ->
    ⊢ WP [AI_label n esk es]
         @ s; E
         {{ v, ∃ vh', ⌜v = @brV i vh'⌝ ∗
                      ⌜lh_depth (lh_of_vh vh') = S (lh_depth (lh_of_vh vh))⌝ ∗
                      ⌜get_base_l vh = get_base_l vh'⌝ }}.
  Proof.
    iIntros (Hdepth ->) "*".
    destruct (Nat.lt_exists_pred _ _ Hdepth) as [j [-> _]].
    destruct (vh_decrease vh) as [vh' |] eqn:Hvh.
    - iApply wp_value.
      + instantiate (1 := brV (VH_rec [] n esk vh' [])).
        by rewrite (vfill_decrease _ Hvh).
      + iExists (VH_rec [] n esk vh' []).
        repeat iSplit; iPureIntro.
        * done.
        * cbn. by rewrite (lh_depth_vh_decrease vh).
        * cbn. by rewrite (get_base_vh_decrease Hvh).
    - exfalso. eapply vh_depth_can_decrease.
      + exact Hdepth.
      + exact Hvh.
  Qed.

  Lemma lwp_cwp_label s E (f : frame) es esk n L R Ψ Φ :
    ↪[frame] f -∗
    ↪[RUN] -∗
    (↪[frame] f -∗ ↪[RUN] -∗ lenient_wp s E es (cwp_post_lp ((n, Ψ) :: L) R Φ)) -∗
    (∀ f' vs, ⌜length vs = n⌝ -∗ ↪[frame] f' -∗ ↪[RUN] -∗ Ψ f' vs -∗
              lenient_wp s E (v_to_e_list vs ++ esk) (cwp_post_lp L R Φ)) -∗
    lenient_wp s E [AI_label n esk es] (cwp_post_lp L R Φ).
  Proof.
    iIntros "Hfr Hrun Hes Hesk".
    iSpecialize ("Hes" with "[$] [$]").
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_nil.
    iApply wp_label_bind.
    iApply (wp_wand with "Hes").
    iIntros (v) "HΦ".
    change (LH_rec [] n esk (LH_base [] []) []) with (push_base (LH_base [] []) n esk [] []).
    iApply wp_label_pull_nil.
    iApply wp_wasm_empty_ctx.
    destruct v.
    - iDestruct "HΦ" as "(%f' & Hfr & _ & Hrun & HΦ)".
      iApply (wp_wand with "[Hfr Hrun HΦ]").
      + iApply (wp_label_value with "[$] [$]"); first by rewrite iris.to_of_val.
        instantiate (1 := fun v => (∃ vs, ⌜v = immV vs⌝ ∗ Φ f' vs)%I).
        by iFrame.
      + iIntros (v) "[[(%vs' & -> & Hϕ) Hrun] Hf]". iExists f'. iFrame.
    - iDestruct "HΦ" as "(%f' & Hfr & _ & Hbail & _)".
      iApply (wp_wand with "[Hfr]").
      + iApply (wp_label_trap with "[$]"); first done.
        by instantiate (1 := fun v => (⌜v = trapV⌝)%I).
      + iIntros (v) "(-> & Hfr)".
        iExists f'. by iFrame.
    - destruct (Nat.eqb (lh_depth (lh_of_vh lh)) i) eqn:Hlh.
      + rewrite Nat.eqb_eq in Hlh.
        iDestruct "HΦ" as "(%f' & Hf & _ & [Hrun HΦ])".
        unfold iris.of_val.
        iSimpl in "HΦ".
        iUnfold cwp_post_br, vh_depth in "HΦ".
        rewrite Hlh.
        rewrite Nat.sub_diag.
        iDestruct "HΦ" as "(%vs0 & %vs & %Hbase & %Hlen & HΦ)".
        rewrite (vfill_take_base _ _ _ _ Hbase).
        iApply (wp_br with "[$] [$]").
        3: {
          instantiate (2 := v_to_e_list vs).
          destruct (vfill_to_lfilled (set_base_l vs0 lh) (seq.cat (v_to_e_list vs) [AI_basic (BI_br i)])) as [Hdepth Hfilled].
          rewrite (set_base_l_depth vs0) in Hlh.
          by rewrite Hlh in Hfilled.
        }
        * apply forallb_forall.
          apply List.Forall_forall.
          apply Forall_forall.
          intros e He.
          rewrite elem_of_list_fmap in He.
          by destruct He as (v & -> & Hv).
        * by rewrite length_fmap.
        * iIntros "!> Hf Hrun".
          iSpecialize ("Hesk" with "[] [$] [$] [$]"); first done.
          iApply "Hesk".
      + destruct (vfill_to_lfilled lh []) as [Hi _].
        rewrite Nat.eqb_neq in Hlh.
        rename Hlh into Hlh'.
        assert (lh_depth (lh_of_vh lh) <= i /\ lh_depth (lh_of_vh lh) <> i) as Hlh; first done.
        apply Nat.le_neq in Hlh.
        clear Hi Hlh'.
        iApply wp_wand.
        * iApply wp_label_vfill_br; [exact Hlh | done].
        * iIntros (v) "(%vh & -> & %Hdepth & %Hbase)".
          unfold denote_logpred.
          iDestruct "HΦ" as "(%f' & Hfr & _ & [Hrun HΦ])".
          iExists f'. iFrame.
          unfold cwp_post_lp, cwp_post_br, vh_depth, lp_br.
          rewrite Hdepth.
          rewrite (cons_lookup_sub_lt _ _ _ _ Hlh).
          by rewrite Hbase.
    - iDestruct "HΦ" as "(%f' & Hfr & _ & [Hrun HΦ])".
      destruct R; last done.
      destruct r as [n' P].
      iDestruct "HΦ" as "(%vs0 & %vs & %Hbase & %Hlen & HP)".
      iApply wp_value; first by instantiate (1 := retV (SH_rec [] n esk s0 [])).
      iFrame.
      by iExists vs0.
    - iDestruct "HΦ" as "(%_ & _ & _ & [_ []])".
  Qed.

  Lemma lwp_cwp_local s E f0 vs es ts ts2 inst L R Φ :
    ↪[frame] f0 -∗
    ↪[RUN] -∗
    (↪[frame] Build_frame (vs ++ n_zeros ts) inst -∗ ↪[RUN] -∗
     lenient_wp s E
       (map AI_basic [BI_block (Tf [] ts2) es])
       (cwp_post_lp [] (Some (length ts2, Φ f0))
                    (fun _ vs0 => Φ f0 vs0 ∗ ⌜length vs0 = length ts2⌝))) -∗
    lenient_wp s E
      [AI_local (length ts2) (Build_frame (vs ++ n_zeros ts) inst)
         [AI_basic (BI_block (Tf [] ts2) es)]]
      (cwp_post_lp L R Φ).
  Proof.
    iIntros "Hfr Hrun Hes".
    iApply (wp_frame_bind with "[$]"); first done.
    iIntros "Hfr".
    iSpecialize ("Hes" with "[$] [$]").
    iApply (wp_wand with "[Hes]"); first iApply "Hes".
    iIntros (v) "(%f & Hfr & _ & HΦ)".
    iExists f.
    iFrame.
    iIntros "Hfr".
    destruct v.
    - iDestruct "HΦ" as "(Hrun & HΦ & %Hlen2)".
      iApply (wp_wand with "[HΦ Hfr Hrun]").
      + iApply (wp_frame_value with "[$] [$]").
        * apply iris.to_of_val.
        * by rewrite length_map.
        * instantiate (1 := fun v => (∃ vs, ⌜v = immV vs⌝ ∗ Φ f0 vs)%I).
          iModIntro. iExists l. by iFrame.
      + iIntros (v) "([(%vs' & -> & HΦ) Hrun] & Hfr)".
        iExists f0. iFrame.
    - iDestruct "HΦ" as "[Hbail _]".
      iApply (wp_wand with "[Hfr]").
      + iApply (wp_frame_trap with "[$]").
        by instantiate (1 := fun v => ⌜v = trapV⌝%I).
      + iIntros (v) "[-> Hfr]". iExists f0. by iFrame.
    - iUnfold lp_noframe, lp_br, cwp_post_lp, cwp_post_br in "HΦ".
      rewrite lookup_nil.
      iDestruct "HΦ" as "[_ []]".
    - iDestruct "HΦ" as "(Hrun & %vs0 & %vs' & %Hbase & %Hlen' & HΦ)".
      iApply (wp_wand with "[HΦ Hrun Hfr]").
      + iApply wp_frame_return.
        {
          instantiate (2 := v_to_e_list vs').
          instantiate (1 := vs').
          apply to_val_v_to_e.
        }
        { by rewrite length_map. }
        {
          unfold iris.of_val.
          rewrite (sfill_take_base _ _ _ _ Hbase).
          apply sfill_to_lfilled.
        }
        iFrame.
        iApply wp_value.
        { by instantiate (1 := immV vs'). }
        instantiate (1 := fun v => (⌜v = immV vs'⌝ ∗ Φ f0 vs')%I).
        by iFrame.
      + iIntros (v) "[[[-> HΦ] Hrun] Hfr]".
        iExists f0. iFrame.
    - iUnfold lp_noframe, lp_host, cwp_post_lp in "HΦ".
      iDestruct "HΦ" as "[_ []]".
  Qed.

  Lemma cwp_nop s E (f : frame) L R Φ :
    ↪[frame] f -∗ ↪[RUN] -∗ ▷ Φ f [] -∗ CWP [BI_nop] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros "Hf Hrun HΦ".
    unfold cwp_wasm.
    iApply (lenient_wp_nop with "[$] [$] [HΦ]").
    - by iModIntro.
    - done.
  Qed.

  Lemma cwp_unreachable s E (f : frame) L R Φ :
    ↪[frame] f -∗ ↪[RUN] -∗ CWP [BI_unreachable] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros "Hf Hrun".
    unfold cwp_wasm, lenient_wp.
    simpl to_e_list.
    iApply (wp_wand with "[Hf Hrun]").
    - iApply (wp_unreachable with "[$] [$]").
      by instantiate (1 := fun v => ⌜v = trapV⌝%I).
    - iIntros (v) "[[-> Hbail] Hf]".
      by iFrame.
  Qed.

  Lemma cwp_block (f : frame) s E es L R vs ts1 ts2 Φ :
    is_true (basic_const_list vs) ->
    length vs = length ts1 ->
    ↪[frame] f -∗
    ↪[RUN] -∗
    (↪[frame] f -∗ ↪[RUN] -∗ CWP vs ++ es @ s; E UNDER (length ts2, Φ) :: L; R {{ Φ }}) -∗
    CWP vs ++ [BI_block (Tf ts1 ts2) es] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hconst Hlen) "Hf Hrun Hes".
    unfold cwp_wasm, to_e_list.
    change seq.map with (@map basic_instruction administrative_instruction).
    rewrite !map_app.
    iApply (lenient_wp_block _ _ _ _ with "[$] [$]"); eauto.
    { by apply const_list_map_basic. }
    { by rewrite length_map. }
    iIntros "!> Hfr Hrun".
    iApply (lwp_cwp_label with "[$] [$] [Hes]"); first done.
    iIntros (f' vs' Hlen') "Hfr Hrun HΨ".
    rewrite app_nil_r.
    iApply lenient_wp_value.
    - by instantiate (1 := immV vs').
    - iExists f'. iFrame.
  Qed.

  Lemma cwp_loop (f : frame) s E es L R vs ts1 ts2 Φ Ψ :
    length vs = length ts1 ->
    ↪[frame] f -∗
    ↪[RUN] -∗
    (↪[frame] f -∗ ↪[RUN] -∗
     CWP map BI_const vs ++ es @ s; E UNDER (length ts1, Ψ) :: L; R {{ Φ }}) -∗
    □ (∀ f' vs',
         ↪[frame] f' -∗ ↪[RUN] -∗ Ψ f' vs' -∗
         CWP map BI_const vs' ++ es @ s; E UNDER (length ts1, Ψ) :: L; R {{ Φ }}) -∗
    CWP map BI_const vs ++ [BI_loop (Tf ts1 ts2) es] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hlen) "Hfr Hrun Hes #Hloop".
    unfold cwp_wasm, lenient_wp, to_e_list.
    change seq.map with (@map basic_instruction administrative_instruction).
    rewrite !map_app.
    change (map AI_basic [BI_loop (Tf ts1 ts2) es]) with [AI_basic (BI_loop (Tf ts1 ts2) es)].
    rewrite map_map.
    change (@map value administrative_instruction) with (@seq.map value administrative_instruction).
    fold (v_to_e_list vs).
    iApply (wp_loop with "[$] [$]").
    { apply v_to_e_is_const_list. }
    { by rewrite length_map. }
    { done. }
    { done. }
    iIntros "!> Hfr Hrun".
    iApply (lwp_cwp_label with "[$] [$] [Hes]").
    - iIntros "Hfr Hrun". iApply ("Hes" with "[$] [$]").
    - iIntros (f' vs' Hlen') "Hfr Hrun HΨ".
      iLöb as "IH" forall (f' vs' Hlen').
      iApply (wp_loop with "[$] [$]").
      { apply v_to_e_is_const_list. }
      { by rewrite length_map. }
      { done. }
      { done. }
      iIntros "!> Hfr Hrun".
      iApply (lwp_cwp_label with "[$] [$] [HΨ]").
      + iIntros "Hfr Hrun".
        iPoseProof ("Hloop" with "[$] [$] [$]") as "Hes".
        rewrite map_app.
        rewrite map_map.
        iApply "Hes".
      + iApply "IH".
  Qed.

  Lemma cwp_loop' (f : frame) s E es L R vs ts1 ts2 Φ Ψ :
    length vs = length ts1 ->
    ↪[frame] f -∗
    ↪[RUN] -∗
    Ψ f vs -∗
    □ (∀ f' vs',
         ↪[frame] f' -∗ ↪[RUN] -∗ Ψ f' vs' -∗
         CWP map BI_const vs' ++ es @ s; E UNDER (length ts1, Ψ) :: L; R {{ Φ }}) -∗
    CWP map BI_const vs ++ [BI_loop (Tf ts1 ts2) es] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hlen) "Hfr Hrun HΨ #Hloop".
    iApply (cwp_loop with "[$] [$] [HΨ]").
    - done.
    - iIntros "Hfr Hrun".
      by iPoseProof ("Hloop" with "[$] [$] [$]") as "Hes".
    - done.
  Qed.

  Lemma cwp_br (f : frame) s E L R n i P vs Φ :
    L !! i = Some (n, P) ->
    length vs = n ->
    ↪[frame] f -∗
    ↪[RUN] -∗
    P f vs -∗
    CWP map BI_const vs ++ [BI_br i] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hlb Hlen) "Hf Hrun HP".
    unfold cwp_wasm, lenient_wp.
    unfold to_e_list.
    rewrite seq_map_fmap.
    rewrite fmap_app.
    remember (of_val (brV (VH_base i vs []))) as es.
    pose proof Heqes as Heqes'.
    cbn in Heqes.
    replace (v_to_e_list vs) with (AI_basic <$> map BI_const vs) in Heqes; last first.
    {
      unfold v_to_e_list.
      rewrite seq_map_fmap.
      by rewrite <- list_fmap_compose.
    }
    cbn.
    rewrite <- Heqes.
    rewrite Heqes'.
    iApply wp_value'.
    unfold cwp_post_lp, cwp_post_br, denote_logpred; cbn.
    rewrite Nat.sub_0_r.
    rewrite Hlb.
    iFrame.
    by iExists [].
  Qed.

  Lemma cwp_return s E vs (f : frame) n P L Φ :
    length vs = n ->
    ↪[frame] f -∗
    ↪[RUN] -∗
    P vs -∗
    CWP map BI_const vs ++ [BI_return] @ s; E UNDER L; Some (n, P) {{ Φ }}.
  Proof.
    iIntros (Hlen) "Hf Hrun HP".
    unfold cwp_wasm, lenient_wp.
    iApply wp_value.
    - instantiate (1 := retV (SH_base vs [])).
      unfold IntoVal.
      cbn.
      unfold v_to_e_list, to_e_list.
      change (@seq.map basic_instruction administrative_instruction) with (@map basic_instruction administrative_instruction).
      rewrite map_app.
      by rewrite map_map.
    - unfold denote_logpred.
      iExists f.
      iFrame.
      by iExists [].
  Qed.

  Lemma cwp_call s E (f0 : frame) inst vs es ts1 ts2 ts i a L R Φ :
    f0.(f_inst).(inst_funcs) !! i = Some a ->
    length vs = length ts1 ->
    N.of_nat a ↦[wf] FC_func_native inst (Tf ts1 ts2) ts es -∗
    ↪[frame] f0 -∗
    ↪[RUN] -∗
    (N.of_nat a ↦[wf] FC_func_native inst (Tf ts1 ts2) ts es -∗
     ↪[frame] Build_frame (vs ++ n_zeros ts) inst -∗
     ↪[RUN] -∗
     CWP [BI_block (Tf [] ts2) es] @ s; E UNDER []; Some (length ts2, Φ f0)
         {{ _; vs, Φ f0 vs ∗ ⌜length vs = length ts2⌝ }}) -∗
    CWP map BI_const vs ++ [BI_call i] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hi Hlen) "Ha Hfr Hrun Hes".
    unfold cwp_wasm, to_e_list.
    change seq.map with (@map basic_instruction administrative_instruction).
    rewrite map_app.
    rewrite map_map.
    change (map AI_basic [BI_call i]) with [AI_basic (BI_call i)].
    iApply wp_wasm_empty_ctx.
    rewrite <- (app_nil_r [AI_basic (BI_call i)]).
    iApply wp_base_push; first apply v_to_e_is_const_list.
    iApply (wp_call_ctx with "[$] [$]"); first done.
    iIntros "!> Hfr Hrun".
    iApply wp_base_pull.
    iApply wp_wasm_empty_ctx.
    iApply (wp_invoke_native with "[$] [$] [$]").
    { apply to_val_v_to_e. }
    { done. }
    { done. }
    iIntros "!> (Hfr & Hrun & Ha)".
    iApply (lwp_cwp_local with "[$] [$]").
    iIntros "Hfr Hrun".
    by iSpecialize ("Hes" with "[$] [$] [$]").
  Qed.

  Lemma cwp_call_indirect s E (f0 : frame) inst vs es ts1 ts2 ts c i j a L R Φ :
    f0.(f_inst).(inst_funcs) !! i = Some a ->
    f0.(f_inst).(inst_types) !! i = Some (Tf ts1 ts2) ->
    f0.(f_inst).(inst_tab) !! 0 = Some j ->
    length vs = length ts1 ->
    N.of_nat j ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] Some a -∗
    N.of_nat a ↦[wf] FC_func_native inst (Tf ts1 ts2) ts es -∗
    ↪[frame] f0 -∗
    ↪[RUN] -∗
    (N.of_nat j ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] Some a -∗
     N.of_nat a ↦[wf] FC_func_native inst (Tf ts1 ts2) ts es -∗
     ↪[frame] Build_frame (vs ++ n_zeros ts) inst -∗
     ↪[RUN] -∗
     CWP [BI_block (Tf [] ts2) es] @ s; E UNDER []; Some (length ts2, Φ f0)
         {{ _; vs, Φ f0 vs ∗ ⌜length vs = length ts2⌝ }}) -∗
    CWP map BI_const vs ++ [BI_const (VAL_int32 c); BI_call_indirect i] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hfuncs Htypes Htab Hvs) "Hj Ha Hfr Hrun Hes".
    iApply wp_wasm_empty_ctx.
    unfold to_e_list.
    change seq.map with (@map basic_instruction administrative_instruction).
    rewrite map_app.
    rewrite map_map.
    rewrite <- (app_nil_r (map AI_basic _)).
    iApply wp_base_push; first apply v_to_e_is_const_list.
    iApply (wp_call_indirect_success_ctx with "[$] [$] [$] [$]").
    1, 2: done.
    iIntros "!> (Hj & Ha & Hfr) Hrun".
    iApply wp_base_pull.
    iApply wp_wasm_empty_ctx.
    simpl seq.cat.
    rewrite app_nil_r.
    iApply (wp_invoke_native with "[$] [$] [$]").
    { apply to_val_v_to_e. }
    { done. }
    { done. }
    iIntros "!> (Hfr & Hrun & Ha)".
    iApply (lwp_cwp_local with "[$] [$]").
    iIntros "Hfr Hrun".
    by iSpecialize ("Hes" with "[$] [$] [$] [$]").
  Qed.

End control.
