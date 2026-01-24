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

  Lemma compat_block M F L L' n_skip wt wt' wtf wl wl' wlf τs1 τs2 es es' :
    let fe := fe_of_context F <| fe_br_skip := n_skip |> in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let F' := F <| fc_labels ::= cons (τs2, L') |> in
    let ψ := InstrT τs1 τs2 in
    has_instruction_type_ok F ψ L' ->
    (forall m_skip wt wt' wtf wl wl' wlf es',
        let fe' := fe_of_context F' <| fe_br_skip := m_skip |> in
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        run_codegen (compile_instrs mr fe' es) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instruction_type_sem rti sr mr M F' L WT WL (to_e_list es') ψ L') ->
    run_codegen (compile_instr mr fe (IBlock ψ L' es)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L'.
  Proof.
    intros fe F' WT WL ψ Hok IH Hrun.
    cbn [compile_instr] in Hrun.
    inv_cg_bind Hrun ρ wt0 wt0' wl0 wl0' es_nil es0' Hrun1 Hrun2.
    subst wt' wl' es'.
    cbn in Hrun1.
    inv_cg_try_option Hrun1.
    do 2 rewrite app_nil_r in Hrun2.
    subst wt0 wl0 es_nil.
    destruct (prelude.translate_types (fc_type_vars F) τs1) as [ts1|] eqn:Hts1; last done.
    destruct (prelude.translate_types (fc_type_vars F) τs2) as [ts2|] eqn:Hts2; last done.
    simpl in Heq_some.
    inversion Heq_some; subst ρ; clear Heq_some.
    inv_cg_bind Hrun2 ρ wt0 wt1 wl0 wl1 es1 es0 Hrun1 Hrun2.
    destruct ρ, u.
    inv_cg_emit Hrun2.
    rewrite app_nil_r in Hwt_app_eq.
    rewrite app_nil_r in Hwl_app_eq.
    subst wl1 es0 wt0' wl0' wt1 es0'.
    clear Hretval.
    apply run_codegen_capture in Hrun1 as [Hrun1 ->].
    eapply IH in Hrun1.
    unfold have_instruction_type_sem.
(*    iSimpl. *)
    iIntros (se inst lh fr rvs vs θ) "%Henv #Hinst (%Hlhbase & %Hlengthlh & %Hlh & Hlabs)".
    iIntros "Hrvs (%vss & -> & Hvss) (%rvssl & %vssl & %vswl & -> & %Hres & Hvssl) Htok Hfr Hrun".
    iDestruct (translate_types_length with "Hvss") as "%Hlenvss" => //.
    iDestruct (big_sepL2_length with "Hrvs") as "%Hlenrvs". 
    unfold lenient_wp.
    iApply (wp_block with "Hfr Hrun").
    { apply v_to_e_is_const_list. }
    { done. } 
    { rewrite v_to_e_length Hlenvss.
      rewrite length_concat in Hlenrvs. done. }
    { done. }
    iIntros "!> Hfr Hrun".
    iApply (wp_label_bind with "[-]").
    2:{ iPureIntro.
        instantiate (2 := []).
        instantiate (2 := []).
        instantiate (2 := length ts2).
        instantiate (2 := []).
        rewrite /lfilled /lfill /= app_nil_r.
        done. }
    unfold have_instruction_type_sem in Hrun1.
    
(*    simpl in Hrun1. *)
    iApply (wp_wand with "[-]"). 
    { iApply (Hrun1 with "[] Hinst [Hlabs] [$Hrvs] [$Hvss] [$Hvssl] [$Htok] Hfr Hrun") => //.
      - instantiate (1 := lh_plug (LH_rec [] (length ts2) [] (LH_base [] []) []) lh).
        repeat (iSplit; first iPureIntro).
        + apply base_is_empty_plug => //. 
        + apply length_lholeds_app => //=.
          split; last done.
          iIntros (rvs) "(%vss0 & -> & Hvss0)".
          iDestruct (translate_types_length with "Hvss0") as "%Hlenvss0" => //.
          iPureIntro.
          rewrite length_concat //.
        + apply lholed_valid_plug => //.
        + Opaque continuation_interp.
          simpl. 
          iSplitR. 
          * Transparent continuation_interp.
            unfold continuation_interp.
            iExists _,_,_,_,_,_.
            rewrite lh_depth_plug /= Nat.add_sub.
            repeat (iSplit; first iPureIntro).
            -- apply get_layer_plug_precise => //.
            -- done.
            -- rewrite lh_plug_minus => //.
            -- iIntros "!>" (fr vs0 rvs θ0) "Hrvs (%vss0 & -> & Hvss0) (%rvssl0 & %vssl0 & %vswl0 & -> & %Hres0 & Hvssl0) Htok Hfr Hrun".
               rewrite app_nil_r app_nil_r /=.
               iExists _.
               unfold lenient_wp.
               iApply wp_value.
               { apply of_to_val.
                 fold (of_val (immV vs0)).
                 apply to_of_val. }
               unfold denote_logpred.
               iFrame.
               iSplit.
               ++ iExists _. done.
               ++ done.
          * iApply (big_sepL_impl with "Hlabs").
            iIntros "!>" (k x Hk).
            destruct x.
            iIntros "Hcont".
(*            unfold continuation_interp. *)
            iDestruct "Hcont" as (j ?????) "(%Hlayer & %Hdepth & %Hminus & #H)".
            iExists _,_,_,_,_,_.
            rewrite lh_depth_plug.
            replace (lh_depth lh + 1 - S (S k)) with (lh_depth lh - S k); last lia.           
            repeat (iSplit; first iPureIntro).
            -- apply get_layer_plug_shallow => //=.
               replace (lh_depth lh + 1 - S (S k)) with (lh_depth lh - S k); last lia.
               done.
            -- simpl.
               replace (lh_depth lh + 1 - S (S k)) with (lh_depth lh - S k); last lia.
               exact Hdepth.
            -- apply lh_minus_plug => //.
            -- done. 
      - iExists _. done. 
    } 
    clear Hrun1 IH. 
    iIntros (v) "H".
    unfold denote_logpred.
    iSimpl in "H".
    iDestruct "H" as (f) "(Hf & _ & Hv)".
    iIntros (LI HLI).
    apply lfilled_Ind_Equivalent in HLI.
    inversion HLI; subst.
    inversion H8; subst.
    iSimpl. rewrite seq.cats0.
    destruct v.
    - (* immV case *)
      iSimpl in "Hv".
      iDestruct "Hv" as "(Hrun & Hframe & Hframeinv)".
      iApply (wp_wand with "[Hf Hrun]").
      { iApply (wp_label_value with "Hf Hrun"); first by apply to_of_val.
        by instantiate (1 := λ v, ⌜ v = immV _ ⌝%I). }
      iIntros (v) "[[-> Hrun] Hf]".
      iFrame. 
    - (* trapV case *)
      iSimpl in "Hv".
      iDestruct "Hv" as "[Hbail _]".
      iApply (wp_wand with "[Hf]").
      { iApply (wp_label_trap with "Hf") => //.
        by instantiate (1 := λ v, ⌜ v = trapV ⌝%I). }
      iIntros (v) "[-> Hf]".
      iFrame. 
    - (* brV case *)
      iSimpl in "Hv".
      iDestruct "Hv" as "[Hrun Hbr]".
      iDestruct (br_interp_eq with "Hbr") as "Hbr".
      unfold br_interp0.
      iSimpl in "Hbr".
      iDestruct "Hbr" as (k p lh' lh'' τs es0 es1 es2 vs0 vs1 rvs)
                           "(%Hbaselh0 & %Hdepthlh0 & %Hlab & %Hlayer & %Hdepthlh'' & %Hminus & Hrvs & (%vss0 & -> & Hvss0) & Hbr)".
      destruct (decide ( i = p)).
      + (* case 1: the br targets this exact label *)
        iClear "Hbr".
        subst p. 
        destruct (pull_base_l_drop_len lh0 (length (vs0 ++ vs1) - length ts2)) eqn:Hpb.
        unfold of_val. 
        erewrite vfill_pull_base_l_take_len.
        2:{ exact Hpb. }
        pose proof (vfill_to_lfilled v ((v_to_e_list l0) ++ [AI_basic (BI_br i)])) as [Hle Hfill].
        erewrite <- lh_depth_pull_base_l_take_len in Hfill;[|eauto]. 
        rewrite -e in Hfill.
        rewrite -e Nat.sub_diag /= in Hlab.
        rewrite -e Nat.sub_diag /= in Hlayer.
        rewrite lh_depth_plug /= in Hlayer.
        rewrite Nat.add_sub in Hlayer.
        inversion Hlab; subst τs2; clear Hlab.
        iDestruct (translate_types_length with "Hvss0") as "%Hlenvss0" => //.
        iDestruct (big_sepL2_length with "Hrvs") as "%Hlenrvs0". 
        iApply (wp_br with "Hf Hrun").
        3: exact Hfill.
        * apply v_to_e_is_const_list. 
        * rewrite length_fmap.
           eapply length_pull_base_l_take_len in Hpb;[|eauto]. rewrite Hpb.
           assert (length (vs0 ++ vs1) >= length ts2);[|lia].
           rewrite length_app Hlenvss0. rewrite length_concat in Hlenrvs0. 
           rewrite -Hlenrvs0. lia. 
        * iNext. iIntros "Hf Hrun".
           rewrite app_nil_r.
           iApply wp_value.
           { apply of_to_val. apply to_val_v_to_e. }
           iSimpl. iFrame.
           admit. 
(*           iSplitR. 
           { admit. }
           iExists _,_. iSplit; first done.
           iSplitR; last iSplitR. 
           -- iExists _,_. done. 
           -- iExists _,_. 
              iSplit; first done.
              iSplit; first done. 
              iSplit; first done.
              admit.
           -- iSimpl. iExists _.
              admit. *)
      + (* case 2: the br is still stuck *)
        assert (i > p) as Hip.
        { destruct (vfill_to_lfilled lh0 []) as [? _].
          rewrite Hdepthlh0 in H.
          lia. } 
        destruct i; first lia.
        destruct (vh_decrease lh0) eqn:Hlh0.
        2:{ exfalso. clear - Hip Hlh0 Hdepthlh0.
            eapply vh_depth_can_decrease => //.
            by rewrite Hdepthlh0. } 
        iApply wp_value.
        { apply of_to_val. 
          simpl.
          unfold RichWasm.iris.language.iris.iris.to_val.
          simpl.
          rewrite seq.cats0.
          specialize (to_of_val (brV lh0)) as H.
          simpl in H.
          unfold RichWasm.iris.language.iris.iris.to_val in H.
          destruct (merge_values_list _) ; try by exfalso.
          inversion H; subst v0; clear H.
          rewrite Hlh0. 
          done. } 
        iSimpl.
        iFrame.
        rewrite br_interp_eq.
        rewrite /br_interp0 /=.
        rewrite lh_depth_plug /= in Hlayer.
        apply get_layer_plug_shallow_inv in Hlayer as (lhnew & Hlayer & ->).
        2:{ clear - Hip.
            assert (S i - p > 0); first lia.
            assert (lh_depth lh > 0).
            { admit. } 
            lia. }
        iExists _, (S p).
        repeat iExists _.
        iDestruct (translate_types_length with "Hvss0") as "%Hlenvss0" => //.
        { admit. } 
        iFrame "Hvss0".
        repeat (iSplit; first iPureIntro).
        -- apply get_base_vh_decrease in Hlh0.
           rewrite Hlh0. done.
        -- apply lh_of_vh_decrease in Hlh0.
           rewrite -Hlh0 in Hdepthlh0.
           rewrite Hdepthlh0. done.
        -- destruct (S i - p) eqn:Hip'; first lia. 
           simpl in Hlab.
           replace (S i - S p) with n0; last lia.
           done.
        -- rewrite <- Hlayer.
           f_equal. lia.
        -- rewrite lh_depth_plug /= in Hdepthlh''.
           instantiate (1 := lh'').
           lia.
        -- rewrite lh_depth_plug /= in Hdepthlh''.
           admit. (* manipulate minus *)
        -- iFrame.
           iSplit; first done.
           iIntros (fr θ0) "Hfr H1 H2".
           iDestruct ("Hbr" with "Hfr H1 H2") as "H".
           assert (lh_depth lhnew = i - p).
           { (* should be given by Hlayer, just need to convince lia *)
             admit. }
           
             iIntros (LI HLI').
             iApply (wp_br_ctx_shift_inv with "[] [H]"); last first.
             ++ iPureIntro.
                apply get_layer_depth in Hlayer.
                rewrite H in HLI'.
                exact HLI'.
             ++ iIntros "Hrun".
                rewrite lh_depth_plug H /=.
                replace (lh_plug (LH_rec [] (length ts2) [] (LH_base [] []) []) lhnew) with (push_base lhnew (length ts2) [] [] []).
                2:{ (* should be easy *) admit. }
                replace (S (i - p + 1)) with (S (S (i - p))); last lia.
                replace (S (i - p)) with (S i - p); last lia.
                iFrame.
             ++ admit.
             ++ replace (lh_depth lh + 1 - S (S i - p))
                  with (lh_depth lh - S (i - p)) in Hlayer; last lia. 
                eapply get_layer_lookup_lh_lengths in Hlayer => //.
                2:{ replace (S i - p) with (S (i - p)) in Hlab; last lia.
                    simpl in Hlab. done. }
                admit. (* massage get_layer_lookup_lh_lengths and Hlenvss0 *)
             ++ done.
             ++ apply v_to_e_is_const_list.
    - (* retV case *)
      iApply wp_value.
      { apply of_to_val.
        unfold RichWasm.iris.language.iris.iris.to_val.
        simpl.
        specialize (to_of_val (retV s)) as H.
        simpl in H.
        unfold RichWasm.iris.language.iris.iris.to_val in H.
        destruct (merge_values_list _); try by exfalso.
        inversion H; subst v; clear H.
        done. }
      iSimpl.
      iSimpl in "Hv". 
      iDestruct "Hv" as "(Hrun & %vs0 & %vs' & %rvs & %Hgetbase & Hrvs & (%vss0 & -> & Hvss0) & Hret)".
      iFrame.
      iExists _. iSplit; first done. iSplit; first done.
      iIntros (fr fr') "Hf Hrun".
      admit. (* generalise s in IH? Check out interp_return_label in iris-wasm *)
    - iSimpl in "Hv". iDestruct "Hv" as "[_ ?]" => //.
  Admitted.

End Fundamental.
