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


  Lemma compat_ite M F L L' wt wt' wtf wl wl' wlf es1 es2 es' τs1 τs2 :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let F' := F <| fc_labels ::= cons (τs2, L') |> in
    let ψ := InstrT (τs1 ++ [type_i32]) τs2 in
    has_instruction_type_ok F ψ L' ->
    (forall wt wt' wtf wl wl' wlf es',
        let fe := fe_of_context F' in
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        run_codegen (compile_instrs mr fe es1) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instruction_type_sem rti sr mr M F' L WT WL (to_e_list es') (InstrT τs1 τs2) L') ->
    (forall wt wt' wtf wl wl' wlf es',
        let fe := fe_of_context F' in
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        run_codegen (compile_instrs mr fe es2) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instruction_type_sem rti sr mr M F' L WT WL (to_e_list es') (InstrT τs1 τs2) L') ->
    run_codegen (compile_instr mr fe (IIte ψ L' es1 es2)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L'.
  Proof.
    intros fe WT WL F' ψ Hok Hthen Helse Hcodegen.
    iIntros (se inst lh fr rvs vs θ Henv) "#Hinst #Hctxt Hrvs Hvss Hvsl Hrt Hfr Hrun".
    iDestruct "Hvss" as (vss) "(-> & Hvss)".
    (*
    iDestruct "Hvsl" as (vsl' vswl') "(-> & %Hlocs & %Hrestype & Hlocs)".
    iDestruct "Hfrinv" as "[Htok Hfrinv]".
    apply Forall2_length in Hlocs as Hlenvsl.
    iDestruct (big_sepL2_length with "Hlocs") as "%Hlenvsl'".
    rewrite length_map in Hlenvsl'.
    rewrite map_app.
    iDestruct (big_sepL2_app_inv_l with "Hvss") as (vss1 vssi32) "(-> & Hvss1 & Hvssi32)".
    destruct vssi32; first done.
    iDestruct "Hvssi32" as "[Hvssi32 Hvoid]".
    destruct vssi32; last done.
    iClear "Hvoid".
    iDestruct (value_interp_eq with "Hvssi32") as "Hvssi32".
    iSimpl in "Hvssi32".
    iDestruct "Hvssi32" as (κ) "(%Heq & Hκ & _)".
    inversion Heq; subst κ; clear Heq.
    iSimpl in "Hκ".
    iDestruct "Hκ" as "%Hκ".

(*    destruct vswl; last by inversion Hrestype. *)
    destruct o as [|v vs]; inversion Hκ; subst; clear Hκ. 
    destruct vs as [|v' vs]; inversion H4; subst; clear H4.
    unfold primitive_rep_interp in H2.
    destruct H2 as [n ->].

(*    inversion Hok; subst.
    destruct H as [Hτs1 Hτs2].
    apply Forall_app in Hτs1 as [Hτs1 Hi32].
    inversion Hi32; subst.
    inversion H2; subst.
    inversion H; subst.
    inversion H4; subst. *)
    


    replace (compile_instr mr fe (IIte ψ L' es1 es2))
      with (compile_ite fe ψ (compile_instrs mr fe es1) (compile_instrs mr fe es2))
      in Hcodegen; last done.
    remember (compile_instrs mr fe es1) as compes1.
    remember (compile_instrs mr fe es2) as compes2.
    Opaque if_c. 
    simpl in Hcodegen. 


    inv_cg_bind Hcodegen ρ1 wl1 wl1' es_nil es1' Htype_rep Hcodegen.
    inv_cg_try_option Htype_rep.
    subst wl1 es_nil.
    rewrite app_nil_l in Hes_app_eq; subst es1'. 
    inv_cg_bind Hcodegen ρ2 wl2 wl2' es_nil es1' Htype_rep Hcodegen.
    inv_cg_try_option Htype_rep.
    subst wl2 es_nil.
    rewrite app_nil_l in Hes_app_eq; subst es1'. 

    inv_cg_bind Hcodegen ρ3 wl3 wl3' es_nil es1' Hcodegen Hend.
    rewrite /run_codegen /= in Hend.
    inversion Hend; subst wl3' es1'; clear Hend.
    rewrite app_nil_r in Hes_app_eq; subst es_nil.
    destruct ρ3.
    destruct u, u0. 
    
    Transparent if_c.
    rewrite /if_c in Hcodegen.
    subst wl1' wl' wl2'.
    rewrite !app_nil_r !app_nil_l.

    inv_cg_bind Hcodegen ρ3 wl1 wl1' es_nil es1' Hes1 Hcodegen.
    destruct ρ3. destruct u.
    subst es'.
    inv_cg_bind Hcodegen ρ3 wl2 wl2' es_nil' es2' Hes2 Hcodegen.
    destruct ρ3. destruct u.
    subst es1'.
    rewrite /run_codegen /= in Hcodegen.
    inversion Hcodegen; subst wl1' wl2' es2'; clear Hcodegen.
    apply run_codegen_capture in Hes1 as [Hes1 ->].
    apply run_codegen_capture in Hes2 as [Hes2 ->].

(*    unfold compile_instrs in Hthen.
    destruct u, u0. *)
    subst compes1 compes2.
    rewrite !app_nil_r in Hes1.
    rewrite !app_nil_r in Hes2.
    apply (Hthen _ _ (wl2 ++ wlf)) in Hes1; eauto.
    apply (Helse _ _ wlf) in Hes2; eauto.
    rewrite <- !app_assoc in Hes2.

    rewrite removelast_last in Heq_some.

    iDestruct (big_sepL2_length with "Hvss1") as "%Hlen1".
    (* iDestruct (big_sepL2_length with "Hvss0") as "%Hlen0". *)
    rewrite length_map in Hlen1.
(*    rewrite length_map in Hlen0. *)
    iDestruct (translate_types_length_subst _ _ _ _ _ _ _ _ Heq_some with "Hvss1") as "%Hlen1'".
    
    
    iSimpl.
    subst wl3.
    rewrite -> !app_nil_r in *.
    rewrite -> !app_nil_l in *.
    unfold lenient_wp.
    rewrite concat_app.
    rewrite -v_to_e_cat.
    rewrite cat_app -app_assoc.
    iSimpl.
    iApply wp_wasm_empty_ctx.
    rewrite <- (app_assoc _ [AI_basic _]).
    rewrite <- app_assoc in Hrestype.
    cbn.
    rewrite (separate2 (AI_basic _)).
    iApply wp_base_push; first by apply v_to_e_is_const_list.
    destruct (value_eq_dec (VAL_int32 n) (VAL_int32 (Wasm_int.int_zero i32m))).
    - (* n is false *)
      inversion e; subst.
      iApply (wp_if_false_ctx with "Hfr Hrun") => //.
      iIntros "!> Hfr Hrun".
      iApply wp_base_pull.
      iSimpl.
      iApply wp_wasm_empty_ctx.
      iApply (wp_block with "Hfr Hrun") => //.
      { apply v_to_e_is_const_list. }
      { rewrite v_to_e_length.
        rewrite length_concat.
        done. }
      iIntros "!> Hfr Hrun".
      iApply (wp_label_bind with "[-]").
      2:{ iPureIntro. instantiate (5 := []).
          rewrite /lfilled /lfill /= app_nil_r //. }
      iApply (wp_wand with "[-]").
      + iApply (Hes2 with "[%] Hinst [Hctxt] [$Hvss1] [$Hlocs] [$Htok] Hfr Hrun"); first assumption; cycle 1.
        * done.
        * iExists _; done.
        * iExists _, _. done.
        * instantiate (1 := (* push_base lh (length ρ2) [] [] []). *)
                         lh_plug (LH_rec _ _ _ (LH_base _ _) _) lh).  
          iDestruct "Hctxt" as "(%Hbase & %Hlength & %Hvalid & Hconts)".
          repeat iSplitR.
          all: try iPureIntro.
          -- apply base_is_empty_plug => //.
          -- eapply length_lholeds_app => //.
             split => //. 
             iIntros (?) "(%vss & -> & Hvss)".
             iDestruct (translate_types_length with "Hvss") as "%H".
             ++ exact Heq_some0.
             ++ rewrite length_concat -H. done. 
          -- apply lholed_valid_plug => //=.
             split => //. 
             apply v_to_e_is_const_list.
          -- iSimpl. iSplitR; last first. 
             ++ iApply (big_sepL_impl with "Hconts").
                iIntros "!>" (k [ts ctx] Hk) "#Hcont".
                unfold continuation_interp.
                iDestruct "Hcont" as (j es0 es es' lh' lh'') "(%Hlayer & %Hdepth & %Hminus & #Hcont)".
                iExists _,_,_,_,_,_.
                repeat iSplitR.
                1-3: iPureIntro.
                ** rewrite lh_depth_plug. simpl.
                   replace (lh_depth lh + 1 - S (S k)) with (lh_depth lh - S k); last lia.
                   apply get_layer_plug_shallow.
                   exact Hlayer. 
                ** rewrite lh_depth_plug. simpl.
                   replace (lh_depth lh + 1 - S (S k)) with
                     (lh_depth lh - S k); first exact Hdepth.
                   lia. 
                ** apply lh_minus_plug. done.
                ** iIntros "!>" (vs fr) "Hvs Hfr Hrun Hframe Hframe'".
                   iDestruct ("Hcont" with "Hvs Hfr Hrun Hframe Hframe'") as (τs') "Hexp".
                   iExists τs'.
                   done.

             ++ iExists _, _, _, _,_, _.
               iSplit.
               { iPureIntro.
                 rewrite lh_depth_plug /= Nat.add_sub.
                 apply get_layer_plug_precise => //. } 
               iSplit; first iSimpl.
               { (* instantiate (5 := lh). *)
                 rewrite lh_depth_plug /= Nat.add_sub //. }
               iSplit.
               { iPureIntro. 
                 erewrite lh_plug_minus => //. }
               iIntros "!>" (vs fr) "Hvs Hfr Hrun Hframe Hframe'".
               iExists _.
               unfold expr_interp.
               iSimpl.
               unfold lenient_wp.
               do 3 instantiate (2 := []).
               rewrite app_nil_r app_nil_r /=.

               iApply wp_value.
               { apply of_to_val. unfold language.to_val.
                 simpl. apply to_val_v_to_e. } 
               rewrite /denote_logpred /=.
               iFrame.
(*             iApply (big_sepL_impl with "Hconts").
             iIntros "!>" (k [ts ctx] Hk) "#Hcont".
             unfold continuation_interp.
             iDestruct "Hcont" as (j es0 es es' lh' lh'') "(%Hlayer & %Hdepth & %Hminus & #Hcont)".
             iExists _,_,_,_,_,_.
             repeat iSplitR.
             1-3: iPureIntro.
             ++ rewrite lh_depth_plug. simpl.
                replace (lh_depth lh + 1 - S (S k)) with (lh_depth lh - S k); last lia.
                apply get_layer_plug_shallow.
                exact Hlayer. 
             ++ rewrite lh_depth_plug. simpl.
                replace (lh_depth lh + 1 - S (S k)) with
                  (lh_depth lh - S k); first exact Hdepth.
                lia. 
             ++ apply lh_minus_plug. done.
             ++ iIntros "!>" (vs fr) "Hvs Hfr Hframe".
                iDestruct ("Hcont" with "Hvs Hfr Hframe") as (τs') "Hexp".
                iExists τs'.
                done.
        * done.
        * iExists _, _. iSplit; first done. iSplit; first done.
          rewrite <- !app_assoc in Hrestype.
          iPureIntro. exact Hrestype. *)

      + iIntros (v) "H".
        rewrite /denote_logpred /lp_noframe /=.
        iIntros (LI HLI).
        apply lfilled_Ind_Equivalent in HLI; inversion HLI; subst.
        cbn.
        inversion H8; subst.
        clear HLI H7 H8 H1.
        iSimpl.

        destruct v.
        * (* immV case *)
          iDestruct "H" as "(%fr & Hfr & (Htok & _) & (%vssl & %vswl0 & %Heq & %Hlocs' & %Hrestype' & Hlocs) & Hrun & %vss & -> & Hvss)".
          subst fr.
          iApply (wp_wand with "[Hfr Hrun]").
          { iApply (wp_label_value with "Hfr Hrun").
            - rewrite seq.cats0. rewrite to_of_val. done.
            - by instantiate (1 := λ v, ⌜ v = immV _ ⌝%I). }
          iIntros (v) "[[-> Hrun] Hfr]".
          iFrame.
          iSplit. 
          -- iExists _,_. done.
          -- iSplit; last done. iExists _. done. 
        * (* trapV case *)
          iDestruct "H" as "(%fr & Hfr & (Htok & %vssl & %vswl0' & -> & % & %) & Hbail & _)".
          iApply (wp_wand with "[Hfr]").
          { iApply (wp_label_trap with "Hfr") => //.
            instantiate (1 := λ v, ⌜ v = trapV ⌝%I) => //. }
          iIntros (v) "[-> Hfr]".
          iFrame.
          iExists _,_. done.
        * (* brV case *)
          iDestruct "H" as "(%fr & Hfr & (Htok & %vssl & %vswl0' & -> & %Hlocs' & %Hrestype') & Hrun & Hbr)".
          iDestruct (br_interp_eq with "Hbr") as "Hbr".
          unfold br_interp0. iSimpl in "Hbr".
          iDestruct "Hbr" as (k p lh' lh'' τs es0 es es' vs0 vs) "(%Hgetbase & %Hdepth & %Hlabels & %Hlayer & %Hdepth' & %Hminus & (%vss2 & -> & Hvss2) & Hbr)".
          iDestruct (big_sepL2_length with "Hvss2") as "%Hlen2".
          (* iDestruct (translate_types_length with "Hvss2") as "%Hlen2'".
          ; first exact Heqtrans2. *)
(*          (* may need to first progress in wp before yielding frame *)
          iDestruct ("Hbr" with "Hfr [Hvss2] [$Htok]") as "Hbr".
          { iExists _,_. iSplit; first done. admit. } 
          { iExists _,_. iSplit; first done. done. } 
          unfold lenient_wp_ctx.
          (* iDestruct ("Hbr" with "[]") as "Hbr".
          { iPureIntro. 
            rewrite lh_depth_plug /=. *)

          (* Hmmmm this next part should work… *) 
(*          iDestruct wp_value_fupd as "[H _]"; 
            last iMod ("H" with "Hbr") as "Hbr".
          { unfold IntoVal. apply of_to_val.
            unfold language.to_val. simpl. 
            rewrite (separate1 (AI_basic _)).
            apply to_val_br_eq. }
          iClear "H".
          unfold denote_logpred.
          iSimpl in "Hbr".
          iDestruct "Hbr" as "(Hbr & %fr & Hfr & %vssl' & %vswl'' & -> & Hlocs & Hrestype' & Htok)". *) *)
          destruct (decide (i = p)).
          -- (* targetting this exact block *)
            subst p. 
            destruct (pull_base_l_drop_len lh0 (length (vs0 ++ concat vss2) - length ρ2)) eqn:Hpb.
            rewrite seq.cats0.
            unfold of_val. 
            erewrite vfill_pull_base_l_take_len.
            2:{ exact Hpb. }
            pose proof (vfill_to_lfilled v ((v_to_e_list l1) ++ [AI_basic (BI_br i)])) as [Hle Hfill].
            erewrite <- lh_depth_pull_base_l_take_len in Hfill;[|eauto]. 
            rewrite -e0 in Hfill.
            rewrite -e0 Nat.sub_diag /= in Hlabels.
            rewrite -e0 Nat.sub_diag /= in Hlayer.
            rewrite lh_depth_plug /= in Hlayer.
            rewrite Nat.add_sub in Hlayer.
(*            erewrite get_layer_plug_precise in Hlayer.
            2:{ Search lh. done. *)
            
            rewrite -e0 Nat.sub_diag. 
            inversion Hlabels; subst τs2; clear Hlabels. 
            iApply (wp_br with "Hfr Hrun").
            3: exact Hfill.
            ++ apply v_to_e_is_const_list. 
            ++ rewrite length_fmap.
               eapply length_pull_base_l_take_len in Hpb;[|eauto]. rewrite Hpb.
               assert (length (vs0 ++ concat vss2) >= length ρ2);[|lia].
               rewrite -Hgetbase.
               admit. 
(*               rewrite Hlen2. lia. } *)
            ++ iNext. iIntros "Hf Hrun".
               rewrite app_nil_r.
               iApply wp_value.
               { apply of_to_val. apply to_val_v_to_e. }
(*               iDestruct ("Hbr" with "Hf [Hvss2] [$Htok]") as "Hbr".
               { iExists _,_. iSplit; first done. iSplit; first done.
                 iSplit; first done.  admit. } 
               { iExists _,_. iSplit; first done. done. }  *)
               iFrame.
               iSplitR; last iSplitR. 
               ** iExists _,_. iSplit; first done.
                  done.
               ** iExists _,_. iSplit; first done.
                  iSplit; first (iPureIntro; exact Hlocs').
                  iSplit; first done.
                  admit.
               ** admit.
(*          -- (* targetting this exact block *)
            rewrite lh_depth_plug /= Nat.add_sub in Hdepth' Hlayer.
            replace iris_lfilled_properties.get_layer with get_layer in Hlayer; last done
            erewrite get_layer_plug_precise in Hlayer.
            3: done.
            2:{ admit. }
            inversion Hlayer; subst; clear Hlayer.
            simpl in Hlabels.
            inversion Hlabels; subst; clear Hlabels. 
            assert (j = p) as ->.
            { 
            assert (i = p) as ->.
            { clear - Heqhop Hdepth.
              specialize (vfill_to_lfilled lh0 []) as [H _].
              rewrite Hdepth in H. lia. }
            assert (j = p) as ->.
            { admit. }
            rewrite Nat.sub_diag lh_depth_plug /= Nat.add_sub in Hdepth'.
            rewrite Nat.sub_diag /= in Hlabels.
            inversion Hlabels; subst τs; clear Hlabels. 
            iDestruct (translate_types_length with "Hvss2") as "%Hlen2'".
            { exact Heq_some0. }
            rewrite Nat.sub_diag in Hlayer.
            rewrite lh_depth_plug /= in Hlayer.
            rewrite Nat.add_sub in Hlayer.
            replace ( iris_lfilled_properties.get_layer
                        (lh_plug (LH_rec [] (length ρ2) [] (LH_base [] []) []) lh) 
                        (lh_depth lh))
              with ( get_layer
                       (lh_plug (LH_rec [] (length ρ2) [] (LH_base [] []) []) lh) 
                       (lh_depth lh)) in Hlayer; last done.
            erewrite get_layer_plug_precise in Hlayer => //.
            2:{ admit. }
            inversion Hlayer; subst. 

            iApply (wp_br with "[]").
            3:{ rewrite seq.cats0 /=. 
                instantiate (1 := p).
                instantiate (1 := v_to_e_list (concat vss2)).
                instantiate (1 := lh_of_vh (replace_base lh0 vs0)).
                clear - Hgetbase Hdepth.
                apply lfilled_get_replace_base => //. } 
            ++ apply v_to_e_is_const_list.
            ++ rewrite v_to_e_length length_concat //.
            ++ admit. (* def of br_interp? or my proof? *) 
            ++ admit. (* fix def of br_interp *) 
            ++ iIntros "!> Hf Hrun".
               edestruct const_list_to_val as [vs Hvs]; first by apply v_to_e_is_const_li
               iApply wp_value.
               { apply of_to_val. rewrite app_nil_r. exact Hvs. }
               iSimpl. iFrame.
               iSplitL "Hvss2".
               ** apply v_to_e_list_to_val in Hvs as Hvs'.
                  apply v_to_e_inj in Hvs' as ->.
                  iExists _. iSplit; first done.
                  admit. 
               ** iExists _,_. iSplit; first done.
                  admit. *)
          -- (* still blocked *)
            assert (i > p) as Hip.
            { destruct (vfill_to_lfilled lh0 []) as [? _].
              rewrite Hdepth in H.
              lia. } 
            destruct i; first lia.
            destruct (vh_decrease lh0) eqn:Hlh0.
            2:{ exfalso. clear - Hip Hlh0 Hdepth.
                eapply vh_depth_can_decrease => //.
                by rewrite Hdepth. } 
            iApply wp_value.
            { apply of_to_val. rewrite seq.cats0 /=. 
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
(*            iDestruct ("Hbr" with "Hfr [Hvss2] [$Htok]") as "Hbr".
            { iExists _,_. iSplit; first done. iSplit; first done.
              iSplit; first done. admit. } 
            { iExists _,_. iSplit; first done. done. }  *)

            iFrame.
            iSplitR.
            ++ iExists _,_. iSplit; first done. done. 
            ++ iApply br_interp_eq.
               rewrite /br_interp0 /=.
               rewrite lh_depth_plug /= in Hlayer.
               apply get_layer_plug_shallow_inv in Hlayer as (lhnew & Hlayer & ->).
               2:{ clear - Hip.
                   assert (S i - p > 0); first lia.
                   assert (lh_depth lh > 0).
                   { admit. } 
                   lia. }
                  
               repeat iExists _.
               iFrame "Hvss2".
               repeat (iSplit; first iPureIntro).
               ** apply get_base_vh_decrease in Hlh0.
                  rewrite Hlh0. done.
               ** apply lh_of_vh_decrease in Hlh0.
                  rewrite -Hlh0 in Hdepth.
                  rewrite Hdepth. done.
               ** destruct (S i - p) eqn:Hip'; first lia. 
                  simpl in Hlabels.
                  replace (S i - S p) with n0; last lia.
                  done.
               ** rewrite <- Hlayer.
                  f_equal. lia.
               ** rewrite lh_depth_plug /= in Hdepth'.
                  instantiate (1 := lh'').
                  lia.
               ** admit.
               ** done.
               ** iIntros (fr) "Hfr H1 H2".
                  iDestruct ("Hbr" with "Hfr H1 H2") as "H".
                  iIntros (LI HLI).
                  (* br index weirdness *)
                  admit. 
        * iApply wp_value.
          { apply of_to_val.
            rewrite seq.cats0 /=.
            unfold RichWasm.iris.language.iris.iris.to_val.
            simpl.
            specialize (to_of_val (retV s)) as H.
            simpl in H.
            unfold RichWasm.iris.language.iris.iris.to_val in H.
            destruct (merge_values_list _); try by exfalso.
            inversion H; subst v; clear H.
            done. }
          iSimpl.
          iDestruct "H" as "(%fr & Hfr & (Htok & %vssl & %vswl0' & -> & % & %) & Hrun & %vs0 & %vs & %Hgetbase & (%vss & -> & Hvss) & Hret)".
          iFrame.
          iSplit.
          -- iExists _,_. done.
          -- iExists _,_. iSplit; first done. iSplit; first done.
             iIntros (fr fr') "Hf".
             admit. (* generalise s in IH? *)
        * iDestruct "H" as "(%fr & Hfr & _ & _ & ?)"; done.
    - (* n is true *)
      admit.
    *)
  Admitted.

End Fundamental.
