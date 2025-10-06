Require Import RecordUpdate.RecordUpdate.

From iris.proofmode Require Import base tactics classes.

From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import prelude codegen instruction module.
From RichWasm.iris Require Import autowp gc.
From RichWasm.iris.language Require Import lenient_wp lwp_pure lwp_structural logpred.
From RichWasm.iris.logrel Require Import relations fundamental_kinding.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Fundamental.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!RichWasmGCG Σ}.

  Variable sr : store_runtime.
  Variable mr : module_runtime.

  (* This should be moved to the logpred module. *)
  Definition lp_wand' Φ1 Φ2 : iProp Σ :=
    ∀ lv, denote_logpred Φ1 lv -∗ denote_logpred Φ2 lv.

  (* This should be moved to the lwp_structural module. *)
  Lemma lwp_wand s E es Φ Ψ :
    ⊢ lp_wand' Φ Ψ -∗
      lenient_wp s E es Φ -∗
      lenient_wp s E es Ψ.
  Proof.
    unfold lp_wand', lenient_wp.
    iIntros "Hwand HΦ".
    iApply (wp_wand with "[$] [$]").
  Qed.

  Lemma compat_nop M F L wl wl' es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [] [] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (INop ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Proof.
    (* This is currently following the compat_copy lemma very closely *)
    intros me fe ψ Hok Hcompile.
    inv_cg_emit Hcompile.
    unfold have_instruction_type_sem.
    destruct ψ eqn:Hψ.
    inversion Hψ; subst l l0.
    iIntros (? ? ? ? ? ?) "Henv Hinst Hlf".
    iIntros (? ?) "Hvs Hframe Hfr Hrun".
    unfold expr_interp; cbn.
    iDestruct "Hvs" as "(%vss & %Hconcat & Hvs)".
    iPoseProof (big_sepL2_length with "[$Hvs]") as "%Hlens".
    (* To prove a list is nil, it's often easier to destruct it and
       then show the cons case is impossible.

       Here the congruence tactic deals with the 3 subgoals where
       something is not nil, where the hyps Hlens or Hconcat equate
       terms with obviously different constructors, like
         v :: vs = []
       or
         0 = S (...).                               - Ryan *)
    destruct vss, vs; cbn in Hconcat, Hlens; try congruence.
    cbn.
    (* To apply lenient_wp_nop, some strangeness has to happen
     with ->[RUN] being in the Phi. This is where lwp_wand comes in.*)

    (* I've tried to clean this definition up a bit, but it's the same
       as the one that was in an instantiate (1 := ...) tactic earlier
       -Ryan *)
    set (Ψ := {|
            lp_fr := λ fr, ∃ vs__L vs__WL,
              ⌜fr = {| W.f_locs := vs__L ++ vs__WL; W.f_inst := inst |}⌝ ∗
              (∃ vss, ⌜vs__L = concat vss⌝ ∗
                      [∗ list] τ;vs ∈ map (subst_type s__mem s__rep s__size VarT) L;vss,
                      value_interp sr mr se τ (SValues vs)) ∗
                  ⌜result_type_interp wl vs__WL⌝ ∗ na_own logrel_nais ⊤;
            lp_val :=
              λ vs, ∃ vss, ⌜vs = concat vss⌝ ∗
                           [∗ list] τ;vs' ∈ [];vss, value_interp sr mr se τ (SValues vs');
            lp_trap := True;
            lp_br := br_interp sr mr se F (map (subst_type s__mem s__rep s__size VarT) L) wl inst lh F.(fc_labels);
            lp_ret := return_interp sr mr se F;
            lp_host := fun _ _ _ _ => False
          |}%I).
    iApply lwp_wand; [| iApply (lenient_wp_nop _ _ Ψ)].
    (* Note: this strange iApply in the second subgoal makes sure that the
     ?Goal is made into the right shape (lp_run ?Goal) in the first subgoal*)
    - unfold lp_wand'.
      iIntros (lv).
      unfold denote_logpred.
      cbn.
      iIntros "[LPrunframe [%f [Hf Hlpfr]]]".
      iSplitL "LPrunframe".
      + unfold lp_run.
        unfold lp_with.
        cbn.
        case lv; simpl; auto.
        * iDestruct "LPrunframe" as "[H1 [H2 H3]]". iFrame.
        * iIntros. iDestruct "LPrunframe" as "[H _]". iExact "H".
        * iIntros. by iDestruct "LPrunframe" as "[H _]".
        * iIntros. by iDestruct "LPrunframe" as "[H _]".
      + iFrame.
    - cbn. iFrame. cbn. iExists _. iSplit; auto. auto.
  Qed.

  Lemma compat_unreachable M F L L' wl wl' ψ es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr me fe (IUnreachable ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_copy M F L wl wl' τ es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [τ] [τ; τ] in
    has_copyability F τ ExCopy ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (ICopy ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Proof.
    intros me fe ψ Hcopy Hok Hcompile.
    unfold compile_instr in Hcompile.
    inv_cg_bind Hcompile ρ wl1 es_nil es1 Htype_rep Hcompile.
    inv_cg_bind Hcompile ιs wl2 es_nil' es2 Heval_rep Hcompile.
    unfold have_instruction_type_sem.
    destruct ψ eqn:Hψ.
    inversion Hψ; subst l l0.
    iIntros (? ? ? ? ? ?) "Henv Hinst Hlh".
    iIntros (fr vs) "Hvs Hframe Hfr Hrun".
    unfold expr_interp.
    cbn.
    inv_cg_try_option Htype_rep.
    inv_cg_try_option Heval_rep.
    rewrite app_nil_l.
    inversion Hcopy as [F' τ' ρ' χ ? Hhas_kind HF' Hτ' Hχ].
    subst F' τ'.
    pose proof (kinding_sound sr mr F s__mem s__rep s__size se _ _ Hhas_kind) as Hhas_kind_sem.
    iPoseProof (Hhas_kind_sem with "Henv") as "Hskind".
    iDestruct "Hskind" as "[Hrefine Hcopyable]".
    iEval (cbn) in "Hcopyable".
    assert (ρ' = ρ).
    {
      apply type_rep_has_kind_agree in Hhas_kind.
      rewrite Heq_some in Hhas_kind.
      congruence.
    }
    subst ρ'.
    iDestruct "Hvs" as "(%vss & %Hconcat & Hvs)".
    iPoseProof (big_sepL2_length with "[$Hvs]") as "%Hlens".
    destruct vss as [|vs' [|vs'' vss]]; cbn in Hlens, Hconcat; try congruence.
    rewrite app_nil_r in Hconcat; subst vs'.
    rewrite big_sepL2_singleton.
    iApply (lwp_wand with "[Hframe]"); last first.
    - iApply ("Hcopyable" with "[] [] [$Hfr] [$Hrun] [$Hvs]").
      + inversion Hok. inversion H. inversion H4.
        admit.
      + iPureIntro. unfold is_copy_operation. repeat eexists. admit.
    - iIntros (lv) "(Hcopy & %fr' & Hfr & <-)".
      unfold lp_wand', denote_logpred.
      cbn.
      iSplitL "Hcopy".
      + destruct lv; cbn; try iDestruct "Hcopy" as "[]".
        * iDestruct "Hcopy" as "[? (%vs1 & %vs2 & %Hl & Hvs1 & Hvs2)]".
          iFrame.
          iExists [vs1; vs2].
          cbn.
          rewrite app_nil_r.
          by iFrame.
        * iDestruct "Hcopy" as "[? []]".
      + by iFrame.
  Admitted.

  Lemma compat_drop M F L wl wl' τ es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [τ] [] in
    has_dropability F τ ExDrop ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (IDrop ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_num M F L wl wl' ψ e es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    has_instruction_type_num e ψ ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (INum ψ e)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_num_const M F L wl wl' n ν κ es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [] [NumT κ ν] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (INumConst ψ n)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_block M F L L' wl wl' τs1 τs2 es es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let F' := F <| fc_labels ::= cons (τs2, L') |> in
    let ψ := InstrT τs1 τs2 in
    has_instruction_type_ok F ψ L' ->
    (forall wl wl' es',
        let fe' := fe_of_context F' in
        run_codegen (compile_instrs me fe' es) wl = inr ((), wl', es') ->
        ⊢ have_instruction_type_sem sr mr M F' L wl' (to_e_list es') ψ L') ->
    run_codegen (compile_instr me fe (IBlock ψ L' es)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_loop M F L wl wl' es es' τs1 τs2 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let F' := F <| fc_labels ::= cons (τs1, L) |> in
    let ψ := InstrT τs1 τs2 in
    has_instruction_type_ok F ψ L ->
    (forall wl wl' es',
        let fe' := fe_of_context F' in
        run_codegen (compile_instrs me fe' es) wl = inr ((), wl', es') ->
        ⊢ have_instruction_type_sem sr mr M F' L wl' (to_e_list es') ψ L) ->
    run_codegen (compile_instr me fe (ILoop ψ es)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Fixpoint replace_base {n} (vh: valid_holed n) vs :=
    match vh with
    | VH_base n _ es => VH_base n vs es
    | VH_rec n b c d vh e => VH_rec b c d (replace_base vh vs) e
    end. 

(*  Lemma lfilled_replace_base {n} vh vs1 vs2 :=
    get_base vh = vs1 ++ vs2 ->
    lfilled  *)
  
  Lemma compat_ite M F L L' wl wl' es1 es2 es' τs1 τs2 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT (τs1 ++ [type_i32]) τs2 in
    has_instruction_type_ok F ψ L' ->
    (forall wl wl' es',
        run_codegen (compile_instrs me fe es1) wl = inr ((), wl', es') ->
        ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') (InstrT τs1 τs2) L') ->
    (forall wl wl' es',
        run_codegen (compile_instrs me fe es2) wl = inr ((), wl', es') ->
        ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') (InstrT τs1 τs2) L') ->
    run_codegen (compile_instr me fe (IIte ψ L' es1 es2)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L'.
  Proof.
    intros me fe ψ Hok Hthen Helse Hcodegen.
    iIntros (smem srep ssize se inst lh) "Hsubst Hinst Hctxt".
    iIntros (fr vs) "Hvss Hvsl Hfr Hrun".
    iDestruct "Hvss" as (vss) "(-> & Hvss)".
    iDestruct "Hvsl" as (vsl vswl) "(-> & Hvss0 & %Hrestype & Htok)".
    iDestruct "Hvss0" as (vss0) "[-> Hvss0]".
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
    destruct Hκ as (vs & Heq & Hrepr).
    inversion Heq; subst o; clear Heq.

(*    destruct vswl; last by inversion Hrestype. *)
    rewrite /representation_interp0 /= in Hrepr.
    destruct Hrepr as (ιs & Heq & Hvs).
    inversion Heq; subst ιs; clear Heq.
    destruct vs; inversion Hvs; subst.
    destruct vs; last by inversion H4.
    unfold primitive_rep_interp in H2.
    destruct H2 as [n ->].
    clear Hvs H4.

(*    inversion Hok; subst.
    destruct H as [Hτs1 Hτs2].
    apply Forall_app in Hτs1 as [Hτs1 Hi32].
    inversion Hi32; subst.
    inversion H2; subst.
    inversion H; subst.
    inversion H4; subst. *)

    rewrite /= /compile_ite in Hcodegen. 
    inv_cg_bind Hcodegen ρ wl1 es_nil es1' Htype_rep Hcodegen.
    inv_cg_try_option Htype_rep.
    subst.

(*    unfold util.ignore in Hcodegen. *)
    inv_cg_bind Hcodegen ρ' wl2 es_nil' es2' Htype_rep' Hcodegen.
    rewrite /run_codegen /= in Hcodegen.
    inversion Hcodegen; subst wl' es2'; clear Hcodegen.
    rewrite app_nil_r in Hes_app_eq.
    subst es_nil'.
    rewrite app_nil_r app_nil_l.
    unfold if_c in Htype_rep'.
    inv_cg_bind Htype_rep' ρ'' wl3 es_nil'' es3' Hes1 Hcodegen.
    subst es1'.
    destruct ρ''.
    inv_cg_bind Hcodegen ρ'' wl4 es_nil''' es4' Hes2 Hcodegen.
    subst es3'.
    destruct ρ''.
    rewrite /run_codegen /= in Hcodegen.
    inversion Hcodegen.
    subst ρ' wl4 es4'.
    clear Hcodegen.
    apply run_codegen_capture in Hes1 as [Hes1 ->].
    apply run_codegen_capture in Hes2 as [Hes2 ->].

    unfold compile_instrs in Hthen.
    destruct u, u0.
    apply Hthen in Hes1.
    apply Helse in Hes2.

    subst ψ.
    simpl in Heq_some.
    remember (translate_types (fc_type_vars F) (τs1 ++ [type_i32])) as trans1.
    destruct trans1 as [trans1|]; last done.
    remember (translate_types (fc_type_vars F) τs2) as trans2.
    destruct trans2 as [trans2|]; last done.
    simpl in Heq_some.
    inversion Heq_some; subst ρ; clear Heq_some.
    iSimpl.
    unfold lenient_wp.
    rewrite concat_app /=.
    rewrite -v_to_e_cat.
    rewrite cat_app -app_assoc /=.
    iApply wp_wasm_empty_ctx.
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
      { admit. }
      iIntros "!> Hfr Hrun".
      iApply (wp_label_bind with "[-]").
      2:{ iPureIntro. instantiate (5 := []).
          rewrite /lfilled /lfill /= app_nil_r //. }
      iApply (wp_wand with "[-]").
      + simpl in Hes2.
        iApply (Hes2 with "Hsubst Hinst Hctxt [$Hvss1] [$Htok Hvss0] Hfr Hrun"); first done.
        iExists _, _. iSplit; first done. iSplit.
        * iExists _. iSplit; first done. iExact "Hvss0".
        * iSplit; last done. iPureIntro. exact Hrestype. 
      + iIntros (v) "H".
        rewrite /denote_logpred /lp_noframe /=.
        iIntros (LI HLI).
        apply lfilled_Ind_Equivalent in HLI; inversion HLI; subst.
        inversion H8; subst.
        clear HLI H7 H8 H1.
        iSimpl.

        destruct v.
        * iDestruct "H" as "(((%vss & -> & Hvss) & Hrun) & %fr & Hfr & %vsl & %vswl' & -> & (%vss' & -> & Hvss') & %Hrestype' & Htok)".
          edestruct const_list_to_val as [vs Hvs]; first by apply v_to_e_is_const_list.
          iApply (wp_wand with "[Hfr Hrun]").
          { iApply (wp_label_value with "Hfr Hrun").
            - rewrite seq.cats0. exact Hvs.
            - by instantiate (1 := λ v, ⌜ v = immV vs ⌝%I). }
          iIntros (v) "[[-> Hrun] Hfr]".
          iFrame.
          apply v_to_e_list_to_val in Hvs as Hvs'.
          apply v_to_e_inj in Hvs' as ->.
          iSplit; first done.
          iExists _,_. iSplit; first done.
          iFrame. iSplit => //.
        * iDestruct "H" as "([Hbail _] & %fr & Hfr & %vsl & %vswl' & -> & (%vss & -> & Hvss) & %Hrestype' & Htok)".
          iApply (wp_wand with "[Hfr]").
          { iApply (wp_label_trap with "Hfr") => //.
            instantiate (1 := λ v, ⌜ v = trapV ⌝%I) => //. }
          iIntros (v) "[-> Hfr]".
          iFrame.
          iExists _, _. iSplit; first done.
          iFrame. iSplit => //.
        * iDestruct "H" as "(Hbr & %fr & Hfr & %vsl & %vswl' & -> & (%vss & -> & Hvss) & %Hrestype' & Htok)".
          iDestruct (br_interp_eq with "Hbr") as "Hbr".
          unfold br_interp0. iSimpl in "Hbr".
          iDestruct "Hbr" as (j k p lh' lh'' _ τs es0 es es' vs0 vs) "(%Hgetbase & %Hdepth & %Hlabels & %Hlayer & %Hdepth' & %Hminus & (%vss2 & -> & Hvss2) & Hbr)".
          (* may need to first progress in wp before yielding frame *)
          iDestruct ("Hbr" with "Hfr [Hvss Hvss2 $Htok]") as "Hbr".
          { iExists _,_. iSplit; first done. iFrame. done. } 
          unfold lenient_wp.
          iDestruct wp_value_fupd as "[H _]"; 
            last iMod ("H" with "Hbr") as "Hbr".
          { unfold IntoVal. apply of_to_val.
            unfold language.to_val. simpl. 
            rewrite (separate1 (AI_basic _)).
            apply to_val_br_eq. }
          iClear "H".
          unfold denote_logpred.
          iSimpl in "Hbr".
          iDestruct "Hbr" as "(Hbr & %fr & Hfr & %vsl & %vswl'' & -> & (%vss3 & -> & Hvss3) & Hrestype' & Htok)".
          
          remember (i - p) as hop.
          destruct hop.
          -- (* targetting this exact block *)
            assert (i = p) as ->.
            { admit. } 
            iApply (wp_br with "Hfr").
            3:{ rewrite seq.cats0 /=. 
                instantiate (1 := p).
                instantiate (1 := v_to_e_list (concat vss2)).
                instantiate (1 := lh_of_vh (replace_base lh0 vs0)).
                admit. (* auxiliary lemma *) } 
            ++ apply v_to_e_is_const_list.
            ++ admit. (* use sepL2 and Heqtrans2 *) 
            ++ admit. (* fix def of br_interp *) 
            ++ iIntros "!> Hf Hrun".
               edestruct const_list_to_val as [vs Hvs]; first by apply v_to_e_is_const_list. 
               iApply wp_value.
               { apply of_to_val. rewrite app_nil_r. exact Hvs. }
               iSimpl. iFrame.
               iSplitL "Hbr".
               ** apply v_to_e_list_to_val in Hvs as Hvs'.
                  apply v_to_e_inj in Hvs' as ->.
                  iExists _. iSplit; first done.
                  admit. 
               ** iExists _, _. iSplit; first done. iFrame. done.
          -- (* still blocked *)
            assert (i > p) as Hip; first lia.
            destruct i; first lia.
            destruct (vh_decrease lh0) eqn:Hlh0.
            2:{ admit. (* Hip and Hlh0 should be contradictory *) }
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
            iSimpl. iFrame.
            iSplitL "Hbr".
            ++ admit.
            ++ iExists _,_. iSplit; first done.
               iFrame.  done. 
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
          iDestruct "H" as "((%ts0 & %ts & %vs & %Htrans & %Hbase & (%vss & -> & Hvss) & Hret) & %fr & Hfr & %vsl & %vswl' & -> & (%vss' & -> & Hvss') & %Hrestype' & Htok)".
          iSplitL "Hvss Hret".
          -- iExists _,_,_. iSplit; first done. iSplit; first done. iFrame.
             iSplit; first done.
             iIntros (fr fr') "Hf".
             admit.
          -- iFrame. iExists _,_.
             iSplit; first done. iFrame. done.
        * iDestruct "H" as "[? _]"; done.
    - (* n is true *)
      admit. 
  Admitted. 


  Lemma compat_br M F L L' wl wl' es' i τs1 τs τs2 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT (τs1 ++ τs) τs2 in
    F.(fc_labels) !! i = Some (τs, L) ->
    Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr me fe (IBr ψ i)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_return M F L L' wl wl' es' τs1 τs τs2 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT (τs1 ++ τs) τs2 in
    F.(fc_return) = τs ->
    Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr me fe (IReturn ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_local_get M F L wl wl' es' i τ ιs :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [] [τ] in
    let ρ := ProdR (map PrimR ιs) in
    let τ' := RepT (VALTYPE ρ ImCopy ImDrop) ρ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []) in
    let L' := <[ i := τ']> L in
    F.(typing.fc_locals) !! i = Some ιs ->
    L !! i = Some τ ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr me fe (ILocalGet ψ i)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_local_get_copy M F L wl wl' es' i τ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [] [τ] in
    L !! i = Some τ ->
    has_copyability F τ ImCopy ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (ILocalGet ψ i)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_local_set M F L wl wl' es' i τ τ' ιs :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [τ'] [] in
    let L' := <[ i := τ']> L in
    L !! i = Some τ ->
    has_dropability F τ ImDrop ->
    F.(typing.fc_locals) !! i = Some ιs ->
    type_rep_eval F τ' ιs ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr me fe (ILocalSet ψ i)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_global_get M F L wl wl' es' i ω τ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [] [τ] in
    M.(mc_globals) !! i = Some (ω, τ) ->
    has_copyability F τ ImCopy ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (IGlobalGet ψ i)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_global_set M F L wl wl' es' i τ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [τ] [] in
    M.(mc_globals) !! i = Some (Mut, τ) ->
    has_dropability F τ ImDrop ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (IGlobalSet ψ i)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_global_swap M F L wl wl' es' i τ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [τ] [τ] in
    M.(mc_globals) !! i = Some (Mut, τ) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (IGlobalSwap ψ i)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_coderef M F L wl wl' es' i ϕ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let τ := CodeRefT (VALTYPE (PrimR I32R) ImCopy ImDrop) ϕ in
    let ψ := InstrT [] [τ] in
    M.(mc_table) !! i = Some ϕ ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (ICodeRef ψ i)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_inst M F L wl wl' es' ix ϕ ϕ' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let κ := VALTYPE (PrimR I32R) ImCopy ImDrop in
    let ψ := InstrT [CodeRefT κ ϕ] [CodeRefT κ ϕ'] in
    function_type_inst F ix ϕ ϕ' ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (IInst ψ ix)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_call M F L wl wl' es' i ixs ϕ τs1 τs2 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT τs1 τs2 in
    M.(mc_functions) !! i = Some ϕ ->
    function_type_insts F ixs ϕ (MonoFunT τs1 τs2) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (ICall ψ i ixs)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_call_indirect M F L wl wl' es' τs1 τs2 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let κ := VALTYPE (PrimR I32R) ImCopy ImDrop in
    let ψ := InstrT (τs1 ++ [CodeRefT κ (MonoFunT τs1 τs2)]) τs2 in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (ICallIndirect ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_inject M F L wl wl' es' i τs τ κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [τ] [SumT κ τs] in
    τs !! i = Some τ ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (IInject ψ i)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_case M F L L' wl wl' es' ess τs τ' κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [SumT κ τs] [τ'] in
    (Forall2
      (fun τ es =>
         forall wl wl' es',
           run_codegen (compile_instrs me fe es) wl = inr ((), wl', es') ->
           ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') (InstrT [τ] [τ']) L')
      τs ess) ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr me fe (ICase ψ L' ess)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_group M F L wl wl' es' τs κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT τs [ProdT κ τs] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (IGroup ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ungroup M F L wl wl' es' τs κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [ProdT κ τs] τs in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (IUngroup ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_fold M F L wl wl' es' τ κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
    let ψ := InstrT [τ0] [RecT κ τ] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (IFold ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_unfold M F L wl wl' es' τ κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
    let ψ := InstrT [RecT κ τ] [τ0] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (IUnfold ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_pack M F L wl wl' es' τ τ' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [τ] [τ'] in
    packed_existential F τ τ' ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (IPack ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_unpack M F F0 L L' L0 L0' wl wl' es es' es0 ψ ψ0 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    unpacked_existential F L es ψ L' F0 L0 es0 ψ0 L0' ->
    has_instruction_type_ok F ψ L' ->
    (forall wl wl' es',
        let fe0 := fe_of_context F0 in
        run_codegen (compile_instrs me fe0 es0) wl = inr ((), wl', es') ->
        ⊢ have_instruction_type_sem sr mr M F0 L0 wl' (to_e_list es') ψ0 L0') ->
    run_codegen (compile_instr me fe (IUnpack ψ L' es)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_wrap M F L wl wl' es' τ0 ρ κ ιs ιs0 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [τ0] [RepT κ ρ τ0] in
    type_rep_eval F τ0 ιs0 ->
    eval_rep ρ = Some ιs ->
    convertible_to ιs0 ιs ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (IWrap ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_unwrap M F L wl wl' es' τ0 ρ κ ιs ιs0 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [RepT κ ρ τ0] [τ0] in
    type_rep_eval F τ0 ιs0 ->
    eval_rep ρ = Some ιs ->
    convertible_to ιs0 ιs ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (IUnwrap ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_tag M F L wl wl' es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [type_i32] [type_i31] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (ITag ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_untag M F L wl wl' es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [type_i31] [type_i32] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (IUntag ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ref_new M F L wl wl' es' τ τ' κ μ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [τ] [RefT κ μ τ'] in
    mono_mem μ ->
    stores_as F τ τ' ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (IRefNew ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ref_load M F L wl wl' es' π pr κ μ τ τval :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [RefT κ μ τ] [RefT κ μ τ; τval] in
    resolves_path τ π None pr ->
    has_copyability F pr.(pr_target) ImCopy ->
    loads_as F pr.(pr_target) τval ->
    Forall (mono_size F) pr.(pr_prefix) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (IRefLoad ψ π)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ref_store M F L wl wl' es' π pr κ μ τ τval :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [RefT κ μ τ; τval] [RefT κ μ τ] in
    resolves_path τ π None pr ->
    has_dropability F pr.(pr_target) ImDrop ->
    stores_as F τval pr.(pr_target) ->
    Forall (mono_size F) pr.(pr_prefix) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (IRefStore ψ π)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ref_mm_store M F L wl wl' es' π pr κ κ' τ τval τmem :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [RefT κ (ConstM MemMM) τ; τval] [RefT κ' (ConstM MemMM) pr.(pr_replaced)] in
    stores_as F τval τmem ->
    resolves_path τ π (Some τmem) pr ->
    has_dropability F pr.(pr_target) ImDrop ->
    type_size_eq F pr.(pr_target) τmem ->
    Forall (mono_size F) pr.(pr_prefix) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (IRefStore ψ π)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ref_swap M F L wl wl' es' π pr κ μ τ τval :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [RefT κ μ τ; τval] [RefT κ μ τ; τval] in
    resolves_path τ π None pr ->
    Forall (mono_size F) pr.(pr_prefix) ->
    loads_as F τval pr.(pr_target) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (IRefSwap ψ π)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ref_mm_swap M F L wl wl' es' π pr κ κ' τ τval τval' τmem :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ :=
      InstrT [RefT κ (ConstM MemMM) τ; τval'] [RefT κ' (ConstM MemMM) pr.(pr_replaced); τval]
    in
    stores_as F τval τmem ->
    resolves_path τ π (Some τmem) pr ->
    Forall (mono_size F) pr.(pr_prefix) ->
    loads_as F pr.(pr_target) τval ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr me fe (IRefSwap ψ π)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L.
  Admitted.

  Lemma compat_nil M F L wl wl' es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    run_codegen (compile_instrs me fe []) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') (InstrT [] []) L.
  Proof.
    intros me fe Hcompile.
    cbn in Hcompile.
    inversion Hcompile.

    unfold have_instruction_type_sem.
    iIntros (? ? ? ? ? ?) "Henv Hinst Hlf".
    iIntros (? ?) "Hvs Hframe Hfr Hrun".
    unfold expr_interp; cbn.

    iApply lenient_wp_val_app'.
    iApply lenient_wp_nil.
    unfold lp_combine, denote_logpred; cbn.
    rewrite seq.cats0.
    iFrame.
  Qed.

  Lemma compat_cons M F L1 L2 L3 wl wl' es' e es τs1 τs2 τs3 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    (forall wl wl' es',
        run_codegen (compile_instr me fe e) wl = inr ((), wl', es') ->
        ⊢ have_instruction_type_sem sr mr M F L1 wl' (to_e_list es') (InstrT τs1 τs2) L2) ->
    (forall wl wl' es',
        run_codegen (compile_instrs me fe es) wl = inr ((), wl', es') ->
        ⊢ have_instruction_type_sem sr mr M F L2 wl' (to_e_list es') (InstrT τs2 τs3) L3) ->
    run_codegen (compile_instrs me fe (e :: es)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L1 wl' (to_e_list es') (InstrT τs1 τs3) L3.
  Admitted.

  Lemma compat_frame M F L L' wl wl' es es' τ τs1 τs2 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    has_mono_rep F τ ->
    (forall wl wl' es',
        run_codegen (compile_instrs me fe es) wl = inr ((), wl', es') ->
        ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') (InstrT τs1 τs2) L') ->
    run_codegen (compile_instrs me fe es) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') (InstrT (τ :: τs1) (τ :: τs2)) L'.
  Admitted.

  Theorem fundamental_theorem M F L L' wl wl' es es' tf :
    have_instruction_type M F L es tf L' ->
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    run_codegen (compile_instrs me fe es) wl = inr (tt, wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') tf L'.
  Proof.
    intros Htype.
    generalize dependent es'.
    generalize dependent wl'.
    generalize dependent wl.
    induction Htype using have_instruction_type_mind with
      (P1 := fun M F L e ψ L' =>
               forall wl wl' es',
                 let me := me_of_context M mr in
                 let fe := fe_of_context F in
                 run_codegen (compile_instr me fe e) wl = inr (tt, wl', es') ->
                 ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') ψ L');
      intros wl wl' es' me fe Hcomp.
    - eapply compat_nop; eassumption.
    - eapply compat_unreachable; eassumption.
    - eapply compat_copy; eassumption.
    - eapply compat_drop; eassumption.
    - eapply compat_num; eassumption.
    - eapply compat_num_const; eassumption.
    - eapply compat_block; eassumption.
    - eapply compat_loop; eassumption.
    - eapply compat_ite with (es1 := es1); eassumption.
    - eapply compat_br; eassumption.
    - eapply compat_return; eassumption.
    - eapply compat_local_get; eassumption.
    - eapply compat_local_get_copy; eassumption.
    - eapply compat_local_set; eassumption.
    - eapply compat_global_get; eassumption.
    - eapply compat_global_set; eassumption.
    - eapply compat_global_swap; eassumption.
    - eapply compat_coderef; eassumption.
    - eapply compat_inst; eassumption.
    - eapply compat_call; eassumption.
    - eapply compat_call_indirect; eassumption.
    - eapply compat_inject; eassumption.
    - eapply compat_case; eassumption.
    - eapply compat_group; eassumption.
    - eapply compat_ungroup; eassumption.
    - eapply compat_fold; eassumption.
    - eapply compat_unfold; eassumption.
    - eapply compat_pack; eassumption.
    - eapply compat_unpack; eassumption.
    - eapply compat_wrap; eassumption.
    - eapply compat_unwrap; eassumption.
    - eapply compat_tag; eassumption.
    - eapply compat_untag; eassumption.
    - eapply compat_ref_new; eassumption.
    - eapply compat_ref_load; eassumption.
    - eapply compat_ref_store; eassumption.
    - eapply compat_ref_mm_store; eassumption.
    - eapply compat_ref_swap; eassumption.
    - eapply compat_ref_mm_swap with (τmem := τmem); eassumption.
    - eapply compat_nil; eassumption.
    - eapply compat_cons; eassumption.
    - eapply compat_frame; eassumption.
  Qed.

End Fundamental.
