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

  Lemma compat_binary_case M F L L' n_skip wt wt' wtf wl wl' wlf es' ess es1 es2 τs τ1 τ2 τs' κ :
    ess = [es1; es2] ->
    τs = [τ1; τ2] ->
    let fe := fe_of_context F <| fe_br_skip := n_skip |> in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let F' := F <| fc_labels ::= cons (τs', L') |> in
    let ψ := InstrT [SumT κ τs] τs' in
    Forall2
      (fun τ es =>
         (forall m_skip wt wt' wtf wl wl' wlf es',
            let fe' := fe_of_context F' <| fe_br_skip := m_skip |> in
            let WT := wt ++ wt' ++ wtf in
            let WL := wl ++ wl' ++ wlf in
            run_codegen (compile_instrs mr fe' es) wt wl = inr ((), wt', wl', es') ->
            ⊢ have_instruction_type_sem rti sr mr M F' L WT WL (to_e_list es') (InstrT [τ] τs') L'))
      τs ess ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ICase ψ L' ess)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L'.
  Proof.
    intros -> -> fe WT WL F' Ψ Hforall Hok Hcg.
    rewrite Forall2_cons_iff in Hforall.
    destruct Hforall as [Hes1 H2].
    rewrite Forall2_cons_iff in H2.
    destruct H2 as [Hes2 _].
    subst Ψ.
    cbn [compile_instr] in Hcg.
    destruct κ as [ ρ c d | ]; last inversion Hcg.
    destruct ρ  as [ | ρs_sum | | ]; try done.
    destruct τs' as [ | τ_res τs' ]; first done.
    destruct τs'; last done.


    inv_cg_bind Hcg wt_ret ?wt ?wt ?wl ?wl ?es ?es Hres_type Hcg.
    inv_cg_try_option Hres_type; subst.
    inv_cg_bind Hcg ρs_atom ?wt ?wt ?wl ?wl ?es ?es Hιs Hcg.
    inv_cg_try_option Hιs; subst.
    inv_cg_bind Hcg val_idxs wt_save ?wt wl_save ?wl es_save ?es Hsave Hcg.
    repeat rewrite app_nil_r in Hsave.

    (* Save tag *)
    inv_cg_bind Hcg tag_idx ?wt ?wt ?wl ?wl ?es ?es HsaveTag Hcg.
    unfold save_stack1 in HsaveTag.
    inv_cg_bind HsaveTag tag_idx' ?wt ?wt ?wl ?wl ?es ?es Halloc_tag HsaveTag.
    apply wp_wlalloc in Halloc_tag as [Hlocal_tag_idx [-> [-> ->]]].
    inv_cg_bind HsaveTag [] ?wt ?wt ?wl ?wl es_set_tag ?es HsetTag HretTagIdx.
    inv_cg_emit HsetTag; subst.
    inv_cg_ret HretTagIdx; subst.

    clear_nils.
    set (tag_idx := (Mk_localidx (fe_wlocal_offset fe + length (wl ++ wl_save)))).
    replace (Mk_localidx (fe_wlocal_offset fe + length (wl ++ wl_save))) with tag_idx in *; last done.

    (* Case blocks *)
    inv_cg_bind Hcg pair ?wt ?wt ?wl ?wl ?es es_done_bl Hcases HdoneBlock.
    destruct pair, u.
    inv_cg_emit HdoneBlock; subst.

    apply run_codegen_capture in Hcases as [Hcases ->].
    cbv [map length seq zip Datatypes.uncurry] in Hcases.

    clear_nils.

    inv_cg_bind Hcases [] ?wt ?wt ?wl ?wl ?es es_unr Hcases Hunreachable.
    inv_cg_emit Hunreachable; subst.

    inv_cg_bind Hcases ?units ?wt ?wt ?wl ?wl ?es es_case1 Hcases Hret.
    inv_cg_ret Hret; subst.


    (* Case es1 *)
    inv_cg_bind Hcases [] ?wt ?wt ?wl ?wl ?es es_case1 Hcase_es1 Hcase_es2.

    inv_cg_bind Hcase_es1 ?pair ?wt ?wt ?wl ?wl ?es ?es Hcase_es1 Hcase_es1_block.
    destruct pair, u.
    inv_cg_emit Hcase_es1_block; subst.
    apply run_codegen_capture in Hcase_es1 as [Hcase_es1 ->].

    inv_cg_bind Hcase_es1 [] ?wt ?wt ?wl ?wl ?es ?es Hget_tag Hcase_es1.
    inv_cg_emit Hget_tag; subst.

    inv_cg_bind Hcase_es1 [] ?wt ?wt ?wl ?wl ?es ?es Htag0 Hcase_es1.
    inv_cg_emit Htag0; subst.

    inv_cg_bind Hcase_es1 [] ?wt ?wt ?wl ?wl ?es ?es Hcompare_tag Hcase_es1.
    inv_cg_emit Hcompare_tag; subst.

    inv_cg_bind Hcase_es1 [] ?wt ?wt ?wl ?wl ?es ?es Hbr_case Hcase_es1.
    inv_cg_emit Hbr_case; subst.

    inv_cg_bind Hcase_es1 [] ?wt ?wt ?wl ?wl ?es ?es Hcase_es1 Hbr_cases.
    inv_cg_emit Hbr_cases; subst.

    inv_cg_bind Hcase_es1 ρ_case1 ?wt ?wt ?wl ?wl ?es ?es Hlookup Hcase_es1.
    inv_cg_try_option Hlookup; subst.

    inv_cg_bind Hcase_es1 case_1_sum_locals ?wt ?wt ?wl ?wl ?es ?es Hinject Hcase_es1.
    inv_cg_try_option Hinject; subst.

    inv_cg_bind Hcase_es1 [] ?wt wt_case_1 ?wl wl_case_1 ?es es_case_1 Hget_locals_1 Hcase_es1.
    inv_cg_bind Hget_locals_1 case_1_val_idxs ?wt wt_get_locals_1 ?wl wl_get_locals_1 ?es es_get_locals_1 Hnths_error Hget_locals_1.
    inv_cg_try_option Hnths_error; subst.

    clear_nils.

    destruct (run_codegen_get_locals _ _ _ _ _ _ _ Hget_locals_1) as [_ [-> ->]].


    (* Case es2 *)

    inv_cg_bind Hcase_es2 ?units ?wt ?wt ?wl ?wl ?es ?es Hcase_es2 Hmret.
    inv_cg_ret Hmret; subst.

    inv_cg_bind Hcase_es2 [] ?wt ?wt ?wl ?wl ?es ?es Hcase_es2 Hmret.
    inv_cg_ret Hmret; subst.

    inv_cg_bind Hcase_es2 pair ?wt ?wt ?wl ?wl ?es ?es Hcase_es2 Hcase_es2_block.
    destruct pair, u.
    inv_cg_emit Hcase_es2_block; subst.
    apply run_codegen_capture in Hcase_es2 as [Hcase_es2 ->].

    inv_cg_bind Hcase_es2 [] ?wt ?wt ?wl ?wl ?es ?es Hget_tag Hcase_es2.
    inv_cg_emit Hget_tag; subst.

    inv_cg_bind Hcase_es2 [] ?wt ?wt ?wl ?wl ?es ?es Htag0 Hcase_es2.
    inv_cg_emit Htag0; subst.

    inv_cg_bind Hcase_es2 [] ?wt ?wt ?wl ?wl ?es ?es Hcompare_tag Hcase_es2.
    inv_cg_emit Hcompare_tag; subst.

    inv_cg_bind Hcase_es2 [] ?wt ?wt ?wl ?wl ?es ?es Hbr_case Hcase_es2.
    inv_cg_emit Hbr_case; subst.

    inv_cg_bind Hcase_es2 [] ?wt ?wt ?wl ?wl ?es ?es Hcase_es2 Hbr_cases.
    inv_cg_emit Hbr_cases; subst.

    inv_cg_bind Hcase_es2 ρ_case2 ?wt ?wt ?wl ?wl ?es ?es Hlookup Hcase_es2.
    inv_cg_try_option Hlookup; subst.

    inv_cg_bind Hcase_es2 case_2_sum_locals ?wt ?wt ?wl ?wl ?es ?es Hinject Hcase_es2.
    inv_cg_try_option Hinject; subst.

    inv_cg_bind Hcase_es2 [] ?wt wt_case_2 ?wl wl_case_2 ?es es_case_2 Hget_locals_2 Hcase_es2.
    inv_cg_bind Hget_locals_2 case_2_val_idxs ?wt wt_get_locals_2 ?wl wl_get_locals_2 ?es es_get_locals_2 Hnths_error Hget_locals_2.
    inv_cg_try_option Hnths_error; subst.

    clear_nils.

    destruct (run_codegen_get_locals _ _ _ _ _ _ _ Hget_locals_2) as [_ [-> ->]].

    (* clean up *)
    subst WT WL.
    clear_nils.
    simplify_eq.

    (* Iris Proof *)
    iIntros (? ? ? ? ? ? ? ?) "#Hinst #Hctx Hrvs Hvs Hframe Hrt Hfr Hrun".
    iDestruct (Hes1 _ _ _ wtf _ _ wlf _ Hcase_es1) as "Hsem_es1".
    iDestruct (Hes2 _ _ _ wtf _ _ wlf _ Hcase_es2) as "Hsem_es2".

    replace (language.of_val (immV vs)) with (v_to_e_list vs); last done.
    unfold expr_interp.

    rewrite to_e_list_app.
    rewrite (app_assoc (v_to_e_list _)).

    (* Our values are in the value interpretation for our specific SumT *)
    (* This means that the values represent the tag and the payload. *)
    iDestruct (values_interp_one_eq with "Hvs") as "Hvs".
    iDestruct (value_interp_eq with "Hvs") as "Hvs".
    unfold value_interp0, value_se_interp0.
    iDestruct "Hvs" as "(%κ & %Hkind_sum & Hskind_as_type & Hsum_interp)".
    (*unfold type_skind in Hkind_sum.*)
    iDestruct "Hsum_interp" as (i os0 os_i τ_i ιs ιs_i ixs  HSAtoms Htype_lookup Htype_arep Heval_rep_tail Hinject_sum_arep Hos0_ixs) "Hvalue_interp_os_i".
    (*assert (os = I32A (Wasm_int.int_of_Z i32m i) :: os0) as ->; first by inversion HSAtoms.*)
    simplify_eq.

    iDestruct (big_sepL2_length with "Hrvs") as "%Hlen".
    destruct vs as [|v_tag vs_payload]; first inversion Hlen.
    clear Hlen.
    iDestruct (atoms_interp_cons with "Hrvs") as "[-> Hatoms_interp_payload]".



    iPoseProof (frame_interp_wl_interp with "Hframe") as "%Hwl"; first done.
    set (Φ := {| lp_fr_inv := λ _, True;
                lp_val := λ f vs',
                    ⌜∀ i, i ∉ val_idxs -> f_locs f !! localimm i = f_locs fr !! localimm i⌝ ∗
                    ⌜Forall2 (fun i v => f_locs f !! localimm i = Some v) val_idxs vs_payload⌝ ∗
                    ⌜vs' = [VAL_int32 (Wasm_int.Int32.repr i)]⌝;
                lp_trap := False;
                lp_br := λ _ _ _, False;
                lp_ret := λ _, False;
                lp_host := λ _ _ _ _, False |}%I : @logpred Σ).
    iApply (lenient_wp_seq with "[Hfr Hrun]").
    {
      iSimpl.
      iApply lenient_wp_val_cons.
      eapply (lwp_save_stack_w _ (lp_combine Φ [VAL_int32 (Wasm_int.Int32.repr i)])) in Hsave; eauto.
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
    subst Φ.
    destruct w; iEval (cbn) in "Hnotrap"; try done;
      try (iDestruct "Hnotrap" as "[? ?]"; done).
    iDestruct "Hnotrap" as "(Hrun & %Hsame & %Hsaved & ->)".
    replace (language.of_val) with (of_val); last done.
    cbn [of_val].
    rewrite v_to_e_list1.

    (* Store tag *)
    lwp_chomp 2.
    iApply (lenient_wp_seq with "[Hfr Hrun]").
    {
      set (Φ := {| lp_fr_inv := λ _, True;
                  lp_val := λ f vs',
                    ⌜∀ j, j ≠ (fe_wlocal_offset fe + length (wl ++ wl_save))%nat -> f_locs f !! j = f_locs fr_saved !! j⌝ ∗
                    ⌜f_locs f !! (fe_wlocal_offset fe + length (wl ++ wl_save))%nat = Some (VAL_int32 (Wasm_int.Int32.repr i))⌝ ∗
                    ⌜vs' = []⌝;
                  lp_trap := False;
                  lp_br := λ _ _ _, False;
                  lp_ret := λ _, False;
                  lp_host := λ _ _ _ _, False |}%I : @logpred Σ).
      iApply (lenient_wp_set_local _ _ _ Φ); last iFrame.
      1: admit. (* fe_wlocal_offset fe + length (wl ++ wl_save) < length (f_locs fr_saved) *)
      unfold lp_val, Φ.
      iSplit.
      - iIntros "!> %j".
        iPureIntro.
        intros Hneq.
        simpl.
        apply util.set_nth_neq; try done.
        admit. (* fe_wlocal_offset fe + length (wl ++ wl_save) < length (f_locs fr_saved) *)
      - iSimpl.
        iSplit; last done.
        iPureIntro.
        apply set_nth_read.
    }
    { by iIntros. }
    iIntros (w fr_saved_and_tag) "Hnotrap Hfr _".
    destruct w; iEval (cbn) in "Hnotrap"; try done;
      try (iDestruct "Hnotrap" as "[? ?]"; done).
    iDestruct "Hnotrap" as "(Hrun & %Hsame' & %Hsaved_and_tag' & ->)".
    clear_nils.

    (* -------- Case blocks -------- *)
    rewrite <- (app_nil_l [AI_basic _]).
    iApply (lenient_wp_block with "[$] [$]"); auto.
    iIntros "!> Hf Hrun".
    rewrite app_nil_l.
    iApply lwp_wasm_empty_ctx.
    iApply lwp_label_push_nil.
    iApply lwp_ctx_bind; first done.
    (* -------- Case 1 -------- *)
    lwp_chomp 1%nat.
    iApply (lenient_wp_seq with "[Hf Hrun]").
    {
      rewrite <- (app_nil_l [AI_basic _]).
      iApply (lenient_wp_block with "[$] [$]"); auto.
      iIntros "!> Hf Hrun".
      rewrite app_nil_l.
      iApply lwp_wasm_empty_ctx.
      iApply lwp_label_push_nil.
      iApply lwp_ctx_bind; first done.
      (* Get tag from local *)
      lwp_chomp 1%nat.
      iApply (lenient_wp_seq with "[Hf Hrun]").
      {
        iApply lenient_wp_get_local; first apply Hsaved_and_tag'.
        iFrame.
        auto_logp.
      }
      { by iIntros (fr') "Htrap". }
      iIntros (w ?fr) "Hnotrap Hf _".
      destruct w; iEval (cbn) in "Hnotrap"; try done;
      try (iDestruct "Hnotrap" as "[? ?]"; done).
      iDestruct "Hnotrap" as "(Hrun & -> & ->)".
      replace (language.of_val) with (of_val); last done.
      iSimpl.

      (* compare tag with case number: 0 *)
      lwp_chomp 3%nat.
      iApply (lenient_wp_seq with "[Hf Hrun]").
      {
        iApply lwp_relop; first done.
        iFrame.
        iSimpl.
        auto_logp.
      }
      { by iIntros. }
      iIntros (w ?fr) "Hnotrap Hf _".
      destruct w; iEval (cbn) in "Hnotrap"; try done;
      try (iDestruct "Hnotrap" as "[? ?]"; done).
      iDestruct "Hnotrap" as "(Hrun & -> & ->)".
      replace (language.of_val) with (of_val); last done.
      iSimpl.

      lwp_chomp 2%nat; rewrite take_0; rewrite drop_0.

      (* Case analysis: Is tag 0? *)
      destruct (Datatypes.negb _); cbn [wasm_bool]; last first.

      - (* Case: Tag it 0 *)
        iApply (lenient_wp_seq with "[Hf Hrun]").
        {
          iApply lenient_wp_br_if_false; first done.
          iFrame.
          auto_logp.
        }
        { by iIntros. }
        iIntros (w ?fr) "Hnotrap Hf _".
        destruct w; iEval (cbn) in "Hnotrap"; try done;
        try (iDestruct "Hnotrap" as "[? ?]"; done).
        iDestruct "Hnotrap" as "(Hrun & -> & ->)".
        replace (language.of_val) with (of_val); last done.
        iSimpl.

        (* get locals corresponding to payload of sum *)
        eapply lwp_restore_stack_w in Hget_locals_1; eauto using Forall2_length.
        2: { admit. }
        instantiate (2 := fr_saved_and_tag) in Hget_locals_1.
        destruct Hget_locals_1 as (_ & _ & _ & Hget_locals_1).
        iDestruct (Hget_locals_1 with "[$] [$] []") as "Hget_locals_1"; clear Hget_locals_1.
        {
          iPureIntro.
          admit.
        }
        admit.

        (* Reason about code for case 1 *)

      - (* Case: Tag is not 0 *)
        iApply (lenient_wp_seq with "[Hf Hrun]").
        {
          iApply lenient_wp_br_if_true; first done.
          iFrame.
          iIntros "!> Hf Hr".
          iApply lenient_wp_value; first by instantiate (1 := brV (VH_base 0 [] [])).
          iFrame.
          auto_logp.
        }
        { by iIntros. }
        iIntros (w ?fr) "Hnotrap Hf _".
        destruct w; iEval (cbn) in "Hnotrap"; try done;
        try (iDestruct "Hnotrap" as "[? ?]"; done).
        iDestruct "Hnotrap" as "(Hrun & %Hfr_vh)".
        destruct Hfr_vh as [-> [-> Hvh]].
        simpl in Hvh; simplify_eq.
        replace (language.of_val) with (of_val); last done.
        iSimpl.
        iApply lwp_wasm_empty_ctx.

          (* iApply (wp_br_ctx with "[$] [$]"). *)
          (* 1: by instantiate (1 := []). *)
          (* 1: done. *)
          (* 2: { *)
          (*   iPureIntro. *)
          (*   instantiate (1 := 0). *)
          (*   instantiate (1 := []). *)
          (*   instantiate (1 := LH_base [] _). *)
          (*   unfold lfilled, lfill => //=. *)
          (* } *)
          admit.
        }
        { admit. }
        admit.

Admitted.

  Lemma compat_case M F L L' n_skip wt wt' wtf wl wl' wlf es' ess τs τs' κ :
    let fe := fe_of_context F <| fe_br_skip := n_skip |> in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let F' := F <| fc_labels ::= cons (τs', L') |> in
    let ψ := InstrT [SumT κ τs] τs' in
    Forall2
      (fun τ es =>
         (forall m_skip wt wt' wtf wl wl' wlf es',
            let fe' := fe_of_context F' <| fe_br_skip := m_skip |> in
            let WT := wt ++ wt' ++ wtf in
            let WL := wl ++ wl' ++ wlf in
            run_codegen (compile_instrs mr fe' es) wt wl = inr ((), wt', wl', es') ->
            ⊢ have_instruction_type_sem rti sr mr M F' L WT WL (to_e_list es') (InstrT [τ] τs') L'))
      τs ess ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ICase ψ L' ess)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L'.
  Admitted.

End Fundamental.
