Require Import RecordUpdate.RecordUpdate.
From stdpp Require Import base list.

From iris.proofmode Require Import base proofmode classes.

From RichWasm.named_props Require Import named_props custom_syntax.
From RichWasm.wasm Require Import operations.
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

  Lemma compat_binary_case M F L L' wt wt' wtf wl wl' wlf es' ess es1 es2 τs τ1 τ2 τs' κ :
    ess = [es1; es2] ->
    τs = [τ1; τ2] ->
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let F' := F <| fc_labels ::= cons (τs', L') |> in
    let ψ := InstrT [SumT κ τs] τs' in
    Forall2
      (fun τ es =>
         (forall wt wt' wtf wl wl' wlf es',
            let fe' := fe_of_context F' in
            let WT := wt ++ wt' ++ wtf in
            let WL := wl ++ wl' ++ wlf in
            run_codegen (compile_instrs mr fe' es) wt wl = inr ((), wt', wl', es') ->
            ⊢ have_instr_type_sem rti sr mr M F' L WT WL es' (InstrT [τ] τs') L'))
      τs ess ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ICase ψ L' ess)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL es' ψ L'.
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


    inv_cg_bind Hcg wl_ret ?wt ?wt ?wl ?wl ?es ?es Hres_type Hcg.
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

    (* Put default result values on stack *)
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_create_defaults ?es Hcreate_defaults Hcg.

    (* Case blocks *)
    cbv [map length seq zip Datatypes.uncurry] in Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcases Hunreachable.

    clear_nils.

    inv_cg_bind Hcases ?units ?wt ?wt ?wl ?wl ?es es_case1 Hcases Hret.
    inv_cg_ret Hret; subst.

    (* Case es1 *)
    inv_cg_bind Hcases [] ?wt ?wt ?wl ?wl ?es es_case2 Hcase_es1 Hcase_es2.

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

    inv_cg_bind Hcase_es1 [] ?wt ?wt ?wl ?wl es_drop_1 ?es Hdrop_consts_1 Hcase_es1.

    inv_cg_bind Hcase_es1 ρ_case1 ?wt ?wt ?wl ?wl ?es ?es Hlookup Hcase_es1.
    inv_cg_try_option Hlookup; subst.

    inv_cg_bind Hcase_es1 case_1_sum_locals ?wt ?wt ?wl ?wl ?es ?es Hinject Hcase_es1.
    inv_cg_try_option Hinject; subst.

    inv_cg_bind Hcase_es1 [] ?wt wt_case_1 ?wl wl_case_1 ?es es_case_1 Hget_locals_1 Hcase_es1.
    inv_cg_bind Hget_locals_1 case_1_val_idxs ?wt wt_get_locals_1 ?wl wl_get_locals_1 ?es es_get_locals_1 Hnths_error Hget_locals_1.
    inv_cg_try_option Hnths_error; subst.

    destruct (run_codegen_get_locals _ _ _ _ _ _ _ Hget_locals_1) as ([] & -> & ->).

    clear_nils.


    (* Case es2 *)
    inv_cg_bind Hcase_es2 ?units ?wt ?wt ?wl ?wl ?es ?es Hcase_es2 Hmret.
    inv_cg_ret Hmret; subst.
    inv_cg_bind Hcase_es2 [] ?wt ?wt ?wl ?wl ?es ?es Hcase_es2 Hmret.
    inv_cg_ret Hmret; subst.

    inv_cg_bind Hcase_es2 ?pair ?wt ?wt ?wl ?wl ?es ?es Hcase_es2 Hcase_es2_block.
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

    inv_cg_bind Hcase_es2 [] ?wt ?wt ?wl ?wl es_drop_2 ?es Hdrop_consts_2 Hcase_es2.

    inv_cg_bind Hcase_es2 ρ_case2 ?wt ?wt ?wl ?wl ?es ?es Hlookup Hcase_es2.
    inv_cg_try_option Hlookup; subst.

    inv_cg_bind Hcase_es2 case_2_sum_locals ?wt ?wt ?wl ?wl ?es ?es Hinject Hcase_es2.
    inv_cg_try_option Hinject; subst.

    inv_cg_bind Hcase_es2 [] ?wt wt_case_2 ?wl wl_case_2 ?es es_case_2 Hget_locals_2 Hcase_es2.
    inv_cg_bind Hget_locals_2 case_2_val_idxs ?wt wt_get_locals_2 ?wl wl_get_locals_2 ?es es_get_locals_2 Hnths_error Hget_locals_2.
    inv_cg_try_option Hnths_error; subst.

    destruct (run_codegen_get_locals _ _ _ _ _ _ _ Hget_locals_2) as ([] & -> & ->).

    clear_nils.

    (* Unreachable *)
    inv_cg_bind Hunreachable ?pair ?wt ?wt ?wl ?wl ?es ?es Hunreachable Hunreachable_block.
    destruct pair, u.
    inv_cg_emit Hunreachable_block; subst.
    apply run_codegen_capture in Hunreachable as [Hunreachable ->].

    inv_cg_bind Hunreachable [] ?wt ?wt ?wl ?wl ?es ?es Hget_tag Hunreachable.
    inv_cg_emit Hget_tag; subst.

    inv_cg_bind Hunreachable [] ?wt ?wt ?wl ?wl ?es ?es Htag0 Hunreachable.
    inv_cg_emit Htag0; subst.

    inv_cg_bind Hunreachable [] ?wt ?wt ?wl ?wl ?es ?es Hcompare_tag Hunreachable.
    inv_cg_emit Hcompare_tag; subst.

    inv_cg_bind Hunreachable [] ?wt ?wt ?wl ?wl ?es ?es Hbr_case Hunreachable.
    inv_cg_emit Hbr_case; subst.
    inv_cg_emit Hunreachable; subst.


    (* clean up *)
    subst WT WL.
    clear_nils.
    simplify_eq.

    (* Iris Proof *)
    iIntros (? ? ? ? ? ? ? ? ?) "%Hsem %Hhas_values #Hinst Hctx Hreturn Hrvs Hvs Hframe Hrt Hfr Hrun".
    iDestruct (Hes1 _ _ (wt_case_2 ++ wtf) _ _ (wl_case_2 ++ wlf) _ Hcase_es1) as "Hsem_es1".
    iDestruct (Hes2 _ _ wtf _ _ wlf _ Hcase_es2) as "Hsem_es2".

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
    iDestruct (relations_cwp.atoms_interp_cons with "Hrvs") as "[-> Hatoms_interp_payload]".

    iPoseProof (frame_interp_wl_interp with "Hframe") as "%Hwl"; first done.
    rewrite list_extra.cons_app in Hhas_values.
    apply has_values_app_inv in Hhas_values as (e_tag & es_payload & -> & Hhv_tag & Hhvs_payload).

    rewrite (app_assoc (e_tag ++ _)).
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      rewrite <- (app_assoc e_tag).
      instantiate (1 := λ f vs, (
        ⌜vs = [VAL_int32 (Wasm_int.Int32.repr i)]⌝ ∗
        ⌜∀ i, i ∉ val_idxs -> f_locs f !! localimm i = f_locs fr !! localimm i⌝ ∗
        ⌜Forall2 (fun i v => f_locs f !! localimm i = Some v) val_idxs vs_payload⌝
        )%I).
      iApply cwp_val_app; first done.
      eapply cwp_save_stack_w in Hsave; eauto.
      + destruct Hsave as (-> & -> & -> & Hsave).
        iApply (Hsave with "[$] [$]").
        iIntros (f' [Hfsame Hfchanged]).
        unfold fvs_combine.
        done.
      + admit. (* easy pure conseqeunce of value_interp and
      rep_values_interp, should be proved above the first wp_seq
      rule *)
    }
    iIntros (fr_saved w) "(-> & %Hsame & %Hsaved) Hfr Hrun".

    edestruct (util.nths_error_exists val_idxs case_1_val_idxs vs_payload case_1_sum_locals (Forall2_length _ _ _ Hsaved)) as [case_1_vs_payload Hnerr_payload_c1]; try done.

    edestruct (util.nths_error_exists val_idxs case_2_val_idxs vs_payload case_2_sum_locals (Forall2_length _ _ _ Hsaved)) as [case_2_vs_payload Hnerr_payload_c2]; try done.

    (* Store tag *)
    rewrite (app_assoc (map _ _)).
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      instantiate (1 := λ f vs, (
        ⌜vs = []⌝ ∗
        ⌜∀ j, j ≠ (fe_wlocal_offset fe + length (wl ++ wl_save))%nat -> f_locs f !! j = f_locs fr_saved !! j⌝ ∗
        ⌜f_locs f !! (fe_wlocal_offset fe + length (wl ++ wl_save))%nat = Some (VAL_int32 (Wasm_int.Int32.repr i))⌝
        )%I).
      iApply (cwp_local_set with "[] [$] [$]").
      1: admit. (* localimm tag_idx < length (f_locs fr_saved) *)
      iSplit; first done.
      iSplit.
      - iIntros "!> %j".
        iPureIntro.
        intros Hneq.
        simpl.
        rewrite list_lookup_insert_ne; [reflexivity | lia].
      - iSimpl.
        iPureIntro.
        rewrite list_lookup_insert; try done.
        admit. (* fe_wlocal_offset fe + length (wl ++ wl_save) < length (f_locs fr_saved) *)
        (* Basically same as above *)
    }
    iIntros (fr_saved_and_tag w) "(-> & %Hsame' & %Hsaved_and_tag) Hfr Hrun".
    clear_nils.

    (* (* -------- Case 1 -------- *) *)
    (* iApply (cwp_seq with "[-]"). *)
    (* { *)
    (*   rewrite <- (app_nil_l [prelude.W.BI_block _ _]). *)
    (*   iApply (cwp_block with "[$] [$]"); auto. *)
    (*   iIntros "!> Hf Hrun". *)
    (*   rewrite app_nil_l. *)
    (*   iSimpl. *)
    (**)
    (*   (* Get tag from local *) *)
    (*   rewrite (separate1 (prelude.W.BI_get_local _)). *)
    (*   iApply (cwp_seq with "[Hf Hrun]"). *)
    (*   { *)
    (*     iApply (cwp_local_get with "[] [$] [$]"); first apply Hsaved_and_tag. *)
    (*     by instantiate (1 := λ f v, (⌜v = [_]⌝ ∗ ⌜f = fr_saved_and_tag⌝)%I). *)
    (*   } *)
    (*   iIntros (?fr w) "(-> & ->) Hf Hrun". *)
    (*   iSimpl. *)
    (**)
    (*   (* compare tag with case number: 0 *) *)
    (*   rewrite separate3. *)
    (*   iApply (cwp_seq with "[Hf Hrun]"). *)
    (*   { *)
    (*     iApply (cwp_relop with "[$] [$]"); first done. *)
    (*     iSimpl. *)
    (*     by instantiate (1 := λ f v, (⌜v = [_]⌝ ∗ ⌜f = fr_saved_and_tag⌝)%I). *)
    (*   } *)
    (*   iIntros (?fr w) "(-> & ->) Hf Hrun". *)
    (*   iSimpl. *)
    (**)
    (*   (* Case analysis: Is tag 0? *) *)
    (*   destruct (Datatypes.negb _); cbn [wasm_bool]; last first. *)
    (**)
    (*   - (* Case: Tag is 0 *) *)
    (*     rewrite separate2. *)
    (*     iApply (cwp_seq with "[Hf Hrun]"). *)
    (*     { *)
    (*       iApply (cwp_br_if_zero with "[$] [$]"); first done. *)
    (*       by instantiate (1 := λ f v, (⌜v = []⌝ ∗ ⌜f = fr_saved_and_tag⌝)%I). *)
    (*     } *)
    (*     iIntros (?fr w) "(-> & ->) Hf Hrun". *)
    (*     iSimpl. *)
    (**)
    (*     (* get locals corresponding to payload of sum *) *)
    (*     eapply cwp_restore_stack_w in Hget_locals_1; eauto using Forall2_length. *)
    (*     2 : { *)
    (*       instantiate (1 := case_1_vs_payload). *)
    (*       pose proof (util.nths_error_length _ _ _ Heq_some3) as Hlen_c1vi. *)
    (*       pose proof (util.nths_error_length _ _ _ Hnerr_payload_c1) as Hlen_c1vp. *)
    (*       by rewrite <- Hlen_c1vi. *)
    (*     } *)
    (*     destruct Hget_locals_1 as (_ & _ & _ & Hget_locals_1). *)
    (*     iDestruct (Hget_locals_1 with "[$] [$] []") as "Hget_locals_1"; clear Hget_locals_1. *)
    (*     { *)
    (*       iPureIntro. *)
    (*       pose proof (util.nths_error_Forall2 _ val_idxs case_1_val_idxs vs_payload case_1_vs_payload case_1_sum_locals Hsaved Heq_some3 Hnerr_payload_c1) as Hf_case_1. *)
    (*       admit. *)
    (*       (* TODO: should be provable, but will probably be a bit annoying *) *)
    (*     } *)
    (**)
    (*     iApply (cwp_seq with "[Hget_locals_1]"). *)
    (*     1: iApply "Hget_locals_1". *)
    (*     iIntros (?fr w) "(-> & ->) Hf Hrun". *)
    (**)
    (*     (* Reason about case 1 code *) *)
    (*     rewrite (app_assoc (map _ _)). *)
    (*     iApply (cwp_seq with "[-]"). *)
    (*     { *)
    (*       iApply ("Hsem_es1" with "[//] [] [$] [Hctx] [] [] [] [] [$] [$] [$]"). *)
    (*       - instantiate (1 := case_1_vs_payload); iPureIntro; simpl; rewrite has_values_iff_to_consts; done. *)
    (*       - subst F'. *)
    (*         replace (fc_labels (F <| fc_labels ::= cons ([τ_res], L') |>)) with *)
    (*                 (([τ_res], L') :: fc_labels F); last done. *)
    (*                 erewrite <- length_nil. *)
    (*         iApply labels_interp_cons; try done. *)
    (*         + admit. *)
    (*         + iIntros "!>" (fr' vs') "(Hframe & %os & %Θ & Hvalues & Hatoms & Hrt)". *)
    (*           by instantiate (1 := λ f v, True%I). *)
    (*       - admit. *)
    (*       - admit. *)
    (*       - admit. *)
    (*       - admit. *)
    (*       - admit. *)
    (*     } *)
    (*     iIntros (fr_case1 vs) "(Hframe_interp & %os' & %θ' & Hvalues & Hatoms & Hrt) Hf Hrun". *)
    (**)
    (*     (* Reason about saving result *) *)
    (*     admit. *)
    (**)
    (*   - (* Case: Tag is not 0 *) *)
    (*     rewrite (separate2). *)
    (*     iApply (cwp_seq with "[Hf Hrun]"). *)
    (*     { *)
    (*       rewrite <- (app_nil_l [_; _]). *)
    (*       iApply (cwp_br_if_nonzero with "[$] [$]"). *)
    (*       1, 3, 4: done. *)
    (*       { by instantiate (1 := []). } *)
    (*       by instantiate (1 := λ f v, (⌜v = []⌝ ∗ ⌜f = fr_saved_and_tag⌝)%I). *)
    (*     } *)
    (*     iIntros (?fr w) "[]". *)
    (* } *)
    (* admit. *)
  Admitted.

  Lemma compat_case M F L L' wt wt' wtf wl wl' wlf es' ess τs τs' κ :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let F' := F <| fc_labels ::= cons (τs', L') |> in
    let ψ := InstrT [SumT κ τs] τs' in
    Forall2
      (fun τ es =>
         (forall wt wt' wtf wl wl' wlf es',
            let fe' := fe_of_context F' in
            let WT := wt ++ wt' ++ wtf in
            let WL := wl ++ wl' ++ wlf in
            run_codegen (compile_instrs mr fe' es) wt wl = inr ((), wt', wl', es') ->
            ⊢ have_instr_type_sem rti sr mr M F' L WT WL es' (InstrT [τ] τs') L'))
      τs ess ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ICase ψ L' ess)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL es' ψ L'.
  Admitted.

End Fundamental.
