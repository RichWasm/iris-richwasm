Require Import RecordUpdate.RecordUpdate.
From stdpp Require Import base list.

From iris.proofmode Require Import base proofmode classes.

From RichWasm.named_props Require Import named_props custom_syntax.
From RichWasm.wasm Require Import operations.
From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import prelude codegen instruction module.
From RichWasm.iris Require Import autowp memory util wp_codegen.
From RichWasm.iris.language Require Import cwp logpred.
From RichWasm.iris.logrel Require Import relations fundamental_kinding.

Require Import RichWasm.iris.logrel.compat.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Fundamental.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.


  Lemma compat_case_block_fail F wt wt_save tag_idx (tag i : nat) f wl_others wl_ret es_drop_i es_get_locals_i es_case_i B R L' wl wl_save τ_res val_idxs case_i_val_idxs case_i_sum_locals (vs_res vs_payload case_i_vs_payload : list value) :
    let F' := F <| fc_labels ::= cons ([τ_res], L') |> in
    let fe := fe_of_context F in
    f_locs f !! tag_idx = Some (VAL_int32 (Wasm_int.Int32.repr tag)) ->
    run_codegen (get_locals_w case_i_val_idxs) (wt ++ wt_save)
      (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_others) = inr ((), [], [], es_get_locals_i) ->
    run_codegen (drop_consts wl_ret) (wt ++ wt_save)
      (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_others) = inr ((), [], [], es_drop_i) ->
    util.nths_error val_idxs case_i_sum_locals = Some case_i_val_idxs ->
    util.nths_error vs_payload case_i_sum_locals = Some case_i_vs_payload ->
    prelude.translate_type (fe_type_vars fe) τ_res = Some wl_ret ->
    i ≠ tag ->
    length vs_res = length wl_ret ->
    ⊢
    ↪[frame]f -∗
    ↪[RUN] -∗
      CWP to_consts vs_res ++
        [prelude.W.BI_block (prelude.W.Tf wl_ret wl_ret)
           ([prelude.W.BI_get_local (localimm $ Mk_localidx tag_idx)] ++
            [prelude.W.BI_const
               (prelude.W.VAL_int32 (Wasm_int.int_of_Z i32m i%nat))] ++
            [prelude.W.BI_relop prelude.W.T_i32
               (prelude.W.Relop_i prelude.W.ROI_ne)] ++
            [prelude.W.BI_br_if 0] ++ es_drop_i ++ es_get_locals_i ++ es_case_i)]
        UNDER B; R
        {{ fr'; vs', ⌜fr' = f⌝ ∗ ⌜vs' = vs_res⌝ }}.
  Proof.
    intros F' fe Hlookup_saved_and_tag Hget_locals_i Hdrop_consts_i Hnerr_val_idxs Hnerr_payload_ci Htranslate_type_fe Hneq Hvs_res_length.
    iIntros "Hfr Hrun".

    iApply (cwp_block with "[$] [$]"); auto.
    { apply is_consts_to_consts. }
    { by rewrite length_map. }
    iIntros "!> Hf Hrun".

    iEval (do 3 rewrite app_assoc).
    iApply (cwp_seq with "[Hf Hrun]").
    {
      iEval (do 2 rewrite -app_assoc).
      iApply cwp_val_app; first apply has_values_to_consts.

      (* Get tag from local *)
      rewrite (separate1 (prelude.W.BI_get_local _)).
      iApply (cwp_seq with "[Hf Hrun]").
      {
        iApply (cwp_local_get with "[] [$] [$]"); first apply Hlookup_saved_and_tag.
        by instantiate (1 := λ f' v, (⌜v = [_]⌝ ∗ ⌜f' = f⌝)%I).
      }
      iIntros (?fr w) "(-> & ->) Hf Hrun".
      iSimpl.

      (* compare tag with case number: 0 *)
      rewrite separate3.
      iApply (cwp_seq with "[Hf Hrun]").
      {
        iApply (cwp_relop with "[$] [$]"); first done.
        iSimpl.
        rewrite Wasm_int.Int32.eq_false.
        2: admit. (* TODO: this is not actually provable. We need to know tags aren't huge... Maybe a different approach than destruct i *)
        iSimpl.
        by instantiate (1 := λ f' v, (⌜v = [_]⌝ ∗ ⌜f' = f⌝)%I).
      }
      iIntros (?fr w) "(-> & ->) Hf Hrun".
      iSimpl.
      iApply (cwp_val with "[$] [$]").
      - by instantiate (1 := [(VAL_int32 Wasm_int.Int32.one)]).
      - unfold fvs_combine.
        by instantiate (1 := λ f' v, (⌜v = _ ++ [_]⌝ ∗ ⌜f' = f⌝)%I).
    }
    iIntros (?fr w) "(-> & ->) Hf Hrun".

    iEval (rewrite app_assoc).

    iApply (cwp_seq with "[-]").
    2: {
      instantiate (1 := λ f vs, False%I).
      by iIntros.
    }
    unfold to_consts.
    rewrite map_app.
    rewrite -app_assoc.
    replace (map BI_const [VAL_int32 Wasm_int.Int32.one] ++ [prelude.W.BI_br_if 0])
    with [BI_const (VAL_int32 Wasm_int.Int32.one); prelude.W.BI_br_if 0]; last done.

    iApply (cwp_br_if_nonzero with "[$] [$]"); try done.
    1: apply has_values_to_consts.
    by rewrite length_map.
  Admitted.


  (* TODO: should probably be written using run_codegen somehow *)
  Lemma compat_case_block_success M F L wt wt_save wt_cases wt_others wtf tag_idx (tag i : nat) fr_saved_and_tag wl_ret lmask es_drop_i es_get_locals_i es_case_i B R se L' wl wl_save wl_others wl_cases wlf (τs: list type) τ_i τ_tag τ_res os_payload case_i_os_payload val_idxs case_i_val_idxs case_i_sum_locals (vs_res vs_payload case_i_vs_payload : list value) θ :
    let F' := F <| fc_labels ::= cons ([τ_res], L') |> in
    let fe := fe_of_context F in
    f_locs fr_saved_and_tag !! tag_idx = Some (VAL_int32 (Wasm_int.Int32.repr tag)) ->
    run_codegen (get_locals_w case_i_val_idxs) (wt ++ wt_save ++ wt_others)
    (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_others) = inr ((), [], [], es_get_locals_i) ->
    run_codegen (drop_consts wl_ret) (wt ++ wt_save ++ wt_others)
      (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_others) = inr ((), [], [], es_drop_i) ->
    util.nths_error val_idxs case_i_sum_locals = Some case_i_val_idxs ->
    util.nths_error vs_payload case_i_sum_locals = Some case_i_vs_payload ->
    prelude.translate_type (fe_type_vars fe) τ_res = Some wl_ret ->
    τs !! i = Some τ_i ->
    τs !! tag = Some τ_tag ->
    i = tag ->
    length vs_res = length wl_ret ->
    Forall2
      (λ (i : prelude.W.localidx) (v : value),
         f_locs fr_saved_and_tag !! localimm i = Some v)
       case_i_val_idxs case_i_vs_payload ->
     sem_env_interp F se ->
    ⊢
    have_instr_type_sem rti sr mr M F' L
               (wt ++ wt_save ++ wt_cases ++ wtf)
               (wl ++
                wl_save ++ [prelude.W.T_i32] ++ wl_cases ++ wlf)
               lmask es_case_i (InstrT [τ_i] [τ_res]) L' -∗
    instance_interp rti sr mr M (wt ++ wt_save ++ wt_cases ++ wtf) fr_saved_and_tag.(f_inst) -∗
    labels_interp rti sr se fr_saved_and_tag (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_cases ++ wlf)
      lmask (fc_labels F) B -∗
    return_interp rti sr se (fc_return F) R -∗
    rt_token rti sr θ -∗
    ▷ value_interp rti sr se τ_tag (SAtoms case_i_os_payload) -∗
    atoms_interp os_payload vs_payload -∗
    frame_interp rti sr se L (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_cases ++ wlf)
      fr_saved_and_tag -∗
    ↪[frame]fr_saved_and_tag -∗
    ↪[RUN] -∗
      CWP to_consts vs_res ++
        [prelude.W.BI_block (prelude.W.Tf wl_ret wl_ret)
           ([prelude.W.BI_get_local (localimm $ Mk_localidx tag_idx)] ++
            [prelude.W.BI_const
               (prelude.W.VAL_int32 (Wasm_int.int_of_Z i32m i%nat))] ++
            [prelude.W.BI_relop prelude.W.T_i32
               (prelude.W.Relop_i prelude.W.ROI_ne)] ++
            [prelude.W.BI_br_if 0] ++ es_drop_i ++ es_get_locals_i ++ es_case_i)]
        UNDER B; R
        {{ fr'; vs',
          ( ⌜τ_i = τ_tag⌝ ∗
            ⌜length vs' = length wl_ret⌝ ∗
            frame_interp rti sr se L'
             (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_cases ++ wlf)
             fr' ∗
            ∃ (os' : leibnizO (list atom)) (θ : address_map),
             values_interp rti sr se [τ_res] os' ∗ atoms_interp os' vs' ∗
             rt_token rti sr θ
          )
        }}.
  Proof.
    intros F' fe Hlookup_saved_and_tag Hget_locals_i Hdrop_consts_i Hnerr_val_idxs Hnerr_payload_ci Htranslate_type_fe Ht_lookup_i Ht_lookup_tag Heq Hvs_res_length Hsaved_and_tag Hsem.
    iIntros "Hsem_es_i #Hinst #Hlabels #Hreturn Hrt Hvalue_interp_os_i Hatoms_interp_payload Hframe_saved_and_tag Hfr Hrun".

    iApply (cwp_block with "[$] [$]"); auto.
    { apply is_consts_to_consts. }
    { by rewrite length_map. }
    iIntros "!> Hf Hrun".

    subst i.
    rewrite Ht_lookup_i in Ht_lookup_tag.
    inversion Ht_lookup_tag as [Heq].

    iEval (do 4 rewrite app_assoc).
    iApply (cwp_seq with "[Hf Hrun]").
    {
      iEval (do 3 rewrite -app_assoc).
      iApply cwp_val_app; first apply has_values_to_consts.

      (* Get tag from local *)
      rewrite (separate1 (prelude.W.BI_get_local _)).
      iApply (cwp_seq with "[Hf Hrun]").
      {
        iApply (cwp_local_get with "[] [$] [$]"); first apply Hlookup_saved_and_tag.
        by instantiate (1 := λ f v, (⌜v = [_]⌝ ∗ ⌜f = fr_saved_and_tag⌝)%I).
      }
      iIntros (?fr w) "(-> & ->) Hf Hrun".
      iSimpl.

      (* compare tag with case number: i *)
      rewrite separate3.
      iApply (cwp_seq with "[Hf Hrun]").
      {
        iApply (cwp_relop with "[$] [$]"); first done.
        iSimpl.
        by instantiate (1 := λ f v, (⌜v = [_]⌝ ∗ ⌜f = fr_saved_and_tag⌝)%I).
      }
      iIntros (?fr w) "(-> & ->) Hf Hrun".
      iSimpl.
      iApply (cwp_br_if_zero with "[$] [$]").
      - by rewrite Wasm_int.Int32.eq_true.
      - instantiate (1 := λ f v, (⌜v = vs_res⌝ ∗ ⌜f = fr_saved_and_tag⌝)%I).
        unfold fvs_combine.
        by rewrite app_nil_r.
    }
    iIntros (?fr w) "(-> & ->) Hf Hrun".

    (* drop default values *)
    rewrite (app_assoc (to_consts _)).
    iApply (cwp_seq with "[Hf Hrun]").
    {
      instantiate (1 := λ f vs, (⌜f = fr_saved_and_tag⌝ ∗ ⌜vs = []⌝)%I).
      eapply cwp_drop_consts in Hdrop_consts_i as (_ & _ & _ & Hdrop_consts_i).
      - iDestruct (Hdrop_consts_i with "[$] [$] []") as "Hdrop_consts_i".
        2: iApply "Hdrop_consts_i".
        done.
      - by rewrite length_map.
      - apply is_consts_to_consts.
    }
    iIntros (?fr w) "(-> & ->) Hf Hrun".
    iSimpl.

    (* get locals corresponding to payload of sum *)
    eapply cwp_restore_stack_w in Hget_locals_i; eauto using Forall2_length.
    (* 2 : { *)
    (*   instantiate (1 := case_i_vs_payload). *)
    (*   pose proof (util.nths_error_length _ _ _ Hnerr_val_idxs) as Hlen_civi. *)
    (*   pose proof (util.nths_error_length _ _ _ Hnerr_payload_ci) as Hlen_civp. *)
    (*   by rewrite <- Hlen_civi. *)
    (* } *)
    destruct Hget_locals_i as (_ & _ & _ & Hget_locals_i).
    iDestruct (Hget_locals_i with "[$] [$] []") as "Hget_locals_1"; clear Hget_locals_i; first done.

    iApply (cwp_seq with "[Hget_locals_1]").
    1: iApply "Hget_locals_1".
    iIntros (?fr w) "(-> & ->) Hf Hrun".

    assert (prelude.translate_types (fc_type_vars F) [τ_res] = Some wl_ret) as Htranslate_types_single.
    {
      subst fe.
      unfold fe_of_context, fe_type_vars in Htranslate_type_fe.
      unfold prelude.translate_types.
      simpl.
      rewrite Htranslate_type_fe.
      simpl.
      by rewrite app_nil_r.
    }

    (* Reason about case 1 code *)
    iApply (cwp_wand with "[-]").
    {
      iApply ("Hsem_es_i" with "[//] [] [$] [] [] [Hatoms_interp_payload] [Hvalue_interp_os_i] [Hframe_saved_and_tag] [$] [$] [$]").
      + instantiate (1 := case_i_vs_payload); iPureIntro; simpl; rewrite has_values_iff_to_consts; done.
      + subst F'.
        replace (fc_labels (F <| fc_labels ::= cons ([τ_res], L') |>)) with
            (([τ_res], L') :: fc_labels F); last done.
            iApply labels_interp_cons; try done.
            iIntros "!>" (fr' vs') "(%Hfrel & Hframe & (%os & Hvalues & Hatoms) & [%Θ Hrt])".
            iSplit; first done.
            iDestruct (atoms_interp_length with "Hatoms") as "<-".
            iDestruct (translate_types_comp_interp_length with "Hvalues") as "<-"; try done.
            by iFrame.
      + done.
      + instantiate (1 := case_i_os_payload). admit. (* TODO: should be provable, but might be a little annoying *)
      + by iApply values_interp_one_eq.
      + done.
    }
    iIntros (f vs) "(%Hfrel & Hframe & (%os' & Hvalues & Hatoms) & [%θ' Hrt])".
    iSplit; first done.

    iDestruct (atoms_interp_length with "Hatoms") as "<-".
    iDestruct (translate_types_comp_interp_length with "Hvalues") as "<-"; try done.
    by iFrame.
  Admitted.



  Lemma compat_binary_case M F L L' wt wt' wtf wl wl' wlf es' ess es1 es2 τs τ1 τ2 τs' κ :
    ess = [es1; es2] ->
    τs = [τ1; τ2] ->
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let F' := F <| fc_labels ::= cons (τs', L') |> in
    let ψ := InstrT [SumT κ τs] τs' in
    Forall2
      (fun τ es =>
         (forall wt wt' wtf wl wl' wlf es',
            let fe' := fe_of_context F' in
            let WT := wt ++ wt' ++ wtf in
            let WL := wl ++ wl' ++ wlf in
            let lmask := wlmask fe' wl in
            run_codegen (compile_instrs mr fe' es) wt wl = inr ((), wt', wl', es') ->
            ⊢ have_instr_type_sem rti sr mr M F' L WT WL lmask es' (InstrT [τ] τs') L'))
      τs ess ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ICase ψ L' ess)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L'.
Proof.
    intros -> -> fe WT WL lmask F' Ψ Hforall Hok Hcg.
    rewrite Forall2_cons_iff in Hforall.
    destruct Hforall as [Hes1 H2].
    rewrite Forall2_cons_iff in H2.
    destruct H2 as [Hes2 _].
    subst Ψ.
    cbn [compile_instr] in Hcg.
    destruct κ as [ ρ rf | ]; last inversion Hcg.
    destruct ρ  as [ | ρs_sum | | ]; try done.
    destruct τs' as [ | τ_res τs' ]; first done.
    destruct τs'; last done.

    inv_cg_bind Hcg wl_ret ?wt ?wt ?wl ?wl ?es ?es Hres_type Hcg.
    inv_cg_try_option Hres_type; subst.

    destruct (Wasm_int.Int32.modulus <=? length ρs_sum)%Z eqn:Hcmp; first inversion Hcg.
    inv_cg_bind Hcg ?units ?wt ?wt ?wl ?wl ?es es_case1 Hret Hcg.
    inv_cg_ret Hret; subst.

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
    apply run_codegen_create_defaults in Hcreate_defaults as H.
    destruct H as (_ & -> & -> & _).

    (* Case blocks *)
    cbv [map length seq zip Datatypes.uncurry] in Hcg.

    clear_nils.

    inv_cg_bind Hcg ?units ?wt ?wt ?wl ?wl ?es es_case1 Hcases Hret.
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
    apply run_codegen_drop_consts in Hdrop_consts_1 as H.
    destruct H as (_ & -> & -> & _).

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
    apply run_codegen_drop_consts in Hdrop_consts_2 as H.
    destruct H as (_ & -> & -> & _).

    inv_cg_bind Hcase_es2 ρ_case2 ?wt ?wt ?wl ?wl ?es ?es Hlookup Hcase_es2.
    inv_cg_try_option Hlookup; subst.

    inv_cg_bind Hcase_es2 case_2_sum_locals ?wt ?wt ?wl ?wl ?es ?es Hinject Hcase_es2.
    inv_cg_try_option Hinject; subst.

    inv_cg_bind Hcase_es2 [] ?wt wt_case_2 ?wl wl_case_2 ?es es_case_2 Hget_locals_2 Hcase_es2.
    inv_cg_bind Hget_locals_2 case_2_val_idxs ?wt wt_get_locals_2 ?wl wl_get_locals_2 ?es es_get_locals_2 Hnths_error Hget_locals_2.
    inv_cg_try_option Hnths_error; subst.

    destruct (run_codegen_get_locals _ _ _ _ _ _ _ Hget_locals_2) as ([] & -> & ->).

    (* clean up *)
    subst WT WL.
    clear_nils.
    simplify_eq.

    (* Iris Proof *)
    iIntros (? ? ? ? ? ? ? ?) "%Hsem %Hhas_values #Hinst #Hlabels #Hreturn Hrvs Hvs Hframe Hrt Hfr Hrun".
    iDestruct (Hes1 _ _ (wt_case_2 ++ wtf) _ _ (wl_case_2 ++ wlf) _ Hcase_es1) as "Hsem_es1".
    iDestruct (Hes2 _ _ wtf _ _ wlf _ Hcase_es2) as "Hsem_es2".

    (* Our values are in the value interpretation for our specific SumT *)
    (* This means that the values represent the tag and the payload. *)
    iDestruct (values_interp_one_eq with "Hvs") as "Hvs".
    iDestruct (value_interp_eq with "Hvs") as "Hvs".
    unfold value_interp0, value_se_interp0.
    iDestruct "Hvs" as "(%κ & %Hkind_sum & Hskind_as_type & Hsum_interp)".
    (*unfold type_skind in Hkind_sum.*)
    iDestruct "Hsum_interp" as (tag os' os_tag τ_tag ιs ιs_tag ixs  HSAtoms Htag_type_lookup Htag_type_arep Heval_rep_tail Hinject_sum_arep Hos'_ixs) "Hvalue_interp_os_i".
    (*assert (os = I32A (Wasm_int.int_of_Z i32m i) :: os0) as ->; first by inversion HSAtoms.*)
    simplify_eq.

    iDestruct (big_sepL2_length with "Hrvs") as "%Hlen".
    destruct vs as [|v_tag vs_payload]; first inversion Hlen.
    clear Hlen.
    iDestruct (atoms_interp_cons with "Hrvs") as "[-> Hatoms_interp_payload]".

    iPoseProof (frame_interp_wl_interp with "Hframe") as "%Hwl"; first done.
    rewrite list_extra.cons_app in Hhas_values.
    apply has_values_app_inv in Hhas_values as (e_tag & es_payload & -> & Hhv_tag & Hhvs_payload).

    (* save payload *)
    rewrite (app_assoc (e_tag ++ _)).
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      rewrite <- (app_assoc e_tag).
      instantiate (1 := λ f vs, (
        ⌜vs = [VAL_int32 (Wasm_int.Int32.repr tag)]⌝ ∗
        ⌜∀ i, i ∉ val_idxs -> f_locs f !! localimm i = f_locs fr !! localimm i⌝ ∗
        ⌜Forall2 (fun i v => f_locs f !! localimm i = Some v) val_idxs vs_payload⌝ ∗
        ⌜val_idxs = map prelude.W.Mk_localidx (seq (fe_wlocal_offset fe + length wl) (length wl_save))⌝
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
    iIntros (fr_saved w) "(-> & %Hsame & %Hsaved & %Hval_idxs_seq) Hfr Hrun".
    iAssert
      (frame_interp rti sr se L (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_case_1 ++ wl_case_2 ++ wlf) fr_saved)
      with "[Hframe]" as "Hframe_saved".
    { admit. } (* TODO: Not really sure how to prove this. Definitely need helper lemma *)

    edestruct (util.nths_error_exists val_idxs case_1_val_idxs vs_payload case_1_sum_locals (Forall2_length _ _ _ Hsaved)) as [case_1_vs_payload Hnerr_payload_c1]; try done.

    edestruct (util.nths_error_exists val_idxs case_2_val_idxs vs_payload case_2_sum_locals (Forall2_length _ _ _ Hsaved)) as [case_2_vs_payload Hnerr_payload_c2]; try done.

    iDestruct (frame_interp_wl_interp with "Hframe_saved") as "%Hwl_saved"; first done.
    pose proof (interp_wl_length _ _ _ Hwl_saved) as Hfr_saved_locs_len.

    assert (localimm tag_idx < length (f_locs fr_saved)) as Htag_in_fr_saved.
    {
      subst tag_idx.
      simpl.
      apply Nat.lt_le_trans with (m := fe_wlocal_offset fe + length (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_case_1 ++ wl_case_2 ++ wlf)).
      - rewrite app_assoc.
        rewrite (length_app (wl ++ wl_save) ([prelude.W.T_i32] ++ wl_case_1 ++ wl_case_2 ++ wlf)).
        lias.
      - exact Hfr_saved_locs_len.
    }

    (* Store tag *)
    rewrite (app_assoc (map _ _)).
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      instantiate (1 := λ f vs, (
        ⌜vs = []⌝ ∗
        ⌜∀ j, j ≠ (fe_wlocal_offset fe + length (wl ++ wl_save))%nat -> f_locs f !! j = f_locs fr_saved !! j⌝ ∗
        ⌜f_locs f !! (fe_wlocal_offset fe + length (wl ++ wl_save))%nat = Some (VAL_int32 (Wasm_int.Int32.repr tag))⌝
        )%I).
      iApply (cwp_local_set with "[] [$] [$]"); first done.
      iSplit; first done.
      iSplit.
      - iIntros "!> %j".
        iPureIntro.
        intros Hneq.
        simpl.
        rewrite list_lookup_insert_ne; [reflexivity | lia].
      - iSimpl.
        iPureIntro.
        rewrite list_lookup_insert_eq; try done.
    }
    iIntros (fr_saved_and_tag w) "(-> & %Hsame' & %Hsaved_and_tag) Hfr Hrun".
    clear_nils.

    assert (Forall2 (λ (i : prelude.W.localidx) (v : value), f_locs fr_saved_and_tag !! localimm i = Some v)
      case_1_val_idxs case_1_vs_payload) as Hf_case_1.
    {
      pose proof (util.nths_error_Forall2 _ val_idxs case_1_val_idxs vs_payload case_1_vs_payload case_1_sum_locals Hsaved Heq_some3 Hnerr_payload_c1) as Hf_case_1.
      eapply forall2_lookup_same.
      3: done.
      - intros. apply Hsame'; done.
      - eapply (util.nths_error_Forall _ val_idxs); last done.
        rewrite Hval_idxs_seq.
        rewrite length_app Nat.add_assoc.
        apply map_seq_forall_localidx_neq.
    }

    assert (Forall2 (λ (i : prelude.W.localidx) (v : value), f_locs fr_saved_and_tag !! localimm i = Some v)
      case_2_val_idxs case_2_vs_payload) as Hf_case_2.
    {
      pose proof (util.nths_error_Forall2 _ val_idxs case_2_val_idxs vs_payload case_2_vs_payload case_2_sum_locals Hsaved Heq_some6 Hnerr_payload_c2) as Hf_case_2.
      eapply forall2_lookup_same.
      3: done.
      - intros. apply Hsame'; done.
      - eapply (util.nths_error_Forall _ val_idxs); last done.
        rewrite Hval_idxs_seq.
        rewrite length_app Nat.add_assoc.
        apply map_seq_forall_localidx_neq.
    }

    iAssert
      (frame_interp rti sr se L (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_case_1 ++ wl_case_2 ++ wlf) fr_saved_and_tag)
      with "[Hframe_saved]" as "Hframe_saved_and_tag".
    { admit. } (* TODO: Not really sure how to prove this. Definitely need helper lemma *)

    (* Create defaults *)
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      eapply cwp_create_defaults in Hcreate_defaults as (_ & _ & _ & Hcreate_defaults).
      iDestruct (Hcreate_defaults with "[$] [$] []") as "Hcreate_defaults".
      {
        by instantiate (1 := λ f vs, (⌜f = fr_saved_and_tag⌝ ∗ ⌜vs = (map default_of_value_type wl_ret)⌝)%I).
      }
      iApply "Hcreate_defaults".
    }
    iIntros (??) "[-> ->] Hfr Hrun".

    (* Case analysis: Is tag 0 or 1? *)

    apply lookup_lt_Some in Htag_type_lookup as Hi.
    destruct tag as [| [|]]; last done.

    - (* Case: tag = 0 *)
      (* -------- Case 1 -------- *)
      rewrite (app_assoc (to_consts _)).
      iApply (cwp_seq with "[-]").
      {
        iApply (compat_case_block_success with "[] [$] [$] [$] [$] [$] [$] [] [] [$]").
        2: instantiate (1 := []).
        all: clear_nils.
        2, 3, 4, 5, 6, 7, 8, 9, 12: done.
        (* TODO: Remember frame_rel. *)
        (* 4: iApply "Hsem_es1". *)
        (* 1: done. *)
        (* by rewrite length_map. *)
        all: admit.
      }
      iIntros (f_es_case_1 vs) "(_ & %Hlen_vs & Hframe & %os & %θ' & Hos & Hvs & Hrt) Hfr Hrun".

      (* -------- Case 2 -------- *)
      iApply (cwp_wand with "[Hfr Hrun]").
      {
        iApply (compat_case_block_fail with "[$] [$]").
        2, 3, 4, 5, 6, 8: done.
        2: by instantiate (1 := 0).
        admit. (* TODO: we need to know that es_case_1 doesn't actually change the tag... *)
      }
      (* iIntros (??) "(-> & ->) Hfr Hrun". *)
      (* TODO: we would probably want fr and run resource back from the block_fail lemma *)
      iIntros (??) "(-> & ->)".
      iFrame.
      admit. (* TODO: Remember frame_rel. *)
    - (* Case: tag = 1 *)
      (* -------- Case 1 -------- *)
      rewrite (app_assoc (to_consts _)).
      iApply (cwp_seq with "[Hfr Hrun]").
      {
        iApply (compat_case_block_fail with "[$] [$]").
        7: by instantiate (1 := 1).
        2: instantiate (1 := []).
        1, 2, 3, 4, 5, 6: done.
        by rewrite length_map.
      }
      iIntros (??) "(-> & ->) Hfr Hrun".

      (* -------- Case 2 -------- *)
      iApply (cwp_wand with "[-]").
      {
        iApply (compat_case_block_success with "[] [$] [$] [$] [$] [$] [$] [] [] [$]").
        2, 3, 4, 5, 6, 7, 8, 9, 12: done.
        (* 4: iApply "Hsem_es2". *)
        (* 2: done. *)
        (* 1: done. *)
        (* by rewrite length_map. *)
        (* TODO: Use frame_rel. *)
        all: admit.
      }
      iIntros (f_es_case_2 vs) "(_ & %Hlen_vs & Hframe & %os & %θ' & Hos & Hvs & Hrt)".
      iFrame.
  Admitted.


  (* TODO: remove *)
  Lemma compat_binary_case' M F L L' wt wt' wtf wl wl' wlf es' ess es1 es2 τs τ1 τ2 τs' κ :
    ess = [es1; es2] ->
    τs = [τ1; τ2] ->
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let F' := F <| fc_labels ::= cons (τs', L') |> in
    let ψ := InstrT [SumT κ τs] τs' in
    Forall2
      (fun τ es =>
         (forall wt wt' wtf wl wl' wlf es',
            let fe' := fe_of_context F' in
            let WT := wt ++ wt' ++ wtf in
            let WL := wl ++ wl' ++ wlf in
            let lmask := wlmask fe wl in
            run_codegen (compile_instrs mr fe' es) wt wl = inr ((), wt', wl', es') ->
            ⊢ have_instr_type_sem rti sr mr M F' L WT WL lmask es' (InstrT [τ] τs') L'))
      τs ess ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ICase ψ L' ess)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L'.
  Proof.
    intros -> -> fe WT WL lmask F' Ψ Hforall Hok Hcg.
    rewrite Forall2_cons_iff in Hforall.
    destruct Hforall as [Hes1 H2].
    rewrite Forall2_cons_iff in H2.
    destruct H2 as [Hes2 _].
    subst Ψ.
    cbn [compile_instr] in Hcg.
    destruct κ as [ ρ ref | ]; last inversion Hcg.
    destruct ρ  as [ | ρs_sum | | ]; try done.
    destruct τs' as [ | τ_res τs' ]; first done.
    destruct τs'; last done.


    inv_cg_bind Hcg wl_ret ?wt ?wt ?wl ?wl ?es ?es Hres_type Hcg.
    inv_cg_try_option Hres_type; subst.

    destruct (Wasm_int.Int32.modulus <=? length ρs_sum)%Z eqn:Hcmp; first inversion Hcg.
    clear Hcmp.
    inv_cg_bind Hcg ?units ?wt ?wt ?wl ?wl ?es es_case1 Hret Hcg.
    inv_cg_ret Hret; subst.

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
    apply run_codegen_create_defaults in Hcreate_defaults as H.
    destruct H as (_ & -> & -> & _).

    (* Case blocks *)
    cbv [map length seq zip Datatypes.uncurry] in Hcg.

    clear_nils.

    inv_cg_bind Hcg ?units ?wt ?wt ?wl ?wl ?es es_case1 Hcases Hret.
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
    apply run_codegen_drop_consts in Hdrop_consts_1 as H.
    destruct H as (_ & -> & -> & _).

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
    apply run_codegen_drop_consts in Hdrop_consts_2 as H.
    destruct H as (_ & -> & -> & _).

    inv_cg_bind Hcase_es2 ρ_case2 ?wt ?wt ?wl ?wl ?es ?es Hlookup Hcase_es2.
    inv_cg_try_option Hlookup; subst.

    inv_cg_bind Hcase_es2 case_2_sum_locals ?wt ?wt ?wl ?wl ?es ?es Hinject Hcase_es2.
    inv_cg_try_option Hinject; subst.

    inv_cg_bind Hcase_es2 [] ?wt wt_case_2 ?wl wl_case_2 ?es es_case_2 Hget_locals_2 Hcase_es2.
    inv_cg_bind Hget_locals_2 case_2_val_idxs ?wt wt_get_locals_2 ?wl wl_get_locals_2 ?es es_get_locals_2 Hnths_error Hget_locals_2.
    inv_cg_try_option Hnths_error; subst.

    destruct (run_codegen_get_locals _ _ _ _ _ _ _ Hget_locals_2) as ([] & -> & ->).

    (* clean up *)
    subst WT WL.
    clear_nils.
    simplify_eq.

    (* Iris Proof *)
    iIntros (? ? ? ? ? ? ? ?) "%Hsem %Hhas_values #Hinst #Hlabels #Hreturn Hrvs Hvs Hframe Hrt Hfr Hrun".
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
    iDestruct (atoms_interp_cons with "Hrvs") as "[-> Hatoms_interp_payload]".

    iPoseProof (frame_interp_wl_interp with "Hframe") as "%Hwl"; first done.
    rewrite list_extra.cons_app in Hhas_values.
    apply has_values_app_inv in Hhas_values as (e_tag & es_payload & -> & Hhv_tag & Hhvs_payload).

    (* save payload *)
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
    iAssert
      (frame_interp rti sr se L (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_case_1 ++ wl_case_2 ++ wlf) fr_saved)
      with "[Hframe]" as "Hframe_saved".
    { admit. } (* TODO: Not really sure how to prove this. Definitely need helper lemma *)

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
    iAssert
      (frame_interp rti sr se L (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_case_1 ++ wl_case_2 ++ wlf) fr_saved_and_tag)
      with "[Hframe_saved]" as "Hframe_saved_and_tag".
    { admit. } (* TODO: Not really sure how to prove this. Definitely need helper lemma *)

    (* Create defaults *)
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      eapply cwp_create_defaults in Hcreate_defaults as (_ & _ & _ & Hcreate_defaults).
      iDestruct (Hcreate_defaults with "[$] [$] []") as "Hcreate_defaults".
      {
        by instantiate (1 := λ f vs, (⌜f = fr_saved_and_tag⌝ ∗ ⌜vs = (map default_of_value_type wl_ret)⌝)%I).
      }
      iApply "Hcreate_defaults".
    }
    iIntros (??) "[-> ->] Hfr Hrun".

    (* -------- Case 1 -------- *)
    rewrite (app_assoc (to_consts _)).
    iApply (cwp_seq with "[-]").
    {

      iApply (cwp_block with "[$] [$]"); auto.
      { apply is_consts_to_consts. }
      { by do 2 rewrite length_map. }
      iIntros "!> Hf Hrun".

      (* Case analysis: Is tag 0? *)
      destruct i.
      - (* Case: Tag is 0 *)

        (* TODO: ... *)
        replace (to_consts (map default_of_value_type wl_ret) ++
        [prelude.W.BI_get_local (localimm tag_idx)] ++
        [prelude.W.BI_const (prelude.W.VAL_int32 (Wasm_int.int_of_Z i32m 0%nat))] ++
        [prelude.W.BI_relop prelude.W.T_i32 (prelude.W.Relop_i prelude.W.ROI_ne)] ++
        [prelude.W.BI_br_if 0] ++ _)
        with ((to_consts (map default_of_value_type wl_ret) ++
        [prelude.W.BI_get_local (localimm tag_idx)] ++
        [prelude.W.BI_const (prelude.W.VAL_int32 (Wasm_int.int_of_Z i32m 0%nat))] ++
        [prelude.W.BI_relop prelude.W.T_i32 (prelude.W.Relop_i prelude.W.ROI_ne)] ++
        [prelude.W.BI_br_if 0]) ++ es_drop_1 ++ es_get_locals_1 ++ es_case_1); last admit.

        iApply (cwp_seq with "[Hf Hrun]").
        {
          iApply cwp_val_app; first apply has_values_to_consts.

          (* Get tag from local *)
          rewrite (separate1 (prelude.W.BI_get_local _)).
          iApply (cwp_seq with "[Hf Hrun]").
          {
            iApply (cwp_local_get with "[] [$] [$]"); first apply Hsaved_and_tag.
            by instantiate (1 := λ f v, (⌜v = [_]⌝ ∗ ⌜f = fr_saved_and_tag⌝)%I).
          }
          iIntros (?fr w) "(-> & ->) Hf Hrun".
          iSimpl.

          (* compare tag with case number: 0 *)
          rewrite separate3.
          iApply (cwp_seq with "[Hf Hrun]").
          {
            iApply (cwp_relop with "[$] [$]"); first done.
            iSimpl.
            by instantiate (1 := λ f v, (⌜v = [_]⌝ ∗ ⌜f = fr_saved_and_tag⌝)%I).
          }
          iIntros (?fr w) "(-> & ->) Hf Hrun".
          iSimpl.
          iApply (cwp_br_if_zero with "[$] [$]"); first done.
          instantiate (1 := λ f v, (⌜v = (map default_of_value_type wl_ret)⌝ ∗ ⌜f = fr_saved_and_tag⌝)%I).
          unfold fvs_combine.
          by rewrite app_nil_r.
        }
        iIntros (?fr w) "(-> & ->) Hf Hrun".

        (* drop default values *)
        rewrite (app_assoc (to_consts _)).
        iApply (cwp_seq with "[Hf Hrun]").
        {
          instantiate (1 := λ f vs, (⌜f = fr_saved_and_tag⌝ ∗ ⌜vs = []⌝)%I).
          eapply cwp_drop_consts in Hdrop_consts_1 as (_ & _ & _ & Hdrop_consts_1).
          - iDestruct (Hdrop_consts_1 with "[$] [$] []") as "Hdrop_consts_1".
            2: iApply "Hdrop_consts_1".
            done.
          - by do 2 rewrite length_map.
          - apply is_consts_to_consts.
        }
        iIntros (?fr w) "(-> & ->) Hf Hrun".
        iSimpl.

        (* get locals corresponding to payload of sum *)
        eapply cwp_restore_stack_w in Hget_locals_1; eauto using Forall2_length.
        2 : {
          instantiate (1 := case_1_vs_payload).
          pose proof (util.nths_error_length _ _ _ Heq_some3) as Hlen_c1vi.
          pose proof (util.nths_error_length _ _ _ Hnerr_payload_c1) as Hlen_c1vp.
          by rewrite <- Hlen_c1vi.
        }
        destruct Hget_locals_1 as (_ & _ & _ & Hget_locals_1).
        iDestruct (Hget_locals_1 with "[$] [$] []") as "Hget_locals_1"; clear Hget_locals_1.
        {
          iPureIntro.
          pose proof (util.nths_error_Forall2 _ val_idxs case_1_val_idxs vs_payload case_1_vs_payload case_1_sum_locals Hsaved Heq_some3 Hnerr_payload_c1) as Hf_case_1.
          admit.
          (* TODO: should be provable, but will probably be a bit annoying *)
        }

        iApply (cwp_seq with "[Hget_locals_1]").
        1: iApply "Hget_locals_1".
        iIntros (?fr w) "(-> & ->) Hf Hrun".

        (* Reason about case 1 code *)
        (* TODO: Use frame_rel. *)
        iApply ("Hsem_es1" with "[//] [] [$] [] [] [Hatoms_interp_payload] [Hvalue_interp_os_i] [Hframe_saved_and_tag] [$] [] [$]").
        + instantiate (1 := case_1_vs_payload); iPureIntro; simpl; rewrite has_values_iff_to_consts; done.
        + subst F'.
          replace (fc_labels (F <| fc_labels ::= cons ([τ_res], L') |>)) with
                  (([τ_res], L') :: fc_labels F); last done.
          iApply labels_interp_cons; try done.
          * subst fe. rewrite -Heq_some. simpl.
            unfold prelude.translate_types.
            simpl.
            destruct (prelude.translate_type (fc_type_vars F) τ_res); simpl; try done.
            by rewrite app_nil_r.
          * iIntros "!>" (fr' vs') "(%Hfrel & Hframe & (%os & Hvalues & Hatoms) & [%Θ Hrt])".
            iFrame.
            (* by instantiate (1 := λ f v, True%I). *)
            admit.
          * admit. (* TODO: Use frame_rel. *)
        + done.
        + instantiate (1 := os_i). admit. (* TODO: should be provable, but might be a little annoying *)
        + iApply values_interp_one_eq.
          by inversion Htype_lookup; subst.
        + admit.
        + admit.


      - (* Case: Tag is not 0 *)

        (* TODO: ... *)
        replace (to_consts (map default_of_value_type wl_ret) ++
        [prelude.W.BI_get_local (localimm tag_idx)] ++
        [prelude.W.BI_const (prelude.W.VAL_int32 (Wasm_int.int_of_Z i32m 0%nat))] ++
        [prelude.W.BI_relop prelude.W.T_i32 (prelude.W.Relop_i prelude.W.ROI_ne)] ++ _)
        with ((to_consts (map default_of_value_type wl_ret) ++
        [prelude.W.BI_get_local (localimm tag_idx)] ++
        [prelude.W.BI_const (prelude.W.VAL_int32 (Wasm_int.int_of_Z i32m 0%nat))] ++
        [prelude.W.BI_relop prelude.W.T_i32 (prelude.W.Relop_i prelude.W.ROI_ne)]) ++
        [prelude.W.BI_br_if 0] ++ es_drop_1 ++ es_get_locals_1 ++ es_case_1); last admit.

        iApply (cwp_seq with "[Hf Hrun]").
        {
          iApply cwp_val_app; first apply has_values_to_consts.

          (* Get tag from local *)
          rewrite (separate1 (prelude.W.BI_get_local _)).
          iApply (cwp_seq with "[Hf Hrun]").
          {
            iApply (cwp_local_get with "[] [$] [$]"); first apply Hsaved_and_tag.
            by instantiate (1 := λ f v, (⌜v = [_]⌝ ∗ ⌜f = fr_saved_and_tag⌝)%I).
          }
          iIntros (?fr w) "(-> & ->) Hf Hrun".
          iSimpl.

          (* compare tag with case number: 0 *)
          rewrite separate3.
          iApply (cwp_seq with "[Hf Hrun]").
          {
            iApply (cwp_relop with "[$] [$]"); first done.
            iSimpl.
            rewrite Wasm_int.Int32.eq_false.
            2: admit. (* TODO: this is not actually provable. We need to know tags aren't huge... Maybe a different approach than destruct i *)
            iSimpl.
            by instantiate (1 := λ f v, (⌜v = [_]⌝ ∗ ⌜f = fr_saved_and_tag⌝)%I).
          }
          iIntros (?fr w) "(-> & ->) Hf Hrun".
          iSimpl.
          iApply (cwp_val with "[$] [$]").
          - by instantiate (1 := [(VAL_int32 Wasm_int.Int32.one)]).
          - unfold fvs_combine.
            by instantiate (1 := λ f v, (⌜v = _ ++ [_]⌝ ∗ ⌜f = fr_saved_and_tag⌝)%I).
        }
        iIntros (?fr w) "(-> & ->) Hf Hrun".

        (* TODO: ... *)
        replace (to_consts
        (map default_of_value_type wl_ret ++ [VAL_int32 Wasm_int.Int32.one]) ++
        [prelude.W.BI_br_if 0] ++ _)
        with ((to_consts
        (map default_of_value_type wl_ret ++ [VAL_int32 Wasm_int.Int32.one]) ++
        [prelude.W.BI_br_if 0]) ++ es_drop_1 ++ es_get_locals_1 ++ es_case_1); last admit.
        iApply (cwp_seq with "[-]").
        2: {
          instantiate (1 := λ f vs, False%I).
          by iIntros.
        }
        unfold to_consts.
        rewrite map_app.
        rewrite -app_assoc.
        replace (map BI_const [VAL_int32 Wasm_int.Int32.one] ++ [prelude.W.BI_br_if 0])
        with [BI_const (VAL_int32 Wasm_int.Int32.one); prelude.W.BI_br_if 0]; last done.

        iApply (cwp_br_if_nonzero with "[$] [$]"); try done.
        1: apply has_values_to_consts.
        1: by do 2 rewrite length_map.
        iFrame.
        admit.
    }
    iIntros (??) "H Hf Hr".

    (* -------- Case 2 -------- *)

    admit.
  Admitted.

  Lemma compat_case M F L L' wt wt' wtf wl wl' wlf es' ess τs τs' κ :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let F' := F <| fc_labels ::= cons (τs', L') |> in
    let ψ := InstrT [SumT κ τs] τs' in
    Forall2
      (fun τ es =>
         (forall wt wt' wtf wl wl' wlf es',
            let fe' := fe_of_context F' in
            let WT := wt ++ wt' ++ wtf in
            let WL := wl ++ wl' ++ wlf in
            let lmask := wlmask fe wl in
            run_codegen (compile_instrs mr fe' es) wt wl = inr ((), wt', wl', es') ->
            ⊢ have_instr_type_sem rti sr mr M F' L WT WL lmask es' (InstrT [τ] τs') L'))
      τs ess ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ICase ψ L' ess)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L'.
  Admitted.

End Fundamental.
