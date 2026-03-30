Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.util.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section case.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_case_block_fail F wt wt_save tag_idx (tag i : nat) f wl_others wl_ret es_drop_i es_get_locals_i es_case_i B R wl wl_save τ_res val_idxs case_i_val_idxs case_i_sum_locals (vs_res vs_payload case_i_vs_payload : list value) :
    let fe := fe_of_context F in
    f_locs f !! tag_idx = Some (VAL_int32 (Wasm_int.Int32.repr tag)) ->
    run_codegen (get_locals_w case_i_val_idxs) (wt ++ wt_save)
      (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_others) = inr ((), [], [], es_get_locals_i) ->
    run_codegen (drop_consts wl_ret) (wt ++ wt_save)
      (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_others) = inr ((), [], [], es_drop_i) ->
    util.nths_error val_idxs case_i_sum_locals = Some case_i_val_idxs ->
    util.nths_error vs_payload case_i_sum_locals = Some case_i_vs_payload ->
    prelude.translate_type (fe_type_vars fe) τ_res = Some wl_ret ->
    tag ≠ i ->
    (tag < Wasm_int.Int32.modulus)%Z ->
    (i < Wasm_int.Int32.modulus)%Z ->
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
    intros fe Hlookup_saved_and_tag Hget_locals_i Hdrop_consts_i Hnerr_val_idxs Hnerr_payload_ci Htranslate_type_fe Hneq Htag_lt Hi_lt Hvs_res_length.
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
        2: {
          intro Heq.
          apply Hneq.
          apply Nat2Z.inj.
          apply Wasm_int.Int32.repr_inv; [lia | lia | exact Heq].
        }
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
  Qed.


  (* TODO: should probably be written using run_codegen somehow *)
  Lemma compat_case_block_success M F L wt wt_save wt_cases wt_others wtf tag_idx (tag i : nat) fr_saved_and_tag wl_ret lmask es_drop_i es_get_locals_i es_case_i B R se L' wl wl_save wl_others wl_cases wlf (τs: list type) τ_i τ_tag τ_res os_payload case_i_os_payload val_localidxs case_i_val_idxs case_i_sum_locals (vs_res vs_payload case_i_vs_payload : list value) θ :
    let F' := F <| fc_labels ::= cons ([τ_res], L') |> in
    let fe := fe_of_context F in
    f_locs fr_saved_and_tag !! tag_idx = Some (VAL_int32 (Wasm_int.Int32.repr tag)) ->
    run_codegen (get_locals_w case_i_val_idxs) (wt ++ wt_save ++ wt_others)
        (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_others) = inr ((), [], [], es_get_locals_i) ->
    run_codegen (drop_consts wl_ret) (wt ++ wt_save ++ wt_others)
        (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_others) = inr ((), [], [], es_drop_i) ->
    util.nths_error val_localidxs case_i_sum_locals = Some case_i_val_idxs ->
    util.nths_error vs_payload case_i_sum_locals = Some case_i_vs_payload ->
    prelude.translate_type (fe_type_vars fe) τ_res = Some wl_ret ->
    τs !! i = Some τ_i ->
    τs !! tag = Some τ_tag ->
    i = tag ->
    length vs_res = length wl_ret ->
    Forall2
      (λ (i : prelude.W.localidx) (v : value),
         f_locs fr_saved_and_tag !! localimm i = Some v)
       val_localidxs vs_payload ->
     val_localidxs = map prelude.W.Mk_localidx $ seq (fe_wlocal_offset fe + length wl) (length wl_save) ->
     tag_idx = fe_wlocal_offset fe + length (wl ++ wl_save) ->
     sem_env_interp F se ->
    ⊢
    have_instr_type_sem rti sr mr M F' L
          (wt ++ wt_save ++ wt_cases ++ wtf)
          (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_cases ++ wlf)
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
            ⌜frame_rel lmask fr_saved_and_tag fr'⌝ ∗
            frame_interp rti sr se L'
             (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_cases ++ wlf)
             fr' ∗
            ∃ (os' : leibnizO (list atom)) (θ : address_map),
             values_interp rti sr se [τ_res] os' ∗ atoms_interp os' vs' ∗
             rt_token rti sr θ
          )
        }}.
  Proof.
    intros F' fe Hlookup_saved_and_tag Hget_locals_i Hdrop_consts_i Hnerr_val_idxs Hnerr_payload_ci Htranslate_type_fe Ht_lookup_i Ht_lookup_tag Heq Hvs_res_length Hsaved Hval_localidxs Htag_idx Hsem.
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

    assert (Forall2 (λ (i : prelude.W.localidx) (v : value), f_locs fr_saved_and_tag !! localimm i = Some v)
      case_i_val_idxs case_i_vs_payload) as Hf_case_i.
    {
      pose proof (util.nths_error_Forall2 _ val_localidxs case_i_val_idxs vs_payload case_i_vs_payload case_i_sum_locals Hsaved Hnerr_val_idxs Hnerr_payload_ci) as Hf_case_i.
      eapply forall2_lookup_same.
      3: done.
      - intros. instantiate (1 := tag_idx) in H.
        reflexivity.
      - eapply (util.nths_error_Forall _ val_localidxs); last done.
        subst val_localidxs tag_idx.
        rewrite length_app Nat.add_assoc.
        apply map_seq_forall_localidx_neq.
    }


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
        (* TODO: might need to get the following from the main proof:
          Heq_some1 : ρs_sum !! 0 = Some ρ_case1
          Heq_some2 : inject_sum_rep EmptyEnv ρs_sum ρ_case1 = Some case_1_sum_locals
          Hnerr_payload_c1 : util.nths_error vs_payload case_1_sum_locals = Some case_1_vs_payload

          Htype_lookup : [τ1; τ2] !! 0 = Some τ_i
          Htype_arep : type_arep se τ_i = Some ιs_i
          Heval_rep_tail : tail <$> eval_rep se (SumR ρs_sum) = Some ιs
          Hinject_sum_arep : inject_sum_arep ιs ιs_i = Some ixs
          Hos0_ixs : util.nths_error os0 ixs = Some os_i
         *)
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
    set (τs := [τ1; τ2]).
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

    destruct (Wasm_int.Int32.modulus <? length ρs_sum)%Z eqn:Hcmp; first inversion Hcg.
    inv_cg_bind Hcg ?units ?wt ?wt ?wl ?wl ?es es_case1 Hret Hcg.
    inv_cg_ret Hret; subst.
    apply Z.ltb_ge in Hcmp.

    inv_cg_bind Hcg ρs_atom ?wt ?wt ?wl ?wl ?es ?es Hιs Hcg.
    inv_cg_try_option Hιs; subst.
    inv_cg_bind Hcg val_localidxs wt_save ?wt wl_save ?wl es_save ?es Hsave Hcg.
    repeat rewrite app_nil_r in Hsave.

    (* Save tag *)
    inv_cg_bind Hcg tag_localidx ?wt ?wt ?wl ?wl ?es ?es HsaveTag Hcg.
    unfold save_stack1 in HsaveTag.
    inv_cg_bind HsaveTag ?tl ?wt ?wt ?wl ?wl ?es ?es Halloc_tag HsaveTag.
    apply wp_wlalloc in Halloc_tag as [Hlocal_tag_idx [-> [-> ->]]].
    inv_cg_bind HsaveTag [] ?wt ?wt ?wl ?wl es_set_tag ?es HsetTag HretTagIdx.
    inv_cg_emit HsetTag; subst.
    inv_cg_ret HretTagIdx; subst.

    clear_nils.
    set (tag_idx := (fe_wlocal_offset fe + length (wl ++ wl_save))).
    set (tag_localidx := Mk_localidx tag_idx).
    replace (Mk_localidx (fe_wlocal_offset fe + length (wl ++ wl_save))) with tag_localidx in *; last done.

    (* Put default result values on stack *)
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_create_defaults ?es Hcreate_defaults Hcg.
    apply run_codegen_create_defaults in Hcreate_defaults as H.
    destruct H as (_ & -> & -> & _).

    (* Case blocks *)
    cbv [map length seq zip Datatypes.uncurry] in Hcg.

    clear_nils.

    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es es_case2 Hcase_es1 Hcase_es2.

    (* Case es1 *)

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

    apply lookup_lt_Some in Htag_type_lookup as Htag_size_bound.
    assert (length τs = length ρs_sum) as Htyp_rep_len.
    {
      inversion Hok; subst.
      unfold has_mono_rep_instr in H.
      destruct H as [H _].
      simpl in H.
      rewrite Forall_singleton in H.
      inversion H; subst.
      inversion H1; subst.
      apply has_kind_SumT_inv in H3 as (rf' & HF2).
      by eapply Forall2_length.
    }
    assert (tag < Wasm_int.Int32.modulus)%Z as Htag_in_i32_bound.
    { rewrite Htyp_rep_len in Htag_size_bound. eapply Z.lt_le_trans; last done. by apply Nat2Z.inj_lt. }

    (* TODO: we should also know that tag < length (ρs_sum). This will follow easily from the above and Htag_type_lookup *)

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
      instantiate (1 := λ fr' vs, (
        ∃ val_idxs,
        ⌜vs = [VAL_int32 (Wasm_int.Int32.repr tag)]⌝ ∗
        ⌜frame_rel (λ i, i ∉ val_idxs) fr fr'⌝ ∗
        ⌜Forall2 (fun i v => f_locs fr' !! localimm i = Some v) val_localidxs vs_payload⌝ ∗
        ⌜val_idxs = seq (fe_wlocal_offset fe + length wl) (length wl_save)⌝ ∗
        ⌜val_localidxs = map prelude.W.Mk_localidx val_idxs⌝
        )%I).
      iApply cwp_val_app; first done.
      eapply cwp_save_stack_w in Hsave; eauto.
      + destruct Hsave as (-> & -> & -> & Hsave).
        iApply (Hsave with "[$] [$]").
        iIntros (f' [Hfsame Hfchanged]).
        unfold fvs_combine.
        auto.
      + admit. (* easy pure conseqeunce of value_interp and
      rep_values_interp, should be proved above the first wp_seq
      rule *)
    }
    iIntros (fr_saved w) "(%val_idxs & -> & %Hfrel_fr_saved & %Hsaved & %Hval_idxs_seq & %Hval_localidxs) Hfr Hrun".
    iAssert
      (frame_interp rti sr se L (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_case_1 ++ wl_case_2 ++ wlf) fr_saved)
      with "[Hframe]" as "Hframe_saved".
    { admit. } (* TODO: Not really sure how to prove this. Definitely need helper lemma *)

    edestruct (util.nths_error_exists val_localidxs case_1_val_idxs vs_payload case_1_sum_locals (Forall2_length _ _ _ Hsaved)) as [case_1_vs_payload Hnerr_payload_c1]; try done.

    edestruct (util.nths_error_exists val_localidxs case_2_val_idxs vs_payload case_2_sum_locals (Forall2_length _ _ _ Hsaved)) as [case_2_vs_payload Hnerr_payload_c2]; try done.

    iDestruct (frame_interp_wl_interp with "Hframe_saved") as "%Hwl_saved"; first done.
    pose proof (interp_wl_length _ _ _ Hwl_saved) as Hfr_saved_locs_len.

    assert (tag_idx < length (f_locs fr_saved)) as Htag_in_fr_saved.
    {
      subst tag_idx.
      simpl.
      eapply Nat.lt_le_trans; last done.
      - rewrite app_assoc.
        subst fe.
        instantiate (1 := F).
        repeat rewrite length_app.
        lias.
    }

    (* Store tag *)
    rewrite (app_assoc (map _ _)).
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      instantiate (1 := λ fr' vs, (
        ⌜vs = []⌝ ∗
        ⌜frame_rel (λ j, j ≠ tag_idx) fr_saved fr'⌝ ∗
        ⌜f_locs fr' !! tag_idx = Some (VAL_int32 (Wasm_int.Int32.repr tag))⌝
        )%I).
      iApply (cwp_local_set with "[] [$] [$]"); first done.
      iSplit; first done.
      iSplit.
      - iPureIntro.
        split; last done.
        intros j Hneq.
        simpl.
        rewrite list_lookup_insert_ne; [reflexivity | lia].
      - iSimpl.
        iPureIntro.
        rewrite list_lookup_insert_eq; try done.
    }
    iIntros (fr_saved_and_tag w) "(-> & %Hfrel_fr_saved_and_tag & %Hsaved_and_tag) Hfr Hrun".
    clear_nils.

    (* relate starting frame fr and fr_saved_and_tag *)
    pose proof (frame_rel_mask_trans_combine _ _ _ _ _ Hfrel_fr_saved Hfrel_fr_saved_and_tag) as Hfrel_fr_and_fr_saved_and_tag.
    simpl in Hfrel_fr_and_fr_saved_and_tag.

    assert (frame_rel lmask fr fr_saved_and_tag) as Hfrel_lmask_saved_and_tag.
    {
      eapply frame_rel_mask_mono; [| exact Hfrel_fr_and_fr_saved_and_tag].
      intros i [Hi_lo Hi_hi].
      split.
      + rewrite Hval_idxs_seq.
        intro Hin. apply elem_of_seq in Hin. lia.
      + unfold tag_idx. rewrite length_app. lia.
    }
    pose proof Hfrel_fr_and_fr_saved_and_tag as [_ ->].
    iDestruct (labels_interp_mono _ _ _ _ fr_saved_and_tag _ _ _ _ with "Hlabels") as "Hlabels'"; first done.
    {
      instantiate (1 := (wlmask (fe_of_context F') (wl ++ wl_save ++ [prelude.W.T_i32]))).
      intros i [Hi_lo Hi_hi].
      simpl.
      split.
      + exact Hi_lo.
      + rewrite -fe_of_context_labels.
        rewrite !length_app. simpl.
        subst fe.
        lia.
    }

    assert (Forall2 (λ (i : prelude.W.localidx) (v : value), f_locs fr_saved_and_tag !! localimm i = Some v)
      val_localidxs vs_payload) as Hfr_saved_and_tag_payload.
    {
      eapply forall2_lookup_same.
      3: done.
      - intros. instantiate (1 := tag_idx) in H.
        destruct Hfrel_fr_saved_and_tag as [-> _]; done.
      - subst val_idxs val_localidxs tag_idx.
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
        iApply (compat_case_block_success with "[] [$] [$] [$] [$] [$] [$] [$] [$] [$]").
        2: instantiate (1 := []).
        all: clear_nils.
        1, 2, 3, 4, 5, 6, 8, 9, 11, 13, 14: done.
        4: iApply "Hsem_es1".
        1: done.
        1: by rewrite length_map.
        by subst val_idxs.
      }
      iIntros (f_es_case_1 vs) "(_ & %Hlen_vs & %Hfrel_new & Hframe & %os & %θ' & Hos & Hvs & Hrt) Hfr Hrun".

      (* -------- Case 2 -------- *)
      iApply (cwp_wand with "[Hfr Hrun]").
      {
        iApply (compat_case_block_fail with "[$] [$]").
        2, 3, 4, 5, 6, 9, 10: done.
        2: by instantiate (1 := 0).
        2: done.
        rewrite -Hsaved_and_tag.
        destruct Hfrel_new as [Hmask _].
        symmetry.
        apply Hmask.
        subst tag_idx fe.
        unfold wlmask.
        repeat rewrite length_app.
        rewrite -fe_of_context_labels.
        lias.
      }
      (* iIntros (??) "(-> & ->) Hfr Hrun". *)
      (* TODO: we would probably want fr and run resource back from the block_fail lemma *)
      iIntros (??) "(-> & ->)".
      iFrame.
      iPureIntro.
      rewrite -fe_of_context_labels in Hfrel_new.
      unfold lmask.
      eapply frame_rel_trans.
      + eapply frame_rel_mask_mono; [| exact Hfrel_lmask_saved_and_tag].
        intros i [Hi_lo Hi_hi]. unfold lmask, wlmask. split; exact Hi_lo || exact Hi_hi.
      + eapply frame_rel_wlmask_mono; [| exact Hfrel_new].
        rewrite length_app. lia.

    - (* Case: tag = 1 *)
      (* -------- Case 1 -------- *)
      rewrite (app_assoc (to_consts _)).
      iApply (cwp_seq with "[Hfr Hrun]").
      {
        iApply (compat_case_block_fail with "[$] [$]").
        7: by instantiate (1 := 1).
        2: instantiate (1 := []).
        1, 2, 3, 4, 5, 6, 7, 8: done.
        by rewrite length_map.
      }
      iIntros (??) "(-> & ->) Hfr Hrun".

      iDestruct (labels_interp_mono _ _ _ _ fr_saved_and_tag _ _ _ _ with "Hlabels") as "Hlabels'''"; first done.
      {
        instantiate (1 := (wlmask (fe_of_context F') (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_case_1))).
        intros i [Hi_lo Hi_hi].
        simpl.
        split.
        + exact Hi_lo.
        + rewrite -fe_of_context_labels.
          rewrite !length_app. simpl.
          subst fe.
          lia.
      }

      (* -------- Case 2 -------- *)
      iApply (cwp_wand with "[-]").
      {
        iApply (compat_case_block_success with "[] [$] [$] [$] [$] [$] [$] [$] [$] [$]").
        1, 2, 3, 4, 5, 6, 8, 9, 11, 13, 14, 15: done.
        1: done.
        1: by rewrite length_map.
        by subst val_idxs.
      }
      iIntros (f_es_case_2 vs) "(_ & %Hlen_vs & %Hfrel_new & Hframe & %os & %θ' & Hos & Hvs & Hrt)".
      iFrame.
      iPureIntro.
      rewrite -fe_of_context_labels in Hfrel_new.
      unfold lmask.
      eapply frame_rel_trans.
      + eapply frame_rel_mask_mono; [| exact Hfrel_lmask_saved_and_tag].
        intros i [Hi_lo Hi_hi]. unfold lmask, wlmask. split; exact Hi_lo || exact Hi_hi.
      + eapply frame_rel_wlmask_mono; [| exact Hfrel_new].
        rewrite length_app. lia.
  Admitted.


  Lemma compat_ternary_case M F L L' wt wt' wtf wl wl' wlf es' ess es1 es2 es3 τs τ1 τ2 τ3 τs' κ :
    ess = [es1; es2; es3] ->
    τs = [τ1; τ2; τ3] ->
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
    set (τs := [τ1; τ2; τ3]).
    rewrite Forall2_cons_iff in Hforall.
    destruct Hforall as [Hes1 H2].
    rewrite Forall2_cons_iff in H2.
    destruct H2 as [Hes2 H3].
    rewrite Forall2_cons_iff in H3.
    destruct H3 as [Hes3 _].
    subst Ψ.
    cbn [compile_instr] in Hcg.
    destruct κ as [ ρ rf | ]; last inversion Hcg.
    destruct ρ  as [ | ρs_sum | | ]; try done.
    destruct τs' as [ | τ_res τs' ]; first done.
    destruct τs'; last done.

    inv_cg_bind Hcg wl_ret ?wt ?wt ?wl ?wl ?es ?es Hres_type Hcg.
    inv_cg_try_option Hres_type; subst.

    destruct (Wasm_int.Int32.modulus <? length ρs_sum)%Z eqn:Hcmp; first inversion Hcg.
    inv_cg_bind Hcg ?units ?wt ?wt ?wl ?wl ?es es_case1 Hret Hcg.
    inv_cg_ret Hret; subst.
    apply Z.ltb_ge in Hcmp.

    inv_cg_bind Hcg ρs_atom ?wt ?wt ?wl ?wl ?es ?es Hιs Hcg.
    inv_cg_try_option Hιs; subst.
    inv_cg_bind Hcg val_localidxs wt_save ?wt wl_save ?wl es_save ?es Hsave Hcg.
    repeat rewrite app_nil_r in Hsave.

    (* Save tag *)
    inv_cg_bind Hcg tag_localidx ?wt ?wt ?wl ?wl ?es ?es HsaveTag Hcg.
    unfold save_stack1 in HsaveTag.
    inv_cg_bind HsaveTag ?tl ?wt ?wt ?wl ?wl ?es ?es Halloc_tag HsaveTag.
    apply wp_wlalloc in Halloc_tag as [Hlocal_tag_idx [-> [-> ->]]].
    inv_cg_bind HsaveTag [] ?wt ?wt ?wl ?wl es_set_tag ?es HsetTag HretTagIdx.
    inv_cg_emit HsetTag; subst.
    inv_cg_ret HretTagIdx; subst.

    clear_nils.
    set (tag_idx := (fe_wlocal_offset fe + length (wl ++ wl_save))).
    set (tag_localidx := Mk_localidx tag_idx).
    replace (Mk_localidx (fe_wlocal_offset fe + length (wl ++ wl_save))) with tag_localidx in *; last done.

    (* Put default result values on stack *)
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_create_defaults ?es Hcreate_defaults Hcg.
    apply run_codegen_create_defaults in Hcreate_defaults as H.
    destruct H as (_ & -> & -> & _).

    (* Case blocks *)
    cbv [map length seq zip Datatypes.uncurry] in Hcg.

    clear_nils.

    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es es_case2 Hcase_es1 Hcases.
    inv_cg_bind Hcases [] ?wt ?wt ?wl ?wl ?es ?es Hcase_es2 Hcase_es3.

    (* Case es1 *)

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


    (* Case es3 *)
    inv_cg_bind Hcase_es3 ?units ?wt ?wt ?wl ?wl ?es ?es Hcase_es3 Hmret.
    inv_cg_ret Hmret; subst.

    inv_cg_bind Hcase_es3 ?pair ?wt ?wt ?wl ?wl ?es ?es Hcase_es3 Hcase_es3_block.
    destruct pair, u.
    inv_cg_emit Hcase_es3_block; subst.
    apply run_codegen_capture in Hcase_es3 as [Hcase_es3 ->].

    inv_cg_bind Hcase_es3 [] ?wt ?wt ?wl ?wl ?es ?es Hget_tag Hcase_es3.
    inv_cg_emit Hget_tag; subst.

    inv_cg_bind Hcase_es3 [] ?wt ?wt ?wl ?wl ?es ?es Htag0 Hcase_es3.
    inv_cg_emit Htag0; subst.

    inv_cg_bind Hcase_es3 [] ?wt ?wt ?wl ?wl ?es ?es Hcompare_tag Hcase_es3.
    inv_cg_emit Hcompare_tag; subst.

    inv_cg_bind Hcase_es3 [] ?wt ?wt ?wl ?wl ?es ?es Hbr_case Hcase_es3.
    inv_cg_emit Hbr_case; subst.

    inv_cg_bind Hcase_es3 [] ?wt ?wt ?wl ?wl es_drop_3 ?es Hdrop_consts_3 Hcase_es3.
    apply run_codegen_drop_consts in Hdrop_consts_3 as H.
    destruct H as (_ & -> & -> & _).

    inv_cg_bind Hcase_es3 ρ_case3 ?wt ?wt ?wl ?wl ?es ?es Hlookup Hcase_es3.
    inv_cg_try_option Hlookup; subst.

    inv_cg_bind Hcase_es3 case_3_sum_locals ?wt ?wt ?wl ?wl ?es ?es Hinject Hcase_es3.
    inv_cg_try_option Hinject; subst.

    inv_cg_bind Hcase_es3 [] ?wt wt_case_3 ?wl wl_case_3 ?es es_case_3 Hget_locals_3 Hcase_es3.
    inv_cg_bind Hget_locals_3 case_3_val_idxs ?wt wt_get_locals_3 ?wl wl_get_locals_3 ?es es_get_locals_3 Hnths_error Hget_locals_3.
    inv_cg_try_option Hnths_error; subst.

    destruct (run_codegen_get_locals _ _ _ _ _ _ _ Hget_locals_3) as ([] & -> & ->).


    (* clean up *)
    subst WT WL.
    clear_nils.
    simplify_eq.

    (* Iris Proof *)
    iIntros (? ? ? ? ? ? ? ?) "%Hsem %Hhas_values #Hinst #Hlabels #Hreturn Hrvs Hvs Hframe Hrt Hfr Hrun".
    iDestruct (Hes1 _ _ (wt_case_2 ++ wt_case_3 ++ wtf) _ _ (wl_case_2 ++ wl_case_3 ++ wlf) _ Hcase_es1) as "Hsem_es1".
    iDestruct (Hes2 _ _ (wt_case_3 ++ wtf) _ _ (wl_case_3 ++ wlf) _ Hcase_es2) as "Hsem_es2".
    iDestruct (Hes3 _ _ (wtf) _ _ (wlf) _ Hcase_es3) as "Hsem_es3".

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

    apply lookup_lt_Some in Htag_type_lookup as Htag_size_bound.
    assert (length τs = length ρs_sum) as Htyp_rep_len.
    {
      inversion Hok; subst.
      unfold has_mono_rep_instr in H.
      destruct H as [H _].
      simpl in H.
      rewrite Forall_singleton in H.
      inversion H; subst.
      inversion H1; subst.
      apply has_kind_SumT_inv in H3 as (rf' & HF2).
      by eapply Forall2_length.
    }
    assert (tag < Wasm_int.Int32.modulus)%Z as Htag_in_i32_bound.
    { rewrite Htyp_rep_len in Htag_size_bound. eapply Z.lt_le_trans; last done. by apply Nat2Z.inj_lt. }

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
      instantiate (1 := λ fr' vs, (
        ∃ val_idxs,
        ⌜vs = [VAL_int32 (Wasm_int.Int32.repr tag)]⌝ ∗
        ⌜frame_rel (λ i, i ∉ val_idxs) fr fr'⌝ ∗
        ⌜Forall2 (fun i v => f_locs fr' !! localimm i = Some v) val_localidxs vs_payload⌝ ∗
        ⌜val_idxs = seq (fe_wlocal_offset fe + length wl) (length wl_save)⌝ ∗
        ⌜val_localidxs = map prelude.W.Mk_localidx val_idxs⌝
        )%I).
      iApply cwp_val_app; first done.
      eapply cwp_save_stack_w in Hsave; eauto.
      + destruct Hsave as (-> & -> & -> & Hsave).
        iApply (Hsave with "[$] [$]").
        iIntros (f' [Hfsame Hfchanged]).
        unfold fvs_combine.
        auto.
      + admit. (* easy pure conseqeunce of value_interp and
      rep_values_interp, should be proved above the first wp_seq
      rule *)
    }
    iIntros (fr_saved w) "(%val_idxs & -> & %Hfrel_fr_saved & %Hsaved & %Hval_idxs_seq & %Hval_localidxs) Hfr Hrun".
    iAssert
    (frame_interp rti sr se L (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_case_1 ++ wl_case_2  ++ wl_case_3 ++ wlf) fr_saved)
      with "[Hframe]" as "Hframe_saved".
    { admit. } (* TODO: Not really sure how to prove this. Definitely need helper lemma *)

    edestruct (util.nths_error_exists val_localidxs case_1_val_idxs vs_payload case_1_sum_locals (Forall2_length _ _ _ Hsaved)) as [case_1_vs_payload Hnerr_payload_c1]; try done.

    edestruct (util.nths_error_exists val_localidxs case_2_val_idxs vs_payload case_2_sum_locals (Forall2_length _ _ _ Hsaved)) as [case_2_vs_payload Hnerr_payload_c2]; try done.

    edestruct (util.nths_error_exists val_localidxs case_3_val_idxs vs_payload case_3_sum_locals (Forall2_length _ _ _ Hsaved)) as [case_3_vs_payload Hnerr_payload_c3]; try done.


    iDestruct (frame_interp_wl_interp with "Hframe_saved") as "%Hwl_saved"; first done.
    pose proof (interp_wl_length _ _ _ Hwl_saved) as Hfr_saved_locs_len.

    assert (tag_idx < length (f_locs fr_saved)) as Htag_in_fr_saved.
    {
      subst tag_idx.
      simpl.
      eapply Nat.lt_le_trans; last done.
      - rewrite app_assoc.
        subst fe.
        instantiate (1 := F).
        repeat rewrite length_app.
        lias.
    }

    (* Store tag *)
    rewrite (app_assoc (map _ _)).
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      instantiate (1 := λ fr' vs, (
        ⌜vs = []⌝ ∗
        ⌜frame_rel (λ j, j ≠ tag_idx) fr_saved fr'⌝ ∗
        ⌜f_locs fr' !! tag_idx = Some (VAL_int32 (Wasm_int.Int32.repr tag))⌝
        )%I).
      iApply (cwp_local_set with "[] [$] [$]"); first done.
      iSplit; first done.
      iSplit.
      - iPureIntro.
        split; last done.
        intros j Hneq.
        simpl.
        rewrite list_lookup_insert_ne; [reflexivity | lia].
      - iSimpl.
        iPureIntro.
        rewrite list_lookup_insert_eq; try done.
    }
    iIntros (fr_saved_and_tag w) "(-> & %Hfrel_fr_saved_and_tag & %Hsaved_and_tag) Hfr Hrun".
    clear_nils.

    (* relate starting frame fr and fr_saved_and_tag *)
    pose proof (frame_rel_mask_trans_combine _ _ _ _ _ Hfrel_fr_saved Hfrel_fr_saved_and_tag) as Hfrel_fr_and_fr_saved_and_tag.
    simpl in Hfrel_fr_and_fr_saved_and_tag.

    assert (frame_rel lmask fr fr_saved_and_tag) as Hfrel_lmask_saved_and_tag.
    {
      eapply frame_rel_mask_mono; [| exact Hfrel_fr_and_fr_saved_and_tag].
      intros i [Hi_lo Hi_hi].
      split.
      + rewrite Hval_idxs_seq.
        intro Hin. apply elem_of_seq in Hin. lia.
      + unfold tag_idx. rewrite length_app. lia.
    }
    pose proof Hfrel_fr_and_fr_saved_and_tag as [_ ->].
    iDestruct (labels_interp_mono _ _ _ _ fr_saved_and_tag _ _ _ _ with "Hlabels") as "Hlabels'"; first done.
    {
      instantiate (1 := (wlmask (fe_of_context F') (wl ++ wl_save ++ [prelude.W.T_i32]))).
      intros i [Hi_lo Hi_hi].
      simpl.
      split.
      + exact Hi_lo.
      + rewrite -fe_of_context_labels.
        rewrite !length_app. simpl.
        subst fe.
        lia.
    }

    assert (Forall2 (λ (i : prelude.W.localidx) (v : value), f_locs fr_saved_and_tag !! localimm i = Some v)
      val_localidxs vs_payload) as Hfr_saved_and_tag_payload.
    {
      eapply forall2_lookup_same.
      3: done.
      - intros j Hneq. instantiate (1 := tag_idx) in Hneq.
        destruct Hfrel_fr_saved_and_tag as [-> _]; done.
      - subst val_idxs val_localidxs tag_idx.
        rewrite length_app Nat.add_assoc.
        apply map_seq_forall_localidx_neq.
    }

    iAssert
      (frame_interp rti sr se L (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_case_1 ++ wl_case_2 ++ wl_case_3 ++ wlf) fr_saved_and_tag)
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

    (* Case analysis: Is tag 0 or 1 or 2? *)

    apply lookup_lt_Some in Htag_type_lookup as Hi.
    destruct tag as [| [|[|]]]; last done.

    - (* Case: tag = 0 *)
      (* -------- Case 1 -------- *)
      rewrite (app_assoc (to_consts _)).
      iApply (cwp_seq with "[-]").
      {
        iApply (compat_case_block_success with "[] [$] [$] [$] [$] [$] [$] [$] [$] [$]").
        2: instantiate (1 := []).
        all: clear_nils.
        1, 2, 3, 4, 5, 6, 8, 9, 11, 13, 14: done.
        4: iApply "Hsem_es1".
        1: done.
        1: by rewrite length_map.
        by subst val_idxs.
      }
      iIntros (f_es_case_1 vs) "(_ & %Hlen_vs & %Hfrel_new & Hframe & %os & %θ' & Hos & Hvs & Hrt) Hfr Hrun".

      (* -------- Case 2 -------- *)
      rewrite (app_assoc (to_consts _)).
      iApply (cwp_seq with "[Hfr Hrun]").
      {
        iApply (compat_case_block_fail with "[$] [$]").
        2, 3, 4, 5, 6, 7, 8, 9, 10: done.
        rewrite -Hsaved_and_tag.
        destruct Hfrel_new as [Hmask _].
        symmetry.
        apply Hmask.
        subst tag_idx fe.
        unfold wlmask.
        repeat rewrite length_app.
        rewrite -fe_of_context_labels.
        lias.
      }
      iIntros (??) "(-> & ->) Hfr Hrun".

      (* -------- Case 3 -------- *)
      iApply (cwp_wand with "[Hfr Hrun]").
      {
        iApply (compat_case_block_fail with "[$] [$]").
        2, 3, 4, 5, 6, 8, 9, 10: done.
        2: done.
        rewrite -Hsaved_and_tag.
        destruct Hfrel_new as [Hmask _].
        symmetry.
        apply Hmask.
        subst tag_idx fe.
        unfold wlmask.
        repeat rewrite length_app.
        rewrite -fe_of_context_labels.
        lias.
      }
      iIntros (??) "(-> & ->)".
      iFrame.
      iPureIntro.
      rewrite -fe_of_context_labels in Hfrel_new.
      unfold lmask.
      eapply frame_rel_trans.
      + eapply frame_rel_mask_mono; [| exact Hfrel_lmask_saved_and_tag].
        intros i [Hi_lo Hi_hi]. unfold lmask, wlmask. split; exact Hi_lo || exact Hi_hi.
      + eapply frame_rel_wlmask_mono; [| exact Hfrel_new].
        rewrite length_app. lia.

    - (* Case: tag = 1 *)
      (* -------- Case 1 -------- *)
      rewrite (app_assoc (to_consts _)).
      iApply (cwp_seq with "[Hfr Hrun]").
      {
        iApply (compat_case_block_fail with "[$] [$]").
        7: by instantiate (1 := 1).
        2: instantiate (1 := []).
        1, 2, 3, 4, 5, 6, 7, 8: done.
        by rewrite length_map.
      }
      iIntros (??) "(-> & ->) Hfr Hrun".

      iDestruct (labels_interp_mono _ _ _ _ fr_saved_and_tag _ _ _ _ with "Hlabels") as "Hlabels'''"; first done.
      {
        instantiate (1 := (wlmask (fe_of_context F') (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_case_1))).
        intros i [Hi_lo Hi_hi].
        simpl.
        split.
        + exact Hi_lo.
        + rewrite -fe_of_context_labels.
          rewrite !length_app. simpl.
          subst fe.
          lia.
      }

      (* -------- Case 2 -------- *)
      rewrite (app_assoc (to_consts _)).
      iApply (cwp_seq with "[-]").
      {
        iApply (compat_case_block_success with "[] [$] [$] [$] [$] [$] [$] [$] [$] [$]").
        1, 2, 3, 4, 5, 6, 8, 9, 11, 13, 14: done.
        4: iApply "Hsem_es2".
        1: done.
        1: by rewrite length_map.
        by subst val_idxs.
      }
      iIntros (f_es_case_2 vs) "(_ & %Hlen_vs & %Hfrel_new & Hframe & %os & %θ' & Hos & Hvs & Hrt) Hfr Hrun".

      (* -------- Case 3 -------- *)
      iApply (cwp_wand with "[Hfr Hrun]").
      {
        iApply (compat_case_block_fail with "[$] [$]").
        2, 3, 4, 5, 6, 8, 9, 10: done.
        2: done.
        rewrite -Hsaved_and_tag.
        destruct Hfrel_new as [Hmask _].
        symmetry.
        apply Hmask.
        subst tag_idx fe.
        unfold wlmask.
        repeat rewrite length_app.
        rewrite -fe_of_context_labels.
        lias.
      }
      iIntros (??) "(-> & ->)".
      iFrame.
      iPureIntro.
      rewrite -fe_of_context_labels in Hfrel_new.
      unfold lmask.
      eapply frame_rel_trans.
      + eapply frame_rel_mask_mono; [| exact Hfrel_lmask_saved_and_tag].
        intros i [Hi_lo Hi_hi]. unfold lmask, wlmask. split; exact Hi_lo || exact Hi_hi.
      + eapply frame_rel_wlmask_mono; [| exact Hfrel_new].
        rewrite length_app. lia.

    - (* Case: tag = 2 *)
      (* -------- Case 1 -------- *)
      rewrite (app_assoc (to_consts _)).
      iApply (cwp_seq with "[Hfr Hrun]").
      {
        iApply (compat_case_block_fail with "[$] [$]").
        7: by instantiate (1 := 2).
        2: instantiate (1 := []).
        1, 2, 3, 4, 5, 6, 7, 8: done.
        by rewrite length_map.
      }
      iIntros (??) "(-> & ->) Hfr Hrun".

      (* -------- Case 2 -------- *)
      rewrite (app_assoc (to_consts _)).
      iApply (cwp_seq with "[Hfr Hrun]").
      {
        iApply (compat_case_block_fail with "[$] [$]").
        7: by instantiate (1 := 2).
        2: instantiate (1 := wl_case_1).
        1, 2, 3, 4, 5, 6, 7, 8: done.
        by rewrite length_map.
      }
      iIntros (??) "(-> & ->) Hfr Hrun".

      iDestruct (labels_interp_mono _ _ _ _ fr_saved_and_tag _ _ _ _ with "Hlabels") as "Hlabels'''"; first done.
      {
        instantiate (1 := (wlmask (fe_of_context F') (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_case_1 ++ wl_case_2))).
        intros i [Hi_lo Hi_hi].
        simpl.
        split.
        + exact Hi_lo.
        + rewrite -fe_of_context_labels.
          rewrite !length_app. simpl.
          subst fe.
          lia.
      }

      (* -------- Case 3 -------- *)
      iApply (cwp_wand with "[-]").
      {
        iApply (compat_case_block_success with "[] [$] [$] [$] [$] [$] [$] [$] [$] [$]").
        1, 2, 3, 4, 5, 6, 8, 9, 11, 13, 14: done.
        4: iApply "Hsem_es3".
        1: done.
        1: by rewrite length_map.
        by subst val_idxs.
      }
      iIntros (f_es_case_3 vs) "(_ & %Hlen_vs & %Hfrel_new & Hframe & %os & %θ' & Hos & Hvs & Hrt)".
      iFrame.
      iPureIntro.
      rewrite -fe_of_context_labels in Hfrel_new.
      unfold lmask.
      eapply frame_rel_trans.
      + eapply frame_rel_mask_mono; [| exact Hfrel_lmask_saved_and_tag].
        intros i [Hi_lo Hi_hi]. unfold lmask, wlmask. split; exact Hi_lo || exact Hi_hi.
      + eapply frame_rel_wlmask_mono; [| exact Hfrel_new].
        rewrite length_app. lia.
  Admitted.


  Lemma compile_cases_app fe ess1 ess2 :
    (fix compile_cases fe ess := match ess with
     | [] => [] | es :: ess' => mapM_ (compile_instr mr fe) es :: compile_cases fe ess'
     end) fe (ess1 ++ ess2) =
    (fix compile_cases fe ess := match ess with
     | [] => [] | es :: ess' => mapM_ (compile_instr mr fe) es :: compile_cases fe ess'
     end) fe ess1 ++
    (fix compile_cases fe ess := match ess with
     | [] => [] | es :: ess' => mapM_ (compile_instr mr fe) es :: compile_cases fe ess'
     end) fe ess2.
  Proof.
    induction ess1; simpl; [done | by rewrite IHess1].
  Qed.

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
  Proof.
    intros fe WT WL lmask F' Ψ Hforall Hok Hcg.
    subst Ψ.
    cbn [compile_instr] in Hcg.
    destruct κ as [ ρ rf | ]; last inversion Hcg.
    destruct ρ  as [ | ρs_sum | | ]; try done.
    destruct τs' as [ | τ_res τs' ]; first done.
    destruct τs'; last done.

    inv_cg_bind Hcg wl_ret ?wt ?wt ?wl ?wl ?es ?es Hres_type Hcg.
    inv_cg_try_option Hres_type; subst.

    destruct (Wasm_int.Int32.modulus <? length ρs_sum)%Z eqn:Hcmp; first inversion Hcg.
    inv_cg_bind Hcg ?units ?wt ?wt ?wl ?wl ?es es_case1 Hret Hcg.
    inv_cg_ret Hret; subst.
    apply Z.ltb_ge in Hcmp.

    inv_cg_bind Hcg ρs_atom ?wt ?wt ?wl ?wl ?es ?es Hιs Hcg.
    inv_cg_try_option Hιs; subst.
    inv_cg_bind Hcg val_localidxs wt_save ?wt wl_save ?wl es_save ?es Hsave Hcg.
    repeat rewrite app_nil_r in Hsave.

    (* Save tag *)
    inv_cg_bind Hcg tag_localidx ?wt ?wt ?wl ?wl ?es ?es HsaveTag Hcg.
    unfold save_stack1 in HsaveTag.
    inv_cg_bind HsaveTag ?tl ?wt ?wt ?wl ?wl ?es ?es Halloc_tag HsaveTag.
    apply wp_wlalloc in Halloc_tag as [Hlocal_tag_idx [-> [-> ->]]].
    inv_cg_bind HsaveTag [] ?wt ?wt ?wl ?wl es_set_tag ?es HsetTag HretTagIdx.
    inv_cg_emit HsetTag; subst.
    inv_cg_ret HretTagIdx; subst.

    clear_nils.
    set (tag_idx := (fe_wlocal_offset fe + length (wl ++ wl_save))).
    set (tag_localidx := Mk_localidx tag_idx).
    replace (Mk_localidx (fe_wlocal_offset fe + length (wl ++ wl_save))) with tag_localidx in *; last done.

    (* Put default result values on stack *)
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_create_defaults ?es Hcreate_defaults Hcg.
    apply run_codegen_create_defaults in Hcreate_defaults as H.
    destruct H as (_ & -> & -> & _).

    subst WT WL.
    clear_nils.
    simplify_eq.

    (* Iris Proof *)
    iIntros (? ? ? ? ? ? ? ?) "%Hsem %Hhas_values #Hinst #Hlabels #Hreturn Hrvs Hvs Hframe Hrt Hfr Hrun".

    (* Our values are in the value interpretation for our specific SumT *)
    (* This means that the values represent the tag and the payload. *)
    iDestruct (values_interp_one_eq with "Hvs") as "Hvs".
    iDestruct (value_interp_eq with "Hvs") as "Hvs".
    unfold value_interp0, value_se_interp0.
    iDestruct "Hvs" as "(%κ & %Hkind_sum & Hskind_as_type & Hsum_interp)".
    (*unfold type_skind in Hkind_sum.*)
    iDestruct "Hsum_interp" as (tag os' os_tag τ_tag ιs ιs_tag ixs  HSAtoms Htag_type_lookup Htag_type_arep Heval_rep_tail Hinject_sum_arep Hos'_ixs) "Hvalue_interp_os_i".
    simplify_eq.

    apply lookup_lt_Some in Htag_type_lookup as Htag_size_bound.
    assert (length τs = length ρs_sum) as Htyp_rep_len.
    {
      inversion Hok; subst.
      unfold has_mono_rep_instr in H.
      destruct H as [H _].
      simpl in H.
      rewrite Forall_singleton in H.
      inversion H; subst.
      inversion H1; subst.
      apply has_kind_SumT_inv in H3 as (rf' & HF2).
      by eapply Forall2_length.
    }
    assert (tag < Wasm_int.Int32.modulus)%Z as Htag_in_i32_bound.
    { rewrite Htyp_rep_len in Htag_size_bound. eapply Z.lt_le_trans; last done. by apply Nat2Z.inj_lt. }

    iDestruct (big_sepL2_length with "Hrvs") as "%Hlen".
    destruct vs as [|v_tag vs_payload]; first inversion Hlen.
    clear Hlen.
    iDestruct (atoms_interp_cons with "Hrvs") as "[-> Hatoms_interp_payload]".

    iPoseProof (frame_interp_wl_interp with "Hframe") as "%Hwl"; first done.
    rewrite list_extra.cons_app in Hhas_values.
    apply has_values_app_inv in Hhas_values as (e_tag & es_payload & -> & Hhv_tag & Hhvs_payload).

    (* tag is an index into τs, so we must have: *)
    (* τs = τs_pre ++ [τ_tag] ++ τs_post *)
    (* ess = ess_pre ++ [es_tag] ++ ess_post *)
    apply list_elem_of_split_length in Htag_type_lookup as H.
    destruct H as (τs_pre & τs_post & Hτs_eq & Htag_len).

    rewrite Hτs_eq in Hforall.
    apply Forall2_app_inv_l in Hforall as
      (ess_pre & ess_rest & Hforall_pre & Hforall_rest & ->).
    apply Forall2_cons_inv_l in Hforall_rest as
      (es_tag & ess_post & Hforall_tag & Hforall_post & ->).


    (* save payload *)
    rewrite (app_assoc (e_tag ++ _)).
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      rewrite <- (app_assoc e_tag).
      instantiate (1 := λ fr' vs, (
        ∃ val_idxs,
        ⌜vs = [VAL_int32 (Wasm_int.Int32.repr tag)]⌝ ∗
        ⌜frame_rel (λ i, i ∉ val_idxs) fr fr'⌝ ∗
        ⌜Forall2 (fun i v => f_locs fr' !! localimm i = Some v) val_localidxs vs_payload⌝ ∗
        ⌜val_idxs = seq (fe_wlocal_offset fe + length wl) (length wl_save)⌝ ∗
        ⌜val_localidxs = map prelude.W.Mk_localidx val_idxs⌝
        )%I).
      iApply cwp_val_app; first done.
      eapply cwp_save_stack_w in Hsave; eauto.
      + destruct Hsave as (-> & -> & -> & Hsave).
        iApply (Hsave with "[$] [$]").
        iIntros (f' [Hfsame Hfchanged]).
        unfold fvs_combine.
        auto.
      + admit. (* easy pure conseqeunce of value_interp and
      rep_values_interp, should be proved above the first wp_seq
      rule *)
    }
    iIntros (fr_saved w) "(%val_idxs & -> & %Hfrel_fr_saved & %Hsaved & %Hval_idxs_seq & %Hval_localidxs) Hfr Hrun".
    iAssert
    (frame_interp rti sr se L (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl1 ++ wlf) fr_saved)
      with "[Hframe]" as "Hframe_saved".
    { admit. } (* TODO: Not really sure how to prove this. Definitely need helper lemma *)

    (* edestruct (util.nths_error_exists val_localidxs case_i_val_idxs vs_payload case_i_sum_locals (Forall2_length _ _ _ Hsaved)) as [case_i_vs_payload Hnerr_payload_ci]; try done. *)

    iDestruct (frame_interp_wl_interp with "Hframe_saved") as "%Hwl_saved"; first done.
    pose proof (interp_wl_length _ _ _ Hwl_saved) as Hfr_saved_locs_len.

    assert (tag_idx < length (f_locs fr_saved)) as Htag_in_fr_saved.
    {
      subst tag_idx.
      simpl.
      eapply Nat.lt_le_trans; last done.
      - rewrite app_assoc.
        subst fe.
        instantiate (1 := F).
        repeat rewrite length_app.
        lias.
    }

    (* Store tag *)
    rewrite (app_assoc (map _ _)).
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      instantiate (1 := λ fr' vs, (
        ⌜vs = []⌝ ∗
        ⌜frame_rel (λ j, j ≠ tag_idx) fr_saved fr'⌝ ∗
        ⌜f_locs fr' !! tag_idx = Some (VAL_int32 (Wasm_int.Int32.repr tag))⌝
        )%I).
      iApply (cwp_local_set with "[] [$] [$]"); first done.
      iSplit; first done.
      iSplit.
      - iPureIntro.
        split; last done.
        intros j Hneq.
        simpl.
        rewrite list_lookup_insert_ne; [reflexivity | lia].
      - iSimpl.
        iPureIntro.
        rewrite list_lookup_insert_eq; try done.
    }
    iIntros (fr_saved_and_tag w) "(-> & %Hfrel_fr_saved_and_tag & %Hsaved_and_tag) Hfr Hrun".
    clear_nils.

    (* relate starting frame fr and fr_saved_and_tag *)
    pose proof (frame_rel_mask_trans_combine _ _ _ _ _ Hfrel_fr_saved Hfrel_fr_saved_and_tag) as Hfrel_fr_and_fr_saved_and_tag.
    simpl in Hfrel_fr_and_fr_saved_and_tag.

    assert (frame_rel lmask fr fr_saved_and_tag) as Hfrel_lmask_saved_and_tag.
    {
      eapply frame_rel_mask_mono; [| exact Hfrel_fr_and_fr_saved_and_tag].
      intros i [Hi_lo Hi_hi].
      split.
      + rewrite Hval_idxs_seq.
        intro Hin. apply elem_of_seq in Hin. lia.
      + unfold tag_idx. rewrite length_app. lia.
    }
    pose proof Hfrel_fr_and_fr_saved_and_tag as [_ ->].
    iDestruct (labels_interp_mono _ _ _ _ fr_saved_and_tag _ _ _ _ with "Hlabels") as "Hlabels'"; first done.
    {
      instantiate (1 := (wlmask (fe_of_context F') (wl ++ wl_save ++ [prelude.W.T_i32]))).
      intros i [Hi_lo Hi_hi].
      simpl.
      split.
      + exact Hi_lo.
      + rewrite -fe_of_context_labels.
        rewrite !length_app. simpl.
        subst fe.
        lia.
    }

    assert (Forall2 (λ (i : prelude.W.localidx) (v : value), f_locs fr_saved_and_tag !! localimm i = Some v)
      val_localidxs vs_payload) as Hfr_saved_and_tag_payload.
    {
      eapply forall2_lookup_same.
      3: done.
      - intros j Hneq. instantiate (1 := tag_idx) in Hneq.
        destruct Hfrel_fr_saved_and_tag as [-> _]; done.
      - subst val_idxs val_localidxs tag_idx.
        rewrite length_app Nat.add_assoc.
        apply map_seq_forall_localidx_neq.
    }

    iAssert
    (frame_interp rti sr se L (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl1 ++ wlf) fr_saved_and_tag)
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

    rewrite compile_cases_app in Hcg.
    rewrite map_app in Hcg.
    rewrite map_cons in Hcg.
    rewrite separate1 in Hcg.
    apply run_codegen_case_blocks_blocks_app in Hcg as (wt_pre & wt_tag & wt_post & wl_pre & wl_tag & wl_post & es_pre & es_tag_cg & es_post & Hcg_pre & Hcg_tag & Hcg_post & -> & -> & ->).

    (* (* Case blocks *) *)
    (* cbv [map length seq zip Datatypes.uncurry] in Hcg. *)
    (**)
    (* clear_nils. *)
    (**)
    (* inv_cg_bind Hcg ?units ?wt ?wt ?wl ?wl ?es es_case_i Hcases Hret. *)
    (* inv_cg_ret Hret; subst. *)
    (**)
    (* (* Case es_i *) *)
    (* inv_cg_bind Hcases [] ?wt ?wt ?wl ?wl ?es es_rest Hcase_es_i Hrest. *)
    (**)
    (* inv_cg_bind Hcase_es_i ?pair ?wt ?wt ?wl ?wl ?es ?es Hcase_es_i Hcase_es_i_block. *)
    (* destruct pair, u. *)
    (* inv_cg_emit Hcase_es_i_block; subst. *)
    (* apply run_codegen_capture in Hcase_es_i as [Hcase_es_i ->]. *)
    (**)
    (* inv_cg_bind Hcase_es_i [] ?wt ?wt ?wl ?wl ?es ?es Hget_tag Hcase_es_i. *)
    (* inv_cg_emit Hget_tag; subst. *)
    (**)
    (* inv_cg_bind Hcase_es_i [] ?wt ?wt ?wl ?wl ?es ?es Htag0 Hcase_es_i. *)
    (* inv_cg_emit Htag0; subst. *)
    (**)
    (* inv_cg_bind Hcase_es_i [] ?wt ?wt ?wl ?wl ?es ?es Hcompare_tag Hcase_es_i. *)
    (* inv_cg_emit Hcompare_tag; subst. *)
    (**)
    (* inv_cg_bind Hcase_es_i [] ?wt ?wt ?wl ?wl ?es ?es Hbr_case Hcase_es_i. *)
    (* inv_cg_emit Hbr_case; subst. *)
    (**)
    (* inv_cg_bind Hcase_es_i [] ?wt ?wt ?wl ?wl es_drop_i ?es Hdrop_consts_i Hcase_es_i. *)
    (* apply run_codegen_drop_consts in Hdrop_consts_i as H. *)
    (* destruct H as (_ & -> & -> & _). *)
    (**)
    (* inv_cg_bind Hcase_es_i ρ_casei ?wt ?wt ?wl ?wl ?es ?es Hlookup Hcase_es_i. *)
    (* inv_cg_try_option Hlookup; subst. *)
    (**)
    (* inv_cg_bind Hcase_es_i case_i_sum_locals ?wt ?wt ?wl ?wl ?es ?es Hinject Hcase_es_i. *)
    (* inv_cg_try_option Hinject; subst. *)
    (**)
    (* inv_cg_bind Hcase_es_i [] ?wt wt_case_i ?wl wl_case_i ?es es_case_i Hget_locals_i Hcase_es_i. *)
    (* inv_cg_bind Hget_locals_i case_i_val_idxs ?wt wt_get_locals_i ?wl wl_get_locals_i ?es es_get_locals_i Hnths_error Hget_locals_i. *)
    (* inv_cg_try_option Hnths_error; subst. *)
    (**)
    (* destruct (run_codegen_get_locals _ _ _ _ _ _ _ Hget_locals_i) as ([] & -> & ->). *)
    (**)
    (* (* clean up *) *)
    (* subst WT WL. *)
    (* clear_nils. *)
    (* simplify_eq. *)
    (**)
    (**)
    (* (* save payload *) *)
    (* rewrite (app_assoc (e_tag ++ _)). *)
    (* iApply (cwp_seq with "[Hfr Hrun]"). *)
    (* { *)
    (*   rewrite <- (app_assoc e_tag). *)
    (*   instantiate (1 := λ fr' vs, ( *)
    (*     ∃ val_idxs, *)
    (*     ⌜vs = [VAL_int32 (Wasm_int.Int32.repr tag)]⌝ ∗ *)
    (*     ⌜frame_rel (λ i, i ∉ val_idxs) fr fr'⌝ ∗ *)
    (*     ⌜Forall2 (fun i v => f_locs fr' !! localimm i = Some v) val_localidxs vs_payload⌝ ∗ *)
    (*     ⌜val_idxs = seq (fe_wlocal_offset fe + length wl) (length wl_save)⌝ ∗ *)
    (*     ⌜val_localidxs = map prelude.W.Mk_localidx val_idxs⌝ *)
    (*     )%I). *)
    (*   iApply cwp_val_app; first done. *)
    (*   eapply cwp_save_stack_w in Hsave; eauto. *)
    (*   + destruct Hsave as (-> & -> & -> & Hsave). *)
    (*     iApply (Hsave with "[$] [$]"). *)
    (*     iIntros (f' [Hfsame Hfchanged]). *)
    (*     unfold fvs_combine. *)
    (*     auto. *)
    (*   + admit. (* easy pure conseqeunce of value_interp and *)
    (*   rep_values_interp, should be proved above the first wp_seq *)
    (*   rule *) *)
    (* } *)
    (* iIntros (fr_saved w) "(%val_idxs & -> & %Hfrel_fr_saved & %Hsaved & %Hval_idxs_seq & %Hval_localidxs) Hfr Hrun". *)
    (* iAssert *)
    (* (frame_interp rti sr se L (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_case_i ++ wl2 ++ wlf) fr_saved) *)
    (*   with "[Hframe]" as "Hframe_saved". *)
    (* { admit. } (* TODO: Not really sure how to prove this. Definitely need helper lemma *) *)
    (**)
    (* edestruct (util.nths_error_exists val_localidxs case_i_val_idxs vs_payload case_i_sum_locals (Forall2_length _ _ _ Hsaved)) as [case_i_vs_payload Hnerr_payload_ci]; try done. *)
    (**)
    (* iDestruct (frame_interp_wl_interp with "Hframe_saved") as "%Hwl_saved"; first done. *)
    (* pose proof (interp_wl_length _ _ _ Hwl_saved) as Hfr_saved_locs_len. *)
    (**)
    (* assert (tag_idx < length (f_locs fr_saved)) as Htag_in_fr_saved. *)
    (* { *)
    (*   subst tag_idx. *)
    (*   simpl. *)
    (*   eapply Nat.lt_le_trans; last done. *)
    (*   - rewrite app_assoc. *)
    (*     subst fe. *)
    (*     instantiate (1 := F). *)
    (*     repeat rewrite length_app. *)
    (*     lias. *)
    (* } *)
    (**)
    (* (* Store tag *) *)
    (* rewrite (app_assoc (map _ _)). *)
    (* iApply (cwp_seq with "[Hfr Hrun]"). *)
    (* { *)
    (*   instantiate (1 := λ fr' vs, ( *)
    (*     ⌜vs = []⌝ ∗ *)
    (*     ⌜frame_rel (λ j, j ≠ tag_idx) fr_saved fr'⌝ ∗ *)
    (*     ⌜f_locs fr' !! tag_idx = Some (VAL_int32 (Wasm_int.Int32.repr tag))⌝ *)
    (*     )%I). *)
    (*   iApply (cwp_local_set with "[] [$] [$]"); first done. *)
    (*   iSplit; first done. *)
    (*   iSplit. *)
    (*   - iPureIntro. *)
    (*     split; last done. *)
    (*     intros j Hneq. *)
    (*     simpl. *)
    (*     rewrite list_lookup_insert_ne; [reflexivity | lia]. *)
    (*   - iSimpl. *)
    (*     iPureIntro. *)
    (*     rewrite list_lookup_insert_eq; try done. *)
    (* } *)
    (* iIntros (fr_saved_and_tag w) "(-> & %Hfrel_fr_saved_and_tag & %Hsaved_and_tag) Hfr Hrun". *)
    (* clear_nils. *)
    (**)
    (* (* relate starting frame fr and fr_saved_and_tag *) *)
    (* pose proof (frame_rel_mask_trans_combine _ _ _ _ _ Hfrel_fr_saved Hfrel_fr_saved_and_tag) as Hfrel_fr_and_fr_saved_and_tag. *)
    (* simpl in Hfrel_fr_and_fr_saved_and_tag. *)
    (**)
    (* assert (frame_rel lmask fr fr_saved_and_tag) as Hfrel_lmask_saved_and_tag. *)
    (* { *)
    (*   eapply frame_rel_mask_mono; [| exact Hfrel_fr_and_fr_saved_and_tag]. *)
    (*   intros i [Hi_lo Hi_hi]. *)
    (*   split. *)
    (*   + rewrite Hval_idxs_seq. *)
    (*     intro Hin. apply elem_of_seq in Hin. lia. *)
    (*   + unfold tag_idx. rewrite length_app. lia. *)
    (* } *)
    (* pose proof Hfrel_fr_and_fr_saved_and_tag as [_ ->]. *)
    (* iDestruct (labels_interp_mono _ _ _ _ fr_saved_and_tag _ _ _ _ with "Hlabels") as "Hlabels'"; first done. *)
    (* { *)
    (*   instantiate (1 := (wlmask (fe_of_context F') (wl ++ wl_save ++ [prelude.W.T_i32]))). *)
    (*   intros i [Hi_lo Hi_hi]. *)
    (*   simpl. *)
    (*   split. *)
    (*   + exact Hi_lo. *)
    (*   + rewrite -fe_of_context_labels. *)
    (*     rewrite !length_app. simpl. *)
    (*     subst fe. *)
    (*     lia. *)
    (* } *)
    (**)
    (* assert (Forall2 (λ (i : prelude.W.localidx) (v : value), f_locs fr_saved_and_tag !! localimm i = Some v) *)
    (*   val_localidxs vs_payload) as Hfr_saved_and_tag_payload. *)
    (* { *)
    (*   eapply forall2_lookup_same. *)
    (*   3: done. *)
    (*   - intros j Hneq. instantiate (1 := tag_idx) in Hneq. *)
    (*     destruct Hfrel_fr_saved_and_tag as [-> _]; done. *)
    (*   - subst val_idxs val_localidxs tag_idx. *)
    (*     rewrite length_app Nat.add_assoc. *)
    (*     apply map_seq_forall_localidx_neq. *)
    (* } *)
    (**)
    (* iAssert *)
    (* (frame_interp rti sr se L (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_case_i ++ wl2 ++ wlf) fr_saved_and_tag) *)
    (*   with "[Hframe_saved]" as "Hframe_saved_and_tag". *)
    (* { admit. } (* TODO: Not really sure how to prove this. Definitely need helper lemma *) *)
    (**)
    (* (* Create defaults *) *)
    (* iApply (cwp_seq with "[Hfr Hrun]"). *)
    (* { *)
    (*   eapply cwp_create_defaults in Hcreate_defaults as (_ & _ & _ & Hcreate_defaults). *)
    (*   iDestruct (Hcreate_defaults with "[$] [$] []") as "Hcreate_defaults". *)
    (*   { *)
    (*     by instantiate (1 := λ f vs, (⌜f = fr_saved_and_tag⌝ ∗ ⌜vs = (map default_of_value_type wl_ret)⌝)%I). *)
    (*   } *)
    (*   iApply "Hcreate_defaults". *)
    (* } *)
    (* iIntros (??) "[-> ->] Hfr Hrun". *)
    (**)
    (* (* Case analysis: Is tag 0  *) *)
    (**)
    (* apply lookup_lt_Some in Htag_type_lookup as Hi. *)
    (* destruct tag as [| [|[|]]]; last done. *)
    (**)
    (* - (* Case: tag = 0 *) *)
    (*   (* -------- Case 1 -------- *) *)
    (*   rewrite (app_assoc (to_consts _)). *)
    (*   iApply (cwp_seq with "[-]"). *)
    (*   { *)
    (*     iApply (compat_case_block_success with "[] [$] [$] [$] [$] [$] [$] [$] [$] [$]"). *)
    (*     2: instantiate (1 := []). *)
    (*     all: clear_nils. *)
    (*     1, 2, 3, 4, 5, 6, 8, 9, 11, 13, 14: done. *)
    (*     4: iApply "Hsem_es1". *)
    (*     1: done. *)
    (*     1: by rewrite length_map. *)
    (*     by subst val_idxs. *)
    (*   } *)
    (*   iIntros (f_es_case_1 vs) "(_ & %Hlen_vs & %Hfrel_new & Hframe & %os & %θ' & Hos & Hvs & Hrt) Hfr Hrun". *)
    (**)
    (*   (* -------- Case 2 -------- *) *)
    (*   rewrite (app_assoc (to_consts _)). *)
    (*   iApply (cwp_seq with "[Hfr Hrun]"). *)
    (*   { *)
    (*     iApply (compat_case_block_fail with "[$] [$]"). *)
    (*     2, 3, 4, 5, 6, 7, 8, 9, 10: done. *)
    (*     rewrite -Hsaved_and_tag. *)
    (*     destruct Hfrel_new as [Hmask _]. *)
    (*     symmetry. *)
    (*     apply Hmask. *)
    (*     subst tag_idx fe. *)
    (*     unfold wlmask. *)
    (*     repeat rewrite length_app. *)
    (*     rewrite -fe_of_context_labels. *)
    (*     lias. *)
    (*   } *)
    (*   iIntros (??) "(-> & ->) Hfr Hrun". *)
    (**)
    (*   (* -------- Case 3 -------- *) *)
    (*   iApply (cwp_wand with "[Hfr Hrun]"). *)
    (*   { *)
    (*     iApply (compat_case_block_fail with "[$] [$]"). *)
    (*     2, 3, 4, 5, 6, 8, 9, 10: done. *)
    (*     2: done. *)
    (*     rewrite -Hsaved_and_tag. *)
    (*     destruct Hfrel_new as [Hmask _]. *)
    (*     symmetry. *)
    (*     apply Hmask. *)
    (*     subst tag_idx fe. *)
    (*     unfold wlmask. *)
    (*     repeat rewrite length_app. *)
    (*     rewrite -fe_of_context_labels. *)
    (*     lias. *)
    (*   } *)
    (*   iIntros (??) "(-> & ->)". *)
    (*   iFrame. *)
    (*   iPureIntro. *)
    (*   rewrite -fe_of_context_labels in Hfrel_new. *)
    (*   unfold lmask. *)
    (*   eapply frame_rel_trans. *)
    (*   + eapply frame_rel_mask_mono; [| exact Hfrel_lmask_saved_and_tag]. *)
    (*     intros i [Hi_lo Hi_hi]. unfold lmask, wlmask. split; exact Hi_lo || exact Hi_hi. *)
    (*   + eapply frame_rel_wlmask_mono; [| exact Hfrel_new]. *)
    (*     rewrite length_app. lia. *)
    (**)
    (* - (* Case: tag = 1 *) *)
    (*   (* -------- Case 1 -------- *) *)
    (*   rewrite (app_assoc (to_consts _)). *)
    (*   iApply (cwp_seq with "[Hfr Hrun]"). *)
    (*   { *)
    (*     iApply (compat_case_block_fail with "[$] [$]"). *)
    (*     7: by instantiate (1 := 1). *)
    (*     2: instantiate (1 := []). *)
    (*     1, 2, 3, 4, 5, 6, 7, 8: done. *)
    (*     by rewrite length_map. *)
    (*   } *)
    (*   iIntros (??) "(-> & ->) Hfr Hrun". *)
    (**)
    (*   iDestruct (labels_interp_mono _ _ _ _ fr_saved_and_tag _ _ _ _ with "Hlabels") as "Hlabels'''"; first done. *)
    (*   { *)
    (*     instantiate (1 := (wlmask (fe_of_context F') (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_case_1))). *)
    (*     intros i [Hi_lo Hi_hi]. *)
    (*     simpl. *)
    (*     split. *)
    (*     + exact Hi_lo. *)
    (*     + rewrite -fe_of_context_labels. *)
    (*       rewrite !length_app. simpl. *)
    (*       subst fe. *)
    (*       lia. *)
    (*   } *)
    (**)
    (*   (* -------- Case 2 -------- *) *)
    (*   rewrite (app_assoc (to_consts _)). *)
    (*   iApply (cwp_seq with "[-]"). *)
    (*   { *)
    (*     iApply (compat_case_block_success with "[] [$] [$] [$] [$] [$] [$] [$] [$] [$]"). *)
    (*     1, 2, 3, 4, 5, 6, 8, 9, 11, 13, 14: done. *)
    (*     4: iApply "Hsem_es2". *)
    (*     1: done. *)
    (*     1: by rewrite length_map. *)
    (*     by subst val_idxs. *)
    (*   } *)
    (*   iIntros (f_es_case_2 vs) "(_ & %Hlen_vs & %Hfrel_new & Hframe & %os & %θ' & Hos & Hvs & Hrt) Hfr Hrun". *)
    (**)
    (*   (* -------- Case 3 -------- *) *)
    (*   iApply (cwp_wand with "[Hfr Hrun]"). *)
    (*   { *)
    (*     iApply (compat_case_block_fail with "[$] [$]"). *)
    (*     2, 3, 4, 5, 6, 8, 9, 10: done. *)
    (*     2: done. *)
    (*     rewrite -Hsaved_and_tag. *)
    (*     destruct Hfrel_new as [Hmask _]. *)
    (*     symmetry. *)
    (*     apply Hmask. *)
    (*     subst tag_idx fe. *)
    (*     unfold wlmask. *)
    (*     repeat rewrite length_app. *)
    (*     rewrite -fe_of_context_labels. *)
    (*     lias. *)
    (*   } *)
    (*   iIntros (??) "(-> & ->)". *)
    (*   iFrame. *)
    (*   iPureIntro. *)
    (*   rewrite -fe_of_context_labels in Hfrel_new. *)
    (*   unfold lmask. *)
    (*   eapply frame_rel_trans. *)
    (*   + eapply frame_rel_mask_mono; [| exact Hfrel_lmask_saved_and_tag]. *)
    (*     intros i [Hi_lo Hi_hi]. unfold lmask, wlmask. split; exact Hi_lo || exact Hi_hi. *)
    (*   + eapply frame_rel_wlmask_mono; [| exact Hfrel_new]. *)
    (*     rewrite length_app. lia. *)
    (**)
    (* - (* Case: tag = 2 *) *)
    (*   (* -------- Case 1 -------- *) *)
    (*   rewrite (app_assoc (to_consts _)). *)
    (*   iApply (cwp_seq with "[Hfr Hrun]"). *)
    (*   { *)
    (*     iApply (compat_case_block_fail with "[$] [$]"). *)
    (*     7: by instantiate (1 := 2). *)
    (*     2: instantiate (1 := []). *)
    (*     1, 2, 3, 4, 5, 6, 7, 8: done. *)
    (*     by rewrite length_map. *)
    (*   } *)
    (*   iIntros (??) "(-> & ->) Hfr Hrun". *)
    (**)
    (*   (* -------- Case 2 -------- *) *)
    (*   rewrite (app_assoc (to_consts _)). *)
    (*   iApply (cwp_seq with "[Hfr Hrun]"). *)
    (*   { *)
    (*     iApply (compat_case_block_fail with "[$] [$]"). *)
    (*     7: by instantiate (1 := 2). *)
    (*     2: instantiate (1 := wl_case_1). *)
    (*     1, 2, 3, 4, 5, 6, 7, 8: done. *)
    (*     by rewrite length_map. *)
    (*   } *)
    (*   iIntros (??) "(-> & ->) Hfr Hrun". *)
    (**)
    (*   iDestruct (labels_interp_mono _ _ _ _ fr_saved_and_tag _ _ _ _ with "Hlabels") as "Hlabels'''"; first done. *)
    (*   { *)
    (*     instantiate (1 := (wlmask (fe_of_context F') (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_case_1 ++ wl_case_2))). *)
    (*     intros i [Hi_lo Hi_hi]. *)
    (*     simpl. *)
    (*     split. *)
    (*     + exact Hi_lo. *)
    (*     + rewrite -fe_of_context_labels. *)
    (*       rewrite !length_app. simpl. *)
    (*       subst fe. *)
    (*       lia. *)
    (*   } *)
    (**)
    (*   (* -------- Case 3 -------- *) *)
    (*   iApply (cwp_wand with "[-]"). *)
    (*   { *)
    (*     iApply (compat_case_block_success with "[] [$] [$] [$] [$] [$] [$] [$] [$] [$]"). *)
    (*     1, 2, 3, 4, 5, 6, 8, 9, 11, 13, 14: done. *)
    (*     4: iApply "Hsem_es3". *)
    (*     1: done. *)
    (*     1: by rewrite length_map. *)
    (*     by subst val_idxs. *)
    (*   } *)
    (*   iIntros (f_es_case_3 vs) "(_ & %Hlen_vs & %Hfrel_new & Hframe & %os & %θ' & Hos & Hvs & Hrt)". *)
    (*   iFrame. *)
    (*   iPureIntro. *)
    (*   rewrite -fe_of_context_labels in Hfrel_new. *)
    (*   unfold lmask. *)
    (*   eapply frame_rel_trans. *)
    (*   + eapply frame_rel_mask_mono; [| exact Hfrel_lmask_saved_and_tag]. *)
    (*     intros i [Hi_lo Hi_hi]. unfold lmask, wlmask. split; exact Hi_lo || exact Hi_hi. *)
    (*   + eapply frame_rel_wlmask_mono; [| exact Hfrel_new]. *)
    (*     rewrite length_app. lia. *)
  Admitted.

End case.
