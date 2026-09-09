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

  Lemma compat_case M F L L' wt wt' wtf wl wl' wlf es' ess τs τs' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let F' := F <| fc_labels ::= cons (τs', L') |> in
    let ψ := InstrT [SumT τs] τs' in
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
    destruct τs' as [ | τ_res τs' ]; first done.
    destruct τs'; last done.
    pose proof (has_instruction_type_ok_type_ok F [SumT τs] [τ_res] L' Hok) as [Htoks_sum Htoks_res].
    apply Forall_cons_1 in Htoks_sum as [Htoks_sum' _].
    inversion Htoks_sum'; subst.
    match goal with H : Forall (type_ok F) τs |- _ => rename H into Htoks end.
    cbn [compile_instr] in Hcg.

    inv_cg_bind Hcg ρs_cg ?wt ?wt ?wl ?wl ?es ?es Hρs_cg Hcg.
    inv_cg_try_option Hρs_cg.
    rename Heq_some into Hρs_cg_eq.
    clear Heq_wt Heq_wl Heq_nil.

    (* Recover [ρs_sum]/[Hkinds] from [Hok] (as [compat_inject] does), then
       show the codegen's own [Hρs_cg_eq]-derived [ρs_cg] agrees with
       [ρs_sum] -- replacing the old strategy of destructuring the
       instruction type's embedded kind. *)
    destruct Hok as [Hmono Hok_L].
    destruct Hmono as [Hmono_Sum _].
    rewrite Forall_singleton in Hmono_Sum.
    destruct Hmono_Sum as (ρ_sum & Hρ_sum & Hmono_ρ_sum).
    inversion Hρ_sum as [F0 τ0 ρ0 ξ0 Hkind_sum0].
    subst F0 τ0 ρ0.
    pose proof Hkind_sum0 as Hkind_sum0_copy.
    inversion Hkind_sum0_copy; subst.
    match goal with
    | H : Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs _ _ |- _ => rename H into Hkinds
    end.
    rename ρs into ρs_sum.
    rename ξs into ξs_sum.
    assert (Hkinds_tk : Forall3
              (fun τ' ρ' ξ' => type_kind F.(fc_type_vars) τ' = Some (VALTYPE ρ' ξ'))
              τs ρs_sum ξs_sum).
    { eapply Forall3_impl; first exact Hkinds.
      intros τ' ρ' ξ' Hk; by apply type_kind_has_kind_Some. }
    pose proof (forall3_mapM_type_rep_val _ _ _ _ Hkinds_tk) as Hmapm_rep.
    rewrite Hρs_cg_eq in Hmapm_rep.
    apply Some_inj in Hmapm_rep as <-.
    rename ρs_cg into ρs_sum.
    clear Hkind_sum0_copy.

    inv_cg_bind Hcg wl_ret ?wt ?wt ?wl ?wl ?es ?es Hres_type Hcg.
    inv_cg_try_option Hres_type; subst.

    destruct (Wasm_int.Int32.modulus <? length ρs_sum)%Z eqn:Hcmp; first inversion Hcg.
    inv_cg_bind Hcg ?units ?wt ?wt ?wl ?wl ?es es_case1 Hret Hcg.
    inv_cg_ret Hret; subst.
    apply Z.ltb_ge in Hcmp.

    inv_cg_bind Hcg ιss ?wt ?wt ?wl ?wl ?es ?es Hιs Hcg.
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
    iIntros (? ? ? ? ? ? ? ?) "%Hsem %Hhas_values #Hinst #Hlabels #Hreturn Hrvs Hvs Hframe Hrt Hown Hfr Hrun".

    (* Our values are in the value interpretation for our specific SumT *)
    (* This means that the values represent the tag and the payload. *)
    iDestruct (values_interp_one_eq with "Hvs") as "Hvs".
    iEval (rewrite value_interp_eq) in "Hvs".
    iDestruct "Hvs" as "(%κ & %Hkind_sum & %Hskind_as_type & Hsum_interp)".

    iDestruct "Hsum_interp" as (tag os_payload off count HSAtoms Hsum_offset Hcount) "Hvalue_interp_os_tag".
    cbn in Hsum_offset.
    change (list_lookup tag (map (type_interp rti sr) τs)) with ((type_interp rti sr <$> τs) !! tag).
    rewrite list_lookup_fmap.
    destruct (τs !! tag) as [τ|] eqn:Htag_type_lookup; rewrite Htag_type_lookup; last done.
    iSimpl in "Hvalue_interp_os_tag".
    simplify_eq.

    apply lookup_lt_Some in Htag_type_lookup as Htag_size_bound.
    assert (length τs = length ρs_sum) as Htyp_rep_len
      by (by eapply Forall3_length_lm, Hkinds).
    assert (tag < Wasm_int.Int32.modulus)%Z as Htag_in_i32_bound.
    { rewrite Htyp_rep_len in Htag_size_bound. eapply Z.lt_le_trans; last done. by apply Nat2Z.inj_lt. }
    assert (length τs = length ess) as Hess_typ_len; first by eapply List.Forall2_length.

    iDestruct (big_sepL2_length with "Hrvs") as "%Hlen".
    destruct vs as [|v_tag vs_payload]; first inversion Hlen.
    clear Hlen.
    iDestruct (atoms_interp_cons with "Hrvs") as "[-> Hatoms_interp_payload]".

    iPoseProof (frame_interp_wl_interp with "Hframe") as "%Hwl".
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
    apply Forall2_length in Hforall_pre as Hess_pre_τs_pre.
    apply Forall2_length in Hforall_post as Hess_post_τs_post.
    clear Hforall_pre Hforall_post.

    (* TODO start: this could use a little cleanup + abstract into lemmas? *)
    destruct κ; last destruct Hskind_as_type as [[] _].
    unfold type_skind, eval_kind in Hkind_sum.
    apply bind_Some in Hkind_sum.
    destruct Hkind_sum as (l' & Heval & Hret).
    apply bind_Some in Hret as (ρs0 & Hρs0 & Heq).
    apply Some_inj in Heq.
    inversion Heq; subst l r.
    clear Heq.

    destruct Hskind_as_type as [Hhas_areps Href].
    apply has_areps_cons_exists in Hhas_areps as (ι_tag & ιs_payload & Heq_ιs_cons & Hhas_areps_payload & Hhas_arep_tag).
    apply bind_Some in Hcount as Hcount'.
    destruct Hcount' as [ιs_case_tag_payload' [Hlookup_eval Hcase_tag_payload_count0]].
    apply bind_Some in Hcase_tag_payload_count0 as (ιs_tag_arep & Harep_tag & Hcase_tag_payload_count).
    apply Some_inj in Hcase_tag_payload_count.

    (* Relate the semantic per-branch kind information ([l'], [ρs0], from the
       [add_skind_interp] wrapper on the SumT value) to the codegen's own
       [ρs_sum]/[ιss] (from [Hιs] via [Heq_some0]): both compute
       [mapM (type_skind_go se) τs]/[mapM (eval_rep _) ρs_sum], so by
       determinism [ρs0 = ιss]. *)
    assert (Hkinds_sk : Forall3
              (fun τ' ρ' ξ' => ∀ sκ', eval_kind se (VALTYPE ρ' ξ') = Some sκ' -> type_skind_go se τ' = Some sκ')
              τs ρs_sum ξs_sum).
    { eapply Forall3_impl; first exact Hkinds.
      intros τ' ρ' ξ' Hk sκ' Heval'.
      pose proof (type_skind_has_kind_Some F se τ' (VALTYPE ρ' ξ') sκ' Hk Hsem Heval') as Hres.
      by cbn in Hres. }
    pose proof (mapM_eval_rep_emptyenv _ _ se Heq_some0) as Hmap_eval_rep.
    pose proof (forall3_mapM_type_skind_val se _ _ _ Hkinds_sk _ Hmap_eval_rep) as Hskind_all.
    rewrite Heval in Hskind_all.
    apply Some_inj in Hskind_all.
    assert (Hlen_ιξ : length ιss = length ξs_sum).
    { pose proof (length_mapM _ _ _ Hmap_eval_rep) as H1.
      pose proof (Forall3_length_lm _ _ _ _ Hkinds) as H2.
      pose proof (Forall3_length_lr _ _ _ _ Hkinds) as H3.
      lia. }
    pose proof (mapM_skind_rep_zip _ _ Hlen_ιξ) as Hskind_rep_zip.
    rewrite Hskind_all in Hρs0.
    rewrite Hskind_rep_zip in Hρs0.
    apply Some_inj in Hρs0.
    subst ρs0.
    rename ιss into ιss_payload.
    pose proof (forall3_forall2_type_arep se F τs ρs_sum ιss_payload ξs_sum Hsem Hkinds
                  (mapM_Some_1 _ _ _ Hmap_eval_rep)) as Harep_all.
    (* TODO end *)

    iDestruct (result_type_interp_of_atoms_interp with "Hatoms_interp_payload") as "%Hres_type_vs_payload"; first done.

    (* save payload *)
    injection Heq_ιs_cons as _ Hιs_payload_eq.
    eapply cwp_save_stack_w in Hsave; eauto.
    2: { rewrite Hιs_payload_eq. by rewrite map_comp. }
    2: { by apply Is_true_true. }
    destruct Hsave as (Hval_localidxs_seq & -> & Hwl_save & Hsave).
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
      iApply (Hsave with "[$] [$]").
      iIntros (f' [Hfsame Hfchanged]).
      unfold fvs_combine.
      subst val_localidxs wl_save.
      auto.
    }
    iIntros (fr_saved w) "(%val_idxs & -> & %Hfrel_fr_saved & %Hsaved & %Hval_idxs_seq & %Hval_localidxs) Hfr Hrun".
    clear Hsave.

    iPoseProof (frame_interp_update_frame' with "Hframe") as "Hframe_saved".
    2, 3, 5: done.
    { subst val_idxs fe. by rewrite fe_wlocal_offset_length. }
    { subst wl_save. rewrite Hιs_payload_eq. by rewrite map_comp. }

    iDestruct (frame_interp_wl_interp with "Hframe_saved") as "%Hwl_saved".
    pose proof (interp_wl_length _ _ _ Hwl_saved) as Hfr_saved_locs_len.

    assert (tag_idx < length (f_locs fr_saved)) as Htag_in_fr_saved.
    {
      subst tag_idx.
      simpl.
      eapply Nat.lt_le_trans; last done.
      - rewrite app_assoc.
        subst fe.
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
    iDestruct (labels_interp_mono _ _ _ _ _ fr_saved_and_tag _ _ _ _ with "Hlabels") as "Hlabels'"; first done.
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
        subst wl_save.
        apply map_seq_forall_localidx_neq.
    }

    iEval (rewrite app_assoc) in "Hframe_saved".
    iPoseProof (frame_interp_update_frame' with "Hframe_saved") as "Hframe_saved_and_tag".
    5: {
      instantiate (1 := fr_saved_and_tag).
      instantiate (1 := [tag_idx]).
      eapply frame_rel_mask_mono; last done.
      intros i H ->.
      destruct H. by rewrite list_elem_of_singleton.
    }
    all: try done.
    2: {
      simpl.
      instantiate (1 := [_]).
      by apply Forall2_cons.
    }
    2: {
      apply Forall2_cons; split; last done.
      by eexists.
    }
    {
      subst tag_idx val_idxs fe.
      by rewrite fe_wlocal_offset_length.
    }

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
    apply run_codegen_case_blocks_app in Hcg as (wt_pre & wt_case_tag & wt_post & wl_pre & wl_case_tag & wl_post & es_pre & es_tag_cg & es_post & Hcg_pre & Hcg_tag & Hcg_post & -> & -> & ->).

    replace (length (map _ _)) with (length ess_pre) in Hcg_tag, Hcg_post.
    2: {
      rewrite length_map.
      apply compile_cases_length.
    }
    rewrite Nat.add_0_l in Hcg_tag, Hcg_post.

    (* Reason about ess_pre *)
    iEval (rewrite app_assoc).
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      iApply (cwp_case_blocks_fail wt wt_pre (wl ++ wl_save ++ [prelude.W.T_i32]) wl_pre 0 tag
                (Mk_localidx tag_idx) wl_ret
                (map
                   (λ (c : codegen ()) (i : nat),
                     try_option EFail (sum_offset EmptyEnv ρs_sum i)
                       ≫= λ off : nat,
                       try_option EFail (length <$> ιss_payload !! i)
                         ≫= λ count : nat,
                         restore_stack (take count (drop off val_localidxs)) ≫= λ _ : (), c)
                   ((fix compile_cases (fe : function_env) (ess : list (list instruction)) {struct ess} :
                      list (codegen ()) :=
                       match ess with
                       | [] => []
                       | es :: ess' => mapM_ (compile_instr mr fe) es :: compile_cases fe ess'
                       end)
                      fe ess_pre))
                (map default_of_value_type wl_ret) es_pre fr_saved_and_tag B R with "[$] [$]").
      - right. rewrite Nat.add_0_l. rewrite length_map.
        fold (compile_cases mr fe ess_pre). rewrite <- compile_cases_length.
        rewrite -Hess_pre_τs_pre. subst tag. apply le_n.
      - done.
      - rewrite length_map. rewrite <- Nat2Z.inj_add. rewrite Nat.add_0_l.
        fold (compile_cases mr fe ess_pre). rewrite <- compile_cases_length.
        rewrite -Hess_pre_τs_pre. rewrite <- Htag_len. lia.
      - by rewrite length_map.
      - done.
      - done.
    }
    iIntros (?fr w) "(-> & ->) Hfr Hrun".
    clear Hcg_pre.

    iDestruct (labels_interp_mono _ _ _ _ _ fr_saved_and_tag _ _ _ _ with "Hlabels") as "Hlabels'''"; first done.
    {
      instantiate (1 := (wlmask (fe_of_context F') (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_pre))).
      intros i [Hi_lo Hi_hi].
      simpl.
      split.
      + exact Hi_lo.
      + rewrite -fe_of_context_labels.
        rewrite !length_app. simpl.
        subst fe.
        lia.
    }

    apply cwp_case_block_success with (tag := Wasm_int.Int32.repr tag) in Hcg_tag as
        (es_case_tag & Hcg_case_tag & Hes_case_tag).
    inv_cg_bind Hcg_case_tag off' ?wt ?wt ?wl ?wl ?es ?es Hlookup Hcase_es_tag.
    inv_cg_try_option Hlookup.
    match goal with H : sum_offset EmptyEnv _ _ = Some _ |- _ => rename H into Heq_off_tag end.

    inv_cg_bind Hcase_es_tag count' ?wt ?wt ?wl ?wl ?es ?es Hinject Hcase_es_tag.
    inv_cg_try_option Hinject.
    match goal with H : length <$> _ !! _ = Some _ |- _ => rename H into Heq_count_tag end.

    inv_cg_bind Hcase_es_tag [] ?wt ?wt ?wl ?wl ?es ?es Hget_locals_tag Hcase_es_tag.
    destruct (run_codegen_get_locals _ _ _ _ _ _ _ Hget_locals_tag) as ([] & -> & ->).
    clear_nils.

    (* off' = off *)
    apply sum_offset_emptyenv with (se:=se) in Heq_off_tag.
    rewrite -Hess_pre_τs_pre -Htag_len in Heq_off_tag.
    pose proof (sum_offset_eq_sum_interp_offset se F τs ρs_sum ξs_sum ιss_payload tag Hsem Hkinds Hmap_eval_rep) as Hoff_eq.
    rewrite Hoff_eq Hsum_offset in Heq_off_tag.
    apply Some_inj in Heq_off_tag.
    subst off'.

    (* count' = count *)
    rewrite -Hess_pre_τs_pre -Htag_len in Heq_count_tag.
    edestruct (Forall2_lookup_l _ _ _ _ _ Harep_all Hlookup_eval) as (ιs_tag' & Hιs_tag_lookup & Harep_tag').
    rewrite Harep_tag in Harep_tag'.
    apply Some_inj in Harep_tag'.
    subst ιs_tag'.
    rewrite Hιs_tag_lookup in Heq_count_tag.
    simpl in Heq_count_tag.
    apply Some_inj in Heq_count_tag.
    rewrite Hcase_tag_payload_count in Heq_count_tag.
    subst count'.

    iDestruct (Hforall_tag _ _ (wt_post ++ wtf) _ _ (wl_post ++ wlf) _ Hcase_es_tag) as "Hsem_es_tag".

    rewrite (app_assoc _ es_tag_cg).
    iApply (cwp_seq with "[-]").
    {
      iApply (Hes_case_tag with "[$Hfr] [$Hrun]").
      { rewrite -Hess_pre_τs_pre -Htag_len. by apply nat_repr_i32repr. }
      { by rewrite length_map. }
      { done. }
      iIntros "Hfr Hrun".
      clear Hes_case_tag.

      (* get locals corresponding to payload of sum *)
      eapply cwp_restore_stack_w in Hget_locals_tag.
      2: {
        instantiate (1 := take count (drop off vs_payload)).
        repeat rewrite length_take.
        repeat rewrite length_drop.
        by apply Forall2_length in Hsaved as ->.
      }
      destruct Hget_locals_tag as (_ & _ & _ & Hget_locals_tag).
      iDestruct (Hget_locals_tag with "[$] [$] []") as "Hget_locals_tag"; clear Hget_locals_tag.
      1: {
        iPureIntro.
        apply Forall2_take.
        by apply Forall2_drop.
      }

      iApply (cwp_seq with "[Hget_locals_tag]").
      1: iApply "Hget_locals_tag".
      iIntros (?fr w) "(-> & ->) Hf Hrun".

      assert (prelude.translate_types (fc_type_vars F) [τ_res] = Some wl_ret) as
        Htranslate_types_single.
      {
        subst fe.
        unfold fe_of_context, fe_type_vars in Heq_some.
        unfold prelude.translate_types.
        simpl.
        rewrite Heq_some.
        simpl.
        by rewrite app_nil_r.
      }

      iApply ("Hsem_es_tag" with "[//] [] [] [] [$] [Hatoms_interp_payload] [Hvalue_interp_os_tag] [Hframe_saved_and_tag] [$] [$] [$]").
        + by rewrite has_values_iff_to_consts.
        + by iEval (rewrite -app_assoc).
        + subst F'.
          replace (fc_labels (F <| fc_labels ::= cons ([τ_res], L') |>)) with
              (([τ_res], L') :: fc_labels F); last done.
              iSimpl. iEval (repeat rewrite -app_assoc).
              iApply (labels_interp_cons rti sr); try done.
              iIntros "!>" (fr' vs') "(%Hfrel & Hframe & (%os & Hvalues & Hatoms) & [%Θ Hrt] & Hown)".
              by iFrame.
        + instantiate (1 := (take count (drop off os_payload))).
          by iApply atoms_interp_take_drop.
        + by iApply values_interp_one_eq.
        + by iEval (repeat rewrite -app_assoc).
        + done.
    }

    iIntros (??) "(%Hfrel & Hframe & (% & Hos' & Hvs) & [% Hrt] & Hown) Hfr Hrun".
    iDestruct (atoms_interp_length with "Hvs") as "%Hlen_vs".
    iDestruct (translate_types_comp_interp_length rti sr with "Hos'") as "%Hlen_os'".
    { done. }
    { exact Htoks_res. }
    { cbn. apply bind_Some. exists [wl_ret]. cbn. rewrite app_nil_r. split; last done.
      apply bind_Some. by exists wl_ret. }

    (* Reason about ess_post *)
    iApply (cwp_wand with "[Hfr Hrun]").
    {
      iApply (cwp_case_blocks_fail with "[$] [$]"); last apply Hcg_post.
      - instantiate (1 := tag). left. rewrite -Hess_pre_τs_pre -Htag_len. lia.
      - done.
      - rewrite length_map. fold (compile_cases mr fe ess_post). rewrite <- compile_cases_length.
        rewrite length_app in Hess_typ_len. rewrite length_cons in Hess_typ_len.
        rewrite <- Nat2Z.inj_add.
        rewrite Nat.add_succ_comm.
        rewrite -Hess_typ_len.
        by rewrite Htyp_rep_len.
      - by rewrite -Hlen_os' Hlen_vs.
      - rewrite -Hsaved_and_tag. destruct Hfrel as [Hmask _]. symmetry. apply Hmask.
        subst tag_idx fe. unfold wlmask. repeat rewrite length_app. subst tag_localidx. cbn [localimm].
        split.
        + lia.
        + rewrite length_app. rewrite length_cons. lia.
    }
    iIntros (??) "(-> & ->)".
    iEval (repeat rewrite -app_assoc) in "Hframe".
    iEval (repeat rewrite -app_assoc).
    iFrame.
    iPureIntro.
    unfold lmask.
    eapply frame_rel_trans.
    + eapply frame_rel_mask_mono; [| exact Hfrel_lmask_saved_and_tag].
      intros i [Hi_lo Hi_hi]. unfold lmask, wlmask. split; exact Hi_lo || exact Hi_hi.
    + eapply frame_rel_wlmask_mono; [| exact Hfrel].
      rewrite length_app. rewrite length_app. lia.
  Qed.

End case.
