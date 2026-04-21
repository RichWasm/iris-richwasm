Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section inject.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_inject M F L wt wt' wtf wl wl' wlf es' i τs τ κ :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [τ] [SumT κ τs] in
    τs !! i = Some τ ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IInject ψ i)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmask Ψ Hlookup_i Hok Hcg.
    subst Ψ.
    cbn [compile_instr] in Hcg.
    destruct κ as [ ρ rf | ]; last inversion Hcg.
    destruct ρ  as [ | ρs_sum | | ]; try done.
    (* destruct τs as [ | τ_res τs' ]; first done. *)

    inv_cg_bind Hcg ιss ?wt ?wt ?wl ?wl ?es ?es Hιss Hcg.
    inv_cg_try_option Hιss; subst.

    inv_cg_bind Hcg off ?wt ?wt ?wl ?wl ?es ?es Hoff Hcg.
    inv_cg_try_option Hoff; subst.

    inv_cg_bind Hcg count ?wt ?wt ?wl ?wl ?es ?es Hcount Hcg.
    inv_cg_try_option Hcount; subst.

    inv_cg_bind Hcg ixs wt_ixs ?wt wl_ixs ?wl es_ixs ?es Halloc Hcg.
    subst.
    apply wp_wlallocs in Halloc as (Hixs & -> & Hwl_ixs & ->).

    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_create_defaults ?es Hcreate_defaults Hcg.
    apply run_codegen_create_defaults in Hcreate_defaults as H.
    destruct H as (_ & -> & -> & _).
    rewrite imap_seq map_fmap in Hixs.

    inv_cg_bind Hcg ?units ?wt ?wt ?wl ?wl es_set_sum_locals ?es Hset_sum_locals Hcg.

    inv_cg_bind Hcg ?units ?wt ?wt ?wl ?wl es_set_i_locals ?es Hset_i_locals Hcg.

    inv_cg_bind Hcg ?unit ?wt ?wt ?wl ?wl ?es es_restore_stack Hemit_tag Hrestore_stack.
    inv_cg_emit Hemit_tag; subst.

    subst WT WL.
    clear_nils.
    simplify_eq.

    rewrite -fmap_drop -fmap_take -map_rev in Hset_i_locals.

    (* Iris Proof *)
    iIntros (? ? ? ? ? ? ? ?) "%Hsem %Hhas_values #Hinst #Hlabels #Hreturn Hvs Hos Hframe Hrt Hown Hfr Hrun".

    iDestruct (values_interp_one_eq with "Hos") as "Hos".
    iDestruct (value_interp_eq with "Hos") as "Hos".
    unfold value_interp0, value_se_interp0.
    iDestruct "Hos" as "(%κ & %Hkind_payload & #Hskind_as_type & Hpayload_interp)".

    iPoseProof (frame_interp_wl_interp _ _ _ _ F with "Hframe") as "%Hwl".
    apply has_values_iff_to_consts in Hhas_values as ->.

    (* i is an index into ιss, so we must have: *)
    (* τss = τss_pre ++ [τs_tag] ++ τss_post *)
    (* ιss = ιss_pre ++ [ιs_tag] ++ ιss_post *)
    (* ρs_sum = ρs_sum_pre ++ [ρ_i] ++ ρs_sum_post *)

    apply list_elem_of_split_length in Hlookup_i as H.
    destruct H as (τs_pre & τs_post & Hτs_eq & Hτs_pre_len).

    apply fmap_Some_1 in Heq_some1.
    destruct Heq_some1 as (ιs & Hlookup_ιss & Hcount).
    apply list_elem_of_split_length in Hlookup_ιss as H.
    destruct H as (ιss_pre & ιss_post & Hιs_eq & Hιss_pre_len).
    subst ιss.

    apply mapM_split in Heq_some as Heval_ρs_sum.
    destruct Heval_ρs_sum as (ρs_sum_pre & ρs_sum_post & ρ_i & Hρs_sum_eq & Heval_ρs_sum_pre & Heval_ρ_i & Heval_ρs_sum_post).
    apply length_mapM in Heval_ρs_sum_pre as Hρs_sum_pre_len.
    rewrite -Hιss_pre_len in Hρs_sum_pre_len.

    set (areps_sum' := map translate_arep (concat (ιss_pre ++ ιs :: ιss_post))) in *.
    set (areps_sum'' := (translate_arep <$> concat (ιss_pre ++ ιs :: ιss_post))) in *.
    set (areps_sum := (translate_arep <$> (concat ιss_pre)) ++ (translate_arep <$> ιs) ++ (translate_arep <$> (concat ιss_post))) in *.
    replace areps_sum' with areps_sum in *.
    2: {
      unfold areps_sum, areps_sum'.
      by rewrite concat_app concat_cons map_app map_app.
    }
    replace areps_sum'' with areps_sum in *.
    2: {
      unfold areps_sum, areps_sum''.
      by rewrite -fmap_app -fmap_app concat_app concat_cons fmap_app fmap_app.
    }
    set idxs_all := (seq (fe_wlocal_offset fe + length wl) (length areps_sum)) in Hrestore_stack, Hset_sum_locals.

    destruct κ; last first.
    {
      unfold skind_as_type_interp, ssize_interp.
      iDestruct "Hskind_as_type" as "[[] _]".
    }
    (* unfold type_skind, eval_kind in Hkind_sum. *)
    (* apply bind_Some in Hkind_sum. *)
    (* destruct Hkind_sum as (l' & Heval & Hret). *)
    (* inversion Hret; subst l r. *)
    (* clear Hret. *)
    assert (l = ιs) as ->.
    { admit. } (* TODO *)

    iPoseProof "Hskind_as_type" as "H".
    iDestruct "H" as "[%Hhas_areps %Href]".
    (* apply has_areps_cons_exists in Hhas_areps as (ι_tag & ιs_payload & -> & Hhas_areps_payload & Hhas_arep_tag). *)
(*     apply bind_Some in Hcount as Hcount'. *)
(*     destruct Hcount' as [ιs_case_tag_payload' [Hlookup_eval Hcase_tag_payload_count]]. *)
(*     apply Some_inj in Hcase_tag_payload_count. *)
(*     apply bind_Some in Hlookup_eval as Heval_repr. *)
(*     destruct Heval_repr as [ρ_case_tag_payload' [Hlookup_tag Heval_rep']]. *)
(**)
(*     inversion Heval as [Hιs_sum]. *)
(*     apply bind_Some in Hιs_sum as Hιs_sum. *)
(*     destruct Hιs_sum as [ιss_payload [Hmap_eval_rep Heq]]. *)
(*     apply Some_inj in Heq. *)
(*     simpl in Heq. *)
(*     injection Heq as Htag Hpayload. *)
(*     apply mapM_eval_rep_emptyenv with (se := se) in Heq_some0. *)
(*     rewrite Hmap_eval_rep in Heq_some0. *)
(*     apply Some_inj in Heq_some0 as <-. *)
    (* TODO end *)

    apply bind_Some in Heq_some0 as Hsum.
    destruct Hsum as (ιss_pre' & Hιss_pre' & Hoff).
    apply Some_inj in Hoff as <-.

    have Htake : mapM (eval_rep EmptyEnv) (take i ρs_sum) = Some (take i (ιss_pre ++ ιs :: ιss_post)).
    {
      eapply mapM_take; eauto.
    }

    rewrite Hιss_pre' in Htake.

    rewrite Hιss_pre_len in Htake.
    rewrite take_app in Htake.
    rewrite Nat.sub_diag in Htake.
    rewrite take_0 in Htake.
    clear_nils.
    rewrite firstn_all in Htake.
    apply Some_inj in Htake as ->.

    rewrite length_app !length_map in Hset_i_locals.
    subst count.
    rewrite drop_seq take_seq in Hset_i_locals.
    replace (length ιs `min` _) with (length ιs) in Hset_i_locals.
    2: {
      rewrite length_app.
      rewrite length_fmap.
      lias.
    }
    set idxs_i := (rev (seq (fe_wlocal_offset fe + length wl + length (concat ιss_pre)) (length ιs))) in Hset_i_locals.

    pose proof (result_type_interp_of_defaults (translate_arep <$> concat ιss_pre)) as Hres_type_pre.
    pose proof (result_type_interp_of_defaults (translate_arep <$> ιs)) as Hres_type_def_payload.
    pose proof (result_type_interp_of_defaults (translate_arep <$> concat ιss_post)) as Hres_type_post.
    iDestruct (result_type_interp_of_atoms_interp with "Hvs") as "%Hres_type_vs_payload"; first done.

    pose (sum_vals := fun vs =>
      (default_of_value_types $ translate_arep <$> concat ιss_pre) ++
      vs ++
      (default_of_value_types $ translate_arep <$> concat ιss_post)).

    eapply cwp_set_locals_w in Hset_sum_locals.
    4: done.
    3: {
      instantiate (1 := sum_vals _).
      apply result_type_interp_combine; first done.
      apply result_type_interp_combine; last done.
      apply Hres_type_def_payload.
    }
    2: admit. (* wl_interp *)
    destruct Hset_sum_locals as (_ & -> & -> & Hset_sum_locals).

    iEval (do 2 rewrite app_assoc).
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      iEval (rewrite -app_assoc).
      iApply cwp_val_app.
      1: apply has_values_to_consts.

      iApply (cwp_seq with "[Hfr Hrun]").
      {
        eapply cwp_create_defaults in Hcreate_defaults as (_ & _ & _ & Hcreate_defaults).
        iDestruct (Hcreate_defaults with "[$] [$] []") as "Hcreate_defaults".
        {
          instantiate (1 := λ f vs, (⌜f = fr⌝ ∗ ⌜vs = sum_vals (default_of_value_types $ translate_arep <$> ιs)⌝)%I).
          iPureIntro.
          split; first done.

          unfold sum_vals, areps_sum.
          by rewrite !map_app.
        }
        iApply "Hcreate_defaults".
      }
      iIntros (??) "[-> ->] Hfr Hrun".
      instantiate (1 := λ fr' vs', (
        ⌜vs' = vs⌝ ∗
        ⌜frame_rel (λ i, i ∉ idxs_all) fr fr'⌝ ∗
        ⌜Forall2
          (λ (i : prelude.W.localidx) (v : value), f_locs fr' !! localimm i = Some v)
          (Mk_localidx <$> idxs_all) (sum_vals (default_of_value_types $ translate_arep <$> ιs))⌝
        )%I).
      iApply (Hset_sum_locals with "[$] [$]").
      iIntros (f [Hfrel Hf2]).
      unfold fvs_combine.
      clear_nils.
      done.
    }
    iIntros (fr_init ?) "(-> & %Hfrel_fr_init & %Hsaved_init) Hfr Hrun".

    eapply cwp_set_locals_w in Hset_i_locals; eauto.
    (* 2: by rewrite -app_assoc. *)
    2: admit. (* wl_interp *)
    destruct Hset_i_locals as (Hval_localidxs_seq & -> & -> & Hset_i_locals).
    iEval (rewrite app_assoc).
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      iApply (Hset_i_locals with "[$] [$]").
      iIntros (f' [Hfsame Hfchanged]).
      instantiate (1 := λ fr' vs', (
        ⌜vs' = []⌝ ∗
        ⌜frame_rel (λ i, i ∉ idxs_i) fr_init fr'⌝ ∗
        ⌜Forall2
          (λ (i : prelude.W.localidx) (v : value), f_locs fr' !! localimm i = Some v)
          (Mk_localidx <$> idxs_i) vs⌝
        )%I).
      auto.
    }
    iIntros (fr_saved w) "(-> & %Hfrel_fr_saved & %Hsaved) Hfr Hrun".
    clear Hset_i_locals.
    clear_nils.

    eapply cwp_restore_stack_w with (vs := sum_vals vs) in Hrestore_stack.
    2: {
      subst idxs_all sum_vals areps_sum.
      rewrite length_fmap.
      rewrite length_seq.
      rewrite !length_app.
      rewrite !length_map.
      f_equal.
      f_equal.
      rewrite -(Forall2_length _ _ _ Hres_type_vs_payload).
      by rewrite length_map.
    }
    destruct Hrestore_stack as (_ & -> & -> & Hrestore_stack).
    clear_nils.

    iApply cwp_val_app.
    {
      instantiate (1 := [(instruction.W.VAL_int32 (Wasm_int.Int32.repr i))]).
      simpl.
      unfold value_eqb. by destruct (value_eq_dec _ _).
    }

    assert (Forall2
     (λ (i : prelude.W.localidx) (v : value),
        f_locs fr_saved !! localimm i = Some v)
     (Mk_localidx <$> idxs_all) (sum_vals vs)) as Hsaved_all.
     {
      subst idxs_all areps_sum idxs_i.
      rewrite !length_app in Hsaved_init.
      rewrite !seq_app in Hsaved_init.
      rewrite fmap_app fmap_app in Hsaved_init.
      apply Forall2_app_inv in Hsaved_init as [Hsaved_init_pre Hsaved_init].
      2: by rewrite !length_fmap length_seq /default_of_value_types.
      apply Forall2_app_inv in Hsaved_init as [_ Hsaved_init_post].
      2: by rewrite !length_fmap length_seq /default_of_value_types.

      eapply frame_rel_Forall2_update' in Hsaved_init_pre; try done.
      2: {
        apply Forall_forall.
        intros x Hx.
        rewrite elem_of_seq !length_fmap in Hx.
        rewrite list_elem_of_In -in_rev -list_elem_of_In elem_of_seq.
        lia.
      }

      eapply frame_rel_Forall2_update' in Hsaved_init_post; try done.
      2: {
        apply Forall_forall.
        intros x Hx.
        rewrite elem_of_seq !length_fmap in Hx.
        rewrite list_elem_of_In -in_rev -list_elem_of_In elem_of_seq.
        lia.
      }

      unfold sum_vals.
      rewrite !length_app !length_fmap.
      rewrite !seq_app !fmap_app.
      eapply Forall2_app.
      - by rewrite length_fmap in Hsaved_init_pre.
      - eapply Forall2_app.
        + admit. (* weird rev *)
        + by rewrite !length_fmap in Hsaved_init_post.
     }

    iDestruct (Hrestore_stack with "[$] [$] []") as "Hrestore_stack"; clear Hrestore_stack.
    1: done.

    (* relate starting frame fr and fr_saved *)
    eapply frame_rel_mask_mono in Hfrel_fr_saved as Hfrel_fr_saved_all.
    2: {
      instantiate (1 := λ i, i ∉ idxs_all).
      simpl.
      intros j Hnotinj.
      subst idxs_all idxs_i areps_sum.
      rewrite list_elem_of_In -in_rev -list_elem_of_In elem_of_seq.
      intros Hin.
      apply Hnotinj.
      rewrite list_elem_of_In !length_app !length_fmap.
      apply list_elem_of_In, elem_of_seq.
      lia.
    }
    pose proof (frame_rel_trans _ _ _ _ Hfrel_fr_init Hfrel_fr_saved_all) as Hfrel_fr_to_saved.

    assert (frame_rel lmask fr fr_saved) as Hfrel_fr_to_saved_lmask.
    {
      eapply frame_rel_mask_mono; [| exact Hfrel_fr_to_saved].
      intros j [Hj_lo Hj_hi].
      subst idxs_all areps_sum.
      rewrite elem_of_seq !length_app !length_fmap. lia.
    }
    pose proof Hfrel_fr_to_saved_lmask as [_ ->].
    iDestruct (labels_interp_mono _ _ _ _ _ fr_saved _ _ _ _ with "Hlabels") as "Hlabels'"; try done.

    iPoseProof (frame_interp_update_frame' with "Hframe") as "Hframe_saved".
    5: done.
    {
      subst idxs_all.
      by rewrite fe_wlocal_offset_length.
    }
    1: done.
    1: done.
    1: admit. (* result_type_interp *)

    (* iDestruct (frame_interp_wl_interp with "Hframe_saved") as "%Hwl_saved"; first done. *)
    (* pose proof (interp_wl_length _ _ _ Hwl_saved) as Hfr_saved_locs_len. *)

    iApply (cwp_wand with "[Hrestore_stack]").
    {
      iApply "Hrestore_stack".
    }
    iIntros (?fr w) "(-> & ->)".
    unfold fvs_combine.
    iFrame.
    iSplit; first done.
    iDestruct (atoms_interp_and_areps_of_default_of_areps (concat ιss_pre)) as "(%os_pre & Hatoms_pre & %Hareps_pre)".
    iDestruct (atoms_interp_and_areps_of_default_of_areps (concat ιss_post)) as "(%os_post & Hatoms_post & %Hareps_post)".
    iExists (I32A (Wasm_int.Int32.repr i) :: os_pre ++ os ++ os_post).
    iSplitR "Hvs".
    - rewrite values_interp_one_eq.
      rewrite value_interp_eq.
      iSimpl.
      iExists (SVALTYPE (_ :: (concat ιss_pre) ++ ιs ++ (concat ιss_post)) _).
      repeat iSplit.
      + iPureIntro.
        rewrite bind_Some.
        eexists; split; last done.
        apply mapM_eval_rep_emptyenv with (se := se) in Heq_some.
        rewrite bind_Some.
        eexists; split; first done.
        simpl.
        by rewrite !concat_app concat_cons.
      + iPureIntro.
        rewrite -has_areps_cons.
        split; last done.
        apply has_areps_app_l; first done.
        apply has_areps_app_l; done.
      + admit. (* ref_flag_atoms_interp *)
      + iExists _, _, _, _, _.
        iSplit; first done.
        iSplit.
        { iPureIntro. by apply sum_offset_emptyenv. }
        iSplit.
        {
          iPureIntro.
          subst ρs_sum.
          rewrite list_lookup_middle; last done.
          simpl.
          apply eval_rep_emptyenv with (se := se) in Heval_ρ_i.
          rewrite Heval_ρ_i.
          done.
        }
        iSplit; first done.
        rewrite (has_areps_length _ _ Hareps_pre).
        rewrite (has_areps_length _ _ Hhas_areps).
        rewrite drop_app_length take_app_length.
        rewrite value_interp_eq.
        iFrame.
        iNext.
        iExists _.
        iSplit; done.
    - iApply atoms_interp_cons.
      iSplit; first done.
      iApply atoms_interp_app_split_r; first done.
      iApply (atoms_interp_app_split_r with "Hvs Hatoms_post").
  Admitted.

End inject.
