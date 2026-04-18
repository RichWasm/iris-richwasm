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

    inv_cg_bind Hcg ixs wt_ixs ?wt wl_ixs ?wl es_ixs ?es Hixs Hcg.
    subst.
    apply wp_wlallocs in Hixs as (Hixs & -> & Hwl_ixs & ->).

    inv_cg_bind Hcg ?units ?wt ?wt ?wl ?wl es_set_locals ?es Hset_locals Hcg.

    inv_cg_bind Hcg ?unit ?wt ?wt ?wl ?wl ?es es_restore_stack Hemit_tag Hrestore_stack.
    inv_cg_emit Hemit_tag; subst.

    subst WT WL.
    clear_nils.
    simplify_eq.

    rewrite imap_seq map_fmap -fmap_drop -fmap_take -map_rev in Hset_locals.

    set idxs_i :=
    (rev
       (take count
          (drop off
             (seq (fe_wlocal_offset fe + length wl)
                (length (translate_arep <$> concat ιss)))))) in Hset_locals.

    rewrite imap_seq map_fmap in Hrestore_stack.
    set idxs_all :=
    (seq (fe_wlocal_offset fe + length wl)
          (length (translate_arep <$> concat ιss))) in Hrestore_stack.

    (* Iris Proof *)
    iIntros (? ? ? ? ? ? ? ?) "%Hsem %Hhas_values #Hinst #Hlabels #Hreturn Hvs Hos Hframe Hrt Hown Hfr Hrun".

    iDestruct (values_interp_one_eq with "Hos") as "Hos".
    iDestruct (value_interp_eq with "Hos") as "Hos".
    unfold value_interp0, value_se_interp0.
    iDestruct "Hos" as "(%κ & %Hkind_payload & Hskind_as_type & Hpayload_interp)".

    iPoseProof (frame_interp_wl_interp with "Hframe") as "%Hwl"; first done.
    apply has_values_iff_to_consts in Hhas_values as ->.

    (* i is an index into ιss, so we must have: *)
    (* τss = τss_pre ++ [τs_tag] ++ τss_post *)
    (* ιss = ιss_pre ++ [ιs_tag] ++ ιss_post *)

    apply list_elem_of_split_length in Hlookup_i as H.
    destruct H as (τs_pre & τs_post & Hτs_eq & Htag_len).

    apply fmap_Some_1 in Heq_some1.
    destruct Heq_some1 as (ιs & Hlookup_ιss & Hcount).
    apply list_elem_of_split_length in Hlookup_ιss as H.
    destruct H as (ιss_pre & ιss_post & Hιs_eq & Hi_len).

    assert (map translate_arep (concat ιss) = map translate_arep (concat ιss_pre) ++ map translate_arep ιs ++ map translate_arep (concat ιss_post)) as Htranslate_split.
    {
      subst ιss.
      rewrite concat_app concat_cons.
      by rewrite !map_app.
    }
    rewrite !Htranslate_split.

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
(**)
    unfold skind_as_type_interp.
    iDestruct "Hskind_as_type" as "[%Hhas_areps %Href]".
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

    unfold sum_offset in Heq_some0.
    apply bind_Some in Heq_some0.
    destruct Heq_some0 as (ιss_pre' & Hιss_pre' & Hoff).
    apply Some_inj in Hoff as <-.

    subst ιss.
    have Htake : mapM (eval_rep EmptyEnv) (take i ρs_sum) = Some (take i (ιss_pre ++ ιs :: ιss_post)).
    {
      eapply mapM_take; eauto.
    }

    rewrite Hιss_pre' in Htake.

    rewrite Hi_len in Htake.
    rewrite take_app in Htake.
    rewrite Nat.sub_diag in Htake.
    rewrite take_0 in Htake.
    clear_nils.
    rewrite firstn_all in Htake.
    apply Some_inj in Htake as ->.

    iDestruct (result_type_interp_of_atoms_interp with "Hvs") as "%Hres_type_vs_payload"; first done.

    eapply cwp_set_locals_w in Hset_locals; eauto.
    2: by rewrite -app_assoc.
    destruct Hset_locals as (Hval_localidxs_seq & -> & -> & Hset_locals).
    iEval (rewrite app_assoc).
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      iApply (Hset_locals with "[$] [$]").
      iIntros (f' [Hfsame Hfchanged]).
      instantiate (1 := λ fr' vs, (
        ⌜vs = []⌝ ∗
        ⌜frame_rel (λ i, i ∉ _) fr fr'⌝ ∗
        ⌜Forall2
          (λ (i : prelude.W.localidx) (v : value), f_locs fr' !! localimm i = Some v)
          _ _⌝
        )%I).
      auto.
    }
    iIntros (fr' w) "(-> & %Hfrel_fr' & %Hsaved) Hfr Hrun".
    clear Hset_locals.
    clear_nils.

    iEval (rewrite app_assoc) in "Hframe".
    (* TODO This lemma is not generic enough *)
    iPoseProof (frame_interp_update_frame' with "Hframe") as "Hframe_saved".
    5: done.
    {
      subst idxs_i count.

      rewrite length_app !length_map.
      rewrite drop_seq take_seq.
      admit.
    }
    2: done.
    2: admit. (* TODO: need to know more about l above *)
    1: done.

    (* iDestruct (frame_interp_wl_interp with "Hframe_saved") as "%Hwl_saved"; first done. *)
    (* pose proof (interp_wl_length _ _ _ Hwl_saved) as Hfr_saved_locs_len. *)

    iApply cwp_val_app.
    {
      instantiate (1 := [(instruction.W.VAL_int32 (Wasm_int.Int32.repr i))]).
      simpl.
      unfold value_eqb. by destruct (value_eq_dec _ _).
    }

    set sum_vals :=
    ((default_of_value_types $ translate_arep <$> concat ιss_pre) ++
    vs ++
    (default_of_value_types $ translate_arep <$> concat ιss_post)
    ).

    eapply cwp_restore_stack_w with (vs := sum_vals) in Hrestore_stack.
    2: {
      admit.
      (* instantiate (1 := vs). *)
      (* instantiate (1 := (take count (drop off vs_payload))). *)
      (* repeat rewrite length_take. *)
      (* repeat rewrite length_drop. *)
      (* by apply Forall2_length in Hsaved as ->. *)
    }
    destruct Hrestore_stack as (_ & -> & -> & Hrestore_stack).
    iDestruct (Hrestore_stack with "[$] [$] []") as "Hrestore_stack"; clear Hrestore_stack.
    1: {
      (* iPureIntro. *)
      (* apply Forall2_take. *)
      (* by apply Forall2_drop. *)
      admit.
    }

    iApply (cwp_wand with "[Hrestore_stack]").
    {
      iApply "Hrestore_stack".
    }
    iIntros (?fr w) "(-> & ->)".
    unfold fvs_combine.

  Admitted.

End inject.
