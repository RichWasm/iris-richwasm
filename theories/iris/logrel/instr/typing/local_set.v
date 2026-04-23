Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section local_set.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_local_set M F L wt wt' wtf wl wl' wlf es' i τ τ' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [τ'] [] in
    let L' := <[ i := τ' ]> L in
    L !! i = Some τ ->
    has_ref_flag F τ NoRefs ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ILocalSet ψ i)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L'.
  Proof.
    intros fe WT WL lmask Ψ L' Hlookup_L_i Hrf Hok Hcg.
    subst Ψ.
    cbn [compile_instr] in Hcg.
    (* destruct κ as [ ρ rf | ]; last inversion Hcg. *)
    (* destruct ρ  as [ | ρs_sum | | ]; try done. *)
    (* destruct τs as [ | τ_res τs' ]; first done. *)

    unfold compile_local_set in Hcg.
    inv_cg_bind Hcg ?local_ixs ?wt ?wt ?wl ?wl ?es es_set_locals Hlocal_ixs Hset_locals.
    inv_cg_try_option Hlocal_ixs; subst.

    apply run_codegen_set_locals in Hset_locals as H.
    destruct H as (_ & -> & ->).

    subst WT WL.
    clear_nils.
    simplify_eq.

    (* Iris Proof *)
    iIntros (? ? ? ? ? ? ? ?) "%Hsem %Hhas_values #Hinst #Hlabels #Hreturn Hvs Hos Hframe Hrt Hown Hfr Hrun".

    iDestruct (values_interp_one_eq with "Hos") as "Hos".
    iDestruct (value_interp_eq with "Hos") as "Hos".
    unfold value_interp0, value_se_interp0.
    iDestruct "Hos" as "(%κ & %Hkind_payload & #Hskind_as_type & Hvs_type_interp)".

    iPoseProof (frame_interp_wl_interp _ _ _ _ F with "Hframe") as "%Hwl".
    apply has_values_iff_to_consts in Hhas_values as ->.

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
    (* assert (l = ιs) as ->. *)
    (* { admit. } (* TODO *) *)

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

    (* apply bind_Some in Heq_some0 as Hsum. *)
    (* destruct Hsum as (ιss_pre' & Hιss_pre' & Hoff). *)
    (* apply Some_inj in Hoff as <-. *)
    (**)
    (* have Htake : mapM (eval_rep EmptyEnv) (take i ρs_sum) = Some (take i (ιss_pre ++ ιs :: ιss_post)). *)
    (* { *)
    (*   eapply mapM_take; eauto. *)
    (* } *)
    (**)
    (* rewrite Hιss_pre' in Htake. *)
    (**)
    (* rewrite Hιss_pre_len in Htake. *)
    (* rewrite take_app in Htake. *)
    (* rewrite Nat.sub_diag in Htake. *)
    (* rewrite take_0 in Htake. *)
    (* clear_nils. *)
    (* rewrite firstn_all in Htake. *)
    (* apply Some_inj in Htake as ->. *)
    (**)
    (* rewrite length_app !length_map in Hset_i_locals. *)
    (* subst count. *)
    (* rewrite drop_seq take_seq in Hset_i_locals. *)
    (* replace (length ιs `min` _) with (length ιs) in Hset_i_locals. *)
    (* 2: { *)
    (*   rewrite length_app. *)
    (*   rewrite length_fmap. *)
    (*   lias. *)
    (* } *)
    (* set idxs_i := (seq (fe_wlocal_offset fe + length wl + length (concat ιss_pre)) (length ιs)) in Hset_i_locals. *)
    (**)
    (* pose proof (result_type_interp_of_defaults (translate_arep <$> concat ιss_pre)) as Hres_type_pre. *)
    (* pose proof (result_type_interp_of_defaults (translate_arep <$> ιs)) as Hres_type_def_payload. *)
    (* pose proof (result_type_interp_of_defaults (translate_arep <$> concat ιss_post)) as Hres_type_post. *)
    iDestruct (result_type_interp_of_atoms_interp with "Hvs") as "%Hres_type_vs"; first done.
    (**)
    (* pose (sum_vals := fun vs => *)
    (*   (default_of_value_types $ translate_arep <$> concat ιss_pre) ++ *)
    (*   vs ++ *)
    (*   (default_of_value_types $ translate_arep <$> concat ιss_post)). *)
    (**)
    (* assert (result_type_interp areps_sum (sum_vals (default_of_value_types (translate_arep <$> ιs)))) as Hres_type_default. *)
    (* { *)
    (*   apply result_type_interp_combine; first done. *)
    (*   apply result_type_interp_combine; last done. *)
    (*   apply Hres_type_def_payload. *)
    (* } *)
    (**)
    (* rewrite <- (app_nil_r areps_sum) in Hset_sum_locals. *)
    unfold local_indices in Heq_some.
    apply bind_Some in Heq_some as [ηs [Hlookup_fe_i Hlocal_ixs]].
    apply Some_inj in Hlocal_ixs.

    eapply cwp_set_locals_w in Hset_locals.
    5: {
      instantiate (1 := map translate_arep l).
      instantiate (1 := (sum_list_with length (take i (fe_locals fe)))).
      done.
    }
    6: admit.
    5: done.
    3: done.
    2: apply has_values_to_consts.
    2: {
      unfold fe_wlocal_offset.
      subst fe.
      admit.
    }
    destruct Hset_locals as (_ & _ & _ & Hset_locals).
    iApply (Hset_locals with "[$] [$]").
    clear Hset_locals.
    iIntros (fr' [Hfrel Hf2]).
    iFrame.
    iSplit.
    {
      subst lmask.
      iPureIntro.
      eapply frame_rel_mask_mono; last done.
      intros j Hnotinj.
      simpl.
      admit.
    }

  Admitted.

End local_set.
