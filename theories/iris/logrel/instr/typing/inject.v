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

    (* Iris Proof *)
    iIntros (? ? ? ? ? ? ? ?) "%Hsem %Hhas_values #Hinst #Hlabels #Hreturn Hvs Hos Hframe Hrt Hown Hfr Hrun".

    iDestruct (values_interp_one_eq with "Hos") as "Hos".
    iDestruct (value_interp_eq with "Hos") as "Hos".
    unfold value_interp0, value_se_interp0.
    iDestruct "Hos" as "(%κ & %Hkind_payload & Hskind_as_type & Hpayload_interp)".

    (* apply lookup_lt_Some in Htag_type_lookup as Htag_size_bound. *)
    (* assert (length τs = length ρs_sum) as Htyp_rep_len. *)
    (* { *)
    (*   inversion Hok; subst. *)
    (*   unfold has_mono_rep_instr in H. *)
    (*   destruct H as [H _]. *)
    (*   rewrite Forall_singleton in H. *)
    (*   inversion H; subst. *)
    (*   inversion H1; subst. *)
    (*   apply has_kind_SumT_inv in H3 as (rf' & HF2). *)
    (*   by eapply Forall2_length. *)
    (* } *)
    (* assert (tag < Wasm_int.Int32.modulus)%Z as Htag_in_i32_bound. *)
    (* { rewrite Htyp_rep_len in Htag_size_bound. eapply Z.lt_le_trans; last done. by apply Nat2Z.inj_lt. } *)
    (* assert (length τs = length ess) as Hess_typ_len; first by eapply List.Forall2_length. *)
    (**)
    (* iDestruct (big_sepL2_length with "Hrvs") as "%Hlen". *)
    (* destruct vs as [|v_tag vs_payload]; first inversion Hlen. *)
    (* clear Hlen. *)
    (* iDestruct (atoms_interp_cons with "Hrvs") as "[-> Hatoms_interp_payload]". *)

    iPoseProof (frame_interp_wl_interp with "Hframe") as "%Hwl"; first done.
    (* rewrite list_extra.cons_app in Hhas_values. *)
    apply has_values_iff_to_consts in Hhas_values as ->.

    (* tag is an index into τs, so we must have: *)
    (* τs = τs_pre ++ [τ_tag] ++ τs_post *)
    (* ess = ess_pre ++ [es_tag] ++ ess_post *)
(*     apply list_elem_of_split_length in Htag_type_lookup as H. *)
(*     destruct H as (τs_pre & τs_post & Hτs_eq & Htag_len). *)
(**)
(*     rewrite Hτs_eq in Hforall. *)
(*     apply Forall2_app_inv_l in Hforall as *)
(*       (ess_pre & ess_rest & Hforall_pre & Hforall_rest & ->). *)
(*     apply Forall2_cons_inv_l in Hforall_rest as *)
(*       (es_tag & ess_post & Hforall_tag & Hforall_post & ->). *)
(*     apply Forall2_length in Hforall_pre as Hess_pre_τs_pre. *)
(*     apply Forall2_length in Hforall_post as Hess_post_τs_post. *)
(*     clear Hforall_pre Hforall_post. *)
(**)
(*     (* TODO start: this could use a little cleanup + abstract into lemmas? *) *)
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

    iDestruct (result_type_interp_of_atoms_interp with "Hvs") as "%Hres_type_vs_payload"; first done.

    eapply cwp_set_locals_w in Hset_locals; eauto.
    2: by rewrite -app_assoc.
    2: {
      rewrite imap_seq.
      rewrite map_fmap.
      rewrite -fmap_drop.
      rewrite -fmap_take.
      rewrite -map_rev.
      reflexivity.
    }
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
    iApply cwp_val_app.
    {
      instantiate (1 := [(instruction.W.VAL_int32 (Wasm_int.Int32.repr i))]).
      simpl.
      unfold value_eqb. by destruct (value_eq_dec _ _).
    }

      (* eapply cwp_restore_stack_w in Hrestore_stack. *)
      (* 2: { *)
      (*   instantiate (1 := vs). *)
      (*   instantiate (1 := (take count (drop off vs_payload))). *)
      (*   repeat rewrite length_take. *)
      (*   repeat rewrite length_drop. *)
      (*   by apply Forall2_length in Hsaved as ->. *)
      (* } *)
      (* destruct Hget_locals_tag as (_ & _ & _ & Hget_locals_tag). *)
      (* iDestruct (Hget_locals_tag with "[$] [$] []") as "Hget_locals_tag"; clear Hget_locals_tag. *)
      (* 1: { *)
      (*   iPureIntro. *)
      (*   apply Forall2_take. *)
      (*   by apply Forall2_drop. *)
      (* } *)
      (**)
      (* iApply (cwp_seq with "[Hget_locals_tag]"). *)
      (* 1: iApply "Hget_locals_tag". *)
      (* iIntros (?fr w) "(-> & ->) Hf Hrun". *)


  Admitted.

End inject.
