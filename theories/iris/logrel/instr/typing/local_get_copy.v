Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section local_get_copy.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_local_get_copy M F L wt wt' wtf wl wl' wlf es' i τ :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [] [τ] in
    L !! i = Some τ ->
    has_ref_flag F τ NoRefs ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ILocalGet ψ Copy i)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmask Ψ Hlookup_L_i Hrf Hok Hcg.
    subst Ψ.
    cbn [compile_instr] in Hcg.

    unfold compile_local_get in Hcg.
    inv_cg_bind Hcg ?local_ixs ?wt ?wt ?wl ?wl ?es es_get_locals Hlocal_ixs Hget_locals.
    inv_cg_try_option Hlocal_ixs; subst.

    apply run_codegen_get_locals in Hget_locals as H.
    destruct H as (_ & -> & ->).

    unfold local_indices in Heq_some.
    apply bind_Some in Heq_some as [ηs [Hlookup_fe_i Hlocal_ixs]].
    apply Some_inj in Hlocal_ixs.

    subst WT WL.
    clear_nils.
    simplify_eq.

    (* Iris Proof *)
    iIntros (? ? ? ? ? ? ? ?) "%Hsem %Hhas_values #Hinst #Hlabels #Hreturn Hvs Hos Hframe Hrt Hown Hfr Hrun".

    iDestruct (values_interp_nil_l with "Hos") as "->".
    iDestruct (atoms_interp_nil_l with "Hvs") as "->".
    apply has_values_length in Hhas_values.
    destruct evs as [|]; last done.
    clear_nils.
    iClear (Hhas_values) "Hvs Hos".

    iDestruct (frame_interp_locals_ctx_length with "Hframe") as "%HL_len".

    iDestruct "Hframe" as
      "(%oss & %vss_L & %vs_WL & %Hfr & %Hhas_prims & %Hresult & Hatoms & Hval)".

    have Hsplit := take_drop_middle (fe_locals fe) i ηs Hlookup_fe_i.
    replace (typing.fc_locals F) with (fe_locals fe) in *; last done.
    rewrite <- Hsplit in Hhas_prims.
    apply List.Forall2_app_inv_l in Hhas_prims as (vss_L_pre & vss_L_rest & Hpre & Hrest & ->).
    destruct vss_L_rest as [| vs_L_i vss_L_post]; [inversion Hrest |].
    apply Forall2_cons_1 in Hrest as [Hmid Hpost].

    iDestruct (locals_interp_lookup _ _ _ _ _ _ _ Hlookup_L_i with "Hval") as (oss_pre os_i oss_post Hoss_eq) "[Hval_pre [Hval_i Hval_post]]".

    iEval (rewrite Hoss_eq) in "Hatoms".
    iDestruct (locals_interp_length with "Hval_pre") as %Hlen_pre.
    iDestruct (locals_interp_length with "Hval_post") as %Hlen_post.
    apply Forall2_length in Hpre as Hvs_pre_len.
    apply Forall2_length in Hmid as Hvs_L_i_len.
    apply Forall2_length in Hpost as Hvs_post_len.

    have Hlen_oss_pre : length oss_pre = length vss_L_pre.
    { rewrite <- Hlen_pre, length_take, <- Hvs_pre_len, length_take. lia. }
    have Hlen_oss_post : length oss_post = length vss_L_post.
    { rewrite <- Hlen_post, length_drop, <- Hvs_post_len, length_drop. lia. }

    iDestruct (big_sepL2_app_inv _ _ _ _ _ with "Hatoms") as "[Hatoms_pre Hatoms_rest]"; first by left.
    iDestruct (big_sepL2_cons with "Hatoms_rest") as "[Hatoms_i Hatoms_post]".

    eapply cwp_restore_stack_w in Hget_locals.
    2: {
      instantiate (1 := vs_L_i).
      rewrite length_map.
      rewrite length_seq.
      by apply Forall2_length in Hmid.
    }
    destruct Hget_locals as (_ & _ & _ & Hget_locals).
    iApply (cwp_wand with "[Hfr Hrun]").
    {
      iApply (Hget_locals with "[$] [$]").
      iPureIntro.
      rewrite !concat_app in Hfr.
      rewrite concat_cons in Hfr.
      rewrite -!app_assoc in Hfr.
      apply Forall2_concat in Hpre.
      apply Forall2_length in Hpre as Hvss_L_pre_concat_len.
      rewrite sum_list_with_length_concat.
      rewrite Hvss_L_pre_concat_len.
      rewrite Hvs_L_i_len.
      rewrite Forall2_fmap_l.
      unfold compose.
      simpl.
      apply Forall2_same_length_lookup.
      split.
      { apply length_seq. }
      intros j idx v Hlookup_lidxs Hlookup_v.
      rewrite Hfr.
      apply lookup_seq in Hlookup_lidxs as [-> Hlt].
      rewrite lookup_app_r; [| lia].
      rewrite lookup_app_l; [| lia].
      rewrite -Hlookup_v.
      f_equal.
      lia.
    }
    clear Hget_locals.
    iIntros (?? [-> ->]).
    iSplit; first done.

    inversion Hok; subst.
    have Htype_rep := Forall2_lookup_lr _ _ _ _ _ _ H0 Hlookup_L_i Hlookup_fe_i.
    destruct Htype_rep as (ρ & Hhas_rep & Heval_rep_prim).

    unfold eval_rep_prim in Heval_rep_prim.
    destruct (eval_rep EmptyEnv ρ) as [sρ|] eqn:Heval_rep; simpl in Heval_rep_prim; [| discriminate].
    injection Heval_rep_prim as <-.
    have Heval_rep_se := eval_rep_emptyenv ρ sρ Heval_rep se.

    have Heval_kind : eval_kind se (VALTYPE ρ NoRefs) = Some (SVALTYPE sρ NoRefs).
    { unfold eval_kind. rewrite Heval_rep_se. reflexivity. }

    inversion Hhas_rep; subst.

    inversion Hrf; subst.
    destruct H2 as [H2 Hnorefs].

    have Hkind_agree := has_kind_agree _ _ _ _ H1 H2.
    subst x.
    cbn in Hnorefs.
    destruct ξ; try inversion Hnorefs.
    clear H1 Hnorefs.

    have Hskind := type_skind_has_kind_Some F se τ _ _ H2 Hsem Heval_kind.

    iDestruct (value_interp_ref_flag_atoms _ _ _ _ _ _ _ Hskind with "Hval_i") as %Href.
    have Hatoms_pers := atoms_interp_norefs_persistent se os_i vs_L_i Href.
    iPoseProof "Hatoms_i" as "#Hatoms_i".

    iFrame "Hatoms_i".

    pose proof (kinding_sound rti sr mr _ _ _ _ _ H2 Hsem Heval_kind) as [Hpers _].
    cbn in Hpers.
    iDestruct "Hval_i" as "#Hval_i".

    iDestruct (values_interp_one_eq with "Hval_i") as "Hval_i'".
    iFrame "Hval_i'".
    iSplitR "Hrt Hown"; last iFrame.
    iExists (oss_pre ++ [os_i] ++ oss_post).
    iExists (vss_L_pre ++ [vs_L_i] ++ vss_L_post).
    iFrame.
    iFrame (Hfr Hresult).
    iSplit.
    {
      iPureIntro.
      rewrite <- (take_drop_middle (fe_locals fe) i (map arep_to_prim sρ) Hlookup_fe_i).
      apply Forall2_app; first done.
      apply Forall2_cons; by split.
    }
    iSplitR; first by iApply big_sepL2_singleton.

    unfold locals_interp.
    iEval (rewrite <- (take_drop_middle L i τ Hlookup_L_i)).
    simpl.
    by iFrame.
  Qed.

End local_get_copy.
