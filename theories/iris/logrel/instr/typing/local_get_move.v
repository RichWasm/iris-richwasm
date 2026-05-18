Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section local_get_move.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_local_get_move M F L wt wt' wtf wl wl' wlf es' i τ ηs :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [] [τ] in
    let L' := <[ i := type_plug_prim ηs ]> L in
    F.(typing.fc_locals) !! i = Some ηs ->
    L !! i = Some τ ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ILocalGet ψ Move i)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L'.
  Proof.

    intros fe WT WL lmask Ψ L' Hlookup_F_i Hlookup_L_i Hok Hcg.
    subst Ψ.
    cbn [compile_instr] in Hcg.

    unfold compile_local_get in Hcg.
    inv_cg_bind Hcg ?local_ixs ?wt ?wt ?wl ?wl ?es es_get_locals Hlocal_ixs Hget_locals.
    inv_cg_try_option Hlocal_ixs; subst.

    apply run_codegen_get_locals in Hget_locals as H.
    destruct H as (_ & -> & ->).

    unfold local_indices in Heq_some.
    apply bind_Some in Heq_some as [ηs' [Hlookup_fe_i Hlocal_ixs]].
    apply Some_inj in Hlocal_ixs.

    replace (typing.fc_locals F) with (fe_locals fe) in Hlookup_F_i; last done.
    rewrite Hlookup_fe_i in Hlookup_F_i.
    apply Some_inj in Hlookup_F_i as ->.

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
    iFrame "Hrt Hown".

    inversion Hok; subst.
    eapply Forall2_lookup_lr in H0; try done.
    2: apply list_lookup_insert_eq.
    2: by apply lookup_lt_is_Some_1.
    destruct H0 as (ρ & Hhas_rep & Heval_rep).

    (* TODO: temp *)
    iDestruct (values_interp_one_eq with "Hval_i") as "Hval_i".
    iFrame "Hval_i Hatoms_i".
    (* TODO: temp *)

    unfold frame_interp.
    iFrame (Hfr Hresult).
    iExists (oss_pre ++ [_] ++ oss_post).
    iSplit.
    {
      iPureIntro.
      rewrite <- (take_drop_middle (fe_locals fe) i _ Hlookup_fe_i).
      apply Forall2_app; first done.
      apply Forall2_cons; by split.
    }
    iFrame.

  Admitted.
End local_get_move.
