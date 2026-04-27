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

    unfold local_indices in Heq_some.
    apply bind_Some in Heq_some as [ηs [Hlookup_fe_i Hlocal_ixs]].
    apply Some_inj in Hlocal_ixs.

    subst WT WL.
    clear_nils.
    simplify_eq.

    inversion Hok; subst.
    apply lookup_lt_Some in Hlookup_L_i as Hlen_L.
    have Hi := Forall2_lookup_lr _ _ _ _ _ _ H0 (list_lookup_insert_eq L i τ' Hlen_L) Hlookup_fe_i.
    destruct Hi as (ρ & Hhas_rep & Heval_rep_prim).
    inversion Hhas_rep; subst.
    unfold eval_rep_prim in Heval_rep_prim.
    destruct (eval_rep EmptyEnv ρ) as [ιs|] eqn:Heval_rep; simpl in Heval_rep_prim; [| discriminate].
    apply Some_inj in Heval_rep_prim.

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

    have : subskind_of (SVALTYPE l r) (SVALTYPE ιs ξ).
    { by eapply type_skind_eval_rep_emptyenv. }
    intros Hsubskind.
    have Hlen_eq : length ιs = length ηs by rewrite <- Heval_rep_prim, length_map.
    have Hlen_eq' : length (map translate_arep ιs) = length ηs.
    1: by rewrite length_map.
    inversion Hsubskind; subst.

    iPoseProof "Hskind_as_type" as "H".
    iDestruct "H" as "[%Hhas_areps %Href]".

    iDestruct (result_type_interp_of_atoms_interp with "Hvs") as "%Hres_type_vs"; first done.

    eapply cwp_set_locals_w in Hset_locals.
    5: {
      instantiate (1 := map translate_arep ιs).
      instantiate (1 := (sum_list_with length (take i (fe_locals fe)))).
      done.
    }
    6: by rewrite !length_map.
    5: done.
    3: done.
    2: apply has_values_to_consts.
    2: {
      unfold fe_wlocal_offset.
      subst fe.
      rewrite !length_map.
      rewrite Hlen_eq.
      erewrite sum_list_with_take_S_lookup; last done.
      etransitivity.
      2: apply Nat.le_add_r.
      apply sum_list_with_take_le.
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
      destruct Hnotinj as [Hnotinfe _].
      unfold fe_wlocal_offset in Hnotinfe.
      intro Hin.
      rewrite list_elem_of_In in_seq in Hin.
      rewrite Hlen_eq' in Hin.
      erewrite sum_list_with_take_S_lookup in Hin; last done.
      have Hle := sum_list_with_take_le length (fe_locals fe) (S i).
      subst fe; simpl in Hle, Hnotinfe.
      lia.
    }
  admit.

  Admitted.

End local_set.
