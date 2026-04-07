Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section store_weak.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  (* TEMPORARY. This is a copy. *)
  Lemma rep_ref_kind_ptr_TEMP F κ μ τ ρ ξ :
    has_kind F (RefT κ μ τ) (VALTYPE ρ ξ) ->
    ρ = AtomR PtrR /\ exists ξ', κ = VALTYPE (AtomR PtrR) ξ'.
  Proof.
    intros Hkind.
    remember (RefT κ μ τ) as ref.
    remember (VALTYPE ρ ξ) as val.
    revert Heqval Heqref.
    revert ρ ξ.
    induction Hkind using has_kind_ind'; intros; try congruence.
    - subst κ0.
      split; try congruence.
      inversion Heqref; eauto.
    - subst κ0.
      split; try congruence.
      inversion Heqref; eauto.
    - subst κ'.
      inversion H; subst; eapply IHHkind; eauto.
  Qed.


  Lemma compat_store_weak M F L wt wt' wtf wl wl' wlf es' κ κser μ τ τval π pr :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [RefT κ μ τ; τval] [RefT κ μ τ] in
    resolves_path τ π None pr ->
    has_ref_flag F pr.(pr_target) GCRefs ->
    pr.(pr_target) = SerT κser τval ->
    Forall (has_mono_size F) (pr_prefix pr) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IStore ψ π)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmask ψ Hresolves Hdrop Hser Hmonosize Htype Hcompile.
    unfold WT, WL; clear WT WL.
    cbn in Hcompile.

    inv_cg_bind Hcompile ρ ?wt ?wt ?wl ?wl es_off ?es_rest Hρ Hcompile.
    inv_cg_bind Hcompile ιs ?wt ?wt ?wl ?wl es_ρ ?es_rest Hιs Hcompile.
    inv_cg_bind Hcompile off ?wt ?wt ?wl ?wl  es_fail ?es_rest Hoff Hcompile.
    inv_cg_try_option Hρ; rename Heq_some into Hρ.
    inv_cg_try_option Hιs; rename Heq_some into Hιs.
    inv_cg_try_option Hoff; rename Heq_some into Hoff.
    inv_cg_bind Hcompile lcidxs ?wt ?wt ?wl ?wl  es_save ?es_rest Hsave Hcompile.
    inv_cg_bind Hcompile a ?wt ?wt ?wl ?wl  es_a ?es_rest Ha Hcompile.
    cbn in Ha; inversion Ha; subst; clear Ha.
    inv_cg_bind Hcompile res_emit ?wt ?wt ?wl ?wl  es_emit ?es_rest Hemit Hcompile.
    inv_cg_emit Hemit.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_case_ptr es_ptr_flags Hcompile Hptr_flags.

    (* Some clean up *)
    subst.
    clear_nils.
    destruct u. destruct p; destruct u; destruct u0.

    (* Let's dig into some of the atoms/values that are floating around *)
    unfold have_instr_type_sem.
    iIntros (??????????) "@@@@@@@@@".
    iPoseProof (values_interp_cons_l with "[$Hos]") as "(%os1 & %os2 & -> & Hos1 & Hos2)".
    iEval (rewrite values_interp_one_eq; cbn) in "Hos2".
    iPoseProof (atoms_interp_app_l with "[$Hvs]") as "(%vs1 & %vs2 & -> & Hvs1 & Hvs2)".
    iPoseProof (value_interp_ref_sz with "[$Hos1]") as "%Hos1len".
    destruct os1; [inversion Hos1len | destruct os1; [| inversion Hos1len]].
    rename a into o1.
    iEval (rewrite atoms_interp_one_inv) in "Hvs1".
    iDestruct "Hvs1" as "(%v1 & -> & Hv1)".
    set (ptr_local := sum_list_with length (F.(fc_params) ++ F.(typing.fc_locals)) + length (wl ++ wl6) ) in *.
    iEval (rewrite value_interp_eq) in "Hos1".
    iDestruct "Hos1" as (κ' Hκ') "[Harepos1 Hrefos1]".
    destruct κ'; [|by iDestruct "Harepos1" as "[[] ?]"].
    iDestruct "Harepos1" as "%Harepos1".
    cbn in Hκ'.


    assert (Hκ: eval_rep se (AtomR PtrR) = Some l).
    {
      inversion Htype as [? ? ? Hmono Hctx]; subst.
      destruct Hmono as [Hmono _].
      rewrite Forall_cons in Hmono.
      destruct Hmono as [Hmono Hmonoτval].
      rewrite Forall_singleton in Hmonoτval.
      inversion Hmono as [? ? ? Hrep Hismono]; subst.
      inversion Hrep; subst.
      apply rep_ref_kind_ptr_TEMP in H1; subst.
      destruct H1 as [-> [χ' ->]].
      unfold eval_kind in Hκ'.
      apply bind_Some in Hκ'; destruct Hκ' as [l' [Heval Hret]].
      inversion Hret; subst; auto.
    }
    cbn in Hκ; inversion Hκ; subst l.
    unfold has_areps in Harepos1.
    destruct Harepos1 as [[os1' [Hos1 Harepsos1]] Hrefflag].
    inversion Hos1; subst os1'; clear Hos1. clear Hκ.
    apply Forall2_cons_1 in Harepsos1 as [Harepo1 _].
    destruct o1; inversion Harepo1.
    apply has_values_app_inv in H0 as (evs1 & evs2 & Hevs & Hevs1 & Hevs2).
    pose proof (has_values_length _ _ Hevs1) as Hlenevs1.
    destruct evs1 as [|ev1 [|evvv' evvvs]]; try (cbn in *; congruence).
    iPoseProof (frame_interp_wl_interp with "Hframe") as "%Hwl"; first done.
    subst.
    (* clearing some useless things *)
    clear Hlenevs1 Hos1len.
    rewrite (app_assoc ([ev1] ++ evs2)).
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      rewrite <- (app_assoc [ev1]).
     (* instantiate (1 := λ f vs, (
        ⌜vs = [v1]⌝ ∗
        ⌜∀ i, i ∉ lcidxs -> f_locs f !! localimm i = f_locs fr !! localimm i⌝ ∗
        ⌜Forall2 (fun i v => f_locs f !! localimm i = Some v) lcidxs vs2⌝
        )%I).*)
      instantiate (1 := λ fr' vs, (
        ∃ val_idxs,
        ⌜vs = [v1]⌝ ∗
        ⌜frame_rel (λ i, i ∉ val_idxs) fr fr'⌝ ∗
        ⌜Forall2 (fun i v => f_locs fr' !! localimm i = Some v) lcidxs vs2⌝ ∗
        ⌜val_idxs = seq (fe_wlocal_offset fe + length wl) (length wl6)⌝ ∗
        ⌜lcidxs = map prelude.W.Mk_localidx val_idxs⌝
        )%I).

      iApply cwp_val_app; first done.
      set (temp := map prelude.W.Mk_localidx
                        (seq (fe_wlocal_offset fe + length wl)
                           (length (map translate_prim (map arep_to_prim ιs))))) in *.

      eapply cwp_save_stack_w in Hsave.
      4: {
        apply Hevs2.
      }
      2: apply Hwl.
      + destruct Hsave as (-> & -> & -> & Hsave).
        (*iApply (Hsave with "[$] [$]").
        iIntros (f' [Hfsame Hfchanged]).
        unfold fvs_combine; done.*) admit.
      + admit.
      + admit.
    }

    iIntros (fr_saved w)
      "(%val_idxs & -> & %Hfrel_fr_saved & %Hsaved & %Hval_idxs_seq & %Hval_localidxs) Hfr Hrun".

    assert (ptr_local < length (f_locs fr_saved)) as Hlen.
    {
      admit.
    }


    simpl to_consts. iEval (rewrite app_assoc).

    iApply (cwp_seq with "[Hfr Hrun]").
    {
      simpl app.
      iApply (cwp_local_tee with "[ ] [$] [$]"); first auto.
      admit.
    }

    (*
    iIntros (f0 vs0) "[-> ->] Hfr Hrun".
    eapply cwp_case_ptr in Hcompile.
    2: do 2 instantiate (1 := []).
    2,3: done.
    destruct Hcompile as (?wt & ?wt & ?wt & ?wl & ?wl & ?wl & ?es & ?es & ?es & Hcompile).
    destruct Hcompile as (Hunr & Hload1 & Hload2 & Hwt0 & Hwl0 & Hspec).




    iApply cwp_val_app.
    { instantiate (1 := [v1]).
      apply Is_true_true.
      apply/andP; split => //. by apply/eqP. }

    iApply (cwp_seq with "[Hfr Hrun Hv1 Hrefos1]").
    {
      iApply (Hspec with "[$] [$] [] [$Hv1]").
      {
        iPureIntro; cbn. rewrite list_lookup_insert. by rewrite decide_True.
      }
      iIntros "!> Hfr Hrun Hv1".
      clear_nils.
      iEval (cbn) in "Hrefos1".
      destruct μ as [|[|]]; first done.
      - (* mm *)
        unfold ref_mm_interp.
        admit.
      - (* gc *)
        unfold ref_gc_interp.
        admit.

    }

    iIntros (ff vss) "hi Hfr Hrun".
    subst.
     *)



  Admitted.

End store_weak.
