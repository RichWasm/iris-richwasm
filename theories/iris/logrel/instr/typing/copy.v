Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.copy.
Require Import RichWasm.iris.logrel.logrel_properties.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section copy.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma cwp_save_stack_w' fe tys localidxs idxs wt wl wt' wl' es :
      run_codegen (save_stack_w fe tys) wt wl = inr (localidxs, wt', wl', es) ->
      idxs = seq (fe_wlocal_offset fe + length wl) (length tys) ->
      localidxs = map W.Mk_localidx idxs /\
      wt' = [] /\
      wl' = tys /\
      ⊢ ∀ s E fr vs esv Φ L R wlf,
        ⌜has_values esv vs⌝ -∗
        ⌜wl_interp (fe_wlocal_offset fe) (wl ++ wl' ++ wlf) fr⌝ -∗
        ⌜result_type_interp tys vs⌝ -∗
        ↪[frame] fr -∗
        ↪[RUN] -∗
        (∀ f,
            ⌜frame_rel (λ i, i ∉ idxs) fr f⌝ ∗
            ⌜Forall2 (fun i v => f_locs f !! localimm i = Some v) localidxs vs⌝ -∗
            Φ f []) -∗
        CWP (esv ++ es) @ s; E UNDER L; R {{ Φ }}.
  Proof.
    intros * Hcg ->.
    unfold save_stack_w in Hcg.
    inv_cg_bind Hcg res wt1 wt1' wl1 wl1' es1 es2 Hcg1 Hcg2.
    inv_cg_bind Hcg2 res2 wt2 wt2' wl2 wl2' es3 es4 Hcg2 Hcg3.
    inv_cg_ret Hcg3; subst.
    apply wp_wlallocs in Hcg1.
    destruct Hcg1 as (Hres1 & Hwt1 & Hwl1 & Hes1); subst.
    rewrite imap_seq in Hcg2.
    rewrite imap_seq.
    split; first done.
    replace (wl ++ tys) with (wl ++ tys ++ []) in Hcg2 by (clear_nils; done).
    eapply cwp_set_locals_w_non_fe' in Hcg2; try done; [].
    destruct Hcg2 as (-> & -> & -> & Hcg2).
    clear_nils.
    intuition.
    iIntros (s E fr vs esv Φ L R wlf) "%Hesv %Hwl %Hres Hf Hr".
    by iApply (Hcg2 with "[$]").
  Qed.

  Lemma compat_copy M F L wt wt' wtf wl wl' wlf τ es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [τ] [τ; τ] in
    has_ref_flag F τ GCRefs ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ICopy ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros * Hcopy Hok Hcompile.
    unfold compile_instr in Hcompile.
    inv_cg_bind Hcompile ρ wt1 wt1' wl1 wl1' es_nil es1 Htype_rep Hcompile.
    inv_cg_bind Hcompile ιs wt2 wt2' wl2 wl2' es_nil' es2 Heval_rep Hcompile.
    inv_cg_bind Hcompile idxs ?wt ?wt ?wl ?wl es_save ?es Hsave Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_restore1 ?es Hrestore1 Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_gcs es_restore2 Hgcs Hrestore2.
    inv_cg_try_option Htype_rep.
    inv_cg_try_option Heval_rep.
    subst.
    unfold WT, WL.
    repeat rewrite <- ?app_assoc, -> ?app_nil_l, -> ?app_nil_r in *.
    unfold have_instr_type_sem.
    unfold ψ.
    iIntros (se fr os vs evs θ B R).
    repeat iIntros "@".
    (* Showing that os = concat [os0] and Hty : value_interp τ (SAtoms os0). *)
    inversion Hcopy as [κ [Hkind Hbd]].
    iDestruct "Hos" as "(%oss & -> & Hoss)".
    iEval (cbn) in "Hoss".
    iPoseProof (big_sepL2_cons_inv_l with "Hoss") as "(%os & %oss_nil & -> & Hty & Hoss)".
    iPoseProof (big_sepL2_nil_inv_l with "Hoss") as "->"; iClear "Hoss".
    (* Showing that atoms_interp os vs. *)
    iEval (cbn [concat]; clear_nils) in "Hvs".
    (* Duplicating the semantic value Hty. *)
    iPoseProof (type_dup with "Hty") as "[Hty Hty']"; eauto; [].

    (* Inverting available kind information *)
    clear_nils.
    iEval (rewrite type_interp_eq) in "Hty".
    iDestruct "Hty" as "(%sk & %Hsk & %Hosk & Hpty)".
    apply bind_Some in Heq_some.
    destruct Heq_some as (κ' & Htk & Hρ).
    assert (κ = κ') by eauto using type_kind_has_kind_agree.
    subst κ'.
    destruct κ as [ρ' ξ| c d]; inversion Hρ; subst.
    cbn in Hbd.
    assert (sk = SVALTYPE ιs ξ).
    {
      symmetry.
      eapply type_skind_has_kind_agree; eauto.
      cbn.
      by erewrite eval_rep_emptyenv.
    }
    subst sk.
    cbn in Hosk.
    destruct Hosk as [Hareps Hptrs].
    pose proof Hareps as (os' & Hos' & Hareps').
    inversion Hos'; subst os'; clear Hos'.
    pose proof Hareps' as Hlenos.
    eapply Forall2_length in Hlenos.
    iPoseProof (big_sepL2_length with "Hvs") as "%Hlenvs".
    assert (Hlenisvs: length ιs = length vs) by (etransitivity; eauto).

    (* Characterizing the frame. *)
    iPoseProof (frame_interp_wl_interp with "Hframe") as "%Hwl".

    (* Now for the the steps of the copy compiler gadget. *)
    (* 1: save_stack_arep. *)
    iDestruct (result_type_interp_of_atoms_interp with "Hvs") as "%Hres_type"; eauto; [].
    rewrite -map_map in Hres_type.
    eapply cwp_save_stack_w' in Hsave; eauto; [].
    destruct Hsave as (-> & -> & -> & Hsave).

    iEval (rewrite app_assoc).
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      iApply (Hsave with "[//] [//] [//] [$] [$]").
      iIntros (f) "Hf".
      instantiate (1 := (λ f' vs', ⌜vs' = []⌝ ∗
         ⌜frame_rel
            (λ i : nat,
               i ∉ seq (fe_wlocal_offset fe + length wl) (length (map translate_prim (map arep_to_prim ιs))))
            fr f'⌝ ∗
         ⌜Forall2 (λ (i : prelude.W.localidx) (v : value), f_locs f' !! localimm i = Some v)
            (map W.Mk_localidx
               (seq (fe_wlocal_offset fe + length wl) (length (map translate_prim (map arep_to_prim ιs)))))
            vs⌝
                        )%I).
      by iFrame.
    }
    iIntros (f' vs') "(-> & %Hfrel & %Hall) Hf Hr".

    (* 2: restore_stack (first time). *)
    cbn in Hareps.
    simpl to_consts; simpl app.
    iApply (cwp_seq with "[Hf Hr]").
    {
      eapply cwp_restore_stack_w in Hrestore1;
        last (rewrite !length_map length_seq; eauto); [].
      destruct Hrestore1 as (_ & -> & -> & Hrestore1).
      by iApply (Hrestore1 with "[$] [$]").
    }
    iIntros (f'' vs') "(-> & ->) Hf Hr".

    (* 3: map_gc_ptrs ... (duproot ...) *)
    iEval (rewrite app_assoc).
    iApply (cwp_seq with "[Hf Hr Hvs]").
    {
      (* TODO need to finish map_gc_ptr_duproot in wp_codegen *)
      admit.
    }
    iIntros (f''' vs') "Hpost Hf Hr".

    (* 4: restore_stack (second time) *)

    iApply cwp_val_app; first apply has_values_to_consts.
    eapply cwp_restore_stack_w in Hrestore2;
      last (rewrite !length_map length_seq; eauto); [].
    destruct Hrestore2 as (_ & -> & -> & Hrestore2).
    iApply (cwp_wand with "[Hf Hr]").
    {
      iApply (Hrestore2 with "[$] [$]").
      admit.
    }
    iIntros (f v) "(-> & ->)".
    rewrite /fvs_combine.
    clear_nils.
    iFrame.
    iSplitR; [|iSplitL "Hframe"].
    - admit.
    - admit.
    - iExists (concat [os; os]).
      iSplitL "Hty' Hpty".
      + iExists [os; os].
        rewrite !big_sepL2_cons big_sepL2_nil.
        iFrame.
        iSplitR; [|iSplitL]; try done; [].
        setoid_rewrite type_interp_eq.
        iExists (SVALTYPE ιs ξ).
        by iFrame.
      + cbn [concat]; clear_nils.
        cbn -[atom_interp].
        iApply big_sepL2_app_same_length; first tauto; [].
        admit.
  Admitted.
End copy.
