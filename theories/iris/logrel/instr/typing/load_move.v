Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.case_ptr.
Require Import RichWasm.iris.logrel.load_common.
Require Import RichWasm.iris.logrel.load_move.
Require Import RichWasm.iris.logrel.path.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section load_move.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma has_areps_one ι sv :
    has_areps [ι] sv ->
    ∃ o, sv = SAtoms [o] /\ has_arep ι o.
  Proof.
    unfold has_areps.
    intros (os & -> & Harep).
    inversion Harep; subst.
    inversion H3; subst; eauto.
  Qed.

  Lemma rt_token_update_flags ℓ off fs ws fs' ws' θ lmask :
    "Hfs" ∷ ℓ ↦layout set_flags_at off fs' fs -∗
    "Hptr" ∷ ℓ ↦heap update_path_words off ws ws' -∗
    "Htok" ∷ rt_token rti sr lmask θ -∗
    "%Hfs'" ∷ ⌜Forall2 word_has_flag fs' ws'⌝ -∗
    "%Hmask" ∷ ⌜∀ ℓ', lmask ℓ' ↔ ℓ' ≠ ℓ⌝ -∗
    ("Hfs" ∷ ℓ ↦layout set_flags_at off fs' fs ∗
     "Hptr" ∷ ℓ ↦heap update_path_words off ws ws' ∗
     "Htok" ∷ rt_token rti sr lpall θ).
  Proof.
  Admitted.


  Lemma Forall_repeat {A} {P : A → Prop} n a :
    P a →
    Forall P (repeat a n).
  Proof.
    induction n; intros Hp.
    - done.
    - cbn.
      constructor; eauto.
  Qed.

  Lemma compat_load_move M F L wt wt' wtf wl wl' wlf es' κ κ' κser σ τ τval π pr :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [RefT κ (BaseM MemMM) Mut τ] [RefT κ' (BaseM MemMM) Mut (pr_replaced pr); τval] in
    resolves_path τ π (Some (type_span σ)) pr ->
    has_size F pr.(pr_target) σ ->
    pr.(pr_target) = SerT κser τval ->
    Forall (has_mono_size F) (pr_prefix pr) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ILoad ψ π Move)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmask ψ Hresolves Hsize Hser Hmonosize Htype Hcompile.
    unfold WT, WL; clear WT WL. (* If the WT := or WL := become necessary, comment the unfold/clear*)
    cbn in Hcompile.

    (* Mechanically get through some of the first few things in compile_load *)
    inv_cg_bind Hcompile off ?wt ?wt ?wl ?wl  es_fail ?es_rest Hoff Hcompile.
    inv_cg_bind Hcompile ρ ?wt ?wt ?wl ?wl es_off ?es_rest Hρ Hcompile.
    inv_cg_bind Hcompile ιs ?wt ?wt ?wl ?wl es_ρ ?es_rest Hιs Hcompile.
    inv_cg_try_option Hρ; rename Heq_some into Hρ.
    inv_cg_try_option Hιs; rename Heq_some into Hιs.
    inv_cg_try_option Hoff; rename Heq_some into Hoff.
    inv_cg_bind Hcompile a ?wt ?wt ?wl ?wl es_a ?es_rest Ha Hcompile.
    cbn in Ha; inversion Ha; subst; clear Ha.
    inv_cg_bind Hcompile res_emit ?wt ?wt ?wl ?wl  es_emit ?es_rest Hemit Hcompile.
    inv_cg_emit Hemit.
    inv_cg_bind Hcompile () ?wt ?wt ?wl ?wl es_ptr_flags ?es_rest Hptr_flags Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl  es_case_ptr ?es_rest Hcompile Hignore.
    inv_cg_ret Hignore; subst; clear_nils.

    (* Some clean up *)
    destruct u.
    destruct p as [[] []].
    eapply cwp_case_ptr in Hcompile.
    destruct Hcompile as (?wt & ?wt & ?wt & ?wl & ?wl & ?wl & ?es & ?es & ?es & Hcompile).
    destruct Hcompile as (Hunr & Hloadmm & Hloadgc & -> & -> & Hspec).
    eapply (@cwp_set_pointer_flags Σ _ _ _ mr sr rti) in Hptr_flags.
    destruct Hptr_flags as (_ & -> & -> & Hptr_flags).
    clear_nils.
    clear_nils.
    inv_cg_bind Hloadmm ?ret ?wt ?wt ?wl ?wl es_root_hp es_load Hroot_hp Hload.
    inv_cg_ret Hroot_hp.
    inv_cg_emit Hunr.
    subst; clear_nils.
    repeat match goal with
           | x : () |- _ => destruct x
           | eqn : () = () |- _ => clear eqn
           end.
    clear Hloadgc.

    unfold have_instr_type_sem.
    unfold ψ in *; clear ψ.
    iIntros (se fr os vs evs θ B R).
    repeat iIntros "@".

    pose proof (wp_mem_load_move rti sr _ se _ _ _ _ _ _ _ _ _ _ Hload) as Hload_spec.
    destruct Hload_spec as (_ & -> & -> & Hload_spec).
    clear_nils.

    (* Opening up the val. interp *)
    iEval (rewrite values_interp_one_eq value_interp_eq) in "Hos".
    iDestruct "Hos" as "(%sk & %Hev & %Hsv & Href)".
    iEval (cbn) in "Href".
    cbn in Hev.

    (* Recovering kind-related facts *)
    rewrite -> Hser in *.
    repeat
      match goal with
      | H : has_instruction_type_ok _ _ _ |- _ => inversion H; clear H; subst
      | H : has_mono_rep_instr _ _ |- _ => inversion H; clear H; subst
      | H : Forall _ (_ :: _) |- _ => inversion H; clear H; subst
      | H : Forall _ [] |- _ =>  clear H
      | H : has_mono_rep _ _ |- _ => destruct H as (?ρ & ?Hrep & ?Hmono)
      | H : has_rep _ _ _ |- _ => inversion H; subst; clear H
      | H : has_size _ _ _ |- _ => inversion H; subst; clear H
      | H : MEMTYPE _ _ = MEMTYPE _ _ |- _ => inversion H; subst; clear H
      | H : VALTYPE _ _ = VALTYPE _ _ |- _ => inversion H; subst; clear H
      | H : has_kind ?F (RefT _ _ _ _) _ |- _ => inversion H; subst; clear H
      | H : has_kind ?F (SerT _ _) _ |- _ => inversion H; subst; clear H
      | H : has_kind ?F ?t ?k,
        H' : has_kind ?F ?t ?k' |- _ =>
          pose proof (has_kind_agree F t k k' H H'); clear H'
      end.
    cbn in Hev; inversion Hev; subst; clear Hev.
    destruct Hsv as [Hareps Hptrs].
    eapply has_areps_one in Hareps.
    destruct Hareps as (o & Ho & Harep).
    set (sz := sum_list_with arep_size ιs).
    inversion Ho; subst.
    destruct o; try done.
    iPoseProof (big_sepL2_cons_inv_l with "Hvs") as "(%v & %vs' & -> & Hv & Hvs)".
    iPoseProof (big_sepL2_nil_inv_l with "Hvs") as "->"; iClear "Hvs".
    iDestruct "Hv" as "(%n & %n32 & %Hn32 & -> & %rp & %Hrp & Hrp)".
    iDestruct "Href" as "(%ℓ & %fs & %ws & %Hp & Hfs & Hws & Ht)".
    inversion Hp; subst p; clear Hp.
    destruct rp as [|[|]]; iEval (cbn) in "Hrp"; try done; [].
    inversion Hrp.
    apply has_values_to_consts_inv in Hevs; subst.
    (* 1: storing locals *)
    iEval (rewrite app_assoc).
      set (Q := (λ f' v',
                     ⌜f' = {| W.f_locs := <[(sum_list_with length (typing.fc_locals F) + length wl)%nat :=VAL_int32 n32]> (f_locs fr);
                              W.f_inst := f_inst fr |}⌝ ∗
                             ⌜v' = [VAL_int32 n32]⌝ ∗
                     type_interp rti sr τ se (SWords ws))%I : frame -> list value -> iProp Σ).
    iApply (cwp_seq with "[Hfr Hrun Ht]").
    {
      instantiate (1 := Q).
      cbn.
      iApply (cwp_local_tee with "[Ht] [$] [$]").
      { (* TODO length of f_locs *)
        admit. }
      by iFrame.
    }
    unfold Q; clear Q.

    iIntros (f' vs') "(-> & -> & Ht) Hf Hr".

    pose proof (mono_size_eval_emp_Some (RepS ρ0) ltac:(by constructor)) as (n0 & Hev).
    iPoseProof (resolves_path_inv_sep rti sr se _ _ _ _ Hresolves
               with "[$]") as "U"; eauto.
    { rewrite Hser.
      by constructor. }
    { constructor.
      constructor.
      eapply has_kind_inv in H1.
      inversion H1.
      inversion H2.
      done. }

    iDestruct "U" as "(%Hbd & Hval & Hvput)".
    set (mask' ℓ' := ℓ' ≠ ℓ).
    iPoseProof (rt_token_mono rti sr lpall mask' with "[$Hrt]") as "Hrt".
    { done. }
    iEval (rewrite value_interp_eq) in "Hval".
    iEval (rewrite Hser) in "Hval".
    iDestruct "Hval" as "(%sk & %Hsk & %Hsv & Hval)".
    iEval (cbn) in "Hval".
    iDestruct "Hval"  as "(%os & %Hos0 & Hos)".
    inversion Hos0 as [Hos]; clear Hos0.
    iEval (rewrite type_interp_eq) in "Hos".
    iDestruct "Hos" as "(%sk' & %Hsk' & %Hsv' & Hval)".
    (* more kinding related facts: kind evaluation, etc *)
    pose proof Hsk as Hsktmp.
    rewrite bind_Some in Hsktmp.
    destruct Hsktmp as (n & Hevrep & Hret).
    inversion Hret; subst; clear Hret.
    cbn in Hevrep.
    apply fmap_Some in Hevrep.
    destruct Hevrep as (ιs' & Hevrep & ->).
    cbn in Hρ.
    pose proof Hρ as Hρtmp.
    erewrite type_rep_has_kind_agree in Hρtmp by eauto.
    inversion Hρtmp; subst ρ0; clear Hρtmp.
    pose proof Hevrep as Hevreptmp.
    erewrite eval_rep_emptyenv in Hevreptmp by eauto.
    inversion Hevreptmp; subst ιs'; clear Hevreptmp.
    assert (Hevkind : eval_kind se (VALTYPE ρ x) = Some (SVALTYPE ιs x)).
    {
      cbn.
      by erewrite eval_rep_emptyenv.
    }
    eapply type_skind_has_kind_agree in Hsk'; eauto; subst sk'.
    destruct Hsv' as [(os' & Hos' & Hareps) Hrefflag].
    inversion Hos'; subst os'; clear Hos'.
    cbn in Hev.
    rewrite Hιs in Hev; cbn in Hev; inversion Hev; subst n0; clear Hev.

    iAssert (⌜repr_pointer θ (PtrHeap MemMM ℓ) (tag_address MemMM a)⌝%I)
      with "[Hrt Hrp]" as "%Hrepr". {
      open_rt "Hrt".
      iCombine "Haddr" "Hrp" gives "%Hθ".
      inversion Hrp.
      iPureIntro.
      by constructor.
    }

    iEval (rewrite app_assoc).
    iApply (cwp_seq with "[-]").
    {
      iApply cwp_val_app.
      { eapply has_values_to_consts. }
      iApply (Hptr_flags with "[$] [$] [] [$] [$] [$] [] [-]").
      { eauto. }
      { eauto. }
      { eauto. }
      { cbn.
        rewrite list_lookup_insert_eq; first done.
        (* TODO characterize the length of f_locs *)
        admit. }
      { done. }
      { cbn.
        unfold instance_interp, instance_runtime_interp.
        by iDestruct "Hinst" as "(? & (? & ? & ? & ?) & _)". }
      iIntros "Hfs Hrt %Hmask Hown _".
      unfold fvs_combine; clear_nils.
      instantiate (1 := (λ f' vs',
                          ⌜f' = {|
                             W.f_locs := <[(sum_list_with length (typing.fc_locals F) + length wl)%nat:=VAL_int32 n32]> (f_locs fr);
                             W.f_inst := f_inst fr
                           |}⌝ ∗
                          ⌜vs' = [VAL_int32 n32]⌝ ∗ _ : iProp Σ)%I).
      iSplit; first done.
      iSplit; first done.
      iNamedAccu.
    }
    iIntros (f' vs') "(-> & -> & Haccu) Hf Hr".
    repeat iDestruct "Haccu" as "[@ Haccu]"; iDestruct "Haccu" as "@".
    iApply cwp_val_app.
    { apply has_values_to_consts. }
    iEval (change es_case_ptr with ([] ++ es_case_ptr)).
    iApply (Hspec with "[$] [$] [] [-]").
    { instantiate (1 := []).
      done. }
    { done. }
    { instantiate (2 := PtrHeap MemMM ℓ).
      by constructor. }
    { done. }
    { cbn.
      (* TODO length of f_locs *)
      admit. }
    iIntros "!> Hf Hr".
    clear_nils.

    iApply (Hload_spec with "[$] [$] [$] [$] [] [$] [$]").
    - iPureIntro; congruence.
    - cbn.
      unfold instance_interp, instance_runtime_interp.
      by iDestruct "Hinst" as "(? & (? & ? & ? & ? & ? & ? ) & _)".
    - done.
    - by rewrite sum_list_with_list_sum.
    - instantiate (1:= os).
      done.
    - iPureIntro.
      eapply ser_offsets; eauto.
    - done.
    - (* TODO length of f_locs *)
      admit.
    - (* TODO lookup in f_locs *)
      admit.
    - (* TODO length of f_locs *)
      admit.
    - done.
    - done.
    - done.
    - done.
    - by iDestruct "Hinst" as "(? & ? & ? & ? & ? & ?)".
    - by iDestruct "Hinst" as "(? & ? & ? & ? & ? & ?)".
    - iIntros (f' vs' vsf ns').
      repeat iIntros "@".
      iPoseProof (rt_token_update_flags with "[$] [$] [$] [] [//]") as "(@ & @ & @)".
      {
        iPureIntro.
        rewrite Forall2_fmap_r.
        apply Forall_Forall2_l.
        - by rewrite length_repeat.
        - by apply Forall_repeat.
      }
      unfold fvs_combine.
      iSpecialize ("Hvput" $! (map WordInt ns') with "[] []").
      {
        iPureIntro.
        unfold sz.
        by rewrite length_map Hns'.
      }
      {
        cbn [pr_expected type_span].
        unfold type_span.
        rewrite value_interp_eq.
        iExists _; cbn;try setoid_rewrite Hevrep.
        cbn.
        iSplit; first done.
        cbn.
        eauto.
        iSplit; last done.
        iPureIntro; split.
        - by rewrite length_map.
        - apply Forall_map.
          by apply Forall_true.
      }
      iSplitR; last iSplitR; last iSplitR "Htok Hown"; last iSplitL "Htok".
      + (* TODO reestablish frame_rel *)
        admit.
      + (* TODO reestablish frame_interp *)
        admit.
      + iExists (PtrA (PtrHeap MemMM ℓ) :: os).
        iSplitR "Haddr Hos".
        * iEval (cbn).
          iExists ([PtrA (PtrHeap MemMM ℓ)] :: [os]).
          iSplit; first (cbn; clear_nils; eauto with datatypes).
          iEval (cbn).
          iSplitL "Hfs Hptr Hvput".
          {
            rewrite type_interp_eq.
            iFrame "Hvput".
            iExists _.
            iSplit; first eauto.
            iSplit; last by iFrame.
            iPureIntro.
            split.
            - eexists; eauto.
            - done.
          }
          {
            iSplitL; last done.
            iEval (rewrite type_interp_eq).
            iExists _.
            iFrame.
            iSplit.
            * iPureIntro.
              eapply type_skind_has_kind_Some; eauto.
            * iPureIntro.
              cbn.
              split; eauto.
              eexists; eauto.
          }
        * iFrame.
          iExists _, _; eauto.
      + by eauto.
      + done.
  Admitted.

End load_move.
