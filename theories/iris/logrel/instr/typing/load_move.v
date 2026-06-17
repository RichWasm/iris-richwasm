Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.case_ptr.
Require Import RichWasm.iris.logrel.load.
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

  Lemma layout_ok_lmask_mono lm hm lmask1 lmask2 :
    (∀ ℓ, lmask1 ℓ → lmask2 ℓ) →
    layout_ok lmask2 lm hm →
    layout_ok lmask1 lm hm.
  Proof.
    unfold layout_ok.
    intros Hle Hall.
    eauto using map_Forall2_impl.
  Qed.

  Lemma rt_token_lmask_mono lmask1 lmask2 θ :
    (∀ ℓ, lmask1 ℓ → lmask2 ℓ) →
    rt_token rti sr lmask2 θ -∗
    rt_token rti sr lmask1 θ.
  Proof.
    iIntros (Hle) "Hrt".
    open_rt "Hrt".
    unfold rt_token.
    iExists rm, lm, hm.
    iFrame.
    iPureIntro; intuition eauto using layout_ok_lmask_mono.
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
    inv_cg_bind Hloadmm ?ret ?wt ?wt ?wl ?wl es_root_hp ?es_rest Hroot_hp Hload.
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
      { admit. }
      by iFrame.
    }
    unfold Q; clear Q.

    iIntros (f' vs') "(-> & -> & Ht) Hf Hr".

    iPoseProof (resolves_path_inv_sep rti sr se _ _ _ _ Hresolves
               with "[$]") as "U"; eauto.
    { rewrite Hser.
      by constructor. }
    { constructor.
      constructor.
      admit. }
    { admit. }
    { admit. }

    iDestruct "U" as "(%Hbd & Hval & Hvput)".
    set (mask' ℓ' := ℓ' ≠ ℓ).
    iPoseProof (rt_token_lmask_mono mask' lpall with "Hrt") as "Hrt".
    { done. }
    iEval (rewrite value_interp_eq) in "Hval".
    iPoseProof (virt_to_phys_slice_store_acc_weak with "[] [$] [$] [$]")
      as "(%hm & %Hhml & %Hdoms & Hlocs & Hnophys & (%ns & %ns32 & %Hns & Hphys & Hws) & Hclose)".
    {
      admit.
    }

    iEval (rewrite app_assoc).
    iApply (cwp_seq with "[-]").
    {
      iApply cwp_val_app.
      { eapply has_values_to_consts. }
      admit.
    }

    (* TODO need a wp_load1_move_mm lemma *)
    (* TODO need a wp_load_move_mm lemma *)
    (* TODO need a path lemma? should be shared with store_strong. *)
  Admitted.

End load_move.
