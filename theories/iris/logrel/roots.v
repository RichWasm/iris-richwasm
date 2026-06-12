From mathcomp Require Import eqtype ssrbool.

Require Import RichWasm.util.
Require Import RichWasm.compiler.memory.
Require Import RichWasm.iris.numerics.
Require Import RichWasm.iris.runtime.
Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section roots.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.


  Lemma extract_root_pointer a ℓ e rm :
    a ↦root ℓ -∗
    ghost_map_auth rw_root (1 / 2) rm -∗
    root_memory sr e rm -∗
    ⌜root_ok e rm⌝ -∗
    ∃ ah ah32,
      ⌜N_i32_repr ah ah32⌝ ∗
      ⌜repr_pointer e (PtrHeap MemGC ℓ) ah⌝ ∗
      N.of_nat (sr_mem_gc sr)↦[wms][a] bits (VAL_int32 ah32) ∗
      (N.of_nat (sr_mem_gc sr)↦[wms][a] bits (VAL_int32 ah32) -∗
       a ↦root ℓ ∗
       ghost_map_auth rw_root (1 / 2) rm  ∗
       root_memory sr e rm).
  Proof.
    iIntros "Hr Hroots Hrootm %Hrootok".
    iCombine "Hr" "Hroots" gives "%Hrm".
    pose proof (map_Forall_lookup_1 _ _ _ _ Hrootok Hrm) as [a' He].
    iPoseProof (big_sepM_lookup_acc _ _ _ _ Hrm with "Hrootm") as "[Ha Hrootm]".
    iDestruct "Ha" as "(%ah & %ah32 & %Hrep & %Hah32 & Hptr)".
    iExists ah, ah32.
    iFrame.
    repeat (iSplit; first by auto).
    iIntros "Hpt".
    iFrame.
    iApply "Hrootm"; auto.
  Qed.

  Lemma wp_loadroot wt wl ret wt' wl' es_load :
    run_codegen (loadroot mr) wt wl = inr (ret, wt', wl', es_load) ->
    ret = () /\
    wt' = [] /\
    wl' = [] /\
    ∀ evs a n n32 ℓ e rm,
      N_i32_repr n n32 ->
      has_values evs [VAL_int32 n32] ->
      repr_root_pointer (RootHeap MemGC a) n ->
      root_ok e rm ->
      ⊢ ∀ s E B R Φ f,
          ↪[frame] f -∗
          ↪[RUN] -∗
          ⌜f.(f_inst).(inst_memory) !! memimm mr.(mr_gcmem) = Some sr.(sr_mem_gc)⌝ -∗
          a ↦root ℓ -∗
          ghost_map_auth rw_root (1 / 2) rm -∗
          root_memory sr e rm -∗
          ▷ (∀ ah ah32,
              ⌜N_i32_repr ah ah32⌝ -∗
              ⌜repr_pointer e (PtrHeap MemGC ℓ) ah⌝ -∗
              a ↦root ℓ -∗
              ghost_map_auth rw_root (1 / 2) rm -∗
              root_memory sr e rm -∗
              Φ f [VAL_int32 ah32]) -∗
          CWP evs ++ es_load @ s; E UNDER B; R {{ Φ }}.
  Proof.
    unfold loadroot.
    intros Hcg.
    inv_cg_emit Hcg; subst.
    repeat (split; first done).
    intros * Hn32 Hevs Han Hrok.
    iIntros (s E B R Φ f) "Hf Hrun %Hmem Hrt Hrm Hrmok HΦ".
    iPoseProof (extract_root_pointer with "Hrt [$] [$] [//]")
      as "(%ah & %bs & %Hbs & %Hrep & Hroot & Hsave)".
    inversion Han; subst.
    cbn in Hn32.
    apply Is_true_true in Hevs.
    rewrite (has_values_to_consts_inv _ _ Hevs).
    replace a with ((a - 1) + 1)%N by lia.
    iApply (cwp_load with "[$Hroot] [-Hf Hrun] [$] [$]"); eauto.
    - by f_equal.
    - replace ((a - 1) + 1)%N with a by lia.
      iIntros "!> Hpt".
      iPoseProof ("Hsave" with "Hpt") as "(Hroot & Hrm & Hrmok)".
      iApply ("HΦ" with "[//] [//] [$] [$] [$]"); eauto.
  Qed.

  Lemma wp_registerroot wt wl ret wt' wl' es_register :
    run_codegen (registerroot mr) wt wl = inr (ret, wt', wl', es_register) ->
    ret = () /\
    wt' = [] /\
    wl' = [] /\
      ∀ θ evs ℓ ah ah32,
        repr_pointer θ (PtrHeap MemGC ℓ) ah ->
        N_i32_repr ah ah32 ->
        has_values evs [VAL_int32 ah32] ->
      ⊢ ∀ f B R s E lmask Φ,
        (∀ ar ar32,
           ⌜repr_root_pointer (RootHeap MemGC ar) (tag_address MemGC ar)⌝ -∗
           ar ↦root ℓ -∗ rt_token rti sr lmask θ -∗ na_own logrel_nais E -∗
           ⌜N_i32_repr (tag_address MemGC ar) ar32⌝ -∗
           instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
           Φ f [VAL_int32 ar32]) -∗
        ↪[frame] f -∗
        ↪[RUN] -∗
        ⌜↑ns_fun (N.of_nat (sr_func_registerroot sr)) ⊆ E⌝ -∗
        na_own logrel_nais E  -∗
        rt_token rti sr lmask θ -∗
        instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
        CWP evs ++ es_register @ s; E UNDER B; R {{ Φ }}.
  Proof.
    unfold registerroot.
    intros Hcg.
    inv_cg_emit Hcg; subst.
    repeat (split; first done).
    intros * Hptr Hrah Hevs.
    iIntros (f B R s E lmask Φ) "HΦ Hf Hrun %HE Htok Hrt Hreg".
    apply Is_true_true in Hevs.
    rewrite (has_values_to_consts_inv _ _ Hevs).
    clear Hevs evs.
    unfold instance_rt_func_interp.
    iDestruct "Hreg" as "(%cl & %Hregspc & %Hcl & #Hinv)".
    iPoseProof (na_inv_acc with "Hinv Htok") as "Hopen"; eauto.
    iApply fupd_cwp.
    iMod "Hopen".
    unfold spec_registerroot in Hregspc.
    iDestruct "Hopen" as "[Hop Hcl]".
    iDestruct "Hcl" as "[Htok Hsave]".
    iMod "Hop".
    iModIntro.
    iAssert ((▷ N.of_nat (sr_func_registerroot sr)↦[wf]cl ={E}=∗ na_own logrel_nais E)%I) with "[Hsave Htok]" as "Hsave".
    {
      iIntros "Hcl".
      iApply "Hsave".
      iFrame.
    }
    iApply (cwp_wand_strong with "[Hrt Hop Hf Hrun]").
    { iApply (Hregspc with "[$] [$] [$] [$]"); eauto. }
    { eauto. }
    { eauto. }
    {
      cbn.
      iIntros (f' v) "(<- & Hcl' & [%θ' Hrt] & %ar & %tar & %tar32 & -> & %Hrep & %Hrepr & Hroot)".
      iSpecialize ("Hsave" with "Hcl'").
      iMod "Hsave".
      inversion Hrepr; subst.
      iApply ("HΦ" with "[//] [$] [$] [$] [//] [-]").
      iExists _; eauto.
    }
  Qed.

  Lemma wp_unregisterroot wt wl ret wt' wl' es_unregister :
    run_codegen (unregisterroot mr) wt wl = inr (ret, wt', wl', es_unregister) ->
    ret = () /\
    wt' = [] /\
    wl' = [] /\
      ∀ θ evs tar tar32 ar,
        repr_root_pointer (RootHeap MemGC ar) tar ->
        N_i32_repr tar tar32 ->
        has_values evs [VAL_int32 tar32] ->
      ⊢ ∀ f B R s E lmask Φ ℓ,
        ar ↦root ℓ -∗
        (rt_token rti sr lmask θ -∗ na_own logrel_nais E -∗
         instance_rt_func_interp mr.(mr_func_unregisterroot) sr.(sr_func_unregisterroot) (spec_unregisterroot rti sr) f.(f_inst) -∗
         Φ f []) -∗
        ↪[frame] f -∗
        ↪[RUN] -∗
        ⌜↑ns_fun (N.of_nat (sr_func_unregisterroot sr)) ⊆ E⌝ -∗
        na_own logrel_nais E  -∗
        rt_token rti sr lmask θ -∗
        instance_rt_func_interp mr.(mr_func_unregisterroot) sr.(sr_func_unregisterroot) (spec_unregisterroot rti sr) f.(f_inst) -∗
        CWP evs ++ es_unregister @ s; E UNDER B; R {{ Φ }}.
  Proof.
    unfold unregisterroot.
    intros Hcg.
    inv_cg_emit Hcg; subst.
    repeat (split; first done).


    intros * Hrootptr Hrtar Hevs.
    iIntros (f B R s E lmask Φ ℓ) "Hroot HΦ Hf Hrun %HE Htok Hrt Hreg".
    apply Is_true_true in Hevs.
    rewrite (has_values_to_consts_inv _ _ Hevs).
    clear Hevs evs.
    unfold instance_rt_func_interp.
    iDestruct "Hreg" as "(%cl & %Hregspc & %Hcl & #Hinv)".
    iPoseProof (na_inv_acc with "Hinv Htok") as "Hopen"; eauto.
    iApply fupd_cwp.
    iMod "Hopen".
    unfold spec_unregisterroot in Hregspc.
    iDestruct "Hopen" as "[Hop Hcl]".
    iDestruct "Hcl" as "[Htok Hsave]".
    iMod "Hop".
    iModIntro.
    iAssert ((▷ N.of_nat (sr_func_unregisterroot sr)↦[wf]cl ={E}=∗ na_own logrel_nais E)%I) with "[Hsave Htok]" as "Hsave".
    {
      iIntros "Hcl".
      iApply "Hsave".
      iFrame.
    }
    iApply (cwp_wand_strong with "[Hrt Hop Hf Hrun Hroot]").
    { iApply (Hregspc with "[$] [$] [$] [$] [$]"); eauto. }
    { eauto. }
    { eauto. }
    {
      cbn.
      iIntros (f' v) "(<- & <- & Hcl' & Hrt)".
      iSpecialize ("Hsave" with "Hcl'").
      iMod "Hsave".
      iApply ("HΦ" with "[$] [$] [-]").
      iExists _; eauto.
    }
  Qed.
  (*
   The duproot lemma doesn't hang on to the root resource.
   *)
  Lemma wp_duproot wt wl ret wt' wl' es_dup :
    run_codegen (duproot mr) wt wl = inr (ret, wt', wl', es_dup) ->
    ret = () /\
    wt' = [] /\
    wl' = [] /\
    ∀ evs a n n32 rm θ ℓ,
      N_i32_repr n n32 →
      has_values evs [VAL_int32 n32] ->
      repr_root_pointer (RootHeap MemGC a) n ->
      root_ok θ rm ->
      ⊢ ∀ s E lmask B R Φ f Q,
        ↪[frame] f -∗
        ↪[RUN] -∗
        ⌜inst_memory (f_inst f) !! memimm (mr_gcmem mr) = Some (sr_mem_gc sr)⌝ -∗
        ⌜↑ns_fun (N.of_nat (sr_func_registerroot sr)) ⊆ E⌝ -∗
        a ↦root ℓ -∗
        ghost_map_auth rw_root (1 / 2) rm -∗
        root_memory sr θ rm -∗
        (a ↦root ℓ -∗ ghost_map_auth rw_root (1 / 2) rm -∗ root_memory sr θ rm -∗ rt_token rti sr lmask θ ∗ Q) -∗
        na_own logrel_nais E -∗
        instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
        (∀ ar ar32,
           ⌜repr_root_pointer (RootHeap MemGC ar) (tag_address MemGC ar)⌝ -∗
           ⌜N_i32_repr (tag_address MemGC ar) ar32⌝ -∗
           ar ↦root ℓ -∗
           rt_token rti sr lmask θ -∗
           Q -∗
           na_own logrel_nais E -∗
           instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
           Φ f [VAL_int32 ar32]) -∗
        CWP evs ++ es_dup @ s; E UNDER B; R {{ Φ }}.
  Proof.
    unfold duproot.
    intros Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es_load ?es_reg Hload Hreg.
    eapply wp_loadroot in Hload.
    destruct Hload as (_ & -> & -> & Hload).
    apply wp_registerroot in Hreg.
    destruct Hreg as (-> & -> & -> & Hreg).
    repeat (split; first reflexivity).
    intros evs a n n32 rm e ℓ Hnrep Hevs Hreproot Hrootok.
    specialize (Hload evs a n n32 ℓ e rm Hnrep Hevs Hreproot Hrootok).
    iIntros (s E lmask B R Φ f Q) "Hf Hrun %Hmems %Hmask Htok Hrootm Hrootok Hclose Hinv Hreg HΦ".
    rewrite app_assoc.
    iApply (cwp_seq with "[-Hinv Hreg HΦ]").
    {
      iApply (Hload with "[$] [$] [//] [$] [$] [$]").
      iIntros "!>" (ah ah32 Harep32 Hrep) "Hroot Htok Hrootm".
      instantiate (1:= (fun f' v' =>
                         ⌜f' = f⌝ ∗
                         ∃ ah' ah32',
                             ⌜N_i32_repr ah' ah32'⌝ ∗
                             ⌜repr_pointer e (PtrHeap MemGC ℓ) ah'⌝ ∗
                             ⌜v' = [VAL_int32 ah32']⌝ ∗
                             rt_token rti sr lmask e ∗ Q
                         )%I).
      cbn.
      iSplit; auto.
      iExists _, _.
      iSplit; auto.
      iSplit; auto.
      iSplit; auto.
      iApply ("Hclose" with "[$] [$] [$]").
    }
    cbn.
    cbn; iIntros (f' vs) "(-> & %ah & %ah32 & %Hah & %Hrep & -> & Htok & HQ) Hf Hrun".
    iApply (Hreg with "[HΦ HQ] [$Hf] [$Hrun] [] [$Hinv] [$Htok] [$Hreg]"); eauto.
    - by apply Is_true_true, has_values_to_consts.
    - iIntros (ar ar32 Har) "Hroot' Htok' Hown %Harrep Hinst".
      iApply ("HΦ" with "[//] [//] [$] [$] [$] [$] [$]").
  Qed.

  Lemma wp_root_to_heap locidx wt wl wt' wl' es :
    run_codegen (root_to_heap mr MemGC (Mk_localidx locidx)) wt wl = inr ((), wt', wl', es) ->
    ∀ a n n32 ℓ e rm,
      N_i32_repr n n32 ->
      repr_root_pointer (RootHeap MemGC a) n ->
      root_ok e rm ->
      ⊢ ∀ s E B R Φ f,
          ↪[frame] f -∗
          ↪[RUN] -∗
          ⌜f_locs f !! locidx = Some (VAL_int32 n32)⌝ -∗
          ⌜f.(f_inst).(inst_memory) !! memimm mr.(mr_gcmem) = Some sr.(sr_mem_gc)⌝ -∗
          a ↦root ℓ -∗
          ghost_map_auth rw_root (1 / 2) rm -∗
          root_memory sr e rm -∗
          ▷^3 (∀ ah ah32,
               let f' := {| W.f_locs := <[localimm (Mk_localidx locidx):=VAL_int32 ah32]> (f_locs f);
                           W.f_inst := f_inst f |} in
              ⌜N_i32_repr ah ah32⌝ -∗
              ⌜repr_pointer e (PtrHeap MemGC ℓ) ah⌝ -∗
              a ↦root ℓ -∗
              ghost_map_auth rw_root (1 / 2) rm -∗
              root_memory sr e rm -∗
              Φ f' []) -∗
          CWP es @ s; E UNDER B; R {{ Φ }}.
  Proof.
    unfold root_to_heap.
    intros Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es_get ?es_rest Hget Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es_lr ?es_set Hlr Hset.
    inv_cg_emit Hget.
    inv_cg_emit Hset.
    clear_nils; subst.
    intros * Hn32 Hrep Hroot.
    iIntros (s E B R Φ f) "Hf Hrun %Hloc %Hmem Hroot Hrm Hrmem HΦ".
    iApply (cwp_seq with "[Hf Hrun HΦ]").
    {
      iApply (cwp_local_get with "[HΦ] [$] [$]"); first eauto.
      iModIntro.
      instantiate (1 := (λ f' v', ⌜f' = f⌝ ∗ ⌜v' = [VAL_int32 n32]⌝ ∗ _)%I).
      iSplit; first done.
      iSplit; first done.
      iApply "HΦ".
    }
    iIntros (f' vs) "(-> & -> & HΦ) Hf Hrun".
    rewrite app_assoc.
    iApply (cwp_seq with "[-]").
    {
      pose proof (wp_loadroot _ _ _ _ _ _ Hlr) as (_ & -> & -> & Hloadroot).
      iApply (Hloadroot with "[$] [$] [//] [$] [$] [$]").
      - eauto.
      - apply Is_true_true, has_values_to_consts.
      - eauto.
      - eauto.
      - iModIntro.
        iIntros (ah ah32) "%Hah32 %Hrepr Hroot Hrm Hrmem".
        instantiate
          (1 := (λ f' vs',
             ∃ ah ah32,
             ⌜f' = f⌝ ∗
             ⌜vs' = [VAL_int32 ah32]⌝ ∗
             ⌜N_i32_repr ah ah32⌝ ∗
             ⌜repr_pointer e (PtrHeap MemGC ℓ) ah⌝ ∗
             _
          )%I).
        iExists ah, ah32.
        iSplit; first done.
        iSplit; first done.
        iSplit; first done.
        iSplit; first done.
        iNamedAccu.
    }
    iIntros (f' vs') "(%ah & %ah32 & -> & -> & %Hah32 & %Hrepr & @ & @ & @ & @) Hf Hrun".
    clear Hretval0 Hretval.
    iApply (cwp_local_set with "[-Hrun Hf] [$] [$]");
      first eauto using lookup_lt_Some.
    iModIntro.
    iSpecialize ("HΦ" $! ah ah32 with "[//] [//]").
    by repeat iSpecialize ("HΦ" with "[$]").
  Qed.

End roots.
