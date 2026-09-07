Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.store_common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section inject_new.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma flags_words_length_eq lmask θ ℓ fs ws :
    lmask ℓ ->
    rt_token rti sr lmask θ -∗
    ℓ ↦layout fs -∗
    ℓ ↦heap ws -∗
    ⌜length fs = length ws⌝.
  Proof.
    iIntros (Hlmask) "Hrt Hlayout Hheap".
    iDestruct "Hrt" as "(%rm & %lm & %hm &
      Haddr_auth & Hroot & Hlayout_auth & Hheap_auth & Hrti &
      %Hinj & %Hrootok & Hrootmem & %Hlayoutok & %Hheapok & Hheapmem)".
    iCombine "Hlayout_auth" "Hlayout" gives "%Hlm_lookup".
    iCombine "Hheap_auth" "Hheap" gives "%Hhm_lookup".
    iPureIntro.
    specialize (Hlayoutok ℓ).
    rewrite Hlm_lookup Hhm_lookup in Hlayoutok.
    inversion Hlayoutok; subst.
    by apply Forall2_length in H1.
  Qed.

  Lemma elem_of_map_inj {A B} (f : A -> B) x (xs : list A) :
    (forall x y, f x = f y -> x = y) ->
    f x ∈ map f xs ->
    x ∈ xs.
  Proof.
    intros Hinj Helem.
    induction xs; first inversion Helem.
    inversion Helem.
    - apply Hinj in H1. rewrite -H1. constructor.
    - apply list_elem_of_further. by apply IHxs.
  Qed.

  Lemma compat_inject_new M F L wt wt' wtf wl wl' wlf es' μ i τ τs κr κv κs :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let τs' := zip_with SerT κs τs in
    let ψ := InstrT [τ] [RefT κr μ Imm (VariantT κv τs')] in
    length κs = length τs ->
    τs !! i = Some τ ->
    mono_mem μ ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IInjectNew ψ i)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    iIntros (?????? Hκs_τs Hτ [bm ->] [[Hτ_mono Href_mono] HL_ok] Hcg ????????) "@@@@@@@@@@@@".

    rewrite Forall_singleton in Hτ_mono.
    destruct Hτ_mono as (ρ & Hτρ & Hρ_mono).
    inversion Hτρ.
    rename H into Hτ_kind.
    subst F0 τ0 ρ0.
    destruct κv as [|σ ξ']; first inversion Hcg.

    rewrite Forall_singleton in Href_mono.
    destruct Href_mono as (ρref & Hρref & _).
    inversion Hρref.
    subst F0 τ0 ρ0.
    rename H into Href_kind.
    assert (has_kind F (VariantT (MEMTYPE σ ξ') τs') (MEMTYPE σ ξ')) as Hkind_variant.
    {
      inversion Href_kind.
      - inversion H1. by subst.
      - inversion H1. by subst.
    }
    rename ξ0 into ξref.
    clear Hρref.
    inversion Hkind_variant.
    subst F0 σ ξ' τs0.
    clear Hkind_variant.
    rename H1 into Hτs'_kind.

    apply lookup_lt_Some in Hτ as Hi_lt.
    rewrite -Hκs_τs in Hi_lt.
    rewrite -lookup_lt_is_Some in Hi_lt.
    destruct Hi_lt as [κ_ser Hκ_ser].
    assert (τs' !! i = Some (SerT κ_ser τ)) as Hτ'.
    { rewrite lookup_zip_with_Some. by exists κ_ser, τ. }

    pose proof Hτ' as Hτ'2.
    eapply Forall3_lookup_l in Hτ'2 as (σ & ξi & Hσ & Hξi & Hτ_ser_kind); last apply Hτs'_kind.
    cbn in Hτ_ser_kind.
    inversion Hτ_ser_kind.
    subst F0 κ τ0 σ ξ0 κ_ser κ0.
    rename ρ0 into ρi.
    rename H1 into Hρi_kind.
    clear Hτ_ser_kind Hτs'_kind.
    pose proof (has_kind_agree _ _ _ _ Hτ_kind Hρi_kind) as H.
    inversion H.
    subst ρi ξi.
    clear H Hρi_kind.

    inv_cg_bind Hcg ρ' ?wt ?wt ?wl ?wl ?es ?es Hcg_rep Hcg.
    inv_cg_try_option Hcg_rep.
    rename Heq_some into Hρ'.
    inv_cg_bind Hcg ιs ?wt ?wt ?wl ?wl ?es ?es Hcg_arep Hcg.
    inv_cg_try_option Hcg_arep.
    rename Heq_some into Hιs.
    inv_cg_bind Hcg n ?wt ?wt ?wl ?wl ?es ?es Hcg_n Hcg.
    inv_cg_try_option Hcg_n.
    rename Heq_some into Hn.
    apply bind_Some in Hn as (ns & Hns & Hn).
    fold (eval_size EmptyEnv) in Hns.
    inversion Hn.
    subst n.
    clear Hn.
    inv_cg_bind Hcg xs ?wt ?wt ?wl ?wl ?es ?es Hcg_save Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_alloc Hcg.
    inv_cg_bind Hcg laddr ?wt ?wt ?wl ?wl ?es ?es Hcg_laddr Hcg.
    apply wp_wlalloc in Hcg_laddr as (Hladdr & -> & -> & ->).
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_set_laddr Hcg.
    inv_cg_emit Hcg_set_laddr.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_flags Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_tag Hcg.
    inv_cg_emit Hcg_tag.
    inv_cg_bind Hcg ltag ?wt ?wt ?wl ?wl ?es ?es Hcg_ltag Hcg.
    apply wp_wlalloc in Hcg_ltag as (Hltag & -> & -> & ->).
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_set_ltag Hcg.
    inv_cg_emit Hcg_set_ltag.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_store_tag Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_store Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_get_laddr Hcg_regroot.
    inv_cg_emit Hcg_get_laddr.
    subst wt0 wl0 es wt2 wl2 es1 wt4 wl4 es3 wt9 wl9 wt10 wl10 es9 wt15 wl15 es14 wt16 wl16 wt17
      wl17 es16 wt24 wl24 es23 wt23 wl23 es22 wt21 wl21 es20 wt19 wl19 es18 wt18 wl18 es17 es15 wt14
      wl14 es13 wt12 wl12 es11 wt11 wl11 es8 es10 wt7 wl7 es6 wt5 wl5 es4 wt3 wl3 es2 wt1 wl1 es0
      wt' wl' es' WL WT.
    clear_nils.
    clear Hretval Hretval0 Hretval1 Hretval2.
    set WL := wl ++ wl6 ++ wl8 ++ [W.T_i32] ++ wl13 ++ [W.T_i32] ++ wl20 ++ wl22 ++ wl25 ++ wlf.
    set WT := wt ++ wt6 ++ wt8 ++ wt13 ++ wt20 ++ wt22 ++ wt25 ++ wtf.

    apply type_rep_has_kind_agree in Hτ_kind as H.
    rewrite Hρ' in H.
    inversion H.
    subst ρ'.
    clear H.

    pose proof (mapM_lookup _ _ _ i Hns) as Hns_i.
    rewrite Hσ in Hns_i.
    cbn in Hns_i.
    rewrite Hιs in Hns_i.
    cbn in Hns_i.
    symmetry in Hns_i.
    change (list_sum (map arep_size ιs)) with (areps_size ιs) in Hns_i.

    rewrite values_interp_one_eq value_interp_eq -type_interp_eq.
    iDestruct (type_interp_skind_svalue with "Hos") as "(%sκ & %Hsκ & %Hsv)".
    apply eval_rep_emptyenv with (se := se) in Hιs as Hιs_se.
    apply eval_kind_of_eval_rep with (ξ := ξ) in Hιs_se as Heval_kind.
    pose proof (type_skind_has_kind_agree _ _ _ _ _ _ Hτ_kind Hse Heval_kind Hsκ) as <-.
    iDestruct (type_interp_implies_has_areps with "Hos") as "%Hos"; first done.
    iDestruct (result_type_interp_of_atoms_interp with "Hvs") as "%Hvs"; first done.
    iDestruct (frame_interp_wl_interp with "Hframe") as "%HWL".

    rewrite app_assoc.
    eapply cwp_save_stack_w in Hcg_save as (Hxs & -> & -> & Hes5); first last.
    { by rewrite length_map length_map. }
    { by apply Is_true_true. }
    { by rewrite map_map. }
    { done. }
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      iApply (Hes5 with "[$Hfr] [$Hrun]").
      iIntros (?) "[%Hfrel %Hlocs]".
      by instantiate
           (1 := fun f vs' =>
                   (⌜frame_rel (fun i => i ∉ seq (fe_wlocal_offset fe + length wl) (length ιs)) fr f⌝ ∗
                      ⌜Forall2 (fun i v => f_locs f !! localimm i = Some v) xs vs⌝ ∗
                   ⌜vs' = []⌝)%I).
    }

    clear Hes5.
    iIntros (??) "(%Hfrel & %Hlocs & ->) Hfr Hrun".
    iDestruct (frame_interp_update_frame' with "Hframe") as "Hframe".
    3: apply Hlocs.
    { done. }
    { subst xs. by do 2 f_equal; [rewrite fe_wlocal_offset_length|rewrite !length_map]. }
    { by rewrite map_map. }
    { by rewrite -fe_wlocal_offset_length !length_map. }
    fold WL.
    clear HWL.
    iDestruct (frame_interp_wl_interp with "Hframe") as "%HWL".
    apply interp_wl_length in HWL as Hfr_len.

    assert (localimm laddr < length f.(f_locs)) as Hladdr_lt.
    {
      eapply Nat.lt_le_trans; last apply Hfr_len. subst laddr WL. cbn.
      rewrite !length_app length_cons. cbn. lia.
    }

    assert (localimm ltag < length f.(f_locs)) as Hltag_lt.
    {
      eapply Nat.lt_le_trans; last apply Hfr_len. subst ltag WL. cbn.
      rewrite !length_app !length_cons length_app length_cons. lia.
    }

    assert (localimm laddr <> localimm ltag) as Hladdr_ltag_ne.
    {
      intros Hcontra. subst laddr ltag. inversion Hcontra.
      rewrite Nat.add_cancel_l !length_app !Nat.add_cancel_l (plus_n_O (length wl8)) -Nat.add_assoc
        Nat.add_cancel_l in H0.
      cbn in H0.
      congruence.
    }

    destruct bm.
    - (* MM *)
      inv_cg_ret Hcg_regroot.
      subst wt25 wl25 es24.
      clear Hretval.
      rewrite app_nil_r.

      eapply cwp_alloc_mm in Hcg_alloc as (_ & -> & -> & Hes7).
      rewrite app_assoc.
      iApply (cwp_seq with "[-Hvs Hos Hframe]").
      {
        iApply (Hes7 with "[$Hfr] [$Hrun] [] [$Hown] [$Hrt]").
        - done.
        - destruct Hfrel as [_ <-]. by iDestruct "Hinst" as "(_ & [H _] & _)".
        - iIntros "[% Hrt] Hown _" (?????) "%Hta32 %Hta Haddr Hlayout Hheap".
          instantiate
            (1 := fun f' vs' =>
                    (∃ θ' ℓ a ta ta32 ws,
                        ⌜f' = f⌝ ∗
                          ⌜vs' = [VAL_int32 ta32]⌝ ∗
                          ⌜N_i32_repr ta ta32⌝ ∗
                          ⌜repr_root_pointer (RootHeap MemMM a) ta⌝ ∗
                          rt_token rti sr lpall θ' ∗
                          na_own logrel_nais ⊤ ∗
                          ℓ ↦addr (MemMM, a) ∗
                          ℓ ↦layout repeat FlagInt (S (list_max ns)) ∗
                          ℓ ↦heap ws)%I).
          iExists _, _, _, _, _, _.
          by iFrame.
      }

      clear Hes7.
      iIntros (??)
        "(% & % & % & % & % & % & <- & -> & %Hta32 & %Hta & Hrt & Hown & Haddr & Hlayout & Hheap)
         Hf Hrun".
      rewrite app_assoc.
      iApply (cwp_seq with "[Hf Hrun]").
      {
        iApply (cwp_local_set with "[] [$Hf] [$Hrun]").
        - done.
        - by instantiate
               (1 := fun f' vs' =>
                       (⌜f' = f0 <| f_locs ::= <[ localimm laddr := VAL_int32 ta32 ]> |>⌝ ∗
                          ⌜vs' = []⌝)%I).
      }

      iIntros (??) "[-> ->] Hf Hrun".
      eapply cwp_set_pointer_flags in Hcg_flags as (_ & -> & -> & Hes12).
      rewrite app_assoc.
      iApply (cwp_seq with "[Hrt Hown Hlayout Hf Hrun]").
      {
        iDestruct (rt_token_lpall _ _ (fun ℓ' => ℓ <> ℓ') with "Hrt") as "Hrt".
        iApply (Hes12 with "[$Hlayout] [$Hrt] [] [$Hown] [$Hf] [$Hrun]").
        - done.
        - by intros H.
        - admit.
        - by rewrite list_lookup_insert_eq.
        - done.
        - unfold set. destruct Hfrel as [_ <-]. by iDestruct "Hinst" as "(_ & (_ & _ & H & _) & _)".
        - iIntros "Hlayout Hrt _ Hown _".
          instantiate
            (1 := fun f' vs' =>
                    (⌜f' = f0 <| f_locs ::= <[ localimm laddr := VAL_int32 ta32 ]> |>⌝ ∗
                       ⌜vs' = []⌝ ∗
                       ℓ ↦layout set_flags_at 1 (flat_map arep_flags ιs) (repeat FlagInt (S (list_max ns))) ∗
                       rt_token rti sr (fun ℓ' => ℓ <> ℓ') θ' ∗
                       na_own logrel_nais ⊤)%I).
          by iFrame.
      }

      clear Hes12.
      iIntros (??) "(-> & -> & Hlayout & Hrt & Hown) Hf Hrun".
      rewrite app_nil_l app_assoc.
      iApply (cwp_seq with "[Hf Hrun]").
      {
        iApply (cwp_local_set with "[] [$Hf] [$Hrun]").
        - by rewrite length_insert.
        - by instantiate
               (1 := fun f' vs' =>
                       (⌜f' = f0 <| f_locs ::= <[ localimm laddr := VAL_int32 ta32 ]> |>
                                 <| f_locs ::= <[ localimm ltag := VAL_int32 (Wasm_int.int_of_Z i32m i) ]> |>⌝ ∗
                          ⌜vs' = []⌝)%I).
      }

      iIntros (??) "[-> ->] Hf Hrun".
      eapply wp_store1_mm_strong in Hcg_store_tag as (_ & -> & -> & Hes19).
      rewrite app_assoc.
      iApply (cwp_seq with "[Haddr Hheap Hrt Hf Hrun]").
      {
        iApply (Hes19 with "[$Hf] [$Hrun] [$Hheap] [$Haddr] [] [$Hrt]").
        - iPureIntro. by intros H.
        - iPureIntro. instantiate (1 := ta32). unfold set. cbn.
          by rewrite list_lookup_insert_ne; first rewrite list_lookup_insert_eq.
        - iPureIntro. unfold set. cbn. rewrite list_lookup_insert_eq; first done.
          by rewrite length_insert.
        - inversion Hta. by subst ta.
        - by inversion Hta.
        - by inversion Hta.
        - admit.
        - by instantiate (1 := I32A (Wasm_int.Int32.repr i)).
        - done.
        - unfold set. destruct Hfrel as [_ <-]. by iDestruct "Hinst" as "(_ & _ & _ & _ & H & _)".
        - done.
        - iIntros "Hheap Haddr Hrt".
          instantiate
            (1 := fun f' vs' =>
                    (⌜f' = f0 <| f_locs ::= <[ localimm laddr := VAL_int32 ta32 ]> |>
                              <| f_locs ::= <[ localimm ltag := VAL_int32 (Wasm_int.int_of_Z i32m i)]> |>⌝ ∗
                       ⌜vs' = []⌝ ∗
                       ℓ ↦heap path.update_path_words 0 ws (serialize_atom (I32A (Wasm_int.Int32.repr i))) ∗
                       ℓ ↦addr (MemMM, a) ∗
                       rt_token rti sr (λ ℓ' : location, ℓ ≠ ℓ') θ')%I).
          by iFrame.
      }

      clear Hes19.
      destruct Hos as (os' & Hos' & Hos).
      inversion Hos'.
      subst os'.
      clear Hos'.
      iIntros (??) "(-> & -> & Hheap & Haddr & Hrt) Hf Hrun".
      rewrite app_nil_l.
      eapply wp_store_strong_mm in Hcg_store as (_ & -> & -> & Hes21); last first.
      { admit. }
      iApply (cwp_seq with "[Hheap Haddr Hrt Hf Hrun]").
      {
        iApply (Hes21 with "[$Hf] [$Hrun] [$Hheap] [$Haddr] [] [$Hrt]").
        - iPureIntro. by intro.
        - iPureIntro. unfold set.
          by rewrite list_lookup_insert_ne; first rewrite list_lookup_insert_eq.
        - admit.
        - inversion Hta. by subst ta.
        - by inversion Hta.
        - by inversion Hta.
        - admit.
        - done.
        - done.
        - unfold set. destruct Hfrel as [_ <-]. by iDestruct "Hinst" as "(_ & _ & _ & _ & H & _)".
        - admit.
        - iIntros "Hheap Haddr Hrt".
          instantiate
            (1 := fun f' vs' =>
                    (⌜f' = f0 <| f_locs ::= <[ localimm laddr := VAL_int32 ta32 ]> |>
                              <| f_locs ::= <[ localimm ltag := VAL_int32 (Wasm_int.int_of_Z i32m i) ]> |>⌝ ∗
                     ⌜vs' = []⌝ ∗
                     ℓ ↦heap path.update_path_words 1
                               (path.update_path_words 0 ws
                                  (serialize_atom (I32A (Wasm_int.Int32.repr i))))
                               (concat (map serialize_atom os)) ∗
                     ℓ ↦addr (MemMM, a) ∗
                     rt_token rti sr (λ ℓ' : location, ℓ ≠ ℓ') θ')%I).
          by iFrame.
      }

      clear Hes21.
      iIntros (??) "(-> & -> & Hheap & Haddr & Hrt) Hf Hrun".
      rewrite app_nil_l.
      iApply (cwp_local_get with "[-Hf Hrun] [$Hf] [$Hrun]").
      { unfold set. by rewrite list_lookup_insert_ne; first rewrite list_lookup_insert_eq. }

      iModIntro.
      iSplitR; last iSplitL "Hframe"; last iSplitR "Hrt Hown"; last iSplitL "Hrt"; last done.
      + admit.
      + admit.
      + iExists [PtrA (PtrHeap MemMM ℓ)]. admit.
      + iExists θ'. admit.
    - (* GC *)
      assert (κr = VALTYPE (AtomR PtrR) GCRefs) by by inversion Href_kind.
      subst κr.
      clear Href_kind.

      eapply cwp_alloc_gc in Hcg_alloc as (_ & -> & -> & Hes7).
      rewrite app_nil_l.
      iApply (cwp_seq with "[Hrt Hown Hfr Hrun]").
      {
        iApply (Hes7 with "[$Hfr] [$Hrun] [] [$Hown] [$Hrt]").
        - done.
        - destruct Hfrel as [_ <-]. by iDestruct "Hinst" as "(_ & (_ & H & _) & _)".
        - iIntros "Hown _" (?????) "%Hta32 %Hta Hrt Hlayout Hheap".
          instantiate
            (1 := fun f' vs' =>
                    (∃ θ' ℓ ta ta32 ws,
                        ⌜f = f'⌝ ∗ ⌜vs' = [VAL_int32 ta32]⌝ ∗
                        ⌜N_i32_repr ta ta32⌝ ∗ ⌜repr_pointer θ' (PtrHeap MemGC ℓ) ta⌝ ∗
                        na_own logrel_nais ⊤ ∗ rt_token rti sr lpall θ' ∗
                        ℓ ↦layout repeat FlagInt (S (list_max ns)) ∗ ℓ ↦heap ws)%I).
          iFrame.
          by iExists _, _.
      }

      clear Hes7.
      iIntros (??) "(% & % & % & % & % & <- & -> & %Hta32 & %Hta & Hown & Hrt & Hlayout & Hheap)
                    Hf Hrun".
      iDestruct (flags_words_length_eq with "Hrt Hlayout Hheap") as "%Hws_len"; first done.
      rewrite length_repeat in Hws_len.
      destruct ws; first inversion Hws_len.
      rewrite length_cons in Hws_len.
      inversion Hws_len.
      clear Hws_len.
      rename H0 into Hws_len.

      pose proof (list_elem_of_split_length _ _ _ Hns_i) as (ns1 & ns2 & Hns_sp & Hns1).
      assert (areps_size ιs <= length ws) as Hws_lb.
      {
        rewrite -Hws_len.
        pose proof (list_max_app ns1 (areps_size ιs :: ns2)) as H.
        cbn in H.
        rewrite -Hns_sp in H.
        rewrite H Nat.max_assoc (Nat.max_comm (list_max ns1)) -Nat.max_assoc.
        apply Nat.le_max_l.
      }

      rewrite app_assoc.
      iApply (cwp_seq with "[Hf Hrun]").
      {
        iApply (cwp_local_set with "[] [$Hf] [$Hrun]").
        - done.
        - by instantiate
               (1 := fun f' vs' => (⌜f' = f <| f_locs ::= <[ localimm laddr := VAL_int32 ta32 ]> |>⌝ ∗
                                   ⌜vs' = []⌝)%I).
      }

      iIntros (??) "[-> ->] Hf Hrun".
      rewrite app_nil_l.
      eapply cwp_set_pointer_flags in Hcg_flags as (_ & -> & -> & Hes12).
      iApply (cwp_seq with "[Hown Hrt Hlayout Hf Hrun]").
      {
        iDestruct (rt_token_lpall _ _ (fun ℓ' => ℓ <> ℓ') with "Hrt") as "Hrt".
        iApply (Hes12 with "[$Hlayout] [$Hrt] [] [$Hown] [$Hf] [$Hrun]").
        - done.
        - by intro.
        - done.
        - unfold set. by rewrite list_lookup_insert_eq.
        - done.
        - unfold set. destruct Hfrel as [_ <-]. by iDestruct "Hinst" as "(_ & (_ & _ & H & _) & _)".
        - iIntros "Hlayout Hrt _ Hown _".
          instantiate
            (1 := fun f' vs' =>
                    (⌜f' = f <| f_locs ::= <[ localimm laddr := VAL_int32 ta32 ]> |>⌝ ∗
                       ⌜vs' = []⌝ ∗
                       ℓ ↦layout set_flags_at 1 (flat_map arep_flags ιs) (repeat FlagInt (S (list_max ns))) ∗
                       rt_token rti sr (λ ℓ' : location, ℓ ≠ ℓ') θ' ∗
                       na_own logrel_nais ⊤)%I).
          by iFrame.
      }

      clear Hes12.
      iIntros (??) "(-> & -> & Hlayout & Hrt & Hown) Hf Hrun".
      rewrite app_nil_l.
      rewrite app_assoc.
      iApply (cwp_seq with "[Hf Hrun]").
      {
        iApply (cwp_local_set with "[] [$Hf] [$Hrun]").
        - unfold set. by rewrite length_insert.
        - by instantiate
               (1 := fun f' vs' =>
                       (⌜f' = f <| f_locs ::= <[ localimm laddr := VAL_int32 ta32 ]> |>
                                <| f_locs ::= <[ localimm ltag := VAL_int32 (Wasm_int.int_of_Z i32m i) ]> |>⌝ ∗
                          ⌜vs' = []⌝)%I).
      }

      iIntros (??) "[-> ->] Hf Hrun".
      rewrite app_nil_l.
      eapply wp_store1_gc_strong in Hcg_store_tag as (_ & -> & -> & Hes19).
      iApply (cwp_seq with "[Hheap Hlayout Hrt Hown Hf Hrun]").
      {
        inversion Hta.
        subst θ0 μ ℓ0.
        iApply (Hes19 with "[$Hf] [$Hrun] [$Hheap] [] [] [$Hrt] [] [$Hown]").
        - done.
        - iPureIntro. by intro.
        - unfold set. destruct Hfrel as [_ <-].
          by iDestruct "Hinst" as "(_ & (_ & _ & _ & _ & _ & H) & _)".
        - done.
        - iPureIntro. unfold set.
          by rewrite list_lookup_insert_ne; first rewrite list_lookup_insert_eq.
        - iPureIntro. unfold set. rewrite list_lookup_insert_eq; first done.
          by rewrite length_insert.
        - by subst ta.
        - done.
        - done.
        - iPureIntro. cbn. lia.
        - by instantiate (1 := I32A (Wasm_int.Int32.repr i)).
        - done.
        - done.
        - unfold set. destruct Hfrel as [_ <-]. by iDestruct "Hinst" as "(_ & _ & _ & _ & H & _)".
        - unfold set. destruct Hfrel as [_ <-]. by iDestruct "Hinst" as "(_ & _ & _ & _ & _ & H)".
        - done.
        - iIntros "Hheap Hown _ Hrt".
          instantiate
            (1 := fun f' vs' =>
                    (⌜f' = f <| f_locs ::= <[ localimm laddr := VAL_int32 ta32 ]> |>
                             <| f_locs ::= <[ localimm ltag := VAL_int32 (Wasm_int.int_of_Z i32m i)]> |>⌝ ∗
                       ⌜vs' = []⌝ ∗
                       ℓ ↦layout set_flags_at 1 (flat_map arep_flags ιs) (repeat FlagInt (S (list_max ns))) ∗
                       ℓ ↦heap path.update_path_words 0 (w :: ws) (serialize_atom (I32A (Wasm_int.Int32.repr i))) ∗
                       na_own logrel_nais ⊤ ∗
                       rt_token rti sr (λ ℓ' : location, ℓ ≠ ℓ') θ')%I).
          by iFrame.
      }

      clear Hes19.
      destruct Hos as (os' & Hos' & Hos).
      inversion Hos'.
      subst os'.
      clear Hos'.
      iIntros (??) "(-> & -> & Hlayout & Hheap & Hown & Hrt) Hf Hrun".
      rewrite app_nil_l.
      eapply wp_store_strong_gc in Hcg_store as (_ & -> & -> & Hes21); last first.
      { subst xs. by rewrite length_map length_seq. }
      iApply (cwp_seq with "[Hvs Hheap Hown Hrt Hf Hrun]").
      {
        inversion Hta.
        subst θ0 μ ℓ0.
        iApply (Hes21 with "[$Hf] [$Hrun] [$Hheap] [] [] [$Hrt] [] [$Hown] [] [] [] [] [] [] [] [] [] [] [] [] [$Hvs]").
        - done.
        - iPureIntro. by intro.
        - unfold set. destruct Hfrel as [_ <-].
          by iDestruct "Hinst" as "(_ & (_ & _ & _ & _ & _ & H) & _)".
        - done.
        - iPureIntro. unfold set.
          by rewrite list_lookup_insert_ne; first rewrite list_lookup_insert_eq.
        - iPureIntro.
          eapply forall2_lookup_same' with (P := fun x => x <> localimm laddr /\ x <> localimm ltag);
            last apply Hlocs.
          + intros x [Hx_laddr Hx_ltag]. by do 2 (rewrite list_lookup_insert_ne; last done).
          + apply Forall_forall. intros x Hx. rewrite Hxs in Hx. destruct x as [x].
            apply elem_of_map_inj in Hx; last by (intros ?? H; inversion H).
            rewrite elem_of_seq in Hx. destruct Hx as [Hx_lb Hx_ub].
            split.
            * subst laddr. rewrite app_nil_r length_app !length_map Nat.add_assoc. intros H.
              cbn [localimm] in H. rewrite H in Hx_ub. apply (Nat.lt_irrefl _ Hx_ub).
            * subst ltag. rewrite app_nil_r app_nil_l !length_app !length_map !Nat.add_assoc.
              cbn [localimm length]. intros H. lia.
        - by subst ta.
        - done.
        - done.
        - iPureIntro. cbn. apply le_n_S. by rewrite drop_0 sum_list_with_list_sum.
        - done.
        - done.
        - done.
        - unfold set. destruct Hfrel as [_ <-]. by iDestruct "Hinst" as "(_ & _ & _ & _ & H & _)".
        - unfold set. destruct Hfrel as [_ <-]. by iDestruct "Hinst" as "(_ & _ & _ & _ & _ & H)".
        - iIntros "Hheap Hown _ Hrt".
          instantiate
            (1 := fun f' vs' =>
                    (⌜f' = f <| f_locs ::= <[ localimm laddr := VAL_int32 ta32 ]> |>
                             <| f_locs ::= <[localimm ltag := VAL_int32 (Wasm_int.int_of_Z i32m i) ]> |>⌝ ∗
                       ⌜vs' = []⌝ ∗
                       ℓ ↦heap path.update_path_words 1
                                 (path.update_path_words 0 (w :: ws)
                                    (serialize_atom (I32A (Wasm_int.Int32.repr i))))
                                 (concat (map serialize_atom os)) ∗
                      na_own logrel_nais ⊤ ∗
                      rt_token rti sr (λ ℓ' : location, ℓ ≠ ℓ') θ')%I).
          by iFrame.
      }

      clear Hes21.
      iIntros (??) "(-> & -> & Hheap & Hown & Hrt) Hf Hrun".
      rewrite app_nil_l.
      iApply (cwp_seq with "[Hf Hrun]").
      {
        iApply (cwp_local_get with "[] [$Hf] [$Hrun]").
        - unfold set. by rewrite list_lookup_insert_ne; first rewrite list_lookup_insert_eq.
        - by instantiate
               (1 := fun f' vs' =>
                       (⌜f' = f <| f_locs ::= <[ localimm laddr := VAL_int32 ta32 ]> |>
                                <| f_locs ::= <[ localimm ltag := VAL_int32 (Wasm_int.int_of_Z i32m i) ]> |>⌝ ∗
                          ⌜vs' = [VAL_int32 ta32]⌝)%I).
      }

      iIntros (??) "[-> ->] Hf Hrun".
      assert (1 + length (flat_map arep_flags ιs) <= length (repeat FlagInt (S (list_max ns)))) as H.
      {
        rewrite flat_map_concat_map length_arep_flags_size sum_list_with_list_sum length_repeat
          Hws_len.
        change (list_sum (map arep_size ιs)) with (areps_size ιs).
        lia.
      }
      apply updating_flags in H as (fs1 & fs_old & fs2 & Hfs & -> & Hfs_old & Hfs1).
      rewrite -Nat.add_1_l repeat_app in Hfs.
      apply app_inj_1 in Hfs as [Hfs1' Hfs]; last done.
      cbn in Hfs1'.
      subst fs1.
      clear Hfs1.
      rewrite -separate1.
      rewrite (Nat.le_add_sub (areps_size ιs) (list_max ns)) in Hfs; last lia.
      rewrite repeat_app in Hfs.
      apply app_inj_1 in Hfs as [H Hfs]; last by rewrite length_repeat Hfs_old flat_map_concat_map
                                                   length_arep_flags_size sum_list_with_list_sum.
      subst fs_old.
      rename fs2 into fs.
      symmetry in Hfs.
      clear Hfs_old.

      rewrite load_common.update_path_words_first load_common.update_path_words_empty_2
        load_common.update_path_words_succ.
      assert (0 + length (concat (map serialize_atom os)) <= length ws).
      { by rewrite length_concat map_map (load_common.has_areps_size ιs). }
      apply load_common.updating_words in H as (ws1 & ws_old & ws2 & -> & -> & H2 & H3).
      apply nil_length_inv in H3 as ->.
      rewrite app_nil_l.
      rewrite app_nil_l length_app in Hws_len, Hws_lb.
      rewrite H2 in Hws_len, Hws_lb.
      clear H2 ws_old.
      rewrite -flat_map_concat_map.
      rewrite -flat_map_concat_map in Hws_len, Hws_lb.
      apply Arith_base.plus_minus_stt in Hws_len as Hws_len'.
      rename ws2 into ws.

      iAssert (type_interp rti sr (VariantT (MEMTYPE (SumS σs) (ref_flag_lub ξs)) τs') se
                 (SWords (WordInt (Wasm_int.N_of_uint i32m (Wasm_int.Int32.repr i))
                            :: flat_map serialize_atom os ++ ws)))
        with "[Hos]" as "Hvariant".
      {
        rewrite (type_interp_eq _ _ (VariantT _ _)).
        iExists (SMEMTYPE (S (list_max ns)) (ref_flag_lub ξs)).
        iSplitR.
        { iPureIntro. apply (path.eval_sizes_emptyenv (se' := se)) in Hns. cbn. by rewrite Hns. }
        iSplitR.
        {
          iPureIntro. split.
          - cbn. f_equal. by rewrite length_app.
          - cbn. admit.
        }
        cbn.
        iExists i, (Z.to_N (Wasm_int.Int32.Z_mod_modulus i)), (flat_map serialize_atom os), ws.
        iSplitR.
        { iPureIntro. admit. }
        iSplitR; first done.
        iSplitR.
        { iPureIntro. admit. }
        change (list_lookup i (map (type_interp rti sr) τs')) with (map (type_interp rti sr) τs' !! i).
        erewrite map_lookup_helper_forwards; last done.
        rewrite (type_interp_eq _ _ (SerT _ _)).
        iExists (SMEMTYPE (areps_size ιs) ξ).
        iSplitR.
        { iPureIntro. apply eval_rep_emptyenv with (se := se) in Hιs. cbn. by rewrite Hιs. }
        iSplitR.
        { iPureIntro. cbn. admit. }
        iExists _. by iFrame.
      }

      iMod (na_inv_alloc logrel_nais _ (ns_ref ℓ) with "[Hlayout Hheap Hvariant]") as "#Hinv".
      { iModIntro. iEval (rewrite (bi.later_intro (type_interp _ _ _ _ _))) in "Hvariant". iAccu. }

      eapply roots.wp_registerroot in Hcg_regroot as (_ & -> & -> & Hes24).
      iApply (Hes24 with "[-Hf Hrun Hown Hrt] [$Hf] [$Hrun] [] [] [$Hown] [$Hrt]").
      + done.
      + done.
      + apply Is_true_true. apply has_values_to_consts.
      + iIntros (??) "%Har Hroot Hrt Hown %Har32 _".
        iSplitR; last iSplitL "Hframe"; last iSplitR "Hrt Hown"; last iSplitR "Hown"; last done.
        * iPureIntro. split; last by (unfold set; destruct Hfrel as [_ <-]).
          apply frame_rel_mask_mono with (lmask' := lmask) in Hfrel; last first.
          { intros x Hx Hcontra. unfold lmask, wlmask in Hx. rewrite elem_of_seq in Hcontra. lia. }
          intros x Hx. unfold set. rewrite !list_lookup_insert_ne.
          -- destruct Hfrel as [H _]. by apply H.
          -- subst laddr. cbn [localimm]. rewrite app_nil_r length_app !length_map.
             intros Hcontra. unfold lmask, wlmask in Hx. lia.
          -- subst ltag. cbn [localimm]. rewrite app_nil_r app_nil_l !length_app !length_map.
             intros Hcontra. unfold lmask, wlmask in Hx. lia.
        * unfold WL. rewrite !app_nil_l (app_assoc [W.T_i32]) (app_assoc wl).
          iApply frame_interp_update_frame; last done.
          -- cbn [length app plus].
             by rewrite !length_app !length_map Nat.add_assoc -fe_wlocal_offset_length.
          -- instantiate (1 := [VAL_int32 ta32; VAL_int32 (Wasm_int.int_of_Z i32m i)]).
             constructor.
             ++ rewrite list_lookup_insert_ne; last first.
                {
                  intros H. apply Hladdr_ltag_ne. rewrite H. subst laddr.
                  by rewrite app_nil_r !length_app !length_map Nat.add_assoc.
                }
                unfold set. subst laddr. cbn. rewrite app_nil_r length_app !length_map Nat.add_assoc.
                rewrite list_lookup_insert_eq; first done.
                by rewrite app_nil_r length_app !length_map Nat.add_assoc in Hladdr_lt.
             ++ constructor; last done. subst ltag.
                rewrite app_nil_r app_nil_l !length_app !length_map !Nat.add_assoc Nat.add_1_r.
                unfold set. rewrite list_lookup_insert_eq; first done.
                rewrite length_insert.
                by rewrite app_nil_r app_nil_l !length_app !length_map !Nat.add_assoc Nat.add_1_r
                  in Hltag_lt.
          -- constructor; first by eexists. by constructor; first eexists.
          -- split; last done. intros x Hx. unfold set. cbn.
             apply notin_seq_S in Hx as [H Hx1].
             apply notin_seq_S in H as [_ Hx0].
             rewrite Nat.add_0_r in Hx0.
             rewrite list_lookup_insert_ne; first rewrite list_lookup_insert_ne; first done.
             ++ subst laddr. symmetry. by rewrite app_nil_r !length_app !length_map !Nat.add_assoc.
             ++ subst ltag. symmetry.
                by rewrite app_nil_r app_nil_l !length_app !length_map !Nat.add_assoc.
        * iExists [PtrA (PtrHeap MemGC ℓ)].
          iSplitR "Hroot".
          -- rewrite values_interp_one_eq value_interp_eq. iExists (SVALTYPE [PtrR] GCRefs).
             iSplitR; first done. iSplitR.
             {
               iPureIntro. split.
               - eexists. split; first done. repeat constructor.
               - repeat constructor.
             }
             cbn.
             iExists _, _, _.
             by iSplitR.
          -- cbn. iSplitL; last done. iExists _, _. iSplitR.
             { iPureIntro. apply Har32. }
             iSplitR; first done. iExists (RootHeap MemGC ar). by iFrame.
        * iExists θ'. admit.
      + done.
      + done.
      + unfold set. destruct Hfrel as [_ <-].
        by iDestruct "Hinst" as "(_ & (_ & _ & _ & _ & H & _) & _)".
  Admitted.

End inject_new.
