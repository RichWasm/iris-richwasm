From mathcomp Require Import ssrbool eqtype.
Require Import RichWasm.compiler.memory.
Require Import RichWasm.util.
Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.case_ptr.
Require Import RichWasm.iris.logrel.roots.
Require Import RichWasm.iris.logrel.load_common.
Require Import RichWasm.iris.logrel.store_common.
Require Import RichWasm.iris.logrel.path.
Require Import RichWasm.iris.logrel.rt_token.
Require Import RichWasm.iris.numerics.
(* TODO: fix imports *)

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section new.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.


  Lemma notin_seq_S start n i :
    i ∉ seq start n /\ i <> start + n
    <-> i ∉ seq start (S n).
  Proof.
    rewrite seq_S.
    set_solver.
  Qed.


  Lemma compat_new M F L wt wt' wtf wl wl' wlf κ κser μ β τ es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [τ] [RefT κ μ β (SerT κser τ)] in
    mono_mem μ ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (INew ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmask ψ Hmono_mem Hok Hcg.
    destruct μ; try done.
    simpl in Hcg.
    inv_cg_bind Hcg ρ ?wt ?wt ?wl ?wl ?es ?es_rest Hρ Hcg; subst.
    inv_cg_try_option Hρ; rename Heq_some into Hρ; subst.
    inv_cg_bind Hcg ιs ?wt ?wt ?wl ?wl es_arep ?es_rest Hιs Hcg; subst.
    inv_cg_try_option Hιs; rename Heq_some into Hιs.
    inv_cg_bind Hcg lidxs ?wt ?wt ?wl ?wl es_save_stack ?es_rest Hsave_stack Hcg; subst.
    eapply cwp_save_stack_w' in Hsave_stack as (H & -> & -> & Hsave_stack_spec); last done.
    instantiate (1 := wl3 ++ wlf) in Hsave_stack_spec.
    clear_nils.
    subst lidxs. (* doing -> above doesn't substitutate all appearance of lidxs for some reason... *)
    set (lidxs := map memory.W.Mk_localidx (seq (fe_wlocal_offset fe + length wl) (length (map translate_prim (map arep_to_prim ιs))))) in *.
    inv_cg_bind Hcg () ?wt ?wt ?wl ?wl es_alloc ?es_rest Halloc Hcg; subst.
    inv_cg_bind Hcg addr_lidx ?wt ?wt ?wl ?wl es_wlalloc ?es_rest Hwlalloc Hcg; subst.
    apply wp_wlalloc in Hwlalloc as (-> & -> & -> & ->).
    clear_nils.
    set (addr_lidx := Mk_localidx (fe_wlocal_offset fe + length (wl ++ map translate_prim (map arep_to_prim ιs)))) in *.
    inv_cg_bind Hcg () ?wt ?wt ?wl ?wl es_set_addr ?es_rest Hset_addr Hcg; subst.
    inv_cg_emit Hset_addr; subst.
    inv_cg_bind Hcg () ?wt ?wt ?wl ?wl es_set_pointer_flags ?es_rest Hset_pointer_flags Hcg; subst.
    inv_cg_bind Hcg () ?wt ?wt ?wl ?wl es_mstore_vals ?es_rest Hmstore_vals Hcg; subst.
    inv_cg_bind Hcg () ?wt ?wt ?wl ?wl es_get_addr ?es_rest Hget_addr Hbase; subst.
    inv_cg_emit Hget_addr; subst.
    eapply cwp_set_pointer_flags in Hset_pointer_flags as (_ & -> & -> & Hptr_flags_spec).

    subst WL WT.

    clear_nils.
    simplify_eq.


    iIntros (????????) "@@@@@@@@@@@@".

    rewrite values_interp_one_eq.

    inversion Hok; clear Hok; subst.
    inversion H; clear H; subst.
    inversion H1; subst; clear H5.
    inversion H2; subst; clear H6.
    destruct H4 as (?ρ & ?Hrep & ?Hmono).
    cbn in Hρ.
    inversion Hrep; subst; clear Hrep.
    rename H into Hhas_kind.
    apply type_rep_has_kind_agree in Hhas_kind as Htype_rep.
    destruct H5 as (ρ_ref & Hrep_ref & His_mono_rep).
    inversion Hrep_ref; subst.
    rewrite Htype_rep in Hρ; inversion Hρ; subst.
    rename H into Href_has_kind.

    rewrite value_interp_eq.
    iEval (cbn -[pre_type_interp type_skind]) in "Hos".
    iDestruct "Hos" as "(%sκ_temp & %Htypeskindtemp & %Harepsoon & Hpre_type_interp)".
    destruct sκ_temp; try (inversion Harepsoon; done).
    assert (ιs = l /\ ξ = r) as (<- & <-). {
    pose proof (type_skind_eval_rep_emptyenv se F ρ _ _ τ _ _
                  Hhas_kind Hse Hιs Htypeskindtemp).
      done.
    }
    destruct Harepsoon as (Hareps & Hforall_ref_flag_interp).

    iPoseProof (frame_interp_wl_interp with "Hframe") as "%Hwl".
    iDestruct (result_type_interp_of_atoms_interp with "Hvs") as "%Hres_type_vs"; try done.


    (* Step 1: Save stack *)
    iEval (rewrite app_assoc).
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      iApply (Hsave_stack_spec with "[//] [//] [] [$] [$]").
      {
        unfold translate_arep in Hres_type_vs.
        rewrite map_comp. done.
      }
      iIntros (f) "Hf".
      instantiate (1 := (λ fr' vs', ⌜vs' = []⌝ ∗
         ⌜frame_rel
            (λ i : nat,
               i ∉ seq (fe_wlocal_offset fe + length wl) (length (map translate_prim (map arep_to_prim ιs))))
            fr fr'⌝ ∗
         ⌜Forall2 (λ (i : prelude.W.localidx) (v : value), f_locs fr' !! localimm i = Some v)
            (map W.Mk_localidx
               (seq (fe_wlocal_offset fe + length wl) (length (map translate_prim (map arep_to_prim ιs)))))
            vs⌝
                        )%I).
      by iFrame.
    }
    iIntros (fr_save_stack vs') "(-> & %Hfrel & %Hall) Hfr Hrun".
    clear_nils.
    clear Hsave_stack_spec.

    destruct b.
    1: refine ?[MemMM]. 2: refine ?[MemGC].

    [MemMM]: {
      (* Step 2: Allocate the new value *)
      destruct (cwp_alloc_mm mr sr rti (areps_size ιs) _ _ _ _ _ _ Halloc) as (_ & -> & -> & Halloc_spec).
      iAssert (instance_rt_func_interp mr.(mr_func_mmalloc) sr.(sr_func_mmalloc) (runtime.spec_mmalloc rti sr) fr_save_stack.(f_inst)) as "#Hmmalloc".
      {
        rewrite -(proj2 Hfrel).
        iDestruct "Hinst" as "(_ & [Hmmalloc _] & _)".
        iExact "Hmmalloc".
      }
      iApply (cwp_seq with "[Hfr Hrun Hown Hrt]").
      {
        iApply (Halloc_spec _ _ _ _ ⊤ _ _ with "Hfr Hrun [] Hown Hrt Hmmalloc").
        1: iPureIntro; solve_ndisj.
        iIntros "Hrt' Hown' _ %ℓ %a %ta %ta32 %ws %Htarepr %Hrootrepr Haddr Hlayout Hheap".
        instantiate (1 := (λ fr' vs',
          ∃ ℓ a ta ta32 ws,
            ⌜vs' = [VAL_int32 ta32]⌝ ∗
            ⌜fr' = fr_save_stack⌝ ∗
            ⌜N_i32_repr ta ta32⌝ ∗
            ⌜repr_root_pointer (RootHeap MemMM a) ta⌝ ∗
            ℓ ↦addr (MemMM, a) ∗
            ℓ ↦layout repeat FlagInt (areps_size ιs) ∗
            ℓ ↦heap ws ∗
            (∃ θ', rt_token rti sr lpall θ') ∗
            na_own logrel_nais ⊤)%I).
        iExists ℓ, a, ta, ta32, ws.
        iSplit; first done.
        iSplit; first done.
        iSplit; first (iPureIntro; exact Htarepr).
        iSplit; first (iPureIntro; exact Hrootrepr).
        iFrame.
      }
      iIntros (??) "(%ℓ & %a & %ta & %ta32 & %ws & -> & -> & %Htarepr' & %Hrootrepr' & Haddr & Hlayout & Hheap & Hrt' & Hown') Hfr Hrun".

      iDestruct "Hrt'" as "(%θ' & Hrt')".

      apply wp_ret in Hbase as (_ & -> & -> & ->).
      clear_nils.

      (* Pure facts from repr_root_pointer *)
      have Hrootmod : (a `mod` 4 = 0)%N. { inversion Hrootrepr'; done. }
      have Hrootnz : (a ≠ 0)%N. { inversion Hrootrepr'; done. }
      have Hta_eq : ta = tag_address MemMM a. { inversion Hrootrepr'; done. }
      subst ta.

      (* Extract length ws = areps_size ιs from layout_ok before restricting mask *)
      iAssert (rt_token rti sr lpall θ' ∗ ℓ ↦layout repeat FlagInt (areps_size ιs) ∗ ℓ ↦heap ws ∗
               ⌜length ws = areps_size ιs⌝)%I
        with "[Hrt' Hlayout Hheap]" as "(Hrt' & Hlayout & Hheap & %Hws_length)". {
        iDestruct "Hrt'" as "(%rm & %lm & %hm &
          Haddr_auth & Hroot & Hlayout_auth & Hheap_auth & Hrti &
          %Hinj & %Hrootok & Hrootmem & %Hlayoutok & %Hheapok & Hheapmem)".
        iCombine "Hlayout_auth" "Hlayout" gives "%Hlm_lookup".
        iCombine "Hheap_auth" "Hheap" gives "%Hhm_lookup".
        iSplitL "Haddr_auth Hroot Hlayout_auth Hheap_auth Hrti Hrootmem Hheapmem".
        - iExists rm, lm, hm. iFrame.
          do 3 (iSplit; [iPureIntro; assumption |]); iPureIntro; assumption.
        - iSplitL "Hlayout"; first iFrame.
          iSplitL "Hheap"; first iFrame.
          iPureIntro.
          unfold layout_ok in Hlayoutok.
          unfold map_Forall2 in Hlayoutok.
          specialize (Hlayoutok ℓ).
          rewrite Hlm_lookup Hhm_lookup in Hlayoutok.
          inversion Hlayoutok; subst.
          apply Forall2_length in H4; try done.
          rewrite length_repeat in H4.
          done.
      }

      (* Weaken rt_token mask to exclude ℓ *)
      set (rtmask := (λ (l : location), l ≠ ℓ)).
      iAssert (rt_token rti sr rtmask θ') with "[Hrt']" as "Hrt'".
      { by iApply rt_token_lpall. }

      iAssert (⌜θ' !! ℓ = Some (MemMM, a)⌝)%I as "%Hθ_lookup".
      {
        iDestruct "Hrt'" as "(%rm & %lm & %hm &
          Haddr_auth & Hroot & Hlayout_auth & Hheap_auth & Hrti &
          %Hinj & %Hrootok & Hrootmem & %Hlayoutok & %Hheapok & Hheapmem)".
        by iCombine "Haddr_auth" "Haddr" gives "%H".
      }

      have Hrepr_ptr : repr_pointer θ' (PtrHeap MemMM ℓ) (tag_address MemMM a).
      { apply RepPtrHeap; done. }
      have Hnort : ¬ rtmask ℓ. { unfold rtmask. tauto. }

      (* Get setflag func interp from instance_interp. *)
      iAssert (instance_rt_func_interp mr.(mr_func_setflag) sr.(sr_func_setflag)
                 (runtime.spec_setflag rti sr) fr_save_stack.(f_inst)) as "#Hsetflag". {
        rewrite -(proj2 Hfrel).
        iDestruct "Hinst" as "(_ & (_ & _ & ? & _) & _)".
        iFrame "#".
      }

      have Hlt_fr_save_stack : localimm addr_lidx < length (f_locs fr_save_stack). {
        have Hlt_fr : localimm addr_lidx < length (f_locs fr). {
          have Hbound := interp_wl_length _ _ _ Hwl.
          unfold addr_lidx; cbn in Hbound |- *.
          rewrite !length_app in Hbound; rewrite length_app; simpl in Hbound. lia.
        }
        have Hnotin : localimm addr_lidx ∉ seq (fe_wlocal_offset fe + length wl) (length (map translate_prim (map arep_to_prim ιs))). {
          intro Hin; apply elem_of_seq in Hin.
          unfold addr_lidx in Hin; cbn in Hin; rewrite length_app in Hin; lia.
        }
        have Hlookup_eq := (proj1 Hfrel) _ Hnotin.
        have [v Hv] := lookup_lt_is_Some_2 (f_locs fr) _ Hlt_fr.
        apply (lookup_lt_Some (f_locs fr_save_stack) _ v).
        congruence.
      }

      iEval (rewrite app_assoc).
      (* Step 4: store ta32 to local *)
      iApply (cwp_seq with "[Hfr Hrun]").
      {
        iApply (cwp_local_set with "[] Hfr Hrun"); first done.
        iNext.
        instantiate (1 := (λ fr' vs',
          ⌜vs' = []⌝ ∗
          ⌜fr' = {| W.f_locs := <[localimm addr_lidx := VAL_int32 ta32]> (f_locs fr_save_stack);
                     W.f_inst := f_inst fr_save_stack |}⌝ ∗
          (_ : iProp Σ))%I).
        iSplit; first done.
        iSplit; first done.
        iNamedAccu.
      }
      iIntros (fr_set_addr ?) "(-> & %Hframe_set & Haccu) Hfr Hrun".
      iClear "Haccu".
      clear_nils.

      assert (frame_rel (λ i, i ≠ localimm addr_lidx) fr_save_stack fr_set_addr) as Hfrel_save_set.
      {
        subst fr_set_addr.
        unfold frame_rel.
        split; last done.
        unfold mask_locs_eq.
        intros.
        simpl.
        symmetry.
        apply list_lookup_insert_ne.
        done.
      }
      pose proof (frame_rel_mask_trans_combine _ _ _ _ _ Hfrel Hfrel_save_set) as Hfrel_set_addr.
      eapply frame_rel_mask_mono in Hfrel_set_addr; last first.
      {
        instantiate (1 := λ i , i ∉ seq (fe_wlocal_offset fe + length wl) (S (length (map translate_prim (map arep_to_prim ιs))))).
        intros i Hnotin.
        simpl in Hnotin.
        simpl.
        rewrite length_app.
        rewrite Nat.add_assoc.
        rewrite notin_seq_S.
        done.
      }
      eapply frame_rel_Forall2_update' in Hall; last first.
      2: {
        instantiate (1 := fr_set_addr).
        instantiate (1 := [localimm addr_lidx]).
        eapply frame_rel_mask_mono; last done.
        set_solver.
      }
      2: done.
      {
        eapply Forall_impl.
        - apply seq_forall_leq.
        - intros i Hi Hin.
          apply list_elem_of_singleton in Hin as ->.
          subst addr_lidx.
          simpl in Hi.
          rewrite length_app in Hi.
          lia.
      }

      specialize Hptr_flags_spec with (fr := fr_set_addr) (ta := tag_address MemMM a) (ta32 := ta32)
        (lmask := rtmask) (θ := θ') (μ := MemMM) (ℓ := ℓ).
      have Hav : f_locs fr_set_addr !! localimm addr_lidx = Some (VAL_int32 ta32). {
        rewrite Hframe_set. cbn. apply list_lookup_insert_eq. done.
      }
      specialize (Hptr_flags_spec Htarepr' Hnort Hrepr_ptr Hav).

      (* Step 5: set pointer flag *)
      iApply (cwp_seq with "[Hlayout Hrt' Hown' Hfr Hrun]").
      {
        iApply (Hptr_flags_spec $! _ ⊤ with "[$] [$] [] [$] [$] [$] [] []").
        { iPureIntro. solve_ndisj. }
        { rewrite Hframe_set; cbn. iExact "Hsetflag". }
        iIntros "Hlayout' Hrt' _ Hown' #_".
        instantiate (1 := (λ fr' vs', ⌜fr' = fr_set_addr /\ vs' = []⌝ ∗ (_ : iProp Σ))%I).
        iSplit; first (iPureIntro; done).
        iNamedAccu.
      }
      iIntros (??) "((-> & ->) & Haccu) Hfr Hrun".
      repeat iDestruct "Haccu" as "[@ Haccu]"; iDestruct "Haccu" as "@".
      clear_nils.

      (* Step 6: store new value in memory *)
      have Hlen : length lidxs = length ιs. { unfold lidxs; rewrite !length_map length_seq; done. }
      destruct (wp_store_strong_mm rti sr mr addr_lidx 0 ιs lidxs _ _ _ _ _ _ Hlen Hmstore_vals)
        as (_ & -> & -> & Hmstore_spec).
      iPoseProof (atoms_interp_to_weak_memMM with "[$] [$]") as "[Hrt' Hvs_weak]".
      iApply (cwp_seq with "[-]").
      {
        iApply (Hmstore_spec with "[$] [$] [$] [$] [//] [$]
          [] [] [] [] [] [] [] [] [] [$Hvs_weak] [-]").
        - iPureIntro. exact Hav.
        - iPureIntro. done.
        - iPureIntro. exact Htarepr'.
        - iPureIntro. exact Hrootmod.
        - iPureIntro. exact Hrootnz.
        - iPureIntro.
          rewrite sum_list_with_list_sum.
          unfold areps_size in Hws_length; cbn in Hws_length.
          lia.
        - iPureIntro. destruct Hareps as (os' & Hoseq & Hfarep).
          by inversion Hoseq.
        - iPureIntro. done.
        - unfold base_mem_idx.
          iDestruct "Hinst" as "(_ & _ & _ & _ & %Hmemmm & _)".
          iPureIntro.
          rewrite Hframe_set; cbn.
          rewrite -(proj2 Hfrel).
          exact Hmemmm.
        - iIntros "Hheap' Haddr' Hrt'".
          instantiate (1 := (λ fr' vs', ⌜fr' = fr_set_addr /\ vs' = []⌝ ∗ (_ : iProp Σ))%I).
          iSplit; first (iPureIntro; done).
          iNamedAccu.
      }
      iIntros (??) "((-> & ->) & Haccu) Hfr Hrun".
      repeat iDestruct "Haccu" as "[@ Haccu]"; iDestruct "Haccu" as "@".
      clear_nils.

      (* Step 7: get addr to stored value *)
      iApply (cwp_wand with "[Hfr Hrun]").
      {
        iApply (cwp_local_get with "[] [$] [$]").
        { exact Hav. }
        iNext.
        instantiate (1 := (λ fr' vs', ⌜fr' = fr_set_addr /\ vs' = [VAL_int32 ta32]⌝)%I).
        done.
      }
      iIntros (??) "(-> & ->)".

      assert (frame_rel lmask fr fr_set_addr) as Hfrel_lmask_set_addr.
      {
        eapply frame_rel_mask_mono; [| exact Hfrel_set_addr].
        intros i [Hi_lo Hi_hi].
        intro Hin. apply elem_of_seq in Hin. lia.
      }
      iFrame (Hfrel_lmask_set_addr).
      do 2 iEval (rewrite app_assoc) in "Hframe".
      do 2 iEval (rewrite -(app_assoc wl)) in "Hframe".

      iPoseProof (frame_interp_update_frame _ _ _ _ _ _ _ _ _ _ _ fr_set_addr with "[$Hframe]") as "Hframe".
      4: exact Hfrel_set_addr.
      1: by rewrite length_app (Nat.add_comm _ (length [W.T_i32])) fe_wlocal_offset_length.
      2: {
        apply Forall2_app.
        - by rewrite /result_type_interp /translate_arep -map_comp in Hres_type_vs.
        - instantiate (1 := [VAL_int32 ta32]).
          apply List.Forall2_cons; last done.
          simpl.
          eauto.
      }
      {
        rewrite seq_S.
        rewrite Forall2_fmap_l in Hall.
        cbn in Hall.
        unfold compose in Hall.
        simpl in Hall.

        apply Forall2_app.
        - exact Hall.
        - rewrite Forall2_cons; split; last done.
          unfold addr_lidx in Hav.
          rewrite length_app Nat.add_assoc in Hav.
          done.
      }
      iEval (rewrite -!app_assoc) in "Hframe".
      iFrame "Hframe".
      iFrame.

      open_rt "Hrt'".
      iCombine "Hlayout'" "Hlayout" gives "%Hlm_lookup".
      iCombine "Hheap'" "Hheap" gives "%Hhm_lookup".
      assert (Hnewlayout : layout_ok lpall lm hm).
      {
        unfold layout_ok, map_Forall2 in *.
        intros k. specialize (Hlayoutok k).
        destruct (decide (k = ℓ)) as [->|Hkne].
        - rewrite Hlm_lookup Hhm_lookup. constructor. intros _.
          have Hfa2 := has_areps_imp_word_has_flag _ _ Hareps.
          have Hfl_len : length (flat_map arep_flags ιs) = areps_size ιs.
          { rewrite flat_map_concat_map length_arep_flags_size.
            unfold areps_size. exact sum_list_with_list_sum. }
          have Hwslen' : length (concat (map serialize_atom os)) = length ws.
          { rewrite <- flat_map_concat_map.
            have Hthis := Forall2_length _ _ _ Hfa2.
            rewrite <- flat_map_concat_map in Hthis.
            lia. }
          rewrite (update_path_words_all _ _  Hwslen').
          pose proof (updating_flags 0 (flat_map arep_flags ιs) (repeat FlagInt (areps_size ιs))
              ltac:(rewrite length_repeat; lia))
            as (fs1 & fs_old & fs2 & Hfs_eq & Hset_eq & Hlen_old & Hlen1).
          destruct fs1 as [| ? ?]; [| simpl in Hlen1; lia].
          rewrite app_nil_l in Hfs_eq, Hset_eq.
          have Hfs2_nil : fs2 = [].
          { have Hfs2_len : length fs2 = 0.
            { have := f_equal length Hfs_eq.
              rewrite length_repeat length_app Hlen_old Hfl_len. lia. }
            by destruct fs2. }
          subst fs2.
          rewrite app_nil_r in Hset_eq.
          rewrite Hset_eq flat_map_concat_map.
          rewrite flat_map_concat_map in Hfa2.
          exact Hfa2.
        - inversion Hlayoutok.
          + specialize (H4 Hkne); constructor; done.
          + constructor.
      }
      clear Hlayoutok.
      iAssert (rt_token rti sr lpall θ')
        with "[Haddr Hroot Hlayout Hheap Hrti Hrootmem Hheapmem]" as "Hrt'".
      { unfold rt_token. iExists rm, lm, hm. iFrame. done. }
      iFrame.
      iExists [PtrA (PtrHeap MemMM ℓ)].

      (* Derive pure kinding facts from Hok before the split *)
      assert (Hκ : κ = VALTYPE (AtomR PtrR) AnyRefs). {
        inversion Href_has_kind; subst; try done.
      }
      subst κ.
      assert (Hκser : κser = MEMTYPE (RepS ρ) ξ). {
        inversion Hrep_ref; subst; clear Hrep_ref.
        inversion H; subst.
        inversion H5; subst.
        have Heq := has_kind_agree F τ _ _ H6 Hhas_kind.
        inversion Heq; subst; done.
      }
      subst κser.
      have Hevρse : eval_rep se ρ = Some ιs := eval_rep_emptyenv _ _ Hιs se.
      have Hevκser : eval_kind se (MEMTYPE (RepS ρ) ξ) = Some (SMEMTYPE (areps_size ιs) ξ). {
        unfold eval_kind; cbn; rewrite Hevρse; cbn; done.
      }
      have Htypeskind_ser : type_skind (Σ:=Σ) se (SerT (MEMTYPE (RepS ρ) ξ) τ) =
          Some (SMEMTYPE (areps_size ιs) ξ). {
        cbn; exact Hevκser.
      }
      have Hfa2 : Forall2 word_has_flag (concat (map arep_flags ιs)) (flat_map serialize_atom os).
      { apply Forall2_impl with (P := fun f w => Is_true (word_has_flag f w)).
        1: exact (has_areps_imp_word_has_flag _ _ Hareps).
        intros f w H; destruct (word_has_flag f w); done.
      }
      have Hwslen' : length (concat (map serialize_atom os)) = length ws. {
        rewrite <- flat_map_concat_map.
        have Hthis := Forall2_length _ _ _ Hfa2.
        rewrite <- flat_map_concat_map in Hthis.
        have Hfl_len : length (flat_map arep_flags ιs) = areps_size ιs. {
          rewrite flat_map_concat_map length_arep_flags_size.
          unfold areps_size; exact sum_list_with_list_sum.
        }
        lia.
      }
      iSplitR "Haddr'".
      * iEval (cbn).
        iExists ([[PtrA (PtrHeap MemMM ℓ)]]).
        iSplit; first (cbn; clear_nils; eauto with datatypes).
        iEval (cbn).
        iSplit; last done.
        rewrite type_interp_eq.
        iExists (SVALTYPE [PtrR] AnyRefs).
        iSplitR.
        { iPureIntro; cbn; unfold eval_kind; cbn; done. }
        iSplitR.
        { iPureIntro; split.
          - unfold has_areps; eexists; split; first done.
            constructor; [unfold has_arep; done | constructor].
          - unfold ref_flag_atoms_interp, forall_satoms; cbn.
            apply Forall_cons; by split.
        }
        cbn.
        destruct β.
        + (* Mut *)
          iExists ℓ, _, _.
          iSplitR; first done.
          iFrame "Hlayout' Hheap'".
          rewrite (update_path_words_all _ _ Hwslen').
          rewrite <- flat_map_concat_map.
          iNext.
          rewrite type_interp_eq; iEval (cbn).
          iExists (SMEMTYPE (areps_size ιs) ξ).
          iSplitR; first (iPureIntro; exact Htypeskind_ser).

          iSplitR; first (iPureIntro; split; [rewrite flat_map_concat_map; lia | ]).
          {
            rewrite flat_map_concat_map.
            apply forall_ptr_atom_to_word_ref_flag_interp.
            done.
          }
          iExists os.
          iSplitR; first (iPureIntro; rewrite flat_map_concat_map; done).
          rewrite type_interp_eq.
          iFrame.
          eauto.
        + (* Imm *)
          admit.
      *
        rewrite atoms_interp_cons.
        iSplitL; last (cbn; done).
        cbn.
        iExists (tag_address MemMM a), ta32.
        iSplitR; first (iPureIntro; exact Htarepr').
        iSplitR; first done.
        iExists (RootHeap MemMM a).
        iSplitR; first (iPureIntro; exact Hrootrepr').
        cbn.
        iExact "Haddr'".
    }


    [MemGC]: {
      admit.
    }

  Admitted.

End new.
