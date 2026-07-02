From mathcomp Require Import ssrbool eqtype.
Require Import RichWasm.compiler.memory.
Require Import RichWasm.util.
Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.case_ptr.
Require Import RichWasm.iris.logrel.roots.
Require Import RichWasm.iris.logrel.load_common.
Require Import RichWasm.iris.logrel.path.
Require Import RichWasm.iris.logrel.rt_token.
Require Import RichWasm.iris.logrel.virt_to_phys_strong.
Require Import RichWasm.iris.numerics.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section store_common.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma split_word_has_flag_arep off ιs ι ws os:
    off + sum_list_with arep_size ιs ≤ length ws ->
    Forall2 has_arep ιs os ->
    Forall2 word_has_flag (concat (map arep_flags ιs) ++ concat (map arep_flags [ι]))
      (take (sum_list_with arep_size ιs + sum_list_with arep_size [ι]) (drop off ws)) ->
    Forall2 word_has_flag (concat (map arep_flags ιs))
      (take (sum_list_with arep_size ιs) (drop off ws)) /\
      Forall2 word_has_flag (arep_flags ι)
        (take (arep_size ι) (drop (off + sum_list_with arep_size ιs)
                               (update_path_words off ws (concat (map serialize_atom os))))).
  Proof.
    intros Hlen Hos Hsliceflags.

    pose proof Hsliceflags as Hsliceflags'.

    set (l := sum_list_with arep_size ιs) in *.
    apply (Forall2_take _ _ _ l) in Hsliceflags.
    rewrite take_take in Hsliceflags.
    assert (l `min` (l + sum_list_with arep_size [ι]) = l) by lia.
    rewrite H in Hsliceflags.
    assert (l = length (concat (map arep_flags ιs))). {
      symmetry. apply length_arep_flags_size.
    }
    pose proof (take_app_length' _ (concat (map arep_flags [ι])) _ H0).
    rewrite H1 in Hsliceflags.

    split; first done.

    assert (l = length (concat (map serialize_atom os))). {
      unfold l.
      rewrite <- length_arep_flags_size.
      symmetry.
      apply has_arep_means_equal_lengths; done.
    }
    (* we need off + sum_list_with arep_size ιs ≤ length ws *)
    (* anyway time for Hsliceflags' to be dropped *)
    cbn in Hsliceflags'.
    clear_nils. rewrite Nat.add_0_r in Hsliceflags'.

    apply (Forall2_drop _ _ _ l) in Hsliceflags'.
    rewrite H0 in Hsliceflags'.
    rewrite drop_app_length in Hsliceflags'.
    rewrite <- H0 in Hsliceflags'.

    rewrite <- take_drop_commute in Hsliceflags'.
    rewrite drop_drop in Hsliceflags'.

    (* finally update_path_words shenanigans *)
    rewrite H2 in Hlen.
    apply updating_words in Hlen.
    destruct Hlen as (ws1 & wsold & ws2 & -> & -> & Hlenmatch & Hlenws1).
    rewrite <- Hlenws1; rewrite <- Hlenws1 in Hsliceflags'.
    rewrite drop_app_add; rewrite drop_app_add in Hsliceflags'.
    rewrite <- (Nat.add_0_r l); rewrite <- (Nat.add_0_r l) in Hsliceflags'.
    rewrite H2. rewrite H2 in Hsliceflags'; rewrite <- Hlenmatch in Hsliceflags'.
    rewrite drop_app_add.
    rewrite drop_app_add in Hsliceflags'.

    done.




  Qed.



  Lemma wp_store_w_strict μ t off wt wl wt' wl' es ret :
    run_codegen (store_w mr μ t off) wt wl = inr (ret, wt', wl', es) ->
    ret = () /\
    wt' = [] /\
    wl' = [] /\
    forall ℓ ℓ32 memidx memidxN (f: frame) B R Φ v (bs: bytes),
        N_i32_repr ℓ ℓ32 ->
        N_nat_repr memidx memidxN ->
        inst_memory (f_inst f) !! base_mem_idx mr μ = Some memidx ->
        types_agree t v ->
        length bs = length_t t ->
        ⊢ ∀ s E,
          ↪[frame] f -∗
          ↪[RUN] -∗
          memidxN ↦[wms][ℓ + byte_offset μ off] bs -∗
          ▷ (memidxN ↦[wms][ℓ + byte_offset μ off] bits v -∗ Φ f []) -∗
          CWP [W.BI_const (VAL_int32 ℓ32); W.BI_const v] ++ es @ s; E UNDER B; R {{ Φ }}.
  Proof.
    intros Hcg.
    unfold store_w in Hcg.
    inv_cg_emit Hcg; subst es wt' wl' ret.
    split; [auto|].
    split; [auto|].
    split; [auto|].
    intros * Hℓ Hmemidx Hmem Hty Hlen.
    iIntros (s E) "Hf Hrun Hbytes HΦ".
    iApply (cwp_store with "[$] [$] [$] [$]"); eauto.
  Qed.

  Lemma wp_store_w μ t off wt wl wt' wl' es ret :
    run_codegen (store_w mr μ t off) wt wl = inr (ret, wt', wl', es) ->
    ret = () /\
    wt' = [] /\
    wl' = [] /\
    forall ℓ ℓ32 memidx memidxN (f: frame) B R Φ v (bs: bytes),
        N_i32_repr (tag_address μ ℓ) ℓ32 ->
        N_nat_repr memidx memidxN ->
        inst_memory (f_inst f) !! base_mem_idx mr μ = Some memidx ->
        (ℓ `mod` 4 = 0)%N ->
        (ℓ <> 0)%N ->
        types_agree t v ->
        length bs = length_t t ->
        ⊢ ∀ s E,
          ↪[frame] f -∗
          ↪[RUN] -∗
          memidxN ↦[wms][ℓ + 4 * N.of_nat off] bs -∗
          ▷ (memidxN ↦[wms][ℓ + 4 * N.of_nat off] bits v -∗ Φ f []) -∗
          CWP [W.BI_const (VAL_int32 ℓ32); W.BI_const v] ++ es @ s; E UNDER B; R {{ Φ }}.
  Proof.
    intros Hcg.
    apply wp_store_w_strict in Hcg.
    intuition.
    iIntros (s E) "Hf Hrun Hbytes HΦ".
    assert (4 <= ℓ)%N by (by eapply mod_bound_nonzero).
    assert ((ℓ + 4 * N.of_nat off = tag_address μ ℓ + byte_offset μ off)%N) as Heq.
    { destruct μ; cbn; unfold offset_mm, offset_gc; lia. }
    rewrite Heq.
    iApply (H3 with "[$] [$] [Hbytes] [HΦ]"); eauto.
  Qed.




(* -------------------- STORE WEAK MM ----------------------- *)



  Lemma wp_store1_mm_weak a_idx off ι v_idx wt wl ret wt' wl' es :
    run_codegen (store1 mr MemMM a_idx off v_idx ι) wt wl = inr (ret, wt', wl', es) ->
    ret = () /\ wt' = [] /\ wl' = [] /\
    ∀ f ℓ a a32 val_v lmask θ o ws E B R Φ,
    ⊢ "Hf"       ∷ ↪[frame] f -∗
      "Hrun"     ∷ ↪[RUN] -∗
      "Hptr"     ∷ ℓ ↦heap ws -∗
      "Haddr"    ∷ ℓ ↦addr (MemMM, a) -∗
      "%Hℓmask"  ∷ ⌜lmask ℓ⌝ -∗
      "Htok"     ∷ rt_token rti sr lmask θ -∗
      "%Ha32"    ∷ ⌜f_locs f !! localimm a_idx = Some (VAL_int32 a32)⌝ -∗
      "%Hv"      ∷ ⌜f_locs f !! localimm v_idx = Some val_v⌝ -∗
      "%Hrepa"   ∷ ⌜N_i32_repr (tag_address MemMM a) a32⌝ -∗
      "%Hmod"    ∷ ⌜(a `mod` 4 = 0)%N⌝ -∗
      "%Hnz"     ∷ ⌜(a ≠ 0)%N⌝ -∗
      "%Hbound"  ∷ ⌜off + arep_size ι ≤ length ws⌝ -∗
      "%Harep"   ∷ ⌜has_arep ι o⌝ -∗
      "%Hsliceflags" ∷ ⌜Forall2 word_has_flag (arep_flags ι) (take (arep_size ι) (drop off ws))⌝ -∗
      "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemMM)⌝ -∗
      "%Hmemmm"  ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
      "Hat"      ∷ atom_interp_weak θ MemMM o val_v -∗
      "HΦ"       ∷ (ℓ ↦heap (update_path_words off ws (serialize_atom o)) -∗
                    ℓ ↦addr (MemMM, a) -∗
                    rt_token rti sr lmask θ -∗
                    Φ f []) -∗
    CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
    intros Hcg.
    unfold store1 in Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_a ?rest Ha Hcg.
    inv_cg_emit Ha; subst.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_v es_store_w Hv Hcg.
    inv_cg_emit Hv; subst.
    apply wp_store_w in Hcg.
    destruct Hcg as (-> & -> & -> & Hstore_spec).
    clear_nils.
    do 3 split; try done.
    intros *.
    repeat iIntros "@".
    (* get_local for address *)
    iApply (cwp_seq with "[Hf Hrun]").
    {
      iApply (cwp_local_get with "[] [$] [$]"); eauto.
      now instantiate (1:= λ f' v', ⌜f' = f ∧ v' = [VAL_int32 a32]⌝%I).
    }
    iIntros (f' vs') "[-> ->] Hf Hrun".
    rewrite app_assoc.
    (* get_local for value *)
    iApply (cwp_seq with "[Hf Hrun]").
    {
      iApply cwp_val_app; first apply has_values_to_consts.
      iApply (cwp_local_get with "[] [$] [$]"); eauto.
      now instantiate (1:= λ f' v', ⌜f' = f ∧ v' = [VAL_int32 a32; val_v]⌝%I).
    }
    iIntros (f' vs') "[-> ->] Hf Hrun".
    (* Open abstract-physical connection for the slice [off, off + arep_size ι) *)
    iPoseProof (virt_to_phys_slice_store_acc_weak _ _ lmask off (arep_size ι) with "[//] [$Htok] [$Hptr] [$Haddr]")
      as "(%hm & %Hhm & %Hdomθhm & %Hlocsθ_ws & Hnp & (%ns & %ns32 & %Hns & Hphys & Hwords) & Hclose)".
    (* atom_to_words_mm consumes Hat; it also returns types_agree which is needed for Hstore_spec *)
    iPoseProof (atom_to_words_mm θ ι o val_v Harep with "[$Hat]") as "(%ns_new & %ns32_new & %Hns_new & %Hbits & %Htypes & Hwords_new)".
    (* Extract pure facts from Hnp, derive dom θ cond for new words, then reconstruct Hnp *)
    iDestruct "Hnp" as "(Haddr & %rm & %lm & Hroot & Hlayout & Hrti & %Hinj & %Hrootok & Hrootmem & %Hheapok)".
    iPoseProof (words_interp_locs_dom_θ θ rm MemMM _ ns_new Hrootok with "[$] [$] [$]")
      as "%Hlocsθ_new".
    iAssert (rt_token_nophys rti sr lmask θ hm) with "[Haddr Hroot Hlayout Hrti Hrootmem]" as "Hnp".
    { iFrame. iPureIntro. split; last split; done. }
    (* Compute byte-length of old slice *)
    iPoseProof (big_sepL2_length with "Hwords") as "%Hlenws".
    assert (Hlenbytes : length (flat_map serialise_i32 ns32) = length_t (translate_arep ι)).
    {
      rewrite len_ser32.
      rewrite -(Forall2_length _ _ _ Hns).
      rewrite -Hlenws length_take length_drop length_t_translate_arep.
      lia.
    }
    iApply cwp_fupd.
    iApply (Hstore_spec a a32 (sr_mem_mm sr) (rt_memaddr sr MemMM) with "[$Hf] [$Hrun] [$Hphys]"); eauto.
    iNext; iIntros "Hnew_phys".
    iEval (rewrite <- Hbits) in "Hnew_phys".
    iMod ("Hclose" $! (serialize_atom o) ns_new ns32_new
      with "[%] [%] [%] [%] [%] [$Hnew_phys] [$Hwords_new] [$Hnp]") as "(Hptr_new & Haddr & Htok)".
    - exact (has_arep_size ι o Harep).
    - exact Hns_new.
    - intros flags H.
      exact (update_path_words_flags_compat ι o ws off Harep Hbound Hsliceflags flags H).
    - eapply Forall_impl.
      + exact (update_path_words_locs_incl (dom θ) ws off (serialize_atom o) Hlocsθ_ws Hlocsθ_new).
      + intros ℓ' Hℓ'. rewrite <- Hdomθhm. exact Hℓ'.
    -  exact (update_path_words_locs_incl (dom θ) ws off (serialize_atom o)
               Hlocsθ_ws Hlocsθ_new).
    - iModIntro. iApply ("HΦ" with "[$] [$]"); iFrame.
  Qed.

  Lemma wp_store_weak_mm_inner a_idx ιs :
    ∀ off vs_idx wt wl ret wt' wl' es,
    length vs_idx = length ιs -> (* needs to be true for ret = .. to hold *)
    run_codegen (foldlM
         (λ (off : nat) '(v, ι),
            store1 mr MemMM a_idx off v ι ≫= λ _ : (), Monad.ret (off + arep_size ι))
         off (zip vs_idx ιs)) wt wl = inr (ret, wt', wl', es) ->
    ret = seq.foldl (λ off' ι, off' + arep_size ι) off ιs /\
    wt' = [] /\ wl' = [] /\ (* if I'm understanding wt' and wl' right *)
    ∀ f ℓ a a32 val_vs lmask θ os ws E B R Φ,
    ⊢ "Hf"       ∷ ↪[frame] f -∗
      "Hrun"     ∷ ↪[RUN] -∗
      "Hptr"     ∷ ℓ ↦heap ws -∗
      "Haddr"    ∷ ℓ ↦addr (MemMM, a) -∗
      "%Hℓmask"  ∷ ⌜lmask ℓ⌝ -∗
      "Htok"     ∷ rt_token rti sr lmask θ -∗
      "%Ha32"    ∷ ⌜f_locs f !! localimm a_idx = Some (VAL_int32 a32)⌝ -∗
      "%Hv"      ∷ ⌜Forall2 (λ v_idx val_v, f_locs f !! localimm v_idx = Some val_v) vs_idx val_vs⌝ -∗
      "%Hrepa"   ∷ ⌜N_i32_repr (tag_address MemMM a) a32⌝ -∗
      "%Hmod"    ∷ ⌜(a `mod` 4 = 0)%N⌝ -∗
      "%Hnz"     ∷ ⌜(a ≠ 0)%N⌝ -∗
      "%Hbound"  ∷ ⌜off + sum_list_with arep_size ιs ≤ length ws⌝ -∗
      "%Harep"   ∷ ⌜Forall2 has_arep ιs os⌝ -∗
      "%Hsliceflags" ∷ ⌜Forall2 word_has_flag (concat (map arep_flags ιs))
                                              (take (sum_list_with arep_size ιs) (drop off ws))⌝ -∗
      "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemMM)⌝ -∗
      "%Hmemmm"  ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
      "Hat"      ∷ ([∗ list] o;val_v ∈ os;val_vs, atom_interp_weak θ MemMM o val_v) -∗
      "HΦ"       ∷ (ℓ ↦heap (update_path_words off ws (concat (map serialize_atom os))) -∗
                    ℓ ↦addr (MemMM, a) -∗
                    rt_token rti sr lmask θ -∗
                    Φ f []) -∗
    CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
    induction ιs as [| ιs ι] using seq.last_ind; intros * Hlen Hcg *.
    - assert (zip vs_idx ([]:list atomic_rep) = []) by (by apply zip_nil_r).
      rewrite H in Hcg.
      cbn in Hcg.
      inversion Hcg; subst.
      do 3 split; try done.
      intros *; repeat iIntros "@".
      iApply (cwp_nil with "[$] [$]").
      (* os is nil, val_vs is nil, and ws didn't update *)
      inversion Harep; subst.
      iPoseProof (big_sepL2_nil_inv_l with "[$Hat]") as "%Hvalvslen". subst.
      assert (update_path_words ret ws (concat (map serialize_atom [])) = ws). {
        cbn.
        apply update_path_words_empty_2.
      }
      rewrite H0.
      iApply ("HΦ" with "[$] [$] [$]").
    - (* to start with, we need to make
         (zip vs_idx (seq.rcons ιs ι)) = seq.rcons (zip vs_idx_small ιs) (v_idx, ι) *)
      (* we know that length ιs = length os = length val_vs = length vs_idx
                            Harep         Hat           Hv
         so then we know vs_idx must be equal to some seq.rcons vs_idx v_idx. then zip seq.rcons?
         I think that should work, but that's not interesting right at this moment so asserting
       *)
      rename vs_idx into vs_idx_big.
      assert (∃ vs_idx v_idx, vs_idx_big = seq.rcons vs_idx v_idx /\ length vs_idx = length ιs). {
        rewrite rcons_app in Hlen.
        rewrite length_app in Hlen.
        cbn in Hlen.
        apply length_split in Hlen as (vs_idx & v_idxT & -> & hlen1 & hlen2).
        destruct v_idxT as [|v_idx rest]; [inversion hlen2|].
        destruct rest; [|inversion hlen2].
        exists vs_idx, v_idx.
        rewrite rcons_app.
        done.
      }
      destruct H as (vs_idx & v_idx & -> & Hleminis).

      assert (zip (seq.rcons vs_idx v_idx) (seq.rcons ιs ι) =
                seq.rcons (zip vs_idx ιs) (v_idx, ι)). {
        by apply zip_rcons.
      }
      rewrite H in Hcg.

      apply inv_foldlM_rcons in Hcg.
      rewrite seq.foldl_rcons.
      destruct Hcg as (off_ιs & wt_ι & wt_ιs & wl_ι & wl_ιs & es_ι & es_ιs & Hinit & Hlast).
      destruct Hlast as (Hlast & -> & -> & ->).
      inv_cg_bind Hlast a0' wt_bs wt_b wl_bs wl_b es_bs es_b Hbs Hfb.
      subst.
      inv_cg_ret Hfb; subst.
      eapply IHιs in Hinit; auto.
      clear IHιs.

      destruct Hinit as (-> & -> & -> & Hinit).
      pose proof Hbs as Hbs'.
      clear_nils.

      apply (wp_store1_mm_weak) in Hbs'.
      destruct Hbs' as (-> & -> & -> & Hbs_spec).

      do 3 (split; first by auto).

      (* finally the iris proof... *)
      (* note that the overall structure is to do cwp_seq and use Hinit then Hbs_spec *)
      intros *; repeat iIntros "@".

      (* the thing we need to do before cwp_seq is split up Hat into the Hinit part and the
         Hbs part. This involves showing os = seq.rcons os o and val_vs = seq.rcons os o *)
      pose proof Harep as Hosslicing.
      eapply Forall2_rcons_inv_l in Hosslicing; try done.
      rename os into os_big.
      destruct Hosslicing as (o & os & Ho & Hos & Hos_eq).
      subst os_big.
      rename val_vs into val_vs_big.
      iPoseProof (big_sepL2_rcons_inv_l with "[$Hat]") as
        "(%val_v & %val_vs & -> & Hoa & Hat)"; try done.
      (* rewrite <- rcons_app in Hv. *)
      pose proof Hv as Hvslicing.
      rewrite !rcons_app in Hv.
      eapply Forall2_rcons_inv_l in Hvslicing; try done.
      destruct Hvslicing as (valvstemp & valvtemp & Hlocsvalv & Hlocsvalvs & Hinv).
      apply seq.rcons_inj in Hinv; inversion Hinv; subst; clear Hinv.

      (* the new one is hslice flags *)
      rewrite !rcons_app in Hsliceflags.
      rewrite map_app in Hsliceflags.
      rewrite sum_list_with_app in Hsliceflags.
      rewrite concat_app in Hsliceflags.

      (* I need this both for split_word_has_flag_arep and the Hinit! *)
      assert (Hlensmall: off + sum_list_with arep_size ιs ≤ length ws). {
          rewrite rcons_app in Hbound.
          rewrite sum_list_with_app in Hbound.
          lia.
      }
      apply (split_word_has_flag_arep _ _ _ _ os Hlensmall Hos) in Hsliceflags as htemp.
      destruct htemp as [Hflagsιs Hflagsι].
      (* put some more in here but for now this is enough lol *)

      (* Now we can cwp_seq. Note lots of pure Forall/rcons manipulations happen inside
         that might be better brought outside (we'll see).
       *)
      iApply (cwp_seq with "[Hf Hrun Hptr Haddr Htok HΦ Hat]"). {
        iApply (Hinit with "[$] [$] [$] [$] [//] [$] [//] [//]
                            [//] [//] [//] [//] [//] [//] [//] [//] [$] [-]").
        iIntros "Hℓ Harrt Hrt".
        let Q := open_constr:(_ : iProp Σ) in
        instantiate (1 := (λ f'' vs'', ⌜f'' = f /\ vs'' = []⌝ ∗ Q)%I).
        cbn.
        iSplitR; first done.
        iAccu.
      }
      cbn.
      iIntros (f0 vs) "Hres Hf Hrun".
      iDestruct "Hres" as "((-> & ->) & HΦ & Hℓ_heap & Hℓ_addr & Hrt)".
      clear_nils.

      (* and now apply the hbs! *)
      iApply (Hbs_spec with "[$] [$] [$] [$] [//] [$] [//] [//]
                            [//] [//] [//] [] [//] [] [//] [//] [$] [-]").
      + iPureIntro.
        (* this will end up true due to Hbound and Hos *)
        rewrite rcons_app in Hbound.
        rewrite sum_list_with_app in Hbound.
        cbn in Hbound.
        rewrite seq_foldl_sum_list_with.
        rewrite update_path_words_size.
        2: {
          rewrite (has_arep_means_equal_lengths _ _ Hos).
          rewrite length_arep_flags_size.
          lia.
        }
        lia.

      + iPureIntro.
        rewrite seq_foldl_sum_list_with.
        done.
      + iIntros "Hℓ_heap Hℓ_addr Hrt".
        (* one last update_path_words manipulation *)
        assert (update_path_words off ws (concat (map serialize_atom (seq.rcons os o))) =
                  update_path_words
                        (seq.foldl (λ (off' : nat) (ι0 : atomic_rep), off' + arep_size ι0)
                           off ιs)
                        (update_path_words off ws (concat (map serialize_atom os)))
                        (serialize_atom o)
               ). {
          rewrite seq_foldl_sum_list_with.
          change map with @seq.map.
          rewrite seq.map_rcons.
          rewrite rcons_app.
          rewrite concat_app.
          cbn. clear_nils.
          change @seq.map with map.
          assert (length (concat (map serialize_atom os)) = sum_list_with arep_size ιs). {
            rewrite (has_arep_means_equal_lengths _ _ Hos).
            rewrite length_arep_flags_size.
            done.
          }
          rewrite <- H0.
          apply update_path_words_in_stages.
        }
        rewrite <- H0.
        iApply ("HΦ" with "[$] [$] [$]").

  Qed.

  Lemma wp_store_weak_mm a_idx off ιs vs_idx wt wl ret wt' wl' es :
    length vs_idx = length ιs -> (* needs to be true for ret = .. to hold *)
    run_codegen (memory.store mr MemMM a_idx off vs_idx ιs) wt wl = inr (ret, wt', wl', es) ->
    ret = () /\ wt' = [] /\ wl' = [] /\ (* if I'm understanding wt' and wl' right *)
    ∀ f ℓ a a32 val_vs lmask θ os ws E B R Φ,
    ⊢ "Hf"       ∷ ↪[frame] f -∗
      "Hrun"     ∷ ↪[RUN] -∗
      "Hptr"     ∷ ℓ ↦heap ws -∗
      "Haddr"    ∷ ℓ ↦addr (MemMM, a) -∗
      "%Hℓmask"  ∷ ⌜lmask ℓ⌝ -∗
      "Htok"     ∷ rt_token rti sr lmask θ -∗
      "%Ha32"    ∷ ⌜f_locs f !! localimm a_idx = Some (VAL_int32 a32)⌝ -∗
      "%Hv"      ∷ ⌜Forall2 (λ v_idx val_v, f_locs f !! localimm v_idx = Some val_v) vs_idx val_vs⌝ -∗
      "%Hrepa"   ∷ ⌜N_i32_repr (tag_address MemMM a) a32⌝ -∗
      "%Hmod"    ∷ ⌜(a `mod` 4 = 0)%N⌝ -∗
      "%Hnz"     ∷ ⌜(a ≠ 0)%N⌝ -∗
      "%Hbound"  ∷ ⌜off + sum_list_with arep_size ιs ≤ length ws⌝ -∗
      "%Harep"   ∷ ⌜Forall2 has_arep ιs os⌝ -∗
      "%Hsliceflags" ∷ ⌜Forall2 word_has_flag (concat (map arep_flags ιs))
                                              (take (sum_list_with arep_size ιs) (drop off ws))⌝ -∗
      "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemMM)⌝ -∗
      "%Hmemmm"  ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
      "Hat"      ∷ ([∗ list] o;val_v ∈ os;val_vs, atom_interp_weak θ MemMM o val_v) -∗
      "HΦ"       ∷ (ℓ ↦heap (update_path_words off ws (concat (map serialize_atom os))) -∗
                    ℓ ↦addr (MemMM, a) -∗
                    rt_token rti sr lmask θ -∗
                    Φ f []) -∗
    CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
    intros Hlen Hcg.
    unfold memory.store in Hcg.
    apply wp_ignore in Hcg.
    destruct Hcg as (-> & off' & Hcg).
    pose proof (wp_store_weak_mm_inner _ _ _ _ _ _ _ _ _ _ Hlen Hcg) as (-> & U & V & W).
    intuition.
  Qed.


(* -------------------- STORE WEAK GC ----------------------- *)


  Lemma virt_to_phys_slice_store_acc_weak_gc lmask off sz ℓ μ a θ ws :
    let slice := take sz (drop off ws) in
    ⊢ ⌜off + sz <= length ws⌝ -∗
      rt_token rti sr lmask θ -∗
      ℓ ↦heap ws -∗
      (* ℓ ↦addr (μ, a) -∗ *)
      ⌜ θ !! ℓ = Some (μ, a)⌝ -∗
      ∃ hm,
        ⌜hm !! ℓ = Some ws⌝ ∗
        ⌜dom θ = dom hm⌝ ∗
        ⌜Forall (λ ℓ', ℓ' ∈ dom θ) (flat_map locations ws)⌝ ∗
        rt_token_nophys rti sr lmask θ hm ∗
        (∃ (ns : list N) (ns32 : list i32),
          ⌜Forall2 N_i32_repr ns ns32⌝ ∗
          rt_memaddr sr μ ↦[wms][a + 4 * N.of_nat off] flat_map serialise_i32 ns32 ∗
          words_interp θ μ slice ns) ∗
        (∀ (ws_new : list word) (ns' : list N) (ns32' : list i32),
          ⌜length ws_new = sz⌝ -∗
          ⌜Forall2 N_i32_repr ns' ns32'⌝ -∗
          ⌜∀ flags, Forall2 word_has_flag flags ws →
                    Forall2 word_has_flag flags (update_path_words off ws ws_new)⌝ -∗
          ⌜Forall (λ ℓ', ℓ' ∈ dom hm) (flat_map locations (update_path_words off ws ws_new))⌝ -∗
          ⌜Forall (λ ℓ', ℓ' ∈ dom θ) (flat_map locations (update_path_words off ws ws_new))⌝ -∗
          rt_memaddr sr μ ↦[wms][a + 4 * N.of_nat off] flat_map serialise_i32 ns32' -∗
          words_interp θ μ ws_new ns' -∗
          rt_token_nophys rti sr lmask θ hm -∗
          |==> ℓ ↦heap (update_path_words off ws ws_new) ∗
               (* ℓ ↦addr (μ, a) ∗ *)
               rt_token rti sr lmask θ).
  Proof.
    iIntros (slice) "%Hlenbdd Hrt Hpt %Hθℓ".
    open_rt "Hrt".
    iExists hm.
    iCombine "Hpt Hheap" gives "%Hhm".
    (* iCombine "Ha Haddr" gives "%Hθℓ". *)
    iPoseProof (heap_memory_dom_eq with "Hheapmem") as "%Hdomθhm".
    iPoseProof (heap_memory_delete sr ℓ _ _ ws with "Hheapmem") as "(HR & Hheapcont)"; eauto.
    (* Derive Forall (ℓ' ∈ dom θ) (flat_map locations ws) from heap_ok condition 3 *)
    have Hlocsθ_ws : Forall (λ ℓ', ℓ' ∈ dom θ) (flat_map locations ws).
    { destruct Hheapok as (_ & Hdomθ).
      unfold map_Forall2 in Hdomθ.
      specialize (Hdomθ ℓ).
      rewrite Hhm Hθℓ in Hdomθ.
      inversion Hdomθ. exact H1. }
    iSplit; first (iPureIntro; exact Hhm).
    iSplit; first (iPureIntro; exact Hdomθhm).
    iSplit; first (iPureIntro; exact Hlocsθ_ws).
    iFrame "Haddr".
    iSplitL "Hroot Hlayout Hrti Hrootmem"; first by iFrame.
    iDestruct "HR" as "(%ns_all & %ns32_all & %Hns_all & Hphys_all & Hwords_all)".
    assert (ws = take off ws ++ slice ++ drop (off + sz) ws) as Hws.
    {
      rewrite app_assoc. unfold slice. by rewrite take_take_drop take_drop.
    }
    assert (length slice = sz) as Hslicelen.
    { unfold slice; apply length_take_le; rewrite length_drop; lia. }
    iEval (setoid_rewrite Hws) in "Hwords_all".
    iPoseProof (big_sepL2_app_inv_l with "Hwords_all") as "(%ns_pre & %ns_rest & -> & Hpre & Hwords_rest)".
    iPoseProof (big_sepL2_app_inv_l with "Hwords_rest") as "(%ns_mid & %ns_post & -> & Hwords & Hpost)".
    pose proof Hns_all as Hns_all'.
    apply Forall2_app_inv_l in Hns_all'.
    destruct Hns_all' as (ns32_pre & ns32_rest & Hns_pre & Hns_rest & ->).
    apply Forall2_app_inv_l in Hns_rest.
    destruct Hns_rest as (ns32_mid & ns32_post & Hns_mid & Hns_post & ->).
    rewrite !flat_map_app.
    rewrite !wms_app; try by eauto.
    iDestruct "Hphys_all" as "(Hphys_pre & Hphys & Hphys_post)".
    pose proof (Forall2_length _ _ _ Hns_pre) as Hnslenpre.
    pose proof (Forall2_length _ _ _ Hns_mid) as Hnslen.
    iPoseProof (big_sepL2_length with "Hpre") as "%Hlenpre'".
    iPoseProof (big_sepL2_length with "Hpost") as "%Hlenpost'".
    iPoseProof (big_sepL2_length with "Hwords") as "%Hlenws'".
    assert (length (flat_map serialise_i32 ns32_pre) = 4 * off) as Hlenpre.
    {
      rewrite len_ser32. rewrite -Hnslenpre -Hlenpre' length_take_le; lia.
    }
    rewrite Hlenpre Nat2N.inj_mul.
    iSplitL "Hwords Hphys"; first by iFrame.
    (* Closing frame *)
    iIntros (ws_new ns' ns32') "%Hlenws_new %Hns'' %Hflags_compat %Hlocshm %Hlocsθ Hphys' Hwords' Hnp".
    iMod (ghost_map_update (update_path_words off ws ws_new) with "Hheap Hpt") as "[Hheap' Hpt']".
    iModIntro.
    iFrame "Hpt'".
    pose proof (Forall2_length _ _ _ Hns'') as Hns32'len.
    iPoseProof (big_sepL2_length with "Hwords'") as "%Hns'len".
    set (hm' := <[ℓ := update_path_words off ws ws_new]> hm).
    iAssert (rt_token_nophys rti sr lmask θ hm') with "[Hnp]" as "Hnp'".
    { iApply (rt_token_nophys_insert_heap_weak _ _ _ _ _ _ ws with "Hnp").
      - exact Hhm.
      - intro Hcontra; done.
      - eauto.
      - eauto. }
    iApply (rt_token_putheap rti sr lmask θ hm' with "Hnp'").
    unfold rt_token_phys.
    iFrame "Hheap'".
    iApply ("Hheapcont" $! (update_path_words off ws ws_new)).
    iExists (ns_pre ++ ns' ++ ns_post), (ns32_pre ++ ns32' ++ ns32_post).
    iSplit; first by (iPureIntro; eauto using Forall2_app).
    iSplitL "Hphys_pre Hphys' Hphys_post".
    - iCombine "Hphys_pre Hphys' Hphys_post" as "Hphys_all".
      rewrite -wms_app; last by (rewrite !len_ser32; lia).
      rewrite -wms_app; last (rewrite !len_ser32 -Hnslenpre -Hlenpre' length_take_le; lia).
      rewrite -!flat_map_app.
      iFrame "Hphys_all".
    - unfold update_path_words; rewrite Hlenws_new.
      unfold words_interp.
      iCombine "Hpre Hwords' Hpost" as "Hwords_all".
      repeat (rewrite <- big_sepL2_app_same_length; last by (rewrite -?Hlenpre' -?Hns'len; lia)).
      rewrite drop_drop.
      iFrame.
  Qed.


  Lemma wp_store1_gc_state a_idx off ι v_idx wt wl ret wt' wl' es :
    run_codegen (store1 mr MemGC a_idx off v_idx ι) wt wl = inr (ret, wt', wl', es) ->
    ret = () /\ wt' = [] /\ wl' = [].
  Proof.
    intros Hcg.
    unfold store1 in Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_a ?rest Ha Hcg.
    inv_cg_emit Ha; subst.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_v es_store_w Hv Hcg.
    inv_cg_emit Hv; subst.
    clear_nils.
    destruct ret; clear Hretval Hretval0.
    split; first done.

    destruct (atomic_rep_eq_dec ι PtrR).
    - (* ι = PtrR *)
      subst ι.
      apply wp_ite_gc_ptr_ptr_cg_state in Hcg.
      destruct Hcg as (?wt & ?wt & ?wt & ?wl & ?wl & ?wl & ?es & ?es & ?es & rest).
      destruct rest as (Hcg1 & Hcg2 & Hcg3 & -> & ->).

      apply wp_store_w in Hcg1 as (_ & -> & -> & _).
      apply wp_store_w in Hcg2 as (_ & -> & -> & _).
      clear_nils.


      inv_cg_bind Hcg3 [] ?wt ?wt ?wl ?wl es_loadroot ?rest Hloadroot Hcg3.
      clear es_store_w.
      inv_cg_bind Hcg3 [] ?wt ?wt ?wl ?wl es_store_w ?rest Hstore Hcg3.
      inv_cg_bind Hcg3 [] ?wt ?wt ?wl ?wl es_loc es_unregister Hloc Hunregister.
      inv_cg_emit Hloc; subst.
      clear_nils; clear Hretval.

      apply (wp_loadroot sr) in Hloadroot as (_ & -> & -> & _).
      apply wp_store_w in Hstore as (_ & -> & -> & _).
      apply (wp_unregisterroot rti sr) in Hunregister as (_ & -> & -> & _).
      clear_nils.
      done.
    - (* ι <> PtrR *)
      eapply wp_ite_gc_ptr_nonptr in Hcg; last assumption.
      apply wp_store_w in Hcg as (_ & -> & -> & _).
      done.
  Qed.

  (* speculative store1 gc lemma *)
  Lemma wp_store1_gc_weak a_idx off ι v_idx wt wl ret wt' wl' es :
    run_codegen (store1 mr MemGC a_idx off v_idx ι) wt wl = inr (ret, wt', wl', es) ->
    ret = () /\ wt' = [] /\ wl' = [] /\
    ∀ f ℓ a a32 val_v lmask θ o ws E B R Φ,
    ⊢ "Hf"       ∷ ↪[frame] f -∗
      "Hrun"     ∷ ↪[RUN] -∗
      "Hptr"     ∷ ℓ ↦heap ws -∗
      "%Haddr"   ∷ ⌜ θ !! ℓ = Some (MemGC, a)⌝ -∗
      "%Hℓmask"  ∷ ⌜lmask ℓ⌝ -∗
      "Htok"     ∷ rt_token rti sr lmask θ -∗
      "Hunreg"   ∷ instance_rt_func_interp (mr_func_unregisterroot mr) (sr_func_unregisterroot sr) (runtime.spec_unregisterroot rti sr) (f_inst f) -∗
      "Hown"     ∷ na_own logrel_nais E -∗
      "%Hmask"   ∷ ⌜↑ns_fun (N.of_nat (sr_func_unregisterroot sr)) ⊆ E⌝ -∗
      "%Ha32"    ∷ ⌜f_locs f !! localimm a_idx = Some (VAL_int32 a32)⌝ -∗
      "%Hv"      ∷ ⌜f_locs f !! localimm v_idx = Some val_v⌝ -∗
      "%Hrepa"   ∷ ⌜N_i32_repr (tag_address MemGC a) a32⌝ -∗
      "%Hmod"    ∷ ⌜(a `mod` 4 = 0)%N⌝ -∗
      "%Hnz"     ∷ ⌜(a ≠ 0)%N⌝ -∗
      "%Hbound"  ∷ ⌜off + arep_size ι ≤ length ws⌝ -∗
      "%Harep"   ∷ ⌜has_arep ι o⌝ -∗
      "%Hsliceflags" ∷ ⌜Forall2 word_has_flag (arep_flags ι) (take (arep_size ι) (drop off ws))⌝ -∗
      "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemMM)⌝ -∗
      "%Hrepgc"  ∷ ⌜N_nat_repr (sr_mem_gc sr) (rt_memaddr sr MemGC)⌝ -∗
      "%Hmemmm"  ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
      "%Hmemgc"  ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemGC = Some (sr_mem_gc sr)⌝ -∗
      "Hat"      ∷ atom_interp o val_v -∗ (* most likely to change *)
      "HΦ"       ∷ (ℓ ↦heap (update_path_words off ws (serialize_atom o)) -∗
                    na_own logrel_nais E -∗
                    instance_rt_func_interp (mr_func_unregisterroot mr) (sr_func_unregisterroot sr) (runtime.spec_unregisterroot rti sr) (f_inst f) -∗
                    rt_token rti sr lmask θ -∗
                    Φ f []) -∗
    CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
    intros Hcg.
    apply wp_store1_gc_state in Hcg as Hcgstate.
    destruct Hcgstate as (-> & -> & ->).
    do 3 (split; first done).

    unfold store1 in Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_a ?rest Ha Hcg.
    inv_cg_emit Ha; subst.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_v es_store_w Hv Hcg.
    inv_cg_emit Hv; subst.
    clear_nils.
    clear Hretval Hretval0.
    subst.

    (* now we need to do two locals -> values cwp conversions before we can
       use the ite_gc_ptr spec *)
    (* so, the iris proofs starts now *)
    intros *; repeat iIntros "@".
    rewrite app_assoc.
    iApply (cwp_seq with "[Hf Hrun]"). {
      iApply (cwp_seq with "[Hf Hrun]"). {
        iApply (cwp_local_get with "[] [$] [$]"); eauto.
        by instantiate (1 := λ f' v', (⌜f' = f⌝ ∗ ⌜v' = [VAL_int32 a32]⌝)%I).
      }
      iIntros (f' vs) "[-> ->] Hf Hr".

      iApply cwp_val_app; [by apply has_values_to_consts|].
      iApply (cwp_local_get with "[] [$] [$]"); eauto.
      instantiate (1 := λ f' v', (⌜f' = f⌝ ∗ ⌜v' = [VAL_int32 a32; val_v]⌝)%I).
      iModIntro.
      unfold fvs_combine; cbn.
      done.
    }
    iIntros (f' vs) "[-> ->] Hf Hr".

    (* ite gc ptr requires knowing if ι = PtrR or not *)
    destruct (atomic_rep_eq_dec ι PtrR).

    - (* ι = PtrR case *)
      subst ι.
      (* deconstructing val_v to use wp_ite_gc_ptr_ptr *)
      pose proof Harep as Harepsave.
      cbn in Harep.
      destruct o; try inversion Harep; clear Harep.
      (* NOTE: o = PtrA p *)
      (* this case is STORING PtrA p *)

      (* we need this to apply wp_ite_gc_ptr_ptr, but we otherwise only dig
         into atom_interp in the cases themselves *)
      iPoseProof (atom_interp_ptr_shaped_pure with "Hat") as
        "(%n & %n32 & %Nrepr & -> & %Hptrshaped)".
      (* NOTE: I'm not including the repr_ptr because that needs to be taken
          out with the root_pointer_interp in the future *)


      (* finally digging into the ite-gc! *)
      eapply wp_ite_gc_ptr_ptr with (evs:=to_consts [VAL_int32 a32; VAL_int32 n32])
                                    (vs:=[VAL_int32 a32; VAL_int32 n32]) in Hcg;
        [|by apply Is_true_true, has_values_to_consts| done | exact Hptrshaped | exact Nrepr].
      destruct Hcg as (?wt & ?wt & ?wt & ?wl & ?wl & ?wl & es1 & es2 & es3 & Hcompile).
      destruct Hcompile as (Hcg1 & Hcg2 & Hcg3 & Hwt7 & Hwl7 & Hes_store_w).
      clear_nils.

      (* given that hcg3 has a bunch more stuff to do, I'm going to apply Hes_store_w*)
      (* now *)
      iApply (Hes_store_w with "[$] [$] [//]").
      clear Hes_store_w.
      iIntros "!> Hf Hrun".

      (* now we destruct p! Ryan inverted ptr_shaped so we'll do that too *)
      inversion Hptrshaped; subst; last destruct μ eqn:?.
      + (* Hcg1 - Ptr Int - done with atom_interp *)
        apply wp_store_w in Hcg1 as (_ & -> & -> & Hcg1spec).

        (* Note: this happens so late because the MM case needs full rttoken *)
        iPoseProof (virt_to_phys_slice_store_acc_weak_gc lmask off (arep_size PtrR)
                     with "[//] [$Htok] [$Hptr] [//]")
          as "(%hm & %Hhm & %Hdomθhm & %Hlocsθ_ws & Hnp &
          (%ns & %ns32 & %Hns & Hphys & Hwords) & Hclose)".

        (* we always heat hat inside *)
        iAssert (atom_interp_weak θ MemGC (PtrA (PtrInt n0)) (VAL_int32 n32))
          with "[]" as "Hat2". {
          cbn.
          iExists (2 * n0)%N, n32.
          iSplitR; [done| iSplitR; [done|]].
          iPureIntro.
          constructor.
        }
        (* I. didnd't have to eat Hat. What. It's still there.
          I guess bc it's all numbers it's fine. Rest of proof continues as normal *)

        iPoseProof (atom_to_words_gc θ PtrR _ _ Harepsave with "[$Hat2]") as
          "(%ns_new & %ns32_new & %Hns_new & %Hbits & %Htypes & Hwords_new)".

        (* Extract pure facts from Hnp, derive dom θ cond for new words, then reconstruct Hnp *)
        iDestruct "Hnp" as "(Haddr_auth & %rm & %lm & Hroot & Hlayout & Hrti & %Hinj & %Hrootok & Hrootmem & %Hheapok)".
        iPoseProof (words_interp_locs_dom_θ θ rm MemGC _ _ Hrootok with "[$Hwords_new] [$] [$]")
          as "%Hlocsθ_new".
        iAssert (rt_token_nophys rti sr lmask θ hm) with "[Hroot Hlayout Hrti Hrootmem Haddr_auth]" as "Hnp".
        { iFrame. iPureIntro. split; last split; done. }

        specialize (Hcg1spec a a32).
        specialize (Hcg1spec (sr_mem_gc sr) (rt_memaddr sr MemGC)).
        specialize Hcg1spec with (v:=(VAL_int32 n32)).
        specialize Hcg1spec with (bs:=(flat_map serialise_i32 ns32)).
        (* I need a pure fact about the length of ns and ns32 here *)
        iPoseProof (big_sepL2_length with "[$Hwords]") as "%Hlenns".
        pose proof (Forall2_length _ _ _ Hsliceflags) as Hlenareps.
        pose proof (Forall2_length _ _ _ Hns) as Hnslen.
        rewrite <- Hlenareps in Hlenns.
        rewrite <- Hlenns in Hnslen.
        cbn in Hnslen.

        iApply cwp_fupd. (* necessary for a later iMod *)
        iApply (Hcg1spec with "[$] [$] [$] [-]"); try done; try (cbn; done). {
          cbn.
          rewrite len_ser32.
          destruct ns32 as [|nn32 ns32]; try inversion Hnslen.
          destruct ns32; try inversion H0.
          cbn.
          done.
        }
        iIntros "!> Haddr".

        (* we need to use Hclose now! We have a bunch of tiny facts we need to do so *)
        cbn [bits].
        assert (serialise_i32 n32 = flat_map serialise_i32 [n32]) by done.
        rewrite H.
        iSpecialize ("Hclose" $! (serialize_atom (PtrA (PtrInt n0))) [(2 * n0)%N] [n32]).
        iSpecialize ("Hclose" with "[//] [%] [%] [%] [%] [$]").
        * constructor; done.
        * intros flags H2.
          eapply update_path_words_flags_compat; [exact Harepsave|done|done|done].
        * eapply Forall_impl.
          -- exact (update_path_words_locs_incl (dom θ) ws off _ Hlocsθ_ws Hlocsθ_new).
          -- intros ℓ' Hℓ'. rewrite <- Hdomθhm. exact Hℓ'.
        * eapply update_path_words_locs_incl; try done.
        * iAssert (⌜ns_new = [(2 * n0)%N]⌝%I) with "[Hwords_new]" as "->". {
            cbn.
            iPoseProof (big_sepL2_length with "[$Hwords_new]") as "%lenn".
            destruct ns_new as [|nn nrest]; inversion lenn.
            destruct nrest; inversion H1; clear H1.
            cbn.
            iDestruct "Hwords_new" as "(%Hrepr2 & _)".
            inversion Hrepr2; subst.
            done.
          }
          iSpecialize ("Hclose" with "[$Hwords_new] [$Hnp]").
          iMod "Hclose".
          iModIntro.
          iDestruct "Hclose" as "[pls hlp]".
          iApply ("HΦ" with "[$] [$] [$] [$]").
      + (* Hcg2 - Ptr MM *)
        apply wp_store_w in Hcg2 as (_ & -> & -> & Hcg2spec).
        (* start with unfolding atom_interp a bit *)
        iEval (cbn) in "Hat".
        iDestruct "Hat" as "(%n' & %n32' & %forinv & %toinv & Hrp)".
        inversion toinv; subst n32'; clear toinv.
        pose proof (N_i32_repr_inj _ _ _ forinv Nrepr) as ->; clear forinv.
        iDestruct "Hrp" as "(%rp & %Hreprroot & Haddr_ℓ0)".

        inversion Hreprroot. {
          exfalso.
          apply N.Div0.mod_divides in H as [c ->].
          lia.
        }
        iEval (cbn) in "Haddr_ℓ0".
        destruct μ0; try done.
        subst rp.
        assert (a1 = a0). {
          cbn in H1.
          assert (4 <= a1)%N by (by eapply mod_bound_nonzero).
          assert (4 <= a0)%N by (by eapply mod_bound_nonzero).
          lia.
        }
        subst a1.

        (* This here is what needs the full rt token!! *)
        iAssert (⌜θ !! ℓ0 = Some (MemMM, a0)⌝%I) with "[Haddr_ℓ0 Htok]" as "%Hθℓ0". {
          open_rt "Htok".
          by iPoseProof (ghost_map_lookup with "[$Haddr] [$]") as "%Hθℓ".
        }

        (* we can not break the token up again *)
        iPoseProof (virt_to_phys_slice_store_acc_weak_gc lmask off (arep_size PtrR)
                     with "[//] [$Htok] [$Hptr] [//]")
          as "(%hm & %Hhm & %Hdomθhm & %Hlocsθ_ws & Hnp &
          (%ns & %ns32 & %Hns & Hphys & Hwords) & Hclose)".

        (* make an atom_interp_weak *)
        iAssert (atom_interp_weak θ MemGC (PtrA (PtrHeap MemMM ℓ0)) (VAL_int32 n32))
          with "[Haddr_ℓ0]" as "Hat2". {
          cbn.
          iExists (tag_address MemMM a0)%N, n32.
          iSplitR; [done| iSplitR; [done|]].
          iExists a0.
          iFrame.
          iPureIntro.
          constructor; try done.
        }

        iPoseProof (atom_to_words_gc θ PtrR _ _ Harepsave with "[$Hat2]") as
          "(%ns_new & %ns32_new & %Hns_new & %Hbits & %Htypes & Hwords_new)".

        (* Extract pure facts from Hnp, derive dom θ cond for new words, then reconstruct Hnp *)
        iDestruct "Hnp" as "(Haddr_auth & %rm & %lm & Hroot & Hlayout & Hrti & %Hinj & %Hrootok & Hrootmem & %Hheapok)".
        iPoseProof (words_interp_locs_dom_θ θ rm MemGC _ _ Hrootok with "[$Hwords_new] [$Hroot] [$]")
          as "%Hlocsθ_new".
        iAssert (rt_token_nophys rti sr lmask θ hm) with "[Hroot Hlayout Hrti Hrootmem Haddr_auth]" as "Hnp".
        { by iFrame. }

        specialize (Hcg2spec a a32).
        specialize (Hcg2spec (sr_mem_gc sr) (rt_memaddr sr MemGC)).
        specialize Hcg2spec with (v:=(VAL_int32 n32)).
        specialize Hcg2spec with (bs:=(flat_map serialise_i32 ns32)).
        (* I need a pure fact about the length of ns and ns32 here *)
        iPoseProof (big_sepL2_length with "[$Hwords]") as "%Hlenns".
        pose proof (Forall2_length _ _ _ Hsliceflags) as Hlenareps.
        pose proof (Forall2_length _ _ _ Hns) as Hnslen.
        rewrite <- Hlenareps in Hlenns.
        rewrite <- Hlenns in Hnslen.
        cbn in Hnslen.

        iApply cwp_fupd. (* necessary for a later iMod *)
        iApply (Hcg2spec with "[$] [$] [$] [-]"); try done; try (cbn; done). {
          cbn.
          rewrite len_ser32.
          destruct ns32 as [|nn32 ns32]; try inversion Hnslen.
          destruct ns32; try inversion H5.
          cbn.
          done.
        }
        iIntros "!> Haddr".

        (* we need to use Hclose now! We have a bunch of tiny facts we need to do so *)

        iPoseProof (big_sepL2_length with "[$Hwords_new]") as "%Hlenns_new".
        cbn in Hlenns_new.
        destruct ns_new as [| n_new ns_new]; try inversion Hlenns_new.
        destruct ns_new; inversion H5; subst; clear H5.
        pose proof (Forall2_length _ _ _ Hns_new) as Hnslen_new.
        cbn in Hnslen_new.
        destruct ns32_new as [| n32_new ns32_new]; try inversion Hnslen_new.
        destruct ns32_new; inversion H5; subst; clear H5.
        clear Hlenns_new Hnslen_new.

        rewrite <- Hbits.
        cbn [bits].
        assert (serialise_i32 n32_new = flat_map serialise_i32 [n32_new]) by done.
        rewrite <- H3.

        iSpecialize ("Hclose" $! (serialize_atom (PtrA (PtrHeap MemMM ℓ0)))
                                    [n_new] [n32_new]).
        iSpecialize ("Hclose" with "[//] [%] [%] [%] [%] [$]").
        * done.
        * intros flags H5.
          eapply update_path_words_flags_compat; [exact Harepsave|done|done|done].
        * eapply Forall_impl.
          -- exact (update_path_words_locs_incl (dom θ) ws off _ Hlocsθ_ws Hlocsθ_new).
          -- intros ℓ' Hℓ'. rewrite <- Hdomθhm. exact Hℓ'.
        * eapply update_path_words_locs_incl; try done.
        * iSpecialize ("Hclose" with "[$Hwords_new] [$Hnp]").
          iMod "Hclose".
          iModIntro.
          iDestruct "Hclose" as "[pls hlp]".
          iApply ("HΦ" with "[$] [$] [$] [$]").
      + (* Hcg3 - Ptr GC *)
        inv_cg_bind Hcg3 [] ?wt ?wt ?wl ?wl es_loadroot ?rest Hloadroot Hcg3.
        clear es_store_w.
        inv_cg_bind Hcg3 [] ?wt ?wt ?wl ?wl es_store_w ?rest Hstore Hcg3.
        inv_cg_bind Hcg3 [] ?wt ?wt ?wl ?wl es_loc es_unregister Hloc Hunregister.
        inv_cg_emit Hloc; subst.
        clear_nils; clear Hretval.

        (* stuff to do before doing starting to deal with cwp stuff*)
        (* note:  *)
        iEval (cbn) in "Hat".
        iDestruct "Hat" as "(%n' & %n32' & %forinv & %toinv & Hrp)".
        inversion toinv; subst n32'; clear toinv.
        pose proof (N_i32_repr_inj _ _ _ forinv Nrepr) as ->; clear forinv.
        iDestruct "Hrp" as "(%rp & %Hreprroot & Hroot_ℓ0)".
        inversion Hreprroot. {
          exfalso.
          apply N.Div0.mod_divides in H as [c ->].
          lia.
        }
        iEval (cbn) in "Hroot_ℓ0".
        destruct μ; try done.
        subst rp.
        assert (a1 = a0). {
          cbn in H1.
          lia.
        }
        subst a1.

        iPoseProof (virt_to_phys_slice_store_acc_weak_gc lmask off (arep_size PtrR)
                     with "[//] [$Htok] [$Hptr] [//]")
          as "(%hm & %Hhm & %Hdomθhm & %Hlocsθ_ws & Hnp &
          (%ns & %ns32 & %Hns & Hphys & Hwords) & Hclose)".

        (* for myself: we are STORING PtrA PtrHeap MemGC ℓ0 *)

        (* ------ LOAD ROOT ------- *)
        apply (wp_loadroot sr) in Hloadroot as (_ & -> & -> & Hloadroot_spec).
        rewrite app_assoc.

        (* break apart rt token *)
        iDestruct "Hnp" as "(Haddr_auth & %rm & %lm & Hroot & Hlayout & Hrti & %Hinj & %Hrootok & Hrootmem & %Hheapok)".

        iApply (cwp_seq with "[Hf Hrun Hroot_ℓ0 Hrootmem Hroot]"). {
          (* to isolate load_root, first a val_app *)
          change (to_consts [?x; ?y]) with ((to_consts [x]) ++ to_consts [y]).
          rewrite <- app_assoc.
          iApply cwp_val_app; first apply has_values_to_consts.

          iApply (Hloadroot_spec with "[$] [$] [] [$] [$] [$]");
            [exact Nrepr|by apply Is_true_true, has_values_to_consts|
             exact Hreprroot| exact Hrootok | iPureIntro; exact Hmemgc | ].
          iNext.
          iIntros (ah ah32) "Hreprah Hreprptr Hroot_ℓ0 Hroot Hrootmem".

          let Q := open_constr:(_ : iProp Σ) in
          instantiate (1 :=
            (λ f'' vs'', ∃ ah ah32,
              ⌜f'' = f /\ vs'' = [VAL_int32 a32; VAL_int32 ah32]⌝ ∗ ⌜N_i32_repr ah ah32⌝
                                  ∗ ⌜repr_pointer θ (PtrHeap MemGC ℓ0) ah⌝ ∗ Q)%I).
          unfold fvs_combine; cbn.
          iExists ah, ah32.
          iSplitR; first done.
          iFrame.
          iAccu.
        }

        iIntros (f' vs') "Hres Hf Hrun".
        iDestruct "Hres" as "(%ah & %ah32 & (-> & ->)
          & %Hrepr_ah & %Hrepr_ptr & Hroot_ℓ0 & Hroot & Hrootmem)".
        iAssert (rt_token_nophys rti sr lmask θ hm) with "[Hroot Hlayout Hrti Hrootmem Haddr_auth]" as "Hnp".
        { by iFrame. }
        clear dependent rm. clear dependent lm. clear Hinj.

        (* we are past loadroot!! *)
        clear Hloadroot_spec.

        (* ------ STORE W ------- *)
        apply wp_store_w in Hstore as (_ & -> & -> & Hcg3spec).

        (* this is where we finally need words interp. We get this through
           asserting atom_interp_weak *)
        iAssert (atom_interp_weak θ MemGC (PtrA (PtrHeap MemGC ℓ0)) (VAL_int32 ah32))
          with "[]" as "Hat". {
          cbn.
          iExists ah, ah32.
          done.
        }

        iPoseProof (atom_to_words_gc θ PtrR _ _ Harepsave with "[$Hat]") as
          "(%ns_new & %ns32_new & %Hns_new & %Hbits & %Htypes & Hwords_new)".

        (* Extract pure facts from Hnp, derive dom θ cond for new words, then reconstruct Hnp *)
        iDestruct "Hnp" as "(Haddr_auth & %rm & %lm & Hroot & Hlayout & Hrti & %Hinj & %Hrootok & Hrootmem & %Hheapok)".
        iPoseProof (words_interp_locs_dom_θ θ rm MemGC _ _ Hrootok with "[$Hwords_new] [$Hroot] [$]")
          as "%Hlocsθ_new".
        iAssert (rt_token_nophys rti sr lmask θ hm) with "[Hroot Hlayout Hrti Hrootmem Haddr_auth]" as "Hnp".
        { by iFrame. }
        clear dependent rm; clear dependent lm; clear Hinj.
        move Hcg3spec at bottom.

        (* alright we need to spec again. I'm so suspicious *)
        (* like we needed to do loadroot before we could get atom_interp_weak so
           that's good*)
        (* but where is a0 ↦root ℓ0 gonna go... *)
        rewrite app_assoc.
        iPoseProof (big_sepL2_length with "[$Hwords]") as "%Hlenns".
        pose proof (Forall2_length _ _ _ Hsliceflags) as Hlenareps.
        pose proof (Forall2_length _ _ _ Hns) as Hnslen.
        rewrite <- Hlenareps in Hlenns.
        rewrite <- Hlenns in Hnslen.
        cbn in Hnslen.

        (* iApply cwp_fupd.  *)
        iApply (cwp_seq with "[Hf Hrun Hphys]"). {
          iApply (Hcg3spec with "[$] [$] [$]"); try done. {
            cbn.
            rewrite len_ser32.
            destruct ns32 as [|nn32 ns32]; try inversion Hnslen.
            destruct ns32; try inversion H5.
            cbn.
            done.
          }
          iNext.
          iIntros "Hphys".

          (* let Q := open_constr:(_ : iProp Σ) in *)
          instantiate (1 := (λ f'' vs'',
                ⌜f'' = f /\ vs'' = []⌝ ∗
                rt_memaddr sr MemGC↦[wms][a + 4 * N.of_nat off]bits (VAL_int32 ah32))%I).
          iEval (cbn).
          iSplitR; first done.
          iClear "Hat Hwords_new".
          iFrame.
        }
        iIntros (f0 vs0) "Hres Hf Hrun".
        iDestruct "Hres" as "((-> & ->) & Hphys)".
        clear_nils.

        (* ------ GET LOCAL ------- *)
        iApply (cwp_seq with "[Hf Hrun]").
        {
          iClear "Hat Hwords_new". (* else the eauto doesn't work lol *)
          iApply (cwp_local_get with "[] [$] [$]"); eauto.
          now instantiate (1:= λ f' v', ⌜f' = f ∧ v' = [VAL_int32 n32]⌝%I).
        }
        iIntros (f' vs') "[-> ->] Hf Hrun".

        (* ------ UNREGISTER ROOT ------ *)
        apply (wp_unregisterroot rti sr) in Hunregister as (_ & -> & -> & Hunreg_spec).
        move Hunreg_spec at bottom.

        (* use Hclose now to get rt token *)
        iPoseProof (big_sepL2_length with "[$Hwords_new]") as "%Hlenns_new".
        cbn in Hlenns_new.
        destruct ns_new as [| n_new ns_new]; try inversion Hlenns_new.
        destruct ns_new; inversion H5; subst; clear H5.
        pose proof (Forall2_length _ _ _ Hns_new) as Hnslen_new.
        cbn in Hnslen_new.
        destruct ns32_new as [| n32_new ns32_new]; try inversion Hnslen_new.
        destruct ns32_new; inversion H5; subst; clear H5.
        clear Hlenns_new Hnslen_new.



        iSpecialize ("Hclose" $! ((serialize_atom (PtrA (PtrHeap MemGC ℓ0))))).
        iSpecialize ("Hclose" $! [n_new] [n32_new]).

        rewrite Hbits.

        iApply fupd_cwp.
        iMod ("Hclose" with "[//] [//] [%] [%] [%] [$] [$] [$]") as "(Hℓ_heap & Hrt)".
        { intros flags H3.
          eapply update_path_words_flags_compat; [exact Harepsave|done|done|done]. }
        { eapply Forall_impl.
          -- exact (update_path_words_locs_incl (dom θ) ws off _ Hlocsθ_ws Hlocsθ_new).
          -- intros ℓ' Hℓ'. rewrite <- Hdomθhm. exact Hℓ'. }
        { eapply update_path_words_locs_incl; try done. }
        iModIntro.

        (* finally, unreg spec! *)
        iApply (Hunreg_spec with "[$] [HΦ Hℓ_heap Hwords] [$] [$] [//] [$] [$] [$]");
          [ | | apply Is_true_true, has_values_to_consts | ]; try done.
        iIntros "Hrt Hown Hinstance".
        iApply ("HΦ" with "[$] [$] [$] [$]").
    - (* ι <> PtrR case *)
      eapply wp_ite_gc_ptr_nonptr in Hcg; last assumption.
      apply wp_store_w in Hcg as (_ & _ & _ & Hcgspec).


      iPoseProof (virt_to_phys_slice_store_acc_weak_gc lmask off (arep_size ι)
                   with "[//] [$Htok] [$Hptr] [//]")
        as "(%hm & %Hhm & %Hdomθhm & %Hlocsθ_ws & Hnp &
          (%ns & %ns32 & %Hns & Hphys & Hwords) & Hclose)".

      iPoseProof ((atom_interp_to_weak_memGC_nonptr o val_v ι θ Harep n) with "[$Hat]") as "Hat".

      iPoseProof (atom_to_words_gc θ ι _ _ Harep with "[$Hat]") as
        "(%ns_new & %ns32_new & %Hns_new & %Hbits & %Htypes & Hwords_new)".

      (* Extract pure facts from Hnp, derive dom θ cond for new words, then reconstruct Hnp *)
      iDestruct "Hnp" as "(Haddr_auth & %rm & %lm & Hroot & Hlayout & Hrti & %Hinj & %Hrootok & Hrootmem & %Hheapok)".
      iPoseProof (words_interp_locs_dom_θ θ rm MemGC _ _ Hrootok with "[$Hwords_new] [$Hroot] [$Haddr_auth]")
        as "%Hlocsθ_new".
      iAssert (rt_token_nophys rti sr lmask θ hm) with "[Hroot Hlayout Hrti Hrootmem Haddr_auth]" as "Hnp".
      { by iFrame. }
      clear dependent rm; clear dependent lm; clear Hinj.

      move Hcgspec at bottom.
      specialize (Hcgspec a a32).
      specialize (Hcgspec (sr_mem_gc sr) (rt_memaddr sr MemGC)).
      specialize Hcgspec with (v:=val_v).
      specialize Hcgspec with (bs:=(flat_map serialise_i32 ns32)).
      (* I need a pure fact about the length of ns and ns32 here *)
      iPoseProof (big_sepL2_length with "[$Hwords]") as "%Hlenns".
      pose proof (Forall2_length _ _ _ Hsliceflags) as Hlenareps.
      pose proof (Forall2_length _ _ _ Hns) as Hnslen.
      rewrite <- Hlenareps in Hlenns.
      rewrite <- Hlenns in Hnslen.

      iApply cwp_fupd. (* necessary for a later iMod *)
      iApply (Hcgspec with "[$] [$] [$] [-]"); try done; try (cbn; done). {
        cbn.
        rewrite len_ser32.
        rewrite length_t_translate_arep.
        assert (length (arep_flags ι) = arep_size ι) by (destruct ι; done).
        lia.
      }
      iIntros "!> Haddr".

      (* we need to use Hclose now! We have a bunch of tiny facts we need to do so *)
      rewrite <- Hbits.
      iSpecialize ("Hclose" $! (serialize_atom o) ns_new ns32_new).
      iSpecialize ("Hclose" with "[%] [//] [%] [%] [%] [$]").
      * by apply has_arep_size.
      * intros flags H2.
        eapply update_path_words_flags_compat; [exact Harep|done|done|done].
      * eapply Forall_impl.
        -- exact (update_path_words_locs_incl (dom θ) ws off _ Hlocsθ_ws Hlocsθ_new).
        -- intros ℓ' Hℓ'. rewrite <- Hdomθhm. exact Hℓ'.
      * eapply update_path_words_locs_incl; try done.
      * iSpecialize ("Hclose" with "[$Hwords_new] [$Hnp]").
        iMod "Hclose".
        iModIntro.
        iDestruct "Hclose" as "[pls hlp]".
        iApply ("HΦ" with "[$] [$] [$] [$]").
  Qed.

  Lemma wp_store_weak_gc_inner a_idx ιs:
    ∀ off vs_idx wt wl ret wt' wl' es,
    length vs_idx = length ιs ->
    run_codegen (foldlM
         (λ (off : nat) '(v, ι),
            store1 mr MemGC a_idx off v ι ≫= λ _ : (), Monad.ret (off + arep_size ι))
         off (zip vs_idx ιs)) wt wl = inr (ret, wt', wl', es) ->
    ret = seq.foldl (λ off' ι, off' + arep_size ι) off ιs /\
    wt' = [] /\ wl' = [] /\
    ∀ f ℓ a a32 val_vs lmask θ os ws E B R Φ,
    ⊢ "Hf"       ∷ ↪[frame] f -∗
      "Hrun"     ∷ ↪[RUN] -∗
      "Hptr"     ∷ ℓ ↦heap ws -∗
      "%Haddr"   ∷ ⌜ θ !! ℓ = Some (MemGC, a)⌝ -∗
      "%Hℓmask"  ∷ ⌜lmask ℓ⌝ -∗
      "Htok"     ∷ rt_token rti sr lmask θ -∗
      "Hunreg"   ∷ instance_rt_func_interp (mr_func_unregisterroot mr) (sr_func_unregisterroot sr) (runtime.spec_unregisterroot rti sr) (f_inst f) -∗
      "Hown"     ∷ na_own logrel_nais E -∗
      "%Hmask"   ∷ ⌜↑ns_fun (N.of_nat (sr_func_unregisterroot sr)) ⊆ E⌝ -∗
      "%Ha32"    ∷ ⌜f_locs f !! localimm a_idx = Some (VAL_int32 a32)⌝ -∗
      "%Hv"      ∷ ⌜Forall2 (λ v_idx val_v, f_locs f !! localimm v_idx = Some val_v) vs_idx val_vs⌝ -∗
      "%Hrepa"   ∷ ⌜N_i32_repr (tag_address MemGC a) a32⌝ -∗
      "%Hmod"    ∷ ⌜(a `mod` 4 = 0)%N⌝ -∗
      "%Hnz"     ∷ ⌜(a ≠ 0)%N⌝ -∗
      "%Hbound"  ∷ ⌜off + sum_list_with arep_size ιs ≤ length ws⌝ -∗
      "%Harep"   ∷ ⌜Forall2 has_arep ιs os⌝ -∗
      "%Hsliceflags" ∷ ⌜Forall2 word_has_flag (concat (map arep_flags ιs))
                                               (take (sum_list_with arep_size ιs) (drop off ws))⌝ -∗
      "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemMM)⌝ -∗
      "%Hrepgc"  ∷ ⌜N_nat_repr (sr_mem_gc sr) (rt_memaddr sr MemGC)⌝ -∗
      "%Hmemmm"  ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
      "%Hmemgc"  ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemGC = Some (sr_mem_gc sr)⌝ -∗
      "Hat"      ∷ atoms_interp os val_vs -∗
      "HΦ"       ∷ (ℓ ↦heap (update_path_words off ws (concat (map serialize_atom os))) -∗
                    na_own logrel_nais E -∗
                    instance_rt_func_interp (mr_func_unregisterroot mr) (sr_func_unregisterroot sr) (runtime.spec_unregisterroot rti sr) (f_inst f) -∗
                    rt_token rti sr lmask θ -∗
                    Φ f []) -∗
    CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
    induction ιs as [| ιs ι] using seq.last_ind; intros * Hlen Hcg *.
    - assert (zip vs_idx ([]:list atomic_rep) = []) by (by apply zip_nil_r).
      rewrite H in Hcg.
      cbn in Hcg.
      inversion Hcg; subst.
      do 3 split; try done.
      intros *; repeat iIntros "@".
      iApply (cwp_nil with "[$] [$]").
      (* os is nil, val_vs is nil, and ws didn't update *)
      inversion Harep; subst.
      iPoseProof (big_sepL2_nil_inv_l with "[$Hat]") as "%Hvalvslen". subst.
      assert (update_path_words ret ws (concat (map serialize_atom [])) = ws). {
        cbn.
        apply update_path_words_empty_2.
      }
      rewrite H0.
      iApply ("HΦ" with "[$] [$] [$] [$]").
    - (* to start with, we need to make
         (zip vs_idx (seq.rcons ιs ι)) = seq.rcons (zip vs_idx_small ιs) (v_idx, ι) *)
      (* we know that length ιs = length os = length val_vs = length vs_idx
                            Harep         Hat           Hv
         so then we know vs_idx must be equal to some seq.rcons vs_idx v_idx. then zip seq.rcons?
         I think that should work, but that's not interesting right at this moment so asserting
       *)
      rename vs_idx into vs_idx_big.
      assert (∃ vs_idx v_idx, vs_idx_big = seq.rcons vs_idx v_idx /\ length vs_idx = length ιs). {
        rewrite rcons_app in Hlen.
        rewrite length_app in Hlen.
        cbn in Hlen.
        apply length_split in Hlen as (vs_idx & v_idxT & -> & hlen1 & hlen2).
        destruct v_idxT as [|v_idx rest]; [inversion hlen2|].
        destruct rest; [|inversion hlen2].
        exists vs_idx, v_idx.
        rewrite rcons_app.
        done.
      }
      destruct H as (vs_idx & v_idx & -> & Hleminis).

      assert (zip (seq.rcons vs_idx v_idx) (seq.rcons ιs ι) =
                seq.rcons (zip vs_idx ιs) (v_idx, ι)). {
        by apply zip_rcons.
      }
      rewrite H in Hcg.

      apply inv_foldlM_rcons in Hcg.
      rewrite seq.foldl_rcons.
      destruct Hcg as (off_ιs & wt_ι & wt_ιs & wl_ι & wl_ιs & es_ι & es_ιs & Hinit & Hlast).
      destruct Hlast as (Hlast & -> & -> & ->).
      inv_cg_bind Hlast a0' wt_bs wt_b wl_bs wl_b es_bs es_b Hbs Hfb.
      subst.
      inv_cg_ret Hfb; subst.
      eapply IHιs in Hinit; auto.
      clear IHιs.

      destruct Hinit as (-> & -> & -> & Hinit).
      pose proof Hbs as Hbs'.
      clear_nils.

      apply (wp_store1_gc_weak) in Hbs'.
      destruct Hbs' as (-> & -> & -> & Hbs_spec).

      do 3 (split; first by auto).

      (* finally the iris proof... *)
      (* note that the overall structure is to do cwp_seq and use Hinit then Hbs_spec *)
      intros *; repeat iIntros "@".

      (* the thing we need to do before cwp_seq is split up Hat into the Hinit part and the
         Hbs part. This involves showing os = seq.rcons os o and val_vs = seq.rcons os o *)
      pose proof Harep as Hosslicing.
      eapply Forall2_rcons_inv_l in Hosslicing; try done.
      rename os into os_big.
      destruct Hosslicing as (o & os & Ho & Hos & Hos_eq).
      subst os_big.
      rename val_vs into val_vs_big.
      unfold atoms_interp.
      Opaque atom_interp. cbn.
      iPoseProof (big_sepL2_rcons_inv_l with "[$Hat]") as
        "(%val_v & %val_vs & -> & Hoa & Hat)"; try done.
      Transparent atom_interp.
      (* rewrite <- rcons_app in Hv. *)
      pose proof Hv as Hvslicing.
      rewrite !rcons_app in Hv.
      eapply Forall2_rcons_inv_l in Hvslicing; try done.
      destruct Hvslicing as (valvstemp & valvtemp & Hlocsvalv & Hlocsvalvs & Hinv).
      apply seq.rcons_inj in Hinv; inversion Hinv; subst; clear Hinv.

      (* the new one is hslice flags *)
      rewrite !rcons_app in Hsliceflags.
      rewrite map_app in Hsliceflags.
      rewrite sum_list_with_app in Hsliceflags.
      rewrite concat_app in Hsliceflags.

      (* I need this both for split_word_has_flag_arep and the Hinit! *)
      assert (Hlensmall: off + sum_list_with arep_size ιs ≤ length ws). {
          rewrite rcons_app in Hbound.
          rewrite sum_list_with_app in Hbound.
          lia.
      }
      apply (split_word_has_flag_arep _ _ _ _ os Hlensmall Hos) in Hsliceflags as htemp.
      destruct htemp as [Hflagsιs Hflagsι].
      (* put some more in here but for now this is enough lol *)

      (* Now we can cwp_seq. Note lots of pure Forall/rcons manipulations happen inside
         that might be better brought outside (we'll see).
       *)
      iApply (cwp_seq with "[Hf Hrun Hptr Htok HΦ Hat Hunreg Hown]"). {
        iApply (Hinit with "[$] [$] [$] [//] [//] [$] [$] [$] [//] [//] [//]
                            [//] [//] [//] [//] [//] [//] [//] [//] [//] [//] [$] [-]").
        iIntros "Hℓ Hown Hunreg Hrt".
        let Q := open_constr:(_ : iProp Σ) in
        instantiate (1 := (λ f'' vs'', ⌜f'' = f /\ vs'' = []⌝ ∗ Q)%I).
        cbn.
        iSplitR; first done.
        iAccu.
      }
      cbn.
      iIntros (f0 vs) "Hres Hf Hrun".
      iDestruct "Hres" as "((-> & ->) & HΦ & Hℓ_heap & Hown & Hunreg & Hrt)".
      clear_nils.

      (* and now apply the hbs! *)
      iApply (Hbs_spec with "[$] [$] [$] [//] [//] [$] [$] [$] [//] [//] [//]
                            [//] [//] [//] [] [//] [] [//] [//] [//] [//] [$Hoa] [-]").
      + iPureIntro.
        (* this will end up true due to Hbound and Hos *)
        rewrite rcons_app in Hbound.
        rewrite sum_list_with_app in Hbound.
        cbn in Hbound.
        rewrite seq_foldl_sum_list_with.
        rewrite update_path_words_size.
        2: {
          rewrite (has_arep_means_equal_lengths _ _ Hos).
          rewrite length_arep_flags_size.
          lia.
        }
        lia.

      + iPureIntro.
        rewrite seq_foldl_sum_list_with.
        done.
      + iIntros "Hℓ_heap Hown Hunreg Hrt".
        (* one last update_path_words manipulation *)
        assert (update_path_words off ws (concat (map serialize_atom (seq.rcons os o))) =
                  update_path_words
                        (seq.foldl (λ (off' : nat) (ι0 : atomic_rep), off' + arep_size ι0)
                           off ιs)
                        (update_path_words off ws (concat (map serialize_atom os)))
                        (serialize_atom o)
               ). {
          rewrite seq_foldl_sum_list_with.
          change map with @seq.map.
          rewrite seq.map_rcons.
          rewrite rcons_app.
          rewrite concat_app.
          cbn. clear_nils.
          change @seq.map with map.
          assert (length (concat (map serialize_atom os)) = sum_list_with arep_size ιs). {
            rewrite (has_arep_means_equal_lengths _ _ Hos).
            rewrite length_arep_flags_size.
            done.
          }
          rewrite <- H0.
          apply update_path_words_in_stages.
        }
        rewrite <- H0.
        iApply ("HΦ" with "[$] [$] [$] [$]").

  Qed.

  Lemma wp_store_weak_gc a_idx off ιs vs_idx wt wl ret wt' wl' es :
    length vs_idx = length ιs ->
    run_codegen (memory.store mr MemGC a_idx off vs_idx ιs) wt wl = inr (ret, wt', wl', es) ->
    ret = () /\ wt' = [] /\ wl' = [] /\
    ∀ f ℓ a a32 val_vs lmask θ os ws E B R Φ,
    ⊢ "Hf"       ∷ ↪[frame] f -∗
      "Hrun"     ∷ ↪[RUN] -∗
      "Hptr"     ∷ ℓ ↦heap ws -∗
      "%Haddr"   ∷ ⌜ θ !! ℓ = Some (MemGC, a)⌝ -∗
      "%Hℓmask"  ∷ ⌜lmask ℓ⌝ -∗
      "Htok"     ∷ rt_token rti sr lmask θ -∗
      "Hunreg"   ∷ instance_rt_func_interp (mr_func_unregisterroot mr) (sr_func_unregisterroot sr) (runtime.spec_unregisterroot rti sr) (f_inst f) -∗
      "Hown"     ∷ na_own logrel_nais E -∗
      "%Hmask"   ∷ ⌜↑ns_fun (N.of_nat (sr_func_unregisterroot sr)) ⊆ E⌝ -∗
      "%Ha32"    ∷ ⌜f_locs f !! localimm a_idx = Some (VAL_int32 a32)⌝ -∗
      "%Hv"      ∷ ⌜Forall2 (λ v_idx val_v, f_locs f !! localimm v_idx = Some val_v) vs_idx val_vs⌝ -∗
      "%Hrepa"   ∷ ⌜N_i32_repr (tag_address MemGC a) a32⌝ -∗
      "%Hmod"    ∷ ⌜(a `mod` 4 = 0)%N⌝ -∗
      "%Hnz"     ∷ ⌜(a ≠ 0)%N⌝ -∗
      "%Hbound"  ∷ ⌜off + sum_list_with arep_size ιs ≤ length ws⌝ -∗
      "%Harep"   ∷ ⌜Forall2 has_arep ιs os⌝ -∗
      "%Hsliceflags" ∷ ⌜Forall2 word_has_flag (concat (map arep_flags ιs))
                                               (take (sum_list_with arep_size ιs) (drop off ws))⌝ -∗
      "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemMM)⌝ -∗
      "%Hrepgc"  ∷ ⌜N_nat_repr (sr_mem_gc sr) (rt_memaddr sr MemGC)⌝ -∗
      "%Hmemmm"  ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
      "%Hmemgc"  ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemGC = Some (sr_mem_gc sr)⌝ -∗
      "Hat"      ∷ atoms_interp os val_vs -∗ (* most likely to change *)
      "HΦ"       ∷ (ℓ ↦heap (update_path_words off ws (concat (map serialize_atom os))) -∗
                    na_own logrel_nais E -∗
                    instance_rt_func_interp (mr_func_unregisterroot mr) (sr_func_unregisterroot sr) (runtime.spec_unregisterroot rti sr) (f_inst f) -∗
                    rt_token rti sr lmask θ -∗
                    Φ f []) -∗
    CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
    intros Hlen Hcg.
    unfold memory.store in Hcg.
    apply wp_ignore in Hcg.
    destruct Hcg as (-> & off' & Hcg).
    pose proof (wp_store_weak_gc_inner _ _ _ _ _ _ _ _ _ _ Hlen Hcg) as (-> & U & V & W).
    intuition.
  Qed.




(* -------------------- STORE STRONG MM ----------------------- *)



  Lemma wp_store1_mm_strong a_idx off ι v_idx wt wl ret wt' wl' es :
    run_codegen (store1 mr MemMM a_idx off v_idx ι) wt wl = inr (ret, wt', wl', es) ->
    ret = () /\ wt' = [] /\ wl' = [] /\
    ∀ f ℓ a a32 val_v lmask θ o ws E B R Φ,
    ⊢ "Hf"       ∷ ↪[frame] f -∗
      "Hrun"     ∷ ↪[RUN] -∗
      "Hptr"     ∷ ℓ ↦heap ws -∗
      "Haddr"    ∷ ℓ ↦addr (MemMM, a) -∗
      "%Hℓmasknot"  ∷ ⌜¬ lmask ℓ⌝ -∗ (* to specify you're Messing with stuff *)
      "Htok"     ∷ rt_token rti sr lmask θ -∗
      "%Ha32"    ∷ ⌜f_locs f !! localimm a_idx = Some (VAL_int32 a32)⌝ -∗
      "%Hv"      ∷ ⌜f_locs f !! localimm v_idx = Some val_v⌝ -∗
      "%Hrepa"   ∷ ⌜N_i32_repr (tag_address MemMM a) a32⌝ -∗
      "%Hmod"    ∷ ⌜(a `mod` 4 = 0)%N⌝ -∗
      "%Hnz"     ∷ ⌜(a ≠ 0)%N⌝ -∗
      "%Hbound"  ∷ ⌜off + arep_size ι ≤ length ws⌝ -∗
      "%Harep"   ∷ ⌜has_arep ι o⌝ -∗ (* what you're putting in *)
      "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemMM)⌝ -∗
      "%Hmemmm"  ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
      "Hat"      ∷ atom_interp_weak θ MemMM o val_v -∗
      "HΦ"       ∷ (ℓ ↦heap (update_path_words off ws (serialize_atom o)) -∗
                    ℓ ↦addr (MemMM, a) -∗
                    rt_token rti sr lmask θ -∗
                    Φ f []) -∗
    CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
    intros Hcg.
    unfold store1 in Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_a ?rest Ha Hcg.
    inv_cg_emit Ha; subst.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_v es_store_w Hv Hcg.
    inv_cg_emit Hv; subst.
    apply wp_store_w in Hcg.
    destruct Hcg as (-> & -> & -> & Hstore_spec).
    clear_nils.
    do 3 (split; first done).
    intros *.
    repeat iIntros "@".
    (* get_local for address *)
    iApply (cwp_seq with "[Hf Hrun]").
    {
      iApply (cwp_local_get with "[] [$] [$]"); eauto.
      now instantiate (1:= λ f' v', ⌜f' = f ∧ v' = [VAL_int32 a32]⌝%I).
    }
    iIntros (f' vs') "[-> ->] Hf Hrun".
    rewrite app_assoc.
    (* get_local for value *)
    iApply (cwp_seq with "[Hf Hrun]").
    {
      iApply cwp_val_app; first apply has_values_to_consts.
      iApply (cwp_local_get with "[] [$] [$]"); eauto.
      now instantiate (1:= λ f' v', ⌜f' = f ∧ v' = [VAL_int32 a32; val_v]⌝%I).
    }
    iIntros (f' vs') "[-> ->] Hf Hrun".
    (* Open abstract-physical connection for the slice [off, off + arep_size ι) *)
    iPoseProof (virt_to_phys_slice_store_acc_strong rti sr lmask off (arep_size ι) with "[//] [$Htok] [$Hptr] [$Haddr] [//]")
      as "(%hm & %Hhm & %Hdomθhm & %Hlocsθ_ws & Hnp & (%ns & %ns32 & %Hns & Hphys & Hwords) & Hclose)".
    (* atom_to_words_mm consumes Hat; it also returns types_agree which is needed for Hstore_spec *)
    iPoseProof (atom_to_words_mm θ ι o val_v Harep with "[$Hat]") as "(%ns_new & %ns32_new & %Hns_new & %Hbits & %Htypes & Hwords_new)".
    (* Extract pure facts from Hnp, derive dom θ cond for new words, then reconstruct Hnp *)
    unfold rt_token_nophys.
    iDestruct "Hnp" as "(Haddr & (%rm & %lm & Hroot & Hlayout & Hrti & %Hinj & %Hrootok & Hrootmem & %Hheapok))".
    iPoseProof (words_interp_locs_dom_θ θ rm MemMM _ ns_new Hrootok with "[$Hwords_new] [$Hroot] [$Haddr]")
      as "%Hlocsθ_new".
    iAssert (rt_token_nophys rti sr lmask θ hm) with "[Hroot Hlayout Hrti Hrootmem Haddr]" as "Hnp".
    { iFrame. iPureIntro. split; last split; done. }
    (* Compute byte-length of old slice *)
    iPoseProof (big_sepL2_length with "Hwords") as "%Hlenws".
    assert (Hlenbytes : length (flat_map serialise_i32 ns32) = length_t (translate_arep ι)).
    {
      rewrite len_ser32.
      rewrite -(Forall2_length _ _ _ Hns).
      rewrite -Hlenws length_take length_drop length_t_translate_arep.
      lia.
    }
    iApply cwp_fupd.
    iApply (Hstore_spec a a32 (sr_mem_mm sr) (rt_memaddr sr MemMM) with "[$Hf] [$Hrun] [$Hphys]"); eauto.
    iNext; iIntros "Hnew_phys".
    iEval (rewrite <- Hbits) in "Hnew_phys".
    iMod ("Hclose" $! (serialize_atom o) ns_new ns32_new
      with "[%] [%] [%] [%] [$Hnew_phys] [$Hwords_new] [$Hnp]") as "(Hptr_new & Haddr & Htok)".
    - exact (has_arep_size ι o Harep).
    - exact Hns_new.
    - eapply Forall_impl.
      + exact (update_path_words_locs_incl (dom θ) ws off (serialize_atom o) Hlocsθ_ws Hlocsθ_new).
      + intros ℓ' Hℓ'. rewrite <- Hdomθhm. exact Hℓ'.
    -  exact (update_path_words_locs_incl (dom θ) ws off (serialize_atom o)
               Hlocsθ_ws Hlocsθ_new).
    - iModIntro. iApply ("HΦ" with "[$] [$]"); iFrame.
  Qed.

  Lemma wp_store_strong_mm_inner a_idx ιs :
    ∀ off vs_idx wt wl ret wt' wl' es,
    length vs_idx = length ιs -> (* needs to be true for ret = .. to hold *)
    run_codegen (foldlM
         (λ (off : nat) '(v, ι),
            store1 mr MemMM a_idx off v ι ≫= λ _ : (), Monad.ret (off + arep_size ι))
         off (zip vs_idx ιs)) wt wl = inr (ret, wt', wl', es) ->
    ret = seq.foldl (λ (off':nat) (ι:atomic_rep), off' + arep_size ι)%nat off ιs /\
    wt' = [] /\ wl' = [] /\
    ∀ f ℓ a a32 val_vs lmask θ os ws E B R Φ,
    ⊢ "Hf"       ∷ ↪[frame] f -∗
      "Hrun"     ∷ ↪[RUN] -∗
      "Hptr"     ∷ ℓ ↦heap ws -∗
      "Haddr"    ∷ ℓ ↦addr (MemMM, a) -∗
      "%Hℓmask"  ∷ ⌜¬ lmask ℓ⌝ -∗
      "Htok"     ∷ rt_token rti sr lmask θ -∗
      "%Ha32"    ∷ ⌜f_locs f !! localimm a_idx = Some (VAL_int32 a32)⌝ -∗
      "%Hv"      ∷ ⌜Forall2 (λ v_idx val_v, f_locs f !! localimm v_idx = Some val_v) vs_idx val_vs⌝ -∗
      "%Hrepa"   ∷ ⌜N_i32_repr (tag_address MemMM a) a32⌝ -∗
      "%Hmod"    ∷ ⌜(a `mod` 4 = 0)%N⌝ -∗
      "%Hnz"     ∷ ⌜(a ≠ 0)%N⌝ -∗
      "%Hbound"  ∷ ⌜off + sum_list_with arep_size ιs ≤ length ws⌝ -∗
      "%Harep"   ∷ ⌜Forall2 has_arep ιs os⌝ -∗
      (* "%Hsliceflags" ∷ ⌜Forall2 word_has_flag (concat (map arep_flags ιs)) *)
      (*                                         (take (sum_list_with arep_size ιs) (drop off ws))⌝ -∗ *)
      "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemMM)⌝ -∗
      "%Hmemmm"  ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
      "Hat"      ∷ ([∗ list] o;val_v ∈ os;val_vs, atom_interp_weak θ MemMM o val_v) -∗
      "HΦ"       ∷ (ℓ ↦heap (update_path_words off ws (concat (map serialize_atom os))) -∗
                    ℓ ↦addr (MemMM, a) -∗
                    rt_token rti sr lmask θ -∗
                    Φ f []) -∗
    CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
    induction ιs as [| ιs ι] using seq.last_ind; intros * Hlen Hcg *.
    - assert (zip vs_idx ([]:list atomic_rep) = []) by (by apply zip_nil_r).
      rewrite H in Hcg.
      cbn in Hcg.
      inversion Hcg; subst.
      do 3 (split; first done).
      intros *; repeat iIntros "@".
      iApply (cwp_nil with "[$] [$]").
      (* os is nil, val_vs is nil, and ws didn't update *)
      inversion Harep; subst.
      iPoseProof (big_sepL2_nil_inv_l with "[$Hat]") as "%Hvalvslen". subst.
      assert (update_path_words ret ws (concat (map serialize_atom [])) = ws). {
        cbn.
        apply update_path_words_empty_2.
      }
      rewrite H0.
      iApply ("HΦ" with "[$] [$] [$]").
    - (* to start with, we need to make
         (zip vs_idx (seq.rcons ιs ι)) = seq.rcons (zip vs_idx_small ιs) (v_idx, ι)
         but we can only know this is safe when we know something about vs_idx. This
         is why we need the length vs_idx = length ιs.

         NOTE: I tried to make a set up where the ret = ... was after introing the
         iris resources (because then you can get it through Hv/Hat/Harep). But it just
         didn't work lol. I think length vs_idx = length ιs should always be satisfied
         anyway so should be okay?
       *)
      rename vs_idx into vs_idx_big.
      assert (∃ vs_idx v_idx, vs_idx_big = vs_idx ++ [v_idx]
                              /\ length vs_idx = length ιs). {
        rewrite rcons_app in Hlen.
        rewrite length_app in Hlen.
        cbn in Hlen.
        apply length_split in Hlen as (vs_idx & v_idxT & -> & hlen1 & hlen2).
        destruct v_idxT as [|v_idx rest]; [inversion hlen2|].
        destruct rest; [|inversion hlen2].
        exists vs_idx, v_idx; done.
      }
      destruct H as (vs_idx & v_idx & Hbig & Hlenminis).
      subst vs_idx_big.

      rewrite <- rcons_app in Hcg.
      assert (zip (seq.rcons vs_idx v_idx) (seq.rcons ιs ι) =
                seq.rcons (zip vs_idx ιs) (v_idx, ι)). {
        by apply zip_rcons.
      }
      rewrite H in Hcg.

      (* split the codegen into first portion and last one *)
      apply inv_foldlM_rcons in Hcg.
      rewrite seq.foldl_rcons.
      destruct Hcg as (off_ιs & wt_ι & wt_ιs & wl_ι & wl_ιs & es_ι & es_ιs & Hinit & Hlast).
      destruct Hlast as (Hlast & -> & -> & ->).
      inv_cg_bind Hlast a0' wt_bs wt_b wl_bs wl_b es_bs es_b Hbs Hfb.
      subst.
      inv_cg_ret Hfb; subst.

      (* Use IH for first portion *)
      eapply IHιs in Hinit; auto.
      clear IHιs.
      destruct Hinit as (-> & -> & -> & Hinit).
      pose proof Hbs as Hbs'.
      clear_nils.
      (* use wp_store1 for the last one *)
      apply (wp_store1_mm_strong) in Hbs'.
      destruct Hbs' as (-> & -> & -> & Hbs_spec).

      do 3 (split; first auto).

      (* finally the iris proof... *)
      (* note that the overall structure is to do cwp_seq and use Hinit then Hbs_spec *)

      intros *; repeat iIntros "@".


      (* THE FOLLOWING SECTION IS A BUNCH OF LENGTHS STUFF and some breaking apart *)
      (* we know that length ιs = length os = length val_vs = length vs_idx
                            Harep         Hat           Hv
         so then we know vs_idx must be equal to some seq.rcons vs_idx v_idx. then zip seq.rcons?
       *)
      pose proof Harep as Hosslicing.
      eapply Forall2_rcons_inv_l in Hosslicing; try done. (* TODO move out of load *)
      rename os into os_big.
      destruct Hosslicing as (o & os & Ho & Hos & Hos_eq).
      subst os_big.
      rename val_vs into val_vs_big.
      iPoseProof (big_sepL2_rcons_inv_l with "[$Hat]") as
        "(%val_v & %val_vs & -> & Hoa & Hat)"; try done.
      rewrite <- rcons_app in Hv.
      pose proof Hv as Hvslicing.
      rewrite !rcons_app in Hv.
      eapply Forall2_rcons_inv_l in Hvslicing; try done.
      destruct Hvslicing as (valvstemp & valvtemp & Hlocsvalv & Hlocsvalvs & Hinv).
      apply seq.rcons_inj in Hinv; inversion Hinv; subst; clear Hinv.


      (* some manipulations that don't have to be before cwp_seq, but cleaner! *)
      (* split Hv *)
      (* Now we can cwp_seq.
       *)
      iApply (cwp_seq with "[Hf Hrun Hptr Haddr Htok HΦ Hat]"). {
        iApply (Hinit with "[$] [$] [$] [$] [//] [$] [//] [//]
                            [//] [//] [//] [] [//] [//] [//] [$] [-]").
        - iPureIntro.
          rewrite rcons_app in Hbound.
          rewrite sum_list_with_app in Hbound.
          lia.
        - iIntros "Hℓ Harrt Hrt".
          let Q := open_constr:(_ : iProp Σ) in
          instantiate (1 := (λ f'' vs'', ⌜f'' = f /\ vs'' = []⌝ ∗ Q)%I).
          cbn.
          iSplitR; first done.
          iAccu.
      }
      cbn.
      iIntros (f0 vs) "Hres Hf Hrun".
      iDestruct "Hres" as "((-> & ->) & HΦ & Hℓ_heap & Hℓ_addr & Hrt)".
      clear_nils.

      (* and now apply the hbs! *)
      iApply (Hbs_spec with "[$] [$] [$] [$] [//] [$] [//] [//]
                            [//] [//] [//] [] [//] [//] [//] [$] [-]").
      + iPureIntro.
        (* this will end up true due to Hbound and Hos *)
        rewrite rcons_app in Hbound.
        rewrite sum_list_with_app in Hbound.
        cbn in Hbound.
        rewrite seq_foldl_sum_list_with.
        rewrite update_path_words_size.
        2: {
          rewrite (has_arep_means_equal_lengths _ _ Hos).
          rewrite length_arep_flags_size.
          lia.
        }
        lia.
      + iIntros "Hℓ_heap Hℓ_addr Hrt".
        (* one last update_path_words manipulation *)
        assert (Hupdating: update_path_words off ws (concat (map serialize_atom (seq.rcons os o))) =
                  update_path_words
                        (seq.foldl (λ (off' : nat) (ι0 : atomic_rep), off' + arep_size ι0)
                           off ιs)
                        (update_path_words off ws (concat (map serialize_atom os)))
                        (serialize_atom o)
               ). {
          rewrite seq_foldl_sum_list_with.
          change map with @seq.map.
          rewrite seq.map_rcons.
          rewrite rcons_app.
          rewrite concat_app.
          cbn. clear_nils.
          change @seq.map with map.
          assert (length (concat (map serialize_atom os)) = sum_list_with arep_size ιs). {
            rewrite (has_arep_means_equal_lengths _ _ Hos).
            rewrite length_arep_flags_size.
            done.
          }
          rewrite <- H0.
          apply update_path_words_in_stages.
        }
        rewrite <- Hupdating.
        iApply ("HΦ" with "[$] [$] [$]").

  Qed.

  Lemma wp_store_strong_mm a_idx off ιs vs_idx wt wl ret wt' wl' es :
    length vs_idx = length ιs ->
    run_codegen (memory.store mr MemMM a_idx off vs_idx ιs) wt wl = inr (ret, wt', wl', es) ->
    ret = () /\ wt' = [] /\ wl' = [] /\
    ∀ f ℓ a a32 val_vs lmask θ os ws E B R Φ,
    ⊢ "Hf"       ∷ ↪[frame] f -∗
      "Hrun"     ∷ ↪[RUN] -∗
      "Hptr"     ∷ ℓ ↦heap ws -∗
      "Haddr"    ∷ ℓ ↦addr (MemMM, a) -∗
      "%Hℓmask"  ∷ ⌜¬ lmask ℓ⌝ -∗
      "Htok"     ∷ rt_token rti sr lmask θ -∗
      "%Ha32"    ∷ ⌜f_locs f !! localimm a_idx = Some (VAL_int32 a32)⌝ -∗
      "%Hv"      ∷ ⌜Forall2 (λ v_idx val_v, f_locs f !! localimm v_idx = Some val_v) vs_idx val_vs⌝ -∗
      "%Hrepa"   ∷ ⌜N_i32_repr (tag_address MemMM a) a32⌝ -∗
      "%Hmod"    ∷ ⌜(a `mod` 4 = 0)%N⌝ -∗
      "%Hnz"     ∷ ⌜(a ≠ 0)%N⌝ -∗
      "%Hbound"  ∷ ⌜off + sum_list_with arep_size ιs ≤ length ws⌝ -∗
      "%Harep"   ∷ ⌜Forall2 has_arep ιs os⌝ -∗
      (* "%Hsliceflags" ∷ ⌜Forall2 word_has_flag (concat (map arep_flags ιs)) (* this here will also have to change *) *)
      (*                                         (take (sum_list_with arep_size ιs) (drop off ws))⌝ -∗ *)
      "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemMM)⌝ -∗
      "%Hmemmm"  ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
      "Hat"      ∷ ([∗ list] o;val_v ∈ os;val_vs, atom_interp_weak θ MemMM o val_v) -∗
      "HΦ"       ∷ (ℓ ↦heap (update_path_words off ws (concat (map serialize_atom os))) -∗
                    ℓ ↦addr (MemMM, a) -∗
                    rt_token rti sr lmask θ -∗
                    Φ f []) -∗
    CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
    intros Hlen Hcg.
    unfold memory.store in Hcg.
    apply wp_ignore in Hcg.
    destruct Hcg as (-> & off' & Hcg).
    pose proof (wp_store_strong_mm_inner _ _ _ _ _ _ _ _ _ _ Hlen Hcg) as (-> & U & V & W).
    intuition.
  Qed.





(* -------------------- STORE STRONG GC ----------------------- *)



  Lemma wp_store1_gc_strong a_idx off ι v_idx wt wl ret wt' wl' es :
    run_codegen (store1 mr MemGC a_idx off v_idx ι) wt wl = inr (ret, wt', wl', es) ->
    ret = () /\ wt' = [] /\ wl' = [] /\
    ∀ f ℓ a a32 val_v lmask θ o ws E B R Φ,
    ⊢ "Hf"       ∷ ↪[frame] f -∗
      "Hrun"     ∷ ↪[RUN] -∗
      "Hptr"     ∷ ℓ ↦heap ws -∗
      "%Haddr"   ∷ ⌜ θ !! ℓ = Some (MemGC, a)⌝ -∗
      "%Hℓmask"  ∷ ⌜¬ lmask ℓ⌝ -∗
      "Htok"     ∷ rt_token rti sr lmask θ -∗
      "Hunreg"   ∷ instance_rt_func_interp (mr_func_unregisterroot mr) (sr_func_unregisterroot sr) (runtime.spec_unregisterroot rti sr) (f_inst f) -∗
      "Hown"     ∷ na_own logrel_nais E -∗
      "%Hmask"   ∷ ⌜↑ns_fun (N.of_nat (sr_func_unregisterroot sr)) ⊆ E⌝ -∗
      "%Ha32"    ∷ ⌜f_locs f !! localimm a_idx = Some (VAL_int32 a32)⌝ -∗
      "%Hv"      ∷ ⌜f_locs f !! localimm v_idx = Some val_v⌝ -∗
      "%Hrepa"   ∷ ⌜N_i32_repr (tag_address MemGC a) a32⌝ -∗
      "%Hmod"    ∷ ⌜(a `mod` 4 = 0)%N⌝ -∗
      "%Hnz"     ∷ ⌜(a ≠ 0)%N⌝ -∗
      "%Hbound"  ∷ ⌜off + arep_size ι ≤ length ws⌝ -∗
      "%Harep"   ∷ ⌜has_arep ι o⌝ -∗
      "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemMM)⌝ -∗
      "%Hrepgc"  ∷ ⌜N_nat_repr (sr_mem_gc sr) (rt_memaddr sr MemGC)⌝ -∗
      "%Hmemmm"  ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
      "%Hmemgc"  ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemGC = Some (sr_mem_gc sr)⌝ -∗
      "Hat"      ∷ atom_interp o val_v -∗ (* most likely to change *)
      "HΦ"       ∷ (ℓ ↦heap (update_path_words off ws (serialize_atom o)) -∗
                    na_own logrel_nais E -∗
                    instance_rt_func_interp (mr_func_unregisterroot mr) (sr_func_unregisterroot sr) (runtime.spec_unregisterroot rti sr) (f_inst f) -∗
                    rt_token rti sr lmask θ -∗
                    Φ f []) -∗
    CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
    intros Hcg.
    apply wp_store1_gc_state in Hcg as Hcgstate.
    destruct Hcgstate as (-> & -> & ->).
    do 3 (split; first done).

    unfold store1 in Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_a ?rest Ha Hcg.
    inv_cg_emit Ha; subst.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_v es_store_w Hv Hcg.
    inv_cg_emit Hv; subst.
    clear_nils.
    clear Hretval Hretval0.
    subst.

    (* now we need to do two locals -> values cwp conversions before we can
       use the ite_gc_ptr spec *)
    (* so, the iris proofs starts now *)
    intros *; repeat iIntros "@".
    rewrite app_assoc.
    iApply (cwp_seq with "[Hf Hrun]"). {
      iApply (cwp_seq with "[Hf Hrun]"). {
        iApply (cwp_local_get with "[] [$] [$]"); eauto.
        by instantiate (1 := λ f' v', (⌜f' = f⌝ ∗ ⌜v' = [VAL_int32 a32]⌝)%I).
      }
      iIntros (f' vs) "[-> ->] Hf Hr".

      iApply cwp_val_app; [by apply has_values_to_consts|].
      iApply (cwp_local_get with "[] [$] [$]"); eauto.
      instantiate (1 := λ f' v', (⌜f' = f⌝ ∗ ⌜v' = [VAL_int32 a32; val_v]⌝)%I).
      iModIntro.
      unfold fvs_combine; cbn.
      done.
    }
    iIntros (f' vs) "[-> ->] Hf Hr".

    (* ite gc ptr requires knowing if ι = PtrR or not *)
    destruct (atomic_rep_eq_dec ι PtrR).

    - (* ι = PtrR case *)
      subst ι.
      (* deconstructing val_v to use wp_ite_gc_ptr_ptr *)
      pose proof Harep as Harepsave.
      cbn in Harep.
      destruct o; try inversion Harep; clear Harep.
      (* NOTE: o = PtrA p *)
      (* this case is STORING PtrA p *)

      (* we need this to apply wp_ite_gc_ptr_ptr, but we otherwise only dig
         into atom_interp in the cases themselves *)
      iPoseProof (atom_interp_ptr_shaped_pure with "Hat") as
        "(%n & %n32 & %Nrepr & -> & %Hptrshaped)".
      (* NOTE: I'm not including the repr_ptr because that needs to be taken
          out with the root_pointer_interp in the future *)


      (* finally digging into the ite-gc! *)
      eapply wp_ite_gc_ptr_ptr with (evs:=to_consts [VAL_int32 a32; VAL_int32 n32])
                                    (vs:=[VAL_int32 a32; VAL_int32 n32]) in Hcg;
        [|by apply Is_true_true, has_values_to_consts| done | exact Hptrshaped | exact Nrepr].
      destruct Hcg as (?wt & ?wt & ?wt & ?wl & ?wl & ?wl & es1 & es2 & es3 & Hcompile).
      destruct Hcompile as (Hcg1 & Hcg2 & Hcg3 & Hwt7 & Hwl7 & Hes_store_w).
      clear_nils.

      (* given that hcg3 has a bunch more stuff to do, I'm going to apply Hes_store_w*)
      (* now *)
      iApply (Hes_store_w with "[$] [$] [//]").
      clear Hes_store_w.
      iIntros "!> Hf Hrun".

      (* now we destruct p! Ryan inverted ptr_shaped so we'll do that too *)
      inversion Hptrshaped; subst; last destruct μ eqn:?.
      + (* Hcg1 - Ptr Int - done with atom_interp *)
        apply wp_store_w in Hcg1 as (_ & -> & -> & Hcg1spec).

        (* Note: this happens so late because the MM case needs full rttoken *)
        iPoseProof (virt_to_phys_slice_store_acc_strong_gc rti sr lmask off (arep_size PtrR)
                     with "[//] [$Htok] [$Hptr] [//] [//]")
          as "(%hm & %Hhm & %Hdomθhm & %Hlocsθ_ws & Hnp &
          (%ns & %ns32 & %Hns & Hphys & Hwords) & Hclose)".

        (* we always heat hat inside *)
        iAssert (atom_interp_weak θ MemGC (PtrA (PtrInt n0)) (VAL_int32 n32))
          with "[]" as "Hat2". {
          cbn.
          iExists (2 * n0)%N, n32.
          iSplitR; [done| iSplitR; [done|]].
          iPureIntro.
          constructor.
        }
        (* I. didnd't have to eat Hat. What. It's still there.
          I guess bc it's all numbers it's fine. Rest of proof continues as normal *)

        iPoseProof (atom_to_words_gc θ PtrR _ _ Harepsave with "[$Hat2]") as
          "(%ns_new & %ns32_new & %Hns_new & %Hbits & %Htypes & Hwords_new)".

        (* Extract pure facts from Hnp, derive dom θ cond for new words, then reconstruct Hnp *)
        iDestruct "Hnp" as "(Haddr_auth & %rm & %lm & Hroot & Hlayout & Hrti & %Hinj & %Hrootok & Hrootmem & %Hheapok)".
        iPoseProof (words_interp_locs_dom_θ θ rm MemGC _ _ Hrootok with "[$Hwords_new] [$] [$]")
          as "%Hlocsθ_new".
        iAssert (rt_token_nophys rti sr lmask θ hm) with "[Hroot Hlayout Hrti Hrootmem Haddr_auth]" as "Hnp".
        { iFrame. iPureIntro. split; last split; done. }

        specialize (Hcg1spec a a32).
        specialize (Hcg1spec (sr_mem_gc sr) (rt_memaddr sr MemGC)).
        specialize Hcg1spec with (v:=(VAL_int32 n32)).
        specialize Hcg1spec with (bs:=(flat_map serialise_i32 ns32)).
        (* I need a pure fact about the length of ns and ns32 here *)
        iPoseProof (big_sepL2_length with "[$Hwords]") as "%Hlenns".
        pose proof (Forall2_length _ _ _ Hns) as Hnslen.
        assert (Hlendrop: 1 ≤ length (drop off ws)). {
          rewrite length_drop.
          cbn in Hbound.
          lia.
        }
        rewrite length_take_le in Hlenns; try done.
        rewrite <- Hlenns in Hnslen.
        change 1 with (arep_size PtrR) in Hnslen.
        cbn in Hnslen.

        iApply cwp_fupd. (* necessary for a later iMod *)
        iApply (Hcg1spec with "[$] [$] [$] [-]"); try done; try (cbn; done). {
          cbn.
          rewrite len_ser32.
          destruct ns32 as [|nn32 ns32]; try inversion Hnslen.
          destruct ns32; try inversion H0.
          cbn.
          done.
        }
        iIntros "!> Haddr".

        (* we need to use Hclose now! We have a bunch of tiny facts we need to do so *)
        cbn [bits].
        assert (serialise_i32 n32 = flat_map serialise_i32 [n32]) by done.
        rewrite H.
        iSpecialize ("Hclose" $! (serialize_atom (PtrA (PtrInt n0))) [(2 * n0)%N] [n32]).
        iSpecialize ("Hclose" with "[//] [%] [%] [%] [$]").
        * constructor; done.
        (* * intros flags H2. *)
        (*   eapply update_path_words_flags_compat; [exact Harepsave|done|done|done]. *)
        * eapply Forall_impl.
          -- exact (update_path_words_locs_incl (dom θ) ws off _ Hlocsθ_ws Hlocsθ_new).
          -- intros ℓ' Hℓ'. rewrite <- Hdomθhm. exact Hℓ'.
        * eapply update_path_words_locs_incl; try done.
        * iAssert (⌜ns_new = [(2 * n0)%N]⌝%I) with "[Hwords_new]" as "->". {
            cbn.
            iPoseProof (big_sepL2_length with "[$Hwords_new]") as "%lenn".
            destruct ns_new as [|nn nrest]; inversion lenn.
            destruct nrest; inversion H1; clear H1.
            cbn.
            iDestruct "Hwords_new" as "(%Hrepr2 & _)".
            inversion Hrepr2; subst.
            done.
          }
          iSpecialize ("Hclose" with "[$Hwords_new] [$Hnp]").
          iMod "Hclose".
          iModIntro.
          iDestruct "Hclose" as "[pls hlp]".
          iApply ("HΦ" with "[$] [$] [$] [$]").
      + (* Hcg2 - Ptr MM *)
        apply wp_store_w in Hcg2 as (_ & -> & -> & Hcg2spec).
        (* start with unfolding atom_interp a bit *)
        iEval (cbn) in "Hat".
        iDestruct "Hat" as "(%n' & %n32' & %forinv & %toinv & Hrp)".
        inversion toinv; subst n32'; clear toinv.
        pose proof (N_i32_repr_inj _ _ _ forinv Nrepr) as ->; clear forinv.
        iDestruct "Hrp" as "(%rp & %Hreprroot & Haddr_ℓ0)".

        inversion Hreprroot. {
          exfalso.
          apply N.Div0.mod_divides in H as [c ->].
          lia.
        }
        iEval (cbn) in "Haddr_ℓ0".
        destruct μ0; try done.
        subst rp.
        assert (a1 = a0). {
          cbn in H1.
          assert (4 <= a1)%N by (by eapply mod_bound_nonzero).
          assert (4 <= a0)%N by (by eapply mod_bound_nonzero).
          lia.
        }
        subst a1.

        (* This here is what needs the full rt token!! *)
        iAssert (⌜θ !! ℓ0 = Some (MemMM, a0)⌝%I) with "[Haddr_ℓ0 Htok]" as "%Hθℓ0". {
          open_rt "Htok".
          by iPoseProof (ghost_map_lookup with "[$Haddr] [$]") as "%Hθℓ".
        }

        (* we can not break the token up again *)
        iPoseProof (virt_to_phys_slice_store_acc_strong_gc rti sr lmask off (arep_size PtrR)
                     with "[//] [$Htok] [$Hptr] [//] [//]")
          as "(%hm & %Hhm & %Hdomθhm & %Hlocsθ_ws & Hnp &
          (%ns & %ns32 & %Hns & Hphys & Hwords) & Hclose)".

        (* make an atom_interp_weak *)
        iAssert (atom_interp_weak θ MemGC (PtrA (PtrHeap MemMM ℓ0)) (VAL_int32 n32))
          with "[Haddr_ℓ0]" as "Hat2". {
          cbn.
          iExists (tag_address MemMM a0)%N, n32.
          iSplitR; [done| iSplitR; [done|]].
          iExists a0.
          iFrame.
          iPureIntro.
          constructor; try done.
        }

        iPoseProof (atom_to_words_gc θ PtrR _ _ Harepsave with "[$Hat2]") as
          "(%ns_new & %ns32_new & %Hns_new & %Hbits & %Htypes & Hwords_new)".

        (* Extract pure facts from Hnp, derive dom θ cond for new words, then reconstruct Hnp *)
        iDestruct "Hnp" as "(Haddr_auth & %rm & %lm & Hroot & Hlayout & Hrti & %Hinj & %Hrootok & Hrootmem & %Hheapok)".
        iPoseProof (words_interp_locs_dom_θ θ rm MemGC _ _ Hrootok with "[$Hwords_new] [$Hroot] [$]")
          as "%Hlocsθ_new".
        iAssert (rt_token_nophys rti sr lmask θ hm) with "[Hroot Hlayout Hrti Hrootmem Haddr_auth]" as "Hnp".
        { by iFrame. }

        specialize (Hcg2spec a a32).
        specialize (Hcg2spec (sr_mem_gc sr) (rt_memaddr sr MemGC)).
        specialize Hcg2spec with (v:=(VAL_int32 n32)).
        specialize Hcg2spec with (bs:=(flat_map serialise_i32 ns32)).
        (* I need a pure fact about the length of ns and ns32 here *)
        iPoseProof (big_sepL2_length with "[$Hwords]") as "%Hlenns".
        pose proof (Forall2_length _ _ _ Hns) as Hnslen.
        assert (Hlendrop: 1 ≤ length (drop off ws)). {
          rewrite length_drop.
          cbn in Hbound.
          lia.
        }
        rewrite length_take_le in Hlenns; try done.
        rewrite <- Hlenns in Hnslen.
        change 1 with (arep_size PtrR) in Hnslen.
        cbn in Hnslen.

        iApply cwp_fupd. (* necessary for a later iMod *)
        iApply (Hcg2spec with "[$] [$] [$] [-]"); try done; try (cbn; done). {
          cbn.
          rewrite len_ser32.
          destruct ns32 as [|nn32 ns32]; try inversion Hnslen.
          destruct ns32; try inversion H5.
          cbn.
          done.
        }
        iIntros "!> Haddr".

        (* we need to use Hclose now! We have a bunch of tiny facts we need to do so *)

        iPoseProof (big_sepL2_length with "[$Hwords_new]") as "%Hlenns_new".
        cbn in Hlenns_new.
        destruct ns_new as [| n_new ns_new]; try inversion Hlenns_new.
        destruct ns_new; inversion H5; subst; clear H5.
        pose proof (Forall2_length _ _ _ Hns_new) as Hnslen_new.
        cbn in Hnslen_new.
        destruct ns32_new as [| n32_new ns32_new]; try inversion Hnslen_new.
        destruct ns32_new; inversion H5; subst; clear H5.
        clear Hlenns_new Hnslen_new.

        rewrite <- Hbits.
        cbn [bits].
        assert (serialise_i32 n32_new = flat_map serialise_i32 [n32_new]) by done.
        rewrite <- H3.

        iSpecialize ("Hclose" $! (serialize_atom (PtrA (PtrHeap MemMM ℓ0)))
                                    [n_new] [n32_new]).
        iSpecialize ("Hclose" with "[//] [%] [%] [%] [$]").
        * done.
        (* * intros flags H5. *)
        (*   eapply update_path_words_flags_compat; [exact Harepsave|done|done|done]. *)
        * eapply Forall_impl.
          -- exact (update_path_words_locs_incl (dom θ) ws off _ Hlocsθ_ws Hlocsθ_new).
          -- intros ℓ' Hℓ'. rewrite <- Hdomθhm. exact Hℓ'.
        * eapply update_path_words_locs_incl; try done.
        * iSpecialize ("Hclose" with "[$Hwords_new] [$Hnp]").
          iMod "Hclose".
          iModIntro.
          iDestruct "Hclose" as "[pls hlp]".
          iApply ("HΦ" with "[$] [$] [$] [$]").
      + (* Hcg3 - Ptr GC *)
        inv_cg_bind Hcg3 [] ?wt ?wt ?wl ?wl es_loadroot ?rest Hloadroot Hcg3.
        clear es_store_w.
        inv_cg_bind Hcg3 [] ?wt ?wt ?wl ?wl es_store_w ?rest Hstore Hcg3.
        inv_cg_bind Hcg3 [] ?wt ?wt ?wl ?wl es_loc es_unregister Hloc Hunregister.
        inv_cg_emit Hloc; subst.
        clear_nils; clear Hretval.

        (* stuff to do before doing starting to deal with cwp stuff*)
        (* note:  *)
        iEval (cbn) in "Hat".
        iDestruct "Hat" as "(%n' & %n32' & %forinv & %toinv & Hrp)".
        inversion toinv; subst n32'; clear toinv.
        pose proof (N_i32_repr_inj _ _ _ forinv Nrepr) as ->; clear forinv.
        iDestruct "Hrp" as "(%rp & %Hreprroot & Hroot_ℓ0)".
        inversion Hreprroot. {
          exfalso.
          apply N.Div0.mod_divides in H as [c ->].
          lia.
        }
        iEval (cbn) in "Hroot_ℓ0".
        destruct μ; try done.
        subst rp.
        assert (a1 = a0). {
          cbn in H1.
          lia.
        }
        subst a1.

        iPoseProof (virt_to_phys_slice_store_acc_strong_gc rti sr lmask off (arep_size PtrR)
                     with "[//] [$Htok] [$Hptr] [//] [//]")
          as "(%hm & %Hhm & %Hdomθhm & %Hlocsθ_ws & Hnp &
          (%ns & %ns32 & %Hns & Hphys & Hwords) & Hclose)".

        (* for myself: we are STORING PtrA PtrHeap MemGC ℓ0 *)

        (* ------ LOAD ROOT ------- *)
        apply (wp_loadroot sr) in Hloadroot as (_ & -> & -> & Hloadroot_spec).
        rewrite app_assoc.

        (* break apart rt token *)
        iDestruct "Hnp" as "(Haddr_auth & %rm & %lm & Hroot & Hlayout & Hrti & %Hinj & %Hrootok & Hrootmem & %Hheapok)".

        iApply (cwp_seq with "[Hf Hrun Hroot_ℓ0 Hrootmem Hroot]"). {
          (* to isolate load_root, first a val_app *)
          change (to_consts [?x; ?y]) with ((to_consts [x]) ++ to_consts [y]).
          rewrite <- app_assoc.
          iApply cwp_val_app; first apply has_values_to_consts.

          iApply (Hloadroot_spec with "[$] [$] [] [$] [$] [$]");
            [exact Nrepr|by apply Is_true_true, has_values_to_consts|
             exact Hreprroot| exact Hrootok | iPureIntro; exact Hmemgc | ].
          iNext.
          iIntros (ah ah32) "Hreprah Hreprptr Hroot_ℓ0 Hroot Hrootmem".

          let Q := open_constr:(_ : iProp Σ) in
          instantiate (1 :=
            (λ f'' vs'', ∃ ah ah32,
              ⌜f'' = f /\ vs'' = [VAL_int32 a32; VAL_int32 ah32]⌝ ∗ ⌜N_i32_repr ah ah32⌝
                                  ∗ ⌜repr_pointer θ (PtrHeap MemGC ℓ0) ah⌝ ∗ Q)%I).
          unfold fvs_combine; cbn.
          iExists ah, ah32.
          iSplitR; first done.
          iFrame.
          iAccu.
        }

        iIntros (f' vs') "Hres Hf Hrun".
        iDestruct "Hres" as "(%ah & %ah32 & (-> & ->)
          & %Hrepr_ah & %Hrepr_ptr & Hroot_ℓ0 & Hroot & Hrootmem)".
        iAssert (rt_token_nophys rti sr lmask θ hm) with "[Hroot Hlayout Hrti Hrootmem Haddr_auth]" as "Hnp".
        { by iFrame. }
        clear dependent rm. clear dependent lm. clear Hinj.

        (* we are past loadroot!! *)
        clear Hloadroot_spec.

        (* ------ STORE W ------- *)
        apply wp_store_w in Hstore as (_ & -> & -> & Hcg3spec).

        (* this is where we finally need words interp. We get this through
           asserting atom_interp_weak *)
        iAssert (atom_interp_weak θ MemGC (PtrA (PtrHeap MemGC ℓ0)) (VAL_int32 ah32))
          with "[]" as "Hat". {
          cbn.
          iExists ah, ah32.
          done.
        }

        iPoseProof (atom_to_words_gc θ PtrR _ _ Harepsave with "[$Hat]") as
          "(%ns_new & %ns32_new & %Hns_new & %Hbits & %Htypes & Hwords_new)".

        (* Extract pure facts from Hnp, derive dom θ cond for new words, then reconstruct Hnp *)
        iDestruct "Hnp" as "(Haddr_auth & %rm & %lm & Hroot & Hlayout & Hrti & %Hinj & %Hrootok & Hrootmem & %Hheapok)".
        iPoseProof (words_interp_locs_dom_θ θ rm MemGC _ _ Hrootok with "[$Hwords_new] [$Hroot] [$]")
          as "%Hlocsθ_new".
        iAssert (rt_token_nophys rti sr lmask θ hm) with "[Hroot Hlayout Hrti Hrootmem Haddr_auth]" as "Hnp".
        { by iFrame. }
        clear dependent rm; clear dependent lm; clear Hinj.
        move Hcg3spec at bottom.

        (* alright we need to spec again. I'm so suspicious *)
        (* like we needed to do loadroot before we could get atom_interp_weak so
           that's good*)
        (* but where is a0 ↦root ℓ0 gonna go... *)
        rewrite app_assoc.
        iPoseProof (big_sepL2_length with "[$Hwords]") as "%Hlenns".
        pose proof (Forall2_length _ _ _ Hns) as Hnslen.
        assert (Hlendrop: 1 ≤ length (drop off ws)). {
          rewrite length_drop.
          cbn in Hbound.
          lia.
        }
        rewrite length_take_le in Hlenns; try done.
        rewrite <- Hlenns in Hnslen.
        change 1 with (arep_size PtrR) in Hnslen.
        cbn in Hnslen.

        (* iApply cwp_fupd.  *)
        iApply (cwp_seq with "[Hf Hrun Hphys]"). {
          iApply (Hcg3spec with "[$] [$] [$]"); try done. {
            cbn.
            rewrite len_ser32.
            destruct ns32 as [|nn32 ns32]; try inversion Hnslen.
            destruct ns32; try inversion H5.
            cbn.
            done.
          }
          iNext.
          iIntros "Hphys".

          (* let Q := open_constr:(_ : iProp Σ) in *)
          instantiate (1 := (λ f'' vs'',
                ⌜f'' = f /\ vs'' = []⌝ ∗
                rt_memaddr sr MemGC↦[wms][a + 4 * N.of_nat off]bits (VAL_int32 ah32))%I).
          iEval (cbn).
          iSplitR; first done.
          iClear "Hat Hwords_new".
          iFrame.
        }
        iIntros (f0 vs0) "Hres Hf Hrun".
        iDestruct "Hres" as "((-> & ->) & Hphys)".
        clear_nils.

        (* ------ GET LOCAL ------- *)
        iApply (cwp_seq with "[Hf Hrun]").
        {
          iClear "Hat Hwords_new". (* else the eauto doesn't work lol *)
          iApply (cwp_local_get with "[] [$] [$]"); eauto.
          now instantiate (1:= λ f' v', ⌜f' = f ∧ v' = [VAL_int32 n32]⌝%I).
        }
        iIntros (f' vs') "[-> ->] Hf Hrun".

        (* ------ UNREGISTER ROOT ------ *)
        apply (wp_unregisterroot rti sr) in Hunregister as (_ & -> & -> & Hunreg_spec).
        move Hunreg_spec at bottom.

        (* use Hclose now to get rt token *)
        iPoseProof (big_sepL2_length with "[$Hwords_new]") as "%Hlenns_new".
        cbn in Hlenns_new.
        destruct ns_new as [| n_new ns_new]; try inversion Hlenns_new.
        destruct ns_new; inversion H5; subst; clear H5.
        pose proof (Forall2_length _ _ _ Hns_new) as Hnslen_new.
        cbn in Hnslen_new.
        destruct ns32_new as [| n32_new ns32_new]; try inversion Hnslen_new.
        destruct ns32_new; inversion H5; subst; clear H5.
        clear Hlenns_new Hnslen_new.



        iSpecialize ("Hclose" $! ((serialize_atom (PtrA (PtrHeap MemGC ℓ0))))).
        iSpecialize ("Hclose" $! [n_new] [n32_new]).

        rewrite Hbits.

        iApply fupd_cwp.
        iMod ("Hclose" with "[//] [//] [%] [%] [$] [$] [$]") as "(Hℓ_heap & Hrt)".
        (* { intros flags H3. *)
        (*   eapply update_path_words_flags_compat; [exact Harepsave|done|done|done]. } *)
        { eapply Forall_impl.
          -- exact (update_path_words_locs_incl (dom θ) ws off _ Hlocsθ_ws Hlocsθ_new).
          -- intros ℓ' Hℓ'. rewrite <- Hdomθhm. exact Hℓ'. }
        { eapply update_path_words_locs_incl; try done. }
        iModIntro.

        (* finally, unreg spec! *)
        iApply (Hunreg_spec with "[$] [HΦ Hℓ_heap Hwords] [$] [$] [//] [$] [$] [$]");
          [ | | apply Is_true_true, has_values_to_consts | ]; try done.
        iIntros "Hrt Hown Hinstance".
        iApply ("HΦ" with "[$] [$] [$] [$]").
    - (* ι <> PtrR case *)
      eapply wp_ite_gc_ptr_nonptr in Hcg; last assumption.
      apply wp_store_w in Hcg as (_ & _ & _ & Hcgspec).


      iPoseProof (virt_to_phys_slice_store_acc_strong_gc rti sr lmask off (arep_size ι)
                   with "[//] [$Htok] [$Hptr] [//] [//]")
        as "(%hm & %Hhm & %Hdomθhm & %Hlocsθ_ws & Hnp &
          (%ns & %ns32 & %Hns & Hphys & Hwords) & Hclose)".

      iPoseProof ((atom_interp_to_weak_memGC_nonptr o val_v ι θ Harep n) with "[$Hat]") as "Hat".

      iPoseProof (atom_to_words_gc θ ι _ _ Harep with "[$Hat]") as
        "(%ns_new & %ns32_new & %Hns_new & %Hbits & %Htypes & Hwords_new)".

      (* Extract pure facts from Hnp, derive dom θ cond for new words, then reconstruct Hnp *)
      iDestruct "Hnp" as "(Haddr_auth & %rm & %lm & Hroot & Hlayout & Hrti & %Hinj & %Hrootok & Hrootmem & %Hheapok)".
      iPoseProof (words_interp_locs_dom_θ θ rm MemGC _ _ Hrootok with "[$Hwords_new] [$Hroot] [$Haddr_auth]")
        as "%Hlocsθ_new".
      iAssert (rt_token_nophys rti sr lmask θ hm) with "[Hroot Hlayout Hrti Hrootmem Haddr_auth]" as "Hnp".
      { by iFrame. }
      clear dependent rm; clear dependent lm; clear Hinj.

      move Hcgspec at bottom.
      specialize (Hcgspec a a32).
      specialize (Hcgspec (sr_mem_gc sr) (rt_memaddr sr MemGC)).
      specialize Hcgspec with (v:=val_v).
      specialize Hcgspec with (bs:=(flat_map serialise_i32 ns32)).
      (* I need a pure fact about the length of ns and ns32 here *)
      iPoseProof (big_sepL2_length with "[$Hwords]") as "%Hlenns".
      pose proof (Forall2_length _ _ _ Hns) as Hnslen.
      assert (Hlendrop: (arep_size ι) ≤ length (drop off ws)). {
        rewrite length_drop.
        lia.
      }
      rewrite length_take_le in Hlenns; try done.
      rewrite <- Hlenns in Hnslen.

      iApply cwp_fupd. (* necessary for a later iMod *)
      iApply (Hcgspec with "[$] [$] [$] [-]"); try done; try (cbn; done). {
        cbn.
        rewrite len_ser32.
        rewrite length_t_translate_arep.
        assert (length (arep_flags ι) = arep_size ι) by (destruct ι; done).
        lia.
      }
      iIntros "!> Haddr".

      (* we need to use Hclose now! We have a bunch of tiny facts we need to do so *)
      rewrite <- Hbits.
      iSpecialize ("Hclose" $! (serialize_atom o) ns_new ns32_new).
      iSpecialize ("Hclose" with "[%] [//] [%] [%] [$]").
      * by apply has_arep_size.
      * eapply Forall_impl.
        -- exact (update_path_words_locs_incl (dom θ) ws off _ Hlocsθ_ws Hlocsθ_new).
        -- intros ℓ' Hℓ'. rewrite <- Hdomθhm. exact Hℓ'.
      * eapply update_path_words_locs_incl; try done.
      * iSpecialize ("Hclose" with "[$Hwords_new] [$Hnp]").
        iMod "Hclose".
        iModIntro.
        iDestruct "Hclose" as "[pls hlp]".
        iApply ("HΦ" with "[$] [$] [$] [$]").
  Qed.

  Lemma wp_store_strong_gc_inner a_idx ιs:
    ∀ off vs_idx wt wl ret wt' wl' es,
    length vs_idx = length ιs ->
    run_codegen (foldlM
         (λ (off : nat) '(v, ι),
            store1 mr MemGC a_idx off v ι ≫= λ _ : (), Monad.ret (off + arep_size ι))
         off (zip vs_idx ιs)) wt wl = inr (ret, wt', wl', es) ->
    ret = seq.foldl (λ off' ι, off' + arep_size ι) off ιs /\
    wt' = [] /\ wl' = [] /\
    ∀ f ℓ a a32 val_vs lmask θ os ws E B R Φ,
    ⊢ "Hf"       ∷ ↪[frame] f -∗
      "Hrun"     ∷ ↪[RUN] -∗
      "Hptr"     ∷ ℓ ↦heap ws -∗
      "%Haddr"   ∷ ⌜ θ !! ℓ = Some (MemGC, a)⌝ -∗
      "%Hℓmask"  ∷ ⌜¬ lmask ℓ⌝ -∗
      "Htok"     ∷ rt_token rti sr lmask θ -∗
      "Hunreg"   ∷ instance_rt_func_interp (mr_func_unregisterroot mr) (sr_func_unregisterroot sr) (runtime.spec_unregisterroot rti sr) (f_inst f) -∗
      "Hown"     ∷ na_own logrel_nais E -∗
      "%Hmask"   ∷ ⌜↑ns_fun (N.of_nat (sr_func_unregisterroot sr)) ⊆ E⌝ -∗
      "%Ha32"    ∷ ⌜f_locs f !! localimm a_idx = Some (VAL_int32 a32)⌝ -∗
      "%Hv"      ∷ ⌜Forall2 (λ v_idx val_v, f_locs f !! localimm v_idx = Some val_v) vs_idx val_vs⌝ -∗
      "%Hrepa"   ∷ ⌜N_i32_repr (tag_address MemGC a) a32⌝ -∗
      "%Hmod"    ∷ ⌜(a `mod` 4 = 0)%N⌝ -∗
      "%Hnz"     ∷ ⌜(a ≠ 0)%N⌝ -∗
      "%Hbound"  ∷ ⌜off + sum_list_with arep_size ιs ≤ length ws⌝ -∗
      "%Harep"   ∷ ⌜Forall2 has_arep ιs os⌝ -∗
      (* "%Hsliceflags" ∷ ⌜Forall2 word_has_flag (concat (map arep_flags ιs)) *)
      (*                                          (take (sum_list_with arep_size ιs) (drop off ws))⌝ -∗ *)
      "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemMM)⌝ -∗
      "%Hrepgc"  ∷ ⌜N_nat_repr (sr_mem_gc sr) (rt_memaddr sr MemGC)⌝ -∗
      "%Hmemmm"  ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
      "%Hmemgc"  ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemGC = Some (sr_mem_gc sr)⌝ -∗
      "Hat"      ∷ atoms_interp os val_vs -∗
      "HΦ"       ∷ (ℓ ↦heap (update_path_words off ws (concat (map serialize_atom os))) -∗
                    na_own logrel_nais E -∗
                    instance_rt_func_interp (mr_func_unregisterroot mr) (sr_func_unregisterroot sr) (runtime.spec_unregisterroot rti sr) (f_inst f) -∗
                    rt_token rti sr lmask θ -∗
                    Φ f []) -∗
    CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
    induction ιs as [| ιs ι] using seq.last_ind; intros * Hlen Hcg *.
    - assert (zip vs_idx ([]:list atomic_rep) = []) by (by apply zip_nil_r).
      rewrite H in Hcg.
      cbn in Hcg.
      inversion Hcg; subst.
      do 3 split; try done.
      intros *; repeat iIntros "@".
      iApply (cwp_nil with "[$] [$]").
      (* os is nil, val_vs is nil, and ws didn't update *)
      inversion Harep; subst.
      iPoseProof (big_sepL2_nil_inv_l with "[$Hat]") as "%Hvalvslen". subst.
      assert (update_path_words ret ws (concat (map serialize_atom [])) = ws). {
        cbn.
        apply update_path_words_empty_2.
      }
      rewrite H0.
      iApply ("HΦ" with "[$] [$] [$] [$]").
    - (* to start with, we need to make
         (zip vs_idx (seq.rcons ιs ι)) = seq.rcons (zip vs_idx_small ιs) (v_idx, ι) *)
      (* we know that length ιs = length os = length val_vs = length vs_idx
                            Harep         Hat           Hv
         so then we know vs_idx must be equal to some seq.rcons vs_idx v_idx. then zip seq.rcons?
         I think that should work, but that's not interesting right at this moment so asserting
       *)
      rename vs_idx into vs_idx_big.
      assert (∃ vs_idx v_idx, vs_idx_big = seq.rcons vs_idx v_idx /\ length vs_idx = length ιs). {
        rewrite rcons_app in Hlen.
        rewrite length_app in Hlen.
        cbn in Hlen.
        apply length_split in Hlen as (vs_idx & v_idxT & -> & hlen1 & hlen2).
        destruct v_idxT as [|v_idx rest]; [inversion hlen2|].
        destruct rest; [|inversion hlen2].
        exists vs_idx, v_idx.
        rewrite rcons_app.
        done.
      }
      destruct H as (vs_idx & v_idx & -> & Hleminis).

      assert (zip (seq.rcons vs_idx v_idx) (seq.rcons ιs ι) =
                seq.rcons (zip vs_idx ιs) (v_idx, ι)). {
        by apply zip_rcons.
      }
      rewrite H in Hcg.

      apply inv_foldlM_rcons in Hcg.
      rewrite seq.foldl_rcons.
      destruct Hcg as (off_ιs & wt_ι & wt_ιs & wl_ι & wl_ιs & es_ι & es_ιs & Hinit & Hlast).
      destruct Hlast as (Hlast & -> & -> & ->).
      inv_cg_bind Hlast a0' wt_bs wt_b wl_bs wl_b es_bs es_b Hbs Hfb.
      subst.
      inv_cg_ret Hfb; subst.
      eapply IHιs in Hinit; auto.
      clear IHιs.

      destruct Hinit as (-> & -> & -> & Hinit).
      pose proof Hbs as Hbs'.
      clear_nils.

      apply (wp_store1_gc_strong) in Hbs'.
      destruct Hbs' as (-> & -> & -> & Hbs_spec).

      do 3 (split; first by auto).

      (* finally the iris proof... *)
      (* note that the overall structure is to do cwp_seq and use Hinit then Hbs_spec *)
      intros *; repeat iIntros "@".

      (* the thing we need to do before cwp_seq is split up Hat into the Hinit part and the
         Hbs part. This involves showing os = seq.rcons os o and val_vs = seq.rcons os o *)
      pose proof Harep as Hosslicing.
      eapply Forall2_rcons_inv_l in Hosslicing; try done.
      rename os into os_big.
      destruct Hosslicing as (o & os & Ho & Hos & Hos_eq).
      subst os_big.
      rename val_vs into val_vs_big.
      unfold atoms_interp.
      Opaque atom_interp. cbn.
      iPoseProof (big_sepL2_rcons_inv_l with "[$Hat]") as
        "(%val_v & %val_vs & -> & Hoa & Hat)"; try done.
      Transparent atom_interp.
      (* rewrite <- rcons_app in Hv. *)
      pose proof Hv as Hvslicing.
      rewrite !rcons_app in Hv.
      eapply Forall2_rcons_inv_l in Hvslicing; try done.
      destruct Hvslicing as (valvstemp & valvtemp & Hlocsvalv & Hlocsvalvs & Hinv).
      apply seq.rcons_inj in Hinv; inversion Hinv; subst; clear Hinv.

      (* the new one is hslice flags *)
      (* rewrite !rcons_app in Hsliceflags. *)
      (* rewrite map_app in Hsliceflags. *)
      (* rewrite sum_list_with_app in Hsliceflags. *)
      (* rewrite concat_app in Hsliceflags. *)

      (* I need this both for split_word_has_flag_arep and the Hinit! *)
      assert (Hlensmall: off + sum_list_with arep_size ιs ≤ length ws). {
          rewrite rcons_app in Hbound.
          rewrite sum_list_with_app in Hbound.
          lia.
      }
      (* apply (split_word_has_flag_arep _ _ _ _ os Hlensmall Hos) in Hsliceflags as htemp. *)
      (* destruct htemp as [Hflagsιs Hflagsι]. *)
      (* put some more in here but for now this is enough lol *)

      (* Now we can cwp_seq. Note lots of pure Forall/rcons manipulations happen inside
         that might be better brought outside (we'll see).
       *)
      iApply (cwp_seq with "[Hf Hrun Hptr Htok HΦ Hat Hunreg Hown]"). {
        iApply (Hinit with "[$] [$] [$] [//] [//] [$] [$] [$] [//] [//] [//]
                            [//] [//] [//] [//] [//] [//] [//] [//] [//] [$] [-]").
        iIntros "Hℓ Hown Hunreg Hrt".
        let Q := open_constr:(_ : iProp Σ) in
        instantiate (1 := (λ f'' vs'', ⌜f'' = f /\ vs'' = []⌝ ∗ Q)%I).
        cbn.
        iSplitR; first done.
        iAccu.
      }
      cbn.
      iIntros (f0 vs) "Hres Hf Hrun".
      iDestruct "Hres" as "((-> & ->) & HΦ & Hℓ_heap & Hown & Hunreg & Hrt)".
      clear_nils.

      (* and now apply the hbs! *)
      iApply (Hbs_spec with "[$] [$] [$] [//] [//] [$] [$] [$] [//] [//] [//]
                            [//] [//] [//] [] [//] [//] [//] [//] [//] [$Hoa] [-]").
      + iPureIntro.
        (* this will end up true due to Hbound and Hos *)
        rewrite rcons_app in Hbound.
        rewrite sum_list_with_app in Hbound.
        cbn in Hbound.
        rewrite seq_foldl_sum_list_with.
        rewrite update_path_words_size.
        2: {
          rewrite (has_arep_means_equal_lengths _ _ Hos).
          rewrite length_arep_flags_size.
          lia.
        }
        lia.

      + iIntros "Hℓ_heap Hown Hunreg Hrt".
        (* one last update_path_words manipulation *)
        assert (update_path_words off ws (concat (map serialize_atom (seq.rcons os o))) =
                  update_path_words
                        (seq.foldl (λ (off' : nat) (ι0 : atomic_rep), off' + arep_size ι0)
                           off ιs)
                        (update_path_words off ws (concat (map serialize_atom os)))
                        (serialize_atom o)
               ). {
          rewrite seq_foldl_sum_list_with.
          change map with @seq.map.
          rewrite seq.map_rcons.
          rewrite rcons_app.
          rewrite concat_app.
          cbn. clear_nils.
          change @seq.map with map.
          assert (length (concat (map serialize_atom os)) = sum_list_with arep_size ιs). {
            rewrite (has_arep_means_equal_lengths _ _ Hos).
            rewrite length_arep_flags_size.
            done.
          }
          rewrite <- H0.
          apply update_path_words_in_stages.
        }
        rewrite <- H0.
        iApply ("HΦ" with "[$] [$] [$] [$]").

  Qed.

  Lemma wp_store_strong_gc a_idx off ιs vs_idx wt wl ret wt' wl' es :
    length vs_idx = length ιs ->
    run_codegen (memory.store mr MemGC a_idx off vs_idx ιs) wt wl = inr (ret, wt', wl', es) ->
    ret = () /\ wt' = [] /\ wl' = [] /\
    ∀ f ℓ a a32 val_vs lmask θ os ws E B R Φ,
    ⊢ "Hf"       ∷ ↪[frame] f -∗
      "Hrun"     ∷ ↪[RUN] -∗
      "Hptr"     ∷ ℓ ↦heap ws -∗
      "%Haddr"   ∷ ⌜ θ !! ℓ = Some (MemGC, a)⌝ -∗
      "%Hℓmask"  ∷ ⌜¬ lmask ℓ⌝ -∗
      "Htok"     ∷ rt_token rti sr lmask θ -∗
      "Hunreg"   ∷ instance_rt_func_interp (mr_func_unregisterroot mr) (sr_func_unregisterroot sr) (runtime.spec_unregisterroot rti sr) (f_inst f) -∗
      "Hown"     ∷ na_own logrel_nais E -∗
      "%Hmask"   ∷ ⌜↑ns_fun (N.of_nat (sr_func_unregisterroot sr)) ⊆ E⌝ -∗
      "%Ha32"    ∷ ⌜f_locs f !! localimm a_idx = Some (VAL_int32 a32)⌝ -∗
      "%Hv"      ∷ ⌜Forall2 (λ v_idx val_v, f_locs f !! localimm v_idx = Some val_v) vs_idx val_vs⌝ -∗
      "%Hrepa"   ∷ ⌜N_i32_repr (tag_address MemGC a) a32⌝ -∗
      "%Hmod"    ∷ ⌜(a `mod` 4 = 0)%N⌝ -∗
      "%Hnz"     ∷ ⌜(a ≠ 0)%N⌝ -∗
      "%Hbound"  ∷ ⌜off + sum_list_with arep_size ιs ≤ length ws⌝ -∗
      "%Harep"   ∷ ⌜Forall2 has_arep ιs os⌝ -∗
      "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemMM)⌝ -∗
      "%Hrepgc"  ∷ ⌜N_nat_repr (sr_mem_gc sr) (rt_memaddr sr MemGC)⌝ -∗
      "%Hmemmm"  ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
      "%Hmemgc"  ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemGC = Some (sr_mem_gc sr)⌝ -∗
      "Hat"      ∷ atoms_interp os val_vs -∗ (* most likely to change *)
      "HΦ"       ∷ (ℓ ↦heap (update_path_words off ws (concat (map serialize_atom os))) -∗
                    na_own logrel_nais E -∗
                    instance_rt_func_interp (mr_func_unregisterroot mr) (sr_func_unregisterroot sr) (runtime.spec_unregisterroot rti sr) (f_inst f) -∗
                    rt_token rti sr lmask θ -∗
                    Φ f []) -∗
    CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
    intros Hlen Hcg.
    unfold memory.store in Hcg.
    apply wp_ignore in Hcg.
    destruct Hcg as (-> & off' & Hcg).
    pose proof (wp_store_strong_gc_inner _ _ _ _ _ _ _ _ _ _ Hlen Hcg) as (-> & U & V & W).
    intuition.
  Qed.





End store_common.
