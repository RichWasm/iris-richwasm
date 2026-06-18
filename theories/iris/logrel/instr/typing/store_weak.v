From mathcomp Require Import ssrbool eqtype.
Require Import RichWasm.compiler.memory.
Require Import RichWasm.util.
Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.case_ptr.
Require Import RichWasm.iris.logrel.roots.
Require Import RichWasm.iris.logrel.load_common.
Require Import RichWasm.iris.logrel.path.
Require Import RichWasm.iris.logrel.rt_token.
Require Import RichWasm.iris.numerics.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section store_weak.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.


  (* this is a very particular lemma that's necessary in store_weak mm that I can't imagine
     being generally useful. I also didn't focus on making this clean
   *)
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
    iPoseProof (atom_to_words_mm rti sr mr θ ι o val_v Harep with "[$Hat]") as "(%ns_new & %ns32_new & %Hns_new & %Hbits & %Htypes & Hwords_new)".
    (* Extract pure facts from Hnp, derive dom θ cond for new words, then reconstruct Hnp *)
    iDestruct "Hnp" as "(%rm & %lm & Hroot & Hlayout & Hrti & %Hinj & Hownmm & Howngc & %Hrootok & Hrootmem & %Hheapok)".
    iPoseProof (words_interp_locs_dom_θ θ rm MemMM _ ns_new Hrootok with "[$Hwords_new] [$Hroot]")
      as "%Hlocsθ_new".
    iAssert (rt_token_nophys rti sr lmask θ hm) with "[Hroot Hlayout Hrti Hownmm Howngc Hrootmem]" as "Hnp".
    { iExists rm, lm. iFrame. iPureIntro. split; last split; done. }
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
    iSplitL "Hroot Hlayout Hrti Hownmm Howngc Hrootmem"; first by iFrame.
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
    iFrame "Haddr Hheap'".
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


  Lemma atom_interp_ptr_shaped_pure ptr v:
    atom_interp (PtrA ptr) v -∗
    ⌜∃ (n:N) (n32:i32), N_i32_repr n n32 /\ v = VAL_int32 n32 /\
      ptr_shaped ptr n⌝.
  Proof.
    iIntros "Hat".
    iPoseProof (atom_interp_ptr_shaped with "Hat") as
      "(%n & %n32 & %nrepr & -> & %ptrshaped & (%rp & %hrepr & _))".
    iPureIntro.
    exists n, n32.
    intuition.
  Qed.

  Lemma repr_root_pointer_stupid_inv μ1 μ0 a1 a0:
    repr_root_pointer (RootHeap μ1 a1) (tag_address μ0 a0) ->
    repr_root_pointer (RootHeap μ1 a1) (tag_address μ1 a1).
  Proof.
    intros.
    remember (tag_address μ0 a0).
    inversion H; subst.
    rewrite <- H3 in H.
    done.
  Qed.


  (* speculative store1 gc lemma *)
  Lemma wp_store1_gc_weak_MAYBE a_idx off ι v_idx wt wl ret wt' wl' es :
    run_codegen (store1 mr MemGC a_idx off v_idx ι) wt wl = inr (ret, wt', wl', es) ->
    (* ret = () /\ wt = [] /\ wl' = [] /\  MAKE THIS A _STATE LEMMA
       in mm I could get away with it with the length thing; here not at all *)
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
    unfold store1 in Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_a ?rest Ha Hcg.
    inv_cg_emit Ha; subst.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_v es_store_w Hv Hcg.
    inv_cg_emit Hv; subst.
    clear_nils.
    destruct ret; clear Hretval Hretval0.

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

    (* we need to use a virt_to_phys slice lemma here! *)
    (* it needs to be new because of the ℓ ↦addr shenanigans *)
    iPoseProof (virt_to_phys_slice_store_acc_weak_gc lmask off (arep_size ι)
                 with "[//] [$Htok] [$Hptr] [//]")
      as "(%hm & %Hhm & %Hdomθhm & %Hlocsθ_ws & Hnp &
          (%ns & %ns32 & %Hns & Hphys & Hwords) & Hclose)".


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
        [|by apply Is_true_true, has_values_to_consts|done| exact Hptrshaped | exact Nrepr].
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

        iPoseProof (atom_to_words_gc rti sr mr θ PtrR _ _ Harepsave with "[$Hat2]") as
          "(%ns_new & %ns32_new & %Hns_new & %Hbits & %Htypes & Hwords_new)".

        (* Extract pure facts from Hnp, derive dom θ cond for new words, then reconstruct Hnp *)
        iDestruct "Hnp" as "(%rm & %lm & Hroot & Hlayout & Hrti & %Hinj & Hownmm & Howngc & %Hrootok & Hrootmem & %Hheapok)".
        iPoseProof (words_interp_locs_dom_θ θ rm MemGC _ _ Hrootok with "[$Hwords_new] [$Hroot]")
          as "%Hlocsθ_new".
        iAssert (rt_token_nophys rti sr lmask θ hm) with "[Hroot Hlayout Hrti Hownmm Howngc Hrootmem]" as "Hnp".
        { iExists rm, lm. iFrame. iPureIntro. split; last split; done. }

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
        admit.
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
          (* a0 is even by H, but h3 says its odd (and not 0 so no saturating -) *)
          admit.
        }
        iEval (cbn) in "Hroot_ℓ0".
        destruct μ; try done.
        subst rp.
        assert (a1 = a0). {
          cbn in H1.
          lia.
        }
        subst a1.

        (* for myself: we are STORING PtrA PtrHeap MemGC ℓ0 *)

        (* ------ LOAD ROOT ------- *)
        apply (wp_loadroot sr) in Hloadroot as (_ & -> & -> & Hloadroot_spec).
        rewrite app_assoc.

        (* break apart rt token *)
        iDestruct "Hnp" as "(%rm & %lm & Hroot & Hlayout & Hrti & %Hinj & Hownmm & Howngc & %Hrootok & Hrootmem & %Hheapok)".

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
        iAssert (rt_token_nophys rti sr lmask θ hm) with "[Hroot Hlayout Hrti Hownmm Howngc Hrootmem]" as "Hnp".
        { iExists rm, lm. iFrame. iPureIntro. split; last split; done. }
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

        iPoseProof (atom_to_words_gc rti sr mr θ PtrR _ _ Harepsave with "[$Hat]") as
          "(%ns_new & %ns32_new & %Hns_new & %Hbits & %Htypes & Hwords_new)".

        (* Extract pure facts from Hnp, derive dom θ cond for new words, then reconstruct Hnp *)
        iDestruct "Hnp" as "(%rm & %lm & Hroot & Hlayout & Hrti & %Hinj & Hownmm & Howngc & %Hrootok & Hrootmem & %Hheapok)".
        iPoseProof (words_interp_locs_dom_θ θ rm MemGC _ _ Hrootok with "[$Hwords_new] [$Hroot]")
          as "%Hlocsθ_new".
        iAssert (rt_token_nophys rti sr lmask θ hm) with "[Hroot Hlayout Hrti Hownmm Howngc Hrootmem]" as "Hnp".
        { iExists rm, lm. iFrame. iPureIntro. split; last split; done. }
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
      apply wp_store_w in Hcg as (_ & -> & -> & Hcgspec).

      (* also need physical stuff *)
      admit.


  Admitted.






  (* this is a "get me all the kind info please" lemma
     a bit old bc it has some things it doesn't strickly need, but that's
     okay.
   *)
  Lemma get_all_kinding_info_store_weak_general τ κ μ τval π pr :
    let ψ := InstrT [RefT κ μ Mut τ; τval] [RefT κ μ Mut τ] in
    resolves_path τ π None pr ->
    ∀ F off ρ se sκ κser L ιs o1,
      sem_env_interp F se ->
      path_offset (fe_of_context F) τ π = Some off ->
      Forall (has_mono_size F) pr.(pr_prefix) ->
      type_skind (Σ:=Σ) se (RefT κ μ Mut τ) = Some sκ ->
      eval_kind se κ = Some sκ ->
      (* eval_mem se μ = Some MemMM -> *)
      has_ref_flag F (pr_target pr) GCRefs ->
      pr_target pr = SerT κser τval ->
      has_instruction_type_ok F ψ L ->
      type_rep (fe_type_vars (fe_of_context F)) τval = Some ρ ->
      eval_rep EmptyEnv ρ = Some ιs ->
      skind_has_svalue sκ (SAtoms [o1]) ->
      (∃ σ ξ ξser sz ξ_ref,
          has_kind F τ (MEMTYPE σ ξ) /\
            has_kind F (pr.(pr_target)) (MEMTYPE (RepS ρ) ξser) /\
            has_kind F τval (VALTYPE ρ ξser) /\
            eval_size EmptyEnv (RepS ρ) = Some sz /\
            κ = VALTYPE (AtomR PtrR) ξ_ref /\
            sκ = SVALTYPE [PtrR] ξ_ref /\
            sum_list_with arep_size ιs = sz /\
            eval_kind se κser = Some (SMEMTYPE sz ξser) /\
            length (flat_map arep_flags ιs) = sz /\
            type_skind se τval = Some (SVALTYPE ιs ξser) /\
            type_skind se (SerT κser τval) = Some (SMEMTYPE sz ξser)).
  Proof.
    intros ψ Hresolves.
    intros * Hse Hoffset Hmono Htypeskind Hevalκ Href Hprtarget Hok Hrep Hevalρ Hsksv.

    rewrite Hprtarget in Href.
    unfold ψ in Hok.
    inversion Hok; subst.
    destruct H as [Href2 _].
    inversion Href2. subst.
    destruct H2 as (? & Hrep3 & Hmono2).
    inversion Hrep3; subst.
    apply has_kind_ref_ty in H.
    destruct H as (σ & ξτ & Hkind).

    assert (has_mono_size F (pr_target pr)).
    {
      repeat
        match goal with
        | H : has_instruction_type_ok _ _ _ |- _ => inversion H; clear H; subst
        | H : has_mono_rep_instr _ _ |- _ => inversion H; clear H; subst
        | H : Forall _ (_ :: _) |- _ => inversion H; clear H; subst
        | H : Forall _ [] |- _ =>  clear H
        | H : has_mono_rep _ _ |- _ => destruct H as (?ρ & ?Hrep & ?Hmono)
        | H : has_rep _ _ _ |- _ => inversion H; subst; clear H
        | H : MEMTYPE _ _ = MEMTYPE _ _ |- _ => inversion H; subst; clear H
        | H : VALTYPE _ _ = VALTYPE _ _ |- _ => inversion H; subst; clear H
        | H : has_kind ?F (RefT _ _ _ _) _ |- _ => eapply has_kind_ref_ty in H; destruct H as (? & ? & ?); subst
        | H : has_kind ?F ?t ?k,
          H' : has_kind ?F ?t ?k' |- _ =>
            pose proof (has_kind_agree F t k k' H H'); clear H'
        end.
      pose proof Hresolves as Hresolves'.
      rewrite Hprtarget.
      eapply pr_target_kind in Hresolves'; eauto using KSer.
      destruct Hresolves' as (ktgt & Hkind0).
      rewrite Hprtarget in Hkind0.
      inversion Hkind0; subst.
      unfold κ0 in *.
      eexists; eauto.
      unfold is_mono_size.
      constructor.
      repeat
        match goal with
        | H : has_mono_rep_instr _ _ |- _ => inversion H; clear H; subst
        | H : Forall _ (_ :: _) |- _ => inversion H; clear H; subst
        | H : Forall _ [] |- _ =>  clear H
        | H : has_mono_rep _ _ |- _ => destruct H as (?ρ & ?Hrep & ?Hmono)
        | H : has_rep _ _ _ |- _ => inversion H; subst; clear H
        | H : MEMTYPE _ _ = MEMTYPE _ _ |- _ => inversion H; subst; clear H
        | H : VALTYPE _ _ = VALTYPE _ _ |- _ => inversion H; subst; clear H
        | H : has_kind ?F ?t ?k,
          H' : has_kind ?F ?t ?k' |- _ =>
            pose proof (has_kind_agree F t k k' H H'); clear H'
        end.
      by unfold is_mono_rep in *.
    }

    inversion H as [? ? σtgt ξser Hhktgt Htgtmono HF' HT]; subst.
    rewrite Hprtarget in Hhktgt.
    inversion Hhktgt; subst. unfold κ1 in *; clear κ1.

    pose proof (mono_size_eval_emp_Some _ Htgtmono) as (sz & Hev).

    unfold type_rep in Hrep.

    (* type_kind_has_kind_agree *)
    apply bind_Some in Hrep.
    destruct Hrep as (κ_temp & type_kind_τval & kindrep).
    pose proof (type_kind_has_kind_agree F τval _ _ H4 type_kind_τval).
    subst.
    inversion kindrep; subst.

    (* the other things that would be nice: sκ is SVALTYPE .. *)
    inversion Hrep3; subst. (* ey win we have valtype *)
    rename H1 into Hkind_ref. rename x into ρ_ref. rename ξ0 into ξ_ref.

    (* okay what I want now is that ρ_ref is AtomR PtrR *)
    assert (ρ_ref = AtomR PtrR). {
      inversion Hkind_ref; subst; done.
    }
    subst.
    (* then ξ_ref will be either GCRef of AnyRef which isn't smthn rn *)
    (* future lemma that takes in eval_mem μ can say smthn tho *)
    destruct sκ; [| by destruct Hsksv].
    rename r into ξ_sκ.
    assert (κ = VALTYPE (AtomR PtrR) ξ_ref). {
      inversion Hkind_ref; done.
    }
    subst.

    assert (ξ_ref = ξ_sκ). {
      cbn in Hevalκ. inversion Hevalκ; done.
    }
    subst ξ_sκ.
    assert (l = [PtrR]). {
      cbn in Hevalκ. inversion Hevalκ; done.
    }
    subst.


    assert (sum_list_with arep_size ιs = sz). {
      (* I think this is the right lemma at least *)
      unfold eval_size in Hev.
      rewrite Hevalρ in Hev.
      cbn in Hev. inversion Hev; subst.
      by apply sum_list_with_list_sum.
    }

    (* next up: κser stuff *)
    rename κ0 into κser.
    assert (eval_kind (senv_empty (Σ:=Σ)) κser = Some (SMEMTYPE sz ξser)). {
      cbn.
      rewrite eval_rep_senv_empty_irrel.
      rewrite Hevalρ.
      cbn.
      rewrite sum_list_with_list_sum in H1.
      rewrite H1.
      done.
    }
    assert (eval_kind se κser = Some (SMEMTYPE sz ξser)). {
      by apply eval_kind_senv_empty_le.
    }

    (* random thing for flags *)
    assert (length (flat_map arep_flags ιs) = sz). {
      rewrite length_flat_map.
      assert (∀ ι, length (arep_flags ι) = arep_size ι). {
        intros ι; destruct ι; cbn; done.
      }
      setoid_rewrite H6.
      rewrite <- sum_list_with_list_sum.
      done.
    }

    (* I need type_skind se τval *)
    assert (Hevalρse: eval_rep se ρ = Some ιs). {
      by apply eval_rep_emptyenv.
    }
    assert (eval_kind se (VALTYPE ρ ξser) = Some (SVALTYPE ιs ξser)). {
      unfold eval_kind.
      rewrite Hevalρse.
      cbn.
      done.
    }
    assert (type_skind se τval = Some (SVALTYPE ιs ξser)). {
      eapply type_skind_has_kind_Some; try done.
    }

    assert (type_skind se (SerT κser τval) = Some (SMEMTYPE sz ξser)). {
      eapply type_skind_has_kind_Some; try done.
    }

    (* always do all the way at the end. Ideally, should always be basically
     just eexists -> done. *)
    rewrite Hprtarget.
    do 5 eexists.
    done.
  Qed.

  Lemma compat_store_weak M F L wt wt' wtf wl wl' wlf es' κ κser μ τ τval π pr :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [RefT κ μ Mut τ; τval] [RefT κ μ Mut τ] in
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

    (** COMPILER DESTRUCTION **)
    inv_cg_bind Hcompile ρ ?wt ?wt ?wl ?wl es_off ?es_rest Hρ Hcompile.
    inv_cg_bind Hcompile ιs ?wt ?wt ?wl ?wl es_ρ ?es_rest Hιs Hcompile.
    inv_cg_bind Hcompile off ?wt ?wt ?wl ?wl  es_fail ?es_rest Hoff Hcompile.
    inv_cg_try_option Hρ; rename Heq_some into Hρ.
    inv_cg_try_option Hιs; rename Heq_some into Hιs.
    inv_cg_try_option Hoff; rename Heq_some into Hoff.
    inv_cg_bind Hcompile val_localidxs ?wt ?wt wl_save ?wl  es_save ?es_rest Hsave Hcompile.
    inv_cg_bind Hcompile a ?wt ?wt ?wl ?wl  es_a ?es_rest Ha Hcompile.
    cbn in Ha; inversion Ha; subst; clear Ha.
    inv_cg_bind Hcompile res_emit ?wt ?wt ?wl ?wl  es_emit ?es_rest Hemit Hcompile.
    inv_cg_emit Hemit.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_case_ptr es_ptr_flags Hcompile Hptr_flags.

    (* Some clean up *)
    subst.
    clear_nils.
    destruct u. destruct p; destruct u; destruct u0.

    (* Summary: (put any useful info about the variables here. probs obvious stuff)
       - wl_save is the list of locals associated with the thing we're storing into memory
     *)



    (** OUTERMOST DIGGING **)
    unfold have_instr_type_sem.
    iIntros (??????????) "@@@@@@@@@@".

    (* we have two things on the stack: a reference and a τval *)
    (* separate the value interp *)
    iPoseProof (values_interp_cons_l with "[$Hos]") as "(%os1 & %os2 & -> & Hos1 & Hos2)".
    iEval (rewrite values_interp_one_eq; cbn) in "Hos2".
    iPoseProof (atoms_interp_app_l with "[$Hvs]") as "(%vs1 & %vs2 & -> & Hvs1 & Hvs2)".
    iPoseProof (value_interp_ref_sz with "[$Hos1]") as "%Hos1len".
    destruct os1; [inversion Hos1len | destruct os1; [| inversion Hos1len]].
    rename a into o1.
    iEval (rewrite atoms_interp_one_inv) in "Hvs1".
    iDestruct "Hvs1" as "(%v1 & -> & Hv1)".
    clear Hos1len.
    rewrite value_interp_eq.
    iDestruct "Hos1" as (sκ Hsκ) "[%skindsv Ho1]".

    (* Summary:
       - o1 is the atom associated with the ref, and v1 is its associated value
       - os2 are the atoms associated with τval, and vs2 are its values
       Note: o1 is Ptr _, but it's easier to get that after splitting between MM
       and GC.
     *)

    (* Set any other useful keys here? *)
    set (ptr_local := sum_list_with length F.(typing.fc_locals) + length (wl ++ wl_save) ) in *.



    (** KINDING STUFF *)

    pose proof (Hsκ) as Hevalκ.
    cbn in Hevalκ.
    (* this lemma is a quarantine zone for all things kinding
       if we need more info in the future it can be added. Also potentially
       eventually make _MM and _GC versions that use eval_mem, if necessary
     *)
    pose proof
      (get_all_kinding_info_store_weak_general
         τ κ μ τval π pr Hresolves
         F off ρ se sκ κser L ιs o1
         H Hoff Hmonosize Hsκ Hevalκ Hdrop Hser Htype Hρ Hιs skindsv
      ) as AllKinding.
    destruct AllKinding as
      (σ & ξ & ξser & sz & ξ_ref &
         Hkind_τ & Hkind_prtarget & Hkind_τval & Hevalsize & -> & -> &
          Hιssz & Hevalκser & Hflaglengths & Htypeskindτval & Htypeskindsert).


    (** OTHER GENERAL FACTS THAT WE NEED FOR BOTH CASES **)
    (* NOTE: highly recommend folding as much of this section as possible *)

    (* for saving the stack, frame interp thingy*)
    iPoseProof (frame_interp_wl_interp with "Hframe") as "%Hwl".

    (* this section establishes a bound on ptr_local which is necessary everywhere *)
    set (locsz :=
               length (concat (typing.fc_locals F)) +
               length (wl ++ wl_save) +
               length (T_i32 :: wl2 ++ wl3 ++ wlf)).
    iAssert (⌜length (f_locs fr) = locsz ⌝ %I) as "%Hflen". {
      iDestruct "Hframe" as "(%osf & %vss_L & %vs_WL & %Hlocs & %Hprims & %Hretty & Hats &  Hlocs)".
      rewrite Hlocs.
      unfold locsz.
      rewrite length_app.
      apply Forall2_Forall2_length in Hprims.
      unfold result_type_interp in Hretty.
      rewrite !length_concat Hprims.
      eapply Forall2_length in Hretty.
      rewrite !length_app in Hretty.
      rewrite -Hretty.
      cbn.
      iEval (rewrite !length_app).
      iEval (rewrite !Nat.add_assoc).
      done.
    }
    assert (ptr_local < length (f_locs fr)) as Hptrlocalfr. {
      rewrite Hflen.
      unfold locsz, ptr_local.
      rewrite sum_list_with_list_sum length_concat.
      cbn; lia.
    }



    (** BEGIN THE SPLIT **)

    (* This is where it's best to show o1 is ptr and v1 a ptr shaped number,
       so the first bit of both sections is dedicated to that.
       this bit first for that `last done` in the splitting line.
     *)
    iEval (cbn) in "Ho1".

    destruct (eval_mem se μ) eqn:evalμ; last done; destruct b.
    1: refine ?[MemMM]. 2: refine ?[MemGC].

    [MemMM]: {
      iEval (cbn) in "Ho1".
      iDestruct "Ho1" as "(%ℓ & %fs & %ws & %toinvert & Hℓ_layout & Hℓ_heap & Hτ)".
      inversion toinvert; subst o1; clear toinvert.
      iPoseProof (atom_interp_ptr_shaped with "Hv1") as
        "(%n & %n32 & %Hn32 & -> & %Hnshp & %rp & %Hreproot & Hv1)".
      apply has_values_app_inv in H0.
      destruct H0 as (ev1 & evs2 & -> & Hev1 & Hevs2).
      apply has_values_to_consts_inv in Hev1 as Hev1tosubst.
      cbn in Hev1tosubst. subst ev1.
      (* right here: need to dig into root pointer a lot *)
      (* Our facts:
         - ptr_shaped (PtrHeap MemMM ℓ) n
         X repr_root_pointer rp n DONE: GOT a AND MOD STUFF OUT OF THIS
         X root_pointer_interp rp (PtrHeapMemMM ℓ) DONE: GOT ->ADDR OUT OF THIS
       *)
      destruct rp; iEval (cbn) in "Hv1"; try done.
      destruct μ0; iEval (cbn) in "Hv1"; try done.
      (* okay now to connect a and n *)
      inversion Hreproot. subst μ0 a0.
      rename H2 into Hamod3; rename H4 into Hanot0; rename H3 into Han.
      pose proof Han as Htagaddress.
      cbn in Han.
      assert (Hna: (n+3)%N=a).
      { assert (4 <= a)%N by (by eapply mod_bound_nonzero). lia. }
      (* okay sure lemma here to connect ↦addr to θ
       related to ghost_map_auth rw_addr (1 / 2) θ bc lookup fragment :) *)
      iAssert (⌜repr_pointer θ (PtrHeap MemMM ℓ) n⌝%I) with "[Hrt Hv1]" as "%Hrepr". {
        (* we need θ !! l = Some (MemMM, a) *)
        unfold rt_token.
        iDestruct "Hrt" as "(%rm & %lm & %hm & Haddr & _)".
        iPoseProof (ghost_map_lookup with "[$] [$]") as "%Hθℓ".
        iPureIntro.
        rewrite <- Htagaddress.
        by constructor.
      }

      (* another improtant thing soon is that lpall ℓ is true *)
      assert (Hlmask: lpall ℓ) by done.

      (* we need that the original fs and ws satisfy layoutok *)
      iAssert (⌜Forall2 word_has_flag fs ws⌝%I) with "[Hℓ_layout Hℓ_heap Hrt]" as "%Hfswsmatch". {
        open_rt "Hrt".
        iPoseProof (ghost_map_lookup with "[$Hlayout] [$Hℓ_layout]") as "%Hθlayout".
        iPoseProof (ghost_map_lookup with "[$Hheap] [$Hℓ_heap]") as "%Hθheap".
        iPureIntro.
        unfold layout_ok in Hlayoutok.
        unfold map_Forall2 in Hlayoutok.
        specialize (Hlayoutok ℓ).
        rewrite Hθlayout in Hlayoutok; rewrite Hθheap in Hlayoutok.

        inversion Hlayoutok; subst.
        specialize (H2 ltac:(auto)).
        eapply Forall2_impl; [exact H2|].
        intros f' w' Hwh; cbn in Hwh; apply Is_true_true; exact Hwh.
      }


      (* Summary:
         - o1 became (PtrHeap MemMM ℓ), v1 became (VAL_int32 n32), ev1 became BI_const...
         - n32 is... the address associated with the pointer? Or at minimum it is the
           actual thing on the stack.
         - we also dug into the value interp of the reference, getting the following:
           + we got rp, the root pointer associated with ℓ, and a bunch of ℓ resources
             and destruct rp to get mod info associated with n and n+3
           + we also importantly got the type interpretation of τ (what's currently being
             pointed to by the reference) and the words ws currently sitting there
       *)


      (** PUT FACTOIDS WE NEED HERE (THAT ARE MM/GC SPECIFIC) **)
      (* I think some of the kinding quarantine but with resources can be
         here. Not all of it because of path lemma, though. *)
      (* mini kinding quarantine right here! I should make it a lemma eventually *)
      iAssert (⌜Forall2 has_arep ιs os2 /\ has_areps ιs (SAtoms os2) /\
               Forall (forall_ptr_word (ref_flag_ptr_interp ξser))
                (concat (map serialize_atom os2))
                  ⌝%I)
         with "[Hvs2 Hos2]" as "%KindingQuarantine". {
        rewrite value_interp_eq.
        iEval (cbn -[pre_type_interp type_skind]) in "Hos2".
        iDestruct "Hos2" as "(%sκ_temp & %Htypeskindtemp & %Harepsoon & pre)".
        iPureIntro.
        rewrite Htypeskindτval in Htypeskindtemp.
        inversion Htypeskindtemp. subst sκ_temp.
        destruct Harepsoon as (Hareps & Hforallatomref).

        repeat split.
        - unfold has_areps in Hareps.
          destruct Hareps as (os & toinvert & yes).
          inversion toinvert; subst; done.
        - done.
        - by apply forall_ptr_atom_to_word_ref_flag_interp.
      }
      destruct KindingQuarantine as (Harepιsos2 & Hareps & Hrefinterp).
      assert (Hos2sz: length (concat (map serialize_atom os2)) = sz). {
        assert (length (concat (map serialize_atom os2)) = length (flat_map arep_flags ιs)). {
          rewrite flat_map_concat_map.
          apply has_arep_means_equal_lengths; done.
        }
        by etransitivity.
      }
      iDestruct (result_type_interp_of_atoms_interp with "Hvs2") as "%Hres_type_vs2"; try done.

      (** TIME TO BOOGIE *)
      (* note: I think saving stack and local tee can happen before the split *)
      (* it's a little easier to already have v1 being an n32 though *)

      (** SAVING STACK AND LOCAL TEE *)
      (* First, saving stack to clear evs2 and es_save *)

      (* apply lemma on the codegen. order of goals to help with evars *)
      eapply cwp_save_stack_w in Hsave; auto.
      4: exact Hevs2.
      3: {
        unfold translate_arep in Hres_type_vs2.
        rewrite map_comp. done.
      }
      2: exact Hwl.
      destruct Hsave as (Hval_localidxs_seq & -> & Hwl_save & Hsave).

      (* now to use the facts we got *)
      rewrite (app_assoc _ es_save _).
      rewrite <- (app_assoc _ evs2 _).
      iApply (cwp_seq with "[Hfr Hrun]").
      {
        (* note: this is 100% copied from case.v lol *)
        (* it looks like this is all just related to cwp_save_stack so should be the same *)
        (* possibility of it being incorrect *)
        instantiate (1 := λ fr' vs, (
          ∃ val_idxs,
          ⌜vs = [VAL_int32 n32]⌝ ∗
          ⌜frame_rel (λ i, i ∉ val_idxs) fr fr'⌝ ∗
          ⌜Forall2 (fun i v => f_locs fr' !! localimm i = Some v) val_localidxs vs2⌝ ∗
          ⌜val_idxs = seq (fe_wlocal_offset fe + length wl) (length wl_save)⌝ ∗
          ⌜val_localidxs = map prelude.W.Mk_localidx val_idxs⌝
                                    )%I).
        iApply cwp_val_app; first done.
        iApply (Hsave with "[$] [$]").
        iIntros (f' [Hfsame Hfchanged]).
        unfold fvs_combine.
        subst val_localidxs wl_save.
        auto.
      }
      iIntros (fr_saved w) "(%val_idxs & -> & %Hfrel_fr_saved & %Hsaved & %Hval_idxs_seq & %Hval_localidxs) Hfr Hrun".
      clear Hsave.

      iPoseProof (frame_interp_update_frame' with "Hframe") as "Hframe_saved".
      2, 3, 5: done.
      { subst val_idxs fe. by rewrite fe_wlocal_offset_length. }
      { subst wl_save.
        by rewrite map_comp.
      }

      iDestruct (frame_interp_wl_interp with "Hframe_saved") as "%Hwl_saved".
      pose proof (interp_wl_length _ _ _ Hwl_saved) as Hfr_saved_locs_len.

      (* Reestablish ptr_local length *)
      assert (Hptrlocalfrsaved: ptr_local < length (f_locs fr_saved)). {
        (* If this isn't true this is weird, but seems hardish to prove *)
        subst ptr_local.
        simpl.
        eapply Nat.lt_le_trans; last done.
        - rewrite app_assoc.
          subst fe.
          repeat rewrite length_app.
          unfold fe_wlocal_offset.
          lias.
      }

      (* Next: local_tee stuff *)
      set (fr' := ({|
                     W.f_locs :=
                       <[localimm (prelude.W.Mk_localidx ptr_local):=
                           VAL_int32 n32]> (f_locs fr_saved);
                     W.f_inst := f_inst fr_saved
                   |})) in *.
      rewrite (app_assoc (to_consts [VAL_int32 n32]) _ _).
      iApply (cwp_seq with "[Hfr Hrun]").
      {
        (* this is copied from load.v *)
        iApply (cwp_local_tee with "[] [$] [$]").
        - done.
        - now instantiate (1:= λ f'' v'', ⌜f'' = fr' /\ v'' = [VAL_int32 n32]⌝%I).
      }
      iIntros (? ?) "(-> & ->) Hf Hrun".

      (* do some frame interp updating *)
      iEval (rewrite app_assoc) in "Hframe_saved".
      iPoseProof (frame_interp_update_frame' with "Hframe_saved") as "Hframe".
      5: {
        instantiate (1 := fr').
        instantiate (1 := [ptr_local]).
        unfold fr'.
        unfold frame_rel.
        cbn; split; [|done].
        unfold mask_locs_eq. cbn.
        intros i Hipls.
        symmetry.
        apply list_lookup_insert_ne.
        intros ->; apply Hipls; left.
      }
      all: try done.
      2: {
        simpl.
        instantiate (1 := [_]).
        apply Forall2_cons.
        split; [|done].
        cbn.
        by apply list_lookup_insert_eq.
      }
      2: {
        apply Forall2_cons; split; last done.
        by eexists.
      }
      {
        subst ptr_local fe.
        cbn.
        rewrite sum_list_with_length_concat.
        done.
      }

      (* Summary:
         - Used up evs2 and es_save_stack and "put" the pointer in front of es_case_ptr block
         - Our frame changed twice: fr_saved is after saving the stack (so lots of things)
           got put into locals, and fr' is after putting n32 into the local associated
           with the ptr.
         - We also got a bunch of val_indx stuffs everywhere
         - Also update frame_interp resources here

         Note: probably put lemmas and facts related to saving the stack here. Try to make
         them lemmas, since the GC case also needs them.
      *)


      (** ----------------- STORE TIME -------------------- **)
      (* Apply the case ptr lemma onto the codegen *)
      apply cwp_case_ptr in Hcompile.
      destruct Hcompile as
        (wt_unreach & wt_memMM & wt_memGC &
           wl_unreach & wl_memMM & wl_memGC &
           es_unreach & es_memMM & es_memGC & Hcompile).
      destruct Hcompile as
        (Hcg_unreach & Hcg_memMM & Hcg_memGC & -> & -> & Hcaseptr_spec).


      (* Specialize the spec with out variables *)
      specialize (Hcaseptr_spec [] []).
      specialize (Hcaseptr_spec (PtrHeap MemMM ℓ) n n32).
      specialize (Hcaseptr_spec ltac:(eauto) ltac:(auto) ltac:(auto) ltac:(auto)).
      clear_nils.

      (* do a bit more work in Hcg_memMM *)
      (* note: I need to this now bc I get info about which wl_memMMs are empty *)
      (* which I need outside the cwp_seq *)
      inv_cg_bind Hcg_memMM what ?wt ?wt ?wl ?wl
        es_root_to_heap es_store Hcg_root Hcg_store.
      destruct what.
      cbn in Hcg_root.
      inversion Hcg_root. subst wt0 wl0 es_root_to_heap; clear_nils; clear Hcg_root.
      subst wt1 wl1.

      (* HERE ARE THE TWO SPECS WE HAVE: PATH AND STORE *)
      pose proof
        (resolves_path_inv_sep_weak rti sr se
           τ π pr Hresolves F off ρ σ ξ ξser sz) as Hpath_spec.
      specialize (Hpath_spec H Hoff Hmonosize Hkind_τ Hkind_prtarget Hevalsize).

      assert (Hstupidlen: length val_localidxs = length ιs). {
        move Hres_type_vs2 at bottom.
        move Hsaved at bottom.
        apply Forall2_length in Hsaved.
        unfold result_type_interp in Hres_type_vs2.
        apply Forall2_length in Hres_type_vs2.
        rewrite length_map in Hres_type_vs2.
        etransitivity; done.
      }

      pose proof (wp_store_weak_mm _ _ _ _ _ _ _ _ _ _ Hstupidlen Hcg_store) as Hstore_spec.
      destruct Hstore_spec as (_ & -> & -> & Hstore_spec).

      (* A cwp_val_app, which I'm confused why it's on the stack at all but oh well *)
      iApply cwp_val_app; first done.
      unfold fvs_combine.

      iApply (cwp_seq with "[-]").
      {
        iApply (Hcaseptr_spec with "[$] [$] [] [-]");
          [iPureIntro; cbn; by apply list_lookup_insert_eq|].
        iModIntro.
        iIntros "Hfr Hrun".

        (** ACTUALLY STORING TIME **)
        (* let's start specialize the store spec *)
        specialize Hstore_spec with (f:=fr').
        specialize Hstore_spec with (a:=a%N).
        specialize Hstore_spec with (a32:=n32).
        specialize Hstore_spec with (val_vs:=vs2).
        specialize Hstore_spec with (lmask:=lpall).
        specialize Hstore_spec with (θ:=θ).
        specialize Hstore_spec with (ℓ:=ℓ).
        specialize Hstore_spec with (os:=os2).
        specialize Hstore_spec with (ws:=ws).


        (* ws is likely coming from path_spec *)
        (* I think ℓ might change? Wait I'm getting confused lol *)
        (* and os will be tied to ws *)

        (* let's try using the path spec *)
        iPoseProof (Hpath_spec $! ws with "[$Hτ]") as "Hpath_spec".
        iDestruct "Hpath_spec" as "(%Hwslengths & Htarget & Hcontinuation)".
        rewrite Hser. clear_nils.

        iAssert (⌜Forall2 (λ (f : pointer_flag) (w : word), word_has_flag f w)
           (concat (map arep_flags ιs))
           (take (sum_list_with arep_size ιs) (drop off ws))⌝%I) with "[Htarget]" as "%Hhasflags". {
          (* hm unsure how this will go *)
          rewrite Hιssz.
          unfold get_path_words.
          rewrite value_interp_eq.
          iEval (cbn -[type_skind pre_type_interp]) in "Htarget".
          iDestruct "Htarget" as "(%sκ & %Htemp & %Hyeah & Htype)".
          rewrite Htypeskindsert in Htemp.
          inversion Htemp; subst sκ.
          destruct Hyeah as (_ & Hrefflag).
          iEval (cbn) in "Htype".
          (* I'm scared *)
          iDestruct "Htype" as "(%os & %Hserialized & Htype)".
          rewrite type_interp_eq.
          iEval (cbn -[type_skind pre_type_interp]) in "Htype".
          rewrite Htypeskindτval.
          iDestruct "Htype" as "(%sκ & %toinvert & %Helpme & Htype)".
          inversion toinvert; subst sκ. clear Htemp toinvert.
          destruct Helpme as (Hosιs & Hptros).

          iPureIntro.
          inversion Hserialized.
          rewrite !H1.
          rewrite H1 in Hrefflag.

          (* dealing with Is_true and is_true lol *)
          eapply Forall2_impl.
          1: by apply has_areps_imp_word_has_flag.
          intros.
          cbn in H0.
          apply Is_true_true.
          done.
        }

        (* we need to transform atoms_interp to weak now! *)
        iPoseProof (atoms_interp_to_weak_memMM with "[$] [$Hvs2]") as "[Hrt Hvs2]".

        (* let's try applying Hstore_spec. Oh boy oh boy. Currently fully giving atoms_interp to store *)
        iApply (Hstore_spec with "[$] [$] [$] [$] [] [$] [] [] [] [] [] [] [] [] [] [] [$Hvs2] [-]");
          clear Hstore_spec; try done.
        - iPureIntro.
          by (cbn; by apply list_lookup_insert_eq).
        - iPureIntro. (* this is by Hsaved and the fact that ptr_local is after all val_idxs *)
          cbn.
          set (val_idx_upper_bound := (fe_wlocal_offset fe + length wl) +
                                (length (map translate_prim (map arep_to_prim ιs)))).
          assert (val_idx_upper_bound < ptr_local + 1). {
            subst val_idx_upper_bound ptr_local.
            cbn.
            repeat rewrite length_app.
            assert (length wl_save = length (map translate_prim (map arep_to_prim ιs))). {
              rewrite Hwl_save; done.
            }
            rewrite H0.
            lia.
          }
          (* the reason the +1 is on the right is bc technically possible *)
          (* that everything is empty and val_localidx = [], and so then the *)
          (* the negation saturates and there's an <= *)

          eapply (forall2_lookup_same (f_locs fr_saved) _ _ _ ptr_local localimm).
          + intros j Hneq. rewrite list_lookup_insert_ne; [done | lia].
          + rewrite Hval_localidxs Hval_idxs_seq.
            eapply Forall_impl; first apply (map_seq_forall_localidx_neq (fe_wlocal_offset fe + length wl) (length wl_save)).
            intros i Hneq. unfold ptr_local. rewrite length_app. subst fe. unfold fe_wlocal_offset in Hneq. simpl in Hneq. lia.
          + exact Hsaved.
        - iPureIntro. cbn.
          rewrite Han. done.
        - iPureIntro. rewrite Hιssz. done.
        - unfold instance_interp.
          unfold base_mem_idx.
          iDestruct "Hinst" as "(_ & _ & _ & _ & %TheThing & _)".
          iPureIntro.
          cbn.
          (* fr_inst fr = fr_inst fr_saved *)
          unfold frame_rel in Hfrel_fr_saved.
          destruct Hfrel_fr_saved as (_ & <-).
          done.
        - (* we're almost back :) *)
          iIntros "Hℓ_heap Hℓ_addr Hrt".
          (* If there's anything else we need to take out, put it here! *)
          (* I need the info about off and sz we get from path lemma *)
          let Q := open_constr:(_ : iProp Σ) in
          instantiate (1 := λ f'' vs', (⌜f'' = fr' /\ vs' = []
              /\ (off + sz ≤ length ws)
                ⌝
              ∗ Q)%I).
          iEval (cbn).
          iSplitR; first done.
          (* after we play around a bit more it'll be iAccu *)
          (* we need to use the continuation NOW *)
          iSpecialize ("Hcontinuation" $! (concat (map serialize_atom os2)) Hos2sz).
          iAssert (value_interp rti sr se (SerT κser τval) (SWords (concat (map serialize_atom os2))))
            with "[Hos2]" as "Hnewsert". {
            iEval (rewrite value_interp_eq).
            iEval (cbn).
            rewrite Hevalκser.
            iExists (SMEMTYPE sz ξser).
            iSplitR; first done.
            iSplitR; first done.
            iExists os2; iFrame.
            rewrite flat_map_concat_map.
            done.
          }
          iSpecialize ("Hcontinuation" with "[$Hnewsert]").
          (* why do we have the old value_interp still... this feels deeply deeply odd odd *)
          (* I have confirmed that this is okay *)
          iAccu.
      }




      (** ----------------- POINTER FLAGS --------------------- **)
      iIntros (fr_store vs_store) "Hres Hfr Hrun".
      (* note: this is a bit annoying without iNamedAccu, but oh well *)
      iDestruct "Hres" as "((-> & -> & %Hwslength)
             & Hown & Hℓ_fs & Hframe & Holdval & Hℓ_newws & Hℓ_addr
            & Hrt & Hvalτ)".
      rename fr' into fr_store.

      clear_nils.

      (* in order to use the pointer flags spec, we need to intentionally weaken the rttoken *)
      (* in store strong, the store lemma will weak it for us *)
      set (rtmask := (λ l, l ≠ ℓ)).
      iAssert (rt_token rti sr rtmask θ) with "[Hrt]" as "Hrt". {
        by iApply rt_token_lpall.
      }

      (* apply the spec onto the codegen and slowly specialize *)
      eapply cwp_set_pointer_flags in Hptr_flags.
      destruct Hptr_flags as (_ & -> & -> & Hptr_flags_spec).
      specialize (Hptr_flags_spec fr_store n n32).
      specialize (Hptr_flags_spec rtmask).
      specialize (Hptr_flags_spec θ).
      specialize (Hptr_flags_spec MemMM ℓ).
      clear_nils.

      (* we need four pure facts before using the spec:
         - off + length ιs < Int32.mod. Maybe from Hcg_memMM's memory.store?
         - N_i32_repr n n32. We have this.
         - repr_pointer θ (ptr) n, which we got earlier
         - f_locs fr_caseptr !! .. = n32. This is then just the minimum
           requirement of relating fr_caseptr and fr'
       *)
      assert (¬ rtmask ℓ). {
        unfold rtmask.
        auto.
      }
      assert (H3: f_locs fr_store !! localimm (prelude.W.Mk_localidx ptr_local) =
                    Some (VAL_int32 n32)) by (cbn; by apply list_lookup_insert_eq).
      specialize (Hptr_flags_spec ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto)).

      (* Time for the case pointer spec! *)
      iApply (Hptr_flags_spec with "[$] [$] [] [$] [$] [$] [] [-]").
      1: done.
      1: {
        unfold instance_interp.
        unfold instance_runtime_interp.
        (* show f_inst fr_store = f_inst fr *)
        iEval (cbn).
        destruct Hfrel_fr_saved as (_ & <-).
        iDestruct "Hinst" as "(_ & (_ & _ & Yes & _) & _)".
        iFrame "#".
      }

      (* this iIntros is from the ptr flags spec *)
      iIntros "Hℓ_fs Hrt #Hnsfun Hown #Hinst_spec".
      clear_nils.

      set (new_fs := set_flags_at off (flat_map arep_flags ιs) fs) in *.
      set (new_ws := update_path_words off ws (concat (map serialize_atom os2))) in *.

      (* now, we need to restablish rttoken *)
      (* i think we need a bunch of stuff. First that original words
         and layout have correct stuff
       *)
      (* Establish that the new fs/ws satisfy heap_ok *)
      assert (Hnewfswsmatch: Forall2 word_has_flag new_fs new_ws). {
        (* break apart the flags. Length lemmas for easier lemma application *)
        assert (sz = length (flat_map arep_flags ιs)). {
          subst sz.
          done.
        }
        assert (length fs = length ws). {
          eapply Forall2_length; exact Hfswsmatch.
        }
        pose proof (Hwslength) as Hlenflags.
        rewrite H1 in Hlenflags. rewrite <- H2 in Hlenflags.
        pose proof (updating_flags off (flat_map arep_flags ιs) fs ltac:(lia))
          as (fs1 & fs_old & fs2 & -> & Hfs & Hlenoldfs & Hlenfs1).
        unfold new_fs. rewrite Hfs.

        (* same thing but for words *)
        pose proof Hwslength as Hlenwords. rewrite <- Hos2sz in Hlenwords.
        pose proof (updating_words off (concat (map serialize_atom os2)) ws ltac:(lia))
          as (ws1 & ws_old & ws2 & -> & Hws & Hlenoldws & Hlenws1).
        unfold new_ws. rewrite Hws.

        assert (length fs2 = length ws2). {
          rewrite !length_app in H2. lia.
        }

        (* break apart the old has flags *)
        pose proof (Forall2_app_inv _ fs1 _ ws1 _ ltac:(lia) Hfswsmatch) as [Hfs1ws1 Hrest].
        pose proof (Forall2_app_inv _ fs_old _ ws_old _ ltac:(lia) Hrest) as [Hold Hfs2ws2].
        apply Forall2_app; [done | apply Forall2_app; [|done]].

        (* apply lemma for new section *)
        move Harepιsos2 at bottom.
        rewrite <- flat_map_concat_map.
        rewrite flat_map_concat_map.
        apply has_areps_imp_word_has_flag in Hareps as Hnew.
        eapply Forall2_impl; [exact Hnew|].
        intros f' w' Hwh; cbn in Hwh; apply Is_true_true; exact Hwh.
      }

      open_rt "Hrt".
      iAssert (⌜lm !! ℓ = Some new_fs⌝%I) with "[Hℓ_fs Hlayout]" as "%Hlmℓ". {
        iApply (ghost_map_lookup with "[$] [$]").
      }
      iAssert (⌜hm !! ℓ = Some new_ws⌝%I) with "[Hℓ_newws Hheap]" as "%Hhmℓ". {
        iApply (ghost_map_lookup with "[$] [$]").
      }
      assert (Hnewlayout: layout_ok lpall lm hm). {
        unfold layout_ok in *.
        unfold map_Forall2 in *.
        unfold rtmask in Hlayoutok.
        intros k.
        specialize (Hlayoutok k).
        destruct (decide (k=ℓ)); subst => //=.
        - rewrite Hlmℓ; rewrite Hhmℓ.
          constructor.
          intros.
          eapply Forall2_impl; [done|].
          intros f' w' Hwh; cbn in Hwh; apply Is_true_true; exact Hwh.
        - inversion Hlayoutok.
          + specialize (H4 n0); constructor; done.
          + constructor.
      }
      clear Hlayoutok. (* don't want to accidentally use it *)

      iAssert (rt_token rti sr lpall θ) with
        "[Haddr Hroot Hlayout Hheap Hrti Hownmm Howngc Hrootmem Hheapmem]" as "Hrt". {
        unfold rt_token.
        iExists rm, lm, hm.
        iFrame.
        done.
      }
      (* I don't think we wwant some of these pure things since we've closed rt_token *)
      clear dependent rm.
      clear dependent lm.
      clear dependent hm.
      clear Hinj.

      iFrame.

      (** ----- REESTABLISHING VALUE_INTERP AT THE END ------- *)

      (* frame interp and frame rel shouldn't be insane as I think *)
      (* they'll be preserved? we'll see *)
      iSplitR.
      - iPureIntro.
        unfold lmask.
        apply (frame_rel_trans lmask fr fr_saved fr_store).
        + unfold lmask.
          eapply frame_rel_mask_mono; [| exact Hfrel_fr_saved].
          intros i Hiwlmask.
          cbn.
          unfold wlmask in Hiwlmask.
          rewrite Hval_idxs_seq.
          intro Hin. apply elem_of_seq in Hin. lia.
        + unfold fr_store, lmask.
          unfold frame_rel.
          cbn.
          split; [|done].
          unfold mask_locs_eq.
          unfold wlmask.
          intros i [Hlo Hhi].
          symmetry.
          apply list_lookup_insert_ne.
          unfold ptr_local. rewrite length_app. subst fe. unfold fe_wlocal_offset in *. simpl in *. lia.
      - (* Here lies reestablishing value interp *)
        (* the resources used here is everything leftover (except old val):
           - ℓ ↦heap, ℓ ↦addr, ℓ↦layout
           - value_interp τ for new words
         *)
        iExists ([PtrA (PtrHeap MemMM ℓ)]).
        iEval (cbn).
        iSplitL "Hℓ_fs Hvalτ Hℓ_newws"; [|iSplitL; [|done]].
        + iExists [[PtrA (PtrHeap MemMM ℓ)]].
          iEval (cbn); iSplitR; [done|iSplitL;[|done]].
          rewrite type_interp_eq; iEval (cbn).
          rewrite evalμ.
          iEval (cbn).

          iExists (SVALTYPE [PtrR] ξ_ref).
          iSplitR; [done|].
          iSplitR.
          * iPureIntro.
            done. (* note: this won't be as clean in the GC case I think *)
          * iExists ℓ, _, _.
            iFrame.
            done.
        + iExists n, n32.
          iSplitR; [done| iSplitR; [done|]].
          iExists (RootHeap MemMM a).
          iSplitR; [done|].
          done.
    }










    [MemGC]: {
      (* note: this first set up has a lot of copying *)
      iEval (cbn) in "Ho1".
      iDestruct "Ho1" as "(%ℓ & %fs & %toinvert & Hτ)".
      inversion toinvert; subst; clear toinvert.
      iPoseProof (atom_interp_ptr_shaped with "Hv1") as
        "(%n & %n32 & %Hn32 & -> & %Hnshp & %rp & %Hreproot & Hv1)".
      apply has_values_app_inv in H0.
      destruct H0 as (ev1 & evs2 & -> & Hev1 & Hevs2).
      apply has_values_to_consts_inv in Hev1 as Hev1tosubst.
      cbn in Hev1tosubst; subst.

      (* Summary:
         - o1 became (PtrHeap MemGC ℓ), v1 became (VAL_int32 n32), ev1 became BI_const...
         - n32 is... the address associated with the pointer? Or at minimum it is the
           actual thing on the stack.
         - we also dug into the value interp of the reference, getting the following:
           + we got rp, the root pointer associated with ℓ, and a bunch of ℓ resources
             hidden underneath an invariant
           + we also got the type interpretation of the words sitting in memory under an
             invariant
       *)


      (** PUT FACTOIDS WE NEED HERE (THAT ARE MM/GC SPECIFIC) **)



      (** TIME TO BOOGIE *)

      (** SAVING STACK AND LOCAL TEE *)
      (* First, saving stack to clear evs2 and es_save *)

      (* apply lemma on the codegen. order of goals to help with evars *)
      iAssert (⌜has_areps ιs (SAtoms os2)⌝%I) with "[Hos2]" as "%Hareps2". {
        rewrite value_interp_eq.
        iEval (cbn -[pre_type_interp type_skind]) in "Hos2".
        iDestruct "Hos2" as "(%sκ_temp & %Htypeskindtemp & %Harepsoon & pre)".
        iPureIntro.
        rewrite Htypeskindτval in Htypeskindtemp.
        inversion Htypeskindtemp; subst.
        destruct Harepsoon as [H' _]; exact H'.
      }
      iDestruct (result_type_interp_of_atoms_interp with "Hvs2") as "%Hres_type_vs2"; [exact Hareps2|].
      eapply cwp_save_stack_w in Hsave; auto.
      4: exact Hevs2.
      3: {
        unfold translate_arep in Hres_type_vs2.
        by rewrite map_comp.
      }
      2: exact Hwl.
      destruct Hsave as (Hval_localidxs_seq & -> & Hwl_save & Hsave).

      (* now to use the facts we got *)
      rewrite (app_assoc _ es_save _).
      rewrite <- (app_assoc _ evs2 _).
      iApply (cwp_seq with "[Hfr Hrun]").
      {
        (* note: this is 100% copied from case.v lol *)
        (* it looks like this is all just related to cwp_save_stack so should be the same *)
        (* possibility of it being incorrect *)
        instantiate (1 := λ fr' vs, (
          ∃ val_idxs,
          ⌜vs = [VAL_int32 n32]⌝ ∗
          ⌜frame_rel (λ i, i ∉ val_idxs) fr fr'⌝ ∗
          ⌜Forall2 (fun i v => f_locs fr' !! localimm i = Some v) val_localidxs vs2⌝ ∗
          ⌜val_idxs = seq (fe_wlocal_offset fe + length wl) (length wl_save)⌝ ∗
          ⌜val_localidxs = map prelude.W.Mk_localidx val_idxs⌝
                                    )%I).
        iApply cwp_val_app; first done.
        iApply (Hsave with "[$] [$]").
        iIntros (f' [Hfsame Hfchanged]).
        unfold fvs_combine.
        subst val_localidxs wl_save.
        auto.
      }
      iIntros (fr_saved w) "(%val_idxs & -> & %Hfrel_fr_saved & %Hsaved & %Hval_idxs_seq & %Hval_localidxs) Hfr Hrun".
      clear Hsave.

      (* Next: local_tee stuff *)
      set (f' := ({|
                     W.f_locs :=
                       <[localimm (prelude.W.Mk_localidx ptr_local):=
                           VAL_int32 n32]> (f_locs fr_saved);
                     W.f_inst := f_inst fr_saved
                   |})) in *.
      rewrite (app_assoc (to_consts [VAL_int32 n32]) _ _).
      iApply (cwp_seq with "[Hfr Hrun]").
      {
        (* this is copied from load.v *)
        iApply (cwp_local_tee with "[] [$] [$]").
        - cbn.
          assert (ptr_local ∉ val_idxs) as Hnotinval. {
            rewrite Hval_idxs_seq.
            intro Hin. apply elem_of_seq in Hin.
            rewrite /ptr_local length_app /fe_wlocal_offset in Hin. subst fe. simpl in Hin. lia.
          }
          rewrite <- lookup_lt_is_Some.
          rewrite <- (proj1 Hfrel_fr_saved ptr_local Hnotinval).
          rewrite lookup_lt_is_Some.
          exact Hptrlocalfr.
        - now instantiate (1:= λ f'' v'', ⌜f'' = f' /\ v'' = [VAL_int32 n32]⌝%I).
      }
      iIntros (? ?) "(-> & ->) Hf Hrun".

      (* Summary:
         - Used up evs2 and es_save_stack and "put" the pointer in front of es_case_ptr block
         - Our frame changed twice: fr_saved is after saving the stack (so lots of things)
           got put into locals, and f' is after putting n32 into the local associated
           with the ptr.
         - We also got a bunch of val_indx stuffs everywhere

         Note: probably put lemmas and facts related to saving the stack here.
      *)


      (** CASE PTR TIME **)
      (* Apply the lemma into the codegen *)
      apply cwp_case_ptr in Hcompile.
      destruct Hcompile as
        (wt_unreach & wt_memMM & wt_memGC &
           wl_unreach & wl_memMM & wl_memGC &
           es_unreach & es_memMM & es_memGC & Hcompile).
      destruct Hcompile as
        (Hcg_unreach & Hcg_memMM & Hcg_memGC & -> & -> & Hcaseptr_spec).

      (* Specialize the spec with out variables *)
      specialize (Hcaseptr_spec [] []).
      specialize (Hcaseptr_spec (PtrHeap MemGC ℓ) n n32).
      specialize (Hcaseptr_spec ltac:(eauto) ltac:(auto) ltac:(auto) ltac:(auto)).
      clear_nils.

      (* A cwp_val_app, which I'm confused why it's on the stack at all but oh well *)
      iApply cwp_val_app; first done.
      unfold fvs_combine.

      (* Now we can cwp_seq and use the spec *)

      iApply (cwp_seq with "[-]").
      {
        iApply (Hcaseptr_spec with "[$] [$] [] [-]").
        { iPureIntro. cbn. apply list_lookup_insert_eq.
          assert (ptr_local ∉ val_idxs) as Hnotinval. {
            rewrite Hval_idxs_seq.
            intro Hin. apply elem_of_seq in Hin.
            rewrite /ptr_local length_app /fe_wlocal_offset in Hin. subst fe. simpl in Hin. lia.
          }
          rewrite <- lookup_lt_is_Some.
          rewrite <- (proj1 Hfrel_fr_saved ptr_local Hnotinval).
          rewrite lookup_lt_is_Some.
          exact Hptrlocalfr.
        }
        iModIntro. iIntros "Hfr Hrun".
        (* Decompose es_memGC into root_to_heap ([get_local; load; set_local]) + memory.store *)
        inv_cg_bind Hcg_memGC what_gc ?wt ?wt ?wl ?wl
          es_root_to_heap_gc es_store_gc Hcg_root_gc Hcg_store_gc.
        destruct what_gc.
        (* root_pointer_interp rp (PtrHeap MemGC ℓ) forces rp = RootHeap MemGC a_root *)
        destruct rp as [? | [|] a_root].
        { iEval (cbn) in "Hv1". iExFalso; iExact "Hv1". }
        { iEval (cbn) in "Hv1". iExFalso; iExact "Hv1". }
        (* Get root resources for wp_root_to_heap *)
        unfold rt_token.
        iDestruct "Hrt" as "(%rm_gc & %lm_gc & %hm_gc &
          Haddr_gc & Hroot_gc_auth & Hlayout_gc & Hheap_gc &
          Hrti_gc & %Hinj_gc & Hownmm_gc & Howngc_gc &
          %Hrootok_gc & Hrootmem_gc & %Hheapok_gc & Hheapmem_gc)".
        pose proof (wp_root_to_heap sr _ _ _ _ _ _ _ Hcg_root_gc) as Hrth_gc.
        specialize (Hrth_gc a_root n n32 ℓ θ rm_gc Hn32 Hreproot Hrootok_gc).
        (* Inner cwp_seq: split root_to_heap from memory.store *)
        iApply (cwp_seq with "[Hfr Hrun Hv1 Hroot_gc_auth Hrootmem_gc]").
        {
          iApply (Hrth_gc with "[$Hfr] [$Hrun] [] [] [$Hv1] [$Hroot_gc_auth] [$Hrootmem_gc]").
          - (* f'.f_locs !! ptr_local = Some (VAL_int32 n32) *)
            iPureIntro. cbn. apply list_lookup_insert_eq.
            assert (ptr_local ∉ val_idxs) as Hnotinval. {
              rewrite Hval_idxs_seq. intro Hin. apply elem_of_seq in Hin.
              rewrite /ptr_local length_app /fe_wlocal_offset in Hin. subst fe. simpl in Hin. lia.
            }
            rewrite <- lookup_lt_is_Some.
            rewrite <- (proj1 Hfrel_fr_saved ptr_local Hnotinval).
            rewrite lookup_lt_is_Some. exact Hptrlocalfr.
          - (* f'.f_inst = f_inst fr_saved = f_inst fr; extract GC mem idx from Hinst *)
            iDestruct "Hinst" as "(_ & _ & _ & _ & _ & %Hgcmem)".
            iPureIntro. cbn.
            rewrite <- (proj2 Hfrel_fr_saved).
            exact Hgcmem.
          - (* After root_to_heap: ptr_local holds the actual GC heap address ah32 *)
            iIntros "!>!>!>" (ah ah32) "%Hah32 %Hrepr_gc Hv1' Hroot_gc_auth' Hrootmem_gc'".
            instantiate (1 := λ f'' v'', (
              ⌜v'' = []⌝ ∗
              ∃ ah ah32,
              ⌜f''.(W.f_inst) = f_inst fr_saved⌝ ∗
              ⌜f''.(W.f_locs) !! ptr_local = Some (VAL_int32 ah32)⌝ ∗
              ⌜N_i32_repr ah ah32⌝ ∗
              ⌜repr_pointer θ (PtrHeap MemGC ℓ) ah⌝ ∗
              a_root ↦root ℓ ∗
              ghost_map_auth rw_root (1/2) rm_gc ∗
              root_memory sr θ rm_gc)%I).
            iSplit; first done.
            iExists ah, ah32.
            iSplit; first done.
            iSplit. { (* ptr_local is now ah32 in the new frame *)
              iPureIntro. cbn. apply list_lookup_insert_eq.
              rewrite length_insert.
              assert (ptr_local ∉ val_idxs) as Hnotinval. {
                rewrite Hval_idxs_seq. intro Hin. apply elem_of_seq in Hin.
                rewrite /ptr_local length_app /fe_wlocal_offset in Hin. subst fe. simpl in Hin. lia.
              }
              rewrite <- lookup_lt_is_Some.
              rewrite <- (proj1 Hfrel_fr_saved ptr_local Hnotinval).
              rewrite lookup_lt_is_Some. exact Hptrlocalfr.
            }
            iSplit; first done.
            iSplit; first done.
            iFrame.
        }
        iIntros (f'' v'')
          "(-> & %ah & %ah32 & %Hfinst & %Hflocs & %Hah32 & %Hrepr_gc & Hv1' & Hroot_gc_auth' & Hrootmem_gc')
           Hfr Hrun".
        (* Restore rt_token *)
        iAssert (rt_token rti sr lpall θ) with
          "[Haddr_gc Hroot_gc_auth' Hlayout_gc Hheap_gc Hrti_gc
            Hownmm_gc Howngc_gc Hrootmem_gc' Hheapmem_gc]" as "Hrt".
        { unfold rt_token. iExists rm_gc, lm_gc, hm_gc.
          iFrame. by iFrame (Hinj_gc Hrootok_gc Hheapok_gc).
        }
        iSimpl.
        admit.
      }
      iIntros (fr_store vs_store) "Hres Hfr Hrun".
      (* TODO: apply pointer flags spec, reestablish frame_rel and value_interp. *)
      admit.
    }


  Admitted.

End store_weak.
