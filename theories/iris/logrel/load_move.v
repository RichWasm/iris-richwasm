From mathcomp Require Import eqtype ssrbool.

From Stdlib Require Import NArith.NArith.
Require Import RichWasm.util.
Require Import RichWasm.compiler.memory.
Require Import RichWasm.iris.numerics.
Require Import RichWasm.iris.runtime.
Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.case_ptr.
Require Import RichWasm.iris.logrel.path.
Require Import RichWasm.iris.logrel.roots.
Require Import RichWasm.iris.logrel.load_common.
Require Import RichWasm.iris.logrel.virt_to_phys_strong.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section load_move.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma Forall_repeat {A} {P : A → Prop} n a :
    P a →
    Forall P (repeat a n).
  Proof.
    induction n; intros Hp.
    - done.
    - cbn.
      constructor; eauto.
  Qed.


  Lemma reconstitute_val_strong θ μ o ws off ι ns ns32 :
    "Hws" ∷ words_interp θ μ (get_path_words off (arep_size ι) ws) ns -∗
    "%Hbound" ∷ ⌜off + arep_size ι <= length ws⌝ -∗
    "%Harep" ∷ ⌜has_arep ι o⌝ -∗
    "%Hser" ∷ ⌜serialize_atom o = get_path_words off (arep_size ι) ws⌝ -∗
    "%Hns" ∷ ⌜Forall2 N_i32_repr ns ns32⌝ -∗
    ∃ v, ⌜flat_map serialise_i32 ns32 = bits v⌝ ∗
         atom_interp_weak θ μ o v ∗
         words_interp θ μ (map WordInt ns) ns.
  Proof.
    repeat iIntros "@".
    set (bs := flat_map serialise_i32 ns32).
    pose proof Hns as Hnslen.
    pose proof (has_arep_size ι o Harep) as Hreplen.
    apply Forall2_length in Hnslen.
    iPoseProof (big_sepL2_length with "Hws") as "%Hlenws".
    assert (length ns32 = length (get_path_words off (arep_size ι) ws)) as Hseglen;
      first by rewrite Hlenws.
    destruct o, ι; try elim Harep.
    - iExists (wasm_deserialise bs T_i32).
      iSplitR.
      {
        rewrite bits_deserialise; first done.
        rewrite len_ser32.
        rewrite Hseglen -Hser.
        by rewrite Hreplen.
      }
      cbn in Hbound.
      inversion Hser as [Hser'].
      cbn [arep_size] in *.
      rewrite -Hser'.
      rewrite -Hser' in Hlenws.
      destruct ns as [| n [| n' ns']]; cbn in Hlenws; try lia; clear Hlenws.
      destruct ns32 as [| n32 [| n32' ns32']]; cbn in Hnslen; try lia; clear Hnslen.
      inversion Hns as [|A B C D Hn _]; subst A B C D.
      setoid_rewrite big_sepL2_singleton.
      destruct μ; [destruct p; [| destruct μ]|];
        try solve [
          iDestruct "Hws" as "%Hrep";
          iPureIntro;
          intuition;
          exists n, n32; intuition eauto;
          cbn [bs flat_map];
          apply deserialise_serialise_i32
        ].
      all: cbn;
           iFrame.
      all: iSplitR; last done.
      all: iExists n32.
      all: iSplitR; first done.
      all: iPureIntro; cbn; clear_nils.
      all: apply deserialise_serialise_i32.
    - rewrite -Hser.
      rewrite -Hser in Hlenws; cbn in Hlenws.
      destruct ns as [| n' [| n'' ns']]; cbn in Hlenws; try lia; clear Hlenws.
      destruct ns32 as [| n32 [| n32' ns32']]; cbn in Hnslen; try lia; clear Hnslen.
      inversion Hns as [|A B C D Hn _]; subst A B C D.
      setoid_rewrite big_sepL2_singleton.
      iDestruct "Hws" as "%Hws".
      subst n'.
      iPureIntro.
      exists (wasm_deserialise bs T_i32).
      rewrite bits_deserialise; eauto.
      intuition.
      rewrite deserialise_serialise_i32.
      assert (N_i32_repr (Wasm_int.N_of_uint i32m n) n) by reflexivity.
      by erewrite (N_i32_repr_inj2 _ n32 n).
    - rewrite -Hser.
      rewrite -Hser in Hlenws; cbn in Hlenws.
      destruct ns as [| n' [| n'' [| n''' ns']]]; cbn in Hlenws; try lia; clear Hlenws.
      destruct ns32 as [| n32 [| n32' [| n32'' ns32']]]; cbn in Hnslen; try lia; clear Hnslen.
      inversion Hns as [|A B C D Hn [|A' B' C' D' Hn' _]]; subst.
      setoid_rewrite big_sepL2_cons.
      setoid_rewrite big_sepL2_cons.
      iDestruct "Hws" as "(%Hws1 & %Hws2 & _)".
      cbn.
      iPureIntro.
      exists (wasm_deserialise bs T_i64).
      intuition.
      + admit.
      + admit.
    - rewrite -Hser.
      rewrite -Hser in Hlenws; cbn in Hlenws.
      destruct ns as [| n' [| n'' ns']]; cbn in Hlenws; try lia; clear Hlenws.
      destruct ns32 as [| n32 [| n32' ns32']]; cbn in Hnslen; try lia; clear Hnslen.
      inversion Hns as [|A B C D Hn _]; subst A B C D.
      setoid_rewrite big_sepL2_singleton.
      iDestruct "Hws" as "%Hws".
      subst n'.
      iPureIntro.
      exists (wasm_deserialise bs T_f32).
      rewrite bits_deserialise; eauto.
      intuition.
      admit. (* need deser-ser lemma *)
    - rewrite -Hser.
      rewrite -Hser in Hlenws; cbn in Hlenws.
      destruct ns as [| n' [| n'' [| n''' ns']]]; cbn in Hlenws; try lia; clear Hlenws.
      destruct ns32 as [| n32 [| n32' [| n32'' ns32']]]; cbn in Hnslen; try lia; clear Hnslen.
      inversion Hns as [|A B C D Hn [|A' B' C' D' Hn' _]]; subst.
      setoid_rewrite big_sepL2_cons.
      setoid_rewrite big_sepL2_cons.
      iDestruct "Hws" as "(%Hws1 & %Hws2 & _)".
      cbn.
      iPureIntro.
      exists (wasm_deserialise bs T_f64).
      intuition.
      + admit.
      + admit.
  Admitted.

  Lemma types_agree_atom_interp ι o v :
    ι ≠ PtrR →
    types_agree (translate_arep ι) v →
    has_arep ι o →
    ⊢ atom_interp o v.
  Proof.
    intros Hcontra Hag Harep.
    destruct ι, o, v; try done; unfold atom_interp; cbn.
  Abort.

  Lemma wp_load1_move_mm (se : @semantic_env Σ) F lidx off ι wt wl ret wt' wl' es :
    let fe := fe_of_context F in
    run_codegen (memory.load1 mr fe MemMM Move lidx off ι) wt wl = inr (ret, wt', wl', es) ->
    ∀ f ℓ a32 a o ws s E B R θ lmask Φ,
    ⊢ "Hf" ∷ ↪[frame] f -∗
      "Hrun" ∷ ↪[RUN] -∗
      "Hptr" ∷ ℓ ↦heap ws -∗
      "Haddr" ∷ ℓ ↦addr (MemMM, a) -∗
      "Hown"  ∷ na_own logrel_nais E -∗
      "Htok"  ∷ rt_token rti sr lmask θ -∗
      "Hregf" ∷ instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
      "%Hℓmask"  ∷ ⌜¬ lmask ℓ⌝ -∗
      "%Hmask" ∷ ⌜↑ns_fun (N.of_nat (sr_func_registerroot sr)) ⊆ E⌝ -∗
      "%Hbound" ∷ ⌜off + arep_size ι ≤ length ws⌝ -∗
      "%Harep" ∷ ⌜has_arep ι o⌝ -∗
      "%Hser" ∷ ⌜serialize_atom o = get_path_words off (arep_size ι) ws⌝ -∗
      "%Hse" ∷ ⌜sem_env_interp F se⌝ -∗
      "%Hfsz" ∷ ⌜fe_wlocal_offset fe + length wl + length wl' <= length (f_locs f)⌝ -∗
      "%Hlidx" ∷ ⌜f_locs f !! localimm lidx = Some (VAL_int32 a32)⌝ -∗
      "%Hrepa" ∷ ⌜N_i32_repr (tag_address MemMM a) a32⌝ -∗
      "%Hrepa_mod" ∷ ⌜a `mod` 4 = 0⌝%N -∗
      "%Hrepa_nz" ∷ ⌜a ≠ 0⌝%N -∗
      "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemMM)⌝ -∗
      "%Hmemmm" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
      "%Hmemgc" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemGC = Some (sr_mem_gc sr)⌝ -∗
      "HΦ" ∷
        (∀ f' vf v ns',
           "%Hns'" ∷ ⌜length ns' = arep_size ι⌝ -∗
           "%Hf'"  ∷ ⌜f' = mk_load1_frame fe f (length wl) vf⌝ -∗
           "%Hvf"  ∷ ⌜types_agree (translate_arep ι) vf⌝ -∗
           "Hptr"  ∷ ℓ ↦heap update_path_words off ws (map WordInt ns') -∗
           "Haddr" ∷ ℓ ↦addr (MemMM, a) -∗
           "Hown"  ∷ na_own logrel_nais E -∗
           "Htok"  ∷ rt_token rti sr lmask θ -∗
           "Hregf" ∷ instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
           "Ho"    ∷ atom_interp o v -∗
           Φ f' [v]) -∗
      CWP es @ s; E UNDER B; R {{ Φ }}.
  Proof.
    unfold load1.
    intros Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_get ?es_rest Hget Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_load_w ?es_rest Hload_w Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_wlalloc ?es_rest Hwlalloc Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_save ?es_rest Hsave Hcompile.
    apply wp_wlalloc in Hwlalloc.
    destruct Hwlalloc as (Hidx & -> & -> & ->).
    eapply wp_load_w in Hload_w.
    destruct Hload_w as (_ & -> & -> & Hload_w).
    inversion Hidx; subst n; clear Hidx.
    inv_cg_emit Hget; subst.
    inv_cg_emit Hsave; subst.
    clear Hretval Hretval0.
    clear_nils.
    intros *.
    repeat iIntros "@".
    iApply (cwp_seq with "[Hf Hrun]").
    {
      iApply (cwp_local_get with "[] [$] [$]"); eauto.
      now instantiate (1:= λ f' v', ⌜f' = f /\ v' = [VAL_int32 a32]⌝%I).
    }
    iIntros (f' vs') "[-> ->] Hf Hrun".
    rewrite app_assoc.
    (* Opening virt resources *)
    iPoseProof (virt_to_phys_slice_store_acc_strong _ _ lmask off (arep_size ι) with "[//] [$] [$] [$] [//]")
      as "(%hm & %Hhm & %Hdomθhm & %Hlocsθ_ws & Hnp & (%ns & %ns32 & %Hns & Hphys & Hwords) & Hclose)".
    (* Opening word_interp *)
    iPoseProof (reconstitute_val_strong with "[$Hwords] [//] [//] [//] [//]") as "(%v & %Hserws & Hat & Hret)".
    rewrite !Hserws.
    set (PHYS := (rt_memaddr sr MemMM↦[wms][a + 4 * N.of_nat off]bits v)%I) in *.
    iPoseProof (atom_interp_weak_types_agree with "[//] [$Hat]") as "%Htag".
    iApply (cwp_seq with "[Hf Hrun Hphys]").
    {
      iApply (Hload_w with "[$] [$] [$]"); try done.
      instantiate (1 := λ f' v', (⌜f' = f⌝ ∗ ⌜v' = [v]⌝ ∗ PHYS)%I).
      eauto.
    }
    iIntros (? ?) "(-> & -> & Hphys) Hf Hrun".
    rewrite app_assoc.
    set (vloc := localimm (W.Mk_localidx (fe_wlocal_offset (fe_of_context F) + length wl))).
    set (f' := {| f_locs := <[vloc := v]> (f_locs f);
                  f_inst := f_inst f |}).
    iApply (cwp_seq with "[Hf Hrun]").
    {
      iApply (cwp_local_tee with "[] [$] [$]").
      - unfold vloc.
        cbn in *; lia.
      - now instantiate (1:= λ f'' v'', ⌜f'' = f' /\ v'' = [v]⌝%I).
    }
    iIntros (? ?) "(-> & ->) Hf Hrun".
    assert (length ns = arep_size ι) as Hlenns.
    {
      pose proof (length_bits v _ ltac:(eassumption)) as Hbits.
      rewrite length_t_translate_arep in Hbits.
      erewrite Forall2_length by eauto.
      rewrite -Hserws in Hbits.
      rewrite len_ser32 in Hbits.
      lia.
    }
    assert (off + length (map WordInt ns) ≤ length ws) as Hbdns.
    { rewrite length_map; lia. }
    pose proof (updating_words off (map WordInt ns) ws ltac:(assumption))
      as (ws_l & ws0 & ws_r & -> & Hupdate & Hlenws0 & Hlenws_l).
    iSpecialize ("Hclose" with "[] [] [] [] [Hphys] [Hret] [$Hnp]").
    { iPureIntro.
      instantiate (1:=(map WordInt ns)).
      rewrite length_map.
      done.
    }
    { iPureIntro. apply Hns. }
    { iPureIntro.
      revert Hlocsθ_ws.
      rewrite Hupdate !flat_map_app !Forall_app -Hdomθhm.
      intuition.
      replace (flat_map _ _) with (@nil location); first done.
      symmetry.
      rewrite flat_map_concat_map map_map map_const.
      eapply concat_nil_Forall.
      by apply Forall_repeat. }
    { iPureIntro.
      revert Hlocsθ_ws.
      rewrite Hupdate !flat_map_app !Forall_app.
      intuition.
      replace (flat_map _ _) with (@nil location); first done.
      symmetry.
      rewrite flat_map_concat_map map_map map_const.
      eapply concat_nil_Forall.
      by apply Forall_repeat. }
    { unfold PHYS. rewrite -Hserws.
      done. }
    { by iApply "Hret". }
    iApply fupd_cwp.
    iMod "Hclose" as "(Hhp & Haddr & Htok)".
    iModIntro.
    destruct (atomic_rep_eq_dec ι PtrR).
    + subst ι.
      destruct o; try (exfalso; tauto).
      iPoseProof (atom_interp_weak_ptr_shaped with "Hat") as "(%av & %av32 & -> & %Hav32 & %Hshp)".
      eapply wp_ite_gc_ptr_ptr with (evs:= to_consts [VAL_int32 av32]) (vs:=[VAL_int32 av32]) in Hcompile;
        [|by apply Is_true_true, has_values_to_consts| done | by eauto | eapply Hav32 ].
      destruct Hcompile as (?wt & ?wt & ?wt & ?wl & ?wl & ?wl & ?es & ?es & ?es & Hcompile).
      destruct Hcompile as (Hcg1 & Hcg2 & Hcg3 & Hwt7 & Hwl7 & Hes_rest2).
      iApply (Hes_rest2 with "[$] [$] []").
      { iPureIntro.
        rewrite list_lookup_insert_eq; first done.
        cbn in Hfsz; cbn; lia. }
      iIntros "!> Hf Hr".
      inv_cg_ret Hcg1.
      inv_cg_ret Hcg2.
      inv_cg_ret Hcg3.
      clear_nils.
      iAssert ((CWP to_consts [VAL_int32 av32] @ s; E UNDER []; R {{ f0; vs, Φ f0 vs }})%I) with "[-]" as "H";
        last (destruct p as [| [|]]; by iApply "H").
      iApply (cwp_val with "[$] [$]"); first (clear_nils; eauto using has_values_to_consts).
      iApply ("HΦ" with "[] [] [] [$] [$] [$] [$] [$] [-]").
      - done.
      - unfold f', mk_load1_frame.
        unfold vloc.
        iPureIntro; done.
      - done.
      - iDestruct "Hat" as "(%n & %n32 & %Hn32 & -> & Hat)".
        iExists n, n32.
        repeat (iSplit; first done).
        destruct p; iRevert "Hat".
        * iIntros "%Hat".
          iExists (RootInt n0).
          iSplit; auto.
          iPureIntro.
          inversion Hat; subst; eauto.
          by constructor.
        * destruct μ; cbn.
          -- iIntros "(%rp & %Hat & Hℓ_addr)".
             inversion Hat; subst.
             iExists (RootHeap MemMM rp).
             cbn.
             iFrame.
             done. (* NOTE: addr used here, no longer missing *)
          -- iIntros "(%ah & %Hroot & Hroot)".
             iExists (RootHeap MemGC ah).
             iFrame.
             iPureIntro.
             inversion Hroot.
             by constructor.
    + eapply wp_ite_gc_ptr_nonptr in Hcompile; last assumption.
      inv_cg_ret Hcompile; subst; clear_nils.
      iApply (cwp_val with "[$] [$]"); first eauto using has_values_to_consts.
      iApply ("HΦ" with "[] [] [] [$] [$] [$] [$] [$] [Hat]").
      * done.
      * eauto.
      * done.
      * destruct ι, o, v; done.
  Qed.

  Lemma wp_mem_load_move_inner ιs :
    ∀ (se : @semantic_env Σ) F lidx off wt wl ret wt' wl' es,
    let fe := fe_of_context F in
      run_codegen
        (foldlM
           (λ off' ι, load1 mr fe MemMM Move lidx off' ι;; Monad.ret (off' + arep_size ι))
           off ιs)
        wt wl = inr (ret, wt', wl', es) →
    let offs := snd $ seq.foldl (λ '(off', offs) ι, (off' + arep_size ι, seq.rcons offs off'))
                  (off, []) ιs in
    let offs_szs := seq.zip offs (map arep_size ιs) in
    ret = seq.foldl (λ off' ι, off' + arep_size ι) off ιs ∧
    wt' = [] ∧
    wl' = map translate_arep ιs ∧
    ∀ f ℓ a32 a os ws E B R θ lmask Φ,
    ⊢ "Hf" ∷ ↪[frame] f -∗
      "Hrun" ∷ ↪[RUN] -∗
      "Hptr" ∷ ℓ ↦heap ws -∗
      "Haddr" ∷ ℓ ↦addr (MemMM, a) -∗
      "%Hℓmask"  ∷ ⌜¬ lmask ℓ⌝ -∗
      "Hown"  ∷ na_own logrel_nais E -∗
      "Htok"  ∷ rt_token rti sr lmask θ -∗
      "Hregf" ∷ instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
      "%Hmask" ∷ ⌜↑ns_fun (N.of_nat (sr_func_registerroot sr)) ⊆ E⌝ -∗
      "%Hbound" ∷ ⌜off + sum_list_with arep_size ιs ≤ length ws⌝ -∗
      "%Harep" ∷ ⌜Forall2 has_arep ιs os⌝ -∗
      "%Hser" ∷ ⌜Forall2 (λ o '(off, sz), serialize_atom o = get_path_words off sz ws) os offs_szs⌝ -∗
      "%Hse" ∷ ⌜sem_env_interp F se⌝ -∗
      "%Hfsz" ∷ ⌜fe_wlocal_offset fe + length wl + length wl' <= length (f_locs f)⌝ -∗
      "%Hlidx" ∷ ⌜f_locs f !! localimm lidx = Some (VAL_int32 a32)⌝ -∗
      "%Hlidx_bdd" ∷ ⌜localimm lidx < fe_wlocal_offset fe + length wl⌝ -∗
      "%Hrepa" ∷ ⌜N_i32_repr (tag_address MemMM a) a32⌝ -∗
      "%Hrepa_mod" ∷ ⌜a `mod` 4 = 0⌝%N -∗
      "%Hrepa_nz" ∷ ⌜a ≠ 0⌝%N -∗
      "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemMM)⌝ -∗
      "%Hmemmm" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
      "%Hmemgc" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemGC = Some (sr_mem_gc sr)⌝ -∗
      "HΦ" ∷
        (∀ f' vs vsf ns',
           "Hptr"  ∷ ℓ ↦heap update_path_words off ws (map WordInt ns') -∗
           "Haddr" ∷ ℓ ↦addr (MemMM, a) -∗
           "Hown"  ∷ na_own logrel_nais E -∗
           "Htok"  ∷ rt_token rti sr lmask θ -∗
           "Hregf" ∷ instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
           "Hos"    ∷ ([∗ list] o;v ∈ os; vs, atom_interp o v) -∗
           "%Hns'" ∷ ⌜length ns' = areps_size ιs⌝ -∗
           "%Hf'"  ∷ ⌜f' = mk_load_frame fe f wl vsf⌝ -∗
           "%Hvsf" ∷ ⌜Forall2 (λ ι vf, types_agree (translate_arep ι) vf) ιs vsf⌝ -∗
           Φ f' vs) -∗
      CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
    induction ιs as [| ιs ι] using seq.last_ind; intros * Hcg *.
    - cbn in Hcg.
      inversion Hcg; subst ret wt' wl' es.
      repeat (split; first done).
      intros *.
      repeat iIntros "@".
      iApply (cwp_nil with "[$] [$]").
      inversion Harep; subst.
      iApply ("HΦ" $! f [] [] [] with "[Hptr] [$Haddr] [$Hown] [$Htok] [$Hregf] [$]"); try done; [].
      by rewrite update_path_words_empty_2.
    - apply inv_foldlM_rcons in Hcg.
      destruct Hcg as (n & ?wt & ?wt & ?wl & ?wl & es_fold & es_load & Hfold & Hload & -> & -> & ->).
      inv_cg_bind Hload ?ret ?wt ?wt ?wl ?wl es_load1 ?es_rest Hload1 Hret.
      inv_cg_ret Hret; subst; clear_nils.
      pose proof (IHιs se _ _ _ _ _ _ _ _ _ Hfold) as (-> & -> & -> & IHspec).
      pose proof (wp_mem_load1_cg_state rti sr mr _ _ _ _ _ _ _ _ _ _ _ _ Hload1) as (-> & -> & ->).
      split.
      { by rewrite seq.foldl_rcons. }
      split.
      { done. }
      split.
      { by rewrite rcons_app map_app. }
      intros *.
      repeat iIntros "@".
      apply Forall2_rcons_inv_l in Harep.
      destruct Harep as (o & os' & Ho & Hos & ->).
      rename os' into os.

      iApply (cwp_seq with "[-HΦ]").
      {
        apply Forall2_rcons_inv_l in Hser.
        destruct Hser as ([off' sz'] & offs_szs' & Hoffsz & Hser' & Hoffs_szs).
        rename Hser' into Hser.
        iPoseProof (IHspec with "[$] [$] [$] [$] [//] [$] [$] [$] [//]") as "IH".
        iApply "IH"; try done.
        - iPureIntro.
          rewrite sum_list_with_rcons in Hbound.
          lia.
        - iPureIntro.
          unfold offs_szs, offs in Hoffs_szs.
          rewrite seq.foldl_rcons in Hoffs_szs.
          rewrite -> seq.map_rcons in Hoffs_szs.
          destruct (seq.foldl (λ '(off', offs) (ι : atomic_rep), (off' + arep_size ι, seq.rcons offs off')) (
                        off, []) ιs) as [off0 offs0] eqn:Heqfold.
          assert (seq.size offs0 = seq.size (seq.map arep_size ιs)).
          {
            erewrite load_fold_offs_len ; eauto.
            change @seq.size with @length.
            change @seq.map with @map.
            rewrite length_map.
            by apply Nat.add_0_r.
          }
          cbn in Hoffs_szs.
          rewrite seq.zip_rcons in Hoffs_szs; last done.
          eapply seq.rcons_inj in Hoffs_szs.
          inversion Hoffs_szs; subst.
          apply Hser.
        - rewrite length_app in Hfsz; cbn in Hfsz.
          iPureIntro.
          cbn.
          lia.
        - iIntros (f' vs' vsf' ns').
          repeat iIntros "@".
          instantiate (1 :=
            (λ f' vs',
              ∃ vsf' ns',
                ⌜f' = mk_load_frame (fe_of_context F) f wl vsf'⌝ ∗
                ([∗ list] o;v ∈ os;vs', atom_interp o v) ∗
                ⌜Forall2 (λ (ι : atomic_rep) (vf : value), types_agree (translate_arep ι) vf) ιs vsf'⌝ ∗
                "Hptr" ∷ ℓ ↦heap update_path_words off ws (map WordInt ns') ∗
                "%Hns'" ∷ ⌜length ns' = areps_size ιs⌝ ∗
                ?[Q])%I).
          iExists vsf'.
          iFrame.
          iSplitR; first done.
          iSplitR; first done.
          iSplitR; first done.
          iNamedAccu.
      }
      iIntros (f' vs') "(%vsf' & %ns' & -> & Hats & %Htys & Hrest) Hf Hr".
      repeat iDestruct "Hrest" as "[@ Hrest]"; iDestruct "Hrest" as "@".
      iApply cwp_val_app; first apply has_values_to_consts.
      iApply (wp_load1_move_mm with "[$] [$] [$] [$] [$] [$] [Hregf] [//] [//] []");
        first eassumption;
        try done.
      + by rewrite load_frame_inst.
      + rewrite simple_fold_sum_list_with.
        iPureIntro.
        rewrite sum_list_with_rcons in Hbound.
        rewrite update_path_words_size; first lia.
        rewrite length_map Hns'.
        unfold areps_size.
        cbn.
        rewrite -sum_list_with_list_sum.
        lia.
      + iPureIntro.
        rewrite simple_fold_sum_list_with.
        unfold offs_szs, offs in Hser.
        rewrite seq.foldl_rcons in Hser.
        destruct (seq.foldl (λ '(off', offs) (ι : atomic_rep), (off' + arep_size ι, seq.rcons offs off')) (off, []) ιs) as [off' offs'] eqn:Hfold'.
        cbn in Hser.
        change @map with @seq.map in Hser.
        rewrite seq.map_rcons in Hser.

        assert (seq.size offs' = seq.size (seq.map arep_size ιs)).
        { erewrite load_fold_offs_len; eauto.
          cbn.
          rewrite seq.size_map.
          change @seq.size with @length.
          lia. }

        assert (off + length (map WordInt ns') ≤ length ws).
        {
          rewrite length_map Hns'.
          rewrite sum_list_with_rcons sum_list_with_list_sum in Hbound.
          unfold areps_size; cbn; lia.
        }
        pose proof (updating_words off (map WordInt ns') ws ltac:(auto))
          as (ws_l & ws0 & ws_r & -> & Hupdate & Hlen0 & Hlen_l).
        rewrite seq.zip_rcons in Hser; last done.
        rewrite !rcons_app in Hser.
        apply Forall2_app_inv in Hser.
        {
          destruct Hser as [Hsers Hser].
          inversion Hser; subst.
          rewrite H4.
          rewrite Hupdate.
          unfold get_path_words.
          rewrite !app_assoc.
          erewrite <- (simple_fold_fancy_fold rti sr mr ιs off'); last by eauto.
          rewrite simple_fold_sum_list_with.
          rewrite !drop_app_length'; first done.
          {
            rewrite !length_app !length_map.
            rewrite sum_list_with_list_sum.
            unfold areps_size in Hns'; cbn in Hns'.
            congruence.
          }
          {
            rewrite !length_app Hlen0 !length_map.
            rewrite sum_list_with_list_sum.
            unfold areps_size in Hns'; cbn in Hns'.
            congruence.
          }
        }
        apply Forall2_length in Hser.
        rewrite !length_app in Hser; cbn in Hser; lia.
      + iPureIntro.
        rewrite !length_app !length_map; cbn.
        rewrite !length_app !length_map in Hfsz; cbn in Hfsz.
        rewrite load_frame_length.
        lia.
      + iPureIntro.
        by rewrite mk_load_frame_stable_part.
      + by rewrite load_frame_inst.
      + by rewrite load_frame_inst.
      + iIntros (f' vf' v' ns'').
        repeat iIntros "@".
        iApply ("HΦ" with "[Hptr] [Haddr] [$Hown] [$Htok] [Hregf] [Hats Ho] [] [] []").
        * by erewrite update_update_wordint.
        * done.
        * by rewrite load_frame_inst.
        * rewrite rcons_app.
          iApply (big_sepL2_app with "[Hats]"); iFrame.
          done.
        * iPureIntro.
          rewrite length_app rcons_app Hns' Hns'0.
          unfold areps_size, compose.
          rewrite map_app list_sum_app.
          cbn.
          lia.
        * rewrite length_app length_map in Hf'.
          pose proof (Forall2_length _ _ _ Htys) as Hvsflen.
          rewrite Hvsflen in Hf'.
          rewrite mk_frame_rcons in Hf'; eauto.
        * iPureIntro.
          rewrite rcons_app.
          apply Forall2_app; first done.
          by constructor.
  Qed.

  Lemma wp_mem_load_move (se : @semantic_env Σ) F lidx off ιs wt wl ret wt' wl' es :
    let fe := fe_of_context F in
    run_codegen (memory.load mr fe MemMM Move lidx off ιs) wt wl = inr (ret, wt', wl', es) →
    let offs := snd $ seq.foldl (λ '(off', offs) ι, (off' + arep_size ι, seq.rcons offs off'))
                  (off, []) ιs in
    let offs_szs := seq.zip offs (map arep_size ιs) in
    ret = () /\
    wt' = [] ∧
    wl' = map translate_arep ιs ∧
    ∀ f ℓ a32 a os ws E B R θ lmask Φ,
    ⊢ "Hf" ∷ ↪[frame] f -∗
      "Hrun" ∷ ↪[RUN] -∗
      "Hptr" ∷ ℓ ↦heap ws -∗
      "Haddr" ∷ ℓ ↦addr (MemMM, a) -∗
      "%Hℓmask"  ∷ ⌜¬ lmask ℓ⌝ -∗
      "Hown"  ∷ na_own logrel_nais E -∗
      "Htok"  ∷ rt_token rti sr lmask θ -∗
      "Hregf" ∷ instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
      "%Hmask" ∷ ⌜↑ns_fun (N.of_nat (sr_func_registerroot sr)) ⊆ E⌝ -∗
      "%Hbound" ∷ ⌜off + sum_list_with arep_size ιs ≤ length ws⌝ -∗
      "%Harep" ∷ ⌜Forall2 has_arep ιs os⌝ -∗
      "%Hser" ∷ ⌜Forall2 (λ o '(off, sz), serialize_atom o = get_path_words off sz ws) os offs_szs⌝ -∗
      "%Hse" ∷ ⌜sem_env_interp F se⌝ -∗
      "%Hfsz" ∷ ⌜fe_wlocal_offset fe + length wl + length wl' <= length (f_locs f)⌝ -∗
      "%Hlidx" ∷ ⌜f_locs f !! localimm lidx = Some (VAL_int32 a32)⌝ -∗
      "%Hlidx_bdd" ∷ ⌜localimm lidx < fe_wlocal_offset fe + length wl⌝ -∗
      "%Hrepa" ∷ ⌜N_i32_repr (tag_address MemMM a) a32⌝ -∗
      "%Hrepa_mod" ∷ ⌜a `mod` 4 = 0⌝%N -∗
      "%Hrepa_nz" ∷ ⌜a ≠ 0⌝%N -∗
      "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemMM)⌝ -∗
      "%Hmemmm" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
      "%Hmemgc" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemGC = Some (sr_mem_gc sr)⌝ -∗
      "HΦ" ∷
        (∀ f' vs vsf ns',
           "%Hns'" ∷ ⌜length ns' = areps_size ιs⌝ -∗
           "%Hf'"  ∷ ⌜f' = mk_load_frame fe f wl vsf⌝ -∗
           "%Hvsf" ∷ ⌜Forall2 (λ ι vf, types_agree (translate_arep ι) vf) ιs vsf⌝ -∗
           "Hptr"  ∷ ℓ ↦heap update_path_words off ws (map WordInt ns') -∗
           "Haddr" ∷ ℓ ↦addr (MemMM, a) -∗
           "Hown"  ∷ na_own logrel_nais E -∗
           "Htok"  ∷ rt_token rti sr lmask θ -∗
           "Hregf" ∷ instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
           "Hos"    ∷ ([∗ list] o;v ∈ os; vs, atom_interp o v) -∗
           Φ f' vs) -∗
      CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
    iIntros (? Hcg ? ?).
    apply wp_ignore in Hcg.
    destruct Hcg as (-> & ret' & Hcg).
    pose proof (wp_mem_load_move_inner _ se _ _ _ _ _ _ _ _ _ Hcg)
     as (-> & -> & -> & Hspec).
    split; first done.
    split; first done.
    split; first done.
    intros *.
    repeat iIntros "@".
    iPoseProof Hspec as "Hspec".
    repeat iSpecialize ("Hspec" with "[$]").
    repeat iSpecialize ("Hspec" with "[//]").
    repeat iSpecialize ("Hspec" with "[$]").
    iApply "Hspec"; eauto.
    iIntros (f' vs' vsf' ns').
    repeat iIntros "@".
    iApply ("HΦ" with "[//] [//] [//] [$] [$] [$] [$] [$] [$]").
  Qed.


  (* --------------------- LOAD MOVE GC ----------------------- *)

  Lemma wp_load1_move_gc (se : @semantic_env Σ) F lidx off ι wt wl ret wt' wl' es :
    let fe := fe_of_context F in
    run_codegen (memory.load1 mr fe MemGC Move lidx off ι) wt wl = inr (ret, wt', wl', es) ->
    ∀ f ℓ a32 a o ws s E B R θ lmask Φ,
    ⊢ "Hf" ∷ ↪[frame] f -∗
      "Hrun" ∷ ↪[RUN] -∗
      "Hptr" ∷ ℓ ↦heap ws -∗
      "%Haddr" ∷ ⌜θ !! ℓ = Some (MemGC, a)⌝ -∗
      "Hown"  ∷ na_own logrel_nais E -∗
      "Htok"  ∷ rt_token rti sr lmask θ -∗
      "Hregf" ∷ instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
      "%Hℓmask" ∷ ⌜¬ lmask ℓ ⌝ -∗
      "%Hmask" ∷ ⌜↑ns_fun (N.of_nat (sr_func_registerroot sr)) ⊆ E⌝ -∗
      "%Hbound" ∷ ⌜off + arep_size ι ≤ length ws⌝ -∗
      "%Harep" ∷ ⌜has_arep ι o⌝ -∗
      "%Hser" ∷ ⌜serialize_atom o = get_path_words off (arep_size ι) ws⌝ -∗
      "%Hse" ∷ ⌜sem_env_interp F se⌝ -∗
      "%Hfsz" ∷ ⌜fe_wlocal_offset fe + length wl + length wl' <= length (f_locs f)⌝ -∗
      "%Hlidx" ∷ ⌜f_locs f !! localimm lidx = Some (VAL_int32 a32)⌝ -∗
      "%Hrepa" ∷ ⌜N_i32_repr (tag_address MemGC a) a32⌝ -∗
      "%Hrepa_mod" ∷ ⌜a `mod` 4 = 0⌝%N -∗
      "%Hrepa_nz" ∷ ⌜a <> 0⌝%N -∗
      "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemMM)⌝ -∗
      "%Hmemmm" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
      "%Hmemgc" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemGC = Some (sr_mem_gc sr)⌝ -∗
      "HΦ" ∷ ▷ (∀ f' vf v ns',
           "%Hns'" ∷ ⌜length ns' = arep_size ι⌝ -∗
           "%Hf'"  ∷ ⌜f' = mk_load1_frame fe f (length wl) vf⌝ -∗
           "%Hvf"  ∷ ⌜types_agree (translate_arep ι) vf⌝ -∗
           "Hptr"  ∷ ℓ ↦heap update_path_words off ws (map WordInt ns') -∗
           "Hown"  ∷ na_own logrel_nais E -∗
           "Htok"  ∷ rt_token rti sr lmask θ -∗
           "Hregf" ∷ instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
           "Ho"    ∷ atom_interp o v -∗
           Φ f' [v]) -∗
      CWP es @ s; E UNDER B; R {{ Φ }}.
  Proof.
    iIntros (fe Hcg).
    unfold load1.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_get ?es_rest Hget Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_load_w ?es_rest Hload_w Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_wlalloc ?es_rest Hwlalloc Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_save es_if Hsave Hcg.
    destruct ret.
    inversion Hget; subst; clear Hget.
    apply wp_load_w in Hload_w.
    destruct Hload_w as (_ & -> & -> & Hload_w).
    apply wp_wlalloc in Hwlalloc.
    destruct Hwlalloc as (Hidx & -> & -> & ->).
    inversion Hidx; subst n; clear Hidx.
    inversion Hsave; subst; clear Hsave.
    clear_nils.
    intros *.
    repeat iIntros "@".
    iApply (cwp_seq with "[Hf Hrun]").
    {
      iApply (cwp_local_get with "[] [$] [$]"); eauto.
      by instantiate (1 := λ f' v', (⌜f' = f⌝ ∗ ⌜v' = [VAL_int32 a32]⌝)%I).
    }
    iIntros (f' vs) "[-> ->] Hf Hr".
    iEval (rewrite app_assoc).
    (* Converting virtual resources to physical ones *)
    iPoseProof ( virt_to_phys_slice_store_acc_strong_gc rti sr lmask off (arep_size ι)
                 with "[//] [$] [$] [//] [//]")
      as "(%hm & %Hhm & %Hdomθhm & %Hlocsθ_ws & Hnp &
          (%ns & %ns32 & %Hns & Hphys & Hwords) & Hclose)".
    (* Opening word_interp *)
    iPoseProof (reconstitute_val_strong with "[$Hwords] [//] [//] [//] [//]")
      as "(%v & %Hserws & Hat & Hret)".
    rewrite !Hserws.
    set (PHYS := (rt_memaddr sr MemGC↦[wms][a + 4 * N.of_nat off]bits v)%I) in *.
    iPoseProof (atom_interp_weak_types_agree with "[//] [$Hat]") as "%Htag".
    iApply (cwp_seq with "[Hf Hr Hphys]").
    {
      iApply (Hload_w with "[$] [$] [$]"); try done.
      instantiate (1 := λ f' v', (⌜f' = f⌝ ∗ ⌜v' = [v]⌝ ∗ PHYS)%I).
      eauto.
    }
    iIntros (? ?) "(-> & -> & Hphys) Hf Hrun".
    rewrite app_assoc.
    set (vloc := localimm (W.Mk_localidx (fe_wlocal_offset (fe_of_context F) + length wl))).
    set (f' := {| f_locs := <[vloc := v]> (f_locs f);
                  f_inst := f_inst f |}).
    (* Including HΦ here so we can peel a later off of it. *)
    iApply (cwp_seq with "[Hf Hrun HΦ]").
    {
      iApply (cwp_local_tee with "[HΦ] [$] [$]").
      - unfold vloc.
        cbn in *; lia.
      - iModIntro.
        instantiate (1:= λ f'' v'', (⌜f'' = f' /\ v'' = [v]⌝ ∗ _)%I).
        iSplit; first done.
        iApply "HΦ".
    }
    iIntros (? ?) "((-> & ->) & HΦ) Hf Hrun".

    (* factsssss *)
    assert (length ns = arep_size ι) as Hlenns.
    {
      pose proof (length_bits v _ ltac:(eassumption)) as Hbits.
      rewrite length_t_translate_arep in Hbits.
      erewrite Forall2_length by eauto.
      rewrite -Hserws in Hbits.
      rewrite len_ser32 in Hbits.
      lia.
    }
    assert (off + length (map WordInt ns) ≤ length ws) as Hbdns.
    { rewrite length_map; lia. }
    pose proof (updating_words off (map WordInt ns) ws ltac:(assumption))
      as (ws_l & ws0 & ws_r & -> & Hupdate & Hlenws0 & Hlenws_l).

    destruct (atomic_rep_eq_dec ι PtrR).
    - subst ι.
      destruct o; try (exfalso; tauto).
      iPoseProof (atom_interp_weak_ptr_shaped with "Hat") as
        "(%pn & %pn32 & -> & %Hpn32 & %Hshp)".
      eapply wp_ite_gc_ptr_ptr with (evs:= to_consts [VAL_int32 pn32]) (vs:=[VAL_int32 pn32]) in Hcg;
        [|by apply Is_true_true, has_values_to_consts|done|done|done].
      destruct Hcg as (?wt & ?wt & ?wt & ?wl & ?wl & ?wl & ?es & ?es & ?es & Hcompile).
      destruct Hcompile as (Hcg1 & Hcg2 & Hcg3 & Hwt7 & Hwl7 & Hes_rest2).
      iApply (Hes_rest2 with "[$] [$] []").
      {
        iPureIntro; cbn.
        rewrite list_lookup_insert.
        rewrite decide_True; auto.
        split; first done.
        cbn in Hfsz.
        subst.
        rewrite !length_app in Hfsz.
        eapply Nat.lt_le_trans; last apply Hfsz.
        lia.
      }
      iIntros "!> Hf Hrun".
      subst wt7 wl7.
      inv_cg_ret Hcg1.
      inv_cg_ret Hcg2.
      clear_nils.
      inversion Hshp; subst; last destruct μ eqn:?.
      + iApply fupd_cwp.
        iApply (cwp_val with "[$] [$]"); eauto using has_values_to_consts.
        iAssert (atom_interp (PtrA (PtrInt n)) (VAL_int32 pn32)) as "Hat'".
        {
          subst.
          iExists (2 * n)%N, pn32.
          repeat iSplit; try done.
          iExists (RootInt n).
          iSplit; eauto.
          iPureIntro; constructor.
        }
        iSpecialize ("Hclose" $! (map WordInt ns) ns ns32).
        iSpecialize ("Hclose" with "[%] [//] [%] [%] [Hphys] [$] [$]").
        { by rewrite length_map. }
        {
          revert Hlocsθ_ws.
          rewrite Hupdate !flat_map_app !Forall_app -Hdomθhm.
          intuition.
          replace (flat_map _ _) with (@nil location); first done.
          symmetry.
          rewrite flat_map_concat_map map_map map_const.
          eapply concat_nil_Forall.
          by apply Forall_repeat.
        }
        {
          revert Hlocsθ_ws.
          rewrite Hupdate !flat_map_app !Forall_app.
          intuition.
          replace (flat_map _ _) with (@nil location); first done.
          symmetry.
          rewrite flat_map_concat_map map_map map_const.
          eapply concat_nil_Forall.
          by apply Forall_repeat.
        }
        { unfold PHYS. rewrite -Hserws. done. }

        iMod "Hclose" as "(Hhp & Htok)".
        iModIntro.

        iApply ("HΦ" with "[//] [//] [//] [$] [$] [$] [$] [$]").
      + iApply fupd_cwp.
        iApply (cwp_val with "[$] [$]"); eauto using has_values_to_consts.
        iAssert (atom_interp (PtrA (PtrHeap MemMM ℓ0)) (VAL_int32 pn32)) with "[Hat]"
          as "Hat'".
        {
          subst; cbn.
          iExists (tag_address MemMM a0), pn32.
          repeat iSplit; try done.
          iExists (RootHeap MemMM a0).
          iSplitR; first (iPureIntro; constructor; auto).
          iDestruct "Hat" as "(%n' & %n32' & %nreprtoinv & %toinv & (%a' & %hrepra' & Haddr))".
          inversion toinv; subst n32'.
          assert (tag_address MemMM a0 = n') by (eapply N_i32_repr_inj; done).
          subst n'.
          inversion hrepra'; subst.
          assert (a' = a0). {
            admit. (* number stuff *)
          }
          subst a'.
          done.
        }
        iSpecialize ("Hclose" $! (map WordInt ns) ns ns32).
        iSpecialize ("Hclose" with "[%] [//] [%] [%] [Hphys] [$] [$]").
        { by rewrite length_map. }
        {
          revert Hlocsθ_ws.
          rewrite Hupdate !flat_map_app !Forall_app -Hdomθhm.
          intuition.
          replace (flat_map _ _) with (@nil location); first done.
          symmetry.
          rewrite flat_map_concat_map map_map map_const.
          eapply concat_nil_Forall.
          by apply Forall_repeat.
        }
        {
          revert Hlocsθ_ws.
          rewrite Hupdate !flat_map_app !Forall_app.
          intuition.
          replace (flat_map _ _) with (@nil location); first done.
          symmetry.
          rewrite flat_map_concat_map map_map map_const.
          eapply concat_nil_Forall.
          by apply Forall_repeat.
        }
        { unfold PHYS. rewrite -Hserws. done. }

        iMod "Hclose" as "(Hhp & Htok)".
        iModIntro.

        iApply ("HΦ" with "[//] [//] [//] [$] [$] [$] [$] [$]").
      + (* GC case. Register root time *)
        apply (wp_registerroot rti sr mr) in Hcg3.
        destruct Hcg3 as (_ & -> & -> & Hreg_spec).

        (* I need to use Hclose now in order to get the rt token out *)
        iApply fupd_cwp.
        iSpecialize ("Hclose" $! (map WordInt ns) ns ns32).
        iSpecialize ("Hclose" with "[%] [//] [%] [%] [Hphys] [$] [$]").
        { by rewrite length_map. }
        {
          revert Hlocsθ_ws.
          rewrite Hupdate !flat_map_app !Forall_app -Hdomθhm.
          intuition.
          replace (flat_map _ _) with (@nil location); first done.
          symmetry.
          rewrite flat_map_concat_map map_map map_const.
          eapply concat_nil_Forall.
          by apply Forall_repeat.
        }
        {
          revert Hlocsθ_ws.
          rewrite Hupdate !flat_map_app !Forall_app.
          intuition.
          replace (flat_map _ _) with (@nil location); first done.
          symmetry.
          rewrite flat_map_concat_map map_map map_const.
          eapply concat_nil_Forall.
          by apply Forall_repeat.
        }
        { unfold PHYS. rewrite -Hserws. done. }

        iMod "Hclose" as "(Hhp & Htok)".
        iModIntro.

        iAssert (⌜θ !! ℓ0 = Some (MemGC, a0)⌝%I) with "[Hat]" as "%ℓ0θ". {
          cbn.
          iDestruct "Hat" as "(%n' & %n32' & %nrepr' & %toinv & %repr')".
          iPureIntro.
          inversion toinv; subst n32'.
          assert (tag_address MemGC a0 = n') by (eapply N_i32_repr_inj; done).
          subst n'.
          inversion repr'; subst.
          subst.
          assert (a1 = a0). {
            admit. (* number stuff *)
          }
          subst a0.
          done.
        }

        iApply (Hreg_spec with "[Hat HΦ Hhp] [$] [$] [//] [$] [$] [$]").
        3: by (apply Is_true_true; apply has_values_to_consts).
        2: done.
        {
          instantiate (1:=ℓ0).
          constructor; try done.
        }

        iIntros (ar ar32) "%Hreprroot Har_root Hrt Hown %Hi32reprroot Hreg".

        (* finally atom_interp *)
        iAssert (atom_interp (PtrA (PtrHeap MemGC ℓ0)) (VAL_int32 ar32))
          with "[Hat Har_root]"
          as "Hat'".
        {
          subst; cbn.
          iDestruct "Hat" as "(%n' & %n32' & %nrepr' & %toinv & %reprptr)".
          inversion toinv; subst n32'; clear toinv.
          move Hpn32 at bottom. move Hshp at bottom.
          assert (tag_address MemGC a0 = n') by (eapply N_i32_repr_inj; done).
          subst n'.

          iExists (tag_address MemGC ar), ar32.
          repeat iSplit; try done.
          iExists (RootHeap MemGC ar).
          iSplitR; try done.
        }

        iApply ("HΦ" with "[//] [//] [//] [$] [$] [$] [$] [$]").
    - eapply wp_ite_gc_ptr_nonptr in Hcg; last assumption.
      inv_cg_ret Hcg; subst.
      clear_nils.
      iApply fupd_cwp.
      iApply (cwp_val with "[$] [$]"); eauto using has_values_to_consts.

      iAssert (atom_interp o v) with "[Hat]" as "Hat'".
      {
        cbn.
        move Harep at bottom.
        destruct o; cbn.
        1: {
          destruct ι; cbn in Harep; try inversion Harep.
          contradiction.
        }
        all: done.
      }

      iSpecialize ("Hclose" $! (map WordInt ns) ns ns32).
      iSpecialize ("Hclose" with "[%] [//] [%] [%] [Hphys] [$] [$]").
      { by rewrite length_map. }
      {
        revert Hlocsθ_ws.
        rewrite Hupdate !flat_map_app !Forall_app -Hdomθhm.
        intuition.
        replace (flat_map _ _) with (@nil location); first done.
        symmetry.
        rewrite flat_map_concat_map map_map map_const.
        eapply concat_nil_Forall.
        by apply Forall_repeat.
      }
      {
        revert Hlocsθ_ws.
        rewrite Hupdate !flat_map_app !Forall_app.
        intuition.
        replace (flat_map _ _) with (@nil location); first done.
        symmetry.
        rewrite flat_map_concat_map map_map map_const.
        eapply concat_nil_Forall.
        by apply Forall_repeat.
      }
      { unfold PHYS. rewrite -Hserws. done. }

      iMod "Hclose" as "(Hhp & Htok)".
      iModIntro.

      iApply ("HΦ" with "[//] [//] [//] [$] [$] [$] [$] [$]").

  Admitted.

  Lemma wp_mem_load_move_gc_inner ιs :
    ∀ (se : @semantic_env Σ) F lidx off wt wl ret wt' wl' es,
    let fe := fe_of_context F in
      run_codegen
        (foldlM
           (λ off' ι, load1 mr fe MemGC Move lidx off' ι;; Monad.ret (off' + arep_size ι))
           off ιs)
        wt wl = inr (ret, wt', wl', es) →
    let offs := snd $ seq.foldl (λ '(off', offs) ι, (off' + arep_size ι, seq.rcons offs off'))
                  (off, []) ιs in
    let offs_szs := seq.zip offs (map arep_size ιs) in
    ret = seq.foldl (λ off' ι, off' + arep_size ι) off ιs ∧
    wt' = [] ∧
    wl' = map translate_arep ιs ∧
    ∀ f ℓ a32 a os ws E B R θ lmask Φ,
    ⊢ "Hf" ∷ ↪[frame] f -∗
      "Hrun" ∷ ↪[RUN] -∗
      "Hptr" ∷ ℓ ↦heap ws -∗
      "%Haddr" ∷ ⌜θ !! ℓ = Some (MemGC, a)⌝ -∗
      "%Hℓmask"  ∷ ⌜¬ lmask ℓ⌝ -∗
      "Hown"  ∷ na_own logrel_nais E -∗
      "Htok"  ∷ rt_token rti sr lmask θ -∗
      "Hregf" ∷ instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
      "%Hmask" ∷ ⌜↑ns_fun (N.of_nat (sr_func_registerroot sr)) ⊆ E⌝ -∗
      "%Hbound" ∷ ⌜off + sum_list_with arep_size ιs ≤ length ws⌝ -∗
      "%Harep" ∷ ⌜Forall2 has_arep ιs os⌝ -∗
      "%Hser" ∷ ⌜Forall2 (λ o '(off, sz), serialize_atom o = get_path_words off sz ws) os offs_szs⌝ -∗
      "%Hse" ∷ ⌜sem_env_interp F se⌝ -∗
      "%Hfsz" ∷ ⌜fe_wlocal_offset fe + length wl + length wl' <= length (f_locs f)⌝ -∗
      "%Hlidx" ∷ ⌜f_locs f !! localimm lidx = Some (VAL_int32 a32)⌝ -∗
      "%Hlidx_bdd" ∷ ⌜localimm lidx < fe_wlocal_offset fe + length wl⌝ -∗
      "%Hrepa" ∷ ⌜N_i32_repr (tag_address MemGC a) a32⌝ -∗
      "%Hrepa_mod" ∷ ⌜a `mod` 4 = 0⌝%N -∗
      "%Hrepa_nz" ∷ ⌜a ≠ 0⌝%N -∗
      "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemMM)⌝ -∗
      "%Hmemmm" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
      "%Hmemgc" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemGC = Some (sr_mem_gc sr)⌝ -∗
      "HΦ" ∷
        (∀ f' vs vsf ns',
           "%Hns'" ∷ ⌜length ns' = areps_size ιs⌝ -∗
           "%Hf'"  ∷ ⌜f' = mk_load_frame fe f wl vsf⌝ -∗
           "%Hvsf" ∷ ⌜Forall2 (λ ι vf, types_agree (translate_arep ι) vf) ιs vsf⌝ -∗
           "Hptr"  ∷ ℓ ↦heap update_path_words off ws (map WordInt ns') -∗
           "Hown"  ∷ na_own logrel_nais E -∗
           "Htok"  ∷ rt_token rti sr lmask θ -∗
           "Hregf" ∷ instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
           "Hos"    ∷ ([∗ list] o;v ∈ os; vs, atom_interp o v) -∗
           Φ f' vs) -∗
      CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
    induction ιs as [| ιs ι] using seq.last_ind; intros * Hcg *.
    - cbn in Hcg.
      inversion Hcg; subst ret wt' wl' es.
      repeat (split; first done).
      intros *.
      repeat iIntros "@".
      iApply (cwp_nil with "[$] [$]").
      inversion Harep; subst.
      iApply ("HΦ" $! f [] [] [] with "[//] [//] [//] [Hptr] [$Hown] [$Htok] [$Hregf] [$]"); try done; [].
      by rewrite update_path_words_empty_2.
    - apply inv_foldlM_rcons in Hcg.
      destruct Hcg as (n & ?wt & ?wt & ?wl & ?wl & es_fold & es_load & Hfold & Hload & -> & -> & ->).
      inv_cg_bind Hload ?ret ?wt ?wt ?wl ?wl es_load1 ?es_rest Hload1 Hret.
      inv_cg_ret Hret; subst; clear_nils.
      pose proof (IHιs se _ _ _ _ _ _ _ _ _ Hfold) as (-> & -> & -> & IHspec).
      pose proof (wp_mem_load1_cg_state rti sr mr _ _ _ _ _ _ _ _ _ _ _ _ Hload1) as (-> & -> & ->).
      split.
      { by rewrite seq.foldl_rcons. }
      split.
      { done. }
      split.
      { by rewrite rcons_app map_app. }
      intros *.
      repeat iIntros "@".
      apply Forall2_rcons_inv_l in Harep.
      destruct Harep as (o & os' & Ho & Hos & ->).
      rename os' into os.

      iApply (cwp_seq with "[-HΦ]").
      {
        apply Forall2_rcons_inv_l in Hser.
        destruct Hser as ([off' sz'] & offs_szs' & Hoffsz & Hser' & Hoffs_szs).
        rename Hser' into Hser.
        iPoseProof (IHspec with "[$] [$] [$] [//] [//] [$] [$] [$] [//] [%] [//]") as "IH".
        { rewrite sum_list_with_rcons in Hbound. lia. }
        iApply "IH"; try done.
        - iPureIntro.
          unfold offs_szs, offs in Hoffs_szs.
          rewrite seq.foldl_rcons in Hoffs_szs.
          rewrite -> seq.map_rcons in Hoffs_szs.
          destruct (seq.foldl (λ '(off', offs) (ι : atomic_rep), (off' + arep_size ι, seq.rcons offs off')) (
                        off, []) ιs) as [off0 offs0] eqn:Heqfold.
          assert (seq.size offs0 = seq.size (seq.map arep_size ιs)).
          {
            erewrite load_fold_offs_len ; eauto.
            change @seq.size with @length.
            change @seq.map with @map.
            rewrite length_map.
            by apply Nat.add_0_r.
          }
          cbn in Hoffs_szs.
          rewrite seq.zip_rcons in Hoffs_szs; last done.
          eapply seq.rcons_inj in Hoffs_szs.
          inversion Hoffs_szs; subst.
          apply Hser.
        - rewrite length_app in Hfsz; cbn in Hfsz.
          iPureIntro.
          cbn.
          lia.
        - iIntros (f' vs' vsf' ns').
          repeat iIntros "@".
          instantiate (1 :=
            (λ f' vs',
              ∃ vsf' ns',
                ⌜f' = mk_load_frame (fe_of_context F) f wl vsf'⌝ ∗
                ([∗ list] o;v ∈ os;vs', atom_interp o v) ∗
                ⌜Forall2 (λ (ι : atomic_rep) (vf : value), types_agree (translate_arep ι) vf) ιs vsf'⌝ ∗
                "Hptr" ∷ ℓ ↦heap update_path_words off ws (map WordInt ns') ∗
                "%Hns'" ∷ ⌜length ns' = areps_size ιs⌝ ∗
                ?[Q])%I).
          iExists vsf'.
          iFrame.
          iSplitR; first done.
          iSplitR; first done.
          iSplitR; first done.
          iNamedAccu.
      }
      iIntros (f' vs') "(%vsf' & %ns' & -> & Hats & %Htys & Hrest) Hf Hr".
      repeat iDestruct "Hrest" as "[@ Hrest]"; iDestruct "Hrest" as "@".
      iApply cwp_val_app; first apply has_values_to_consts.
      iApply (wp_load1_move_gc with "[$] [$] [$] [//] [$] [$] [Hregf] [//] [//] []");
        first eassumption;
        try done.
      + by rewrite load_frame_inst.
      + rewrite simple_fold_sum_list_with.
        iPureIntro.
        rewrite sum_list_with_rcons in Hbound.
        rewrite update_path_words_size; first lia.
        rewrite length_map Hns'.
        unfold areps_size.
        cbn.
        rewrite -sum_list_with_list_sum.
        lia.
      + iPureIntro.
        rewrite simple_fold_sum_list_with.
        unfold offs_szs, offs in Hser.
        rewrite seq.foldl_rcons in Hser.
        destruct (seq.foldl (λ '(off', offs) (ι : atomic_rep), (off' + arep_size ι, seq.rcons offs off')) (off, []) ιs) as [off' offs'] eqn:Hfold'.
        cbn in Hser.
        change @map with @seq.map in Hser.
        rewrite seq.map_rcons in Hser.

        assert (seq.size offs' = seq.size (seq.map arep_size ιs)).
        { erewrite load_fold_offs_len; eauto.
          cbn.
          rewrite seq.size_map.
          change @seq.size with @length.
          lia. }

        assert (off + length (map WordInt ns') ≤ length ws).
        {
          rewrite length_map Hns'.
          rewrite sum_list_with_rcons sum_list_with_list_sum in Hbound.
          unfold areps_size; cbn; lia.
        }
        pose proof (updating_words off (map WordInt ns') ws ltac:(auto))
          as (ws_l & ws0 & ws_r & -> & Hupdate & Hlen0 & Hlen_l).
        rewrite seq.zip_rcons in Hser; last done.
        rewrite !rcons_app in Hser.
        apply Forall2_app_inv in Hser.
        {
          destruct Hser as [Hsers Hser].
          inversion Hser; subst.
          rewrite H4.
          rewrite Hupdate.
          unfold get_path_words.
          rewrite !app_assoc.
          erewrite <- (simple_fold_fancy_fold rti sr mr ιs off'); last by eauto.
          rewrite simple_fold_sum_list_with.
          rewrite !drop_app_length'; first done.
          {
            rewrite !length_app !length_map.
            rewrite sum_list_with_list_sum.
            unfold areps_size in Hns'; cbn in Hns'.
            congruence.
          }
          {
            rewrite !length_app Hlen0 !length_map.
            rewrite sum_list_with_list_sum.
            unfold areps_size in Hns'; cbn in Hns'.
            congruence.
          }
        }
        apply Forall2_length in Hser.
        rewrite !length_app in Hser; cbn in Hser; lia.
      + iPureIntro.
        rewrite !length_app !length_map; cbn.
        rewrite !length_app !length_map in Hfsz; cbn in Hfsz.
        rewrite load_frame_length.
        lia.
      + iPureIntro.
        by rewrite mk_load_frame_stable_part.
      + by rewrite load_frame_inst.
      + by rewrite load_frame_inst.
      + iModIntro.
        iIntros (f' vf' v' ns'').
        repeat iIntros "@".
        iApply ("HΦ" with "[] [] [] [Hptr] [$Hown] [$Htok] [Hregf] [Hats Ho]").
        4: by erewrite update_update_wordint. (* to instantiate evars *)
        all: try done.
        * iPureIntro.
          rewrite length_app rcons_app Hns' Hns'0.
          unfold areps_size, compose.
          rewrite map_app list_sum_app.
          cbn.
          lia.
        * rewrite length_app length_map in Hf'.
          pose proof (Forall2_length _ _ _ Htys) as Hvsflen.
          rewrite Hvsflen in Hf'.
          rewrite mk_frame_rcons in Hf'; eauto.
        * iPureIntro.
          rewrite rcons_app.
          apply Forall2_app; first done.
          by constructor.
        * by rewrite load_frame_inst.
        * rewrite rcons_app.
          iApply (big_sepL2_app with "[Hats]"); iFrame.
          done.
  Qed.

  Lemma wp_mem_load_move_gc (se : @semantic_env Σ) F lidx off ιs wt wl ret wt' wl' es :
    let fe := fe_of_context F in
    run_codegen (memory.load mr fe MemGC Move lidx off ιs) wt wl = inr (ret, wt', wl', es) →
    let offs := snd $ seq.foldl (λ '(off', offs) ι, (off' + arep_size ι, seq.rcons offs off'))
                  (off, []) ιs in
    let offs_szs := seq.zip offs (map arep_size ιs) in
    ret = () /\
    wt' = [] ∧
    wl' = map translate_arep ιs ∧
    ∀ f ℓ a32 a os ws E B R θ lmask Φ,
    ⊢ "Hf" ∷ ↪[frame] f -∗
      "Hrun" ∷ ↪[RUN] -∗
      "Hptr" ∷ ℓ ↦heap ws -∗
      "%Haddr" ∷ ⌜θ !! ℓ = Some (MemGC, a)⌝ -∗
      "%Hℓmask"  ∷ ⌜¬ lmask ℓ⌝ -∗
      "Hown"  ∷ na_own logrel_nais E -∗
      "Htok"  ∷ rt_token rti sr lmask θ -∗
      "Hregf" ∷ instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
      "%Hmask" ∷ ⌜↑ns_fun (N.of_nat (sr_func_registerroot sr)) ⊆ E⌝ -∗
      "%Hbound" ∷ ⌜off + sum_list_with arep_size ιs ≤ length ws⌝ -∗
      "%Harep" ∷ ⌜Forall2 has_arep ιs os⌝ -∗
      "%Hser" ∷ ⌜Forall2 (λ o '(off, sz), serialize_atom o = get_path_words off sz ws) os offs_szs⌝ -∗
      "%Hse" ∷ ⌜sem_env_interp F se⌝ -∗
      "%Hfsz" ∷ ⌜fe_wlocal_offset fe + length wl + length wl' <= length (f_locs f)⌝ -∗
      "%Hlidx" ∷ ⌜f_locs f !! localimm lidx = Some (VAL_int32 a32)⌝ -∗
      "%Hlidx_bdd" ∷ ⌜localimm lidx < fe_wlocal_offset fe + length wl⌝ -∗
      "%Hrepa" ∷ ⌜N_i32_repr (tag_address MemGC a) a32⌝ -∗
      "%Hrepa_mod" ∷ ⌜a `mod` 4 = 0⌝%N -∗
      "%Hrepa_nz" ∷ ⌜a ≠ 0⌝%N -∗
      "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemMM)⌝ -∗
      "%Hmemmm" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
      "%Hmemgc" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemGC = Some (sr_mem_gc sr)⌝ -∗
      "HΦ" ∷
        (∀ f' vs vsf ns',
           "%Hns'" ∷ ⌜length ns' = areps_size ιs⌝ -∗
           "%Hf'"  ∷ ⌜f' = mk_load_frame fe f wl vsf⌝ -∗
           "%Hvsf" ∷ ⌜Forall2 (λ ι vf, types_agree (translate_arep ι) vf) ιs vsf⌝ -∗
           "Hptr"  ∷ ℓ ↦heap update_path_words off ws (map WordInt ns') -∗
           "Hown"  ∷ na_own logrel_nais E -∗
           "Htok"  ∷ rt_token rti sr lmask θ -∗
           "Hregf" ∷ instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
           "Hos"    ∷ ([∗ list] o;v ∈ os; vs, atom_interp o v) -∗
           Φ f' vs) -∗
      CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
    iIntros (? Hcg ? ?).
    apply wp_ignore in Hcg.
    destruct Hcg as (-> & ret' & Hcg).
    pose proof (wp_mem_load_move_gc_inner _ se _ _ _ _ _ _ _ _ _ Hcg)
     as (-> & -> & -> & Hspec).
    split; first done.
    split; first done.
    split; first done.
    intros *.
    repeat iIntros "@".
    iPoseProof Hspec as "Hspec".
    repeat iSpecialize ("Hspec" with "[$]").
    repeat iSpecialize ("Hspec" with "[//]").
    repeat iSpecialize ("Hspec" with "[$]").
    iApply "Hspec"; eauto.
  Qed.


End load_move.
