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
      iDestruct "Hws" as "(%a & %Hrep & Ha)".
      iSplitL.
      + iExists n, n32.
        iFrame.
        iPureIntro.
        intuition eauto.
        apply deserialise_serialise_i32.
      + done.
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

    iSpecialize ("Hclose" with "[] [] [] [] [Hphys] [Hat Hret] [$Hnp]").
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { unfold PHYS. rewrite -Hserws.
      done. }
    { by iApply "Hret". }
    iApply fupd_cwp.
    iMod "Hclose" as "(Hhp & Haddr & Htok)".
    iModIntro.
    destruct (atomic_rep_eq_dec ι PtrR).
    + subst ι.
      destruct o; try (exfalso; tauto).
      eapply wp_ite_gc_ptr_ptr with (evs:= to_consts [v]) (vs:=[v]) in Hcompile;
        [|by apply Is_true_true, has_values_to_consts|done| by econstructor |done].
      destruct Hcompile as (?wt & ?wt & ?wt & ?wl & ?wl & ?wl & ?es & ?es & ?es & Hcompile).
      destruct Hcompile as (Hcg1 & Hcg2 & Hcg3 & Hwt7 & Hwl7 & Hes_rest2).
      iApply (Hes_rest2 with "[$] [$] []").
      { admit.}
      { iIntros "!> Hf Hr".
        inv_cg_ret Hcg2.
        iApply (cwp_val with "[$] [$]"); first (clear_nils; eauto using has_values_to_consts).
        iApply ("HΦ" with "[] [] [] [$] [$] [$] [$] [$] []").
        - admit.
        - admit.
        - admit.
        - admit.
      }
    + eapply wp_ite_gc_ptr_nonptr in Hcompile; last assumption.
      inv_cg_ret Hcompile; subst; clear_nils.
      iApply (cwp_val with "[$] [$]"); first eauto using has_values_to_consts.
      iApply ("HΦ" with "[] [] [] [$] [$] [$] [$] [$] []").
      * admit.
      * admit.
      * admit.
      * admit.
  Admitted.

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
          { admit. }
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
      + admit.
      + admit.
      + admit.
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
  Admitted.

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

End load_move.
