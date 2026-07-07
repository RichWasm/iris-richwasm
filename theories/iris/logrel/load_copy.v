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

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section load_copy.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.


  Lemma wp_load1_copy_mm (se : @semantic_env Σ) F lidx off ι wt wl ret wt' wl' es :
    let fe := fe_of_context F in
    run_codegen (memory.load1 mr fe MemMM Copy lidx off ι) wt wl = inr (ret, wt', wl', es) ->
    ∀ f ℓ a32 a o ws s E B R θ lmask Φ,
    ⊢ "Hf" ∷ ↪[frame] f -∗
      "Hrun" ∷ ↪[RUN] -∗
      "Hptr" ∷ ℓ ↦heap ws -∗
      "Haddr" ∷ ℓ ↦addr (MemMM, a) -∗
      "Hown"  ∷ na_own logrel_nais E -∗
      "Htok"  ∷ rt_token rti sr lmask θ -∗
      "Hregf" ∷ instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
      "%Hmask" ∷ ⌜↑ns_fun (N.of_nat (sr_func_registerroot sr)) ⊆ E⌝ -∗
      "%Hbound" ∷ ⌜off + arep_size ι ≤ length ws⌝ -∗
      "%Harep" ∷ ⌜has_arep ι o⌝ -∗
      "%Hser" ∷ ⌜serialize_atom o = get_path_words off (arep_size ι) ws⌝ -∗
      "%Hse" ∷ ⌜sem_env_interp F se⌝ -∗
      "%Hfsz" ∷ ⌜fe_wlocal_offset fe + length wl + length wl' <= length (f_locs f)⌝ -∗
      "%Hlidx" ∷ ⌜f_locs f !! localimm lidx = Some (VAL_int32 a32)⌝ -∗
      "%Hrepa" ∷ ⌜N_i32_repr (tag_address MemMM a) a32⌝ -∗
      "%Hrepa_mod" ∷ ⌜a `mod` 4 = 0⌝%N -∗
      "%Hrepa_nz" ∷ ⌜a <> 0⌝%N -∗
      "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemMM)⌝ -∗
      "%Hmemmm" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
      "%Hmemgc" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemGC = Some (sr_mem_gc sr)⌝ -∗
      "HΦ" ∷
        (∀ f' vf v,
           "%Hf'"  ∷ ⌜f' = mk_load1_frame fe f (length wl) vf⌝ -∗
           "%Hvf"  ∷ ⌜types_agree (translate_arep ι) vf⌝ -∗
           "Hptr"  ∷ ℓ ↦heap ws -∗
           "Haddr" ∷ ℓ ↦addr (MemMM, a) -∗
           "Hown"  ∷ na_own logrel_nais E -∗
           "Htok"  ∷ rt_token rti sr lmask θ -∗
           "Hregf" ∷ instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
           "Ho"    ∷ (⌜atom_copyable o⌝ -∗ atom_interp o v) -∗
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
    iPoseProof (virt_to_phys_slice_acc rti sr off (arep_size ι) with "[//] [$] [$] [$]")
      as "(%hm & Hnp & [(%ns & %ns32 & %Hrepns & Hphys & Hwords) Hclose])".
    (* Opening word_interp *)
    iPoseProof (reconstitute_val with "[$Hwords] [//] [//] [//] [//]") as "(%v & %Hserws & Hat & Hret)".
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
    destruct (atomic_rep_eq_dec ι PtrR).
    - subst ι.
      destruct o; try (exfalso; tauto).
      iPoseProof (atom_interp_weak_ptr_shaped with "Hat") as "(%pn & %pn32 & -> & %Hpn32 & %Hshp)".
      eapply wp_ite_gc_ptr_ptr with (evs:= to_consts [VAL_int32 pn32]) (vs:=[VAL_int32 pn32]) in Hcompile;
        [|by apply Is_true_true, has_values_to_consts|done|done|done].
      destruct Hcompile as (?wt & ?wt & ?wt & ?wl & ?wl & ?wl & ?es & ?es & ?es & Hcompile).
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
      inversion Hshp; subst; last destruct μ.
      + iApply (cwp_val with "[$] [$]"); eauto using has_values_to_consts.
        iAssert (atom_interp (PtrA (PtrInt n)) (VAL_int32 pn32)) as "Hat'".
        {
          subst.
          iExists (2 * n)%N, pn32.
          repeat iSplit; try done.
          iExists (RootInt n).
          iSplit; eauto.
          iPureIntro; constructor.
        }
        iPoseProof ("Hret" with "Hat") as "Hwords".
        iAssert (ℓ ↦heap ws ∗ ℓ ↦addr (MemMM, a) ∗ rt_token rti sr lmask θ)%I with "[Hclose Hphys Hwords Hnp]" as "(Hheap & Haddr & Htok)".
        {
          unfold PHYS.
          rewrite -Hserws.
          iApply ("Hclose" with "[Hphys Hwords] [$]").
          by iFrame.
        }
        subst f'.
        iApply ("HΦ" with "[//] [//] [$] [$] [$] [$] [$] [-]").
        by iIntros "_".
      + iApply (cwp_val with "[$] [$]"); eauto using has_values_to_consts.
        iPoseProof ("Hret" with "Hat") as "Hwords".
        iAssert (ℓ ↦heap ws ∗ ℓ ↦addr (MemMM, a) ∗ rt_token rti sr lmask θ)%I with "[Hclose Hphys Hwords Hnp]" as "(Hheap & Haddr & Htok)".
        {
          unfold PHYS.
          rewrite -Hserws.
          iApply ("Hclose" with "[Hphys Hwords] [$]"); by iFrame.
        }
        iApply ("HΦ" with "[//] [//] [$] [$] [$] [$] [$] [-]").
        by iIntros "Hcontra".
      + iEval (cbn) in "Hat".
        iDestruct "Hat" as "(%n & %n32 & %Hn32 & %Hpn32' & (%ar & %Har & Hrt))".
        pose proof (wp_duproot rti sr mr _ _ _ _ _ _ Hcg3) as Hduproot.
        destruct Hduproot as (_ & -> & -> & Hduproot).
        clear Hes_rest2.
        iDestruct "Hnp" as "(Haddr & (%rm & %lm & Hroot & Hlayout & Hrti & Hinj & Hrest))".
        iDestruct "Hrest" as "(%Hrootok & Hrootmem & Hheapok)".
        iCombine "Hrt" "Hroot" gives "%Hrm".
        unfold PHYS.
        rewrite -Hserws.
        iApply (Hduproot with "[$] [$] [//] [//] [$] [$] [$]
                  [Hphys Hclose Hret Hlayout
                   Hrti Hinj Hheapok Haddr] [$] [$]"); eauto.
        {
          apply Is_true_true.
          inversion Hpn32'.
          eapply has_values_to_consts.
        }
        {
          iIntros "Hrt Hgh Hrm".
          iPoseProof ("Hret" with "[Hrt]") as "Hwords";
            first by cbn; iFrame; eauto.
          unfold rt_token_nophys.
          iPoseProof ("Hclose" with "[Hphys Hwords]") as "Hclose".
          {
            by iFrame.
          }
          iPoseProof ("Hclose" with "[-]") as "(Hpt & Hpt' & Htok)"; iFrame; eauto.
          iAccu.
        }
        iIntros (ar' ar'32) "%Hreproot %Hrepar Hrt Htok [Hws Ha] Hinvs Hreg".
        iApply ("HΦ" with "[//] [//] [$] [$] [$] [$] [$] [-]").
        iIntros "_".
        cbn.
        iExists (tag_address MemGC ar'), ar'32.
        unfold root_pointer_interp.
        iSplit; first eauto.
        iSplit; first eauto.
        iExists (RootHeap MemGC ar').
        by iFrame.
    - eapply wp_ite_gc_ptr_nonptr in Hcompile; last assumption.
      inv_cg_ret Hcompile; subst.
      clear_nils.
      iApply (cwp_val with "[$] [$]"); eauto using has_values_to_consts.
      unfold has_arep in *.
      assert (expect_heap_ptr o = None).
      {
        by destruct o, ι.
      }
      assert (Persistent (atom_interp_weak θ MemMM o v));
        first by apply atom_interp_weak_dup.
      iPoseProof "Hat" as "#Hat".
      iPoseProof ("Hret" with "Hat") as "Hwords".
      iPoseProof ("Hclose" with "[Hphys Hwords] [$Hnp]") as "(Hws & Ha & Htok)".
      {
        unfold PHYS.
        rewrite -Hserws.
        by iFrame.
      }
      iApply ("HΦ" with "[//] [//] [$] [$] [$] [$] [$] [-]").
      iIntros "_".
      iApply atom_interp_weak_promote; auto.
  Qed.

  Lemma wp_load1_copy_gc (se : @semantic_env Σ) F lidx off ι wt wl ret wt' wl' es :
    let fe := fe_of_context F in
    run_codegen (memory.load1 mr fe MemGC Copy lidx off ι) wt wl = inr (ret, wt', wl', es) ->
    ∀ f ℓ a32 a o ws s E B R θ lmask Φ,
    ⊢ "Hf" ∷ ↪[frame] f -∗
      "Hrun" ∷ ↪[RUN] -∗
      "Hptr" ∷ ℓ ↦heap ws -∗
      "%Haddr" ∷ ⌜θ !! ℓ = Some (MemGC, a)⌝ -∗
      "Hown"  ∷ na_own logrel_nais E -∗
      "Htok"  ∷ rt_token rti sr lmask θ -∗
      "Hregf" ∷ instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
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
      "HΦ" ∷ ▷ (∀ f' vf v,
           "%Hf'"  ∷ ⌜f' = mk_load1_frame fe f (length wl) vf⌝ -∗
           "%Hvf"  ∷ ⌜types_agree (translate_arep ι) vf⌝ -∗
           "Hptr"  ∷ ℓ ↦heap ws -∗
           "Hown"  ∷ na_own logrel_nais E -∗
           "Htok"  ∷ rt_token rti sr lmask θ -∗
           "Hregf" ∷ instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
           "Ho"    ∷ (⌜atom_copyable o⌝ -∗ atom_interp o v) -∗
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
    iPoseProof ( virt_to_phys_slice_acc_gc rti sr off (arep_size ι) with "[//] [$] [$] [//]")
      as "(%hm & Hnp & [(%ns & %ns32 & %Hrepns & Hphys & Hwords) Hclose])".
    (* Opening word_interp *)
    iPoseProof (reconstitute_val with "[$Hwords] [//] [//] [//] [//]")
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
    destruct (atomic_rep_eq_dec ι PtrR).
    - subst ι.
      destruct o; try (exfalso; tauto).
      iPoseProof (atom_interp_weak_ptr_shaped with "Hat") as "(%pn & %pn32 & -> & %Hpn32 & %Hshp)".
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
      + iApply (cwp_val with "[$] [$]"); eauto using has_values_to_consts.
        iAssert (atom_interp (PtrA (PtrInt n)) (VAL_int32 pn32)) as "Hat'".
        {
          subst.
          iExists (2 * n)%N, pn32.
          repeat iSplit; try done.
          iExists (RootInt n).
          iSplit; eauto.
          iPureIntro; constructor.
        }
        iPoseProof ("Hret" with "Hat") as "Hwords".
        iAssert (ℓ ↦heap ws ∗ rt_token rti sr lmask θ)%I with "[Hclose Hphys Hwords Hnp]" as "(Hheap & Htok)".
        {
          unfold PHYS.
          rewrite -Hserws.
          iApply ("Hclose" with "[Hphys Hwords] [$]").
          by iFrame.
        }
        subst f'.
        iApply ("HΦ" with "[//] [//] [$] [$] [$] [$] [-]").
        by iIntros "_".
      + iApply (cwp_val with "[$] [$]"); eauto using has_values_to_consts.
        iPoseProof ("Hret" with "Hat") as "Hwords".
        iAssert (ℓ ↦heap ws ∗ rt_token rti sr lmask θ)%I with "[Hclose Hphys Hwords Hnp]" as "(Hheap & Htok)".
        {
          unfold PHYS.
          rewrite -Hserws.
          iApply ("Hclose" with "[Hphys Hwords] [$]"); by iFrame.
        }
        iApply ("HΦ" with "[//] [//] [$] [$] [$] [$] [-]").
        by iIntros "Hcontra".
      + iEval (cbn) in "Hat".
        iPoseProof "Hat" as "#Hat".
        iPoseProof "Hat" as "(%n & %n32 & %Hn32 & %Ha & %Hrep)".
        inversion Hrep; subst.
        iPoseProof ("Hret" with "Hat") as "Hwords".
        iAssert (ℓ ↦heap ws ∗ rt_token rti sr lmask θ)%I with "[Hclose Hphys Hwords Hnp]" as "(Hheap & Htok)".
        {
          unfold PHYS.
          rewrite -Hserws.
          iApply ("Hclose" with "[Hphys Hwords] [$]").
          by iFrame.
        }
        pose proof (wp_registerroot rti sr mr _ _ _ _ _ _ Hcg3) as Hregroot.
        destruct Hregroot as (_ & -> & -> & Hregroot).
        inversion Ha; subst pn32.
        iApply (Hregroot with "[HΦ Hheap] [$] [$] [] [$] [$] [$]"); eauto.
        {
          apply Is_true_true.
          subst.
          eapply has_values_to_consts.
        }
        iIntros (ar' ar'32) "%Hreproot Hrt Htok Hinvs %Har'32 Hfn".
        iApply ("HΦ" with "[] [] [$] [$Hinvs] [$Htok] [$Hfn] [-] "); eauto.
        iIntros "_".
        iExists (tag_address MemGC ar'), ar'32.
        unfold root_pointer_interp.
        iSplit; first eauto.
        iSplit; first eauto.
        iExists (RootHeap MemGC ar').
        by iFrame.
    - eapply wp_ite_gc_ptr_nonptr in Hcg; last assumption.
      inv_cg_ret Hcg; subst.
      clear_nils.
      iApply (cwp_val with "[$] [$]"); eauto using has_values_to_consts.
      unfold has_arep in *.
      assert (expect_heap_ptr o = None).
      {
        by destruct o, ι.
      }
      assert (Persistent (atom_interp_weak θ MemGC o v));
        first by apply atom_interp_weak_dup.
      iPoseProof "Hat" as "#Hat".
      iPoseProof ("Hret" with "Hat") as "Hwords".
      iPoseProof ("Hclose" with "[Hphys Hwords] [$Hnp]") as "(Hws & Htok)".
      {
        unfold PHYS.
        rewrite -Hserws.
        by iFrame.
      }
      iApply ("HΦ" with "[//] [//] [$] [$] [$] [$] [-]").
      iIntros "_".
      iApply atom_interp_weak_promote; auto.
  Qed.

  Lemma wp_mem_load_copy_mm_inner (se : @semantic_env Σ) F lidx ιs :
    let fe := fe_of_context F in
    ∀ off wt wl ret wt' wl' es,
      run_codegen
        (foldlM
           (λ off' ι, load1 mr fe MemMM Copy lidx off' ι;; Monad.ret (off' + arep_size ι))
           off ιs)
        wt wl = inr (ret, wt', wl', es) →
      let offs := snd $ seq.foldl (λ '(off', offs) ι, (off' + arep_size ι, seq.rcons offs off'))
                    (off, []) ιs in
      let offs_szs := seq.zip offs (map arep_size ιs) in
      ret = seq.foldl (λ off' ι, off' + arep_size ι) off ιs ∧
      wt' = [] ∧
      wl' = map translate_arep ιs ∧
      ∀ f ℓ a32 a os ws E B R θ lmask Φ,
    ⊢ "Hptr" ∷ ℓ ↦heap ws -∗
      "Haddr" ∷ ℓ ↦addr (MemMM, a) -∗
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
      "%Hrepa_nz" ∷ ⌜a <> 0⌝%N -∗
      "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemMM)⌝ -∗
      "%Hmemmm" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
      "%Hmemgc" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemGC = Some (sr_mem_gc sr)⌝ -∗
      "HΦ" ∷
        (∀ f' vs vsf,
           "%Hf'"     ∷ ⌜f' = mk_load_frame fe f wl vsf⌝ -∗
           "%Hvsf" ∷ ⌜Forall2 (λ ι vf, types_agree (translate_arep ι) vf) ιs vsf⌝ -∗
           "Hptr"  ∷ ℓ ↦heap ws -∗
           "Haddr" ∷ ℓ ↦addr (MemMM, a) -∗
           "Hown"  ∷ na_own logrel_nais E -∗
           "Htok"  ∷ rt_token rti sr lmask θ -∗
           "Hregf" ∷ instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
           "Hos"    ∷ ([∗ list] o;v ∈ os; vs, (⌜atom_copyable o⌝ -∗ atom_interp o v)) -∗
           Φ f' vs) -∗
      "Hf" ∷ ↪[frame] f -∗
      "Hrun" ∷ ↪[RUN] -∗
      CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
    induction ιs as [| ιs ι] using seq.last_ind; intros * Hcg *.
    - cbn in Hcg.
      inversion Hcg; subst.
      split; last split; last split; try done.
      intros *; repeat iIntros "@".
      iApply (cwp_nil with "[$] [$]").
      unfold mk_load_frame.
      iApply ("HΦ" with "[] [//] [$] [$] [$] [$] [$] []").
      + done.
      + inversion Harep.
        by iApply big_sepL2_nil.
    - apply inv_foldlM_rcons in Hcg.
      rewrite seq.foldl_rcons.
      destruct Hcg as (off_ιs & wt_ι & wt_ιs & wl_ι & wl_ιs & es_ι & es_ιs & Hinit & Hlast).
      destruct Hlast as (Hlast & -> & -> & ->).
      inv_cg_bind Hlast a0' wt_bs wt_b wl_bs wl_b es_bs es_b Hbs Hfb.
      subst.
      inv_cg_ret Hfb; subst.
      eapply IHιs in Hinit.
      clear IHιs.
      destruct Hinit as (-> & -> & -> & Hinit).
      pose proof Hbs as Hbs'.
      eapply (wp_mem_load1_cg_state rti sr mr) in Hbs'.
      destruct Hbs' as (-> & -> & ->).
      subst; clear_nils.
      change map with @seq.map.
      rewrite seq.map_rcons -seq.cats1 W.cat_app.
      repeat (split; first by auto).
      intros *; repeat iIntros "@".
      (* inverting forall2 where there's an rcons in only one side *)
      pose proof (Forall2_rcons_inv_l _ _ _ _ Harep) as (o & os' & Ho & Hos' & Hos_eq).
      rewrite Hos_eq in Hser.
      pose proof (Forall2_rcons_inv_l _ _ _ _ Hser) as ([off' sz'] & offs_szs' & Hsero & Hseros' & Hoffs_szs_eq).
      unfold offs_szs in Hoffs_szs_eq.
      remember (seq.foldl (λ '(off', offs) (ι : atomic_rep), (off' + arep_size ι, seq.rcons offs off')) (
                    off, []) (seq.rcons ιs ι))
        as big_fold in *.
      rewrite seq.foldl_rcons in Heqbig_fold.
      destruct (seq.foldl (λ '(off', offs) (ι : atomic_rep), (off' + arep_size ι, seq.rcons offs off')) (off, []) ιs)
        as [off0 offs0] eqn:?Hfold.
      assert (seq.size offs0 = seq.size ιs).
      {
        erewrite load_fold_offs_len; eauto.
        by rewrite Nat.add_0_r.
      }
      iPoseProof (Hinit with "[$] [$] [$] [$] [$]") as "Hinit".
      clear Hinit.
      repeat iPoseProof ("Hinit" with "[//]") as "Hinit".
      iSpecialize ("Hinit" with "[] [//] [] [//] [] [//] [//] [//] [//] [//] [//] [//] [//]");
      last iSpecialize ("Hinit" with "[]").
      {
        iPureIntro.
        rewrite rcons_app sum_list_with_app in Hbound; cbn in Hbound.
        lia.
      }
      {
        iPureIntro.
        cbn.
        change @map with @seq.map in Hoffs_szs_eq.
        rewrite /offs Heqbig_fold seq.map_rcons in Hoffs_szs_eq.
        cbn in Hoffs_szs_eq.
        rewrite seq.zip_rcons in Hoffs_szs_eq; last by rewrite seq.size_map.
        pose proof (seq.rcons_inj Hoffs_szs_eq) as Hinv.
        by inversion Hinv; subst.
      }
      {
        iPureIntro.
        rewrite length_app in Hfsz.
        unfold fe in Hfsz.
        change @seq.map with @map in Hfsz.
        lia.
      }
      {
        iIntros (f' vs vsf).
        repeat iIntros "@".
        (* DEMO: using iAccu to save proof state *)
        let Q := open_constr:(_ : iProp Σ) in
          instantiate (1 := (λ f0 vs0, ∃ vsf,
                              (* stuff to say about f0 and vs0 *)
                              ⌜f0 = mk_load_frame fe f wl vsf⌝ ∗
                              ⌜Forall2 (λ (ι : atomic_rep) (vf : value), types_agree (translate_arep ι) vf) ιs vsf⌝ ∗
                              ([∗ list] o0;v ∈ os';vs0, ⌜atom_copyable o0⌝ -∗ atom_interp o0 v) ∗
                              rt_token rti sr lmask θ ∗
                              (* evar for collecting everything else *)
                              (* make sure nothing that goes in here mentions f', or vs! *)
                              Q)%I).
        iExists vsf.
        iFrame "Hos Htok".
        iSplit; first done.
        iSplit; first done.
        (* accumulates everything in the evar *)
        iNamedAccu.
      }
      iApply (cwp_seq with "[Hinit Hf Hrun]");
        first iApply ("Hinit" with "[$] [$]").
      iIntros (f' vs') "(%vsf & -> & %Hvsf & Hos & Htok & @ & @ & @ & @) Hf Hr".
      iApply cwp_val_app; first eauto using has_values_to_consts.
      iEval (erewrite <- (load_frame_inst fe f wl vsf)) in "Hregf".
      pose proof Hfold as Hfold'.
      apply simple_fold_fancy_fold in Hfold'.
      replace offs with (seq.rcons offs0 off0) in *;
        last by rewrite /offs Heqbig_fold.
      iApply (wp_load1_copy_mm with "[$] [$] [$] [$] [$] [$] [$]").
      all:try eauto || iPureIntro.
      + rewrite simple_fold_sum_list_with.
        rewrite sum_list_with_rcons in Hbound.
        lia.
      + rewrite Hsero.
        revert Hoffs_szs_eq.
        change @map with @seq.map.
        rewrite seq.map_rcons.
        rewrite seq.zip_rcons;
          last by rewrite seq.size_map.
        intros Heq.
        apply seq.rcons_inj in Heq.
        inversion Heq; subst off'.
        f_equal.
        symmetry; eapply simple_fold_fancy_fold; eauto.
      + revert Hfsz.
        change @seq.map with @map.
        rewrite length_app load_frame_length; cbn.
        rewrite length_app.
        lia.
      + rewrite mk_load_frame_stable_part; done.
      + rewrite load_frame_inst.
        eauto.
      + rewrite load_frame_inst.
        eauto.
      + iIntros (f'' vf v) "@@@@@@@@".
        unfold fvs_combine.
        iApply ("HΦ" with "[] [] [$] [$] [$] [$] [Hregf] [Ho Hos]").
        * iPureIntro.
          instantiate (1:=vsf ++ [vf]).
          rewrite Hf'.
          rewrite -mk_frame_rcons; try eauto.
          f_equal.
          rewrite length_app length_map.
          f_equal.
          eapply Forall2_length; eapply Hvsf.
        * iPureIntro; rewrite rcons_app.
          apply Forall2_app; eauto.
        * by rewrite load_frame_inst.
        * rewrite Hos_eq -rcons_app big_sepL2_rcons.
          iFrame.
  Qed.

  Lemma wp_mem_load_copy_mm (se : @semantic_env Σ) F lidx ιs :
    let fe := fe_of_context F in
    ∀ off wt wl ret wt' wl' es,
      run_codegen (memory.load mr fe MemMM Copy lidx off ιs) wt wl = inr (ret, wt', wl', es) ->
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
        "%Hrepa_nz" ∷ ⌜a <> 0⌝%N -∗
        "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemMM)⌝ -∗
        "%Hmemmm" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
        "%Hmemgc" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemGC = Some (sr_mem_gc sr)⌝ -∗
        "HΦ" ∷
          (∀ f' vs vsf,
             "%Hf'"     ∷ ⌜f' = mk_load_frame fe f wl vsf⌝ -∗
             "%Hvsf" ∷ ⌜Forall2 (λ ι vf, types_agree (translate_arep ι) vf) ιs vsf⌝ -∗
             "Hptr"  ∷ ℓ ↦heap ws -∗
             "Haddr" ∷ ℓ ↦addr (MemMM, a) -∗
             "Hown"  ∷ na_own logrel_nais E -∗
             "Htok"  ∷ rt_token rti sr lmask θ -∗
             "Hregf" ∷ instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
             "Hos"    ∷ ([∗ list] o;v ∈ os; vs, (⌜atom_copyable o⌝ -∗ atom_interp o v)) -∗
             Φ f' vs) -∗
        CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
    unfold memory.load.
    intros * Hcg.
    apply wp_ignore in Hcg.
    destruct Hcg as (-> & off' & Hcg).
    pose proof (wp_mem_load_copy_mm_inner se _ _ _ _ _ _ _ _ _ _ Hcg) as (-> & U & V & W).
    intuition.
    repeat iIntros "@".
    iPoseProof W as "W".
    by repeat (iSpecialize ("W" with "[$]") || iSpecialize ("W" with "[//]")).
  Qed.

  Lemma wp_mem_load_copy_gc_inner (se : @semantic_env Σ) F lidx ιs :
    let fe := fe_of_context F in
    ∀ off wt wl ret wt' wl' es,
      run_codegen
        (foldlM
           (λ off' ι, load1 mr fe MemGC Copy lidx off' ι;; Monad.ret (off' + arep_size ι))
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
        "%Hrepa_nz" ∷ ⌜a <> 0⌝%N -∗
        "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_gc sr) (rt_memaddr sr MemGC)⌝ -∗
        "%Hmemmm" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
        "%Hmemgc" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemGC = Some (sr_mem_gc sr)⌝ -∗
        "HΦ" ∷
          ▷^(length ιs) (∀ f' vs vsf,
             "%Hf'"  ∷ ⌜f' = mk_load_frame fe f wl vsf⌝ -∗
             "%Hvsf" ∷ ⌜Forall2 (λ ι vf, types_agree (translate_arep ι) vf) ιs vsf⌝ -∗
             "Hptr"  ∷ ℓ ↦heap ws -∗
             "Hown"  ∷ na_own logrel_nais E -∗
             "Htok"  ∷ rt_token rti sr lmask θ -∗
             "Hregf" ∷ instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
             "Hos"    ∷ ([∗ list] o;v ∈ os; vs, (⌜atom_copyable o⌝ -∗ atom_interp o v)) -∗
             Φ f' vs) -∗
        CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
    induction ιs as [| ιs ι] using seq.last_ind; intros * Hcg *.
    - cbn in Hcg.
      inversion Hcg; subst.
      split; last split; last split; try done.
      intros *; repeat iIntros "@".
      iApply (cwp_nil with "[$] [$]").
      unfold mk_load_frame.
      iApply ("HΦ" with "[] [//] [$] [$] [$] [$] []").
      + done.
      + inversion Harep.
        by iApply big_sepL2_nil.
    - apply inv_foldlM_rcons in Hcg.
      rewrite seq.foldl_rcons.
      destruct Hcg as (off_ιs & wt_ι & wt_ιs & wl_ι & wl_ιs & es_ι & es_ιs & Hinit & Hlast).
      destruct Hlast as (Hlast & -> & -> & ->).
      inv_cg_bind Hlast a0' wt_bs wt_b wl_bs wl_b es_bs es_b Hbs Hfb.
      subst.
      inv_cg_ret Hfb; subst.
      eapply IHιs in Hinit.
      clear IHιs.
      destruct Hinit as (-> & -> & -> & Hinit).
      pose proof Hbs as Hbs'.
      eapply (wp_mem_load1_cg_state rti sr mr) in Hbs'.
      destruct Hbs' as (-> & -> & ->).
      subst; clear_nils.
      change map with @seq.map.
      rewrite seq.map_rcons -seq.cats1 W.cat_app.
      repeat (split; first by auto).
      intros *; repeat iIntros "@".
      (* inverting forall2 where there's an rcons in only one side *)
      pose proof (Forall2_rcons_inv_l _ _ _ _ Harep) as (o & os' & Ho & Hos' & Hos_eq).
      rewrite Hos_eq in Hser.
      pose proof (Forall2_rcons_inv_l _ _ _ _ Hser) as ([off' sz'] & offs_szs' & Hsero & Hseros' & Hoffs_szs_eq).
      unfold offs_szs in Hoffs_szs_eq.
      remember (seq.foldl (λ '(off', offs) (ι : atomic_rep), (off' + arep_size ι, seq.rcons offs off')) (
                    off, []) (seq.rcons ιs ι))
        as big_fold in *.
      rewrite seq.foldl_rcons in Heqbig_fold.
      destruct (seq.foldl (λ '(off', offs) (ι : atomic_rep), (off' + arep_size ι, seq.rcons offs off')) (off, []) ιs)
        as [off0 offs0] eqn:?Hfold.
      assert (seq.size offs0 = seq.size ιs).
      {
        erewrite load_fold_offs_len; eauto.
        by rewrite Nat.add_0_r.
      }
      iEval (change @length with @seq.size;
             rewrite seq.size_rcons bi.laterN_later)
        in "HΦ".
      iApply (cwp_seq with "[-]").
      {
        iPoseProof (Hinit with "[$] [$] [$] [//] [$] [$] [$]") as "Hinit".
        clear Hinit.
        repeat iPoseProof ("Hinit" with "[//]") as "Hinit".
        iSpecialize ("Hinit" with "[] [//] [] [//] [] [//] [//] [//] [//] [//] [//] [//] [//]");
        last iSpecialize ("Hinit" with "[HΦ]").
        {
          iPureIntro.
          rewrite rcons_app sum_list_with_app in Hbound; cbn in Hbound.
          lia.
        }
        {
          iPureIntro.
          cbn.
          change @map with @seq.map in Hoffs_szs_eq.
          rewrite /offs Heqbig_fold seq.map_rcons in Hoffs_szs_eq.
          cbn in Hoffs_szs_eq.
          rewrite seq.zip_rcons in Hoffs_szs_eq; last by rewrite seq.size_map.
          pose proof (seq.rcons_inj Hoffs_szs_eq) as Hinv.
          by inversion Hinv; subst.
        }
        {
          iPureIntro.
          rewrite length_app in Hfsz.
          unfold fe in Hfsz.
          change @seq.map with @map in Hfsz.
          lia.
        }
        {
          iIntros "!>".
          iIntros (f' vs vsf).
          repeat iIntros "@".
          (* DEMO: using iAccu to save proof state *)
          let Q := open_constr:(_ : iProp Σ) in
            instantiate (1 := (λ f0 vs0, ∃ vsf,
                                (* stuff to say about f0 and vs0 *)
                                ⌜f0 = mk_load_frame fe f wl vsf⌝ ∗
                                ⌜Forall2 (λ (ι : atomic_rep) (vf : value), types_agree (translate_arep ι) vf) ιs vsf⌝ ∗
                                ([∗ list] o0;v ∈ os';vs0, ⌜atom_copyable o0⌝ -∗ atom_interp o0 v) ∗
                                rt_token rti sr lmask θ ∗
                                (* evar for collecting everything else *)
                                (* make sure nothing that goes in here mentions f' or vs! *)
                                Q)%I).
          iExists vsf.
          iFrame "Hos Htok".
          iSplit; first done.
          iSplit; first done.
          (* accumulates everything in the evar *)
          iNamedAccu.
        }
        iApply "Hinit".
      }
      iIntros (f' vs') "(%vsf & -> & %Hvsf & Hos & Htok & @ & @ & @) Hf Hr".
      iApply cwp_val_app; first eauto using has_values_to_consts.
      iEval (erewrite <- (load_frame_inst fe f wl vsf)) in "Hregf".
      pose proof Hfold as Hfold'.
      apply simple_fold_fancy_fold in Hfold'.
      replace offs with (seq.rcons offs0 off0) in *;
        last by rewrite /offs Heqbig_fold.
      iApply (wp_load1_copy_gc with "[$] [$] [$] [//] [$] [$] [$]").
      all:try eauto || iPureIntro.
      + rewrite simple_fold_sum_list_with.
        rewrite sum_list_with_rcons in Hbound.
        lia.
      + rewrite Hsero.
        revert Hoffs_szs_eq.
        change @map with @seq.map.
        rewrite seq.map_rcons.
        rewrite seq.zip_rcons;
          last by rewrite seq.size_map.
        intros Heq.
        apply seq.rcons_inj in Heq.
        inversion Heq; subst off'.
        f_equal.
        symmetry; eapply simple_fold_fancy_fold; eauto.
      + revert Hfsz.
        change @seq.map with @map.
        rewrite length_app load_frame_length; cbn.
        rewrite length_app.
        lia.
      + rewrite mk_load_frame_stable_part; done.
      + rewrite load_frame_inst.
        eauto.
      + rewrite load_frame_inst.
        eauto.
      + iModIntro.
        iIntros (f'' vf v).
        repeat iIntros "@".
        unfold fvs_combine.
        rewrite load_frame_inst.
        iApply ("HΦ" with "[] [] [$] [$] [$] [$] [Ho Hos]").
        * iPureIntro.
          instantiate (1:=vsf ++ [vf]).
          rewrite Hf'.
          rewrite -mk_frame_rcons; eauto.
          f_equal.
          rewrite length_app length_map.
          f_equal.
          eapply Forall2_length; eapply Hvsf.
        * iPureIntro; rewrite rcons_app.
          apply Forall2_app; eauto.
        * rewrite Hos_eq -rcons_app big_sepL2_rcons.
          iFrame.
  Qed.

  Lemma wp_mem_load_copy_gc (se : @semantic_env Σ) F lidx ιs :
    let fe := fe_of_context F in
    ∀ off wt wl ret wt' wl' es,
      run_codegen (memory.load mr fe MemGC Copy lidx off ιs) wt wl = inr (ret, wt', wl', es) ->
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
        "%Hrepa_nz" ∷ ⌜a <> 0⌝%N -∗
        "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_gc sr) (rt_memaddr sr MemGC)⌝ -∗
        "%Hmemmm" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
        "%Hmemgc" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemGC = Some (sr_mem_gc sr)⌝ -∗
        "HΦ" ∷
          ▷^(length ιs) (∀ f' vs vsf,
             "%Hf'"  ∷ ⌜f' = mk_load_frame fe f wl vsf⌝ -∗
             "%Hvsf" ∷ ⌜Forall2 (λ ι vf, types_agree (translate_arep ι) vf) ιs vsf⌝ -∗
             "Hptr"  ∷ ℓ ↦heap ws -∗
             "Hown"  ∷ na_own logrel_nais E -∗
             "Htok"  ∷ rt_token rti sr lmask θ -∗
             "Hregf" ∷ instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
             "Hos"    ∷ ([∗ list] o;v ∈ os; vs, (⌜atom_copyable o⌝ -∗ atom_interp o v)) -∗
             Φ f' vs) -∗
        CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
    intros * Hcg ? ?.
    apply wp_ignore in Hcg.
    destruct Hcg as (-> & res' & Hcg).
    eapply wp_mem_load_copy_gc_inner in Hcg.
    destruct Hcg as (-> & -> & -> & Hspec).
    split; first done.
    split; first done.
    split; first done.
    exact Hspec.
  Qed.

End load_copy.
