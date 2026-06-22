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
Require Import RichWasm.iris.logrel.rt_token.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section virt_to_phys_strong.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.


  Lemma heap_ok_update_strong θ lmask lm hm ℓ ws' flags :
    layout_ok lmask lm hm ->
    heap_ok θ hm →
    ¬ lmask ℓ ->
    lm !! ℓ = Some flags →
    (* Forall2 word_has_flag flags ws' → *)
    Forall (λ ℓ', ℓ' ∈ dom hm) (flat_map locations ws') →
    Forall (λ ℓ', ℓ' ∈ dom θ) (flat_map locations ws') →
    layout_ok lmask lm (<[ℓ := ws']> hm) /\ heap_ok θ (<[ℓ := ws']> hm).
  Proof.
    intros Hflags (Hdomhm & Hdomθ) Hlmask Hlm Hlocshm Hlocsθ.
    unfold layout_ok in Hflags.
    unfold map_Forall2 in Hflags, Hdomθ.
    unfold map_Forall in Hdomhm.
    have Hhmℓ : is_Some (hm !! ℓ).
    { have := Hflags ℓ. rewrite Hlm. intros H. inversion H. eauto. }
    destruct Hhmℓ as [ws_old Hws_old].
    have Hθℓ : is_Some (θ !! ℓ).
    { have := Hdomθ ℓ. rewrite Hws_old. intros H. inversion H. eauto. }
    destruct Hθℓ as [x Hθℓv].
    split; [| split].
    - unfold layout_ok. unfold map_Forall2. intro k.
      destruct (decide (k = ℓ)) as [->|Hne].
      + rewrite lookup_insert Hlm decide_True; last done. constructor.
        intros Hl2.
        by specialize (Hlmask Hl2). (* NOTE: THIS IS WHERE LMASK = FALSE COMES IN *)
      + rewrite lookup_insert_ne //.
    - unfold map_Forall. intros k ws Hk.
      destruct (decide (k = ℓ)) as [->|Hne].
      + rewrite lookup_insert decide_True in Hk; last done. injection Hk as <-.
        eapply Forall_impl; first exact Hlocshm.
        intros ℓ' Hℓ'. rewrite dom_insert_L. set_solver.
      + rewrite lookup_insert_ne // in Hk.
        eapply Forall_impl; first exact (Hdomhm k ws Hk).
        intros ℓ' Hℓ'. rewrite dom_insert_L. set_solver.
    - unfold map_Forall2. intro k.
      destruct (decide (k = ℓ)) as [->|Hne].
      + rewrite lookup_insert Hθℓv decide_True; last done. constructor. exact Hlocsθ.
      + rewrite lookup_insert_ne //.
  Qed.


  (* also weak. and here's where you need to know it's in the mask? I think? *)
  Lemma rt_token_nophys_insert_heap_strong θ lmask hm ℓ ws ws' :
    hm !! ℓ = Some ws →
    ¬ lmask ℓ ->
    (* (∀ flags, Forall2 word_has_flag flags ws → Forall2 word_has_flag flags ws') → *)
    Forall (λ ℓ', ℓ' ∈ dom hm) (flat_map locations ws') →
    Forall (λ ℓ', ℓ' ∈ dom θ) (flat_map locations ws') →
    rt_token_nophys rti sr lmask θ hm -∗
    rt_token_nophys rti sr lmask θ (<[ℓ := ws']> hm).
  Proof.
    intros Hhm Hl Hlocshm Hlocsθ.
    iIntros "(Haddr & %rm & %lm & Hroot & Hlayout & Hrti & %Hinj & %Hrootok & Hrootmem & %Hlayoutok & %Hheapok)".
    iFrame.
    iSplit; first done.
    iSplit; first done.
    iPureIntro.
    have Hmapflags : ∃ flags, lm !! ℓ = Some flags ∧
                                (lmask ℓ -> Forall2 word_has_flag flags ws).
    { unfold map_Forall2 in Hlayoutok. specialize (Hlayoutok ℓ).
      rewrite Hhm in Hlayoutok. inversion Hlayoutok. exists x. split; done. }
    destruct Hmapflags as [flags [Hflm Hwsflags]].
    eapply heap_ok_update_strong.
    4: exact Hflm.
    all: try done.
  Qed.


  (* I DONT KNOW IF IT SHOULD BE THE ALLMASK. MAYBE. MAKING IT LMASK FOR NOW *)
  (* ALSO NOT SUPER CERTAIN THE IF lmask ℓ IS A CORRECT HYPO TO HAVE *)
  Lemma virt_to_phys_slice_store_acc_strong lmask off sz ℓ μ a θ ws :
    let slice := take sz (drop off ws) in
    ⊢ ⌜off + sz <= length ws⌝ -∗
      rt_token rti sr lmask θ -∗
      ℓ ↦heap ws -∗
      ℓ ↦addr (μ, a) -∗
      ⌜¬ lmask ℓ⌝ -∗
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
          (* ⌜∀ flags, Forall2 word_has_flag flags ws → *)
          (*           Forall2 word_has_flag flags (update_path_words off ws ws_new)⌝ -∗ *)
          ⌜Forall (λ ℓ', ℓ' ∈ dom hm) (flat_map locations (update_path_words off ws ws_new))⌝ -∗
          ⌜Forall (λ ℓ', ℓ' ∈ dom θ) (flat_map locations (update_path_words off ws ws_new))⌝ -∗
          rt_memaddr sr μ ↦[wms][a + 4 * N.of_nat off] flat_map serialise_i32 ns32' -∗
          words_interp θ μ ws_new ns' -∗
          rt_token_nophys rti sr lmask θ hm -∗
          |==> ℓ ↦heap (update_path_words off ws ws_new) ∗
               ℓ ↦addr (μ, a) ∗
               rt_token rti sr lmask θ).
  Proof.
    iIntros (slice) "%Hlenbdd Hrt Hpt Ha %Hlmask".
    open_rt "Hrt".
    iExists hm.
    iCombine "Hpt Hheap" gives "%Hhm".
    iCombine "Ha Haddr" gives "%Hθℓ".
    iPoseProof (heap_memory_dom_eq with "Hheapmem") as "%Hdomθhm".
    iPoseProof (heap_memory_delete _ ℓ _ _ ws with "Hheapmem") as "(HR & Hheapcont)"; eauto.
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
    iSplitL "Hroot Haddr Hlayout Hrti Hrootmem"; first by iFrame.
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
    iIntros (ws_new ns' ns32') "%Hlenws_new %Hns'' %Hlocshm %Hlocsθ Hphys' Hwords' Hnp".
    iMod (ghost_map_update (update_path_words off ws ws_new) with "Hheap Hpt") as "[Hheap' Hpt']".
    iModIntro.
    iFrame "Hpt' Ha".
    pose proof (Forall2_length _ _ _ Hns'') as Hns32'len.
    iPoseProof (big_sepL2_length with "Hwords'") as "%Hns'len".
    set (hm' := <[ℓ := update_path_words off ws ws_new]> hm).
    iAssert ((rt_token_nophys rti sr lmask θ hm')%I) with "[Hnp]" as "Hnp'".
    { iApply (rt_token_nophys_insert_heap_strong _ _ _ _ ws with "Hnp").
      - exact Hhm.
      - (* what I changed *) exact Hlmask.
      - exact Hlocshm.
      - exact Hlocsθ. }
    iApply (rt_token_putheap _ _ lmask θ hm' with "Hnp'").
    unfold rt_token_phys.
    iFrame.
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

End virt_to_phys_strong.
