From mathcomp Require Import eqtype ssrbool.

From Stdlib Require Import NArith.NArith.
Require Import RichWasm.util.
Require Import RichWasm.compiler.memory.
Require Import RichWasm.iris.numerics.
Require Import RichWasm.iris.runtime.
Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.case_ptr.
Require Import RichWasm.iris.logrel.path.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Ltac open_rt H :=
  iDestruct H
    as "(%rm & %lm & %hm &
         Haddr & Hroot & Hlayout & Hheap & Hrti & %Hinj & Hownmm &
         Howngc & %Hrootok & Hrootmem & %Hheapok & Hheapmem)".

Section load.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.


  Lemma atoms_interp_nil_inv vs :
    atoms_interp [] vs ⊣⊢ ⌜vs = []⌝ .
  Proof.
    iSplit.
    - setoid_rewrite big_sepL2_nil_inv_l.
      done.
    - iIntros (->); cbn; done.
  Qed.

  Lemma atoms_interp_cons_inv o os vs :
    ⊢ atoms_interp (o :: os) vs -∗ ∃ v vs', ⌜vs = v :: vs'⌝ ∗ atom_interp o v ∗ atoms_interp os vs'.
  Proof.
    iIntros "Hat".
    iEval (unfold atoms_interp) in "Hat".
    setoid_rewrite big_sepL2_cons_inv_l.
    iDestruct "Hat" as (v vs' Hvs) "(Hv & Hvs')".
    iExists v, vs'; iFrame; done.
  Qed.

  Lemma atoms_interp_length os vs :
    ⊢ atoms_interp os vs -∗ ⌜length os = length vs⌝.
  Proof.
    iApply big_sepL2_length.
  Qed.

  Lemma atoms_interp_one_inv o vs :
    atoms_interp [o] vs ⊣⊢ ∃ v, ⌜vs = [v]⌝ ∗ atom_interp o v.
  Proof.
    iSplit.
    - iIntros "Hvs".
      iPoseProof (atoms_interp_cons_inv with "Hvs") as (v vs' Heq) "[Hv Hnil]".
      rewrite atoms_interp_nil_inv.
      iDestruct "Hnil" as "%Hnil"; subst.
      iExists v; auto.
    - iIntros "(%v & -> & Hv)".
      cbn; auto.
  Qed.

  Lemma rep_ref_kind_ptr F κ μ β τ ρ ξ :
    has_kind F (RefT κ μ β τ) (VALTYPE ρ ξ) ->
    ρ = AtomR PtrR /\ exists ξ', κ = VALTYPE (AtomR PtrR) ξ'.
  Proof.
    intros Hkind.
    remember (RefT κ μ β τ) as ref.
    remember (VALTYPE ρ ξ) as val.
    revert Heqval Heqref.
    revert ρ ξ.
    induction Hkind using has_kind_ind'; intros; try congruence.
    - subst κ0.
      split; try congruence.
      inversion Heqref; eauto.
    - subst κ0.
      split; try congruence.
      inversion Heqref; eauto.
  Qed.

  Lemma Z_even_mod_even :
    forall n k : Z,
    Z.even k = true ->
    Z.even (n mod k) = Z.even n.
  Proof.
    intros n k Hk.
    apply Bool.eq_true_iff_eq.

    assert (Hk2 : (k mod 2)%Z = 0).
    { rewrite Zmod_even. by rewrite Hk. }
    destruct (Z.eq_dec k 0) as [Hk0 | Hk0].
    { subst. by rewrite Zmod_0_r. }

    rewrite (Z.mod_eq n k); last done.

    replace (n - k * (n / k))%Z with (n + (k * -(n / k)))%Z; last lia.
    rewrite Z.even_add_mul_even.
    2: { rewrite <- Z.even_spec. rewrite Zeven_mod. lia. }
    done.
  Qed.

  Lemma Z_Even_mod_Even :
    forall n k, Z.Even k -> Z.Even (n mod k) <-> Z.Even n.
  Proof.
    intros n k Hk.
    do 2 rewrite <- Z.even_spec.
    rewrite Z_even_mod_even; first done.
    by apply Z.even_spec.
  Qed.

  Lemma Z_mod_even_mod_2 :
    forall n k,
    Z.Even k ->
    ((n mod k) mod 2)%Z = (n mod 2)%Z.
  Proof.
    intros n k Hk.
    rewrite Zmod_even.
    rewrite Z_even_mod_even; last by rewrite Z.even_spec.
    symmetry.
    apply Zmod_even.
  Qed.

  Lemma mod32_mod2 (n: Z) :
    (((2 * n) mod 4294967296) mod 2)%Z = 0.
  Proof.
    rewrite Z_mod_even_mod_2; last by rewrite <- Z.even_spec.
    rewrite Zmod_even.
    by rewrite Z.even_even.
  Qed.

  Lemma wp_load_w_strict μ t off wt wl wt' wl' es ret :
    run_codegen (load_w mr μ t off) wt wl = inr (ret, wt', wl', es) ->
    ret = () /\
    wt' = [] /\
    wl' = [] /\
    forall ℓ ℓ32 memidx memidxN (f: frame) B R Φ v,
        N_i32_repr ℓ ℓ32 ->
        N_nat_repr memidx memidxN ->
        inst_memory (f_inst f) !! base_mem_idx mr μ = Some memidx ->
        types_agree t v ->
        ⊢ ∀ s E,
          ↪[frame] f -∗
          ↪[RUN] -∗
          memidxN ↦[wms][ℓ + byte_offset μ off]bits v -∗
          ▷ (memidxN↦[wms][ℓ + byte_offset μ off]bits v -∗ Φ f [v]) -∗
          CWP W.BI_const (VAL_int32 ℓ32) :: es @ s; E UNDER B; R {{ Φ }}.
  Proof.
    intros Hcg.
    unfold load_w in Hcg.
    inv_cg_emit Hcg; subst es wt' wl' ret.
    split; [auto|].
    split; [auto|].
    split; [auto|].
    intros * Hℓ Hmemidx Hmem Hty.
    iIntros (s E) "Hf Hrun Hptr HΦ".
    iApply (cwp_load with "[$] [$] [$] [$]"); eauto.
  Qed.

  Lemma mod_bound_nonzero (a b : N) :
    (a <> 0 ->
     a `mod` b = 0 ->
     b <= a)%N.
  Proof.
  Admitted.

  (* This version is looser about the offset in the points-to,
     but it needs to know that l mod 4 = 0 and l <> 0. *)
  Lemma wp_load_w μ t off wt wl wt' wl' es ret :
    run_codegen (load_w mr μ t off) wt wl = inr (ret, wt', wl', es) ->
    ret = () /\
    wt' = [] /\
    wl' = [] /\
    forall ℓ ℓ32 memidx memidxN (f: frame) B R Φ v,
        N_i32_repr (tag_address μ ℓ)%N ℓ32 ->
        N_nat_repr memidx memidxN ->
        inst_memory (f_inst f) !! base_mem_idx mr μ = Some memidx ->
        (ℓ `mod` 4 = 0)%N ->
        (ℓ <> 0)%N ->
        types_agree t v ->
        ⊢ ∀ s E,
          ↪[frame] f -∗
          ↪[RUN] -∗
          memidxN ↦[wms][ℓ + 4 * N.of_nat off] bits v -∗
          ▷ (memidxN↦[wms][ℓ + 4 * N.of_nat off] bits v -∗ Φ f [v]) -∗
          CWP W.BI_const (VAL_int32 ℓ32) :: es @ s; E UNDER B; R {{ Φ }}.
  Proof.
    intros Hcg.
    apply wp_load_w_strict in Hcg.
    intuition.
    iIntros (s E) "Hf Hrun Hv Hpost".
    assert (4 <= ℓ)%N.
    {
      by eapply mod_bound_nonzero.
    }
    assert ((ℓ + 4 * N.of_nat off = tag_address μ ℓ + byte_offset μ off)%N) as Heq.
    {
      destruct μ; cbn; unfold offset_mm, offset_gc; lia.
    }
    rewrite Heq.
    iApply (H3 with "[$] [$] [Hv] [Hpost]"); eauto.
  Qed.


  Lemma wp_ite_gc_ptr_ptr_cg_state i ts1 ts2 do_gc do_nongc ret wt wl wt' wl' es:
    run_codegen (ite_gc_ptr PtrR i (W.Tf ts1 ts2) do_gc do_nongc) wt wl = inr (ret, wt', wl', es) ->
    ∃ wt1 wt2 wt3 wl1 wl2 wl3 es1 es2 es3,
      run_codegen do_nongc wt wl = inr ((), wt1, wl1, es1) ∧
      run_codegen do_nongc (wt ++ wt1) (wl ++ wl1) = inr ((), wt2, wl2, es2) /\
        run_codegen do_gc (wt ++ wt1 ++ wt2) (wl ++ wl1 ++ wl2) = inr ((), wt3, wl3, es3) /\
      wt' = wt1 ++ wt2 ++ wt3 /\
      wl' = wl1 ++ wl2 ++ wl3.
  Proof.
    unfold ite_gc_ptr.
    intros Hcg.
    apply wp_ignore in Hcg.
    destruct Hcg as ([] & [ [] [[] []]] & Hcg).
    eapply cwp_case_ptr in Hcg; eauto.
    destruct Hcg as (?wt & ?wt & ?wt & ?wl & ?wl & ?wl & ?es & ?es & ?es & Hcg).
    destruct ret.
    exists wt0, wt1, wt2, wl0, wl1, wl2, es0, es1, es2.
    destruct Hcg as (Hnon1 & Hnon2 & Hgc & Hwt' & Hwl' & Hspec).
    eauto.
  Qed.


  Lemma wp_ite_gc_ptr_ptr i ts1 ts2 do_gc do_nongc ret wt wl wt' wl' es evs vs s E R L Φ f ptr n n32:
    run_codegen (ite_gc_ptr PtrR i (W.Tf ts1 ts2) do_gc do_nongc) wt wl = inr (ret, wt', wl', es) ->
    has_values evs vs ->
    length ts1 = length vs ->
    ptr_shaped ptr n ->
    N_i32_repr n n32 ->
    ∃ wt1 wt2 wt3 wl1 wl2 wl3 es1 es2 es3,
      run_codegen do_nongc wt wl = inr ((), wt1, wl1, es1) ∧
      run_codegen do_nongc (wt ++ wt1) (wl ++ wl1) = inr ((), wt2, wl2, es2) /\
      run_codegen do_gc (wt ++ wt1 ++ wt2) (wl ++ wl1 ++ wl2) = inr ((), wt3, wl3, es3) /\
      wt' = wt1 ++ wt2 ++ wt3 /\
      wl' = wl1 ++ wl2 ++ wl3 ∧
      ⊢ ↪[frame]f -∗
         ↪[RUN] -∗
        ⌜f_locs f !! localimm i = Some (VAL_int32 n32)⌝ -∗
        ▷ ( ↪[frame]f -∗
            ↪[RUN] -∗
           match ptr with
           | PtrInt _ => CWP evs ++ es1 @ s; E UNDER []; R {{ f; vs, Φ f vs }}
           | PtrHeap MemMM _ => CWP evs ++ es2 @ s; E UNDER []; R {{ f; vs, Φ f vs }}
           | PtrHeap MemGC _ => CWP evs ++ es3 @ s; E UNDER []; R {{ f; vs, Φ f vs }}
           end) -∗
        CWP evs ++ es @ s; E UNDER L; R {{ f; vs, Φ f vs }}.
  Proof.
    unfold ite_gc_ptr.
    intros Hcg Hevs Hlen.
    apply wp_ignore in Hcg.
    destruct Hcg as ([] & [ [] [[] []]] & Hcg).
    eapply cwp_case_ptr in Hcg; eauto.
    destruct Hcg as (?wt & ?wt & ?wt & ?wl & ?wl & ?wl & ?es & ?es & ?es & Hcg).
    destruct ret.
    exists wt0, wt1, wt2, wl0, wl1, wl2, es0, es1, es2.
    destruct Hcg as (Hnon1 & Hnon2 & Hgc & Hwt' & Hwl' & Hspec).
    split; first auto.
    split; first auto.
    split; first auto.
    split; first auto.
    split; first auto.
    iIntros "Hf Hrun %Hi Hbr".
    by iApply (Hspec with "[$] [$] [//] [$]").
  Qed.

  Lemma wp_ite_gc_ptr_nonptr ι i ts1 ts2 do_gc do_nongc ret wt wl wt' wl' es :
    ι <> PtrR ->
    run_codegen (ite_gc_ptr ι i (W.Tf ts1 ts2) do_gc do_nongc) wt wl = inr (ret, wt', wl', es) ->
    run_codegen (do_nongc) wt wl = inr (ret, wt', wl', es).
  Proof.
    intros Hι Hcg.
    destruct ι; solve [exfalso; by apply Hι | by apply Hcg].
  Qed.

  Lemma arep_types_agree ι o v :
    has_arep ι o ->
    atom_interp o v -∗
    ⌜types_agree (translate_arep ι) v⌝.
  Proof.
    destruct ι, o; cbn;
      iIntros "%Harep ->" || iIntros "%Harep Hat";
      auto.
    iDestruct "Hat" as "(%n & %n32 & %nrep & -> & _)".
    auto.
  Qed.

  Lemma extract_root_pointer a ℓ e rm :
    a ↦root ℓ -∗
    ghost_map_auth rw_root (1 / 2) rm -∗
    root_memory sr e rm -∗
    ⌜root_ok e rm⌝ -∗
    ∃ ah ah32,
      ⌜N_i32_repr ah ah32⌝ ∗
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
      as "(%ah & %bs & %Hbs & Hroot & Hsave)".
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
      iApply ("HΦ" with "[//] [$] [$] [$]"); eauto.
  Qed.

  Lemma wp_registerroot wt wl ret wt' wl' es_register :
    run_codegen (registerroot mr) wt wl = inr (ret, wt', wl', es_register) ->
    ret = () /\
    wt' = [] /\
    wl' = [] /\
      ∀ e evs ℓ ah ah32,
        repr_pointer e (PtrHeap MemGC ℓ) ah ->
        N_i32_repr ah ah32 ->
        has_values evs [VAL_int32 ah32] ->
      ⊢ ∀ f B R s E Φ,
        (∀ e' ar ar32,
           ⌜repr_root_pointer (RootHeap MemGC ar) (tag_address MemGC ar)⌝ -∗
           ar ↦root ℓ -∗ rt_token rti sr e' -∗ na_own logrel_nais E -∗
           ⌜N_i32_repr (tag_address MemGC ar) ar32⌝ -∗
           instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
           Φ f [VAL_int32 ar32]) -∗
        ↪[frame] f -∗
        ↪[RUN] -∗
        ⌜↑ns_fun (N.of_nat (sr_func_registerroot sr)) ⊆ E⌝ -∗
        na_own logrel_nais E  -∗
        rt_token rti sr e -∗
        instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
        CWP evs ++ es_register @ s; E UNDER B; R {{ Φ }}.
  Proof.
    unfold registerroot.
    intros Hcg.
    inv_cg_emit Hcg; subst.
    repeat (split; first done).
    intros * Hptr Hrah Hevs.
    iIntros (f B R s E Φ) "HΦ Hf Hrun %HE Htok Hrt Hreg".
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

  Lemma wp_duproot wt wl ret wt' wl' es_dup :
    run_codegen (duproot mr) wt wl = inr (ret, wt', wl', es_dup) ->
    ret = () /\
    wt' = [] /\
    wl' = [] /\
    ∀ evs a n n32 rm e ℓ,
      N_i32_repr n n32 →
      has_values evs [VAL_int32 n32] ->
      repr_root_pointer (RootHeap MemGC a) n ->
      root_ok e rm ->
      ⊢ ∀ s E B R Φ f,
        ↪[frame] f -∗
        ↪[RUN] -∗
        ⌜inst_memory (f_inst f) !! memimm (mr_gcmem mr) = Some (sr_mem_gc sr)⌝ -∗
        ⌜↑ns_fun (N.of_nat (sr_func_registerroot sr)) ⊆ E⌝ -∗
        a ↦root ℓ -∗
        ghost_map_auth rw_root (1 / 2) rm -∗
        root_memory sr e rm -∗
        (a ↦root ℓ -∗
         ghost_map_auth rw_root (1 / 2) rm -∗
         root_memory sr e rm -∗
         rt_token rti sr e) -∗
        na_own logrel_nais E -∗
        instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
        (∀ e' ar ar32,
           ⌜repr_root_pointer (RootHeap MemGC ar) (tag_address MemGC ar)⌝ -∗
           ⌜N_i32_repr (tag_address MemGC ar) ar32⌝ -∗
           ar ↦root ℓ -∗
           rt_token rti sr e' -∗
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
    iIntros (s E B R Φ f) "Hf Hrun %Hmems %Hmask Htok Hrootm Hrootok Hclose Hinv Hreg HΦ".
    rewrite app_assoc.
    iApply (cwp_seq with "[-Hinv Hreg HΦ]").
    {
      iApply (Hload with "[$] [$] [//] [$] [$] [$]").
      iIntros "!>" (ah ah32 Harep32) "Hroot Htok".
      instantiate (1:= (fun f' v' =>
                         ⌜f' = f⌝ ∗
                         ∃ ah' ah32',
                             ⌜N_i32_repr ah' ah32'⌝ ∗
                             ⌜v' = [VAL_int32 ah32']⌝ ∗
                             ⌜rm !! a = Some ℓ⌝ ∗
                             rt_token rti sr e
                         )%I).
      cbn.
      iIntros "Hrootm".
      iCombine "Hroot" "Htok" gives "%Hrm".
      iSplit; auto.
      iExists _, _.
      iSplit; auto.
      iSplit; auto.
      iSplit; auto.
      iApply ("Hclose" with "[$] [$] [$]").
    }
    cbn; iIntros (f' vs) "(-> & %ah & %ah32 & %Hah & -> & %Hrma & Htok) Hf Hrun".
    assert (repr_pointer e (PtrHeap MemGC a) n).
    {
      inversion Hreproot; subst.
      constructor; eauto.
      unfold root_ok in Hrootok.
      Print root_ok.
      admit. (* stuck here: need to know that e !! a = Some (MemGC, a), which seems wrong *)
    }
    iApply (Hreg with "[HΦ] [$Hf] [$Hrun] [] [$Hinv] [$Htok] [$Hreg]"); eauto.
    - admit.
    - iIntros (ar ar32 e' Har) "Hroot' Htok' Hown %Harrep".
      admit.
  Admitted.

  Definition mk_load1_frame fe f vloc v :=
    let vloc := localimm (W.Mk_localidx (fe_wlocal_offset fe + vloc)) in
    {| f_locs := <[vloc := v]> (f_locs f);
       f_inst := f_inst f |}.

  Lemma mk_load1_frame_stable_part fe f vloc v :
    ∀ i,
      i < fe_wlocal_offset fe + vloc ->
      f_locs (mk_load1_frame fe f vloc v) !! i = f_locs f !! i.
  Proof.
    intros i Hlt.
    cbn.
    rewrite list_lookup_insert_ne; [done | lia].
  Qed.

  Definition atom_copyable (o : atom) : Prop :=
    match o with
    | PtrA (PtrHeap MemMM ℓ) => False
    | _ => True
    end.

  Definition mk_load1_post o v v' : iProp Σ :=
    (∃ e', rt_token rti sr e' ∗
           atom_interp o v ∗
           atom_interp o v')%I.

  Definition congeal32 (ns : list i32) : option i32 :=
    match ns with
    | [n] => Some n
    | _ => None
    end.

  Definition congeal64 (ns : list i32) : option i64 :=
    match ns with
    | [n1; n2] =>
        let n1' := Wasm_int.Int32.unsigned n1 in
        let n2' := Wasm_int.Int32.unsigned n2 in
        Some (Wasm_int.Int64.repr (Z.shiftl n1' 32 + n2'))
    | _ => None
    end.

  Definition mk_float32 (i : i32) : f32 :=
    Wasm_float.FloatSize32.of_bits
      {| Integers.Int.intval := Wasm_int.Int32.intval i;
         Integers.Int.intrange := unkeyed (Wasm_int.Int32.intrange i) |}.

  Definition mk_float64 (i : i64) : f64 :=
    Wasm_float.FloatSize64.of_bits
      {| Integers.Int64.intval := Wasm_int.Int64.intval i;
         Integers.Int64.intrange := unkeyed (Wasm_int.Int64.intrange i) |}.

  Definition congeal_atom (ι : atomic_rep) (ns32 : list i32) : option value :=
    match ι with
    | PtrR
    | I32R => option_map VAL_int32 (congeal32 ns32)
    | I64R => option_map VAL_int64 (congeal64 ns32)
    | F32R => option_map (VAL_float32 ∘ mk_float32) (congeal32 ns32)
    | F64R => option_map (VAL_float64 ∘ mk_float64) (congeal64 ns32)
    end.

  Definition congeal_atoms (ιs : list atomic_rep) (nss32 : list (list i32)) : option (list value) :=
    mapM (curry congeal_atom) (zip ιs nss32).

  Lemma congeal_types_agree ι ns32 v :
    congeal_atom ι ns32 = Some v ->
    types_agree (translate_arep ι) v.
  Proof.
    induction ι; cbn; intros Hcong; destruct ns32 as [| ? [| ? [| ? ]]]; try done;
      cbn in Hcong; inversion Hcong; subst; done.
  Qed.

  Lemma gc_word_to_atom ι o ns ns32 v θ :
    ref_flag_atoms_interp GCRefs (SAtoms [o]) ->
    Forall2 N_i32_repr ns ns32 ->
    has_arep ι o ->
    congeal_atom ι ns32 = Some v ->
    words_interp θ MemMM (serialize_atom o) ns -∗
    atom_interp o v.
  Proof.
    intros Href Hns Harep Hv.
    iIntros "Hw".
    destruct o, ι; cbn in Harep; try done.
    - inversion Href; subst.
      cbn in *.
      destruct ns32 as [| n32 [| n' ns']];
        cbn in Hv; inversion Hv; subst.
      apply Forall2_cons_inv_r in Hns.
      destruct Hns as (n & ns' & Hnrep & Hbad & ->).
      inversion Hbad; subst.
      rewrite big_sepL2_singleton.
      cbn.
      destruct p as [ | [|]]; cbn in *; try done.
      + iDestruct "Hw" as "%Hw".
        inversion Hw; subst.
        rename n0 into n.
        iExists (2 * n)%N, n32.
        iSplit; eauto.
        iSplit; eauto.
        iExists (RootInt n).
        cbn.
        iPureIntro; split; eauto.
        constructor.
      + iDestruct "Hw" as "(%a & %Ha & Hroot)".
        iExists _, _; eauto.
    - cbn.
      iPoseProof (big_sepL2_cons_inv_l with "Hw") as "(%n' & %ns' & %Hns' & Hn & Hns)".
      cbn.
      iPoseProof (big_sepL2_nil_inv_l with "Hns") as "->".
      subst.
      iDestruct "Hn" as "->".
      destruct ns32 as [| ? [| ? ?]]; cbn in Hv; inversion Hv; subst.
      inversion Hns; subst.
      iPureIntro. f_equal.
      eapply N_i32_repr_inj2; eauto.
      done.
    - admit.
    - cbn.
      iPoseProof (big_sepL2_cons_inv_l with "Hw") as "(%n' & %ns' & %Hns' & Hn & Hns)".
      cbn.
      iPoseProof (big_sepL2_nil_inv_l with "Hns") as "->".
      subst.
      iDestruct "Hn" as "->".
      destruct ns32 as [| ? [| ? ?]]; cbn in Hv; inversion Hv; subst.
      inversion Hns; subst.
      iPureIntro.
      admit.
    - admit.
  Admitted.

  Definition mk_load1_frame' fe f vloc v :=
    let vloc := localimm (W.Mk_localidx (fe_wlocal_offset fe + vloc)) in
    {| f_locs := <[vloc := v]> (f_locs f);
       f_inst := f_inst f |}.

  Definition rt_token_phys θ hm : iProp Σ :=
      ghost_map_auth rw_addr (1/2) θ ∗
      heap_memory sr θ hm ∗
      ghost_map_auth rw_heap 1 hm.

  Definition rt_token_nophys (θ : address_map) hm : iProp Σ :=
    ∃ rm lm,
      ghost_map_auth rw_root (1/2) rm ∗
      ghost_map_auth rw_layout (1/2) lm ∗
      rti θ rm lm ∗
      ⌜gmap_injective θ⌝ ∗
      own_addr_mm θ hm ∗
      own_addr_gc θ ∗
      ⌜root_ok θ rm⌝ ∗
      root_memory sr θ rm ∗
      ⌜heap_ok θ lm hm⌝.

  Lemma rt_token_getheap θ :
    rt_token rti sr θ -∗
    ∃ hm,
      rt_token_phys θ hm ∗
      rt_token_nophys θ hm.
  Proof.
    iIntros "Hrt".
    open_rt "Hrt".
    by iFrame.
  Qed.

  Lemma rt_token_putheap θ hm :
    rt_token_nophys θ hm -∗
    rt_token_phys θ hm -∗
    rt_token rti sr θ.
  Proof.
    iIntros "Hnph Hph".
    iDestruct "Hnph" as "(%rm & %lm & Hnoheap)".
    iDestruct "Hph" as "(? & ? & ?)".
    iExists rm, lm, hm.
    by iFrame.
  Qed.

  Lemma virt_to_phys_acc ℓ μ a θ ws :
    let R ns ns32 :=
      (⌜Forall2 N_i32_repr ns ns32⌝ ∗
       rt_memaddr sr μ↦[wms][a]flat_map serialise_i32 ns32 ∗
       words_interp θ μ ws ns)%I in
    ⊢ rt_token rti sr θ -∗
      ℓ ↦heap ws -∗
      ℓ ↦addr (μ, a) -∗
      ∃ hm,
        rt_token_nophys θ hm ∗
        (∃ ns ns32, R ns ns32) ∗
        (∀ ns' ns32',
          R ns' ns32' -∗
          rt_token_nophys θ hm -∗
          ℓ ↦heap ws ∗
          ℓ ↦addr (μ, a) ∗
          rt_token rti sr θ).
  Proof.
    iIntros (R) "Hrt Hpt Ha".
    open_rt "Hrt".
    iExists hm.
    iCombine "Hpt Hheap" gives "%Hhm".
    iCombine "Ha Haddr" gives "%Ha".
    iPoseProof (big_sepM2_lookup_acc with "Hheapmem") as "Hlookup"; eauto.
    iEval (cbn) in "Hlookup".
    iSplitL "Hroot Hlayout Hrti Hownmm Howngc Hrootmem"; first by iFrame.
    iDestruct "Hlookup" as "(HR & Hcont)".
    iSplitL "HR"; first by iApply "HR".
    iIntros (ns ns32) "HR Hnp".
    iPoseProof ("Hcont" with "[$HR]") as "Hclosed".
    iSplitL "Hpt"; first iFrame.
    iSplitL "Ha"; first iFrame.
    iApply (rt_token_putheap with "[$]").
    iFrame.
  Qed.

  Lemma virt_to_phys_slice_acc off sz ℓ μ a θ ws :
    let slice {A} (x : list A) := take sz (drop off x) in
    let R ns ns32 :=
      (⌜Forall2 N_i32_repr ns ns32⌝ ∗
       rt_memaddr sr μ↦[wms][a + 4 * N.of_nat off]flat_map serialise_i32 ns32 ∗
       words_interp θ μ (slice ws) ns)%I in
    ⊢ rt_token rti sr θ -∗
      ℓ ↦heap ws -∗
      ℓ ↦addr (μ, a) -∗
      ∃ hm,
        rt_token_nophys θ hm ∗
        (∃ ns ns32, R ns ns32) ∗
        (∀ ns' ns32',
          R ns' ns32' -∗
          rt_token_nophys θ hm -∗
          ℓ ↦heap ws ∗
          ℓ ↦addr (μ, a) ∗
          rt_token rti sr θ).
  Proof.
  Admitted.

  Lemma len_ser32 ns :
    (length (flat_map serialise_i32 ns) = 4 * length ns)%nat.
  Proof.
    induction ns.
    - done.
    - unfold serialise_i32.
      cbn -[Nat.mul].
      rewrite length_app.
      rewrite Memdata.encode_int_length.
      rewrite IHns.
      cbn.
      lia.
  Qed.

  Lemma has_arep_size ι o :
    has_arep ι o ->
    length (serialize_atom o) = arep_size ι.
  Proof.
    destruct ι, o; intros H; done.
  Qed.

  Definition ptr_root
    (θ : address_map) (μ : base_memory) (o : atom) (v : value) : iProp Σ :=
    match o with
    | PtrA p =>
        ∃ n n32,
          ⌜N_i32_repr n n32⌝ ∗
          ⌜v = VAL_int32 n32⌝ ∗
          match μ, p with
          | MemMM, PtrHeap MemGC ℓ =>
              ∃ a, ⌜repr_root_pointer (RootHeap MemGC a) n⌝ ∗ a ↦root ℓ
          | _, _ => ⌜repr_pointer θ p n⌝
          end
    | I32A n => ⌜v = VAL_int32 n⌝
    | I64A n => ⌜v = VAL_int64 n⌝
    | F32A n => ⌜v = VAL_float32 n⌝
    | F64A n => ⌜v = VAL_float64 n⌝
    end.


  Lemma get_path_words1 off ws :
    off + 1 <= length ws ->
    ∃ w, get_path_words off 1 ws = [w].
  Proof.
    intros Hlen.
    unfold get_path_words.
    destruct (drop off ws) as [| w' ws'] eqn:Hdrop;
      pose proof (f_equal length Hdrop) as Hdroplen;
      rewrite length_drop in Hdroplen;
      cbn in Hdroplen.
    - lia.
    - eexists; done.
  Qed.

  Ltac do_get_path_words1 w :=
     let H := fresh "Hpath" in
     pose proof (get_path_words1 _ _ ltac:(eauto)) as [w H];
     rewrite H.

  Lemma get_path_words2 off ws :
    off + 2 <= length ws ->
    ∃ w1 w2, get_path_words off 2 ws = [w1; w2].
  Proof.
    intros Hlen.
    unfold get_path_words.
    destruct (drop off ws) as [| w' [| w'' ws']] eqn:Hdrop;
      pose proof (f_equal length Hdrop) as Hdroplen;
      rewrite length_drop in Hdroplen;
      cbn in Hdroplen;
      try lia.
    eexists; eexists; done.
  Qed.

  (* not the most informative option here. we will want to know that
     [atom_interp o v] eventually... *)
  Lemma reconstitute_val θ μ o ws off ι ns ns32 :
    "Hws" ∷ words_interp θ μ (get_path_words off (arep_size ι) ws) ns -∗
    "%Hbound" ∷ ⌜off + arep_size ι <= length ws⌝ -∗
    "%Harep" ∷ ⌜has_arep ι o⌝ -∗
    "%Hser" ∷ ⌜serialize_atom o = get_path_words off (arep_size ι) ws⌝ -∗
    "%Hns" ∷ ⌜Forall2 N_i32_repr ns ns32⌝ -∗
    ∃ v, ⌜flat_map serialise_i32 ns32 = bits v⌝ ∗
         atom_interp_weak θ μ o v ∗
         (atom_interp_weak θ μ o v -∗
          words_interp θ μ (get_path_words off (arep_size ι) ws) ns).
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
      + iIntros "(%n' & %n32' & %Hrep' & %Hn32' & H'')".
        rewrite deserialise_serialise_i32 in Hn32'.
        inversion Hn32'; subst n32'.
        by rewrite (N_i32_repr_inj n32 n n').
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

  Lemma atom_interp_weak_types_agree ι o μ e v :
    "%Harep" ∷ ⌜has_arep ι o⌝ -∗
    "Hat" ∷ atom_interp_weak e μ o v -∗
     ⌜types_agree (translate_arep ι) v⌝.
  Proof.
    repeat iIntros "@".
    destruct o, ι; try done; cbn [atom_interp_weak];
      try (iDestruct "Hat" as "->"; done).
    by iDestruct "Hat" as "(%n & %n32 & _ & -> & _)".
  Qed.

  Lemma atom_interp_weak_ptr_shaped θ μ p v :
    atom_interp_weak θ μ (PtrA p) v -∗
    ⌜∃ n n32, v = VAL_int32 n32 /\ N_i32_repr n n32 /\ ptr_shaped p n⌝.
  Proof.
    iIntros "(%n & %n32 & %Hrep & %Heq & H)".
    subst.
    iExists n, n32.
    iSplit; eauto.
    iSplit; eauto.
    destruct μ, p; try destruct μ; cbn;
      try (iDestruct "H" as "%H"; iPureIntro; inversion H; subst; constructor; eauto).
    iDestruct "H" as "(%a & %repr & _)".
    iPureIntro.
    inversion repr; subst; constructor; eauto.
  Qed.

  Lemma wp_load1_copy_mm (se : @semantic_env Σ) F lidx off ι wt wl ret wt' wl' es :
    let fe := fe_of_context F in
    run_codegen (memory.load1 mr fe MemMM Copy lidx off ι) wt wl = inr (ret, wt', wl', es) ->
    ∀ f ℓ a32 a o ws s E B R e Φ,
    ⊢ "Hptr" ∷ ℓ ↦heap ws -∗
      "Haddr" ∷ ℓ ↦addr (MemMM, a) -∗
      "Hown"  ∷ na_own logrel_nais E -∗
      "Htok"  ∷ rt_token rti sr e -∗
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
        (∀ e' vf v,
           let f' := mk_load1_frame fe f (length wl) vf in
           "Hptr"  ∷ ℓ ↦heap ws -∗
           "Haddr" ∷ ℓ ↦addr (MemMM, a) -∗
           "Hown"  ∷ na_own logrel_nais E -∗
           "Htok"  ∷ rt_token rti sr e' -∗
           "Hregf" ∷ instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
           "Ho"    ∷ (⌜atom_copyable o⌝ -∗ atom_interp o v) -∗
           Φ f' [v]) -∗
      "Hf" ∷ ↪[frame] f -∗
      "Hrun" ∷ ↪[RUN] -∗
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
    iPoseProof (virt_to_phys_slice_acc off (arep_size ι) with "[$] [$] [$]")
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
        iAssert (ℓ ↦heap ws ∗ ℓ ↦addr (MemMM, a) ∗ rt_token rti sr e)%I with "[Hclose Hphys Hwords Hnp]" as "(Hheap & Haddr & Htok)".
        {
          unfold PHYS.
          rewrite -Hserws.
          iApply ("Hclose" with "[Hphys Hwords] [$]").
          by iFrame.
        }
        iApply ("HΦ" with "[$] [$] [$] [$] [$] [-]").
        by iIntros "_".
      + iApply (cwp_val with "[$] [$]"); eauto using has_values_to_consts.
        iPoseProof ("Hret" with "Hat") as "Hwords".
        iAssert (ℓ ↦heap ws ∗ ℓ ↦addr (MemMM, a) ∗ rt_token rti sr e)%I with "[Hclose Hphys Hwords Hnp]" as "(Hheap & Haddr & Htok)".
        {
          unfold PHYS.
          rewrite -Hserws.
          iApply ("Hclose" with "[Hphys Hwords] [$]"); by iFrame.
        }
        iApply ("HΦ" with "[$] [$] [$] [$] [$] [-]").
        by iIntros "Hcontra".
      + iEval (cbn) in "Hat".
        iDestruct "Hat" as "(%n & %n32 & %Hn32 & %Hpn32' & (%ar & %Har & Hrt))".
        apply wp_duproot in Hcg3.
        destruct Hcg3 as (_ & -> & -> & Hduproot).
        clear Hes_rest2.
        iDestruct "Hnp" as "(%rm & %lm & Hroot & Hlayout & Hrti & Hinj & Hownmm & Howngc & Hrest)".
        iDestruct "Hrest" as "(%Hrootok & Hrootmem & Hheapok)".
        iCombine "Hrt" "Hroot" gives "%Hrm".
        iApply (Hduproot with "[$] [$] [//] [//] [] [$] [$]"); eauto.
        * apply Is_true_true.
          inversion Hpn32'.
          eapply has_values_to_consts.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
    - eapply wp_ite_gc_ptr_nonptr in Hcompile; last assumption.
      inv_cg_ret Hcompile; subst.
      clear_nils.
      iApply (cwp_val with "[$] [$]"); eauto using has_values_to_consts.
      unfold has_arep in *.
      assert (Persistent (atom_interp o v)).
      {
        apply atom_interp_dup.
        by destruct o, ι.
      }
  Admitted.

  Lemma wp_mem_load1_copy_mm_cg_state
    fe lidx off ι wt wl ret wt' wl' es :
    run_codegen (memory.load1 mr fe MemMM Copy lidx off ι) wt wl = inr (ret, wt', wl', es) ->
    ret = () ∧ wt' = [] ∧ wl' = [translate_arep ι].
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
    inversion Hidx; subst n.
    inv_cg_emit Hget; subst.
    inv_cg_emit Hsave; subst.
    clear Hretval Hretval0.
    clear_nils.
    destruct (atomic_rep_eq_dec ι PtrR); subst.
    - eapply wp_ite_gc_ptr_ptr_cg_state in Hcompile; eauto.
      destruct Hcompile as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hdup & -> & ->).
      inv_cg_ret  H.
      inv_cg_ret  H0.
      subst; clear_nils.
      apply wp_duproot in Hdup.
      destruct Hdup as (_ & -> & -> & _).
      by destruct ret.
    - apply wp_ite_gc_ptr_nonptr in Hcompile; eauto.
      inv_cg_ret Hcompile; eauto.
  Qed.

  Lemma inv_foldlM_nil {A B} (f : A → B → codegen A) (a : A) wt wl a' wt' wl' es :
    run_codegen (foldlM f a []) wt wl = inr (a', wt', wl', es) ->
    a' = a /\
    wt' = [] /\
    wl' = [] /\
    es = [].
  Proof.
    cbn.
    intros Heq.
    by inversion Heq.
  Qed.

  Lemma inv_foldlM_rcons {A B} (f : A → B → codegen A) (b : B) (bs : list B) (a : A) wt wl a' wt' wl' es :
    run_codegen (foldlM f a (seq.rcons bs b)) wt wl = inr (a', wt', wl', es) ->
    ∃ a0 wt_b wt_bs wl_b wl_bs es_b es_bs,
      run_codegen (foldlM f a bs) wt wl = inr (a0, wt_bs, wl_bs, es_bs) ∧
      run_codegen (f a0 b) (wt ++ wt_bs) (wl ++ wl_bs) = inr (a', wt_b, wl_b, es_b) /\
      wt' = wt_bs ++ wt_b ∧
      wl' = wl_bs ++ wl_b ∧
      es = es_bs ++ es_b.
  Proof.
    intros Hcg.
    unfold foldlM in Hcg.
    rewrite seq.foldl_rcons in Hcg.
    inv_cg_bind Hcg a0 wt_bs wt_b wl_bs wl_b es_bs es_b Hbs Hfb.
    exists a0. repeat eexists; eauto.
  Qed.

  Lemma Forall2_rcons_inv_l:
    ∀ {A B : Type} (P : A → B → Prop) (x : A) (l : list A) (k : list B),
      Forall2 P (seq.rcons l x) k → ∃ (y : B) (k' : list B), P x y ∧ Forall2 P l k' ∧ k = seq.rcons k' y.
  Proof.
  Admitted.

  Lemma big_sepL2_rcons_inv_l:
    ∀ {PROP : bi} {A B : Type} (Φ : nat → A → B → PROP) (x1 : A) (l1 : list A) (l2 : list B),
      ([∗ list] k↦y1;y2 ∈ (seq.rcons l1 x1);l2, Φ k y1 y2)
      ⊢ ∃ (x2 : B) (l2' : list B),
          ⌜l2 = seq.rcons l2' x2⌝ ∧ Φ 0 x1 x2 ∗ ([∗ list] k↦y1;y2 ∈ l1;l2', Φ (S k) y1 y2).
  Proof.
  Admitted.

  Lemma big_sepL2_rcons_inv_r :
    ∀ {PROP: bi} {A B : Type} (Φ : nat → A → B → PROP) (x2 : B) (l1 : list A) (l2 : list B),
         ([∗ list] k↦y1;y2 ∈ l1;(seq.rcons l2 x2), Φ k y1 y2)
         ⊢ ∃ (x1 : A) (l1' : list A),
             ⌜l1 = seq.rcons l1' x1⌝ ∧ Φ 0 x1 x2 ∗ ([∗ list] k↦y1;y2 ∈ l1';l2, Φ (S k) y1 y2).
  Proof.
  Admitted.

  Lemma big_sepL2_rcons :
    ∀ {PROP : bi} {A B : Type} (Φ : nat → A → B → PROP) (x1 : A) (x2 : B) (l1 : list A) (l2 : list B),
      ([∗ list] k↦y1;y2 ∈ (seq.rcons l1 x1);(seq.rcons l2 x2), Φ k y1 y2) ⊣⊢ Φ 0 x1 x2 ∗ ([∗ list] k↦y1;y2 ∈ l1;l2, Φ (S k) y1 y2).
  Proof.
  Admitted.

  Lemma foldl_map :
    ∀ A B (f : A → B) l,
      seq.map f l = seq.foldl (λ l' a, seq.rcons l' (f a)) [] l.
  Proof.
    induction l as [| l x] using seq.last_ind; intros *.
    - reflexivity.
    - rewrite seq.foldl_rcons.
      rewrite seq.map_rcons.
      congruence.
  Qed.

  Definition mk_load_frame fe f (wl : wlocal_ctx) (vs : list value) :=
    let vvs := imap (λ i v, (v, length wl + i)) vs in
    seq.foldl (λ f '(v, vloc), mk_load1_frame fe f vloc v) f vvs.

  Lemma load1_frame_inst fe f v vloc :
    f_inst (mk_load1_frame fe f v vloc) = f_inst f.
  Proof.
    done.
  Qed.

  Lemma load1_frame_length fe f v vloc :
    length (f_locs (mk_load1_frame fe f vloc v)) = length (f_locs f).
  Proof.
    by rewrite length_insert.
  Qed.

  Lemma imap_rcons A B (x : A) (xs : list A) (f: nat -> A -> B) :
    imap f (seq.rcons xs x) = seq.rcons (imap f xs) (f (length xs) x).
  Proof.
    revert f.
    induction xs; intros f.
    - done.
    - cbn.
      f_equal.
      by rewrite IHxs.
  Qed.

  Lemma load_frame_inst fe f wl vs :
    f_inst (mk_load_frame fe f wl vs) = f_inst f.
  Proof.
    induction vs using seq.last_ind; cbn.
    - tauto.
    - unfold mk_load_frame.
      rewrite imap_rcons.
      rewrite seq.foldl_rcons.
      rewrite load1_frame_inst.
      apply IHvs.
  Qed.

  Lemma load_frame_length fe f wl vs :
    length (f_locs (mk_load_frame fe f wl vs)) = length (f_locs f).
  Proof.
    induction vs using seq.last_ind; cbn.
    - tauto.
    - unfold mk_load_frame.
      by rewrite imap_rcons seq.foldl_rcons load1_frame_length IHvs.
  Qed.

  Lemma mk_load_frame_stable_part fe f wl vs :
    ∀ i,
      i < fe_wlocal_offset fe + length wl  ->
      f_locs (mk_load_frame fe f wl vs) !! i = f_locs f !! i.
  Proof.
    induction vs using seq.last_ind; cbn.
    - tauto.
    - unfold mk_load_frame.
      intros i Hlt.
      rewrite imap_rcons seq.foldl_rcons.
      rewrite mk_load1_frame_stable_part; [|lia].
      by rewrite IHvs.
  Qed.

  Definition mk_load_post os (vs vs' : list value) : iProp Σ :=
    (⌜seq.size vs = seq.size vs'⌝ ∗
    [∗ list] o; '(v, v') ∈ os; (seq.zip vs vs'),
         (⌜atom_copyable o⌝ -∗ atom_interp o v) ∗
         atom_interp o v')%I.

  Lemma frame_ext : forall f f',
    f_inst f = f_inst f' ->
    f_locs f = f_locs f' ->
    f = f'.
  Proof.
    intros [i l] [i' l']; cbn; congruence.
  Qed.

  Lemma congeal_rcons ιs ι nss ns vs :
    congeal_atoms (seq.rcons ιs ι) (seq.rcons nss ns) = Some vs ->
    exists vs' v, vs = seq.rcons vs' v /\ congeal_atoms ιs nss = Some vs' /\ congeal_atom ι ns = Some v.
  Proof.
  Admitted.

  Lemma ref_flag_atoms_interp_rcons:
    ∀ (ξ : ref_flag) (o : atom) (os : list atom),
      ref_flag_atoms_interp ξ (SAtoms (seq.rcons os o)) ↔
      forall_ptr_atom (ref_flag_ptr_interp ξ) o ∧ ref_flag_atoms_interp ξ (SAtoms os).
  Proof.
  Admitted.

  (* memory.load uses an ignore, so we have to use this lemma for the inductive proof *)
  Lemma wp_mem_load_copy_mm_inner fe lidx ιs :
    ∀ off wt wl ret wt' wl' es,
      run_codegen
        (foldlM
           (λ off' ι, load1 mr fe MemMM Copy lidx off' ι;; Monad.ret (off' + arep_size ι))
           off ιs)
        wt wl = inr (ret, wt', wl', es) →
      ret = seq.foldl (λ off' ι, off' + arep_size ι) off ιs ∧
      wt' = [] ∧
      wl' = map translate_arep ιs ∧
      ∀ ℓ ℓ32 memidx memidxN f E,
        N_i32_repr ℓ ℓ32 →
        inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some memidx →
        inst_memory (f_inst f) !! memimm (mr_gcmem mr) = Some (sr_mem_gc sr) →
        N_nat_repr memidx memidxN →
        ↑ns_fun (N.of_nat (sr_func_registerroot sr)) ⊆ E →
        f_locs f !! localimm lidx = Some (VAL_int32 ℓ32) →
        localimm lidx < fe_wlocal_offset fe + length wl ->
        fe_wlocal_offset fe + length wl + length wl' <= length (f_locs f) ->
        ∀ os nss nss32 vs,
          Forall2 has_arep ιs os →
          Forall2 (Forall2 N_i32_repr) nss nss32 ->
          congeal_atoms ιs nss32 = Some vs ->
          ref_flag_atoms_interp GCRefs (SAtoms os) ->
          ⊢ ∀ e,
            na_own logrel_nais E  -∗
            rt_token rti sr e -∗
            instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
            ([∗ list] o; ns ∈ os; nss, words_interp e MemMM (serialize_atom o) ns) -∗
            let offs := snd $ seq.foldl (λ '(off', offs) ι, (off' + arep_size ι, seq.rcons offs off'))
                                                       (off, []) ιs in
            ([∗ list] off'; v ∈ offs; vs, memidxN ↦[wms][ℓ + byte_offset MemMM off'] bits v) -∗
            ∀ Φ B R,
              ↪[frame] f -∗
              ↪[RUN] -∗
              (∀ f' e' vs',
                ⌜f' = mk_load_frame fe f wl vs⌝ -∗
                na_own logrel_nais E  -∗
                rt_token rti sr e' -∗
                instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
                ([∗ list] off'; v ∈ offs; vs, memidxN ↦[wms][ℓ + byte_offset MemMM off'] bits v) -∗
                mk_load_post os vs vs' -∗
                Φ f' vs') -∗
              CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
    induction ιs as [| ιs ι] using seq.last_ind; intros * Hcg.
    - apply inv_foldlM_nil in Hcg.
      destruct Hcg as (-> & -> & -> & ->).
      intuition.
      iIntros (e) "Hown Htok Hinst Hats Hpts".
      apply Forall2_nil_inv_l in H7.
      subst os.
      iPoseProof (big_sepL2_nil_inv_l with "Hats") as "%Hnil".
      subst nss.
      cbn in H9.
      inversion H9; subst.
      iIntros (Φ B R) "Hf Hrun HΦ".
      iApply (cwp_nil with "[$] [$]").
      iApply ("HΦ" with "[//] [$] [$] [$] [//] []").
      unfold mk_load_post.
      cbn.
      by iFrame.
    - apply inv_foldlM_rcons in Hcg.
      rewrite seq.foldl_rcons.
      destruct Hcg as (off_ιs & wt_ι & wt_ιs & wl_ι & wl_ιs & es_ι & es_ιs & Hinit & Hlast).
      destruct Hlast as (Hlast & -> & -> & ->).
      inv_cg_bind Hlast a0' wt_bs wt_b wl_bs wl_b es_bs es_b Hbs Hfb.
      subst.
      inv_cg_ret Hfb; subst.
      eapply IHιs in Hinit.
      destruct Hinit as (-> & -> & -> & Hinit).
      pose proof Hbs as Hbs'.
      eapply wp_mem_load1_copy_mm_cg_state in Hbs'.
      destruct Hbs' as (-> & -> & ->).
      subst; clear_nils.
      repeat (split; first by auto).
      split.
      {
        change map with @seq.map.
        by rewrite seq.map_rcons -seq.cats1 W.cat_app.
      }
      intros ℓ ℓ32 memidx memidxN f E Hrepℓ Hgcmem Hmmmem Hrepmemidx Hmask Hlidx Hbd.
      specialize (Hinit ℓ ℓ32 memidx memidxN f E Hrepℓ Hgcmem Hmmmem Hrepmemidx Hmask Hlidx Hbd).
      intros Hfe os nss nss32 vs Hareps Hnss Hcong Hgc.
      rewrite length_app in Hfe.
      specialize (Hinit ltac:(lia)).
      iIntros (e) "Hown Htok Hinst Hats Hpts".
      iIntros (Φ B R) "Hf Hrun HΦ".
      apply Forall2_rcons_inv_l in Hareps.
      destruct Hareps as (o & os' & Harep & Hareps & ->).
      rename os' into os.
      iPoseProof (big_sepL2_rcons_inv_l with "Hats") as "(%ns & %nss' & %Heqns & Hat & Hats)".
      subst nss.
      apply Forall2_rcons_inv_l in Hnss.
      destruct Hnss as (ns32 & nss32' & Hns32 & Hnss32' & ->).
      apply congeal_rcons in Hcong.
      destruct Hcong as (vs'' & v'' & -> & Hats & Hat).
      rewrite ref_flag_atoms_interp_rcons in Hgc.
      destruct Hgc as [Hgc1 Hgc2].
      iPoseProof (big_sepL2_rcons_inv_r with "Hpts") as "(%off0 & %offs' & %Heq & Hpt & Hpts)".
      rewrite seq.foldl_rcons in Heq.
      destruct (seq.foldl _ _ _) as [off' offs] eqn:Heqf.
      eapply seq.rcons_inj in Heq; inversion Heq; subst offs' off0; clear Heq.
      iPoseProof (Hinit with "Hown Htok Hinst Hats Hpts") as "Hinit"; eauto.
      cbn [snd].
      cbn.
      (* This should be factored out... *)
      assert (Hfolds : ∀ ιs off off' offs,
                 seq.foldl (λ '(off', offs) ι, (off' + arep_size ι, seq.rcons offs off'))
                   (off, [])
                   ιs =
                   (off', offs) →
                 off' = seq.foldl (λ (off'0 : nat) (ι0 : atomic_rep), off'0 + arep_size ι0) off ιs).
      {
        repeat match goal with H : _ |- _ => clear H end.
        induction ιs using seq.last_ind;
          intros off off' offs; cbn.
        - intros Heq; by inversion Heq.
        - intros Heq.
          rewrite seq.foldl_rcons in Heq.
          destruct (seq.foldl _ _ ιs) eqn:Heq'.
          inversion Heq; subst; clear Heq.
          specialize (IHιs _ _ _ Heq').
          by rewrite IHιs seq.foldl_rcons.
      }
      iApply (cwp_seq with "[Hinit Hf Hrun] [-]").
      + iApply ("Hinit" with "[$] [$]").
        instantiate (1 := (λ f' vs',
                            ⌜f' = mk_load_frame fe f wl vs''⌝ ∗
                 ∃ e'', na_own logrel_nais E ∗ rt_token rti sr e'' ∗
                 instance_rt_func_interp (mr_func_registerroot mr) (sr_func_registerroot sr)
                   (spec_registerroot rti sr) (f_inst f) ∗
                   ([∗ list] off'0;v ∈ offs;vs'', memidxN↦[wms][ℓ + byte_offset MemMM off'0] bits v) ∗
                    mk_load_post os vs'' vs')%I).
        cbn.
        iIntros (f' e' vs') "-> Hown Htok Hinst Hpts HΦ".
        by iFrame.
      + iIntros (f' vs') "(%Hinst & %e' & Hown & Htok & #Hinst & Hpts & Hpost) Hf Hrun".
        iApply cwp_val_app; first eauto using has_values_to_consts.
        cbn.
        admit.
        (*
        iApply (wp_mem_load1_copy_mm with "[$] [$] [] [//] [$] [Hpt] [$Hown] [$Htok] [Hinst]"); first eauto;
          first apply Hrepℓ; first apply Hrepmemidx; (by rewrite Hinst load_frame_inst) || eauto.
        {
          rewrite length_app Hinst load_frame_length.
          lia.
        }
        { by rewrite Hinst mk_load_frame_stable_part. }
        {
          admit.
        }
        {
          cbn.
          apply Hfolds in Heqf.
          by rewrite Heqf.
        }
        iIntros "#Hinst' Hpt Hown %e'0 %v' Htok Hov Hov'".
        unfold fvs_combine.
        replace (vs' ++ [v']) with (seq.rcons vs' v')
          by (rewrite <- seq.cats1; done).
        iDestruct "Hpost" as "(%Hvsvs' & Hpost)".
        iApply ("HΦ" with "[] [$Hown] [$] [$] [Hpts Hpt] [-]").
        * iPureIntro.
          rewrite Hinst.
          apply frame_ext.
          -- rewrite !load_frame_inst. done.
          -- unfold mk_load_frame, mk_load1_frame.
             rewrite !imap_rcons !seq.foldl_rcons.
             cbn.
             rewrite length_app length_map.
             replace (length ιs) with (length vs''); first done.
             erewrite (Forall2_length _ _ _ Hareps).
             admit.
        * rewrite seq.foldl_rcons.
          cbn.
          rewrite !Heqf big_sepL2_rcons.
          rewrite -(Hfolds ιs off off' offs ltac:(eauto)).
          iFrame.
        * unfold mk_load_post.
          iSplit; first by rewrite !seq.size_rcons Hvsvs'.
          rewrite seq.zip_rcons; last done.
          rewrite big_sepL2_rcons.
          iFrame.
        *)
  Admitted.

  Lemma wp_mem_load_copy_mm fe lidx ιs off wt wl ret wt' wl' es :
    run_codegen (memory.load mr fe MemMM Copy lidx off ιs) wt wl = inr (ret, wt', wl', es) ->
    ret = tt /\
    wt' = [] ∧
    wl' = map translate_arep ιs ∧
    ∀ ℓ ℓ32 memidx memidxN f E,
      N_i32_repr ℓ ℓ32 →
      inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some memidx →
      inst_memory (f_inst f) !! memimm (mr_gcmem mr) = Some (sr_mem_gc sr) →
      N_nat_repr memidx memidxN →
      ↑ns_fun (N.of_nat (sr_func_registerroot sr)) ⊆ E →
      f_locs f !! localimm lidx = Some (VAL_int32 ℓ32) →
      localimm lidx < fe_wlocal_offset fe + length wl ->
      fe_wlocal_offset fe + length wl + length wl' <= length (f_locs f) ->
      ∀ os nss nss32 vs,
        Forall2 has_arep ιs os →
        Forall2 (Forall2 N_i32_repr) nss nss32 ->
        congeal_atoms ιs nss32 = Some vs ->
        ref_flag_atoms_interp GCRefs (SAtoms os) ->
        ⊢ ∀ e,
          na_own logrel_nais E  -∗
          rt_token rti sr e -∗
          instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
          ([∗ list] o; ns ∈ os; nss, words_interp e MemMM (serialize_atom o) ns) -∗
          let offs := snd $ seq.foldl (λ '(off', offs) ι, (off' + arep_size ι, seq.rcons offs off'))
                                                     (off, []) ιs in
          ([∗ list] off'; v ∈ offs; vs, memidxN ↦[wms][ℓ + byte_offset MemMM off'] bits v) -∗
          ∀ Φ B R,
            ↪[frame] f -∗
            ↪[RUN] -∗
            (∀ f' e' vs',
              ⌜f' = mk_load_frame fe f wl vs⌝ -∗
              na_own logrel_nais E  -∗
              rt_token rti sr e' -∗
              instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
              ([∗ list] off'; v ∈ offs; vs, memidxN ↦[wms][ℓ + byte_offset MemMM off'] bits v) -∗
              mk_load_post os vs vs' -∗
              Φ f' vs') -∗
            CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
    unfold memory.load.
    intros Hcg.
    apply wp_ignore in Hcg.
    destruct Hcg as (-> & off' & Hcg).
    apply wp_mem_load_copy_mm_inner in Hcg.
    tauto.
  Qed.
End load.
