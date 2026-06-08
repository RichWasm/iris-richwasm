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

  Lemma virt_to_phys_slice_acc off sz ℓ μ a θ ws :
    let slice {A} (x : list A) := take sz (drop off x) in
    let R ns ns32 :=
      (⌜Forall2 N_i32_repr ns ns32⌝ ∗
       rt_memaddr sr μ↦[wms][a + 4 * N.of_nat off]flat_map serialise_i32 ns32 ∗
       words_interp θ μ (slice ws) ns)%I in
    ⊢ ⌜off + sz <= length ws⌝ -∗
      rt_token rti sr θ -∗
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
    iIntros (slice R) "%Hlenbdd Hrt Hpt Ha".
    open_rt "Hrt".
    iExists hm.
    iCombine "Hpt Hheap" gives "%Hhm".
    iCombine "Ha Haddr" gives "%Ha".
    iPoseProof (big_sepM2_lookup_acc with "Hheapmem") as "Hlookup"; eauto.
    iEval (cbn) in "Hlookup".
    iSplitL "Hroot Hlayout Hrti Hownmm Howngc Hrootmem"; first by iFrame.
    iDestruct "Hlookup" as "(HR & Hcont)".
    iDestruct "HR" as "(%ns & %ns32 & %Hns & Hphys & Hwords)".
    assert (ws = take off ws ++ slice _ ws ++ drop (off + sz) ws) as Hws.
    {
      rewrite app_assoc.
      unfold slice.
      by rewrite take_take_drop take_drop.
    }
    iEval (setoid_rewrite Hws) in "Hwords".
    iPoseProof (big_sepL2_app_inv_l with "Hwords") as "(%ns_pre & %ns' & -> & Hpre & Hwords)".
    iPoseProof (big_sepL2_app_inv_l with "Hwords") as "(%ns & %ns_post & -> & Hwords & Hpost)".
    pose proof Hns as Hns'.
    apply Forall2_app_inv_l in Hns'.
    destruct Hns' as (ns32_pre & ns32' & Hns_pre & Hns' & ->).
    apply Forall2_app_inv_l in Hns'.
    destruct Hns' as (ns32 & ns32_post & Hns' & Hns_post & ->).
    rewrite !flat_map_app.
    rewrite !wms_app; try by eauto.
    iDestruct "Hphys" as "(Hphys_pre & Hphys & Hphys_post)".
    pose proof (Forall2_length _ _ _ Hns_pre) as Hnslenpre.
    pose proof (Forall2_length _ _ _ Hns') as Hnslen.
    pose proof (Forall2_length _ _ _ Hns_post) as Hnslenpost.
    iPoseProof (big_sepL2_length with "Hpre") as "%Hlenpre'".
    iPoseProof (big_sepL2_length with "Hpost") as "%Hlenpost'".
    iPoseProof (big_sepL2_length with "Hwords") as "%Hlenws'".
    assert (length (flat_map serialise_i32 ns32_pre) = 4 * off) as Hlenpre.
    {
      rewrite len_ser32.
      rewrite -Hnslenpre -Hlenpre' length_take_le; lia.
    }
    rewrite Hlenpre.
    rewrite Nat2N.inj_mul.
    iSplitL "Hwords Hphys";
      first by iFrame.
    iIntros (ns' ns32') "(%Hns'' & Hphys & Hwords) Hnp".
    pose proof (Forall2_length _ _ _ Hns'') as Hns32'len.
    iPoseProof (big_sepL2_length with "Hwords") as "%Hns'len".
    unfold words_interp.
    iCombine "Hpre Hwords Hpost" as "Hwords".
    repeat (rewrite <- big_sepL2_app_same_length; last by intuition congruence).
    rewrite -Hws.
    iCombine "Hphys_pre Hphys Hphys_post" as "Hphys".
    rewrite -wms_app;
      last by rewrite !len_ser32 -Hns32'len -Hns'len Hlenws' Hnslen.
    rewrite -wms_app;
      last (rewrite !len_ser32 -Hnslenpre -Hlenpre' length_take_le; lia).
    iPoseProof ("Hcont" with "[Hphys Hwords]") as "Hclosed".
    {
      rewrite <- !flat_map_app.
      iFrame.
      iPureIntro; eauto using Forall2_app.
    }
    iSplitL "Hpt"; first iFrame.
    iSplitL "Ha"; first iFrame.
    iApply (rt_token_putheap with "[$]").
    iFrame.
  Qed.

  Lemma has_arep_size ι o :
    has_arep ι o ->
    length (serialize_atom o) = arep_size ι.
  Proof.
    destruct ι, o; intros H; done.
  Qed.

  Lemma length_t_translate_arep ι :
    length_t (translate_arep ι) = 4 * arep_size ι.
  Proof.
    destruct ι; done.
  Qed.

  Lemma heap_memory_delete ℓ μ a ws θ hm :
    θ !! ℓ = Some (μ, a) →
    hm !! ℓ = Some ws →
    heap_memory sr θ hm ⊢
      (∃ ns ns32, ⌜Forall2 N_i32_repr ns ns32⌝ ∗
                  rt_memaddr sr μ ↦[wms][a] flat_map serialise_i32 ns32 ∗
                  words_interp θ μ ws ns) ∗
      ∀ ws',
        (∃ ns' ns32', ⌜Forall2 N_i32_repr ns' ns32'⌝ ∗
                      rt_memaddr sr μ ↦[wms][a] flat_map serialise_i32 ns32' ∗
                      words_interp θ μ ws' ns') -∗
        heap_memory sr θ (<[ℓ := ws']> hm).
  Proof.
    intros Hθℓ Hhm.
    iIntros "Hmem". unfold heap_memory.
    have Hθ : <[ℓ := (μ, a)]> (delete ℓ θ) = θ.
    { apply map_eq; intros k; destruct (decide (k = ℓ)) as [->|Hne].
      - rewrite lookup_insert -Hθℓ. by rewrite decide_True.
      - rewrite lookup_insert_ne // lookup_delete_ne //. }
    have Hhm0 : <[ℓ := ws]> (delete ℓ hm) = hm.
    { apply map_eq; intros k; destruct (decide (k = ℓ)) as [->|Hne].
      - rewrite lookup_insert -Hhm. by rewrite decide_True.
      - rewrite lookup_insert_ne // lookup_delete_ne //. }
    iEval (rewrite -{1 2}Hθ -{1}Hhm0) in "Hmem".
    iEval (rewrite big_sepM2_insert_delete) in "Hmem".
    rewrite !delete_delete_eq.
    iDestruct "Hmem" as "[Hentry Hrest]".
    iSplitL "Hentry"; first by rewrite Hθ.
    iIntros (ws') "Hws'".
    unfold heap_memory.
    have Hhm' : <[ℓ := ws']> hm = <[ℓ := ws']> (delete ℓ hm).
    { apply map_eq; intros k; destruct (decide (k = ℓ)) as [->|Hne].
      - rewrite !lookup_insert. by rewrite !decide_True.
      - by rewrite !lookup_insert_ne // lookup_delete_ne. }
    iEval (rewrite -{1 2}Hθ Hhm').
    iEval (rewrite big_sepM2_insert_delete).
    rewrite !delete_delete_eq.
    iFrame.
    by rewrite Hθ.
  Qed.

  Lemma own_addr_mm_trivial (θ : address_map) (ℓ : location) :
    ⊢ ∃ a : N, ⌜θ !! ℓ = Some (MemMM, a)⌝ -∗ ℓ ↦addr (MemMM, a).
  Proof.
    destruct (θ !! ℓ) as [[μ a] |] eqn:Hθ.
    - iExists (a + 1)%N. iIntros "%H". simplify_eq. lia.
    - iExists 0%N. by iIntros "%H".
  Qed.

  Lemma own_addr_mm_trivial_list (θ : address_map) (ℓs : list location) :
    ⊢ [∗ list] ℓ ∈ ℓs,
        ∃ a : N, ⌜θ !! ℓ = Some (MemMM, a)⌝ -∗ ℓ ↦addr (MemMM, a).
  Proof.
    iInduction ℓs as [|ℓ rest] "IH".
    - done.
    - iSplitL.
      + iApply own_addr_mm_trivial.
      + iApply "IH".
  Qed.

  Lemma arep_flags_of_serialize_atom ι o :
    has_arep ι o →
    Forall2 word_has_flag (arep_flags ι) (serialize_atom o).
  Proof.
    intros Harep. destruct ι, o; try done.
    all: repeat constructor; done.
  Qed.

  Lemma heap_memory_dom_eq θ hm :
    heap_memory sr θ hm ⊢ ⌜dom θ = dom hm⌝.
  Proof. iApply big_sepM2_dom. Qed.

  (* From words_interp, all heap-pointer locations are in dom θ *)
  Lemma words_interp_locs_dom_θ θ rm μ ws ns :
    root_ok θ rm →
    words_interp θ μ ws ns -∗
    ghost_map_auth rw_root (1/2) rm -∗
    ⌜Forall (λ ℓ, ℓ ∈ dom θ) (flat_map locations ws)⌝.
  Proof.
    iIntros (Hrootok) "Hwords Hroot".
    iInduction ws as [|w ws'] "IH" forall (ns).
    - iDestruct (big_sepL2_nil_inv_l with "Hwords") as "->". done.
    - iDestruct (big_sepL2_cons_inv_l with "Hwords") as "(%n & %ns' & -> & Hword & Hwords')".
      destruct w as [[m | μ' ℓ] | m].
      + (* WordPtr (PtrInt m): locations = [] *)
        iApply ("IH" with "Hwords' Hroot").
      + (* WordPtr (PtrHeap μ' ℓ): location = [ℓ] *)
        cbn [flat_map locations].
        destruct μ, μ'.
        * (* MemMM / MemMM: word_interp = ⌜repr_pointer θ (PtrHeap MemMM ℓ) n⌝ *)
          iDestruct "Hword" as "%Hrep".
          iDestruct ("IH" with "Hwords' Hroot") as "%Htail".
          iPureIntro. apply Forall_app. split.
          -- apply Forall_singleton. apply elem_of_dom. inversion Hrep. eauto.
          -- exact Htail.
        * (* MemMM / MemGC: word_interp = ∃ a, ⌜repr_root_pointer ...⌝ ∗ a ↦root ℓ *)
          iDestruct "Hword" as "(%a & _ & Helem)".
          (* iCombine is non-destructive: Helem and Hroot both remain in context *)
          iCombine "Helem Hroot" gives "%Hrm".
          have Hdomℓ : ℓ ∈ dom θ.
          { apply elem_of_dom.
            destruct (map_Forall_lookup_1 _ _ _ _ Hrootok Hrm) as [a' Ha']. eauto. }
          iDestruct ("IH" with "Hwords' Hroot") as "%Htail".
          iPureIntro. apply Forall_app.
          by rewrite Forall_singleton.
        * (* MemGC / MemMM: word_interp = ⌜repr_pointer θ (PtrHeap MemMM ℓ) n⌝ *)
          iDestruct "Hword" as "%Hrep".
          iDestruct ("IH" with "Hwords' Hroot") as "%Htail".
          iPureIntro. apply Forall_app. split.
          -- apply Forall_singleton. apply elem_of_dom. inversion Hrep. eauto.
          -- exact Htail.
        * (* MemGC / MemGC: word_interp = ⌜repr_pointer θ (PtrHeap MemGC ℓ) n⌝ *)
          iDestruct "Hword" as "%Hrep".
          iDestruct ("IH" with "Hwords' Hroot") as "%Htail".
          iPureIntro. apply Forall_app. split.
          -- apply Forall_singleton. apply elem_of_dom. inversion Hrep. eauto.
          -- exact Htail.
      + (* WordInt m: locations = [] *)
        iApply ("IH" with "Hwords' Hroot").
  Qed.

  Lemma Forall2_word_has_flag_inj fs1 fs2 ws :
    Forall2 word_has_flag fs1 ws →
    Forall2 word_has_flag fs2 ws →
    fs1 = fs2.
  Proof.
    intro H; revert fs2.
    induction H as [|f1 fs1' w ws' Hf1 _ IH]; intros fs2 H2.
    - inversion H2; done.
    - inversion H2 as [|f2 ? ? ? Hf2 H2' Heq1 Heq2]; subst.
      f_equal.
      + destruct f1, f2, w; simpl in *; try congruence; by destruct fs1'.
      + exact (IH _ H2').
  Qed.

  (* The flag structure is preserved when updating a slice with a same-arep atom.
     The old slice (take (arep_size ι) (drop off ws)) must already have flags
     arep_flags ι. *)
  Lemma update_path_words_flags_compat ι o ws off :
    has_arep ι o →
    off + arep_size ι ≤ length ws →
    Forall2 word_has_flag (arep_flags ι) (take (arep_size ι) (drop off ws)) →
    ∀ flags, Forall2 word_has_flag flags ws →
             Forall2 word_has_flag flags (update_path_words off ws (serialize_atom o)).
  Proof.
    intros Harep Hbound Holdflags flags Hflags.
    pose proof (arep_flags_of_serialize_atom ι o Harep) as Hser.
    pose proof (has_arep_size ι o Harep) as Hser_len.
    have Hmid : take (arep_size ι) (drop off flags) = arep_flags ι.
    { apply (Forall2_word_has_flag_inj _ _ (take (arep_size ι) (drop off ws))).
      - apply Forall2_take. apply Forall2_drop. exact Hflags.
      - exact Holdflags. }
    unfold update_path_words. rewrite Hser_len.
    rewrite <- (take_drop off flags).
    apply Forall2_app.
    - apply Forall2_take. exact Hflags.
    - rewrite <- (take_drop (arep_size ι) (drop off flags)).
      apply Forall2_app.
      + rewrite Hmid. exact Hser.
      + rewrite !drop_drop.
        rewrite Nat.add_comm.
        by apply Forall2_drop.
  Qed.

  Lemma update_path_words_empty_1 off ws_new :
    update_path_words off [] ws_new = ws_new.
  Proof.
    unfold update_path_words.
    by rewrite take_nil !drop_nil app_nil_r.
  Qed.

  Lemma update_path_words_empty_2 off ws :
    update_path_words off ws [] = ws.
  Proof.
    unfold update_path_words.
    simpl.
    by rewrite drop_0 take_drop.
  Qed.


  Lemma update_path_words_succ off w ws ws_new :
    update_path_words (S off) (w :: ws) ws_new =
    w :: update_path_words off ws ws_new.
  Proof.
    unfold update_path_words.
    simpl.
    done.
  Qed.

  Lemma update_path_words_first w ws w_new ws_new :
    update_path_words 0 (w :: ws) (w_new :: ws_new) =
    w_new :: update_path_words 0 ws ws_new.
  Proof.
    unfold update_path_words.
    simpl.
    done.
  Qed.

  (* Locations in update_path_words are covered if old and new words' locs are *)
  Lemma update_path_words_locs_incl (dom_set : gset location) ws off ws_new :
    Forall (λ ℓ, ℓ ∈ dom_set) (flat_map locations ws) →
    Forall (λ ℓ, ℓ ∈ dom_set) (flat_map locations ws_new) →
    Forall (λ ℓ, ℓ ∈ dom_set) (flat_map locations (update_path_words off ws ws_new)).
  Proof.
    revert off ws_new.
    induction ws as [| w ws];
    intros off ws_new Hws Hwsnew.
    - simpl in Hws.
      by rewrite update_path_words_empty_1.
    - destruct ws_new as [|w_new ws_new]; first by rewrite update_path_words_empty_2.
      simpl in Hws.
      apply Forall_app in Hws as [Hw Hws].
      destruct off; last first.
      + rewrite update_path_words_succ.
        simpl.
        rewrite Forall_app.
        split; first done.
        by apply IHws.
      + rewrite update_path_words_first.
        simpl.
        rewrite Forall_app.
        simpl in Hwsnew.
        apply Forall_app in Hwsnew as [Hwnew Hwsnew].
        split; first done.
        by apply IHws.
  Qed.

  Lemma heap_ok_update θ lm hm ℓ ws' flags :
    heap_ok θ lm hm →
    lm !! ℓ = Some flags →
    Forall2 word_has_flag flags ws' →
    Forall (λ ℓ', ℓ' ∈ dom hm) (flat_map locations ws') →
    Forall (λ ℓ', ℓ' ∈ dom θ) (flat_map locations ws') →
    heap_ok θ lm (<[ℓ := ws']> hm).
  Proof.
    intros (Hflags & Hdomhm & Hdomθ) Hlm Hws' Hlocshm Hlocsθ.
    unfold map_Forall2 in Hflags, Hdomθ.
    unfold map_Forall in Hdomhm.
    have Hhmℓ : is_Some (hm !! ℓ).
    { have := Hflags ℓ. rewrite Hlm. intros H. inversion H. eauto. }
    destruct Hhmℓ as [ws_old Hws_old].
    have Hθℓ : is_Some (θ !! ℓ).
    { have := Hdomθ ℓ. rewrite Hws_old. intros H. inversion H. eauto. }
    destruct Hθℓ as [x Hθℓv].
    split; [| split].
    - unfold map_Forall2. intro k.
      destruct (decide (k = ℓ)) as [->|Hne].
      + rewrite lookup_insert Hlm decide_True; last done. constructor. simpl.
        (* is_true vs Is_true ... *)
        eapply Forall2_impl; [exact Hws'|].
        intros f w H.  by rewrite H.
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

  Lemma rt_token_nophys_insert_heap θ hm ℓ ws ws' :
    hm !! ℓ = Some ws →
    (∀ flags, Forall2 word_has_flag flags ws → Forall2 word_has_flag flags ws') →
    Forall (λ ℓ', ℓ' ∈ dom hm) (flat_map locations ws') →
    Forall (λ ℓ', ℓ' ∈ dom θ) (flat_map locations ws') →
    rt_token_nophys θ hm -∗
    rt_token_nophys θ (<[ℓ := ws']> hm).
  Proof.
    intros Hhm Hflags_compat Hlocshm Hlocsθ.
    iIntros "(%rm & %lm & Hroot & Hlayout & Hrti & %Hinj & Hownmm & Howngc & %Hrootok & Hrootmem & %Hheapok)".
    iExists rm, lm.
    iFrame "Hroot Hlayout Hrti Howngc Hrootmem".
    iSplit; first done.
    iSplit; last (iSplit; first done).
    - (* own_addr_mm θ (<[ℓ := ws']> hm) *)
      unfold own_addr_mm.
      have Hhm' : <[ℓ := ws']> hm = <[ℓ := ws']> (delete ℓ hm).
      { apply map_eq; intros k; destruct (decide (k = ℓ)) as [->|Hne].
        - rewrite !lookup_insert. by rewrite !decide_True.
        - by rewrite !lookup_insert_ne // lookup_delete_ne. }
      rewrite Hhm'.
      iEval (rewrite big_sepM_insert_delete).
      rewrite delete_delete_eq.
      iSplitL "".
      * iApply own_addr_mm_trivial_list.
      * iPoseProof (big_sepM_delete _ hm ℓ ws Hhm with "Hownmm") as "[_ $]".
    - iPureIntro.
      have Hmapflags : ∃ flags, lm !! ℓ = Some flags ∧ Forall2 word_has_flag flags ws.
      { destruct Hheapok as (Hcomp1 & _).
        unfold map_Forall2 in Hcomp1. specialize (Hcomp1 ℓ).
        rewrite Hhm in Hcomp1. inversion Hcomp1. exists x. split; auto. simpl in H1.
        eapply Forall2_impl; first exact H1.
        intros f w H'. destruct (word_has_flag f w) eqn:H''; first done. by rewrite H'' in H'. }
      destruct Hmapflags as [flags [Hflm Hwsflags]].
      eapply heap_ok_update.
      2: exact Hflm.
      all: try done.
      exact (Hflags_compat flags Hwsflags).
  Qed.

  Lemma virt_to_phys_slice_store_acc off sz ℓ μ a θ ws :
    let slice := take sz (drop off ws) in
    ⊢ ⌜off + sz <= length ws⌝ -∗
      rt_token rti sr θ -∗
      ℓ ↦heap ws -∗
      ℓ ↦addr (μ, a) -∗
      ∃ hm,
        ⌜hm !! ℓ = Some ws⌝ ∗
        ⌜dom θ = dom hm⌝ ∗
        ⌜Forall (λ ℓ', ℓ' ∈ dom θ) (flat_map locations ws)⌝ ∗
        rt_token_nophys θ hm ∗
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
          rt_token_nophys θ hm -∗
          |==> ℓ ↦heap (update_path_words off ws ws_new) ∗
               ℓ ↦addr (μ, a) ∗
               rt_token rti sr θ).
  Proof.
    iIntros (slice) "%Hlenbdd Hrt Hpt Ha".
    open_rt "Hrt".
    iExists hm.
    iCombine "Hpt Hheap" gives "%Hhm".
    iCombine "Ha Haddr" gives "%Hθℓ".
    iPoseProof (heap_memory_dom_eq with "Hheapmem") as "%Hdomθhm".
    iPoseProof (heap_memory_delete ℓ _ _ ws with "Hheapmem") as "(HR & Hheapcont)"; eauto.
    (* Derive Forall (ℓ' ∈ dom θ) (flat_map locations ws) from heap_ok condition 3 *)
    have Hlocsθ_ws : Forall (λ ℓ', ℓ' ∈ dom θ) (flat_map locations ws).
    { destruct Hheapok as (_ & _ & Hdomθ).
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
    iFrame "Hpt' Ha".
    pose proof (Forall2_length _ _ _ Hns'') as Hns32'len.
    iPoseProof (big_sepL2_length with "Hwords'") as "%Hns'len".
    set (hm' := <[ℓ := update_path_words off ws ws_new]> hm).
    iAssert (rt_token_nophys θ hm') with "[Hnp]" as "Hnp'".
    { iApply (rt_token_nophys_insert_heap _ _ _ ws with "Hnp").
      - exact Hhm.
      - exact Hflags_compat.
      - exact Hlocshm.
      - exact Hlocsθ. }
    iApply (rt_token_putheap θ hm' with "Hnp'").
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

  Lemma atom_to_words_mm θ ι o val_v :
    has_arep ι o ->
    atom_interp_weak θ MemMM o val_v -∗
    ∃ (ns : list N) (ns32 : list i32),
      ⌜Forall2 N_i32_repr ns ns32⌝ ∗
      ⌜flat_map serialise_i32 ns32 = bits val_v⌝ ∗
      ⌜types_agree (translate_arep ι) val_v⌝ ∗
      words_interp θ MemMM (serialize_atom o) ns.
  Proof.
  Admitted.

  Lemma has_areps_size ιs os :
    Forall2 has_arep ιs os ->
    map (length ∘ serialize_atom) os = map arep_size ιs.
  Proof.
    intros Hall; induction Hall; first done.
    cbn.
    erewrite has_arep_size; eauto.
    congruence.
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

  Lemma atom_interp_weak_dup θ μ o v :
    expect_heap_ptr o = None ->
    Persistent (atom_interp_weak θ μ o v).
  Proof.
    intros Heq.
    unfold atom_interp_weak.
    destruct o; first destruct p as [n|ℓ], μ;
      try by inversion Heq;
      repeat (apply bi.pure_persistent
      || (apply bi.exist_persistent; intros ?x)
      || apply bi.sep_persistent).
  Qed.

  Lemma atom_interp_weak_promote θ μ o v :
    expect_heap_ptr o = None ->
    atom_interp_weak θ μ o v -∗
    atom_interp o v.
  Proof.
    intros Heq.
    unfold atom_interp, atom_interp_weak.
    destruct o; first destruct p as [n|ℓ] eqn:Hp;
      try inversion Heq;
      try (by iIntros "->").
    destruct μ.
    all:iIntros "(%n' & %n32 & %Hnrep & -> & %Hrep)".
    all:cbn.
    all:iExists _, _; repeat (iSplit; first done).
    all:iExists (RootInt n).
    all:cbn.
    all:inversion Hrep; subst; eauto.
    all:iPureIntro.
    all:split; auto.
    all:by constructor.
  Qed.

  Lemma wp_load1_copy_mm (se : @semantic_env Σ) F lidx off ι wt wl ret wt' wl' es :
    let fe := fe_of_context F in
    run_codegen (memory.load1 mr fe MemMM Copy lidx off ι) wt wl = inr (ret, wt', wl', es) ->
    ∀ f ℓ a32 a o ws s E B R e Φ,
    ⊢ "Hf" ∷ ↪[frame] f -∗
      "Hrun" ∷ ↪[RUN] -∗
      "Hptr" ∷ ℓ ↦heap ws -∗
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
        (∀ e' f' vf v,
           "%Hf'"  ∷ ⌜f' = mk_load1_frame fe f (length wl) vf⌝ -∗
           "%Hvf"  ∷ ⌜types_agree (translate_arep ι) vf⌝ -∗
           "Hptr"  ∷ ℓ ↦heap ws -∗
           "Haddr" ∷ ℓ ↦addr (MemMM, a) -∗
           "Hown"  ∷ na_own logrel_nais E -∗
           "Htok"  ∷ rt_token rti sr e' -∗
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
    iPoseProof (virt_to_phys_slice_acc off (arep_size ι) with "[//] [$] [$] [$]")
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
        subst f'.
        iApply ("HΦ" with "[//] [//] [$] [$] [$] [$] [$] [-]").
        by iIntros "_".
      + iApply (cwp_val with "[$] [$]"); eauto using has_values_to_consts.
        iPoseProof ("Hret" with "Hat") as "Hwords".
        iAssert (ℓ ↦heap ws ∗ ℓ ↦addr (MemMM, a) ∗ rt_token rti sr e)%I with "[Hclose Hphys Hwords Hnp]" as "(Hheap & Haddr & Htok)".
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
        iDestruct "Hnp" as "(%rm & %lm & Hroot & Hlayout & Hrti & Hinj & Hownmm & Howngc & Hrest)".
        iDestruct "Hrest" as "(%Hrootok & Hrootmem & Hheapok)".
        iCombine "Hrt" "Hroot" gives "%Hrm".
        unfold PHYS.
        rewrite -Hserws.
        iApply (Hduproot with "[$] [$] [//] [//] [$] [$] [$]
                  [Hphys Hclose Hret Hlayout
                   Hrti Hinj Hownmm Howngc Hheapok] [$] [$]"); eauto.
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
        iIntros (e' ar' ar'32) "%Hreproot %Hrepar Hrt Htok [Hws Ha] Hinvs Hreg".
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
      assert (Persistent (atom_interp_weak e MemMM o v));
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
    ∀ f ℓ a32 a o ws s E B R e Φ,
    ⊢ "Hf" ∷ ↪[frame] f -∗
      "Hrun" ∷ ↪[RUN] -∗
      "Hptr" ∷ ℓ ↦heap ws -∗
      "Haddr" ∷ a ↦root ℓ -∗
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
        (∀ e' f' vf v,
           "%Hf'"  ∷ ⌜f' = mk_load1_frame fe f (length wl) vf⌝ -∗
           "%Hvf"  ∷ ⌜types_agree (translate_arep ι) vf⌝ -∗
           "Hptr"  ∷ ℓ ↦heap ws -∗
           "Haddr" ∷ a ↦root ℓ -∗
           "Hown"  ∷ na_own logrel_nais E -∗
           "Htok"  ∷ rt_token rti sr e' -∗
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
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_save ?es_rest Hsave Hcg.
    apply wp_wlalloc in Hwlalloc.
    destruct Hwlalloc as (Hidx & -> & -> & ->).
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
      pose proof (wp_duproot rti sr mr _ _ _ _ _ _ Hdup) as Hduproot.
      destruct Hduproot as (_ & -> & -> & _).
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

  Lemma rcons_app {X} : forall (xs : list X) x,
      seq.rcons xs x = xs ++ [x].
  Proof.
    induction xs; intros x.
    - reflexivity.
    - cbn.
      by rewrite IHxs.
  Qed.

  Lemma flat_map_rcons X Y (f : X -> list Y) xs x :
    flat_map f (seq.rcons xs x) = flat_map f xs ++ f x.
  Proof.
    revert x.
    induction xs; cbn; intros.
    - by clear_nils.
    - by rewrite -app_assoc IHxs.
  Qed.

  Lemma mk_frame_rcons fe f wl vs v :
    mk_load1_frame fe (mk_load_frame fe f wl vs) (length wl + length vs) v =
      mk_load_frame fe f wl (vs ++ [v]).
  Proof.
  Admitted.

  Lemma load_fold_offs_len ιs : ∀ off' offs' off offs,
    seq.foldl (λ '(off, offs) ι, (off + arep_size ι, seq.rcons offs off)) (off, offs) ιs = (off', offs') ->
    length offs' = length ιs + length offs.
  Proof.
    change @length with @seq.size.
    induction ιs as [| ιs ι] using seq.last_ind; intros * Hfold.
    - by inversion Hfold.
    - rewrite seq.foldl_rcons in Hfold.
      destruct (seq.foldl _ _ _) as [off0 offs0] eqn:?.
      inversion Hfold; subst; clear Hfold.
      eapply IHιs in Heqy.
      rewrite !seq.size_rcons.
      lia.
  Qed.

  Lemma simple_fold_fancy_fold ιs : ∀ off' offs' off offs,
    seq.foldl (λ '(off, offs) ι, (off + arep_size ι, seq.rcons offs off)) (off, offs) ιs = (off', offs') ->
    seq.foldl (λ off' ι, off' + arep_size ι) off ιs = off'.
  Proof.
  Admitted.

  Lemma simple_fold_sum_list_with ιs : ∀ off,
    seq.foldl (λ off' ι, off' + arep_size ι) off ιs = off + sum_list_with arep_size ιs.
  Admitted.

  Lemma sum_list_with_rcons {X : Type} (f : X -> nat) (x : X) (xs : list X) :
    sum_list_with f (seq.rcons xs x) = f x + sum_list_with f xs.
  Proof.
  Admitted.

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
      ∀ f ℓ a32 a os ws E B R e Φ,
    ⊢ "Hptr" ∷ ℓ ↦heap ws -∗
      "Haddr" ∷ ℓ ↦addr (MemMM, a) -∗
      "Hown"  ∷ na_own logrel_nais E -∗
      "Htok"  ∷ rt_token rti sr e -∗
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
        (∀ e' f' vs vsf,
           "%Hf'"     ∷ ⌜f' = mk_load_frame fe f wl vsf⌝ -∗
           "%Hvsf" ∷ ⌜Forall2 (λ ι vf, types_agree (translate_arep ι) vf) ιs vsf⌝ -∗
           "Hptr"  ∷ ℓ ↦heap ws -∗
           "Haddr" ∷ ℓ ↦addr (MemMM, a) -∗
           "Hown"  ∷ na_own logrel_nais E -∗
           "Htok"  ∷ rt_token rti sr e' -∗
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
      eapply wp_mem_load1_copy_mm_cg_state in Hbs'.
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
        iIntros (e' f' vs vsf).
        repeat iIntros "@".
        (* DEMO: using iAccu to save proof state *)
        let Q := open_constr:(_ : iProp Σ) in
          instantiate (1 := (λ f0 vs0, ∃ e' vsf,
                              (* stuff to say about e' f0 and vs0 *)
                              ⌜f0 = mk_load_frame fe f wl vsf⌝ ∗
                              ⌜Forall2 (λ (ι : atomic_rep) (vf : value), types_agree (translate_arep ι) vf) ιs vsf⌝ ∗
                              ([∗ list] o0;v ∈ os';vs0, ⌜atom_copyable o0⌝ -∗ atom_interp o0 v) ∗
                              rt_token rti sr e' ∗
                              (* evar for collecting everything else *)
                              (* make sure nothing that goes in here mentions e', f', or vs! *)
                              Q)%I).
        iExists e', vsf.
        iFrame "Hos Htok".
        iSplit; first done.
        iSplit; first done.
        (* accumulates everything in the evar *)
        iNamedAccu.
      }
      iApply (cwp_seq with "[Hinit Hf Hrun]");
        first iApply ("Hinit" with "[$] [$]").
      iIntros (f' vs') "(%e' & %vsf & -> & %Hvsf & Hos & Htok & @ & @ & @ & @) Hf Hr".
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
      + iIntros (e'' f'' vf v) "@@@@@@@@".
        unfold fvs_combine.
        iApply ("HΦ" with "[] [] [$] [$] [$] [$] [Hregf] [Ho Hos]").
        * iPureIntro.
          instantiate (1:=vsf ++ [vf]).
          rewrite Hf'.
          rewrite -mk_frame_rcons.
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
      ∀ f ℓ a32 a os ws E B R e Φ,
      ⊢ "Hf" ∷ ↪[frame] f -∗
        "Hrun" ∷ ↪[RUN] -∗
        "Hptr" ∷ ℓ ↦heap ws -∗
        "Haddr" ∷ ℓ ↦addr (MemMM, a) -∗
        "Hown"  ∷ na_own logrel_nais E -∗
        "Htok"  ∷ rt_token rti sr e -∗
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
          (∀ θ' f' vs vsf,
             "%Hf'"     ∷ ⌜f' = mk_load_frame fe f wl vsf⌝ -∗
             "%Hvsf" ∷ ⌜Forall2 (λ ι vf, types_agree (translate_arep ι) vf) ιs vsf⌝ -∗
             "Hptr"  ∷ ℓ ↦heap ws -∗
             "Haddr" ∷ ℓ ↦addr (MemMM, a) -∗
             "Hown"  ∷ na_own logrel_nais E -∗
             "Htok"  ∷ rt_token rti sr θ' -∗
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

  Lemma wp_mem_load_copy_gc (se : @semantic_env Σ) F lidx ιs :
    let fe := fe_of_context F in
    ∀ off wt wl ret wt' wl' es,
      run_codegen (memory.load mr fe MemGC Copy lidx off ιs) wt wl = inr (ret, wt', wl', es) ->
      let offs := snd $ seq.foldl (λ '(off', offs) ι, (off' + arep_size ι, seq.rcons offs off'))
                    (off, []) ιs in
      let offs_szs := seq.zip offs (map arep_size ιs) in
      ∀ f ℓ a32 a os ws E B R θ Φ,
      ⊢ "Hf" ∷ ↪[frame] f -∗
        "Hrun" ∷ ↪[RUN] -∗
        "Hptr" ∷ ℓ ↦heap ws -∗
        "%Haddr" ∷ ⌜θ !! ℓ = Some (MemGC, a)⌝ -∗
        "Hown"  ∷ na_own logrel_nais E -∗
        "Htok"  ∷ rt_token rti sr θ -∗
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
        "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemGC)⌝ -∗
        "%Hmemmm" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
        "%Hmemgc" ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemGC = Some (sr_mem_gc sr)⌝ -∗
        "HΦ" ∷
          (∀ θ' f' vs vsf,
             "%Hf'"     ∷ ⌜f' = mk_load_frame fe f wl vsf⌝ -∗
             "%Hvsf" ∷ ⌜Forall2 (λ ι vf, types_agree (translate_arep ι) vf) ιs vsf⌝ -∗
             "Hptr"  ∷ ℓ ↦heap ws -∗
             "%Haddr'" ∷ ⌜θ' !! ℓ = Some (MemGC, a)⌝ -∗
             "Hown"  ∷ na_own logrel_nais E -∗
             "Htok"  ∷ rt_token rti sr θ' -∗
             "Hregf" ∷ instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
             "Hos"    ∷ ([∗ list] o;v ∈ os; vs, (⌜atom_copyable o⌝ -∗ atom_interp o v)) -∗
             Φ f' vs) -∗
        CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
  Admitted.
End load.
