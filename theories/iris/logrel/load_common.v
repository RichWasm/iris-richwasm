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

Section load_common.

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
    intros.
    apply N.Div0.mod_divides in H0 as [c ->].
    destruct c; lias.
  Qed.

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

  Definition mk_load1_post lmask o v v' : iProp Σ :=
    (∃ e', rt_token rti sr lmask e' ∗
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

  Lemma virt_to_phys_acc ℓ μ a lmask θ ws :
    let R ns ns32 :=
      (⌜Forall2 N_i32_repr ns ns32⌝ ∗
       rt_memaddr sr μ↦[wms][a]flat_map serialise_i32 ns32 ∗
       words_interp θ μ ws ns)%I in
    ⊢ rt_token rti sr lmask θ -∗
      ℓ ↦heap ws -∗
      ℓ ↦addr (μ, a) -∗
      ∃ hm,
        rt_token_nophys rti sr lmask θ hm ∗
        (∃ ns ns32, R ns ns32) ∗
        (∀ ns' ns32',
          R ns' ns32' -∗
          rt_token_nophys rti sr lmask θ hm -∗
          ℓ ↦heap ws ∗
          ℓ ↦addr (μ, a) ∗
          rt_token rti sr lmask θ).
  Proof.
    iIntros (R) "Hrt Hpt Ha".
    open_rt "Hrt".
    iExists hm.
    iCombine "Hpt Hheap" gives "%Hhm".
    iCombine "Ha Haddr" gives "%Ha".
    iPoseProof (big_sepM2_lookup_acc with "Hheapmem") as "Hlookup"; eauto.
    iEval (cbn) in "Hlookup".
    iSplitL "Hroot Hlayout Hrti Hrootmem Haddr"; first by iFrame.
    iDestruct "Hlookup" as "(HR & Hcont)".
    iSplitL "HR"; first by iApply "HR".
    iIntros (ns ns32) "HR Hnp".
    iPoseProof ("Hcont" with "[$HR]") as "Hclosed".
    iSplitL "Hpt"; first iFrame.
    iSplitL "Ha"; first iFrame.
    iApply (rt_token_putheap with "[$]").
    iFrame.
  Qed.

  (* This variant of virt_to_phys_acc does not need an addr points-to and instead expects
     you to already know θ !! ℓ = Some (MemGC, a). *)
  Lemma virt_to_phys_acc_gc ℓ a lmask θ ws :
    let R ns ns32 :=
      (⌜Forall2 N_i32_repr ns ns32⌝ ∗
       rt_memaddr sr MemGC↦[wms][a]flat_map serialise_i32 ns32 ∗
       words_interp θ MemGC ws ns)%I in
    ⊢ rt_token rti sr lmask θ -∗
      ℓ ↦heap ws -∗
      ⌜θ !! ℓ = Some (MemGC, a)⌝ -∗
      ∃ hm,
        rt_token_nophys rti sr lmask θ hm ∗
        (∃ ns ns32, R ns ns32) ∗
        (∀ ns' ns32',
          R ns' ns32' -∗
          rt_token_nophys rti sr lmask θ hm -∗
          ℓ ↦heap ws ∗
          rt_token rti sr lmask θ).
  Proof.
    iIntros (R) "Hrt Hpt %Ha".
    open_rt "Hrt".
    iCombine "Hheap Hpt" gives "%Hpt".
    iPoseProof (big_sepM2_lookup_acc with "Hheapmem") as "Hlookup"; eauto.
    iEval (cbn) in "Hlookup".
    iDestruct "Hlookup" as "(HR & Hcont)".
    iExists hm.
    iSplitR "HR Hheap Hpt Hcont"; first by iFrame.
    iSplitL "HR"; first by iFrame.
    iIntros (ns ns32) "HR Htok".
    iSplitL "Hpt"; first by iFrame.
    iPoseProof ("Hcont" with "[$HR]") as "Hclosed".
    iApply (rt_token_putheap with "[$] [$]").
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

  Lemma virt_to_phys_slice_acc off sz ℓ μ a lmask θ ws :
    let slice {A} (x : list A) := take sz (drop off x) in
    let R ns ns32 :=
      (⌜Forall2 N_i32_repr ns ns32⌝ ∗
       rt_memaddr sr μ↦[wms][a + 4 * N.of_nat off]flat_map serialise_i32 ns32 ∗
       words_interp θ μ (slice ws) ns)%I in
    ⊢ ⌜off + sz <= length ws⌝ -∗
      rt_token rti sr lmask θ -∗
      ℓ ↦heap ws -∗
      ℓ ↦addr (μ, a) -∗
      ∃ hm,
        rt_token_nophys rti sr lmask θ hm ∗
        (∃ ns ns32, R ns ns32) ∗
        (∀ ns' ns32',
          R ns' ns32' -∗
          rt_token_nophys rti sr lmask θ hm -∗
          ℓ ↦heap ws ∗
          ℓ ↦addr (μ, a) ∗
          rt_token rti sr lmask θ).
  Proof.
    iIntros (slice R) "%Hlenbdd Hrt Hpt Ha".
    open_rt "Hrt".
    iExists hm.
    iCombine "Hpt Hheap" gives "%Hhm".
    iCombine "Ha Haddr" gives "%Ha".
    iPoseProof (big_sepM2_lookup_acc with "Hheapmem") as "Hlookup"; eauto.
    iEval (cbn) in "Hlookup".
    iSplitL "Hroot Haddr Hlayout Hrti Hrootmem"; first by iFrame.
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

  Lemma virt_to_phys_slice_acc_gc off sz ℓ μ a lmask θ ws :
    let slice {A} (x : list A) := take sz (drop off x) in
    let R ns ns32 :=
      (⌜Forall2 N_i32_repr ns ns32⌝ ∗
       rt_memaddr sr μ↦[wms][a + 4 * N.of_nat off]flat_map serialise_i32 ns32 ∗
       words_interp θ μ (slice ws) ns)%I in
    ⊢ ⌜off + sz <= length ws⌝ -∗
      rt_token rti sr lmask θ -∗
      ℓ ↦heap ws -∗
      ⌜θ !! ℓ = Some (μ, a)⌝ -∗
      ∃ hm,
        rt_token_nophys rti sr lmask θ hm ∗
        (∃ ns ns32, R ns ns32) ∗
        (∀ ns' ns32',
          R ns' ns32' -∗
          rt_token_nophys rti sr lmask θ hm -∗
          ℓ ↦heap ws ∗
          rt_token rti sr lmask θ).
  Proof.
    iIntros (slice R) "%Hlenbdd Hrt Hpt %Ha".
    open_rt "Hrt".
    iExists hm.
    iCombine "Hpt Hheap" gives "%Hhm".
    iPoseProof (big_sepM2_lookup_acc with "Hheapmem") as "Hlookup"; eauto.
    iEval (cbn) in "Hlookup".
    iSplitL "Hroot Hlayout Hrti Haddr Hrootmem"; first by iFrame.
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
    iApply (rt_token_putheap with "[$] [$]").
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

  Lemma arep_flags_of_serialize_atom ι o :
    has_arep ι o →
    Forall2 word_has_flag (arep_flags ι) (serialize_atom o).
  Proof.
    intros Harep. destruct ι, o; try done.
    all: repeat constructor; done.
  Qed.

  (* From words_interp, all heap-pointer locations are in dom θ *)
  Lemma words_interp_locs_dom_θ θ rm μ ws ns :
    root_ok θ rm →
    words_interp θ μ ws ns -∗
    ghost_map_auth rw_root (1/2) rm -∗
    ghost_map_auth rw_addr (1/2) θ -∗
    ⌜Forall (λ ℓ, ℓ ∈ dom θ) (flat_map locations ws)⌝.
  Proof.
    iIntros (Hrootok) "Hwords Hroot Haddr".
    iInduction ws as [|w ws'] "IH" forall (ns).
    - iDestruct (big_sepL2_nil_inv_l with "Hwords") as "->". done.
    - iDestruct (big_sepL2_cons_inv_l with "Hwords") as "(%n & %ns' & -> & Hword & Hwords')".
      destruct w as [[m | μ' ℓ] | m].
      + (* WordPtr (PtrInt m): locations = [] *)
        iApply ("IH" with "[$] [$] [$]").
      + (* WordPtr (PtrHeap μ' ℓ): location = [ℓ] *)
        cbn [flat_map locations].
        destruct μ, μ'.
        * (* MemMM / MemMM: word_interp = ⌜repr_pointer θ (PtrHeap MemMM ℓ) n⌝ *)
          cbn.
          iDestruct "Hword" as "(%a & %Hrep & Ha)".
          iCombine "Ha" "Haddr" gives "%Hfind".
          iDestruct ("IH" with "[$] [$] [$]") as "%Htail".
          iPureIntro. apply Forall_cons. split.
          -- apply elem_of_dom. by rewrite Hfind.
          -- exact Htail.
        * (* MemMM / MemGC: word_interp = ∃ a, ⌜repr_root_pointer ...⌝ ∗ a ↦root ℓ *)
          iDestruct "Hword" as "(%a & _ & Helem)".
          (* iCombine is non-destructive: Helem and Hroot both remain in context *)
          iCombine "Helem Hroot" gives "%Hrm".
          have Hdomℓ : ℓ ∈ dom θ.
          { apply elem_of_dom.
            destruct (map_Forall_lookup_1 _ _ _ _ Hrootok Hrm) as [a' Ha']. eauto. }
          iDestruct ("IH" with "[$] [$] [$]") as "%Htail".
          iPureIntro. apply Forall_app.
          by rewrite Forall_singleton.
        * (* MemGC / MemMM: word_interp = ⌜repr_pointer θ (PtrHeap MemMM ℓ) n⌝ *)
          cbn.
          iDestruct "Hword" as "(%a & %Hrep & Ha)".
          iCombine "Ha" "Haddr" gives "%Hfind".
          iDestruct ("IH" with "[$] [$] [$]") as "%Htail".
          iPureIntro. apply Forall_cons. split.
          -- apply elem_of_dom. by rewrite Hfind.
          -- exact Htail.
        * (* MemGC / MemGC: word_interp = ⌜repr_pointer θ (PtrHeap MemGC ℓ) n⌝ *)
          iDestruct "Hword" as "%Hrep".
          iDestruct ("IH" with "[$] [$] [$]") as "%Htail".
          iPureIntro. apply Forall_app. split.
          -- apply Forall_singleton. apply elem_of_dom. inversion Hrep. eauto.
          -- exact Htail.
      + (* WordInt m: locations = [] *)
        iApply ("IH" with "[$] [$] [$]").
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

  Lemma updating_words (off : nat) (adding ws : list word) :
    off + length adding ≤ length ws →
    ∃ ws1 ws_old ws2,
      ws = ws1 ++ ws_old ++ ws2 ∧
      update_path_words off ws adding = ws1 ++ adding ++ ws2 ∧
      length ws_old = length adding ∧
      length ws1 = off.
  Proof.
    revert off adding.
    induction ws as [|w ws IH].
    - intros off adding Hlens.
      cbn in Hlens. destruct off; [|lia]. destruct adding; [|cbn in Hlens; lia].
      exists [], [], []. unfold update_path_words. done.
    - intros off adding Hlens.
      destruct off.
      + destruct adding as [|a adding].
        * exists [], [], (w :: ws). unfold update_path_words. clear_nils. done.
        * cbn in Hlens.
          specialize (IH 0 adding ltac:(lia)) as (ws1 & ws_old & ws2 & Hws & Hset & Hlenold & Hlenws1).
          assert (ws1 = []) as -> by (destruct ws1; [done | cbn in Hlenws1; lia]).
          cbn in Hws.
          exists [], (w :: ws_old), ws2.
          split; [rewrite Hws; done |].
          split; [clear_nils; rewrite update_path_words_first Hset; done |].
          split; [cbn; lia | done].
      + cbn in Hlens.
        specialize (IH off adding ltac:(lia)) as (ws1 & ws_old & ws2 & Hws & Hset & Hlenold & Hlenws1).
        exists (w :: ws1), ws_old, ws2.
        split; [rewrite Hws; done |].
        split; [rewrite update_path_words_succ Hset; done |].
        split; [done | cbn; lia].
  Qed.

  (* this can be generalized but we get offset >= as1 not often *)
  Lemma update_path_words_too_long :
    ∀ as1 off as2,
      update_path_words (off + length as1) as1 as2 = as1 ++ as2.
  Proof.
    intros as1.
    induction as1 as [|a as1]; intros.
    - cbn.
      rewrite update_path_words_empty_1.
      done.
    - cbn [length].
      rewrite Nat.add_succ_r.
      rewrite update_path_words_succ.
      rewrite IHas1.
      done.
  Qed.

  (* note: may need to add length things but I don't think so *)
  Lemma update_path_words_in_stages:
    ∀ ws as1 as2 off,
    update_path_words off ws (as1 ++ as2) =
      update_path_words (off + length as1) (update_path_words off ws as1) as2.
  Proof.
    intros ws.
    induction ws as [|w ws]; intros.
    - rewrite !update_path_words_empty_1.
      rewrite update_path_words_too_long.
      done.
    - destruct off.
      + destruct as1 as [|a as1].
        * clear_nils.
          rewrite update_path_words_empty_2.
          cbn. done.
        * change ((a::as1)++as2) with (a::as1++as2).
          do 2 (rewrite update_path_words_first).
          rewrite IHws.
          cbn. done.
      + do 2 (rewrite update_path_words_succ).
        rewrite IHws.
        cbn. done.
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

  (* changing this. This is one that will PRESERVE THE LAYOUT *)
  (* so ℓ starts in the mask and will end in the mask *)
  (* the fact that this passes without lmask ℓ means that it can be in or out *)
  (* I think. It's a bit suspicious to me ngl. *)
  Lemma heap_ok_update_weak θ lmask lm hm ℓ ws' flags :
    layout_ok lmask lm hm ->
    heap_ok θ hm →
    lm !! ℓ = Some flags →
    (lmask ℓ → Forall2 word_has_flag flags ws') →
    Forall (λ ℓ', ℓ' ∈ dom hm) (flat_map locations ws') →
    Forall (λ ℓ', ℓ' ∈ dom θ) (flat_map locations ws') →
    layout_ok lmask lm (<[ℓ := ws']> hm) /\ heap_ok θ (<[ℓ := ws']> hm).
  Proof.
    intros Hflags (Hdomhm & Hdomθ) Hlm Hws' Hlocshm Hlocsθ.
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
        (* is_true vs Is_true ... *)
        eapply Forall2_impl; [by apply Hws'|].
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

  (* also weak. and here's where you need to know it's in the mask? I think? *)
  Lemma rt_token_nophys_insert_heap_weak θ lmask hm ℓ ws ws' :
    hm !! ℓ = Some ws →
    (lmask ℓ → ∀ flags, Forall2 word_has_flag flags ws → Forall2 word_has_flag flags ws') →
    Forall (λ ℓ', ℓ' ∈ dom hm) (flat_map locations ws') →
    Forall (λ ℓ', ℓ' ∈ dom θ) (flat_map locations ws') →
    rt_token_nophys rti sr lmask θ hm -∗
    rt_token_nophys rti sr lmask θ (<[ℓ := ws']> hm).
  Proof.
    intros Hhm Hflags_compat Hlocshm Hlocsθ.
    iIntros "(Haddr & %rm & %lm & Hroot & Hlayout & Hrti & %Hinj & %Hrootok & Hrootmem & %Hlayoutok & %Hheapok)".
    iFrame.
    iSplit; first done.
    iSplit; first done.
    iPureIntro.
    have Hmapflags : ∃ flags, lm !! ℓ = Some flags ∧
                                (lmask ℓ -> Forall2 word_has_flag flags ws).
     {
       unfold layout_ok, map_Forall2 in Hlayoutok. specialize (Hlayoutok ℓ).
       rewrite Hhm in Hlayoutok. inversion Hlayoutok. exists x. split; auto. simpl in H1.
       intros Hl2. specialize (H1 Hl2).
       eapply Forall2_impl; first exact H1.
       intros f w H'. destruct (word_has_flag f w) eqn:H''; first done. by rewrite H'' in H'. }
    destruct Hmapflags as [flags [Hflm Hwsflags]].
    eapply heap_ok_update_weak.
    3: exact Hflm.
    all: try done.
    intros Hl.
    specialize (Hwsflags Hl).
    exact (Hflags_compat Hl flags Hwsflags).
  Qed.

  Lemma virt_to_phys_slice_store_acc_weak lmask off sz ℓ μ a θ ws :
    let slice := take sz (drop off ws) in
    ⊢ ⌜off + sz <= length ws⌝ -∗
      rt_token rti sr lmask θ -∗
      ℓ ↦heap ws -∗
      ℓ ↦addr (μ, a) -∗
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
               ℓ ↦addr (μ, a) ∗
               rt_token rti sr lmask θ).
  Proof.
    iIntros (slice) "%Hlenbdd Hrt Hpt Ha".
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
    iIntros (ws_new ns' ns32') "%Hlenws_new %Hns'' %Hflags_compat %Hlocshm %Hlocsθ Hphys' Hwords' Hnp".
    iMod (ghost_map_update (update_path_words off ws ws_new) with "Hheap Hpt") as "[Hheap' Hpt']".
    iModIntro.
    iFrame "Hpt' Ha".
    pose proof (Forall2_length _ _ _ Hns'') as Hns32'len.
    iPoseProof (big_sepL2_length with "Hwords'") as "%Hns'len".
    set (hm' := <[ℓ := update_path_words off ws ws_new]> hm).
    iAssert (rt_token_nophys rti sr lmask θ hm') with "[Hnp]" as "Hnp'".
    { iApply (rt_token_nophys_insert_heap_weak _ _ _ _ ws with "Hnp").
      - exact Hhm.
      - intro Hcontra; done.
      - eauto.
      - eauto. }
    iApply (rt_token_putheap _ _ lmask θ hm' with "Hnp'").
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

  Lemma atom_to_words_mm θ ι o val_v :
    has_arep ι o ->
    atom_interp_weak θ MemMM o val_v -∗
    ∃ (ns : list N) (ns32 : list i32),
      ⌜Forall2 N_i32_repr ns ns32⌝ ∗
      ⌜flat_map serialise_i32 ns32 = bits val_v⌝ ∗
      ⌜types_agree (translate_arep ι) val_v⌝ ∗
      words_interp θ MemMM (serialize_atom o) ns.
  Proof.
    iIntros (Harep) "Hat".
    destruct ι.
    - pose proof Harep as Harepsave.
      destruct o; cbn in Harep; try inversion Harep; clear Harep.
      iEval (cbn) in "Hat".
      iDestruct "Hat" as "(%n & %n32 & %Nrepr & -> & Hat)".
      iExists [n], [n32].
      iSplitR; [|iSplitR; [|iSplitR]]; try iPureIntro; try done; try (constructor;done).
      cbn.
      iFrame.
    - destruct o; cbn in Harep; try inversion Harep; clear Harep.
      iEval (cbn) in "Hat".
      iDestruct "Hat" as "->".
      cbn.
      unfold word_interp.
      iExists [(Z.to_N (Wasm_int.Int32.unsigned n))].
      iExists [n].
      iSplitR; [|iSplitR; [|iSplitR]]; try iPureIntro; try done; try (constructor;done).
      cbn.
      auto.
    - destruct o; cbn in Harep; try inversion Harep; clear Harep.
      iEval (cbn) in "Hat".
      iDestruct "Hat" as "->".
      cbn.
      unfold word_interp.
      iExists [(Z.to_N (Wasm_int.Int32.Z_mod_modulus (Wasm_int.Int64.unsigned n)));
        (Z.to_N (Wasm_int.Int64.unsigned n ≫ 32))].
      iExists _.
  (* I'm pretty confident this is true but splitting apart the serializing
     is tricky? *)
      admit.
      (* iSplitR; [|iSplitR; [|iSplitR]]; try iPureIntro; try done; try (constructor;done). *)
      (* 2: { *)
      (*   Search serialise_i64. *)
      (* } *)
      (* + constructor. *)
      (*   * Check ((Wasm_int.Int32.Z_mod_modulus (Wasm_int.Int64.unsigned n))). *)
      (*     Search i64. *)
      (*     Search (Wasm_int.Int32.Z_mod_modulus). *)
      (*     instantiate (1:= ((Wasm_int.Int32.Z_mod_modulus (Wasm_int.Int64.unsigned n)))). *)
      (* auto. *)
  Admitted.


  Lemma atom_to_words_gc θ ι o val_v :
    has_arep ι o ->
    atom_interp_weak θ MemGC o val_v -∗
    ∃ (ns : list N) (ns32 : list i32),
      ⌜Forall2 N_i32_repr ns ns32⌝ ∗
      ⌜flat_map serialise_i32 ns32 = bits val_v⌝ ∗
      ⌜types_agree (translate_arep ι) val_v⌝ ∗
      words_interp θ MemGC (serialize_atom o) ns.
  Proof.
    iIntros (Harep) "Hat".
    destruct ι.
    - pose proof Harep as Harepsave.
      destruct o; cbn in Harep; try inversion Harep; clear Harep.
      iEval (cbn) in "Hat".
      iDestruct "Hat" as "(%n & %n32 & %Nrepr & -> & Hat)".
      iExists [n], [n32].
      iSplitR; [|iSplitR; [|iSplitR]]; try iPureIntro; try done; try (constructor;done).
      cbn.
      iFrame.
      (* okay cool! I expect the other cases to be as true as the mm ones *)
    - destruct o; cbn in Harep; try inversion Harep; clear Harep.
      iEval (cbn) in "Hat".
      iDestruct "Hat" as "->".
      cbn.
      unfold word_interp.
      iExists [(Z.to_N (Wasm_int.Int32.unsigned n))].
      iExists [n].
      iSplitR; [|iSplitR; [|iSplitR]]; try iPureIntro; try done; try (constructor;done).
      cbn.
      auto.
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
      destruct μ; destruct p; try destruct μ.
      + iDestruct "Hws" as "%Hrep";
          iPureIntro;
          intuition;
          exists n, n32; intuition eauto;
          cbn [bs flat_map];
          apply deserialise_serialise_i32.
      + iDestruct "Hws" as "(%a & %Hrep & Haddr)".
        iSplitL "Haddr".
        * iFrame.
          inversion Hrep; subst.
          iPureIntro.
          do 2 eexists; intuition eauto.
          apply deserialise_serialise_i32.
        * rewrite deserialise_serialise_i32.
          cbn.
          iIntros "(%n' & %n32' & %Hnrep & %Hval & %a' & %Hrep' & Haddr)".
          inversion Hval; subst n32'.
          assert (n = n') by (eapply N_i32_repr_inj; eauto).
          subst n'.
          inversion Hrep; subst.
          inversion Hrep'; subst.
          assert ((4 <= a')%N) by (by eapply mod_bound_nonzero).
          assert ((4 <= a)%N) by (by eapply mod_bound_nonzero).
          assert (a' = a) by lia.
          subst a'.
          iExists a.
          by iFrame.
      + iDestruct "Hws" as "(%a & %Hrep & Hroot)".
        iSplitL "Hroot".
        * iFrame.
          inversion Hrep; subst.
          iPureIntro.
          do 2 eexists; intuition eauto.
          apply deserialise_serialise_i32.
        * rewrite deserialise_serialise_i32.
          cbn.
          iIntros "(%n' & %n32' & %Hnrep & %Hval & %a' & %Hrep' & Haddr)".
          inversion Hval; subst n32'.
          assert (n = n') by (eapply N_i32_repr_inj; eauto).
          subst n'.
          inversion Hrep; subst.
          inversion Hrep'; subst.
          assert ((4 <= a')%N) by (by eapply mod_bound_nonzero).
          assert ((4 <= a)%N) by (by eapply mod_bound_nonzero).
          assert (a' = a) by lia.
          subst a'.
          iExists a.
          by iFrame.
      + iDestruct "Hws" as "%Hrep";
          iPureIntro;
          intuition;
          exists n, n32; intuition eauto;
          cbn [bs flat_map];
          apply deserialise_serialise_i32.
      + iDestruct "Hws" as "(%a & %Hrep & Hroot)".
        iSplitL "Hroot".
        * iFrame.
          inversion Hrep; subst.
          iPureIntro.
          do 2 eexists; intuition eauto.
          apply deserialise_serialise_i32.
        * rewrite deserialise_serialise_i32.
          cbn.
          iIntros "(%n' & %n32' & %Hnrep & %Hval & %a' & %Hrep' & Haddr)".
          inversion Hval; subst n32'.
          assert (n = n') by (eapply N_i32_repr_inj; eauto).
          subst n'.
          inversion Hrep; subst.
          inversion Hrep'; subst.
          assert ((4 <= a')%N) by (by eapply mod_bound_nonzero).
          assert ((4 <= a)%N) by (by eapply mod_bound_nonzero).
          assert (a' = a) by lia.
          subst a'.
          iExists a.
          by iFrame.
      + iDestruct "Hws" as "%Hrep";
          iPureIntro;
          intuition;
          exists n, n32; intuition eauto;
          cbn [bs flat_map];
          apply deserialise_serialise_i32.
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
    destruct μ, p; try destruct μ; cbn.
    - iDestruct "H" as "%H".
      iPureIntro. inversion H. subst. constructor.
    - iDestruct "H" as "(%a & %repr & _)".
      iPureIntro.
      inversion repr; subst; constructor; eauto.
    - iDestruct "H" as "(%a & %repr & _)".
      iPureIntro.
      inversion repr; subst; constructor; eauto.
    - iDestruct "H" as "%H".
      iPureIntro. inversion H. subst. constructor.
    - iDestruct "H" as "(%a & %repr & _)".
      iPureIntro.
      inversion repr; subst; constructor; eauto.
    - iDestruct "H" as "%H".
      iPureIntro. inversion H. subst. constructor; eauto.
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



  Lemma wp_mem_load1_cg_state
    μ fe con lidx off ι wt wl ret wt' wl' es :
    run_codegen (memory.load1 mr fe μ con lidx off ι) wt wl = inr (ret, wt', wl', es) ->
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
      destruct μ.
      + destruct con.
        * pose proof (wp_duproot rti sr mr _ _ _ _ _ _ Hdup) as Hduproot.
          destruct Hduproot as (_ & -> & -> & _).
          by destruct ret.
        * inv_cg_ret Hdup.
          by destruct ret.
      + pose proof (wp_registerroot rti sr mr _ _ _ _ _ _ Hdup) as Hregroot.
        destruct Hregroot as (_ & -> & -> & _).
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
    intros A B P x l k H.
    rewrite rcons_app in H.
    apply Forall2_app_inv_l in H as [k1 [k2 [Heq [Hk1 Hk2]]]].
    apply Forall2_length in Hk1 as Hlen2. simpl in Hlen2.
    destruct k2 as [| y []]; simpl in Hlen2; try lia.
    inversion Hk1 as [| ay bl al1 al2 Hpair Hfl]; subst.
    exists y, k1.
    repeat split; try done.
    by rewrite rcons_app.
  Qed.

  Lemma big_sepL2_rcons_inv_l:
    ∀ {PROP : bi} {A B : Type} (Φ : nat → A → B → PROP) (x1 : A) (l1 : list A) (l2 : list B),
      ([∗ list] k↦y1;y2 ∈ (seq.rcons l1 x1);l2, Φ k y1 y2)
      ⊢ ∃ (x2 : B) (l2' : list B),
          ⌜l2 = seq.rcons l2' x2⌝ ∧ Φ 0 x1 x2 ∗ ([∗ list] k↦y1;y2 ∈ l1;l2', Φ (S k) y1 y2).
  Proof using.
  Admitted.

  Lemma big_sepL2_rcons_inv_r :
    ∀ {PROP: bi} {A B : Type} (Φ : nat → A → B → PROP) (x2 : B) (l1 : list A) (l2 : list B),
         ([∗ list] k↦y1;y2 ∈ l1;(seq.rcons l2 x2), Φ k y1 y2)
         ⊢ ∃ (x1 : A) (l1' : list A),
             ⌜l1 = seq.rcons l1' x1⌝ ∧ Φ 0 x1 x2 ∗ ([∗ list] k↦y1;y2 ∈ l1';l2, Φ (S k) y1 y2).
  Proof using.
  Admitted.

  Lemma big_sepL2_rcons :
    ∀ {PROP : bi} {A B : Type} (Φ : nat → A → B → PROP) (x1 : A) (x2 : B) (l1 : list A) (l2 : list B),
      ([∗ list] k↦y1;y2 ∈ (seq.rcons l1 x1);(seq.rcons l2 x2), Φ k y1 y2) ⊣⊢ Φ 0 x1 x2 ∗ ([∗ list] k↦y1;y2 ∈ l1;l2, Φ (S k) y1 y2).
  Proof using.
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
  Proof using.
  Admitted.

  Lemma ref_flag_atoms_interp_rcons:
    ∀ (ξ : ref_flag) (o : atom) (os : list atom),
      ref_flag_atoms_interp ξ (SAtoms (seq.rcons os o)) ↔
      forall_ptr_atom (ref_flag_ptr_interp ξ) o ∧ ref_flag_atoms_interp ξ (SAtoms os).
  Proof.
    intros ξ o os.
    unfold ref_flag_atoms_interp, forall_satoms.
    rewrite rcons_app Forall_app.
    split.
    - intros [Hos Ho]. split; [by apply Forall_inv in Ho | done].
    - intros [Ho Hos]. split; [done |]. constructor; [done | constructor].
  Qed.

  (* Lemma rcons_app {X} : forall (xs : list X) x, *)
  (*     seq.rcons xs x = xs ++ [x]. *)
  (* Proof. *)
  (*   induction xs; intros x. *)
  (*   - reflexivity. *)
  (*   - cbn. *)
  (*     by rewrite IHxs. *)
  (* Qed. *)

  (* Lemma flat_map_rcons X Y (f : X -> list Y) xs x : *)
  (*   flat_map f (seq.rcons xs x) = flat_map f xs ++ f x. *)
  (* Proof. *)
  (*   revert x. *)
  (*   induction xs; cbn; intros. *)
  (*   - by clear_nils. *)
  (*   - by rewrite -app_assoc IHxs. *)
  (* Qed. *)

  Lemma mk_frame_rcons fe f wl vs v :
    mk_load1_frame fe (mk_load_frame fe f wl vs) (length wl + length vs) v =
      mk_load_frame fe f wl (vs ++ [v]).
  Proof.
    unfold mk_load_frame.
    by rewrite -rcons_app imap_rcons seq.foldl_rcons.
  Qed.

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
    induction ιs as [| ιs ι IH] using seq.last_ind; intros off' offs' off offs Hfold.
    - by inversion Hfold.
    - rewrite seq.foldl_rcons in Hfold.
      destruct seq.foldl as [off'' offs''] eqn:Hf.
      inversion Hfold; subst.
      rewrite seq.foldl_rcons.
      by erewrite (IH _ _ _ _ Hf).
  Qed.

  Lemma simple_fold_sum_list_with ιs : ∀ off,
    seq.foldl (λ off' ι, off' + arep_size ι) off ιs = off + sum_list_with arep_size ιs.
  Proof.
    intros off.
    apply seq_foldl_sum_list_with.
  Qed.

  (* Lemma sum_list_with_rcons {X : Type} (f : X -> nat) (x : X) (xs : list X) : *)
  (*   sum_list_with f (seq.rcons xs x) = f x + sum_list_with f xs. *)
  (* Proof. *)
  (* Admitted. *)

  Lemma update_update_wordint ιs off ws ns1 ns2 :
    update_path_words (seq.foldl (λ off' ι0, off' + arep_size ι0) off ιs)
      (update_path_words off ws (map WordInt ns1))
      (map WordInt ns2) =
      update_path_words off ws (map WordInt (ns1 ++ ns2)).
  Proof.
  Admitted.

  Lemma Forall2_rcons_inv_r:
    ∀ {A B : Type} (P : A → B → Prop) (x : B) (l : list B) (k : list A),
      Forall2 P k (seq.rcons l x) → ∃ (y : A) (k' : list A), P y x ∧ Forall2 P k' l ∧ k = seq.rcons k' y.
  Proof.
    intros A B P x l.
    induction l as [| l0 l IH]; intros k H.
    - simpl in H.
      destruct k as [| y []]; [by inversion H | | apply Forall2_length in H; simpl in H; lia].
      inversion H as [| ay bl al1 al2 Hpair Hfl]; subst.
      inversion Hfl; subst.
      exists y, []. simpl. eauto.
    - simpl in H.
      apply Forall2_length in H as Hlen. simpl in Hlen.
      destruct k as [| y k']; [simpl in Hlen; lia |].
      inversion H as [| ay bl al1 al2 Hpair Hfl]; subst.
      apply IH in Hfl as [z [k1 [Hz [Hfl2 ->]]]].
      exists z, (y :: k1).
      split; [done|]. split; [constructor; done|]. done.
  Qed.

  Lemma Forall2_rcons {A B : Type} (P : A -> B -> Prop) xs x ys y :
    Forall2 P xs ys ->
    P x y ->
    Forall2 P (seq.rcons xs x) (seq.rcons ys y).
  Proof.
    intros H Hxy.
    rewrite !rcons_app.
    apply Forall2_app; [done|].
    by constructor.
  Qed.

  Lemma get_path_split_app ι o os off sz ws :
    off + sz <= length ws ->
    has_arep ι o ->
    get_path_words off sz ws = flat_map serialize_atom os ++ serialize_atom o ->
    arep_size ι <= sz /\
    get_path_words off (sz - arep_size ι) ws = flat_map serialize_atom os /\
    get_path_words (off + sz - arep_size ι) (arep_size ι) ws = serialize_atom o.
  Proof.
    intros Hlen Ho Hws.
    assert (arep_size ι ≤ sz).
    {
      apply (f_equal length) in Hws.
      rewrite length_take length_drop length_app in Hws.
      erewrite has_arep_size in Hws; eauto.
      lia.
    }
    assert (get_path_words off sz ws =
              get_path_words off (sz - arep_size ι) ws ++
              get_path_words (off + sz - arep_size ι) (arep_size ι) ws).
    {
      unfold get_path_words.
      replace (@take word sz) with (@take word ((sz - arep_size ι) + arep_size ι));
        last (f_equal; lia).
      rewrite -take_take_drop.
      rewrite drop_drop.
      repeat f_equal; lia.
    }
    rewrite H0 in Hws.
    eapply app_inj_1 in Hws; eauto.
    apply (f_equal length) in Hws.
    rewrite !length_app in Hws.
    assert (length (get_path_words (off + sz - arep_size ι) (arep_size ι) ws)
            = arep_size ι) as Hlast
        by (rewrite length_take length_drop; lia).
    rewrite Hlast in Hws.
    erewrite has_arep_size in Hws; last by eauto.
    lia.
  Qed.

  Lemma ser_offsets os : ∀ (off : nat) ntgt ws ιs,
    off + ntgt <= length ws ->
    Forall2 has_arep ιs os ->
    get_path_words off ntgt ws = flat_map serialize_atom os ->
    Forall2
      (λ o '(off0, sz), serialize_atom o = get_path_words off0 sz ws)
      os
     (seq.zip
        (seq.foldl (λ '(off', offs) ι, ((off' + arep_size ι)%nat, seq.rcons offs off'))
                   (off, [])
                   ιs).2
        (map arep_size ιs)).
  Proof.
    induction os as [|os o] using seq.last_ind; intros * Hlen Hreps Hser.
    - cbn in Hser.
      inversion Hreps; subst.
      econstructor.
    - apply Forall2_rcons_inv_r in Hreps.
      destruct Hreps as (ι & ιs' & Ho & Hos & ->).
      change map with @seq.map.
      rewrite seq.map_rcons.
      rewrite seq.foldl_rcons.
      destruct (seq.foldl
            (λ '(off', offs) (ι0 : atomic_rep),
               (off' + arep_size ι0, seq.rcons offs off'))
            (off, []) ιs') as [off' offs] eqn:Hoffs.
      pose proof Hoffs as Hoffslen.
      apply load_fold_offs_len in Hoffslen; cbn in Hoffslen; rewrite Nat.add_0_r in Hoffslen.
      rewrite flat_map_rcons in Hser.
      rewrite seq.zip_rcons;
        last (rewrite seq.size_map; by apply Hoffslen).
      eapply get_path_split_app in Hser; eauto.
      destruct Hser as (Hsz & Hseros & Hsero).
      apply Forall2_rcons.
      + eapply IHos in Hos; try eapply Hseros; eauto; last lia.
        by rewrite Hoffs in Hos.
      + eapply simple_fold_fancy_fold in Hoffs; eauto.
        rewrite simple_fold_sum_list_with in Hoffs; eauto.
        rewrite -Hoffs.
        rewrite -Hsero.
        f_equal.
        rewrite sum_list_with_list_sum.
        erewrite <- has_areps_size; last eauto.
        rewrite -map_map.
        apply (f_equal length) in Hseros.
        rewrite length_take length_drop in Hseros.
        rewrite flat_map_concat_map length_concat in Hseros.
        rewrite -Hseros.
        lia.
  Qed.

  Lemma mk_load_frame_locs F wl f vs_l vs0 vs vs_r :
    let fe := fe_of_context F in
    length vs_l = sum_list_with length (typing.fc_locals F) + length wl ->
    length vs = length vs0 ->
    f_locs f = vs_l ++ vs0 ++ vs_r ->
    f_locs (mk_load_frame (fe_of_context F) f wl vs) = vs_l ++ vs ++ vs_r.
  Proof.
    revert vs0 vs_r.
    induction vs as [|vs v] using seq.last_ind; cbn; intros * Hvss Hvs0 Hf.
    - destruct vs0; cbn in * ;try lia.
      done.
    - destruct vs0 using seq.last_ind;
        first (change @length with @seq.size in Hvs0;
                 by rewrite seq.size_rcons in Hvs0).
      change @length with @seq.size in Hvs0.
      unfold mk_load_frame in *.
      rewrite imap_rcons seq.foldl_rcons.
      rewrite !seq.size_rcons in Hvs0.
      cbn.
      setoid_rewrite IHvs;
        last (by rewrite Hf rcons_app -app_assoc);
        eauto.
      rewrite sum_list_with_list_sum.
      rewrite -length_concat.
      rewrite Nat.add_assoc.
      assert (length vs_l = length (concat (typing.fc_locals F)) + length wl) as Hvsslen.
      {
        rewrite !length_concat Hvss.
        by rewrite sum_list_with_list_sum.
      }
      rewrite -Hvsslen.
      rewrite insert_app_r; f_equal.
      rewrite app_assoc.
      rewrite insert_app_l; f_equal.
      + rewrite rcons_app.
        replace (length vs) with (length vs + 0) by lia.
        by rewrite insert_app_r.
      + rewrite length_app; cbn.
        lia.
  Qed.

  Lemma types_agree_val_interp t v :
    types_agree t v <-> value_type_interp t v.
  Proof.
    unfold types_agree, value_type_interp.
    destruct t, v; cbn;
      match goal with
      | |- is_true true <-> _ =>
          split; [eexists; eauto | done]
      | |- is_true false <-> _ =>
          split; [intros f; inversion f |
                  intros (v & Hv); inversion Hv ]
      end.
  Qed.


  Lemma load_restore_frame wl wlf1 wlf2 se F L ah32 vn32 fr ptr_local vs ιs :
    let wls := wl ++ T_i32 :: wlf1 ++ map translate_arep ιs ++ wlf2 in
    "Hframe" ∷ frame_interp rti sr se (typing.fc_locals F) L wls fr -∗
    "%Hptr_local" ∷ ⌜(ptr_local = sum_list_with length (typing.fc_locals F) + length wl)%nat⌝ -∗
    "%Hvs" ∷ ⌜Forall2 (λ ι v, types_agree (translate_arep ι) v) ιs vs⌝ -∗
    frame_interp rti sr se (typing.fc_locals F) L wls
      (mk_load_frame (fe_of_context F)
        {|
          W.f_locs :=
            <[localimm (Mk_localidx ptr_local):=VAL_int32 ah32]>
              (f_locs {| W.f_locs := <[ptr_local:=VAL_int32 vn32]> (f_locs fr); W.f_inst := f_inst fr |});
          W.f_inst := f_inst {| W.f_locs := <[ptr_local:=VAL_int32 vn32]> (f_locs fr); W.f_inst := f_inst fr |}
        |} (wl ++ [T_i32] ++ wlf1) vs).
  Proof.
    iIntros (wls).
    repeat iIntros "@".
    unfold frame_interp.
    iDestruct "Hframe" as "(%ηss & %vss_L' & %vs_WL' & %fr' & Hframe)".
    iDestruct "Hframe" as "(%Hprims & %Hres & Hats & Hlocs)".
    apply Forall2_app_inv_l in Hres.
    destruct Hres as (vs1 & vs' & Hvs1 & Hvs' & ->).
    apply Forall2_cons_inv_l in Hvs'.
    destruct Hvs' as (v1 & vs'' & Hv1 & Hvs'' & ->).
    change (v1 :: vs'') with ([v1] ++ vs'') in *.
    apply Forall2_app_inv_l in Hvs''.
    destruct Hvs'' as (?vs & ?vs & ?Hvs & ?Hv1 & ->).
    apply Forall2_app_inv_l in Hv0.
    destruct Hv0 as (?vs & ?vs & ?Hvs & ?Hvs & ->).
    subst ptr_local.
    pose proof Hvs as Hvslen; apply Forall2_length in Hvslen.
    pose proof Hvs0 as Hvs0len; apply Forall2_length in Hvs0len.
    pose proof Hvs1 as Hvs1len; apply Forall2_length in Hvs1len.
    pose proof Hvs2 as Hvs3len; apply Forall2_length in Hvs3len.
    pose proof Hvs3 as Hvs4len; apply Forall2_length in Hvs4len.
    pose proof Hprims as Hvsslen. apply Forall2_Forall2_length in Hvsslen.
    iExists _, vss_L', _.
    iFrame.
    iPureIntro.
    intuition.
    - assert (map length vss_L' = map length (typing.fc_locals F)) as Hvss.
      { apply Forall2_Forall2_length in Hprims. congruence. }
      cbn.
      erewrite mk_load_frame_locs.
      + instantiate (2 := vs4).
        instantiate (2 := concat vss_L' ++ vs1 ++ [VAL_int32 ah32] ++ vs0).
        instantiate (1 := vs1 ++ [VAL_int32 ah32] ++ vs0 ++ vs ++ vs4).
        rewrite -!app_assoc.
        cbn.
        f_equal.
      + rewrite !length_app !length_cons length_concat.
        rewrite Hvss sum_list_with_list_sum; cbn.
        lia.
      + instantiate (1 := vs3).
        by rewrite -Hvs3len -Hvslen length_map.
      + cbn -[app].
        rewrite fr'.
        rewrite !Hvs1len.
        rewrite !sum_list_with_list_sum -!Hvss -length_concat.
        repeat rewrite insert_app_r.
        cbn [app].
        rewrite insert_app_r_alt; last done.
        rewrite insert_app_r_alt; last done.
        rewrite !Nat.sub_diag; cbn.
        by rewrite -!app_assoc; cbn.
    - unfold result_type_interp, wls.
      cbn [app].
      repeat (constructor || apply Forall2_app); eauto.
      + (* val_interp for ah32 *)
        eexists; eauto.
      + (* val_interps for vs *)
        rewrite Forall2_fmap_l.
        eapply Forall2_impl; first eapply Hvs.
        intros ι v Hv.
        by rewrite types_agree_val_interp in Hv.
  Qed.


End load_common.
