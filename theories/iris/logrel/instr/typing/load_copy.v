From mathcomp Require Import eqtype ssrbool.

Require Import RichWasm.util.
Require Import RichWasm.compiler.memory.
Require Import RichWasm.iris.numerics.
Require Import RichWasm.iris.runtime.
Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section load_copy.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma Z_i32_repr_inj2 z i j:
    Z_i32_repr z i ->
    Z_i32_repr z j ->
    i = j.
  Proof.
    unfold Z_i32_repr, Wasm_int.Int32.unsigned.
    intros Hi Hj.
    destruct i as [i ibdd].
    destruct j as [j jbdd].
    simpl in Hi, Hj; subst.
    destruct ibdd, jbdd.
    f_equal; f_equal; eauto using Wasm_int.Int32.Z_lt_irrelevant.
  Qed.

  Lemma N_i32_repr_inj2 n i j:
    N_i32_repr n i ->
    N_i32_repr n j ->
    i = j.
  Proof.
    unfold N_i32_repr, Wasm_int.N_of_uint; cbn.
    intros Hi Hj.
    destruct i as [i ibdd].
    destruct j as [j jbdd].
    simpl in Hi, Hj; subst.
    destruct ibdd, jbdd.
    assert (i = j) by lia; subst i.
    f_equal; f_equal; eauto using Wasm_int.Int32.Z_lt_irrelevant.
  Qed.

  Lemma cwp_mod2_test_1 f (idx: nat) k k32 E :
    N_i32_repr k k32 ->
    f.(f_locs) !! idx = Some (VAL_int32 k32) →
    (k `mod` 2 = 0)%N →
    ⊢ ↪[frame] f -∗
      ↪[RUN] -∗
      CWP [memory.W.BI_get_local idx;
           memory.W.BI_const (memory.W.VAL_int32 (Wasm_int.int_of_Z i32m 1));
           memory.W.BI_binop memory.W.T_i32 (memory.W.Binop_i memory.W.BOI_and);
           memory.W.BI_testop memory.W.T_i32 memory.W.TO_eqz]
          @ E
          UNDER []; None
          {{ f'; vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr 1)]⌝ }}.
  Proof.
    iIntros (Hk Hidx Hmod) "Hf Hrun".
    cwp_chomp 3%nat.
    iApply (cwp_seq with "[Hf Hrun]").
    - cwp_chomp 1%nat.
      iApply (cwp_seq with "[Hf Hrun]").
      + iApply (cwp_local_get with "[] [$] [$]"); first done.
        instantiate (1 := λ f' vs, ⌜f' = f /\ vs = [VAL_int32 k32]⌝%I).
        by iFrame.
      + iIntros (w f' [-> ->]) "Hf Hrun".
        assert (Hlandz: N.land k 1 = 0%N).
        { by rewrite (N.land_ones _ 1) Hmod. }
        iApply (cwp_binop with "[$] [$]").
        * cbn.
          reflexivity.
        * instantiate (1 := λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr 0)]⌝%I).
          cbn.
          iPureIntro.
          split; first done.
          do 2 f_equal.
          unfold Wasm_int.Int32.iand.
          pose proof (and_N_cong k 1%N k32 (Wasm_int.Int32.repr 1)
                        ltac:(assumption)
                               ltac:(apply N_repr_i32repr; by vm_compute))
                     as Hrep.
          rewrite Hlandz in Hrep.
          specialize (Hrep ltac:(by vm_compute)).
          eapply N_i32_repr_inj2; eauto.
          constructor.
    - iIntros (w f' [-> ->]) "Hf' Hrun".
      iApply (cwp_testop_i32 with "[$] [$]").
      + reflexivity.
      + cbn.
        iFrame.
        iSplit; eauto.
  Qed.

  Lemma cwp_mod2_test_1_2 f (idx: nat) k k32 E :
    N_i32_repr k k32 ->
    f.(f_locs) !! idx = Some (VAL_int32 k32) ->
    (k `mod` 2 = 1)%N ->
    ⊢ ↪[frame] f -∗
      ↪[RUN] -∗
      CWP [memory.W.BI_get_local idx;
           memory.W.BI_const (memory.W.VAL_int32 (Wasm_int.int_of_Z i32m 1));
           memory.W.BI_binop memory.W.T_i32 (memory.W.Binop_i memory.W.BOI_and);
           memory.W.BI_testop memory.W.T_i32 memory.W.TO_eqz]
          @ E
          UNDER []; None
          {{ f'; vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr 0)]⌝ }}.
  Proof.
    iIntros (Hk Hidx Hmod) "Hf Hrun".
    cwp_chomp 3%nat.
    iApply (cwp_seq with "[Hf Hrun]").
    - cwp_chomp 1%nat.
      iApply (cwp_seq with "[Hf Hrun]").
      + iApply (cwp_local_get with "[] [$] [$]"); first done.
        by instantiate (1 := λ f' vs, ⌜f' = f /\ vs = [VAL_int32 k32]⌝%I).
      + iIntros (w f' [-> ->]) "Hf Hrun".
        iApply (cwp_binop with "[$] [$]"); first done.
        instantiate (1 := λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr 1)]⌝%I).
        iPureIntro.
        split; first done.
        do 2 f_equal.
        cbn.
        unfold Wasm_int.Int32.iand.
        assert (Hlandz: N.land k 1 = 1%N).
        { by rewrite (N.land_ones _ 1) Hmod. }
        pose proof (and_N_cong k 1%N k32 (Wasm_int.Int32.repr 1)
                      ltac:(assumption)
                             ltac:(apply N_repr_i32repr; by vm_compute))
                   as Hrep.
        rewrite Hlandz in Hrep.
        specialize (Hrep ltac:(by vm_compute)).
        eapply N_i32_repr_inj2; eauto.
        constructor.
    - iIntros (w f' [-> ->]) "Hf' Hrun".
      iApply (cwp_testop_i32 with "[$] [$]").
      + reflexivity.
      + cbn.
        iFrame.
        iSplit; eauto.
  Qed.

  Lemma cwp_mod4_sub3_test_old f (idx: nat) k E :
    ⊢ ⌜f.(f_locs) !! idx = Some (VAL_int32 (Wasm_int.Int32.repr (k - 3)))⌝ →
      ⌜((Wasm_int.Int32.unsigned (Wasm_int.Int32.repr k)) `mod` 4 = 0)%Z⌝ →
      ↪[frame] f -∗
      ↪[RUN] -∗
      CWP [memory.W.BI_get_local idx;
           memory.W.BI_const (memory.W.VAL_int32 (Wasm_int.int_of_Z i32m 2));
           memory.W.BI_binop memory.W.T_i32 (memory.W.Binop_i memory.W.BOI_and);
           memory.W.BI_testop memory.W.T_i32 memory.W.TO_eqz]
          @ E
          UNDER []; None
          {{ f'; vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr 1)]⌝ }}.
  Proof.
    iIntros (Hidx Hmod) "Hf Hrun".
    cwp_chomp 3%nat.
    iApply (cwp_seq with "[Hf Hrun]").
    - cwp_chomp 1%nat.
      iApply (cwp_seq with "[Hf Hrun]").
      + iApply (cwp_local_get with "[] [$] [$]"); first done.
        by instantiate (1 := (λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr (k - 3))]⌝)%I).
      + iIntros (w f' [-> ->]) "Hf Hrun".
        iApply (cwp_binop with "[$] [$]").
        * cbn.
          reflexivity.
        * iFrame.
          instantiate (1 := (λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr 0)]⌝)%I).
          iPureIntro.
          split; first done.
          cbn.
          do 2 f_equal.
          unfold Wasm_int.Int32.iand.
          unfold Wasm_int.Int32.and.
          f_equal.
          unfold Wasm_int.Int32.repr, Wasm_int.Int32.unsigned in *; simpl in *.
          rewrite Wasm_int.Int32.Z_mod_modulus_eq.
          rewrite Wasm_int.Int32.Z_mod_modulus_eq in Hmod.
          replace (Wasm_int.Int32.modulus) with (4 * 1073741824)%Z in Hmod; last done.
          rewrite Z.mul_comm in Hmod.
          rewrite Zaux.Zmod_mod_mult in Hmod; try done.
          rewrite Zmod_divides in Hmod; last done.
          destruct Hmod as [? ->].
          unfold Wasm_int.Int32.modulus, Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize, two_power_nat; simpl.
          apply Z.bits_inj_iff.
          intros i.
          rewrite Z.land_spec.
          rewrite Z.testbit_0_l.
          destruct (Z.eq_dec i 1) as [-> | Hi].
          ** apply andb_false_intro1.
             replace (4294967296)%Z with (2 ^ 32)%Z; last lia.
             rewrite Z.mod_pow2_bits_low; last lia.
             replace (4)%Z with (2 ^ 2)%Z; last lia.
             rewrite Z.mul_comm.
             rewrite Z.add_bit1.
             rewrite Z.mul_pow2_bits_low; last lia.
             rewrite Z.mul_pow2_bits_low; last lia.
             done.
          ** rewrite (Z.pow2_bits_false 1 i); [|lia].
             apply andb_false_r.
    - iIntros (w f' [-> ->]) "Hf Hrun".
      iApply (cwp_testop_i32 with "[$] [$]").
      + reflexivity.
      + cbn.
        iFrame.
        iSplit; eauto.
  Qed.

  Lemma cwp_mod4_sub3_test f (idx: nat) k k32 E :
    N_i32_repr (k - 3) k32 ->
    f.(f_locs) !! idx = Some (VAL_int32 k32) ->
    (k `mod` 4 = 0)%N →
    k <> 0%N ->
    ⊢ ↪[frame] f -∗
      ↪[RUN] -∗
      CWP [memory.W.BI_get_local idx;
           memory.W.BI_const (memory.W.VAL_int32 (Wasm_int.int_of_Z i32m 2));
           memory.W.BI_binop memory.W.T_i32 (memory.W.Binop_i memory.W.BOI_and);
           memory.W.BI_testop memory.W.T_i32 memory.W.TO_eqz]
          @ E
          UNDER []; None
          {{ f'; vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr 1)]⌝ }}.
  Proof.
    intros Hrep Hloc Hmod Hnz.
    iApply (cwp_mod4_sub3_test_old _ _ (Z.of_N k)); iPureIntro.
    - rewrite Hloc; do 2 f_equal.
      eapply N_i32_repr_inj2; eauto.
      assert (Hsub: (Z.of_N k - 3 = Z.of_N (k - 3))%Z).
      {
        rewrite N2Z.inj_sub; first done.
        eapply N_i32_repr_bdd in Hrep.
        destruct k; try lia.
        destruct p as [? | ? |]; try (vm_compute in Hmod; lia).
        destruct p as [? | ? |]; try (vm_compute in Hmod; lia).
      }
      rewrite Hsub.
      apply N_repr_i32repr.
      + eapply N_i32_repr_bdd; eauto.
      + by apply N_Z_repr_of_N.
    - cbn.
      rewrite Wasm_int.Int32.Z_mod_modulus_eq.
      rewrite Z.mod_mod_divide.
      + change 4%Z with (Z.of_N 4%N).
        by rewrite -N2Z.inj_mod Hmod.
      + apply Z.divide_gcd_iff; first lia.
        by vm_compute.
  Qed.

  Lemma cwp_mod4_sub1_test_old f (idx: nat) k E :
    ⊢ ⌜f.(f_locs) !! idx = Some (VAL_int32 (Wasm_int.Int32.repr (k - 1)))⌝ →
      ⌜((Wasm_int.Int32.unsigned (Wasm_int.Int32.repr k)) `mod` 4 = 0)%Z⌝ →
      ↪[frame] f -∗
      ↪[RUN] -∗
      CWP [memory.W.BI_get_local idx;
           memory.W.BI_const (memory.W.VAL_int32 (Wasm_int.int_of_Z i32m 2));
           memory.W.BI_binop memory.W.T_i32 (memory.W.Binop_i memory.W.BOI_and);
           memory.W.BI_testop memory.W.T_i32 memory.W.TO_eqz]
          @ E
          UNDER []; None
          {{ f'; vs, ⌜f' = f⌝ ∗ ⌜vs = [VAL_int32 (Wasm_int.Int32.repr 0)]⌝ }}.
  Proof.
    iIntros (Hidx Hmod) "Hf Hrun".
    cwp_chomp 3%nat.
    iApply (cwp_seq with "[Hf Hrun]").
    - cwp_chomp 1%nat.
      iApply (cwp_seq with "[Hf Hrun]").
      + iApply (cwp_local_get with "[] [$] [$]"); first done.
        instantiate (1 := (λ f' vs, ⌜f' = f⌝ ∗ ⌜vs = [VAL_int32 (Wasm_int.Int32.repr (k - 1))]⌝)%I).
        by iFrame.
      + iIntros (w f' [-> ->]) "Hf Hrun".
        iApply (cwp_binop with "[$] [$]").
        * cbn.
          reflexivity.
        * iFrame.
          instantiate (1 := (λ f' vs, ⌜f' = f⌝ ∗ ⌜vs = [VAL_int32 (Wasm_int.Int32.repr 2)]⌝)%I).
          iPureIntro.
          split; first done.
          cbn.
          do 2 f_equal.
          unfold Wasm_int.Int32.iand.
          unfold Wasm_int.Int32.and.
          f_equal.
          unfold Wasm_int.Int32.repr, Wasm_int.Int32.unsigned in *; simpl in *.
          rewrite Wasm_int.Int32.Z_mod_modulus_eq.
          rewrite Wasm_int.Int32.Z_mod_modulus_eq in Hmod.
          replace (Wasm_int.Int32.modulus) with (4 * 1073741824)%Z in Hmod; last done.
          rewrite Z.mul_comm in Hmod.
          rewrite Zaux.Zmod_mod_mult in Hmod; try done.
          rewrite Zmod_divides in Hmod; last done.
          destruct Hmod as [? ->].
          unfold Wasm_int.Int32.modulus, Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize, two_power_nat; simpl.
          apply Z.bits_inj_iff.
          intros i.
          rewrite Z.land_spec.
          destruct (Z.eq_dec i 1) as [-> | Hi].
          ** replace (4294967296)%Z with (2 ^ 32)%Z; last lia.
             rewrite Z.mod_pow2_bits_low; last lia.
             replace (4)%Z with (2 ^ 2)%Z; last lia.
             rewrite Z.mul_comm.
             rewrite Z.add_bit1.
             rewrite Z.mul_pow2_bits_low; last lia.
             rewrite Z.mul_pow2_bits_low; last lia.
             done.
          ** rewrite (Z.pow2_bits_false 1 i); [|lia].
             apply andb_false_r.
    - iIntros (w f' [-> ->]) "Hf Hrun".
      iApply (cwp_testop_i32 with "[$] [$]").
      + reflexivity.
      + cbn.
        iFrame.
        iSplit; eauto.
  Qed.

  Lemma cwp_mod4_sub1_test f (idx: nat) k k32 E :
    N_i32_repr (k - 1) k32 ->
    f.(f_locs) !! idx = Some (VAL_int32 k32) ->
    (k `mod` 4 = 0)%N →
    k <> 0%N ->
    ⊢ ↪[frame] f -∗
      ↪[RUN] -∗
      CWP [memory.W.BI_get_local idx;
           memory.W.BI_const (memory.W.VAL_int32 (Wasm_int.int_of_Z i32m 2));
           memory.W.BI_binop memory.W.T_i32 (memory.W.Binop_i memory.W.BOI_and);
           memory.W.BI_testop memory.W.T_i32 memory.W.TO_eqz]
          @ E
          UNDER []; None
          {{ f'; vs, ⌜f' = f⌝ ∗ ⌜vs = [VAL_int32 (Wasm_int.Int32.repr 0)]⌝ }}.
  Proof.
    intros Hrep Hloc Hmod Hnz.
    iApply (cwp_mod4_sub1_test_old _ _ (Z.of_N k)); iPureIntro.
    - rewrite Hloc; do 2 f_equal.
      eapply N_i32_repr_inj2; eauto.
      assert (Hsub: (Z.of_N k - 1 = Z.of_N (k - 1))%Z).
      {
        rewrite N2Z.inj_sub; first done.
        eapply N_i32_repr_bdd in Hrep.
        destruct k; try lia.
      }
      rewrite Hsub.
      apply N_repr_i32repr.
      + eapply N_i32_repr_bdd; eauto.
      + by apply N_Z_repr_of_N.
    - cbn.
      rewrite Wasm_int.Int32.Z_mod_modulus_eq.
      rewrite Z.mod_mod_divide.
      + change 4%Z with (Z.of_N 4%N).
        by rewrite -N2Z.inj_mod Hmod.
      + apply Z.divide_gcd_iff; first lia.
        by vm_compute.
  Qed.

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

  Lemma value_interp_ref_sz se κ μ τ os :
    ⊢ value_interp rti sr se (RefT κ μ τ) (SAtoms os) -∗ ⌜length os = 1⌝.
  Proof.
    iIntros "Hv".
    rewrite value_interp_eq; cbn.
    iDestruct "Hv" as "(%κ0 & %Heval & Hkind & Hmem)".
    destruct μ as [| [|]]; auto.
    - iDestruct "Hmem" as "(%ℓ & %fs & %ws & %Hos & _)".
      by inversion Hos.
    - iDestruct "Hmem" as "(%ℓ & %fs & %Hos & _)".
      by inversion Hos.
  Qed.

  Lemma rep_ref_kind_ptr F κ μ τ ρ ξ :
    has_kind F (RefT κ μ τ) (VALTYPE ρ ξ) ->
    ρ = AtomR PtrR /\ exists ξ', κ = VALTYPE (AtomR PtrR) ξ'.
  Proof.
    intros Hkind.
    remember (RefT κ μ τ) as ref.
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
    - subst κ'.
      inversion H; subst; eapply IHHkind; eauto.
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

  Lemma root_pointer_heap_shp_inv rp μ ℓ :
    root_pointer_interp rp (PtrHeap μ ℓ) -∗
    ⌜∃ a, rp = RootHeap μ a⌝.
  Proof.
    iIntros "H".
    destruct rp; first done.
    cbn.
    iDestruct "H" as "(-> & _)".
    by iExists _.
  Qed.

  Lemma wp_load_w μ t off wt wl wt' wl' es ret :
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

  Lemma tag_address_odd μ a :
    (a `mod` 4 = 0 ->
     a <> 0 ->
     tag_address μ a `mod` 2 = 1)%N.
  Proof.
  Admitted.

  Lemma cwp_case_ptr {A B} (c1 : codegen B) (c2: base_memory -> codegen A) idx
    wt wt' wl wl' ts1 ts2 es x y z :
    run_codegen (memory.case_ptr idx (Tf ts1 ts2) c1 c2) wt wl = inr (x, (y, z), wt', wl', es) ->
    exists wt1 wt2 wt3 wl1 wl2 wl3 es1 es2 es3,
      run_codegen c1 wt wl = inr (x, wt1, wl1, es1) /\
      run_codegen (c2 MemMM) (wt ++ wt1) (wl ++ wl1) = inr (y, wt2, wl2, es2) /\
      run_codegen (c2 MemGC) (wt ++ wt1 ++ wt2) (wl ++ wl1 ++ wl2) = inr (z, wt3, wl3, es3) /\
      wt' = wt1 ++ wt2 ++ wt3 /\
      wl' = wl1 ++ wl2 ++ wl3 /\
      forall evs vs,
        has_values evs vs ->
        length ts1 = length vs ->
        ⊢ ∀ (s: stuckness) E L R (ptr: pointer) Φ (v: value) (f: frame),
          ↪[frame] f -∗
          ↪[RUN] -∗
          ⌜f.(f_locs) !! localimm idx = Some v⌝ -∗
          atom_interp (PtrA ptr) v -∗
          ▷ (↪[frame]f -∗
              ↪[RUN] -∗
              atom_interp (PtrA ptr) v -∗
              match ptr with
              | PtrInt z => CWP evs ++ es1 @ s; E UNDER []; R {{ Φ }}
              | PtrHeap MemMM l => CWP evs ++ es2 @ s; E UNDER []; R {{ Φ }}
              | PtrHeap MemGC l => CWP evs ++ es3 @ s; E UNDER []; R {{ Φ }}
              end) -∗
          CWP evs ++ es @ s; E UNDER L; R {{ Φ }}.
  Proof.
    intros Hcg.
    unfold memory.case_ptr in Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es_isptr ?es_if_isptr Hcg_isptr Hcg_if_isptr.
    inv_cg_emit_all Hcg_isptr.
    subst.
    rewrite -> !app_nil_l, !app_nil_r in *.
    eapply cwp_if_c in Hcg_if_isptr; eauto.
    destruct Hcg_if_isptr as (?wt & ?wt & ?wl & ?wl & es_int & es_case_m & Hcg_int & Hcg_case_m & -> & -> & Hwp_if_isptr).
    inv_cg_bind Hcg_case_m [] ?wt ?wt ?wl ?wl ?es_mm_or_gc es_if_m Hcg_mm_or_gc Hcg_if_m.
    inv_cg_emit_all Hcg_mm_or_gc.
    subst.
    eapply cwp_if_c in Hcg_if_m; eauto.
    destruct Hcg_if_m as (?wt & ?wt & ?wl & ?wl & es_mm & es_gc & Hcg_mm & Hcg_gc & -> & -> & Hwp_if_m).
    rewrite <- !app_assoc, !app_nil_r, !app_nil_l in *.
    exists wt0, wt1, wt2, wl0, wl1, wl2.
    exists es_int, es_mm, es_gc.
    do 5 (split; first done).
    intros evs vs Hval Hlen.
    assert (is_consts evs).
    {
      apply Is_true_true.
      eapply has_values_is_consts.
      apply Is_true_true.
      apply Hval.
    }
    assert (length evs = length ts1)
      by (erewrite has_values_length; eauto).
    clear Hcg_int Hcg_mm Hcg_gc Hretval Hretval0.
    iIntros (s E L R ptr Φ v f) "Hframe Hrun %Hlookup_f Hrep Hptr".
    destruct ptr.
    - iEval (cbn) in "Hrep".
      iDestruct "Hrep" as "(%vn & %vn32 & %Hvn & -> & %rp & %Hrep & Hroot)".
      destruct rp as [r|? ?].
      + rewrite app_assoc.
        iApply (cwp_seq with "[Hframe Hrun]").
        {
          iApply cwp_val_app; eauto.
          iApply cwp_label_take.
          instantiate (2 := 0%nat).
          iApply cwp_return_none.
          iApply (cwp_wand with "[Hframe Hrun]").
          {
            iApply (cwp_mod2_test_1 with "[$] [$]"); eauto.
            inversion Hrep.
            rewrite N.mul_comm.
            apply N.Div0.mod_mul.
          }
          cbn.
          instantiate (1:= λ f' vs', ⌜f' = f /\ vs' = vs ++ [VAL_int32 (Wasm_int.Int32.repr 1)]⌝%I).
          iIntros (vs' f') "[-> ->]".
          unfold fvs_combine; simpl; auto.
        }
        iIntros (vs' f') "[-> ->] Hf Hrun".
        unfold to_consts; rewrite map_app -app_assoc.
        erewrite <- has_values_to_consts_inv by eauto.
        iApply (Hwp_if_isptr with "[$] [$]"); auto.
        iLeft.
        iSplit; [iPureIntro; done|].
        iIntros "!> Hf Hrun".
        iApply (cwp_label_wand with "[-]");
          [| iApply label_ctx_wand_nil].
        iApply ("Hptr" with "[$] [$]").
        iExists vn, vn32; auto.
      + done.
    - iDestruct "Hrep" as "(%vn & %vn32 & %Hvn & -> & %rp & %Hrep & Hroot)".
      iPoseProof (root_pointer_heap_shp_inv with "Hroot") as "(%a & ->)".
      inversion Hrep as [|? ? Hmod]; subst.
      rewrite app_assoc.
      iApply (cwp_seq with "[Hframe Hrun]").
      {
        iApply cwp_val_app; [eauto|].
        iApply (cwp_wand with "[Hframe Hrun]").
        {
          iApply cwp_label_take.
          instantiate (2 := 0%nat).
          iApply cwp_return_none.
          iApply (cwp_mod2_test_1_2 with "[$] [$]"); eauto.
          apply tag_address_odd; eauto.
        }
        unfold fvs_combine.
        instantiate (1:= (λ f' vs', ⌜f' = f /\ vs' = vs ++ [VAL_int32 (Wasm_int.Int32.repr 0)]⌝ )%I).
        by iIntros (f' v') "[-> ->]".
      }
      iIntros (w f' [-> ->]) "Hf Hrun".
      unfold to_consts; rewrite map_app -app_assoc.
      erewrite <- has_values_to_consts_inv by eauto.
      iApply (Hwp_if_isptr with "[$] [$]"); auto.
      iRight.
      iSplit; first done.
      iIntros "!> Hframe Hrun".
      rewrite app_assoc.
      destruct μ.
      + iApply (cwp_seq with "[Hframe Hrun]").
        {
          iApply cwp_val_app; eauto.
          iApply (cwp_wand with "[Hframe Hrun]").
          {
            simpl tag_address in Hlookup_f.
            cbn.
            rewrite <- (app_nil_l [_]).
            rewrite app_nil_l.
            iApply cwp_label_take.
            instantiate (2 := 0%nat).
            iApply cwp_return_none.
            iApply (cwp_mod4_sub3_test with "[$] [$]"); eauto.
          }
          iIntros (f' vs') "[-> ->]".
          instantiate (1 := λ f' vs', ⌜f' = f /\ vs' = vs ++ [VAL_int32 (Wasm_int.Int32.repr 1)]⌝%I).
          auto.
        }
        iIntros (w f' [-> ->]) "Hf Hrun".
        unfold to_consts; rewrite map_app -app_assoc.
        erewrite <- has_values_to_consts_inv by eauto.
        iApply (Hwp_if_m with "[$] [$]"); auto.
        iLeft.
        iSplit; eauto.
        iIntros  "!> Hf Hrun".
        iApply (cwp_label_wand with "[Hptr Hroot Hf Hrun]");
          [| iApply label_ctx_wand_nil].
        iApply ("Hptr" with "[$] [$]").
        iExists _, _; eauto.
      + iApply (cwp_seq with "[Hframe Hrun]").
        {
          iApply cwp_val_app; eauto.
          iApply (cwp_wand with "[Hframe Hrun]").
          {
            simpl tag_address in Hlookup_f.
            cbn.
            rewrite <- (app_nil_l [_]).
            rewrite app_nil_l.
            iApply cwp_label_take.
            instantiate (2 := 0%nat).
            iApply cwp_return_none.
            iApply (cwp_mod4_sub1_test with "[$] [$]"); eauto.
          }
          iIntros (f' vs') "[-> ->]".
          instantiate (1 := λ f' vs', ⌜f' = f /\ vs' = vs ++ [VAL_int32 (Wasm_int.Int32.repr 0)]⌝%I).
          auto.
        }
        iIntros (w f' [-> ->]) "Hf Hrun".
        unfold to_consts; rewrite map_app -app_assoc.
        erewrite <- has_values_to_consts_inv by eauto.
        iApply (Hwp_if_m with "[$] [$]"); auto.
        iRight.
        iSplit; eauto.
        iIntros  "!> Hf Hrun".
        iApply (cwp_label_wand with "[Hptr Hroot Hf Hrun]");
          [| iApply label_ctx_wand_nil].
        iApply ("Hptr" with "[$] [$]").
        iExists _, _; eauto.
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

  Lemma wp_ite_gc_ptr_ptr i ts1 ts2 do_gc do_nongc ret wt wl wt' wl' es evs vs s E R L Φ f v:
    run_codegen (ite_gc_ptr PtrR i (W.Tf ts1 ts2) do_gc do_nongc) wt wl = inr (ret, wt', wl', es) ->
    has_values evs vs ->
    length ts1 = length vs ->
    ∃ wt1 wt2 wt3 wl1 wl2 wl3 es1 es2 es3,
      run_codegen do_nongc wt wl = inr ((), wt1, wl1, es1) ∧
      run_codegen do_nongc (wt ++ wt1) (wl ++ wl1) = inr ((), wt2, wl2, es2) /\
        run_codegen do_gc (wt ++ wt1 ++ wt2) (wl ++ wl1 ++ wl2) = inr ((), wt3, wl3, es3) /\
      wt' = wt1 ++ wt2 ++ wt3 /\
        wl' = wl1 ++ wl2 ++ wl3 ∧
        ⊢ ∀ ptr,
            ↪[frame]f -∗
             ↪[RUN] -∗
            ⌜f_locs f !! localimm i = Some v⌝ -∗
            atom_interp (PtrA ptr) v -∗
            ▷ ( ↪[frame]f -∗
                ↪[RUN] -∗
               atom_interp (PtrA ptr) v -∗
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
    iIntros (ptr) "Hf Hrun %Hi Hat Hbr".
    iApply (Hspec with "[$] [$] [//] [$]"); eauto.
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

  Lemma extract_root_pointer a ℓ e :
    a ↦root ℓ -∗
    rt_token rti sr e -∗
    ∃ ah ah32,
      ⌜repr_pointer e (PtrHeap MemGC ℓ) ah⌝ ∗
      ⌜N_i32_repr ah ah32⌝ ∗
      N.of_nat (sr_mem_gc sr)↦[wms][a] bits (VAL_int32 ah32) ∗
      (N.of_nat (sr_mem_gc sr)↦[wms][a] bits (VAL_int32 ah32) -∗
       a ↦root ℓ ∗
       rt_token rti sr e).
  Proof.
    iIntros "Hr Htok".
    unfold rt_token.
    iDestruct "Htok" as "(%rm & %lm & %hm & Haddrs & Hroots & Hlayouts & Hheaps & Htok)".
    iDestruct "Htok" as "(Hrti & %Hinj & Hownmm & Howngc & %Hrootok & Hrootm & %Hheapok & Hheapm)".
    iCombine "Hr" "Hroots" gives "%Hrm".
    pose proof (map_Forall_lookup_1 _ _ _ _ Hrootok Hrm) as [a' He].
    iPoseProof (big_sepM_lookup_acc _ _ _ _ Hrm with "Hrootm") as "[Ha Hrootm]".
    iDestruct "Ha" as "(%ah & %ah32 & %Hrep & %Hah32 & Hptr)".
    iExists ah, ah32.
    iFrame.
    repeat (iSplit; first by auto).
    iIntros "Hpt".
    iExists _, _, _.
    iFrame.
    repeat (iSplit; auto).
    iApply "Hrootm"; auto.
  Qed.

  Lemma wp_loadroot wt wl ret wt' wl' es_load :
    run_codegen (loadroot mr) wt wl = inr (ret, wt', wl', es_load) ->
    ret = () /\
    wt' = [] /\
    wl' = [] /\
    ∀ evs a n n32,
      N_i32_repr n n32 ->
      has_values evs [VAL_int32 n32] ->
      repr_root_pointer (RootHeap MemGC a) n ->
      ⊢ ∀ s E B R Φ e f ℓ,
          ↪[frame] f -∗
          ↪[RUN] -∗
          ⌜f.(f_inst).(inst_memory) !! memimm mr.(mr_gcmem) = Some sr.(sr_mem_gc)⌝ -∗
          a ↦root ℓ -∗
          rt_token rti sr e -∗
          ▷ (∀ ah ah32,
              ⌜repr_pointer e (PtrHeap MemGC ℓ) ah⌝ -∗
              ⌜N_i32_repr ah ah32⌝ -∗
              a ↦root ℓ -∗
              rt_token rti sr e -∗
              Φ f [VAL_int32 ah32]) -∗
          CWP evs ++ es_load @ s; E UNDER B; R {{ Φ }}.
  Proof.
    unfold loadroot.
    intros Hcg.
    inv_cg_emit Hcg; subst.
    repeat (split; first done).
    intros * Hn32 Hevs Han.
    iIntros (s E B R Φ e f ℓ) "Hf Hrun %Hmem Hroot Htok HΦ".
    iPoseProof (extract_root_pointer with "Hroot Htok")
      as "(%ah & %bs & %Hrep & %Hbs & Hroot & Hsave)".
    inversion Han; subst.
    cbn in Hn32.
    apply Is_true_true in Hevs.
    rewrite (has_values_to_consts_inv _ _ Hevs).
    replace a with ((a - 1) + 1)%N by lia.
    iApply (cwp_load with "[$Hroot] [Hsave HΦ] [$Hf] [$Hrun]"); eauto.
    - by f_equal.
    - replace ((a - 1) + 1)%N with a by lia.
      iIntros "!> Hpt".
      iPoseProof ("Hsave" with "Hpt") as "[Hroot Htok]".
      iApply ("HΦ" with "[//] [//] [$] [$]"); eauto.
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
    ∀ evs a n n32,
      N_i32_repr n n32 →
      has_values evs [VAL_int32 n32] ->
      repr_root_pointer (RootHeap MemGC a) n ->
      ⊢ ∀ s E B R Φ f ℓ e,
        ↪[frame] f -∗
        ↪[RUN] -∗
        ⌜inst_memory (f_inst f) !! memimm (mr_gcmem mr) = Some (sr_mem_gc sr)⌝ -∗
        ⌜↑ns_fun (N.of_nat (sr_func_registerroot sr)) ⊆ E⌝ -∗
        a ↦root ℓ -∗
        rt_token rti sr e -∗
        na_own logrel_nais E -∗
        instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
        (∀ e' ar ar32,
           ⌜repr_root_pointer (RootHeap MemGC ar) (tag_address MemGC ar)⌝ -∗
           ⌜N_i32_repr (tag_address MemGC ar) ar32⌝ -∗
           a ↦root ℓ -∗
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
    apply wp_loadroot in Hload.
    destruct Hload as (_ & -> & -> & Hload).
    clear_nils.
    apply wp_registerroot in Hreg.
    destruct Hreg as (-> & -> & -> & Hreg).
    repeat (split; first reflexivity).
    intros evs a n n32 Hnrep Hevs Hreproot.
    specialize (Hload evs a n n32 Hnrep Hevs Hreproot).
    iIntros (s E B R Φ f ℓ e) "Hf Hrun %Hmems %Hmask Hroot Htok Hinv Hreg HΦ".
    rewrite app_assoc.
    iApply (cwp_seq with "[-Hinv Hreg HΦ]").
    {
      iApply (Hload with "[$] [$] [//] [$] [$]").
      iIntros "!>" (ah ah32 Harep Harep32) "Hroot Htok".
      instantiate (1:= (fun f' v' =>
                         ⌜f' = f⌝ ∗
                         ∃ ah' ah32',
                             ⌜N_i32_repr ah' ah32'⌝ ∗
                             ⌜v' = [VAL_int32 ah32']⌝ ∗
                             ⌜repr_pointer e (PtrHeap MemGC ℓ) ah'⌝ ∗
                             a ↦root ℓ ∗ rt_token rti sr e
                         )%I).
      cbn.
      iSplit; auto.
      iExists _, _; by iFrame.
    }
    cbn; iIntros (f' vs) "(-> & %ah & %ah32 & %Hah & -> & %Hahrep & Hroot & Htok) Hf Hrun".
    iApply (Hreg with "[Hroot HΦ] [$Hf] [$Hrun] [] [$Hinv] [$Htok] [$Hreg]"); eauto.
    - apply Is_true_true, has_values_to_consts.
    - iIntros (ar ar32 e' Har) "Hroot' Htok' Hown %Harrep".
      iApply ("HΦ" with "[] [] [$] [$] [$] [$]"); eauto.
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

  Definition expect_heap_ptr (o : atom) : option (base_memory * location) :=
    match o with
    | PtrA (PtrHeap μ ℓ) => Some (μ, ℓ)
    | _ => None
    end.

  Definition mk_load1_post o v v' : iProp Σ :=
    (∃ e', rt_token rti sr e' ∗
           atom_interp o v ∗
           atom_interp o v')%I.

  Lemma atom_interp_dup o v :
    expect_heap_ptr o = None ->
    Persistent (atom_interp o v).
  Proof.
    destruct o; cbn; intros Heq; try apply bi.pure_persistent.
    repeat (apply bi.pure_persistent
            || (apply bi.exist_persistent; intros ?x)
            || apply bi.sep_persistent).
    destruct p; try congruence.
    destruct x1; cbn;
      repeat (apply bi.pure_persistent
              || (apply bi.exist_persistent; intros ?x)
              || apply bi.sep_persistent).
  Qed.

  Lemma wp_mem_load1_copy_mm_es
    fe lidx off ι o wt wl ret wt' wl' es ℓ ℓ32 B R
    (f: frame) memidx memidxN v Φ :
    run_codegen (memory.load1 mr fe MemMM Copy lidx off ι) wt wl = inr (ret, wt', wl', es) ->
    N_i32_repr ℓ ℓ32 ->
    N_nat_repr memidx memidxN ->
    inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some memidx ->
    fe_wlocal_offset fe + length wl < length (f_locs f) ->
    f_locs f !! localimm lidx = Some (VAL_int32 ℓ32) ->
    has_arep ι o ->
    let f' := mk_load1_frame fe f (length wl) v in
    ⊢ ∀ s E e, ↪[frame] f -∗
      ↪[RUN] -∗
      ⌜inst_memory (f_inst f) !! memimm (mr_gcmem mr) = Some (sr_mem_gc sr)⌝ -∗
      ⌜↑ns_fun (N.of_nat (sr_func_registerroot sr)) ⊆ E⌝ -∗
      atom_interp o v -∗
      memidxN ↦[wms][ℓ + byte_offset MemMM off]bits v -∗
      na_own logrel_nais E  -∗
      rt_token rti sr e -∗
      instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
      (instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
       memidxN↦[wms][ℓ + byte_offset MemMM off] bits v -∗
       na_own logrel_nais E  -∗
       ∀ e' v',
         rt_token rti sr e' -∗
         (⌜atom_copyable o⌝ -∗ atom_interp o v) -∗
         atom_interp o v' -∗
         Φ f' [v']) -∗
      CWP es @ s; E UNDER B; R {{ Φ }}.
  Proof.
    unfold load1.
    intros Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_get ?es_rest Hget Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_ret ?es_rest Hret Hcompile.
    cbn in Hret; inversion Hret; subst; clear Hret.
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
    intros.
    iIntros (s E e) "Hf Hrun %Hgcmem %Hmask Ho Hmem Hinv Htok Hinst HΦ".
    iPoseProof (arep_types_agree with "Ho") as "%Hag"; eauto.
    iApply (cwp_seq with "[Hf Hrun]").
    {
      iApply (cwp_local_get with "[] [$] [$]"); eauto.
      now instantiate (1:= λ f' v', ⌜f' = f /\ v' = [VAL_int32 ℓ32]⌝%I).
    }
    iIntros (f' vs') "[-> ->] Hf Hrun".
    rewrite app_assoc.
    iApply (cwp_seq with "[Hf Hrun Hmem]").
    {
      iApply (Hload_w with "[$] [$] [$]"); try done.
      iIntros "!> Hmem".
      instantiate (1:= λ f' v', (⌜f' = f⌝ ∗ ⌜v' = [v]⌝ ∗ _)%I).
      repeat iSplit; auto.
      iApply "Hmem".
    }
    iIntros (? ?) "(-> & -> & Hmem) Hf Hrun".
    rewrite app_assoc.
    set (vloc := localimm (W.Mk_localidx (fe_wlocal_offset fe + length wl))).
    set (f' := {| f_locs := <[vloc := v]> (f_locs f);
                  f_inst := f_inst f |}).
    iApply (cwp_seq with "[Hf Hrun]").
    {
      iApply (cwp_local_tee with "[] [$] [$]").
      - auto.
      - now instantiate (1:= λ f'' v'', ⌜f'' = f' /\ v'' = [v]⌝%I).
    }
    iIntros (? ?) "(-> & ->) Hf Hrun".
    destruct (atomic_rep_eq_dec ι PtrR).
    - subst ι.
      destruct o; try (exfalso; tauto).
      eapply wp_ite_gc_ptr_ptr with (evs:= to_consts [v]) (vs:=[v]) in Hcompile;
        [|apply Is_true_true, has_values_to_consts|auto].
      destruct Hcompile as (?wt & ?wt & ?wt & ?wl & ?wl & ?wl & ?es & ?es & ?es & Hcompile).
      destruct Hcompile as (Hcg1 & Hcg2 & Hcg3 & Hwt7 & Hwl7 & Hes_rest2).
      iApply (Hes_rest2 with "[$] [$] [] [$]").
      {
        iPureIntro; cbn.
        rewrite list_lookup_insert.
        by rewrite decide_True.
      }
      iIntros "!> Hf Hrun Hat".
      subst wt7 wl7.
      inv_cg_ret Hcg1.
      inv_cg_ret Hcg2.
      clear_nils.
      iDestruct "Hat" as "(%n & %n32 & %Hn & -> & %rp & %Hrp & Hrpp)".
      unfold root_pointer_interp.
      destruct rp, p as [k | [|] ℓ0]; try done.
      + iDestruct "Hrpp" as "->".
        iApply (cwp_val with "[$] [$]"); eauto using has_values_to_consts.
        iAssert (atom_interp (PtrA (PtrInt k)) (VAL_int32 n32)) as "Hat".
        {
          cbn.
          iExists n, n32; repeat (iSplit; first eauto).
          iExists _; iSplit; eauto.
        }
        iApply ("HΦ" with "[$] [$] [$] [$] [$Hat] [$Hat]").
        cbn; done.
      + iDestruct "Hrpp" as "(-> & Hrpp)".
        iApply (cwp_val with "[$] [$]"); eauto using has_values_to_consts.
        iApply ("HΦ" with "[$] [$] [$] [$Htok] [] [Hrpp]").
        * cbn.
          iIntros "[]".
        * cbn.
          unfold root_pointer_interp.
          iExists n, n32.
          repeat (iSplit; first done).
          iExists (RootHeap MemMM a).
          repeat (iSplit; first done).
          iFrame; done.
      + iDestruct "Hrpp" as "(-> & Hrpp)".
        (* need lemma about duproot. *)
        apply wp_duproot in Hcg3.
        destruct Hcg3 as (_ & -> & -> & Hduproot).
        clear Hes_rest2.
        iApply (Hduproot with "[$] [$] [] [] [$Hrpp] [$] [$] [$] [-]"); eauto.
        * apply Is_true_true.
          eapply has_values_to_consts.
        * iIntros (e' ar ar32) "%Har %Hrep Hroot Hroot' Htok Hown #Hfn".
          iApply ("HΦ" with "[$] [$] [$] [$] [Hroot] [Hroot']"); cbn.
          -- iIntros "_".
             iExists n, n32.
             repeat (iSplit; first done).
             iExists (RootHeap MemGC a); by iFrame.
          -- iExists (tag_address MemGC ar), ar32.
             repeat (iSplit; first done).
             iExists (RootHeap MemGC ar); by iFrame.
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
      iPoseProof "Ho" as "#Ho".
      iApply ("HΦ" with "[$] [$] [$] [$Htok] [Ho] [$]").
      by iIntros "_".
  Qed.

  Lemma wp_mem_load1_copy_mm_cg_state
    fe lidx off ι wt wl ret wt' wl' es :
    run_codegen (memory.load1 mr fe MemMM Copy lidx off ι) wt wl = inr (ret, wt', wl', es) ->
    ret = () ∧ wt' = [] ∧ wl' = [translate_arep ι].
  Proof.
    unfold load1.
    intros Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_get ?es_rest Hget Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_ret ?es_rest Hret Hcompile.
    cbn in Hret; inversion Hret; subst; clear Hret.
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
        fe_wlocal_offset fe + length wl + length wl' < length (f_locs f) ->
        ∀ os,
          Forall2 has_arep ιs os →
          ⊢ ∀ e vs,
            na_own logrel_nais E  -∗
            rt_token rti sr e -∗
            instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
            ([∗ list] o; v ∈ os; vs, atom_interp o v) -∗
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
      iIntros (e vs) "Hown Htok Hinst Hats Hpts".
      apply Forall2_nil_inv_l in H7.
      subst os.
      iPoseProof (big_sepL2_nil_inv_l with "Hats") as "%Hnil".
      subst vs.
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
      intros Hfe os Hareps.
      rewrite length_app in Hfe.
      specialize (Hinit ltac:(lia)).
      iIntros (e vs) "Hown Htok Hinst Hats Hpts".
      iIntros (Φ B R) "Hf Hrun HΦ".
      apply Forall2_rcons_inv_l in Hareps.
      destruct Hareps as (o & os' & Harep & Hareps & ->).
      rename os' into os.
      specialize (Hinit os Hareps).
      iPoseProof (big_sepL2_rcons_inv_l with "Hats") as "(%v & %vs' & -> & Hat & Hats)".
      rename vs' into vs.
      iPoseProof (big_sepL2_rcons_inv_r with "Hpts") as "(%off0 & %offs' & %Heq & Hpt & Hpts)".
      simpl in Heq.
      rewrite seq.foldl_rcons in Heq.
      destruct (seq.foldl _ _ _) as [off' offs] eqn:Heqf.
      eapply seq.rcons_inj in Heq; inversion Heq; subst offs' off0; clear Heq.
      iPoseProof (Hinit) as "Hinit".
      iPoseProof (big_sepL2_length with "Hats") as "%Hlen_os_vs".
      iSpecialize ("Hinit" with "Hown Htok Hinst Hats Hpts").
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
                            ⌜f' = mk_load_frame fe f wl vs⌝ ∗
                 ∃ e'', na_own logrel_nais E ∗ rt_token rti sr e'' ∗
                 instance_rt_func_interp (mr_func_registerroot mr) (sr_func_registerroot sr)
                   (spec_registerroot rti sr) (f_inst f) ∗
                   ([∗ list] off'0;v0 ∈ (off', offs).2;vs, memidxN↦[wms][ℓ + byte_offset MemMM off'0]bits v0) ∗
                    mk_load_post os vs vs')%I).
        cbn.
        iIntros (f' e' vs') "-> Hown Htok Hinst Hpts HΦ".
        by iFrame.
      + iIntros (f' vs') "(%Hinst & %e' & Hown & Htok & #Hinst & Hpts & Hpost) Hf Hrun".
        iApply cwp_val_app; first eauto using has_values_to_consts.
        cbn.
        iApply (wp_mem_load1_copy_mm_es with "[$] [$] [] [//] [$] [Hpt] [$Hown] [$Htok] [Hinst]"); first eauto;
          first apply Hrepℓ; first apply Hrepmemidx; (by rewrite Hinst load_frame_inst) || eauto.
        {
          rewrite length_app Hinst load_frame_length.
          lia.
        }
        { by rewrite Hinst mk_load_frame_stable_part. }
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
             now replace (length ιs) with (length vs)
               by (erewrite (Forall2_length _ _ _ Hareps); eauto).
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
  Qed.


  Lemma wp_mem_load_copy_mm fe lidx off ιs wt wl ret wt' wl' es :
    run_codegen (memory.load mr fe MemMM Copy lidx off ιs) wt wl = inr (ret, wt', wl', es) ->
    ret = () /\
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
      fe_wlocal_offset fe + length wl + length wl' < length (f_locs f) ->
      ∀ os,
        Forall2 has_arep ιs os →
        ⊢ ∀ e vs,
          na_own logrel_nais E  -∗
          rt_token rti sr e -∗
          instance_rt_func_interp mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) f.(f_inst) -∗
          ([∗ list] o; v ∈ os; vs, atom_interp o v) -∗
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

  Lemma compat_load_copy M F L wt wt' wtf wl wl' wlf es' κ κser μ τ τval π pr :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [RefT κ μ τ] [RefT κ μ τ; τval] in
    has_ref_flag F τval GCRefs ->
    resolves_path τ π None pr ->
    pr.(pr_target) = SerT κser τval ->
    Forall (has_mono_size F) (pr_prefix pr) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ILoad ψ π Copy)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmask ψ Hcopyability Hresolves Hser Hmonosize Htype Hcompile.
    unfold WT, WL; clear WT WL. (* If the WT := or WL := become necessary, comment the unfold/clear*)
    cbn in Hcompile.

    (* Mechanically get through some of the first few things in compile_load *)
    inv_cg_bind Hcompile off ?wt ?wt ?wl ?wl  es_fail ?es_rest Hoff Hcompile.
    inv_cg_bind Hcompile ρ ?wt ?wt ?wl ?wl es_off ?es_rest Hρ Hcompile.
    inv_cg_bind Hcompile ιs ?wt ?wt ?wl ?wl es_ρ ?es_rest Hιs Hcompile.
    inv_cg_try_option Hρ; rename Heq_some into Hρ.
    inv_cg_try_option Hιs; rename Heq_some into Hιs.
    inv_cg_try_option Hoff; rename Heq_some into Hoff.
    inv_cg_bind Hcompile a ?wt ?wt ?wl ?wl es_a ?es_rest Ha Hcompile.
    cbn in Ha; inversion Ha; subst; clear Ha.
    inv_cg_bind Hcompile res_emit ?wt ?wt ?wl ?wl  es_emit ?es_rest Hemit Hcompile.
    inv_cg_emit Hemit.
    inv_cg_bind Hcompile () ?wt ?wt ?wl ?wl es_empty ?es_rest Hempty Hcompile.
    cbn in Hempty; inversion Hempty; subst; clear Hempty.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl  es_case_ptr ?es_rest Hcompile Hignore.
    cbn in Hignore; inversion Hignore; subst; clear Hignore.

    (* Some clean up *)
    assert (Hu: u = ()). { by destruct u. }
    assert (Hp: p = ((),())). { by destruct p as [[] []]. }
    subst.
    rewrite ?app_nil_r ?app_nil_l -?app_assoc.
    rewrite ?app_nil_r ?app_nil_l -?app_assoc in Hcompile.
    simpl app.
    unfold have_instr_type_sem.
    iIntros (se fr os vs evs θ B R Hse Hevs) "@ @ @ @ @ @ @ @ @ @".
    iEval (rewrite values_interp_one_eq; cbn) in "Hos".
    iPoseProof (value_interp_ref_sz with "Hos") as "%Hlen_os".
    iEval (rewrite value_interp_eq) in "Hos".
    iDestruct "Hos" as (κ' Hκ') "[Harep Href]".
    destruct κ'; [|by iDestruct "Harep" as "[[] ?]"].
    iDestruct "Harep" as "%Harep".
    change instruction.W.T_i32 with T_i32 in *.
    change prelude.W.Mk_localidx with Mk_localidx in *.
    change instruction.W.BI_unreachable with BI_unreachable in *.
    change instruction.W.BI_tee_local with BI_tee_local in *.
    set (ptr_local := sum_list_with length F.(typing.fc_locals) + length wl) in *.

    cbn in Hκ'.
    iAssert (⌜ptr_local < length (f_locs fr)⌝%I) as "%Hlen".
    {
      (* need a lemma about frame_interp, I think? *)
      admit.
    }
    assert (Hκ: eval_rep se (AtomR PtrR) = Some l).
    {
      inversion Htype as [? ? ? Hmono Hctx]; subst.
      destruct Hmono as [Hmono _].
      rewrite Forall_singleton in Hmono.
      inversion Hmono as [? ? ? Hrep Hismono]; subst.
      inversion Hrep; subst.
      cbn.
      apply rep_ref_kind_ptr in H; subst.
      destruct H as [-> [χ' ->]].
      unfold eval_kind in Hκ'.
      apply bind_Some in Hκ'; destruct Hκ' as [l' [Heval Hret]].
      inversion Hret; subst; auto.
    }
    cbn in Hκ; inversion Hκ; subst l.
    destruct Harep as [[os' [Hos Hareps]] Hrefflag].
    inversion Hos; subst os'; clear Hos.
    iPoseProof (atoms_interp_length os vs with "Hvs") as "%Hlen_os_vs".
    pose proof (has_values_length _ _ Hevs) as Hlen_evs_vs.
    destruct evs as [|ev [|ev' evs]]; try (cbn in *; congruence).
    destruct vs as [|v [|v' vs]]; try (cbn in *; congruence).
    destruct os as [|o [|o' os]]; try (cbn in *; congruence).
    inversion Hareps as [| ? ? ? ? Harep _]; subst.
    destruct o; inversion Harep; clear Harep Hareps.
    cbn [app].
    iEval (cbn) in "Href".
    destruct μ as [|[|]]; first done.
    - unfold ref_mm_interp.
      iDestruct "Href" as (ℓ fs ws Hsv) "(Hℓl & Hℓh & Hws)".
      inversion Hsv; subst p; clear Hsv.
      rewrite value_interp_eq.


    change (?x :: ?y :: ?z) with ([x; y] ++ z).
    set (f' := {| f_locs := <[ptr_local:=v ]> (f_locs fr);
                  f_inst := f_inst fr |}).
    iApply (cwp_seq with "[Hfr Hrun Hws]").
    {
      change ([?ev; ?x]) with ([ev] ++ [x]).
      rewrite (has_values_to_consts_inv _ _ Hevs).
      iApply (cwp_local_tee with "[Hws] [$] [$]"); first eauto.
      instantiate (1:= λ f'' vs', (⌜f'' = f' /\ vs' = [v]⌝ ∗ value_interp0 rti sr (value_interp rti sr) se τ (SWords ws))%I).
      by iFrame.
    }
    iIntros (f vs) "([-> ->] & Hws) Hf Hrun".
    iEval (cbn) in "Hws".
    iDestruct "Hws" as "(%κ' & %Hsk & Hk & Ht)".

    eapply cwp_case_ptr in Hcompile.
    destruct Hcompile as (?wt & ?wt & ?wt & ?wl & ?wl & ?wl & ?es & ?es & ?es & Hcompile).
    destruct Hcompile as (Hunr & Hload1 & Hload2 & Hwt0 & Hwl0 & Hspec).
    rewrite atoms_interp_one_inv.
    iDestruct "Hvs" as "(%v' & %Hv' & Hat)".
    inversion Hv'; subst v'; clear Hv'.
    iApply cwp_val_app.
    { instantiate (1 := [v]). apply Is_true_true. apply/andP; split => //. by apply/eqP. }
    specialize (Hspec [] [] ltac:(eauto) ltac:(done)).
    clear_nils.
    iApply (Hspec with "[$] [$] [] [$Hat]").
    {
      iPureIntro; cbn.
      rewrite list_lookup_insert.
      by rewrite decide_True.
    }
    iIntros "!> Hf Hrun Hat".
    assert (Hκ'': ∃ ξ, κ' = SMEMTYPE (length ws) ξ).
    { admit. }
    destruct Hκ'' as [ξ ->].

      (* need lemma about memory.load *)
      apply wp_mem_load_copy_mm in Hload1.
      destruct Hload1 as (_ & -> & -> & Hload).
      unfold atom_interp; iEval (cbn) in "Hat".
      iDestruct "Hat" as "(%n & %n32 & %Hrep & -> & Hat')".
      iDestruct "Hinst" as "(%Hitys & (Hmm & Hgc & Hset & Hclr & Hreg & Hunreg) & Hinstfns & Htab & %Hmemm & %Hmemgc)".
      iApply (Hload with "[$] [$] [] [Hat'] [Ht Hk] [$] [$] [-]").
      + admit.
      + eauto.
      + eauto.
      + admit.
      + eauto.
      + simpl.
        by rewrite list_lookup_insert_eq.
      + cbn.
        rewrite length_app length_cons.
        lia.
      + cbn.
        rewrite length_insert.
        admit.
      + admit. (* need to go via kinding theorem *)
      + iApply "Hreg".
      + admit.
        (*
        erewrite (big_sepL2_cons _ (PtrA (PtrHeap MemMM ℓ)) (VAL_int32 n32) [] []).
        iFrame; by eauto.
        *)
      + admit.
      + iIntros (f'' e' vs') "-> Hown Htok #Hinst' Hpts Hpost".
        unfold fvs_combine.
        iFrame.
        iSplitR; [|iSplitL "Hframe"].
        * admit.
        * unfold mk_load_frame.
          cbn [seq.foldl imap].
          unfold frame_interp.
          iDestruct "Hframe" as "(%ηss & %L' & %WL' & %fr' & Hframe)".
          iDestruct "Hframe" as "(%Hprims & %Hres & Hats & Hlocs)".
          iExists _, L', _.
          iFrame.
          iPureIntro.
          intuition.
          -- cbn.
             unfold ptr_local.
             assert (length L' = length (concat (typing.fc_locals F))).
             { by eapply Forall2_length in Hprims. }
             admit.
          -- unfold result_type_interp in Hres.
             unfold result_type_interp.
             admit.
        * iExists (_ :: _). instantiate (2:=PtrA (PtrHeap MemMM ℓ)).
          admit.
    - unfold ref_gc_interp.
      iDestruct "Href" as (ℓ fs Hsv) "Hinv".
      inversion Hsv; subst.
      (* need lemma about memory.load *)
      admit.
  Admitted.

End load_copy.
