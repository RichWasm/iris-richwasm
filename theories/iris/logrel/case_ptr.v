From mathcomp Require Import eqtype ssrbool.

Require Import RichWasm.util.
Require Import RichWasm.compiler.memory.
Require Import RichWasm.compiler.prelude.
Require Import RichWasm.compiler.codegen.
Require Import RichWasm.iris.numerics.
Require Import RichWasm.iris.memory.
Require Import RichWasm.iris.language.cwp.
Require Import RichWasm.iris.wp_codegen.
Require Import RichWasm.syntax.
From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import list.
From RichWasm.iris.language Require Import iris_wp_def lenient_wp logpred.
Require Import RichWasm.iris.logrel.
Require Import RichWasm.iris.logrel.logrel_properties.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section case_ptr.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

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


  Lemma tag_address_odd μ a :
    (a `mod` 4 = 0 ->
     a <> 0 ->
     tag_address μ a `mod` 2 = 1)%N.
  Proof.
    intros Hmod Hnz.
    apply N.Div0.mod_divides in Hmod as [k ->].
    destruct μ; cbn.
    - replace (4 * k - 3)%N with (1 + (2 * k - 2) * 2)%N by lia.
      rewrite N.Div0.mod_add.
      reflexivity.
    - replace (4 * k - 1)%N with (1 + (2 * k - 1) * 2)%N by lia.
      rewrite N.Div0.mod_add.
      reflexivity.
  Qed.

  (* Inductive ptr_shaped : pointer -> N -> Prop := *)
  (* | IntShaped : *)
  (*   ∀ n : N, ptr_shaped (PtrInt n) (2 * n)%N *)
  (* | PtrShaped : *)
  (*   ∀ ℓ μ a, *)
  (*   (a `mod` 4 = 0)%N -> *)
  (*   a <> 0%N -> *)
  (*   ptr_shaped (PtrHeap μ ℓ) (tag_address μ a). *)

  Lemma cwp_case_ptr {A B} (c1 : codegen B) (c2: base_memory -> codegen A) idx
    wt wt' wl wl' ts1 ts2 es x y z :
    run_codegen (memory.case_ptr idx (Tf ts1 ts2) c1 c2) wt wl = inr (x, (y, z), wt', wl', es) ->
    exists wt1 wt2 wt3 wl1 wl2 wl3 es1 es2 es3,
      run_codegen c1 wt wl = inr (x, wt1, wl1, es1) /\
      run_codegen (c2 MemMM) (wt ++ wt1) (wl ++ wl1) = inr (y, wt2, wl2, es2) /\
      run_codegen (c2 MemGC) (wt ++ wt1 ++ wt2) (wl ++ wl1 ++ wl2) = inr (z, wt3, wl3, es3) /\
      wt' = wt1 ++ wt2 ++ wt3 /\
      wl' = wl1 ++ wl2 ++ wl3 /\
      forall evs vs ptr n n32,
        has_values evs vs ->
        length ts1 = length vs ->
        ptr_shaped ptr n ->
        N_i32_repr n n32 ->
        ⊢ ∀ (s: stuckness) E L R Φ (f: frame),
          ↪[frame] f -∗
          ↪[RUN] -∗
          ⌜f.(f_locs) !! localimm idx = Some (VAL_int32 n32)⌝ -∗
          ▷ (↪[frame]f -∗
              ↪[RUN] -∗
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
    intros * Hval Hlen Hshape Hn32.
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
    iIntros (s E L R Φ f) "Hframe Hrun %Hlookup_f Hptr".
    inversion Hshape; subst; rewrite app_assoc.
    - iApply (cwp_seq with "[Hframe Hrun]").
      {
        iApply cwp_val_app; eauto.
        iApply cwp_label_take.
        instantiate (2 := 0%nat).
        iApply cwp_return_none.
        iApply (cwp_wand with "[Hframe Hrun]").
        {
          iApply (cwp_mod2_test_1 with "[$] [$]"); eauto.
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
    - iApply (cwp_seq with "[Hframe Hrun]").
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
        iApply (cwp_label_wand with "[Hptr Hf Hrun]");
          [| iApply label_ctx_wand_nil].
        iApply ("Hptr" with "[$] [$]").
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
        iApply (cwp_label_wand with "[Hptr Hf Hrun]");
          [| iApply label_ctx_wand_nil].
        iApply ("Hptr" with "[$] [$]").
  Qed.
End case_ptr.
