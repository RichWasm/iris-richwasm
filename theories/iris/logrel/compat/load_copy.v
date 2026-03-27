From Stdlib Require Import ZArith.

Require Import RecordUpdate.RecordUpdate.

From mathcomp Require Import ssrbool eqtype.

From stdpp Require Import base list.

From iris.proofmode Require Import base proofmode classes.

From RichWasm.named_props Require Import named_props custom_syntax.
From RichWasm.wasm Require Import operations.
From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import prelude codegen instruction module memory.
From RichWasm.iris Require Import autowp memory util wp_codegen numerics.
From RichWasm.iris.language Require Import cwp logpred.
From RichWasm.iris.logrel Require Import relations.
From RichWasm.iris.logrel.compat Require Import common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Fundamental.

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
        ⊢ ↪[frame] f -∗
          ↪[RUN] -∗
          memidxN ↦[wms][ℓ + byte_offset μ off]bits v -∗
          ▷ (memidxN↦[wms][ℓ + byte_offset μ off]bits v -∗ Φ f [v]) -∗
          CWP W.BI_const (VAL_int32 ℓ32) :: es UNDER B; R {{ Φ }}.
  Proof.
    intros Hcg.
    unfold load_w in Hcg.
    inv_cg_emit Hcg; subst es wt' wl' ret.
    split; [auto|].
    split; [auto|].
    split; [auto|].
    intros * Hℓ Hmemidx Hmem Hty.
    iIntros "Hf Hrun Hptr HΦ".
    iApply (cwp_load with "[$] [$] [$] [$]"); eauto.
  Qed.

  Lemma wp_mem_load1_copy_mm
    se fe lidx off ι wt wl ret wt' wl' es fs ws ℓ ℓ32 τ π B R
    (f: frame) memidx memidxN v Φ :
    run_codegen (memory.load1 mr fe MemMM Copy lidx off ι) wt wl = inr (ret, wt', wl', es) ->
    N_i32_repr ℓ ℓ32 ->
    N_nat_repr memidx memidxN ->
    inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some memidx ->
    f_locs f !! localimm lidx = Some (VAL_int32 ℓ32) ->
    types_agree (translate_arep ι) v ->
    ret = () /\
    ⊢ ↪[frame] f -∗
      ↪[RUN] -∗
      ℓ ↦layout fs -∗
      ℓ ↦heap ws -∗
      memidxN ↦[wms][ℓ + byte_offset MemMM off]bits v -∗
      ▷ value_interp rti sr se τ (SWords ws) -∗
      ⌜path_offset fe τ π = Some off⌝ -∗
      CWP es UNDER B; R {{ Φ }}.
  Proof.
    unfold load1.
    intros Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_get ?es_rest Hget Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_ret ?es_rest Hret Hcompile.
    cbn in Hret; inversion Hret; subst; clear Hret.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_load_w ?es_rest Hload_w Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_wlalloc ?es_rest Hwlalloc Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_save ?es_rest Hsave Hcompile.
    subst.
    apply wp_wlalloc in Hwlalloc.
    destruct Hwlalloc as (Hidx & -> & -> & ->).
    eapply wp_load_w in Hload_w.
    destruct Hload_w as (_ & -> & -> & Hload_w).
    inversion Hidx; subst n.
    inv_cg_emit Hget; subst.
    inv_cg_emit Hsave; subst.
    clear Hretval Hretval0.
    clear_nils.
    destruct ret.
    split; [reflexivity|].
    iIntros "Hf Hrun Hfs Hws Hmem Hval %Hpath".
    iApply (cwp_seq with "[Hf Hrun]").
    {
      iApply (cwp_local_get with "[] [$] [$]"); eauto.
      now instantiate (1:= λ f' v', ⌜f' = f /\ v' = [VAL_int32 ℓ32]⌝%I).
    }
    iIntros (f' vs') "[-> ->] Hf Hrun".
    rewrite app_assoc.
    iApply (cwp_seq with "[Hf Hrun Hmem]").
    {
      iApply (Hload_w with "[$] [$] [$]").
      1, 2, 3, 4: done.
      iIntros "!> Hmem".
      instantiate (1:= λ f' v', (⌜f' = f⌝ ∗ ⌜v' = [v]⌝ ∗ _)%I).
      cbn.
      iSplit; [done|].
      iSplit; [done|].
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
      - admit.
      - now instantiate (1:= λ f'' v'', ⌜f'' = f' /\ v'' = [v]⌝%I).
    }
    iIntros (? ?) "(-> & ->) Hf Hrun".
    unfold ite_gc_ptr in Hcompile.
    admit.
  Abort.

  Lemma mem_load_copy_mm_spec se fe lidx off ιs wt wl ret wt' wl' es fs ws ℓ τ π ev B R :
    run_codegen (memory.load mr fe MemMM Copy lidx off ιs) wt wl = inr (ret, wt', wl', es) ->
    ret = () /\
    ⊢ ℓ ↦layout fs -∗
      ℓ ↦heap ws -∗
      ▷ value_interp rti sr se τ (SWords ws) -∗
      ⌜path_offset fe τ π = Some off⌝ -∗
      CWP ev :: es UNDER B; R {{ fr'; vs', True }}.
  Proof.
  Abort.

  Lemma cwp_mod2_test_1 f (idx: nat) k E :
    ⊢ ⌜f.(f_locs) !! idx = Some (VAL_int32 (Wasm_int.Int32.repr k))⌝ →
      ⌜((Wasm_int.Int32.unsigned (Wasm_int.Int32.repr k)) `mod` 2 = 0)%Z⌝ →
      ↪[frame] f -∗
      ↪[RUN] -∗
      CWP [memory.W.BI_get_local idx;
           memory.W.BI_const (memory.W.VAL_int32 (Wasm_int.int_of_Z i32m 1));
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
        instantiate (1 := λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr k)]⌝%I).
        by iFrame.
      + iIntros (w f' [-> ->]) "Hf Hrun".
        iApply (cwp_binop with "[$] [$]").
        * cbn.
          reflexivity.
        * instantiate (1 := λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr 0)]⌝%I).
          cbn.
          iPureIntro.
          split; first done.
          do 2 f_equal.
          unfold Wasm_int.Int32.iand.
          unfold Wasm_int.Int32.and.
          f_equal.
          rewrite (Z.land_ones _ 1); lias.
    - iIntros (w f' [-> ->]) "Hf' Hrun".
      iApply (cwp_testop_i32 with "[$] [$]").
      + reflexivity.
      + cbn.
        iFrame.
        iSplit; eauto.
  Qed.

  Lemma cwp_mod2_test_1_2 f (idx: nat) k E :
    ⊢ ⌜f.(f_locs) !! idx = Some (VAL_int32 (Wasm_int.Int32.repr k))⌝ →
    ⌜((Wasm_int.Int32.unsigned (Wasm_int.Int32.repr k)) `mod` 2 = 1)%Z⌝ →
    ↪[frame] f -∗
    ↪[RUN] -∗
    CWP [memory.W.BI_get_local idx;
         memory.W.BI_const (memory.W.VAL_int32 (Wasm_int.int_of_Z i32m 1));
         memory.W.BI_binop memory.W.T_i32 (memory.W.Binop_i memory.W.BOI_and);
         memory.W.BI_testop memory.W.T_i32 memory.W.TO_eqz]
        @ E
        UNDER []; None
        {{ f'; vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr 0)]⌝ }}.
  Proof.
    iIntros (Hidx Hmod) "Hf Hrun".
    cwp_chomp 3%nat.
    iApply (cwp_seq with "[Hf Hrun]").
    - cwp_chomp 1%nat.
      iApply (cwp_seq with "[Hf Hrun]").
      + iApply (cwp_local_get with "[] [$] [$]"); first done.
        by instantiate (1 := λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr k)]⌝%I).
      + iIntros (w f' [-> ->]) "Hf Hrun".
        iApply (cwp_binop with "[$] [$]"); first done.
        instantiate (1 := λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr 1)]⌝%I).
        iPureIntro.
        split; first done.
        do 2 f_equal.
        cbn.
        unfold Wasm_int.Int32.iand.
        unfold Wasm_int.Int32.and.
        f_equal.
        rewrite (Z.land_ones _ 1); lias.
    - iIntros (w f' [-> ->]) "Hf' Hrun".
      iApply (cwp_testop_i32 with "[$] [$]").
      + reflexivity.
      + cbn.
        iFrame.
        iSplit; eauto.
  Qed.

  Lemma cwp_mod4_sub3_test f (idx: nat) k E :
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

    Lemma cwp_mod4_sub1_test f (idx: nat) k E :
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

  (* Note: The lemma assumes no input values to the case_ptr as no use case of it has needed it.
     It should, however, be possible to prove a version  that assumes values on the stack. *)
  Lemma cwp_case_ptr {A B} s E L R idx (c1 : codegen B) (c2: base_memory -> codegen A)
    wt wt' wl wl' ts1 ts2 evs vs es x y z v (f: frame) Φ :
    run_codegen (memory.case_ptr idx (Tf ts1 ts2) c1 c2) wt wl = inr (x, (y, z), wt', wl', es) ->
    has_values evs vs ->
    length ts1 = length vs ->
    exists wt1 wt2 wt3 wl1 wl2 wl3 es1 es2 es3,
      run_codegen c1 wt wl = inr (x, wt1, wl1, es1) /\
      run_codegen (c2 MemMM) (wt ++ wt1) (wl ++ wl1) = inr (y, wt2, wl2, es2) /\
      run_codegen (c2 MemGC) (wt ++ wt1 ++ wt2) (wl ++ wl1 ++ wl2) = inr (z, wt3, wl3, es3) /\
      wt' = wt1 ++ wt2 ++ wt3 /\
      wl' = wl1 ++ wl2 ++ wl3 /\
      ⊢ ∀ ptr,
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
    intros Hcg Hevs Hlen.
    assert (is_consts evs).
    { eapply Is_true_true. eapply has_values_is_consts. by apply Is_true_true. }
    assert (length evs = length ts1)
      by (erewrite has_values_length; eauto).
    unfold memory.case_ptr in Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es_isptr ?es_if_isptr Hcg_isptr Hcg_if_isptr.
    inv_cg_emit_all Hcg_isptr.
    subst.
    rewrite -> !app_nil_l, !app_nil_r in *.
    eapply (cwp_if_c s E) in Hcg_if_isptr; eauto.
    destruct Hcg_if_isptr as (?wt & ?wt & ?wl & ?wl & es_int & es_case_m & Hcg_int & Hcg_case_m & -> & -> & Hwp_if_isptr).
    inv_cg_bind Hcg_case_m [] ?wt ?wt ?wl ?wl ?es_mm_or_gc es_if_m Hcg_mm_or_gc Hcg_if_m.
    inv_cg_emit_all Hcg_mm_or_gc.
    subst.
    eapply (cwp_if_c s E) in Hcg_if_m; eauto.
    destruct Hcg_if_m as (?wt & ?wt & ?wl & ?wl & es_mm & es_gc & Hcg_mm & Hcg_gc & -> & -> & Hwp_if_m).
    rewrite <- !app_assoc, !app_nil_r, !app_nil_l in *.
    exists wt0, wt1, wt2, wl0, wl1, wl2.
    exists es_int, es_mm, es_gc.
    do 5 (split; first done).
    clear Hcg_int Hcg_mm Hcg_gc Hretval Hretval0.
    iIntros (ptr) "Hframe Hrun %Hlookup_f Hrep Hptr".
    destruct ptr.
    - iEval (cbn) in "Hrep".
      iDestruct "Hrep" as "(%vn & -> & %rp & %Hrp & Hrep)".
      destruct rp as [r|? ?].
      + iPoseProof "Hrep" as "->".
        inversion Hrp; subst.
        rewrite app_assoc.
        iApply (cwp_seq with "[Hframe Hrun]").
        {
          iApply cwp_val_app; eauto.
          iApply cwp_label_take.
          instantiate (2 := 0%nat).
          iApply cwp_return_none.
          iApply (cwp_wand with "[Hframe Hrun]").
          {
            iApply (cwp_mod2_test_1 with "[] [] [$] [$]"); eauto.
            iPureIntro.
            unfold Wasm_int.Int32.repr; simpl.
            rewrite Wasm_int.Int32.Z_mod_modulus_eq.
            unfold Wasm_int.Int32.modulus, Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
            unfold two_power_nat.
            simpl.
            apply mod32_mod2.
          }
          cbn.
          instantiate (1:= λ f' vs', ⌜f' = f /\ vs' = vs ++ [VAL_int32 (Wasm_int.Int32.repr 1)]⌝%I).
          iIntros (vs' f') "[-> ->]".
          unfold fvs_combine; simpl; auto.
        }
        iIntros (vs' f') "[-> ->] Hf Hrun".
        unfold to_consts; rewrite map_app -app_assoc.
        erewrite <- has_values_to_consts_inv by eauto.
        iApply (Hwp_if_isptr with "[$] [$]").
        iLeft.
        iSplit; [iPureIntro; done|].
        iIntros "!> Hf Hrun".
        iApply (cwp_label_wand with "[Hptr Hf Hrun]");
          [| iApply label_ctx_wand_nil].
        iApply ("Hptr" with "[$] [$]").
        iExists _; eauto.
      + done.
    - iDestruct "Hrep" as "(%l & -> & %rp & %Hrep & Hroot)".
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
          iApply (cwp_mod2_test_1_2 with "[] [] [$] [$]"); eauto.
          unfold Wasm_int.Int32.repr; simpl.
          rewrite Wasm_int.Int32.Z_mod_modulus_eq.
          unfold Wasm_int.Int32.modulus, Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
          unfold two_power_nat.
          simpl.
          rewrite Z_mod_even_mod_2; last by rewrite <- Z.even_spec.
          destruct μ; simpl.
          1,2: apply N.Div0.mod_divides in Hmod as [c ->].
          1,2: rewrite N2Z.inj_mul.
          1,2: simpl.
          1,2: rewrite Zmod_even.
          1,2: rewrite Z.even_sub.
          1,2: replace 4%Z with (2 * 2)%Z; last done.
          1,2: rewrite <- Z.mul_assoc.
          1,2: rewrite Z.even_even.
          1,2: done.
        }
        unfold fvs_combine.
        instantiate (1:= (λ f' vs', ⌜f' = f /\ vs' = vs ++ [VAL_int32 (Wasm_int.Int32.repr 0)]⌝ )%I).
        by iIntros (f' v') "[-> ->]".
      }
      iIntros (w f' [-> ->]) "Hf Hrun".
      unfold to_consts; rewrite map_app -app_assoc.
      erewrite <- has_values_to_consts_inv by eauto.
      iApply (Hwp_if_isptr with "[$] [$]").
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
            iApply (cwp_mod4_sub3_test with "[] [] [$] [$]"); eauto.
            iPureIntro.
            unfold Wasm_int.Int32.repr; simpl.
            rewrite Wasm_int.Int32.Z_mod_modulus_eq.
            unfold Wasm_int.Int32.modulus, Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
            unfold two_power_nat; simpl.
            replace (4294967296)%Z with (4 * 1073741824)%Z; last done.
            rewrite Z.mul_comm.
            rewrite Zaux.Zmod_mod_mult; try done.
            apply N2Z.inj_iff in Hmod.
            rewrite N2Z.inj_mod in Hmod.
            done.
          }
          iIntros (f' vs') "[-> ->]".
          instantiate (1 := λ f' vs', ⌜f' = f /\ vs' = vs ++ [VAL_int32 (Wasm_int.Int32.repr 1)]⌝%I).
          auto.
        }
        iIntros (w f' [-> ->]) "Hf Hrun".
        unfold to_consts; rewrite map_app -app_assoc.
        erewrite <- has_values_to_consts_inv by eauto.
        iApply (Hwp_if_m with "[$] [$]").
        iLeft.
        iSplit; eauto.
        iIntros  "!> Hf Hrun".
        iApply (cwp_label_wand with "[Hptr Hroot Hf Hrun]");
          [| iApply label_ctx_wand_nil].
        iApply ("Hptr" with "[$] [$]").
        iExists _; eauto.
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
            iApply (cwp_mod4_sub1_test with "[//] [] [$] [$]").
            iPureIntro.
            unfold Wasm_int.Int32.repr; simpl.
            rewrite Wasm_int.Int32.Z_mod_modulus_eq.
            unfold Wasm_int.Int32.modulus, Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
            unfold two_power_nat; simpl.
            replace (4294967296)%Z with (4 * 1073741824)%Z; last done.
            rewrite Z.mul_comm.
            rewrite Zaux.Zmod_mod_mult; try done.
            apply N2Z.inj_iff in Hmod.
            rewrite N2Z.inj_mod in Hmod.
            done.
          }
          iIntros (f' vs') "[-> ->]".
          instantiate (1 := λ f' vs', ⌜f' = f /\ vs' = vs ++ [VAL_int32 (Wasm_int.Int32.repr 0)]⌝%I).
          auto.
        }
        iIntros (w f' [-> ->]) "Hf Hrun".
        unfold to_consts; rewrite map_app -app_assoc.
        erewrite <- has_values_to_consts_inv by eauto.
        iApply (Hwp_if_m with "[$] [$]").
        iRight.
        iSplit; eauto.
        iIntros  "!> Hf Hrun".
        iApply (cwp_label_wand with "[Hptr Hroot Hf Hrun]");
          [| iApply label_ctx_wand_nil].
        iApply ("Hptr" with "[$] [$]").
        iExists _; eauto.
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
    iIntros (se fr os vs evs θ B R Hse Hevs) "Hinst Hlbl Hret Hats Hvals Hfr Hrt Hf Hrun".
    iEval (rewrite values_interp_one_eq; cbn) in "Hvals".
    iPoseProof (value_interp_ref_sz with "Hvals") as "%Hlen_os".
    iEval (rewrite value_interp_eq) in "Hvals".
    iDestruct "Hvals" as (κ' Hκ') "[Harep Href]".
    destruct κ'; [|by iDestruct "Harep" as "[[] ?]"].
    iDestruct "Harep" as "%Harep".
    change instruction.W.T_i32 with T_i32 in *.
    change prelude.W.Mk_localidx with Mk_localidx in *.
    change instruction.W.BI_unreachable with BI_unreachable in *.
    change instruction.W.BI_tee_local with BI_tee_local in *.
    set (ptr_local := sum_list_with length (typing.fc_locals F) + length wl) in *.

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
    iPoseProof (atoms_interp_length os vs with "Hats") as "%Hlen_os_vs".
    pose proof (has_values_length _ _ Hevs) as Hlen_evs_vs.
    destruct evs as [|ev [|ev' evs]]; try (cbn in *; congruence).
    destruct vs as [|v [|v' vs]]; try (cbn in *; congruence).
    destruct os as [|o [|o' os]]; try (cbn in *; congruence).
    inversion Hareps as [| ? ? ? ? Harep _]; subst.
    destruct o; inversion Harep; clear Harep Hareps.
    cbn [app].
    change (?x :: ?y :: ?z) with ([x; y] ++ z).
    set (f' := {| f_locs := <[ptr_local:=v ]> (f_locs fr);
                  f_inst := f_inst fr |}).
    iApply (cwp_seq with "[Hf Hrun]").
    {
      change ([?ev; ?x]) with ([ev] ++ [x]).
      rewrite (has_values_to_consts_inv _ _ Hevs).
      iApply (cwp_local_tee with "[ ] [$] [$]"); eauto.
      by instantiate (1:= λ f'' vs', ⌜f'' = f' /\ vs' = [v]⌝%I).
    }
    iIntros (f vs) "[-> ->] Hf Hrun".
    eapply cwp_case_ptr in Hcompile.
    2: do 2 instantiate (1 := []).
    2, 3: done.
    destruct Hcompile as (?wt & ?wt & ?wt & ?wl & ?wl & ?wl & ?es & ?es & ?es & Hcompile).
    destruct Hcompile as (Hunr & Hload1 & Hload2 & Hwt0 & Hwl0 & Hspec).
    rewrite atoms_interp_one_inv.
    iDestruct "Hats" as "(%v' & %Hv' & Hat)".
    inversion Hv'; subst v'; clear Hv'.
    iApply cwp_val_app.
    { instantiate (1 := [v]). apply Is_true_true. apply/andP; split => //. by apply/eqP. }
    iApply (Hspec with "[$] [$] [] [$Hat]").
    {
      iPureIntro; cbn.
      rewrite list_lookup_insert.
      by rewrite decide_True.
    }
    iIntros "!> Hf Hrun Hat".
    iEval (cbn) in "Href".
    destruct μ as [|[|]]; first done.
    - unfold ref_mm_interp.
      iDestruct "Href" as (ℓ fs ws Hsv) "(Hℓl & Hℓh & Hws)".
      inversion Hsv; subst.
      rewrite value_interp_eq.
      (* need lemma about memory.load *)
      assert (Hlenιs: length ιs = 1) by admit.
      destruct ιs as [| ι [| ? ? ]]; try discriminate Hlenιs.
      cbn in Hload1.
      admit.
    - unfold ref_gc_interp.
      iDestruct "Href" as (ℓ fs Hsv) "Hinv".
      inversion Hsv; subst.
      (* need lemma about memory.load *)
      admit.
  Admitted.

End Fundamental.
