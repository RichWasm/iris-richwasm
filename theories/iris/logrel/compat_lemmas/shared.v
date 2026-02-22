From Stdlib Require Import ZArith.
From stdpp Require Import base list.

From iris.proofmode Require Import base tactics classes.
From Wasm Require Import operations.
From Wasm.iris.logrel Require Import iris_fundamental_composition.

From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import prelude codegen instruction module.
From RichWasm.iris Require Import autowp memory util wp_codegen.
From RichWasm.iris.language Require Import lenient_wp lwp_pure lwp_structural lwp_resources logpred wp_sem_ctx lwp_trap.
From RichWasm.iris.logrel Require Import relations fundamental_kinding.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Ltac clear_nils :=
  repeat rewrite <- ?app_assoc, -> ?app_nil_l, -> ?app_nil_r in *.

(* TODO relocate *)
Lemma get_base_l_append {i : nat} (lh : valid_holed i) e :
  get_base_l (vh_append lh e) = get_base_l lh.
Proof.
  induction lh;simpl;auto.
Qed.


Section Fundamental_Shared.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma Forall2_Forall2_cat_length {X Y} (P : X -> Y -> Prop) xss yss :
    Forall2 (Forall2 P) xss yss ->
    length (concat xss) = length (concat yss).
  Proof.
    intros H.
    do 2 rewrite length_concat.
    f_equal.
    rewrite list_eq_Forall2.
    rewrite Forall2_fmap.
    eapply Forall2_impl; eauto.
    eapply Forall2_length; eauto.
  Qed.
  
  Lemma concat_len_inj {X} (xss yss : list (list X)) :
    concat xss = concat yss ->
    Forall2 (λ xs ys, length xs = length ys) xss yss ->
    xss = yss.
  Proof.
    revert yss.
    induction xss as [|xs xss]; intros yss Hcat Hlens.
    - destruct yss; by inversion Hlens.
    - destruct yss as [|ys yss]; first by inversion Hlens.
      inversion Hlens; cbn.
      cbn in Hcat.
      apply app_inj_1 in Hcat; auto.
      destruct Hcat as [Hxsys Hcats].
      subst.
      f_equal.
      eauto.
  Qed.

  (* useful lemma for proving compat lemmas for instructions erased by the compiler. *)
  Lemma sem_type_erased M F L WT WL ψ τs1 τs2 :
    ψ = InstrT τs1 τs2 ->
    ⊢ (∀ se vs,
          values_interp rti sr se τs1 vs -∗
          values_interp rti sr se τs2 vs) -∗
      have_instruction_type_sem rti sr mr M F L WT WL [] ψ L.
  Proof.
    iIntros (->) "Hcast".
    iIntros (se inst lh Henv fr rvs vs θ) "Hinst Hctx Hrvs Hvs Hfr Hrt Hf Hrun".
    rewrite app_nil_r.
    unfold expr_interp.
    iApply lenient_wp_value; first done.
    iFrame.
    by iApply "Hcast".
  Qed.

  Lemma sem_type_erased_nop M F L WT WL ψ τs1 τs2 :
    ψ = InstrT τs1 τs2 ->
    ⊢ (∀ se vs,
          values_interp rti sr se τs1 vs -∗
          ▷values_interp rti sr se τs2 vs) -∗
      have_instruction_type_sem rti sr mr M F L WT WL [AI_basic BI_nop] ψ L.
  Proof.
    iIntros (->) "Hcast".
    iIntros (se inst lh fr rvs vs θ Henv) "Hinst Hctx Hrvs Hvs Hfr Hrt Hf Hrun".
    unfold expr_interp.
    iApply lenient_wp_val_app'.
    iApply (lenient_wp_nop with "[$] [$] [Hfr Hrvs Hvs Hrt Hcast] []").
    - iFrame.
      rewrite seq.cats0.
      iSpecialize ("Hcast" with "Hvs").
      iFrame.
    - done.
  Qed.

  Lemma values_interp_cons_inv se τ τs os :
    ⊢ values_interp rti sr se (τ :: τs) os -∗
      ∃ os1 os2,
        ⌜os = os1 ++ os2⌝ ∗
        value_interp rti sr se τ (SAtoms os1) ∗
        values_interp rti sr se τs os2.
  Proof.
    iIntros "(%vss & %Hconcat & Hval)".
    rewrite big_sepL2_cons_inv_l.
    iDestruct "Hval" as "(%vs1 & %vss2 & %Hvss & Hvs1 & Hvss2)".
    iExists vs1, (concat vss2).
    iSplit; first by rewrite Hconcat Hvss.
    iSplitL "Hvs1".
    - done.
    - iExists _.
      iSplit; done.
  Qed.

  Lemma values_interp_one_eq se τ os :
    values_interp rti sr se [τ] os ⊣⊢ value_interp rti sr se τ (SAtoms os).
  Proof.
    unfold values_interp.
    iSplit.
    - iIntros "(%vss & -> & H)".
      rewrite big_sepL2_cons_inv_l.
      iDestruct "H" as "(%vs & %lnil & -> & Hv & Hnils)".
      rewrite big_sepL2_nil_inv_l.
      iDestruct "Hnils" as "->".
      cbn.
      by rewrite app_nil_r.
    - iIntros "H".
      iExists [os].
      iSplit.
      + cbn. by rewrite app_nil_r.
      + iApply big_sepL2_cons.
        iFrame.
        by iApply big_sepL2_nil.
  Qed.


  Lemma eval_rep_emptyenv :
    forall ρ ιs,
      eval_rep EmptyEnv ρ = Some ιs ->
      ∀ (se: semantic_env (Σ:=Σ)),
        eval_rep se ρ = Some ιs.
  Proof.
    induction ρ using rep_ind; intros * Hev *; cbn in Hev; cbn.
    - inversion Hev.
    - rewrite -Hev.
      do 2 f_equal.
      rewrite bind_Some in Hev.
      destruct Hev as (pdist & Hmax & Hret).
      rewrite fmap_Some in Hmax.
      destruct Hmax as (ιss & Hevals & Hmax).
      assert (Hdefd: is_Some (mapM (eval_rep EmptyEnv) ρs)) by (eexists; eapply Hevals).
      apply mapM_is_Some_1 in Hdefd.
      apply Forall_mapM_ext.
      eapply Forall_impl.
      { eapply (List.Forall_and H Hdefd). }
      cbn.
      intros ρ [Hev [ιs' Hempty]].
      erewrite Hev; eauto.
    - rewrite -Hev.
      f_equal.
      apply fmap_Some in Hev.
      destruct Hev as (ιss & Hev & _).
      apply mk_is_Some in Hev.
      apply mapM_is_Some_1 in Hev.
      apply Forall_mapM_ext.
      eapply Forall_impl.
      { eapply (List.Forall_and H Hev). }
      cbn.
      intros ρ [Hev' [ιs' Hempty]].
      erewrite Hev'; eauto.
    - done.
  Qed.
  
  Lemma to_e_list_app es1 es2 :
    to_e_list (es1 ++ es2) = to_e_list es1 ++ to_e_list es2.
  Proof.
    by rewrite to_e_list_cat cat_app.
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

  Lemma wp_mod4_sub1_test f (idx: nat) k E :
    ⊢ ⌜f.(f_locs) !! idx = Some (VAL_int32 (Wasm_int.Int32.repr (k - 1)))⌝ →
      ⌜((Wasm_int.Int32.unsigned (Wasm_int.Int32.repr k)) `mod` 4 = 0)%Z⌝ →
      ↪[frame] f -∗
      ↪[RUN] -∗
      lenient_wp NotStuck E
        (to_e_list [memory.W.BI_get_local idx;
                    memory.W.BI_const (memory.W.VAL_int32 (Wasm_int.int_of_Z i32m 2));
                    memory.W.BI_binop memory.W.T_i32 (memory.W.Binop_i memory.W.BOI_and);
                    memory.W.BI_testop memory.W.T_i32 memory.W.TO_eqz])
        {| lp_fr_inv := λ _, True;
           lp_val := λ f' vs, ⌜f' = f⌝ ∗ ⌜vs = [VAL_int32 (Wasm_int.Int32.repr 0)]⌝;
           lp_trap := False;
           lp_br := λ _ _, False;
           lp_ret := λ _, False;
           lp_host := λ _ _ _ _, False; |}%I.
  Proof.
    iIntros (Hidx Hmod) "Hf Hrun".
    lwp_chomp 3.
    iApply (lenient_wp_seq with "[Hf Hrun]").
    - lwp_chomp 1.
      iApply (lenient_wp_seq with "[Hf Hrun]").
      + iApply lenient_wp_get_local; eauto.
        iFrame.
        by instantiate (1 := {| lp_fr_inv := λ _, True;
                               lp_val := λ f' vs, ⌜f' = f⌝ ∗ ⌜vs = [VAL_int32 (Wasm_int.Int32.repr (k - 1))]⌝;
                               lp_trap := False;
                               lp_br := λ _ _, False;
                               lp_ret := λ _, False;
                               lp_host := λ _ _ _ _, False; |}%I).
      + cbn; iIntros (?) "?"; done.
      + iIntros (w f') "Hpre".
        destruct w; iEval (cbn) in "Hpre";
          try solve [done | iDestruct "Hpre" as "[? ?]"; done].
        iDestruct "Hpre" as "(Hrun & -> & ->)".
        iIntros "Hf _".
        iApply lwp_binop.
        * cbn.
          reflexivity.
        * iFrame.
          (*Eval vm_compute in (let k := 8%Z in Z.land (k - 1) 2%Z).*)
          instantiate (1 := {| lp_fr_inv := λ _, True;
                              lp_val := λ f' vs, ⌜f' = f⌝ ∗ ⌜vs = [VAL_int32 (Wasm_int.Int32.repr 2)]⌝;
                               lp_trap := False;
                               lp_br := λ _ _, False;
                               lp_ret := λ _, False;
                               lp_host := λ _ _ _ _, False; |}%I).
          cbn.
          iSplit; [|done].
          iSplit; [done|].
          iPureIntro.
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
    - done.
    - iIntros (w f') "Hnotrap Hf' _".
      destruct w; iEval (cbn) in "Hnotrap"; try done;
        try (iDestruct "Hnotrap" as "[? ?]"; done).
      iDestruct "Hnotrap" as "(Hrun & -> & ->)".
      iApply lwp_testop_i32.
      + reflexivity.
      + cbn.
        iFrame.
        iSplit; eauto.
  Qed.

  Lemma wp_mod4_sub3_test f (idx: nat) k E :
    ⊢ ⌜f.(f_locs) !! idx = Some (VAL_int32 (Wasm_int.Int32.repr (k - 3)))⌝ →
      ⌜((Wasm_int.Int32.unsigned (Wasm_int.Int32.repr k)) `mod` 4 = 0)%Z⌝ →
      ↪[frame] f -∗
      ↪[RUN] -∗
      lenient_wp NotStuck E
        (to_e_list [memory.W.BI_get_local idx;
                    memory.W.BI_const (memory.W.VAL_int32 (Wasm_int.int_of_Z i32m 2));
                    memory.W.BI_binop memory.W.T_i32 (memory.W.Binop_i memory.W.BOI_and);
                    memory.W.BI_testop memory.W.T_i32 memory.W.TO_eqz])
        {| 
            lp_fr_inv := λ _, True;
            lp_val := λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr 1)]⌝;
            lp_trap := False;
            lp_br := λ _ _, False;
            lp_ret := λ _, False;
            lp_host := λ _ _ _ _, False; |}%I.
  Proof.
    iIntros (Hidx Hmod) "Hf Hrun".
    lwp_chomp 3.
    iApply (lenient_wp_seq with "[Hf Hrun]").
    - lwp_chomp 1.
      iApply (lenient_wp_seq with "[Hf Hrun]").
      + iApply lenient_wp_get_local; eauto.
        iFrame.
        by instantiate (1 := {| 
                               lp_fr_inv := λ _, True;
                               lp_val := λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr (k - 3))]⌝;
                               lp_trap := False;
                               lp_br := λ _ _, False;
                               lp_ret := λ _, False;
                               lp_host := λ _ _ _ _, False; |}%I).
      + cbn; iIntros (?) "?"; done.
      + iIntros (w f') "Hpre".
        destruct w; iEval (cbn) in "Hpre";
          try solve [done | iDestruct "Hpre" as "[? ?]"; done].
        iDestruct "Hpre" as "(Hrun & -> & ->)".
        iIntros "Hf _".
        iApply lwp_binop.
        * cbn.
          reflexivity.
        * iFrame.
          (*Eval vm_compute in (let k := 8%Z in Z.land (k - 1) 2%Z).*)
          instantiate (1 := {| lp_fr_inv := λ _, True;
                               lp_val := λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr 0)]⌝;
                               lp_trap := False;
                               lp_br := λ _ _, False;
                               lp_ret := λ _, False;
                               lp_host := λ _ _ _ _, False; |}%I).
          cbn.
          iSplit; [|done].
          iSplit; [done|].
          iPureIntro.
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
    - done.
    - iIntros (w f') "Hnotrap Hf' _".
      destruct w; iEval (cbn) in "Hnotrap"; try done;
        try (iDestruct "Hnotrap" as "[? ?]"; done).
      iDestruct "Hnotrap" as "(Hrun & -> & ->)".
      iApply lwp_testop_i32.
      + reflexivity.
      + cbn.
        iFrame.
        iSplit; eauto.
  Qed.

  Lemma wp_mod2_test_1 f (idx: nat) k E :
    ⊢ ⌜f.(f_locs) !! idx = Some (VAL_int32 (Wasm_int.Int32.repr k))⌝ →
      ⌜((Wasm_int.Int32.unsigned (Wasm_int.Int32.repr k)) `mod` 2 = 0)%Z⌝ →
      ↪[frame] f -∗
      ↪[RUN] -∗
      lenient_wp NotStuck E
        (to_e_list [memory.W.BI_get_local idx;
                    memory.W.BI_const (memory.W.VAL_int32 (Wasm_int.int_of_Z i32m 1));
                    memory.W.BI_binop memory.W.T_i32 (memory.W.Binop_i memory.W.BOI_and);
                    memory.W.BI_testop memory.W.T_i32 memory.W.TO_eqz])
        {| lp_fr_inv := λ _, True;
           lp_val := λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr 1)]⌝;
           lp_trap := False;
           lp_br := λ _ _, False;
           lp_ret := λ _, False;
           lp_host := λ _ _ _ _, False; |}%I.
  Proof.
    iIntros (Hidx Hmod) "Hf Hrun".
    lwp_chomp 3.
    iApply (lenient_wp_seq with "[Hf Hrun]").
    - lwp_chomp 1.
      iApply (lenient_wp_seq with "[Hf Hrun]").
      + iApply lenient_wp_get_local; eauto.
        iFrame.
        by instantiate (1 := {| lp_fr_inv := λ _, True;
                               lp_val := λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr k)]⌝;
                               lp_trap := False;
                               lp_br := λ _ _, False;
                               lp_ret := λ _, False;
                               lp_host := λ _ _ _ _, False; |}%I).
      + cbn; iIntros (?) "?"; done.
      + iIntros (w f') "Hpre".
        destruct w; iEval (cbn) in "Hpre";
          try solve [done | iDestruct "Hpre" as "[? ?]"; done].
        iDestruct "Hpre" as "(Hrun & -> & ->)".
        iIntros "Hf _".
        iApply lwp_binop.
        * cbn.
          reflexivity.
        * iFrame.
          instantiate (1 := {| lp_fr_inv := λ _, True;
                              lp_val := λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr 0)]⌝;
                              lp_trap := False;
                              lp_br := λ _ _, False;
                              lp_ret := λ _, False;
                              lp_host := λ _ _ _ _, False; |}%I).
          cbn.
          iSplit; [|done].
          iSplit; [done|].
          iPureIntro.
          do 2 f_equal.
          unfold Wasm_int.Int32.iand.
          unfold Wasm_int.Int32.and.
          f_equal.
          rewrite (Z.land_ones _ 1); lias.
    - done.
    - iIntros (w f') "Hnotrap Hf' _".
      destruct w; iEval (cbn) in "Hnotrap"; try done;
        try (iDestruct "Hnotrap" as "[? ?]"; done).
      iDestruct "Hnotrap" as "(Hrun & -> & ->)".
      iApply lwp_testop_i32.
      + reflexivity.
      + cbn.
        iFrame.
        iSplit; eauto.
  Qed.
  

  (* TODO: combine with above *)
  Lemma wp_mod2_test_1_2 f (idx: nat) k E :
    ⊢ ⌜f.(f_locs) !! idx = Some (VAL_int32 (Wasm_int.Int32.repr k))⌝ →
    ⌜((Wasm_int.Int32.unsigned (Wasm_int.Int32.repr k)) `mod` 2 = 1)%Z⌝ →
    ↪[frame] f -∗
    ↪[RUN] -∗
    lenient_wp NotStuck E
    (to_e_list [memory.W.BI_get_local idx;
    memory.W.BI_const (memory.W.VAL_int32 (Wasm_int.int_of_Z i32m 1));
    memory.W.BI_binop memory.W.T_i32 (memory.W.Binop_i memory.W.BOI_and);
    memory.W.BI_testop memory.W.T_i32 memory.W.TO_eqz])
    {| lp_fr_inv := λ _, True;
      lp_val := λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr 0)]⌝;
      lp_trap := False;
      lp_br := λ _ _, False;
      lp_ret := λ _, False;
      lp_host := λ _ _ _ _, False; |}%I.
  Proof.
    iIntros (Hidx Hmod) "Hf Hrun".
    lwp_chomp 3.
    iApply (lenient_wp_seq with "[Hf Hrun]").
    - lwp_chomp 1.
      iApply (lenient_wp_seq with "[Hf Hrun]").
      + iApply lenient_wp_get_local; eauto.
        iFrame.
        by instantiate (1 := {| lp_fr_inv := λ _, True;
          lp_val := λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr k)]⌝;
          lp_trap := False;
          lp_br := λ _ _, False;
          lp_ret := λ _, False;
          lp_host := λ _ _ _ _, False; |}%I).
      + cbn; iIntros (?) "?"; done.
      + iIntros (w f') "Hpre".
        destruct w; iEval (cbn) in "Hpre";
        try solve [done | iDestruct "Hpre" as "[? ?]"; done].
        iDestruct "Hpre" as "(Hrun & -> & ->)".
        iIntros "Hf _".
        iApply lwp_binop.
        * cbn.
          reflexivity.
        * iFrame.
          instantiate (1 := {| lp_fr_inv := λ _, True;
            lp_val := λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr 1)]⌝;
            lp_trap := False;
            lp_br := λ _ _, False;
            lp_ret := λ _, False;
            lp_host := λ _ _ _ _, False; |}%I).
            cbn.
            iSplit; [|done].
            iSplit; [done|].
            iPureIntro.
            do 2 f_equal.
            unfold Wasm_int.Int32.iand.
            unfold Wasm_int.Int32.and.
            f_equal.
            rewrite (Z.land_ones _ 1); lias.
    - done.
    - iIntros (w f') "Hnotrap Hf' _".
      destruct w; iEval (cbn) in "Hnotrap"; try done;
      try (iDestruct "Hnotrap" as "[? ?]"; done).
      iDestruct "Hnotrap" as "(Hrun & -> & ->)".
      iApply lwp_testop_i32.
      + reflexivity.
      + cbn.
        iFrame.
        iSplit; eauto.
  Qed.






  Lemma lwp_wasm_empty_ctx s E es Φ:
    lenient_wp s E es Φ ∗-∗ lenient_wp_ctx s E es Φ 0 (LH_base nil nil).
  Proof.
    by iApply wp_wasm_empty_ctx.
  Qed.

  Lemma lwp_label_push s E Φ i lh n es es0 vs es':
    is_true (const_list vs) ->
    ⊢ lenient_wp_ctx s E es Φ (S i) (push_base lh n es0 vs es') -∗
      lenient_wp_ctx s E [AI_label n es0 (vs ++ es ++ es')] Φ i lh.
  Proof.
    iIntros (Hconst) "Hwp".
    change @app with @seq.cat.
    by iApply wp_label_push.
  Qed.

  Lemma lwp_label_push_nil s E Φ i lh n es es0:
    ⊢ lenient_wp_ctx s E es Φ (S i) (push_base lh n es0 [] []) -∗
      lenient_wp_ctx s E [AI_label n es0 es] Φ i lh.
  Proof.
    by iApply wp_label_push_nil.
  Qed.

  Lemma lwp_label_pull s E Φ i lh n es es0 vs es':
    is_true (const_list vs) ->
    ⊢ lenient_wp_ctx s E [AI_label n es0 (vs ++ es ++ es')] Φ i lh -∗
      lenient_wp_ctx s E es Φ (S i) (push_base lh n es0 vs es').
  Proof.
    iIntros (Hconst) "Hwp".
    change @app with @seq.cat.
    by iApply wp_label_pull.
  Qed.

  Lemma lwp_label_pull_nil s E Φ i lh n es es0:
    ⊢ lenient_wp_ctx s E [AI_label n es0 es] Φ i lh -∗
      lenient_wp_ctx s E es Φ (S i) (push_base lh n es0 [] []).
  Proof.
    by iApply wp_label_pull_nil.
  Qed.


  Definition lp_bind s E i lh (Φ: logpred) : logpred :=
    let wp_val f := (λ e, 
                       ↪[frame] f -∗
                       ↪[RUN] -∗
                       Φ.(lp_fr_inv) f -∗
                       lenient_wp_ctx s E e Φ i lh)%I in
    let wp := λ e, (∀ f: datatypes.frame, 
                       ↪[frame] f -∗
                       ↪[RUN] -∗
                       Φ.(lp_fr_inv) f -∗
                       lenient_wp_ctx s E e Φ i lh)%I in
    let wp_trap := λ e, (∀ f: datatypes.frame, 
                       ↪[frame] f -∗
                       ↪[BAIL] -∗
                       Φ.(lp_fr_inv) f -∗
                       lenient_wp_ctx s E e Φ i lh)%I in
    {|
      lp_fr_inv := Φ.(lp_fr_inv);
      lp_val := λ f v, wp_val f (v_to_e_list v);
      lp_trap := wp_trap [AI_trap];
      lp_br := λ n vh, wp (vfill vh [AI_basic (BI_br n)]);
      lp_ret := λ sh, wp (sfill sh [AI_basic BI_return]);
      lp_host := λ tf h vcs sh, wp (llfill sh [AI_call_host tf h vcs])
    |}.

  Lemma lwp_ctx_bind s E Φ i lh es:
    base_is_empty lh ->
    ⊢ lenient_wp s E es (lp_bind s E i lh Φ) -∗
      lenient_wp_ctx s E es Φ i lh.
  Proof.
    iIntros (Hbase) "Hwp".
    iApply wp_ctx_bind; first auto.
    iApply (wp_wand with "Hwp").
    iIntros (w) "(%f & Hf & Hinv & Hwp)".
    destruct w.
    - cbn.
      unfold lenient_wp_ctx.
      iDestruct "Hwp" as "(Hrun & Hwp)".
      iApply ("Hwp" with "[Hf] [Hrun] [Hinv]").
      all:iFrame.
    - iDestruct "Hwp" as "(Hbail & Hwp)".
      iApply ("Hwp" with "[Hf] [Hbail] [Hinv]").
      all:iFrame.
    - iDestruct "Hwp" as "(Hrun & Hwp)".
      iApply ("Hwp" with "[Hf] [Hrun] [Hinv]").
      all:iFrame.
    - iDestruct "Hwp" as "(Hrun & Hwp)".
      iApply ("Hwp" with "[Hf] [Hrun] [Hinv]").
      all:iFrame.
    - iDestruct "Hwp" as "(Hrun & Hwp)".
      iApply ("Hwp" with "[Hf] [Hrun] [Hinv]").
      all:iFrame.
  Qed.



  Open Scope Z_scope.

  Lemma Z_even_mod_even :
    forall n k : Z,
    Z.even k = true ->
    Z.even (n mod k) = Z.even n.
  Proof.
    intros n k Hk.
    apply Bool.eq_true_iff_eq.

    assert (Hk2 : k mod 2 = 0).
    { rewrite Zmod_even. by rewrite Hk. }
    destruct (Z.eq_dec k 0) as [Hk0 | Hk0].
    { subst. by rewrite Zmod_0_r. }

    rewrite (Z.mod_eq n k); last done.

    replace (n - k * (n / k)) with (n + (k * -(n / k))); last lia.
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
    (n mod k) mod 2 = n mod 2.
  Proof.
    intros n k Hk.
    rewrite Zmod_even.
    rewrite Z_even_mod_even; last by rewrite Z.even_spec.
    symmetry.
    apply Zmod_even.
  Qed.


  Lemma mod32_mod2 (n: Z) :
    (((2 * n) mod 4294967296) mod 2) = 0.
  Proof.
    rewrite Z_mod_even_mod_2; last by rewrite <- Z.even_spec.
    rewrite Zmod_even.
    by rewrite Z.even_even.
  Qed.


  (**
     Note: The lemma assumes no input values to the case_ptr as no use case of it has needed it.
     It should, however, be possible to prove a version  that assumes values on the stack.
  *)
  Lemma wp_case_ptr {A B} s E idx t2s (c1 : codegen B) (c2: base_memory -> codegen A) wt wt' wl wl' es x y z v (f: frame) Φ :
    run_codegen (memory.case_ptr idx (Tf [] t2s) c1 c2) wt wl = inr (x, (y, z), wt', wl', es) ->
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
            match ptr with
            | PtrInt z => lenient_wp s E [AI_basic (BI_block (Tf [] t2s) es1)] Φ
            | PtrHeap MemMM l => lenient_wp s E [AI_basic (BI_block (Tf [] t2s) es2)] (lp_bind s E 1 (LH_rec [] (length t2s) [] (LH_base [] []) []) Φ)
            | PtrHeap MemGC l => lenient_wp s E [AI_basic (BI_block (Tf [] t2s) es3)] (lp_bind s E 1 (LH_rec [] (length t2s) [] (LH_base [] []) []) Φ)
            end) -∗
        atom_interp (PtrA ptr) v ∗
        lenient_wp s E (to_e_list es) Φ.
  Proof.
    intros Hcg.
    unfold memory.case_ptr in Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es_isptr ?es_if_isptr Hcg_isptr Hcg_if_isptr. inv_cg_emit_all Hcg_isptr.
    subst.

    rewrite -> !app_nil_l, !app_nil_r in *.
    eapply (lwp_if_c s E) in Hcg_if_isptr.
    destruct Hcg_if_isptr as (?wt & ?wt & ?wl & ?wl & es_int & es_case_m & Hcg_int & Hcg_case_m & -> & -> & Hwp_if_isptr).
    inv_cg_bind Hcg_case_m [] ?wt ?wt ?wl ?wl ?es_mm_or_gc es_if_m Hcg_mm_or_gc Hcg_if_m.
    inv_cg_emit_all Hcg_mm_or_gc.
    subst.

    eapply (lwp_if_c s E) in Hcg_if_m.
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
        iSplitR.
        * cbn; eauto.
        * rewrite to_e_list_app.
          iApply (lenient_wp_seq with "[Hframe Hrun]").
          {
            iApply (wp_mod2_test_1 with "[] [] [$] [$]"); eauto.
            iPureIntro.
            unfold Wasm_int.Int32.repr; simpl.
            rewrite Wasm_int.Int32.Z_mod_modulus_eq.
            unfold Wasm_int.Int32.modulus, Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
            unfold two_power_nat.
            simpl.
            apply mod32_mod2.
          }
          { cbn. iIntros (?) "?". done. }
          iIntros (w f') "Hnotrap Hf _".
          destruct w; try solve [done | iDestruct "Hnotrap" as "[? ?]"; done].
          iDestruct "Hnotrap" as "(Hrun & -> & ->)".
          iApply (Hwp_if_isptr with "[$] [$]").
          iLeft.
          iSplit; done.
      + done.
    - iDestruct "Hrep" as "(%l & -> & %rp & %Hrep & Hroot)".
      iPoseProof (root_pointer_heap_shp_inv with "Hroot") as "(%a & ->)".
      iSplitL "Hroot"; first (iExists _; by iFrame).
      inversion Hrep as [|? ? Hmod]; subst.
      rewrite to_e_list_app.
      iApply (lenient_wp_seq with "[Hframe Hrun]").
      {
        iApply (wp_mod2_test_1_2 with "[] [] [$] [$]"); eauto.
        iPureIntro.
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
        1,2: replace 4 with (2 * 2); last done.
        1,2: rewrite <- Z.mul_assoc.
        1,2: rewrite Z.even_even.
        1,2: done.
      }
      { cbn. iIntros (?) "?". done. }
      iIntros (w f') "Hnotrap Hf _".
      destruct w; try solve [done | iDestruct "Hnotrap" as "[? ?]"; done].
      iDestruct "Hnotrap" as "(Hrun & -> & ->)".
      iApply (Hwp_if_isptr with "[$] [$]").
      iRight.
      iSplit; first done.
      iIntros "!> Hframe Hrun".
      destruct μ.
      + simpl tag_address in Hlookup_f.
        cbn.
        lwp_chomp 0%nat.
        iApply (lenient_wp_block with "[$] [$]"); auto.
        iIntros "!> Hf Hrun".
        rewrite app_nil_l.

        iApply lwp_wasm_empty_ctx.
        iApply lwp_label_push_nil.
        iApply lwp_ctx_bind; first done.
        lwp_chomp 4%nat.
        rewrite take_0 drop_0.
        iApply (lenient_wp_seq with "[Hf Hrun]").
        * iApply (wp_mod4_sub3_test with "[//] [] [$] [$]").
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
        * iIntros (?) "?". done.
        * iIntros (w f') "Ht Hf' Hfrinv".
           destruct w; cbn; try done; try (iDestruct "Ht" as "(? & ?)"; done).
           iDestruct "Ht" as "(Hrun & -> & ->)".
           cbn.
           iApply (Hwp_if_m with "[$] [$]").
           iLeft.
           iSplit; auto.
      + simpl tag_address in Hlookup_f.
        cbn.
        lwp_chomp 0%nat.
        iApply (lenient_wp_block with "[$] [$]"); auto.
        iIntros "!> Hf Hrun".
        rewrite app_nil_l.
        iApply lwp_wasm_empty_ctx.
        iApply lwp_label_push_nil.
        iApply lwp_ctx_bind; first done.
        lwp_chomp 4%nat.
        rewrite take_0 drop_0.
        iApply (lenient_wp_seq with "[Hf Hrun]").
        * iApply (wp_mod4_sub1_test with "[//] [] [$] [$]").
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
        * iIntros (?) "?". done.
        * iIntros (w f') "Ht Hf' Hfrinv".
           destruct w; cbn; try done; try (iDestruct "Ht" as "(? & ?)"; done).
           iDestruct "Ht" as "(Hrun & -> & ->)".
           cbn.
           iApply (Hwp_if_m with "[$] [$]").
           iRight.
           iSplit; auto.
  Qed.

  (* This version of the lemma is proved in terms of the existing lemma
     wp_case_ptr. This makes the proof artificially short. *)
  Lemma wp_case_ptr_wp_sem_ctx_derived {A B} s E LS RS idx t2s (c1 : codegen B) (c2: base_memory -> codegen A) wt wt' wl wl' es x y z v (f: frame) Φ :
    run_codegen (memory.case_ptr idx (Tf [] t2s) c1 c2) wt wl = inr (x, (y, z), wt', wl', es) ->
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
            match ptr with
            | PtrInt z => wp_sem_ctx s E es1 ([], None) Φ
            | PtrHeap MemMM l => wp_sem_ctx s E es2 ([], None) Φ
            | PtrHeap MemGC l => wp_sem_ctx s E es3 ([], None) Φ
            end) -∗
        atom_interp (PtrA ptr) v ∗
        wp_sem_ctx s E es (LS, RS) Φ.
  Proof.
    intros Hcomp.
    eapply (wp_case_ptr s E) in Hcomp.
    destruct Hcomp as (wt1 & wt2 & wt3 & Hcomp).
    exists wt1, wt2, wt3.
    destruct Hcomp as (wl1 & wl2 & wl3 & Hcomp).
    exists wl1, wl2, wl3.
    destruct Hcomp as (es1 & es2 & es3 & Hcomp).
    exists es1, es2, es3.
    destruct Hcomp as (Hc1 & Hc2 & Hc3 & Hwt' & Hwl' & Hspec).
    repeat (split; first assumption).
    iIntros "%ptr Hf Hrun %Hlocs Hv Hwp".
    iApply (Hspec with "[$] [$] [//] [$]").
    iRevert "Hwp".
    iIntros "Hwp !> Hf Hrun".
    destruct ptr; [|destruct μ].
    - iApply (wp_sem_ctx_block_peel with "[Hwp] [$] [$]").
      iIntros "Hf Hrun".
      iApply wp_sem_ctx_clear_labels.
      iApply ("Hwp" with "[$] [$]").
    - iApply (lwp_wand with "[Hwp Hf Hrun]").
      {
        iApply (wp_sem_ctx_block_peel with "[Hwp] [$] [$]").
        iIntros "Hf Hrun".
        iApply wp_sem_ctx_clear_labels.
        iApply ("Hwp" with "[$] [$]").
      }
      instantiate (1 := None).
      instantiate (1 := []).
      iIntros "%lv H".
      destruct lv.
      + unfold wp_sem_ctx_post, lp_bind, denote_logpred; cbn.
        iDestruct "H" as (f') "(Hf & _ & Hrun & HΦ)".
        iExists f'; iFrame; iIntros "Hf Hrun _".
        iApply (wp_val_return with "[$] [$]").
        { apply v_to_e_is_const_list. }
        iIntros "Hf Hrun".
        iApply wp_value.
        {
          rewrite app_nil_l app_nil_r.
          by rewrite of_val_imm.
        }
        cbn.
        iFrame.
      + unfold wp_sem_ctx_post, lp_bind, denote_logpred; cbn.
        iDestruct "H" as (f') "(Hf & _ & Hrun & HΦ)".
        iFrame.
        iIntros (f'') "Hf Hbail _".
        replace [AI_trap] with ([] ++ [AI_trap] ++ []) by auto.
        unfold lenient_wp_ctx.
        iApply (wp_wand_ctx with "[Hf]").
        { iApply wp_trap_ctx; done. }
        iIntros (w) "(-> & Hf)".
        iExists f''; iFrame; done.
      + unfold wp_sem_ctx_post, lp_bind, denote_logpred; cbn.
        iDestruct "H" as (f') "(Hf & _ & Hrun & HΦ)".
        by rewrite lookup_nil.
      + unfold wp_sem_ctx_post, lp_bind, denote_logpred; cbn.
        by iDestruct "H" as (f') "(Hf & _ & Hrun & HΦ)".
      + unfold wp_sem_ctx_post, lp_bind, denote_logpred; cbn.
        by iDestruct "H" as (f') "(Hf & _ & Hrun & HΦ)".
    - iApply (lwp_wand with "[Hwp Hf Hrun]").
      {
        iApply (wp_sem_ctx_block_peel with "[Hwp] [$] [$]").
        iIntros "Hf Hrun".
        iApply wp_sem_ctx_clear_labels.
        iApply ("Hwp" with "[$] [$]").
      }
      instantiate (1 := None).
      instantiate (1 := []).
      iIntros "%lv H".
      destruct lv.
      + unfold wp_sem_ctx_post, lp_bind, denote_logpred; cbn.
        iDestruct "H" as (f') "(Hf & _ & Hrun & HΦ)".
        iExists f'; iFrame; iIntros "Hf Hrun _".
        iApply (wp_val_return with "[$] [$]").
        { apply v_to_e_is_const_list. }
        iIntros "Hf Hrun".
        iApply wp_value.
        {
          rewrite app_nil_l app_nil_r.
          by rewrite of_val_imm.
        }
        cbn.
        iFrame.
      + unfold wp_sem_ctx_post, lp_bind, denote_logpred; cbn.
        iDestruct "H" as (f') "(Hf & _ & Hrun & HΦ)".
        iFrame.
        iIntros (f'') "Hf Hbail _".
        replace [AI_trap] with ([] ++ [AI_trap] ++ []) by auto.
        unfold lenient_wp_ctx.
        iApply (wp_wand_ctx with "[Hf]").
        { iApply wp_trap_ctx; done. }
        iIntros (w) "(-> & Hf)".
        iExists f''; iFrame; done.
      + unfold wp_sem_ctx_post, lp_bind, denote_logpred; cbn.
        iDestruct "H" as (f') "(Hf & _ & Hrun & HΦ)".
        by rewrite lookup_nil.
      + unfold wp_sem_ctx_post, lp_bind, denote_logpred; cbn.
        by iDestruct "H" as (f') "(Hf & _ & Hrun & HΦ)".
      + unfold wp_sem_ctx_post, lp_bind, denote_logpred; cbn.
        by iDestruct "H" as (f') "(Hf & _ & Hrun & HΦ)".
  Qed.

  Lemma simple_get_base_l_append s es :
    wp_sem_ctx.simple_get_base_l (sh_append s (to_e_list es)) =
      wp_sem_ctx.simple_get_base_l s.
  Proof.
    induction s; first done.
    cbn. by rewrite <- IHs.
  Qed.

  Lemma append_lh_depth {i : nat} (lh : valid_holed i) e :
    lh_depth (lh_of_vh lh) = lh_depth (lh_of_vh (vh_append lh e)).
  Proof.
    induction lh; simpl; auto.
  Qed.

  Lemma wp_sem_ctx_seq s E es1 es2 LS RS Φ1 Φ :
    wp_sem_ctx NotStuck E es1 (LS, RS) Φ1 -∗
    (∀ vs (f: datatypes.frame),
       Φ1 f vs -∗
       ↪[frame]f -∗
       ↪[RUN] -∗
       wp_sem_ctx s E (map BI_const vs ++ es2) (LS, RS) Φ) -∗
    wp_sem_ctx s E (es1 ++ es2) (LS, RS) Φ.
  Proof.
    iIntros "Hes1 Hes2".
    unfold wp_sem_ctx.
    rewrite to_e_list_app.
    iApply (lenient_wp_seq with "[$Hes1] [] [Hes2]").
    - done.
    - cbn.
      iIntros (w f) "Hw Hf _".
      destruct w.
      + cbn.
        unfold v_to_e_list, to_e_list.
        change @seq.map with @map.
        setoid_rewrite map_app.
        setoid_rewrite map_comp.
        iDestruct "Hw" as "[Hrun HΦ1]".
        iApply ("Hes2" with "[$] [$] [$]").
      + simpl of_val.
        change [AI_trap] with ([] ++ [AI_trap]).
        rewrite <- app_assoc.
        iApply (lwp_trap with "[] [] [$Hf]"); auto.
      + rewrite of_val_br_app_r.
        iApply lenient_wp_value; first done.
        iDestruct "Hw" as "[Hrun Hbr]".
        iExists f; iFrame.
        cbn.
        rewrite get_base_l_append.
        by rewrite <- append_lh_depth.
      + rewrite of_val_ret_app_r.
        iApply lenient_wp_value; first done.
        iDestruct "Hw" as "[Hrun Hret]".
        iExists f; iFrame.
        cbn.
        destruct RS; [|done].
        destruct r as [Pre Post].
        by rewrite simple_get_base_l_append.
      + cbn.
        iDestruct "Hw" as "[? ?]".
        done.
  Qed.

  Lemma wp_sem_ctx_lwp s E LS es es' Φ Φ':
    to_e_list es = es' ->
    lenient_wp s E es' Φ' -∗
    lp_wand' Φ' (wp_sem_ctx_post LS Φ) -∗
    wp_sem_ctx s E es LS Φ.
  Proof.
    unfold wp_sem_ctx.
    iIntros (->) "Hes' Hwand".
    iApply (lwp_wand with "[$] [$]").
  Qed.

  Ltac wp_sem_ctx_chomp n :=
    match goal with
    | |- context [ environments.envs_entails _ (wp_sem_ctx _ _ ?es _ _) ] =>
        iEval (rewrite -(take_drop n es); simpl firstn; simpl skipn)
    end.

  Lemma wp_sem_ctx_mod4_sub1_test f (idx: nat) k E :
    ⊢ ⌜f.(f_locs) !! idx = Some (VAL_int32 (Wasm_int.Int32.repr (k - 1)))⌝ →
      ⌜((Wasm_int.Int32.unsigned (Wasm_int.Int32.repr k)) `mod` 4 = 0)%Z⌝ →
      ↪[frame] f -∗
      ↪[RUN] -∗
      wp_sem_ctx NotStuck E
        [memory.W.BI_get_local idx;
         memory.W.BI_const (memory.W.VAL_int32 (Wasm_int.int_of_Z i32m 2));
         memory.W.BI_binop memory.W.T_i32 (memory.W.Binop_i memory.W.BOI_and);
         memory.W.BI_testop memory.W.T_i32 memory.W.TO_eqz]
        ([], None)
        (λ f' vs, ⌜f' = f⌝ ∗ ⌜vs = [VAL_int32 (Wasm_int.Int32.repr 0)]⌝%I).
  Proof.
    iIntros (Hidx Hmod) "Hf Hrun".
    wp_sem_ctx_chomp 3%nat.
    iApply (wp_sem_ctx_seq with "[Hf Hrun]").
    - wp_sem_ctx_chomp 1%nat.
      iApply (wp_sem_ctx_seq with "[Hf Hrun]").
      + iApply lenient_wp_get_local; eauto.
        iFrame.
        by instantiate (1 := (λ f' vs, ⌜f' = f⌝ ∗ ⌜vs = [VAL_int32 (Wasm_int.Int32.repr (k - 1))]⌝)%I).
      + iIntros (w f' [-> ->]) "Hf Hrun".
        iApply lwp_binop.
        * cbn.
          reflexivity.
        * iFrame.
          instantiate (1 := (λ f' vs, ⌜f' = f⌝ ∗ ⌜vs = [VAL_int32 (Wasm_int.Int32.repr 2)]⌝)%I).
          cbn.
          iSplit; [|done].
          iSplit; [done|].
          iPureIntro.
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
      iApply lwp_testop_i32.
      + reflexivity.
      + cbn.
        iFrame.
        iSplit; eauto.
  Qed.

  Lemma wp_sem_ctx_mod4_sub3_test f (idx: nat) k E :
    ⊢ ⌜f.(f_locs) !! idx = Some (VAL_int32 (Wasm_int.Int32.repr (k - 3)))⌝ →
      ⌜((Wasm_int.Int32.unsigned (Wasm_int.Int32.repr k)) `mod` 4 = 0)%Z⌝ →
      ↪[frame] f -∗
      ↪[RUN] -∗
      wp_sem_ctx NotStuck E
        [memory.W.BI_get_local idx;
         memory.W.BI_const (memory.W.VAL_int32 (Wasm_int.int_of_Z i32m 2));
         memory.W.BI_binop memory.W.T_i32 (memory.W.Binop_i memory.W.BOI_and);
         memory.W.BI_testop memory.W.T_i32 memory.W.TO_eqz]
        ([], None)
        (λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr 1)]⌝%I).
  Proof.
    iIntros (Hidx Hmod) "Hf Hrun".
    wp_sem_ctx_chomp 3%nat.
    iApply (wp_sem_ctx_seq with "[Hf Hrun]").
    - wp_sem_ctx_chomp 1%nat.
      iApply (wp_sem_ctx_seq with "[Hf Hrun]").
      + iApply lenient_wp_get_local; eauto.
        iFrame.
        by instantiate (1 := (λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr (k - 3))]⌝)%I).
      + iIntros (w f' [-> ->]) "Hf Hrun".
        iApply lwp_binop.
        * cbn.
          reflexivity.
        * iFrame.
          instantiate (1 := (λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr 0)]⌝)%I).
          cbn.
          iSplit; [|done].
          iSplit; [done|].
          iPureIntro.
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
      iApply lwp_testop_i32.
      + reflexivity.
      + cbn.
        iFrame.
        iSplit; eauto.
  Qed.

  Lemma wp_sem_ctx_mod2_test_1 f (idx: nat) k E :
    ⊢ ⌜f.(f_locs) !! idx = Some (VAL_int32 (Wasm_int.Int32.repr k))⌝ →
      ⌜((Wasm_int.Int32.unsigned (Wasm_int.Int32.repr k)) `mod` 2 = 0)%Z⌝ →
      ↪[frame] f -∗
      ↪[RUN] -∗
      wp_sem_ctx NotStuck E
        [memory.W.BI_get_local idx;
         memory.W.BI_const (memory.W.VAL_int32 (Wasm_int.int_of_Z i32m 1));
         memory.W.BI_binop memory.W.T_i32 (memory.W.Binop_i memory.W.BOI_and);
         memory.W.BI_testop memory.W.T_i32 memory.W.TO_eqz]
        ([], None)
        (λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr 1)]⌝).
  Proof.
    iIntros (Hidx Hmod) "Hf Hrun".
    wp_sem_ctx_chomp 3%nat.
    iApply (wp_sem_ctx_seq with "[Hf Hrun]").
    - wp_sem_ctx_chomp 1%nat.
      iApply (wp_sem_ctx_seq with "[Hf Hrun]").
      + iApply lenient_wp_get_local; eauto.
        iFrame.
        by instantiate (1 := λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr k)]⌝%I).
      + iIntros (w f' [-> ->]) "Hf Hrun".
        iApply lwp_binop.
        * cbn.
          reflexivity.
        * iFrame.
          instantiate (1 := λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr 0)]⌝%I).
          cbn.
          iSplit; [|done].
          iSplit; [done|].
          iPureIntro.
          do 2 f_equal.
          unfold Wasm_int.Int32.iand.
          unfold Wasm_int.Int32.and.
          f_equal.
          rewrite (Z.land_ones _ 1); lias.
    - iIntros (w f' [-> ->]) "Hf' Hrun".
      iApply lwp_testop_i32.
      + reflexivity.
      + cbn.
        iFrame.
        iSplit; eauto.
  Qed.

  Lemma wp_sem_ctx_mod2_test_1_2 f (idx: nat) k E :
    ⊢ ⌜f.(f_locs) !! idx = Some (VAL_int32 (Wasm_int.Int32.repr k))⌝ →
    ⌜((Wasm_int.Int32.unsigned (Wasm_int.Int32.repr k)) `mod` 2 = 1)%Z⌝ →
    ↪[frame] f -∗
    ↪[RUN] -∗
    wp_sem_ctx NotStuck E
      [memory.W.BI_get_local idx;
       memory.W.BI_const (memory.W.VAL_int32 (Wasm_int.int_of_Z i32m 1));
       memory.W.BI_binop memory.W.T_i32 (memory.W.Binop_i memory.W.BOI_and);
       memory.W.BI_testop memory.W.T_i32 memory.W.TO_eqz]
      ([], None)
      (λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr 0)]⌝%I).
  Proof.
    iIntros (Hidx Hmod) "Hf Hrun".
    wp_sem_ctx_chomp 3%nat.
    iApply (wp_sem_ctx_seq with "[Hf Hrun]").
    - wp_sem_ctx_chomp 1%nat.
      iApply (wp_sem_ctx_seq with "[Hf Hrun]").
      + iApply lenient_wp_get_local; eauto.
        iFrame.
        by instantiate (1 := λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr k)]⌝%I).
      + iIntros (w f' [-> ->]) "Hf Hrun".
        iApply lwp_binop.
        * cbn.
          reflexivity.
        * iFrame.
          instantiate (1 := λ f' vs, ⌜f' = f /\ vs = [VAL_int32 (Wasm_int.Int32.repr 1)]⌝%I).
          cbn.
          iSplit; [|done].
          iSplit; [done|].
          iPureIntro.
          do 2 f_equal.
          unfold Wasm_int.Int32.iand.
          unfold Wasm_int.Int32.and.
          f_equal.
          rewrite (Z.land_ones _ 1); lias.
    - iIntros (w f' [-> ->]) "Hf' Hrun".
      iApply lwp_testop_i32.
      + reflexivity.
      + cbn.
        iFrame.
        iSplit; eauto.
  Qed.

  Lemma wp_sem_ctx_if_c_weak {A B} s E tf (c1 : codegen A) (c2 : codegen B) wt wt' wl wl' es x y LS :
    run_codegen (if_c tf c1 c2) wt wl = inr (x, y, wt', wl', es) ->
    exists wt1 wt2 wl1 wl2 es1 es2,
      run_codegen c1 wt wl = inr (x, wt1, wl1, es1) /\
      run_codegen c2 (wt ++ wt1) (wl ++ wl1) = inr (y, wt2, wl2, es2) /\
      wt' = wt1 ++ wt2 /\
      wl' = wl1 ++ wl2 /\
      ⊢ ∀ Φ (f: frame) i,
          ↪[frame] f -∗
          ↪[RUN] -∗
          ((⌜i <> Wasm_int.int_zero i32m⌝ ∧
              ▷ (↪[frame] f -∗ ↪[RUN] -∗ wp_sem_ctx s E [BI_block tf es1] LS Φ)) ∨
             (⌜i = Wasm_int.int_zero i32m⌝ ∧
                ▷ (↪[frame] f -∗ ↪[RUN] -∗ wp_sem_ctx s E [BI_block tf es2] LS Φ))) -∗
          wp_sem_ctx s E (BI_const (VAL_int32 i) :: es) LS Φ.
  Proof.
    intros Hcg.
    unfold wp_sem_ctx.
    eapply lwp_if_c in Hcg.
    destruct Hcg as (wt1 & wt2 & wl1 & wl2 & es1 & es2 & Hcg1 & Hcg2 & Hwt' & Hwl' & Hwp).
    do 6 eexists; split; eauto.
    do 3 (split; eauto).
    iIntros (Φ f i) "Hf Hrun Hbranches".
    iApply (Hwp with "[$] [$]"); eauto.
  Qed.

  Lemma wp_case_ptr_wp_sem_ctx_direct {A B} s E LS RS idx (c1 : codegen B) (c2: base_memory -> codegen A) wt wt' wl wl' es x y z v (f: frame) Φ :
    run_codegen (memory.case_ptr idx (Tf [] []) c1 c2) wt wl = inr (x, (y, z), wt', wl', es) ->
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
            match ptr with
            | PtrInt z => wp_sem_ctx s E es1 ([], None)  Φ
            | PtrHeap MemMM l => wp_sem_ctx s E es2 ([], None) Φ
            | PtrHeap MemGC l => wp_sem_ctx s E es3 ([], None) Φ
            end) -∗
        atom_interp (PtrA ptr) v ∗
        wp_sem_ctx s E es (LS, RS) Φ.
  Proof.
    intros Hcg.
    unfold memory.case_ptr in Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es_isptr ?es_if_isptr Hcg_isptr Hcg_if_isptr. inv_cg_emit_all Hcg_isptr.
    subst.
    rewrite -> !app_nil_l, !app_nil_r in *.
    eapply (wp_sem_ctx_if_c_weak s E) in Hcg_if_isptr.
    destruct Hcg_if_isptr as (?wt & ?wt & ?wl & ?wl & es_int & es_case_m & Hcg_int & Hcg_case_m & -> & -> & Hwp_if_isptr).
    inv_cg_bind Hcg_case_m [] ?wt ?wt ?wl ?wl ?es_mm_or_gc es_if_m Hcg_mm_or_gc Hcg_if_m.
    inv_cg_emit_all Hcg_mm_or_gc.
    subst.
    eapply (lwp_if_c s E) in Hcg_if_m.
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
        iSplitR.
        * cbn; eauto.
        * iApply (wp_sem_ctx_seq with "[Hframe Hrun]").
          {
            iApply wp_sem_ctx_mono; [by iApply sem_ctx_imp_bot | eauto | ].
            iApply (wp_sem_ctx_mod2_test_1 with "[] [] [$] [$]"); eauto.
            iPureIntro.
            unfold Wasm_int.Int32.repr; simpl.
            rewrite Wasm_int.Int32.Z_mod_modulus_eq.
            unfold Wasm_int.Int32.modulus, Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
            unfold two_power_nat.
            simpl.
            apply mod32_mod2.
          }
          iIntros (vs f') "[-> ->] Hf Hrun".
          iApply (Hwp_if_isptr with "[$] [$]").
          iLeft.
          iSplit; [iPureIntro; done|].
          iIntros "!> Hf Hrun".
          iApply (wp_sem_ctx_block_peel with "[Hptr] [$] [$]").
          iIntros "Hf Hrun".
          iApply wp_sem_ctx_clear_labels.
          iApply ("Hptr" with "[$] [$]").
      + done.
    - iDestruct "Hrep" as "(%l & -> & %rp & %Hrep & Hroot)".
      iPoseProof (root_pointer_heap_shp_inv with "Hroot") as "(%a & ->)".
      iSplitL "Hroot"; first (iExists _; by iFrame).
      inversion Hrep as [|? ? Hmod]; subst.
      iApply (wp_sem_ctx_seq with "[Hframe Hrun]").
      {
        iApply wp_sem_ctx_mono; [by iApply sem_ctx_imp_bot | eauto | ].
        iApply (wp_sem_ctx_mod2_test_1_2 with "[] [] [$] [$]"); eauto.
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
        1,2: replace 4 with (2 * 2); last done.
        1,2: rewrite <- Z.mul_assoc.
        1,2: rewrite Z.even_even.
        1,2: done.
      }
      iIntros (w f' [-> ->]) "Hf Hrun".
      iApply (Hwp_if_isptr with "[$] [$]").
      iRight.
      iSplit; first done.
      iIntros "!> Hframe Hrun".
      destruct μ.
      + simpl tag_address in Hlookup_f.
        cbn.
        iApply (wp_sem_ctx_block_peel with "[Hptr] [$] [$]").
        iIntros "Hf Hrun".
        wp_sem_ctx_chomp 4%nat.
        iApply (wp_sem_ctx_seq with "[Hf Hrun]").
        * iApply wp_sem_ctx_clear_labels.
          iApply (wp_sem_ctx_mod4_sub3_test with "[//] [] [$] [$]"); eauto.
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
        * iIntros (w f' [-> ->]) "Hf Hrun".
          iApply (Hwp_if_m with "[$] [$]").
          iLeft.
          iSplit; eauto.
          iIntros  "!> Hf Hrun".
          iApply (wp_sem_ctx_block_peel with "[Hptr] [$] [$]").
          iIntros "Hf Hrun".
          iApply wp_sem_ctx_clear_labels.
          iApply ("Hptr" with "[$] [$]").
      + simpl tag_address in Hlookup_f.
        cbn.
        iApply (wp_sem_ctx_block_peel with "[Hptr] [$] [$]").
        iIntros "Hf Hrun".
        wp_sem_ctx_chomp 4%nat.
        rewrite take_0 drop_0.
        iApply (wp_sem_ctx_seq with "[Hf Hrun]").
        * iApply wp_sem_ctx_clear_labels.
          iApply (wp_sem_ctx_mod4_sub1_test with "[//] [] [$] [$]").
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
        * iIntros (w f' [-> ->]) "Hf Hrun".
          iApply (Hwp_if_m with "[$] [$]").
          iRight.
          iSplit; auto.
          iIntros  "!> Hf Hrun".
          iApply (wp_sem_ctx_block_peel with "[Hptr] [$] [$]").
          iIntros "Hf Hrun".
          iApply wp_sem_ctx_clear_labels.
          iApply ("Hptr" with "[$] [$]").
  Qed.

  Close Scope Z_scope.


  Lemma wp_map_cg_ptr_duproot ι idx wt wl res wt' wl' es:
    run_codegen (memory.map_gc_ptr ι idx (memory.duproot mr)) wt wl = inr (res, wt', wl', es) ->
    res = () /\ wt' = [] /\ wl' = [].
  Proof.
    unfold memory.map_gc_ptr, memory.ite_gc_ptr; intros Hcg.
    destruct ι.
    - apply wp_ignore in Hcg.
      destruct Hcg as (-> & res' & Hcg).
      admit.
    - cbn; inv_cg_ret Hcg; done.
    - cbn; inv_cg_ret Hcg; done.
    - cbn; inv_cg_ret Hcg; done.
    - cbn; inv_cg_ret Hcg; done.
  Admitted.

  Lemma wp_map_gc_ptrs_duproot ιs idxs wt wl res wt' wl' es_gcs:
    run_codegen (memory.map_gc_ptrs ιs idxs (memory.duproot mr)) wt wl = inr (res, wt', wl', es_gcs) ->
    res = () /\ wt' = [] /\ wl' = [].
  Proof.
    unfold memory.map_gc_ptrs, util.mapM_.
    intros Hcg.
    apply wp_ignore in Hcg.
    destruct Hcg as (-> & res' & Hcg).
    remember (zip ιs idxs) as ιidxs.
    revert Heqιidxs Hcg.
    revert ιs idxs wt wl res' wt' wl' es_gcs.
    induction ιidxs as [|[ι idx] ιidxs].
    - intros.
      apply wp_mapM_nil in Hcg.
      destruct Hcg as (-> & -> & -> & ->).
      done.
    - intros.
      destruct ιs as [|ι' ιs], idxs as [|idx' idxs]; inversion Heqιidxs.
      subst ι' idx'.
      apply wp_mapM_cons in Hcg.
      destruct Hcg as (res & ?wt & ?wl & ?es & ?res & ?wt & ?wl & ?es & Hdup & Hcg & Heqs).
      destruct Heqs as (-> & -> & -> & ->).
      eapply IHιidxs in Hcg; eauto.
      destruct Hcg as (_ & -> & ->).
      split; auto.
      apply wp_map_cg_ptr_duproot in Hdup.
      destruct Hdup as (-> & -> & ->).
      done.
  Qed.


  Fixpoint replace_base {n} (vh: valid_holed n) vs :=
    match vh with
    | VH_base n _ es => VH_base n vs es
    | VH_rec n b c d vh e => VH_rec b c d (replace_base vh vs) e
    end.

  Lemma lfilled_get_replace_base {n} (vh: valid_holed n) es vs1 vs2:
    get_base_l vh = vs1 ++ vs2 ->
    lh_depth (lh_of_vh vh) = n ->
    is_true (lfilled n (lh_of_vh (replace_base vh vs1))
               (seq.cat (v_to_e_list vs2) es) (vfill vh es)).
  Proof.
    induction vh => //=.
    - intros -> <-.
      unfold lfilled, lfill => //=.
      rewrite v_to_e_is_const_list /=.
      rewrite -v_to_e_cat.
      repeat rewrite cat_app.
      repeat rewrite app_assoc.
      done.
    - intros Hbase Hdepth.
      apply eq_add_S in Hdepth.
      specialize (IHvh Hbase Hdepth).
      unfold lfilled, lfill; fold lfill.
      rewrite v_to_e_is_const_list.
      unfold lfilled in IHvh.
      destruct (lfill _ _ _) => //.
      apply b2p in IHvh as <-.
      done.
  Qed. 


    Lemma translate_types_app ks t1s t2s res :
    prelude.translate_types ks (t1s ++ t2s) = Some res ->
    exists res1 res2, prelude.translate_types ks t1s = Some res1 /\
                 prelude.translate_types ks t2s = Some res2 /\
                 res = res1 ++ res2.
  Proof.
    generalize dependent res. 
    induction t1s => //=.
    - intros res Htrans. exists [], res. done.
    - intros res Htrans.
      unfold prelude.translate_types in Htrans.
      simpl in Htrans.
      destruct (prelude.translate_type ks a) eqn:Ha; simpl in Htrans => //. 
      destruct (mapM (prelude.translate_type ks) (t1s ++ t2s)) eqn:Htrans';
        simpl in Htrans => //. 
      inversion Htrans; subst res.
      edestruct IHt1s as (res1 & res2 & Htrans1 & Htrans2 & Hres).
      + unfold prelude.translate_types.
        rewrite Htrans'.
        simpl. done.
      + exists (l ++ res1), res2.
        repeat split => //=.
        * rewrite /prelude.translate_types /=.
          unfold prelude.translate_types in Htrans1.
          destruct (mapM (prelude.translate_type ks) t1s) eqn:Htrans1' => //. 
          rewrite Ha /=.
          simpl in Htrans1. inversion Htrans1; subst res1 => //.
        * rewrite Hres app_assoc //.
  Qed.



  (*  Lemma translate_subst ks a ts smem srep ssize st:
    translate_type ks a = Some ts ->
    exists ts', translate_type ks (subst_type smem srep ssize st a) = Some ts' /\
             length ts = length ts'.
  Proof.
    unfold translate_type.
    destruct (type_rep ks a) eqn:Ha => //=. 
    destruct a => //=.
    - 
  
  Lemma eval_rep_subst_length srep r :
    length (eval_rep r) = length (eval_rep (subst_representation srep r)). 


  Lemma value_interp_length ts se F smem srep ssize a vs :
    translate_type (fc_type_vars F) a = Some ts ->
    (subst_env_interp sr F smem srep ssize se ∗
       value_interp sr mr se (subst_type smem srep ssize VarT a) (SValues vs)
       ⊢ ⌜ length vs = length ts ⌝)%I.
  Proof.
    iIntros (Ha) "[Hse Ha]".
    unfold subst_env_interp.
    iDestruct "Hse" as "(%Hse & Hse)".
    unfold sem_env_interp. 
    iDestruct (value_interp_eq with "Ha") as "Ha".
    unfold value_interp0.
    simpl.
    unfold translate_type in Ha.
    unfold type_rep in Ha.
    unfold type_kind in Ha.
    iDestruct "Ha" as (κ) "(%Hkind & Hkind & Ha)".
    destruct a => //=.
    - destruct (fc_type_vars F !! n) eqn:Hksn; last done.
      simpl in Ha.
      unfold kind_rep in Ha.
      destruct k => //=.
      simpl in Ha.
      simpl in Hkind.
      unfold type_var_interp.
      rewrite -nth_error_lookup in Hkind.
      rewrite nth_error_map in Hkind.
      destruct (nth_error se n) eqn:Hsen; last by rewrite Hsen in Hkind.
      destruct o. rewrite Hsen /= in Hkind.
      inversion Hkind; subst o; clear Hkind.
      erewrite nth_error_nth.
      2:{ rewrite nth_error_map. rewrite Hsen. done. }
      rewrite nth_error_lookup in Hsen.
      iDestruct (big_sepL2_lookup _ _ _ _ _ _ Hsen Hksn with "Hse") as "[%Heq _]".
      simpl in Heq; subst κ. 
      simpl.
      iDestruct "Hkind" as "%Hkind".
      destruct Hkind as (vs0 & Heq & Hrepr).
      inversion Heq; subst vs0; clear Heq.
      unfold representation_interp0 in Hrepr.
      destruct Hrepr as (ιs & Hιs & Hιvs).
      unfold translate_rep in Ha.
      iPureIntro.
      apply Forall2_length in Hιvs.
      rewrite -Hιvs.
      destruct (eval_rep r) eqn:Hr; last done.
      simpl in Ha.
      inversion Ha; subst ts.
      rewrite length_map.

      
      Check eval_rep.
      
      
      unfold subst_representation in Hιs. 

      unfold nth. 
      iClear "Hkind".  clear. 
      
      
      Set Printing All. 
      rewrite map_nth. 
      simpl in H
      Search (nth_error (map _ _) _).
      Search (map _ _ !! _).
      
    all: destruct (ks !! n) eqn:Hksn; last done.
    all: simpl in Ha.
    all: simpl in Hkind.
    all: inversion Hkind; subst κ; clear Hkind.
    all: unfold kind_as_type_interp.
    all: destruct k => //=.
    all: simpl in Ha.
    all: iDestruct "Hkind" as %Hkind.
    all: destruct Hkind as (vs' & Hvs & Hrep).
    all: inversion Hvs; subst vs'; clear Hvs.
    - iPureIntro.
      destruct r => //=.
      all: rewrite /translate_rep /= in Ha.
      all: simpl in Hrep.
      + induction l.
        * simpl in Hrep, Ha.
          inversion Ha; subst ts => //=.
          unfold representation_interp0 in Hrep.
          destruct Hrep as (ιs & Hιs & Hl1).
          simpl in Hιs.
          inversion Hιs; subst ιs.
          inversion Hl1; subst.
          inversion H3; subst. done.
        * simpl in Ha.
          destruct (eval_rep a) eqn:Ha'; last done.
          simpl in Ha.
          destruct (mapM eval_rep l) eqn:Hl; last done.
          simpl in Ha.
          inversion Ha; subst ts; clear Ha.
          simpl in IHl.
          unfold representation_interp0 in Hrep.
          destruct Hrep as (ιs & Hιs & Hvs).
          simpl in Hιs.
          destruct (eval_rep (subst_representation srep a)) eqn:Ha''; last done.
          simpl in Hιs.
          destruct (mapM eval_rep (map (subst_representation srep) l)) eqn:Hl'; last done.
          simpl in Hιs.
          inversion Hιs; subst ιs.
          unfold representation_interp0 in IHl.
          simpl in IHl.
          rewrite Hl' /= in IHl.
          apply IHl.
          -- eexists. split; first done.
             
       *)   

  Lemma translate_types_length_subst ks ts res vs se smem srep ssize :
    prelude.translate_types ks ts = Some res ->
    (([∗ list] y1;y2 ∈ map (subst_type smem srep ssize VarT) ts;vs, 
       value_interp rti sr se y1 (SAtoms y2))
       ⊢ ⌜ length res = list_sum (map length vs) ⌝)%I.
  Proof.
  Admitted. 
(*    generalize dependent vs. generalize dependent res. 
    induction ts; iIntros (res vs Hres) "H".
    { destruct vs; last done.
      rewrite /translate_types /= in Hres.
      inversion Hres; subst; done. }
    rewrite /translate_types /= in Hres.
    destruct (translate_type ks a) eqn:Ha; last done.
    destruct (mapM (translate_type ks) ts) eqn:Htrans; last done.
    simpl in Hres.
    inversion Hres; subst res; clear Hres.
    destruct vs; first done.
    iDestruct "H" as "[Ha H]".
    iDestruct (IHts with "H") as "%IH".
    { rewrite /translate_types Htrans //. }
    iClear "H".
 *)

  Lemma translate_types_length (ks : list kind) ts res vs se:
    prelude.translate_types ks ts = Some res ->
    (([∗ list] y1;y2 ∈ ts;vs, 
       value_interp rti sr se y1 (SAtoms y2))
       ⊢ ⌜ length res = list_sum (map length vs) ⌝)%I.
  Proof.
    iIntros (H) "H".
    iApply (translate_types_length_subst _ _ _ _ _ _ _ _ H).
    instantiate (1 := VarS).
    instantiate (1 := VarR).
    instantiate (1 := VarM).
    replace (map (subst_type VarM VarR VarS VarT) ts) with ts; first done.
    clear. induction ts => //=.
    rewrite instId'_type -IHts //. 
  Qed.

  Lemma length_lholeds_bef_aft se l lh bef aft:
    length_lholeds rti sr se l lh <->
      length_lholeds rti sr se l (lh_bef_aft bef lh aft).
  Proof.
    induction lh => //=.
    { destruct l => //=. }
    destruct l => //=.
  Qed. 
  
  Lemma length_lholeds_app se l1 l2 lh1 lh2:
    length_lholeds rti sr se l1 lh1 ->
    length_lholeds rti sr se l2 lh2 ->
    length_lholeds rti sr se (l1 ++ l2) (lh_plug lh2 lh1).
  Proof.
    generalize dependent l1.
    induction lh1 => //=.
    - destruct l1 ; last by destruct p.
      intros _ H.
      apply length_lholeds_bef_aft => //. 
    - destruct l3 => //=.
      destruct p.
      intros [Hn Hlh1] Hlh2.
      split; last by apply IHlh1.
      exact Hn.
  Qed. 

  Lemma lholed_valid_plug lh1 lh2:
    lholed_valid lh1 -> lholed_valid lh2 -> lholed_valid (lh_plug lh2 lh1).
  Proof.
    induction lh1; first destruct lh2 => //=.
    - intros ??; by apply const_list_concat.
    - intros ? [??]. split => //. 
      by apply const_list_concat.
    - intros [??] ?. split => //.
      apply IHlh1 => //.
  Qed.

  Lemma to_val_v_to_e vs :
    to_val (v_to_e_list vs) = Some (immV vs).
  Proof.
    induction vs => //=.
    unfold to_val.
    unfold RichWasm.iris.language.iris.iris.to_val.
    rewrite (separate1 (AI_basic _)).
    rewrite map_app.
    rewrite -cat_app.
    rewrite merge_app.
    unfold to_val, RichWasm.iris.language.iris.iris.to_val in IHvs.
    destruct (merge_values_list _) eqn:Hvs => //.
    inversion IHvs; subst v.
    simpl. done.
  Qed. 

  Fixpoint pull_base_l_drop_len {i : nat} (vh : valid_holed i) (len : nat) :=
    match vh with
    | VH_base j vs es => (VH_base j (take len vs) es, drop len vs)
    | @VH_rec j vs m es' lh' es => let '(lh'',l1) := pull_base_l_drop_len lh' len in
                                  (@VH_rec j vs m es' lh'' es,l1)
    end.

  Lemma vfill_pull_base_l_take_len {i : nat} (vh : valid_holed i) (len : nat) es vh' vs :
    pull_base_l_drop_len vh len = (vh', vs) ->
    vfill vh es = vfill vh' (((λ x : value, AI_basic (BI_const x)) <$> vs) ++ es).
  Proof.
    intros Heq.
    induction vh.
    { simpl in *. simplify_eq. simpl.
      rewrite -!app_assoc. repeat rewrite v_to_e_is_fmap. rewrite fmap_take fmap_drop.
      rewrite (app_assoc (take _ _)).
      rewrite (take_drop len ((λ x : value, AI_basic (BI_const x)) <$> l)). auto. }
    { simpl in *.
      destruct (pull_base_l_drop_len vh len) eqn:Heq'.
      simplify_eq. simpl. f_equiv. f_equiv.
      erewrite IHvh;eauto. 
    }
  Qed.

  Lemma lh_depth_pull_base_l_take_len {i : nat} (vh : valid_holed i) (len : nat) vh' vs :
    pull_base_l_drop_len vh len = (vh', vs) ->
    lh_depth (lh_of_vh vh) = lh_depth (lh_of_vh vh').
  Proof.
    intros Heq.
    induction vh;simpl in *;simplify_eq;auto.
    destruct (pull_base_l_drop_len vh len) eqn:Heq'.
    simplify_eq. simpl. erewrite IHvh;eauto.
  Qed.

  Lemma length_pull_base_l_take_len {i : nat} (vh : valid_holed i) (len : nat) vh' vs vs' :
    get_base_l vh = vs' ->
    pull_base_l_drop_len vh len = (vh', vs) ->
    length vs = length vs' - len.
  Proof.
    intros Hbase Hpull.
    induction vh;simpl in *;simplify_eq.
    { rewrite length_drop. auto. }
    { destruct (pull_base_l_drop_len vh len) eqn:Heq'.
      simplify_eq. simpl. erewrite IHvh;eauto. }
  Qed.

  Lemma get_layer_depth lh k a b c lh' d:
    get_layer lh k = Some (a, b, c, lh', d) ->
    lh_depth lh = lh_depth lh' + k + 1.
  Proof.
    generalize dependent k. 
    induction lh => //=.
    destruct k => //=.
    - intros Heq; inversion Heq; subst.
      lia.
    - intros H. apply IHlh in H.
      rewrite H. lia.
  Qed.

  Lemma length_length_lholeds se l lh:
        length_lholeds rti sr se l lh ->
        length l = lh_depth lh.
  Proof.
    generalize dependent lh. 
    induction l; destruct lh => //=.
    { destruct a => //. }
    destruct a => //=.
    intros [??].
    apply IHl in H0.
    rewrite H0 //.
  Qed. 

  Lemma get_layer_lookup_lh_lengths se l lh i ts ctx vs' n2 es lh' es2' :
    length_lholeds rti sr se (rev l) lh ->
    l !! i = Some (ts, ctx) ->
    get_layer lh (lh_depth lh - S i) = Some (vs', n2, es, lh', es2') ->
    n2 = length ts.
  Proof.
  Admitted. 
(*    revert lh i ts ctx vs' n2 es lh' es2'.
    induction l using rev_ind;intros lh i ts ctx vs' n2 es lh' es2' Hlen Hlook Hlay.
    - done. 
    - apply length_length_lholeds in Hlen as Hdep.
      rewrite length_rev in Hdep.
      destruct lh;[done|].
      rewrite length_app /= PeanoNat.Nat.add_1_r in Hdep.
      destruct (decide (i = length l)).
      + subst. simpl in *.
        inversion Hdep as [Heq].
        rewrite Heq PeanoNat.Nat.sub_diag in Hlay. simplify_eq.
        rewrite rev_unit in Hlen. simpl in Hlen. destruct x.
        destruct Hlen as [? ?].
        rewrite lookup_snoc in Hlook. simplify_eq. }
      { apply lookup_lt_Some in Hlook as Hlt.
        rewrite length_app /= PeanoNat.Nat.add_1_r in Hlt.
        assert (i < length l) as Hlt';[lia|].
        rewrite lookup_app_l in Hlook;auto.
        simpl in Hlay.

        inversion Hdep as [Heq].
        destruct (lh_depth lh - i) eqn:Hi;[lia|].
        assert (n1 = lh_depth lh - S i);[lia|subst n1].
        eapply IHl in Hlook;eauto.
        rewrite rev_unit in Hlen. inversion Hlen;auto.
      }
    }
  Qed. *)

    Lemma length1concat (vss: list (list value)) (vs: list value):
    1 = length vss ->
    vs = concat vss ->
    vss = [vs].
  Proof.
    intros Hlength Hconcat.
    destruct vss as [| v vs1]; inversion Hlength.
    symmetry in H0; apply nil_length_inv in H0; subst; simpl.
    by rewrite app_nil_r.
  Qed.


    (* some lemmas borrowed from iris_fundamental_weakening.v *)
  Lemma get_base_l_push_const {i : nat} (lh : valid_holed i) w :
    get_base_l (vh_push_const lh w) = (w ++ get_base_l lh) ∨
      get_base_l (vh_push_const lh w) = get_base_l lh.
  Proof.
    induction lh.
    { left. auto. }
    { simpl. by right. }
  Qed.

  Lemma push_const_lh_depth {i : nat} (lh : valid_holed i) w :
    lh_depth (lh_of_vh lh) = lh_depth (lh_of_vh (vh_push_const lh w)).
  Proof.
    induction lh;simpl;auto.
  Qed.

  Lemma simple_get_base_l_push_const (lh : simple_valid_holed) w :
    simple_get_base_l (sh_push_const lh w) = (w ++ simple_get_base_l lh) ∨
    simple_get_base_l (sh_push_const lh w) = simple_get_base_l lh.
  Proof.
    induction lh.
    { left. auto. }
    { simpl. by right. }
  Qed.

  Lemma sh_push_const_lh_depth (lh : simple_valid_holed) w :
    lh_depth (lh_of_sh lh) = lh_depth (lh_of_sh (sh_push_const lh w)).
  Proof.
    induction lh;simpl;auto.
  Qed.

  Lemma br_interp_val_app se τr L WL inst lh τc i lh' τ os vs :
    ⊢ value_interp rti sr se τ (SAtoms os) -∗
      atoms_interp os vs -∗
      br_interp rti sr se τr L WL inst lh τc i lh' -∗
      br_interp rti sr se τr L WL inst lh τc i (vh_push_const lh' vs).
  Proof.
    revert lh' os vs.
    iLöb as "IH".
    iIntros (lh' rvs vs) "Hrvs Hvs Hbr".
    iEval (rewrite br_interp_eq) in "Hbr".
    iDestruct "Hbr" as "(%k & %p & %lh1 & %lh2 & %τs & %es0 & %es1 & %es2 & %vs0 & %vs1 & %rvs1 & Hbr)".
    rewrite br_interp_eq.
    iDestruct "Hbr" as "(%Hbase & %Hdepth & %Hlbty & %Hlayer & %Hdepth' & %Hminus & Hvs1 & Hrvs1 & Hbr)".
    pose proof (get_base_l_push_const lh' vs) as [Hbase' | Hbase'].
    - iExists k, p, lh1, lh2, τs, es0, es1, es2, (vs ++ vs0), vs1, rvs1.
      iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit]]]]]; try iPureIntro.
      + by rewrite Hbase' Hbase -app_assoc.
      + by rewrite -push_const_lh_depth Hdepth.
      + auto.
      + auto.
      + by rewrite Hdepth'.
      + auto.
      + iFrame.
    - iExists k, p, lh1, lh2, τs, es0, es1, es2, vs0, vs1, rvs1.
      iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit]]]]]; try iPureIntro.
      + by rewrite Hbase' Hbase.
      + by rewrite -push_const_lh_depth Hdepth.
      + auto.
      + auto.
      + by rewrite Hdepth'.
      + auto.
      + iFrame.
  Qed.

  Lemma const_list_map ws1 :
    is_true (const_list (map (λ x : value, AI_basic (BI_const x)) ws1)).
  Proof.
    induction ws1.
    - done.
    - by rewrite Wasm.properties.const_list_cons.
  Qed.

  Lemma lfilled_simple_get_base_pull j sh e LI ws1 ws2 :
    simple_get_base_l sh = ws1 ++ ws2 ->
    is_true (lfilled j (lh_of_sh sh) e LI) ->
    ∃ lh, is_true (lfilled j lh (of_val (immV ws2) ++ e) LI).
  Proof.
    revert j e LI ws1 ws2.
    induction sh;intros j e LI ws1 ws2 Hbase Hfill%lfilled_Ind_Equivalent.
    { simpl in *. inversion Hfill;simplify_eq.
      eexists. rewrite map_app.
      repeat erewrite <- app_assoc. erewrite (app_assoc _ e).
      apply lfilled_Ind_Equivalent. constructor.
      apply const_list_map. }
    { simpl in Hfill. inversion Hfill;simplify_eq.
      apply lfilled_Ind_Equivalent in H8.
      eapply IHsh in H8 as Hlh';eauto.
      destruct Hlh' as [lh Hfill'].
      eexists.
      apply lfilled_Ind_Equivalent.
      constructor;eauto.
      apply lfilled_Ind_Equivalent;eauto. }
  Qed.

  Lemma return_interp_val_app se τr τ s os vs :
    ⊢ value_interp rti sr se τ (SAtoms os) -∗
      atoms_interp os vs -∗
      return_interp rti sr se τr s -∗
      return_interp rti sr se τr (sh_push_const s vs).
  Proof.
    iIntros "Hrvs Hvs Hr".
    iDestruct "Hr" as "(%vs1 & %vs2 & %rvs1 & %Hs & Hrvs1 & Hvs1 & Hr)".
    pose proof (sfill_to_lfilled s ([AI_basic BI_return])) as Hj.
    pose proof Hs as Hpull.
    eapply lfilled_simple_get_base_pull in Hpull; try apply Hj.
    destruct Hpull as [lhp Hpull].
    pose proof (sfill_to_lfilled (sh_push_const s vs) ([AI_basic BI_return])) as Hj'.
    destruct (simple_get_base_l_push_const s vs) as [Hs' | Hs'].
    - rewrite Hs in Hs'. 
      rewrite app_assoc in Hs'.
      pose proof Hs' as Hpull'.
      eapply lfilled_simple_get_base_pull in Hpull'; try apply Hj'.
      destruct Hpull' as [lhp' Hpull'].
      iExists (vs ++ vs1), vs2, rvs1.
      iSplit; first by rewrite Hs'.
      iFrame.
      iIntros (fr fr') "Hf Hrun".
      iSpecialize ("Hr" $! fr fr' with "Hf").
      iApply (wp_ret_shift _ _ _ _ _ _ _ _ _ _ _ (v_to_e_list vs2) with "[$Hrun] [$Hr]").
      + apply v_to_e_is_const_list.
      + by rewrite length_map.
      + apply Hpull.
      + eapply Hpull'.
    - rewrite Hs in Hs'. 
      pose proof Hs' as Hpull'.
      eapply lfilled_simple_get_base_pull in Hpull'; try apply Hj'.
      destruct Hpull' as [lhp' Hpull'].
      iExists vs1, vs2, rvs1.
      iSplit; first by rewrite Hs'.
      iFrame.
      iIntros (fr fr') "Hf Hrun".
      iSpecialize ("Hr" $! fr fr' with "Hf").
      iApply (wp_ret_shift _ _ _ _ _ _ _ _ _ _ _ (v_to_e_list vs2) with "[$Hrun] [$Hr]").
      + apply v_to_e_is_const_list.
      + by rewrite length_map.
      + apply Hpull.
      + eapply Hpull'.
  Qed.
  
  Lemma expr_interp_val_app se τr τc L WL τs inst lh es τ os vs :
    ⊢ expr_interp rti sr se τr τc L WL τs inst lh es -∗
      value_interp rti sr se τ (SAtoms os) -∗
      atoms_interp os vs -∗
      expr_interp rti sr se τr τc L WL (τ :: τs) inst lh (v_to_e_list vs ++ es).
  Proof.
    iIntros "Hes Hrvs Hvs".
    iApply lenient_wp_val_app'.
    iApply (lwp_wand with "Hes").
    set (Φ :=
           {|
             lp_fr_inv := const True%I;
             lp_val := λ f vs0, 
               (frame_interp rti sr se L WL inst f ∗
                ∃ os θ, values_interp rti sr se τs os ∗
                        atoms_interp os vs0 ∗
                        rt_token rti sr θ)%I;
             lp_trap := True%I;
             lp_br := λ n, br_interp rti sr se τr L WL inst lh τc n;
             lp_ret := return_interp rti sr se τr;
             lp_host := λ _ _ _ _, False%I
           |}).
    set (Ψ := lp_combine _ _).
    iIntros (lv) "(%f & Hf & Hfrinv & HΦ)".
    iExists f.
    change (lp_fr_inv Ψ) with (lp_fr_inv Φ).
    iFrame.
    destruct lv; unfold lp_noframe.
    - cbn in *.
      iDestruct "HΦ" as "(Hfr & Hrun & Hvs')".
      iFrame.
      iDestruct "Hvs'" as "(%rvs' & %θ' & (%vss & %Hvss & Hτs) & Hrvs' & Hrti)".
      iExists (os ++ rvs'), _.
      iFrame.
      iExists (os :: vss); iFrame.
      cbn.
      by rewrite Hvss.
    - done.
    - iDestruct "HΦ" as "[Hrun Hbr]".
      iFrame.
      iApply (br_interp_val_app with "[$] [$] [$]").
    - iDestruct "HΦ" as "[Hrun Hret]".
      iFrame "Hrun".
      iApply (return_interp_val_app with "[$] [$] [$]").
    - done.
  Qed.

End Fundamental_Shared.
