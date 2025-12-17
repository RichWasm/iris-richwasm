Require Import RecordUpdate.RecordUpdate.
From stdpp Require Import base list.

From iris.proofmode Require Import base tactics classes.
From Wasm Require Import operations.

From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import prelude codegen instruction module.
From RichWasm.iris Require Import autowp memory util wp_codegen.
From RichWasm.iris.language Require Import lenient_wp lwp_pure lwp_structural lwp_resources logpred.
From RichWasm.iris.logrel Require Import relations fundamental_kinding.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Fundamental.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Ltac clear_nils :=
    repeat rewrite <- ?app_assoc, -> ?app_nil_l, -> ?app_nil_r in *.

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

  Lemma compat_nop M F L wt wt' wtf wl wl' wlf es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [] [] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (INop ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Proof.
    (* This is currently following the compat_copy lemma very closely *)
    intros fe WT WL ψ Hok Hcompile.
    inv_cg_emit Hcompile; subst.
    unfold have_instruction_type_sem.
    destruct ψ eqn:Hψ.
    inversion Hψ; subst l l0.
    iIntros (? ? ? ? ? ? ? ?) "Hinst Hctx Hrvs Hvs Hframe Hrt Hf Hrun".
    unfold expr_interp.
    iEval (cbn) in "Hrvs"; iEval (cbn) in "Hvs".
    iDestruct "Hvs" as "(%rvss & %Hconcat & Hrvss)".
    iPoseProof (big_sepL2_length with "[$Hrvss]") as "%Hlens_rvss".
    iPoseProof (big_sepL2_length with "[$Hrvs]") as "%Hlens_rvs_vs".
    cbn in Hlens_rvss.
    destruct rvss, os; cbn in Hconcat, Hlens_rvss; try congruence.
    cbn in Hlens_rvs_vs. destruct vs; cbn in Hlens_rvs_vs; try congruence.
    iApply (lenient_wp_nop with "[$] [$] [Hframe Hrt] []").
    - iModIntro.
      iFrame.
      iExists []; cbn.
      iSplitR; [|done].
      iExists []; auto.
    - done.
  Qed.

  Lemma compat_unreachable M F L L' wt wt' wtf wl wl' wlf ψ es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (IUnreachable ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L'.
  Admitted.
 
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

  Lemma frame_interp_wl_interp se F L WL inst fr :
    frame_interp rti sr se L WL inst fr -∗
    ⌜wl_interp (fe_wlocal_offset (fe_of_context F)) WL fr⌝.
  Proof.
  Admitted.

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

  Search "wp_block".

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



  Require Import ZArith.
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


  Lemma wp_case_ptr {A B} s E idx (c1 : codegen B) (c2: base_memory -> codegen A) wt wt' wl wl' es x y z v (f: frame) Φ :
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
            | PtrInt z => lenient_wp s E [AI_basic (BI_block (Tf [] []) es1)] Φ
            | PtrHeap MemMM l => lenient_wp s E [AI_basic (BI_block (Tf [] []) es2)] (lp_bind s E 1 (LH_rec [] 0 [] (LH_base [] []) []) Φ)
            | PtrHeap MemGC l => lenient_wp s E [AI_basic (BI_block (Tf [] []) es3)] (lp_bind s E 1 (LH_rec [] 0 [] (LH_base [] []) []) Φ)
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
      (*rewrite <- (app_nil_l [AI_basic (BI_block tf (_ ++ _))]).*)
      (*destruct tf as [tf1 tf2].*)
      (*iApply (lenient_wp_block with "[$] [$]"); auto.*)
      (*{ admit. }*)
      (*iIntros "!> Hframe Hrun".*)
      (*rewrite app_nil_l.*)
      (*iApply lwp_wasm_empty_ctx.*)
      (*iApply lwp_label_push_nil.*)
      (*iApply lwp_ctx_bind; first done.*)
      (*rewrite to_e_list_app.*)
      (*iApply (lenient_wp_seq with "[Hframe Hrun]").*)
      (*{*)
      (*  iApply wp_mod2_test_2 with .*)
      (*}*)
      (*lwp_chomp 4%nat.*)
      (*rewrite take_0 drop_0.*)
      (*iApply (lenient_wp_seq with "[Hframe Hrun]").*)

      destruct μ.
      + simpl tag_address in Hlookup_f.
        cbn.
        lwp_chomp 0%nat.
        iApply (lenient_wp_block with "[$] [$]"); auto.
        iIntros "!> Hf Hrun".
        rewrite app_nil_l.
        Search (AI_label).

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
      + replace
        ([memory.W.BI_get_local (localimm idx);
        memory.W.BI_const (memory.W.VAL_int32 (Wasm_int.int_of_Z i32m 1));
        memory.W.BI_binop memory.W.T_i32 (memory.W.Binop_i memory.W.BOI_and);
        memory.W.BI_testop memory.W.T_i32 memory.W.TO_eqz])
        with
          [BI_const (VAL_int32 (Wasm_int.int_zero i32m))]
          by admit.
        admit.
  Admitted.
 
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

  Lemma compat_copy M F L wt wt' wtf wl wl' wlf τ es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [τ] [τ; τ] in
    has_copyability F τ ExCopy ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ICopy ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Proof.
    intros fe WT WL ψ Hcopy Hok Hcompile.
    unfold compile_instr in Hcompile.
    inv_cg_bind Hcompile ρ wt1 wt1' wl1 wl1' es_nil es1 Htype_rep Hcompile.
    inv_cg_bind Hcompile ιs wt2 wt2' wl2 wl2' es_nil' es2 Heval_rep Hcompile.
    inv_cg_bind Hcompile idxs ?wt ?wt ?wl ?wl es_save ?es Hsave Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_restore1 ?es Hrestore1 Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_gcs es_restore2 Hgcs Hrestore2.
    inv_cg_try_option Htype_rep.
    inv_cg_try_option Heval_rep.
    subst.
    unfold WT, WL.
    repeat rewrite <- ?app_assoc, -> ?app_nil_l, -> ?app_nil_r in *.
    unfold have_instruction_type_sem.
    unfold ψ.
    iIntros (se inst lh fr rvs vs θ) "%Henv #Hinst #Hlh Hrvs Hvs Hframe Hrt Hfr Hrun".
    unfold expr_interp.
    inversion Hcopy as [F' τ' ρ' χ ? Hhas_kind HF' Hτ' Hχ].
    subst F' τ'.
    assert (ρ' = ρ).
    {
      apply type_rep_has_kind_agree in Hhas_kind.
      rewrite Heq_some in Hhas_kind.
      congruence.
    }
    subst ρ'.
    assert (Heval: eval_kind se (VALTYPE ρ ExCopy δ) = Some (SVALTYPE ιs ExCopy δ)).
    {
      unfold eval_kind.
      by erewrite eval_rep_emptyenv.
    }
    pose proof (kinding_sound rti sr mr F se _ _ _ Hhas_kind ltac:(eauto) Heval) as Hskind.
    destruct Hskind as [Hrefine Hcopyable].
    cbn in Hcopyable.
    iDestruct "Hvs" as "(%vss & %Hconcat & Hvs)".
    iPoseProof (big_sepL2_length with "[$Hvs]") as "%Hlens".
    destruct vss as [|vs' [|vs'' vss]]; cbn in Hlens, Hconcat; try congruence.
    rewrite app_nil_r in Hconcat; subst vs'; clear Hlens.
    rewrite big_sepL2_singleton.
    iEval (cbn -[return_interp br_interp values_interp atoms_interp frame_interp]).
    rewrite to_e_list_app.
    rewrite (app_assoc (v_to_e_list _)).
    iPoseProof (frame_interp_wl_interp with "Hframe") as "%Hwl".
    set (Φ := {| lp_fr_inv := λ _, True;
               lp_val := λ f vs', 
                  ⌜∀ i, i ∉ idxs -> f_locs f !! localimm i = f_locs fr !! localimm i⌝ ∗
                  ⌜Forall2 (fun i v => f_locs f !! localimm i = Some v) idxs vs⌝ ∗
                  ⌜vs' = []⌝;
               lp_trap := False;
               lp_br := λ _ _, False;
               lp_ret := λ _, False;
                lp_host := λ _ _ _ _, False |}%I : @logpred Σ).
    iApply (lenient_wp_seq with "[Hfr Hrun]").
    {
      eapply (lwp_save_stack_w _ Φ) in Hsave; eauto.
      + destruct Hsave as (-> & -> & -> & Hsave).
        iApply (Hsave with "[$] [$]").
        iIntros (f' [Hfsame Hfchanged]).
        done.
      + admit. (* easy pure conseqeunce of value_interp and
      rep_values_interp, should be proved above the first wp_seq
      rule *)
    }
    { by iIntros (fr') "Htrap". }
    iIntros (w fr_saved) "Hnotrap Hfr _".
    rewrite to_e_list_app.
    rewrite (app_assoc (of_val _)).
    set (Φ2 := {| lp_fr_inv := λ _, True;
                 lp_val := λ f vs',
                   ⌜∀ i, i ∉ idxs -> f_locs f !! localimm i = f_locs fr !! localimm i⌝ ∗
                   ⌜Forall2 (fun i v => f_locs f !! localimm i = Some v) idxs vs⌝ ∗
                   ⌜vs' = vs⌝;
                 lp_trap := False;
                 lp_br := λ _ _, False;
                 lp_ret := λ _, False;
                 lp_host := λ _ _ _ _, False |}%I : @logpred Σ).
    destruct w; iEval (cbn) in "Hnotrap"; try done;
      try (iDestruct "Hnotrap" as "[? ?]"; done).
    iDestruct "Hnotrap" as "(Hrun & %Hsame & %Hsaved & ->)".
    eapply lwp_restore_stack_w in Hrestore1; eauto using Forall2_length.
    destruct Hrestore1 as (? & -> & -> & Hrestore1).
    iApply (lenient_wp_seq with "[Hfr Hrun]").
    {
      iEval (cbn).
      iApply (Hrestore1 with "[$] [$] [//]").
    }
    { by iIntros (w) "Htrap". }
    clear Hrestore1.
    iIntros (w fr_saved') "HΦ2 Hf _".
    destruct w; iEval (cbn) in "HΦ2"; try done;
      try (iDestruct "HΦ2" as "[? ?]"; done).
    iDestruct "HΦ2" as "(Hrun & -> & ->)".
    admit.
  Admitted.

  Lemma compat_drop M F L wt wt' wtf wl wl' wlf τ es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [τ] [] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IDrop ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Admitted.

  Ltac solve_post_lwp_num :=
    iFrame; iModIntro; cbn;
    (match goal with
      | |- context [ (VAL_int32 ?x) ] => iExists [I32A x]
      | |- context [ (VAL_int64 ?x) ] => iExists [I64A x]
      | |- context [ (VAL_float32 ?x) ] => iExists [F32A x]
      | |- context [ (VAL_float64 ?x) ] => iExists [F64A x]
    end);
    iEval (cbn); iSplitR; try iSplitR; auto;
    (match goal with
      | |- context [ (?x = concat _) ] => iExists [x]
    end);
    iEval (cbn); iSplitL; try iSplitL; auto;
    iApply value_interp_eq; cbn;
    iExists _; iSplitL; try iSplitL; auto; cbn;
    iPureIntro;
    eexists; split; auto;
    apply Forall2_cons_iff; split; auto;
    by unfold has_arep.

  Lemma one_rep_in_rvs_vs rvs vs rtii srr se:
    (forall i, atoms_interp rvs vs -∗
    values_interp rtii srr se [NumT (VALTYPE (AtomR (int_type_arep i)) ImCopy ImDrop) (IntT i)] rvs -∗
    ⌜(exists n, vs = [VAL_int32 n] /\ i = I32T) \/ (exists n, vs = [VAL_int64 n] /\ i = I64T)⌝)
    /\
    (forall i, atoms_interp rvs vs -∗
    values_interp rtii srr se [NumT (VALTYPE (AtomR (float_type_arep i)) ImCopy ImDrop) (FloatT i)] rvs -∗
    ⌜(exists n, vs = [VAL_float32 n] /\ i = F32T) \/ (exists n, vs = [VAL_float64 n] /\ i = F64T)⌝)
  .
  Proof.
    split; intros.
    all: iIntros "Hrvs Hvs".
    all: iEval (cbn) in "Hvs"; iEval (cbn) in "Hrvs".
    all: iDestruct "Hvs" as "(%rvss & %Hconcat_rvss & Hrvss)".
    all: iPoseProof (big_sepL2_length with "[$Hrvss]") as "%Hlens_rvss".
    all: iPoseProof (big_sepL2_length with "[$Hrvs]") as "%Hlens_vs_rvs".
    all: simpl in Hlens_rvss.

    (* For some reason I couldn't use length1concat?? *)
    all: assert (Hrvsss: rvss = [rvs]).
    1, 3:
      destruct rvss as [ | rv rvs1 ]; inversion Hlens_rvss;
      symmetry in H0; apply nil_length_inv in H0; subst; simpl;
      by rewrite app_nil_r.
    all: rewrite Hrvsss.
    all: iEval (cbn) in "Hrvss".
    all: iDestruct "Hrvss" as "[Hvs _]".
    all: iPoseProof (value_interp_eq with "Hvs") as "Hvs".
    all: iEval (cbn) in "Hvs".
    all: iDestruct "Hvs" as "(%k & %Hk & Hkindinterp & _)".
    all: inversion Hk.
    all: iEval (cbn) in "Hkindinterp".
    all: iPoseProof "Hkindinterp" as "%Hkindinterp".
    (* Have to dig in and prove rvs is just an integer *)
    all: unfold has_areps in Hkindinterp.
    all: destruct Hkindinterp as (rvs0 & Hrvs0 & Hprimprep).
    all: inversion Hrvs0.
    all: rewrite <- H1 in Hprimprep. (* subst does too much here*)
    all: apply Forall2_length in Hprimprep as Hrvslength.
    all: cbn in Hrvslength.
    all: destruct rvs as [|rv rvs]; inversion Hrvslength.
    all: symmetry in H2; apply nil_length_inv in H2.
    all: subst.
    all: apply Forall2_cons_iff in Hprimprep.
    all: destruct Hprimprep as [Hrv _].

    all: destruct i eqn:Hi; cbn [int_type_arep] in *; cbn [float_type_arep] in *.
    all: cbn in Hrv.
    all: destruct rv; cbn in Hrv; try (inversion Hrv); subst.
    (* Now genuinely new bit: show vs has an integer *)
    (* temporary cleaning this is a mess *)
    all: cbn in Hlens_vs_rvs.
    all: destruct vs as [| v vs]; inversion Hlens_vs_rvs.
    all: symmetry in H0; apply nil_length_inv in H0; subst.
    all: iEval (cbn) in "Hrvs".
    all: iDestruct "Hrvs" as "(%Hv & _)".
    all: subst.
    all: iPureIntro.
    all: try (left; by eexists).
    all: try (right; by eexists).
  Qed.

  Lemma two_rep_in_rvs_vs rvs vs rtii srr se :
    (forall i, atoms_interp rvs vs -∗
    values_interp rtii srr se [NumT (VALTYPE (AtomR (int_type_arep i)) ImCopy ImDrop) (IntT i);
                               NumT (VALTYPE (AtomR (int_type_arep i)) ImCopy ImDrop) (IntT i)] rvs -∗
    ⌜(exists n1 n2, vs = [VAL_int32 n1; VAL_int32 n2] /\ i = I32T) \/
      (exists n1 n2, vs = [VAL_int64 n1; VAL_int64 n2] /\ i = I64T)⌝)
    /\
    (forall i, atoms_interp rvs vs -∗
    values_interp rtii srr se [NumT (VALTYPE (AtomR (float_type_arep i)) ImCopy ImDrop) (FloatT i);
                               NumT (VALTYPE (AtomR (float_type_arep i)) ImCopy ImDrop) (FloatT i)] rvs -∗
    ⌜(exists n1 n2, vs = [VAL_float32 n1; VAL_float32 n2] /\ i = F32T) \/
      (exists n1 n2, vs = [VAL_float64 n1; VAL_float64 n2] /\ i = F64T)⌝)
  .
  Proof.
    split; intros.
    all: iIntros "Hrvs Hvs".
    all: iEval (cbn) in "Hvs"; iEval (cbn) in "Hrvs".
    all: iDestruct "Hvs" as "(%rvss & %Hconcat_rvss & Hrvss)".
    all: iPoseProof (big_sepL2_length with "[$Hrvss]") as "%Hlens_rvss".
    all: iPoseProof (big_sepL2_length with "[$Hrvs]") as "%Hlens_vs_rvs".
    all: simpl in Hlens_rvss.

    all: assert (Hrvsss: exists rv1 rv2, rvss = [rv1; rv2] /\ rvs = rv1 ++ rv2).
    1, 3:
      destruct rvss as [ | rv1 rvss ]; inversion Hlens_rvss;
      exists rv1;
      destruct rvss as [ | rv2 nope ]; inversion H0;
      symmetry in H1; apply nil_length_inv in H1; subst; simpl;
      exists rv2;
      by rewrite app_nil_r.

    all: destruct Hrvsss as (rv1 & rv2 & Hrvsss & Hrvs).
    all: rewrite Hrvsss.
    all: iEval (cbn) in "Hrvss".
    all: iDestruct "Hrvss" as "(Hvs1 & Hvs2 & _)".
    all: iPoseProof (value_interp_eq with "Hvs1") as "Hvs1".
    all: iEval (cbn) in "Hvs1".
    all: iDestruct "Hvs1" as "(%k1 & %Hk1 & Hkindinterp1 & _)".
    all: inversion Hk1.
    all: iEval (cbn) in "Hkindinterp1".
    all: iPoseProof (value_interp_eq with "Hvs2") as "Hvs2".
    all: iEval (cbn) in "Hvs2".
    all: iDestruct "Hvs2" as "(%k2 & %Hk2 & Hkindinterp2 & _)".
    all: inversion Hk2.
    all: iEval (cbn) in "Hkindinterp2".

    all: iPoseProof "Hkindinterp1" as "%Hkindinterp1".
    all: iPoseProof "Hkindinterp2" as "%Hkindinterp2".
    (* Have to dig in and prove rvs1 is just an integer *)
    all: unfold has_areps in Hkindinterp1.
    all: unfold has_areps in Hkindinterp2.
    all: destruct Hkindinterp1 as (rvs1_0 & Hrvs1 & Hprimprep1).
    all: destruct Hkindinterp2 as (rvs2_0 & Hrvs2 & Hprimprep2).
    all: inversion Hrvs1; rewrite <- H2 in Hprimprep1.
    all: inversion Hrvs2; rewrite <- H3 in Hprimprep2.
    all: apply Forall2_length in Hprimprep1 as Hrvs1length.
    all: apply Forall2_length in Hprimprep2 as Hrvs2length.
    all: cbn in Hrvs1length, Hrvs2length; subst.
    all: destruct rvs1_0 as [ | rv1 rvs1_0]; inversion Hrvs1length.
    all: symmetry in H0; apply nil_length_inv in H0; subst.
    all: destruct rvs2_0 as [ | rv2 rvs2_0 ]; inversion Hrvs2length.
    all: symmetry in H0; apply nil_length_inv in H0; subst.

    all: apply Forall2_cons_iff in Hprimprep1.
    all: apply Forall2_cons_iff in Hprimprep2.
    all: destruct Hprimprep1 as [Hrv1 _].
    all: destruct Hprimprep2 as [Hrv2 _].

    (* This is pain. Time to destruct i. *)
    (* I'm not going to destruct the unop just yet bc probably lwp lemma about it *)
    all: destruct i; cbn [int_type_arep] in *; cbn [float_type_arep] in *.
    all: cbn in Hrv1, Hrv2.
    all: destruct rv1; destruct rv2; cbn in Hrv1; cbn in Hrv2; try easy; subst.
    all: rename n into n1; rename n0 into n2.
    (* Now genuinely new bit: show vs has an integer *)
    (* temporary cleaning this is a mess *)
    all: clear Hrvs1 Hrvs2 Hrv1 Hrv2 Hrvs1length Hrvs2length Hk1 Hk2.
    all: cbn in Hlens_vs_rvs.
    all: destruct vs as [| vs1 [ | vs2 nope ]]; inversion Hlens_vs_rvs.
    all: symmetry in H0; apply nil_length_inv in H0; subst.
    all: iEval (cbn) in "Hrvs".
    all: iDestruct "Hrvs" as "(%Hv1 & %Hv2 & _)"; subst.
    all: iPureIntro.
    all: try (left; by repeat eexists).
    all: try (right; by repeat eexists).
  Qed.


  Ltac one_num_set_up τ n :=
    inversion Htypenum; subst;
    unfold τ in *; unfold int_type_type, float_type_type in *;
    unfold type_i64, type_i32, type_f64, type_f32 in *;
    iIntros (? ? ? ? ? ? ?) "%Henv #Hinst #Hctx Hrvs Hvs Hfr Hrt Hf Hrun";
    edestruct (one_rep_in_rvs_vs) as [one_rep_in_rvs_vs_ints one_rep_in_rvs_vs_floats];
    try (iPoseProof (one_rep_in_rvs_vs_ints n with "[$Hrvs] [$Hvs]") as "%Hvs");
    try (iPoseProof (one_rep_in_rvs_vs_floats n with "[$Hrvs] [$Hvs]") as "%Hvs");
    iClear "Hrvs"; iClear "Hvs".
  Ltac two_num_set_up τ n :=
    inversion Htypenum; subst;
    unfold τ in *; unfold int_type_type, float_type_type in *;
    unfold type_i64, type_i32, type_f64, type_f32 in *;
    iIntros (? ? ? ? ? ? ?) "%Henv #Hinst #Hctx Hrvs Hvs Hfr Hrt Hf Hrun";
    edestruct (two_rep_in_rvs_vs) as [two_rep_in_rvs_vs_ints two_rep_in_rvs_vs_floats];
    try (iPoseProof (two_rep_in_rvs_vs_ints n with "[$Hrvs] [$Hvs]") as "%Hvs");
    try (iPoseProof (two_rep_in_rvs_vs_floats n with "[$Hrvs] [$Hvs]") as "%Hvs");
    iClear "Hrvs"; iClear "Hvs".


  Lemma compat_num M F L wt wt' wtf wl wl' wlf ψ e es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    has_instruction_type_num e ψ ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (INum ψ e)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Proof.
    intros fe WT WL Htypenum Htype Hcompile.
    cbn in Hcompile.
    (* There are 8 cases for e in the way it can compile. So, destruct and get 8 cases. *)
    destruct e; cbn in Hcompile; inversion Hcompile; subst; clear Hcompile.
    - rename i0 into unop.

      one_num_set_up τ i.
      destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; subst.

      all: destruct unop; iEval (cbn).
      all: iApply lwp_unop; [cbn; auto | solve_post_lwp_num].

    - rename i0 into binop.

      two_num_set_up τ i.
      destruct Hvs as [(n1 & n2 & Hvs & Hi) | (n1 & n2 & Hvs & Hi)]; subst.

      all: destruct binop; try (destruct s).

      (* Gather up all of the partials, as normal lwp_binop does not apply on them *)
      all: match goal with
         | |- context [ (_ (_ I32T) (_ (_ (DivI SignU))) ) ] =>
             destruct (Wasm_int.Int32.idiv_u n1 n2) eqn:HPartialResult
         | |- context [ (_ (_ I32T) (_ (_ (DivI SignS))) ) ] =>
             destruct (Wasm_int.Int32.idiv_s n1 n2) eqn:HPartialResult
         | |- context [ (_ (_ I32T) (_ (_ (RemI SignU))) ) ] =>
             destruct (Wasm_int.Int32.irem_u n1 n2) eqn:HPartialResult
         | |- context [ (_ (_ I32T) (_ (_ (RemI SignS))) ) ] =>
             destruct (Wasm_int.Int32.irem_s n1 n2) eqn:HPartialResult
         | |- context [ (_ (_ I64T) (_ (_ (DivI SignU))) ) ] =>
             destruct (Wasm_int.Int64.idiv_u n1 n2) eqn:HPartialResult
         | |- context [ (_ (_ I64T) (_ (_ (DivI SignS))) ) ] =>
             destruct (Wasm_int.Int64.idiv_s n1 n2) eqn:HPartialResult
         | |- context [ (_ (_ I64T) (_ (_ (RemI SignU))) ) ] =>
             destruct (Wasm_int.Int64.irem_u n1 n2) eqn:HPartialResult
         | |- context [ (_ (_ I64T) (_ (_ (RemI SignS))) ) ] =>
             destruct (Wasm_int.Int64.irem_s n1 n2) eqn:HPartialResult
          (* Note: this case solves all non-partial binops *)
         | _ => iApply lwp_binop;
                [cbn; (try rewrite HPartialResult); cbn; auto | solve_post_lwp_num]
           end.
      (* This solves the goals where the result actually exists *)
      all: match type of HPartialResult with
           | (_ = Some _) => iApply lwp_binop;
                [cbn; (try rewrite HPartialResult); cbn; auto | solve_post_lwp_num]
           | _ => idtac
           end.

      (* Everything remaining is partial binop results *)
      all: iEval (cbn).
      all: iApply lwp_binop_failure; [cbn; unfold option_map; by rewrite HPartialResult |].
      all: iFrame.
      all: by iEval (cbn).

    - rename i0 into testop.

      one_num_set_up τ i.
      destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; subst.

      all: destruct testop; iEval (cbn).
      + iApply lwp_testop_i32; [cbn; auto | solve_post_lwp_num].
      + iApply lwp_testop_i64; [cbn; auto | solve_post_lwp_num].

    - rename i0 into relop.

      two_num_set_up τ i.
      destruct Hvs as [(n1 & n2 & Hvs & Hi) | (n1 & n2 & Hvs & Hi)]; subst.

      all: destruct relop; iEval (cbn).
      all: iApply lwp_relop; [cbn; auto | solve_post_lwp_num].

    - rename f0 into unop.

      (* one float set up *)
      one_num_set_up τ f.
      destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; subst.

      all: destruct unop; iEval (cbn).
      all: iApply lwp_unop; [cbn; auto | solve_post_lwp_num].

    - rename f0 into binop.

      two_num_set_up τ f.
      destruct Hvs as [(n1 & n2 & Hvs & Hi) | (n1 & n2 & Hvs & Hi)]; subst.

      (* Float binops aren't partial! *)
      all: destruct binop.
      all: iApply lwp_binop; [cbn; auto | solve_post_lwp_num].

    - rename f0 into relop.

      two_num_set_up τ f.
      destruct Hvs as [(n1 & n2 & Hvs & Hi) | (n1 & n2 & Hvs & Hi)]; subst.

      all: destruct relop; iEval (cbn).
      all: iApply lwp_relop; [cbn; auto | solve_post_lwp_num].

    - (* Conversion operations!  *)
      inversion Htypenum; subst.
      rename Htypenum into Htypecvt; rename H0 into Htypenum.

      destruct c.
      all: cbn [translate_cvt_op].
      + one_num_set_up type_i64 I64T.
        destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; try (inversion Hi); subst.

        iEval (cbn).
        iApply lwp_cvtop_convert; cbn; auto.
        solve_post_lwp_num.
      + one_num_set_up type_i64 I32T.
        destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; try (inversion Hi); subst.

        destruct s.
        all: iEval (cbn).
        all: iApply lwp_cvtop_convert; cbn; auto.
        all: solve_post_lwp_num.
      + one_num_set_up type_i64 f.
        destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; try (inversion Hi); subst.

        all: match goal with
             | |- context [ F32T ] =>
                 destruct (cvt (translate_int_type i) (Some (translate_sign s)) (VAL_float32 n))
                       eqn:HPartialResult
             | |- context [ F64T ] =>
                 destruct (cvt (translate_int_type i) (Some (translate_sign s)) (VAL_float64 n))
                       eqn:HPartialResult
             end.
        all: match type of HPartialResult with
               (* Actual results! *)
             | (_ = Some _) =>
                 destruct s; destruct i; iEval (cbn);
                 iApply lwp_cvtop_convert; cbn; auto;
                 try (unfold cvt in HPartialResult; cbn in *;
                      by rewrite HPartialResult); auto;
                 cbn in HPartialResult; unfold option_map in HPartialResult;
                 cbn in HPartialResult;
                 match type of HPartialResult with
                 | (match ?x with |Some _=>_ |None=>_ end = _) =>
                     destruct x; cbn in HPartialResult; inversion HPartialResult
                 end;
                 solve_post_lwp_num
            (* Partials! *)
            | (_ = None) => idtac
             end.
        all: iApply lwp_cvtop_convert_failure; [cbn; unfold option_map; by rewrite HPartialResult | cbn; auto |].
        all: iFrame; by iEval (cbn).
      + one_num_set_up type_i64 F64T.
        destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; try (inversion Hi); subst.

        iEval (cbn).
        iApply lwp_cvtop_convert; cbn; auto.
        solve_post_lwp_num.
      + one_num_set_up type_i64 F32T.
        destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; try (inversion Hi); subst.

        iEval (cbn).
        iApply lwp_cvtop_convert; cbn; auto.
        solve_post_lwp_num.
      + one_num_set_up type_i64 i.
        destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; try (inversion Hi); subst.

        all: match goal with
             | |- context [ I32T ] =>
                 destruct (cvt (translate_float_type f) (Some (translate_sign s)) (VAL_int32 n))
                       eqn:HPartialResult
             | |- context [ I64T ] =>
                 destruct (cvt (translate_float_type f) (Some (translate_sign s)) (VAL_int64 n))
                       eqn:HPartialResult
             end.
        all: match type of HPartialResult with
             | (_ = Some _) =>
                 destruct s; destruct f; iEval (cbn);
                 iApply lwp_cvtop_convert; cbn; auto;
                 try (unfold cvt in HPartialResult; cbn in *; by rewrite HPartialResult); auto;
                 cbn in HPartialResult; inversion HPartialResult;
                 solve_post_lwp_num
             | (_ = None) => idtac
             end.
         all: iApply lwp_cvtop_convert_failure; [cbn; unfold option_map; by rewrite HPartialResult | cbn; auto |].
         all: iFrame; by iEval (cbn).
      + (* We'll need to split into cases again. This was the only thing that worked for some reason *)
        destruct n eqn:Hn;
          [ destruct i eqn:Hii; [one_num_set_up type_i64 I32T | one_num_set_up type_i64 I64T ] |
            destruct f eqn:Hf; [one_num_set_up type_i64 F32T | one_num_set_up type_i64 F64T ]  ].

        all: destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; try (inversion Hi); subst.

        all: iEval (cbn).
        all: iApply lwp_cvtop_reinterpret; cbn; auto.
        all: solve_post_lwp_num.
  Qed.

  Lemma compat_num_const M F L wt wt' wtf wl wl' wlf n ν es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [] [num_type_type ν] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (INumConst ψ n)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Proof.
    intros fe WT WL ψ Hok Hcompile. cbn in Hcompile.
    (* Immediately, we must destruct ν *)
    destruct ν; cbn in Hcompile; inversion Hcompile.
    (* From here on out, we have an integer case and a float case (until we split
       further into 32/64 *)

    (* Some basic intros, unfolds, proving empty lists empty *)
    all: unfold have_instruction_type_sem.
    all: iIntros (? ? ? ? ? ? ?) "Henv Hinst Hctx Hrvs Hvs Hfr Hrt Hf Hrun".
    all: iEval (cbn) in "Hrvs"; iEval (cbn) in "Hvs".
    all: iDestruct "Hvs" as "(%rvss & %Hconcat & Hrvss)".
    all: iPoseProof (big_sepL2_length with "[$Hrvss]") as "%Hlens_rvss";
      iPoseProof (big_sepL2_length with "[$Hrvs]") as "%Hlens_rvs_vs".
    all: cbn in Hlens_rvss; destruct rvss, os; cbn in Hconcat, Hlens_rvss;
      try congruence.
    all: cbn in Hlens_rvs_vs; destruct vs; cbn in Hlens_rvs_vs; try congruence.

    (* Now it's time to apply lenient_wp *)
    all: iApply lenient_wp_value.
    (* In int case, instantiate value with int value. Float in float case *)
    (* Automatics don't work great here *)
    1: by instantiate (1 := (immV [(value_of_Z (translate_num_type (IntT i)) n)])%I).
    2: by instantiate (1 := (immV [(value_of_Z (translate_num_type (FloatT f)) n)])%I).

    all: unfold denote_logpred; iFrame; iEval (cbn).
    (* Split into 32/64 cases *)
    1: destruct i.
    3: destruct f.
    all: iEval (cbn).
    (* automatic exists don't work well here unfortunately *)
    1: iExists [I32A (Wasm_int.Int32.repr n)].
    2: iExists [I64A (Wasm_int.Int64.repr n)].
    3: iExists [F32A (Wasm_float.FloatSize32.of_bits (Integers.Int.repr n))].
    4: iExists [F64A (Wasm_float.FloatSize64.of_bits (Integers.Int64.repr n))].
    all: iEval (cbn).
    all: iSplitL; try iSplitL; auto.
    (* once again, automatic exists don't work great *)
    1: iExists [[I32A (Wasm_int.Int32.repr n)]].
    2: iExists [[I64A (Wasm_int.Int64.repr n)]].
    3: iExists [[F32A (Wasm_float.FloatSize32.of_bits (Integers.Int.repr n))]].
    4: iExists [[F64A (Wasm_float.FloatSize64.of_bits (Integers.Int64.repr n))]].
    all: iEval (cbn); iSplitR; auto; iSplitL; auto.
    (* Dig into value interp a bit, then smooth sailing *)
    all: iApply value_interp_eq; iEval (cbn).
    all: iExists _.
    all: iSplitR; auto; iSplitL; auto; iEval (cbn).
    all: iPureIntro.
    all: eexists; split; auto.
    all: apply Forall2_cons_iff.
    all: split; try (by apply Forall2_nill).
    all: done.
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

  Lemma compat_block M F L L' wt wt' wtf wl wl' wlf τs1 τs2 es es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let F' := F <| fc_labels ::= cons (τs2, L') |> in
    let ψ := InstrT τs1 τs2 in
    has_instruction_type_ok F ψ L' ->
    (forall wt wt' wtf wl wl' wlf es',
        let fe' := fe_of_context F' in
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        run_codegen (compile_instrs mr fe' es) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instruction_type_sem rti sr mr M F' L WT WL (to_e_list es') ψ L') ->
    run_codegen (compile_instr mr fe (IBlock ψ L' es)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L'.
  Proof.
    intros fe F' WT WL ψ Hok IH Hrun.
    cbn [compile_instr] in Hrun.
    inv_cg_bind Hrun ρ wt0 wt0' wl0 wl0' es_nil es0' Hrun1 Hrun2.
    subst wt' wl' es'.
    cbn in Hrun1.
    inv_cg_try_option Hrun1.
    do 2 rewrite app_nil_r in Hrun2.
    subst wt0 wl0 es_nil.
    destruct (prelude.translate_types (fc_type_vars F) τs1) as [ts1|] eqn:Hts1; last done.
    destruct (prelude.translate_types (fc_type_vars F) τs2) as [ts2|] eqn:Hts2; last done.
    simpl in Heq_some.
    inversion Heq_some; subst ρ; clear Heq_some.
    inv_cg_bind Hrun2 ρ wt0 wt1 wl0 wl1 es1 es0 Hrun1 Hrun2.
    destruct ρ, u.
    inv_cg_emit Hrun2.
    rewrite app_nil_r in Hwt_app_eq.
    rewrite app_nil_r in Hwl_app_eq.
    subst wl1 es0 wt0' wl0' wt1 es0'.
    clear Hretval.
    apply run_codegen_capture in Hrun1 as [Hrun1 ->].
    eapply IH in Hrun1.
    unfold have_instruction_type_sem.
(*    iSimpl. *)
    iIntros (se inst lh fr rvs vs θ) "%Henv #Hinst (%Hlhbase & %Hlengthlh & %Hlh & Hlabs)".
    iIntros "Hrvs (%vss & -> & Hvss) (%rvssl & %vssl & %vswl & -> & %Hres & Hvssl) Htok Hfr Hrun".
    iDestruct (translate_types_length with "Hvss") as "%Hlenvss" => //.
    iDestruct (big_sepL2_length with "Hrvs") as "%Hlenrvs". 
    unfold lenient_wp.
    iApply (wp_block with "Hfr Hrun").
    { apply v_to_e_is_const_list. }
    { done. } 
    { rewrite v_to_e_length Hlenvss.
      rewrite length_concat in Hlenrvs. done. }
    { done. }
    iIntros "!> Hfr Hrun".
    iApply (wp_label_bind with "[-]").
    2:{ iPureIntro.
        instantiate (2 := []).
        instantiate (2 := []).
        instantiate (2 := length ts2).
        instantiate (2 := []).
        rewrite /lfilled /lfill /= app_nil_r.
        done. }
    unfold have_instruction_type_sem in Hrun1.
    
(*    simpl in Hrun1. *)
    iApply (wp_wand with "[-]"). 
    { iApply (Hrun1 with "[] Hinst [Hlabs] [$Hrvs] [$Hvss] [$Hvssl] [$Htok] Hfr Hrun") => //.
      - instantiate (1 := lh_plug (LH_rec [] (length ts2) [] (LH_base [] []) []) lh).
        repeat (iSplit; first iPureIntro).
        + apply base_is_empty_plug => //. 
        + apply length_lholeds_app => //=.
          split; last done.
          iIntros (rvs) "(%vss0 & -> & Hvss0)".
          iDestruct (translate_types_length with "Hvss0") as "%Hlenvss0" => //.
          iPureIntro.
          rewrite length_concat //.
        + apply lholed_valid_plug => //.
        + Opaque continuation_interp.
          simpl. 
          iSplitR. 
          * Transparent continuation_interp.
            unfold continuation_interp.
            iExists _,_,_,_,_,_.
            rewrite lh_depth_plug /= Nat.add_sub.
            repeat (iSplit; first iPureIntro).
            -- apply get_layer_plug_precise => //.
            -- done.
            -- rewrite lh_plug_minus => //.
            -- iIntros "!>" (fr vs0 rvs θ0) "Hrvs (%vss0 & -> & Hvss0) (%rvssl0 & %vssl0 & %vswl0 & -> & %Hres0 & Hvssl0) Htok Hfr Hrun".
               rewrite app_nil_r app_nil_r /=.
               iExists _.
               unfold lenient_wp.
               iApply wp_value.
               { apply of_to_val.
                 fold (of_val (immV vs0)).
                 apply to_of_val. }
               unfold denote_logpred.
               iFrame.
               iSplit.
               ++ iExists _. done.
               ++ done.
          * iApply (big_sepL_impl with "Hlabs").
            iIntros "!>" (k x Hk).
            destruct x.
            iIntros "Hcont".
(*            unfold continuation_interp. *)
            iDestruct "Hcont" as (j ?????) "(%Hlayer & %Hdepth & %Hminus & #H)".
            iExists _,_,_,_,_,_.
            rewrite lh_depth_plug.
            replace (lh_depth lh + 1 - S (S k)) with (lh_depth lh - S k); last lia.           
            repeat (iSplit; first iPureIntro).
            -- apply get_layer_plug_shallow => //=.
               replace (lh_depth lh + 1 - S (S k)) with (lh_depth lh - S k); last lia.
               done.
            -- simpl.
               replace (lh_depth lh + 1 - S (S k)) with (lh_depth lh - S k); last lia.
               exact Hdepth.
            -- apply lh_minus_plug => //.
            -- done. 
      - iExists _. done. 
    } 
    clear Hrun1 IH. 
    iIntros (v) "H".
    unfold denote_logpred.
    iSimpl in "H".
    iDestruct "H" as (f) "(Hf & _ & Hv)".
    iIntros (LI HLI).
    apply lfilled_Ind_Equivalent in HLI.
    inversion HLI; subst.
    inversion H8; subst.
    iSimpl. rewrite seq.cats0.
    destruct v.
    - (* immV case *)
      iSimpl in "Hv".
      iDestruct "Hv" as "(Hrun & Hframe & Hframeinv)".
      iApply (wp_wand with "[Hf Hrun]").
      { iApply (wp_label_value with "Hf Hrun"); first by apply to_of_val.
        by instantiate (1 := λ v, ⌜ v = immV _ ⌝%I). }
      iIntros (v) "[[-> Hrun] Hf]".
      iFrame. 
    - (* trapV case *)
      iSimpl in "Hv".
      iDestruct "Hv" as "[Hbail _]".
      iApply (wp_wand with "[Hf]").
      { iApply (wp_label_trap with "Hf") => //.
        by instantiate (1 := λ v, ⌜ v = trapV ⌝%I). }
      iIntros (v) "[-> Hf]".
      iFrame. 
    - (* brV case *)
      iSimpl in "Hv".
      iDestruct "Hv" as "[Hrun Hbr]".
      iDestruct (br_interp_eq with "Hbr") as "Hbr".
      unfold br_interp0.
      iSimpl in "Hbr".
      iDestruct "Hbr" as (k p lh' lh'' τs es0 es1 es2 vs0 vs1 rvs)
                           "(%Hbaselh0 & %Hdepthlh0 & %Hlab & %Hlayer & %Hdepthlh'' & %Hminus & Hrvs & (%vss0 & -> & Hvss0) & Hbr)".
      destruct (decide ( i = p)).
      + (* case 1: the br targets this exact label *)
        iClear "Hbr".
        subst p. 
        destruct (pull_base_l_drop_len lh0 (length (vs0 ++ vs1) - length ts2)) eqn:Hpb.
        unfold of_val. 
        erewrite vfill_pull_base_l_take_len.
        2:{ exact Hpb. }
        pose proof (vfill_to_lfilled v ((v_to_e_list l0) ++ [AI_basic (BI_br i)])) as [Hle Hfill].
        erewrite <- lh_depth_pull_base_l_take_len in Hfill;[|eauto]. 
        rewrite -e in Hfill.
        rewrite -e Nat.sub_diag /= in Hlab.
        rewrite -e Nat.sub_diag /= in Hlayer.
        rewrite lh_depth_plug /= in Hlayer.
        rewrite Nat.add_sub in Hlayer.
        inversion Hlab; subst τs2; clear Hlab.
        iDestruct (translate_types_length with "Hvss0") as "%Hlenvss0" => //.
        iDestruct (big_sepL2_length with "Hrvs") as "%Hlenrvs0". 
        iApply (wp_br with "Hf Hrun").
        3: exact Hfill.
        * apply v_to_e_is_const_list. 
        * rewrite length_fmap.
           eapply length_pull_base_l_take_len in Hpb;[|eauto]. rewrite Hpb.
           assert (length (vs0 ++ vs1) >= length ts2);[|lia].
           rewrite length_app Hlenvss0. rewrite length_concat in Hlenrvs0. 
           rewrite -Hlenrvs0. lia. 
        * iNext. iIntros "Hf Hrun".
           rewrite app_nil_r.
           iApply wp_value.
           { apply of_to_val. apply to_val_v_to_e. }
           iSimpl. iFrame.
           admit. 
(*           iSplitR. 
           { admit. }
           iExists _,_. iSplit; first done.
           iSplitR; last iSplitR. 
           -- iExists _,_. done. 
           -- iExists _,_. 
              iSplit; first done.
              iSplit; first done. 
              iSplit; first done.
              admit.
           -- iSimpl. iExists _.
              admit. *)
      + (* case 2: the br is still stuck *)
        assert (i > p) as Hip.
        { destruct (vfill_to_lfilled lh0 []) as [? _].
          rewrite Hdepthlh0 in H.
          lia. } 
        destruct i; first lia.
        destruct (vh_decrease lh0) eqn:Hlh0.
        2:{ exfalso. clear - Hip Hlh0 Hdepthlh0.
            eapply vh_depth_can_decrease => //.
            by rewrite Hdepthlh0. } 
        iApply wp_value.
        { apply of_to_val. 
          simpl.
          unfold RichWasm.iris.language.iris.iris.to_val.
          simpl.
          rewrite seq.cats0.
          specialize (to_of_val (brV lh0)) as H.
          simpl in H.
          unfold RichWasm.iris.language.iris.iris.to_val in H.
          destruct (merge_values_list _) ; try by exfalso.
          inversion H; subst v0; clear H.
          rewrite Hlh0. 
          done. } 
        iSimpl.
        iFrame.
        rewrite br_interp_eq.
        rewrite /br_interp0 /=.
        rewrite lh_depth_plug /= in Hlayer.
        apply get_layer_plug_shallow_inv in Hlayer as (lhnew & Hlayer & ->).
        2:{ clear - Hip.
            assert (S i - p > 0); first lia.
            assert (lh_depth lh > 0).
            { admit. } 
            lia. }
        iExists _, (S p).
        repeat iExists _.
        iDestruct (translate_types_length with "Hvss0") as "%Hlenvss0" => //.
        { admit. } 
        iFrame "Hvss0".
        repeat (iSplit; first iPureIntro).
        -- apply get_base_vh_decrease in Hlh0.
           rewrite Hlh0. done.
        -- apply lh_of_vh_decrease in Hlh0.
           rewrite -Hlh0 in Hdepthlh0.
           rewrite Hdepthlh0. done.
        -- destruct (S i - p) eqn:Hip'; first lia. 
           simpl in Hlab.
           replace (S i - S p) with n0; last lia.
           done.
        -- rewrite <- Hlayer.
           f_equal. lia.
        -- rewrite lh_depth_plug /= in Hdepthlh''.
           instantiate (1 := lh'').
           lia.
        -- rewrite lh_depth_plug /= in Hdepthlh''.
           admit. (* manipulate minus *)
        -- iFrame.
           iSplit; first done.
           iIntros (fr θ0) "Hfr H1 H2".
           iDestruct ("Hbr" with "Hfr H1 H2") as "H".
           assert (lh_depth lhnew = i - p).
           { (* should be given by Hlayer, just need to convince lia *)
             admit. }
           
             iIntros (LI HLI').
             iApply (wp_br_ctx_shift_inv with "[] [H]"); last first.
             ++ iPureIntro.
                apply get_layer_depth in Hlayer.
                rewrite H in HLI'.
                exact HLI'.
             ++ iIntros "Hrun".
                rewrite lh_depth_plug H /=.
                replace (lh_plug (LH_rec [] (length ts2) [] (LH_base [] []) []) lhnew) with (push_base lhnew (length ts2) [] [] []).
                2:{ (* should be easy *) admit. }
                replace (S (i - p + 1)) with (S (S (i - p))); last lia.
                replace (S (i - p)) with (S i - p); last lia.
                iFrame.
             ++ admit.
             ++ replace (lh_depth lh + 1 - S (S i - p))
                  with (lh_depth lh - S (i - p)) in Hlayer; last lia. 
                eapply get_layer_lookup_lh_lengths in Hlayer => //.
                2:{ replace (S i - p) with (S (i - p)) in Hlab; last lia.
                    simpl in Hlab. done. }
                admit. (* massage get_layer_lookup_lh_lengths and Hlenvss0 *)
             ++ done.
             ++ apply v_to_e_is_const_list.
    - (* retV case *)
      iApply wp_value.
      { apply of_to_val.
        unfold RichWasm.iris.language.iris.iris.to_val.
        simpl.
        specialize (to_of_val (retV s)) as H.
        simpl in H.
        unfold RichWasm.iris.language.iris.iris.to_val in H.
        destruct (merge_values_list _); try by exfalso.
        inversion H; subst v; clear H.
        done. }
      iSimpl.
      iSimpl in "Hv". 
      iDestruct "Hv" as "(Hrun & %vs0 & %vs' & %rvs & %Hgetbase & Hrvs & (%vss0 & -> & Hvss0) & Hret)".
      iFrame.
      iExists _. iSplit; first done. iSplit; first done.
      iIntros (fr fr') "Hf Hrun".
      admit. (* generalise s in IH? Check out interp_return_label in iris-wasm *)
    - iSimpl in "Hv". iDestruct "Hv" as "[_ ?]" => //.
  Admitted. 

  Lemma compat_loop M F L wt wt' wtf wl wl' wlf es es' τs1 τs2 :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let F' := F <| fc_labels ::= cons (τs1, L) |> in
    let ψ := InstrT τs1 τs2 in
    has_instruction_type_ok F ψ L ->
    (forall wt wt' wtf wl wl' wlf es',
        let fe' := fe_of_context F' in
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        run_codegen (compile_instrs mr fe' es) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instruction_type_sem rti sr mr M F' L WT WL (to_e_list es') ψ L) ->
    run_codegen (compile_instr mr fe (ILoop ψ es)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ite M F L L' wt wt' wtf wl wl' wlf es1 es2 es' τs1 τs2 :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let F' := F <| fc_labels ::= cons (τs2, L') |> in
    let ψ := InstrT (τs1 ++ [type_i32]) τs2 in
    has_instruction_type_ok F ψ L' ->
    (forall wt wt' wtf wl wl' wlf es',
        let fe := fe_of_context F' in
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        run_codegen (compile_instrs mr fe es1) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instruction_type_sem rti sr mr M F' L WT WL (to_e_list es') (InstrT τs1 τs2) L') ->
    (forall wt wt' wtf wl wl' wlf es',
        let fe := fe_of_context F' in
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        run_codegen (compile_instrs mr fe es2) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instruction_type_sem rti sr mr M F' L WT WL (to_e_list es') (InstrT τs1 τs2) L') ->
    run_codegen (compile_instr mr fe (IIte ψ L' es1 es2)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L'.
  Proof.
    intros fe WT WL F' ψ Hok Hthen Helse Hcodegen.
    iIntros (se inst lh fr rvs vs θ Henv) "#Hinst #Hctxt Hrvs Hvss Hvsl Hrt Hfr Hrun".
    iDestruct "Hvss" as (vss) "(-> & Hvss)".
    (*
    iDestruct "Hvsl" as (vsl' vswl') "(-> & %Hlocs & %Hrestype & Hlocs)".
    iDestruct "Hfrinv" as "[Htok Hfrinv]".
    apply Forall2_length in Hlocs as Hlenvsl.
    iDestruct (big_sepL2_length with "Hlocs") as "%Hlenvsl'".
    rewrite length_map in Hlenvsl'.
    rewrite map_app.
    iDestruct (big_sepL2_app_inv_l with "Hvss") as (vss1 vssi32) "(-> & Hvss1 & Hvssi32)".
    destruct vssi32; first done.
    iDestruct "Hvssi32" as "[Hvssi32 Hvoid]".
    destruct vssi32; last done.
    iClear "Hvoid".
    iDestruct (value_interp_eq with "Hvssi32") as "Hvssi32".
    iSimpl in "Hvssi32".
    iDestruct "Hvssi32" as (κ) "(%Heq & Hκ & _)".
    inversion Heq; subst κ; clear Heq.
    iSimpl in "Hκ".
    iDestruct "Hκ" as "%Hκ".

(*    destruct vswl; last by inversion Hrestype. *)
    destruct o as [|v vs]; inversion Hκ; subst; clear Hκ. 
    destruct vs as [|v' vs]; inversion H4; subst; clear H4.
    unfold primitive_rep_interp in H2.
    destruct H2 as [n ->].

(*    inversion Hok; subst.
    destruct H as [Hτs1 Hτs2].
    apply Forall_app in Hτs1 as [Hτs1 Hi32].
    inversion Hi32; subst.
    inversion H2; subst.
    inversion H; subst.
    inversion H4; subst. *)
    


    replace (compile_instr mr fe (IIte ψ L' es1 es2))
      with (compile_ite fe ψ (compile_instrs mr fe es1) (compile_instrs mr fe es2))
      in Hcodegen; last done.
    remember (compile_instrs mr fe es1) as compes1.
    remember (compile_instrs mr fe es2) as compes2.
    Opaque if_c. 
    simpl in Hcodegen. 


    inv_cg_bind Hcodegen ρ1 wl1 wl1' es_nil es1' Htype_rep Hcodegen.
    inv_cg_try_option Htype_rep.
    subst wl1 es_nil.
    rewrite app_nil_l in Hes_app_eq; subst es1'. 
    inv_cg_bind Hcodegen ρ2 wl2 wl2' es_nil es1' Htype_rep Hcodegen.
    inv_cg_try_option Htype_rep.
    subst wl2 es_nil.
    rewrite app_nil_l in Hes_app_eq; subst es1'. 

    inv_cg_bind Hcodegen ρ3 wl3 wl3' es_nil es1' Hcodegen Hend.
    rewrite /run_codegen /= in Hend.
    inversion Hend; subst wl3' es1'; clear Hend.
    rewrite app_nil_r in Hes_app_eq; subst es_nil.
    destruct ρ3.
    destruct u, u0. 
    
    Transparent if_c.
    rewrite /if_c in Hcodegen.
    subst wl1' wl' wl2'.
    rewrite !app_nil_r !app_nil_l.

    inv_cg_bind Hcodegen ρ3 wl1 wl1' es_nil es1' Hes1 Hcodegen.
    destruct ρ3. destruct u.
    subst es'.
    inv_cg_bind Hcodegen ρ3 wl2 wl2' es_nil' es2' Hes2 Hcodegen.
    destruct ρ3. destruct u.
    subst es1'.
    rewrite /run_codegen /= in Hcodegen.
    inversion Hcodegen; subst wl1' wl2' es2'; clear Hcodegen.
    apply run_codegen_capture in Hes1 as [Hes1 ->].
    apply run_codegen_capture in Hes2 as [Hes2 ->].

(*    unfold compile_instrs in Hthen.
    destruct u, u0. *)
    subst compes1 compes2.
    rewrite !app_nil_r in Hes1.
    rewrite !app_nil_r in Hes2.
    apply (Hthen _ _ (wl2 ++ wlf)) in Hes1; eauto.
    apply (Helse _ _ wlf) in Hes2; eauto.
    rewrite <- !app_assoc in Hes2.

    rewrite removelast_last in Heq_some.

    iDestruct (big_sepL2_length with "Hvss1") as "%Hlen1".
    (* iDestruct (big_sepL2_length with "Hvss0") as "%Hlen0". *)
    rewrite length_map in Hlen1.
(*    rewrite length_map in Hlen0. *)
    iDestruct (translate_types_length_subst _ _ _ _ _ _ _ _ Heq_some with "Hvss1") as "%Hlen1'".
    
    
    iSimpl.
    subst wl3.
    rewrite -> !app_nil_r in *.
    rewrite -> !app_nil_l in *.
    unfold lenient_wp.
    rewrite concat_app.
    rewrite -v_to_e_cat.
    rewrite cat_app -app_assoc.
    iSimpl.
    iApply wp_wasm_empty_ctx.
    rewrite <- (app_assoc _ [AI_basic _]).
    rewrite <- app_assoc in Hrestype.
    cbn.
    rewrite (separate2 (AI_basic _)).
    iApply wp_base_push; first by apply v_to_e_is_const_list.
    destruct (value_eq_dec (VAL_int32 n) (VAL_int32 (Wasm_int.int_zero i32m))).
    - (* n is false *)
      inversion e; subst.
      iApply (wp_if_false_ctx with "Hfr Hrun") => //.
      iIntros "!> Hfr Hrun".
      iApply wp_base_pull.
      iSimpl.
      iApply wp_wasm_empty_ctx.
      iApply (wp_block with "Hfr Hrun") => //.
      { apply v_to_e_is_const_list. }
      { rewrite v_to_e_length.
        rewrite length_concat.
        done. }
      iIntros "!> Hfr Hrun".
      iApply (wp_label_bind with "[-]").
      2:{ iPureIntro. instantiate (5 := []).
          rewrite /lfilled /lfill /= app_nil_r //. }
      iApply (wp_wand with "[-]").
      + iApply (Hes2 with "[%] Hinst [Hctxt] [$Hvss1] [$Hlocs] [$Htok] Hfr Hrun"); first assumption; cycle 1.
        * done.
        * iExists _; done.
        * iExists _, _. done.
        * instantiate (1 := (* push_base lh (length ρ2) [] [] []). *)
                         lh_plug (LH_rec _ _ _ (LH_base _ _) _) lh).  
          iDestruct "Hctxt" as "(%Hbase & %Hlength & %Hvalid & Hconts)".
          repeat iSplitR.
          all: try iPureIntro.
          -- apply base_is_empty_plug => //.
          -- eapply length_lholeds_app => //.
             split => //. 
             iIntros (?) "(%vss & -> & Hvss)".
             iDestruct (translate_types_length with "Hvss") as "%H".
             ++ exact Heq_some0.
             ++ rewrite length_concat -H. done. 
          -- apply lholed_valid_plug => //=.
             split => //. 
             apply v_to_e_is_const_list.
          -- iSimpl. iSplitR; last first. 
             ++ iApply (big_sepL_impl with "Hconts").
                iIntros "!>" (k [ts ctx] Hk) "#Hcont".
                unfold continuation_interp.
                iDestruct "Hcont" as (j es0 es es' lh' lh'') "(%Hlayer & %Hdepth & %Hminus & #Hcont)".
                iExists _,_,_,_,_,_.
                repeat iSplitR.
                1-3: iPureIntro.
                ** rewrite lh_depth_plug. simpl.
                   replace (lh_depth lh + 1 - S (S k)) with (lh_depth lh - S k); last lia.
                   apply get_layer_plug_shallow.
                   exact Hlayer. 
                ** rewrite lh_depth_plug. simpl.
                   replace (lh_depth lh + 1 - S (S k)) with
                     (lh_depth lh - S k); first exact Hdepth.
                   lia. 
                ** apply lh_minus_plug. done.
                ** iIntros "!>" (vs fr) "Hvs Hfr Hrun Hframe Hframe'".
                   iDestruct ("Hcont" with "Hvs Hfr Hrun Hframe Hframe'") as (τs') "Hexp".
                   iExists τs'.
                   done.

             ++ iExists _, _, _, _,_, _.
               iSplit.
               { iPureIntro.
                 rewrite lh_depth_plug /= Nat.add_sub.
                 apply get_layer_plug_precise => //. } 
               iSplit; first iSimpl.
               { (* instantiate (5 := lh). *)
                 rewrite lh_depth_plug /= Nat.add_sub //. }
               iSplit.
               { iPureIntro. 
                 erewrite lh_plug_minus => //. }
               iIntros "!>" (vs fr) "Hvs Hfr Hrun Hframe Hframe'".
               iExists _.
               unfold expr_interp.
               iSimpl.
               unfold lenient_wp.
               do 3 instantiate (2 := []).
               rewrite app_nil_r app_nil_r /=.

               iApply wp_value.
               { apply of_to_val. unfold language.to_val.
                 simpl. apply to_val_v_to_e. } 
               rewrite /denote_logpred /=.
               iFrame.
(*             iApply (big_sepL_impl with "Hconts").
             iIntros "!>" (k [ts ctx] Hk) "#Hcont".
             unfold continuation_interp.
             iDestruct "Hcont" as (j es0 es es' lh' lh'') "(%Hlayer & %Hdepth & %Hminus & #Hcont)".
             iExists _,_,_,_,_,_.
             repeat iSplitR.
             1-3: iPureIntro.
             ++ rewrite lh_depth_plug. simpl.
                replace (lh_depth lh + 1 - S (S k)) with (lh_depth lh - S k); last lia.
                apply get_layer_plug_shallow.
                exact Hlayer. 
             ++ rewrite lh_depth_plug. simpl.
                replace (lh_depth lh + 1 - S (S k)) with
                  (lh_depth lh - S k); first exact Hdepth.
                lia. 
             ++ apply lh_minus_plug. done.
             ++ iIntros "!>" (vs fr) "Hvs Hfr Hframe".
                iDestruct ("Hcont" with "Hvs Hfr Hframe") as (τs') "Hexp".
                iExists τs'.
                done.
        * done.
        * iExists _, _. iSplit; first done. iSplit; first done.
          rewrite <- !app_assoc in Hrestype.
          iPureIntro. exact Hrestype. *)

      + iIntros (v) "H".
        rewrite /denote_logpred /lp_noframe /=.
        iIntros (LI HLI).
        apply lfilled_Ind_Equivalent in HLI; inversion HLI; subst.
        cbn.
        inversion H8; subst.
        clear HLI H7 H8 H1.
        iSimpl.

        destruct v.
        * (* immV case *)
          iDestruct "H" as "(%fr & Hfr & (Htok & _) & (%vssl & %vswl0 & %Heq & %Hlocs' & %Hrestype' & Hlocs) & Hrun & %vss & -> & Hvss)".
          subst fr.
          iApply (wp_wand with "[Hfr Hrun]").
          { iApply (wp_label_value with "Hfr Hrun").
            - rewrite seq.cats0. rewrite to_of_val. done.
            - by instantiate (1 := λ v, ⌜ v = immV _ ⌝%I). }
          iIntros (v) "[[-> Hrun] Hfr]".
          iFrame.
          iSplit. 
          -- iExists _,_. done.
          -- iSplit; last done. iExists _. done. 
        * (* trapV case *)
          iDestruct "H" as "(%fr & Hfr & (Htok & %vssl & %vswl0' & -> & % & %) & Hbail & _)".
          iApply (wp_wand with "[Hfr]").
          { iApply (wp_label_trap with "Hfr") => //.
            instantiate (1 := λ v, ⌜ v = trapV ⌝%I) => //. }
          iIntros (v) "[-> Hfr]".
          iFrame.
          iExists _,_. done.
        * (* brV case *)
          iDestruct "H" as "(%fr & Hfr & (Htok & %vssl & %vswl0' & -> & %Hlocs' & %Hrestype') & Hrun & Hbr)".
          iDestruct (br_interp_eq with "Hbr") as "Hbr".
          unfold br_interp0. iSimpl in "Hbr".
          iDestruct "Hbr" as (k p lh' lh'' τs es0 es es' vs0 vs) "(%Hgetbase & %Hdepth & %Hlabels & %Hlayer & %Hdepth' & %Hminus & (%vss2 & -> & Hvss2) & Hbr)".
          iDestruct (big_sepL2_length with "Hvss2") as "%Hlen2".
          (* iDestruct (translate_types_length with "Hvss2") as "%Hlen2'".
          ; first exact Heqtrans2. *)
(*          (* may need to first progress in wp before yielding frame *)
          iDestruct ("Hbr" with "Hfr [Hvss2] [$Htok]") as "Hbr".
          { iExists _,_. iSplit; first done. admit. } 
          { iExists _,_. iSplit; first done. done. } 
          unfold lenient_wp_ctx.
          (* iDestruct ("Hbr" with "[]") as "Hbr".
          { iPureIntro. 
            rewrite lh_depth_plug /=. *)

          (* Hmmmm this next part should work… *) 
(*          iDestruct wp_value_fupd as "[H _]"; 
            last iMod ("H" with "Hbr") as "Hbr".
          { unfold IntoVal. apply of_to_val.
            unfold language.to_val. simpl. 
            rewrite (separate1 (AI_basic _)).
            apply to_val_br_eq. }
          iClear "H".
          unfold denote_logpred.
          iSimpl in "Hbr".
          iDestruct "Hbr" as "(Hbr & %fr & Hfr & %vssl' & %vswl'' & -> & Hlocs & Hrestype' & Htok)". *) *)
          destruct (decide (i = p)).
          -- (* targetting this exact block *)
            subst p. 
            destruct (pull_base_l_drop_len lh0 (length (vs0 ++ concat vss2) - length ρ2)) eqn:Hpb.
            rewrite seq.cats0.
            unfold of_val. 
            erewrite vfill_pull_base_l_take_len.
            2:{ exact Hpb. }
            pose proof (vfill_to_lfilled v ((v_to_e_list l1) ++ [AI_basic (BI_br i)])) as [Hle Hfill].
            erewrite <- lh_depth_pull_base_l_take_len in Hfill;[|eauto]. 
            rewrite -e0 in Hfill.
            rewrite -e0 Nat.sub_diag /= in Hlabels.
            rewrite -e0 Nat.sub_diag /= in Hlayer.
            rewrite lh_depth_plug /= in Hlayer.
            rewrite Nat.add_sub in Hlayer.
(*            erewrite get_layer_plug_precise in Hlayer.
            2:{ Search lh. done. *)
            
            rewrite -e0 Nat.sub_diag. 
            inversion Hlabels; subst τs2; clear Hlabels. 
            iApply (wp_br with "Hfr Hrun").
            3: exact Hfill.
            ++ apply v_to_e_is_const_list. 
            ++ rewrite length_fmap.
               eapply length_pull_base_l_take_len in Hpb;[|eauto]. rewrite Hpb.
               assert (length (vs0 ++ concat vss2) >= length ρ2);[|lia].
               rewrite -Hgetbase.
               admit. 
(*               rewrite Hlen2. lia. } *)
            ++ iNext. iIntros "Hf Hrun".
               rewrite app_nil_r.
               iApply wp_value.
               { apply of_to_val. apply to_val_v_to_e. }
(*               iDestruct ("Hbr" with "Hf [Hvss2] [$Htok]") as "Hbr".
               { iExists _,_. iSplit; first done. iSplit; first done.
                 iSplit; first done.  admit. } 
               { iExists _,_. iSplit; first done. done. }  *)
               iFrame.
               iSplitR; last iSplitR. 
               ** iExists _,_. iSplit; first done.
                  done.
               ** iExists _,_. iSplit; first done.
                  iSplit; first (iPureIntro; exact Hlocs').
                  iSplit; first done.
                  admit.
               ** admit.
(*          -- (* targetting this exact block *)
            rewrite lh_depth_plug /= Nat.add_sub in Hdepth' Hlayer.
            replace iris_lfilled_properties.get_layer with get_layer in Hlayer; last done
            erewrite get_layer_plug_precise in Hlayer.
            3: done.
            2:{ admit. }
            inversion Hlayer; subst; clear Hlayer.
            simpl in Hlabels.
            inversion Hlabels; subst; clear Hlabels. 
            assert (j = p) as ->.
            { 
            assert (i = p) as ->.
            { clear - Heqhop Hdepth.
              specialize (vfill_to_lfilled lh0 []) as [H _].
              rewrite Hdepth in H. lia. }
            assert (j = p) as ->.
            { admit. }
            rewrite Nat.sub_diag lh_depth_plug /= Nat.add_sub in Hdepth'.
            rewrite Nat.sub_diag /= in Hlabels.
            inversion Hlabels; subst τs; clear Hlabels. 
            iDestruct (translate_types_length with "Hvss2") as "%Hlen2'".
            { exact Heq_some0. }
            rewrite Nat.sub_diag in Hlayer.
            rewrite lh_depth_plug /= in Hlayer.
            rewrite Nat.add_sub in Hlayer.
            replace ( iris_lfilled_properties.get_layer
                        (lh_plug (LH_rec [] (length ρ2) [] (LH_base [] []) []) lh) 
                        (lh_depth lh))
              with ( get_layer
                       (lh_plug (LH_rec [] (length ρ2) [] (LH_base [] []) []) lh) 
                       (lh_depth lh)) in Hlayer; last done.
            erewrite get_layer_plug_precise in Hlayer => //.
            2:{ admit. }
            inversion Hlayer; subst. 

            iApply (wp_br with "[]").
            3:{ rewrite seq.cats0 /=. 
                instantiate (1 := p).
                instantiate (1 := v_to_e_list (concat vss2)).
                instantiate (1 := lh_of_vh (replace_base lh0 vs0)).
                clear - Hgetbase Hdepth.
                apply lfilled_get_replace_base => //. } 
            ++ apply v_to_e_is_const_list.
            ++ rewrite v_to_e_length length_concat //.
            ++ admit. (* def of br_interp? or my proof? *) 
            ++ admit. (* fix def of br_interp *) 
            ++ iIntros "!> Hf Hrun".
               edestruct const_list_to_val as [vs Hvs]; first by apply v_to_e_is_const_li
               iApply wp_value.
               { apply of_to_val. rewrite app_nil_r. exact Hvs. }
               iSimpl. iFrame.
               iSplitL "Hvss2".
               ** apply v_to_e_list_to_val in Hvs as Hvs'.
                  apply v_to_e_inj in Hvs' as ->.
                  iExists _. iSplit; first done.
                  admit. 
               ** iExists _,_. iSplit; first done.
                  admit. *)
          -- (* still blocked *)
            assert (i > p) as Hip.
            { destruct (vfill_to_lfilled lh0 []) as [? _].
              rewrite Hdepth in H.
              lia. } 
            destruct i; first lia.
            destruct (vh_decrease lh0) eqn:Hlh0.
            2:{ exfalso. clear - Hip Hlh0 Hdepth.
                eapply vh_depth_can_decrease => //.
                by rewrite Hdepth. } 
            iApply wp_value.
            { apply of_to_val. rewrite seq.cats0 /=. 
              simpl.
              unfold RichWasm.iris.language.iris.iris.to_val.
              simpl.
              rewrite seq.cats0.
              specialize (to_of_val (brV lh0)) as H.
              simpl in H.
              unfold RichWasm.iris.language.iris.iris.to_val in H.
              destruct (merge_values_list _) ; try by exfalso.
              inversion H; subst v0; clear H.
              rewrite Hlh0. 
              done. } 
            iSimpl.
(*            iDestruct ("Hbr" with "Hfr [Hvss2] [$Htok]") as "Hbr".
            { iExists _,_. iSplit; first done. iSplit; first done.
              iSplit; first done. admit. } 
            { iExists _,_. iSplit; first done. done. }  *)

            iFrame.
            iSplitR.
            ++ iExists _,_. iSplit; first done. done. 
            ++ iApply br_interp_eq.
               rewrite /br_interp0 /=.
               rewrite lh_depth_plug /= in Hlayer.
               apply get_layer_plug_shallow_inv in Hlayer as (lhnew & Hlayer & ->).
               2:{ clear - Hip.
                   assert (S i - p > 0); first lia.
                   assert (lh_depth lh > 0).
                   { admit. } 
                   lia. }
                  
               repeat iExists _.
               iFrame "Hvss2".
               repeat (iSplit; first iPureIntro).
               ** apply get_base_vh_decrease in Hlh0.
                  rewrite Hlh0. done.
               ** apply lh_of_vh_decrease in Hlh0.
                  rewrite -Hlh0 in Hdepth.
                  rewrite Hdepth. done.
               ** destruct (S i - p) eqn:Hip'; first lia. 
                  simpl in Hlabels.
                  replace (S i - S p) with n0; last lia.
                  done.
               ** rewrite <- Hlayer.
                  f_equal. lia.
               ** rewrite lh_depth_plug /= in Hdepth'.
                  instantiate (1 := lh'').
                  lia.
               ** admit.
               ** done.
               ** iIntros (fr) "Hfr H1 H2".
                  iDestruct ("Hbr" with "Hfr H1 H2") as "H".
                  iIntros (LI HLI).
                  (* br index weirdness *)
                  admit. 
        * iApply wp_value.
          { apply of_to_val.
            rewrite seq.cats0 /=.
            unfold RichWasm.iris.language.iris.iris.to_val.
            simpl.
            specialize (to_of_val (retV s)) as H.
            simpl in H.
            unfold RichWasm.iris.language.iris.iris.to_val in H.
            destruct (merge_values_list _); try by exfalso.
            inversion H; subst v; clear H.
            done. }
          iSimpl.
          iDestruct "H" as "(%fr & Hfr & (Htok & %vssl & %vswl0' & -> & % & %) & Hrun & %vs0 & %vs & %Hgetbase & (%vss & -> & Hvss) & Hret)".
          iFrame.
          iSplit.
          -- iExists _,_. done.
          -- iExists _,_. iSplit; first done. iSplit; first done.
             iIntros (fr fr') "Hf".
             admit. (* generalise s in IH? *)
        * iDestruct "H" as "(%fr & Hfr & _ & _ & ?)"; done.
    - (* n is true *)
      admit.
    *)
  Admitted.

  Lemma compat_br M F L L' wt wt' wtf wl wl' wlf es' i τs1 τs τs2 :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT (τs1 ++ τs) τs2 in
    F.(fc_labels) !! i = Some (τs, L) ->
    Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (IBr ψ i)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_return M F L L' wt wt' wtf wl wl' wlf es' τs1 τs τs2 :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT (τs1 ++ τs) τs2 in
    F.(fc_return) = τs ->
    Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (IReturn ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_local_get_copy M F L wt wt' wtf wl wl' wlf es' i τ :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [] [τ] in
    L !! i = Some τ ->
    has_copyability F τ ImCopy ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ILocalGet ψ i)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Admitted.

  Lemma compat_local_get_move M F L wt wt' wtf wl wl' wlf es' i τ ηs :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [] [τ] in
    let L' := <[ i := type_plug_prim ηs ]> L in
    F.(typing.fc_locals) !! i = Some ηs ->
    L !! i = Some τ ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ILocalGet ψ i)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_local_set M F L wt wt' wtf wl wl' wlf es' i τ :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [τ] [] in
    let L' := <[ i := τ ]> L in
    (∀ τ0, L !! i = Some τ0 → has_dropability F τ0 ImDrop) ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ILocalSet ψ i)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_coderef M F L wt wt' wtf wl wl' wlf es' i ϕ :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let τ := CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop) ϕ in
    let ψ := InstrT [] [τ] in
    M.(mc_table) !! i = Some ϕ ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ICodeRef ψ i)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Admitted.

  Lemma compat_inst M F L wt wt' wtf wl wl' wlf es' ix ϕ ϕ' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let κ := VALTYPE (AtomR I32R) ImCopy ImDrop in
    let ψ := InstrT [CodeRefT κ ϕ] [CodeRefT κ ϕ'] in
    function_type_inst F ix ϕ ϕ' ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IInst ψ ix)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Proof.
    intros fe WT WL κ ψ Hfinst Hok Hcg.
    cbn in Hcg; inversion Hcg; subst wt' wl' es'; clear Hcg.
    simpl to_e_list.
    iApply sem_type_erased; first done.
    iIntros (se vs) "Hrec".
    do 2 rewrite values_interp_one_eq value_interp_eq.
    cbn [subst_type].
    cbn -[closure_interp0].
    iDestruct "Hrec" as "(%κ' & %Hκ' & Hkindinterp & %i & %j & %cl & %Hvs & Hrec)".
    inversion Hκ'; subst κ'; clear Hκ'.
    inversion Hvs; subst vs; clear Hvs.
    iExists (SVALTYPE [I32R] ImCopy ImDrop).
    iSplit; first done.
    iFrame.
    iExists i, j, cl.
    iSplit; first done.
    iDestruct "Hrec" as "(Hrec & Hj & Hcl)".
    iFrame.
    iModIntro.
    (* prove that closure interp at ϕ implies closure interp at any instantiation ϕ' *)
    (* Will probably want to proceed by induction on function_type_inst? *)
  Admitted.

  Lemma compat_call M F L wt wt' wtf wl wl' wlf es' i ixs ϕ τs1 τs2 :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT τs1 τs2 in
    M.(mc_functions) !! i = Some ϕ ->
    function_type_insts F ixs ϕ (MonoFunT τs1 τs2) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ICall ψ i ixs)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Admitted.

  Lemma compat_call_indirect M F L wt wt' wtf wl wl' wlf es' τs1 τs2 :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let κ := VALTYPE (AtomR I32R) ImCopy ImDrop in
    let ψ := InstrT (τs1 ++ [CodeRefT κ (MonoFunT τs1 τs2)]) τs2 in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ICallIndirect ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Admitted.

  Lemma compat_inject M F L wt wt' wtf wl wl' wlf es' i τs τ κ :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [τ] [SumT κ τs] in
    τs !! i = Some τ ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IInject ψ i)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Admitted.

  Lemma compat_inject_new M F L wt wt' wtf wl wl' wlf es' μ i τ τs κr κv κs :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let τs' := zip_with SerT κs τs in
    let ψ := InstrT [τ] [RefT κr μ (VariantT κv τs)] in
    τs !! i = Some τ ->
    mono_mem μ ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IInjectNew ψ i)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Admitted.

  Lemma compat_case M F L L' wt wt' wtf wl wl' wlf es' ess τs τs' κ :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let F' := F <| fc_labels ::= cons (τs', L') |> in
    let ψ := InstrT [SumT κ τs] τs' in
    Forall2
      (fun τ es =>
         (forall wt wt' wtf wl wl' wlf es',
            let fe' := fe_of_context F' in
            let WT := wt ++ wt' ++ wtf in
            let WL := wl ++ wl' ++ wlf in
            run_codegen (compile_instrs mr fe' es) wt wl = inr ((), wt', wl', es') ->
            ⊢ have_instruction_type_sem rti sr mr M F' L WT WL (to_e_list es') (InstrT [τ] τs') L'))
      τs ess ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ICase ψ L' ess)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_case_load_copy M F L L' wt wt' wtf wl wl' wlf ess es' τs τs' μ κr κv κs :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let F' := F <| fc_labels ::= cons (τs', L') |> in
    let τs_ser := zip_with SerT κs τs in
    let ψ := InstrT [RefT κr μ (VariantT κv τs_ser)] (RefT κr μ (VariantT κv τs') :: τs') in
    Forall (fun τ => has_copyability F τ ExCopy) τs ->
    Forall2
      (fun τ es =>
         (forall wt wt' wtf wl wl' wlf es',
            let fe' := fe_of_context F' in
            let WT := wt ++ wt' ++ wtf in
            let WL := wl ++ wl' ++ wlf in
            run_codegen (compile_instrs mr fe' es) wt wl = inr ((), wt', wl', es') ->
            ⊢ have_instruction_type_sem rti sr mr M F' L WT WL (to_e_list es') (InstrT [τ] τs') L'))
      τs ess ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ICaseLoad ψ Copy L' ess)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_case_load_move M F L L' wt wt' wtf wl wl' wlf ess es' τs τs' κr κv κs :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let F' := F <| fc_labels ::= cons (τs', L') |> in
    let τs_ser := zip_with SerT κs τs in
    let ψ := InstrT [RefT κr (BaseM MemMM) (VariantT κv τs_ser)] τs' in
    Forall2
      (fun τ es =>
         (forall wt wt' wtf wl wl' wlf es',
            let fe' := fe_of_context F' in
            let WT := wt ++ wt' ++ wtf in
            let WL := wl ++ wl' ++ wlf in
            run_codegen (compile_instrs mr fe' es) wt wl = inr ((), wt', wl', es') ->
           ⊢ have_instruction_type_sem rti sr mr M F' L WT WL (to_e_list es') (InstrT [τ] τs') L'))
      τs ess ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ICaseLoad ψ Move L' ess)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_group M F L wt wt' wtf wl wl' wlf es' τs κ :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT τs [ProdT κ τs] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IGroup ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ungroup M F L wt wt' wtf wl wl' wlf es' τs κ :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [ProdT κ τs] τs in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IUngroup ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Proof.
    intros fe WT WL ψ Hok Hcg.
    inversion Hok as [F' ψ' L' Hmono Hok'].
    subst F' ψ' L'.
    cbn in Hcg; inversion Hcg; subst wt' wl' es'.
    simpl to_e_list.
    iApply sem_type_erased_nop; first done.
    iIntros (se vs) "Hvs".
    rewrite values_interp_one_eq value_interp_eq.
    cbn.
    iDestruct "Hvs" as "(%κ' & %Hκ' & Hkind & Hvs)".
  Admitted.

  Lemma compat_fold M F L wt wt' wtf wl wl' wlf es' τ κ :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
    let ψ := InstrT [τ0] [RecT κ τ] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IFold ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Proof.
    intros fe WT WL τrec ψ Hok Hcg.
    cbn in Hcg; inversion Hcg; subst wt' wl' es'; clear Hcg.
    simpl to_e_list.
    iApply sem_type_erased; first done.
    iIntros (se vs) "Hrec".
    do 2 rewrite values_interp_one_eq value_interp_eq.
    iEval (cbn).
    admit.
  Admitted.

  Lemma compat_unfold M F L wt wt' wtf wl wl' wlf es' τ κ :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
    let ψ := InstrT [RecT κ τ] [τ0] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IUnfold ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Proof.
    intros fe WT WL τrec ψ Hok Hcg.
    cbn in Hcg; inversion Hcg; subst wt' wl' es'; clear Hcg.
    simpl to_e_list.
    iApply sem_type_erased; first done.
    iIntros (se vs) "Hrec".
    do 2 rewrite values_interp_one_eq value_interp_eq.
    iEval (cbn) in "Hrec".
    admit.
  Admitted.

  Lemma compat_pack M F L wt wt' wtf wl wl' wlf es' τ τ' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [τ] [τ'] in
    packed_existential F τ τ' ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IPack ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Proof.
    intros fe WT WL τrec ψ Hok Hcg.
    cbn in Hcg; inversion Hcg; subst wt' wl' es'; clear Hcg.
    simpl to_e_list.
    iApply sem_type_erased; first done.
    iIntros (se vs) "Hrec".
    do 2 rewrite values_interp_one_eq value_interp_eq.
  Admitted.

  Lemma compat_unpack M F F0' L L' L0 L0' wt wt' wtf wl wl' wlf es es' es0 τs1 τs2 ψ0 :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let F' := F <| fc_labels ::= cons (τs2, L') |> in
    let ψ := InstrT τs1 τs2 in
    unpacked_existential F' L es ψ L' F0' L0 es0 ψ0 L0' ->
    has_instruction_type_ok F ψ L' ->
    (forall wt wt' wtf wl wl' wlf es',
        let fe0' := fe_of_context F0' in
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        run_codegen (compile_instrs mr fe0' es0) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instruction_type_sem rti sr mr M F0' L0 WT WL (to_e_list es') ψ0 L0') ->
    run_codegen (compile_instr mr fe (IUnpack ψ L' es)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L'.
  Admitted.

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

  Lemma compat_tag M F L wt wt' wtf wl wl' wlf es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [type_i32] [type_i31] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ITag ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Proof.
    intros fe WT WL ψ Hok Hcompile.
    cbn in Hcompile; inversion Hcompile; subst; clear Hcompile.

    iIntros (se inst lh fr rvs vs θ) "%Henv #Hinst #Hlf Hrvs Hvs Hframe Hrt Hfr Hrun".

    (* A loooong section to prove that vs just has an integer in it *)
    (* First, show that rvs just has one thing in it *)
    iEval (cbn) in "Hvs"; iEval (cbn) in "Hrvs".
    iDestruct "Hvs" as "(%rvss & %Hconcat_rvss & Hrvss)".
    iPoseProof (big_sepL2_length with "[$Hrvss]") as "%Hlens_rvss".
    iPoseProof (big_sepL2_length with "[$Hrvs]") as "%Hlens_vs_rvs".
    simpl in Hlens_rvss.

    (* For some reason I couldn't use length1concat?? *)
    assert (Hrvsss: rvss = [rvs]).
    {
      destruct rvss as [ | rv rvs1 ]; inversion Hlens_rvss.
      symmetry in H0; apply nil_length_inv in H0; subst; simpl.
      by rewrite app_nil_r.
    }
    rewrite Hrvsss.
    iEval (cbn) in "Hrvss".
    iDestruct "Hrvss" as "[Hvs _]".
    iPoseProof (value_interp_eq with "Hvs") as "Hvs".
    iEval (cbn) in "Hvs".
    iDestruct "Hvs" as "(%k & %Hk & Hkindinterp & _)".
    inversion Hk.
    iEval (cbn) in "Hkindinterp".
    iPoseProof "Hkindinterp" as "%Hkindinterp".
    (* Have to dig in and prove rvs is just an integer *)
    unfold has_areps in Hkindinterp.
    destruct Hkindinterp as (rvs0 & Hrvs0 & Hprimprep).
    inversion Hrvs0.
    rewrite <- H1 in Hprimprep. (* subst does too much here*)
    apply Forall2_length in Hprimprep as Hrvslength.
    cbn in Hrvslength.
    destruct rvs as [|rv rvs]; inversion Hrvslength.
    symmetry in H2; apply nil_length_inv in H2.
    subst.
    (* So close *)
    apply Forall2_cons_iff in Hprimprep.
    destruct Hprimprep as [Hrv _].
    cbn in Hrv.
    destruct rv; cbn in Hrv; try easy; subst.

    (* Now genuinely new bit: show vs has an integer *)
    (* temporary cleaning this is a mess *)
    clear Hconcat_rvss Hlens_rvss Hk Hrvslength Hrvs0 Hrv.
    cbn in Hlens_vs_rvs.
    destruct vs as [| v vs]; inversion Hlens_vs_rvs.
    symmetry in H0; apply nil_length_inv in H0; subst.
    iEval (cbn) in "Hrvs".
    iDestruct "Hrvs" as "(%Hv & _)"; subst.

    (* Okay yay! Now we can apply lwp_binop. *)
    iClear "Hinst"; iClear "Hlf".
    iEval (cbn).
    iApply lwp_binop.
    - cbn. auto. (* get the pure value that the computations gets you *)
    - (* Four of the resources are just trivial *)
      iFrame.
      (* let's prove this value!*)
      iModIntro; cbn.
      unfold Wasm_int.Int32.ishl, Wasm_int.Int32.shl, Z.shiftl; cbn.
      iExists [PtrA (PtrInt (Wasm_int.Int32.unsigned n))].
      iSplitR; cbn; try (iSplitR; auto); last first.
      * iExists _; iSplitL; auto.
        iExists (RootInt (Wasm_int.Int32.unsigned n)).
        cbn.
        iSplit; auto using ReprRootInt.
      * iExists [[PtrA (PtrInt (Wasm_int.Int32.unsigned n))]].
        iSplitL; cbn; auto; iSplitL; auto.

        iApply value_interp_eq; cbn.
        iExists _; iSplitL; auto; iSplitL; auto; cbn.
        iPureIntro.

        eexists; split; auto.
        apply Forall2_cons_iff; split; auto.
        by unfold has_areps.
  Qed.

  Lemma compat_untag M F L wt wt' wtf wl wl' wlf es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [type_i31] [type_i32] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IUntag ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Proof.
    intros fe WT WL ψ Hok Hcompile.
    cbn in Hcompile; inversion Hcompile; subst; clear Hcompile.

    iIntros (se inst lh fr rvs vs θ) "%Henv #Hinst #Hlf Hrvs Hvs Hframe Hrt Hfr Hrun".

    (* A loooong section to prove that vs just has an integer in it *)
    (* First, show that rvs just has one thing in it *)
    iEval (cbn) in "Hvs"; iEval (cbn) in "Hrvs".
    iDestruct "Hvs" as "(%rvss & %Hconcat_rvss & Hrvss)".
    iPoseProof (big_sepL2_length with "[$Hrvss]") as "%Hlens_rvss".
    iPoseProof (big_sepL2_length with "[$Hrvs]") as "%Hlens_vs_rvs".
    simpl in Hlens_rvss.

    (* For some reason I couldn't use length1concat?? *)
    assert (Hrvsss: rvss = [rvs]).
    {
      destruct rvss as [ | rv rvs1 ]; inversion Hlens_rvss.
      symmetry in H0; apply nil_length_inv in H0; subst; simpl.
      by rewrite app_nil_r.
    }
    rewrite Hrvsss.
    iEval (cbn) in "Hrvss".
    iDestruct "Hrvss" as "[Hvs _]".
    iPoseProof (value_interp_eq with "Hvs") as "Hvs".
    iEval (cbn) in "Hvs".
    iDestruct "Hvs" as "(%k & %Hk & Hkindinterp & _)".
    inversion Hk.
    iEval (cbn) in "Hkindinterp".
    iPoseProof "Hkindinterp" as "%Hkindinterp".
    (* Have to dig in and prove rvs is just an integer *)
    unfold has_areps in Hkindinterp.
    destruct Hkindinterp as (rvs0 & Hrvs0 & Hprimprep).
    inversion Hrvs0.
    rewrite <- H1 in Hprimprep. (* subst does too much here*)
    apply Forall2_length in Hprimprep as Hrvslength.
    cbn in Hrvslength.
    destruct rvs as [|rv rvs]; inversion Hrvslength.
    symmetry in H2; apply nil_length_inv in H2.
    subst.
    (* So close *)
    apply Forall2_cons_iff in Hprimprep.
    destruct Hprimprep as [Hrv _].
    cbn in Hrv.
    destruct rv; cbn in Hrv; try easy; subst.

    (* Now genuinely new bit: show vs has an a pointer *)
    (* temporary cleaning this is a mess *)
    clear Hconcat_rvss Hlens_rvss Hk Hrvslength Hrvs0 Hrv.
    cbn in Hlens_vs_rvs.
    destruct vs as [| v vs]; inversion Hlens_vs_rvs.
    symmetry in H0; apply nil_length_inv in H0; subst.
    iEval (cbn) in "Hrvs".
    iDestruct "Hrvs" as "[(%n & %Hv & %rp & %Hrepr & Hinterp) _]"; subst.

    (* Okay yay! Now we can apply lwp_binop. *)
    iClear "Hinst"; iClear "Hlf".
    iEval (cbn).
    iApply lwp_binop.
    - cbn. auto. (* get the pure value that the computations gets you *)
    - (* Four of the resources are just trivial *)
      iFrame.
      (* let's prove this value!*)
      iModIntro; cbn.
      iExists [I32A (Wasm_int.Int32.ishr_u (Wasm_int.Int32.repr n) (Wasm_int.Int32.repr 1))].
      iSplitR; cbn; try (iSplitR; auto).
      iExists [[I32A (Wasm_int.Int32.ishr_u (Wasm_int.Int32.repr n) (Wasm_int.Int32.repr 1))]].
      iSplitR; cbn; auto; iSplitL; auto.

      iApply value_interp_eq; cbn.
      iExists _; iSplitL; auto; iSplitL; auto; cbn.
      iPureIntro.

      eexists; split; auto.
      apply Forall2_cons_iff; split; auto.
      by unfold has_areps.
  Qed.

  Lemma compat_cast M F L wt wt' wtf wl wl' wlf es' τ τ' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [τ] [τ'] in
    type_eq F τ τ' ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ICast ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Admitted.

  Lemma compat_new M F L wt wt' wtf wl wl' wlf κ κser μ τ es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [τ] [RefT κ μ (SerT κser τ)] in
    mono_mem μ ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (INew ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Admitted.

  Lemma compat_load_copy M F L wt wt' wtf wl wl' wlf es' κ κser μ τ τval π pr :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [RefT κ μ τ] [RefT κ μ τ; τval] in
    has_copyability F τval ExCopy ->
    resolves_path τ π None pr ->
    pr.(pr_target) = SerT κser τval ->
    Forall (has_mono_size F) (pr_prefix pr) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ILoad ψ π Copy)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Proof.
    intros fe WT WL ψ Hcopyability Hresolves Hser Hmonosize Htype Hcompile.
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
    assert (Hu: u = ()). { admit. }
    assert (Hp: p = ((),())). { admit. }
    subst.
    clear_nils.

    (* Next is case ptr *)

  Admitted.

  Lemma compat_load_move M F L wt wt' wtf wl wl' wlf es' κ κ' κser σ τ τval π pr :
    let fe := fe_of_context F in   
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [RefT κ (BaseM MemMM) τ] [RefT κ' (BaseM MemMM) (pr_replaced pr); τval] in
    resolves_path τ π (Some (type_span σ)) pr ->
    has_size F pr.(pr_target) σ ->
    pr.(pr_target) = SerT κser τval ->
    Forall (has_mono_size F) (pr_prefix pr) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ILoad ψ π Move)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Proof.
    intros fe WT WL ψ Hresolves Hsize Hser Hmonosize Htype Hcompile.
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
    inv_cg_bind Hcompile () ?wt ?wt ?wl ?wl es_ptr_flags ?es_rest Hptr_flags Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl  es_case_ptr ?es_rest Hcompile Hignore.
    cbn in Hignore; inversion Hignore; subst; clear Hignore.

    (* Some clean up *)
    assert (Hu: u = ()). { admit. }
    assert (Hp: p = ((),())). { admit. }
    subst.
    clear_nils.

    (* Next is case ptr *)
    (* WAITING FOE LEMMA *)

  Admitted.

  Lemma compat_store_weak M F L wt wt' wtf wl wl' wlf es' κ κser μ τ τval π pr :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [RefT κ μ τ; τval] [RefT κ μ τ] in
    resolves_path τ π None pr ->
    has_dropability F pr.(pr_target) ImDrop ->
    pr.(pr_target) = SerT κser τval ->
    Forall (has_mono_size F) (pr_prefix pr) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IStore ψ π)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Proof.
    intros fe WT WL ψ Hresolves Hdrop Hser Hmonosize Htype Hcompile.
    unfold WT, WL; clear WT WL.
    (* If the WT := or WL := become necessary, undo the unfold/clear*)
    cbn in Hcompile.

    (* Mechanically get through some of the first few things in compile_swap *)
    inv_cg_bind Hcompile ρ ?wt ?wt ?wl ?wl es_off ?es_rest Hρ Hcompile.
    inv_cg_bind Hcompile ιs ?wt ?wt ?wl ?wl es_ρ ?es_rest Hιs Hcompile.
    inv_cg_bind Hcompile off ?wt ?wt ?wl ?wl  es_fail ?es_rest Hoff Hcompile.
    inv_cg_try_option Hρ; rename Heq_some into Hρ.
    inv_cg_try_option Hιs; rename Heq_some into Hιs.
    inv_cg_try_option Hoff; rename Heq_some into Hoff.
    inv_cg_bind Hcompile vs ?wt ?wt ?wl ?wl  es_save ?es_rest Hsave Hcompile.
    inv_cg_bind Hcompile a ?wt ?wt ?wl ?wl  es_a ?es_rest Ha Hcompile.
    cbn in Ha; inversion Ha; subst; clear Ha.
    inv_cg_bind Hcompile res_emit ?wt ?wt ?wl ?wl  es_emit ?es_rest Hemit Hcompile.
    inv_cg_emit Hemit.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_case_ptr es_ptr_flags Hcompile Hptr_flags.

    (* Some clean up *)
    subst.
    clear_nils.

    (* The next step is a case_ptr, for which a lemma is currently being proven about *)

  Admitted.

  Lemma compat_store_strong M F L wt wt' wtf wl wl' wlf es' κ κ' κser σ ρ τ τval π pr :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [RefT κ (BaseM MemMM) τ; τval] [RefT κ' (BaseM MemMM) (pr_replaced pr)] in
    resolves_path τ π (Some (SerT κser τval)) pr ->
    has_dropability F pr.(pr_target) ImDrop ->
    has_size F pr.(pr_target) σ ->
    has_rep F τval ρ ->
    eval_size EmptyEnv σ = eval_rep_size EmptyEnv ρ ->
    Forall (has_mono_size F) (pr_prefix pr) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IStore ψ π)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Proof.
    intros fe WT WL ψ Hresolves Hdrop Hsize Hrep Henv Hmonosize Htype Hcompile.
    unfold WT, WL; clear WT WL.
    (* If the WT := or WL := become necessary, undo the unfold/clear*)
    cbn in Hcompile.

    (* Mechanically get through some of the first few things in compile_swap *)
    inv_cg_bind Hcompile ρ_inner ?wt ?wt ?wl ?wl es_off ?es_rest Hρ_inner Hcompile.
    inv_cg_bind Hcompile ιs ?wt ?wt ?wl ?wl es_ρ ?es_rest Hιs Hcompile.
    inv_cg_bind Hcompile off ?wt ?wt ?wl ?wl  es_fail ?es_rest Hoff Hcompile.
    inv_cg_try_option Hρ_inner; rename Heq_some into Hρ_inner.
    inv_cg_try_option Hιs; rename Heq_some into Hιs.
    inv_cg_try_option Hoff; rename Heq_some into Hoff.
    inv_cg_bind Hcompile vs ?wt ?wt ?wl ?wl  es_save ?es_rest Hsave Hcompile.
    inv_cg_bind Hcompile a ?wt ?wt ?wl ?wl  es_a ?es_rest Ha Hcompile.
    cbn in Ha; inversion Ha; subst; clear Ha.
    inv_cg_bind Hcompile res_emit ?wt ?wt ?wl ?wl  es_emit ?es_rest Hemit Hcompile.
    inv_cg_emit Hemit.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_case_ptr es_ptr_flags Hcompile Hptr_flags.

    (* Some clean up *)
    subst.
    clear_nils.

    (* The next step is a case_ptr, for which a lemma is currently being proven about *)

  Admitted.



  Lemma compat_swap M F L wt wt' wtf wl wl' wlf es' κ κser μ τ τval π pr :
     let fe := fe_of_context F in   
     let WT := wt ++ wt' ++ wtf in
     let WL := wl ++ wl' ++ wlf in
     let ψ := InstrT [RefT κ μ τ; τval] [RefT κ μ τ; τval] in
     resolves_path τ π None pr ->
     Forall (has_mono_size F) (pr_prefix pr) ->
     pr.(pr_target) = SerT κser τval ->
     has_instruction_type_ok F ψ L ->
     run_codegen (compile_instr mr fe (ISwap ψ π)) wt wl = inr ((), wt', wl', es') ->
     ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Proof.
    intros fe WT WL ψ Hresolves Hmonosize Hser Htype Hcompile. unfold WT, WL; clear WT WL.
    (* If the WT := or WL := become necessary, undo the unfold/clear*)
    cbn in Hcompile.

    (* Mechanically get through some of the first few things in compile_swap *)
    inv_cg_bind Hcompile ρ ?wt ?wt ?wl ?wl es_off ?es_rest Hρ Hcompile.
    inv_cg_bind Hcompile ιs ?wt ?wt ?wl ?wl es_ρ ?es_rest Hιs Hcompile.
    inv_cg_bind Hcompile off ?wt ?wt ?wl ?wl  es_fail ?es_rest Hoff Hcompile.
    inv_cg_try_option Hρ; rename Heq_some into Hρ.
    inv_cg_try_option Hιs; rename Heq_some into Hιs.
    inv_cg_try_option Hoff; rename Heq_some into Hoff.
    inv_cg_bind Hcompile vs ?wt ?wt ?wl ?wl  es_save ?es_rest Hsave Hcompile.
    inv_cg_bind Hcompile a ?wt ?wt ?wl ?wl  es_a ?es_rest Ha Hcompile.
    cbn in Ha; inversion Ha; subst; clear Ha.
    inv_cg_bind Hcompile res_emit ?wt ?wt ?wl ?wl  es_emit ?es_rest Hemit Hcompile.
    inv_cg_emit Hemit.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl  es_case_ptr ?es_rest Hcompile Hignore.
    cbn in Hignore; inversion Hignore; subst; clear Hignore.

    (* Some clean up *)
    assert (Hu: u = ()). { admit. }
    assert (Hp: p = ((),())). { admit. }
    subst.
    clear_nils.

    (* The next step is a case_ptr, for which a lemma is currently being proven about *)

  Admitted.

  Lemma compat_nil M F L wt wt' wtf wl wl' wlf es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    run_codegen (compile_instrs mr fe []) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') (InstrT [] []) L.
  Proof.
    intros fe WT WL Hcompile.
    cbn in Hcompile.
    inversion Hcompile.

    iIntros (se inst lh fr rvs vs θ) "%Henv #Hinst #Hlf Hrvs Hvs Hframe Hrt Hfr Hrun".

    iEval (cbn) in "Hrvs"; iEval (cbn) in "Hvs".
    iDestruct "Hvs" as "(%rvss & %Hconcat & Hrvss)".
    iPoseProof (big_sepL2_length with "[$Hrvss]") as "%Hlens_rvss".
    iPoseProof (big_sepL2_length with "[$Hrvs]") as "%Hlens_rvs_vs".
    cbn in Hlens_rvss.
    destruct rvss, rvs; cbn in Hconcat, Hlens_rvss; try congruence.
    cbn in Hlens_rvs_vs. destruct vs; cbn in Hlens_rvs_vs; try congruence.

    rewrite !app_nil_l.
    unfold expr_interp.

    iApply lenient_wp_nil.
    unfold lp_combine, denote_logpred; cbn.
    iFrame.
    iExists []; auto.
    iSplit; auto.
    iExists []; auto.
  Qed.

  Lemma compat_app M F L1 L2 L3 wt wt' wtf wl wl' wlf es' es1 es2 τs1 τs2 τs3 :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    (forall wt wt' wtf wl wl' wlf es',
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        run_codegen (compile_instrs mr fe es1) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instruction_type_sem rti sr mr M F L1 WT WL (to_e_list es') (InstrT τs1 τs2) L2) ->
    (forall wt wt' wtf wl wl' wlf es',
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        run_codegen (compile_instrs mr fe es2) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instruction_type_sem rti sr mr M F L2 WT WL (to_e_list es') (InstrT τs2 τs3) L3) ->
    run_codegen (compile_instrs mr fe (es1 ++ es2)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L1 WT WL (to_e_list es') (InstrT τs1 τs3) L3.
  Proof.
    intros fe WT WL Hes1 Hes2 Hcompile; rename wl' into wl''; rename wt' into wt''; rename es' into es''.
    (* Step 1: split out Hcompile into Hcompile_e and Hcompile_es *)

    (* For Hcompile_e *)
    unfold compile_instrs in Hcompile.
    cbn in Hcompile.
    inv_cg_bind Hcompile res wt_full wttemp wl_full wltemp es' es2_temp' Hcompile Hcompile_empty; subst.
    inversion Hcompile_empty; subst; clear Hcompile_empty.
    rewrite app_nil_r.

    assert (Hcompile_split: exists wt1 wt2 wl1 wl2 es1' es2',
              run_codegen (compile_instrs mr fe es1) wt wl = inr ((), wt1, wl1, es1')
               /\
              run_codegen (compile_instrs mr fe es2) (wt ++ wt1) (wl ++ wl1) =
                inr ((), wt2, wl2, es2')
               /\
              wt_full = wt1 ++ wt2
               /\
              wl_full = wl1 ++ wl2
               /\
              es' = es1' ++ es2'
           ).
    {
      (* This is mainly a proof about the codegen monad. Weirdly difficult for whatever reason.
         Come back to it later. *)
      admit.
    }
    destruct Hcompile_split as (wt1&wt2&wl1&wl2&es1'&es2'& Hcompile_es1 & Hcompile_es2 & H1 & H2 & H3); subst.

    (* This is very silly but I can't figure out how to just rewrite with WT := ... *)
    assert (Temp: WT = wt ++ ((wt1 ++ wt2) ++ []) ++ wtf) by auto; rewrite Temp; clear Temp.
    assert (Temp: WL = wl ++ ((wl1 ++ wl2) ++ []) ++ wlf) by auto; rewrite Temp; clear Temp.
    repeat rewrite app_nil_r.

    apply (Hes1 wt wt1 (wt2 ++ wtf) wl wl1 (wl2 ++ wlf) es1') in Hcompile_es1 as Hsem_es1.
    apply (Hes2 (wt ++ wt1) wt2 wtf (wl ++ wl1) wl2 wlf es2') in Hcompile_es2 as Hsem_es2.

    (* Temporary context clean up*)
    clear Hes1 Hes2 Hcompile Hcompile_es1 Hcompile_es2 WT WL.
    rewrite to_e_list_app.
    repeat rewrite <- app_assoc.

    (* Time for type semantic! *)
    unfold have_instruction_type_sem.
    iIntros (? ? ? ? ? ? ?) "%Henv #Hinst #Hctx Hrvs Hvs Hfr Hrt Hf Hrun".
    unfold have_instruction_type_sem in Hsem_es1, Hsem_es2.
    iPoseProof (Hsem_es1) as "Hsem_es1"; iPoseProof (Hsem_es2) as "Hsem_es2".

    (* Start passing resources *)
    iSpecialize ("Hsem_es1" $! se inst lh fr os vs θ Henv with "Hinst Hctx Hrvs Hvs Hfr Hrt Hf Hrun").
    rewrite (app_assoc (language.of_val (immV vs)) (to_e_list es1') (to_e_list es2')).

    iApply (lenient_wp_seq with "[Hsem_es1]").
    - iApply "Hsem_es1".
    - done.
    - iIntros (w f) "Hvs Hfr _".
      destruct w eqn:Hw.
      + (* Value case *)
        iDestruct "Hvs" as "(Hrun & Hframe & Hval)". rename l into vs0.
        iDestruct "Hval" as "[%rvs0 [%θ0 (Hval_interp & Hrep_interp & Hrt)]]".

        (* This makes the rewrites a little nicer *)
        assert (Temp: forall A (l1:list A) l2 l3 l4, l1 ++ l2 ++ l3 ++ l4 = (l1 ++ l2) ++ l3 ++ l4).
        { intros. by rewrite app_assoc. }

        repeat (rewrite Temp).
        iSpecialize ("Hsem_es2" $! se inst lh f rvs0 vs0 θ0 Henv
                      with "Hinst Hctx Hrep_interp Hval_interp Hframe Hrt Hfr Hrun").
        iApply "Hsem_es2".
      + done.
      + iEval (cbn) in "Hvs". iDestruct "Hvs" as "(Hrun & Hbr_interp)".
        iEval (cbn).
        (* Some sort of lenient_wp lemma about BI_br *)
        admit.
      + (* string of specific cbns for a cleaner context *)
        iEval (cbn [lp_notrap]) in "Hvs". iEval (cbn [lp_noframe]) in "Hvs".
        iEval (cbn [lp_ret]) in "Hvs".
        iDestruct "Hvs" as "(Hrun & Hret_interp)".
        iEval (cbn).
        (* Some sort of lenient_wp lemma about BI_return *)
        admit.
      + (* While call_host is still just False, this works. *)
        iEval (cbn) in "Hvs".
        iDestruct "Hvs" as "(_ & HF)".
        auto.
  Admitted.

  Lemma compat_singleton M F L L' wt wt' wtf wl wl' wlf e ψ es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    (forall wt wt' wtf wl wl' wlf es',
       let fe := fe_of_context F in
       let WT := wt ++ wt' ++ wtf in
       let WL := wl ++ wl' ++ wlf in
       run_codegen (compile_instr mr fe e) wt wl = inr ((), wt', wl', es') ->
       ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L') ->
    run_codegen (compile_instrs mr fe [e]) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L'.
  Proof.
    intros fe WT WL IH Hcg.
    unfold compile_instrs, util.mapM_ in Hcg.
    apply wp_ignore in Hcg.
    destruct Hcg as (_ & ? & Hcg).
    apply wp_mapM_cons in Hcg.
    destruct Hcg as ([] & ? & ? & ? & yss_xs & ? & ? & ? & He & Hret & -> & Hwt & Hwl & ->).
    cbn in Hret; inversion Hret; subst; clear Hret.
    apply IH.
    rewrite -> !app_nil_r in *.
    eauto.
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

  Lemma compat_frame M F L L' wt wt' wtf wl wl' wlf es es' τ τs1 τs2 :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    has_mono_rep F τ ->
    (forall wt wt' wtf wl wl' wlf es',
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        run_codegen (compile_instrs mr fe es) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') (InstrT τs1 τs2) L') ->
    run_codegen (compile_instrs mr fe es) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') (InstrT (τ :: τs1) (τ :: τs2)) L'.
  Proof.
    intros fe WT WL Hmono IH Hcg.
    eapply (IH _ _ _ _ _ wlf) in Hcg.
    iIntros (se inst lh fr rvs vs θ) "%Henv #Hinst #Hlf Hrvs Hvs Hframe Hrt Hfr Hrun".
    iPoseProof (values_interp_cons_inv with "Hvs") as "(%rvs1 & %rvs2 & %Hvs & Hty1 & Hty2)".
    subst rvs.
    iPoseProof (big_sepL2_app_inv_l with "Hrvs") as "(%vs1 & %vs2 & -> & Hvs1 & Hvs2)".
    iPoseProof (Hcg $! se inst lh fr rvs2 vs2 θ Henv with "Hinst Hlf") as "IH".
    iSpecialize ("IH" with "Hvs2 Hty2 [$] [$] [$] [$]").
    simpl language.of_val.
    iEval (repeat rewrite -cat_app).
    rewrite -v_to_e_cat.
    repeat rewrite cat_app.
    rewrite -app_assoc.
    iEval (cbn [List.map]).
    iApply (expr_interp_val_app with "[$] [$] [$]").
  Qed.

  Theorem fundamental_theorem M F L L' wt wt' wtf wl wl' wlf es es' tf :
    have_instruction_type M F L es tf L' ->
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    run_codegen (compile_instrs mr fe es) wt wl = inr (tt, wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') tf L'.
  Proof.
    intros Htype.
    generalize dependent es'.
    generalize dependent wlf.
    generalize dependent wl'.
    generalize dependent wl.
    generalize dependent wtf.
    generalize dependent wt'.
    generalize dependent wt.
    induction Htype using have_instruction_type_mind with
      (P1 := fun M F L e ψ L' =>
               forall wt wt' wtf wl wl' wlf es',
                 let fe := fe_of_context F in
                 let WT := wt ++ wt' ++ wtf in
                 let WL := wl ++ wl' ++ wlf in
                 run_codegen (compile_instr mr fe e) wt wl = inr (tt, wt', wl', es') ->
                 ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L');
      intros wt wt' wtf wl wl' wlf wes fe WT WL Hcomp.
    - eapply compat_nop; eassumption.
    - eapply compat_unreachable; eassumption.
    - eapply compat_copy; eassumption.
    - eapply compat_drop; eassumption.
    - eapply compat_num; eassumption.
    - eapply compat_num_const; eassumption.
    - eapply compat_block; eassumption.
    - eapply compat_loop; eassumption.
    - eapply compat_ite in Hcomp; eassumption.
    - eapply compat_br; eassumption.
    - eapply compat_return; eassumption.
    - eapply compat_local_get_copy; eassumption.
    - eapply compat_local_get_move; eassumption.
    - eapply compat_local_set; eassumption.
    - eapply compat_coderef; eassumption.
    - eapply compat_inst; eassumption.
    - eapply compat_call; eassumption.
    - eapply compat_call_indirect; eassumption.
    - eapply compat_inject; eassumption.
    - eapply compat_inject_new; eassumption.
    - eapply compat_case; eassumption.
    - eapply compat_case_load_copy; eassumption.
    - eapply compat_case_load_move; eassumption.
    - eapply compat_group; eassumption.
    - eapply compat_ungroup; eassumption.
    - eapply compat_fold; eassumption.
    - eapply compat_unfold; eassumption.
    - eapply compat_pack; eassumption.
    - eapply compat_unpack; eassumption.
    - eapply compat_tag; eassumption.
    - eapply compat_untag; eassumption.
    - eapply compat_cast; eassumption.
    - eapply compat_new; eassumption.
    - eapply compat_load_copy; eassumption.
    - eapply compat_load_move; eassumption.
    - eapply compat_store_weak; eassumption.
    - eapply compat_store_strong; eassumption.
    - eapply compat_swap; eassumption.
    - eapply compat_nil; eassumption.
    - eapply compat_app in Hcomp; eassumption.
    - eapply compat_singleton; eassumption.
    - eapply compat_frame; eassumption.
  Qed.

End Fundamental.
