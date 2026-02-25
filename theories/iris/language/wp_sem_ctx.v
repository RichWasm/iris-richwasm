(* Weakest preconditions with a "semantic label context"

Ignoring some irrelevant bits, the wp_wasm_ctx modality is written
  WP es CTX lh {{ Q }}.
It is defined using the hole-filling operation lh[es], like this:
  WP es CTX lh {{ Q }} := WP lh[es] CTX lh {{ Q }}.
Unfortunately, the hole-filling operation renders proofs difficult. In this
file we outline a "logical approach" to the context which replaces
lh with a list of specifications (P, Q), one for each label in lh.
*)

From RichWasm.iris.rules Require Import iris_rules_structural iris_rules_trap iris_rules_bind iris_rules_control.
From RichWasm.iris.language Require Import iris_wp_def logpred lwp_structural.
Import iris.algebra.list.
From iris.proofmode Require Import base tactics classes.
Require Import lenient_wp.

Set Bullet Behavior "Strict Subproofs".

Section wp_sem_ctx.

  Context `{!wasmG Σ}.

  (* Specification for a label. *)
  (* "protocol" from logics for effect handlers? *) 
  Definition lb_spec : Type :=
    nat *
      (datatypes.frame -> list value -> iProp Σ) *
      (datatypes.frame -> list value -> iProp Σ).

  (* TODO: is postcondition the right shape? *)
  Definition ret_spec : Type := (list value -> iProp Σ) * (datatypes.frame -> list value -> iProp Σ).

  Definition sem_ctx : Type := list lb_spec * option ret_spec.

  (* TODO: duplicate in relations.v *)
  Fixpoint simple_get_base_l (lh : simple_valid_holed) :=
    match lh with
    | SH_base vs _ => vs
    | SH_rec _ _ _ lh' _ => simple_get_base_l lh'
    end.

  Definition wp_sem_ctx_post '((LS, RS) : sem_ctx) Φ :=
    {|
      lp_fr_inv _ := True;
      lp_trap := True;
      lp_val := Φ;
      lp_br fr i vh :=
        match LS !! (i - lh_depth (lh_of_vh vh)) with
        | Some (n, P, _) => ⌜length (get_base_l vh) = n⌝ ∗ P fr (get_base_l vh)
        | None => False
        end;
      lp_ret svh :=
        match RS with
        | Some (P, _) => P (simple_get_base_l svh)
        | None => False
        end;
      lp_host _ _ _ _ := False;
    |}%I.

  Definition wp_sem_ctx s E es S Φ :=
    lenient_wp s E (to_e_list es) (wp_sem_ctx_post S Φ).

  Lemma wp_sem_ctx_br (f: datatypes.frame) s E LS RS n k P Q vs Φ :
    LS !! k = Some (n, P, Q) ->
    length vs = n ->
    ↪[frame] f -∗
    ↪[RUN] -∗
    P f vs -∗
    (∀ f' vs', Q f' vs' -∗ Φ f' vs') -∗
    wp_sem_ctx s E (map BI_const vs ++ [BI_br k]) (LS, RS) Φ.
  Proof.
    iIntros (Hlb Hlen) "Hf Hrun HP HQ".
    unfold wp_sem_ctx, lenient_wp.
    unfold to_e_list.
    rewrite seq_map_fmap.
    rewrite fmap_app.
    remember (of_val (brV (VH_base k vs []))) as es.
    pose proof Heqes as Heqes'.
    cbn in Heqes.
    replace (v_to_e_list vs) with (AI_basic <$> map BI_const vs) in Heqes; last first.
    {
      unfold v_to_e_list.
      rewrite seq_map_fmap.
      by rewrite <- list_fmap_compose.
    }
    cbn.
    rewrite <- Heqes.
    rewrite Heqes'.
    iApply wp_value'.
    unfold wp_sem_ctx_post, denote_logpred; cbn.
    rewrite Nat.sub_0_r.
    rewrite Hlb.
    by iFrame.
  Qed.

  Lemma wp_sem_ctx_clear_labels s E es LS RS Φ :
    wp_sem_ctx s E es ([], RS) Φ ⊢
    wp_sem_ctx s E es (LS, RS) Φ.
  Proof.
    iIntros "Hwp".
    iApply (lwp_wand with "Hwp").
    iIntros (lv) "HΦ".
    destruct lv; try done.
    iDestruct "HΦ" as "(%f & Hfr & Hfrinv & HΦ)".
    unfold lp_noframe, lp_br, wp_sem_ctx_post.
    rewrite lookup_nil.
    iDestruct "HΦ" as "[_ []]".
  Qed.

  Fixpoint clear_base_l {i : nat} (vh : valid_holed i) : valid_holed i :=
    match vh with
    | VH_base n _ es => VH_base n [] es
    | VH_rec _ vs n es1 lh' es2 => VH_rec vs n es1 (clear_base_l lh') es2
    end.

  Lemma clear_base_l_depth {i: nat} (vh : valid_holed i) :
    lh_depth (lh_of_vh vh) = lh_depth (lh_of_vh (clear_base_l vh)).
  Admitted.

  Lemma vfill_move_base {i : nat} (vh : valid_holed i) (es : list administrative_instruction) :
    vfill vh es = vfill (clear_base_l vh) (seq.cat (AI_basic ∘ BI_const <$> get_base_l vh) es).
  Admitted.

  (* Copied from get_base_vh_decrease. *)
  Lemma lh_depth_vh_decrease {m : nat} (vh : valid_holed (S m)) vh' :
    vh_decrease vh = Some vh' ->
    lh_depth (lh_of_vh vh') = lh_depth (lh_of_vh vh).
  Proof.
    set (n := S m) in vh.
    pose (Logic.eq_refl : n = S m) as Hn.
    change vh with (match Hn in _ = w return valid_holed w with
                    | Logic.eq_refl => vh end).
    clearbody n Hn.
    generalize dependent m.
    induction vh; intros m vh' Hn.
    - destruct n => //=.
      pose proof (eq_add_S _ _ Hn) as Hm.
      assert (Hn = f_equal S Hm) as Hproof.
      apply Eqdep.EqdepTheory.UIP.
      replace (vh_decrease (match Hn in _ = w return (valid_holed w) with
                            | Logic.eq_refl => VH_base (S n) l l0 end)) with
        (match Hm in _ = w return (option (valid_holed w)) with
         | Logic.eq_refl => vh_decrease (VH_base (S n) l l0) end);
        last by rewrite Hproof; destruct Hm.
      destruct Hm; simpl. intros H; inversion H; subst vh'.
      clear. destruct Hn. done.
    - pose proof (eq_add_S _ _ Hn) as Hm.
      assert (Hn = f_equal S Hm) as Hproof.
      apply Eqdep.EqdepTheory.UIP.
      replace (vh_decrease (match Hn in _ = w return (valid_holed w) with
                            | Logic.eq_refl => VH_rec l n0 l0 vh l1 end)) with
        (match Hm in _ = w return (option (valid_holed w)) with
         | Logic.eq_refl => vh_decrease (VH_rec l n0 l0 vh l1) end);
        last by rewrite Hproof ; destruct Hm.
      replace (get_base_l match Hn in (_ = w) return (valid_holed w) with
                 | Logic.eq_refl => VH_rec l n0 l0 vh l1
                 end) with
        (match Hm in _ = w return (list value) with
         | Logic.eq_refl => get_base_l (VH_rec l n0 l0 vh l1) end);
        last by rewrite Hproof; destruct Hm.
      destruct Hm => //=.
      destruct n => //=.
      destruct (vh_decrease vh) eqn:Hvh => //.
      intros H; inversion H; subst vh'.
      simpl.
      pose proof (eq_add_S _ _ Hn) as Hm.
      pose proof (eq_add_S _ _ Hm) as Hp.
      assert (Hm = f_equal S Hp) as Hproof'.
      apply Eqdep.EqdepTheory.UIP.
      specialize (IHvh n v Hm).
      rewrite IHvh.
      (* This is the only line that's different... *)
      { clear. destruct Hm. by destruct Hn. }
      replace (vh_decrease match Hm in (_ = w) return (valid_holed w) with
                 | Logic.eq_refl => vh
                 end) with
        (match Hp in (_ = w) return (option (valid_holed w)) with
         | Logic.eq_refl => vh_decrease vh end); last by rewrite Hproof'; clear; destruct Hp.
      rewrite Hvh. clear.
      assert (Hp = Logic.eq_refl).
      apply Eqdep.EqdepTheory.UIP.
      rewrite H. done.
  Qed.

  Lemma wp_br_wrap s E n i (vh : valid_holed i) es esk :
    lh_depth (lh_of_vh vh) < i ->
    es = vfill vh [AI_basic (BI_br i)] ->
    ⊢ WP [AI_label n esk es]
         @ s; E
         {{ v, ∃ vh', ⌜v = @brV i vh'⌝ ∗
                      ⌜lh_depth (lh_of_vh vh') = S (lh_depth (lh_of_vh vh))⌝ ∗
                      ⌜get_base_l vh = get_base_l vh'⌝ }}.
  Proof.
    iIntros (Hdepth ->) "*".
    destruct (Nat.lt_exists_pred _ _ Hdepth) as [j [-> _]].
    destruct (vh_decrease vh) as [vh' |] eqn:Hvh.
    - iApply wp_value.
      + instantiate (1 := brV (VH_rec [] n esk vh' [])).
        by rewrite (vfill_decrease _ Hvh).
      + iExists (VH_rec [] n esk vh' []).
        repeat iSplit; iPureIntro.
        * done.
        * cbn. by rewrite (lh_depth_vh_decrease vh).
        * cbn. by rewrite (get_base_vh_decrease Hvh).
    - exfalso. eapply vh_depth_can_decrease.
      + exact Hdepth.
      + exact Hvh.
  Qed.

  Lemma cons_lookup_sub_lt {A} i j x (xs : list A) :
    j < i ->
    (x :: xs) !! (i - j) = xs !! (i - S j).
  Admitted.

  Definition is_basic_const (e : basic_instruction) : bool :=
    match e with
    | BI_const _ => true
    | _ => false
    end.

  Definition basic_const_list (es : list basic_instruction) : bool :=
    forallb is_basic_const es.

  Lemma const_list_map_basic vs :
    is_true (basic_const_list vs) ->
    is_true (const_list (map AI_basic vs)).
  Proof.
    intros Hvs.
    apply forallb_forall.
    intros e He.
    unfold is_true, basic_const_list in Hvs.
    rewrite forallb_forall in Hvs.
    apply in_map_iff in He.
    destruct He as (e' & <- & He').
    specialize Hvs with e'.
    by apply Hvs in He'.
  Qed.

  Lemma wp_sem_ctx_block_peel (f : datatypes.frame) s E es LS RS vs ts1 ts2 Φ :
    is_true (basic_const_list vs) ->
    length vs = length ts1 ->
    ↪[frame] f -∗
    ↪[RUN] -∗
    (↪[frame] f -∗ ↪[RUN] -∗ wp_sem_ctx s E (vs ++ es) ((length ts2, Φ, Φ) :: LS, None) Φ) -∗
    wp_sem_ctx s E (vs ++ [BI_block (Tf ts1 ts2) es]) (LS, RS) Φ.
  Proof.
    iIntros (Hconst Hlen) "Hf Hrun Hes".
    unfold wp_sem_ctx, to_e_list.
    change seq.map with (@map basic_instruction administrative_instruction).
    rewrite !map_app.
    iApply (lenient_wp_block _ _ _ _ with "[$] [$]"); eauto.
    { by apply const_list_map_basic. }
    { by rewrite length_map. }
    iIntros "!> Hf Hrun".
    iSpecialize ("Hes" with "[$] [$]").
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_nil.
    iApply wp_label_bind.
    iApply (wp_wand with "Hes").
    iIntros (v) "HΦ".
    change (LH_rec [] (length ts2) [] (LH_base [] []) []) with
      (push_base (LH_base [] []) (length ts2) [] [] []).
    iApply wp_label_pull_nil.
    iApply wp_wasm_empty_ctx.
    destruct v.
    - iDestruct "HΦ" as "(%f' & Hfr & _ & Hrun & HΦ)".
      iApply (wp_wand with "[Hfr Hrun HΦ]").
      + iApply (wp_label_value with "[$] [$]"); first by rewrite iris.to_of_val.
        instantiate (1 := fun v => (∃ vs, ⌜v = immV vs⌝ ∗ Φ f' vs)%I).
        by iFrame.
      + iIntros (v) "[[(%vs' & -> & Hϕ) Hrun] Hf]". iExists f'. iFrame.
    - iDestruct "HΦ" as "(%f' & Hfr & _ & Hbail & _)".
      iApply (wp_wand with "[Hfr]").
      + iApply (wp_label_trap with "[$]"); first done.
        by instantiate (1 := fun v => (⌜v = trapV⌝)%I).
      + iIntros (v) "(-> & Hfr)".
        iExists f'. by iFrame.
    - destruct (Nat.eqb (lh_depth (lh_of_vh lh)) i) eqn:Hlh.
      + rewrite Nat.eqb_eq in Hlh.
        iDestruct "HΦ" as "(%f' & Hf & _ & [Hrun HΦ])".
        unfold iris.of_val.
        rewrite vfill_move_base.
        iSimpl in "HΦ".
        rewrite Hlh.
        rewrite Nat.sub_diag.
        iSimpl in "HΦ".
        iDestruct "HΦ" as "[%Hlen2 HΦ]".
        iApply (wp_br with "[$] [$]").
        3: {
          instantiate (2 := v_to_e_list (get_base_l lh)).
          destruct (vfill_to_lfilled (clear_base_l lh) (seq.cat (v_to_e_list (get_base_l lh)) [AI_basic (BI_br i)])) as [Hdepth Hfilled].
          rewrite clear_base_l_depth in Hlh.
          by rewrite Hlh in Hfilled.
        }
        * apply forallb_forall.
          apply List.Forall_forall.
          apply Forall_forall.
          intros e He.
          rewrite elem_of_list_fmap in He.
          by destruct He as (v & -> & Hv).
        * by rewrite length_fmap.
        * iIntros "!> Hf Hrun".
          rewrite app_nil_r.
          iApply wp_value.
          -- instantiate (1 := immV (get_base_l lh)). by unfold IntoVal.
          -- iExists f'. iFrame.
      + destruct (vfill_to_lfilled lh []) as [Hi _].
        rewrite Nat.eqb_neq in Hlh.
        rename Hlh into Hlh'.
        assert (lh_depth (lh_of_vh lh) <= i /\ lh_depth (lh_of_vh lh) <> i) as Hlh; first done.
        apply Nat.le_neq in Hlh.
        clear Hi Hlh'.
        iApply wp_wand.
        * iApply wp_br_wrap; [exact Hlh | done].
        * iIntros (v) "(%vh & -> & %Hdepth & %Hbase)".
          unfold denote_logpred.
          iDestruct "HΦ" as "(%f' & Hfr & _ & [Hrun HΦ])".
          iExists f'. iFrame.
          unfold wp_sem_ctx_post, lp_br.
          rewrite Hdepth.
          rewrite (cons_lookup_sub_lt _ _ _ _ Hlh).
          by rewrite Hbase.
    - iDestruct "HΦ" as "(%_ & _ & _ & [_ []])".
    - iDestruct "HΦ" as "(%_ & _ & _ & [_ []])".
  Qed.

  Lemma wp_semctx_loop (f : datatypes.frame) s E es LS RS vs ts1 ts2 Φ Ψ :
    length vs = length ts1 ->
    ↪[frame] f -∗
    ↪[RUN] -∗
    Ψ f vs -∗
    □ (∀ f' vs',
         ↪[frame] f' -∗ ↪[RUN] -∗ Ψ f' vs' -∗
         wp_sem_ctx s E (map BI_const vs' ++ es) ((length ts1, Ψ, Φ) :: LS, None) Φ) -∗
    wp_sem_ctx s E (map BI_const vs ++ [BI_loop (Tf ts1 ts2) es]) (LS, RS) Φ.
  Proof.
    iIntros (Hlen) "Hfr Hrun HΨ #Hloop".
    unfold wp_sem_ctx, lenient_wp, to_e_list.
    change seq.map with (@map basic_instruction administrative_instruction).
    rewrite !map_app.
    change (map AI_basic [BI_loop (Tf ts1 ts2) es]) with [AI_basic (BI_loop (Tf ts1 ts2) es)].
    rewrite map_map.
    change (@map value administrative_instruction) with (@seq.map value administrative_instruction).
    fold (v_to_e_list vs).
    iLöb as "IH" forall (f vs Hlen).
    iApply (wp_loop with "[$] [$]").
    { apply v_to_e_is_const_list. }
    { by rewrite length_map. }
    { done. }
    { done. }
    iIntros "!> Hfr Hrun".
    iPoseProof ("Hloop" with "[$] [$] [$]") as "Hes".
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_nil.
    iApply wp_label_bind.
    rewrite map_app.
    rewrite map_map.
    change (@map value administrative_instruction) with (@seq.map value administrative_instruction).
    fold (v_to_e_list vs).
    iApply (wp_wand with "Hes").
    iIntros (v) "HΦ".
    change (LH_rec [] (length ts1) [AI_basic (BI_loop (Tf ts1 ts2) es)] (LH_base [] []) []) with
      (push_base (LH_base [] []) (length ts1) [AI_basic (BI_loop (Tf ts1 ts2) es)] [] []).
    iApply wp_label_pull_nil.
    iApply wp_wasm_empty_ctx.
    destruct v.
    - iDestruct "HΦ" as "(%f' & Hfr & _ & Hrun & HΦ)".
      iApply (wp_wand with "[Hfr Hrun HΦ]").
      + iApply (wp_label_value with "[$] [$]"); first by rewrite iris.to_of_val.
        instantiate (1 := fun v => (∃ vs, ⌜v = immV vs⌝ ∗ Φ f' vs)%I).
        by iFrame.
      + iIntros (v) "[[(%vs' & -> & Hϕ) Hrun] Hf]". iExists f'. iFrame.
    - iDestruct "HΦ" as "(%f' & Hfr & _ & Hbail & _)".
      iApply (wp_wand with "[Hfr]").
      + iApply (wp_label_trap with "[$]"); first done.
        by instantiate (1 := fun v => (⌜v = trapV⌝)%I).
      + iIntros (v) "(-> & Hfr)".
        iExists f'. by iFrame.
    - destruct (Nat.eqb (lh_depth (lh_of_vh lh)) i) eqn:Hlh.
      + rewrite Nat.eqb_eq in Hlh.
        iDestruct "HΦ" as "(%f' & Hf & _ & [Hrun HΦ])".
        unfold iris.of_val.
        rewrite vfill_move_base.
        iSimpl in "HΦ".
        rewrite Hlh.
        rewrite Nat.sub_diag.
        iSimpl in "HΦ".
        iDestruct "HΦ" as "[%Hlen_lh HΦ]".
        iApply (wp_br with "[$] [$]").
        3: {
          instantiate (2 := v_to_e_list (get_base_l lh)).
          destruct (vfill_to_lfilled (clear_base_l lh) (seq.cat (v_to_e_list (get_base_l lh)) [AI_basic (BI_br i)])) as [Hdepth Hfilled].
          rewrite clear_base_l_depth in Hlh.
          by rewrite Hlh in Hfilled.
        }
        {
          apply forallb_forall.
          apply List.Forall_forall.
          apply Forall_forall.
          intros e He.
          rewrite elem_of_list_fmap in He.
          by destruct He as (v & -> & Hv).
        }
        { by rewrite map_length. }
        iIntros "!> Hf Hrun".
        iApply ("IH" with "[] [$] [$]"); done.
      + destruct (vfill_to_lfilled lh []) as [Hi _].
        rewrite Nat.eqb_neq in Hlh.
        rename Hlh into Hlh'.
        assert (lh_depth (lh_of_vh lh) <= i /\ lh_depth (lh_of_vh lh) <> i) as Hlh; first done.
        apply Nat.le_neq in Hlh.
        clear Hi Hlh'.
        iApply wp_wand.
        * iApply wp_br_wrap; [exact Hlh | done].
        * iIntros (v) "(%vh & -> & %Hdepth & %Hbase)".
          unfold denote_logpred.
          iDestruct "HΦ" as "(%f' & Hfr & _ & [Hrun HΦ])".
          iExists f'. iFrame.
          unfold wp_sem_ctx_post, lp_br.
          rewrite Hdepth.
          rewrite (cons_lookup_sub_lt _ _ _ _ Hlh).
          by rewrite Hbase.
    - iDestruct "HΦ" as "(%_ & _ & _ & [_ []])".
    - iDestruct "HΦ" as "(%_ & _ & _ & [_ []])".
  Qed.

  Definition sem_ctx_imp : sem_ctx -> sem_ctx -> iProp Σ.
  Admitted.

  Lemma sem_ctx_imp_bot LS :
    ⊢ sem_ctx_imp ([], None) LS.
  Admitted.

  Lemma wp_sem_ctx_mono s E es LS LS' Φ Φ' :
    ⊢ sem_ctx_imp LS LS' -∗
      (∀ f vs, Φ f vs -∗ Φ' f vs) -∗
      wp_sem_ctx s E es LS Φ -∗
      wp_sem_ctx s E es LS' Φ'.
  Proof.
  Admitted.

End wp_sem_ctx.
