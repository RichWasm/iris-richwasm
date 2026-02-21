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
From RichWasm.iris.language Require Import iris_wp_def logpred.
Import iris.algebra.list.
From iris.proofmode Require Import base tactics classes.
Require Import lenient_wp.
Set Bullet Behavior "Strict Subproofs".

Section wp_sem_ctx.
  Context `{!wasmG Σ}.
  Open Scope bi_scope.
  (* Specification for a label. *)
  (* "protocol" from logics for effect handlers? *) 
  Definition lb_spec : Type := (list value -> iProp Σ) * (datatypes.frame -> list value -> iProp Σ).

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
      lp_fr_inv := λ _, True;
      lp_trap := True;
      lp_val := Φ;
      lp_br := λ i vh,
        match LS !! (i - lh_depth (lh_of_vh vh)) with
        | Some (P, Q) => P (get_base_l vh)
        | None => False
        end;
      lp_ret := λ svh,
        match RS with
        | Some (P, Q) => P (simple_get_base_l svh)
        | None => False
        end;
      lp_host := λ _ _ _ _, False;
    |}.

  Definition wp_sem_ctx s E es S Φ :=
    lenient_wp s E (to_e_list es) (wp_sem_ctx_post S Φ).

  Lemma wp_label_peel s E m ces es Φ :
    ⊢ WP es @ s; E CTX 1; LH_rec [] m [] (LH_base [] []) []
         {{ v, ∃ (f : datatypes.frame),
               ↪[frame] f ∗
                 match v with immV _ | brV _ _ => ↪[RUN] | trapV => ↪[BAIL] | _ => False end ∗
                 Φ f v }} -∗
      WP [AI_label m ces es] @ s; E
         {{ v, ∃ (f : datatypes.frame),
               ↪[frame] f ∗
                 match v with immV _ | brV _ _ => ↪[RUN] | trapV => ↪[BAIL] | _ => False end ∗
                 Φ f v }}.
  Admitted.
  (*
  Proof.
    iIntros "Hes".
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_nil.
    cbn.
    iApply (wp_ctx_bind s E _ es 1 _); first done.
    iApply (wp_wand with "[$Hes]").
    iIntros (w) "(%f & Hfr & HΦ & Hnobr)".
    destruct w.
    - iApply (wp_val_return with "[$] [$]").
      apply v_to_e_is_const_list.
      iIntros "Hfr Hrun".
      rewrite app_nil_r app_nil_l.
      iApply wp_value; try iFrame.
      reflexivity.
      auto.
    - change (iris.of_val trapV) with ([] ++ [AI_trap] ++ []).
      iApply (wp_wand_ctx with "[Hfr]").
      + iApply wp_trap_ctx; done.
      + iIntros (w) "[-> Hf]".
        iExists f.
        iFrame.
    - iDestruct "HΦ" as "[]".
    - iDestruct "HΦ" as "[]".
    - iDestruct "HΦ" as "[]".
  Qed.
  *)

  Lemma wp_sem_ctx_br (f: datatypes.frame) s E LS RS k P Q vs Φ :
    ⊢ ↪[frame] f -∗
      ↪[RUN] -∗
      ⌜LS !! k = Some (P, Q)⌝ -∗
      P vs -∗
      (∀ f' vs', Q f' vs' -∗ Φ f' vs') -∗
      wp_sem_ctx s E (map BI_const vs ++ [BI_br k]) (LS, RS) Φ.
  Proof.
    iIntros "Hf Hrun %Hlb HP HQ".
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
    iFrame.
  Qed.

  Fixpoint clear_base_l {i : nat} (vh : valid_holed i) : valid_holed i :=
    match vh with
    | VH_base n _ es => VH_base n [] es
    | VH_rec _ vs n es1 lh' es2 => VH_rec vs n es1 (clear_base_l lh') es2
    end.

  Lemma clear_base_l_depth {i: nat} (vh : valid_holed i) :
    lh_depth (lh_of_vh vh) = lh_depth (lh_of_vh (clear_base_l vh)).
  Admitted.

  Lemma vfill_move_base {i} (vh : valid_holed i) (es : list administrative_instruction) :
    vfill vh es = vfill (clear_base_l vh) (seq.cat (AI_basic ∘ BI_const <$> get_base_l vh) es).
  Admitted.

  Lemma wp_br_wrap s E n i j lh LI :
    j < i ->
    is_true (lfilled j lh [AI_basic (BI_br i)] LI) ->
    ⊢ WP [AI_label n [] LI]
         @ s; E
         {{ v, ∃ vh, ⌜v = @brV i vh⌝ ∗
                     ⌜lh_depth (lh_of_vh vh) = S j⌝ (* ∗
                     ⌜get_base_l vh = get_base_l lh⌝ *) }}.
  Admitted.

  Lemma cons_lookup_sub_lt {A} i j x (xs : list A) :
    j < i ->
    (x :: xs) !! (i - j) = xs !! (i - S j).
  Admitted.

  Lemma wp_sem_ctx_block_peel (f : datatypes.frame) s E es LS RS ts Φ :
    ⊢ □ (∀ f vs, Φ f vs -∗ Φ f vs ∗ ⌜length vs = length ts⌝) -∗
      (↪[frame] f -∗ ↪[RUN] -∗ wp_sem_ctx s E es ((Φ f, Φ) :: LS, None) Φ) -∗
      ↪[frame] f -∗
      ↪[RUN] -∗
      wp_sem_ctx s E [BI_block (Tf [] ts) es] (LS, RS) Φ.
  Proof.
    iIntros "#Hlen Hes Hf Hrun".
    iApply (wp_block _ _ _ [] with "[$] [$]"); eauto.
    iIntros "!> Hf Hrun".
    iSpecialize ("Hes" with "[$] [$]").
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_nil.
    iApply wp_label_bind.
    iApply (wp_wand with "Hes").
    iIntros (v) "HΦ".
    change (LH_rec [] (length ts) [] (LH_base [] []) []) with
      (push_base (LH_base [] []) (length ts) [] [] []).
    iApply wp_label_pull_nil.
    iApply wp_wasm_empty_ctx.
    destruct v.
    - iApply wp_wand.
      + iApply wp_label_value.
        * by rewrite iris.to_of_val.
        * admit. (* frame *)
        * admit. (* run *)
        * admit. (* goal *)
      + iIntros (v) "[[Hϕ Hrun] Hf]".
        admit. (* postcondition on value *)
    - admit. (* trap *)
    - destruct (Nat.eqb (lh_depth (lh_of_vh lh)) i) eqn:Hlh.
      + rewrite Nat.eqb_eq in Hlh.
        iDestruct "HΦ" as "(%f' & Hf & _ & [Hrun HΦ])".
        unfold iris.of_val.
        rewrite vfill_move_base.
        iSimpl in "HΦ".
        rewrite Hlh.
        rewrite Nat.sub_diag.
        iSimpl in "HΦ".
        iSpecialize ("Hlen" with "HΦ").
        iDestruct "Hlen" as "[HΦ %Hlen]".
        iApply (wp_br with "[$] [$]").
        3: {
          instantiate (2 := AI_basic ∘ BI_const <$> get_base_l lh).
          destruct (vfill_to_lfilled (clear_base_l lh) (seq.cat (AI_basic ∘ BI_const <$> get_base_l lh) [AI_basic (BI_br i)])) as [Hdepth Hfilled].
          rewrite clear_base_l_depth in Hlh.
          by rewrite Hlh in Hfilled.
        }
        * admit. (* const_list *)
        * admit. (* length *)
        * iIntros "!> Hf Hrun". admit.
      + destruct (vfill_to_lfilled lh []) as [Hi _].
        rewrite Nat.eqb_neq in Hlh.
        rename Hlh into Hlh'.
        assert (lh_depth (lh_of_vh lh) <= i /\ lh_depth (lh_of_vh lh) <> i) as Hlh.
        { done. }
        apply Nat.le_neq in Hlh.
        clear Hi Hlh'.
        iApply wp_wand.
        * iApply wp_br_wrap.
          -- exact Hlh.
          -- by destruct (vfill_to_lfilled lh [AI_basic (BI_br i)]) as [_ H].
        * iIntros (v) "(%vh & -> & %Hdepth)".
          unfold denote_logpred.
          iDestruct "HΦ" as "(%f' & Hfr & _ & [Hrun HΦ])".
          iExists f'. iFrame.
          unfold wp_sem_ctx_post, lp_br.
          rewrite Hdepth.
          rewrite (cons_lookup_sub_lt _ _ _ _ Hlh).
          (* bases should be the same *)
          admit.
    - iDestruct "HΦ" as "(%_ & _ & _ & [_ []])".
    - iDestruct "HΦ" as "(%_ & _ & _ & [_ []])".
  Abort.

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
