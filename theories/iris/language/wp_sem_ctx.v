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

  Lemma wp_vfill_push es n (vh : valid_holed n) s E Φ :
    WP es @ s; E CTX (lh_depth (lh_of_vh vh)); lh_of_vh vh {{ v, Φ v}} ⊢
    WP vfill vh es @ s; E {{ v, Φ v }}.
  Admitted.

  Lemma wp_ctx_vfill_push es n (vh : valid_holed n) s E Φ lh lh' d1 d2 :
    d1 = lh_depth (lh_plug lh (lh_of_vh vh)) ->
    d2 = lh_depth lh ->
    lh' = lh_plug lh (lh_of_vh vh) ->
    WP es @ s; E CTX d1; lh' {{ v, Φ v }} ⊢
    WP vfill vh es @ s; E CTX d2; lh {{ v, Φ v }}.
  Admitted.

  Lemma wp_ctx_br_stuck i j brV s E lh lh0 vh :
    lh = lh_plug lh0 vh ->
    i >= j ->
    (* vs ++ [br ...] *)
    ⊢ WP [AI_basic (BI_br i)] @ s; E CTX j; lh {{ v, ⌜v = brV vh⌝ }}.
  Admitted.

  Lemma wp_sem_ctx_block_peel (f: datatypes.frame) s E es LS RS ts Φ :
    ⊢ (↪[frame] f -∗ ↪[RUN] -∗ wp_sem_ctx s E es ((Φ f, Φ) :: LS, None) Φ) -∗
      ↪[frame] f -∗
      ↪[RUN] -∗
      wp_sem_ctx s E [BI_block (Tf [] ts) es] (LS, RS) Φ.
  Proof.
    iIntros "Hes Hf Hrun".
    iApply (wp_block _ _ _ [] with "[$] [$]"); eauto.
    iIntros "!> Hf Hrun".
    iSpecialize ("Hes" with "[$] [$]").
    iApply (wp_wand with "[Hes]").
    iApply wp_label_peel.
    {
      instantiate (1 := λ f v,
                     match v with
                     | immV vs => Φ f vs
                     | trapV => True
                     | brV i vh =>
                         match LS !! (i - lh_depth (lh_of_vh vh)) with
                         | Some (P, _) => P (get_base_l vh)
                         | None => False
                         end | _ => False end).
      iApply wp_label_bind.
      iApply (wp_wand with "[$Hes]").
      iIntros (w) "HΦ".
      iDestruct "HΦ" as "(%f' & Hf & H)".
      destruct w; try iFrame.
      - iDestruct "H" as "(_ & Hrun & HΦ)".
        change (LH_rec [] (length ts) [] (LH_base [] []) []) with
          (push_base (LH_base [] []) (length ts) [] [] []).
        iApply wp_label_pull_nil.
        iApply wp_wasm_empty_ctx.
        iApply (wp_wand with "[Hf Hrun HΦ]").
        {
          iApply (wp_label_value with "[$] [$]").
          - change (v_to_e_list l) with (iris.of_val (immV l)). apply iris.to_of_val.
          - by instantiate (1:= λ w, match w with immV vs => Φ f' vs | _ => False end).
        }
        iIntros (v) "[[Hv Hrun] Hf]".
        iExists f'. destruct v; first iFrame; by iExFalso.
      - admit.
      - iDestruct "H" as "(_ & Hrun & HΦ)".
        destruct i.
        + cbn. remember 0 as i. destruct lh; last congruence.
          subst n. cbn.
          admit.
        + cbn. iApply wp_ctx_vfill_push; try done.
          iApply wp_wand_ctx.
          {
            iApply wp_ctx_br_stuck; first done.
            admit.
          }
          iIntros (v ->).
          iExists f'. iFrame.
          admit.
      - iDestruct "H" as "(_ & _ & [])".
      - iDestruct "H" as "(_ & _ & [])".
    }
    iIntros (w) "HΦ".
    destruct w.
    - iDestruct "HΦ" as "(%f' & Hf & Hrun & HΦ)". iFrame.
    - iDestruct "HΦ" as "(%f' & Hf & Hrun & HΦ)". iFrame.
    - iDestruct "HΦ" as "(%f' & Hf & Hrun & HLS)". iFrame.
    - by iDestruct "HΦ" as "(%f' & Hf & Hrun & %Hcontra)".
    - by iDestruct "HΦ" as "(%f' & Hf & Hrun & %Hcontra)".
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
