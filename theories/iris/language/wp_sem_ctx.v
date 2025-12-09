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
  Definition lb_spec : Type :=
    (list value -> iProp Σ) * (datatypes.frame -> list value -> iProp Σ).
  
  Definition sem_ctx := list lb_spec.

  Definition wp_sem_ctx_post (S: sem_ctx) Φ :=
    {|
      lp_fr_inv := λ _, True;
      lp_trap := True;
      lp_val := Φ;
      lp_br := λ k lh,
        match S !! k with
        | Some (P, Q) =>
          P (get_base_l lh) ∗ (∀ f vs, Q f vs -∗ Φ f vs)
        | None => False
        end;
      lp_ret := λ _, False;
      lp_host := λ _ _ _ _, False;
    |}.

  Definition wp_sem_ctx s E es S Φ :=
    lenient_wp s E (to_e_list es) (wp_sem_ctx_post S Φ).

  Lemma wp_label_peel (f: datatypes.frame) s E m ces es Φ :
    ⊢ ↪[frame] f -∗
      ↪[RUN] -∗
      WP es @ s; E {{ v, Φ v ∗ ⌜match v with
                                | trapV | immV _ => True
                                | retV _ | brV _ _ | callHostV _ _ _ _ => False
                                end⌝ }} -∗
      WP [AI_label m ces es] @ s; E {{ w, Φ w }}.
  Proof.
    iIntros "Hfr Hrun Hes".
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_nil.
    cbn.
    iApply (wp_ctx_bind s E Φ es 1 _); first done.
    iApply (wp_wand with "[$Hes]").
    iIntros (w) "[HΦ %Hnobr]".
    destruct w.
    - iApply (wp_val_return with "[$] [$]").
      apply v_to_e_is_const_list.
      iIntros "Hfr Hrun".
      rewrite app_nil_r app_nil_l.
      iApply wp_value; done.
    - change (iris.of_val trapV) with ([] ++ [AI_trap] ++ []).
      iApply (wp_wand_ctx with "[Hfr]").
      + iApply wp_trap_ctx; done.
      + iIntros (w) "[-> Hf]".
        done.
    - by exfalso.
    - by exfalso.
    - by exfalso.
  Qed.

  Lemma wp_sem_ctx_br (f: datatypes.frame) s E LS k P Q vs Φ :
    ⊢ ↪[frame] f -∗
      ↪[RUN] -∗
      ⌜LS !! k = Some (P, Q)⌝ -∗
      P vs -∗
      (∀ f' vs', Q f' vs' -∗ Φ f' vs') -∗
      wp_sem_ctx s E (map BI_const vs ++ [BI_br k]) LS Φ.
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
    rewrite Hlb.
    iFrame.
  Qed.

  Lemma wp_sem_ctx_block_peel (f: datatypes.frame) s E es LS ts Φ :
    ⊢ ↪[frame] f -∗
      ↪[RUN] -∗
      wp_sem_ctx s E es [] Φ -∗
      wp_sem_ctx s E [BI_block (Tf [] ts) es] LS Φ.
  Proof.
    iIntros "Hf Hrun Hes".
    unfold wp_sem_ctx.
    cbn.
    unfold lenient_wp.
    iApply (wp_block _ _ _ [] with "[$] [$]"); eauto.
    iIntros "!> Hf Hrun".
    cbn.
    iApply (wp_label_peel with "[$] [$]").
    iApply (wp_wand with "[$Hes]").
    iIntros (w) "HΦ".
    destruct w.
    - iFrame.
    - iFrame.
    - unfold wp_sem_ctx_post, denote_logpred; cbn.
      rewrite lookup_nil.
      iDestruct "HΦ" as "(%f' & Hf & _ & Hrun & %Hcontra)".
      done.
    - iDestruct "HΦ" as "(%f' & Hf & _ & Hrun & %Hcontra)".
      done.
    - iDestruct "HΦ" as "(%f' & Hf & _ & Hrun & %Hcontra)".
      done.
  Qed.

End wp_sem_ctx.
