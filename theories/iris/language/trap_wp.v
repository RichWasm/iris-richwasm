From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
Require Import iris_wp_def iris_rules_pure iris_rules_structural.

Section wp_bail.
  Context `{!wasmG Σ}.
  Variables (s: stuckness) (E: coPset).

  Definition bail_post Φv Φbr Φret Φhost :=
    λ w,
      match w with
      | trapV => ↪[BAIL]
      | immV v => Φv v ∗ ↪[RUN]
      | brV i lh => Φbr i lh ∗ ↪[RUN]
      | retV lh => Φret lh ∗ ↪[RUN]
      | callHostV ft hf vs lh => Φhost ft hf vs lh ∗ ↪[RUN]
      end%I.

  Definition wp_bail
    (e: language.expr wasm_lang)
    (Φv : list value → iProp Σ)
    (Φbr : ∀ x : nat, valid_holed x → iProp Σ)
    (Φret : simple_valid_holed → iProp Σ)
    (Φhost : function_type → hostfuncidx → list value → llholed → iProp Σ) 
    : iProp Σ :=
    ↪[RUN] -∗
    WP e @ s; E {{ bail_post Φv Φbr Φret Φhost }}.

    Lemma wp_nil (Φ : iProp Σ) f :
      ↪[frame] f ∗ Φ ⊢ wp_bail [] (fun v => Φ) (λ _ _, False%I) (λ _, False%I) (λ _ _ _ _, False%I).
    Proof using.
      iIntros "[Hframe HΦ] Hrun".
      rewrite wp_unfold. unfold wp_pre. iFrame. done.
    Qed.

    Lemma wp_val (Φ: val -> iProp Σ) (v: value) (es: language.expr wasm_lang) :
      wp_bail es (λ w, Φ (val_combine (immV [v]) w)) ⊢ wp_bail (AI_basic (BI_const v) :: es) (λ w, Φ w).
    Proof.
      iIntros "Hes Hrun".
      iPoseProof ("Hes" with "Hrun") as "Hes".
      rewrite !wp_unfold /wp_pre /=.
      iEval (cbn).
      destruct (to_val es) as [vs|] eqn:Hesval.
      - admit.
      - rewrite to_val_cons_None; [|done].
        iIntros (σ ns κ κs nt) "Hσ".
        iSpecialize ("Hes" $! σ ns κ κs nt with "[$]").
        iMod "Hes".
        iModIntro.
        iDestruct "Hes" as "(%Hstuck & Hes)".
        iSplit.
        + destruct s.
          * admit.
          * admit.
        + 

      rewrite -seq.cat1s.
      Search wp BI_const.
      Check wp_val_app.
    iSplit.
  destruct (

  unfold wp, wp_wasm, wp'.
  Search wp.

  
