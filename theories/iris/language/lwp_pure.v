From RichWasm.iris.rules Require Import iris_rules_pure iris_rules_trap.
From RichWasm.iris.language Require Import iris_wp_def logpred lenient_wp.
Import iris.algebra.list.
From iris.proofmode Require Import base tactics classes.
Set Bullet Behavior "Strict Subproofs".

Section lwp_pure.
  Context `{!wasmG Σ}.
  Open Scope bi_scope.
  
  Lemma lwp_binop s E Φ op t v1 v2 v (f: datatypes.frame) :
    app_binop op v1 v2 = Some v →
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) f [v] ∗
    Φ.(lp_fr_inv) f
    ⊢ lenient_wp s E [AI_basic (BI_const v1);
                      AI_basic (BI_const v2); AI_basic (BI_binop t op)] Φ.
  Proof.
    iIntros (Happ) "(Hf & Hrun & Hval & Hfrinv)".
    iApply (wp_wand with "[Hf Hrun Hval]").
    - iApply (wp_binop with "[$] [$]").
      eauto.
      instantiate (1:= λ v, ↪[RUN] -∗ lp_noframe Φ f v).
      iFrame.
      by iIntros "!> ?".
    - iIntros (w) "[[Hnofr Hrun] Hf]".
      iSpecialize ("Hnofr" with "Hrun").
      iFrame.
  Qed.

  (* IS THIS SUS WHAT IS THIS *)
  Lemma lwp_binop_failure s E Φ op v1 v2 t f:
    app_binop op v1 v2 = None →
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_trap) ∗
    Φ.(lp_fr) f ∗
    Φ.(lp_fr_inv) f
    ⊢ lenient_wp s E [AI_basic (BI_const v1); AI_basic (BI_const v2);
      AI_basic (BI_binop t op)] Φ.
  Proof.
    iIntros (Happ) "(Hf & Hrun & Hval & Hfr & Hfrinv)".
    iApply (wp_wand with "[Hf Hfr Hrun Hval]").
    - iApply (wp_binop_failure with "[Hval] [$Hf] [$Hrun]").
      eauto.
      instantiate (1:= λ v, ↪[BAIL] -∗ lp_noframe Φ f v).
      iFrame.
      by iIntros "!> ?".
    - iIntros (w) "[[Hnofr Hrun] Hf]".
      iSpecialize ("Hnofr" with "Hrun").
      iFrame.
  Qed.

  Lemma lwp_cvtop_convert s E sx t1 t2 v v' f Φ :
    cvt t2 sx v = Some v' →
    is_true (types_agree t1 v) →
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) [v'] ∗
    Φ.(lp_fr) f ∗
    Φ.(lp_fr_inv) f
    ⊢ lenient_wp s E [AI_basic (BI_const v);
      AI_basic (BI_cvtop t2 CVO_convert t1 sx)] Φ.
  Proof.
    iIntros (Happ Htypesagree) "(Hf & Hrun & Hval & Hfr & Hfrinv)".
    iApply (wp_wand with "[Hf Hfr Hrun Hval]").
    - iApply (wp_cvtop_convert with "[$] [$]").
      eauto. auto.
      instantiate (1:= λ v, ↪[RUN] -∗ lp_noframe Φ f v).
      iFrame.
      by iIntros "!> ?".
    - iIntros (w) "[[Hnofr Hrun] Hf]".
      iSpecialize ("Hnofr" with "Hrun").
      iFrame.
  Qed.

  Lemma lwp_cvtop_convert_failure s E Φ sx t1 t2 v f :
    cvt t2 sx v = None →
    is_true (types_agree t1 v) →
    ↪[frame] f ∗
    ↪[BAIL] ∗
    ▷ Φ.(lp_trap) ∗
    Φ.(lp_fr) f ∗
    Φ.(lp_fr_inv) f
    ⊢ lenient_wp s E [AI_basic (BI_const v);
      AI_basic (BI_cvtop t2 CVO_convert t1 sx)] Φ.
  Proof.
    iIntros (Happ Htypesagree) "(Hf & Hrun & Htrap & Hfr & Hfrinv)".
    iApply (wp_wand with "[Hf Hfr Hrun Htrap]").
    About wp_cvtop_convert_failure.
    (*
      Can't figure out how to get this to work
    - iApply (wp_cvtop_convert_failure with "[$] [$]").
      auto. auto.
      instantiate (1:= lp_noframe Φ f).
      iFrame.
      by iIntros "!> ?".
    - iIntros (w) "[[Hnofr Hrun] Hf]".
      iSpecialize ("Hnofr" with "Hrun").
      iFrame.
     *)

  Admitted.

  Lemma lwp_cvtop_reinterpret s E Φ t1 t2 v v' f :
    wasm_deserialise (bits v) t2 = v' →
    is_true (types_agree t1 v) →
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) [v'] ∗
    Φ.(lp_fr) f ∗
    Φ.(lp_fr_inv) f
    ⊢ lenient_wp s E [AI_basic (BI_const v);
      AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] Φ.
  Proof.
    iIntros (Happ Htypesagree) "(Hf & Hrun & Hval & Hfr & Hfrinv)".
    iApply (wp_wand with "[Hf Hfr Hrun Hval]").
    - iApply (wp_cvtop_reinterpret with "[$] [$]").
      eauto. auto.
      instantiate (1:= λ v, ↪[RUN] -∗ lp_noframe Φ f v).
      iFrame.
      by iIntros "!> ?".
    - iIntros (w) "[[Hnofr Hrun] Hf]".
      iSpecialize ("Hnofr" with "Hrun").
      iFrame.
  Admitted.

  Lemma lwp_unop s E Φ op t v1 v (f: datatypes.frame) :
    app_unop op v1 = v →
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) f [v] ∗
    Φ.(lp_fr_inv) f
    ⊢ lenient_wp s E [AI_basic (BI_const v1); AI_basic (BI_unop t op)] Φ.
  Proof.
    iIntros (Happ) "(Hf & Hrun & Hval & Hfrinv)".
    iApply (wp_wand with "[Hf Hrun Hval]").
    - iApply (wp_unop with "[$] [$]"); eauto.
      instantiate (1:= λ v, ↪[RUN] -∗ lp_noframe Φ f v).
      iFrame.
      by iIntros "!> ?".
    - iIntros (w) "[[Hnofr Hrun] Hf]".
      iSpecialize ("Hnofr" with "Hrun").
      iFrame.
  Qed.

  (* the wp versions are split into i32 and i64 for some reason *)
  Lemma lwp_testop_i32 s E Φ op v b f :
    app_testop_i (e:=i32t) op v = b →
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) [VAL_int32 (wasm_bool b)] ∗
    Φ.(lp_fr) f ∗
    Φ.(lp_fr_inv) f
    ⊢ lenient_wp s E [AI_basic (BI_const (VAL_int32 v));
      AI_basic (BI_testop T_i32 op)] Φ.
  Proof.
    iIntros (Happ) "(Hf & Hrun & Hval & Hfr & Hfrinv)".
    iApply (wp_wand with "[Hf Hfr Hrun Hval]").
    - iApply (wp_testop_i32 with "[$] [$]"); eauto.
      instantiate (1:= λ v, ↪[RUN] -∗ lp_noframe Φ f v).
      iFrame.
      by iIntros "!> ?".
    - iIntros (w) "[[Hnofr Hrun] Hf]".
      iSpecialize ("Hnofr" with "Hrun").
      iFrame.
  Qed.
  Lemma lwp_testop_i64 s E Φ op v b f :
    app_testop_i (e:=i64t) op v = b →
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) [VAL_int32 (wasm_bool b)] ∗
    Φ.(lp_fr) f ∗
    Φ.(lp_fr_inv) f
    ⊢ lenient_wp s E [AI_basic (BI_const (VAL_int64 v));
      AI_basic (BI_testop T_i64 op)] Φ.
  Proof.
    iIntros (Happ) "(Hf & Hrun & Hval & Hfr & Hfrinv)".
    iApply (wp_wand with "[Hf Hfr Hrun Hval]").
    - iApply (wp_testop_i64 with "[$] [$]"); eauto.
      instantiate (1:= λ v, ↪[RUN] -∗ lp_noframe Φ f v).
      iFrame.
      by iIntros "!> ?".
    - iIntros (w) "[[Hnofr Hrun] Hf]".
      iSpecialize ("Hnofr" with "Hrun").
      iFrame.
  Qed.



  Lemma lwp_relop s E Φ op t v1 v2 b (f: datatypes.frame) :
    app_relop op v1 v2 = b →
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) f [VAL_int32 (wasm_bool b)] ∗
    Φ.(lp_fr_inv) f
    ⊢ lenient_wp s E [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_relop t op)] Φ.
  Proof.
    iIntros (Happ) "(Hf & Hrun & Hval & Hfrinv)".
    iApply (wp_wand with "[Hf Hrun Hval]").
    - iApply (wp_relop with "[$] [$]").
      eauto.
      instantiate (1:= λ v, ↪[RUN] -∗ lp_noframe Φ f v).
      iFrame.
      by iIntros "!> ?".
    - iIntros (w) "[[Hnofr Hrun] Hf]".
      iSpecialize ("Hnofr" with "Hrun").
      iFrame.
  Qed.

  Lemma lwp_testop_i32 s E Φ op v b (f: datatypes.frame) :
    app_testop_i (e:=i32t) op v = b →
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) f [VAL_int32 (wasm_bool b)] ∗
    Φ.(lp_fr_inv) f
    ⊢ lenient_wp s E [AI_basic (BI_const (VAL_int32 v)); AI_basic (BI_testop T_i32 op)] Φ.
  Proof.
    iIntros (Happ) "(Hf & Hrun & Hval & Hfrinv)".
    iApply (wp_wand with "[Hf Hrun Hval]").
    - iApply (wp_testop_i32 with "[$] [$]").
      eauto.
      instantiate (1:= λ v, ↪[RUN] -∗ lp_noframe Φ f v).
      iFrame.
      by iIntros "!> ?".
    - iIntros (w) "[[Hnofr Hrun] Hf]".
      iSpecialize ("Hnofr" with "Hrun").
      iFrame.
  Qed.

  Lemma lwp_testop_i64 s E Φ op v b (f: datatypes.frame) :
    app_testop_i (e:=i64t) op v = b →
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) f [VAL_int32 (wasm_bool b)] ∗
    Φ.(lp_fr_inv) f
    ⊢ lenient_wp s E [AI_basic (BI_const (VAL_int64 v)); AI_basic (BI_testop T_i64 op)] Φ.
  Proof.
    iIntros (Happ) "(Hf & Hrun & Hval & Hfrinv)".
    iApply (wp_wand with "[Hf Hrun Hval]").
    - iApply (wp_testop_i64 with "[$] [$]").
      eauto.
      instantiate (1:= λ v, ↪[RUN] -∗ lp_noframe Φ f v).
      iFrame.
      by iIntros "!> ?".
    - iIntros (w) "[[Hnofr Hrun] Hf]".
      iSpecialize ("Hnofr" with "Hrun").
      iFrame.
  Qed.

  Lemma lenient_wp_nop s E Φ f :
    ⊢ ↪[RUN] -∗
      ↪[frame] f -∗
      ▷ Φ.(lp_val) f [] -∗
      Φ.(lp_fr_inv) f -∗
      lenient_wp s E [AI_basic BI_nop] Φ.
  Proof.
    iIntros "HR Hf HΦ Hfrinv".
    iApply (wp_wand with "[HR HΦ Hf]").
    iApply (wp_nop with "[$] [$]").
    - instantiate (1 := λ v, ↪[RUN] -∗ lp_noframe Φ f v).
      iFrame.
      by iIntros "!> ?".
    - iIntros (w) "[[Hnof HR] Hf]".
      iSpecialize ("Hnof" with "HR").
      iFrame.
  Qed.

End lwp_pure.
