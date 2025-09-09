From RichWasm.iris.rules Require Import iris_rules_pure iris_rules_trap.
From RichWasm.iris.language Require Import iris_wp_def logpred lenient_wp.
Import iris.algebra.list.
From iris.proofmode Require Import base tactics classes.
Set Bullet Behavior "Strict Subproofs".

Section lwp_pure.
  Context `{!wasmG Σ}.
  Open Scope bi_scope.
  
  Lemma lwp_unop s E Φ op t v v' (f: datatypes.frame) :
    app_unop op v = v' ->
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) [v'] ∗
    Φ.(lp_fr) f
    ⊢ lenient_wp s E [AI_basic (BI_const v); AI_basic (BI_unop t op)] (lp_run Φ).
  Proof.
    iIntros (Happ) "(Hf & Hrun & Hval & Hfr)".
    iApply (wp_wand with "[Hf Hrun Hval]").
    - iApply (wp_unop with "[$] [$]").
      eauto.
      by instantiate (1:= lp_noframe Φ).
    - iIntros (w) "[[Hnofr Hrun] Hf]".
      unfold lp_run.
      rewrite -lp_with_sep.
      iFrame.
  Qed.

  Lemma lwp_binop s E Φ op t v1 v2 v (f: datatypes.frame) :
    app_binop op v1 v2 = Some v →
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) [v] ∗
    Φ.(lp_fr) f
    ⊢ lenient_wp s E [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] (lp_run Φ).
  Proof.
    iIntros (Happ) "(Hf & Hrun & Hval & Hfr)".
    iApply (wp_wand with "[Hf Hrun Hval]").
    - iApply (wp_binop with "[$] [$]").
      eauto.
      by instantiate (1:= lp_noframe Φ).
    - iIntros (w) "[[Hnofr Hrun] Hf]".
      unfold lp_run.
      rewrite -lp_with_sep.
      iFrame.
  Qed.
  
  Lemma lwp_binop_failure s E Φ op t v1 v2 (f: datatypes.frame) :
    app_binop op v1 v2 = None →
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_trap) ∗
    Φ.(lp_fr) f
    ⊢ lenient_wp s E [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] Φ.
    iIntros (Happ) "(Hf & Hrun & Htrap & Hfr)".
    iApply (wp_wand with "[Hf Hrun Htrap]").
    - iApply (wp_binop_failure with "[Htrap] [$] [$]").
      eauto.
      by instantiate (1:= lp_nobail Φ).
    - iIntros (w) "[[Hbail Hrun] Hf]".
      destruct w; cbn; try iDestruct "Hbail" as "[]".
      by iFrame.
  Qed.

  Lemma lwp_relop s E Φ op t v1 v2 b (f: datatypes.frame) :
    app_relop op v1 v2 = b →
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) [VAL_int32 (wasm_bool b)] ∗
    Φ.(lp_fr) f
    ⊢ lenient_wp s E [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_relop t op)] (lp_run Φ).
  Proof.
    iIntros (Happ) "(Hf & Hrun & Hval & Hfr)".
    iApply (wp_wand with "[Hf Hrun Hval]").
    - iApply (wp_relop with "[$] [$]").
      eauto.
      by instantiate (1:= lp_noframe Φ).
    - iIntros (w) "[[Hnofr Hrun] Hf]".
      unfold lp_run.
      rewrite -lp_with_sep.
      iFrame.
  Qed.
  
  Lemma lwp_testop_i32 s E Φ v b op (f: datatypes.frame) :
    app_testop_i (e:=i32t) op v = b ->
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) [VAL_int32 (wasm_bool b)] ∗
    Φ.(lp_fr) f
    ⊢ lenient_wp s E [AI_basic (BI_const (VAL_int32 v)); AI_basic (BI_testop T_i32 op)] (lp_run Φ).
  Proof.
  Admitted.
  
  Lemma lwp_testop_i64 s E Φ v b op (f: datatypes.frame) :
    app_testop_i (e:=i64t) op v = b ->
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) [VAL_int32 (wasm_bool b)] ∗
    Φ.(lp_fr) f
    ⊢ lenient_wp s E [AI_basic (BI_const (VAL_int64 v)); AI_basic (BI_testop T_i64 op)] (lp_run Φ).
  Proof.
  Admitted.

  Lemma lwp_cvtop_convert s E Φ v v' t1 t2 sx (f: datatypes.frame) :
    cvt t2 sx v = Some v' ->
    types_agree t1 v ->
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) [v']
    ⊢ lenient_wp s E [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] (lp_run Φ).
  Proof.
  Admitted.

  Lemma lwp_cvtop_reinterpret s E Φ v v' t1 t2 (f: datatypes.frame) :
    wasm_deserialise (bits v) t2 = v' ->
    types_agree t1 v ->
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) [v']
    ⊢ lenient_wp s E [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] (lp_run Φ).
  Proof.
  Admitted.

  Lemma lwp_unreachable  s E Φ (f: datatypes.frame) :
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_trap)
    ⊢ lenient_wp s E [AI_basic BI_unreachable] Φ.
  Proof.
  Admitted.

  Lemma lwp_nop s E Φ :
    ↪[RUN] ∗
    denote_logpred Φ (immV [])
    ⊢ lenient_wp s E [AI_basic BI_nop] (lp_run Φ).
  Proof.
    iIntros "(HR & HΦ & %f & Hf & Hfpred)".
    unfold lp_run.
    iApply (wp_wand with "[HR HΦ Hf]").
    iApply (wp_nop with "[$] [$]").
    iApply "HΦ".
    iIntros (w) "[[Hnof HR] Hf]".
    iEval (rewrite -lp_with_sep).
    iFrame.
  Qed.

  Lemma lwp_drop s E Φ v (f: datatypes.frame) :
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) []
    ⊢ lenient_wp s E [AI_basic (BI_const v); AI_basic BI_drop] (lp_run Φ).
  Proof.
  Admitted.
  
  Lemma lwp_select_false s E Φ n v1 v2 (f: datatypes.frame) :
    n = Wasm_int.int_zero i32m ->
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) [v2]
    ⊢ lenient_wp s E 
        [AI_basic (BI_const v1); AI_basic (BI_const v2);
         AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_select)]
        (lp_run Φ).
  Proof.
  Admitted.
  
  Lemma lwp_select_true s E Φ n v1 v2 (f: datatypes.frame) :
    n = Wasm_int.int_zero i32m ->
    ↪[frame] f ∗
    ↪[RUN] ∗
    ▷ Φ.(lp_val) [v1]
    ⊢ lenient_wp s E 
        [AI_basic (BI_const v1); AI_basic (BI_const v2);
         AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_select)]
        (lp_run Φ).
  Proof.
  Admitted.

End lwp_pure.
