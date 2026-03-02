Require Import iris.proofmode.tactics.

From RichWasm.iris.language Require Import iris_wp_def lwp_pure.
Require Import RichWasm.iris.language.cwp.def.
Require Import RichWasm.iris.rules.iris_rules_pure.

Set Bullet Behavior "Strict Subproofs".

Section numeric.

  Context `{!wasmG Σ}.

  Lemma cwp_unop s E (f : frame) v v' t op L R Φ :
    app_unop op v = v' ->
    ↪[frame] f -∗
    ↪[RUN] -∗
    ▷ Φ f [v'] -∗
    CWP [BI_const v; BI_unop t op] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hop) "Hf Hrun HΦ".
    iApply lwp_unop; first done.
    iFrame.
  Qed.

  Lemma cwp_binop s E (f : frame) v1 v2 v t op L R Φ :
    app_binop op v1 v2 = Some v ->
    ↪[frame] f -∗
    ↪[RUN] -∗
    ▷ Φ f [v] -∗
    CWP [BI_const v1; BI_const v2; BI_binop t op] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hop) "Hf Hrun HΦ".
    iApply lwp_binop; first done.
    iFrame.
  Qed.

  Lemma cwp_binop_fail s E (f : frame) v1 v2 t op L R Φ :
    app_binop op v1 v2 = None ->
    ↪[frame] f -∗
    ↪[RUN] -∗
    CWP [BI_const v1; BI_const v2; BI_binop t op] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hop) "Hf Hrun".
    iApply lwp_binop_failure; first done.
    by iFrame.
  Qed.

  Lemma cwp_testop_i32 s E (f : frame) v b op L R Φ :
    app_testop_i op v = b ->
    ↪[frame] f -∗
    ↪[RUN] -∗
    ▷ Φ f [VAL_int32 (wasm_bool b)] -∗
    CWP [BI_const (VAL_int32 v); BI_testop T_i32 op] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hop) "Hf Hrun HΦ".
    iApply lwp_testop_i32; first done.
    iFrame.
  Qed.

  Lemma cwp_testop_i64 s E (f : frame) v b op L R Φ :
    app_testop_i op v = b ->
    ↪[frame] f -∗
    ↪[RUN] -∗
    ▷ Φ f [VAL_int32 (wasm_bool b)] -∗
    CWP [BI_const (VAL_int64 v); BI_testop T_i64 op] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hop) "Hf Hrun HΦ".
    iApply lwp_testop_i64; first done.
    iFrame.
  Qed.

  Lemma cwp_relop s E (f : frame) v1 v2 b t op L R Φ :
    app_relop op v1 v2 = b ->
    ↪[frame] f -∗
    ↪[RUN] -∗
    ▷ Φ f [VAL_int32 (wasm_bool b)] -∗
    CWP [BI_const v1; BI_const v2; BI_relop t op] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hop) "Hf Hrun HΦ".
    iApply lwp_relop; first done.
    iFrame.
  Qed.

  Lemma cwp_cvtop_convert s E (f : frame) v v' t1 t2 sx L R Φ :
    cvt t2 sx v = Some v' ->
    types_agree t1 v ->
    ↪[frame] f -∗
    ↪[RUN] -∗
    ▷ Φ f [v'] -∗
    CWP [BI_const v; BI_cvtop t2 CVO_convert t1 sx] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hcvt Htv) "Hf Hrun HΦ".
    iApply lwp_cvtop_convert.
    { done. }
    { by apply Is_true_true. }
    iFrame.
  Qed.

  Lemma cwp_cvtop_convert_fail s E (f : frame) v t1 t2 sx L R Φ :
    cvt t2 sx v = None ->
    types_agree t1 v ->
    ↪[frame] f -∗
    ↪[RUN] -∗
    CWP [BI_const v; BI_cvtop t2 CVO_convert t1 sx] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hcvt Htv) "Hf Hrun".
    iApply lwp_cvtop_convert_failure.
    { done. }
    { by apply Is_true_true. }
    by iFrame.
  Qed.

  Lemma cwp_cvtop_reinterpret s E (f : frame) v v' t1 t2 L R Φ :
    wasm_deserialise (bits v) t2 = v' ->
    types_agree t1 v ->
    ↪[frame] f -∗
    ↪[RUN] -∗
    ▷ Φ f [v'] -∗
    CWP [BI_const v; BI_cvtop t2 CVO_reinterpret t1 None] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hcvt Htv) "Hf Hrun HΦ".
    iApply lwp_cvtop_reinterpret.
    { done. }
    { by apply Is_true_true. }
    iFrame.
  Qed.

End numeric.
