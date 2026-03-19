Require Import iris.proofmode.tactics.

From RichWasm.iris.language Require Import iris_wp_def lwp_pure.
Require Import RichWasm.iris.numerics.
Require Import RichWasm.iris.language.cwp.def.
Require Import RichWasm.iris.rules.iris_rules_pure.

Set Bullet Behavior "Strict Subproofs".

Section numeric.

  Context `{!wasmG Σ}.

  Lemma cwp_unop s E f v v' t op L R Φ :
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

  Lemma cwp_binop s E f v1 v2 v t op L R Φ :
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

  Lemma cwp_binop_fail s E f v1 v2 t op L R Φ :
    app_binop op v1 v2 = None ->
    ↪[frame] f -∗
    ↪[RUN] -∗
    CWP [BI_const v1; BI_const v2; BI_binop t op] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hop) "Hf Hrun".
    iApply lwp_binop_failure; first done.
    by iFrame.
  Qed.

  Lemma cwp_testop_i32 s E f v b op L R Φ :
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

  Lemma cwp_testop_i64 s E f v b op L R Φ :
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

  Lemma cwp_relop s E f v1 v2 b t op L R Φ :
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

  Lemma cwp_cvtop_convert s E f v v' t1 t2 sx L R Φ :
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

  Lemma cwp_cvtop_convert_fail s E f v t1 t2 sx L R Φ :
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

  Lemma cwp_cvtop_reinterpret s E f v v' t1 t2 L R Φ :
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

  (* Lemmas for specific operators with lemmas proved in theories/numerics.v *)
  Lemma cwp_add32 s E L R (f: frame) x x32 y y32 Φ :
    N_i32_repr x x32 ->
    N_i32_repr y y32 ->
    (Z.of_N (x + y) < Wasm_int.Int32.modulus)%Z ->
    ▷ (∀ z32, ⌜N_i32_repr (x + y) z32⌝ -∗ Φ f [VAL_int32 z32]) -∗
    ↪[frame] f -∗
    ↪[RUN] -∗
    CWP [BI_const (VAL_int32 x32);
         BI_const (VAL_int32 y32);
         BI_binop T_i32 (Binop_i BOI_add)]
      @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hrx Hry Hbdd) "HΦ Hf Hrun".
    iApply (cwp_binop with "[$] [$]"); eauto.
    iModIntro.
    iApply "HΦ".
    iPureIntro.
    apply iadd_N_cong; eauto.
  Qed.

  Lemma cwp_shl32 s E L R (f: frame) x x32 y y32 Φ :
    N_i32_repr x x32 ->
    N_i32_repr y y32 ->
    (Z.of_N (N.shiftl x y) < Wasm_int.Int32.modulus)%Z ->
    ▷ (∀ z32, ⌜N_i32_repr (N.shiftl x y) z32⌝ -∗ Φ f [VAL_int32 z32]) -∗
    ↪[frame] f -∗
    ↪[RUN] -∗
    CWP [BI_const (VAL_int32 x32);
         BI_const (VAL_int32 y32);
         BI_binop T_i32 (Binop_i BOI_shl)]
      @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hrx Hry Hbdd) "HΦ Hf Hrun".
    iApply (cwp_binop with "[$] [$]"); eauto.
    iModIntro.
    iApply "HΦ".
    iPureIntro.
    apply shl_N_cong; eauto.
  Qed.

  Lemma cwp_shr32 s E L R (f: frame) x x32 y y32 Φ :
    N_i32_repr x x32 ->
    N_i32_repr y y32 ->
    (Z.of_N (N.shiftr x y) < Wasm_int.Int32.modulus)%Z ->
    ▷ (∀ z32, ⌜N_i32_repr (N.shiftr x y) z32⌝ -∗ Φ f [VAL_int32 z32]) -∗
    ↪[frame] f -∗
    ↪[RUN] -∗
    CWP [BI_const (VAL_int32 x32);
         BI_const (VAL_int32 y32);
         BI_binop T_i32 (Binop_i (BOI_shr Wasm.datatypes.SX_U))]
      @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hrx Hry Hbdd) "HΦ Hf Hrun".
    iApply (cwp_binop with "[$] [$]"); eauto.
    iModIntro.
    iApply "HΦ".
    iPureIntro.
    apply shru_N_cong; eauto.
  Qed.

  Lemma cwp_eqz s E L R (f: frame) x x32 Φ :
    N_i32_repr x x32 ->
    ▷ Φ f [VAL_int32 (wasm_bool (N.eqb 0 x))] -∗
    ↪[frame] f -∗
    ↪[RUN] -∗
    CWP [BI_const (VAL_int32 x32);
         BI_testop T_i32 TO_eqz]
      @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros (Hrx) "HΦ Hf Hrun".
    iApply (cwp_testop_i32 with "[$] [$]"); eauto.
    now rewrite (eqz_N_cong _ _ Hrx).
  Qed.

End numeric.
