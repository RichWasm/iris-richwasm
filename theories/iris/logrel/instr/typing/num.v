Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section num.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma one_rep_in_rvs_vs rvs vs rtii srr se:
    (forall i, atoms_interp rvs vs -∗
    values_interp rtii srr se [NumT (VALTYPE (AtomR (int_type_arep i)) NoRefs) (IntT i)] rvs -∗
    ⌜(exists n, vs = [VAL_int32 n] /\ i = I32T) \/ (exists n, vs = [VAL_int64 n] /\ i = I64T)⌝)
    /\
    (forall i, atoms_interp rvs vs -∗
    values_interp rtii srr se [NumT (VALTYPE (AtomR (float_type_arep i)) NoRefs) (FloatT i)] rvs -∗
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
    all: destruct Hkindinterp as [(rvs0 & Hrvs0 & Hprimprep) Hnorefs].
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
    values_interp rtii srr se [NumT (VALTYPE (AtomR (int_type_arep i)) NoRefs) (IntT i);
                               NumT (VALTYPE (AtomR (int_type_arep i)) NoRefs) (IntT i)] rvs -∗
    ⌜(exists n1 n2, vs = [VAL_int32 n1; VAL_int32 n2] /\ i = I32T) \/
      (exists n1 n2, vs = [VAL_int64 n1; VAL_int64 n2] /\ i = I64T)⌝)
    /\
    (forall i, atoms_interp rvs vs -∗
    values_interp rtii srr se [NumT (VALTYPE (AtomR (float_type_arep i)) NoRefs) (FloatT i);
                               NumT (VALTYPE (AtomR (float_type_arep i)) NoRefs) (FloatT i)] rvs -∗
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
    all: destruct Hkindinterp1 as [(rvs1_0 & Hrvs1 & Hprimprep1) Hnorefs1].
    all: destruct Hkindinterp2 as [(rvs2_0 & Hrvs2 & Hprimprep2) Hnorefs2].
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
    iIntros (????????) "@@@@@@@@@@@@";
    edestruct (one_rep_in_rvs_vs) as [one_rep_in_rvs_vs_ints one_rep_in_rvs_vs_floats];
    try (iPoseProof (one_rep_in_rvs_vs_ints n with "[$Hvs] [$Hos]") as "%Hvs");
    try (iPoseProof (one_rep_in_rvs_vs_floats n with "[$Hvs] [$Hos]") as "%Hvs");
    iClear "Hos Hvs".

  Ltac two_num_set_up τ n :=
    inversion Htypenum; subst;
    unfold τ in *; unfold int_type_type, float_type_type in *;
    unfold type_i64, type_i32, type_f64, type_f32 in *;
    iIntros (????????) "@@@@@@@@@@@@";
    edestruct (two_rep_in_rvs_vs) as [two_rep_in_rvs_vs_ints two_rep_in_rvs_vs_floats];
    try (iPoseProof (two_rep_in_rvs_vs_ints n with "[$Hvs] [$Hos]") as "%Hvs");
    try (iPoseProof (two_rep_in_rvs_vs_floats n with "[$Hvs] [$Hos]") as "%Hvs");
    iClear "Hos Hvs".

  Ltac solve_post_cwp_num :=
    iModIntro; iFrame;
    iSplitR; auto;
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
    split; econstructor; split; auto;
    try (apply Forall2_cons; split; [|by apply Forall2_nil]; done);
    try (apply Forall_singleton; done).

  Lemma compat_num M F L wt wt' wtf wl wl' wlf ψ e es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    has_instruction_type_num e ψ ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (INum ψ e)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmask Htypenum Htype Hcg.
    cbn in Hcg.

    destruct e; cbn in Hcg; inversion Hcg; subst; clear Hcg.
    - (* unop int *)
      rename i0 into unop.

      one_num_set_up τ i.
      destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; subst.

      all: apply has_values_to_consts_inv in Hevs; cbn in Hevs; rewrite Hevs.
      all: change ([?x]++[?y]) with ([x;y]).
      all: iApply (cwp_unop with "[$] [$] [-]"); [cbn; auto | solve_post_cwp_num].
    - (* binop int *)
      rename i0 into binop.

      two_num_set_up τ i.
      destruct Hvs as [(n1 & n2 & Hvs & Hi) | (n1 & n2 & Hvs & Hi)]; subst.
      all: apply has_values_to_consts_inv in Hevs; cbn in Hevs; rewrite Hevs.
      all: change ([?x;?z]++[?y]) with ([x;z;y]).

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
         | _ => iApply (cwp_binop with "[$] [$] [-]");
                [cbn; auto | solve_post_cwp_num]
           end.
    (*   (* This solves the goals where the result actually exists *) *)
      all: match type of HPartialResult with
           | (_ = Some _) => iApply (cwp_binop with "[$] [$] [-]");
                [cbn; (try rewrite HPartialResult); cbn; auto | solve_post_cwp_num]
           | _ => idtac
           end.

      (* Everything remaining is partial binop results *)
      all: iEval (cbn).
      all: iApply (cwp_binop_fail with "[$] [$]");
        cbn; unfold option_map; by rewrite HPartialResult.
    - (* testop int *)
      rename i0 into testop.

      one_num_set_up τ i.
      destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; subst.

      all: apply has_values_to_consts_inv in Hevs; cbn in Hevs; rewrite Hevs.
      all: destruct testop; iEval (cbn).
      + iApply (cwp_testop_i32 with "[$] [$] [-]"); [cbn; auto | solve_post_cwp_num].
      + iApply (cwp_testop_i64 with "[$] [$] [-]"); [cbn; auto | solve_post_cwp_num].
    - (* relop int *)
      rename i0 into relop.

      two_num_set_up τ i.
      destruct Hvs as [(n1 & n2 & Hvs & Hi) | (n1 & n2 & Hvs & Hi)]; subst.

      all: apply has_values_to_consts_inv in Hevs; cbn in Hevs; rewrite Hevs.
      all: destruct relop; iEval (cbn).
      all: iApply (cwp_relop with "[$] [$] [-]"); [cbn; auto | solve_post_cwp_num].
    - (* unop float *)
      rename f0 into unop.

      one_num_set_up τ f.
      destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; subst.

      all: apply has_values_to_consts_inv in Hevs; cbn in Hevs; rewrite Hevs.
      all: change ([?x]++[?y]) with ([x;y]).
      all: iApply (cwp_unop with "[$] [$] [-]"); [cbn; auto | solve_post_cwp_num].

    - (* binop float *)
      rename f0 into relop.

      two_num_set_up τ f.
      destruct Hvs as [(n1 & n2 & Hvs & Hi) | (n1 & n2 & Hvs & Hi)]; subst.

      all: apply has_values_to_consts_inv in Hevs; cbn in Hevs; rewrite Hevs.
      all: destruct relop; iEval (cbn).
      all: iApply (cwp_binop with "[$] [$] [-]"); [cbn; auto | solve_post_cwp_num].
    - (* relop float *)
      rename f0 into relop.

      two_num_set_up τ f.
      destruct Hvs as [(n1 & n2 & Hvs & Hi) | (n1 & n2 & Hvs & Hi)]; subst.

      all: apply has_values_to_consts_inv in Hevs; cbn in Hevs; rewrite Hevs.
      all: destruct relop; iEval (cbn).
      all: iApply (cwp_relop with "[$] [$] [-]"); [cbn; auto | solve_post_cwp_num].
    - (* cvt *)
      inversion Htypenum; subst.
      rename Htypenum into Htypecvt; rename H0 into Htypenum.

      destruct c.
      all: cbn [translate_cvt_op].
      + one_num_set_up type_i64 I64T.
        destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; try (inversion Hi); subst.

        apply has_values_to_consts_inv in Hevs; cbn in Hevs; rewrite Hevs.
        iEval (cbn).
        iApply (cwp_cvtop_convert with "[$] [$] [-]");
          [cbn; auto | cbn; auto | solve_post_cwp_num].
      + one_num_set_up type_i64 I32T.
        destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; try (inversion Hi); subst.
        apply has_values_to_consts_inv in Hevs; cbn in Hevs; rewrite Hevs.

        destruct s.
        all: iEval (cbn).
        all: iApply (cwp_cvtop_convert with "[$] [$] [-]");
          [cbn; auto | cbn; auto | solve_post_cwp_num].
      + one_num_set_up type_i64 f.
        destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; try (inversion Hi); subst.
        all: apply has_values_to_consts_inv in Hevs; cbn in Hevs; rewrite Hevs.

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
                 try (destruct s; destruct i; iEval (cbn);
                 iApply (cwp_cvtop_convert with "[$] [$] [-]");
                      try (unfold cvt in HPartialResult; cbn in *; by rewrite HPartialResult);
                      try by (cbn;auto);
                 cbn in HPartialResult; unfold option_map in HPartialResult; cbn in HPartialResult;
                 match type of HPartialResult with
                 | (match ?x with |Some _=>_ |None=>_ end = _) =>
                     destruct x; cbn in HPartialResult; inversion HPartialResult
                 end;
                 solve_post_cwp_num)
             (* Partials! *)
             | (_ = None) => idtac
             end.
        all: iApply (cwp_cvtop_convert_fail with "[$] [$]");
          [cbn; unfold option_map; by rewrite HPartialResult | cbn; auto].
      + one_num_set_up type_i64 F64T.
        destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; try (inversion Hi); subst.
        apply has_values_to_consts_inv in Hevs; cbn in Hevs; rewrite Hevs.

        iEval (cbn).
        iApply (cwp_cvtop_convert with "[$] [$] [-]");
          [cbn; auto | cbn; auto | solve_post_cwp_num].
      + one_num_set_up type_i64 F32T.
        destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; try (inversion Hi); subst.
        apply has_values_to_consts_inv in Hevs; cbn in Hevs; rewrite Hevs.

        iEval (cbn).
        iApply (cwp_cvtop_convert with "[$] [$] [-]");
          [cbn; auto | cbn; auto | solve_post_cwp_num].
      + one_num_set_up type_i64 i.
        destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; try (inversion Hi); subst.
        all: apply has_values_to_consts_inv in Hevs; cbn in Hevs; rewrite Hevs.

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
                 iApply (cwp_cvtop_convert with "[$] [$] [-]"); cbn; auto;
                 try (unfold cvt in HPartialResult; cbn in *; by rewrite HPartialResult); auto;
                 cbn in HPartialResult; inversion HPartialResult;
                 solve_post_cwp_num
             | (_ = None) => idtac
             end.
         all: iApply (cwp_cvtop_convert_fail with "[$] [$]");
           [cbn; unfold option_map; by rewrite HPartialResult | cbn; auto ].
      + (* We'll need to split into cases again. This was the only thing that worked for some reason *)
        destruct n eqn:Hn;
          [ destruct i eqn:Hii; [one_num_set_up type_i64 I32T | one_num_set_up type_i64 I64T ] |
            destruct f eqn:Hf; [one_num_set_up type_i64 F32T | one_num_set_up type_i64 F64T ]  ].

        all: destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; try (inversion Hi); subst.
        all: apply has_values_to_consts_inv in Hevs; cbn in Hevs; rewrite Hevs.

        all: iEval (cbn).
        all: iApply (cwp_cvtop_reinterpret with "[$] [$] [-]");
          [cbn;auto | cbn;auto | solve_post_cwp_num].
  Qed.

End num.
