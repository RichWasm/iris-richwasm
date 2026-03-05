Require Import RecordUpdate.RecordUpdate.
From stdpp Require Import base list.

From iris.proofmode Require Import base tactics classes.
From Wasm Require Import operations.

From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import prelude codegen instruction module.
From RichWasm.iris Require Import autowp memory util wp_codegen.
From RichWasm.iris.language Require Import lenient_wp lwp_pure lwp_structural lwp_resources logpred.
From RichWasm.iris.logrel Require Import relations fundamental_kinding.

Require Export shared.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Fundamental.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Ltac solve_post_lwp_num :=
    iFrame; iModIntro; cbn;
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
    eexists; split; auto;
    apply Forall2_cons_iff; split; auto;
    by unfold has_arep.

  Lemma one_rep_in_rvs_vs rvs vs rtii srr se:
    (forall i, atoms_interp rvs vs -∗
    values_interp rtii srr se [NumT (VALTYPE (AtomR (int_type_arep i)) ImCopy ImDrop) (IntT i)] rvs -∗
    ⌜(exists n, vs = [VAL_int32 n] /\ i = I32T) \/ (exists n, vs = [VAL_int64 n] /\ i = I64T)⌝)
    /\
    (forall i, atoms_interp rvs vs -∗
    values_interp rtii srr se [NumT (VALTYPE (AtomR (float_type_arep i)) ImCopy ImDrop) (FloatT i)] rvs -∗
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
    all: destruct Hkindinterp as (rvs0 & Hrvs0 & Hprimprep).
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
    values_interp rtii srr se [NumT (VALTYPE (AtomR (int_type_arep i)) ImCopy ImDrop) (IntT i);
                               NumT (VALTYPE (AtomR (int_type_arep i)) ImCopy ImDrop) (IntT i)] rvs -∗
    ⌜(exists n1 n2, vs = [VAL_int32 n1; VAL_int32 n2] /\ i = I32T) \/
      (exists n1 n2, vs = [VAL_int64 n1; VAL_int64 n2] /\ i = I64T)⌝)
    /\
    (forall i, atoms_interp rvs vs -∗
    values_interp rtii srr se [NumT (VALTYPE (AtomR (float_type_arep i)) ImCopy ImDrop) (FloatT i);
                               NumT (VALTYPE (AtomR (float_type_arep i)) ImCopy ImDrop) (FloatT i)] rvs -∗
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
    all: destruct Hkindinterp1 as (rvs1_0 & Hrvs1 & Hprimprep1).
    all: destruct Hkindinterp2 as (rvs2_0 & Hrvs2 & Hprimprep2).
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
    iIntros (? ? ? ? ? ? ?) "%Henv #Hinst #Hctx Hrvs Hvs Hfr Hrt Hf Hrun";
    edestruct (one_rep_in_rvs_vs) as [one_rep_in_rvs_vs_ints one_rep_in_rvs_vs_floats];
    try (iPoseProof (one_rep_in_rvs_vs_ints n with "[$Hrvs] [$Hvs]") as "%Hvs");
    try (iPoseProof (one_rep_in_rvs_vs_floats n with "[$Hrvs] [$Hvs]") as "%Hvs");
    iClear "Hrvs"; iClear "Hvs".
  Ltac two_num_set_up τ n :=
    inversion Htypenum; subst;
    unfold τ in *; unfold int_type_type, float_type_type in *;
    unfold type_i64, type_i32, type_f64, type_f32 in *;
    iIntros (? ? ? ? ? ? ?) "%Henv #Hinst #Hctx Hrvs Hvs Hfr Hrt Hf Hrun";
    edestruct (two_rep_in_rvs_vs) as [two_rep_in_rvs_vs_ints two_rep_in_rvs_vs_floats];
    try (iPoseProof (two_rep_in_rvs_vs_ints n with "[$Hrvs] [$Hvs]") as "%Hvs");
    try (iPoseProof (two_rep_in_rvs_vs_floats n with "[$Hrvs] [$Hvs]") as "%Hvs");
    iClear "Hrvs"; iClear "Hvs".


  Lemma compat_num M F L wt wt' wtf wl wl' wlf ψ e es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    has_instruction_type_num e ψ ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (INum ψ e)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Proof.
    intros fe WT WL Htypenum Htype Hcompile.
    cbn in Hcompile.
    (* There are 8 cases for e in the way it can compile. So, destruct and get 8 cases. *)
    destruct e; cbn in Hcompile; inversion Hcompile; subst; clear Hcompile.
    - rename i0 into unop.

      one_num_set_up τ i.
      destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; subst.

      all: destruct unop; iEval (cbn).
      all: iApply lwp_unop; [cbn; auto | solve_post_lwp_num].

    - rename i0 into binop.

      two_num_set_up τ i.
      destruct Hvs as [(n1 & n2 & Hvs & Hi) | (n1 & n2 & Hvs & Hi)]; subst.

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
         | _ => iApply lwp_binop;
                [cbn; (try rewrite HPartialResult); cbn; auto | solve_post_lwp_num]
           end.
      (* This solves the goals where the result actually exists *)
      all: match type of HPartialResult with
           | (_ = Some _) => iApply lwp_binop;
                [cbn; (try rewrite HPartialResult); cbn; auto | solve_post_lwp_num]
           | _ => idtac
           end.

      (* Everything remaining is partial binop results *)
      all: iEval (cbn).
      all: iApply lwp_binop_failure; [cbn; unfold option_map; by rewrite HPartialResult |].
      all: iFrame.
      all: by iEval (cbn).

    - rename i0 into testop.

      one_num_set_up τ i.
      destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; subst.

      all: destruct testop; iEval (cbn).
      + iApply lwp_testop_i32; [cbn; auto | solve_post_lwp_num].
      + iApply lwp_testop_i64; [cbn; auto | solve_post_lwp_num].

    - rename i0 into relop.

      two_num_set_up τ i.
      destruct Hvs as [(n1 & n2 & Hvs & Hi) | (n1 & n2 & Hvs & Hi)]; subst.

      all: destruct relop; iEval (cbn).
      all: iApply lwp_relop; [cbn; auto | solve_post_lwp_num].

    - rename f0 into unop.

      (* one float set up *)
      one_num_set_up τ f.
      destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; subst.

      all: destruct unop; iEval (cbn).
      all: iApply lwp_unop; [cbn; auto | solve_post_lwp_num].

    - rename f0 into binop.

      two_num_set_up τ f.
      destruct Hvs as [(n1 & n2 & Hvs & Hi) | (n1 & n2 & Hvs & Hi)]; subst.

      (* Float binops aren't partial! *)
      all: destruct binop.
      all: iApply lwp_binop; [cbn; auto | solve_post_lwp_num].

    - rename f0 into relop.

      two_num_set_up τ f.
      destruct Hvs as [(n1 & n2 & Hvs & Hi) | (n1 & n2 & Hvs & Hi)]; subst.

      all: destruct relop; iEval (cbn).
      all: iApply lwp_relop; [cbn; auto | solve_post_lwp_num].

    - (* Conversion operations!  *)
      inversion Htypenum; subst.
      rename Htypenum into Htypecvt; rename H0 into Htypenum.

      destruct c.
      all: cbn [translate_cvt_op].
      + one_num_set_up type_i64 I64T.
        destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; try (inversion Hi); subst.

        iEval (cbn).
        iApply lwp_cvtop_convert; cbn; auto.
        solve_post_lwp_num.
      + one_num_set_up type_i64 I32T.
        destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; try (inversion Hi); subst.

        destruct s.
        all: iEval (cbn).
        all: iApply lwp_cvtop_convert; cbn; auto.
        all: solve_post_lwp_num.
      + one_num_set_up type_i64 f.
        destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; try (inversion Hi); subst.

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
                 destruct s; destruct i; iEval (cbn);
                 iApply lwp_cvtop_convert; cbn; auto;
                 try (unfold cvt in HPartialResult; cbn in *;
                      by rewrite HPartialResult); auto;
                 cbn in HPartialResult; unfold option_map in HPartialResult;
                 cbn in HPartialResult;
                 match type of HPartialResult with
                 | (match ?x with |Some _=>_ |None=>_ end = _) =>
                     destruct x; cbn in HPartialResult; inversion HPartialResult
                 end;
                 solve_post_lwp_num
            (* Partials! *)
            | (_ = None) => idtac
             end.
        all: iApply lwp_cvtop_convert_failure; [cbn; unfold option_map; by rewrite HPartialResult | cbn; auto |].
        all: iFrame; by iEval (cbn).
      + one_num_set_up type_i64 F64T.
        destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; try (inversion Hi); subst.

        iEval (cbn).
        iApply lwp_cvtop_convert; cbn; auto.
        solve_post_lwp_num.
      + one_num_set_up type_i64 F32T.
        destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; try (inversion Hi); subst.

        iEval (cbn).
        iApply lwp_cvtop_convert; cbn; auto.
        solve_post_lwp_num.
      + one_num_set_up type_i64 i.
        destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; try (inversion Hi); subst.

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
                 iApply lwp_cvtop_convert; cbn; auto;
                 try (unfold cvt in HPartialResult; cbn in *; by rewrite HPartialResult); auto;
                 cbn in HPartialResult; inversion HPartialResult;
                 solve_post_lwp_num
             | (_ = None) => idtac
             end.
         all: iApply lwp_cvtop_convert_failure; [cbn; unfold option_map; by rewrite HPartialResult | cbn; auto |].
         all: iFrame; by iEval (cbn).
      + (* We'll need to split into cases again. This was the only thing that worked for some reason *)
        destruct n eqn:Hn;
          [ destruct i eqn:Hii; [one_num_set_up type_i64 I32T | one_num_set_up type_i64 I64T ] |
            destruct f eqn:Hf; [one_num_set_up type_i64 F32T | one_num_set_up type_i64 F64T ]  ].

        all: destruct Hvs as [(n & Hvs & Hi) | (n & Hvs & Hi)]; try (inversion Hi); subst.

        all: iEval (cbn).
        all: iApply lwp_cvtop_reinterpret; cbn; auto.
        all: solve_post_lwp_num.
  Qed.

End Fundamental.
