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

  Lemma compat_tag M F L n_skip wt wt' wtf wl wl' wlf es' :
    let fe := fe_of_context F <| fe_br_skip := n_skip |> in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [type_i32] [type_i31] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ITag ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L.
  Proof.
    intros fe WT WL ψ Hok Hcompile.
    cbn in Hcompile; inversion Hcompile; subst; clear Hcompile.

    iIntros (se inst lh fr rvs vs θ) "%Henv #Hinst #Hlf Hrvs Hvs Hframe Hrt Hfr Hrun".

    (* A loooong section to prove that vs just has an integer in it *)
    (* First, show that rvs just has one thing in it *)
    iEval (cbn) in "Hvs"; iEval (cbn) in "Hrvs".
    iDestruct "Hvs" as "(%rvss & %Hconcat_rvss & Hrvss)".
    iPoseProof (big_sepL2_length with "[$Hrvss]") as "%Hlens_rvss".
    iPoseProof (big_sepL2_length with "[$Hrvs]") as "%Hlens_vs_rvs".
    simpl in Hlens_rvss.

    (* For some reason I couldn't use length1concat?? *)
    assert (Hrvsss: rvss = [rvs]).
    {
      destruct rvss as [ | rv rvs1 ]; inversion Hlens_rvss.
      symmetry in H0; apply nil_length_inv in H0; subst; simpl.
      by rewrite app_nil_r.
    }
    rewrite Hrvsss.
    iEval (cbn) in "Hrvss".
    iDestruct "Hrvss" as "[Hvs _]".
    iPoseProof (value_interp_eq with "Hvs") as "Hvs".
    iEval (cbn) in "Hvs".
    iDestruct "Hvs" as "(%k & %Hk & Hkindinterp & _)".
    inversion Hk.
    iEval (cbn) in "Hkindinterp".
    iPoseProof "Hkindinterp" as "%Hkindinterp".
    (* Have to dig in and prove rvs is just an integer *)
    unfold has_areps in Hkindinterp.
    destruct Hkindinterp as (rvs0 & Hrvs0 & Hprimprep).
    inversion Hrvs0.
    rewrite <- H1 in Hprimprep. (* subst does too much here*)
    apply Forall2_length in Hprimprep as Hrvslength.
    cbn in Hrvslength.
    destruct rvs as [|rv rvs]; inversion Hrvslength.
    symmetry in H2; apply nil_length_inv in H2.
    subst.
    (* So close *)
    apply Forall2_cons_iff in Hprimprep.
    destruct Hprimprep as [Hrv _].
    cbn in Hrv.
    destruct rv; cbn in Hrv; try easy; subst.

    (* Now genuinely new bit: show vs has an integer *)
    (* temporary cleaning this is a mess *)
    clear Hconcat_rvss Hlens_rvss Hk Hrvslength Hrvs0 Hrv.
    cbn in Hlens_vs_rvs.
    destruct vs as [| v vs]; inversion Hlens_vs_rvs.
    symmetry in H0; apply nil_length_inv in H0; subst.
    iEval (cbn) in "Hrvs".
    iDestruct "Hrvs" as "(%Hv & _)"; subst.

    (* Okay yay! Now we can apply lwp_binop. *)
    iClear "Hinst"; iClear "Hlf".
    iEval (cbn).
    iApply lwp_binop.
    - cbn. auto. (* get the pure value that the computations gets you *)
    - (* Four of the resources are just trivial *)
      iFrame.
      (* let's prove this value!*)
      iModIntro; cbn.
      unfold Wasm_int.Int32.ishl, Wasm_int.Int32.shl, Z.shiftl; cbn.
      iExists [PtrA (PtrInt (Wasm_int.Int32.unsigned n))].
      iSplitR; cbn; try (iSplitR; auto); last first.
      * iExists _; iSplitL; auto.
        iExists (RootInt (Wasm_int.Int32.unsigned n)).
        cbn.
        iSplit; auto using ReprRootInt.
      * iExists [[PtrA (PtrInt (Wasm_int.Int32.unsigned n))]].
        iSplitL; cbn; auto; iSplitL; auto.

        iApply value_interp_eq; cbn.
        iExists _; iSplitL; auto; iSplitL; auto; cbn.
        iPureIntro.

        eexists; split; auto.
        apply Forall2_cons_iff; split; auto.
        by unfold has_areps.
  Qed.

End Fundamental.
