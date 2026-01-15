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

  Lemma compat_app M F L1 L2 L3 wt wt' wtf wl wl' wlf es' es1 es2 τs1 τs2 τs3 :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    (forall wt wt' wtf wl wl' wlf es',
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        run_codegen (compile_instrs mr fe es1) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instruction_type_sem rti sr mr M F L1 WT WL (to_e_list es') (InstrT τs1 τs2) L2) ->
    (forall wt wt' wtf wl wl' wlf es',
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        run_codegen (compile_instrs mr fe es2) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instruction_type_sem rti sr mr M F L2 WT WL (to_e_list es') (InstrT τs2 τs3) L3) ->
    run_codegen (compile_instrs mr fe (es1 ++ es2)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L1 WT WL (to_e_list es') (InstrT τs1 τs3) L3.
  Proof.
    intros fe WT WL Hes1 Hes2 Hcompile; rename wl' into wl''; rename wt' into wt''; rename es' into es''.
    (* Step 1: split out Hcompile into Hcompile_e and Hcompile_es *)

    (* For Hcompile_e *)
    unfold compile_instrs in Hcompile.
    cbn in Hcompile.
    inv_cg_bind Hcompile res wt_full wttemp wl_full wltemp es' es2_temp' Hcompile Hcompile_empty; subst.
    inversion Hcompile_empty; subst; clear Hcompile_empty.
    rewrite app_nil_r.

    assert (Hcompile_split: exists wt1 wt2 wl1 wl2 es1' es2',
              run_codegen (compile_instrs mr fe es1) wt wl = inr ((), wt1, wl1, es1')
               /\
              run_codegen (compile_instrs mr fe es2) (wt ++ wt1) (wl ++ wl1) =
                inr ((), wt2, wl2, es2')
               /\
              wt_full = wt1 ++ wt2
               /\
              wl_full = wl1 ++ wl2
               /\
              es' = es1' ++ es2'
           ).
    {
      (* This is mainly a proof about the codegen monad. Weirdly difficult for whatever reason.
         Come back to it later. *)
      admit.
    }
    destruct Hcompile_split as (wt1&wt2&wl1&wl2&es1'&es2'& Hcompile_es1 & Hcompile_es2 & H1 & H2 & H3); subst.

    (* This is very silly but I can't figure out how to just rewrite with WT := ... *)
    assert (Temp: WT = wt ++ ((wt1 ++ wt2) ++ []) ++ wtf) by auto; rewrite Temp; clear Temp.
    assert (Temp: WL = wl ++ ((wl1 ++ wl2) ++ []) ++ wlf) by auto; rewrite Temp; clear Temp.
    repeat rewrite app_nil_r.

    apply (Hes1 wt wt1 (wt2 ++ wtf) wl wl1 (wl2 ++ wlf) es1') in Hcompile_es1 as Hsem_es1.
    apply (Hes2 (wt ++ wt1) wt2 wtf (wl ++ wl1) wl2 wlf es2') in Hcompile_es2 as Hsem_es2.

    (* Temporary context clean up*)
    clear Hes1 Hes2 Hcompile Hcompile_es1 Hcompile_es2 WT WL.
    rewrite to_e_list_app.
    repeat rewrite <- app_assoc.

    (* Time for type semantic! *)
    unfold have_instruction_type_sem.
    iIntros (? ? ? ? ? ? ?) "%Henv #Hinst #Hctx Hrvs Hvs Hfr Hrt Hf Hrun".
    unfold have_instruction_type_sem in Hsem_es1, Hsem_es2.
    iPoseProof (Hsem_es1) as "Hsem_es1"; iPoseProof (Hsem_es2) as "Hsem_es2".

    (* Start passing resources *)
    iSpecialize ("Hsem_es1" $! se inst lh fr os vs θ Henv with "Hinst Hctx Hrvs Hvs Hfr Hrt Hf Hrun").
    rewrite (app_assoc (language.of_val (immV vs)) (to_e_list es1') (to_e_list es2')).

    iApply (lenient_wp_seq with "[Hsem_es1]").
    - iApply "Hsem_es1".
    - done.
    - iIntros (w f) "Hvs Hfr _".
      destruct w eqn:Hw.
      + (* Value case *)
        iDestruct "Hvs" as "(Hrun & Hframe & Hval)". rename l into vs0.
        iDestruct "Hval" as "[%rvs0 [%θ0 (Hval_interp & Hrep_interp & Hrt)]]".

        (* This makes the rewrites a little nicer *)
        assert (Temp: forall A (l1:list A) l2 l3 l4, l1 ++ l2 ++ l3 ++ l4 = (l1 ++ l2) ++ l3 ++ l4).
        { intros. by rewrite app_assoc. }

        repeat (rewrite Temp).
        iSpecialize ("Hsem_es2" $! se inst lh f rvs0 vs0 θ0 Henv
                      with "Hinst Hctx Hrep_interp Hval_interp Hframe Hrt Hfr Hrun").
        iApply "Hsem_es2".
      + done.
      + iEval (cbn) in "Hvs". iDestruct "Hvs" as "(Hrun & Hbr_interp)".
        iEval (cbn).
        (* Some sort of lenient_wp lemma about BI_br *)
        admit.
      + (* string of specific cbns for a cleaner context *)
        iEval (cbn [lp_notrap]) in "Hvs". iEval (cbn [lp_noframe]) in "Hvs".
        iEval (cbn [lp_ret]) in "Hvs".
        iDestruct "Hvs" as "(Hrun & Hret_interp)".
        iEval (cbn).
        (* Some sort of lenient_wp lemma about BI_return *)
        admit.
      + (* While call_host is still just False, this works. *)
        iEval (cbn) in "Hvs".
        iDestruct "Hvs" as "(_ & HF)".
        auto.
  Admitted.

End Fundamental.
