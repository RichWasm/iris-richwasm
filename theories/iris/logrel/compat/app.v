Require Import RecordUpdate.RecordUpdate.
From stdpp Require Import base list.

From iris.proofmode Require Import base proofmode classes.

From RichWasm.named_props Require Import named_props custom_syntax.
From RichWasm.wasm Require Import operations.
From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import prelude codegen instruction module.
From RichWasm.iris Require Import autowp memory util wp_codegen.
From RichWasm.iris.language Require Import cwp logpred.
From RichWasm.iris.logrel Require Import relations fundamental_kinding.
Require Import RichWasm.iris.logrel.compat.common.

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
        ⊢ have_instr_type_sem rti sr mr M F L1 WT WL es' (InstrT τs1 τs2) L2) ->
    (forall wt wt' wtf wl wl' wlf es',
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        run_codegen (compile_instrs mr fe es2) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instr_type_sem rti sr mr M F L2 WT WL es' (InstrT τs2 τs3) L3) ->
    run_codegen (compile_instrs mr fe (es1 ++ es2)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L1 WT WL es' (InstrT τs1 τs3) L3.
  Proof.
    intros fe WT WL IH1 IH2 Hcg.
    assert (Hcompile_split: exists wt1 wt2 wl1 wl2 es1' es2',
               run_codegen (compile_instrs mr fe es1) wt wl = inr ((), wt1, wl1, es1') /\
               run_codegen (compile_instrs mr fe es2) (wt ++ wt1) (wl ++ wl1) =
                 inr ((), wt2, wl2, es2') /\
               wt' = wt1 ++ wt2 /\ wl' = wl1 ++ wl2  /\  es' = es1' ++ es2' ).
     {
       (* This is mainly a proof about the codegen monad. Weirdly difficult for whatever reason.
          Come back to it later. *)
       admit.
     }
    destruct Hcompile_split as (wt1&wt2&wl1&wl2&es1'&es2'&
                                  Hcompile_es1 & Hcompile_es2 & H1 & H2 & H3); subst.
    apply (IH1 _ _ (wt2++wtf) _ _ (wl2++wlf) _) in Hcompile_es1.
    apply (IH2 _ _ wtf _ _ wlf _) in Hcompile_es2.
    iPoseProof Hcompile_es1 as "Hcompile_es1"; iPoseProof Hcompile_es2 as "Hcompile_es2".
    assert (tt: WT = wt ++ (wt1 ++ wt2) ++ wtf) by auto; rewrite tt; clear tt.
    assert (tt: WL = wl ++ (wl1 ++ wl2) ++ wlf) by auto; rewrite tt; clear tt.
    repeat rewrite <- app_assoc.

    iIntros (?????????) "@@@@@@@@@@@".
    iSpecialize ("Hcompile_es1" $! se inst fr os vs evs θ B R Hse Hevs
                  with "Hinst Hlabels Hreturn Hvs Hos Hframe Hrt Hfr Hrun").
    iEval (rewrite app_assoc).

    iApply (cwp_seq with "[$Hcompile_es1]"). clear θ fr.
    iIntros (fr vs2) "[HIfr (%os2 & %θ & HIhvs & HIos & Hrt)] Hfr Hrun".

    iApply ("Hcompile_es2" with "[] [] [$] [$] [$] [$] [$] [$] [$] [$] [$]"); iPureIntro; auto.
    apply has_values_to_consts.
  Admitted.

End Fundamental.
