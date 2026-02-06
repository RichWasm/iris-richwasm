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

  Lemma compat_binary_case M F L L' n_skip wt wt' wtf wl wl' wlf es' ess es1 es2 τs τ1 τ2 τs' κ :
    ess = [es1; es2] ->
    τs = [τ1; τ2] ->
    let fe := fe_of_context F <| fe_br_skip := n_skip |> in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let F' := F <| fc_labels ::= cons (τs', L') |> in
    let ψ := InstrT [SumT κ τs] τs' in
    Forall2
      (fun τ es =>
         (forall m_skip wt wt' wtf wl wl' wlf es',
            let fe' := fe_of_context F' <| fe_br_skip := m_skip |> in
            let WT := wt ++ wt' ++ wtf in
            let WL := wl ++ wl' ++ wlf in
            run_codegen (compile_instrs mr fe' es) wt wl = inr ((), wt', wl', es') ->
            ⊢ have_instruction_type_sem rti sr mr M F' L WT WL (to_e_list es') (InstrT [τ] τs') L'))
      τs ess ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ICase ψ L' ess)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L'.
  Proof.
    intros -> -> fe WT WL F' Ψ Hforall Hok Hcg.
    rewrite Forall2_cons_iff in Hforall.
    destruct Hforall as [Hes1 H2].
    rewrite Forall2_cons_iff in H2.
    destruct H2 as [Hes2 _].
    subst Ψ.
    cbn [compile_instr] in Hcg.
    destruct κ as [ ρ c d | ]; last inversion Hcg.
    destruct ρ  as [ | ρs_sum | | ]; try done.
    destruct τs' as [ | τ_res τs' ]; first done.
    destruct τs'; last done.


    inv_cg_bind Hcg wt_ret ?wt ?wt ?wl ?wl ?es ?es Hres_type Hcg.
    inv_cg_try_option Hres_type; subst.
    inv_cg_bind Hcg ρs_atom ?wt ?wt ?wl ?wl ?es ?es Hιs Hcg.
    inv_cg_try_option Hιs; subst.
    inv_cg_bind Hcg val_idxs wt_save ?wt wl_save ?wl es_save ?es Hsave Hcg.
    repeat rewrite app_nil_r in Hsave.


    (* Case blocks *)
    inv_cg_bind Hcg tag_idx ?wt ?wt ?wl ?wl es_save_tag ?es HsaveTag Hcg.
    inv_cg_bind Hcg pair ?wt ?wt ?wl ?wl ?es es_done_bl Hcases HdoneBlock.
    destruct pair, u.
    inv_cg_emit HdoneBlock; subst.

    apply run_codegen_capture in Hcases as [Hcases ->].
    cbv [map length seq zip Datatypes.uncurry] in Hcases.

    clear_nils.

    inv_cg_bind Hcases [] ?wt ?wt ?wl ?wl ?es es_unr Hcases Hunreachable.
    inv_cg_emit Hunreachable; subst.

    inv_cg_bind Hcases ?units ?wt ?wt ?wl ?wl ?es es_case1 Hcases Hret.
    inv_cg_ret Hret; subst.


    (* Case es1 *)
    inv_cg_bind Hcases [] ?wt ?wt ?wl ?wl ?es es_case1 Hcase_es1 Hcase_es2.

    inv_cg_bind Hcase_es1 ?pair ?wt ?wt ?wl ?wl ?es ?es Hcase_es1 Hcase_es1_block.
    destruct pair, u.
    inv_cg_emit Hcase_es1_block; subst.
    apply run_codegen_capture in Hcase_es1 as [Hcase_es1 ->].

    inv_cg_bind Hcase_es1 [] ?wt ?wt ?wl ?wl ?es ?es Hget_tag Hcase_es1.
    inv_cg_emit Hget_tag; subst.

    inv_cg_bind Hcase_es1 [] ?wt ?wt ?wl ?wl ?es ?es Htag0 Hcase_es1.
    inv_cg_emit Htag0; subst.

    inv_cg_bind Hcase_es1 [] ?wt ?wt ?wl ?wl ?es ?es Hcompare_tag Hcase_es1.
    inv_cg_emit Hcompare_tag; subst.

    inv_cg_bind Hcase_es1 [] ?wt ?wt ?wl ?wl ?es ?es Hbr_case Hcase_es1.
    inv_cg_emit Hbr_case; subst.

    inv_cg_bind Hcase_es1 [] ?wt ?wt ?wl ?wl ?es ?es Hcase_es1 Hbr_cases.
    inv_cg_emit Hbr_cases; subst.

    inv_cg_bind Hcase_es1 ρ_case1 ?wt ?wt ?wl ?wl ?es ?es Hlookup Hcase_es1.
    inv_cg_try_option Hlookup; subst.

    inv_cg_bind Hcase_es1 case_1_sum_locals ?wt ?wt ?wl ?wl ?es ?es Hinject Hcase_es1.
    inv_cg_try_option Hinject; subst.

    inv_cg_bind Hcase_es1 [] ?wt wt_case_1 ?wl wl_case_1 ?es es_case_1 Hget_locals_1 Hcase_es1.
    inv_cg_bind Hget_locals_1 case_1_val_idxs ?wt wt_get_locals_1 ?wl wl_get_locals_1 ?es es_get_locals_1 Hnths_error Hget_locals_1.
    inv_cg_try_option Hnths_error; subst.

    clear_nils.

    destruct (run_codegen_get_locals _ _ _ _ _ _ _ Hget_locals_1) as [_ [-> ->]].


    (* Case es2 *)

    inv_cg_bind Hcase_es2 ?units ?wt ?wt ?wl ?wl ?es ?es Hcase_es2 Hmret.
    inv_cg_ret Hmret; subst.

    inv_cg_bind Hcase_es2 [] ?wt ?wt ?wl ?wl ?es ?es Hcase_es2 Hmret.
    inv_cg_ret Hmret; subst.

    inv_cg_bind Hcase_es2 pair ?wt ?wt ?wl ?wl ?es ?es Hcase_es2 Hcase_es2_block.
    destruct pair, u.
    inv_cg_emit Hcase_es2_block; subst.
    apply run_codegen_capture in Hcase_es2 as [Hcase_es2 ->].

    inv_cg_bind Hcase_es2 [] ?wt ?wt ?wl ?wl ?es ?es Hget_tag Hcase_es2.
    inv_cg_emit Hget_tag; subst.

    inv_cg_bind Hcase_es2 [] ?wt ?wt ?wl ?wl ?es ?es Htag0 Hcase_es2.
    inv_cg_emit Htag0; subst.

    inv_cg_bind Hcase_es2 [] ?wt ?wt ?wl ?wl ?es ?es Hcompare_tag Hcase_es2.
    inv_cg_emit Hcompare_tag; subst.

    inv_cg_bind Hcase_es2 [] ?wt ?wt ?wl ?wl ?es ?es Hbr_case Hcase_es2.
    inv_cg_emit Hbr_case; subst.

    inv_cg_bind Hcase_es2 [] ?wt ?wt ?wl ?wl ?es ?es Hcase_es2 Hbr_cases.
    inv_cg_emit Hbr_cases; subst.

    inv_cg_bind Hcase_es2 ρ_case2 ?wt ?wt ?wl ?wl ?es ?es Hlookup Hcase_es2.
    inv_cg_try_option Hlookup; subst.

    inv_cg_bind Hcase_es2 case_2_sum_locals ?wt ?wt ?wl ?wl ?es ?es Hinject Hcase_es2.
    inv_cg_try_option Hinject; subst.

    inv_cg_bind Hcase_es2 [] ?wt wt_case_2 ?wl wl_case_2 ?es es_case_2 Hget_locals_2 Hcase_es2.
    inv_cg_bind Hget_locals_2 case_2_val_idxs ?wt wt_get_locals_2 ?wl wl_get_locals_2 ?es es_get_locals_2 Hnths_error Hget_locals_2.
    inv_cg_try_option Hnths_error; subst.

    clear_nils.

    destruct (run_codegen_get_locals _ _ _ _ _ _ _ Hget_locals_2) as [_ [-> ->]].

    (* clean up *)
    subst WT WL.
    clear_nils.
    simplify_eq.

    (* Iris Proof *)
    iIntros (? ? ? ? ? ? ? ?) "#Hinst #Hctx Hrvs Hvs Hframe Hrt Hf Hrun".
    iDestruct (Hes1 _ _ _ wtf _ _ wlf _ Hcase_es1) as "Hsem_es1".
    iDestruct (Hes2 _ _ _ wtf _ _ wlf _ Hcase_es2) as "Hsem_es2".

    replace (language.of_val (immV vs)) with (v_to_e_list vs); last done.
    unfold expr_interp.


Admitted.

  Lemma compat_case M F L L' n_skip wt wt' wtf wl wl' wlf es' ess τs τs' κ :
    let fe := fe_of_context F <| fe_br_skip := n_skip |> in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let F' := F <| fc_labels ::= cons (τs', L') |> in
    let ψ := InstrT [SumT κ τs] τs' in
    Forall2
      (fun τ es =>
         (forall m_skip wt wt' wtf wl wl' wlf es',
            let fe' := fe_of_context F' <| fe_br_skip := m_skip |> in
            let WT := wt ++ wt' ++ wtf in
            let WL := wl ++ wl' ++ wlf in
            run_codegen (compile_instrs mr fe' es) wt wl = inr ((), wt', wl', es') ->
            ⊢ have_instruction_type_sem rti sr mr M F' L WT WL (to_e_list es') (InstrT [τ] τs') L'))
      τs ess ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ICase ψ L' ess)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L WT WL (to_e_list es') ψ L'.
  Admitted.

End Fundamental.
