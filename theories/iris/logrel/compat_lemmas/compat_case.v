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
    destruct κ; last inversion Hcg.
    destruct r; try done.
    destruct τs'; first done.
    destruct τs'; last done.


    inv_cg_bind Hcg ?ρ ?wt ?wt ?wl ?wl ?es ?es Hres_type Hcg.
    inv_cg_try_option Hres_type; subst.
    inv_cg_bind Hcg ?ρ ?wt ?wt ?wl ?wl ?es ?es Hιs Hcg.
    inv_cg_try_option Hιs; subst.
    inv_cg_bind Hcg vs wt_save ?wt wl_save ?wl es_save ?es Hsave Hcg.
    repeat rewrite app_nil_r in Hsave.

    (* TODO: update tactics to reflect new case_blocks definition *)

    (* Case blocks *)
    (*inv_cg_bind Hcg ?ρ ?wt ?wt ?wl ?wl ?es es_done Hcases Hcg.*)
    (*destruct ρ1 u.*)
    (*inv_cg_emit Hcg; subst.*)
    (**)
    (*apply run_codegen_capture in Hcases as [Hcases ->].*)
    (*unfold map in Hcases.*)
    (*repeat rewrite app_nil_r in Hcases.*)
    (**)
    (*repeat rewrite app_nil_l.*)
    (**)
    (*(* Case es1 *)*)
    (*inv_cg_bind Hcases ?ρ ?wt ?wt ?wl ?wl ?es es_case1 Hcases Hcase_es1.*)
    (**)
    (*inv_cg_bind Hcase_es1 ?ρ ?wt ?wt ?wl ?wl ?es ?es Hcase_es1 Hcase_es1_br.*)
    (*inv_cg_emit Hcase_es1_br; subst.*)
    (**)
    (*inv_cg_bind Hcase_es1 ?ρ ?wt ?wt ?wl ?wl ?es ?es Hlookup_l_0 Hcase_es1.*)
    (*inv_cg_try_option Hlookup_l_0; subst.*)
    (**)
    (*inv_cg_bind Hcase_es1 ?ρ ?wt ?wt ?wl ?wl ?es ?es Hinject Hcase_es1.*)
    (*inv_cg_try_option Hinject; subst.*)
    (**)
    (*inv_cg_bind Hcase_es1 ?ρ ?wt wt_case_1 ?wl wl_case_1 ?es es_case_1 Hget_locals_1 Hcase_es1.*)
    (*inv_cg_bind Hget_locals_1 ?ρ ?wt wt_get_locals_1 ?wl wl_get_locals_1 ?es es_get_locals_1 Hnths_error Hget_locals_1.*)
    (*inv_cg_try_option Hnths_error; subst.*)
    (**)
    (*inv_cg_bind Hcases ?ρ ?wt ?wt ?wl ?wl ?es ?es Hcases Hblock_case1.*)
    (*destruct ρ7, u.*)
    (*inv_cg_emit Hblock_case1; subst.*)
    (**)
    (*destruct (run_codegen_get_locals _ _ _ _ _ _ _ Hget_locals_1) as [_ [-> ->]].*)
    (**)
    (*apply run_codegen_capture in Hcases as [Hcases ->].*)
    (**)
    (**)
    (*(* Case es2 *)*)
    (*inv_cg_bind Hcases ?ρ ?wt ?wt ?wl ?wl ?es ?es Hcases Hcase_es2.*)
    (**)
    (*inv_cg_bind Hcase_es2 ?ρ ?wt ?wt ?wl ?wl ?es ?es Hcase_es2 Hcase_es2_br.*)
    (*inv_cg_emit Hcase_es2_br; subst.*)
    (**)
    (*inv_cg_bind Hcase_es2 ?ρ ?wt ?wt ?wl ?wl ?es ?es Hlookup_l_1 Hcase_es2.*)
    (*inv_cg_try_option Hlookup_l_1; subst.*)
    (**)
    (*inv_cg_bind Hcase_es2 ?ρ ?wt ?wt ?wl ?wl ?es ?es Hinject Hcase_es2.*)
    (*inv_cg_try_option Hinject; subst.*)
    (**)
    (*inv_cg_bind Hcase_es2 ?ρ ?wt wt_case_2 ?wl wl_case_2 ?es es_case_2 Hget_locals_2 Hcase_es2.*)
    (*inv_cg_bind Hget_locals_2 ?ρ ?wt wt_get_locals_2 ?wl wl_get_locals_2 ?es es_get_locals_2 Hnths_error Hget_locals_2.*)
    (*inv_cg_try_option Hnths_error; subst.*)
    (**)
    (*inv_cg_bind Hcases ?ρ ?wt ?wt ?wl ?wl ?es ?es Hcases Hblock_case2.*)
    (*destruct ρ12, u.*)
    (*inv_cg_emit Hblock_case2; subst.*)
    (**)
    (*destruct (run_codegen_get_locals _ _ _ _ _ _ _ Hget_locals_2) as [_ [-> ->]].*)
    (**)
    (*apply run_codegen_capture in Hcases as [Hcases ->].*)
    (**)
    (**)
    (*(* br_table *)*)
    (**)
    (*inv_cg_bind Hcases ?ρ ?wt ?wt ?wl ?wl ?es ?es Hbr_table Hunreachable.*)
    (*inv_cg_emit Hunreachable; subst.*)
    (**)
    (*inv_cg_bind Hbr_table ?ρ ?wt ?wt ?wl ?wl ?es ?es ?Hbr_table Hblock_default.*)
    (**)
    (*destruct ρ12, u.*)
    (*inv_cg_emit Hblock_default; subst.*)
    (**)
    (*apply run_codegen_capture in Hbr_table as [Hbr_table ->].*)
    (*inv_cg_emit Hbr_table; subst.*)
    (**)
    (*(* clean up *)*)
    (*subst WT WL.*)
    (*clear_nils.*)
    (**)
    (*set (x := (rev (seq 1 (0 + 1 + 1)))).*)
    (*simpl in x.*)
    (*subst x.*)
    (**)
    (*set (x := (0 + 1)).*)
    (*simpl in x.*)
    (*subst x.*)
    (**)
    (*set (x := (1 + 1)).*)
    (*simpl in x.*)
    (*subst x.*)
    (**)
    (*simplify_eq.*)
    (*destruct ρ2, ρ5, ρ7, ρ10.*)
    (**)
    (*simpl in Heq_some4.*)
    (**)
    (*(* Iris Proof *)*)
    (*iIntros (? ? ? ? ? ? ? ?) "#Hinst #Hctx Hrvs Hvs Hframe Hrt Hf Hrun".*)
    (*replace (language.of_val (immV vs0)) with (v_to_e_list vs0); last done.*)
    (*unfold expr_interp.*)
    (**)
    (**)
    (*iDestruct (Hes1 _ _ _ wtf _ _ wlf _ Hcase_es1) as "Hsem_es1".*)
    (*iDestruct (Hes2 _ _ _ wtf _ _ wlf _ Hcase_es2) as "Hsem_es2".*)

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
