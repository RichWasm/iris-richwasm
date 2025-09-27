Require Import RecordUpdate.RecordUpdate.

From iris.proofmode Require Import base tactics classes.

From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import codegen instrs modules util.
From RichWasm.iris Require Import autowp gc.
From RichWasm.iris.language Require Import lenient_wp lwp_pure lwp_structural logpred.
From RichWasm.iris.logrel Require Import relations fundamental_kinding.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Fundamental.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!RichWasmGCG Σ}.

  Variable sr : store_runtime.
  Variable mr : module_runtime.

  (* This should be moved to the logpred module. *)
  Definition lp_wand' Φ1 Φ2 : iProp Σ :=
    ∀ lv, denote_logpred Φ1 lv -∗ denote_logpred Φ2 lv.

  (* This should be moved to the lwp_structural module. *)
  Lemma lwp_wand s E es Φ Ψ :
    ⊢ lp_wand' Φ Ψ -∗
      lenient_wp s E es Φ -∗
      lenient_wp s E es Ψ.
  Proof.
    unfold lp_wand', lenient_wp.
    iIntros "Hwand HΦ".
    iApply (wp_wand with "[$] [$]").
  Qed.

  Lemma compat_nop M F L wl wl' es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [] [] in
    run_codegen (compile_instr me fe (INop ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Proof.
    (* This is currently following the compat_copy lemma very closely *)
    intros me fe ψ Hcompile.
    inv_cg_emit Hcompile.
    unfold have_instruction_type_sem.
    destruct ψ eqn:Hψ.
    inversion Hψ; subst l l0.
    iIntros (? ? ? ? ? ?) "Henv Hinst Hlf".
    iIntros (? ?) "Hvs Hframe Hfr Hrun".
    unfold expr_interp; cbn.
    iDestruct "Hvs" as "(%vss & %Hconcat & Hvs)".
    iPoseProof (big_sepL2_length with "[$Hvs]") as "%Hlens".
    (* To prove a list is nil, it's often easier to destruct it and
       then show the cons case is impossible.

       Here the congruence tactic deals with the 3 subgoals where
       something is not nil, where the hyps Hlens or Hconcat equate
       terms with obviously different constructors, like
         v :: vs = []
       or
         0 = S (...).                               - Ryan *)
    destruct vss, vs; cbn in Hconcat, Hlens; try congruence.
    cbn.
    (* To apply lenient_wp_nop, some strangeness has to happen
     with ->[RUN] being in the Phi. This is where lwp_wand comes in.*)

    (* I've tried to clean this definition up a bit, but it's the same
       as the one that was in an instantiate (1 := ...) tactic earlier
       -Ryan *)
    set (Ψ := {|
            lp_fr := λ fr, ∃ vs__L vs__WL,
              ⌜fr = {| W.f_locs := vs__L ++ vs__WL; W.f_inst := inst |}⌝ ∗
              (∃ vss, ⌜vs__L = concat vss⌝ ∗
                      [∗ list] τ;vs ∈ map (subst_type s__mem s__rep s__size VarT) L;vss,
                      value_interp sr mr se τ (SValues vs)) ∗
                  ⌜result_type_interp [] vs__WL⌝ ∗ na_own logrel_nais ⊤;
            lp_val :=
              λ vs, ∃ vss, ⌜vs = concat vss⌝ ∗
                           [∗ list] τ;vs' ∈ [];vss, value_interp sr mr se τ (SValues vs');
            lp_trap := True;
            lp_br := br_interp sr mr se F (map (subst_type s__mem s__rep s__size VarT) L) [] inst lh F.(fc_labels);
            lp_ret := return_interp sr mr se F;
            lp_host := fun _ _ _ _ => False
          |}%I).
    iApply lwp_wand; [| iApply (lenient_wp_nop _ _ Ψ)].
    (* Note: this strange iApply in the second subgoal makes sure that the
     ?Goal is made into the right shape (lp_run ?Goal) in the first subgoal*)
    - unfold lp_wand'.
      iIntros (lv).
      unfold denote_logpred.
      cbn.
      iIntros "[LPrunframe [%f [Hf Hlpfr]]]".
      iSplitL "LPrunframe".
      + unfold lp_run.
        unfold lp_with.
        cbn.
        case lv; simpl; auto.
        * iDestruct "LPrunframe" as "[H1 [H2 H3]]". iFrame.
        * iIntros. iDestruct "LPrunframe" as "[H _]". iExact "H".
        * iIntros. by iDestruct "LPrunframe" as "[H _]".
        * iIntros. by iDestruct "LPrunframe" as "[H _]".
      + iFrame.
    - cbn. iFrame. cbn. iExists _. iSplit; auto. auto.
  Qed.

  Lemma compat_unreachable M F L L' wl wl' ψ es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    has_instruction_type_ok F L ψ L' ->
    run_codegen (compile_instr me fe (IUnreachable ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L'.
  Admitted.

  Lemma subst_repr_closed_nop ρ :
    repr_closed ρ -> 
    ∀ s, subst_representation s ρ = ρ.
  Proof.
  Admitted.
  
  Lemma mono_rep_closed F τ ρ :
    has_mono_rep F τ ->
    has_rep F τ ρ ->
    repr_closed ρ.
  Proof.
  Admitted.

  Lemma compat_copy M F L wl wl' τ es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    has_mono_rep F τ ->
    has_copyability F τ ExCopy ->
    let ψ := InstrT [τ] [τ; τ] in
    run_codegen (compile_instr me fe (ICopy ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Proof.
    intros me fe Hmono Hcopy ψ Hcompile.
    unfold compile_instr in Hcompile.
    cbn in Hcompile.
    inv_cg_bind Hcompile ρ wl1 es_nil es1 Htype_rep Hcompile.
    unfold have_instruction_type_sem.
    destruct ψ eqn:Hψ.
    inversion Hψ; subst l l0.
    iIntros (? ? ? ? ? ?) "Henv Hinst Hlh".
    iIntros (fr vs) "Hvs Hframe Hfr Hrun".
    unfold expr_interp.
    cbn.
    inv_cg_try_option Htype_rep.
    rewrite app_nil_l.
    inversion Hcopy as [F' τ' ρ' χ ? Hhas_kind HF' Hτ' Hχ].
    subst F' τ'.
    pose proof (kinding_sound sr mr F s__mem s__rep s__size se _ _ Hhas_kind) as Hhas_kind_sem.
    iPoseProof (Hhas_kind_sem with "Henv") as "Hskind".
    iDestruct "Hskind" as "[Hrefine Hcopyable]".
    iEval (cbn) in "Hcopyable".
    assert (ρ' = ρ).
    { 
      apply type_rep_has_kind_agree in Hhas_kind.
      rewrite Heq_some in Hhas_kind.
      congruence.
    }
    subst ρ'.
    iDestruct "Hvs" as "(%vss & %Hconcat & Hvs)".
    iPoseProof (big_sepL2_length with "[$Hvs]") as "%Hlens".
    destruct vss as [|vs' [|vs'' vss]]; cbn in Hlens, Hconcat; try congruence.
    rewrite app_nil_r in Hconcat; subst vs'.
    rewrite big_sepL2_singleton.
    iApply (lwp_wand with "[Hframe]"); last first.
    - iApply ("Hcopyable" with "[] [$Hfr] [$Hrun] [$Hvs]").
      rewrite subst_repr_closed_nop;
        [|eapply mono_rep_closed; eauto; econstructor; eauto].
      iPureIntro.
      unfold is_copy_operation.
      repeat eexists.
      apply Hcompile.
    - iIntros (sv) "(Hcopy & %fr' & Hfr & <-)".
      unfold lp_wand', denote_logpred.
      cbn.
      iSplitL "Hcopy".
      + destruct sv; cbn; try iDestruct "Hcopy" as "[]".
        * iDestruct "Hcopy" as "[(%vs1 & %vs2 & %Hl & Hvs1 & Hvs2) ?]".
          iFrame.
          iExists [vs1; vs2].
          cbn.
          rewrite app_nil_r.
          by iFrame.
        * iDestruct "Hcopy" as "[? []]".
      + by iFrame.
  Qed.

  Lemma compat_drop M F L wl wl' τ es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    local_ctx_ok F L ->
    has_dropability F τ ExDrop ->
    has_mono_rep F τ ->
    let ψ := InstrT [τ] [] in
    run_codegen (compile_instr me fe (IDrop ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_num M F L wl wl' ψ e es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    local_ctx_ok F L ->
    has_instruction_type_num e ψ ->
    run_codegen (compile_instr me fe (INum ψ e)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_num_const M F L wl wl' n ν κ es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    local_ctx_ok F L ->
    has_kind F (NumT κ ν) κ ->
    let ψ := InstrT [] [NumT κ ν] in
    run_codegen (compile_instr me fe (INumConst ψ n)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_block M F L wl wl' ξ τs1 τs2 es es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    local_ctx_ok F L ->
    local_fx_ok F ξ ->
    let L' := update_locals ξ L in
    let F' := F <| fc_labels ::= cons (τs2, L') |> in
    let ψ := InstrT τs1 τs2 in
    has_mono_rep_instr F ψ ->
    have_instruction_type M F' L es ψ L' ->
    (forall wl wl' es',
        let fe' := fe_of_context F' in
        run_codegen (compile_instrs me fe' es) wl = inr ((), wl', es') ->
        ⊢ have_instruction_type_sem sr mr M F' L wl' (to_e_list es') ψ L') ->
    run_codegen (compile_instr me fe (IBlock ψ ξ es)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_loop M F L wl wl' es es' τs1 τs2 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    local_ctx_ok F L ->
    let F' := F <| fc_labels ::= cons (τs1, L) |> in
    let ψ := InstrT τs1 τs2 in
    has_mono_rep_instr F ψ ->
    have_instruction_type M F' L es ψ L ->
    (forall wl wl' es',
        let fe' := fe_of_context F' in
        run_codegen (compile_instrs me fe' es) wl = inr ((), wl', es') ->
        ⊢ have_instruction_type_sem sr mr M F' L wl' (to_e_list es') ψ L) ->
    run_codegen (compile_instr me fe (ILoop ψ es)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ite M F L wl wl' es1 es2 es' ξ τs1 τs2 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let L' := update_locals ξ L in
    local_ctx_ok F L ->
    local_fx_ok F ξ ->
    Forall (has_mono_rep F) τs1 ->
    Forall (has_mono_rep F) τs2 ->
    have_instruction_type M F L es1 (InstrT τs1 τs2) L' ->
    have_instruction_type M F L es2 (InstrT τs1 τs2) L' ->
    (forall wl wl' es',
        run_codegen (compile_instrs me fe es1) wl = inr ((), wl', es') ->
        ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') (InstrT τs1 τs2) L') ->
    (forall wl wl' es',
        run_codegen (compile_instrs me fe es2) wl = inr ((), wl', es') ->
        ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') (InstrT τs1 τs2) L') ->
    let ψ := InstrT (τs1 ++ [type_i32]) τs2 in
    run_codegen (compile_instr me fe (IIte ψ ξ es1 es2)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_br M F L L' wl wl' es' n τs1 τs τs2 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    local_ctx_ok F L ->
    local_ctx_ok F L' ->
    fc_labels F !! n = Some (τs, L) ->
    Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
    let ψ := InstrT (τs1 ++ τs) τs2 in
    run_codegen (compile_instr me fe (IBr ψ n)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_return M F L L' wl wl' es' τs τs1 τs2 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    local_ctx_ok F L ->
    local_ctx_ok F L' ->
    fc_return F = τs ->
    Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
    let ψ := InstrT (τs1 ++ τs) τs2 in
    has_mono_rep_instr F ψ ->
    run_codegen (compile_instr me fe (IReturn ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_local_get M F L wl wl' es' n τ ρ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    local_ctx_ok F L ->
    F.(typing.fc_locals) !! n = Some ρ ->
    mono_rep ρ ->
    L !! n = Some τ ->
    let τ' := RepT (VALTYPE ρ ImCopy ImDrop) ρ (ProdT (VALTYPE (ProdR []) ImCopy ImDrop) []) in
    let L' := <[n := τ']> L in
    let ψ := InstrT [] [τ] in
    run_codegen (compile_instr me fe (ILocalGet ψ n)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_local_get_copy M F L wl wl' es' n τ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    local_ctx_ok F L ->
    L !! n = Some τ ->
    has_copyability F τ ImCopy ->
    let ψ := InstrT [] [τ] in
    run_codegen (compile_instr me fe (ILocalGet ψ n)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_local_set M F L wl wl' es' n τ τ' ρ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    local_ctx_ok F L ->
    typing.fc_locals F !! n = Some ρ ->
    L !! n = Some τ ->
    has_dropability F τ ImDrop ->
    type_rep_eq F τ' ρ ->
    let L' := <[n := τ']> L in
    let ψ := InstrT [τ'] [] in
    run_codegen (compile_instr me fe (ILocalSet ψ n)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_global_get M F L wl wl' es' n m τ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    local_ctx_ok F L ->
    mc_globals M !! n = Some (m, τ) ->
    has_mono_rep F τ ->
    has_copyability F τ ImCopy ->
    let ψ := InstrT [] [τ] in
    run_codegen (compile_instr me fe (IGlobalGet ψ n)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_global_set M F L wl wl' es' n τ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    local_ctx_ok F L ->
    mc_globals M !! n = Some (Mut, τ) ->
    has_mono_rep F τ ->
    has_dropability F τ ImDrop ->
    let ψ := InstrT [τ] [] in
    run_codegen (compile_instr me fe (IGlobalSet ψ n)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_global_swap M F L wl wl' es' n τ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    local_ctx_ok F L ->
    mc_globals M !! n = Some (Mut, τ) ->
    has_mono_rep F τ ->
    let ψ := InstrT [τ] [τ] in
    run_codegen (compile_instr me fe (IGlobalSwap ψ n)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_coderef M F L wl wl' es' i ϕ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    local_ctx_ok F L ->
    mc_table M !! i = Some ϕ ->
    function_type_ok F ϕ ->
    let τ := CodeRefT (VALTYPE (PrimR I32R) ImCopy ImDrop) ϕ in
    let ψ := InstrT [] [τ] in
    run_codegen (compile_instr me fe (ICodeRef ψ i)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_inst M F L wl wl' es' ix ϕ ϕ' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    local_ctx_ok F L ->
    function_type_ok F ϕ ->
    function_type_inst F ix ϕ ϕ' ->
    let κ := VALTYPE (PrimR I32R) ImCopy ImDrop in
    let ψ := InstrT [CodeRefT κ ϕ] [CodeRefT κ ϕ'] in
    run_codegen (compile_instr me fe (IInst ψ ix)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_call M F L wl wl' es' i ixs ϕ τs1 τs2 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    local_ctx_ok F L ->
    mc_functions M !! i = Some ϕ ->
    let ψ := InstrT τs1 τs2 in
    has_mono_rep_instr F ψ ->
    function_type_insts F ixs ϕ (MonoFunT ψ) ->
    run_codegen (compile_instr me fe (ICall ψ i ixs)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_call_indirect M F L wl wl' es' τs1 τs2 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    local_ctx_ok F L ->
    Forall (has_mono_rep F) τs1 ->
    Forall (has_mono_rep F) τs2 ->
    let κ := VALTYPE (PrimR I32R) ImCopy ImDrop in
    let ψ := InstrT (τs1 ++ [CodeRefT κ (MonoFunT (InstrT τs1 τs2))]) τs2 in
    run_codegen (compile_instr me fe (ICallIndirect ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_inject M F L wl wl' es' i τs τ κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    local_ctx_ok F L ->
    τs !! i = Some τ ->
    has_kind F (SumT κ τs) κ ->
    Forall (has_mono_rep F) τs ->
    let ψ := InstrT [τ] [SumT κ τs] in
    run_codegen (compile_instr me fe (IInject ψ i)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_case M F L wl wl' es' ξ ess τ' τs κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let L' := update_locals ξ L in
    Forall2 (fun τ es => have_instruction_type M F L es (InstrT [τ] [τ']) L') τs ess ->
    let ψ := InstrT [SumT κ τs] [τ'] in
    run_codegen (compile_instr me fe (ICase ψ ξ ess)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_group M F L wl wl' es' τs ρs χ δ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    Forall2 (fun τ ρ => has_kind F τ (VALTYPE ρ χ δ)) τs ρs ->
    let τ := ProdT (VALTYPE (ProdR ρs) χ δ) τs in
    let ψ := InstrT τs [τ] in
    run_codegen (compile_instr me fe (IGroup ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ungroup M F L wl wl' es' τs κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let τ := ProdT κ τs in
    let ψ := InstrT [τ] τs in
    run_codegen (compile_instr me fe (IUngroup ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_fold M F L wl wl' es' τ κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    has_kind F (RecT κ τ) κ ->
    let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
    let ψ := InstrT [τ0] [RecT κ τ] in
    run_codegen (compile_instr me fe (IFold ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_unfold M F L wl wl' es' τ κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
    let ψ := InstrT [RecT κ τ] [τ0] in
    run_codegen (compile_instr me fe (IUnfold ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_pack M F L wl wl' es' τ τ' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    packed_existential F τ τ' ->
    let ψ := InstrT [τ] [τ'] in
    run_codegen (compile_instr me fe (IPack ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_unpack M F F0 L L0 L0' ξ wl wl' es es0 es' ψ ψ0 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let L' := update_locals ξ L in
    unpacked_existential F L es ψ L'
                        F0 L0 es0 ψ0 L0' ->
    have_instruction_type M F0 L0 es0 ψ0 L0' ->
    run_codegen (compile_instr me fe (IUnpack ψ ξ es)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_wrap M F L wl wl' es' τ0 ρ0 ρ ιs0 ιs χ δ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    has_kind F τ0 (VALTYPE ρ0 χ δ) ->
    eval_rep ρ0 = Some ιs0 ->
    eval_rep ρ = Some ιs ->
    convertible_to ιs0 ιs ->
    let τ := RepT (VALTYPE ρ χ δ) ρ τ0 in
    let ψ := InstrT [τ0] [τ] in
    run_codegen (compile_instr me fe (IWrap ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_unwrap M F L wl wl' es' τ0 ρ0 ρ ιs0 ιs χ δ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    has_kind F τ0 (VALTYPE ρ0 χ δ) ->
    eval_rep ρ0 = Some ιs0 ->
    eval_rep ρ = Some ιs ->
    convertible_to ιs0 ιs ->
    let τ := RepT (VALTYPE ρ χ δ) ρ τ0 in
    let ψ := InstrT [τ] [τ0] in
    run_codegen (compile_instr me fe (IUnwrap ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_tag M F L wl wl' es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [type_i32] [type_i31] in
    run_codegen (compile_instr me fe (ITag ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_untag M F L wl wl' es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := InstrT [type_i31] [type_i32] in
    run_codegen (compile_instr me fe (IUntag ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ref_new M F L wl wl' es' μ τ τ' κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    mono_mem μ ->
    stores_as F τ τ' ->
    let τ_ref := RefT κ μ τ' in
    has_kind F τ κ ->
    let ψ := InstrT [τ] [τ_ref] in
    run_codegen (compile_instr me fe (IRefNew ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ref_load M F L wl wl' es' μ π τ τ_val pr ρ δ κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    resolve_path τ π None pr ->
    Forall (mono_size F) pr.(pr_prefix) ->
    has_kind F pr.(pr_target) (VALTYPE ρ ImCopy δ) ->
    loads_as F pr.(pr_target) τ_val ->
    rep_ok kc_empty ρ ->
    let τ_ref := RefT κ μ τ in
    has_kind F τ_ref κ ->
    let ψ := InstrT [τ_ref] [τ_ref; τ_val] in
    run_codegen (compile_instr me fe (IRefLoad ψ π)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ref_store M F L wl wl' es' μ π τ τ_val pr κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    resolve_path τ π None pr ->
    Forall (mono_size F) pr.(pr_prefix) ->
    has_dropability F pr.(pr_target) ImDrop ->
    stores_as F τ_val pr.(pr_target) ->
    let τ_ref := RefT κ μ τ in
    let ψ := InstrT [τ_ref; τ_val] [τ] in
    run_codegen (compile_instr me fe (IRefStore ψ π)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ref_mm_store M F L wl wl' es' π τ τ_val τ_val' pr κ κ' σ σ' δ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    resolve_path τ π (Some τ_val') pr ->
    Forall (mono_size F) pr.(pr_prefix) ->
    stores_as F τ_val τ_val' ->
    has_kind F pr.(pr_target) (MEMTYPE (Sized σ) (ConstM MemMM) ImDrop) ->
    has_kind F τ_val' (MEMTYPE (Sized σ') (ConstM MemMM) δ) ->
    size_eq σ σ' ->
    let τ_ref := RefT κ (ConstM MemMM) τ in
    let τ_ref' := RefT κ' (ConstM MemMM) pr.(pr_replaced) in
    has_kind F τ_ref κ ->
    has_kind F τ_ref' κ' ->
    let ψ := InstrT [τ_ref; τ_val] [τ_ref'] in
    run_codegen (compile_instr me fe (IRefStore ψ π)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ref_swap M F L wl wl' es' π τ τ_val pr κ μ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    resolve_path τ π None pr ->
    Forall (mono_size F) pr.(pr_prefix) ->
    loads_as F τ_val pr.(pr_target) ->
    let τ_ref := RefT κ μ τ in
    let ψ := InstrT [τ_ref; τ_val] [τ_ref; τ_val] in
    run_codegen (compile_instr me fe (IRefSwap ψ π)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ref_mm_swap M F L wl wl' es' π τ τ_val τ_val' τ__π κ κ' pr :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    resolve_path τ π (Some τ_val') pr ->
    Forall (mono_size F) pr.(pr_prefix) ->
    stores_as F τ_val τ_val' ->
    loads_as F pr.(pr_target) τ__π ->
    has_mono_rep F τ__π ->
    let τ_ref := RefT κ (ConstM MemMM) τ in
    let τ_ref' := RefT κ' (ConstM MemMM) pr.(pr_replaced) in
    has_kind F τ_ref κ ->
    has_kind F τ_ref' κ' ->
    let ψ := InstrT [τ_ref; τ_val] [τ_ref'; τ__π] in
    run_codegen (compile_instr me fe (IRefSwap ψ π)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_nil M F L wl wl' es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    run_codegen (compile_instrs me fe []) es' = inr ((), wl, wl') ->
    ⊢ have_instruction_type_sem sr mr M F L wl (to_e_list wl') (InstrT [] []) L.
  Admitted.

  Lemma compat_cons M F L1 L2 L3 wl wl' es' e es τs1 τs2 τs3 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    has_instruction_type M F L1 e (InstrT τs1 τs2) L2 ->
    have_instruction_type M F L2 es (InstrT τs2 τs3) L3 ->
    (forall es' wl wl',
        run_codegen (compile_instr me fe e) wl = inr ((), wl', es') ->
        ⊢ have_instruction_type_sem sr mr M F L1 [] (to_e_list es') (InstrT τs1 τs2) L2) ->
    (forall wl wl' es',
        run_codegen (compile_instrs me fe es) wl = inr ((), wl', es') ->
        ⊢ have_instruction_type_sem sr mr M F L2 wl' (to_e_list es') (InstrT τs2 τs3) L3) ->
    run_codegen (compile_instrs me fe (e :: es)) es' = inr ((), wl, wl') ->
    ⊢ have_instruction_type_sem sr mr M F L1 wl (to_e_list wl') (InstrT τs1 τs3) L3.
  Admitted.

  Lemma compat_frame M F L L' wl wl' es es' τ τs1 τs2 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    have_instruction_type M F L es (InstrT τs1 τs2) L' ->
    has_mono_rep F τ ->
    (forall wl wl' es',
        run_codegen (compile_instrs me fe es) wl = inr ((), wl', es') ->
        ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') (InstrT τs1 τs2) L') ->
    run_codegen (compile_instrs me fe es) es' = inr ((), wl, wl') ->
    ⊢ have_instruction_type_sem sr mr M F L wl (to_e_list wl') (InstrT (τ :: τs1) (τ :: τs2)) L'.
  Admitted.

  Theorem fundamental_theorem M F L L' wl wl' es es' tf :
    have_instruction_type M F L es tf L' ->
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    run_codegen (compile_instrs me fe es) wl = inr (tt, wl', es') ->
    ⊢ have_instruction_type_sem sr mr M F L wl' (to_e_list es') tf L'.
  Proof.
    intros Htype.
    generalize dependent es'.
    generalize dependent wl'.
    generalize dependent wl.
    induction Htype using have_instruction_type_mind with
      (P := fun M F L e ψ L' _ =>
              forall es' wl wl',
                let me := me_of_context M mr in
                let fe := fe_of_context F in
                run_codegen (compile_instr me fe e) wl = inr (tt, wl', es') ->
                ⊢ have_instruction_type_sem sr mr M F L [] (to_e_list es') ψ L');
      intros es' wl wl' me fe Hcomp.
    - eapply compat_nop; eassumption.
    - eapply compat_unreachable; eassumption.
    - eapply compat_copy; eassumption.
    - eapply compat_drop; eassumption.
    - eapply compat_num; eassumption.
    - eapply compat_num_const; eassumption.
    - eapply compat_block; eassumption.
    - eapply compat_loop; eassumption.
    - eapply compat_ite.
      5: exact Htype1.
      all: eassumption.
    - eapply compat_br; eassumption.
    - eapply compat_return; eassumption.
    - eapply compat_local_get; eassumption.
    - eapply compat_local_get_copy; eassumption.
    - eapply compat_local_set; eassumption.
    - eapply compat_global_get; eassumption.
    - eapply compat_global_set; eassumption.
    - eapply compat_global_swap; eassumption.
    - eapply compat_coderef; eassumption.
    - eapply compat_inst; eassumption.
    - eapply compat_call; eassumption.
    - eapply compat_call_indirect; eassumption.
    - eapply compat_inject; eassumption.
    - eapply compat_case; eassumption.
    - eapply compat_group; eassumption.
    - eapply compat_ungroup; eassumption.
    - eapply compat_fold; eassumption.
    - eapply compat_unfold; eassumption.
    - eapply compat_pack; eassumption.
    - eapply compat_unpack; eassumption.
    - eapply compat_wrap; eassumption.
    - eapply compat_unwrap; eassumption.
    - eapply compat_tag; eassumption.
    - eapply compat_untag; eassumption.
    - eapply compat_ref_new; eassumption.
    - eapply compat_ref_load; eassumption.
    - eapply compat_ref_store; eassumption.
    - eapply compat_ref_mm_store; eassumption.
    - eapply compat_ref_swap; eassumption.
    - eapply compat_ref_mm_swap; eassumption.
    - eapply compat_nil; eassumption.
    - eapply compat_cons; eassumption.
    - eapply compat_frame; eassumption.
  Qed.

End Fundamental.
