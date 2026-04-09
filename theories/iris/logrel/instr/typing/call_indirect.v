Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section call_indirect.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma helper {A:Type} :
    ∀ (vs:list A) v, last (vs ++ [v]) = Some v.
  Proof.
    intros.
    induction vs; auto.
    change ((a::vs)++[v]) with (a::(vs++[v])).
    unfold last in *.
    destruct (vs ++ [v]); inversion IHvs. auto.
  Qed.

  Lemma value_interp_coderef se os κ τs1 τs2 :
    value_interp rti sr se (CodeRefT κ (MonoFunT τs1 τs2)) (SAtoms os) -∗ ∃ n, ⌜os = [I32A n]⌝.
  Proof.
    iIntros "Hval".
    iPoseProof (value_interp_eq with "Hval") as "Hval".
    iEval (cbn) in "Hval".
    iDestruct "Hval" as "(%κ0 & %Hκ & Rest)".
    destruct κ0; auto; [ | iDestruct "Rest" as "[[[] _] _]"].
    iDestruct "Rest" as "((%Hareps & %Href) & Oh)".

    iDestruct "Oh" as "(%i & %j & %cl & %toinv & what & nstab & nsfun)".

    inversion toinv; subst; clear toinv.
    auto.

  Qed.

  Lemma compat_call_indirect M F L wt wt' wtf wl wl' wlf es' τs1 τs2 :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let κ := VALTYPE (AtomR I32R) NoRefs in
    let ψ := InstrT (τs1 ++ [CodeRefT κ (MonoFunT τs1 τs2)]) τs2 in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ICallIndirect ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmask κ ψ Hok Hcg.
    unfold WT, WL; clear WT WL.

    cbn in Hcg.
    unfold compile_call_indirect in *.

    inv_cg_bind Hcg τ ?wt ?wt ?wl ?wl es_what ?es_rest Hτ Hcg.
    inv_cg_try_option Hτ. rename Heq_some into Hτ.
    inv_cg_bind Hcg ϕ ?wt ?wt ?wl ?wl es_τ ?es_rest Hιs Hcg.
    destruct τ; cbn in Hιs; inversion Hιs.
    inv_cg_bind Hcg ϕ_W ?wt ?wt ?wl ?wl es_ιs ?es_rest Hoff Hcg.
    inv_cg_try_option Hoff. rename Heq_some into Hoff.
    inv_cg_bind Hcg i ?wt ?wt ?wl ?wl es_wtinsert ?es_rest Hi Hcg.
    inv_cg_emit Hcg.

    subst; clear_nils; clear Hretval Hιs.

    rewrite helper in Hτ. inversion Hτ; subst. clear Hτ.

    (* okay let's try wtinsert *)
    unfold wtinsert in Hi.
    inv_cg_bind Hi huh ?wt ?wt ?wl ?wl es_what2 ?es_rest Haccum Hi.
    destruct huh. subst.

    iIntros (??????????) "@@@@@@@@@".
    (* okay we need to clear out evs *)
    iPoseProof (values_interp_app_l with "Hos")
      as "(%os1 & %os2 & -> & Hosτs1 & HosCoderef)"; auto.
    iPoseProof (atoms_interp_app_l with "Hvs")
      as "(%vs1 & %vs2 & -> & Hvsτs1 & HvsCoderef)"; auto.

   apply has_values_app_inv in H0 as (evs1 & evs2 & -> & Hevs1 & Hevs2).
   iEval (rewrite values_interp_one_eq; cbn) in "HosCoderef".

   (* I need to break it up actually so coopy pasting
   iPoseProof (value_interp_coderef with "HosCoderef") as "[%n %Hoscoderef]". *)
   iPoseProof (value_interp_eq with "HosCoderef") as "HosCoderef".
   iDestruct "HosCoderef" as "(%κ0 & %Hκ & Rest)".
   destruct κ0; auto; [ | iDestruct "Rest" as "[[[] _] _]"].
   iDestruct "Rest" as "((%Hareps & %Href) & Oh)".

   iDestruct "Oh" as "(%i2 & %j & %cl & %toinv & what & nstab & nsfun)".
   inversion toinv; subst; clear toinv.
   inversion Hκ; subst.

   iEval (rewrite atoms_interp_one_inv) in "HvsCoderef".
   iDestruct "HvsCoderef" as "[%v [-> HvsCoderef]]".
   apply has_values_to_consts_inv in Hevs2 as Evs2Singleton.
   cbn in Evs2Singleton. subst evs2.
   (* now need to unfold atom_interp a bit *)
   iEval (cbn) in "HvsCoderef".
   iDestruct "HvsCoderef" as "->".





    destruct (list_find (λ v2 : function_type, W.function_type_eqb ϕ_W v2) l) eqn:Hmaybe.
    - (* the thing is Some *)
      destruct p.
      cbn in Hi. inversion Hi. subst.
      clear Hi.
      cbn in Haccum. inversion Haccum. subst. clear Haccum.
      clear_nils.

      change (?x ++ [?y] ++ [?z]) with (x ++ [y;z]).
      iEval (cbn) in "what".
      destruct cl; last done.
      destruct f0.
      iApply (cwp_call_indirect with "[$Hrun] [$Hfr] [nstab] [nsfun]"); auto.
      4: exact.




      all: admit.
    - (* the thing is None *)
      cbn in Hi. inversion Hi; subst; clear Hi.
      clear_nils.
      cbn in Haccum; inversion Haccum; subst; clear Haccum. clear_nils.
      admit.



  Admitted.

End call_indirect.
