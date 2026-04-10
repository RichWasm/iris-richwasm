Require Import RichWasm.iris.logrel.instr.typing.common.
From mathcomp Require Import ssrbool eqtype.

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
   set (CodeRefsType := MonoFunT τs1 τs2) in *.
   assert (HCodeRefsType: CodeRefsType = MonoFunT τs1 τs2) by auto.

   (* I need to break it up actually so coopy pasting
   iPoseProof (value_interp_coderef with "HosCoderef") as "[%n %Hoscoderef]". *)
   iPoseProof (value_interp_eq with "HosCoderef") as "HosCoderef".
   iDestruct "HosCoderef" as "(%κ0 & %Hκ & Rest)".
   destruct κ0; auto; [ | iDestruct "Rest" as "[[[] _] _]"].
   iDestruct "Rest" as "((%Hareps & %Href) & Oh)".

   (* Note: closure interp shows up here, introducing cl *)
   iDestruct "Oh" as "(%i2 & %j & %cl & %toinv & what & nstab & nsfun)".
   inversion toinv; subst; clear toinv.
   inversion Hκ; subst.

   iEval (rewrite atoms_interp_one_inv) in "HvsCoderef".
   iDestruct "HvsCoderef" as "[%v [-> HvsCoderef]]".
   apply has_values_to_consts_inv in Hevs2 as Evs2Singleton.
   cbn in Evs2Singleton. subst evs2.
   iEval (cbn) in "HvsCoderef".
   iDestruct "HvsCoderef" as "->".

   (* Note: InnerFunc shows up here after destructing cl *)
   destruct cl; last done.
   cbn in Haccum; inversion Haccum; subst; clear Haccum.
   clear_nils.
   (* note: es_rest is also empty, but I only learn that after
      destructing the list_find *)


   (* let's rename some things for my own sake *)
   rename i0 into inst.
   rename f into InnerFunc.
   rename l0 into ts.
   rename l1 into es.
   rename i2 into c.
   rename j into a.
   rename evs1 into evs.
   rename vs1 into vs.
   rename fr into f0.
   set (TheIndex := (typeimm i)) in *.

   (* I think the first three things will fome out of instance interp *)
   (* instance_interp -> instance_functions_interp has inst_funcs *)
   (* the other two are top level instance_interp *)




    destruct (list_find (λ v2 : function_type, W.function_type_eqb ϕ_W v2) l) eqn:Hmaybe.
    - (* the thing is Some *)
      destruct p.
      cbn in Hi. inversion Hi. subst.
      clear Hi.
      clear_nils.
      rename n into i.
      set (c32 := Wasm_int.Int32.repr (Z.of_N c)) in *.
      rename f into FoundFunction.
      unfold instance_interp.


      (* First save that l's length is shorter *)
      pose proof Hmaybe as Hhello.
      apply list_find_Some in Hmaybe as (LatI & FuncsEqual & EarlierNot).

      apply list_find_app_l with (l2:=wtf) in Hhello.

      iDestruct "Hinst" as "[%tosubst Hinst]".
      rewrite <- tosubst in Hhello.
      apply Is_true_true in FuncsEqual.
      move/eqP in FuncsEqual.

      subst ϕ_W.

      destruct InnerFunc eqn:HInnerFunc.

      rename r into τs1_inner; rename r0 into τs2_inner.
      rewrite HCodeRefsType.
      unfold closure_interp0.
      iEval (cbn) in "what".
      iDestruct "what" as "(%Hts1inner & %Hts2inner & what)".


      (* we need to connect the foundfunction to the inner func. I'm like
         almost certain they're equal.

         okay they HAVE to be equal, but I'm not sure how to show that... *)
      (* one thing I figure out actually is that I can't use what in the proof
         bc to use anything in what, I need to already have proven that
         found function and inner funct are equal.
       *)
      iAssert ((⌜InnerFunc = FoundFunction⌝)%I ) with "[]" as "%Yeah". {
        iPureIntro.
        rewrite HCodeRefsType in Hoff.
        cbn in Hoff.
        apply bind_Some in Hoff as (x & transts1 & rest).
        apply bind_Some in rest as (x2 & transts2 & rest).
        rename x into ts1_tounify.
        rename x2 into ts2_tounify.
        inversion rest.
        eapply (translate_types_comp_sem _ _ _ _ _ _ _ H) in transts1; auto.
        eapply (translate_types_comp_sem _ _ _ _ _ _ _ H) in transts2; auto.
        subst; auto.
        rewrite Hts1inner in transts1.
        rewrite Hts2inner in transts2.
        inversion transts1; subst. inversion transts2; subst. done.
      }
      idtac.
      subst InnerFunc.


      (* we need to get some of the f0 stuff out now *)

      change (?x ++ [?y] ++ [?z]) with (x ++ [y;z]).
      iApply (cwp_call_indirect with "[$Hrun] [$Hfr] [nstab] [nsfun]"); auto.




      all: admit.
    - (* the thing is None *)
      cbn in Hi. inversion Hi; subst; clear Hi.
      clear_nils.
      admit.



  Admitted.

End call_indirect.
