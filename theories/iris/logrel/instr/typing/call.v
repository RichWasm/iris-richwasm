Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section call.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma closure_cant_be_func_host :
    ∀ ϕ se ft ix,
      (* function_type_insts F ixs ϕ ϕ' -> *)
      closure_interp0 rti sr (value_interp rti sr) se ϕ (FC_func_host ft ix) -∗ False.
  Proof.
    induction ϕ.
    - by iIntros.
    - iIntros (???) "#Hcl".
      cbn.
      iSpecialize ("Hcl" $! MemMM).
      iPoseProof (IHϕ (senv_insert_mem MemMM se) ft ix) as "IHϕ".
      iApply IHϕ; done.
    - iIntros (???) "#Hcl".
      cbn.
      iSpecialize ("Hcl" $! []).
      iPoseProof (IHϕ (senv_insert_rep [] se) ft ix) as "IHϕ".
      iApply IHϕ; done.
    - iIntros (???) "#Hcl".
      cbn.
      iSpecialize ("Hcl" $! 42).
      iPoseProof (IHϕ (senv_insert_size 42 se) ft ix) as "IHϕ".
      iApply IHϕ; done.

    - iIntros (???) "#Hcl".
      cbn.
      (* okay yes but idk how to pull a T out of my hat *)
      (* or an sκ for that matter *)
      (* i have at least convinced myself that closure interp
         100% only works over  FC_func_native
       *)
      (* if that isn't the case this will be interesting *)
      (* also I think I get the k and sκ out of
         function_type_insts, but the induction got weird
       *)
  Admitted.

  Lemma compat_call M F L wt wt' wtf wl wl' wlf es' i ixs ϕ τs1 τs2 :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT τs1 τs2 in
    M.(mc_functions) !! i = Some ϕ ->
    function_type_insts F ixs ϕ (MonoFunT τs1 τs2) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ICall ψ i ixs)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmas ψ Hϕ Hfuntype Hok Hcg.
    cbn in Hcg; inversion Hcg; subst; clear Hcg.



    iIntros (??????????) "@@@@@@@@@@".

    (* Note: we are going to be using cwp_call. When I say first/second
       goal, I'm talking about those. *)

    (* second goal: has_values evs vs. Done by H0 *)
    (* fifth goal: ↪[frame]fr. Done by "Hfr" *)
    (* sixth goal: ↪[RUN]. Done by "Hrun"*)

    (* seventh goal: ▷ ?aN ↦[wf] FC_func_native inst (Tf ts1 ts2) ts es
               this is in instance_interp -> instance_functions_interp
               then Hϕ says that i,ϕ satisfies, for some i' = a and cl
                    1. exactly goal 1, but _+i
                    2. closure_interp .. ϕ cl
                       I think this will get us ts1, ts2, ts, and es
                    3. N.of_nat ?a |->[wf] cl, which is seventh goal
               there will be playing with opening/closing invariants
     *)
    (* first goal: f.(f_inst).inst(funcs) (i + funcimm (mr_func_user mr)) = Some a
       gotten from seventh goal decomposition, Done by Instlookup *)
    (* fourth goal: N_nat_repr a (N.of_nat a)
       this is either just fine or will encounter 2^32 issues again *)
    (* third goal: length evs = length ts1
       I'll cross this bridge when I have more info (especially with translate_types) *)

    (** So, first portion: dig into instance interp as much as possible **)
    iDestruct "Hinst" as "(%HWT & #Hruni & #Hfunci & #Htablei & %Hmm & %Hcg)".
    iPoseProof ((big_sepL_lookup _ _ _ _ Hϕ) with "Hfunci") as "Hϕ".
    iDestruct "Hϕ" as "(%a & %cl & %Instlookup & #Hcl & #nsfun)".

    (* we need cl to be FC_func_native inst ...
       okay yes it will be because of closure_interp.
     *)
    iEval (cbn) in "Hcl".
    destruct cl as [inst ft ts es | f1 f2];
      [|iPoseProof (closure_cant_be_func_host with "[$Hcl]") as "[]"].
    destruct ft as [ts1 ts2].
    iEval (cbn) in "Hcl".

    (* okay so length evs = length ts1 is going to be weird *)
    (* it's going to be a weird combo of closure interp to get
       translate_types se τs1 = Some ts1, that'll use translate_types_sem_interp_length,
       then atoms_interp_length, then has_values_length

       but I have no idea so how to get the translate_types out of there. It's deep in there

       I'll admit for now
     *)

    (* before applying, open invariant *)
    iApply fupd_cwp.
    iMod (na_inv_acc with "nsfun Hown") as "(nsfun1 & Hown & Hclose1)".
    1,2: done.
    iModIntro.

    iApply (cwp_call with "[$] [$] [$] [-]"); auto.
    - rewrite Nat.add_comm.
      done.
    - done.
    - admit. (* here's the one *)
    - done.
    - iModIntro.
      iIntros "Hfr Hrun nsfun1".

      (* idk if we need to close it now or not but we can lol *)
      iApply fupd_cwp.
      iMod ("Hclose1" with "[$Hown $nsfun1]") as "Hown".
      iModIntro.

      (* okay. This will be gotten out of the closure interp, Hcl *)
      (* but. there's an ixs number of ∀ μ ρ κ ... in the way *)
      (* hm... *)


  Admitted.

End call.
