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

  (* Note: there's a lot more we know about se', τs1, and τs2 *)
  (* I'll figure out what I need as I go *)
  Lemma unravel_closure_interp :
    ∀ F ixs τs1_s τs2_s ϕ se se_cl cl,
      sem_env_interp (Σ:=Σ) F se ->
      function_type_insts F ixs ϕ (MonoFunT τs1_s τs2_s) ->
      closure_interp0 rti sr (value_interp rti sr) se_cl ϕ cl -∗
      (∃ se' τs1 τs2, mono_closure_interp0 rti sr (value_interp rti sr) se' τs1 τs2 cl).
  Proof.
    intros.
    generalize dependent se.
    generalize dependent se_cl.
    remember (MonoFunT τs1_s τs2_s) as ϕ'.
    induction H0.
    - subst.
      intros.
      iIntros "#Hcl".
      unfold closure_interp0.
      iExists se_cl, τs1_s, τs2_s.
      done.
    - destruct ϕ.
      + intros.
        iIntros "#Hcl".
        inversion H.
      + intros.
        iIntros "#Hcl".
        inversion H; subst.
        (* this apply chooses the wrong se' *)
        iApply IHfunction_type_insts; auto.
        (* now this is substitution lemmas *)
        all: admit.
      + admit.
      + admit.
      + intros.
        iIntros "#Hcl".
        inversion H; subst.
        unfold closure_interp0.
        (* now I need a sκ and T st
           eval_kind se k = sκ   ==   Heval
           skind_interp sκ T     ==   Hskind
         *)

        apply has_kind_inv in H7 as Hkok.
        inversion Hkok; subst.
        apply (eval_kind_ok_Some _ _ _ H1) in H3 as Heval.
        inversion Heval; rename x into sκ; subst.
        apply (kinding_sound rti sr _ _ _ _ _ H7 H1) in H4 as Hskind.
        iSpecialize ("Hcl" $! sκ (value_interp rti sr se τ)).

        (* bad things with se_cl. induction hates me *)
        (* iApply IHfunction_type_insts; auto; last first. *)
        admit.

  Admitted.

  Lemma closure_cant_be_func_host :
    ∀ F ixs τs1_s τs2_s ϕ se se_cl ft ix,
      sem_env_interp (Σ:=Σ) F se ->
      function_type_insts F ixs ϕ (MonoFunT τs1_s τs2_s) ->
      closure_interp0 rti sr (value_interp rti sr) se_cl ϕ (FC_func_host ft ix) -∗ False.
  Proof.
    intros.
    iIntros "#Hcl".
    pose proof (unravel_closure_interp _ _ _ _ _ se se_cl (FC_func_host ft ix) H H0).
    iPoseProof (H1 with "[$Hcl]") as "Hcl2".
    iEval (cbn) in "Hcl2".
    iDestruct "Hcl2" as "(%a & %b & %c & F)".
    done.
  Qed.

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
      [|iPoseProof (closure_cant_be_func_host with "[$Hcl]") as "[]"; done].
    destruct ft as [ts1 ts2].
    iEval (cbn) in "Hcl".



    (* okay so length evs = length ts1 is going to be weird *)
    (* it's going to be a weird combo of closure interp to get
       translate_types se τs1 = Some ts1, that'll use translate_types_sem_interp_length,
       then atoms_interp_length, then has_values_length

       but I have no idea so how to get the translate_types out of there. It's deep in there

       I'll admit for now
     *)

    (* the translate types and everything will come out of mono_function_interp
       the mono_function_interp will come out of unravel_closure_interp
       however, that's currently not giving us enough info for the length thing.
       I'll add that later
     *)

    iPoseProof (unravel_closure_interp _ _ _ _ _ _ _ _ H Hfuntype with "[$Hcl]")
      as "#Hcl2".
    iDestruct "Hcl2" as "(%se' & %τs1_s & %τs2_s & #Hcl2 )".
    iDestruct "Hcl2" as "(%Htrans1 & %Htrans2 & Hcl2)".
    unfold mono_closure_interp0.

    (* here you can see that we'll need translate_types and some
       connection between τs1_s and τs1. That will need to happen through
       unravel_closure_interp being better
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

      iPoseProof ("Hcl2" with "[$Hvs] [Hos] [$Hrt] [$Hown] [$Hfr] [$Hrun]") as "Hcwp".
      {
        (* this will rely on more connections between se<->se' and τs1<->τs1_s
           this will also have to be added/gotten from unravel_closure_interp
         *)
        admit.
      }

      iApply (cwp_frame_ctx1 with "[Hcwp] [Hframe]").
        { iApply "Hcwp". }
        { iApply "Hframe". }
        { iIntros (??) "Hframe ((%os2 & Hvs2 & Hos2) & [%θ' Hrt] & Hown)". iFrame.
          iSplitR; auto.
          (* here's the necessary τs2<->τs2_s connection *)
          admit.
        }
        { iIntros (?) "Hframe ((%os2 & Hvs2 & Hos2) & [%θ' Hrt] & Hown)". iFrame.
          iSplitR; auto.
          (* same as above *)
          admit.
        }
        {
          iIntros (f vs0) "Hframe ((%os2 & Hvs2 & Hos2) & [%θ' Hrt] & Hown)".
          iFrame.
          (* here we need same as above, but also the same reasoning as for the
             previous length based goal but between vs0?
             ah yes this will similarly go through translate_types/whatever added onto
             unravel_closure_interp and atoms_interp
             so same as above but slightly more involved
           *)
          admit.
        }
  Admitted.

End call.
