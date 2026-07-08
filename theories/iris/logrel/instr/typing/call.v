Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.substitution.
Require Import RichWasm.iris.logrel.env_props.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section call.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  (* a deeply critical lemma that should almost certainly be true *)
  Lemma has_kind_ft_through_inst_iff F ϕ ϕ' ix :
    function_type_inst F ix ϕ ϕ' ->
    (has_kind_ft F ϕ <->
    has_kind_ft F ϕ').
  Proof.
  Admitted.

  Lemma has_kind_ft_through_inst F ϕ ϕ' ix :
    function_type_inst F ix ϕ ϕ' ->
    has_kind_ft F ϕ ->
    has_kind_ft F ϕ'.
  Proof.
    intros.
    by apply (has_kind_ft_through_inst_iff F ϕ ϕ' ix H).
  Qed.

  Lemma has_kind_ft_through_inst_backwards F ϕ ϕ' ix :
    function_type_inst F ix ϕ ϕ' ->
    has_kind_ft F ϕ' ->
    has_kind_ft F ϕ.
  Proof.
    intros.
    by apply (has_kind_ft_through_inst_iff F ϕ ϕ' ix H).
  Qed.


  Lemma unravel_closure_interp :
    ∀ F ixs τs1_s τs2_s ϕ se cl,
      let ϕ' := InnerFunT (MonoFunT τs1_s τs2_s) in
      sem_env_interp (Σ:=Σ) F se ->
      function_type_insts F ixs ϕ ϕ' ->
      has_kind_ft F ϕ ->
      has_kind_ft F ϕ' ->
      closure_interp rti sr ϕ se cl -∗
        (* ϕ' = refresh_kinds_ft F (subst_function_type sub_m sub_r sub_s sub_t ϕ) /\ *)
        mono_closure_interp rti sr
          τs1_s τs2_s (map (type_interp rti sr) τs1_s) (map (type_interp rti sr) τs2_s) se cl.
  Proof.
    intros *. intros Hse Hfinst Hkind_ϕ Hkind_ϕ'.
    subst ϕ'.
    remember (InnerFunT (MonoFunT τs1_s τs2_s)) as ϕ'.
    induction Hfinst; iIntros "Hcl";  subst.
    - done.
    - pose proof (has_kind_ft_through_inst _ _ _ _ H Hkind_ϕ) as Hkind_ϕ_middle.
      inversion H; subst.
      + inversion H0; subst.
        assert (Hϕ': ϕ'0 = refresh_kinds_ift F (subst_inner_function_type VarM VarR VarS (unscoped.scons τ VarT) ϕ)). {
          (* by hkind_ϕ_middle and refresh_kinds_eq_mod_kinds *)
          pose proof (has_kind_ft_function_type_eq_mod_kinds rti sr mr) as (_ & _ & this).
          eapply this; try done.
          inversion Hkind_ϕ_middle; subst; done.
        }
        assert (∃ sκ, eval_kind se κ = Some sκ). {
          apply has_kind_inv in H1 as Hokhas.
          inversion Hokhas as [??? Hok_τ Hok_κ]; subst.
          clear Hokhas.
          destruct (eval_kind_ok_Some _ _ _ Hse Hok_κ) as [sκ_T Hsκ_T].
          inversion H2; subst.
          - cbn in Hsκ_T.
            apply bind_Some in Hsκ_T as (ιs & evalρ & toinv).
            inversion toinv; subst.
            exists (SVALTYPE ιs ξ').
            cbn.
            rewrite evalρ.
            cbn. done.
          - cbn in Hsκ_T.
            apply bind_Some in Hsκ_T as (ιs & evalρ & toinv).
            inversion toinv; subst.
            exists (SMEMTYPE ιs ξ').
            cbn.
            rewrite evalρ.
            cbn. done.
        }
        destruct H4 as (sκ & evalκ).
        clear H3.
        rewrite closure_interp_eq. iEval (cbn -[senv_insert_type]) in "Hcl".
        iPoseProof (inner_closure_interp_scons_insert_type rti sr mr _ _ _ _ _ with "[$Hcl]") as "Hcl2"; try done.
        * rewrite <- Hϕ'.
          inversion Hkind_ϕ_middle; subst. done.
        * inversion Hkind_ϕ; subst.
          inversion H5; subst.
          done.
        * specialize (IHHfinst ltac:(auto) eq_refl ltac:(auto) ltac:(auto)).
          iApply IHHfinst.
          rewrite closure_interp_eq.
          cbn.
          rewrite <- Hϕ'.
          rewrite inner_closure_interp_eq.
          done.
      + rewrite closure_interp_eq. iEval (cbn -[senv_insert_mem]) in "Hcl".
        pose proof (refresh_kinds_id) as (_ & this & _); try done.
        apply this in Hkind_ϕ_middle as torew.
        iDestruct "Hcl" as "#Hcl".
        iPoseProof (closure_interp_scons_insert_mem rti sr mr _ _ with "[$Hcl]") as "Hcl2"; try done.
        * fold ϕ'0.
          rewrite <- torew.
          done.
        * inversion Hkind_ϕ; try done.
        * fold ϕ'0.
          rewrite <- torew.
          specialize (IHHfinst ltac:(auto) eq_refl ltac:(auto) ltac:(auto)).
          by iApply IHHfinst.
      + rewrite closure_interp_eq. iEval (cbn -[senv_insert_rep]) in "Hcl".
        pose proof (refresh_kinds_id) as (_ & this & _); try done.
        apply this in Hkind_ϕ_middle as torew.
        iDestruct "Hcl" as "#Hcl".
        iPoseProof (closure_interp_scons_insert_rep rti sr mr _ _ with "[$Hcl]") as "Hcl2"; try done.
        * fold ϕ'0.
          rewrite <- torew.
          done.
        * inversion Hkind_ϕ; try done.
        * fold ϕ'0.
          rewrite <- torew.
          specialize (IHHfinst ltac:(auto) eq_refl ltac:(auto) ltac:(auto)).
          by iApply IHHfinst.
      + rewrite closure_interp_eq. iEval (cbn -[senv_insert_size]) in "Hcl".
        pose proof (refresh_kinds_id) as (_ & this & _); try done.
        apply this in Hkind_ϕ_middle as torew.
        iDestruct "Hcl" as "#Hcl".
        iPoseProof (closure_interp_scons_insert_size rti sr mr _ _ with "[$Hcl]") as "Hcl2"; try done.
        * fold ϕ'0.
          rewrite <- torew.
          done.
        * inversion Hkind_ϕ; try done.
        * fold ϕ'0.
          rewrite <- torew.
          specialize (IHHfinst ltac:(auto) eq_refl ltac:(auto) ltac:(auto)).
          by iApply IHHfinst.
  Qed.

  Lemma closure_cant_be_func_host :
    ∀ F ixs τs1_s τs2_s ϕ se ft ix,
      sem_env_interp (Σ:=Σ) F se ->
      function_type_insts F ixs ϕ (InnerFunT (MonoFunT τs1_s τs2_s)) ->
      has_kind_ft F ϕ ->
      has_kind_ft F (InnerFunT (MonoFunT τs1_s τs2_s)) ->
      closure_interp rti sr ϕ se (FC_func_host ft ix) -∗ False.
  Proof.
    intros.
    iIntros "#Hcl".
    pose proof (unravel_closure_interp _ _ _ _ _ se (FC_func_host ft ix) H H0); try done.
    iPoseProof (H3 with "[$Hcl]") as "Hcl2"; try done.
  Qed.

  Lemma has_kind_ft_from_ok F τs1 τs2 L :
    has_instruction_type_ok F (InstrT τs1 τs2) L ->
    has_kind_ft F (InnerFunT (MonoFunT τs1 τs2)).
  Proof.
    intros Hok.
    inversion Hok; subst.
    inversion H; subst.
    unfold has_mono_rep in *.
    assert (Forall (λ τ, ∃ κ, has_kind F τ κ) τs1). {
      apply Forall_lookup_2.
      intros i τ Hiτ.
      pose proof (Forall_lookup_1 _ _ _ _ H1 Hiτ).
      cbn in H3.
      destruct H3 as (ρ & hrep & hmono).
      inversion hrep; subst.
      eexists; done.
    }
    apply Forall_exists_Forall2_l in H3.
    destruct H3 as (κs1 & Hτs1). clear H1.
    assert (Forall (λ τ, ∃ κ, has_kind F τ κ) τs2). {
      apply Forall_lookup_2.
      intros i τ Hiτ.
      pose proof (Forall_lookup_1 _ _ _ _ H2 Hiτ).
      cbn in H1.
      destruct H1 as (ρ & hrep & hmono).
      inversion hrep; subst.
      eexists; done.
    }
    apply Forall_exists_Forall2_l in H1.
    destruct H1 as (κs2 & Hτs2). clear H2.
    constructor.
    econstructor; done.
  Qed.

  (* should be true, but requires an actual fully fleged subsitution lemma most likely *)
  (* but for has_kind which. not now. *)
  (* base case is fine though *)
  Lemma has_kind_ft_from_insts_and_ok F ixs ϕ τs1 τs2 L :
    function_type_insts F ixs ϕ (InnerFunT (MonoFunT τs1 τs2)) ->
    has_instruction_type_ok F (InstrT τs1 τs2) L ->
    has_kind_ft F ϕ.
  Proof.
    remember (InnerFunT (MonoFunT τs1 τs2)) as ϕ'.
    intros Hfinst.
    induction Hfinst; intros Hok.
    - subst.
      constructor.
      inversion Hok; subst.
      inversion H; subst.
      unfold has_mono_rep in *.
      assert (Forall (λ τ, ∃ κ, has_kind F τ κ) τs1). {
        apply Forall_lookup_2.
        intros i τ Hiτ.
        pose proof (Forall_lookup_1 _ _ _ _ H1 Hiτ).
        cbn in H3.
        destruct H3 as (ρ & hrep & hmono).
        inversion hrep; subst.
        eexists; done.
      }
      apply Forall_exists_Forall2_l in H3.
      destruct H3 as (κs1 & Hτs1). clear H1.
      assert (Forall (λ τ, ∃ κ, has_kind F τ κ) τs2). {
        apply Forall_lookup_2.
        intros i τ Hiτ.
        pose proof (Forall_lookup_1 _ _ _ _ H2 Hiτ).
        cbn in H1.
        destruct H1 as (ρ & hrep & hmono).
        inversion hrep; subst.
        eexists; done.
      }
      apply Forall_exists_Forall2_l in H1.
      destruct H1 as (κs2 & Hτs2). clear H2.
      econstructor; done.
    - subst ϕ''.
      specialize (IHHfinst eq_refl Hok).
      rename IHHfinst into Hkind_ϕ'.
      by apply (has_kind_ft_through_inst_iff F ϕ ϕ' ix H).
  Qed.


  Lemma compat_call M F L wt wt' wtf wl wl' wlf es' i ixs ϕ τs1 τs2 :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT τs1 τs2 in
    M.(mc_functions) !! i = Some ϕ ->
    function_type_insts F ixs ϕ (InnerFunT (MonoFunT τs1 τs2)) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ICall ψ i ixs)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmas ψ Hϕ Hfuntype Hok Hcg.
    cbn in Hcg; inversion Hcg; subst; clear Hcg.



    iIntros (??????????) "@@@@@@@@@@".
    (** So, first portion: dig into instance interp as much as possible **)
    iDestruct "Hinst" as "(%HWT & #Hruni & #Hfunci & #Htablei & %Hmm & %Hcg)".
    iPoseProof ((big_sepL_lookup _ _ _ _ Hϕ) with "Hfunci") as "Hϕ".
    iDestruct "Hϕ" as "(%a & %cl & %Instlookup & #Hcl & #nsfun)".
    iPoseProof (empty_closure_interp rti sr mr se with "[$Hcl]") as "Hcl2".
    iRename "Hcl" into "HclOLDDDDDDD".
    iRename "Hcl2" into "Hcl".

    (* kinding quarantine *)
    pose proof (has_kind_ft_from_insts_and_ok _ _ _ _ _ _ Hfuntype Hok) as Hkind_ϕ.
    pose proof (has_kind_ft_from_ok _ _ _ _ Hok) as Hkind_mono.



    (* we need cl to be FC_func_native inst ...
       okay yes it will be because of closure_interp.
     *)
    iEval (cbn) in "Hcl".
    destruct cl as [inst ft ts es | f1 f2];
      [|iPoseProof (closure_cant_be_func_host with "[$Hcl]") as "[]"; done].
    destruct ft as [ts1 ts2].
    iEval (cbn) in "Hcl".


    (* kinding quarantine portion *)
    iPoseProof (unravel_closure_interp _ _ _ _ _ _ _ H Hfuntype with "[$Hcl]")
      as "#Hcl2"; try done.
    (* iDestruct "Hcl2" as "(%se' & %τs1_s & %τs2_s & #Hcl2 )". *)
    iDestruct "Hcl2" as "#Hcl2".
    iDestruct "Hcl2" as "(%Htrans1 & %Htrans2 & Hcl2)".

    iAssert (⌜length evs = length ts1⌝%I) as "%hlenevsts1". {
      iPoseProof (translate_types_sem_interp_length with "[$Hos]") as "%len1"; try done.
      rewrite <- len1.
      iPoseProof (big_sepL2_length with "[$Hvs]") as "%len2"; try done.
      rewrite len2.
      iPureIntro.
      unfold has_values in H0.
      apply has_values_length. done.
    }

    (* before applying, open invariant *)
    iApply fupd_cwp.
    iMod (na_inv_acc with "nsfun Hown") as "(nsfun1 & Hown & Hclose1)".
    1,2: done.
    iModIntro.

    iApply (cwp_call with "[$] [$] [$] [-]"); auto.
    - rewrite Nat.add_comm.
      done.
    - done.
    - done.
    - iModIntro.
      iIntros "Hfr Hrun nsfun1".

      (* idk if we need to close it now or not but we can lol *)
      iApply fupd_cwp.
      iMod ("Hclose1" with "[$Hown $nsfun1]") as "Hown".
      iModIntro.

      iPoseProof ("Hcl2" with "[$Hvs] [Hos] [$Hrt] [$Hown] [$Hfr] [$Hrun]") as "Hcwp".
      {
        done.
      }

      iApply (cwp_frame_ctx1 with "[Hcwp] [Hframe]").
        { iApply "Hcwp". }
        { iApply "Hframe". }
        { iIntros (??) "Hframe ((%os2 & Hvs2 & Hos2) & [%θ' Hrt] & Hown)". iFrame.
          iSplitR; auto.
        }
        { iIntros (?) "Hframe ((%os2 & Hvs2 & Hos2) & [%θ' Hrt] & Hown)". iFrame.
          iSplitR; auto.
        }
        {
          iIntros (f vs0) "Hframe ((%os2 & Hvs2 & Hos2) & [%θ' Hrt] & Hown)".
          iAssert (⌜length vs0 = length ts2⌝%I) as "%lenvs0ts2". {
            change (values_interp1 (map (type_interp rti sr) τs2) se os2) with
              (values_interp rti sr se τs2 os2).
            iPoseProof (translate_types_sem_interp_length with "[$Hos2]") as "%len1"; try done.
            rewrite <- len1.
            iPoseProof (big_sepL2_length with "[$Hvs2]") as "%len2"; try done.
          }
          iFrame.
          iSplitR; try done.
        }
  Qed.

End call.
