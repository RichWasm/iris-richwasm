Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.load_common.
From RichWasm.iris.logrel Require Import case_ptr roots load_copy copy.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section case_load.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma stupid ns n i : ns !! i = Some n -> n ≤ list_max ns.
  Proof.
    generalize dependent i; generalize dependent n.
    induction ns.
    - done.
    - intros n i; destruct i.
      + cbn. intros H; inversion H; subst; clear H.
        apply Nat.le_max_l.
      + cbn. intros H; specialize (IHns n i H).
        unfold list_max in IHns.
        lia.
  Qed.

  Lemma variant_inner_type_less_than_outer_n F σ ξ τs_ser n i k τ_ser (se:semantic_env (Σ:=Σ)) n_τ ξ_τ:
    has_kind F (VariantT (MEMTYPE σ ξ) τs_ser) (MEMTYPE σ ξ) ->
    eval_size EmptyEnv σ = Some n ->
    τs_ser !! i = Some (SerT k τ_ser) ->
    eval_kind se k = Some (SMEMTYPE n_τ ξ_τ) ->
    n_τ < n.
  Proof.
    intros Hκ Heval_outer Hτsi Heval_inner.
    inversion Hκ; subst.
    pose proof (@eval_size_emptyenv Σ _ _ Heval_outer se); clear Heval_outer; rename H into Heval_outer.
    cbn in Heval_outer.
    apply bind_Some in Heval_outer.
    destruct Heval_outer as (ns & Hns & Hmax).
    inversion Hmax; clear Hmax; rename H0 into Hmax.
    destruct k as [a b | σ_τ ξ_τ'].
    { cbn in Heval_inner. apply bind_Some in Heval_inner. destruct Heval_inner as (x & y & z). inversion z. }
    cbn in Heval_inner.
    apply bind_Some in Heval_inner as (n_τ' & Heval_στ & toinv).
    inversion toinv; subst; clear toinv.
    assert (σs !! i = Some σ_τ). {
      pose proof (Forall3_lookup_l _ _ _ _ _ _ H1 Hτsi).
      destruct H as (σ_τ' & ξ_τ' & Hσ' & Hξ' & Hkindthing).
      inversion Hkindthing; subst. done.
    }
    pose proof (mapM_lookup _ σs ns i Hns).
    rewrite H in H0. cbn in H0.
    rewrite Heval_στ in H0.
    symmetry in H0.
    apply stupid in H0.
    lia.

  Qed.

  Lemma type_rep_type_skind F τ_ser ρ ιs (se:semantic_env (Σ:=Σ)) ιs' ξ :
    sem_env_interp F se ->
    type_rep (fe_type_vars (fe_of_context F)) τ_ser = Some ρ ->
    eval_rep EmptyEnv ρ = Some ιs ->
    type_skind se τ_ser = Some (SVALTYPE ιs' ξ) ->
    ιs = ιs'.
  Proof.
    intros Hse Hrep Heval Hsk.
    pose proof (@eval_rep_emptyenv Σ _ _ Heval se); clear Heval; rename H into Heval.

    destruct τ_ser; try (destruct k; cbn in Hrep; inversion Hrep); subst;
      try (cbn in Hsk; rewrite Heval in Hsk; inversion Hsk; done).
    cbn in Hsk. cbn in Hrep.
    destruct Hse as (_ & Hse).
    unfold type_ctx_interp in Hse.
    cbn in Hse.
    apply bind_Some in Hrep as (κ & HFn & Hrep).
    apply fmap_Some in Hsk as (skT & Hsen & Hsk).
    pose proof (Forall2_lookup_lr _ _ _ _ _ _ Hse HFn Hsen).
    cbn in H.
    destruct skT. destruct o0.
    destruct H as (H & _ & _).
    cbn in *. subst.
    destruct κ as [ρ' ξ' | a b]; cbn in Hrep; inversion Hrep. subst. clear Hrep.
    cbn in H.
    rewrite Heval in H. cbn in H.
    inversion H; done.
  Qed.

  Lemma kinding_info_for_τ_ser F (se:semantic_env (Σ:=Σ)) τs κs i k τ_ser ιs ξ_ser :
    sem_env_interp F se ->
    Forall (λ τ, has_ref_flag F τ GCRefs) τs ->
    (zip_with SerT κs τs) !! i = Some (SerT k τ_ser) ->
    type_skind se τ_ser = Some (SVALTYPE ιs ξ_ser) ->
    (∃ ρ, has_kind F τ_ser (VALTYPE ρ ξ_ser)) /\ ref_flag_le ξ_ser GCRefs.
  Proof.
    intros Hse Hgc Hi Hskind.
    apply lookup_zip_with_Some in Hi.
    destruct Hi as (k' & t' & toinv & Hκi & Hτi).
    inversion toinv; subst; clear toinv.
    pose proof (Forall_lookup_1 _ _ _ _ Hgc Hτi).
    inversion H; subst. clear dependent k'. rename x into k'.
    destruct H0 as [Hkind Hrefflag].
    assert (∃ ρ, k' = VALTYPE ρ ξ_ser). {
      destruct t'; inversion Hkind; subst.
      all: try by (subst κ; cbn in *; inversion Hskind; subst; eexists; done).
      all: try by (subst κ; cbn in *; apply bind_Some in Hskind as (ιs' & Hevalreps & toinv);
                  inversion toinv; subst; eexists; done).
      all: try by (destruct k' as [ρ' ξ' | σ' ξ']; cbn in *;
                   apply bind_Some in Hskind as (g & h & j); inversion j; try (subst; eexists; done)).
      cbn in *. destruct Hse as (_ & Hse); unfold type_ctx_interp in Hse.
      apply fmap_Some in Hskind as (skT & Hsen & Hsk).
      pose proof (Forall2_lookup_lr _ _ _ _ _ _ Hse H1 Hsen).
      cbn in H; destruct skT as (sk & skT); destruct skT as (skT & T).
      destruct H0 as (H0 & _ & _). cbn in *; subst.
      destruct k' as [ρ' ξ' | a b]; last first.
      { cbn in *. apply bind_Some in H0 as (g & h & j). inversion j. }
      cbn in *. apply bind_Some in H0 as (ιs' & H4 & H5). inversion H5; subst.
      eexists; done.
    }
    destruct H0 as [ρ ->]. cbn in Hrefflag.
    split; first (exists ρ; done); done.
  Qed.

  Lemma atom_interp_from_copyable_for_variants F (se:semantic_env (Σ:=Σ)) τs κs i k τ_ser ιs ξ_ser os vs :
    sem_env_interp F se ->
    Forall (λ τ, has_ref_flag F τ GCRefs) τs ->
    (zip_with SerT κs τs) !! i = Some (SerT k τ_ser) ->
    type_skind se τ_ser = Some (SVALTYPE ιs ξ_ser) ->
    Forall (forall_ptr_atom (ref_flag_ptr_interp ξ_ser)) os ->
    ⊢ ([∗ list] o;v ∈ os;vs, ⌜atom_copyable o⌝ -∗ atom_interp o v) -∗
      ([∗ list] o;v ∈ os;vs, atom_interp o v).
  Proof.
    intros Hse Hgc Hi Hskind Hint.
    apply lookup_zip_with_Some in Hi.
    destruct Hi as (k' & t' & toinv & Hκi & Hτi).
    inversion toinv; subst; clear toinv.
    pose proof (Forall_lookup_1 _ _ _ _ Hgc Hτi).
    inversion H; subst. clear dependent k'. rename x into k'.
    destruct H0 as [Hkind Hrefflag].
    assert (∃ ρ, k' = VALTYPE ρ ξ_ser). {
      destruct t'; inversion Hkind; subst.
      all: try by (subst κ; cbn in *; inversion Hskind; subst; eexists; done).
      all: try by (subst κ; cbn in *; apply bind_Some in Hskind as (ιs' & Hevalreps & toinv);
                  inversion toinv; subst; eexists; done).
      all: try by (destruct k' as [ρ' ξ' | σ' ξ']; cbn in *;
                   apply bind_Some in Hskind as (g & h & j); inversion j; try (subst; eexists; done)).
      cbn in *. destruct Hse as (_ & Hse); unfold type_ctx_interp in Hse.
      apply fmap_Some in Hskind as (skT & Hsen & Hsk).
      pose proof (Forall2_lookup_lr _ _ _ _ _ _ Hse H1 Hsen).
      cbn in H; destruct skT as (sk & skT); destruct skT as (skT & T).
      destruct H0 as (H0 & _ & _). cbn in *; subst.
      destruct k' as [ρ' ξ' | a b]; last first.
      { cbn in *. apply bind_Some in H0 as (g & h & j). inversion j. }
      cbn in *. apply bind_Some in H0 as (ιs' & H4 & H5). inversion H5; subst.
      eexists; done.
    }
    destruct H0 as [ρ ->]. cbn in Hrefflag.
    (* I think we now finally dib;t beed abttgubg wutg regards to t' *)
    clear dependent t'. clear dependent τs. clear ρ.
    (* I think it's finally iris time *)
    iIntros "H".
    iPoseProof (big_sepL2_length with "H") as "%hlen".
    iApply (big_sepL2_wand with "[] [$]").
    iApply big_sepL2_pure.
    iPureIntro.
    (* no more iris time :crab: *)
    split; first done.
    intros n o v Ho Hv. clear dependent v.
    pose proof (Forall_lookup_1 _ _ _ _ Hint Ho).
    destruct ξ_ser.
    - destruct o; try done. destruct p; try done.
    - destruct o; try done.
    - inversion Hrefflag.
  Qed.


  Lemma compat_case_load M F L L' wt wt' wtf wl wl' wlf ess es' τs τs' μ κr κv κs :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let F' := F <| fc_labels ::= cons (τs', L') |> in
    let τs_ser := zip_with SerT κs τs in
    let ψ := InstrT [RefT κr μ Imm (VariantT κv τs_ser)] (RefT κr μ Imm (VariantT κv τs_ser) :: τs') in
    length κs = length τs ->
    Forall (fun τ => has_ref_flag F τ GCRefs) τs ->
    Forall2
      (fun τ es =>
         (forall wt wt' wtf wl wl' wlf es',
            let fe' := fe_of_context F' in
            let WT := wt ++ wt' ++ wtf in
            let WL := wl ++ wl' ++ wlf in
            let lmask := wlmask fe' wl in
            run_codegen (compile_instrs mr fe' es) wt wl = inr ((), wt', wl', es') ->
            ⊢ have_instr_type_sem rti sr mr M F' L WT WL lmask es' (InstrT [τ] τs') L'))
      τs ess ->
    has_instruction_type_ok M F ψ L' ->
    run_codegen (compile_instr mr fe (ICaseLoad ψ L' ess)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L'.
  Proof.
    intros * Hlenκsτs Hgcref IH Hok Hcg.

    (* unfold the codegen, including some destructs *)
    destruct κv as [ρ ξ | σ ξ].
    { cbn in Hcg. inversion Hcg. }
    destruct τs' as [ | τ' τs' ].
    { cbn in Hcg. inversion Hcg. }
    destruct τs'; first last.
    { cbn in Hcg; inversion Hcg. }

    cbn -[compile_cases] in Hcg.
    inv_cg_bind Hcg n ?wt ?wt ?wl ?wl ?es ?es Hn Hcg.
    inv_cg_bind Hcg ts ?wt ?wt ?wl ?wl ?es ?es Hts Hcg.
    destruct (Wasm_int.Int32.modulus <? length τs_ser)%Z eqn:Hlength; first done.
    rewrite Z.ltb_ge in Hlength.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hret Hcg.
    inv_cg_ret Hret.
    inv_cg_bind Hcg x ?wt ?wt ?wl ?wl ?es ?es Hx Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hsetx Hcg.
    inv_cg_bind Hcg [[] [[] []]] ?wt ?wt ?wl ?wl ?es ?es Hcg Hret.
    inv_cg_try_option Hn.
    inv_cg_try_option Hts.
    apply wp_wlalloc in Hx as (-> & -> & -> & ->).
    inv_cg_emit Hsetx.
    subst.
    (* subst wt0 wl0 es wt2 wl2 es1 wt9 wl9 es8 wt7 wl7 es6 wt5 wl5 es4 es2 es0 es' wt3 wl3 wt1 wl1 wt' wl' wt4 wl4 es3 wt8 wl8 es7 wt11 wl11 es10. *)
    rename Hret into Hcg_case_switch.
    clear Hretval Hretval0.
    clear_nils.

    (**  BEGIN IRIS PROOF **)
    iIntros (????????) "@@@@@@@@@@@@".

    (* useful facts through atom and value interp *)
    rewrite values_interp_one_eq.
    iDestruct (value_interp_ref_sz with "Hos") as "%Hos".
    destruct (list_singleton_reflect os); last contradiction.
    rename x into o; subst os; clear Hos.
    rewrite atoms_interp_one_inv.
    iDestruct "Hvs" as "(% & % & Hvs)".
    subst vs.
    rewrite has_values_iff_to_consts in Hevs.
    cbn in Hevs.
    subst evs.
    rewrite value_interp_eq.
    iDestruct "Hos" as "(% & %Hsκ & %Hsκsv & Hos)".

    (* useful variables to set *)
    set (x := fe_wlocal_offset fe + length wl) in *.
    set (locsz := length (concat (typing.fc_locals F)) + length (WL)).
    Ltac clear_frame_things HFLEN LOCSZ WL' := repeat (cbn; try rewrite !length_app;
                  try rewrite !length_insert; try rewrite !length_concat;
                  try rewrite !sum_list_with_list_sum;
                  try rewrite !HFLEN; try unfold LOCSZ; try subst WL').

    (* frame and other facts *)
    iPoseProof (frame_interp_wl_interp with "Hframe") as "%Hwl".

    (* this section establishes a bound on ptr_local which is necessary everywhere *)
    iAssert (⌜length (f_locs fr) = locsz ⌝ %I) as "%Hflen". {
      iDestruct "Hframe" as "(%osf & %vss_L & %vs_WL & %Hlocs & %Hprims & %Hretty & Hats &  Hlocs)".
      rewrite Hlocs.
      unfold locsz.
      rewrite length_app.
      apply Forall2_Forall2_length in Hprims.
      unfold result_type_interp in Hretty.
      rewrite !length_concat Hprims.
      eapply Forall2_length in Hretty.
      rewrite !length_app in Hretty.
      rewrite -Hretty.
      cbn.
      iEval (rewrite !length_app).
      iEval (rewrite !Nat.add_assoc).
      done.
    }
    assert (x < length (f_locs fr)) as Hxfr. {
      rewrite Hflen.
      unfold locsz, x.
      subst WL. cbn; clear_nils.
      rewrite sum_list_with_list_sum length_concat.
      rewrite !length_app.
      cbn; lia.
    }

    (* convenient spot for frame facts so things aren't clogged up elsewhere *)
    assert (Hlookup_x: f_locs {| W.f_locs := <[x:=v]> (f_locs fr); W.f_inst := f_inst fr |}
              !! localimm (Mk_localidx x) = Some v). {
      cbn; apply list_lookup_insert_eq.
      clear_frame_things Hflen locsz WL.
      lia.
    }

    (* Time to split between MM and GC! *)
    iEval (cbn) in "Hos".
    destruct (eval_mem se μ) eqn:evalμ; last done; destruct b.
    1: refine ?[MemMM]. 2: refine ?[MemGC].

    [MemMM]: {
      (* dig into v now that we know μ is MM *)
      iEval (cbn) in "Hos".
      iDestruct "Hos" as "(% & % & % & %Toinv & #Hinv & Hos)".
      (* NOTE: o = PtrA (PtrHeap MemMM ℓ) *)
      inversion Toinv; subst o; clear Toinv.
      iPoseProof (atom_interp_ptr_shaped with "Hvs") as
        "(%nn & %n32 & %Hn32 & -> & %Hnshp & %rp & %Hreproot & Hv1)".
      inversion Hnshp; subst.
      cbn in Hreproot.
      inversion Hreproot; first done; subst.
      iEval (cbn) in "Hv1".
      destruct μ0; last done.
      cbn in H.
      assert (a0 = a). {
        assert (4 <= a)%N by (by eapply mod_bound_nonzero).
        assert (4 <= a0)%N by (by eapply mod_bound_nonzero).
        lia.
      }
      subst a0. clear H3 H0 H.
      rename H1 into Hmod5. rename H4 into Hnonzero.

      (* tee local, with Hos to clear the later *)
      rewrite app_assoc.
      iApply (cwp_seq with "[Hfr Hrun Hos]").
      {
        iApply (cwp_local_tee with "[Hos] [$Hfr] [$Hrun]").
        - subst x. done.
        - iModIntro.
          instantiate (1 := fun fr' vs => (⌜fr' = Build_frame (<[ x := (VAL_int32 n32) ]> fr.(f_locs)) fr.(f_inst)⌝ ∗
                                             ⌜vs = [VAL_int32 n32]⌝ ∗ (type_interp rti sr (VariantT (MEMTYPE σ ξ) τs_ser) se (SWords ws)))%I).
          iFrame.
          iSplitR; done.
      }

      iIntros (??) "[-> [-> Hos]] Hfr Hrun".

      (* Case ptr (now separate from everything else) *)
      (* I do the apply and some of the other work before the cwp_seq for the purpose of less evar weirdness *)
      (* I do literally AS much as possible here *)
      move Hcg at bottom.
      apply cwp_case_ptr in Hcg as (? & ? & ? & ? & ? & ? & ? & ? & ? &
                                      Hcg_unr & Hcg_mm & Hcg_gc & -> & -> & Hcwp).
      inv_cg_emit Hcg_unr.
      subst; clear_nils; clear Hretval.
      inv_cg_bind Hcg_mm [] ?wt ?wt ?wl ?wl ?es ?es Hcg_root Hcg_tag.
      subst; clear_nils. rename es into es_root_to_heap. rename es0 into es_load_tag.
      rename x2 into wt_gc; rename x5 into wl_gc; rename x8 into es_gc.
      cbn in Hcg_root. inversion Hcg_root; subst; clear Hcg_root. (* this will be different in gc *)
      apply wp_mem_load1_cg_state in Hcg_tag as Hstate; try done.
      destruct Hstate as (_ & -> & ->).

      (* frame fact *)
      assert (Hxextrafr:
        fe_wlocal_offset (fe_of_context F) + length (wl ++ [W.T_i32]) + length [translate_arep I32R]
        ≤ length (f_locs {| W.f_locs := <[x:=(VAL_int32 n32)]> (f_locs fr);
                          W.f_inst := f_inst fr |})). {
        clear_frame_things Hflen locsz WL.
        lia.
      }

      (* int he cwp_seq, we will be loading the tag. For that, we need to dig into
       the invariant/type interp. I will do that here *)
      (* we need things in the invariant, so we must open the invariant *)
      iApply fupd_cwp.
      iMod (na_inv_acc with "Hinv Hown") as "U"; eauto.
      iDestruct "U" as "(Hlh & Hown & Hclose)".
      iModIntro.
      iMod "Hlh". iDestruct "Hlh" as "(Hlayout & Hheap)".
      (* factssss *)
      rewrite type_interp_eq.
      iEval (cbn) in "Hos".
      pose proof (eval_size_emptyenv _ _ Heq_some se) as Hevalσ.
      rewrite Hevalσ.
      iEval (cbn) in "Hos".
      iDestruct "Hos" as "(%sκ_var & %ToInv & %Hvar_sksv & Hos)".
      inversion ToInv; subst; clear ToInv.
      destruct Hvar_sksv as [Hws_len Hws_refflag].
      iDestruct "Hos" as "(%i & %iN & %ws0 & %ws_padding & %Hnati & %ToInv & %Hpad & Hos)".
      inversion ToInv; subst; clear ToInv.
      destruct (list_lookup i (map (type_interp rti sr) τs_ser)) as [τ0|] eqn:Hlookup;
        rewrite Hlookup; last done.
      apply map_lookup_helper_backwards in Hlookup as (τ & Hτ & ->).
      assert (i < length τs_ser) as Hi_lt.
      { apply lookup_lt_is_Some. by eexists. }


      (* Do I have enough now? Alright, seq-ing time *)
      clear_nils; iEval (rewrite app_assoc).
      iApply (cwp_seq with "[Hfr Hrun Hv1 Hown Hheap Hrt Hclose Hlayout]"). {
        (* hide the value, bc the case ptr itself doesn't take any args *)
        iApply cwp_val_app; first by apply has_values_to_consts.
        (* now apply *)
        rewrite <- (app_nil_l es9).
        iApply (Hcwp with "[$Hfr] [$Hrun]");
          [by instantiate (1:=[]) | done | done | done | done | ].
        iIntros "!> Hfr Hrun". clear_nils.


        eapply wp_load1_copy_mm in Hcg_tag as H_tag.
        iPoseProof H_tag as "H_tag". clear H_tag.
        iSpecialize ("H_tag" with "[$Hfr] [$Hrun] [$Hheap] [$Hv1]").
        iSpecialize ("H_tag" with "[$Hown] [$Hrt]").

        iApply ("H_tag" with "[] [%] [%]  [%] [%] [%]  [//] [//] [//]
                [//] [//] [//] [//] [] [] ").
        - by iDestruct "Hinst" as "(_ & (_ & _ & _ & _ & that & _) & _)".
        - done. (* can't done in iapply bc of evars *)
        - by eauto with ndisj.
        - cbn; lia.
        - by instantiate (1 := I32A (Wasm_int.int_of_Z i32m (Z.of_nat i))).
        - cbn. rewrite take_0. do 2 f_equal. rewrite <- Hnati.
          rewrite Wasm_int.Int32.Z_mod_modulus_id.
          { rewrite <- Z_nat_N. by rewrite Nat2Z.id. }
          split; first lia. rewrite Nat2Z.inj_lt in Hi_lt.
          eapply Z.lt_le_trans; [apply Hi_lt|apply Hlength].
        - by iDestruct "Hinst" as "(_ & _ & _ & _ & a & b)".
        - by iDestruct "Hinst" as "(_ & _ & _ & _ & a & b)".
        - iIntros (???) "@@@@@@@@".
          iClear "Hregf".
          iSpecialize ("Ho" with "[//]").
          (* Closing the invariant here!! *)
          iSpecialize ("Hclose" with "[Hlayout Hptr Hown]"); first iFrame.
          iDestruct "Ho" as "->".

          instantiate (1 := fun f vs =>
            (∃ vf, (⌜vs = [VAL_int32 n32] ++ [VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat i))]⌝ ∗
                    ⌜f = mk_load1_frame (fe_of_context F)
                      {| W.f_locs := <[x:=VAL_int32 n32]> (f_locs fr); W.f_inst := f_inst fr |}
                      (length (wl ++ [W.T_i32])) vf⌝ ∗
                    ⌜types_agree (translate_arep I32R) vf⌝ ∗
                    ℓ ↦addr (MemMM, a) ∗
                    rt_token rti sr lpall θ ∗
                    |={⊤}=> na_own logrel_nais ⊤))%I).
          iExists vf.
          iFrame.
          iSplitR; first done; iSplitR; first done.
          apply Is_true_true in Hvf.
          done.

      }

      iIntros (??) "Rest Hfr Hrun".
      iDestruct "Rest" as "(%vf & -> & -> & %Hvf & Haddr & Hrt & Hown)".
      iApply fupd_cwp.
      iMod "Hown". iModIntro.
      clear_nils. clear Hcwp Hcg_tag. clear Hcg_gc. (* I think that's fine at least *)

      (* case switch~ *)
      (* for some reason rocq hates cwp_case_switch so long and annoying lol *)
      pose proof cwp_case_switch.
      move Hcg_case_switch at bottom.
      inv_cg_bind Hcg_case_switch [] ?wt ?wt ?wl ?wl ?es ?es Hcg_case_switch Hempty.
      cbn in Hempty; inversion Hempty; subst; clear_nils; clear Hempty.

      rename wt0 into wt_case_switch; rename wl0 into wl_case_switch. rename es into es_case_switch.
      specialize (H (wt ++ wt_gc) wt_case_switch (wl ++ [W.T_i32] ++ [translate_arep I32R] ++ wl_gc) wl_case_switch).
      specialize (H fe ts).
      set (on_each_case := ((λ (c : codegen ()) (i : nat),
               try_option EFail (τs_ser !! i)
               ≫= λ τ : type,
                    try_option EFail match τ with
                                     | SerT _ t => Some t
                                     | _ => None
                                     end
                    ≫= λ τ0 : type,
                         try_option EFail (type_rep (fe_type_vars fe) τ0)
                         ≫= λ ρ : representation,
                              try_option EFail (eval_rep EmptyEnv ρ)
                              ≫= λ ιs : list atomic_rep,
                                   memory.case_ptr (Mk_localidx x) (W.Tf [] ts) (emit W.BI_unreachable)
                                     (λ μ : base_memory, memory.load mr fe μ Copy (Mk_localidx x) 1 ιs)
                                   ≫= λ _ : () * (() * ()), c))) in *.
      set (cases := ((map
            on_each_case
            ((fix compile_cases
                (fe : function_env) (ess : list (list instruction)) {struct ess} :
                  list (codegen ()) :=
                match ess with
                | [] => []
                | es :: ess' => mapM_ (compile_instr mr fe) es :: compile_cases fe ess'
                end)
               fe ess)))) in *.

      apply Forall2_length in IH as Hlen_τs_ess.
      assert (length τs = length τs_ser) as Hlen_τs_ser. {
        by rewrite length_zip_with Hlenκsτs Nat.min_id.
      }
      assert (is_Some (ess !! i)) as Hess_i. {
        apply lookup_lt_is_Some. by rewrite -Hlen_τs_ess Hlen_τs_ser.
      }
      destruct Hess_i as [es Hess_i].

      assert (Hlencases: (length cases ≤ Wasm_int.Int32.modulus)%Z). {
        subst cases.
        by rewrite length_map -compile_cases_length -Hlen_τs_ess Hlen_τs_ser.
      }

      assert (cases !! i = Some (on_each_case (compile_instrs mr fe es))) as Hcase_i. {
        subst cases.
        apply (compile_cases_lookup mr fe) in Hess_i as Hcomes.
        cbn in Hcomes.
        pose proof (map_lookup_helper_forwards on_each_case _ _ _ Hcomes).
        done.
      }

      specialize (H cases (on_each_case (compile_instrs mr fe es))).
      specialize (H i es_case_switch ltac:(auto) ltac:(auto)).
      apply H in Hcg_case_switch; clear H.
      destruct Hcg_case_switch as (?wt_pre & ?wt_c & ?wt_post & ?wl_pre & ?wl_c & ?wl_post &
                                     es_case & Hcg_case & -> & -> & Hcg_case_switch).
      (* I have to hide the n32 again *)
      change (to_consts (?x ++ ?y)) with ((to_consts x) ++ (to_consts y)).
      rewrite <- app_assoc.
      iApply cwp_val_app; first by apply has_values_to_consts.

      (* A slightly stronger postcondition. *)
      set (Φ' := (λ fr_final vs,
        ⌜f_locs fr_final !! (fe_wlocal_offset fe + length (wl ++ [W.T_i32] ++ [translate_arep I32R] ++ wl_gc))%nat =
         Some (VAL_int32 (Wasm_int.Int32.repr i))⌝ ∗
        ⌜length vs = length ts⌝ ∗
         fvs_combine
           (λ (fr' : frame) (vs' : list value),
             ⌜frame_rel lmask fr fr'⌝ ∗
              frame_interp rti sr se (typing.fc_locals F) L' WL fr' ∗
              (∃ os' : leibnizO (list atom),
                 values_interp rti sr se [RefT κr μ Imm (VariantT (MEMTYPE σ ξ) τs_ser); τ'] os' ∗
                 atoms_interp os' vs') ∗
              (∃ θ' : address_map, rt_token rti sr lpall θ') ∗ na_own logrel_nais ⊤)
           [VAL_int32 n32] fr_final vs)%I).
      iApply (cwp_wand _ _ _ _ _ Φ' with "[-]"); swap 1 2.
      {
        iIntros (f' v') "(%Hmask & %Hvs & H)".
        iApply "H".
      }

      iApply (Hcg_case_switch with "[$] [$] [] [-]").
      { admit. } (* wl interp, later *)
      { instantiate (1 := Wasm_int.Int32.repr (Z.of_nat i)).
        apply nat_repr_i32repr.
        eapply Z.lt_le_trans.
        + apply Nat2Z.inj_lt. exact Hi_lt.
        + done. }
      { apply Is_true_true. apply has_values_to_consts. }
      {
        unfold fvs_combine.
        iIntros (fr' vs') "(Hlookup & Hvs & Hrest)".
        unfold lmask.
        eauto.
      }

      iIntros "Hfr Hrun".
      clear Hcg_case_switch.

      (* time to dig into what happens in each case! *)
      unfold on_each_case in Hcg_case.

      inv_cg_bind Hcg_case τ_ser ?wt ?wt ?wl ?wl ?es ?es ?Hcg ?Hcg.
      inv_cg_try_option Hcg.
      inv_cg_bind Hcg0 τ0 ?wt ?wt ?wl ?wl ?es ?es ?Hcg ?Hcg.
      inv_cg_try_option Hcg.
      inv_cg_bind Hcg0 ρ ?wt ?wt ?wl ?wl ?es ?es ?Hcg ?Hcg.
      inv_cg_try_option Hcg.
      inv_cg_bind Hcg0 ιs ?wt ?wt ?wl ?wl ?es ?es ?Hcg ?Hcg.
      inv_cg_try_option Hcg.
      inv_cg_bind Hcg0 [] ?wt ?wt ?wl ?wl ?es ?es Hcg_load_tag Hcg_case.
      clear_nils; subst. destruct u; destruct p. destruct u, u0.

      destruct τ_ser; cbn in Heq_some2; inversion Heq_some2.
      subst τ0; clear Heq_some2.
      rename es8 into es_load; rename es10 into es_compiled.

      (* SAVE *)
      (* now we case ptr to load tag instead of just load copy thing *)

      apply cwp_case_ptr in Hcg_load_tag as (? & ? & ? & ? & ? & ? & ? & ? & ? &
                                      Hcg_unr & Hcg_mm & Hcg_gc & -> & -> & Hcwp).
      inv_cg_emit Hcg_unr.
      subst; clear_nils; clear Hretval.
      rename x1 into wt_mm_load; rename x4 into wl_mm_load; rename x7 into es_mm_load.
      rename x2 into wt_gc_load; rename x5 into wl_gc_load; rename x8 into es_gc_load.
      eapply wp_mem_load_copy_mm in Hcg_mm.
      destruct Hcg_mm as (_ & -> & -> & Hcg_load_payload).
      clear_nils.
      (* before actually doing the cwp_seq with case ptr and load, get as much info as I can now *)

      (* time to dig into SerT k τ_ser. This can't be earlier lol *)
      rewrite Hτ in Heq_some1; inversion Heq_some1; subst; clear Heq_some1.
      rewrite type_interp_eq. iEval (cbn) in "Hos".
      iDestruct "Hos" as "(%sκ_τ & %Heval_k_τ & %Hsksv & (%os & %ToInv & Hos))".
      destruct sκ_τ as [ιs_τ ξ_τ | n_τ ξ_τ]; cbn in Hsksv; try by inversion Hsksv.
      inversion ToInv; subst; clear ToInv.
      destruct Hsksv as [Hn_τ Hrefinterp].

      (* now to dig into τ_ser. the most important fact to find is that
       length (flat_map serialize_atom os) = sum_list_with arep_flags ιs and
       that should just be through Forall2 has_arep ιs os or smthn like that *)
      rewrite type_interp_eq.
      Opaque type_skind.
      iEval (cbn) in "Hos".
      Transparent type_skind.

      assert (n_τ < length (WordInt iN :: flat_map serialize_atom os ++ ws_padding)). {
        cbn; rewrite length_app; cbn.
        lia.
      }

      (* need to open the invariant again~ *)
      iApply fupd_cwp.
      iMod (na_inv_acc with "Hinv Hown") as "U"; eauto.
      iDestruct "U" as "(Hlh & Hown & Hclose)".
      iModIntro.
      iMod "Hlh". iDestruct "Hlh" as "(Hlayout & Hheap)".
      (* I need the Hos stuff *)
      iDestruct "Hos" as "(%sκ0' & %Htorewrite & %Hareps & Hos)".
      destruct sκ0' as [ιs' ξ_ser | g h]; try by inversion Hareps.
      cbn in Heq_some3.
      assert (ιs' = ιs). {
        symmetry.
        eapply type_rep_type_skind; try done.
      }

      subst.
      destruct Hareps as (Hareps & Hrefosinterp).
      unfold has_areps in Hareps.
      destruct Hareps as (os' & toinv & Hareps); inversion toinv; subst os'; clear toinv.

      iApply (cwp_seq with "[Hfr Hrun Hown Haddr Hrt Hheap Hclose Hlayout]"). {

        rewrite <- (app_nil_l es_load).
        iApply (Hcwp with "[$Hfr] [$Hrun]");
          [by instantiate (1:=[]) | done | done | done |  | ].
        { iPureIntro.
          cbn.
          rewrite !length_app; cbn.
          rewrite list_lookup_insert_ne; try lia.
          rewrite list_lookup_insert_ne; try lia.
          apply list_lookup_insert_eq.
          clear_frame_things Hflen locsz WL.
          lia.
        }
        iIntros "!> Hfr Hrun". clear_nils.

        iApply (Hcg_load_payload with "[$] [$] [$] [$] [$] [$] [] [%] [%] [%]
             [%] [%] [//] [%] [%] [%] [%] [//] [//] [//] [] [] [-]"); clear Hcg_load_payload.
        - by iDestruct "Hinst" as "(_ & (_ & _ & _ & _ & that & _) & _)".
        - eauto with ndisj.
        - done.
        - (* yeah kinding quarantine *)
          (* this seems annoying. need to prove that the inner things fit in the bigger *)
          (* need has_areps ιs \os and has_arep_serialize_length which is in type_eq rn *)
          (* I have all the info tho for sure (aside from a type_eq import) *)
          admit.
        - instantiate (1:= os).
          done.
        - (* pathing and serializing *)
          (* this I haven't thought about enough to know if I have everything but I guess yes *)
          (* although I am pretty sure I'll want the has_arep_serialize_length fact from above here too
            so it should probably be outside the iApply *)
          admit.
        - clear_frame_things Hflen locsz WL. (* more frame things *)
          lia.
        - (* some frame preserving stuff *)
          cbn.
          rewrite !length_app; cbn.
          rewrite list_lookup_insert_ne; try lia.
          rewrite list_lookup_insert_ne; try lia.
          apply list_lookup_insert_eq.
          clear_frame_things Hflen locsz WL.
          lia.
        - clear_frame_things Hflen locsz WL.
          lia.
        - done.
        - cbn.
          iDestruct "Hinst" as "(_ & _ & _ & _ & this & that)".
          done.
        - cbn.
          iDestruct "Hinst" as "(_ & _ & _ & _ & this & that)".
          done.
        - iIntros (???) "-> @@@@@@@".
          iClear "Hregf".
          (* close invariant *)
          iSpecialize ("Hclose" with "[Hlayout Hptr Hown]"); first iFrame.
          (* task 1: use Hgcref to get atoms_interp os vs *)
          pose proof (atom_interp_from_copyable_for_variants F se τs κs i k τ_ser ιs ξ_ser os vs Hse Hgcref Hτ Htorewrite Hrefosinterp).
          iPoseProof (H0 with "[$Hos]") as "Hos". clear H0.
          (* the types got weird to set printing all *)
          instantiate (1 := fun f'' vs =>
            (∃ (vsf:list value), (
                    ⌜f'' = (mk_load_frame (fe_of_context F)
          (@set frame (list value) f_locs (fun (f : forall _ : list value, list value) (x0 : frame) => Build_frame (f (f_locs x0)) (f_inst x0))
             (@insert nat value (list value) (@list_insert value)
                (Init.Nat.add (fe_wlocal_offset fe)
                   (@length prelude.W.value_type
                      (@app prelude.W.value_type wl
                         (@app W.value_type (@cons W.value_type W.T_i32 (@nil W.value_type))
                            (@app prelude.W.value_type (@cons prelude.W.value_type (translate_arep I32R) (@nil prelude.W.value_type)) wl_gc)))))
                (VAL_int32 (Wasm_int.Int32.repr (Z.of_nat i))))
             (mk_load1_frame (fe_of_context F)
                (W.Build_frame (@insert nat value (list value) (@list_insert value) x (VAL_int32 n32) (f_locs fr)) (f_inst fr))
                (@length prelude.W.value_type (@app prelude.W.value_type wl (@cons W.value_type W.T_i32 (@nil W.value_type)))) vf))
          (@app prelude.W.value_type wl
             (@app W.value_type (@cons W.value_type W.T_i32 (@nil W.value_type))
                (@app prelude.W.value_type (@cons prelude.W.value_type (translate_arep I32R) (@nil prelude.W.value_type))
                   (@app prelude.W.value_type wl_gc wl_pre))))
          vsf)⌝ ∗
                    ⌜Forall2 (λ (ι : atomic_rep) (vf : value), is_true (types_agree (translate_arep ι) vf)) ιs
      vsf⌝ ∗
                    ([∗ list] o;v ∈ os;vs, atom_interp o v) ∗
                    ℓ ↦addr (MemMM, a) ∗
                    rt_token rti sr lpall θ ∗
                    |={⊤}=> na_own logrel_nais ⊤))%I).
          iExists vsf.
          iFrame. done.
      }

      iIntros (f vs) "(%vsf & -> & %Hvsf & Hvs & Haddr & Hrt & Hown) Hfr Hrun".
      iApply fupd_cwp.
      iMod "Hown".
      iModIntro.
      clear Hcwp Hcg_load_payload.

      (* now we have to finally actually apply the inductive hypothesis. good times *)
      move IH at bottom.
      pose proof Hτ as Hτcopy.
      apply lookup_zip_with_Some in Hτcopy as (kk & tt & toinv & Hki & Hti).
      inversion toinv; subst kk tt; clear toinv.
      pose proof (Forall2_lookup_lr _ _ _ _ _ _ IH Hti Hess_i).
      move Hcg_case at bottom.

      Opaque have_instr_type_sem.
      simpl in H0.
      Transparent have_instr_type_sem.
      subst WL WT; clear_nils.
      set (WT := wt ++ wt_gc ++ wt_pre ++ wt_gc_load ++ wt9 ++ wt_post ++ wtf) in *.
      set (WL := wl ++ [W.T_i32] ++ [translate_arep I32R] ++ wl_gc ++ wl_pre ++ map translate_arep ιs ++ wl_gc_load ++ wl9 ++ wl_post ++ wlf) in *.
      set (WT_pre := wt ++ wt_gc ++ wt_pre ++ wt_gc_load) in *.
      set (WL_pre := wl ++ [W.T_i32] ++ [translate_arep I32R] ++ wl_gc ++ wl_pre ++ map translate_arep ιs ++ wl_gc_load) in *.
      specialize H0 with (wtf:=(wt_post ++ wtf)).
      specialize H0 with (wlf:=(wl_post ++ wlf)).
      apply H0 in Hcg_case.

      (* hmmmmmmmmmmm ok *)

      unfold have_instr_type_sem in Hcg_case.
      unfold fvs_combine.
      set (final_fr := (mk_load_frame (fe_of_context F)
                     (mk_load1_frame (fe_of_context F)
                        {| W.f_locs := <[x:=VAL_int32 n32]> (f_locs fr); W.f_inst := f_inst fr |}
                        (length (wl ++ [W.T_i32])) vf <|
                      f_locs ::=
                      <[fe_wlocal_offset fe + length (wl ++ [W.T_i32] ++ [translate_arep I32R] ++ wl_gc):=
                      VAL_int32 (Wasm_int.Int32.repr i)]> |>)
                     (wl ++ [W.T_i32] ++ [translate_arep I32R] ++ wl_gc ++ wl_pre) vsf)) in *.
      set (final_B := (@cons (prod nat (forall (_ : frame) (_ : list value), uPred (iResUR Σ)))
          (@pair nat (forall (_ : frame) (_ : list value), uPred (iResUR Σ)) (@length prelude.W.value_type ts)
             (fun (f : frame) (vs0 : list value) =>
              @bi_sep (uPredI (iResUR Σ)) (@bi_pure (uPredI (iResUR Σ)) (frame_rel lmask fr f))
                (@bi_sep (uPredI (iResUR Σ))
                   (@ofe_mor_car _ _ _
                      (@ofe_mor_car _ _ _
                         (@ofe_mor_car _ _ _
                            (@ofe_mor_car _ _ _ (@frame_interp Σ logrel_na_invs0 wasmG0 richwasmG0 rti sr se) (typing.fc_locals F)) L')
                         WL)
                      f)
                   (@bi_sep (uPredI (iResUR Σ))
                      (@bi_exist (uPredI (iResUR Σ))
                         (@ofe_car _
                            (@Ofe natSI (list atom) (@equivL (list atom)) (@discrete_dist natSI (list atom) (@equivL (list atom)))
                               (@discrete_ofe_mixin natSI (list atom) (@equivL (list atom)) (@eq_equivalence (list atom)))))
                         (fun
                            os' : @ofe_car _
                                    (@Ofe natSI (list atom) (@equivL (list atom)) (@discrete_dist natSI (list atom) (@equivL (list atom)))
                                       (@discrete_ofe_mixin natSI (list atom) (@equivL (list atom)) (@eq_equivalence (list atom)))) =>
                          @bi_sep (uPredI (iResUR Σ))
                            (@ofe_mor_car _ _ _
                               (@ofe_mor_car _ _ _ (@ofe_mor_car _ _ _ (@values_interp Σ logrel_na_invs0 wasmG0 richwasmG0 rti sr) se)
                                  (@cons type (RefT κr μ Imm (VariantT (MEMTYPE σ ξ) τs_ser)) (@cons type τ' (@nil type))))
                               os')
                            (@ofe_mor_car _ _ _ (@atoms_interp Σ richwasmG0 os') (@app value (@cons value (VAL_int32 n32) (@nil value)) vs0))))
                      (@bi_sep (uPredI (iResUR Σ))
                         (@bi_exist (uPredI (iResUR Σ)) address_map (fun θ' : address_map => @rt_token Σ wasmG0 richwasmG0 rti sr lpall θ'))
                         (@na_own Σ (@logrel_na_invG Σ logrel_na_invs0) (@logrel_nais Σ logrel_na_invs0) (@top coPset coPset_top)))))))
          B)) in *.
      (* NOTE: we need to use something like cwp_frame_ctx1 (but more general) *)
      set (mini_B := (length ts,
        λ (f : frame) (vs0 : list value),
          (⌜frame_rel (wlmask (fe_of_context F') WL_pre) final_fr f⌝ ∗ frame_interp rti sr se (typing.fc_locals F') L' WL f ∗
            (∃ os' : leibnizO (list atom),
              values_interp rti sr se [τ'] os' ∗
              atoms_interp os' (vs0)) ∗
            (∃ θ' : address_map, rt_token rti sr lpall θ') ∗ na_own logrel_nais ⊤)%I)
        :: B).

      (* useful fact for a few places *)
      assert (Hrelfrfinal: frame_rel lmask fr final_fr). {
        unfold final_fr.
        unfold frame_rel.
        rewrite load_frame_inst.
        split; last done.
        unfold mask_locs_eq.
        intros ii [Hii1 Hii2].
        symmetry. rewrite mk_load_frame_stable_part; last first.
        { rewrite !length_app. cbn; cbn in Hii2. lia. }
        Opaque fe_wlocal_offset. cbn.
        rewrite list_lookup_insert_ne; last (rewrite !length_app; cbn; cbn in Hii2; lia).
        rewrite list_lookup_insert_ne; last first.
        { rewrite !length_app; cbn; cbn in Hii2. fold fe. lia. }
        rewrite list_lookup_insert_ne; try done.
        subst x.
        Transparent fe_wlocal_offset.
        lia.
      }

      (* Start specializing the IH! *)
      iPoseProof Hcg_case as "Hcg_case"; clear Hcg_case.
      iSpecialize ("Hcg_case" $! se final_fr os vs (to_consts vs) θ mini_B R).
      clear_nils. fold WT. fold WL.

      (* time to slowly start specializing *)
      iSpecialize ("Hcg_case" $! ltac:(auto) ltac:(apply has_values_to_consts) ltac:(auto)).


      iAssert (labels_interp rti sr se (typing.fc_locals F') final_fr WL
                 (wlmask (fe_of_context F') WL_pre) (fc_labels F') mini_B) as "Hlabelnew". {
        (* I think this is doable *)
        iClear "Hcg_case Hinv Hreturn Hinst".
        assert (typing.fc_locals F' = typing.fc_locals F) by (subst F'; unfold set; cbn; done).
        rewrite H1.
        assert (fe_of_context F' = fe_of_context F). {
          subst F'; unfold set; cbn. done.
        }
        rewrite H2. fold fe.
        subst F'.
        iApply (labels_interp_cons with "[] [Hlabels]"); try done.
        - move Heq_some0 at bottom.
          unfold prelude.translate_types. cbn.
          rewrite Heq_some0. cbn. clear_nils. done.
        - iModIntro. iIntros (fr' vs') "(%Hrel & Hframe & Hosvs & Hrt & Hown)". iFrame.
          iPureIntro.
          assert ((fe_of_context (F <| fc_labels ::= cons ([τ'], L') |>)) = fe) by (unfold set; cbn; done).
          rewrite H3. done.
        - (* I haven't looked closely yet but I think labels_interp_mono should be enough *)
          iApply (labels_interp_mono with "[$]").
          + done.
          + intros ii Hii. unfold lmask in Hii; unfold wlmask in *; subst WL_pre.
            destruct Hii as [Hii1 Hii2].
            split; first done.
            rewrite !length_app.
            lia.
      }
      iClear "Hlabels".
      assert (HWLstupid: WL_pre ++ wl9 ++ wl_post ++ wlf = WL) by (subst WL_pre; clear_nils; done).
      rewrite !HWLstupid.
      iSpecialize ("Hcg_case" with "[$Hlabelnew]").
      iSpecialize ("Hcg_case" $! ltac:(auto)).
      iSpecialize ("Hcg_case" with "[$Hvs]").

      iAssert (values_interp rti sr se [τ_ser] os) with "[Hos]" as "Hos". {
        rewrite values_interp_one_eq.
        rewrite value_interp_eq.
        iFrame.
        iExists (SVALTYPE ιs ξ_ser).
        iSplitR; try done.
        iPureIntro; cbn.
        split; try done.
        unfold has_areps.
        eexists; split; done.
      }

      (* Hcg_case is about to eat the val interp, but we need it later, so duplicate *)
      iAssert ((let T := values_interp rti sr se [τ_ser] os in T ∗ T)%I) with "[Hos]" as "[Hos Hos']". {
        rewrite values_interp_one_eq.
        Transparent value_interp.
        unfold value_interp.
        Opaque value_interp.
        cbn.
        pose proof (kinding_info_for_τ_ser F se τs κs i k τ_ser ιs ξ_ser).

        specialize (H1 ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto)).
        destruct H1 as [[ρ' Hkind] Hrefle].
        iApply (type_dup with "[$]"); done.
      }

      iSpecialize ("Hcg_case" with "[$Hos]").

      iAssert (frame_interp rti sr se (typing.fc_locals F') L WL final_fr) with "[Hframe]" as "Hframe". {
        (* this will be ANNOYING *)
        Opaque frame_interp. subst F'. iEval (unfold set; cbn). Transparent frame_interp.
        subst final_fr.
        iClear "Hinst Hreturn Hinv Hlabelnew".
        subst WL.
        set (temp_fr := ((mk_load1_frame (fe_of_context F)
          {| W.f_locs := <[x:=VAL_int32 n32]> (f_locs fr); W.f_inst := f_inst fr |}
          (length (wl ++ [W.T_i32])) vf <|
        f_locs ::=
        <[fe_wlocal_offset fe + length (wl ++ [W.T_i32] ++ [translate_arep I32R] ++ wl_gc):=
            VAL_int32 (Wasm_int.Int32.repr i)]> |>))) in *.
        replace ((wl ++
                [W.T_i32] ++
                [translate_arep I32R] ++
                wl_gc ++
                wl_pre ++ map translate_arep ιs ++ wl_gc_load ++ wl9 ++ wl_post ++ wlf)) with
               (((wl ++
                [W.T_i32] ++
                [translate_arep I32R] ++
                wl_gc ++
                wl_pre) ++ map translate_arep ιs ++ (wl_gc_load ++ wl9 ++ wl_post ++ wlf))).
        2: by rewrite !app_assoc.
        iApply (load_restore_frame_one_step with "[Hframe] []"); try done.
        unfold temp_fr.
        Opaque frame_interp. cbn. Transparent frame_interp.
        (* I think I just have to do it one at a time given the update frame we have *)
        (* smidge annoying but doable *)
        admit.
      }
      iSpecialize ("Hcg_case" with "[$Hframe] [$Hrt] [$Hown] [$Hfr] [$Hrun]").

      (* Now, we use cwp_frame_ctx! *)
      unfold mini_B, final_B.
      (* oh yeah wait the return might not be some, need a different cwp_frame_ctx *)
      iApply (cwp_frame_ctx_no_R_change with "[$Hcg_case] [Haddr Hos'] [] []").
      { iAccu. }
      (* TODO lemmify some of this? I basically copy-pasted *)
      - iIntros (f vs_res) "(Haddr & Hos') (%Hframerel & Hframe & Hos & Hrt & Hown)".
        iFrame.
        clear_nils. fold WL.
        iFrame.

        (* o = PtrA (PtrHeap MemMM ℓ) *)
        iDestruct "Hos" as "(%os_res & Hos & Hvs)".

        (* fact while we have our stuff *)
        iAssert (⌜length vs_res = length ts⌝%I) with "[Hvs Hos]" as "%Hvsreslen". {
          iPoseProof (atoms_interp_length with "[$Hvs]") as "%Hosreslen".
          rewrite values_interp_one_eq.
          admit.
        }

        iSplit.
        {
          (* NOTE:  HEREthis is where things used to be suspicious, but it's much more doable now, except for some off by ones *)
          (* the key is that we have Hframerel *)
          iPureIntro.
          destruct Hframerel as [Hf1 Hf2].
          unfold mask_locs_eq in Hf1.
          set (TheI := fe_wlocal_offset fe + length (wl ++ [W.T_i32] ++ [translate_arep I32R] ++ wl_gc)) in *.
          specialize (Hf1 TheI).
          rewrite <- Hf1; last first.
          { unfold wlmask, WL_pre, TheI. rewrite !length_app.
            assert ((fe_of_context (F <| fc_labels ::= cons ([τ'], L') |>)) = fe) by (unfold set; cbn; done).
            unfold F'; rewrite !H1. split; try lia.
            cbn.
            (* oh I need ιs to be length at least one? *)
            admit.
          }
          unfold final_fr, TheI.
          rewrite mk_load_frame_stable_part; last first.
          { (* hm and here wl_pre needs to be nonempty which is suspicious as it shouldn't depend on that *) admit. }
          cbn.
          apply list_lookup_insert_eq.
          clear_frame_things Hflen locsz WL.
          (* once again requires ιs to be length at least one, but then that's it *)
          admit.
        }
        iSplitR; first done.
        iSplitR.
        {
          iPureIntro.
          eapply frame_rel_trans; first exact Hrelfrfinal.
          eapply frame_rel_wlmask_mono; last exact Hframerel.
          subst WL_pre; rewrite !length_app; lia.
        }


        iExists ((PtrA (PtrHeap MemMM ℓ)) :: os_res).
        (* the addr goes with atom interp *)
        iSplitL "Hos Hos'".
        + iEval (change (?x::?y) with ([x]++y)).
          iApply (values_interp_app with "[Hos'] [$Hos]").
          iEval (rewrite values_interp_one_eq).
          iEval (rewrite value_interp_eq).
          iExists _.
          iSplitR; first done. iSplitR; first done.
          iEval (cbn).
          rewrite evalμ.
          iExists _, _, _. iSplitR; first done; iSplitR; first done.
          iModIntro.
          rewrite type_interp_eq.
          iExists (SMEMTYPE (length (WordInt iN :: flat_map serialize_atom os ++ ws_padding)) ξ).
          iSplitR; first (cbn; rewrite Hevalσ; cbn; done).
          iSplitR; first done.
          iEval (cbn).
          iExists _, iN, (flat_map serialize_atom os), ws_padding.
          iSplitR; first done. iSplitR; first done. iSplitR; first done.
          assert (list_lookup i (map (type_interp rti sr) τs_ser) = Some (type_interp rti sr (SerT k τ_ser))). {
            apply map_lookup_helper_forwards. done.
          }
          rewrite H1. clear H1.
          rewrite type_interp_eq.
          iExists _. iSplitR; first done. iSplitR; first done.
          iEval (cbn).
          iExists _; iSplitR; first done.
          (* okay FINALLY enough unwrapping *)
          rewrite values_interp_one_eq.
          iFrame.
        + change (?x :: ?y) with ([x] ++ y).
          iApply (atoms_interp_app_split_r with "[Haddr] [$]").
          clear_nils.
          cbn. iSplitL; last done.
          iExists _, n32; iSplitR; first done; iSplitR; first done.
          iExists _; iSplitR; try done.

      - iIntros (f vs_res) "(Haddr & Hos') (%Hframerel & Hframe & Hos & Hrt & Hown)".
        iFrame.
        clear_nils. fold WL.
        iFrame.

        (* o = PtrA (PtrHeap MemMM ℓ) *)
        iDestruct "Hos" as "(%os_res & Hos & Hvs)".


        iSplitR.
        { (* identical to above, which isn't fully proven yet *) admit. }

        iAssert (⌜length vs_res = length ts⌝%I) with "[Hvs Hos]" as "%Hvsreslen". {
          iPoseProof (atoms_interp_length with "[$Hvs]") as "%Hosreslen".
          rewrite values_interp_one_eq.
          admit.
        }

        iSplitR; first done.
        iSplitR.
        { iPureIntro.
          eapply frame_rel_trans; first exact Hrelfrfinal.
          eapply frame_rel_wlmask_mono; last exact Hframerel.
          subst WL_pre; rewrite !length_app; lia.
        }

        iExists ((PtrA (PtrHeap MemMM ℓ)) :: os_res).
        (* the addr goes with atom interp *)
        iSplitL "Hos Hos'".
        + iEval (change (?x::?y) with ([x]++y)).
          iApply (values_interp_app with "[Hos'] [$Hos]").
          iEval (rewrite values_interp_one_eq).
          iEval (rewrite value_interp_eq).
          iExists _.
          iSplitR; first done. iSplitR; first done.
          iEval (cbn).
          rewrite evalμ.
          iExists _, _, _. iSplitR; first done; iSplitR; first done.
          iModIntro.
          rewrite type_interp_eq.
          iExists (SMEMTYPE (length (WordInt iN :: flat_map serialize_atom os ++ ws_padding)) ξ).
          iSplitR; first (cbn; rewrite Hevalσ; cbn; done).
          iSplitR; first done.
          iEval (cbn).
          iExists _, iN, (flat_map serialize_atom os), ws_padding.
          iSplitR; first done. iSplitR; first done. iSplitR; first done.
          assert (list_lookup i (map (type_interp rti sr) τs_ser) = Some (type_interp rti sr (SerT k τ_ser))). {
            apply map_lookup_helper_forwards. done.
          }
          rewrite H1. clear H1.
          rewrite type_interp_eq.
          iExists _. iSplitR; first done. iSplitR; first done.
          iEval (cbn).
          iExists _; iSplitR; first done.
          (* okay FINALLY enough unwrapping *)
          rewrite values_interp_one_eq.
          iFrame.
        + change (?x :: ?y) with ([x] ++ y).
          iApply (atoms_interp_app_split_r with "[Haddr] [$]").
          clear_nils.
          cbn. iSplitL; last done.
          iExists _, n32; iSplitR; first done; iSplitR; first done.
          iExists _; iSplitR; try done.
    }

    [MemGC]: {
      (* dig into v now that we know μ is GC *)
      iEval (cbn) in "Hos".
      iDestruct "Hos" as "(% & % & % & %Toinv & #Hos)".
      inversion Toinv; subst o; clear Toinv.
      iPoseProof (atom_interp_ptr_shaped with "Hvs") as
        "(%nn & %n32 & %Hn32 & -> & %Hnshp & %rp & %Hreproot & Hv1)".
      inversion Hnshp; subst.
      inversion Hreproot; first done; subst.
      iEval (cbn) in "Hv1".
      destruct μ0; first done.
      cbn in H.
      assert (a0 = a). {
        assert (4 <= a)%N by (by eapply mod_bound_nonzero).
        assert (4 <= a0)%N by (by eapply mod_bound_nonzero).
        lia.
      }
      subst a0. clear H3 H0 H.
      rename H1 into Hmod5. rename H4 into Hnonzero.

      admit.
    }

  Admitted.

End case_load.
