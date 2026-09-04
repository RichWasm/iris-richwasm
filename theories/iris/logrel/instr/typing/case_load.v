Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.load_common.
From RichWasm.iris.logrel Require Import case_ptr roots load_copy.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section case_load.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

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
    has_instruction_type_ok F ψ L' ->
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

    cbn in Hcg.
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
    inv_cg_ret Hret.
    subst wt0 wl0 es wt2 wl2 es1 wt9 wl9 es8 wt7 wl7 es6 wt5 wl5 es4 es2 es0 es' wt3 wl3 wt1 wl1 wt' wl' wt4 wl4 es3 wt8 wl8 es7 wt11 wl11 es10.
    clear Hretval Hretval0 Hretval1.
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

    (* FUTURE KINDING QUARANTINE GOES HERE *)


    (* we can process tee local before we split *)
    rewrite app_assoc.
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      iApply (cwp_local_tee with "[] [$Hfr] [$Hrun]").
      - subst x. done.
      - by instantiate (1 := fun fr' vs => (⌜fr' = Build_frame (<[ x := v ]> fr.(f_locs)) fr.(f_inst)⌝ ∗
                                           ⌜vs = [v]⌝)%I).
    }

    iIntros (??) "[-> ->] Hfr Hrun".

    (* convenient spot for frame facts so things aren't clogged up elsewhere *)
    assert (Hlookup_x: f_locs {| W.f_locs := <[x:=v]> (f_locs fr); W.f_inst := f_inst fr |}
              !! localimm (Mk_localidx x) = Some v). {
        cbn.
        apply list_lookup_insert_eq.
        rewrite Hflen.
        unfold locsz. subst WL. cbn.
        rewrite sum_list_with_list_sum length_concat.
        rewrite !length_app. cbn.
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

      (* Apply case ptr lemma *)
      apply cwp_case_ptr in Hcg as (? & ? & ? & ? & ? & ? & ? & ? & ? &
                                      Hcg_unr & Hcg_mm & Hcg_gc & -> & -> & Hcwp).

      (* hide the value, bc the case ptr itself doesn't take any args *)
      iApply cwp_val_app; first by apply has_values_to_consts.
      (* now apply *)
      rewrite <- (app_nil_l es9).
      iApply (Hcwp with "[$Hfr] [$Hrun]");
        [by instantiate (1:=[]) | done | done | done | done | ].
      iIntros "!> Hfr Hrun".
      clear Hcwp Hcg_gc. (* potentially not gc but I think we're good *)

      (* dig into Hcg *)
      inv_cg_emit Hcg_unr.
      inv_cg_bind Hcg_mm [] ?wt ?wt ?wl ?wl ?es ?es Hcg_root Hcg.
      inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_tag Hcg.
      inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg Hcg_case.
      inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_savestack Hcg.
      inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_defaults Hcg_caseblocks.
      cbn in Hcg_case; inversion Hcg_case.
      subst; clear_nils.
      clear Hcg_case Hretval.
      cbn in Hcg_root; inversion Hcg_root; subst; clear Hcg_root.
      (* use wp_root_to_heap in GC *)
      clear_nils.
      rename es1 into es_load_tag.
      rename es5 into es_save_stack.
      rename es7 into es_defaults.
      rename es8 into es_case_blocks.

      (* dig into instructions before case blocks *)

      (* first: load tag *)
      apply wp_mem_load1_cg_state in Hcg_tag as Hstate; try done.
      destruct Hstate as (_ & -> & ->).

      (* quick frame fact, now that some other things are known *)
      assert (Hxextrafr:
        fe_wlocal_offset (fe_of_context F) + length (wl ++ [W.T_i32]) + length [translate_arep I32R]
        ≤ length (f_locs {| W.f_locs := <[x:=(VAL_int32 n32)]> (f_locs fr);
                          W.f_inst := f_inst fr |})). {
cbn.
rewrite length_insert sum_list_with_list_sum.
subst locsz. rewrite Hflen. rewrite length_concat.
subst WL. clear_nils. rewrite !length_app. cbn.
lia.
}

      (* we need things in the invariant, so we must open the invariant *)
      iApply fupd_cwp.
      iMod (na_inv_acc with "Hinv Hown") as "U"; eauto.
      iDestruct "U" as "(Hlh & Hown & Hclose)".
      iModIntro.
      iMod "Hlh". iDestruct "Hlh" as "(Hlayout & Hheap)".
      (* note to self: close invariant all the way at the end? *)

      (* now time to find out some facts about the variant! *)
      (* facts I need:
         - 1 <= length ws
         - serialize_atom ?o = get_path_words 0 (arep_size I32R) ws
         - to get that o, I need to convert i into an i32 (nat -> i32 or N to i32)
       *)
      rewrite type_interp_eq.
      iEval (cbn) in "Hos".
      pose proof (eval_size_emptyenv _ _ Heq_some se) as Hevalσ.
      rewrite Hevalσ.
      iEval (cbn) in "Hos".
      iDestruct "Hos" as "(%sκ_var & %ToInv & %Hvar_sksv & Hos)".
      inversion ToInv; subst; clear ToInv.
      destruct Hvar_sksv as [Hws_len Hws_refflag].
      iDestruct "Hos" as "(%i & %iN & %ws0 & %ws_padding & %Hnati & %ToInv & Hos)".
      inversion ToInv; subst; clear ToInv.
      destruct (list_lookup i (map (type_interp rti sr) τs_ser)) as [τ0|] eqn:Hlookup;
        rewrite Hlookup; last done.
      apply map_lookup_helper_backwards in Hlookup as (τ & Hτ & ->).
      assert (i < length τs_ser) as Hi_lt.
      { apply lookup_lt_is_Some. by eexists. }

      iApply (cwp_seq with "[Hfr Hrun Hv1 Hown Hheap Hrt Hclose Hlayout]"). {
        eapply wp_load1_copy_mm in Hcg_tag as H_tag.
        iPoseProof H_tag as "H_tag". clear H_tag.
        iSpecialize ("H_tag" with "[$Hfr] [$Hrun] [$Hheap] [$Hv1] [$Hown] [$Hrt]").

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
            (∃ vf, (⌜vs = [VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat i))]⌝ ∗
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






      admit.
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
