Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.path.
Require Import RichWasm.iris.logrel.store_common.
Require Import RichWasm.iris.logrel.load_common.
Require Import RichWasm.iris.logrel.case_ptr.
Require Import RichWasm.iris.logrel.roots.
Require Import RichWasm.iris.logrel.load_move.
Require Import RichWasm.iris.numerics.
Require Import RichWasm.compiler.memory.
Require Import RichWasm.util.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section swap.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma get_all_kinding_info_swap τ κ μ τval π pr :
    let ψ := InstrT [RefT κ μ Mut τ; τval] [RefT κ μ Mut τ; τval] in
    resolves_path τ π None pr ->
    ∀ F off ρ se sκ κser L ιs o1,
      sem_env_interp F se ->
      path_offset (fe_of_context F) τ π = Some off ->
      Forall (has_mono_size F) pr.(pr_prefix) ->
      type_skind (Σ:=Σ) se (RefT κ μ Mut τ) = Some sκ ->
      eval_kind se κ = Some sκ ->
      pr_target pr = SerT κser τval ->
      has_instruction_type_ok F ψ L ->
      type_rep (fe_type_vars (fe_of_context F)) τval = Some ρ ->
      eval_rep EmptyEnv ρ = Some ιs ->
      skind_has_svalue sκ (SAtoms [o1]) ->
      (∃ σ ξ ξser sz ξ_ref,
          has_kind F τ (MEMTYPE σ ξ) /\
            has_kind F (pr.(pr_target)) (MEMTYPE (RepS ρ) ξser) /\
            has_kind F τval (VALTYPE ρ ξser) /\
            eval_size EmptyEnv (RepS ρ) = Some sz /\
            κ = VALTYPE (AtomR PtrR) ξ_ref /\
            sκ = SVALTYPE [PtrR] ξ_ref /\
            sum_list_with arep_size ιs = sz /\
            eval_kind se κser = Some (SMEMTYPE sz ξser) /\
            length (flat_map arep_flags ιs) = sz /\
            type_skind se τval = Some (SVALTYPE ιs ξser) /\
            type_skind se (SerT κser τval) = Some (SMEMTYPE sz ξser)).
  Proof.
    intros ψ Hresolves.
    intros * Hse Hoffset Hmono Htypeskind Hevalκ Hprtarget Hok Hrep Hevalρ Hsksv.

    unfold ψ in Hok.
    inversion Hok; subst.
    destruct H as [Href2 _].
    inversion Href2. subst.
    destruct H2 as (? & Hrep3 & Hmono2).
    inversion Hrep3; subst.
    apply has_kind_ref_ty in H.
    destruct H as (σ & ξτ & Hkind).

    assert (has_mono_size F (pr_target pr)).
    {
      repeat
        match goal with
        | H : has_instruction_type_ok _ _ _ |- _ => inversion H; clear H; subst
        | H : has_mono_rep_instr _ _ |- _ => inversion H; clear H; subst
        | H : Forall _ (_ :: _) |- _ => inversion H; clear H; subst
        | H : Forall _ [] |- _ =>  clear H
        | H : has_mono_rep _ _ |- _ => destruct H as (?ρ & ?Hrep & ?Hmono)
        | H : has_rep _ _ _ |- _ => inversion H; subst; clear H
        | H : MEMTYPE _ _ = MEMTYPE _ _ |- _ => inversion H; subst; clear H
        | H : VALTYPE _ _ = VALTYPE _ _ |- _ => inversion H; subst; clear H
        | H : has_kind ?F (RefT _ _ _ _) _ |- _ => eapply has_kind_ref_ty in H; destruct H as (? & ? & ?); subst
        | H : has_kind ?F ?t ?k,
          H' : has_kind ?F ?t ?k' |- _ =>
            pose proof (has_kind_agree F t k k' H H'); clear H'
        end.
      pose proof Hresolves as Hresolves'.
      rewrite Hprtarget.
      eapply pr_target_kind in Hresolves'; eauto using KSer.
      destruct Hresolves' as (ktgt & Hkind0).
      rewrite Hprtarget in Hkind0.
      inversion Hkind0; subst.
      unfold κ0 in *.
      eexists; eauto.
      unfold is_mono_size.
      constructor.
      repeat
        match goal with
        | H : has_mono_rep_instr _ _ |- _ => inversion H; clear H; subst
        | H : Forall _ (_ :: _) |- _ => inversion H; clear H; subst
        | H : Forall _ [] |- _ =>  clear H
        | H : has_mono_rep _ _ |- _ => destruct H as (?ρ & ?Hrep & ?Hmono)
        | H : has_rep _ _ _ |- _ => inversion H; subst; clear H
        | H : MEMTYPE _ _ = MEMTYPE _ _ |- _ => inversion H; subst; clear H
        | H : VALTYPE _ _ = VALTYPE _ _ |- _ => inversion H; subst; clear H
        | H : has_kind ?F ?t ?k,
          H' : has_kind ?F ?t ?k' |- _ =>
            pose proof (has_kind_agree F t k k' H H'); clear H'
        end.
      by unfold is_mono_rep in *.
    }

    inversion H as [? ? σtgt ξser Hhktgt Htgtmono HF' HT]; subst.
    rewrite Hprtarget in Hhktgt.
    inversion Hhktgt; subst. unfold κ1 in *; clear κ1.

    pose proof (mono_size_eval_emp_Some _ Htgtmono) as (sz & Hev).

    unfold type_rep in Hrep.

    (* type_kind_has_kind_agree *)
    apply bind_Some in Hrep.
    destruct Hrep as (κ_temp & type_kind_τval & kindrep).
    pose proof (type_kind_has_kind_agree F τval _ _ H4 type_kind_τval).
    subst.
    inversion kindrep; subst.

    (* the other things that would be nice: sκ is SVALTYPE .. *)
    inversion Hrep3; subst. (* ey win we have valtype *)
    rename H1 into Hkind_ref. rename x into ρ_ref. rename ξ0 into ξ_ref.

    (* okay what I want now is that ρ_ref is AtomR PtrR *)
    assert (ρ_ref = AtomR PtrR). {
      inversion Hkind_ref; subst; done.
    }
    subst.
    (* then ξ_ref will be either GCRef of AnyRef which isn't smthn rn *)
    (* future lemma that takes in eval_mem μ can say smthn tho *)
    destruct sκ; [| by destruct Hsksv].
    rename r into ξ_sκ.
    assert (κ = VALTYPE (AtomR PtrR) ξ_ref). {
      inversion Hkind_ref; done.
    }
    subst.

    assert (ξ_ref = ξ_sκ). {
      cbn in Hevalκ. inversion Hevalκ; done.
    }
    subst ξ_sκ.
    assert (l = [PtrR]). {
      cbn in Hevalκ. inversion Hevalκ; done.
    }
    subst.


    assert (sum_list_with arep_size ιs = sz). {
      (* I think this is the right lemma at least *)
      unfold eval_size in Hev.
      rewrite Hevalρ in Hev.
      cbn in Hev. inversion Hev; subst.
      by apply sum_list_with_list_sum.
    }

    (* next up: κser stuff *)
    rename κ0 into κser.
    assert (eval_kind (senv_empty (Σ:=Σ)) κser = Some (SMEMTYPE sz ξser)). {
      cbn.
      rewrite eval_rep_senv_empty_irrel.
      rewrite Hevalρ.
      cbn.
      rewrite sum_list_with_list_sum in H1.
      rewrite H1.
      done.
    }
    assert (eval_kind se κser = Some (SMEMTYPE sz ξser)). {
      by apply eval_kind_senv_empty_le.
    }

    (* random thing for flags *)
    assert (length (flat_map arep_flags ιs) = sz). {
      rewrite length_flat_map.
      assert (∀ ι, length (arep_flags ι) = arep_size ι). {
        intros ι; destruct ι; cbn; done.
      }
      setoid_rewrite H6.
      rewrite <- sum_list_with_list_sum.
      done.
    }

    (* I need type_skind se τval *)
    assert (Hevalρse: eval_rep se ρ = Some ιs). {
      by apply eval_rep_emptyenv.
    }
    assert (eval_kind se (VALTYPE ρ ξser) = Some (SVALTYPE ιs ξser)). {
      unfold eval_kind.
      rewrite Hevalρse.
      cbn.
      done.
    }
    assert (type_skind se τval = Some (SVALTYPE ιs ξser)). {
      eapply type_skind_has_kind_Some; try done.
    }

    assert (type_skind se (SerT κser τval) = Some (SMEMTYPE sz ξser)). {
      eapply type_skind_has_kind_Some; try done.
    }

    (* always do all the way at the end. Ideally, should always be basically
     just eexists -> done. *)
    rewrite Hprtarget.
    do 5 eexists.
    done.
  Qed.

  Lemma compat_swap M F L wt wt' wtf wl wl' wlf es' κ κser μ τ τval π pr :
     let fe := fe_of_context F in
     let WT := wt ++ wt' ++ wtf in
     let WL := wl ++ wl' ++ wlf in
     let lmask := wlmask fe wl in
     let ψ := InstrT [RefT κ μ Mut τ; τval] [RefT κ μ Mut τ; τval] in
     resolves_path τ π None pr ->
     Forall (has_mono_size F) (pr_prefix pr) ->
     pr.(pr_target) = SerT κser τval ->
     has_instruction_type_ok F ψ L ->
     run_codegen (compile_instr mr fe (ISwap ψ π)) wt wl = inr ((), wt', wl', es') ->
     ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmask ψ Hresolves Hmonosize Hser Htype Hcompile. unfold WT, WL; clear WT WL.
    (* If the WT := or WL := become necessary, undo the unfold/clear*)
    cbn in Hcompile.

    (* Mechanically get through some of the first few things in compile_swap *)
    inv_cg_bind Hcompile ρ ?wt ?wt ?wl ?wl es_off ?es_rest Hρ Hcompile.
    inv_cg_bind Hcompile ιs ?wt ?wt ?wl ?wl es_ρ ?es_rest Hιs Hcompile.
    inv_cg_bind Hcompile off ?wt ?wt ?wl ?wl  es_fail ?es_rest Hoff Hcompile.
    inv_cg_try_option Hρ; rename Heq_some into Hρ.
    inv_cg_try_option Hιs; rename Heq_some into Hιs.
    inv_cg_try_option Hoff; rename Heq_some into Hoff.
    inv_cg_bind Hcompile val_localidxs ?wt ?wt wl_save ?wl  es_save ?es_rest Hsave Hcompile.
    inv_cg_bind Hcompile a ?wt ?wt ?wl ?wl  es_a ?es_rest Ha Hcompile.
    cbn in Ha; inversion Ha; subst; clear Ha.
    inv_cg_bind Hcompile res_emit ?wt ?wt ?wl ?wl  es_emit ?es_rest Hemit Hcompile.
    inv_cg_emit Hemit.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_case_ptr es_ptr_flags Hcompile Hignore.
    cbn in Hignore; inversion Hignore; subst; clear Hignore.

    (* Some clean up *)
    clear_nils.
    destruct u. destruct p; destruct u; destruct u0.

    (** OUTERMOST DIGGING **)
    unfold have_instr_type_sem.
    iIntros (??????????) "@@@@@@@@@@".

    (* we have two things on the stack: a reference and a τval *)
    (* separate the value interp *)
    iPoseProof (values_interp_cons_l with "[$Hos]") as "(%os1 & %os2 & -> & Hos1 & Hos2)".
    iEval (rewrite values_interp_one_eq; cbn) in "Hos2".
    iPoseProof (atoms_interp_app_l with "[$Hvs]") as "(%vs1 & %vs2 & -> & Hvs1 & Hvs2)".
    iPoseProof (value_interp_ref_sz with "[$Hos1]") as "%Hos1len".
    destruct os1; [inversion Hos1len | destruct os1; [| inversion Hos1len]].
    rename a into o1.
    iEval (rewrite atoms_interp_one_inv) in "Hvs1".
    iDestruct "Hvs1" as "(%v1 & -> & Hv1)".
    clear Hos1len.
    rewrite value_interp_eq.
    iDestruct "Hos1" as (sκ Hsκ) "[%skindsv Ho1]".

    (* Summary:
       - o1 is the atom associated with the ref, and v1 is its associated value
       - os2 are the atoms associated with τval, and vs2 are its values
       Note: o1 is Ptr _, but it's easier to get that after splitting between MM
       and GC.
     *)

    (* Set any other useful keys here? *)
    set (ptr_local := sum_list_with length F.(typing.fc_locals) + length (wl ++ wl_save) ) in *.



    (** KINDING STUFF *)

    pose proof (Hsκ) as Hevalκ.
    cbn in Hevalκ.
    (* this lemma is a quarantine zone for all things kinding
       if we need more info in the future it can be added. Also potentially
       eventually make _MM and _GC versions that use eval_mem, if necessary
     *)
    pose proof
      (get_all_kinding_info_swap
         τ κ μ τval π pr Hresolves
         F off ρ se sκ κser L ιs o1
         H Hoff Hmonosize Hsκ Hevalκ Hser Htype Hρ Hιs skindsv
      ) as AllKinding.
    destruct AllKinding as
      (σ & ξ & ξser & sz & ξ_ref &
         Hkind_τ & Hkind_prtarget & Hkind_τval & Hevalsize & -> & -> &
          Hιssz & Hevalκser & Hflaglengths & Htypeskindτval & Htypeskindsert).


    (** OTHER GENERAL FACTS THAT WE NEED FOR BOTH CASES **)
    (* NOTE: highly recommend folding as much of this section as possible *)

    (* for saving the stack, frame interp thingy*)
    iPoseProof (frame_interp_wl_interp with "Hframe") as "%Hwl".

    (* this section establishes a bound on ptr_local which is necessary everywhere *)
    set (locsz :=
               length (concat (typing.fc_locals F)) +
               length (wl ++ wl_save) +
               length (T_i32 :: wl2 ++ wlf)).
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
    assert (ptr_local < length (f_locs fr)) as Hptrlocalfr. {
      rewrite Hflen.
      unfold locsz, ptr_local.
      rewrite sum_list_with_list_sum length_concat.
      cbn; lia.
    }



    (** BEGIN THE SPLIT **)

    (* This is where it's best to show o1 is ptr and v1 a ptr shaped number,
       so the first bit of both sections is dedicated to that.
       this bit first for that `last done` in the splitting line.
     *)
    iEval (cbn) in "Ho1".

    destruct (eval_mem se μ) eqn:evalμ; last done; destruct b.
    1: refine ?[MemMM]. 2: refine ?[MemGC].


    [MemMM]: {
      iEval (cbn) in "Ho1".
      iDestruct "Ho1" as "(%ℓ & %fs & %ws & %toinvert & Hℓ_layout & Hℓ_heap & Hτ)".
      inversion toinvert; subst o1; clear toinvert.
      iPoseProof (atom_interp_ptr_shaped with "Hv1") as
        "(%n & %n32 & %Hn32 & -> & %Hnshp & %rp & %Hreproot & Hv1)".
      apply has_values_app_inv in H0.
      destruct H0 as (ev1 & evs2 & -> & Hev1 & Hevs2).
      apply has_values_to_consts_inv in Hev1 as Hev1tosubst.
      cbn in Hev1tosubst. subst ev1.
      (* right here: need to dig into root pointer a lot *)
      (* Our facts:
         - ptr_shaped (PtrHeap MemMM ℓ) n
         X repr_root_pointer rp n DONE: GOT a AND MOD STUFF OUT OF THIS
         X root_pointer_interp rp (PtrHeapMemMM ℓ) DONE: GOT ->ADDR OUT OF THIS
       *)
      destruct rp; iEval (cbn) in "Hv1"; try done.
      destruct μ0; iEval (cbn) in "Hv1"; try done.
      (* okay now to connect a and n *)
      inversion Hreproot. subst μ0 a0.
      rename H2 into Hamod3; rename H4 into Hanot0; rename H3 into Han.
      pose proof Han as Htagaddress.
      cbn in Han.
      assert (Hna: (n+3)%N=a).
      { assert (4 <= a)%N by (by eapply mod_bound_nonzero). lia. }
      (* okay sure lemma here to connect ↦addr to θ
       related to ghost_map_auth rw_addr (1 / 2) θ bc lookup fragment :) *)
      iAssert (⌜repr_pointer θ (PtrHeap MemMM ℓ) n⌝%I) with "[Hrt Hv1]" as "%Hrepr". {
        (* we need θ !! l = Some (MemMM, a) *)
        unfold rt_token.
        iDestruct "Hrt" as "(%rm & %lm & %hm & Haddr & _)".
        iPoseProof (ghost_map_lookup with "[$] [$]") as "%Hθℓ".
        iPureIntro.
        rewrite <- Htagaddress.
        by constructor.
      }

      (* another improtant thing soon is that lpall ℓ is true *)
      assert (Hlmask: lpall ℓ) by done.

      (* we need that the original fs and ws satisfy layoutok *)
      iAssert (⌜Forall2 word_has_flag fs ws⌝%I) with "[Hℓ_layout Hℓ_heap Hrt]" as "%Hfswsmatch". {
        open_rt "Hrt".
        iPoseProof (ghost_map_lookup with "[$Hlayout] [$Hℓ_layout]") as "%Hθlayout".
        iPoseProof (ghost_map_lookup with "[$Hheap] [$Hℓ_heap]") as "%Hθheap".
        iPureIntro.
        unfold layout_ok in Hlayoutok.
        unfold map_Forall2 in Hlayoutok.
        specialize (Hlayoutok ℓ).
        rewrite Hθlayout in Hlayoutok; rewrite Hθheap in Hlayoutok.

        inversion Hlayoutok; subst.
        specialize (H2 ltac:(auto)).
        done.
      }

      (* some kinding facts *)
      iAssert (⌜Forall2 has_arep ιs os2 /\ has_areps ιs (SAtoms os2) /\
               Forall (forall_ptr_word (ref_flag_ptr_interp ξser))
                (concat (map serialize_atom os2))
                  ⌝%I)
         with "[Hvs2 Hos2]" as "%KindingQuarantine". {
        rewrite value_interp_eq.
        iEval (cbn -[pre_type_interp type_skind]) in "Hos2".
        iDestruct "Hos2" as "(%sκ_temp & %Htypeskindtemp & %Harepsoon & pre)".
        iPureIntro.
        rewrite Htypeskindτval in Htypeskindtemp.
        inversion Htypeskindtemp. subst sκ_temp.
        destruct Harepsoon as (Hareps & Hforallatomref).

        repeat split.
        - unfold has_areps in Hareps.
          destruct Hareps as (os & toinvert & yes).
          inversion toinvert; subst; done.
        - done.
        - by apply forall_ptr_atom_to_word_ref_flag_interp.
      }
      destruct KindingQuarantine as (Harepιsos2 & Hareps & Hrefinterp).
      assert (Hos2sz: length (concat (map serialize_atom os2)) = sz). {
        assert (length (concat (map serialize_atom os2)) = length (flat_map arep_flags ιs)). {
          rewrite flat_map_concat_map.
          apply has_arep_means_equal_lengths; done.
        }
        by etransitivity.
      }
      iDestruct (result_type_interp_of_atoms_interp with "Hvs2") as "%Hres_type_vs2"; try done.


      (* Summary:
         - o1 became (PtrHeap MemMM ℓ), v1 became (VAL_int32 n32), ev1 became BI_const...
         - n32 is... the address associated with the pointer? Or at minimum it is the
           actual thing on the stack.
         - we also dug into the value interp of the reference, getting the following:
           + we got rp, the root pointer associated with ℓ, and a bunch of ℓ resources
             and destruct rp to get mod info associated with n and n+3
           + we also importantly got the type interpretation of τ (what's currently being
             pointed to by the reference) and the words ws currently sitting there
       *)

      (** SAVING STACK AND LOCAL TEE *)
      (* First, saving stack to clear evs2 and es_save *)

      (* apply lemma on the codegen. order of goals to help with evars *)
      eapply cwp_save_stack_w in Hsave; auto.
      4: exact Hevs2.
      3: {
        unfold translate_arep in Hres_type_vs2.
        rewrite map_comp. done.
      }
      2: exact Hwl.
      destruct Hsave as (Hval_localidxs_seq & -> & Hwl_save & Hsave).

      (* now to use the facts we got *)
      rewrite (app_assoc _ es_save _).
      rewrite <- (app_assoc _ evs2 _).
      iApply (cwp_seq with "[Hfr Hrun]").
      {
        (* note: this is 100% copied from case.v lol *)
        (* it looks like this is all just related to cwp_save_stack so should be the same *)
        (* possibility of it being incorrect *)
        instantiate (1 := λ fr' vs, (
          ∃ val_idxs,
          ⌜vs = [VAL_int32 n32]⌝ ∗
          ⌜frame_rel (λ i, i ∉ val_idxs) fr fr'⌝ ∗
          ⌜Forall2 (fun i v => f_locs fr' !! localimm i = Some v) val_localidxs vs2⌝ ∗
          ⌜val_idxs = seq (fe_wlocal_offset fe + length wl) (length wl_save)⌝ ∗
          ⌜val_localidxs = map prelude.W.Mk_localidx val_idxs⌝
                                    )%I).
        iApply cwp_val_app; first done.
        iApply (Hsave with "[$] [$]").
        iIntros (f' [Hfsame Hfchanged]).
        unfold fvs_combine.
        subst val_localidxs wl_save.
        auto.
      }
      iIntros (fr_saved w) "(%val_idxs & -> & %Hfrel_fr_saved & %Hsaved & %Hval_idxs_seq & %Hval_localidxs) Hfr Hrun".
      clear Hsave.

      iPoseProof (frame_interp_update_frame' with "Hframe") as "Hframe_saved".
      2, 3, 5: done.
      { subst val_idxs fe. by rewrite fe_wlocal_offset_length. }
      { subst wl_save.
        by rewrite map_comp.
      }

      iDestruct (frame_interp_wl_interp with "Hframe_saved") as "%Hwl_saved".
      pose proof (interp_wl_length _ _ _ Hwl_saved) as Hfr_saved_locs_len.

      (* Reestablish ptr_local length *)
      assert (Hptrlocalfrsaved: ptr_local < length (f_locs fr_saved)). {
        (* If this isn't true this is weird, but seems hardish to prove *)
        subst ptr_local.
        simpl.
        eapply Nat.lt_le_trans; last done.
        - rewrite app_assoc.
          subst fe.
          repeat rewrite length_app.
          unfold fe_wlocal_offset.
          lias.
      }

      (* Next: local_tee stuff *)
      set (fr' := ({|
                     W.f_locs :=
                       <[localimm (prelude.W.Mk_localidx ptr_local):=
                           VAL_int32 n32]> (f_locs fr_saved);
                     W.f_inst := f_inst fr_saved
                   |})) in *.
      rewrite (app_assoc (to_consts [VAL_int32 n32]) _ _).
      iApply (cwp_seq with "[Hfr Hrun]").
      {
        (* this is copied from load.v *)
        iApply (cwp_local_tee with "[] [$] [$]").
        - done.
        - now instantiate (1:= λ f'' v'', ⌜f'' = fr' /\ v'' = [VAL_int32 n32]⌝%I).
      }
      iIntros (? ?) "(-> & ->) Hf Hrun".

      (* do some frame interp updating *)
      iEval (rewrite app_assoc) in "Hframe_saved".
      iPoseProof (frame_interp_update_frame' with "Hframe_saved") as "Hframe".
      5: {
        instantiate (1 := fr').
        instantiate (1 := [ptr_local]).
        unfold fr'.
        unfold frame_rel.
        cbn; split; [|done].
        unfold mask_locs_eq. cbn.
        intros i Hipls.
        symmetry.
        apply list_lookup_insert_ne.
        intros ->; apply Hipls; left.
      }
      all: try done.
      2: {
        simpl.
        instantiate (1 := [_]).
        apply Forall2_cons.
        split; [|done].
        cbn.
        by apply list_lookup_insert_eq.
      }
      2: {
        apply Forall2_cons; split; last done.
        by eexists.
      }
      {
        subst ptr_local fe.
        cbn.
        rewrite sum_list_with_length_concat.
        done.
      }

      (* Summary:
         - Used up evs2 and es_save_stack and "put" the pointer in front of es_case_ptr block
         - Our frame changed twice: fr_saved is after saving the stack (so lots of things)
           got put into locals, and fr' is after putting n32 into the local associated
           with the ptr.
         - We also got a bunch of val_indx stuffs everywhere
         - Also update frame_interp resources here

         Note: probably put lemmas and facts related to saving the stack here. Try to make
         them lemmas, since the GC case also needs them.
      *)

      (** ----------------- STORE TIME -------------------- **)
      (* Apply the case ptr lemma onto the codegen *)
      apply cwp_case_ptr in Hcompile.
      destruct Hcompile as
        (wt_unreach & wt_memMM & wt_memGC &
           wl_unreach & wl_memMM & wl_memGC &
           es_unreach & es_memMM & es_memGC & Hcompile).
      destruct Hcompile as
        (Hcg_unreach & Hcg_memMM & Hcg_memGC & -> & -> & Hcaseptr_spec).


      (* Specialize the spec with out variables *)
      specialize (Hcaseptr_spec [] []).
      specialize (Hcaseptr_spec (PtrHeap MemMM ℓ) n n32).
      specialize (Hcaseptr_spec ltac:(eauto) ltac:(auto) ltac:(auto) ltac:(auto)).
      clear_nils.

      inv_cg_bind Hcg_memMM what ?wt ?wt ?wl ?wl
        es_root_to_heap es_loadstore Hcg_root Hcg_store.
      destruct what.
      cbn in Hcg_root.
      inversion Hcg_root. subst wt0 wl0 es_root_to_heap; clear_nils; clear Hcg_root.
      subst wt1 wl1.
      inv_cg_bind Hcg_store what ?wt ?wt ?wl ?wl es_load es_store Hcg_load Hcg_store.

      (* HERE ARE THE THREE SPECS WE HAVE: PATH AND STORE AND LOAD *)
      pose proof
        (resolves_path_inv_sep_weak rti sr se
           τ π pr Hresolves F off ρ σ ξ ξser sz) as Hpath_spec.
      specialize (Hpath_spec H Hoff Hmonosize Hkind_τ Hkind_prtarget Hevalsize).

      assert (Hstupidlen: length val_localidxs = length ιs). {
        move Hres_type_vs2 at bottom.
        move Hsaved at bottom.
        apply Forall2_length in Hsaved.
        unfold result_type_interp in Hres_type_vs2.
        apply Forall2_length in Hres_type_vs2.
        rewrite length_map in Hres_type_vs2.
        etransitivity; done.
      }

      pose proof (wp_store_strong_mm rti sr _ _ _ _ _ _ _ _ _ _ _ Hstupidlen Hcg_store) as Hstore_spec.
      destruct Hstore_spec as (_ & -> & -> & Hstore_spec).

      pose proof (wp_mem_load_move rti sr mr se _ _ _ _ _ _ _ _ _ _ Hcg_load) as Hload_spec.
      destruct Hload_spec as (-> & -> & -> & Hload_spec).

      (* I think I can just go? *)
      iApply cwp_val_app; first done.
      unfold fvs_combine; clear_nils.

      iApply (Hcaseptr_spec with "[$] [$] [%] [-]");
        [cbn; by apply list_lookup_insert_eq|].
      iModIntro.
      iIntros "Hfr Hrun".

      iPoseProof (Hpath_spec $! ws with "[$Hτ]") as "Hpath_spec".
      iDestruct "Hpath_spec" as "(%Hwslengths & Htarget & Hcontinuation)".
      rewrite Hser. clear_nils.

      iAssert (⌜Forall2 (λ (f : pointer_flag) (w : word), word_has_flag f w)
                 (concat (map arep_flags ιs))
                 (take (sum_list_with arep_size ιs) (drop off ws))⌝%I) with "[Htarget]" as "%Hhasflags". {
        (* hm unsure how this will go *)
        rewrite Hιssz.
        unfold get_path_words.
        rewrite value_interp_eq.
        iEval (cbn -[type_skind pre_type_interp]) in "Htarget".
        iDestruct "Htarget" as "(%sκ & %Htemp & %Hyeah & Htype)".
        rewrite Htypeskindsert in Htemp.
        inversion Htemp; subst sκ.
        destruct Hyeah as (_ & Hrefflag).
        iEval (cbn) in "Htype".
        (* I'm scared *)
        iDestruct "Htype" as "(%os & %Hserialized & Htype)".
        rewrite type_interp_eq.
        iEval (cbn -[type_skind pre_type_interp]) in "Htype".
        rewrite Htypeskindτval.
        iDestruct "Htype" as "(%sκ & %toinvert & %Helpme & Htype)".
        inversion toinvert; subst sκ. clear Htemp toinvert.
        destruct Helpme as (Hosιs & Hptros).

        iPureIntro.
        inversion Hserialized.
        rewrite !H1.
        rewrite H1 in Hrefflag.

        (* dealing with Is_true and is_true lol *)
        eapply Forall2_impl.
        1: by apply has_areps_imp_word_has_flag.
        intros.
        cbn in H0.
        done.
      }
      (* we now need to dig a bit into htarget to get the os_target out of there *)
      iEval (rewrite value_interp_eq; cbn) in "Htarget".
      rewrite Hevalκser.
      iDestruct "Htarget" as "(%sκ' & %toinv & %Htargetinterp & (%os_inner & %toinv2 & Hτ_target))".
      inversion toinv2 as [Hgetpath_ws_osinner]; clear toinv2.
      inversion toinv; subst; clear toinv.
      iAssert (⌜has_areps ιs (SAtoms os_inner)⌝%I) with "[Hτ_target]" as "%Hareps_inner". {
        iApply (type_interp_implies_has_areps with "[$]"); done.
      }
      assert (Harep_inner: Forall2 has_arep ιs os_inner). {
        unfold has_areps in Hareps_inner.
        destruct Hareps_inner as (os' & toinv & thefact).
        inversion toinv; subst; done.
      }

      (* probably Now I should weaken the token *)
      set (rtmask := (λ l, l ≠ ℓ)).
      iAssert (rt_token rti sr rtmask θ) with "[Hrt]" as "Hrt". {
        by iApply rt_token_lpall.
      }

      (* small frame fact for simplicity *)
      assert (Hfinst_fr'_fr: f_inst fr' = f_inst fr). {
        unfold fr'; cbn.
        by destruct Hfrel_fr_saved as (_ & ->).
      }
      rewrite <- Hfinst_fr'_fr.

      (* --------------- LOAD ------------------ *)
      iApply (cwp_seq with "[Hown Hℓ_heap Hv1 Hfr Hrun Hrt]"). {
        specialize (Hload_spec fr' ℓ n32 a os_inner ws).
        specialize Hload_spec with (lmask:=rtmask).

        iApply (Hload_spec with "[$] [$] [$] [$] [%] [$] [$] [] [//] [//] [//] [%] [//] [%]
                                 [%] [%] [//] [//] [//] [//] [] [] [-]").
        - unfold rtmask; set_solver.
        - by iDestruct "Hinst" as "(_ & (_ & _ & _ & _ & this & _) & _)".
        - eapply ser_offsets; eauto.
        - assert (length (f_locs fr_saved) = length (f_locs fr')). {
            unfold fr'; cbn.
            symmetry.
            by apply length_insert.
          }
          rewrite <- H0.
          rewrite !length_app.
          rewrite !length_app in Hfr_saved_locs_len.
          lia.
        - unfold fr'; cbn.
          apply list_lookup_insert_eq; done.
        - cbn.
          unfold ptr_local.
          rewrite !length_app.
          cbn.
          lia.
        - by iDestruct "Hinst" as "(_ & _ & _ & _ & this & _)".
        - by iDestruct "Hinst" as "(_ & _ & _ & _ & _ & this)".
        - (* we're almost back boys *)
          iIntros (f' vs vsf ns').
          repeat iIntros "@".
          iClear "Hregf".
          (* things we need: the new f' which is mk_load_frame *)
          (* exists vs vsf ns' with all the new facts *)
          let Q := open_constr:(_ : iProp Σ) in
          instantiate (1 := λ f0 v0, (
            ∃ vs vsf ns',
              ⌜v0 = vs⌝ ∗
              ⌜ f0 = (mk_load_frame (fe_of_context F) fr'
                     (wl ++ map translate_prim (map arep_to_prim ιs) ++ [instruction.W.T_i32] ++ wl_unreach)
                     vsf) ⌝ ∗
              ⌜length ns' = areps_size ιs⌝ ∗
              ⌜ Forall2 (λ (ι : atomic_rep) (vf : value), is_true (types_agree (translate_arep ι) vf)) ιs vsf⌝ ∗
              ℓ ↦heap update_path_words off ws (map WordInt ns') ∗
              ℓ ↦addr (MemMM, a) ∗
              ([∗ list] o;v ∈ os_inner;vs, atom_interp o v) ∗
              Q
              )%I).
          iExists vs, vsf, ns'.
          iFrame.
          do 4 (iSplitR; first done).
          iAccu.
      }

      (* restoring things after load *)
      iIntros (fr_load vs_load) "Hres Hf Hrun".
      iDestruct "Hres" as "(%vs & %vsf & %ns' & %tosubst & %Hfr_load & %Hlengnsιs & %Htypesagree
                            & Hℓ_heap & Hℓ_addr & Hatom_target & Hown & Hrt)".
      (* vs_load is what we're returning on the stack *)
      (* es_store is gonna store what's in the locals *)
      (* so we must hide the vs_load consts *)
      iApply cwp_val_app; first (by apply has_values_to_consts).
      unfold fvs_combine.

      iPoseProof (atoms_interp_to_weak_memMM with "[$] [$Hvs2]") as "[Hrt Hvs2]".

      assert (Hfinst_fr'_frload: f_inst fr' = f_inst fr_load). {
        subst fr_load.
        cbn.
        rewrite load_frame_inst.
        done.
      }
      rewrite Hfinst_fr'_frload.

      (* ---------------- STORE ------------------ *)
      move Hstore_spec at bottom.
      specialize (Hstore_spec fr_load ℓ a n32 vs2 rtmask θ os2
                    (update_path_words off ws (map WordInt ns'))).

      iApply (Hstore_spec with "[$] [$] [$] [$] [%] [$] [%] [%] [//] [//] [//] [%] [//] [//]
                                [] [$]").
      - unfold rtmask; set_solver.
      - (* frame stuff ew *) admit.
      - (* need to prove val_idxs didn't change *) admit.
      - subst.
        rewrite update_path_words_size; first done.
        rewrite length_map.
        rewrite Hlengnsιs.
        unfold areps_size. cbn.
        rewrite <- sum_list_with_list_sum.
        done.
      - by iDestruct "Hinst" as "(_ & _ & _ & _ & this & _)".
      - iIntros "Hℓ_heap Hℓ_addr Hrt".
        clear_nils.
        (* alright. it's time to fight. *)
        (* 1: frame stuff. Prove fr fr_load related with lmask and prove frame_interp *)

        (* 2: rt token stuff. Prove that the flags are restored (word has flag) and restore
              lpall *)

        (* 3: restore the value/atom interp *)


      admit.
    }

    [MemGC]: {

      iEval (cbn) in "Ho1".
      iDestruct "Ho1" as "(%ℓ & %fs & %toinvert & Hτ)".
      inversion toinvert; subst o1; clear toinvert.
      iPoseProof (atom_interp_ptr_shaped with "Hv1") as
        "(%n & %n32 & %Hn32 & -> & %Hnshp & %rp & %Hreproot & Hv1)".
      apply has_values_app_inv in H0.
      destruct H0 as (ev1 & evs2 & -> & Hev1 & Hevs2).
      apply has_values_to_consts_inv in Hev1 as Hev1tosubst.
      cbn in Hev1tosubst. subst ev1.
      (* right here: need to dig into root pointer a lot *)
      (* Our facts:
         - ptr_shaped (PtrHeap MemMM ℓ) n
         X repr_root_pointer rp n DONE: GOT a AND MOD STUFF OUT OF THIS
         X root_pointer_interp rp (PtrHeapMemMM ℓ) DONE: GOT ->ADDR OUT OF THIS
       *)
      destruct rp; iEval (cbn) in "Hv1"; try done.
      destruct μ0; iEval (cbn) in "Hv1"; try done.
      (* okay now to connect a and n *)
      inversion Hreproot. subst μ0 a0.
      rename H2 into Hamod3; rename H4 into Hanot0; rename H3 into Han.
      pose proof Han as Htagaddress.
      cbn in Han.
      assert (Hna: (n+1)%N=a).
      { assert (4 <= a)%N by (by eapply mod_bound_nonzero). lia. }

      (* another improtant thing soon is that lpall ℓ is true *)
      assert (Hlmask: lpall ℓ) by done.

      (* we need that the original fs and ws satisfy layoutok *)
      (* iAssert (⌜Forall2 word_has_flag fs ws⌝%I) with "[Hℓ_layout Hℓ_heap Hrt]" as "%Hfswsmatch". { *)
      (*   open_rt "Hrt". *)
      (*   iPoseProof (ghost_map_lookup with "[$Hlayout] [$Hℓ_layout]") as "%Hθlayout". *)
      (*   iPoseProof (ghost_map_lookup with "[$Hheap] [$Hℓ_heap]") as "%Hθheap". *)
      (*   iPureIntro. *)
      (*   unfold layout_ok in Hlayoutok. *)
      (*   unfold map_Forall2 in Hlayoutok. *)
      (*   specialize (Hlayoutok ℓ). *)
      (*   rewrite Hθlayout in Hlayoutok; rewrite Hθheap in Hlayoutok. *)

      (*   inversion Hlayoutok; subst. *)
      (*   specialize (H2 ltac:(auto)). *)
      (*   done. *)
      (* } *)

      (* some kinding facts *)
      iAssert (⌜Forall2 has_arep ιs os2 /\ has_areps ιs (SAtoms os2) /\
               Forall (forall_ptr_word (ref_flag_ptr_interp ξser))
                (concat (map serialize_atom os2))
                  ⌝%I)
         with "[Hvs2 Hos2]" as "%KindingQuarantine". {
        rewrite value_interp_eq.
        iEval (cbn -[pre_type_interp type_skind]) in "Hos2".
        iDestruct "Hos2" as "(%sκ_temp & %Htypeskindtemp & %Harepsoon & pre)".
        iPureIntro.
        rewrite Htypeskindτval in Htypeskindtemp.
        inversion Htypeskindtemp. subst sκ_temp.
        destruct Harepsoon as (Hareps & Hforallatomref).

        repeat split.
        - unfold has_areps in Hareps.
          destruct Hareps as (os & toinvert & yes).
          inversion toinvert; subst; done.
        - done.
        - by apply forall_ptr_atom_to_word_ref_flag_interp.
      }
      destruct KindingQuarantine as (Harepιsos2 & Hareps & Hrefinterp).
      assert (Hos2sz: length (concat (map serialize_atom os2)) = sz). {
        assert (length (concat (map serialize_atom os2)) = length (flat_map arep_flags ιs)). {
          rewrite flat_map_concat_map.
          apply has_arep_means_equal_lengths; done.
        }
        by etransitivity.
      }
      iDestruct (result_type_interp_of_atoms_interp with "Hvs2") as "%Hres_type_vs2"; try done.


      (* Summary:
         - o1 became (PtrHeap MemMM ℓ), v1 became (VAL_int32 n32), ev1 became BI_const...
         - n32 is... the address associated with the pointer? Or at minimum it is the
           actual thing on the stack.
         - we also dug into the value interp of the reference, getting the following:
           + we got rp, the root pointer associated with ℓ, and a bunch of ℓ resources
             and destruct rp to get mod info associated with n and n+3
           + we also importantly got the type interpretation of τ (what's currently being
             pointed to by the reference) and the words ws currently sitting there
       *)

      (** SAVING STACK AND LOCAL TEE *)
      (* First, saving stack to clear evs2 and es_save *)

      (* apply lemma on the codegen. order of goals to help with evars *)
      eapply cwp_save_stack_w in Hsave; auto.
      4: exact Hevs2.
      3: {
        unfold translate_arep in Hres_type_vs2.
        rewrite map_comp. done.
      }
      2: exact Hwl.
      destruct Hsave as (Hval_localidxs_seq & -> & Hwl_save & Hsave).

      (* now to use the facts we got *)
      rewrite (app_assoc _ es_save _).
      rewrite <- (app_assoc _ evs2 _).
      iApply (cwp_seq with "[Hfr Hrun]").
      {
        (* note: this is 100% copied from case.v lol *)
        (* it looks like this is all just related to cwp_save_stack so should be the same *)
        (* possibility of it being incorrect *)
        instantiate (1 := λ fr' vs, (
          ∃ val_idxs,
          ⌜vs = [VAL_int32 n32]⌝ ∗
          ⌜frame_rel (λ i, i ∉ val_idxs) fr fr'⌝ ∗
          ⌜Forall2 (fun i v => f_locs fr' !! localimm i = Some v) val_localidxs vs2⌝ ∗
          ⌜val_idxs = seq (fe_wlocal_offset fe + length wl) (length wl_save)⌝ ∗
          ⌜val_localidxs = map prelude.W.Mk_localidx val_idxs⌝
                                    )%I).
        iApply cwp_val_app; first done.
        iApply (Hsave with "[$] [$]").
        iIntros (f' [Hfsame Hfchanged]).
        unfold fvs_combine.
        subst val_localidxs wl_save.
        auto.
      }
      iIntros (fr_saved w) "(%val_idxs & -> & %Hfrel_fr_saved & %Hsaved & %Hval_idxs_seq & %Hval_localidxs) Hfr Hrun".
      clear Hsave.

      iPoseProof (frame_interp_update_frame' with "Hframe") as "Hframe_saved".
      2, 3, 5: done.
      { subst val_idxs fe. by rewrite fe_wlocal_offset_length. }
      { subst wl_save.
        by rewrite map_comp.
      }

      iDestruct (frame_interp_wl_interp with "Hframe_saved") as "%Hwl_saved".
      pose proof (interp_wl_length _ _ _ Hwl_saved) as Hfr_saved_locs_len.

      (* Reestablish ptr_local length *)
      assert (Hptrlocalfrsaved: ptr_local < length (f_locs fr_saved)). {
        (* If this isn't true this is weird, but seems hardish to prove *)
        subst ptr_local.
        simpl.
        eapply Nat.lt_le_trans; last done.
        - rewrite app_assoc.
          subst fe.
          repeat rewrite length_app.
          unfold fe_wlocal_offset.
          lias.
      }

      (* Next: local_tee stuff *)
      set (fr' := ({|
                     W.f_locs :=
                       <[localimm (prelude.W.Mk_localidx ptr_local):=
                           VAL_int32 n32]> (f_locs fr_saved);
                     W.f_inst := f_inst fr_saved
                   |})) in *.
      rewrite (app_assoc (to_consts [VAL_int32 n32]) _ _).
      iApply (cwp_seq with "[Hfr Hrun]").
      {
        (* this is copied from load.v *)
        iApply (cwp_local_tee with "[] [$] [$]").
        - done.
        - now instantiate (1:= λ f'' v'', ⌜f'' = fr' /\ v'' = [VAL_int32 n32]⌝%I).
      }
      iIntros (? ?) "(-> & ->) Hf Hrun".

      (* do some frame interp updating *)
      iEval (rewrite app_assoc) in "Hframe_saved".
      iPoseProof (frame_interp_update_frame' with "Hframe_saved") as "Hframe".
      5: {
        instantiate (1 := fr').
        instantiate (1 := [ptr_local]).
        unfold fr'.
        unfold frame_rel.
        cbn; split; [|done].
        unfold mask_locs_eq. cbn.
        intros i Hipls.
        symmetry.
        apply list_lookup_insert_ne.
        intros ->; apply Hipls; left.
      }
      all: try done.
      2: {
        simpl.
        instantiate (1 := [_]).
        apply Forall2_cons.
        split; [|done].
        cbn.
        by apply list_lookup_insert_eq.
      }
      2: {
        apply Forall2_cons; split; last done.
        by eexists.
      }
      {
        subst ptr_local fe.
        cbn.
        rewrite sum_list_with_length_concat.
        done.
      }

      (* Summary:
         - Used up evs2 and es_save_stack and "put" the pointer in front of es_case_ptr block
         - Our frame changed twice: fr_saved is after saving the stack (so lots of things)
           got put into locals, and fr' is after putting n32 into the local associated
           with the ptr.
         - We also got a bunch of val_indx stuffs everywhere
         - Also update frame_interp resources here

         Note: probably put lemmas and facts related to saving the stack here. Try to make
         them lemmas, since the GC case also needs them.
      *)

      (** ----------------- STORE TIME -------------------- **)
      (* Apply the case ptr lemma onto the codegen *)
      apply cwp_case_ptr in Hcompile.
      destruct Hcompile as
        (wt_unreach & wt_memMM & wt_memGC &
           wl_unreach & wl_memMM & wl_memGC &
           es_unreach & es_memMM & es_memGC & Hcompile).
      destruct Hcompile as
        (Hcg_unreach & Hcg_memMM & Hcg_memGC & -> & -> & Hcaseptr_spec).


      (* Specialize the spec with out variables *)
      specialize (Hcaseptr_spec [] []).
      specialize (Hcaseptr_spec (PtrHeap MemGC ℓ) n n32).
      specialize (Hcaseptr_spec ltac:(eauto) ltac:(auto) ltac:(auto) ltac:(auto)).
      clear_nils.

      inv_cg_bind Hcg_memGC what ?wt ?wt ?wl ?wl
        es_root_to_heap es_loadstore Hcg_root Hcg_store.
      destruct what.
      inv_cg_bind Hcg_store what ?wt ?wt ?wl ?wl es_load es_store Hcg_load Hcg_store.


      (* OPEN INVARIANT HERE *)
      iDestruct "Hτ" as "#Hτ".
      iApply fupd_cwp.
      iMod (na_inv_acc with "Hτ Hown") as "U"; eauto.
      iDestruct "U" as "[ (%ws & Hℓ_layout & Hℓ_heap & Hws) [Hown Hclose]]".
      iModIntro.
      iMod "Hℓ_layout".
      iMod "Hℓ_heap".
      set (E' := (⊤ ∖ ↑ns_ref ℓ)) in *.
      assert (↑ns_fun (N.of_nat (sr_func_unregisterroot sr)) ⊆ E')
        by eauto with ndisj.
      (* this may not be the right place for E' but I can't do it inside the cwp_seq *)
      iApply (cwp_wand_strong NotStuck _ E' ⊤ with "[-]"); eauto.

      iAssert (⌜Forall2 word_has_flag fs ws⌝%I) with "[Hℓ_layout Hℓ_heap Hrt]" as "%Hfswsmatch". {
        open_rt "Hrt".
        iPoseProof (ghost_map_lookup with "[$Hlayout] [$Hℓ_layout]") as "%Hθlayout".
        iPoseProof (ghost_map_lookup with "[$Hheap] [$Hℓ_heap]") as "%Hθheap".
        iPureIntro.
        unfold layout_ok in Hlayoutok.
        unfold map_Forall2 in Hlayoutok.
        specialize (Hlayoutok ℓ).
        rewrite Hθlayout in Hlayoutok; rewrite Hθheap in Hlayoutok.

        inversion Hlayoutok; subst.
        assert (ll: lpall ℓ) by done.
        specialize (H3 ll).
        done.
      }


      (* HERE ARE THE THREE SPECS WE HAVE: PATH AND STORE AND LOAD *)
      pose proof
        (resolves_path_inv_sep_weak rti sr se
           τ π pr Hresolves F off ρ σ ξ ξser sz) as Hpath_spec.
      specialize (Hpath_spec H Hoff Hmonosize Hkind_τ Hkind_prtarget Hevalsize).

      assert (Hstupidlen: length val_localidxs = length ιs). {
        move Hres_type_vs2 at bottom.
        move Hsaved at bottom.
        apply Forall2_length in Hsaved.
        unfold result_type_interp in Hres_type_vs2.
        apply Forall2_length in Hres_type_vs2.
        rewrite length_map in Hres_type_vs2.
        etransitivity; done.
      }

      pose proof (wp_store_strong_gc rti sr _ _ _ _ _ _ _ _ _ _ _ Hstupidlen Hcg_store) as Hstore_spec.
      destruct Hstore_spec as (_ & -> & -> & Hstore_spec).

      pose proof (wp_mem_load_move_gc rti sr mr se _ _ _ _ _ _ _ _ _ _ Hcg_load) as Hload_spec.
      destruct Hload_spec as (-> & -> & -> & Hload_spec).

      pose proof (wp_root_to_heap sr _ _ _ _ _ _ _ Hcg_root) as Hrth_gc.

      (* I think I can just go? *)
      iApply cwp_val_app; first done.
      unfold fvs_combine; clear_nils.

      iApply (Hcaseptr_spec with "[$] [$] [%] [-]");
        [cbn; by apply list_lookup_insert_eq|].
      iModIntro.
      iIntros "Hfr Hrun".

      (* I think I'll now apply the root pointer spec? *)
      rename a into a_root.
      iApply (cwp_seq with "[-]").
      {

        (* Get root resources for wp_root_to_heap *)
        unfold rt_token.
        iDestruct "Hrt" as "(%rm_gc & %lm_gc & %hm_gc &
          Haddr_gc & Hroot_gc_auth & Hlayout_gc & Hheap_gc &
          Hrti_gc & %Hinj_gc &
          %Hrootok_gc & Hrootmem_gc & %Hheapok_gc & Hheapmem_gc)".
        specialize (Hrth_gc a_root n n32 ℓ θ rm_gc Hn32 Hreproot Hrootok_gc).
        (* Inner cwp_seq: split root_to_heap from memory.store *)
        (* Note: passing target and continuation to get rid of later lol *)
        iApply (Hrth_gc with "[$Hfr] [$Hrun] [] [] [$Hv1] [$Hroot_gc_auth] [$Hrootmem_gc]").
        - (* f'.f_locs !! ptr_local = Some (VAL_int32 n32) *)
          iPureIntro. cbn. apply list_lookup_insert_eq.
          assert (ptr_local ∉ val_idxs) as Hnotinval. {
            rewrite Hval_idxs_seq. intro Hin. apply elem_of_seq in Hin.
            rewrite /ptr_local length_app /fe_wlocal_offset in Hin. subst fe. simpl in Hin. lia.
          }
          rewrite <- lookup_lt_is_Some.
          rewrite <- (proj1 Hfrel_fr_saved ptr_local Hnotinval).
          rewrite lookup_lt_is_Some. exact Hptrlocalfr.
        - (* f'.f_inst = f_inst fr_saved = f_inst fr; extract GC mem idx from Hinst *)
          iDestruct "Hinst" as "(_ & _ & _ & _ & _ & %Hgcmem)".
          iPureIntro. cbn.
          rewrite <- (proj2 Hfrel_fr_saved).
          exact Hgcmem.
        - (* After root_to_heap: ptr_local holds the actual GC heap address ah32 *)
          iIntros "!>!>!>" (ah ah32) "%Hah32 %Hrepr_gc Hv1' Hroot_gc_auth' Hrootmem_gc'".
          iAssert (rt_token rti sr lpall θ) with
            "[Haddr_gc Hroot_gc_auth' Hlayout_gc Hheap_gc Hrti_gc
            Hrootmem_gc' Hheapmem_gc]" as "Hrt".
          { unfold rt_token. iExists rm_gc, lm_gc, hm_gc.
            iFrame. by iFrame (Hinj_gc Hrootok_gc Hheapok_gc).
          }

          let Q := open_constr:(_ : iProp Σ) in
          instantiate (1 := λ f'' v'', (
          ⌜v'' = []⌝ ∗
          ∃ ah ah32,
            ⌜f'' = ({|
                W.f_locs := <[localimm (Mk_localidx ptr_local):=VAL_int32 ah32]> (f_locs fr');
                W.f_inst := f_inst fr'
            |})⌝ ∗
            ⌜N_i32_repr ah ah32⌝ ∗
            ⌜repr_pointer θ (PtrHeap MemGC ℓ) ah⌝ ∗
            a_root ↦root ℓ ∗
            Q)%I).
          iSplit; first done.
          iExists ah, ah32.
          iSplit; first done.
          iFrame.
          iSplit; first done; iSplit; first done.
          iAccu.
      }
      iIntros (f'' v'') "(-> & %ah & %ah32 & %Hf'' & %Hah32 & rest) Hfr Hrun".
      iDestruct "rest" as "(%Hrepr_gc & Haroot & Hval_os2 & Hoa_os2 & Hframe & Hℓ_fs & Hℓ_ws & rest)".
      iRename "Hτ" into "Hτ_inv".
      iDestruct "rest" as "(Hτ & Hown & Hclose & Hrt)".

      (* now we have the laters cleared out for path spec :) *)
      iPoseProof (Hpath_spec $! ws with "[$Hτ]") as "Hpath_spec".
      iDestruct "Hpath_spec" as "(%Hwslengths & Htarget & Hcontinuation)".
      clear_nils.

      iAssert (⌜Forall2 (λ (f : pointer_flag) (w : word), word_has_flag f w)
                 (concat (map arep_flags ιs))
                 (take (sum_list_with arep_size ιs) (drop off ws))⌝%I)
        with "[Htarget]" as "%Hhasflags". {
        (* hm unsure how this will go *)
        rewrite Hιssz.
        unfold get_path_words.
        rewrite value_interp_eq.
        iEval (cbn -[type_skind pre_type_interp]) in "Htarget".
        iDestruct "Htarget" as "(%sκ & %Htemp & %Hyeah & Htype)".
        rewrite Hser in Htemp.
        rewrite Htypeskindsert in Htemp.
        inversion Htemp; subst sκ.
        destruct Hyeah as (_ & Hrefflag).
        iEval (cbn) in "Htype".
        (* I'm scared *)
        rewrite Hser.
        iDestruct "Htype" as "(%os & %Hserialized & Htype)".
        rewrite type_interp_eq.
        iEval (cbn -[type_skind pre_type_interp]) in "Htype".
        rewrite Htypeskindτval.
        iDestruct "Htype" as "(%sκ & %toinvert & %Helpme & Htype)".
        inversion toinvert; subst sκ. clear Htemp toinvert.
        destruct Helpme as (Hosιs & Hptros).

        iPureIntro.
        inversion Hserialized.
        rewrite !H2.
        rewrite H2 in Hrefflag.

        (* dealing with Is_true and is_true lol *)
        eapply Forall2_impl.
        1: by apply has_areps_imp_word_has_flag.
        intros.
        cbn in H0.
        done.
      }
      (* we now need to dig a bit into htarget to get the os_target out of there *)
      rewrite !Hser.
      iEval (rewrite value_interp_eq; cbn) in "Htarget".
      rewrite Hevalκser.
      iDestruct "Htarget" as "(%sκ' & %toinv & %Htargetinterp & (%os_inner & %toinv2 & Hτ_target))".
      inversion toinv2 as [Hgetpath_ws_osinner]; clear toinv2.
      inversion toinv; subst sκ'; clear toinv.
      iAssert (⌜has_areps ιs (SAtoms os_inner)⌝%I) with "[Hτ_target]" as "%Hareps_inner". {
        iApply (type_interp_implies_has_areps with "[$]"); done.
      }
      assert (Harep_inner: Forall2 has_arep ιs os_inner). {
        unfold has_areps in Hareps_inner.
        destruct Hareps_inner as (os' & toinv & thefact).
        inversion toinv; subst; done.
      }

      (* I think it's time to continue. Hopefully. *)

      (* probably Now I should weaken the token *)
      set (rtmask := (λ l, l ≠ ℓ)).
      iAssert (rt_token rti sr rtmask θ) with "[Hrt]" as "Hrt". {
        by iApply rt_token_lpall.
      }

      (* small frame fact for simplicity *)
      assert (Hfinst_f''_fr: f_inst f'' = f_inst fr). {
        rewrite Hf''; cbn.
        by destruct Hfrel_fr_saved as (_ & ->).
      }
      rewrite <- Hfinst_f''_fr.

      inversion Hrepr_gc.
      subst μ0 θ0 ℓ0.
      subst ah.

      (* --------------- LOAD ------------------ *)
      iApply (cwp_seq with "[Hown Hℓ_ws Hτ_target Hfr Hrun Hrt]"). {
        specialize (Hload_spec f'' ℓ ah32 a os_inner ws).
        specialize Hload_spec with (lmask:=rtmask).



        iApply (Hload_spec with "[$] [$] [$] [//] [%] [$] [$] [] [%] [%] [//] [%] [//] [%]
                                 [%] [%] [//] [//] [//] [//] [] [] [-]").
        - unfold rtmask; set_solver.
        - by iDestruct "Hinst" as "(_ & (_ & _ & _ & _ & this & _) & _)".
        - by eauto with ndisj.
        - subst sz; done.
        - eapply ser_offsets; eauto.
        - assert (length (f_locs fr_saved) = length (f_locs f'')). {
            rewrite Hf''; cbn.
            symmetry.
            rewrite length_insert.
            by apply length_insert.
          }
          rewrite <- H1.
          rewrite !length_app.
          rewrite !length_app in Hfr_saved_locs_len.
          lia.
        - rewrite Hf''; cbn.
          apply list_lookup_insert_eq.
          rewrite length_insert. done.
        - cbn.
          unfold ptr_local.
          rewrite !length_app.
          cbn.
          lia.
        - by iDestruct "Hinst" as "(_ & _ & _ & _ & this & _)".
        - by iDestruct "Hinst" as "(_ & _ & _ & _ & _ & this)".
        - (* we're almost back boys *)
          iIntros (f' vs vsf ns').
          repeat iIntros "@".
          iClear "Hregf".
          (* things we need: the new f' which is mk_load_frame *)
          (* exists vs vsf ns' with all the new facts *)
          let Q := open_constr:(_ : iProp Σ) in
          instantiate (1 := λ f0 v0, (
            ∃ vs vsf ns',
              ⌜v0 = vs⌝ ∗
              ⌜ f0 = (mk_load_frame (fe_of_context F) f''
                        (wl ++ wl_save ++ [instruction.W.T_i32] ++ wl_unreach ++ wl_memMM ++ wl0) vsf) ⌝ ∗
              ⌜length ns' = areps_size ιs⌝ ∗
              ⌜ Forall2 (λ (ι : atomic_rep) (vf : value), is_true (types_agree (translate_arep ι) vf)) ιs vsf⌝ ∗
              ℓ ↦heap update_path_words off ws (map WordInt ns') ∗
              ([∗ list] o;v ∈ os_inner;vs, atom_interp o v) ∗
              Q
              )%I).
          iExists vs, vsf, ns'.
          iFrame.
          do 4 (iSplitR; first done).
          iAccu.
      }

      (* restoring things after load *)
      iIntros (fr_load vs_load) "Hres Hf Hrun".
      iDestruct "Hres" as "(%vs & %vsf & %ns' & %tosubst & %Hfr_load & %Hlengnsιs & %Htypesagree
                            & Hℓ_heap & Hatom_target & Hτval_OLD & Hown & Hrt)".
      subst vs.
      (* vs_load is what we're returning on the stack *)
      (* es_store is gonna store what's in the locals *)
      (* so we must hide the vs_load consts *)
      iApply cwp_val_app; first (by apply has_values_to_consts).
      unfold fvs_combine.

      (* iPoseProof (atoms_interp_to_weak_memMM with "[$] [$Hvs2]") as "[Hrt Hvs2]". *)

      assert (Hfinst_fr'_frload: f_inst f'' = f_inst fr_load). {
        subst fr_load.
        rewrite Hf''.
        cbn.
        rewrite load_frame_inst.
        done.
      }
      rewrite !Hfinst_fr'_frload.

      (* ---------------- STORE ------------------ *)
      move Hstore_spec at bottom.
      specialize (Hstore_spec fr_load ℓ a ah32 vs2 rtmask θ os2
                    (update_path_words off ws (map WordInt ns'))).
      subst sz.
      iApply (Hstore_spec with "[$] [$] [$] [//] [%] [$] [] [$] [%] [%] [%] [//] [//] [//] [%] [//]
                                [] [] [] [] [$]"); try done.
      - unfold rtmask; set_solver.
      - by iDestruct "Hinst" as "(_ & (_ & _ & _ & _ & _ & this) & _)".
      - subst fr_load.
      (* frame stuff ew *)
        admit.
      - (* need to prove val_idxs didn't change *) admit.
      - subst.
        rewrite update_path_words_size; first done.
        rewrite length_map.
        rewrite Hlengnsιs.
        unfold areps_size. cbn.
        rewrite <- sum_list_with_list_sum.
        done.
      - by iDestruct "Hinst" as "(_ & _ & _ & _ & this & _)".
      - by iDestruct "Hinst" as "(_ & _ & _ & _ & _ & that)".
      - iIntros "Hℓ_heap Hown Hunreg Hrt".
        clear_nils.
        (* alright. it's time to fight. *)
        (* 1: frame stuff. Prove fr fr_load related with lmask and prove frame_interp *)

        (* 2: rt token stuff. Prove that the flags are restored (word has flag) and restore
              lpall *)

        (* 3: restore the value/atom interp *)

        (* this has a subgoal of restoring the invariant, which will include copy pasting stuff about
                flags being equal from store weak *)

      admit.
    }

  Admitted.

End swap.
