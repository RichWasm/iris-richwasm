From mathcomp Require Import ssrbool eqtype.
Require Import RichWasm.compiler.memory.
Require Import RichWasm.util.
Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.case_ptr.
Require Import RichWasm.iris.logrel.roots.
Require Import RichWasm.iris.logrel.load_common.
Require Import RichWasm.iris.logrel.store_common.
Require Import RichWasm.iris.logrel.path.
Require Import RichWasm.iris.logrel.rt_token.
Require Import RichWasm.iris.numerics.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section store_weak.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.





  (* this is a "get me all the kind info please" lemma
     a bit old bc it has some things it doesn't strickly need, but that's
     okay.
   *)
  Lemma get_all_kinding_info_store_weak_general τ κ μ τval π pr :
    let ψ := InstrT [RefT κ μ Mut τ; τval] [RefT κ μ Mut τ] in
    resolves_path τ π None pr ->
    ∀ F off ρ se sκ κser L ιs o1,
      sem_env_interp F se ->
      path_offset (fe_of_context F) τ π = Some off ->
      Forall (has_mono_size F) pr.(pr_prefix) ->
      type_skind (Σ:=Σ) se (RefT κ μ Mut τ) = Some sκ ->
      eval_kind se κ = Some sκ ->
      (* eval_mem se μ = Some MemMM -> *)
      has_ref_flag F (pr_target pr) GCRefs ->
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
    intros * Hse Hoffset Hmono Htypeskind Hevalκ Href Hprtarget Hok Hrep Hevalρ Hsksv.

    rewrite Hprtarget in Href.
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


  Lemma compat_store_weak M F L wt wt' wtf wl wl' wlf es' κ κser μ τ τval π pr :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [RefT κ μ Mut τ; τval] [RefT κ μ Mut τ] in
    resolves_path τ π None pr ->
    has_ref_flag F pr.(pr_target) GCRefs ->
    pr.(pr_target) = SerT κser τval ->
    Forall (has_mono_size F) (pr_prefix pr) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IStore ψ π)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmask ψ Hresolves Hdrop Hser Hmonosize Htype Hcompile.
    unfold WT, WL; clear WT WL.
    cbn in Hcompile.

    (** COMPILER DESTRUCTION **)
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
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_case_ptr es_ptr_flags Hcompile Hptr_flags.

    (* Some clean up *)
    subst.
    clear_nils.
    destruct u. destruct p; destruct u; destruct u0.

    (* Summary: (put any useful info about the variables here. probs obvious stuff)
       - wl_save is the list of locals associated with the thing we're storing into memory
     *)



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
      (get_all_kinding_info_store_weak_general
         τ κ μ τval π pr Hresolves
         F off ρ se sκ κser L ιs o1
         H Hoff Hmonosize Hsκ Hevalκ Hdrop Hser Htype Hρ Hιs skindsv
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
               length (T_i32 :: wl2 ++ wl3 ++ wlf)).
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
        eapply Forall2_impl; [exact H2|].
        intros f' w' Hwh; cbn in Hwh; apply Is_true_true; exact Hwh.
      }


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


      (** PUT FACTOIDS WE NEED HERE (THAT ARE MM/GC SPECIFIC) **)
      (* I think some of the kinding quarantine but with resources can be
         here. Not all of it because of path lemma, though. *)
      (* mini kinding quarantine right here! I should make it a lemma eventually *)
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

      (** TIME TO BOOGIE *)
      (* note: I think saving stack and local tee can happen before the split *)
      (* it's a little easier to already have v1 being an n32 though *)

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

      (* do a bit more work in Hcg_memMM *)
      (* note: I need to this now bc I get info about which wl_memMMs are empty *)
      (* which I need outside the cwp_seq *)
      inv_cg_bind Hcg_memMM what ?wt ?wt ?wl ?wl
        es_root_to_heap es_store Hcg_root Hcg_store.
      destruct what.
      cbn in Hcg_root.
      inversion Hcg_root. subst wt0 wl0 es_root_to_heap; clear_nils; clear Hcg_root.
      subst wt1 wl1.

      (* HERE ARE THE TWO SPECS WE HAVE: PATH AND STORE *)
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

      pose proof (wp_store_weak_mm rti sr _ _ _ _ _ _ _ _ _ _ _ Hstupidlen Hcg_store) as Hstore_spec.
      destruct Hstore_spec as (_ & -> & -> & Hstore_spec).

      (* A cwp_val_app, which I'm confused why it's on the stack at all but oh well *)
      iApply cwp_val_app; first done.
      unfold fvs_combine.

      iApply (cwp_seq with "[-]").
      {
        iApply (Hcaseptr_spec with "[$] [$] [] [-]");
          [iPureIntro; cbn; by apply list_lookup_insert_eq|].
        iModIntro.
        iIntros "Hfr Hrun".

        (** ACTUALLY STORING TIME **)
        (* let's start specialize the store spec *)
        specialize Hstore_spec with (f:=fr').
        specialize Hstore_spec with (a:=a%N).
        specialize Hstore_spec with (a32:=n32).
        specialize Hstore_spec with (val_vs:=vs2).
        specialize Hstore_spec with (lmask:=lpall).
        specialize Hstore_spec with (θ:=θ).
        specialize Hstore_spec with (ℓ:=ℓ).
        specialize Hstore_spec with (os:=os2).
        specialize Hstore_spec with (ws:=ws).


        (* ws is likely coming from path_spec *)
        (* I think ℓ might change? Wait I'm getting confused lol *)
        (* and os will be tied to ws *)

        (* let's try using the path spec *)
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
          apply Is_true_true.
          done.
        }

        (* we need to transform atoms_interp to weak now! *)
        iPoseProof (atoms_interp_to_weak_memMM with "[$] [$Hvs2]") as "[Hrt Hvs2]".

        (* let's try applying Hstore_spec. Oh boy oh boy. Currently fully giving atoms_interp to store *)
        iApply (Hstore_spec with "[$] [$] [$] [$] [] [$] [] [] [] [] [] [] [] [] [] [] [$Hvs2] [-]");
          clear Hstore_spec; try done.
        - iPureIntro.
          by (cbn; by apply list_lookup_insert_eq).
        - iPureIntro. (* this is by Hsaved and the fact that ptr_local is after all val_idxs *)
          cbn.
          set (val_idx_upper_bound := (fe_wlocal_offset fe + length wl) +
                                (length (map translate_prim (map arep_to_prim ιs)))).
          assert (val_idx_upper_bound < ptr_local + 1). {
            subst val_idx_upper_bound ptr_local.
            cbn.
            repeat rewrite length_app.
            assert (length wl_save = length (map translate_prim (map arep_to_prim ιs))). {
              rewrite Hwl_save; done.
            }
            rewrite H0.
            lia.
          }
          (* the reason the +1 is on the right is bc technically possible *)
          (* that everything is empty and val_localidx = [], and so then the *)
          (* the negation saturates and there's an <= *)

          eapply (forall2_lookup_same (f_locs fr_saved) _ _ _ ptr_local localimm).
          + intros j Hneq. rewrite list_lookup_insert_ne; [done | lia].
          + rewrite Hval_localidxs Hval_idxs_seq.
            eapply Forall_impl; first apply (map_seq_forall_localidx_neq (fe_wlocal_offset fe + length wl) (length wl_save)).
            intros i Hneq. unfold ptr_local. rewrite length_app. subst fe. unfold fe_wlocal_offset in Hneq. simpl in Hneq. lia.
          + exact Hsaved.
        - iPureIntro. cbn.
          rewrite Han. done.
        - iPureIntro. rewrite Hιssz. done.
        - unfold instance_interp.
          unfold base_mem_idx.
          iDestruct "Hinst" as "(_ & _ & _ & _ & %TheThing & _)".
          iPureIntro.
          cbn.
          (* fr_inst fr = fr_inst fr_saved *)
          unfold frame_rel in Hfrel_fr_saved.
          destruct Hfrel_fr_saved as (_ & <-).
          done.
        - (* we're almost back :) *)
          iIntros "Hℓ_heap Hℓ_addr Hrt".
          (* If there's anything else we need to take out, put it here! *)
          (* I need the info about off and sz we get from path lemma *)
          let Q := open_constr:(_ : iProp Σ) in
          instantiate (1 := λ f'' vs', (⌜f'' = fr' /\ vs' = []
              /\ (off + sz ≤ length ws)
                ⌝
              ∗ Q)%I).
          iEval (cbn).
          iSplitR; first done.
          (* after we play around a bit more it'll be iAccu *)
          (* we need to use the continuation NOW *)
          iSpecialize ("Hcontinuation" $! (concat (map serialize_atom os2)) Hos2sz).
          iAssert (value_interp rti sr se (SerT κser τval) (SWords (concat (map serialize_atom os2))))
            with "[Hos2]" as "Hnewsert". {
            iEval (rewrite value_interp_eq).
            iEval (cbn).
            rewrite Hevalκser.
            iExists (SMEMTYPE sz ξser).
            iSplitR; first done.
            iSplitR; first done.
            iExists os2; iFrame.
            rewrite flat_map_concat_map.
            done.
          }
          iSpecialize ("Hcontinuation" with "[$Hnewsert]").
          (* why do we have the old value_interp still... this feels deeply deeply odd odd *)
          (* I have confirmed that this is okay *)
          iAccu.
      }




      (** ----------------- POINTER FLAGS --------------------- **)
      iIntros (fr_store vs_store) "Hres Hfr Hrun".
      (* note: this is a bit annoying without iNamedAccu, but oh well *)
      iDestruct "Hres" as "((-> & -> & %Hwslength)
             & Hown & Hℓ_fs & Hframe & Holdval & Hℓ_newws & Hℓ_addr
            & Hrt & Hvalτ)".
      rename fr' into fr_store.

      clear_nils.

      (* in order to use the pointer flags spec, we need to intentionally weaken the rttoken *)
      (* in store strong, the store lemma will weak it for us *)
      set (rtmask := (λ l, l ≠ ℓ)).
      iAssert (rt_token rti sr rtmask θ) with "[Hrt]" as "Hrt". {
        by iApply rt_token_lpall.
      }

      (* apply the spec onto the codegen and slowly specialize *)
      eapply cwp_set_pointer_flags in Hptr_flags.
      destruct Hptr_flags as (_ & -> & -> & Hptr_flags_spec).
      specialize (Hptr_flags_spec fr_store n n32).
      specialize (Hptr_flags_spec rtmask).
      specialize (Hptr_flags_spec θ).
      specialize (Hptr_flags_spec MemMM ℓ).
      clear_nils.

      (* we need four pure facts before using the spec:
         - off + length ιs < Int32.mod. Maybe from Hcg_memMM's memory.store?
         - N_i32_repr n n32. We have this.
         - repr_pointer θ (ptr) n, which we got earlier
         - f_locs fr_caseptr !! .. = n32. This is then just the minimum
           requirement of relating fr_caseptr and fr'
       *)
      assert (¬ rtmask ℓ). {
        unfold rtmask.
        auto.
      }
      assert (H3: f_locs fr_store !! localimm (prelude.W.Mk_localidx ptr_local) =
                    Some (VAL_int32 n32)) by (cbn; by apply list_lookup_insert_eq).
      specialize (Hptr_flags_spec ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto)).

      (* Time for the case pointer spec! *)
      iApply (Hptr_flags_spec with "[$] [$] [] [$] [$] [$] [] [-]").
      1: done.
      1: {
        unfold instance_interp.
        unfold instance_runtime_interp.
        (* show f_inst fr_store = f_inst fr *)
        iEval (cbn).
        destruct Hfrel_fr_saved as (_ & <-).
        iDestruct "Hinst" as "(_ & (_ & _ & Yes & _) & _)".
        iFrame "#".
      }

      (* this iIntros is from the ptr flags spec *)
      iIntros "Hℓ_fs Hrt #Hnsfun Hown #Hinst_spec".
      clear_nils.

      set (new_fs := set_flags_at off (flat_map arep_flags ιs) fs) in *.
      set (new_ws := update_path_words off ws (concat (map serialize_atom os2))) in *.

      (* now, we need to restablish rttoken *)
      (* i think we need a bunch of stuff. First that original words
         and layout have correct stuff
       *)
      (* Establish that the new fs/ws satisfy heap_ok *)
      assert (Hnewfswsmatch: Forall2 word_has_flag new_fs new_ws). {
        (* break apart the flags. Length lemmas for easier lemma application *)
        assert (sz = length (flat_map arep_flags ιs)). {
          subst sz.
          done.
        }
        assert (length fs = length ws). {
          eapply Forall2_length; exact Hfswsmatch.
        }
        pose proof (Hwslength) as Hlenflags.
        rewrite H1 in Hlenflags. rewrite <- H2 in Hlenflags.
        pose proof (updating_flags off (flat_map arep_flags ιs) fs ltac:(lia))
          as (fs1 & fs_old & fs2 & -> & Hfs & Hlenoldfs & Hlenfs1).
        unfold new_fs. rewrite Hfs.

        (* same thing but for words *)
        pose proof Hwslength as Hlenwords. rewrite <- Hos2sz in Hlenwords.
        pose proof (updating_words off (concat (map serialize_atom os2)) ws ltac:(lia))
          as (ws1 & ws_old & ws2 & -> & Hws & Hlenoldws & Hlenws1).
        unfold new_ws. rewrite Hws.

        assert (length fs2 = length ws2). {
          rewrite !length_app in H2. lia.
        }

        (* break apart the old has flags *)
        pose proof (Forall2_app_inv _ fs1 _ ws1 _ ltac:(lia) Hfswsmatch) as [Hfs1ws1 Hrest].
        pose proof (Forall2_app_inv _ fs_old _ ws_old _ ltac:(lia) Hrest) as [Hold Hfs2ws2].
        apply Forall2_app; [done | apply Forall2_app; [|done]].

        (* apply lemma for new section *)
        move Harepιsos2 at bottom.
        rewrite <- flat_map_concat_map.
        rewrite flat_map_concat_map.
        apply has_areps_imp_word_has_flag in Hareps as Hnew.
        eapply Forall2_impl; [exact Hnew|].
        intros f' w' Hwh; cbn in Hwh; apply Is_true_true; exact Hwh.
      }

      open_rt "Hrt".
      iAssert (⌜lm !! ℓ = Some new_fs⌝%I) with "[Hℓ_fs Hlayout]" as "%Hlmℓ". {
        iApply (ghost_map_lookup with "[$] [$]").
      }
      iAssert (⌜hm !! ℓ = Some new_ws⌝%I) with "[Hℓ_newws Hheap]" as "%Hhmℓ". {
        iApply (ghost_map_lookup with "[$] [$]").
      }
      assert (Hnewlayout: layout_ok lpall lm hm). {
        unfold layout_ok in *.
        unfold map_Forall2 in *.
        unfold rtmask in Hlayoutok.
        intros k.
        specialize (Hlayoutok k).
        destruct (decide (k=ℓ)); subst => //=.
        - rewrite Hlmℓ; rewrite Hhmℓ.
          constructor.
          intros.
          eapply Forall2_impl; [done|].
          intros f' w' Hwh; cbn in Hwh; apply Is_true_true; exact Hwh.
        - inversion Hlayoutok.
          + specialize (H4 n0); constructor; done.
          + constructor.
      }
      clear Hlayoutok. (* don't want to accidentally use it *)

      iAssert (rt_token rti sr lpall θ) with
        "[Haddr Hroot Hlayout Hheap Hrti Hrootmem Hheapmem]" as "Hrt". {
        unfold rt_token.
        iExists rm, lm, hm.
        iFrame.
        done.
      }
      (* I don't think we wwant some of these pure things since we've closed rt_token *)
      clear dependent rm.
      clear dependent lm.
      clear dependent hm.
      clear Hinj.

      iFrame.

      (** ----- REESTABLISHING VALUE_INTERP AT THE END ------- *)

      (* frame interp and frame rel shouldn't be insane as I think *)
      (* they'll be preserved? we'll see *)
      iSplitR.
      - iPureIntro.
        unfold lmask.
        apply (frame_rel_trans lmask fr fr_saved fr_store).
        + unfold lmask.
          eapply frame_rel_mask_mono; [| exact Hfrel_fr_saved].
          intros i Hiwlmask.
          cbn.
          unfold wlmask in Hiwlmask.
          rewrite Hval_idxs_seq.
          intro Hin. apply elem_of_seq in Hin. lia.
        + unfold fr_store, lmask.
          unfold frame_rel.
          cbn.
          split; [|done].
          unfold mask_locs_eq.
          unfold wlmask.
          intros i [Hlo Hhi].
          symmetry.
          apply list_lookup_insert_ne.
          unfold ptr_local. rewrite length_app. subst fe. unfold fe_wlocal_offset in *. simpl in *. lia.
      - (* Here lies reestablishing value interp *)
        (* the resources used here is everything leftover (except old val):
           - ℓ ↦heap, ℓ ↦addr, ℓ↦layout
           - value_interp τ for new words
         *)
        iExists ([PtrA (PtrHeap MemMM ℓ)]).
        iEval (cbn).
        iSplitL "Hℓ_fs Hvalτ Hℓ_newws"; [|iSplitL; [|done]].
        + iExists [[PtrA (PtrHeap MemMM ℓ)]].
          iEval (cbn); iSplitR; [done|iSplitL;[|done]].
          rewrite type_interp_eq; iEval (cbn).
          rewrite evalμ.
          iEval (cbn).

          iExists (SVALTYPE [PtrR] ξ_ref).
          iSplitR; [done|].
          iSplitR.
          * iPureIntro.
            done. (* note: this won't be as clean in the GC case I think *)
          * iExists ℓ, _, _.
            iFrame.
            done.
        + iExists n, n32.
          iSplitR; [done| iSplitR; [done|]].
          iExists (RootHeap MemMM a).
          iSplitR; [done|].
          done.
    }










    [MemGC]: {
      (* note: this first set up has a lot of copying *)
      iEval (cbn) in "Ho1".
      iDestruct "Ho1" as "(%ℓ & %fs & %toinvert & Hτ)".
      inversion toinvert; subst o1; clear toinvert.
      iPoseProof (atom_interp_ptr_shaped with "Hv1") as
        "(%n & %n32 & %Hn32 & -> & %Hnshp & %rp & %Hreproot & Hv1)".
      apply has_values_app_inv in H0.
      destruct H0 as (ev1 & evs2 & -> & Hev1 & Hevs2).
      apply has_values_to_consts_inv in Hev1 as Hev1tosubst.
      cbn in Hev1tosubst; subst ev1.

      (* Summary:
         - o1 became (PtrHeap MemGC ℓ), v1 became (VAL_int32 n32), ev1 became BI_const...
         - n32 is... the address associated with the pointer? Or at minimum it is the
           actual thing on the stack.
         - we also dug into the value interp of the reference, getting the following:
           + we got rp, the root pointer associated with ℓ, and a bunch of ℓ resources
             hidden underneath an invariant
           + we also got the type interpretation of the words sitting in memory under an
             invariant
       *)


      (** PUT FACTOIDS WE NEED HERE (THAT ARE MM/GC SPECIFIC) **)

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


      (** TIME TO BOOGIE *)

      (** SAVING STACK AND LOCAL TEE *)
      (* First, saving stack to clear evs2 and es_save *)

      (* apply lemma on the codegen. order of goals to help with evars *)
      eapply cwp_save_stack_w in Hsave; auto.
      4: exact Hevs2.
      3: {
        unfold translate_arep in Hres_type_vs2.
        by rewrite map_comp.
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
      set (f' := ({|
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
        - cbn.
          assert (ptr_local ∉ val_idxs) as Hnotinval. {
            rewrite Hval_idxs_seq.
            intro Hin. apply elem_of_seq in Hin.
            rewrite /ptr_local length_app /fe_wlocal_offset in Hin. subst fe. simpl in Hin. lia.
          }
          rewrite <- lookup_lt_is_Some.
          rewrite <- (proj1 Hfrel_fr_saved ptr_local Hnotinval).
          rewrite lookup_lt_is_Some.
          exact Hptrlocalfr.
        - now instantiate (1:= λ f'' v'', ⌜f'' = f' /\ v'' = [VAL_int32 n32]⌝%I).
      }
      iIntros (? ?) "(-> & ->) Hf Hrun".

      (* do some frame interp updating *)
      iEval (rewrite app_assoc) in "Hframe_saved".
      iPoseProof (frame_interp_update_frame' with "Hframe_saved") as "Hframe".
      5: {
        instantiate (1 := f').
        instantiate (1 := [ptr_local]).
        unfold f'.
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
           got put into locals, and f' is after putting n32 into the local associated
           with the ptr.
         - We also got a bunch of val_indx stuffs everywhere

         Note: probably put lemmas and facts related to saving the stack here.
      *)


      (** CASE PTR TIME **)
      (* Apply the lemma into the codegen *)
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

      (* A cwp_val_app, which I'm confused why it's on the stack at all but oh well *)
      iApply cwp_val_app; first done.
      unfold fvs_combine.

      (* I think that now we need to open the Hτ invariant. Bc we need in
         cwp_store, which is inside the following cwp_seq block, and also need it
         outside of it for flags. We'll restore it after flags. *)
      (* NOTE: INVARIANT OPENED HERE *)
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
        eapply Forall2_impl; [exact H3|].
        intros f''' w' Hwh; cbn in Hwh; apply Is_true_true; exact Hwh.
      }


      pose proof
        (resolves_path_inv_sep_weak rti sr se
           τ π pr Hresolves F off ρ σ ξ ξser sz) as Hpath_spec.
      specialize (Hpath_spec H Hoff Hmonosize Hkind_τ Hkind_prtarget Hevalsize).

      iPoseProof (Hpath_spec $! ws) as "Hpath_spec".
      iPoseProof ("Hpath_spec" with "Hws") as "(Hwslengths & Htarget & Hcontinuation)".
      (* iMod "Hws1". iDestruct "Hws1" as "%Hwslengths". *)

      (* Decompose es_memGC into root_to_heap ([get_local; load; set_local]) + memory.store *)
      (* moving this here for scope reasons hopefully *)
      inv_cg_bind Hcg_memGC what_gc ?wt ?wt ?wl ?wl
        es_root_to_heap_gc es_store_gc Hcg_root_gc Hcg_store_gc.
      destruct what_gc.

      (* alright boys it's time  *)

      assert (Hstupidlen: length val_localidxs = length ιs). {
        move Hres_type_vs2 at bottom.
        move Hsaved at bottom.
        apply Forall2_length in Hsaved.
        unfold result_type_interp in Hres_type_vs2.
        apply Forall2_length in Hres_type_vs2.
        rewrite length_map in Hres_type_vs2.
        etransitivity; done.
      }

      pose proof (wp_store_weak_gc rti sr _ _ _ _ _ _ _ _ _ _ _ Hstupidlen Hcg_store_gc) as Hstore_spec.
      destruct Hstore_spec as (_ & -> & -> & Hstore_spec).

      (* Now we can cwp_seq and use the spec *)
      (* NOTE: HERE IS WHERE THE STORE SCOPE BEGINS TODO *)
      iApply (cwp_seq with "[-]").
      {
        iApply (Hcaseptr_spec with "[$] [$] [] [-]").
        { iPureIntro. cbn. apply list_lookup_insert_eq.
          assert (ptr_local ∉ val_idxs) as Hnotinval. {
            rewrite Hval_idxs_seq.
            intro Hin. apply elem_of_seq in Hin.
            rewrite /ptr_local length_app /fe_wlocal_offset in Hin. subst fe. simpl in Hin. lia.
          }
          rewrite <- lookup_lt_is_Some.
          rewrite <- (proj1 Hfrel_fr_saved ptr_local Hnotinval).
          rewrite lookup_lt_is_Some.
          exact Hptrlocalfr.
        }
        iModIntro. iIntros "Hfr Hrun".
        (* root_pointer_interp rp (PtrHeap MemGC ℓ) forces rp = RootHeap MemGC a_root *)
        destruct rp as [? | [|] a_root].
        { iEval (cbn) in "Hv1". iExFalso; iExact "Hv1". }
        { iEval (cbn) in "Hv1". iExFalso; iExact "Hv1". }
        (* Get root resources for wp_root_to_heap *)
        unfold rt_token.
        iDestruct "Hrt" as "(%rm_gc & %lm_gc & %hm_gc &
          Haddr_gc & Hroot_gc_auth & Hlayout_gc & Hheap_gc &
          Hrti_gc & %Hinj_gc &
          %Hrootok_gc & Hrootmem_gc & %Hheapok_gc & Hheapmem_gc)".
        pose proof (wp_root_to_heap sr _ _ _ _ _ _ _ Hcg_root_gc) as Hrth_gc.
        specialize (Hrth_gc a_root n n32 ℓ θ rm_gc Hn32 Hreproot Hrootok_gc).
        (* Inner cwp_seq: split root_to_heap from memory.store *)
        (* Note: passing target and continuation to get rid of later lol *)
        iApply (cwp_seq with "[Hfr Hrun Hv1 Hroot_gc_auth Hrootmem_gc Htarget Hcontinuation]").
        {
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
            let Q := open_constr:(_ : iProp Σ) in
            instantiate (1 := λ f'' v'', (
              ⌜v'' = []⌝ ∗
              ∃ ah ah32,
              ⌜f'' = ({|
                        W.f_locs := <[localimm (Mk_localidx ptr_local):=VAL_int32 ah32]> (f_locs f');
                       W.f_inst := f_inst f'
                    |})⌝ ∗
              ⌜N_i32_repr ah ah32⌝ ∗
              ⌜repr_pointer θ (PtrHeap MemGC ℓ) ah⌝ ∗
              a_root ↦root ℓ ∗
              ghost_map_auth rw_root (1/2) rm_gc ∗
              root_memory sr θ rm_gc ∗
              Q)%I).
            iSplit; first done.
            iExists ah, ah32.
            iSplit; first done.
            iFrame.
            iSplit; first done; iSplit; first done.
            iAccu.
        }
        iIntros (f'' v'')
          "(-> & %ah & %ah32 & %Hf'' & %Hah32 & %Hrepr_gc & Hv1' &
                  Hroot_gc_auth' & Hrootmem_gc' & Htarget & Hcontinuation)
           Hfr Hrun".
        iMod "Hwslengths". iDestruct "Hwslengths" as "%Hwslengths".
        (* Restore rt_token *)
        iAssert (rt_token rti sr lpall θ) with
          "[Haddr_gc Hroot_gc_auth' Hlayout_gc Hheap_gc Hrti_gc
            Hrootmem_gc' Hheapmem_gc]" as "Hrt".
        { unfold rt_token. iExists rm_gc, lm_gc, hm_gc.
          iFrame. by iFrame (Hinj_gc Hrootok_gc Hheapok_gc).
        }
        iSimpl.
        apply wp_root_to_heap_gc in Hcg_root_gc as (_ & -> & ->).

        (* If we need any other frame facts, put them here *)
        assert (Hf''2: f'' = ({|
        W.f_locs := <[localimm (Mk_localidx ptr_local):=VAL_int32 ah32]> (f_locs fr_saved);
                       W.f_inst := f_inst fr_saved
                    |})
               ). {
          rewrite Hf''.
          f_equal.
          unfold f'; cbn.
          apply list_insert_insert_eq.
        }

        (* need to reestablish frame_interp TODO *)

        (* do some frame interp updating *)
        clear_nils.
        iEval (rewrite app_assoc) in "Hframe".
        iPoseProof (frame_interp_update_frame' with "Hframe") as "Hframe".
        5: {
          instantiate (1 := f'').
          instantiate (1 := [ptr_local]).
          rewrite Hf''2.
          unfold frame_rel.
          cbn; split; [|done].
          unfold mask_locs_eq. cbn.
          intros i Hipls.
          symmetry.
          rewrite list_lookup_insert_ne.
          2: set_solver.
          rewrite list_lookup_insert_ne; first done.
          set_solver.
        }
        all: try done.
        2: {
          simpl.
          instantiate (1 := [_]).
          apply Forall2_cons.
          split; [|done].
          cbn.
          rewrite Hf''2.
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


        move Hrepr_gc at bottom.
        inversion Hrepr_gc. subst θ0 μ0 ℓ0.

        (* might be time? I think I have everything I need *)
        specialize (Hstore_spec f'' ℓ a  ah32).
        specialize (Hstore_spec vs2 lpall θ os2 ws).

        rewrite <- H6 in Hah32.

        (* hm I would *really* like Htarget to not have a later *)

        iAssert (⌜Forall2 (λ (f : pointer_flag) (w : word), word_has_flag f w)
           (concat (map arep_flags ιs))
           (take (sum_list_with arep_size ιs) (drop off ws))⌝%I) with "[Htarget]" as "%Hhasflags". {
          (* hm unsure how this will go *)

          rewrite Hιssz.
          unfold get_path_words.
          iEval (rewrite value_interp_eq) in "Htarget".
          iEval (cbn -[type_skind pre_type_interp]) in "Htarget".
          iDestruct "Htarget" as "(%sκ & %Htemp & %Hyeah & Htype)".
          rewrite Hser in Htemp.
          rewrite Htypeskindsert in Htemp.
          inversion Htemp; subst sκ.
          destruct Hyeah as (_ & Hrefflag).
          iEval (cbn) in "Htype".
          (* I'm scared *)
          rewrite !Hser.
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
          apply Is_true_true.
          done.
        }


        iApply (Hstore_spec with "[$] [$] [$] [//] [%] [$] [] [$] [//] [%]
                           [%] [//] [//] [//] [%] [%] [%] [//] [//] [] [] [$] [-]");
          try (cbn; done).
        - rewrite Hf''2; cbn.
          destruct Hfrel_fr_saved as [masklocs <-].
          iDestruct "Hinst" as "(_ & this & _)".
          iDestruct "this" as "(_ & _ & _ & _ & _ & this)".
          done.
        - rewrite Hf''2; cbn.
          apply list_lookup_insert_eq; done.
        - cbn.
          set (val_idx_upper_bound := (fe_wlocal_offset fe + length wl) +
                                (length (map translate_prim (map arep_to_prim ιs)))).
          assert (val_idx_upper_bound < ptr_local + 1). {
            subst val_idx_upper_bound ptr_local.
            cbn.
            repeat rewrite length_app.
            assert (length wl_save = length (map translate_prim (map arep_to_prim ιs))). {
              rewrite Hwl_save; done.
            }
            rewrite H1.
            lia.
          }
          (* the reason the +1 is on the right is bc technically possible *)
          (* that everything is empty and val_localidx = [], and so then the *)
          (* the negation saturates and there's an <= *)

          eapply (forall2_lookup_same (f_locs fr_saved) _ _ _ ptr_local localimm).
          + intros j Hneq.
            rewrite Hf''2; cbn.
            rewrite list_lookup_insert_ne; [done | lia].
          + rewrite Hval_localidxs Hval_idxs_seq.
            eapply Forall_impl; first apply (map_seq_forall_localidx_neq (fe_wlocal_offset fe + length wl) (length wl_save)).
            intros i Hneq. unfold ptr_local. rewrite length_app. subst fe. unfold fe_wlocal_offset in Hneq. simpl in Hneq. lia.
          + exact Hsaved.
        - subst sz. done.
        - rewrite Hf''2.
          cbn.
          destruct Hfrel_fr_saved as (locs & <-).
          iDestruct "Hinst" as "(_ & _ & _ & _ & %TheThing & _)".
          done.
        - rewrite Hf''2.
          cbn.
          destruct Hfrel_fr_saved as (locs & <-).
          unfold instance_interp.
          iDestruct "Hinst" as "(_ & _ & _ & _ & _ & %TheThing)".
          done.
        - iIntros "Hℓ_heap Hown Hunreg Hrt".
          clear Hf''.
          subst f''.
          let Q := open_constr:(_ : iProp Σ) in
          instantiate (1 := λ ff v'', (
              ⌜v'' = []⌝ ∗
              ∃ a_root ah ah32,
              ⌜ff = ({|
                  W.f_locs := <[localimm (Mk_localidx ptr_local):=VAL_int32 ah32]> (f_locs fr_saved);
                  W.f_inst := f_inst fr_saved
                    |})⌝ ∗
              ⌜N_i32_repr ah ah32⌝ ∗
              ⌜off + sz ≤ length ws⌝ ∗
              ⌜wl0 = []⌝ ∗
              ⌜repr_pointer θ (PtrHeap MemGC ℓ) ah⌝ ∗
              ⌜repr_root_pointer (RootHeap MemGC a_root) n⌝ ∗
              a_root ↦root ℓ ∗
              (instance_rt_func_interp (mr_func_unregisterroot mr) (sr_func_unregisterroot sr)
               (runtime.spec_unregisterroot rti sr)
               (f_inst
                  {|
                    W.f_locs :=
                      <[localimm (Mk_localidx ptr_local):=VAL_int32 ah32]> (f_locs fr_saved);
                    W.f_inst := f_inst fr_saved
                  |})) ∗
              (frame_interp rti sr se (typing.fc_locals F) L
               ((wl ++ wl_save) ++ [W.T_i32] ++ wl_unreach ++ wl_memMM ++ wl3 ++ wlf)
               {|
                 W.f_locs :=
                   <[localimm (Mk_localidx ptr_local):=VAL_int32 ah32]> (f_locs fr_saved);
                 W.f_inst := f_inst fr_saved
               |}) ∗
              Q)%I).
          iEval (cbn).
          iSplitR; first done.
          iExists a_root, ah, ah32.
          iSplitR; first done.
          iSplitR; first (subst ah; done).
          iSplitR; first done.
          iSplitR; first done.
          iSplitR; first done.
          iSplitR; first done.
          iFrame.
          rewrite !Hser.
          (* after we play around a bit more it'll be iAccu *)
          (* we need to use the continuation NOW *)
          iSpecialize ("Hcontinuation" $! (concat (map serialize_atom os2)) Hos2sz).
          iAssert (value_interp rti sr se (SerT κser τval) (SWords (concat (map serialize_atom os2))))
            with "[Hos2]" as "Hnewsert". {
            iEval (rewrite value_interp_eq).
            iEval (cbn).
            rewrite Hevalκser.
            iExists (SMEMTYPE sz ξser).
            iSplitR; first done.
            iSplitR; first done.
            iExists os2; iFrame.
            rewrite flat_map_concat_map.
            done.
          }
          iSpecialize ("Hcontinuation" with "[$Hnewsert]").
          (* why do we have the old value_interp still... this feels deeply deeply odd odd *)
          (* I have confirmed that this is okay *)
          clear_nils.
          iAccu.
      }
      clear_nils.
      cbn [f_inst]. (* necessary for no crash for some god forsaken reason *)
      iIntros (fr_store vs_store) "Hres Hfr Hrun".

      iDestruct "Hres" as "(-> & (%a_root & %ah & %ah32 & %Hfr_store & %Hah32 & %Hwslengths & -> &
                           %Hrepr_gc & %Hrepr_root & Hℓ_root & Hunreg & rest))".
      iDestruct "rest" as "(Hframe & Hℓ_layout & Hclose & Htarget_OLD & rest )".
      iDestruct "rest" as "(Hℓ_heap & Hown & Hrt & Hvalτ)".
      rewrite <- Hfr_store.
      (* TODO: apply pointer flags spec, reestablish frame_rel and value_interp. *)

            (* in order to use the pointer flags spec, we need to intentionally weaken the rttoken *)
      (* in store strong, the store lemma will weak it for us *)
      set (rtmask := (λ l, l ≠ ℓ)).
      iAssert (rt_token rti sr rtmask θ) with "[Hrt]" as "Hrt". {
        by iApply rt_token_lpall.
      }

      (* apply the spec onto the codegen and slowly specialize *)
      eapply cwp_set_pointer_flags in Hptr_flags.
      destruct Hptr_flags as (_ & -> & -> & Hptr_flags_spec).
      specialize (Hptr_flags_spec fr_store ah ah32).
      specialize (Hptr_flags_spec rtmask).
      specialize (Hptr_flags_spec θ).
      specialize (Hptr_flags_spec MemGC ℓ).
      clear_nils.

      (* we need four pure facts before using the spec:
         - off + length ιs < Int32.mod. Maybe from Hcg_memMM's memory.store?
         - N_i32_repr n n32. We have this.
         - repr_pointer θ (ptr) n, which we got earlier
         - f_locs fr_caseptr !! .. = n32. This is then just the minimum
           requirement of relating fr_caseptr and fr'
       *)
      assert (¬ rtmask ℓ). {
        unfold rtmask.
        auto.
      }
      assert (H3: f_locs fr_store !! localimm (prelude.W.Mk_localidx ptr_local) =
                    Some (VAL_int32 ah32)) by (subst fr_store; cbn; by apply list_lookup_insert_eq).
      specialize (Hptr_flags_spec ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto)).

      (* Time for the case pointer spec! *)
      iApply (Hptr_flags_spec with "[$] [$] [] [$] [$] [$] [] [-]").
      1: solve_ndisj.
      1: {
        unfold instance_interp.
        unfold instance_runtime_interp.
        subst fr_store.
        (* show f_inst fr_store = f_inst fr *)
        iEval (cbn).
        destruct Hfrel_fr_saved as (_ & <-).
        iDestruct "Hinst" as "(_ & (_ & _ & Yes & _) & _)".
        iFrame "#".
      }

      (* this iIntros is from the ptr flags spec *)
      iIntros "Hℓ_fs Hrt #Hnsfun Hown #Hinst_spec".
      clear_nils.

      set (new_fs := set_flags_at off (flat_map arep_flags ιs) fs) in *.
      set (new_ws := update_path_words off ws (concat (map serialize_atom os2))) in *.
      (* Establish that the new fs/ws satisfy heap_ok *)
      assert (Hnewfswsmatch: Forall2 word_has_flag new_fs new_ws). {
        (* break apart the flags. Length lemmas for easier lemma application *)
        assert (sz = length (flat_map arep_flags ιs)). {
          subst sz.
          done.
        }
        assert (length fs = length ws). {
          eapply Forall2_length; exact Hfswsmatch.
        }
        pose proof (Hwslengths) as Hlenflags.
        rewrite H2 in Hlenflags. rewrite <- H4 in Hlenflags.
        pose proof (updating_flags off (flat_map arep_flags ιs) fs ltac:(lia))
          as (fs1 & fs_old & fs2 & -> & Hfs & Hlenoldfs & Hlenfs1).
        unfold new_fs. rewrite Hfs.

        (* same thing but for words *)
        pose proof Hwslengths as Hlenwords. rewrite <- Hos2sz in Hlenwords.
        pose proof (updating_words off (concat (map serialize_atom os2)) ws ltac:(lia))
          as (ws1 & ws_old & ws2 & -> & Hws & Hlenoldws & Hlenws1).
        unfold new_ws. rewrite Hws.

        assert (length fs2 = length ws2). {
          rewrite !length_app in H4. lia.
        }

        (* break apart the old has flags *)
        pose proof (Forall2_app_inv _ fs1 _ ws1 _ ltac:(lia) Hfswsmatch) as [Hfs1ws1 Hrest].
        pose proof (Forall2_app_inv _ fs_old _ ws_old _ ltac:(lia) Hrest) as [Hold Hfs2ws2].
        apply Forall2_app; [done | apply Forall2_app; [|done]].

        (* apply lemma for new section *)
        move Harepιsos2 at bottom.
        rewrite <- flat_map_concat_map.
        rewrite flat_map_concat_map.
        apply has_areps_imp_word_has_flag in Hareps as Hnew.
        eapply Forall2_impl; [exact Hnew|].
        intros f''' w' Hwh; cbn in Hwh; apply Is_true_true; exact Hwh.
      }
      open_rt "Hrt".
      iAssert (⌜lm !! ℓ = Some new_fs⌝%I) with "[Hℓ_fs Hlayout]" as "%Hlmℓ". {
        iApply (ghost_map_lookup with "[$] [$]").
      }
      iAssert (⌜hm !! ℓ = Some new_ws⌝%I) with "[Hℓ_heap Hheap]" as "%Hhmℓ". {
        iApply (ghost_map_lookup with "[$] [$]").
      }
      assert (Hnewlayout: layout_ok lpall lm hm). {
        unfold layout_ok in *.
        unfold map_Forall2 in *.
        unfold rtmask in Hlayoutok.
        intros k.
        specialize (Hlayoutok k).
        destruct (decide (k=ℓ)); subst => //=.
        - rewrite Hlmℓ; rewrite Hhmℓ.
          constructor.
          intros.
          eapply Forall2_impl; [done|].
          intros f'' w' Hwh; cbn in Hwh; apply Is_true_true; exact Hwh.
        - inversion Hlayoutok.
          + specialize (H5 n0); constructor; done.
          + constructor.
      }
      clear Hlayoutok. (* don't want to accidentally use it *)

      iAssert (rt_token rti sr lpall θ) with
        "[Haddr Hroot Hlayout Hheap Hrti Hrootmem Hheapmem]" as "Hrt". {
        unfold rt_token.
        iExists rm, lm, hm.
        iFrame.
        done.
      }
      (* I don't think we wwant some of these pure things since we've closed rt_token *)
      clear dependent rm.
      clear dependent lm.
      clear dependent hm.
      clear Hinj.

      (* NEW: reestablish type_interp with Hclose *)
      (* and for that, we need to show that new_fs = fs *)
      iAssert (⌜fs = new_fs⌝%I) with "[Htarget_OLD]" as "<-". {
        move Hfswsmatch at bottom.
        move Hos2sz at bottom.
        move Hwslengths at bottom.
        move Hflaglengths at bottom.

        pose proof Hwslengths as HineqForNewFS.
        pose proof Hwslengths as HineqForNewWS.

        pose proof Hfswsmatch as Hfswslen.
        apply Forall2_length in Hfswslen.

        rewrite <- Hos2sz in HineqForNewWS.
        rewrite <- Hfswslen in HineqForNewFS.
        rewrite <- Hflaglengths in HineqForNewFS.

        apply updating_flags in HineqForNewFS.
        apply updating_words in HineqForNewWS.

        subst new_fs; subst new_ws.
        destruct HineqForNewFS as (fs1 & fs_old & fs2 & -> & toref & Hlenoldsf & Hlenfs1).
        destruct HineqForNewWS as (ws1 & ws_old & ws2 & -> & torew & Hlenoldsw & Hlenws1).
        rewrite toref.

        unfold get_path_words.
        iEval (rewrite <- Hlenws1) in "Htarget_OLD".
        rewrite drop_app_length.
        iEval (rewrite <- Hos2sz) in "Htarget_OLD".
        rewrite <- Hlenoldsw.
        rewrite take_app_length.


        apply (Forall2_app_inv ltac:(idtac)) in Hfswsmatch as (Hfs1ws1 & Hrest).
        2: transitivity off; done.
        apply (Forall2_app_inv ltac:(auto)) in Hrest as (Hold & Hfs2ws2).
        2: rewrite Hlenoldsf Hlenoldsw; transitivity sz; done.


        iAssert (⌜Forall2 word_has_flag (flat_map arep_flags ιs) ws_old⌝%I)
          with "[Htarget_OLD]" as "%please" . {

          rewrite !value_interp_eq.
          iEval (cbn) in "Htarget_OLD".
          rewrite Hevalκser; iEval (cbn) in "Htarget_OLD".
          iDestruct "Htarget_OLD" as "(%sκ' & %toinv & there & here)".
          inversion toinv; subst; clear toinv.
          (* has_areps_imp_word_has_flag *)
          iDestruct "here" as "(%os_inner & %toinv & Hτval)".
          inversion toinv; subst ws_old; clear toinv.

          iAssert (⌜has_areps ιs (SAtoms os_inner)⌝%I) with "[Hτval]" as "%finally". {
            iApply (type_interp_implies_has_areps with "[$Hτval]"); done.
          }
          iPureIntro.
          rewrite flat_map_concat_map.
          apply has_areps_imp_word_has_flag in finally.
          eapply Forall2_impl; first (exact finally).
          intros f''' w' Hwh; cbn in Hwh; apply Is_true_true; exact Hwh.
        }
        iPureIntro.
        apply app_inv_head_iff.
        apply app_inv_tail_iff.
        eapply Forall2_word_has_flag_inj; done.

      }
      iSpecialize ("Hclose" with "[$]").
      iMod "Hclose". iModIntro.
      (* wait it ate my value interp completely????? Huh????? *)

      (* need frame interp for iFrame *)
      iFrame.
      (* well.. let's try reestablishing stuff now then I guess *)
      iSplitR.
      - iPureIntro.
        unfold lmask.
        apply (frame_rel_trans lmask fr fr_saved fr_store).
        + unfold lmask.
          eapply frame_rel_mask_mono; [| exact Hfrel_fr_saved].
          intros i Hiwlmask.
          cbn.
          unfold wlmask in Hiwlmask.
          rewrite Hval_idxs_seq.
          intro Hin. apply elem_of_seq in Hin. lia.
        + subst fr_store.
          unfold lmask.
          unfold frame_rel.
          cbn.
          split; [|done].
          unfold mask_locs_eq.
          unfold wlmask.
          intros i [Hlo Hhi].
          symmetry.
          apply list_lookup_insert_ne.
          unfold ptr_local. rewrite length_app. subst fe. unfold fe_wlocal_offset in *. simpl in *. lia.
      - (* Here lies reestablishing value interp *)
        (* the resources used here is everything leftover (except old val):
           - ℓ ↦heap, ℓ ↦addr, ℓ↦layout
           - value_interp τ for new words
         *)
        iExists ([PtrA (PtrHeap MemGC ℓ)]).
        iEval (cbn).
        iSplitR; [|iSplitL; [|done]].
        + iExists [[PtrA (PtrHeap MemGC ℓ)]].
          iEval (cbn); iSplitR; [done|iSplitL;[|done]].
          rewrite type_interp_eq; iEval (cbn).
          rewrite evalμ.
          iEval (cbn).

          iExists (SVALTYPE [PtrR] ξ_ref).
          iSplitR; [done|].
          iSplitR.
          * iPureIntro.
            done. (* note: this won't be as clean in the GC case I think *)
          * iExists ℓ, fs.
            iFrame "#".
            done.
        + iExists n, n32.
          iSplitR; [done| iSplitR; [done|]].
          iExists _.
          iSplitR; [done|].
          iEval (cbn).
          done.
    }

  Qed.



End store_weak.
