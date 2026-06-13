Require Import RichWasm.iris.logrel.instr.typing.common.
From mathcomp Require Import ssrbool eqtype.
Require Import RichWasm.compiler.memory.
Require Import RichWasm.util.
Require Import RichWasm.iris.logrel.case_ptr.
Require Import RichWasm.iris.logrel.roots.
Require Import RichWasm.iris.logrel.load. (* TODO: remove import *)
Require Import RichWasm.iris.logrel.path.
Require Import RichWasm.iris.numerics.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section store_strong.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  (* should probably go into pathing but for now here *)
  Lemma resolves_path_implies_has_kind F τ π κser τval pr σ_rep ξ_rep ρ_τval ξ_τval :
    resolves_path τ π (Some (SerT κser τval)) pr ->
    has_kind F (pr_replaced pr) (MEMTYPE σ_rep ξ_rep) ->
    has_kind F τval (VALTYPE ρ_τval ξ_τval) ->
    has_kind F (SerT κser τval) (MEMTYPE (RepS ρ_τval) ξ_τval).
  Proof.
    intros Hresolves.
    remember (Some (SerT κser τval)).
    generalize dependent ξ_rep.
    generalize dependent σ_rep.
    induction Hresolves.
    - inversion Heqo.
    - intros.
      inversion Heqo; subst; cbn.
      intros.
      inversion H; subst.
      pose proof (has_kind_agree F _ _ _ H0 H3).
      inversion H1; subst; done.
    - intros * Hkindrep Hkindτval.
      unfold pr' in Hkindrep; cbn in Hkindrep.
      inversion Hkindrep; subst.
      apply Forall3_app_inv_l in H2.
      destruct H2 as (σs1 & σs2 & ξs1 & ξs2 & -> & -> & Hprefix & Hhottopic).
      apply Forall3_cons_inv_l in Hhottopic.
      destruct Hhottopic as (σ & σs2' & ξ & ξs2' & -> & -> & Hyay & Hrest).
      eapply IHHresolves; done.
  Qed.


  Lemma get_all_kinding_info_store_strong τ κ τval κ' π pr κser:
    let ψ := InstrT [RefT κ (BaseM MemMM) Mut τ; τval]
               [RefT κ' (BaseM MemMM) Mut (pr_replaced pr)] in
    resolves_path τ π (Some (SerT κser τval)) pr ->
    ∀ F se σ_target ρ_τval L ρ ιs off sκ,
      sem_env_interp (Σ:=Σ) F se ->
      path_offset (fe_of_context F) τ π = Some off ->
      Forall (has_mono_size F) (pr_prefix pr) ->
      type_skind se (RefT κ (BaseM MemMM) Mut τ) = Some sκ ->
      eval_kind se κ = Some sκ ->
      has_ref_flag F (pr_target pr) GCRefs ->
      has_size F (pr_target pr) σ_target ->
      has_rep F τval ρ_τval ->
      eval_size EmptyEnv σ_target = eval_rep_size EmptyEnv ρ_τval ->
      has_instruction_type_ok F ψ L ->
      type_rep (fe_type_vars (fe_of_context F)) τval = Some ρ ->
      eval_rep EmptyEnv ρ = Some ιs ->
      (∃ σ_τ ξ_τ ξ_τval σ_rep ξ_rep ξ_target sz,
          ρ = ρ_τval /\
            has_kind F τval (VALTYPE ρ_τval ξ_τval) /\
            has_kind F τ (MEMTYPE σ_τ ξ_τ) /\
            has_kind F (pr_replaced pr) (MEMTYPE σ_rep ξ_rep) /\
            has_kind F (pr_target pr) (MEMTYPE σ_target ξ_target) /\
            has_kind F (SerT κser τval) (MEMTYPE (RepS ρ_τval) ξ_τval) /\
            eval_size EmptyEnv σ_target = Some sz /\
            eval_size EmptyEnv (RepS ρ_τval) = Some sz /\
            type_skind se τval = Some (SVALTYPE ιs ξ_τval) /\
            sum_list_with arep_size ιs = sz /\
            length (flat_map arep_flags ιs) = sz /\
            κser = MEMTYPE (RepS ρ_τval) ξ_τval /\
            eval_kind se κser = Some (SMEMTYPE sz ξ_τval) /\
            κ' = (VALTYPE (AtomR PtrR) AnyRefs) /\
            eval_kind se κ' = Some (SVALTYPE [PtrR] AnyRefs) /\
            True
      ).
  Proof.
    intros ψ Hresolves.
    intros * Hse Hoffset Hmono Htypeskind Hevalκ Href Hsize Hhasrep Hevalσρ Hok Hrep Hevalρ.

    unfold ψ in Hok.
    inversion Hok; subst.
    destruct H as [Href2 Hrefreplaced].
    inversion Href2. subst.
    destruct H2 as (? & Hrep3 & Hmono2).
    inversion Hrep3; subst.
    apply has_kind_ref_ty in H.
    destruct H as (s & ?t & Hkind).

    inversion Hhasrep; subst.
    inversion Hsize; subst.
    rename ξ0 into ξ_τval.
    rename s into σ_τ.
    rename t into ξ_τ.
    rename x0 into ξ_target.

    unfold type_rep in Hrep.
    pose proof (type_kind_has_kind_is_Some _ _ _ H) as Htypekind.
    inversion Htypekind.
    pose proof (type_kind_has_kind_agree _ _ _ _ H H2) as <-.
    rewrite H2 in Hrep.
    cbn in Hrep.
    inversion Hrep; subst ρ.
    clear Hrep.

    assert (∃ ιs_τval sz, eval_rep EmptyEnv ρ_τval = Some ιs_τval /\
                      eval_rep_size EmptyEnv ρ_τval = Some sz). {
      apply Forall_cons in H3.
      destruct H3 as [Monoτval _].
      inversion Monoτval.
      destruct H3 as [Hrep2 Hmono3].
      assert (x0 = ρ_τval). {
        inversion Hrep2. subst.
        pose proof (has_kind_agree _ _ _ _ H3 H).
        inversion H4; subst; done.
      }
      subst.
      unfold is_mono_rep in Hmono3.
      apply eval_rep_empty_ok_Some in Hmono3.
      inversion Hmono3.
      rename x0 into ιs_τval.
      unfold eval_rep_size.
      rewrite H3.
      cbn.
      repeat eexists; done.
    }
    destruct H4 as (ιs_τval & sz & Hevalrep & Hevalrepsize).
    pose proof Hevalrepsize as Hevalsize.
    rewrite <- Hevalσρ in Hevalsize.

    inversion Hrefreplaced; subst. clear H7.
    destruct H6 as (? & Hrep7 & Hmono7).
    rename x0 into ρ_boring.
    inversion Hrep7; subst.
    apply has_kind_ref_ty in H4.
    destruct H4 as (σ_rep & ξ_rep & Haskindreplaced).

    assert (eval_size EmptyEnv (RepS ρ_τval) = Some sz). {
      unfold eval_size. rewrite Hevalrep.
      cbn.
      unfold eval_rep_size in Hevalrepsize.
      rewrite Hevalrep in Hevalrepsize.
      cbn in Hevalrepsize.
      inversion Hevalrepsize; subst.
      unfold areps_size.
      done.
    }



    assert (has_kind F (SerT κser τval) (MEMTYPE (RepS ρ_τval) ξ_τval)). {
      by eapply resolves_path_implies_has_kind.
    }

    assert (κser = MEMTYPE (RepS ρ_τval) ξ_τval). {
      inversion H5; subst.
      done.
    }
    subst κser.

    rewrite Hevalρ in Hevalrep.
    inversion Hevalrep; subst ιs; clear Hevalrep.
    pose proof (eval_rep_emptyenv _ _ Hevalρ se) as Hevalρse.

    assert (type_skind se τval = Some (SVALTYPE ιs_τval ξ_τval)). {
      eapply type_skind_has_kind_Some; try done.
      cbn.
      rewrite Hevalρse. cbn. done.
    }

    assert (sum_list_with arep_size ιs_τval = sz). {
      (* I think this is the right lemma at least *)
      unfold eval_size in H4.
      rewrite Hevalρ in H4.
      cbn in H4. inversion H4; subst.
      by apply sum_list_with_list_sum.
    }

    assert (length (flat_map arep_flags ιs_τval) = sz). {
      rewrite length_flat_map.
      assert (∀ ι, length (arep_flags ι) = arep_size ι). {
        intros ι; destruct ι; cbn; done.
      }
      setoid_rewrite H8.
      rewrite <- sum_list_with_list_sum.
      done.
    }

    assert (eval_kind se (MEMTYPE (RepS ρ_τval) ξ_τval) = Some (SMEMTYPE sz ξ_τval)). {
      cbn.
      rewrite Hevalρse.
      cbn.
      rewrite <- sum_list_with_list_sum.
      subst; done.
    }

    (* a bit about the resulting reference now *)
    inversion Hrep7. subst F0 τ0 ρ.
    rename ξ1 into ξ_res.
    rename ρ_boring into ρ_res.
    inversion H10. subst κ0 F0 β τ0 ρ_res ξ_res κ'.
    clear H13. clear σ ξ1.
    assert (eval_kind se (VALTYPE (AtomR PtrR) AnyRefs) = Some (SVALTYPE [PtrR] AnyRefs)). {
      cbn. done.
    }


    exists σ_τ, ξ_τ, ξ_τval, σ_rep, ξ_rep, ξ_target, sz.
    repeat split; try done.

  Qed.

  (* Note: copied from store_weak *)
  Lemma wp_store_mm_MAYBE a_idx off ιs vs_idx wt wl ret wt' wl' es :
    run_codegen (memory.store mr MemMM a_idx off vs_idx ιs) wt wl = inr (ret, wt', wl', es) ->
    ret = () /\ wt' = [] /\ wl' = [] /\ (* if I'm understanding wt' and wl' right *)
    ∀ f ℓ a a32 val_vs θ os ws E B R Φ,
    ⊢ "Hf"       ∷ ↪[frame] f -∗
      "Hrun"     ∷ ↪[RUN] -∗
      "Hptr"     ∷ ℓ ↦heap ws -∗
      "Haddr"    ∷ ℓ ↦addr (MemMM, a) -∗
      "Htok"     ∷ rt_token rti sr θ -∗
      "%Ha32"    ∷ ⌜f_locs f !! localimm a_idx = Some (VAL_int32 a32)⌝ -∗
      "%Hv"      ∷ ⌜Forall2 (λ v_idx val_v, f_locs f !! localimm v_idx = Some val_v) vs_idx val_vs⌝ -∗
      "%Hrepa"   ∷ ⌜N_i32_repr (tag_address MemMM a) a32⌝ -∗
      "%Hmod"    ∷ ⌜(a `mod` 4 = 0)%N⌝ -∗
      "%Hnz"     ∷ ⌜(a ≠ 0)%N⌝ -∗
      "%Hbound"  ∷ ⌜off + sum_list_with arep_size ιs ≤ length ws⌝ -∗
      "%Harep"   ∷ ⌜Forall2 has_arep ιs os⌝ -∗
      "%Hsliceflags" ∷ ⌜Forall2 word_has_flag (concat (map arep_flags ιs))
                                              (take (sum_list_with arep_size ιs) (drop off ws))⌝ -∗
      "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemMM)⌝ -∗
      "%Hmemmm"  ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
      "Hat"      ∷ ([∗ list] o;val_v ∈ os;val_vs, atom_interp_weak θ MemMM o val_v) -∗
      "HΦ"       ∷ (ℓ ↦heap (update_path_words off ws (concat (map serialize_atom os))) -∗
                    ℓ ↦addr (MemMM, a) -∗
                    rt_token rti sr θ -∗
                    Φ f []) -∗
    CWP es @ E UNDER B; R {{ Φ }}.
  Proof. Admitted.

  Lemma compat_store_strong M F L wt wt' wtf wl wl' wlf es' κ κ' κser σ ρ τ τval π pr :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [RefT κ (BaseM MemMM) Mut τ; τval] [RefT κ' (BaseM MemMM) Mut (pr_replaced pr)] in
    resolves_path τ π (Some (SerT κser τval)) pr ->
    has_ref_flag F pr.(pr_target) GCRefs ->
    has_size F pr.(pr_target) σ ->
    has_rep F τval ρ ->
    eval_size EmptyEnv σ = eval_rep_size EmptyEnv ρ ->
    Forall (has_mono_size F) (pr_prefix pr) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IStore ψ π)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmask ψ Hresolves Hasflag Hsize Hrep Hevalσρ Hmonosize Htype Hcompile.
    unfold WT, WL; clear WT WL.
    cbn in Hcompile.
    rename ρ into ρ_τval.
    rename σ into σ_target.

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
    iDestruct "Hos1" as (sκ_ref Hsκ_ref) "[%skindsv Ho1]".

    (* Summary:
       - o1 is the atom associated with the ref, and v1 is its associated value
       - os2 are the atoms associated with τval, and vs2 are its values
       Note: o1 is Ptr _, but it's easier to get that after splitting between MM
       and GC.
     *)

    (* Set any other useful keys here? *)
    set (ptr_local := sum_list_with length F.(typing.fc_locals) + length (wl ++ wl_save) ) in *.



    (** KINDING STUFF *)

    pose proof (Hsκ_ref) as Hevalκ_ref.
    cbn in Hevalκ_ref.

    (* Need to update the kinding quarantine in a bit
     *)
    pose proof
      (get_all_kinding_info_store_strong
         τ κ τval κ' π pr κser Hresolves
         F se σ_target ρ_τval L ρ ιs off sκ_ref
         H Hoff Hmonosize Hsκ_ref Hevalκ_ref Hasflag Hsize Hrep Hevalσρ Htype Hρ Hιs
      ) as AllKinding.
    destruct AllKinding as
      (σ_τ & ξ_τ & ξ_τval & σ_rep & ξ_rep & ξ_target & sz &
         -> & Hkind_τval & Hkind_τ & Hkind_rep & Hkind_target & Hkind_sert &
             Heval_σtgt & Heval_ρτval & Htypeskindτval & Hsumwith & Hlengthflags &
             -> & Hevalκser & -> & Hevalκ' & _).


    (** OTHER GENERAL FACTS THAT WE NEED **)
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
    destruct μ; iEval (cbn) in "Hv1"; try done.
    (* okay now to connect a and n *)
    inversion Hreproot. subst μ a0.
    rename H2 into Hamod3; rename H4 into Hanot0; rename H3 into Han.
    pose proof Han as Htagaddress.
    cbn in Han.
    assert (Hna: (n+3)%N=a) by admit. (* use hamod3 and hanot0 *)
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

    (* I'm renaming a few things bc it's confusing *)
    rename os2 into os_τval.
    rename vs2 into vs_τval.
    rename ιs into ιs_τval.



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


    (** RESOURCE KINDING QUARANTINE **)
    iAssert (⌜Forall2 has_arep ιs_τval os_τval /\ has_areps ιs_τval (SAtoms os_τval) /\
               Forall (forall_ptr_word (ref_flag_ptr_interp ξ_τval))
                 (concat (map serialize_atom os_τval))
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
    assert (Hos2sz: length (concat (map serialize_atom os_τval)) = sz). {
      assert (length (concat (map serialize_atom os_τval)) = length (flat_map arep_flags ιs_τval)). {
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
      rewrite map_comp; done.
    }
    2: exact Hwl.
    destruct Hsave as (Hval_localidxs_seq & -> & Hwl_save & Hsave).

    (* now to use the facts we got *)
    rewrite (app_assoc _ es_save _).
    rewrite <- (app_assoc _ evs2 _).
    iApply (cwp_seq with "[Hfr Hrun]"). (* saving stack *)
    {
      (* note: this is 100% copied from case.v lol *)
      (* it looks like this is all just related to cwp_save_stack so should be the same *)
      (* possibility of it being incorrect *)
      instantiate (1 := λ fr' vs, (
          ∃ val_idxs,
               ⌜vs = [VAL_int32 n32]⌝ ∗
               ⌜frame_rel (λ i, i ∉ val_idxs) fr fr'⌝ ∗
               ⌜Forall2 (fun i v => f_locs fr' !! localimm i = Some v) val_localidxs vs_τval⌝ ∗
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
      (* I'm going to cry this is obvious by Hipls *)
      admit.
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
    (* NOTE: RIGHT HERE IS THE BIGGEST DIFFERENCE BETWEEN WEAK AND STRONG *)
    (* THIS IS ALSO USING AN UNPROVED PATH LEMMA *)
    pose proof
      (resolves_path_inv_sep rti sr se
         τ π (Some (SerT (MEMTYPE (RepS ρ_τval) ξ_τval) τval)) pr
         Hresolves F off σ_target σ_τ ξ_τ σ_rep ξ_rep ξ_target (RepS ρ_τval) ξ_τval sz
         H Hoff Hmonosize Hkind_τ Hkind_rep Hkind_target Hkind_sert Heval_σtgt Heval_ρτval
      ) as Hpath_spec.

    (* NOTE: this is using a speculative spec. MIGHT CHANGE *)
    pose proof (wp_store_mm_MAYBE _ _ _ _ _ _ _ _ _ _ Hcg_store) as Hstore_spec.
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
      specialize Hstore_spec with (val_vs:=vs_τval).
      specialize Hstore_spec with (θ:=θ).
      specialize Hstore_spec with (ℓ:=ℓ).
      specialize Hstore_spec with (os:=os_τval).
      specialize Hstore_spec with (ws:=ws).


      (* ws is likely coming from path_spec *)
      (* I think ℓ might change? Wait I'm getting confused lol *)
      (* and os will be tied to ws *)

      (* let's try using the path spec *)
      iPoseProof (Hpath_spec $! ws with "[$Hτ]") as "Hpath_spec".
      iDestruct "Hpath_spec" as "(%Hwslengths & Htarget & Hcontinuation)".
      clear_nils.

      (* I have a piece of paper with some insane ramblings but here are my
           immediate next steps:
           - Using probably just Hos2 (τval val_interp) show has_arep ιs os2
           - Show the word_has_flag. This will specifically come from showing
             ιs are from the center of ws. This might be possible to do
             in kinding quarantine zone
           - Show that atoms_interp os2 vs2 -> atoms_interp_weak, and save whatever
             resources aren't necessary there
           I think this will then be enough to apply the Hstore_spec.
       *)

      (* HUGE HUGE NOTE: THIS IS NOT TRUE FOR STORE STRONG!!!!! *)
      (* IT IS TRUE FOR STORE WEAK *)
      (* CURRENTLY STORE1_MM REQUIRES THIS SORT OF CONDITION *)
      (* iAssert (⌜Forall2 (λ (f : pointer_flag) (w : word), word_has_flag f w) *)
      (*            (concat (map arep_flags ιs_τval)) *)
      (*            (take (sum_list_with arep_size ιs_τval) (drop off ws))⌝%I) with "[Htarget]" as "%Hhasflags". { *)
      (* } *)
      (* future note: show that fs = concat map arep_flags ιs? at some point *)

      (* we need to transform atoms_interp to weak now! *)
      iPoseProof (atoms_interp_to_weak_memMM with "[$] [$Hvs2]") as "[Hrt Hvs2]".

      (* let's try applying Hstore_spec. Oh boy oh boy. Currently fully giving atoms_interp to store *)
      iApply (Hstore_spec with "[$] [$] [$] [$] [$] [] [] [] [] [] [] [] [] [] [] [$Hvs2] [-]");
        clear Hstore_spec; try done.
      - iPureIntro.
        by (cbn; by apply list_lookup_insert_eq).
      - iPureIntro. (* this is by Hsaved and the fact that ptr_local is after all val_idxs *)
        cbn.
        set (val_idx_upper_bound := (fe_wlocal_offset fe + length wl) +
                                      (length (map translate_prim (map arep_to_prim ιs_τval)))).
        assert (val_idx_upper_bound < ptr_local + 1). {
          subst val_idx_upper_bound ptr_local.
          cbn.
          repeat rewrite length_app.
          assert (length wl_save = length (map translate_prim (map arep_to_prim ιs_τval))). {
            rewrite Hwl_save; done.
          }
          rewrite H0.
          lia.
        }
        (* the reason the +1 is on the right is bc technically possible *)
        (* that everything is empty and val_localidx = [], and so then the *)
        (* the negation saturates and there's an <= *)

        (* okay so if val_localidx = [] (aka vs2 = []) then everything is trivial *)
        (* if it's not, then the greatest idx is actually less than ptr_local, so then *)
        (* Hsaved can be used to show that everything stays the same *)
        (* so we're okay *)
        admit.
      - iPureIntro. cbn.
        rewrite Han. done.
      - iPureIntro.
        rewrite Hsumwith.
        done.
      - (* NOT TRUE CANNOT BE PROVEN TODO *)
        admit.
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
                                      /\ (off + sz ≤ length ws)⌝
                                          ∗ Q)%I).
        iEval (cbn).
        iSplitR; first done.
        (* after we play around a bit more it'll be iAccu *)
        (* we need to use the continuation NOW *)
        iSpecialize ("Hcontinuation" $! (concat (map serialize_atom os_τval)) Hos2sz).
        iAssert (value_interp rti sr se (SerT (MEMTYPE (RepS ρ_τval) ξ_τval) τval)
                   (SWords (concat (map serialize_atom os_τval))))
          with "[Hos2]" as "Hnewsert". {
          iEval (rewrite value_interp_eq).
          iEval (cbn).
          (* normal kinding quarantine *)
          iExists (SMEMTYPE sz ξ_τval).
          iSplitR; first done.
          iSplitR; first done.
          iExists os_τval; iFrame.
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
            & Hrt & Hval_newτ)".
    rename fr' into fr_store.

    clear_nils.

    (* apply the spec onto the codegen and slowly specialize *)
    eapply cwp_set_pointer_flags in Hptr_flags.
    destruct Hptr_flags as (_ & -> & -> & Hptr_flags_spec).
    specialize (Hptr_flags_spec fr_store n n32).
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
    assert (H3: f_locs fr_store !! localimm (prelude.W.Mk_localidx ptr_local) =
                  Some (VAL_int32 n32)) by (cbn; by apply list_lookup_insert_eq).
    specialize (Hptr_flags_spec ltac:(auto) ltac:(auto) ltac:(auto)).

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
    iFrame.

    (* since this is store weak, something that should be true:
      assert (Hfs: fs = foldr compose id
                     (map (λ '(ix, fx), <[ix:=flag_of_i32 (i32_of_flag fx)]>)
                        (zip (seq off (length (flat_map arep_flags ιs)))
                           (flat_map arep_flags ιs)))
                     fs). {
        (* this is going to be a deeply intense battle I can feel it *)
        (* okay so let's do some thinking
           - We need to show that the the section from off -> len ιs of fs is
             exactly equal to flat_map arep_flags ιs
           - which it is, bc ιs is the reps of that exact section
     *)
        (* although looking ahead we might not need this?
           If we don't that's weird af. Hm.
           It's gotta be necessary in like reestablishing invariants though
     *)
        admit.
      }
      rewrite <- Hfs.
      This will end up necessary in the gc case but is not necessary here (no invariant stuff)
     *)

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
        (* yes this is true cool *)
        (* I can't find any quick lemmas, though *)
        admit.
      + unfold fr_store, lmask.
        unfold frame_rel.
        cbn.
        split; [|done].
        unfold mask_locs_eq.
        unfold wlmask.
        (* yes htis is also true bc ptr_local is necessarily larger than the okay is *)
        admit.
    - (* Here lies reestablishing value interp *)
      (* the resources used here is everything leftover (except old val):
           - ℓ ↦heap, ℓ ↦addr, ℓ↦layout
           - value_interp τ for new words
       *)
      iExists ([PtrA (PtrHeap MemMM ℓ)]).
      iEval (cbn).
      iSplitL "Hℓ_fs Hval_newτ Hℓ_newws"; [|iSplitL; [|done]].
      + iExists [[PtrA (PtrHeap MemMM ℓ)]].
        iEval (cbn); iSplitR; [done|iSplitL;[|done]].
        rewrite type_interp_eq; iEval (cbn).
        iExists (SVALTYPE [PtrR] AnyRefs).
        iSplitR; [done|].
        iSplitR.
        * iPureIntro.
          split.
          -- unfold has_areps.
             eexists; split; [done|].
             apply Forall2_cons. done.
          -- apply Forall_cons. done.
        * iExists ℓ, _, _.
          iFrame.
          done.
      + iExists n, n32.
        iSplitR; [done| iSplitR; [done|]].
        iExists (RootHeap MemMM a).
        iSplitR; [done|].
        done.

  Admitted.

End store_strong.
