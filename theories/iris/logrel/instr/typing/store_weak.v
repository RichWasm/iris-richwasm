Require Import RichWasm.compiler.memory.
Require Import RichWasm.util.
Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.case_ptr.
Require Import RichWasm.iris.logrel.roots.
Require Import RichWasm.iris.logrel.load. (* TODO: remove import *)
Require Import RichWasm.iris.logrel.path.
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

  (* TEMPORARY. COPIED FROM LOAD_COPY *)
  Lemma sum_list_with_list_sum {A} {f : A -> nat} {xs : list A} :
    sum_list_with f xs = list_sum (map f xs).
  Proof. Admitted.

  (* TEMPORARY. This is a copy. *)
  Lemma rep_ref_kind_ptr_TEMP F κ μ β τ ρ ξ :
    has_kind F (RefT κ μ β τ) (VALTYPE ρ ξ) ->
    ρ = AtomR PtrR /\ exists ξ', κ = VALTYPE (AtomR PtrR) ξ'.
  Proof.
    intros Hkind.
    remember (RefT κ μ β τ) as ref.
    remember (VALTYPE ρ ξ) as val.
    revert Heqval Heqref.
    revert ρ ξ.
    induction Hkind using has_kind_ind'; intros; try congruence.
    - subst κ0.
      split; try congruence.
      inversion Heqref; eauto.
    - subst κ0.
      split; try congruence.
      inversion Heqref; eauto.
    - subst κ0.
      split; try congruence.
      inversion Heqref; eauto.
  Qed.

  (* TEMPORARY. COPIED FROM LOAD_COPY *)
  Lemma atom_interp_ptr_shaped ptr v :
    atom_interp (PtrA ptr) v -∗
    ∃ n n32, ⌜N_i32_repr n n32⌝ ∗
             ⌜v = VAL_int32 n32⌝ ∗
             ⌜ptr_shaped ptr n⌝ ∗
             ∃ rp, ⌜repr_root_pointer rp n⌝ ∗ root_pointer_interp rp ptr.
  Proof. Admitted.

  Lemma wp_store_w_strict μ t off wt wl wt' wl' es ret :
    run_codegen (store_w mr μ t off) wt wl = inr (ret, wt', wl', es) ->
    ret = () /\
    wt' = [] /\
    wl' = [] /\
    forall ℓ ℓ32 memidx memidxN (f: frame) B R Φ v (bs: bytes),
        N_i32_repr ℓ ℓ32 ->
        N_nat_repr memidx memidxN ->
        inst_memory (f_inst f) !! base_mem_idx mr μ = Some memidx ->
        types_agree t v ->
        length bs = length_t t ->
        ⊢ ∀ s E,
          ↪[frame] f -∗
          ↪[RUN] -∗
          memidxN ↦[wms][ℓ + byte_offset μ off] bs -∗
          ▷ (memidxN ↦[wms][ℓ + byte_offset μ off] bits v -∗ Φ f []) -∗
          CWP [W.BI_const (VAL_int32 ℓ32); W.BI_const v] ++ es @ s; E UNDER B; R {{ Φ }}.
  Proof.
    intros Hcg.
    unfold store_w in Hcg.
    inv_cg_emit Hcg; subst es wt' wl' ret.
    split; [auto|].
    split; [auto|].
    split; [auto|].
    intros * Hℓ Hmemidx Hmem Hty Hlen.
    iIntros (s E) "Hf Hrun Hbytes HΦ".
    iApply (cwp_store with "[$] [$] [$] [$]"); eauto.
  Qed.

  Lemma wp_store_w μ t off wt wl wt' wl' es ret :
    run_codegen (store_w mr μ t off) wt wl = inr (ret, wt', wl', es) ->
    ret = () /\
    wt' = [] /\
    wl' = [] /\
    forall ℓ ℓ32 memidx memidxN (f: frame) B R Φ v (bs: bytes),
        N_i32_repr (tag_address μ ℓ) ℓ32 ->
        N_nat_repr memidx memidxN ->
        inst_memory (f_inst f) !! base_mem_idx mr μ = Some memidx ->
        (ℓ `mod` 4 = 0)%N ->
        (ℓ <> 0)%N ->
        types_agree t v ->
        length bs = length_t t ->
        ⊢ ∀ s E,
          ↪[frame] f -∗
          ↪[RUN] -∗
          memidxN ↦[wms][ℓ + 4 * N.of_nat off] bs -∗
          ▷ (memidxN ↦[wms][ℓ + 4 * N.of_nat off] bits v -∗ Φ f []) -∗
          CWP [W.BI_const (VAL_int32 ℓ32); W.BI_const v] ++ es @ s; E UNDER B; R {{ Φ }}.
  Proof.
    intros Hcg.
    apply wp_store_w_strict in Hcg.
    intuition.
    iIntros (s E) "Hf Hrun Hbytes HΦ".
    assert (4 <= ℓ)%N by (by eapply mod_bound_nonzero).
    assert ((ℓ + 4 * N.of_nat off = tag_address μ ℓ + byte_offset μ off)%N) as Heq.
    { destruct μ; cbn; unfold offset_mm, offset_gc; lia. }
    rewrite Heq.
    iApply (H3 with "[$] [$] [Hbytes] [HΦ]"); eauto.
  Qed.

  Lemma wp_store1_mm a_idx off ι v_idx wt wl ret wt' wl' es :
    run_codegen (store1 mr MemMM a_idx off v_idx ι) wt wl = inr (ret, wt', wl', es) ->
    ∀ f ℓ a a32 val_v θ o ws E B R Φ,
    ⊢ "Hf"       ∷ ↪[frame] f -∗
      "Hrun"     ∷ ↪[RUN] -∗
      "Hptr"     ∷ ℓ ↦heap ws -∗
      "Haddr"    ∷ ℓ ↦addr (MemMM, a) -∗
      "Htok"     ∷ rt_token rti sr θ -∗
      "%Ha32"    ∷ ⌜f_locs f !! localimm a_idx = Some (VAL_int32 a32)⌝ -∗
      "%Hv"      ∷ ⌜f_locs f !! localimm v_idx = Some val_v⌝ -∗
      "%Hrepa"   ∷ ⌜N_i32_repr (tag_address MemMM a) a32⌝ -∗
      "%Hmod"    ∷ ⌜(a `mod` 4 = 0)%N⌝ -∗
      "%Hnz"     ∷ ⌜(a ≠ 0)%N⌝ -∗
      "%Hbound"  ∷ ⌜off + arep_size ι ≤ length ws⌝ -∗
      "%Harep"   ∷ ⌜has_arep ι o⌝ -∗
      "%Hrepmem" ∷ ⌜N_nat_repr (sr_mem_mm sr) (rt_memaddr sr MemMM)⌝ -∗
      "%Hmemmm"  ∷ ⌜inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some (sr_mem_mm sr)⌝ -∗
      "Hat"      ∷ atom_interp_weak θ MemMM o val_v -∗
      "HΦ"       ∷ (ℓ ↦heap (update_path_words off ws (serialize_atom o)) -∗
                    ℓ ↦addr (MemMM, a) -∗
                    rt_token rti sr θ -∗
                    Φ f []) -∗
    CWP es @ E UNDER B; R {{ Φ }}.
  Proof.
    intros Hcg.
    unfold store1 in Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_a ?rest Ha Hcg.
    inv_cg_emit Ha; subst.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_v es_store_w Hv Hcg.
    inv_cg_emit Hv; subst.
    apply wp_store_w in Hcg.
    destruct Hcg as (-> & -> & -> & Hstore_spec).
    intros *.
    repeat iIntros "@".
    (* get_local for address *)
    iApply (cwp_seq with "[Hf Hrun]").
    {
      iApply (cwp_local_get with "[] [$] [$]"); eauto.
      now instantiate (1:= λ f' v', ⌜f' = f ∧ v' = [VAL_int32 a32]⌝%I).
    }
    iIntros (f' vs') "[-> ->] Hf Hrun".
    rewrite app_assoc.
    (* get_local for value *)
    iApply (cwp_seq with "[Hf Hrun]").
    {
      iApply cwp_val_app; first apply has_values_to_consts.
      iApply (cwp_local_get with "[] [$] [$]"); eauto.
      now instantiate (1:= λ f' v', ⌜f' = f ∧ v' = [VAL_int32 a32; val_v]⌝%I).
    }
    iIntros (f' vs') "[-> ->] Hf Hrun".
    (* Open abstract-physical connection for the slice [off, off + arep_size ι) *)
    iPoseProof (virt_to_phys_slice_store_acc _ _ mr off (arep_size ι) with "[//] [$Htok] [$Hptr] [$Haddr]")
      as "(%hm & Hnp & (%ns & %ns32 & %Hns & Hphys & Hwords) & Hclose)".
    iPoseProof (atom_interp_weak_types_agree ι o MemMM θ val_v with "[//] [$Hat]") as "%Htypes".
    iPoseProof (atom_to_words_mm rti sr mr θ ι o val_v Harep with "[$Hat]") as "(%ns_new & %ns32_new & %Hns_new & %Hbits & Hwords_new)".
    (* Compute byte-length of old slice *)
    iPoseProof (big_sepL2_length with "Hwords") as "%Hlenws".
    assert (Hlenbytes : length (flat_map serialise_i32 ns32) = length_t (translate_arep ι)).
    {
      rewrite len_ser32.
      rewrite -(Forall2_length _ _ _ Hns).
      rewrite -Hlenws length_take length_drop length_t_translate_arep.
      lia.
    }
    iApply cwp_fupd.
    iApply (Hstore_spec a a32 (sr_mem_mm sr) (rt_memaddr sr MemMM) with "[$Hf] [$Hrun] [$Hphys]"); eauto.
    iNext; iIntros "Hnew_phys".
    iEval (rewrite <- Hbits) in "Hnew_phys".
    iMod ("Hclose" $! (serialize_atom o) ns_new ns32_new
      with "[%] [%] [$Hnew_phys] [$Hwords_new] [$Hnp]") as "(Hptr_new & Haddr & Htok)".
    - exact (has_arep_size ι o Harep).
    - exact Hns_new.
    - iModIntro. iApply ("HΦ" with "[$] [$]"); iFrame.
  Qed.

  (* TEMPORARY: COPIED FROM LOAD_COPY *)
  Lemma has_kind_ref_ty F κ κ' μ β τ :
    has_kind F (RefT κ μ β τ) κ' ->
    ∃ σ ξ,
      has_kind F τ (MEMTYPE σ ξ).
  Proof. Admitted.
  Lemma mono_size_eval_emp_Some σ :
    is_mono_size σ ->
    is_Some (eval_size EmptyEnv σ).
  Proof. Admitted.

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
            sκ = SVALTYPE [PtrR] ξ_ref).
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




    (* always do all the way at the end *)
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
         Hkind_τ & Hkind_prtarget & Hkind_τval & Hevalsize & -> & ->).


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
      inversion toinvert; subst; clear toinvert.
      iPoseProof (atom_interp_ptr_shaped with "Hv1") as
        "(%n & %n32 & %Hn32 & -> & %Hnshp & %rp & %Hreproot & Hv1)".
      apply has_values_app_inv in H0.
      destruct H0 as (ev1 & evs2 & -> & Hev1 & Hevs2).
      apply has_values_to_consts_inv in Hev1 as Hev1tosubst.
      cbn in Hev1tosubst; subst.

      (* Summary:
         - o1 became (PtrHeap MemMM ℓ), v1 became (VAL_int32 n32), ev1 became BI_const...
         - n32 is... the address associated with the pointer? Or at minimum it is the
           actual thing on the stack.
         - we also dug into the value interp of the reference, getting the following:
           + we got rp, the root pointer associated with ℓ, and a bunch of ℓ resources
           + we also importantly got the type interpretation of τ (what's currently being
             pointed to by the reference) and the words ws currently sitting there
       *)


      (** PUT FACTOIDS WE NEED HERE (THAT ARE MM/GC SPECIFIC) **)
      (* I'm going to make the specialized path lemma used here bc I want to try to
         contain all the kinding shenanigans.
       *)

      (** TIME TO BOOGIE *)
      (* note: I think saving stack and local tee can happen before the split *)
      (* it's a little easier to already have v1 being an n32 though *)

      (** SAVING STACK AND LOCAL TEE *)
      (* First, saving stack to clear evs2 and es_save *)

      (* apply lemma on the codegen. order of goals to help with evars *)
      eapply cwp_save_stack_w in Hsave; auto.
      4: exact Hevs2.
      3: {
        (* About result_type_interp_of_atoms_interp. *)
        (* true but boring/later *)
        admit.
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

      (* Reestablish ptr_local length *)
      assert (Hptrlocalfrsaved: ptr_local < length (f_locs fr_saved)). {
        (* If this isn't true this is weird, but seems hardish to prove *)
        admit.
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

      (* Summary:
         - Used up evs2 and es_save_stack and "put" the pointer in front of es_case_ptr block
         - Our frame changed twice: fr_saved is after saving the stack (so lots of things)
           got put into locals, and fr' is after putting n32 into the local associated
           with the ptr.
         - We also got a bunch of val_indx stuffs everywhere

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
        (* first, a smidge more work in Hcg_memMM *)
        inv_cg_bind Hcg_memMM what ?wt ?wt ?wl ?wl
          es_root_to_heap es_store Hcg_root Hcg_store.
        destruct what; subst.
        cbn in Hcg_root.
        inversion Hcg_root; subst. clear_nils.

        (* Actual Store *)
        clear Hval_localidxs.

        (* we can use up Hτ into path spec now if we'd like, unsure when is best *)
        pose proof
          (resolves_path_inv_sep_weak rti sr se
             τ π pr Hresolves F off ρ σ ξ ξser sz) as Hpath_spec.
        specialize (Hpath_spec H Hoff Hmonosize Hkind_τ Hkind_prtarget Hevalsize).

        (* put down a store lemma here *)
        (* this is the most deceiving admit of all time lmao *)
        admit.
      }




      (** ----------------- POINTER FLAGS --------------------- **)
      iIntros (fr_store vs_store) "Hres Hfr Hrun".

      (* unless I'm really tripping, I know that vs_store will be nil?
         So just for the sake of being able to dig into the ptr_flags_spec:
       *)
      assert (vs_store = []) by admit; subst.
      clear_nils.

      (* apply the spec onto the codegen and slowly specialize *)
      eapply cwp_set_pointer_flags in Hptr_flags.
      destruct Hptr_flags as (_ & -> & -> & Hptr_flags_spec).
      specialize (Hptr_flags_spec fr_store n n32).
      (* this theta is ALMOST CERTAINLY going to be different TODO *)
      specialize (Hptr_flags_spec θ).
      specialize (Hptr_flags_spec MemMM ℓ).

      (* we need four pure facts before using the spec:
         - off + length ιs < Int32.mod. Maybe from Hcg_memMM's memory.store?
         - N_i32_repr n n32. We have this.
         - repr_pointer θ (ptr) n. We have repr_root_pointer, which has
           everything but a `θ !! ℓ = Some(μ, a)`. So, we'll need that,
           but I can't actually imagine from where right now
         - f_locs fr_caseptr !! .. = n32. This is then just the minimum
           requirement of relating fr_caseptr and fr'
       *)

      assert (H1: ((off + length (flat_map arep_flags ιs))%nat ≤
                     Wasm_int.Int32.modulus)%Z) by admit.
      assert (H2: repr_pointer θ (PtrHeap MemMM ℓ) n) by admit.
      assert (H3: f_locs fr_store !! localimm (prelude.W.Mk_localidx ptr_local) =
                    Some (VAL_int32 n32)) by admit.
      specialize (Hptr_flags_spec ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto)).

      (* then the things we need out from case_ptrs:
         - ℓ ↦layout fs. Shouldn't be hard to get
         - run time token
         - N.of_nat sr_func_set_flag sr. We'll probably have to open
           the invariant here. (Or maybe we'll open it earlier)
         - na_own
         - Frame and run resources
         - instance interp for set_flag. I think we'll get it out of
           Hinst.

         That is The List of things we need on the other side of case_ptr.
         we'll then just have some "fun" proving our goal Φ with the modified
         resources.
       *)

      (* temporarily, pretend we have them *)
      iApply (Hptr_flags_spec with "[] [] [] [] [] [] [] [-]").
      1: instantiate (1:=fs).
      1-7: admit.

      (* this iIntros is from the ptr flags spec *)
      instantiate (1:= sr).
      instantiate (1:= rti).
      iIntros "Hℓ Hrt #Hnsfun Hown #Hinst_spec".
      clear_nils.
      iFrame.

      (* since this is store weak, something that should be true: *)
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
        (* TODO when things are more close to done, try not using this and
           see what happens
         *)
        admit.
      }
      rewrite <- Hfs.

      (* I want to look at the values interp briefly *)
      (* frame interp and frame rel shouldn't be insane as I think *)
      (* they'll be preserved? we'll see *)
      iSplitR; [|iSplitR].
      - admit.
      - admit.
      - iExists ([PtrA (PtrHeap MemMM ℓ)]).
        (* I think this doesn't change?? *)
        iEval (cbn).
        (* this is just aiming to keep track of what resources we end up needing
         *)
        iSplitL "Hℓ"; [|iSplitL; [|done]].
        + iExists [[PtrA (PtrHeap MemMM ℓ)]].
          iEval (cbn); iSplitR; [done|iSplitL;[|done]].
          rewrite !type_interp_eq; iEval (cbn).
          rewrite evalμ.
          iEval (cbn).

          iExists (SVALTYPE [PtrR] ξ_ref).
          iSplitR; [done|].
          iSplitR.
          * iPureIntro.
            done. (* note: this won't be as clean in the GC case I think *)
          * (* this will depend on the words we get and on fs *)

          (* Facts and resources we need:
             - We need ℓ ↦heap ws for some words
             - And we need a type interp τ for those words
           *)
          admit.
        + iExists n, n32.
          iSplitR; [done| iSplitR; [done|]].
          iExists rp.
          iSplitR; [done|].
          (* Resources we need:
             - root_pointer_interp rp (PtrHeap MemMM ℓ)
               which we had before
           *)
          admit.

    }










    [MemGC]: {
      (* note: this first set up has a lot of copying *)
      iEval (cbn) in "Ho1".
      iDestruct "Ho1" as "(%ℓ & %fs & %toinvert & Hτ)".
      inversion toinvert; subst; clear toinvert.
      iPoseProof (atom_interp_ptr_shaped with "Hv1") as
        "(%n & %n32 & %Hn32 & -> & %Hnshp & %rp & %Hreproot & Hv1)".
      apply has_values_app_inv in H0.
      destruct H0 as (ev1 & evs2 & -> & Hev1 & Hevs2).
      apply has_values_to_consts_inv in Hev1 as Hev1tosubst.
      cbn in Hev1tosubst; subst.

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



      (** TIME TO BOOGIE *)

      (** SAVING STACK AND LOCAL TEE *)
      (* First, saving stack to clear evs2 and es_save *)

      (* apply lemma on the codegen. order of goals to help with evars *)
      eapply cwp_save_stack_w in Hsave; auto.
      4: exact Hevs2.
      3: {
        (* About result_type_interp_of_atoms_interp. *)
        (* true but boring/later *)
        admit.
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
        - admit. (* this probably needs more work? *)
        - now instantiate (1:= λ f'' v'', ⌜f'' = f' /\ v'' = [VAL_int32 n32]⌝%I).
      }
      iIntros (? ?) "(-> & ->) Hf Hrun".

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

      (* Now we can cwp_seq and use the spec *)


      admit.
    }


  Admitted.

End store_weak.
