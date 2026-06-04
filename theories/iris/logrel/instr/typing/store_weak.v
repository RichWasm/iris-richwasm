Require Import RichWasm.compiler.memory.
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

    (* Summary:
       - o1 is the atom associated with the ref, and v1 is its associated value
       - os2 are the atoms associated with τval, and vs2 are its values
       Note: o1 is Ptr _, but it's easier to get that after splitting between MM
       and GC.
     *)

    (* Set any other useful keys here? *)
    set (ptr_local := sum_list_with length F.(typing.fc_locals) + length (wl ++ wl_save) ) in *.



    (** KINDING STUFF *)



    (** OTHER GENERAL FACTS THAT WE NEED FOR BOTH CASES *)
    iPoseProof (frame_interp_wl_interp with "Hframe") as "%Hwl". (* for saving stack *)




    (** BEGIN THE SPLIT **)

    (* This is where it's best to show o1 is ptr and v1 a ptr shaped number,
       so the first bit of both sections is dedicated to that.
       this bit first for that `last done` in the splitting line.
     *)
    rewrite value_interp_eq.
    iDestruct "Hos1" as (sκ Hsκ) "[%skindsv Ho1]".
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

      (* factoid: *)
      assert (Hptrlocalfrsaved: ptr_local < length (f_locs fr_saved)) by admit.

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


      (** ----------------- CASE PTR TIME --------------------- **)
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
        (* this is the most deceiving admit of all time lmao *)
        admit.
      }




      (** ----------------- POINTER FLAGS --------------------- **)
      iIntros (fr_caseptr vs_caseptr) "Hres Hfr Hrun".

      (* unless I'm really tripping, I know that vs_caseptr will be nil?
         So just for the sake of being able to dig into the ptr_flags_spec:
       *)
      assert (vs_caseptr = []) by admit; subst.
      clear_nils.

      (* apply the spec onto the codegen and slowly specialize *)
      eapply cwp_set_pointer_flags in Hptr_flags.
      destruct Hptr_flags as (_ & -> & -> & Hptr_flags_spec).
      specialize (Hptr_flags_spec fr_caseptr n n32).
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
      assert (H3: f_locs fr_caseptr !! localimm (prelude.W.Mk_localidx ptr_local) =
                    Some (VAL_int32 n32)) by admit.
      specialize (Hptr_flags_spec ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto)).

      (* then the things we need out from case_ptrs:
         - ℓ ↦layout fsnew. Shouldn't be hard to get
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
