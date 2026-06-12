From mathcomp Require Import eqtype ssrbool.

Require Import RichWasm.util.
Require Import RichWasm.compiler.memory.
Require Import RichWasm.compiler.prelude.
Require Import RichWasm.compiler.codegen.
Require Import RichWasm.iris.numerics.
Require Import RichWasm.iris.memory.
Require Import RichWasm.iris.language.cwp.
Require Import RichWasm.iris.wp_codegen.
Require Import RichWasm.syntax.
From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import list.
From RichWasm.iris.language Require Import iris_wp_def lenient_wp logpred.
Require Import RichWasm.iris.logrel.
Require Import RichWasm.iris.logrel.logrel_properties.
Require Import RichWasm.iris.logrel.roots.
Require Import RichWasm.iris.logrel.case_ptr.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section map_gc_ptr.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma wp_map_gc_ptr_duproot ι idx wt wl res wt' wl' es:
    run_codegen (map_gc_ptr ι idx (duproot mr)) wt wl = inr (res, wt', wl', es) ->
    res = () /\ wt' = [] /\ wl' = [] /\
    ∀ s E B R Φ f o v lmask θ,
    ⊢ "Hf" ∷ ↪[frame] f -∗
      "Hr" ∷ ↪[RUN] -∗
      "HE" ∷ na_own logrel_nais E -∗
      "Hfunc" ∷ instance_rt_func_interp (mr_func_registerroot mr) (sr_func_registerroot sr) (runtime.spec_registerroot rti sr)
    (f_inst f) -∗
      "Htok" ∷ rt_token rti sr lmask θ -∗
      "Hat" ∷ atom_interp o v -∗
      "%Hi" ∷ ⌜f_locs f !! (localimm idx) = Some v⌝ -∗
      "%Harep" ∷ ⌜has_arep ι o⌝ -∗
      "%Hmm" ∷ ⌜inst_memory (f_inst f) !! memimm (mr_gcmem mr) = Some (sr_mem_gc sr)⌝ -∗
      "%Hmm" ∷ ⌜inst_memory (f_inst f) !! memimm (mr_mmmem mr) = Some (sr_mem_mm sr)⌝ -∗
      "%Hmask" ∷ ⌜↑ns_fun (N.of_nat (sr_func_registerroot sr)) ⊆ E⌝ -∗
      "HΦ" ∷ (∀ v',
        let f' := {| W.f_locs := <[localimm idx:=v']> (f_locs f); W.f_inst := f_inst f |} in
        "Htok" ∷ rt_token rti sr lmask θ -∗
        "HE" ∷ na_own logrel_nais E -∗
        "Hat" ∷ atom_interp o v -∗
        "Hat'" ∷ (⌜atom_copyable o⌝ -∗ atom_interp o v') -∗
        Φ f' []) -∗
      CWP es @ s; E UNDER B; R {{ Φ }}.
  Proof.
    unfold map_gc_ptr, ite_gc_ptr.
    intros Hcg.
    destruct ι.
    - eapply wp_ignore in Hcg.
      destruct Hcg as (-> & ([[] [[] []]] & Hcg)).
      eapply cwp_case_ptr in Hcg.
      destruct Hcg as (wt1 & wt2 & wt3 & wl1 & wl2 & wl3 & es1 & es2 & es3 & Hret & Hret' & Hdup & -> & -> & Hspec).
      inv_cg_ret Hret.
      inv_cg_ret Hret'.
      subst; clear_nils.
      inv_cg_bind Hdup [] ?wt ?wt ?wl ?wl es_get ?es' Hget Hcg.
      inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_dup es_set Hdup Hset.
      inv_cg_emit Hset.
      inv_cg_emit Hget.
      pose proof (wp_duproot rti sr mr _ _ _ _ _ _ Hdup) as (_ & -> & -> & Hdup').
      specialize (Hspec [] []).
      subst; clear_nils.
      repeat (split; first done).
      intros *; repeat iIntros "@".
      destruct o; try inversion Harep; clear Harep.
      iPoseProof (atom_interp_ptr_shaped with "Hat")
        as "(%n & %n32 & %Hn32 & -> & %Hshp & (%rp & %Hrep & Hrep))".
      iApply (Hspec with "[$] [$]"); eauto.
      iIntros "!> Hf Hr".
      destruct p as [ | [|]].
      {
        iApply (cwp_nil with "[$] [$]").
        pose proof (atom_interp_dup (PtrA (PtrInt n0)) (VAL_int32 n32) ltac:(done)).
        iAssert (atom_interp (PtrA (PtrInt n0)) (VAL_int32 n32)) with "[Hrep]" as "#Hat";
          first (iFrame; by eauto).
        iSpecialize ("HΦ" $! (VAL_int32 n32)).
        rewrite list_insert_id; last done.
        destruct f.
        iApply ("HΦ" with "[$] [$]"); eauto.
      }
      {
        iApply (cwp_nil with "[$] [$]").
        iSpecialize ("HΦ" $! (VAL_int32 n32)).
        rewrite list_insert_id; last done.
        destruct f.
        iApply ("HΦ" with "[$] [$] [Hrep]"); eauto.
        - iFrame; eauto.
        - iIntros "F"; done.
      }
      iApply (cwp_seq with "[Hf Hr]").
      {
        iApply (cwp_local_get with "[] [$]"); eauto.
        instantiate (1 := λ f' v', (⌜f' = f⌝ ∗ ⌜v' = [VAL_int32 n32]⌝)%I).
        done.
      }
      iIntros (f' vs') "(-> & ->) Hf Hr".
      iEval (rewrite app_assoc).
      destruct rp as [ | [|]]; try done.
      iEval (cbn) in "Hrep".
      inversion Hrep; subst.
      iPoseProof "Hfunc" as "#Hfunc".
      iApply (cwp_seq with "[Hf Hr Htok Hrep HE]").
      {
        open_rt "Htok".
        iApply (Hdup' with "[$] [$] [//] [//] [$] [$] [$] [-HE] [$HE]").
        - apply Hn32.
        - apply Is_true_true. apply has_values_to_consts.
        - eauto.
        - eauto.
        - iIntros "? ? ?".
          instantiate (1 := (a ↦root ℓ)%I).
          by iFrame.
        - done.
        - iIntros (ar ar32 Hrepr Har32) "Hroot Htok Hroot' Hown Hfunc'".
          iClear "Hfunc'".
          instantiate (1 := λ f' v',
                          (∃ ar ar32,
                              ⌜f' = f⌝ ∗ ⌜v' = [VAL_int32 ar32]⌝ ∗
                              ⌜N_i32_repr (tag_address MemGC ar) ar32⌝ ∗
                              ⌜repr_root_pointer (RootHeap MemGC ar) (tag_address MemGC ar)⌝ ∗
                              _)%I).
          iExists ar, ar32.
          repeat (iSplit; first done).
          iNamedAccu.
      }
      iIntros (f' v') "(%ar & %ar32 & -> & -> & %Har32 & %Hrepar & @ & @ & @ & @) Hf Hr".
      iApply (cwp_local_set with "[-Hf Hr] [$] [$]"); auto.
      + by eapply lookup_lt_Some.
      + iApply ("HΦ" with "[$] [$] [Hroot'] [Hroot]").
        * iExists (tag_address MemGC a), n32; eauto.
        * iIntros "_".
          iExists _, _; eauto.
    - inversion Hcg; subst.
      repeat (split; first done).
      intros *; repeat iIntros "@".
      iApply (cwp_nil with "[$] [$]").
      destruct o; try inversion Harep; clear Harep.
      iPoseProof "Hat" as "%Hat".
      iSpecialize ("HΦ" $! v).
      rewrite list_insert_id; last done.
      destruct f.
      iApply ("HΦ" with "[$] [$] [//] [//]"); done.
    - inversion Hcg; subst.
      repeat (split; first done).
      intros *; repeat iIntros "@".
      iApply (cwp_nil with "[$] [$]").
      destruct o; try inversion Harep; clear Harep.
      iPoseProof "Hat" as "%Hat".
      iSpecialize ("HΦ" $! v).
      rewrite list_insert_id; last done.
      destruct f.
      iApply ("HΦ" with "[$] [$] [//] [//]"); done.
    - inversion Hcg; subst.
      repeat (split; first done).
      intros *; repeat iIntros "@".
      iApply (cwp_nil with "[$] [$]").
      destruct o; try inversion Harep; clear Harep.
      iPoseProof "Hat" as "%Hat".
      iSpecialize ("HΦ" $! v).
      rewrite list_insert_id; last done.
      destruct f.
      iApply ("HΦ" with "[$] [$] [//] [//]"); done.
    - inversion Hcg; subst.
      repeat (split; first done).
      intros *; repeat iIntros "@".
      iApply (cwp_nil with "[$] [$]").
      destruct o; try inversion Harep; clear Harep.
      iPoseProof "Hat" as "%Hat".
      iSpecialize ("HΦ" $! v).
      rewrite list_insert_id; last done.
      destruct f.
      iApply ("HΦ" with "[$] [$] [//] [//]"); done.
  Qed.

  Lemma localimm_injective n m :
    localimm n = localimm m ->
    n = m.
  Proof.
    destruct n, m. cbn.
    congruence.
  Qed.

  Lemma wp_map_gc_ptrs_duproot ιs idxs wt wl res wt' wl' es :
    length ιs = length idxs ->
    NoDup idxs ->
    run_codegen (map_gc_ptrs ιs idxs (duproot mr)) wt wl = inr (res, wt', wl', es) ->
    res = () /\ wt' = [] /\ wl' = [] /\
    ∀ s E B R Φ f os vs lmask θ,
    ⊢ "Hf" ∷ ↪[frame] f -∗
      "Hr" ∷ ↪[RUN] -∗
      "HE" ∷ na_own logrel_nais E -∗
      "#Hfunc" ∷ instance_rt_func_interp (mr_func_registerroot mr) (sr_func_registerroot sr) (runtime.spec_registerroot rti sr)
    (f_inst f) -∗
      "Htok" ∷ rt_token rti sr lmask θ -∗
      "Hat" ∷ ([∗ list] o; v ∈ os; vs, atom_interp o v) -∗
      "%Hi" ∷ ⌜Forall2 (λ idx v, f_locs f !! idx = Some v) (map localimm idxs) vs⌝ -∗
      "%Harep" ∷ ⌜Forall2 has_arep ιs os⌝ -∗
      "%Hmm" ∷ ⌜inst_memory (f_inst f) !! memimm (mr_gcmem mr) = Some (sr_mem_gc sr)⌝ -∗
      "%Hmm" ∷ ⌜inst_memory (f_inst f) !! memimm (mr_mmmem mr) = Some (sr_mem_mm sr)⌝ -∗
      "%Hmask" ∷ ⌜↑ns_fun (N.of_nat (sr_func_registerroot sr)) ⊆ E⌝ -∗
      "HΦ" ∷ (∀ (vs' : list value) f',
        "Htok" ∷ rt_token rti sr lmask θ -∗
        "HE" ∷ na_own logrel_nais E -∗
        "Hats" ∷ ([∗ list] o; v ∈ os; vs, atom_interp o v) -∗
        "Hats'" ∷ ([∗ list] o; v' ∈ os; vs', ⌜atom_copyable o⌝ -∗ atom_interp o v') -∗
        "%Hinst" ∷ ⌜f_inst f' = f_inst f⌝ -∗
        "%Hupd" ∷ ⌜Forall2 (λ i v, f_locs f' !! i = Some v) (map localimm idxs) vs'⌝ -∗
         (* this hypothesis should probably be phrased in terms of frame_rel. *)
        "%Hsame" ∷ ⌜∀ i, prelude.W.Mk_localidx i ∉ idxs → f_locs f' !! i = f_locs f !! i⌝ -∗
        Φ f' []) -∗
      CWP es @ s; E UNDER B; R {{ Φ }}.
  Proof.
    unfold map_gc_ptrs, util.mapM_.
    intros Hlen Hnodup Hcg.
    apply wp_ignore in Hcg.
    destruct Hcg as (-> & res' & Hcg).
    remember (zip ιs idxs) as ιidxs.
    revert Heqιidxs Hlen Hnodup Hcg.
    revert ιs idxs wt wl res' wt' wl' es.
    induction ιidxs as [|[ι idx] ιidxs].
    - intros.
      destruct ιs, idxs; try done.
      apply wp_mapM_nil in Hcg.
      destruct Hcg as (-> & -> & -> & ->).
      repeat (split; first done).
      intros *; repeat iIntros "@".
      inversion Harep; subst os.
      inversion Hi; subst vs.
      iSpecialize ("HΦ" $! [] f).
      setoid_rewrite big_sepL2_nil.
      iApply (cwp_nil with "[$] [$]").
      iApply ("HΦ" with "[$] [$] [//] [//]"); done.
    - intros.
      destruct ιs as [|ι' ιs], idxs as [|idx' idxs]; inversion Heqιidxs.
      subst ι' idx'.
      apply wp_mapM_cons in Hcg.
      destruct Hcg as (res & ?wt & ?wl & ?es & ?res & ?wt & ?wl & ?es & Hdup & Hcg & Heqs).
      destruct Heqs as (-> & -> & -> & ->).
      assert (idx ∉ idxs ∧ NoDup idxs) as [Hfresh Hnodup'];
        first (inversion Hnodup; subst; done);
        clear Hnodup; rename Hnodup' into Hnodup.
      eapply IHιidxs in Hcg; eauto.
      destruct Hcg as (_ & -> & -> & IH).
      apply wp_map_gc_ptr_duproot in Hdup.
      destruct Hdup as (-> & -> & -> & Hspec).
      repeat (split; first done).
      intros *; repeat iIntros "@".
      destruct os as [|o os]; first by inversion Harep.
      destruct vs as [|v vs]; first by inversion Hi.
      inversion Harep as [| ι' o' ιs' os' Harep' Hareps eq1 eq2]; subst; clear Harep.
      rename Harep' into Harep.
      inversion Hi as [| idx' v' idxs' vs' Hi' His eq1 eq2]; subst; clear Hi.
      rename Hi' into Hi.
      setoid_rewrite big_sepL2_cons.
      iDestruct "Hat" as "[Hat Hats]".
      iApply (cwp_seq with "[-HΦ Hats]").
      {
        iApply (Hspec with "[$] [$] [$] [$] [$] [$]"); try done.
        iIntros (v'). repeat iIntros "@".
        instantiate (1 := λ f' vs',
                       (∃ v',
                          ⌜f' = {| W.f_locs := <[localimm idx:=v']> (f_locs f);
                                  W.f_inst := f_inst f |}⌝ ∗
                          ⌜vs' = []⌝ ∗
                          (⌜atom_copyable o⌝ -∗ atom_interp o v') ∗
                          _)%I).
        iExists v'.
        repeat (iSplit; first done).
        iFrame.
        iNamedAccu.
      }
      iIntros (f' vs') "(%v' & -> & -> & Hat' & @ & @ & @) Hf Hr".
      clear_nils.
      iApply (IH with "[$] [$] [$] [$] [$] [$]"); try done.
      {
        iPureIntro.
        pose proof (Forall2_length _ _ _ His) as Hislen.
        eapply big_and_forall2; first eauto.
        intros j idx' Hidx'.
        cbn.
        rewrite list_lookup_insert_ne.
        - eapply Forall2_lookup_l in His; last done.
          destruct His as (v'' & Hvs & Hfs).
          by rewrite Hfs -Hvs.
        - intro Heq; subst idx'.
          rewrite list_lookup_fmap in Hidx'.
          apply fmap_Some in Hidx'.
          destruct Hidx' as (lidx & Hidx' & Hinv).
          apply localimm_injective in Hinv; subst.
          apply Hfresh.
          rewrite list_elem_of_lookup.
          by eauto.
      }
      iIntros (vs' f'). repeat iIntros "@".
      iApply ("HΦ" with "[$] [$] [$] [Hat' Hats']"); try done.
      + instantiate (1 := (v' :: vs')).
        iFrame.
      + iPureIntro.
        rewrite map_cons.
        rewrite Forall2_cons.
        split; last done.
        rewrite Hsame; last by destruct idx.
        cbn.
        rewrite list_lookup_insert_eq; first done.
        by eapply lookup_lt_Some.
      + iPureIntro.
        setoid_rewrite not_elem_of_cons.
        intros i [Hneq Hnotin].
        rewrite Hsame; last done.
        cbn.
        rewrite list_lookup_insert_ne; first done.
        destruct idx; cbn; congruence.
  Qed.

End map_gc_ptr.
