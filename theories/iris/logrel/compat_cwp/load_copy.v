Require Import RecordUpdate.RecordUpdate.

From mathcomp Require Import ssrbool eqtype.

From stdpp Require Import base list.

From iris.proofmode Require Import base tactics classes.
From Wasm Require Import operations.

From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import prelude codegen instruction module memory.
From RichWasm.iris Require Import autowp memory util wp_codegen numerics.
From RichWasm.iris.language Require Import cwp logpred.
From RichWasm.iris.logrel Require Import relations_cwp.
From RichWasm.iris.logrel.compat_lemmas Require Import shared.
From RichWasm.iris.logrel.compat_cwp Require Import common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Fundamental.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma atoms_interp_nil_inv vs :
    atoms_interp [] vs ⊣⊢ ⌜vs = []⌝ .
  Proof.
    iSplit.
    - setoid_rewrite big_sepL2_nil_inv_l.
      done.
    - iIntros (->); cbn; done.
  Qed.

  Lemma atoms_interp_cons_inv o os vs :
    ⊢ atoms_interp (o :: os) vs -∗ ∃ v vs', ⌜vs = v :: vs'⌝ ∗ atom_interp o v ∗ atoms_interp os vs'.
  Proof.
    iIntros "Hat".
    iEval (unfold atoms_interp) in "Hat".
    setoid_rewrite big_sepL2_cons_inv_l.
    iDestruct "Hat" as (v vs' Hvs) "(Hv & Hvs')".
    iExists v, vs'; iFrame; done.
  Qed.

  Lemma atoms_interp_length os vs :
    ⊢ atoms_interp os vs -∗ ⌜length os = length vs⌝.
  Proof.
    iApply big_sepL2_length.
  Qed.

  Lemma atoms_interp_one_inv o vs :
    atoms_interp [o] vs ⊣⊢ ∃ v, ⌜vs = [v]⌝ ∗ atom_interp o v.
  Proof.
    iSplit.
    - iIntros "Hvs".
      iPoseProof (atoms_interp_cons_inv with "Hvs") as (v vs' Heq) "[Hv Hnil]".
      rewrite atoms_interp_nil_inv.
      iDestruct "Hnil" as "%Hnil"; subst.
      iExists v; auto.
    - iIntros "(%v & -> & Hv)".
      cbn; auto.
  Qed.

  Lemma value_interp_ref_sz se κ μ τ os :
    ⊢ value_interp rti sr se (RefT κ μ τ) (SAtoms os) -∗ ⌜length os = 1⌝.
  Proof.
    iIntros "Hv".
    rewrite value_interp_eq; cbn.
    iDestruct "Hv" as "(%κ0 & %Heval & Hkind & Hmem)".
    destruct μ as [| [|]]; auto.
    - iDestruct "Hmem" as "(%ℓ & %fs & %ws & %Hos & _)".
      by inversion Hos.
    - iDestruct "Hmem" as "(%ℓ & %fs & %Hos & _)".
      by inversion Hos.
  Qed.

  Lemma rep_ref_kind_ptr F κ μ τ ρ χ δ :
    has_kind F (RefT κ μ τ) (VALTYPE ρ χ δ) ->
    ρ = AtomR PtrR /\
    exists χ', κ = VALTYPE (AtomR PtrR) χ' ExDrop.
  Proof.
    intros Hkind.
    remember (RefT κ μ τ) as ref.
    remember (VALTYPE ρ χ δ) as val.
    revert Heqval Heqref.
    revert ρ χ δ.
    induction Hkind using has_kind_ind'; intros; try congruence.
    - subst κ0.
      split; try congruence.
      inversion Heqref; eauto.
    - subst κ0.
      split; try congruence.
      inversion Heqref; eauto.
    - subst κ'.
      inversion H; subst; eapply IHHkind; eauto.
  Qed.

  Lemma wp_load_w μ t off wt wl wt' wl' es ret :
    run_codegen (load_w mr μ t off) wt wl = inr (ret, wt', wl', es) ->
    ret = () /\
    wt' = [] /\
    wl' = [] /\
    forall ℓ ℓ32 memidx memidxN (f: frame) B R Φ v,
        N_i32_repr ℓ ℓ32 ->
        N_nat_repr memidx memidxN ->
        inst_memory (f_inst f) !! base_mem_idx mr μ = Some memidx ->
        types_agree t v ->
        ⊢ ↪[frame] f -∗
          ↪[RUN] -∗
          memidxN ↦[wms][ℓ + byte_offset μ off]bits v -∗
          ▷ (memidxN↦[wms][ℓ + byte_offset μ off]bits v -∗ Φ f [v]) -∗
          CWP W.BI_const (VAL_int32 ℓ32) :: es UNDER B; R {{ Φ }}.
  Proof.
    intros Hcg.
    unfold load_w in Hcg.
    inv_cg_emit Hcg; subst es wt' wl' ret.
    split; [auto|].
    split; [auto|].
    split; [auto|].
    intros * Hℓ Hmemidx Hmem Hty.
    iIntros "Hf Hrun Hptr HΦ".
    iApply (cwp_load with "[$] [$] [$] [$]"); eauto.
  Qed.

  Lemma wp_mem_load1_copy_mm
    se fe lidx off ι wt wl ret wt' wl' es fs ws ℓ ℓ32 τ π B R
    (f: frame) memidx memidxN v Φ :
    run_codegen (memory.load1 mr fe MemMM Copy lidx off ι) wt wl = inr (ret, wt', wl', es) ->
    N_i32_repr ℓ ℓ32 ->
    N_nat_repr memidx memidxN ->
    inst_memory (f_inst f) !! base_mem_idx mr MemMM = Some memidx ->
    f_locs f !! localimm lidx = Some (VAL_int32 ℓ32) ->
    types_agree (translate_arep ι) v ->
    ret = () /\
    ⊢ ↪[frame] f -∗
      ↪[RUN] -∗
      ℓ ↦layout fs -∗
      ℓ ↦heap ws -∗
      memidxN ↦[wms][ℓ + byte_offset MemMM off]bits v -∗
      ▷ value_interp rti sr se τ (SWords ws) -∗
      ⌜path_offset fe τ π = Some off⌝ -∗
      CWP es UNDER B; R {{ Φ }}.
  Proof.
    unfold load1.
    intros Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_get ?es_rest Hget Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_ret ?es_rest Hret Hcompile.
    cbn in Hret; inversion Hret; subst; clear Hret.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_load_w ?es_rest Hload_w Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_wlalloc ?es_rest Hwlalloc Hcompile.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl es_save ?es_rest Hsave Hcompile.
    subst.
    apply wp_wlalloc in Hwlalloc.
    destruct Hwlalloc as (Hidx & -> & -> & ->).
    eapply wp_load_w in Hload_w.
    destruct Hload_w as (_ & -> & -> & Hload_w).
    inversion Hidx; subst n.
    inv_cg_emit Hget; subst.
    inv_cg_emit Hsave; subst.
    clear Hretval Hretval0.
    clear_nils.
    destruct ret.
    split; [reflexivity|].
    iIntros "Hf Hrun Hfs Hws Hmem Hval %Hpath".
    iApply (cwp_seq with "[Hf Hrun]").
    {
      iApply (cwp_local_get with "[] [$] [$]"); eauto.
      now instantiate (1:= λ f' v', ⌜f' = f /\ v' = [VAL_int32 ℓ32]⌝%I).
    }
    iIntros (f' vs') "[-> ->] Hf Hrun".
    rewrite app_assoc.
    iApply (cwp_seq with "[Hf Hrun Hmem]").
    {
      iApply (Hload_w with "[$] [$] [$]"); eauto.
      iIntros "!> Hmem".
      instantiate (1:= λ f' v', (⌜f' = f⌝ ∗ ⌜v' = [v]⌝ ∗ _)%I).
      cbn.
      iSplit; [done|].
      iSplit; [done|].
      iApply "Hmem".
    }
    iIntros (? ?) "(-> & -> & Hmem) Hf Hrun".
    rewrite app_assoc.
    set (vloc := localimm (W.Mk_localidx (fe_wlocal_offset fe + length wl))).
    set (f' := {| f_locs := <[vloc := v]> (f_locs f);
                  f_inst := f_inst f |}).
    iApply (cwp_seq with "[Hf Hrun]").
    {
      iApply (cwp_local_tee with "[] [$] [$]").
      - admit.
      - now instantiate (1:= λ f'' v'', ⌜f'' = f' /\ v'' = [v]⌝%I).
    }
    iIntros (? ?) "(-> & ->) Hf Hrun".
    unfold ite_gc_ptr in Hcompile.
    admit.
  Abort.

  Lemma mem_load_copy_mm_spec se fe lidx off ιs wt wl ret wt' wl' es fs ws ℓ τ π ev B R :
    run_codegen (memory.load mr fe MemMM Copy lidx off ιs) wt wl = inr (ret, wt', wl', es) ->
    ret = () /\
    ⊢ ℓ ↦layout fs -∗
      ℓ ↦heap ws -∗
      ▷ value_interp rti sr se τ (SWords ws) -∗
      ⌜path_offset fe τ π = Some off⌝ -∗
      CWP ev :: es UNDER B; R {{ fr'; vs', True }}.
  Proof.
  Abort.

  Lemma compat_load_copy M F L wt wt' wtf wl wl' wlf es' κ κser μ τ τval π pr :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT [RefT κ μ τ] [RefT κ μ τ; τval] in
    has_copyability F τval ExCopy ->
    resolves_path τ π None pr ->
    pr.(pr_target) = SerT κser τval ->
    Forall (has_mono_size F) (pr_prefix pr) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ILoad ψ π Copy)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL es' ψ L.
  Proof.
    intros fe WT WL ψ Hcopyability Hresolves Hser Hmonosize Htype Hcompile.
    unfold WT, WL; clear WT WL. (* If the WT := or WL := become necessary, comment the unfold/clear*)
    cbn in Hcompile.

    (* Mechanically get through some of the first few things in compile_load *)
    inv_cg_bind Hcompile off ?wt ?wt ?wl ?wl  es_fail ?es_rest Hoff Hcompile.
    inv_cg_bind Hcompile ρ ?wt ?wt ?wl ?wl es_off ?es_rest Hρ Hcompile.
    inv_cg_bind Hcompile ιs ?wt ?wt ?wl ?wl es_ρ ?es_rest Hιs Hcompile.
    inv_cg_try_option Hρ; rename Heq_some into Hρ.
    inv_cg_try_option Hιs; rename Heq_some into Hιs.
    inv_cg_try_option Hoff; rename Heq_some into Hoff.
    inv_cg_bind Hcompile a ?wt ?wt ?wl ?wl es_a ?es_rest Ha Hcompile.
    cbn in Ha; inversion Ha; subst; clear Ha.
    inv_cg_bind Hcompile res_emit ?wt ?wt ?wl ?wl  es_emit ?es_rest Hemit Hcompile.
    inv_cg_emit Hemit.
    inv_cg_bind Hcompile () ?wt ?wt ?wl ?wl es_empty ?es_rest Hempty Hcompile.
    cbn in Hempty; inversion Hempty; subst; clear Hempty.
    inv_cg_bind Hcompile [] ?wt ?wt ?wl ?wl  es_case_ptr ?es_rest Hcompile Hignore.
    cbn in Hignore; inversion Hignore; subst; clear Hignore.

    (* Some clean up *)
    assert (Hu: u = ()). { by destruct u. }
    assert (Hp: p = ((),())). { by destruct p as [[] []]. }
    subst.
    rewrite ?app_nil_r ?app_nil_l -?app_assoc.
    rewrite ?app_nil_r ?app_nil_l -?app_assoc in Hcompile.
    simpl app.
    unfold have_instr_type_sem.
    iIntros (se inst fr os vs evs θ B R Hse Hevs) "Hinst Hlbl Hret Hats Hvals Hfr Hrt Hf Hrun".
    iEval (rewrite values_interp_one_eq; cbn) in "Hvals".
    iPoseProof (value_interp_ref_sz with "Hvals") as "%Hlen_os".
    iEval (rewrite value_interp_eq) in "Hvals".
    iDestruct "Hvals" as (κ' Hκ') "[Harep Href]".
    destruct κ'; [|done].
    iDestruct "Harep" as "%Harep".
    change instruction.W.T_i32 with T_i32 in *.
    change prelude.W.Mk_localidx with Mk_localidx in *.
    change instruction.W.BI_unreachable with BI_unreachable in *.
    change instruction.W.BI_tee_local with BI_tee_local in *.
    set (ptr_local := sum_list_with length (typing.fc_locals F) + length wl) in *.

    cbn in Hκ'.
    iAssert (⌜ptr_local < length (f_locs fr)⌝%I) as "%Hlen".
    {
      (* need a lemma about frame_interp, I think? *)
      admit.
    }
    assert (Hκ: eval_rep se (AtomR PtrR) = Some l).
    {
      inversion Htype as [? ? ? Hmono Hctx]; subst.
      destruct Hmono as [Hmono _].
      rewrite Forall_singleton in Hmono.
      inversion Hmono as [? ? ? Hrep Hismono]; subst.
      inversion Hrep; subst.
      apply rep_ref_kind_ptr in H; subst.
      destruct H as [-> [χ' ->]].
      unfold eval_kind in Hκ'.
      apply bind_Some in Hκ'; destruct Hκ' as [l' [Heval Hret]].
      inversion Hret; subst; auto.
    }
    cbn in Hκ; inversion Hκ; subst l.
    destruct Harep as [os' [Hos Hareps]].
    inversion Hos; subst os'; clear Hos.
    iPoseProof (atoms_interp_length os vs with "Hats") as "%Hlen_os_vs".
    pose proof (has_values_length _ _ Hevs) as Hlen_evs_vs.
    destruct evs as [|ev [|ev' evs]]; try (cbn in *; congruence).
    destruct vs as [|v [|v' vs]]; try (cbn in *; congruence).
    destruct os as [|o [|o' os]]; try (cbn in *; congruence).
    inversion Hareps as [| ? ? ? ? Harep _]; subst.
    destruct o; inversion Harep; clear Harep Hareps.
    cbn [app].
    change (?x :: ?y :: ?z) with ([x; y] ++ z).
    set (f' := {| f_locs := <[ptr_local:=v ]> (f_locs fr);
                  f_inst := f_inst fr |}).
    iApply (cwp_seq with "[Hf Hrun]").
    {
      change ([?ev; ?x]) with ([ev] ++ [x]).
      rewrite (has_values_to_consts_inv _ _ Hevs).
      iApply (cwp_local_tee with "[ ] [$] [$]"); eauto.
      by instantiate (1:= λ f'' vs', ⌜f'' = f' /\ vs' = [v]⌝%I).
    }
    iIntros (f vs) "[-> ->] Hf Hrun".
    eapply cwp_case_ptr in Hcompile.
    2: do 2 instantiate (1 := []).
    2, 3: done.
    destruct Hcompile as (?wt & ?wt & ?wt & ?wl & ?wl & ?wl & ?es & ?es & ?es & Hcompile).
    destruct Hcompile as (Hunr & Hload1 & Hload2 & Hwt0 & Hwl0 & Hspec).
    rewrite atoms_interp_one_inv.
    iDestruct "Hats" as "(%v' & %Hv' & Hat)".
    inversion Hv'; subst v'; clear Hv'.
    iApply cwp_val_app.
    { instantiate (1 := [v]). apply Is_true_true. apply/andP; split => //. by apply/eqP. }
    iApply (Hspec with "[$] [$] [] [$Hat]").
    {
      iPureIntro; cbn.
      by rewrite list_lookup_insert.
    }
    iIntros "!> Hf Hrun Hat".
    iEval (cbn) in "Href".
    destruct μ as [|[|]]; first done.
    - unfold ref_mm_interp.
      iDestruct "Href" as (ℓ fs ws Hsv) "(Hℓl & Hℓh & Hws)".
      inversion Hsv; subst.
      rewrite value_interp_eq.
      (* need lemma about memory.load *)
      assert (Hlenιs: length ιs = 1) by admit.
      destruct ιs as [| ι [| ? ? ]]; try discriminate Hlenιs.
      cbn in Hload1.
      admit.
    - unfold ref_gc_interp.
      iDestruct "Href" as (ℓ fs Hsv) "Hinv".
      inversion Hsv; subst.
      (* need lemma about memory.load *)
      admit.
  Admitted.

End Fundamental.
