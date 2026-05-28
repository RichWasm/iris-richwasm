From mathcomp Require Import eqtype ssrbool.

Require Import RichWasm.util.
Require Import RichWasm.compiler.memory.
Require Import RichWasm.iris.numerics.
Require Import RichWasm.iris.runtime.
Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.case_ptr.
Require Import RichWasm.iris.logrel.path.
Require Import RichWasm.iris.logrel.load.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section load_copy.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma Forall2_Forall2_length {A B} {P : A -> B -> Prop} xss yss :
    Forall2 (Forall2 P) xss yss ->
    map length xss = map length yss.
  Proof.
    intros Hall. induction Hall.
    - reflexivity.
    - cbn.
      f_equal; last apply IHHall.
      by eapply Forall2_length.
  Qed.

  Lemma sum_list_with_list_sum {A} {xs : list (list A)} :
    sum_list_with length xs = list_sum (map length xs).
  Proof.
    induction xs.
    - done.
    - cbn.
      by rewrite IHxs.
  Qed.

  (* inversion lemma for learning about tau given a Ref k mu tau *)
  Lemma has_kind_ref_ty F κ κ' μ β τ :
    has_kind F (RefT κ μ β τ) κ' ->
    ∃ σ ξ,
      has_kind F τ (MEMTYPE σ ξ).
  Proof.
    intros Hkind.
    remember (RefT κ μ β τ) as τ0 eqn:Href.
    revert Href.
    revert κ μ.
    induction Hkind; intros κ'' μ' Href;
      try congruence.
    - subst κ. inversion Href; subst.
      by exists σ, ξ.
    - subst κ.
      inversion Href.
      subst.
      by exists σ, ξ.
  Qed.

  Lemma mono_size_eval_emp_Some σ :
    is_mono_size σ ->
    is_Some (eval_size EmptyEnv σ).
  Proof.
    intros Hmono.
    induction σ using size_ind; inversion Hmono; subst.
    - cbn in H1; lia.
    - cbn.
      rewrite !Forall_forall in H H2.
      assert (is_Some (mapM (eval_size EmptyEnv) σs)) as (ns & ->); last done.
      eapply mapM_is_Some_2, Forall_forall; intros; cbn.
      eapply H; try eapply H2; eauto.
    - cbn.
      rewrite !Forall_forall in H H2.
      assert (is_Some (mapM (eval_size EmptyEnv) σs)) as (ns & ->); last done.
      eapply mapM_is_Some_2, Forall_forall; intros; cbn.
      eapply H; try eapply H2; eauto.
    - cbn.
      eapply eval_rep_empty_ok_Some in H1.
      by destruct H1 as (rep & ->).
    - done.
  Qed.

  Lemma value_deser se κ τ ws :
    ⊢ value_interp rti sr se (SerT κ τ) (SWords ws) -∗
      ∃ os, ⌜ws = flat_map serialize_atom os⌝ ∗ value_interp rti sr se τ (SAtoms os).
  Proof.
    iIntros "Hval".
    rewrite value_interp_eq.
    iDestruct "Hval" as "(%sk & %Hevsk & %Hkind & Hval)".
    cbn.
    iDestruct "Hval" as "(%os & %Hws & Hos)".
    inversion Hws; subst.
    iExists os.
    iSplitR; first done.
    done.
  Qed.

  Lemma big_sepL2_take_drop_acc {X Y} {P : X → Y → iProp Σ} xs ys n m :
    ([∗ list] x;y ∈ xs;ys, P x y) -∗
    ([∗ list] x;y ∈ take n (drop m xs);take n (drop m ys), P x y) ∗
    (([∗ list] x;y ∈ take n (drop m xs);take n (drop m ys), P x y) -∗
     ([∗ list] x;y ∈ xs;ys, P x y)).
  Proof.
  Admitted.

  Lemma flat_map_rcons X Y (f : X -> list Y) xs x :
    flat_map f (seq.rcons xs x) = flat_map f xs ++ f x.
  Proof.
    revert x.
    induction xs; cbn; intros.
    - by clear_nils.
    - by rewrite -app_assoc IHxs.
  Qed.

  Lemma length_bits_words ns32 :
    length (flat_map bits (map VAL_int32 ns32)) = 4 * length ns32.
  Proof.
    induction ns32.
    - done.
    - cbn -[bits Nat.mul].
      rewrite length_app.
      rewrite (length_bits _ T_i32); last done.
      rewrite IHns32.
      cbn; lia.
  Qed.

  Lemma offset_plus_lens : forall μ ns32 off,
    (byte_offset μ off + N.of_nat (length (flat_map bits (map VAL_int32 ns32))) = byte_offset μ (off + length ns32))%N.
  Proof.
    setoid_rewrite length_bits_words.
    setoid_rewrite Nat2N.inj_mul.
    replace (N.of_nat 4) with (4%N) by done.
    intros.
    destruct μ; cbn; lia.
  Qed.

  Lemma rcons_app {X} : forall (xs : list X) x,
      seq.rcons xs x = xs ++ [x].
  Proof.
    induction xs; intros x.
    - reflexivity.
    - cbn.
      by rewrite IHxs.
  Qed.

  Lemma drop_rcons_le {X} : forall n (xs : list X) x,
    n <= length xs ->
    drop n (seq.rcons xs x) = seq.rcons (drop n xs) x.
  Proof.
    intros * Hlen.
    rewrite !rcons_app.
    rewrite drop_app.
    replace (n - length xs) with 0 by lia.
    by rewrite drop_0.
  Qed.

  Definition word_interp_weak θ μ (ws : list word) (ns : list N) : iProp Σ :=
    [∗ list] w; n ∈ ws; ns, word_interp θ μ w n.

  (* Not yet correct. This lemma also has to deal with the difference between a
     sequence of i32s (as exists in the word memory model) and bits applied to a
     sequence of values. *)
  Lemma make_load_foldl : forall ιs θ os ns ns_32 a off offs vs,
    length offs + length ιs = length vs ->
    Forall2 has_arep ιs os ->
    Forall2 N_i32_repr ns ns_32 ->
    ([∗ list] o; v ∈ os; vs, atom_interp o v) -∗
    ([∗ list] w; n ∈ flat_map serialize_atom os; ns, word_interp θ MemMM w n) -∗
    rt_memaddr sr MemMM↦[wms][a + byte_offset MemMM off]flat_map bits (map VAL_int32 ns_32) -∗
    [∗ list] off';v ∈ (seq.foldl (λ '(off', offs) (ι : atomic_rep), (off' + arep_size ι, seq.rcons offs off'))
                         (off, offs) ιs).2; drop (length offs) vs,
                         N.of_nat (sr_mem_mm sr)↦[wms][a + byte_offset MemMM off'] bits v.
  Proof.
    intros ιs.
    induction ιs using seq.last_ind; intros * Hoffs Harep Hrep; iIntros "Hats Hws Hpt".
    - iEval (cbn).
      inversion Harep; subst.
      iPoseProof (big_sepL2_nil_inv_l with "Hats") as "->".
      cbn in *.
      assert (length offs = 0) by lia.
      destruct offs; done.
    - apply Forall2_rcons_inv_l in Harep.
      (*
      destruct Harep as (o & os' & Harep & Hreps & Heq).
      rewrite Heq.
      iPoseProof (big_sepL2_rcons_inv_l with "Hats") as "(%vs' & %v & -> & Hat & Hats)".
      rewrite flat_map_rcons.
      iPoseProof (big_sepL2_app_inv_l with "Hws") as "(%ns' & %ns'' & -> & Hws & Hw)".
      eapply Forall2_app_inv_l in Hrep.
      destruct Hrep as (ns32' & ns32'' & Hv & Hvs' & ->).
      iEval (rewrite map_app flat_map_app) in "Hpt".
      iPoseProof (wms_app with "Hpt") as "[Hpt1 Hpt2]"; first eauto.
      iEval (rewrite -N.add_assoc offset_plus_lens) in "Hpt2".
      assert (length offs + length ιs = length v).
      {
        rewrite !length_is_size !seq.size_rcons in Hoffs.
        rewrite !length_is_size; lia.
      }
      rewrite seq.foldl_rcons.
      destruct (seq.foldl
                  (λ '(off', offs) (ι : atomic_rep),
                    (off' + arep_size ι, seq.rcons offs off'))
                  (off, offs) ιs)
        as [off' offs'] eqn:Hfold.
      iAssert (⌜off' = (off + length ns32')%nat⌝%I) as "%Heqoff'".
      {
        admit.
      }
      iAssert (⌜bits vs' = flat_map bits (map VAL_int32 ns32'')⌝%I) as "%Heqvs'".
      {
        admit.
      }
      iPoseProof (IHιs θ os' _ _ _ off offs with "[$Hats] [$Hws] [$Hpt1]") as "IH"; eauto.
      rewrite Hfold.
      cbn [snd].
      rewrite drop_rcons_le; last lia.
      iApply big_sepL2_rcons.
      rewrite Heqoff' Heqvs'.
      iFrame.
      *)
  Admitted.

  Lemma compat_load_copy M F L wt wt' wtf wl wl' wlf es' κ κser μ β τ τval π pr :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [RefT κ μ β τ] [RefT κ μ β τ; τval] in
    has_ref_flag F τval GCRefs ->
    resolves_path τ π None pr ->
    pr.(pr_target) = SerT κser τval ->
    Forall (has_mono_size F) (pr_prefix pr) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ILoad ψ π Copy)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmask ψ Hcopyability Hresolves Hser Hmonosize Htype Hcompile.
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
    iIntros (se fr os vs evs θ B R Hse Hevs) "@ @ @ @ @ @ @ @ @ @".
    iEval (rewrite values_interp_one_eq; cbn) in "Hos".
    iPoseProof (value_interp_ref_sz with "Hos") as "%Hlen_os".
    iDestruct "Hos" as (κ' Hκ') "[Harep Href]".
    destruct κ'; [|by iDestruct "Harep" as "[[] ?]"].
    iDestruct "Harep" as "%Harep".
    change instruction.W.T_i32 with T_i32 in *.
    change prelude.W.Mk_localidx with Mk_localidx in *.
    change instruction.W.BI_unreachable with BI_unreachable in *.
    change instruction.W.BI_tee_local with BI_tee_local in *.
    set (ptr_local := sum_list_with length F.(typing.fc_locals) + length wl) in *.
    cbn in Hκ'.
    set (locsz :=
               length (concat (typing.fc_locals F)) +
               length wl +
               length (T_i32 :: wl0 ++ wlf)).
    iAssert (⌜length (f_locs fr) = locsz⌝%I) as "%Hflen".
    {
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
      by rewrite Nat.add_assoc.
    }
    assert (ptr_local < length (f_locs fr)) as Hlen.
    {
      rewrite Hflen.
      unfold locsz, ptr_local.
      rewrite sum_list_with_list_sum length_concat.
      cbn; lia.
    }
    assert (Hκ: eval_rep se (AtomR PtrR) = Some l).
    {
      destruct Htype as [Hmono Hctx].
      destruct Hmono as [Hmono _].
      rewrite Forall_singleton in Hmono.
      destruct Hmono as (ρ' & Hrep & Hismono).
      inversion Hrep; subst.
      cbn.
      apply rep_ref_kind_ptr in H; subst.
      destruct H as [-> [χ' ->]].
      unfold eval_kind in Hκ'.
      apply bind_Some in Hκ'; destruct Hκ' as [l' [Heval Hret]].
      inversion Hret; subst; auto.
    }
    cbn in Hκ; inversion Hκ; subst l.
    destruct Harep as [[os' [Hos Hareps]] Hrefflag].
    inversion Hos; subst os'; clear Hos.
    iPoseProof (atoms_interp_length os vs with "Hvs") as "%Hlen_os_vs".
    pose proof (has_values_length _ _ Hevs) as Hlen_evs_vs.
    destruct evs as [|ev [|ev' evs]]; try (cbn in *; congruence).
    destruct vs as [|v [|v' vs]]; try (cbn in *; congruence).
    destruct os as [|o [|o' os]]; try (cbn in *; congruence).
    inversion Hareps as [| ? ? ? ? Harep _]; subst.
    destruct o; inversion Harep; clear Harep Hareps.
    cbn [app].
    iEval (cbn) in "Href".
    destruct (eval_mem se μ) as [[|]|]; last done; destruct β.
    - iDestruct "Href" as (ℓ fs ws Hsv) "(Hℓl & Hℓh & Hws)".
      inversion Hsv; subst p; clear Hsv.
      change (?x :: ?y :: ?z) with ([x; y] ++ z).
      set (f' := {| f_locs := <[ptr_local:=v ]> (f_locs fr);
                    f_inst := f_inst fr |}).
      iApply (cwp_seq with "[Hfr Hrun Hws]").
      {
        change ([?ev; ?x]) with ([ev] ++ [x]).
        rewrite (has_values_to_consts_inv _ _ Hevs).
        iApply (cwp_local_tee with "[Hws] [$] [$]"); first eauto.
        instantiate (1:= λ f'' vs', (⌜f'' = f' /\ vs' = [v]⌝ ∗ type_interp rti sr τ se (SWords ws))%I).
        by iFrame.
      }
      iIntros (f vs) "([-> ->] & Hws) Hf Hrun".
      setoid_rewrite type_interp_eq.
      iDestruct "Hws" as "(%κ' & %Hsk & %Hk & Ht)".
      eapply cwp_case_ptr in Hcompile.
      destruct Hcompile as (?wt & ?wt & ?wt & ?wl & ?wl & ?wl & ?es & ?es & ?es & Hcompile).
      destruct Hcompile as (Hunr & Hload1 & Hload2 & Hwt0 & Hwl0 & Hspec).
      inv_cg_bind Hload1 [] ?wt ?wt ?wl ?wl ?es ?es Hret Hload1.
      cbn in Hret.
      inversion Hret.
      subst wt4 wl4 es2.
      rewrite atoms_interp_one_inv.
      iDestruct "Hvs" as "(%v' & %Hv' & Hat)".
      inversion Hv'; subst v'; clear Hv'.
      iApply cwp_val_app.
      { instantiate (1 := [v]). apply Is_true_true. apply/andP; split => //. by apply/eqP. }
      admit.
      (*
      specialize (Hspec [] [] ltac:(eauto) ltac:(done)).
      clear_nils.
      iApply (Hspec with "[$] [$] [] [$Hat]").
      {
        iPureIntro; cbn.
        rewrite list_lookup_insert.
        by rewrite decide_True.
      }
      iIntros "!> Hf Hrun Hat".
      assert (Hκ'': ∃ σ ξ, has_kind F τ (MEMTYPE σ ξ)).
      {
        unfold ψ in Htype.
        inversion Htype; subst.
        destruct H as [Href _].
        rewrite Forall_singleton in Href.
        destruct Href as (ρ' & Hrep & Hmono).
        inversion Hrep; subst.
        eapply has_kind_ref_ty; eauto.
      }
      destruct Hκ'' as (σ & ξ & Hkindτ).
      pose proof Hkindτ as Hkag.
      pose proof (has_kind_inv _ _ _ Hkindτ) as Hhkindok.
      inversion Hhkindok as [F' τ'' κ'' Htyok Hkindok];
        subst F' κ'' τ''; clear Hhkindok.
      pose proof Hkindok as Hev.
      eapply eval_kind_ok_Some in Hev; last done.
      destruct Hev as (sk & Hev).
      pose proof Hsk as Hskag.
      eapply type_skind_has_kind_agree in Hskag; eauto.
      cbn in Hev.
      inversion Hkindok; subst.
      eapply eval_size_ok_Some in H1; eauto.
      destruct H1 as (n & Hevsz).
      rewrite Hevsz in Hev; cbn in Hev; inversion Hev; subst κ'; clear Hev.
      inversion Hsk; subst.
      assert (has_mono_size F (pr_target pr)).
      {
        admit.
      }
      assert (∃ k', type_sz se (fe_of_context F) (pr_target pr) = Some k')
        as [k' Hsztgt].
      {
        unfold type_sz.
        cbn.
        pose proof (has_mono_size_inv _ _ H) as (σ' & ξ' & k' & Hmono & Hkind & Hev).
        eapply has_kind_type_sz in Hkind; eauto.
        rewrite mono_size_eval_emp; eauto.
      }
      iAssert (value_interp rti sr se τ (SWords ws)) with "[Ht]" as "Hval".
      { rewrite type_interp_eq; iExists _; by iFrame. }
      eapply wp_mem_load_copy_mm in Hload1.
      destruct Hload1 as (_ & -> & -> & Hload).
      unfold atom_interp; iEval (cbn) in "Hat".
      iDestruct "Hat" as "(%n' & %n32 & %Hrep & -> & Hat')".
      iDestruct "Hinst" as "(%Hitys & (Hmm & Hgc & Hset & Hclr & Hreg & Hunreg) & Hinstfns & Htab & %Hmemm & %Hmemgc)".
      iEval (rewrite type_interp_eq) in "Hval".
      pose proof Hresolves as Hpath.
      inversion H as [? ? σtgt ξtgt' Hhktgt Htgtmono HF' HT]; subst.
      rewrite Hser in Hhktgt.
      inversion Hhktgt; subst; clear κ1.
      pose proof (mono_size_eval_emp_Some _ Htgtmono) as (ntgt & Hev).
      (* TODO generalize the defn of resolves_path_inv_sep to deal with the
      order of ref_flags here. it puts too many consraints *)
      eapply resolves_path_inv_sep in Hpath;
        try eapply Hser;
        try eapply Hev;
        try eapply Hoff;
        try rewrite Hser; try by eassumption.
      iEval (rewrite -type_interp_eq) in "Hval".
      iEval (unfold root_pointer_interp; cbn) in "Hat'".
      iPoseProof (Hpath with "Hval") as "(%Hwslen & Hval & Hcont)".
      clear Hpath.
      iEval (rewrite Hser) in "Hval".
      inversion Hhktgt.
      subst ξ0 τ0 ρ1 F0.
      pose proof (type_rep_has_kind_agree _ _ _ _ H3) as Hrep'.
      rewrite Hrep' in Hρ.
      inversion Hρ; subst ρ0.
      iEval (rewrite value_interp_eq; unfold add_skind_interp) in "Hval".
      iDestruct "Hval" as "(%sk & %Hvalk & %Hsval & %os & %Heq & Hval)".
      inversion Heq as [Hwords]; clear Heq.
      unfold eval_kind, type_skind in Hvalk; cbn -[eval_size] in Hvalk.
      erewrite eval_size_emptyenv  in Hvalk; last eapply Hev.
      cbn in Hvalk; inversion Hvalk; subst sk.
      iEval (rewrite type_interp_eq) in "Hval".
      iDestruct "Hval" as "(%sk & %Hvalk' & %Hsval' & Hval)".
      cbn in Hsval'.
      assert (Hkindok': kind_ok (fc_kind_ctx F) (VALTYPE ρ ξtgt')).
      {
        constructor.
        eauto.
        admit.
      }
      eapply eval_kind_ok_Some in Hkindok'; eauto.
      destruct Hkindok' as (sk' & Hkeval).
      eapply type_skind_has_kind_Some in H3; eauto.
      cbn in Hkeval.
      erewrite eval_rep_emptyenv in Hkeval; eauto.
      cbn in Hkeval; inversion Hkeval; subst sk'.
      rewrite H3 in Hvalk'; inversion Hvalk'; subst sk.
      destruct Hsval' as (Hhasareps & Hats).
      iDestruct "Hat'" as "(%rp & %Hrepn' & Haddr)".
      destruct rp as [| [|]]; try done.

      iPoseProof (virt_to_phys_acc with "Hrt Hℓh Haddr")
        as "((%ns & %ns_32 & %Hnsrep & Hphys & Hws) & Hphys_to_virt)".
      iPoseProof (big_sepL2_take_drop_acc _ _ ntgt off with "Hws") as "[Hws Hws_cont]".
      fold (get_path_words off ntgt ws).
      rewrite Hwords.
      assert (ref_flag_atoms_interp GCRefs (SAtoms os)). { admit. }
      assert (Forall2 N_i32_repr (take ntgt (drop off ns)) (take ntgt (drop off ns_32))).
      { admit. }
      iApply (Hload with "[$] [] [] [Hws] [Hphys] [$] [$] [-]").
      + admit.
      + eauto.
      + eauto.
      + unfold N_nat_repr.
        reflexivity.
      + eauto.
      + simpl.
        by rewrite list_lookup_insert_eq.
      + cbn.
        rewrite length_app length_cons.
        lia.
      + cbn.
        rewrite length_insert.
        rewrite Hflen.
        unfold locsz.
        cbn.
        rewrite sum_list_with_list_sum length_concat !length_app.
        cbn.
        lia.
      + unfold has_areps in Hhasareps.
        destruct Hhasareps as (os' & Hinv & Hhas). inversion Hinv; subst os'.
        eapply Hhas.
      + admit.
      + (* need lemma to establish congeal_atoms *)
        admit.
      + eauto.
      + admit. (* need to weaken load lemmas to use only parts of rt_token they care about *)
      + eauto.
      + unfold words_interp.
        admit.
      + (* use congeal_atoms to reinterpret Hphys *)
        (*
      need to relate
  [∗ list] off';v ∈ (seq.foldl (λ '(off', offs) (ι : atomic_rep), (off' + arep_size ι, seq.rcons offs off'))
                       (off, []) ιs).2;[VAL_int32 n32], ?Goal2↦[wms][?Goal1 + byte_offset MemMM off']
  bits v
        and the (get_path_words) function.

        The situation is this. If we have
           l ->heap ws
         then by opening up rt_invariant we get an underlying points-to to some
         values vs that can be loaded from along with some information saying ws
         is like vs.
         We need a lemma that goes from these facts (get_path_words ...) and
         (update_path_words ..) to corresponding decompositions of the
         underlying points-tos.
         Then we need another lemma that relates those decompositions to this
         nasty foldl (if it isn't already expressed in that form).
         *)
        unfold fe in Hρ; cbn in Hρ.
        admit.
      + iIntros (f'' e' vs') "-> Hown Htok #Hinst' Hpts Hpost".
        unfold fvs_combine.
        iFrame.
        iSplitR; [|iSplitL "Hframe"].
        * unfold frame_rel.
          cbn.
          iSplit; last by rewrite load_frame_inst.
          (* mask_locs_eq lmask ... mk_load1_frame *)
          admit.
        * unfold mk_load_frame.
          cbn [seq.foldl imap].
          unfold frame_interp.
          iDestruct "Hframe" as "(%ηss & %vss_L' & %vs_WL' & %fr' & Hframe)".
          iDestruct "Hframe" as "(%Hprims & %Hres & Hats & Hlocs)".
          iExists _, vss_L', _.
          iFrame.
          iPureIntro.
          intuition.
          -- cbn.
             unfold ptr_local.
             (* NOTE To Ryan: we added 'concat' in front of vss_L' since we changed frame_interp slightly *)
             assert (length $ concat vss_L' = length (concat (typing.fc_locals F))).
             { apply Forall2_concat in Hprims. by eapply Forall2_length in Hprims. }
             admit.
          -- unfold result_type_interp in Hres.
             unfold result_type_interp.
             admit.
        * unfold mk_load_post.
          iDestruct "Hpost" as "(%Hszvs & Hvs')".
          (* value interpretation goes here *)
          admit.
      *)
    - (* ref mm imm *)
      admit.
    - (* ref gc mut *)
      iDestruct "Href" as (ℓ fs Hsv) "Hinv".
      inversion Hsv; subst.
      (* need lemma about memory.load *)
      admit.
    - (* ref gc imm *)
      admit.
  Admitted.

End load_copy.
