From mathcomp Require Import eqtype ssrbool.

Require Import RichWasm.util.
Require Import RichWasm.compiler.memory.
Require Import RichWasm.iris.numerics.
Require Import RichWasm.iris.runtime.
Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.case_ptr.
Require Import RichWasm.iris.logrel.path.
Require Import RichWasm.iris.logrel.load_common.
Require Import RichWasm.iris.logrel.load_copy.
Require Import RichWasm.iris.logrel.roots.
Require Import RichWasm.iris.logrel.copy.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section load_copy.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  (* Lemma sum_list_with_list_sum {A} {f : A -> nat} {xs : list A} : *)
  (*   sum_list_with f xs = list_sum (map f xs). *)
  (* Proof. *)
  (*   induction xs. *)
  (*   - done. *)
  (*   - cbn. *)
  (*     by rewrite IHxs. *)
  (* Qed. *)

  (* inversion lemma for learning about tau given a Ref k mu tau *)
  (* Lemma has_kind_ref_ty F κ κ' μ β τ : *)
  (*   has_kind F (RefT κ μ β τ) κ' -> *)
  (*   ∃ σ ξ, *)
  (*     has_kind F τ (MEMTYPE σ ξ). *)
  (* Proof. *)
  (*   intros Hkind. *)
  (*   remember (RefT κ μ β τ) as τ0 eqn:Href. *)
  (*   revert Href. *)
  (*   revert κ μ. *)
  (*   induction Hkind; intros κ'' μ' Href; *)
  (*     try congruence. *)
  (*   - subst κ. inversion Href; subst. *)
  (*     by exists σ, ξ. *)
  (*   - subst κ. *)
  (*     inversion Href. *)
  (*     subst. *)
  (*     by exists σ, ξ. *)
  (*   - subst κ. *)
  (*     inversion Href. *)
  (*     subst. *)
  (*     by exists σ, ξ. *)
  (* Qed. *)

  (* Lemma mono_size_eval_emp_Some σ : *)
  (*   is_mono_size σ -> *)
  (*   is_Some (eval_size EmptyEnv σ). *)
  (* Proof. *)
  (*   intros Hmono. *)
  (*   induction σ using size_ind; inversion Hmono; subst. *)
  (*   - cbn in H1; lia. *)
  (*   - cbn. *)
  (*     rewrite !Forall_forall in H H2. *)
  (*     assert (is_Some (mapM (eval_size EmptyEnv) σs)) as (ns & ->); last done. *)
  (*     eapply mapM_is_Some_2, Forall_forall; intros; cbn. *)
  (*     eapply H; try eapply H2; eauto. *)
  (*   - cbn. *)
  (*     rewrite !Forall_forall in H H2. *)
  (*     assert (is_Some (mapM (eval_size EmptyEnv) σs)) as (ns & ->); last done. *)
  (*     eapply mapM_is_Some_2, Forall_forall; intros; cbn. *)
  (*     eapply H; try eapply H2; eauto. *)
  (*   - cbn. *)
  (*     eapply eval_rep_empty_ok_Some in H1. *)
  (*     by destruct H1 as (rep & ->). *)
  (*   - done. *)
  (* Qed. *)

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

  (* Lemma atom_interp_ptr_shaped ptr v : *)
  (*   atom_interp (PtrA ptr) v -∗ *)
  (*   ∃ n n32, ⌜N_i32_repr n n32⌝ ∗ *)
  (*            ⌜v = VAL_int32 n32⌝ ∗ *)
  (*            ⌜ptr_shaped ptr n⌝ ∗ *)
  (*            ∃ rp, ⌜repr_root_pointer rp n⌝ ∗ root_pointer_interp rp ptr. *)
  (* Proof. *)
  (*   iIntros "Hat". *)
  (*   destruct ptr; cbn; unfold root_pointer_interp. *)
  (*   - iDestruct "Hat" as "(%n' & %n32 & %Hn32 & %Hv & (%rp & %Hrp & Hrpn))". *)
  (*     destruct rp; last (destruct μ; done). *)
  (*     iDestruct "Hrpn" as "->". *)
  (*     inversion Hrp; subst. *)
  (*     iExists _, _. *)
  (*     iSplit; first eauto. *)
  (*     iSplit; first eauto. *)
  (*     iSplit; first eauto using ptr_shaped. *)
  (*     iExists (RootInt n); eauto. *)
  (*   - iDestruct "Hat" as "(%n' & %n32 & %Hn32 & %Hv & (%rp & %Hrp & Hrpn))"; subst. *)
  (*     destruct rp; first done. *)
  (*     inversion Hrp; subst. *)
  (*     destruct μ0, μ; try done. *)
  (*     + iExists _, _. *)
  (*       repeat (iSplit; first eauto using ptr_shaped). *)
  (*       iExists _; eauto. *)
  (*     + iExists _, _. *)
  (*       repeat (iSplit; first eauto using ptr_shaped). *)
  (*       iExists _; eauto. *)
  (* Qed. *)

  Lemma values_interp_app se τs1 τs2 os1 os2 :
    values_interp rti sr se τs1 os1 -∗
    values_interp rti sr se τs2 os2 -∗
    values_interp rti sr se (τs1 ++ τs2) (os1 ++ os2).
  Proof.
    iIntros "(%oss1 & -> & Hoss1)".
    iIntros "(%oss2 & -> & Hoss2)".
    iExists (oss1 ++ oss2).
    rewrite map_app concat_app.
    iSplit; first done.
    iPoseProof (big_sepL2_length with "Hoss1") as "%Hlen1".
    iPoseProof (big_sepL2_length with "Hoss2") as "%Hlen2".
    setoid_rewrite big_sepL2_app_same_length; last by eauto.
    by iFrame.
  Qed.

  Lemma forall_ptr_ser P o :
    forall_ptr_atom P o ->
    Forall (forall_ptr_word P) (serialize_atom o).
  Proof.
    destruct o; cbn; try solve [repeat constructor].
    rewrite Forall_singleton.
    done.
  Qed.

  Lemma Forall_forall_ptr_ser ξ os :
    Forall (forall_ptr_atom (ref_flag_ptr_interp ξ)) os ->
    Forall (forall_ptr_word (ref_flag_ptr_interp ξ)) (flat_map serialize_atom os).
  Proof.
    induction os as [| o os]; first done.
    intros Hos.
    inversion Hos; subst.
    cbn.
    rewrite Forall_app.
    eauto using forall_ptr_ser.
  Qed.

  Lemma mk_load_frame_locs F wl f vs_l vs0 vs vs_r :
    let fe := fe_of_context F in
    length vs_l = sum_list_with length (typing.fc_locals F) + length wl ->
    length vs = length vs0 ->
    f_locs f = vs_l ++ vs0 ++ vs_r ->
    f_locs (mk_load_frame (fe_of_context F) f wl vs) = vs_l ++ vs ++ vs_r.
  Proof.
    revert vs0 vs_r.
    induction vs as [|vs v] using seq.last_ind; cbn; intros * Hvss Hvs0 Hf.
    - destruct vs0; cbn in * ;try lia.
      done.
    - destruct vs0 using seq.last_ind;
        first (change @length with @seq.size in Hvs0;
                 by rewrite seq.size_rcons in Hvs0).
      change @length with @seq.size in Hvs0.
      unfold mk_load_frame in *.
      rewrite imap_rcons seq.foldl_rcons.
      rewrite !seq.size_rcons in Hvs0.
      cbn.
      setoid_rewrite IHvs;
        last (by rewrite Hf rcons_app -app_assoc);
        eauto.
      rewrite sum_list_with_list_sum.
      rewrite -length_concat.
      rewrite Nat.add_assoc.
      assert (length vs_l = length (concat (typing.fc_locals F)) + length wl) as Hvsslen.
      {
        rewrite !length_concat Hvss.
        by rewrite sum_list_with_list_sum.
      }
      rewrite -Hvsslen.
      rewrite insert_app_r; f_equal.
      rewrite app_assoc.
      rewrite insert_app_l; f_equal.
      + rewrite rcons_app.
        replace (length vs) with (length vs + 0) by lia.
        by rewrite insert_app_r.
      + rewrite length_app; cbn.
        lia.
  Qed.

  Lemma types_agree_val_interp t v :
    types_agree t v <-> value_type_interp t v.
  Proof.
    unfold types_agree, value_type_interp.
    destruct t, v; cbn;
      match goal with
      | |- is_true true <-> _ =>
          split; [eexists; eauto | done]
      | |- is_true false <-> _ =>
          split; [intros f; inversion f |
                  intros (v & Hv); inversion Hv ]
      end.
  Qed.


  Lemma load_restore_frame wl wlf1 wlf2 se F L ah32 vn32 fr ptr_local vs ιs :
    let wls := wl ++ T_i32 :: wlf1 ++ map translate_arep ιs ++ wlf2 in
    "Hframe" ∷ frame_interp rti sr se (typing.fc_locals F) L wls fr -∗
    "%Hptr_local" ∷ ⌜(ptr_local = sum_list_with length (typing.fc_locals F) + length wl)%nat⌝ -∗
    "%Hvs" ∷ ⌜Forall2 (λ ι v, types_agree (translate_arep ι) v) ιs vs⌝ -∗
    frame_interp rti sr se (typing.fc_locals F) L wls
      (mk_load_frame (fe_of_context F)
        {|
          W.f_locs :=
            <[localimm (Mk_localidx ptr_local):=VAL_int32 ah32]>
              (f_locs {| W.f_locs := <[ptr_local:=VAL_int32 vn32]> (f_locs fr); W.f_inst := f_inst fr |});
          W.f_inst := f_inst {| W.f_locs := <[ptr_local:=VAL_int32 vn32]> (f_locs fr); W.f_inst := f_inst fr |}
        |} (wl ++ [T_i32] ++ wlf1) vs).
  Proof.
    iIntros (wls).
    repeat iIntros "@".
    unfold frame_interp.
    iDestruct "Hframe" as "(%ηss & %vss_L' & %vs_WL' & %fr' & Hframe)".
    iDestruct "Hframe" as "(%Hprims & %Hres & Hats & Hlocs)".
    apply Forall2_app_inv_l in Hres.
    destruct Hres as (vs1 & vs' & Hvs1 & Hvs' & ->).
    apply Forall2_cons_inv_l in Hvs'.
    destruct Hvs' as (v1 & vs'' & Hv1 & Hvs'' & ->).
    change (v1 :: vs'') with ([v1] ++ vs'') in *.
    apply Forall2_app_inv_l in Hvs''.
    destruct Hvs'' as (?vs & ?vs & ?Hvs & ?Hv1 & ->).
    apply Forall2_app_inv_l in Hv0.
    destruct Hv0 as (?vs & ?vs & ?Hvs & ?Hvs & ->).
    subst ptr_local.
    pose proof Hvs as Hvslen; apply Forall2_length in Hvslen.
    pose proof Hvs0 as Hvs0len; apply Forall2_length in Hvs0len.
    pose proof Hvs1 as Hvs1len; apply Forall2_length in Hvs1len.
    pose proof Hvs2 as Hvs3len; apply Forall2_length in Hvs3len.
    pose proof Hvs3 as Hvs4len; apply Forall2_length in Hvs4len.
    pose proof Hprims as Hvsslen. apply Forall2_Forall2_length in Hvsslen.
    iExists _, vss_L', _.
    iFrame.
    iPureIntro.
    intuition.
    - assert (map length vss_L' = map length (typing.fc_locals F)) as Hvss.
      { apply Forall2_Forall2_length in Hprims. congruence. }
      cbn.
      erewrite mk_load_frame_locs.
      + instantiate (2 := vs4).
        instantiate (2 := concat vss_L' ++ vs1 ++ [VAL_int32 ah32] ++ vs0).
        instantiate (1 := vs1 ++ [VAL_int32 ah32] ++ vs0 ++ vs ++ vs4).
        rewrite -!app_assoc.
        cbn.
        f_equal.
      + rewrite !length_app !length_cons length_concat.
        rewrite Hvss sum_list_with_list_sum; cbn.
        lia.
      + instantiate (1 := vs3).
        by rewrite -Hvs3len -Hvslen length_map.
      + cbn -[app].
        rewrite fr'.
        rewrite !Hvs1len.
        rewrite !sum_list_with_list_sum -!Hvss -length_concat.
        repeat rewrite insert_app_r.
        cbn [app].
        rewrite insert_app_r_alt; last done.
        rewrite insert_app_r_alt; last done.
        rewrite !Nat.sub_diag; cbn.
        by rewrite -!app_assoc; cbn.
    - unfold result_type_interp, wls.
      cbn [app].
      repeat (constructor || apply Forall2_app); eauto.
      + (* val_interp for ah32 *)
        eexists; eauto.
      + (* val_interps for vs *)
        rewrite Forall2_fmap_l.
        eapply Forall2_impl; first eapply Hvs.
        intros ι v Hv.
        by rewrite types_agree_val_interp in Hv.
  Qed.

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
    iEval (rewrite value_interp_eq) in "Hos".
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
      rewrite Hser.
      eapply pr_target_kind in Hresolves'; eauto using KSer.
      destruct Hresolves' as (ktgt & Hkind).
      rewrite Hser in Hkind.
      inversion Hkind; subst.
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
    assert (Hκ: eval_rep se (AtomR PtrR) = Some l).
    {
      destruct Htype as [Hmono Hctx].
      destruct Hmono as [Hmono _].
      rewrite Forall_singleton in Hmono.
      destruct Hmono as (ρ' & Hrep & Hismono).
      inversion Hrep as [a b c d Href]; subst.
      cbn.
      apply rep_ref_kind_ptr in Href; subst.
      destruct Href as [-> [χ' ->]].
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
    iEval (cbn -[type_interp]) in "Href".
    destruct (eval_mem se μ) as [[|]|] eqn:Hevmem; last done; destruct β.

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
      iPoseProof (atom_interp_ptr_shaped with "Hat") as "(%vn & %vn32 & %Hvn & -> & %Hvshp & %rp & %Hrpvn & Hrp)".
      specialize (Hspec [] [] (PtrHeap MemMM ℓ) vn vn32 ltac:(eauto)).
      specialize (Hspec ltac:(auto) ltac:(auto) ltac:(auto)).
      clear_nils.
      iApply (Hspec with "[$] [$] []").
      {
        iPureIntro; cbn.
        rewrite list_lookup_insert.
        by rewrite decide_True.
      }
      iIntros "!> Hf Hrun".
      assert (Hκ'': ∃ σ ξ, has_kind F τ (MEMTYPE σ ξ)).
      {
        unfold ψ in Htype.
        inversion Htype; subst.
        destruct H0 as [Href _].
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
      pose proof Hev as Hev'.
      cbn in Hev.
      inversion Hkindok; subst σ0 ξ0 K κ'.
      eapply eval_size_ok_Some in H2; eauto.
      destruct H2 as (n & Hevsz).
      rewrite Hevsz in Hev; cbn in Hev; inversion Hev; clear Hev.
      subst.
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
      iDestruct "Hinst" as "(%Hitys & (Hmm & Hgc & Hset & Hclr & Hreg & Hunreg) & Hinstfns & Htab & %Hmemm & %Hmemgc)".
      iEval (rewrite type_interp_eq) in "Hval".
      pose proof Hresolves as Hpath.
      inversion H as [? ? σtgt ξtgt' Hhktgt Htgtmono HF' HT]; subst.
      rewrite Hser in Hhktgt.
      inversion Hhktgt; subst; clear κ1.
      pose proof (mono_size_eval_emp_Some _ Htgtmono) as (ntgt & Hev).
      eapply resolves_path_inv_sep_weak in Hpath;
        try eapply Hser;
        try eapply Hev;
        try eapply Hoff;
        try rewrite Hser; try by eassumption.
      iEval (rewrite -type_interp_eq) in "Hval".
      iEval (unfold root_pointer_interp; cbn) in "Hrp".
      destruct rp as [| [|]]; [ done | | done].
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
        match goal with
        | H : has_kind _ _ (VALTYPE ρ ξtgt') |- _ =>
            eapply has_kind_inv in H; now inversion H
        end.
      }
      eapply eval_kind_ok_Some in Hkindok'; eauto.
      destruct Hkindok' as (sk' & Hkeval).
      eapply type_skind_has_kind_Some in H3; eauto.
      pose proof Hkeval as Hkeval'.
      cbn in Hkeval.
      erewrite eval_rep_emptyenv in Hkeval; eauto.
      cbn in Hkeval; inversion Hkeval; subst sk'.
      rewrite H3 in Hvalk'; inversion Hvalk'; subst sk.
      destruct Hsval' as (Hhasareps & Hats).
      iPoseProof (frame_interp_locs_len with "Hframe") as "%Hfrlen".
      destruct Hhasareps as (os' & Hos' & Hhasareps).
      inversion Hos'; subst os'.
      inversion Hvshp; subst.
      inversion Hrpvn.
      assert ((4 <= a0)%N);
        first by eapply mod_bound_nonzero.
      assert ((4 <= a)%N);
        first by eapply mod_bound_nonzero.
      replace a0 with a in * by lia; clear a0; subst.
      iPoseProof (Hload with "[$]") as "Hload"; clear Hload.
      repeat (iSpecialize ("Hload" with "[$]") || iSpecialize ("Hload" with "[//]")).
      iApply "Hload".
      + iPureIntro.
        revert Hev.
        cbn.
        rewrite Hιs.
        cbn.
        intros U; inversion U; subst ntgt.
        erewrite sum_list_with_list_sum.
        done.
      + eauto.
      + iPureIntro.
        eapply ser_offsets; eauto.
      + eauto.
      + iPureIntro.
        cbn.
        rewrite length_insert Hfrlen.
        rewrite !length_app !length_cons !length_concat.
        rewrite !length_app sum_list_with_list_sum.
        lia.
      + simpl.
        by rewrite list_lookup_insert_eq.
      + cbn.
        rewrite length_app length_cons.
        iPureIntro.
        lia.
      + eauto.
      + eauto.
      + eauto.
      + eauto.
      + eauto.
      + eauto.
      + iIntros (f'' vs vsf) "->".
        repeat iIntros "@".
        unfold fvs_combine.
        iAssert (type_interp rti sr τval se (SAtoms os)) with "[Hval]" as "Hval".
        {
          rewrite type_interp_eq.
          iExists _.
          iFrame.
          iPureIntro; intuition eauto.
          split; eauto.
          exists os; eauto.
        }
        iPoseProof (type_dup with "Hval") as "[Hval Hval']"; eauto.
        {
          cbn. eauto.
          destruct Hcopyability as (? & Hlek & Hlegc).
          eapply has_kind_agree in Hlek; [|clear Hlek; eauto].
          rewrite -Hlek in Hlegc.
          cbn in Hlegc.
          eapply ref_flag_le_trans; eauto.
        }
        iFrame.
        iSplitR; [|iSplitL "Hframe"].
        * unfold frame_rel.
          cbn.
          iSplit; last by rewrite load_frame_inst.
          iPureIntro; intros i Hmask.
          destruct Hmask as [Hub Hlb].
          rewrite fe_wlocal_offset_length in Hlb.
          rewrite length_concat in Hlb.
          rewrite mk_load_frame_stable_part; cbn.
          {
            rewrite list_lookup_insert.
            unfold ptr_local.
            rewrite decide_False; first done.
            intros [<- Hbd].
            rewrite sum_list_with_list_sum in Hlb.
            lia.
          }
          rewrite sum_list_with_list_sum length_app.
          lia.
        * unfold frame_interp.
          iDestruct "Hframe" as "(%ηss & %vss_L' & %vs_WL' & %fr' & Hframe)".
          iDestruct "Hframe" as "(%Hprims & %Hres & Hats & Hlocs)".
          apply Forall2_app_inv_l in Hres.
          destruct Hres as (vs1 & vs' & Hvs1 & Hvs' & ->).
          apply Forall2_cons_inv_l in Hvs'.
          destruct Hvs' as (v1 & vs'' & Hv1 & Hvs'' & ->).
          apply Forall2_app_inv_l in Hvs''.
          destruct Hvs'' as (?vs & ?vs & ?Hv & ?Hv1 & ->).
          apply Forall2_app_inv_l in Hv.
          destruct Hv as (?vs & ?vs & ?Hvs & ?Hvs & ->).
          apply Forall2_app_inv_l in Hvs0.
          destruct Hvs0 as (?vs & ?vs & ?Hvs & ?Hvs & ->).
          unfold ptr_local.
          iExists _, vss_L', _.
          iFrame.
          iPureIntro.
          intuition.
          -- assert (map length vss_L' = map length (typing.fc_locals F)).
             { apply Forall2_Forall2_length in Hprims. congruence. }
             instantiate (1 := vs1 ++ VAL_int32 vn32 :: vs3 ++ vsf ++ vs5 ++ vs2).
             repeat match goal with
                    | |- _ = ?a1 ++ vsf ++ ?B => fail 1
                    | |- _ = ?a1 ++ ?a2 :: ?a3 =>
                        change (a1 ++ a2 :: a3) with (a1 ++ [a2] ++ a3)
                    | |- _ = ?a1 ++ ?a2 ++ ?a3 => rewrite (app_assoc a1 a2 a3)
                    end.
             erewrite mk_load_frame_locs; first f_equal.
             ++ rewrite -app_assoc !length_app !length_concat sum_list_with_list_sum.
                rewrite H0.
                erewrite (Forall2_length _ wl1), (Forall2_length _ wl) by eauto.
                cbn; lia.
             ++ instantiate (1 := vs0).
                rewrite -(Forall2_length _ _ _ Hvs0).
                rewrite -(Forall2_length _ _ _ Hvsf).
                rewrite length_map.
                done.
             ++ unfold f'.
                cbn.
                rewrite fr'.
                unfold ptr_local.
                rewrite sum_list_with_list_sum -H0 -length_concat.
                rewrite insert_app_r.
                erewrite (Forall2_length _ wl) by eauto.
                replace (length vs1) with (length vs1 + 0) by lia.
                rewrite insert_app_r; cbn.
                by rewrite -!app_assoc.
          -- apply Forall2_app; eauto.
             apply Forall2_cons; split; eauto.
             ++ unfold value_type_interp; eauto.
             ++ rewrite -!app_assoc.
                repeat (apply Forall2_app; eauto).
                rewrite Forall2_fmap_l.
                eapply Forall2_impl; first eapply Hvsf.
                setoid_rewrite types_agree_val_interp.
                done.
        * iExists (PtrA (PtrHeap MemMM ℓ) :: os).
          change [RefT κ μ Mut τ; τval] with ([RefT κ μ Mut τ] ++ [τval]).
          change (PtrA (PtrHeap MemMM ℓ) :: os) with ([PtrA (PtrHeap MemMM ℓ)] ++ os).
          iSpecialize ("Hcont" $! (get_path_words off ntgt ws) with "[] [Hval]").
          {
            iPureIntro.
            cbn in Hsval.
            destruct Hsval as [Hntgt _].
            congruence.
          }
          {
            rewrite Hser value_interp_eq.
            iExists (SMEMTYPE _ ξtgt').
            iSplitR; last iSplitR.
            + iPureIntro.
              cbn.
              erewrite eval_rep_emptyenv; last eauto.
              done.
            + cbn.
              rewrite Hwords.
              iSplit.
              * erewrite <-has_areps_size; last eauto.
                rewrite length_flat_map; done.
              * eauto using Forall_forall_ptr_ser.
            + iExists os.
              rewrite Hwords.
              by iFrame.
          }
          rewrite update_get_path_id; last lia.
          iSplitL "Hval' Hcont Hℓl Hptr".
          {
            iApply (values_interp_app with "[Hcont Hℓl Hptr] [Hval']").
            - iExists [_]; cbn; rewrite app_nil_r.
              iSplit; first eauto.
              iSplitL; last done.
              rewrite type_interp_eq.
              rewrite type_interp_eq.
              iExists (SVALTYPE _ _).
              iSplitR; [|iSplitR].
              + eauto.
              + cbn.
                iSplit.
                * iPureIntro.
                  exists [PtrA (PtrHeap MemMM ℓ)]; intuition.
                  constructor; cbn; done.
                * by cbn.
              + iEval (cbn).
                rewrite Hevmem.
                iExists ℓ, fs, ws.
                rewrite type_interp_eq.
                by iFrame.
            - iExists [os].
              iSplitR; first (cbn; clear_nils; done).
              rewrite big_sepL2_singleton.
              done.
          }
          setoid_rewrite big_sepL2_cons; cbn [const].
          iSplitL "Haddr"; first (iExists _, _; eauto).
          iApply gcrefs_atoms_copyable; eauto.
          destruct Hcopyability as (κ' & Hcopyk & Hle).
          by pose proof (has_kind_agree _ _ _ _ Hcopyk ltac:(eassumption)); subst.

    - iDestruct "Href" as (ℓ fs ws Hsv) "(#Hinv & Hws)".
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
      iPoseProof (atom_interp_ptr_shaped with "Hat") as "(%vn & %vn32 & %Hvn & -> & %Hvshp & %rp & %Hrpvn & Hrp)".
      specialize (Hspec [] [] (PtrHeap MemMM ℓ) vn vn32 ltac:(eauto)).
      specialize (Hspec ltac:(auto) ltac:(auto) ltac:(auto)).
      clear_nils.
      iApply (Hspec with "[$] [$] []").
      {
        iPureIntro; cbn.
        rewrite list_lookup_insert.
        by rewrite decide_True.
      }
      iIntros "!> Hf Hrun".
      assert (Hκ'': ∃ σ ξ, has_kind F τ (MEMTYPE σ ξ)).
      {
        unfold ψ in Htype.
        inversion Htype; subst.
        destruct H0 as [Href _].
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
      pose proof Hev as Hev'.
      cbn in Hev.
      inversion Hkindok; subst σ0 ξ0 K κ'.
      eapply eval_size_ok_Some in H2; eauto.
      destruct H2 as (n & Hevsz).
      rewrite Hevsz in Hev; cbn in Hev; inversion Hev; clear Hev.
      inversion Hsk; subst.
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
      iDestruct "Hinst" as "(%Hitys & (Hmm & Hgc & Hset & Hclr & Hreg & Hunreg) & Hinstfns & Htab & %Hmemm & %Hmemgc)".
      iEval (rewrite type_interp_eq) in "Hval".
      pose proof Hresolves as Hpath.
      inversion H as [? ? σtgt ξtgt' Hhktgt Htgtmono HF' HT]; subst.
      rewrite Hser in Hhktgt.
      inversion Hhktgt; subst; clear κ1.
      pose proof (mono_size_eval_emp_Some _ Htgtmono) as (ntgt & Hev).
      eapply resolves_path_inv_sep_weak in Hpath;
        try eapply Hser;
        try eapply Hev;
        try eapply Hoff;
        try rewrite Hser; try by eassumption.
      iEval (rewrite -type_interp_eq) in "Hval".
      iEval (unfold root_pointer_interp; cbn) in "Hrp".
      destruct rp as [| [|]]; [ done | | done].
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
        match goal with
        | H : has_kind _ _ (VALTYPE ρ ξtgt') |- _ =>
            eapply has_kind_inv in H; now inversion H
        end.
      }
      eapply eval_kind_ok_Some in Hkindok'; eauto.
      destruct Hkindok' as (sk' & Hkeval).
      eapply type_skind_has_kind_Some in H3; eauto.
      pose proof Hkeval as Hkeval'.
      cbn in Hkeval.
      erewrite eval_rep_emptyenv in Hkeval; eauto.
      cbn in Hkeval; inversion Hkeval; subst sk'.
      rewrite H3 in Hvalk'; inversion Hvalk'; subst sk.
      destruct Hsval' as (Hhasareps & Hats).
      iPoseProof (frame_interp_locs_len with "Hframe") as "%Hfrlen".
      destruct Hhasareps as (os' & Hos' & Hhasareps).
      inversion Hos'; subst os'.
      inversion Hvshp; subst.
      inversion Hrpvn.
      assert ((4 <= a0)%N);
        first by eapply mod_bound_nonzero.
      assert ((4 <= a)%N);
        first by eapply mod_bound_nonzero.
      replace a0 with a in * by lia; clear a0; subst.
      iApply fupd_cwp.
      iMod (na_inv_acc with "Hinv Hown") as "U"; eauto.
      iDestruct "U" as "([Hℓl Hℓh] & Hown & Hcloseℓ)".
      set (E' := (⊤ ∖ ↑ns_ref ℓ)) in *.
      assert (↑ns_fun (N.of_nat (sr_func_registerroot sr)) ⊆ E')
        by eauto with ndisj.
      iMod "Hℓh".
      iMod "Hℓl".
      iPoseProof (Hload _ _ _ _ _ _ E' with "[$]") as "Hload"; clear Hload.
      repeat (iSpecialize ("Hload" with "[$]") || iSpecialize ("Hload" with "[//]")).
      iApply (cwp_wand_strong with "[Hload]"); first iApply "Hload".
      + iPureIntro.
        revert Hev.
        cbn.
        rewrite Hιs.
        cbn.
        intros U; inversion U; subst ntgt.
        erewrite sum_list_with_list_sum.
        done.
      + eauto.
      + iPureIntro.
        eapply ser_offsets; eauto.
      + eauto.
      + iPureIntro.
        cbn.
        rewrite length_insert Hfrlen.
        rewrite !length_app !length_cons !length_concat.
        rewrite !length_app sum_list_with_list_sum.
        lia.
      + simpl.
        by rewrite list_lookup_insert_eq.
      + cbn.
        rewrite length_app length_cons.
        iPureIntro.
        lia.
      + eauto.
      + eauto.
      + eauto.
      + eauto.
      + eauto.
      + eauto.
      + iIntros (f'' vs vsf) "->".
        repeat iIntros "@".
        unfold fvs_combine.
        let Q := open_constr:(_ : iProp Σ) in
        instantiate (1 :=
          (λ f0 vs0, ∃ vs vsf,
             ⌜f0 = (mk_load_frame (fe_of_context F) f' (wl ++ [T_i32] ++ wl1) vsf)⌝ ∗
             ⌜vs0 = vs⌝ ∗
             ⌜Forall2 (λ (ι : atomic_rep) (vf : value), types_agree (translate_arep ι) vf) ιs vsf⌝ ∗
             ([∗ list] o;v ∈ os;vs, ⌜atom_copyable o⌝ -∗ atom_interp o v) ∗
             rt_token rti sr lpall θ ∗
             Q
          )%I).
        iExists vs, vsf.
        iSplit; first done.
        iSplit; first done.
        iSplit; first done.
        iSplitL "Hos"; first done.
        iSplitL "Htok"; first done.
        iNamedAccu.
      + eauto.
      + eauto.
      + iIntros "!>".
        iIntros (f v) "(%vs & %vsf & -> & ->  & %Hag & Hcopy & Htok & @ & @ & @ & @)".
        iPoseProof ("Hcloseℓ" with "[$]") as "Hown".
        iMod "Hown".
        iIntros "!>".
        unfold fvs_combine.
        iAssert (type_interp rti sr τval se (SAtoms os)) with "[Hval]" as "Hval".
        {
          rewrite type_interp_eq.
          iExists _.
          iFrame.
          iPureIntro; intuition eauto.
          split; eauto.
          exists os; eauto.
        }
        iPoseProof (type_dup with "Hval") as "[Hval Hval']"; eauto.
        {
          cbn. eauto.
          destruct Hcopyability as (? & Hlek & Hlegc).
          eapply has_kind_agree in Hlek; [|clear Hlek; eauto].
          rewrite -Hlek in Hlegc.
          cbn in Hlegc.
          eapply ref_flag_le_trans; eauto.
        }
        iFrame.
        iSplitR; [|iSplitL "Hframe"].
        * unfold frame_rel.
          cbn.
          iSplit; last by rewrite load_frame_inst.
          iPureIntro; intros i Hmask.
          destruct Hmask as [Hub Hlb].
          rewrite fe_wlocal_offset_length in Hlb.
          rewrite length_concat in Hlb.
          rewrite mk_load_frame_stable_part; cbn.
          {
            rewrite list_lookup_insert.
            unfold ptr_local.
            rewrite decide_False; first done.
            intros [<- Hbd].
            rewrite sum_list_with_list_sum in Hlb.
            lia.
          }
          rewrite sum_list_with_list_sum length_app.
          lia.
        * unfold frame_interp.
          iDestruct "Hframe" as "(%ηss & %vss_L' & %vs_WL' & %fr' & Hframe)".
          iDestruct "Hframe" as "(%Hprims & %Hres & Hats & Hlocs)".
          apply Forall2_app_inv_l in Hres.
          destruct Hres as (vs1 & vs' & Hvs1 & Hvs' & ->).
          apply Forall2_cons_inv_l in Hvs'.
          destruct Hvs' as (v1 & vs'' & Hv1 & Hvs'' & ->).
          apply Forall2_app_inv_l in Hvs''.
          destruct Hvs'' as (?vs & ?vs & ?Hv & ?Hv1 & ->).
          apply Forall2_app_inv_l in Hv.
          destruct Hv as (?vs & ?vs & ?Hvs & ?Hvs & ->).
          apply Forall2_app_inv_l in Hvs0.
          destruct Hvs0 as (?vs & ?vs & ?Hvs & ?Hvs & ->).
          unfold ptr_local.
          iExists _, vss_L', _.
          iFrame.
          iPureIntro.
          intuition.
          -- assert (map length vss_L' = map length (typing.fc_locals F)).
             { apply Forall2_Forall2_length in Hprims. congruence. }
             instantiate (1 := vs1 ++ VAL_int32 vn32 :: vs3 ++ vsf ++ vs5 ++ vs2).
             repeat match goal with
                    | |- _ = ?a1 ++ vsf ++ ?B => fail 1
                    | |- _ = ?a1 ++ ?a2 :: ?a3 =>
                        change (a1 ++ a2 :: a3) with (a1 ++ [a2] ++ a3)
                    | |- _ = ?a1 ++ ?a2 ++ ?a3 => rewrite (app_assoc a1 a2 a3)
                    end.
             erewrite mk_load_frame_locs; first f_equal.
             ++ rewrite -app_assoc !length_app !length_concat sum_list_with_list_sum.
                rewrite H1.
                erewrite (Forall2_length _ wl1), (Forall2_length _ wl) by eauto.
                cbn; lia.
             ++ instantiate (1 := vs0).
                rewrite -(Forall2_length _ _ _ Hvs0).
                rewrite -(Forall2_length _ _ _ Hag).
                rewrite length_map.
                done.
             ++ unfold f'.
                cbn.
                rewrite fr'.
                unfold ptr_local.
                rewrite sum_list_with_list_sum -H1 -length_concat.
                rewrite insert_app_r.
                erewrite (Forall2_length _ wl) by eauto.
                replace (length vs1) with (length vs1 + 0) by lia.
                rewrite insert_app_r; cbn.
                by rewrite -!app_assoc.
          -- apply Forall2_app; eauto.
             apply Forall2_cons; split; eauto.
             ++ unfold value_type_interp; eauto.
             ++ rewrite -!app_assoc.
                repeat (apply Forall2_app; eauto).
                rewrite Forall2_fmap_l.
                eapply Forall2_impl; first eapply Hag.
                setoid_rewrite types_agree_val_interp.
                done.
        * iExists (PtrA (PtrHeap MemMM ℓ) :: os).
          change [RefT κ μ Imm τ; τval] with ([RefT κ μ Imm τ] ++ [τval]).
          change (PtrA (PtrHeap MemMM ℓ) :: os) with ([PtrA (PtrHeap MemMM ℓ)] ++ os).
          iSpecialize ("Hcont" $! (get_path_words off ntgt ws) with "[] [Hval]").
          {
            iPureIntro.
            cbn in Hsval.
            destruct Hsval as [Hntgt _].
            congruence.
          }
          {
            rewrite Hser value_interp_eq.
            iExists (SMEMTYPE _ ξtgt').
            iSplitR; last iSplitR.
            + iPureIntro.
              cbn.
              erewrite eval_rep_emptyenv; last eauto.
              done.
            + cbn.
              rewrite Hwords.
              iSplit.
              * erewrite <-has_areps_size; last eauto.
                rewrite length_flat_map; done.
              * eauto using Forall_forall_ptr_ser.
            + iExists os.
              rewrite Hwords.
              by iFrame.
          }
          rewrite update_get_path_id; last lia.
          iSplitL "Hval' Hcont".
          {
            iApply (values_interp_app with "[Hcont] [Hval']").
            - iExists [_]; cbn; rewrite app_nil_r.
              iSplit; first eauto.
              iSplitL; last done.
              rewrite type_interp_eq.
              rewrite type_interp_eq.
              iExists (SVALTYPE _ _).
              iSplitR; [|iSplitR].
              + eauto.
              + cbn.
                iSplit.
                * iPureIntro.
                  exists [PtrA (PtrHeap MemMM ℓ)]; intuition.
                  constructor; cbn; done.
                * by cbn.
              + iEval (cbn).
                rewrite Hevmem.
                iExists ℓ, fs, ws.
                rewrite type_interp_eq.
                eauto.
            - iExists [os].
              iSplitR; first (cbn; clear_nils; done).
              rewrite big_sepL2_singleton.
              done.
          }
          setoid_rewrite big_sepL2_cons; cbn [const].
          iSplitL "Haddr"; first (iExists _, _; eauto).
          iApply gcrefs_atoms_copyable; eauto.
          destruct Hcopyability as (κ' & Hcopyk & Hle).
          by pose proof (has_kind_agree _ _ _ _ Hcopyk ltac:(eassumption)); subst.

    - (* ref gc mut *)
      iDestruct "Hinst" as "(%Hitys & (Hmm & Hgc & Hset & Hclr & Hreg & Hunreg) & Hinstfns & Htab & %Hmemm & %Hmemgc)".
      iDestruct "Href" as (ℓ fs Hsv) "#Hinv".
      inversion Hsv; subst p; clear Hsv.
      change (?x :: ?y :: ?z) with ([x; y] ++ z).
      set (f' := {| f_locs := <[ptr_local:=v ]> (f_locs fr);
                    f_inst := f_inst fr |}).
      iApply (cwp_seq with "[Hfr Hrun]").
      {
        change ([?ev; ?x]) with ([ev] ++ [x]).
        rewrite (has_values_to_consts_inv _ _ Hevs).
        iApply (cwp_local_tee with "[] [$] [$]"); first eauto.
        instantiate (1:= λ f'' vs', (⌜f'' = f' /\ vs' = [v]⌝)%I).
        by iFrame.
      }
      iIntros (f vs) "[-> ->] Hf Hrun".
      eapply cwp_case_ptr in Hcompile.
      destruct Hcompile as (?wt & ?wt & ?wt & ?wl & ?wl & ?wl & ?es & ?es & ?es & Hcompile).
      destruct Hcompile as (Hunr & Hload1 & Hload2 & Hwt0 & Hwl0 & Hspec).
      rewrite atoms_interp_one_inv.
      iDestruct "Hvs" as "(%v' & %Hv' & Hat)".
      inversion Hv'; subst v'; clear Hv'.
      iApply cwp_val_app.
      { instantiate (1 := [v]). apply Is_true_true. apply/andP; split => //. by apply/eqP. }
      iPoseProof (atom_interp_ptr_shaped with "Hat") as "(%vn & %vn32 & %Hvn & -> & %Hvshp & %rp & %Hrpvn & Hrp)".
      destruct rp as [|[|]]; try (iEval (cbn) in "Hrp"; done).
      specialize (Hspec [] [] (PtrHeap MemGC ℓ) vn vn32 ltac:(eauto)).
      specialize (Hspec ltac:(auto) ltac:(auto) ltac:(auto)).
      clear_nils.
      iApply (Hspec with "[$] [$] []").
      {
        iPureIntro; cbn.
        rewrite list_lookup_insert.
        by rewrite decide_True.
      }
      iIntros "!> Hf Hrun".
      assert (Hκ'': ∃ σ ξ, has_kind F τ (MEMTYPE σ ξ)).
      {
        unfold ψ in Htype.
        inversion Htype; subst.
        destruct H0 as [Href _].
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
      iApply fupd_cwp.
      iMod (na_inv_acc with "Hinv Hown") as "U"; eauto.
      iDestruct "U" as "[ (%ws & Hfs & Hhp & Hws) [Hown Hclose]]".
      iModIntro.
      iMod "Hfs".
      iMod "Hhp".
      set (E' := (⊤ ∖ ↑ns_ref ℓ)) in *.
      assert (↑ns_fun (N.of_nat (sr_func_registerroot sr)) ⊆ E')
        by eauto with ndisj.
      destruct Hev as (sk & Hev).
      inversion Hkindok; subst.
      eapply eval_size_ok_Some in H3; eauto; destruct H3 as (n & Hevsz).
      cbn in Hev.
      rewrite Hevsz in Hev; cbn in Hev; inversion Hev; clear Hev.
      subst sk.
      assert (∃ k', type_sz se (fe_of_context F) (pr_target pr) = Some k')
        as [k' Hsztgt].
      {
        unfold type_sz.
        cbn.
        pose proof (has_mono_size_inv _ _ H) as (σ' & ξ' & k' & Hmono & Hkind & Hev).
        eapply has_kind_type_sz in Hkind; eauto.
        rewrite mono_size_eval_emp; eauto.
      }
      inv_cg_bind Hload2 [] ?wt ?wt ?wl ?wl  ?es_root_hp ?es_load Hcgroot Hcgload.
      inversion Hrpvn.
      iEval (cbn) in "Hrp".
      open_rt "Hrt".
      (* Now: use path lemma to grab the important slice of Hws *)
      (* first, setting up some pure premises for the path lemma *)
      unfold type_sz in Hsztgt.
      assert (∃ ρtgt ξtgt,
                 has_kind F (pr_target pr) κser /\
                 has_kind F τval (VALTYPE ρtgt ξtgt) /\
                 is_mono_size (RepS ρtgt) /\
                 ρ = ρtgt /\
                 κser = MEMTYPE (RepS ρtgt) ξtgt)
        as (ρtgt & ξtgt & Htgt & Hval & Hmono & -> & ->).
      {
        inversion H; subst.
        rename σ0 into σtgt.
        rename ξ0 into ξtgt.
        rewrite Hser in H6.
        inversion H6; subst.
        unfold fe in Hρ.
        unfold fe_of_context in Hρ; cbn in Hρ.
        erewrite type_rep_has_kind_agree in Hρ; last eauto.
        inversion Hρ.
        do 2 eexists.
        by rewrite Hser.
      }
      pose proof Hmono as Hevm.
      eapply mono_size_eval_emp_Some in Hevm.
      destruct Hevm as (m & Hevm).
      (* Applying the path lemma. Since Hws is under a later modality, we only
         get the result under a later modality. *)
      eapply resolves_path_inv_sep_weak in Hresolves; eauto.
      iPoseProof (Hresolves with "Hws") as "(Hws1 & Hws & Hclose_slice)".

      iApply (cwp_seq with "[Hf Hrun Hrp Hws Hroot Hrootmem Hws1 Hclose_slice]").
      {
        eapply wp_root_to_heap in Hcgroot; try eauto.
        iApply (Hcgroot with "[$] [$] [] [] [$] [$] [$] [-]").
        - cbn.
          iPureIntro.
          by rewrite list_lookup_insert_eq.
        - eauto.
        - iIntros "!> !> !> %ah %ah32 %Hah32 %Hrep Hroot Hrm Hrmem".
          instantiate (1 := (λ f0 vs0,
            ∃ ah ah32,
             ⌜N_i32_repr ah ah32⌝ ∗
             ⌜repr_pointer θ (PtrHeap MemGC ℓ) ah⌝ ∗
             ⌜f0 = {| W.f_locs := <[localimm (Mk_localidx ptr_local):=VAL_int32 ah32]> (f_locs f'); W.f_inst := f_inst f' |}⌝ ∗
             ⌜vs0 = []⌝ ∗
             _)%I).
          iExists ah, ah32.
          iSplit; first done.
          iSplit; first done.
          iSplit; first done.
          iSplit; first done.
          iNamedAccu.
      }
      iIntros "%f'' %vs'' (%ah & %ah32 & %Hah32 & %Hrepah & -> & -> & Q) Hf Hr".
      iDestruct "Q" as "(@ & @ & @ & @)".

      iDestruct "Hws1" as "%Hws1".
      (* Now we're going to extract information about the serialized atoms os. *)
      (* This may look awkward because of all the later modalities, but the
         only stuff we actually need before taking a step is pure. *)
      iEval (rewrite type_interp_eq Hser; cbn) in "Hws".
      iDestruct "Hws" as "(%sk & Hevsk & Hkind & %os & Hser & Hosty)".
      iEval (rewrite type_interp_eq) in "Hosty".
      iDestruct "Hosty" as "(%sk' & Hevsk' & Hkind' & Ht)".
      iDestruct "Hser" as "%Hseros"; iDestruct "Hevsk" as "%Hevsk".
      inversion Hseros as [Hseros'].
      iDestruct "Hkind'" as "%Hkind'"; iDestruct "Hevsk'" as "%Hevsk'".
      (* here, need to obtain the physical points-to (I think) *)
      subst.
      inversion Hrepah; subst.
      rename a into a'.
      rename a0 into a.
      iAssert (rt_token rti sr lpall θ) with "[Haddr Hlayout Hheap Hrti Hownmm Howngc Hheapmem Hrm Hrmem]" as "Hrt".
      {
        by iFrame.
      }
      clear_nils.

      (* Showing sk is actually something we already know about *)
      fold (eval_size se (RepS ρtgt)) in Hevsk.
      erewrite eval_size_emptyenv in Hevsk; last eauto.
      cbn in Hevsk; inversion Hevsk; subst; clear Hevsk.
      (* Showing sk' is actually something we already know about *)
      assert (eval_rep se ρtgt = Some ιs) as Hevserep.
      {
        rewrite mono_rep_eval_rep; eauto.
        unfold is_mono_rep.
        by inversion Hmono.
      }
      assert (eval_kind se (VALTYPE ρtgt ξtgt) = Some (SVALTYPE ιs ξtgt)).
      {
        cbn; by rewrite Hevserep.
      }
      assert (type_skind se τval = Some (SVALTYPE ιs ξtgt)) as Hevtval.
      {
        rewrite Hevsk'.
        erewrite type_skind_has_kind_Some in Hevsk'; try solve [cbn; eauto].
      }
      rewrite Hevtval in Hevsk'; inversion Hevsk'; subst sk'; clear Hevsk'.
      (* Now that sk, sk' are refined, we can learn from Hkind and Hkind' *)
      iDestruct "Hkind" as "(%Hm & %Hflags)".
      inversion Hkind' as [Hareps Hats].
      destruct Hareps as (os' & Huseless & Hareps).
      inversion Huseless; subst os'; clear Huseless.
      iApply (cwp_wand_strong _ _ E' ⊤ with "[-]"); eauto.
      eapply wp_mem_load_copy_gc in Hcgload.
      destruct Hcgload as (_ & -> & -> & Hcgload).
      iApply (Hcgload with "[$] [$] [$] [//] [$] [$] []").
      + eauto.
      + done.
      + iPureIntro.
        etransitivity; last eapply Hws1.
        rewrite Hm.
        rewrite sum_list_with_list_sum.
        erewrite <- has_areps_size; last done.
        by rewrite Hseros' length_flat_map.
      + done.
      + iPureIntro.
        by eapply ser_offsets.
      + eauto.
      + iPureIntro.
        cbn.
        rewrite !length_insert Hflen /locsz !length_app !length_cons.
        rewrite !length_app.
        rewrite sum_list_with_length_concat.
        lia.
      + iPureIntro.
        cbn.
        rewrite list_lookup_insert_eq; eauto.
        by rewrite length_insert.
      + iPureIntro.
        unfold ptr_local.
        cbn.
        rewrite length_app; cbn.
        lia.
      + eauto.
      + eauto.
      + eauto.
      + eauto.
      + eauto.
      + eauto.
      + iIntros "!>".
        iIntros (f'' vs vsf) "-> @ @ @ @ @ @".
        iPoseProof (type_dup with "[Ht]") as "[Ht Hret]"; eauto.
        {
          inversion Hcopyability as (k'' & Hk' & Hbd).
          eapply has_kind_agree in Hval; last apply Hk'.
          by rewrite -> Hval in Hbd.
        }
        {
          rewrite type_interp_eq.
          iExists (SVALTYPE ιs ξtgt).
          by eauto.
        }
        iPoseProof ("Hclose_slice" with "[//] [Ht]") as "Hclosed".
        {
          iEval (rewrite value_interp_eq).
          rewrite Hser.
          iExists (SMEMTYPE m ξtgt).
          iSplitR; [|iSplitR]; eauto.
          {
            iPureIntro.
            cbn.
            rewrite Hevserep; cbn.
            rewrite Hm.
            rewrite Hseros'.
            erewrite <- has_areps_size; eauto.
            rewrite length_flat_map.
            done.
          }
          rewrite Hseros'.
          iExists os.
          by eauto.
        }
        iEval (rewrite update_get_path_id; last lia) in "Hclosed".
        iSpecialize ("Hclose" with "[$]").
        iMod "Hclose".
        iModIntro.
        rewrite /fvs_combine.
        iSplitR;
          last iSplitL "Hframe";
          last iSplitL "Hos Hret Hroot";
          last iSplitL "Htok";
          [ | | | by eauto | by eauto ].
        {
          (* restore frame_rel *)
          iPureIntro.
          split; last by rewrite load_frame_inst.
          intros i Hmask.
          destruct Hmask as [Hmask1 Hmask2].
          rewrite mk_load_frame_stable_part.
          - rewrite list_lookup_insert.
            assert (¬ (i = ptr_local)).
            {
              intros ->.
              unfold ptr_local in Hmask2.
              cbn in Hmask2.
              rewrite !sum_list_with_list_sum in Hmask2.
              lia.
            }
            rewrite decide_False; last (cbn; lia).
            rewrite list_lookup_insert.
            rewrite decide_False; last (cbn; lia).
            done.
          - rewrite length_app.
            unfold fe in Hmask2.
            lia.
        }
        {
          (* restore frame_interp *)
          iPoseProof (load_restore_frame wl (wl1 ++ wl2 ++ wl0) wlf) as "Hframe'".
          rewrite -!app_assoc.
          iSpecialize ("Hframe'" with "Hframe [//] [//]").
          iApply "Hframe'".
        }
        {
          iExists (PtrA (PtrHeap MemGC ℓ) :: os).
          iSplitL "Hret".
          - iExists ([[PtrA (PtrHeap MemGC ℓ)]; os]).
            iSplitR; first (cbn; clear_nils; done).
            rewrite !big_sepL2_cons !big_sepL2_nil.
            iFrame.
            iEval (setoid_rewrite type_interp_eq).
            iExists _; repeat iSplit.
            + iPureIntro; eauto.
            + iPureIntro; split; last by eauto.
              eexists; split; eauto.
              constructor; done.
            + iEval (cbn).
              rewrite Hevmem.
              iExists ℓ, fs.
              eauto.
          - (* establish atom_interp for the value stack *)
            unfold atoms_interp.
            cbn [app].
            setoid_rewrite big_sepL2_cons.
            iSplitR "Hos".
            + cbn.
              iExists _, _.
              iSplit; first (iPureIntro; eapply Hvn).
              iSplit; first done.
              iExists _.
              iSplit; first done.
              iFrame.
            + iApply gcrefs_atoms_copyable; eauto.
              destruct Hcopyability as (κ' & Hcopyk & Hle).
              by pose proof (has_kind_agree _ _ _ _ Hcopyk ltac:(eassumption)); subst.
        }

    - (* ref gc imm *)
      iDestruct "Hinst" as "(%Hitys & (Hmm & Hgc & Hset & Hclr & Hreg & Hunreg) & Hinstfns & Htab & %Hmemm & %Hmemgc)".
      iDestruct "Href" as (ℓ fs ws Hsv) "#Hinv".
      inversion Hsv; subst p; clear Hsv.
      change (?x :: ?y :: ?z) with ([x; y] ++ z).
      set (f' := {| f_locs := <[ptr_local:=v ]> (f_locs fr);
                    f_inst := f_inst fr |}).
      iApply (cwp_seq with "[Hfr Hrun]").
      {
        change ([?ev; ?x]) with ([ev] ++ [x]).
        rewrite (has_values_to_consts_inv _ _ Hevs).
        iApply (cwp_local_tee with "[] [$] [$]"); first eauto.
        instantiate (1:= λ f'' vs', (⌜f'' = f' /\ vs' = [v]⌝)%I).
        by iFrame.
      }
      iIntros (f vs) "[-> ->] Hf Hrun".
      eapply cwp_case_ptr in Hcompile.
      destruct Hcompile as (?wt & ?wt & ?wt & ?wl & ?wl & ?wl & ?es & ?es & ?es & Hcompile).
      destruct Hcompile as (Hunr & Hload1 & Hload2 & Hwt0 & Hwl0 & Hspec).
      rewrite atoms_interp_one_inv.
      iDestruct "Hvs" as "(%v' & %Hv' & Hat)".
      inversion Hv'; subst v'; clear Hv'.
      iApply cwp_val_app.
      { instantiate (1 := [v]). apply Is_true_true. apply/andP; split => //. by apply/eqP. }
      iPoseProof (atom_interp_ptr_shaped with "Hat") as "(%vn & %vn32 & %Hvn & -> & %Hvshp & %rp & %Hrpvn & Hrp)".
      destruct rp as [|[|]]; try (iEval (cbn) in "Hrp"; done).
      specialize (Hspec [] [] (PtrHeap MemGC ℓ) vn vn32 ltac:(eauto)).
      specialize (Hspec ltac:(auto) ltac:(auto) ltac:(auto)).
      clear_nils.
      iApply (Hspec with "[$] [$] []").
      {
        iPureIntro; cbn.
        rewrite list_lookup_insert.
        by rewrite decide_True.
      }
      iIntros "!> Hf Hrun".
      assert (Hκ'': ∃ σ ξ, has_kind F τ (MEMTYPE σ ξ)).
      {
        unfold ψ in Htype.
        inversion Htype; subst.
        destruct H0 as [Href _].
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
      iApply fupd_cwp.
      iMod (na_inv_acc with "Hinv Hown") as "U"; eauto.
      iDestruct "U" as "[ (Hfs & Hhp & Hws) [Hown Hclose]]".
      iModIntro.
      iMod "Hfs".
      iMod "Hhp".
      set (E' := (⊤ ∖ ↑ns_ref ℓ)) in *.
      assert (↑ns_fun (N.of_nat (sr_func_registerroot sr)) ⊆ E')
        by eauto with ndisj.
      destruct Hev as (sk & Hev).
      inversion Hkindok; subst.
      eapply eval_size_ok_Some in H3; eauto; destruct H3 as (n & Hevsz).
      cbn in Hev.
      rewrite Hevsz in Hev; cbn in Hev; inversion Hev; clear Hev.
      subst sk.
      assert (∃ k', type_sz se (fe_of_context F) (pr_target pr) = Some k')
        as [k' Hsztgt].
      {
        unfold type_sz.
        cbn.
        pose proof (has_mono_size_inv _ _ H) as (σ' & ξ' & k' & Hmono & Hkind & Hev).
        eapply has_kind_type_sz in Hkind; eauto.
        rewrite mono_size_eval_emp; eauto.
      }
      inv_cg_bind Hload2 [] ?wt ?wt ?wl ?wl  ?es_root_hp ?es_load Hcgroot Hcgload.
      inversion Hrpvn.
      iEval (cbn) in "Hrp".
      open_rt "Hrt".
      (* Now: use path lemma to grab the important slice of Hws *)
      (* first, setting up some pure premises for the path lemma *)
      unfold type_sz in Hsztgt.
      assert (∃ ρtgt ξtgt,
                 has_kind F (pr_target pr) κser /\
                 has_kind F τval (VALTYPE ρtgt ξtgt) /\
                 is_mono_size (RepS ρtgt) /\
                 ρ = ρtgt /\
                 κser = MEMTYPE (RepS ρtgt) ξtgt)
        as (ρtgt & ξtgt & Htgt & Hval & Hmono & -> & ->).
      {
        inversion H; subst.
        rename σ0 into σtgt.
        rename ξ0 into ξtgt.
        rewrite Hser in H6.
        inversion H6; subst.
        unfold fe in Hρ.
        unfold fe_of_context in Hρ; cbn in Hρ.
        erewrite type_rep_has_kind_agree in Hρ; last eauto.
        inversion Hρ.
        do 2 eexists.
        by rewrite Hser.
      }
      pose proof Hmono as Hevm.
      eapply mono_size_eval_emp_Some in Hevm.
      destruct Hevm as (m & Hevm).
      (* Applying the path lemma. Since Hws is under a later modality, we only
         get the result under a later modality. *)
      eapply resolves_path_inv_sep_weak in Hresolves; eauto.
      iPoseProof (Hresolves with "Hws") as "(Hws1 & Hws & Hclose_slice)".

      iApply (cwp_seq with "[Hf Hrun Hrp Hws Hroot Hrootmem Hws1 Hclose_slice]").
      {
        eapply wp_root_to_heap in Hcgroot; try eauto.
        iApply (Hcgroot with "[$] [$] [] [] [$] [$] [$] [-]").
        - cbn.
          iPureIntro.
          by rewrite list_lookup_insert_eq.
        - eauto.
        - iIntros "!> !> !> %ah %ah32 %Hah32 %Hrep Hroot Hrm Hrmem".
          instantiate (1 := (λ f0 vs0,
            ∃ ah ah32,
             ⌜N_i32_repr ah ah32⌝ ∗
             ⌜repr_pointer θ (PtrHeap MemGC ℓ) ah⌝ ∗
             ⌜f0 = {| W.f_locs := <[localimm (Mk_localidx ptr_local):=VAL_int32 ah32]> (f_locs f'); W.f_inst := f_inst f' |}⌝ ∗
             ⌜vs0 = []⌝ ∗
             _)%I).
          iExists ah, ah32.
          iSplit; first done.
          iSplit; first done.
          iSplit; first done.
          iSplit; first done.
          iNamedAccu.
      }
      iIntros "%f'' %vs'' (%ah & %ah32 & %Hah32 & %Hrepah & -> & -> & Q) Hf Hr".
      iDestruct "Q" as "(@ & @ & @ & @)".
      (* here, need to obtain the physical points-to (I think) *)
      subst.
      inversion Hrepah; subst.
      rename a into a'.
      rename a0 into a.
      iAssert (rt_token rti sr lpall θ) with "[Haddr Hlayout Hheap Hrti Hownmm Howngc Hheapmem Hrm Hrmem]" as "Hrt".
      {
        by iFrame.
      }
      clear_nils.
      (* Now: use path lemma to grab the important slice of Hws *)
      (* first, setting up some pure premises for the path lemma *)
      unfold type_sz in Hsztgt.
      iDestruct "Hws1" as "%Hws1".
      iEval (rewrite type_interp_eq Hser; cbn) in "Hws".
      iDestruct "Hws" as "(%sk & Hevsk & Hkind & %os & Hser & Hosty)".
      iEval (rewrite type_interp_eq) in "Hosty".
      iDestruct "Hosty" as "(%sk' & Hevsk' & Hkind' & Ht)".
      iDestruct "Hser" as "%Hseros"; iDestruct "Hevsk" as "%Hevsk".
      inversion Hseros as [Hseros'].
      iDestruct "Hkind'" as "%Hkind'"; iDestruct "Hevsk'" as "%Hevsk'".
      (* Showing sk is actually something we already know about *)
      fold (eval_size se (RepS ρtgt)) in Hevsk.
      erewrite eval_size_emptyenv in Hevsk; last eauto.
      cbn in Hevsk; inversion Hevsk; subst; clear Hevsk.
      (* Showing sk' is actually something we already know about *)
      assert (eval_rep se ρtgt = Some ιs) as Hevserep.
      {
        rewrite mono_rep_eval_rep; eauto.
        unfold is_mono_rep.
        by inversion Hmono.
      }
      assert (eval_kind se (VALTYPE ρtgt ξtgt) = Some (SVALTYPE ιs ξtgt)).
      {
        cbn; by rewrite Hevserep.
      }
      assert (type_skind se τval = Some (SVALTYPE ιs ξtgt)) as Hevtval.
      {
        rewrite Hevsk'.
        erewrite type_skind_has_kind_Some in Hevsk'; try solve [cbn; eauto].
      }
      rewrite Hevtval in Hevsk'; inversion Hevsk'; subst sk'; clear Hevsk'.
      (* Now that sk, sk' are refined, we can learn from Hkind and Hkind' *)
      iDestruct "Hkind" as "(%Hm & %Hflags)".
      inversion Hkind' as [Hareps Hats].
      destruct Hareps as (os' & Huseless & Hareps).
      inversion Huseless; subst os'; clear Huseless.
      iApply (cwp_wand_strong _ _ E' ⊤ with "[-]"); eauto.
      eapply wp_mem_load_copy_gc in Hcgload.
      destruct Hcgload as (_ & -> & -> & Hcgload).
      iApply (Hcgload with "[$] [$] [$] [//] [$] [$] []").
      + eauto.
      + done.
      + iPureIntro.
        etransitivity; last eapply Hws1.
        rewrite Hm.
        rewrite sum_list_with_list_sum.
        erewrite <- has_areps_size; last done.
        by rewrite Hseros' length_flat_map.
      + done.
      + iPureIntro.
        by eapply ser_offsets.
      + eauto.
      + iPureIntro.
        cbn.
        rewrite !length_insert Hflen /locsz !length_app !length_cons.
        rewrite !length_app.
        rewrite sum_list_with_length_concat.
        lia.
      + iPureIntro.
        cbn.
        rewrite list_lookup_insert_eq; eauto.
        by rewrite length_insert.
      + iPureIntro.
        unfold ptr_local.
        cbn.
        rewrite length_app; cbn.
        lia.
      + eauto.
      + eauto.
      + eauto.
      + eauto.
      + eauto.
      + eauto.
      + iIntros "!>".
        iIntros (f'' vs vsf) "-> @ @ @ @ @ @".
        iPoseProof (type_dup with "[Ht]") as "[Ht Hret]"; eauto.
        {
          inversion Hcopyability as (k'' & Hk' & Hbd).
          eapply has_kind_agree in Hval; last apply Hk'.
          by rewrite -> Hval in Hbd.
        }
        {
          iEval (rewrite type_interp_eq).
          iExists (SVALTYPE ιs ξtgt).
          by eauto.
        }
        iPoseProof ("Hclose_slice" with "[//] [Ht]") as "Hclosed".
        {
          iEval (rewrite value_interp_eq).
          rewrite Hser.
          iExists (SMEMTYPE m ξtgt).
          iSplitR; [|iSplitR]; eauto.
          {
            iPureIntro.
            cbn.
            rewrite Hevserep; cbn.
            rewrite Hm.
            rewrite Hseros'.
            erewrite <- has_areps_size; eauto.
            rewrite length_flat_map.
            done.
          }
          rewrite Hseros'.
          iExists os.
          by eauto.
        }
        iEval (rewrite update_get_path_id; last lia) in "Hclosed".
        iSpecialize ("Hclose" with "[$]").
        iMod "Hclose".
        iModIntro.
        rewrite /fvs_combine.
        iSplitR;
          last iSplitL "Hframe";
          last iSplitL "Hos Hret Hroot";
          last iSplitL "Htok";
          [ | | | by eauto | by eauto ].
        {
          (* restore frame_rel *)
          iPureIntro.
          split; last by rewrite load_frame_inst.
          intros i Hmask.
          destruct Hmask as [Hmask1 Hmask2].
          rewrite mk_load_frame_stable_part.
          - rewrite list_lookup_insert.
            assert (¬ (i = ptr_local)).
            {
              intros ->.
              unfold ptr_local in Hmask2.
              cbn in Hmask2.
              rewrite !sum_list_with_list_sum in Hmask2.
              lia.
            }
            rewrite decide_False; last (cbn; lia).
            rewrite list_lookup_insert.
            rewrite decide_False; last (cbn; lia).
            done.
          - rewrite length_app.
            unfold fe in Hmask2.
            lia.
        }
        {
          (* restore frame_interp *)
          iPoseProof (load_restore_frame wl (wl1 ++ wl2 ++ wl0) wlf) as "Hframe'".
          rewrite -!app_assoc.
          iSpecialize ("Hframe'" with "Hframe [//] [//]").
          iApply "Hframe'".
        }
        {
          iExists (PtrA (PtrHeap MemGC ℓ) :: os).
          iSplitL "Hret".
          - iExists ([[PtrA (PtrHeap MemGC ℓ)]; os]).
            iSplitR; first (cbn; clear_nils; done).
            rewrite !big_sepL2_cons !big_sepL2_nil.
            iFrame.
            iEval (setoid_rewrite type_interp_eq).
            iExists _; repeat iSplit.
            + iPureIntro; eauto.
            + iPureIntro; split; last by eauto.
              eexists; split; eauto.
              constructor; done.
            + iEval (cbn).
              rewrite Hevmem.
              iExists ℓ, fs.
              eauto.
          - (* establish atom_interp for the value stack *)
            unfold atoms_interp.
            cbn [app].
            setoid_rewrite big_sepL2_cons.
            iSplitR "Hos".
            + cbn.
              iExists _, _.
              iSplit; first (iPureIntro; eapply Hvn).
              iSplit; first done.
              iExists _.
              iSplit; first done.
              iFrame.
            + iApply gcrefs_atoms_copyable; eauto.
              destruct Hcopyability as (κ' & Hcopyk & Hle).
              by pose proof (has_kind_agree _ _ _ _ Hcopyk ltac:(eassumption)); subst.
        }
  Qed.

End load_copy.
