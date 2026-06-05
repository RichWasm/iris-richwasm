From mathcomp Require Import eqtype ssrbool.

Require Import RichWasm.util.
Require Import RichWasm.compiler.memory.
Require Import RichWasm.iris.numerics.
Require Import RichWasm.iris.runtime.
Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.case_ptr.
Require Import RichWasm.iris.logrel.path.
Require Import RichWasm.iris.logrel.load.
Require Import RichWasm.iris.logrel.roots.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section load_copy.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma sum_list_with_list_sum {A} {f : A -> nat} {xs : list A} :
    sum_list_with f xs = list_sum (map f xs).
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

  Lemma atom_interp_ptr_shaped ptr v :
    atom_interp (PtrA ptr) v -∗
    ∃ n n32, ⌜N_i32_repr n n32⌝ ∗
             ⌜v = VAL_int32 n32⌝ ∗
             ⌜ptr_shaped ptr n⌝ ∗
             ∃ rp, ⌜repr_root_pointer rp n⌝ ∗ root_pointer_interp rp ptr.
  Proof.
    iIntros "Hat".
    destruct ptr; cbn; unfold root_pointer_interp.
    - iDestruct "Hat" as "(%n' & %n32 & %Hn32 & %Hv & (%rp & %Hrp & Hrpn))".
      destruct rp; last (destruct μ; done).
      iDestruct "Hrpn" as "->".
      inversion Hrp; subst.
      iExists _, _.
      iSplit; first eauto.
      iSplit; first eauto.
      iSplit; first eauto using ptr_shaped.
      iExists (RootInt n); eauto.
    - iDestruct "Hat" as "(%n' & %n32 & %Hn32 & %Hv & (%rp & %Hrp & Hrpn))"; subst.
      destruct rp; first done.
      inversion Hrp; subst.
      destruct μ0, μ; try done.
      + iExists _, _.
        repeat (iSplit; first eauto using ptr_shaped).
        iExists _; eauto.
      + iExists _, _.
        repeat (iSplit; first eauto using ptr_shaped).
        iExists _; eauto.
  Qed.

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

  Lemma update_get_path_id off sz ws :
    sz + off ≤ length ws ->
    update_path_words off ws (get_path_words off sz ws) = ws.
  Proof.
    etransitivity; last apply (take_drop off ws).
    unfold update_path_words.
    f_equal.
    etransitivity; last apply (take_drop sz (drop off ws)).
    f_equal.
    rewrite length_take length_drop.
    f_equal; lia.
  Qed.

  Lemma eval_kind_flag (se : @semantic_env Σ) κ sk :
    eval_kind se κ = Some sk ->
    kind_ref_flag κ = skind_ref_flag sk.
  Proof.
    intros Hev.
    destruct κ; cbn in *.
    - apply bind_Some in Hev; destruct Hev as (? & ? & ?).
      cbn in *; inversion H0.
      done.
    - apply bind_Some in Hev; destruct Hev as (? & ? & ?).
      cbn in *; inversion H0.
      done.
  Qed.

  Lemma type_dup se F τ κ sv :
    sem_env_interp F se ->
    has_kind F τ κ ->
    ref_flag_le (kind_ref_flag κ) GCRefs ->
    let T := type_interp rti sr τ se sv in
    T -∗ T ∗ T.
  Proof.
    intros Hse Hkind Hle.
    assert (kind_ok (fc_kind_ctx F) κ) as Hok.
    {
      eapply has_kind_inv in Hkind.
      by inversion Hkind.
    }
    pose proof Hok as Hok'.
    eapply eval_kind_ok_Some in Hok'; eauto.
    destruct Hok' as [sk Hev].
    pose proof Hkind as Hkind'.
    eapply (kinding_sound rti sr) in Hkind'; eauto.
    unfold skind_has_stype in Hkind'.
    destruct Hkind' as [Hrefflag _].
    erewrite <- eval_kind_flag in Hrefflag; eauto.
    eapply ref_flag_stype_interp_refine in Hrefflag; eauto.
    cbn in Hrefflag.
    specialize (Hrefflag sv).
    rewrite value_interp_eq in Hrefflag.
    intros T; unfold T.
    rewrite type_interp_eq.
    iIntros "#HT".
    by iSplit.
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


  Lemma Forall2_rcons_inv_r:
    ∀ {A B : Type} (P : A → B → Prop) (x : B) (l : list B) (k : list A),
      Forall2 P k (seq.rcons l x) → ∃ (y : A) (k' : list A), P y x ∧ Forall2 P k' l ∧ k = seq.rcons k' y.
  Proof.
  Admitted.

  Lemma Forall2_rcons {A B : Type} (P : A -> B -> Prop) xs x ys y :
    Forall2 P xs ys ->
    P x y ->
    Forall2 P (seq.rcons xs x) (seq.rcons ys y).
  Proof.
  Admitted.

  Lemma get_path_split_app ι o os off sz ws :
    off + sz <= length ws ->
    has_arep ι o ->
    get_path_words off sz ws = flat_map serialize_atom os ++ serialize_atom o ->
    arep_size ι <= sz /\
    get_path_words off (sz - arep_size ι) ws = flat_map serialize_atom os /\
    get_path_words (off + sz - arep_size ι) (arep_size ι) ws = serialize_atom o.
  Proof.
    intros Hlen Ho Hws.
    assert (arep_size ι ≤ sz).
    {
      apply (f_equal length) in Hws.
      rewrite length_take length_drop length_app in Hws.
      erewrite has_arep_size in Hws; eauto.
      lia.
    }
    assert (get_path_words off sz ws =
              get_path_words off (sz - arep_size ι) ws ++
              get_path_words (off + sz - arep_size ι) (arep_size ι) ws).
    {
      unfold get_path_words.
      replace (@take word sz) with (@take word ((sz - arep_size ι) + arep_size ι));
        last (f_equal; lia).
      rewrite -take_take_drop.
      rewrite drop_drop.
      repeat f_equal; lia.
    }
    rewrite H0 in Hws.
    eapply app_inj_1 in Hws; eauto.
    apply (f_equal length) in Hws.
    rewrite !length_app in Hws.
    assert (length (get_path_words (off + sz - arep_size ι) (arep_size ι) ws)
            = arep_size ι) as Hlast
        by (rewrite length_take length_drop; lia).
    rewrite Hlast in Hws.
    erewrite has_arep_size in Hws; last by eauto.
    lia.
  Qed.

  Lemma ser_offsets os : ∀ (off : nat) ntgt ws ιs,
    off + ntgt <= length ws ->
    Forall2 has_arep ιs os ->
    get_path_words off ntgt ws = flat_map serialize_atom os ->
    Forall2
      (λ o '(off0, sz), serialize_atom o = get_path_words off0 sz ws)
      os
     (seq.zip
        (seq.foldl (λ '(off', offs) ι, ((off' + arep_size ι)%nat, seq.rcons offs off'))
                   (off, [])
                   ιs).2
        (map arep_size ιs)).
  Proof.
    induction os as [|os o] using seq.last_ind; intros * Hlen Hreps Hser.
    - cbn in Hser.
      inversion Hreps; subst.
      econstructor.
    - apply Forall2_rcons_inv_r in Hreps.
      destruct Hreps as (ι & ιs' & Ho & Hos & ->).
      change map with @seq.map.
      rewrite seq.map_rcons.
      rewrite seq.foldl_rcons.
      destruct (seq.foldl
            (λ '(off', offs) (ι0 : atomic_rep),
               (off' + arep_size ι0, seq.rcons offs off'))
            (off, []) ιs') as [off' offs] eqn:Hoffs.
      pose proof Hoffs as Hoffslen.
      apply load_fold_offs_len in Hoffslen; cbn in Hoffslen; rewrite Nat.add_0_r in Hoffslen.
      rewrite flat_map_rcons in Hser.
      rewrite seq.zip_rcons;
        last (rewrite seq.size_map; by apply Hoffslen).
      eapply get_path_split_app in Hser; eauto.
      destruct Hser as (Hsz & Hseros & Hsero).
      apply Forall2_rcons.
      + eapply IHos in Hos; try eapply Hseros; eauto; last lia.
        by rewrite Hoffs in Hos.
      + eapply simple_fold_fancy_fold in Hoffs; eauto.
        rewrite simple_fold_sum_list_with in Hoffs; eauto.
        rewrite -Hoffs.
        rewrite -Hsero.
        f_equal.
        rewrite sum_list_with_list_sum.
        erewrite <- has_areps_size; last eauto.
        rewrite -map_map.
        apply (f_equal length) in Hseros.
        rewrite length_take length_drop in Hseros.
        rewrite flat_map_concat_map length_concat in Hseros.
        rewrite -Hseros.
        lia.
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
      + iIntros (e' f'' vs vsf) "->".
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
          apply Is_true_true.
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
          iApply big_sepL2_mono; last iApply "Hos".
          intros k o v Ho Hv.
          cbn -[atom_interp].
          iIntros "Hat".
          iApply "Hat"; iPureIntro.
          destruct o; try done.
          destruct p as [| [|]]; try done.
          destruct Hcopyability as (κ' & Hcopyk & Hle).
          pose proof (has_kind_agree _ _ _ _ Hcopyk ltac:(eassumption)); subst.
          cbn in Hle.
          apply list_elem_of_lookup_2 in Ho.
          eapply Forall_forall in Hats; last eauto.
          cbn in Hats.
          destruct ξtgt'; cbn in Hats; done.

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
      + iIntros (e' f'' vs vsf) "->".
        repeat iIntros "@".
        unfold fvs_combine.
        let Q := open_constr:(_ : iProp Σ) in
        instantiate (1 :=
          (λ f0 vs0, ∃ e0 vs vsf,
             ⌜f0 = (mk_load_frame (fe_of_context F) f' (wl ++ [T_i32] ++ wl1) vsf)⌝ ∗
             ⌜vs0 = vs⌝ ∗
             ⌜Forall2 (λ (ι : atomic_rep) (vf : value), types_agree (translate_arep ι) vf) ιs vsf⌝ ∗
             ([∗ list] o;v ∈ os;vs, ⌜atom_copyable o⌝ -∗ atom_interp o v) ∗
             rt_token rti sr e0 ∗
             Q
          )%I).
        iExists e', vs, vsf.
        iSplit; first done.
        iSplit; first done.
        iSplit; first done.
        iSplitL "Hos"; first done.
        iSplitL "Htok"; first done.
        iNamedAccu.
      + eauto.
      + eauto.
      + iIntros "!>".
        iIntros (f v) "(%e & %vs & %vsf & -> & ->  & %Hag & Hcopy & Htok & @ & @ & @ & @)".
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
          apply Is_true_true.
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
          iApply big_sepL2_mono; last iApply "Hcopy".
          intros k o v Ho Hv.
          cbn -[atom_interp].
          iIntros "Hat".
          iApply "Hat"; iPureIntro.
          destruct o; try done.
          destruct p as [| [|]]; try done.
          destruct Hcopyability as (κ' & Hcopyk & Hle).
          pose proof (has_kind_agree _ _ _ _ Hcopyk ltac:(eassumption)); subst.
          cbn in Hle.
          apply list_elem_of_lookup_2 in Ho.
          eapply Forall_forall in Hats; last eauto.
          cbn in Hats.
          destruct ξtgt'; cbn in Hats; done.

    - (* ref gc mut *)
      iDestruct "Href" as (ℓ fs Hsv) "Hinv".
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
      setoid_rewrite type_interp_eq.
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
      iDestruct "U" as "[ (%ws & Hfs & Hhp & Hws) V ]".
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
      inv_cg_bind Hload2 [] ?wt ?wt ?wl ?wl  ?es_root_hp ?es_store Hcgroot Hcgload.
      inversion Hrpvn.
      iEval (cbn) in "Hrp".
      open_rt "Hrt".
      iApply (cwp_seq with "[Hf Hrun Hrp Hws Hroot Hrootmem]").
      {
        eapply wp_root_to_heap in Hcgroot; try eauto.
        iApply (Hcgroot with "[$] [$] [] [] [$] [$] [$] [-]").
        - admit. (* EASY *)
        - admit. (* EASY *)
        - iIntros "!> %ah %ah32 %Hah32 %Hrep Hroot Hrm Hrmem".
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
      clear_nils.

    - (* ref gc imm *)
      admit.
  Admitted.

End load_copy.
