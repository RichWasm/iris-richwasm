Require Import iris.proofmode.proofmode.

From stdpp Require Import list.
From RichWasm Require Import syntax typing util.
From RichWasm.compiler Require Import prelude accum codegen.
From RichWasm.iris Require Import autowp cwp lenient_wp logpred.
Require Import RichWasm.iris.logrel.

Module W := RichWasm.wasm.operations.

Set Bullet Behavior "Strict Subproofs".

Section CodeGen.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!rwasm_gcG Σ}.

  Lemma wp_if_c {A B} s E tf (c1 : codegen A) (c2 : codegen B) wt wt' wl wl' es x y :
    run_codegen (if_c tf c1 c2) wt wl = inr (x, y, wt', wl', es) ->
    exists wt1 wt2 wl1 wl2 es1 es2,
      run_codegen c1 wt wl = inr (x, wt1, wl1, es1) /\
        run_codegen c2 (wt ++ wt1) (wl ++ wl1) = inr (y, wt2, wl2, es2) /\
        wt' = wt1 ++ wt2 /\
        wl' = wl1 ++ wl2 /\
        ⊢ ∀ Φ f i,
          ↪[frame] f -∗
          ↪[RUN] -∗
          ((⌜i <> Wasm_int.int_zero i32m⌝ ∧
              ▷ (↪[frame] f -∗ ↪[RUN] -∗ WP [AI_basic (BI_block tf es1)] @ s; E {{ v, Φ v }})) ∨
             (⌜i = Wasm_int.int_zero i32m⌝ ∧
                ▷ (↪[frame] f -∗ ↪[RUN] -∗ WP [AI_basic (BI_block tf es2)] @ s; E {{ v, Φ v }}))) -∗
          WP to_e_list (BI_const (VAL_int32 i) :: es) @ s; E {{ v, Φ v }}.
  Proof.
    intros Hcomp.
    unfold if_c in Hcomp.

    inv_cg_bind Hcomp x1 wt1 wt2 wl1 wl2 es1 es2 Hcg1 Hcg2.
    destruct x1 as [x' es1'].
    subst es.
    apply run_codegen_capture in Hcg1.
    destruct Hcg1 as [Hcg1 ->].

    inv_cg_bind Hcg2 x2 wt3 wt4 wl3 wl4 es3 es4 Hcg2 Hcg3.
    destruct x2 as [y' es2'].
    subst es2.

    apply run_codegen_capture in Hcg2.
    destruct Hcg2 as [Hcg2 ->].

    cbn in Hcg3.
    inversion Hcg3.
    subst x' y' wl2 es4.
    clear Hcg3.
    rename es1' into es1, es2' into es2.
    subst.

    exists wt1, wt3, wl1, wl3, es1, es2.
    subst.
    split; first assumption.
    split; first assumption.
    split; first by rewrite app_nil_r.
    split; first by rewrite app_nil_r.

    iIntros (Φ f i) "Hfr Hrun Hbl".
    iSimpl.
    iDestruct "Hbl" as "[[%Hi Hbl] | [%Hi Hbl]]".
    - by iApply (wp_if_true with "[$Hfr] [Hrun]"); eauto.
    - by iApply (wp_if_false with "[Hfr] [Hrun]"); auto.
  Qed.

  Lemma lwp_if_c {A B} s E tf (c1 : codegen A) (c2 : codegen B) wt wt' wl wl' es x y :
    run_codegen (if_c tf c1 c2) wt wl = inr (x, y, wt', wl', es) ->
    exists wt1 wt2 wl1 wl2 es1 es2,
      run_codegen c1 wt wl = inr (x, wt1, wl1, es1) /\
        run_codegen c2 (wt ++ wt1) (wl ++ wl1) = inr (y, wt2, wl2, es2) /\
        wt' = wt1 ++ wt2 /\
        wl' = wl1 ++ wl2 /\
        ⊢ ∀ Φ f i,
          ↪[frame] f -∗
          ↪[RUN] -∗
          ((⌜i <> Wasm_int.int_zero i32m⌝ ∧
              ▷ (↪[frame] f -∗ ↪[RUN] -∗ lenient_wp s E [AI_basic (BI_block tf es1)] Φ)) ∨
             (⌜i = Wasm_int.int_zero i32m⌝ ∧
                ▷ (↪[frame] f -∗ ↪[RUN] -∗ lenient_wp s E [AI_basic (BI_block tf es2)] Φ))) -∗
          lenient_wp s E (AI_basic (BI_const (VAL_int32 i)) :: to_e_list es) Φ.
  Proof.
    intros Hcg.
    eapply wp_if_c in Hcg.
    destruct Hcg as (wt1 & wt2 & wl1 & wl2 & es1 & es2 & Hcg1 & Hcg2 & Hwt' & Hwl' & Hwp).
    do 6 eexists; split; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    iIntros (Φ f i) "Hf Hrun Hbranches".
    iApply (Hwp with "[$] [$] [$]").
  Qed.

  Lemma cwp_if_c {T U} (c1 : codegen T) (c2 : codegen U) wt wt' wl wl' ts1 ts2 es x y :
    run_codegen (if_c (Tf ts1 ts2) c1 c2) wt wl = inr (x, y, wt', wl', es) ->
    exists wt1 wt2 wl1 wl2 es1 es2,
      run_codegen c1 wt wl = inr (x, wt1, wl1, es1) /\
      run_codegen c2 (wt ++ wt1) (wl ++ wl1) = inr (y, wt2, wl2, es2) /\
      wt' = wt1 ++ wt2 /\
      wl' = wl1 ++ wl2 /\
      forall evs,
        is_consts evs ->
        length evs = length ts1 ->
        ∀ s E B R Φ f i,
          ↪[frame] f -∗
          ↪[RUN] -∗
          ((⌜i <> Wasm_int.int_zero i32m⌝ ∧
            ▷ (↪[frame] f -∗ ↪[RUN] -∗
              CWP evs ++ es1 @ s; E UNDER (length ts2, Φ) :: B; R {{ Φ }})) ∨
          (⌜i = Wasm_int.int_zero i32m⌝ ∧
            ▷ (↪[frame] f -∗ ↪[RUN] -∗
              CWP evs ++ es2 @ s; E UNDER (length ts2, Φ) :: B; R {{ Φ }}))) -∗
          CWP evs ++ BI_const (VAL_int32 i) :: es @ s; E UNDER B; R {{ Φ }}.
  Proof.
    intros Hcg.
    inv_cg_bind Hcg [x1 x2] wt1 wt2 wl1 wl2 es1 es2 Hcg1 Hcg2.
    inv_cg_bind Hcg2 [x3 x4] wt3 wt4 wl3 wl4 es3 es4 Hcg2 Hcg3.
    inv_cg_bind Hcg3 [] wt5 wt6 wl5 wl6 es5 es6 Hcg3 Hcg4.
    apply run_codegen_capture in Hcg1 as [Hcg1 ->].
    apply run_codegen_capture in Hcg2 as [Hcg2 ->].
    inv_cg_emit Hcg3.
    inv_cg_ret Hcg4.
    inversion Hretval0.
    clear Hretval Hretval0.
    subst es wl' wt' es2 wl2 wt2 es4 wl4 wt4 es6 wl6 wt6 es5 wl5 wt5 x1 x3.
    rewrite !app_nil_r.
    rewrite !app_nil_l.
    exists wt1, wt3, wl1, wl3, x2, x4.
    do 4 (split; first done).
    iIntros (evs Hevs Hlen s E B R Φ f i) "Hfr Hrun [[%Hi Hwp]|[%Hi Hwp]]".
    - iApply (cwp_if_nonzero with "[$] [$]").
      1, 2, 3: done.
      iIntros "!> Hfr Hrun".
      iApply ("Hwp" with "[$] [$]").
    - iApply (cwp_if_zero with "[$] [$]").
      1, 2, 3: done.
      iIntros "!> Hfr Hrun".
      iApply ("Hwp" with "[$] [$]").
  Qed.

  (* Generic monad operations. *)

  Lemma wp_ignore {A} (c : codegen A) wt wl ret wt' wl' es :
    run_codegen (ignore c) wt wl = inr (ret, wt', wl', es) ->
    ret = tt /\
    exists ret',
      run_codegen c wt wl = inr (ret', wt', wl', es).
  Proof.
    intros Hcg.
    inv_cg_bind Hcg res' wt'' wt''' wl'' wl'''  es1 es2 Hcg1 Hcg2.
    inv_cg_ret Hcg2.
    rewrite !app_nil_r.
    eauto.
  Qed.

  Lemma wp_ret {A} (a: A) wt wl v wt' wl' es :
    run_codegen (Monad.ret a) wt wl = inr (v, wt', wl', es) ->
    v = a /\ wt' = [] /\ wl' = [] /\ es = [].
  Proof.
    cbn.
    intros Hcg.
    inversion Hcg; subst; done.
  Qed.

  Lemma wp_mapM_nil {A B} (f : A -> codegen B) wt wl ys wt' wl' es :
    run_codegen (mapM f []) wt wl = inr (ys, wt', wl', es) ->
    wt' = [] /\
    wl' = [] /\
    ys = [] /\
    es = [].
  Proof.
    cbn.
    intros Hcg.
    inversion Hcg.
    done.
  Qed.

  Lemma wp_mapM_cons {A B} (f : A -> codegen B) wt wl yss wt' wl' es x xs :
    run_codegen (mapM f (x :: xs)) wt wl = inr (yss, wt', wl', es) ->
    ∃ ys_x wt_x wl_x es_x yss_xs wt_xs wl_xs es_xs,
      run_codegen (f x) wt wl = inr (ys_x, wt_x, wl_x, es_x) /\
        run_codegen (mapM f xs) (wt ++ wt_x) (wl ++ wl_x) = inr (yss_xs, wt_xs, wl_xs, es_xs) /\
        yss = ys_x :: yss_xs /\
        wt' = wt_x ++ wt_xs /\
        wl' = wl_x ++ wl_xs /\
        es = es_x ++ es_xs.
  Proof.
    cbn.
    intros Hcg.
    inv_cg_bind Hcg res1 wt1 wt1' wl1 wl1' es_fx es2 Hfx Hcg1.
    inv_cg_bind Hcg1 res2 wt2 wt2' wl2 wl2' es_fxs es3 Hfxs Hcg2.
    cbn in Hcg2.
    inversion Hcg2.
    subst.
    repeat eexists; eauto.
    rewrite !app_nil_r; eauto.
  Qed.

  Lemma wp_mapM__cons {A B} (f : A -> codegen B) wt wl yss wt' wl' es x xs :
    run_codegen (mapM_ f (x :: xs)) wt wl = inr (yss, wt', wl', es) ->
    ∃ ys_x wt_x wl_x es_x wt_xs wl_xs es_xs,
      run_codegen (f x) wt wl = inr (ys_x, wt_x, wl_x, es_x) /\
        run_codegen (mapM_ f xs) (wt ++ wt_x) (wl ++ wl_x) = inr ((), wt_xs, wl_xs, es_xs) /\
        yss = () /\
        wt' = wt_x ++ wt_xs /\
        wl' = wl_x ++ wl_xs /\
        es = es_x ++ es_xs.
  Proof.
    intros Hcg.
    apply wp_ignore in Hcg as (-> & ret & Hcg).
    apply wp_mapM_cons in Hcg.
    destruct Hcg as (ys_x & wt_x & wl_x & es_x & yss_xs & wt_xs & wl_xs & es_xs & Hcg & Hcg_rest & Hx & Hwt' & Hwl' & Hes').
    repeat eexists; try done.
    subst.
    unfold mapM_, ignore.
    rewrite <- app_nil_r with (l := wt_xs).
    rewrite <- app_nil_r with (l := wl_xs).
    rewrite <- app_nil_r with (l := es_xs).
    eapply run_codegen_bind_intro; done.
  Qed.

  Lemma wp_mapM_emit wt wl es xs wt' wl' es' :
    run_codegen (mapM emit es) wt wl = inr (xs, wt', wl', es') ->
    xs = repeat tt (length es) /\
      wt' = [] /\
      wl' = [] /\
      es' = es.
  Proof.
    revert es' xs.
    induction es; intros es' xs Hemit.
    - cbn in Hemit.
      inversion Hemit; subst.
      done.
    - apply wp_mapM_cons in Hemit.
      destruct Hemit as (ys_x & wt_x & wl_x & es_x & yss_xs & wt_xs & wl_xs & es_xs & Hemit & Hemits & Hx & Hwt' & Hwl' & Hes').
      subst xs wt' wl' es'.
      inv_cg_emit Hemit; subst.
      rewrite !app_nil_r in Hemits.
      apply IHes in Hemits.
      destruct Hemits as (Hyss & Hwt_xs & Hwl_xs & Hes_xs).
      cbn in *.
      inversion Hes_xs; subst es_xs wt_xs wl_xs.
      split; eauto.
      congruence.
  Qed.

  (* State monad operations. *) 
  Lemma wp_get wt wl v wt' wl' es :
    run_codegen get wt wl = inr (v, wt', wl', es) ->
    v = (wt, wl) /\
      wt' = [] /\
      wl' = [] /\
      es = [].
  Proof.
    unfold get; cbn.
    intros Heq.
    inversion Heq; subst.
    tauto.
  Qed.

  Lemma wp_acc wt wl v wt' wt'' wl' wl'' es :
    run_codegen (acc (wt', wl')) wt wl = inr (v, wt'', wl'', es) ->
    v = () /\
      wt'' = wt' /\
      wl'' = wl' /\
      es = [].
  Proof.
    unfold acc; cbn.
    intros Heq.
    inversion Heq; subst.
    tauto.
  Qed.

  (* Allocating locals. *)
  
  Lemma wp_wlalloc fe ty wt wt' wl wl' idx es :
    run_codegen (wlalloc fe ty) wt wl = inr (idx, wt', wl', es) ->
    idx = Mk_localidx (fe_wlocal_offset fe + length wl) /\
      wt' = [] /\
      wl' = [ty] /\
      es = [].
  Proof.
    unfold wlalloc.
    intros Hcg.
    inv_cg_bind Hcg res wt1 wt1' wl1 wl1' es_get es2 Hget Hcg1.
    destruct res.
    inv_cg_bind Hcg1 res1 wt2 wt2' wl2 wl2' es_acc es_ret Hacc Hret.
    apply wp_get in Hget.
    apply wp_acc in Hacc.
    apply wp_ret in Hret.
    destruct Hget as (? & ? & ? & ?).
    destruct Hacc as (? & ? & ? & ?).
    destruct Hret as (? & ? & ? & ?).
    inversion H.
    subst.
    by rewrite !app_nil_r.
  Qed.

  Lemma wp_wlallocs fe tys wt wl idxs wt' wl' es :
    run_codegen (wlallocs fe tys) wt wl = inr (idxs, wt', wl', es) ->
    idxs = imap (λ i _, Mk_localidx (fe_wlocal_offset fe + length wl + i)) tys /\
      wt' = [] /\
      wl' = tys /\
      es = [].
  Proof.
    revert wt wl idxs wt' wl' es.
    induction tys.
    - intros * Hcg; cbn in *.
      by inversion Hcg.
    - intros * Hcg.
      eapply (wp_mapM_cons (wlalloc fe)) in Hcg.
      destruct Hcg as (ys_a & wt_a & wl_a & es_a & yss_tys & wt_tys & wl_tys & es_tys & Hcg_a & Hcg_tys & Hidxs & Hwt' & Hwl' & Hes).
      subst.
      apply IHtys in Hcg_tys.
      destruct Hcg_tys as (Himap & Hwt_tys & Hwl_tys & Hes_tys); subst.
      apply wp_wlalloc in Hcg_a.
      destruct Hcg_a as (Hys_a & Hwt_a & Hwl_a & Hes_a); subst.
      repeat split; eauto with datatypes.
      cbn.
      f_equal.
      + by rewrite Nat.add_0_r.
      + rewrite length_app Nat.add_1_r; cbn.
        apply imap_ext; intros.
        cbn.
        f_equal.
        lia.
  Qed.

  Lemma rev_reverse {A} (xs: list A) :
    reverse xs = rev xs.
  Proof.
    unfold reverse.
    by rewrite rev_append_rev app_nil_r.
  Qed.

  Lemma rev_append_reverse {A} (xs ys: list A) :
    rev_append xs ys = reverse xs ++ ys.
  Proof.
    rewrite rev_reverse.
    by rewrite rev_append_rev.
  Qed.

  Lemma rev_append_imap_distr {A B} (f: nat -> A -> B) l l' :
    rev_append (imap f l) l' = imap (λ i x, f (length l - 1 - i) x) (reverse l) ++ l'.
  Proof.
    revert f l'.
    induction l; intros f l'.
    - done.
    - rewrite imap_cons.
      cbn.
      rewrite IHl.
      cbn.
      rewrite !rev_append_reverse.
      rewrite imap_app.
      cbn.
      rewrite Nat.add_0_r.
      rewrite -app_assoc.
      cbn.
      f_equal.
      + apply imap_ext.
        intros i x Hfind.
        assert (i < length l).
        {
          rewrite -length_reverse.
          eapply lookup_lt_is_Some_1; eauto.
        }
        f_equal.
        lia.
      + rewrite length_reverse.
        do 2 f_equal.
        lia.
  Qed.
  
  Lemma reverse_imap_distr {A B} (f: nat -> A -> B) l :
    (reverse (imap f l)) = imap (λ i x, f (length l - 1 - i) x) (reverse l).
  Proof.
    unfold reverse.
    rewrite rev_append_imap_distr.
    rewrite rev_append_reverse.
    by rewrite !app_nil_r.
  Qed.
  
  Lemma mapM_comp {A B C} (f: A -> B) (g : B -> codegen C) xs :
    mapM (g ∘ f) xs = mapM g (map f xs).
  Proof.
    induction xs.
    - done.
    - simpl mapM.
      by rewrite IHxs.
  Qed.
  
  Lemma map_imap {A B C} (f : nat -> A -> B) (g : B -> C) xs :
    map g (imap f xs) = imap (λ i x, g (f i x)) xs.
  Proof.
    revert f g.
    induction xs; intros f g.
    - done.
    - cbn.
      by rewrite IHxs.
  Qed.

  (* Saving and restoring the stack. *)

  Lemma map_comp {A B C} (f: A -> B) (g: B -> C) xs :
    map g (map f xs) = map (g ∘ f) xs.
  Proof.
    by apply map_map.
  Qed.

  Lemma localimm_Mk_localidx :
    localimm ∘ Mk_localidx = id.
  Proof.
    reflexivity.
  Qed.

  Lemma interp_wl_length offset wl fr :
    wl_interp offset wl fr ->
    offset + length wl <= length (f_locs fr).
  Proof.
    unfold wl_interp.
    intros (vs & vs' & vs'' & -> & Hlen & Htyp).
    eapply Forall2_length in Htyp.
    rewrite !length_app.
    lia.
  Qed.


  Lemma run_codegen_set_locals idxs wt wl x wt' wl' es' :
    run_codegen (set_locals_w idxs) wt wl = inr (x, wt', wl', es') ->
    x = tt /\
    wt' = [] /\
    wl' = [].
  Proof.
    intros * Hcg.
    (* apply wps/inversion principles *)
    unfold set_locals_w in Hcg.
    cbn in Hcg.
    rewrite -rev_reverse in Hcg.
    unfold mapM_ in Hcg.
    do 2 rewrite mapM_comp in Hcg.
    rewrite map_comp in Hcg.
    rewrite rev_reverse in Hcg.
    rewrite map_rev in Hcg.
    inv_cg_bind Hcg res3 wt3 wt3' wl3 wl3' es5 es6 Hcg Hcg1.
    inv_cg_ret Hcg1; subst.
    apply wp_mapM_emit in Hcg.
    destruct Hcg as (Hres & Hwt & Hwl & Hes); subst res3 wt3 wl3 es5.
    done.
  Qed.

  Lemma cwp_set_locals_w tys L R Φ s E fe wt wl i localidxs idxs v wt' wl' wlf es fr vs evs :
    has_values evs vs ->
    run_codegen (set_locals_w localidxs) wt wl = inr (v, wt', wl', es) ->
    wl_interp (fe_wlocal_offset fe) (wl ++ wlf) fr ->
    i + (length tys) <= (fe_wlocal_offset fe) + (length wl) ->
    idxs = seq i (length tys) ->
    result_type_interp tys vs ->
    localidxs = map W.Mk_localidx idxs ->
    v = () /\
    wt' = [] /\
    wl' = [] /\
    ⊢ ↪[frame] fr -∗
      ↪[RUN] -∗
      (∀ f,
          ⌜frame_rel (λ i, i ∉ idxs) fr f⌝ ∗
          ⌜Forall2 (λ i v, f_locs f !! localimm i = Some v) localidxs vs⌝ -∗
          Φ f []) -∗
          CWP evs ++ es @ s; E UNDER L; R {{ Φ }}.
  Proof.
    intros Hhv Hcg Hwl Hin_range Hidxs Hrt Hlocals.
    apply run_codegen_set_locals in Hcg as H.
    destruct H as (-> & -> & ->).
    split; auto.
    split; auto.
    split; auto.
    iIntros "Hfr Hrun HΦ".
    apply interp_wl_length in Hwl.
    rewrite !length_app in Hwl.
    iRevert (Hcg Hin_range Hidxs Hrt Hlocals Hwl Hhv).
    iInduction vs as [| v vs' IH] using rev_ind forall (i idxs localidxs es evs tys fr); iIntros (Hcg Hin_range Hidxs Hrt Hlocals Hwl Hhv).
    - apply Forall2_length in Hrt as Hlen.
      destruct tys; last done.
      simpl in Hidxs.
      subst idxs localidxs.
      simpl in Hcg.
      inversion Hcg.
      simpl.
      iApply (cwp_val with "[$] [$]"); try done.
      1: by rewrite app_nil_r.
      iApply "HΦ".
      done.
    - apply Forall2_length in Hrt as Hlen.
      (* tys = tys' ++ [ty] *)
      assert (tys ≠ []) as Htysne.
      { intros Hnil. subst.
        simpl in Hrt.
        rewrite length_app in Hlen.
        simpl in Hrt.
        rewrite Nat.add_comm in Hlen.
        done.
      }
      apply exists_last in Htysne as [tys' [ty Htys]].
      subst tys.
      (* evs = evs' ++ [ev] *)
      apply has_values_app_inv in Hhv as (evs' & ev & Heq & Hhv' & Hhv_v).
      apply has_values_length in Hhv_v as Hev_len.
      destruct ev as [|ev []]; try done.
      subst evs.

      rewrite length_app in Hidxs.
      simpl in Hidxs.
      rewrite seq_app in Hidxs.
      simpl in Hidxs.
      subst idxs.
      rewrite map_app in Hlocals.
      simpl in Hlocals.
      subst localidxs.
      simpl in Hcg.
      unfold set_locals_w in Hcg.
      unfold compose in Hcg.
      rewrite rev_unit in Hcg.
      apply wp_mapM__cons in Hcg.
      destruct Hcg as (() & wt_a & wl_a & es_set & wt_tys & wl_tys & es_rest & Hcg_set & Hcg_rest & _ & Hwt' & Hwl' & Hes).
      subst.
      destruct wt_a as [|]; last done.
      destruct wl_a as [|]; last done.
      destruct wt_tys as [|]; last done.
      destruct wl_tys as [|]; last done.
      inv_cg_emit Hcg_set; subst.

      assert (i + length tys' < length (f_locs fr)) as Hin_range'.
      {
        rewrite length_app in Hin_range. simpl in Hin_range. lia.
      }

      iEval (rewrite app_assoc).
      iApply (cwp_seq with "[Hfr Hrun]").
      {
        iEval (rewrite -app_assoc).
        iApply cwp_val_app; first done.
        iSimpl.
        apply has_values_to_consts_inv in Hhv_v.
        simpl in Hhv_v.
        inversion Hhv_v; subst.
        iApply (cwp_local_set with "[] [$] [$]"); first done.
        unfold fvs_combine.
        instantiate (1 := λ fr' vs, ⌜fr' = {| W.f_locs := _; W.f_inst := _ |} /\ vs = vs'⌝%I).
        iPureIntro.
        split; first done.
        by rewrite app_nil_r.
      }
      iIntros (??) "[-> ->] Hfr Hrun".
      iApply ("IH" with "[$] [$] [HΦ]").
      5: {
        iPureIntro.
        apply Forall2_app_inv in Hrt as [Hrt1 Hrt2]; first done.
        rewrite !length_app in Hlen.
        simpl in Hlen.
        lia.
      }
      4: instantiate (1 := i); done.
      4: done.
      3: {
        rewrite length_app in Hin_range.
        simpl in Hin_range.
        iPureIntro.
        lias.
      }
      2: {
        iPureIntro.
        unfold set_locals_w.
        unfold compose.
        rewrite !app_nil_r in Hcg_rest.
        done.
      }
      3: iPureIntro; apply has_values_to_consts.
      2: {
        iPureIntro.
        simpl.
        rewrite length_insert.
        lias.
      }
      iIntros (f [Hfrel Hf2]).
      iApply "HΦ".
      iPureIntro.
      simpl.
      destruct Hfrel as [Hfrel_locs Hfinst].
      unfold mask_locs_eq in Hfrel_locs.
      specialize (Hfrel_locs (i + length tys')) as Hlast.
      rewrite list_lookup_insert in Hlast.
      rewrite decide_True in Hlast.
      2: done.
      rewrite list_elem_of_In in Hlast.
      rewrite in_seq in Hlast.
      have Hv : Some v = f_locs f !! (i + length tys').
      1: apply Hlast. lias.
      split.
      2: {
        apply Forall2_app.
        - exact Hf2.
        - apply Forall2_cons; split; last by apply Forall2_nil.
          done.
      }
      unfold frame_rel.
      simpl in Hfinst.
      split; last done.
      unfold mask_locs_eq.
      intros j Hinj.
      specialize (Hfrel_locs j) as Hj.
      assert (f_locs
      {|
        W.f_locs :=
        <[i + length tys':=v]> (f_locs fr);
        W.f_inst := f_inst fr
      |}
      !! j = f_locs f !! j) as Hlj.
      {
        apply Hj.
        apply not_elem_of_app in Hinj.
        lias.
      }
      rewrite -Hlj.
      simpl.
      apply not_elem_of_app in Hinj as [Hinj1 Hinj2].
      apply not_elem_of_cons in Hinj2 as [Hneq _].
      rewrite list_lookup_insert_ne; [reflexivity | done].
  Qed.

  Lemma cwp_set_locals_w_non_fe tys L R Φ s E fe wt wl localidxs idxs v wt' wl' wlo wlf es fr vs evs :
      has_values evs vs ->
      run_codegen (set_locals_w localidxs) wt (wl ++ tys ++ wlo) = inr (v, wt', wl', es) ->
      wl_interp (fe_wlocal_offset fe) (wl ++ tys ++ wlo ++ wlf) fr ->
      idxs = seq (fe_wlocal_offset fe + length wl) (length tys) ->
      result_type_interp tys vs ->
      localidxs = map W.Mk_localidx idxs ->
      v = () ∧
      wt' = [] /\
      wl' = [] /\
      ⊢ ↪[frame] fr -∗
        ↪[RUN] -∗
        (∀ f,
            ⌜frame_rel (λ i, i ∉ idxs) fr f⌝ ∗
            ⌜Forall2 (λ i v, f_locs f !! localimm i = Some v) localidxs vs⌝ -∗
            Φ f []) -∗
            CWP evs ++ es @ s; E UNDER L; R {{ Φ }}.
  Proof.
    intros Hhv Hcg Hwl_interp Hidxs Hrt Hlocalidxs.
    eapply cwp_set_locals_w with
      (i := fe_wlocal_offset fe + length wl)
      (wl := wl ++ tys ++ wlo)
      (wlf := wlf); try done.
      - by rewrite -!app_assoc.
      - rewrite !length_app. rewrite !Nat.add_assoc. lia.
  Qed.

  Lemma wp_save_stack1 ty :
    forall s E Φ fe wt wl idx wt' wl' es fr (v: value),
      wl_interp (fe_wlocal_offset fe) (wl ++ wl') fr ->
      value_type_interp ty v ->
      run_codegen (save_stack1 fe ty) wt wl = inr (idx, wt', wl', es) ->
      idx = W.Mk_localidx (fe_wlocal_offset fe + length wl) /\
        wt' = [] /\
        wl' = [ty] /\
        ⊢ ↪[frame] fr -∗
          ↪[RUN] -∗
          Φ (immV []) -∗
          WP (AI_basic (BI_const v) :: to_e_list es) @ s; E
             {{ v', (Φ v' ∗ ↪[RUN]) ∗
                     ↪[frame] {| f_locs := seq.set_nth v (f_locs fr) (localimm idx) v;
                                 f_inst := f_inst fr |} }}.
  Proof.
    intros * Hwl Hv.
    unfold save_stack1.
    intros Hcg.
    inv_cg_bind Hcg res wt1 wt1' wl1 wl1' es1 es2 Hcg1 Hcg2.
    inv_cg_bind Hcg2 res2 wt2 wt2' wl2 wl2' es3 es4 Hcg2 Hcg3.
    subst.
    inv_cg_ret Hcg3; subst.
    apply wp_wlalloc in Hcg1.
    destruct Hcg1 as (Hres & Hwt1 & Hwl1 & Hes1); subst res wt1 wl1 es1.
    inv_cg_emit Hcg2.
    subst es3 wt2 wl2 res2.
    rewrite !app_nil_r in Hwl.
    rewrite !app_nil_r.
    split; auto.
    split; auto.
    split; auto.
    iIntros "Hfr Hrun HΦ".
    cbn.
    iApply (wp_set_local with "[HΦ] [$Hfr]"); eauto.
    destruct Hwl as (locs & locs__wl & locs' & Hlocs & Hoff & Hlocsty).
    subst.
    cbn.
    apply Forall2_length in Hlocsty.
    rewrite Hlocs.
    rewrite !length_app.
    rewrite -Hlocsty -Hoff.
    rewrite !length_app.
    cbn.
    lia.
  Qed.

  Lemma cwp_save_stack_w esv tys Φ L R localidxs :
    forall s E fe wt wl idxs wt' wl' wlf es fr vs,
      run_codegen (save_stack_w fe tys) wt wl = inr (localidxs, wt', wl', es) ->
      wl_interp (fe_wlocal_offset fe) (wl ++ wl' ++ wlf) fr ->
      result_type_interp tys vs ->
      has_values esv vs ->
      idxs = seq (fe_wlocal_offset fe + length wl) (length tys) ->
      localidxs = map W.Mk_localidx idxs /\
      wt' = [] /\
      wl' = tys /\
      ⊢ ↪[frame] fr -∗
        ↪[RUN] -∗
        (∀ f,
            ⌜frame_rel (λ i, i ∉ idxs) fr f⌝ ∗
            ⌜Forall2 (fun i v => f_locs f !! localimm i = Some v) localidxs vs⌝ -∗
            Φ f []) -∗
        CWP (esv ++ es) @ s; E UNDER L; R {{ Φ }}.
  Proof.
    intros * Hcg Hwl Hresult Hhas_values Hidxs.
    unfold save_stack_w in Hcg.
    inv_cg_bind Hcg res wt1 wt1' wl1 wl1' es1 es2 Hcg1 Hcg2.
    inv_cg_bind Hcg2 res2 wt2 wt2' wl2 wl2' es3 es4 Hcg2 Hcg3.
    inv_cg_ret Hcg3; subst.
    apply wp_wlallocs in Hcg1.
    destruct Hcg1 as (Hres1 & Hwt1 & Hwl1 & Hes1); subst.
    rewrite imap_seq in Hcg2.
    rewrite imap_seq.
    split; first done.
    rewrite app_nil_r in Hcg2.
    rewrite -(app_nil_r tys) in Hcg2.
    rewrite !app_nil_r !app_nil_l.
    eapply cwp_set_locals_w_non_fe in Hcg2; try done.
    2: by rewrite -!app_assoc in Hwl.
    2: by rewrite app_nil_r.
    destruct Hcg2 as (-> & -> & -> & H).
    split; auto.
    split; first by rewrite app_nil_r.
    iDestruct H as "Hspec".
    iIntros "Hfr Hrun HΦ".
    iApply ("Hspec" with "[$] [$]").
    iIntros (f) "Hinv".
    iEval (rewrite app_nil_r) in "Hinv".
    by iSpecialize ("HΦ" $! f with "Hinv").
  Qed.


  Lemma wp_get_locals vars vals E f :
    Forall2 (fun x v => f.(f_locs) !! x = Some v) vars vals ->
    ⊢ □ ∀ Φ,
            ↪[RUN] -∗
            ↪[frame] f -∗
            (∀ w, ⌜w = immV vals⌝ -∗ ↪[RUN] -∗ ↪[frame] f -∗ Φ w) -∗
            WP to_e_list (List.map BI_get_local vars) @ NotStuck; E {{ Φ }}.
  Proof.
    induction 1.
    - iIntros (Φ) "!> Hrun Hfr HΦ".
      cbn.
      iApply wp_nil_noctx.
      iApply ("HΦ" with "[//] [$] [$]").
    - iIntros (Φ) "!> Hrun Hfr HΦ".
      cbn.
      wp_chomp 1.
      rewrite take_0 drop_0.
      set (Φ' := (λ w, (⌜w = immV [y]⌝ ∗ ↪[RUN]) ∗ ↪[frame]f)%I).
      iApply (wp_seq _ _ Φ Φ').
      iSplitR. { iIntros "((%Hw & _) & _)" => //. }
      iSplitL "Hrun Hfr".
      {
        iApply (wp_get_local with "[] [$] [$]"); auto.
        assumption.
      }
      iIntros (w) "((%Hw & Hrun) & Hfr)".
      subst w.
      iApply (wp_wand _ _ _ (λ w, (⌜w = immV (y::l')⌝ ∗ ↪[RUN]) ∗ ↪[frame] f)%I with "[Hfr Hrun]"); auto.
      iApply wp_val_app; auto.
      iSplitR.
      { iIntros "!> ((%Hw & _) & _)" => //. }
      iApply (IHForall2 with "[$] [$]").
      + iIntros (w) "%Hw Hrun Hfr".
        iFrame.
        subst w; auto.
      + iIntros (v) "[[%Hv Hrun] Hfr]".
        iApply ("HΦ" with "[//] [$] [$]").
  Qed.

  Lemma big_and_forall2 {A} (env vs: list A) (idxs: list nat) :
    length idxs = length vs ->
    (forall k i, idxs !! k = Some i -> env !! i = vs !! k) ->
    Forall2 (fun x v => env !! x = Some v) idxs vs.
  Proof.
    remember (length vs) as len.
    revert Heqlen. revert env vs idxs.
    induction len; intros * Hlen1 Hlen2 Hbig.
    - destruct vs; destruct idxs; simpl in *; try congruence.
      done.
    - destruct vs as [| v vs]; destruct idxs as [| idx idxs]; simpl in *; try congruence.
      apply Forall2_cons; split.
      + specialize (Hbig 0 idx eq_refl).
        done.
      + apply IHlen; eauto.
        intros k i Hki.
        by apply (Hbig (S k) i).
  Qed.

  Lemma wp_restore_stack_w idxs vs wt wt' wl wl' es E ret f Φ :
    length idxs = length vs ->
    run_codegen (restore_stack idxs) wt wl = inr (ret, wt', wl', es) ->
    ret = tt /\
      wt' = [] /\
      wl' = [] /\
      ⊢ ↪[frame] f -∗
        ↪[RUN] -∗
        Φ (immV vs) -∗
        (* this condition appears in the postcondition of the save_stack wp lemma. *)
        ⌜Forall2 (λ i v, f_locs f !! localimm i = Some v) idxs vs⌝ -∗
        WP to_e_list es @ NotStuck; E {{ v, Φ v ∗ ↪[RUN] ∗ ↪[frame] f }}.
  Proof.
    unfold restore_stack.
    intros Hlen Hcg.
    unfold get_locals_w in Hcg.
    apply wp_ignore in Hcg.
    destruct Hcg as [-> [ret' Hcg]].
    do 2 rewrite mapM_comp in Hcg.
    apply wp_mapM_emit in Hcg.
    destruct Hcg as (-> & -> & -> & ->).
    split; auto.
    split; auto.
    split; auto.
    iIntros "Hfr Hrun HΦ Hlocs".
    repeat rewrite big_andL_pure; eauto.
    iDestruct "Hlocs" as "%Hlocs".
    iApply (wp_get_locals with "[$Hrun] [$Hfr]");
      [|iIntros (w ->) "Hrun Hfr"; by iFrame].
    apply big_and_forall2.
    - by rewrite length_map.
    - intros k i Hki.
      rewrite list_lookup_fmap in Hki.
      rewrite fmap_Some in Hki.
      destruct Hki as [x [Hx Hi]]; subst.
      eapply Forall2_lookup_l in Hx; eauto.
      destruct Hx as [y [Hvs Hwhatever]].
      rewrite Hvs.
      rewrite Hwhatever.
      done.
  Qed.

  Lemma lwp_restore_stack_w_generic idxs vs wt wt' wl wl' es E ret f Φ :
    length idxs = length vs ->
    run_codegen (restore_stack idxs) wt wl = inr (ret, wt', wl', es) ->
    ret = tt /\
      wt' = [] /\
      wl' = [] /\
      ⊢ ↪[frame] f -∗
        ↪[RUN] -∗
        ⌜Forall2 (λ i v, f_locs f !! localimm i = Some v) idxs vs⌝ -∗
        Φ.(lp_fr_inv) f -∗
        Φ.(lp_val) f vs -∗
        lenient_wp NotStuck E (to_e_list es) Φ.
  Proof.
    intros Hlen Hcodegen.
    eapply (wp_restore_stack_w _ _ _ _ _ _ _ E _ f
    (λ w, ⌜w = immV vs⌝ ∗ Φ.(lp_fr_inv) f ∗ Φ.(lp_val) f vs)%I)
    in Hcodegen; [| eassumption].
    destruct Hcodegen as (-> & -> & -> & Hwp).
    do 3 split; try done.
    iIntros "Hfr Hrun Hidxs Hfr_inv Hval".
    unfold lenient_wp.
    iApply (wp_wand with "[Hfr Hrun Hidxs Hfr_inv Hval]").
    - iApply (Hwp with "[$] [$] [Hfr_inv Hval] [$]").
      by iFrame.
    - iIntros (v) "((-> & Hfr_inv & Hval) & Hrun & Hfr)".
      unfold denote_logpred; cbn.
      iExists f.
      iFrame.
  Qed.

  Lemma lwp_restore_stack_w idxs vs wt wt' wl wl' es E ret f :
    length idxs = length vs ->
    run_codegen (restore_stack idxs) wt wl = inr (ret, wt', wl', es) ->
    ret = tt /\
      wt' = [] /\
      wl' = [] /\
      ⊢ ↪[frame] f -∗
        ↪[RUN] -∗
        (* this condition appears in the postcondition of the save_stack wp lemma. *)
        ⌜Forall2 (λ i v, f_locs f !! localimm i = Some v) idxs vs⌝ -∗
        lenient_wp NotStuck E (to_e_list es)
          {| lp_fr_inv _ := True;
             lp_val f' vs' := ⌜f' = f /\ vs' = vs⌝%I;
             lp_trap := False;
             lp_br _ _ _ := False;
             lp_ret _ := False;
             lp_host _ _ _ _ := False |}.
  Proof.
    intros Hlen Hcodegen.
    edestruct (lwp_restore_stack_w_generic idxs vs wt wt' wl wl' es E ret f) as (-> & -> & -> & Hwp); try done.
    do 3 split; try done.
    iIntros "Hfr Hrun Hidxs".
    by iApply (Hwp with "Hfr Hrun Hidxs").
  Qed.

  Lemma cwp_restore_stack_w_generic idxs vs wt wt' wl wl' es E ret f L R Φ :
    length idxs = length vs ->
    run_codegen (restore_stack idxs) wt wl = inr (ret, wt', wl', es) ->
    ret = tt /\
      wt' = [] /\
      wl' = [] /\
      ⊢ ↪[frame] f -∗
        ↪[RUN] -∗
        Φ f vs -∗
        ⌜Forall2 (λ i v, f_locs f !! localimm i = Some v) idxs vs⌝ -∗
        CWP es @ NotStuck; E UNDER L; R {{ Φ }}.
  Proof.
    intros Hlen Hcodegen.
    destruct (lwp_restore_stack_w_generic idxs vs wt wt' wl wl' es E ret f
    (cwp_post_lp L R Φ) Hlen Hcodegen)
    as (-> & -> & -> & Hwp).
    do 3 split; try done.
    iIntros "Hfr Hrun HΦ Hidxs".
    unfold cwp_wasm.
    iApply (Hwp with "Hfr Hrun Hidxs").
    - simpl. done.
    - simpl. iExact "HΦ".
  Qed.

  Lemma cwp_restore_stack_w idxs vs wt wt' wl wl' es E ret f L R :
    length idxs = length vs ->
    run_codegen (restore_stack idxs) wt wl = inr (ret, wt', wl', es) ->
    ret = tt /\
      wt' = [] /\
      wl' = [] /\
      ⊢ ↪[frame] f -∗
        ↪[RUN] -∗
        ⌜Forall2 (λ i v, f_locs f !! localimm i = Some v) idxs vs⌝ -∗
        CWP es @ NotStuck; E UNDER L; R {{ f'; vs', ⌜f' = f /\ vs' = vs⌝ }}.
  Proof.
    intros Hlen Hcodegen.
    destruct (cwp_restore_stack_w_generic idxs vs wt wt' wl wl' es E ret f L R
                (fun f' vs' => ⌜f' = f /\ vs' = vs⌝)%I
                Hlen Hcodegen)
      as (-> & -> & -> & Hwp).
    do 3 split; try done.
    iIntros "Hfr Hrun Hidxs".
    by iApply (Hwp with "[$] [$] [//]").
  Qed.

  Lemma cwp_create_defaults types wt wl x wt' wl' es s E L R f Φ :
  run_codegen (create_defaults types) wt wl = inr (x, wt', wl', es) ->
  x = tt /\
  wt' = [] /\
  wl' = [] /\
  ⊢ ↪[frame] f -∗
    ↪[RUN] -∗
    Φ f (map (default_of_value_type) types) -∗
    CWP es @ s; E UNDER L; R {{ Φ }}.
Proof.
  intros Hcg.
  apply run_codegen_create_defaults in Hcg.
  destruct Hcg as (-> & -> & -> & ->).
  do 3 (split; try done).
  iIntros "Hfr Hrun HΦ".
  iApply (cwp_val with "[$] [$] HΦ").
  rewrite -map_comp.
  apply has_values_to_consts.
Qed.

Lemma cwp_drop_consts types wt wl x wt' wl' es E L R f Φ evs :
  length evs = length types ->
  is_consts evs ->
  run_codegen (drop_consts types) wt wl = inr (x, wt', wl', es) ->
  x = tt /\
  wt' = [] /\
  wl' = [] /\
  ⊢ ↪[frame] f -∗
    ↪[RUN] -∗
    Φ f [] -∗
    CWP evs ++ es @ E UNDER L; R {{ Φ }}.
Proof.
  intros Hlen Hconsts Hcg.
  apply run_codegen_drop_consts in Hcg.
  destruct Hcg as (-> & -> & -> & ->).
  do 3 (split; try done).
  iIntros "Hfr Hrun HΦ".
  rewrite -Hlen.
  by iApply (cwp_drops with "[$] [$] [HΦ]").
Qed.

  Lemma wp_bind_err {A B} c (f : A -> codegen B) wt wl err :
    run_codegen (c ≫= f) wt wl = inl err ->
    run_codegen c wt wl = inl err \/
      exists x wt' wl' es,
        run_codegen c wt wl = inr (x, wt', wl', es) /\
        run_codegen (f x) (wt ++ wt') (wl ++ wl') = inl err.
  Proof.
    intros.
    unfold run_codegen in H.
    destruct (WriterMonad.runWriterT _) eqn:Hrun in H; [|congruence].
    destruct (runAccumT _) as [[err' | val]] eqn:Harun in Hrun; [|cbn in *; congruence].
    destruct (c ≫= f) as [x] eqn:? in Harun.
    cbn in *.
    inversion Hrun; subst.
    inversion H; subst.
    clear Hrun.
    inversion Heqc0; subst.
    inversion Harun; subst.
    clear Heqc0 Harun.
    destruct (WriterMonad.runWriterT (runAccumT c (wt, wl))) eqn:Hc.
    - left.
      unfold run_codegen.
      rewrite Hc; congruence.
    - right.
      destruct p as [ret' es'].
      cbn in H1.
      destruct (WriterMonad.runWriterT _) eqn:? in H1; [|cbn in *; try congruence].
      destruct ret' as [ret' [wt' wl']].
      inversion H1; subst e.
      do 4 eexists.
      split.
      + cbn. unfold run_codegen.
        rewrite Hc.
        cbn.
        eauto.
      + unfold run_codegen; cbn.
        unfold mbind in Heqy. cbn in Heqy.
        destruct (WriterMonad.runWriterT (runAccumT (f ret') (wt ++ wt', wl ++ wl'))) eqn:Hf.
        * rewrite Hf in Heqy. rewrite Hf. by inversion Heqy.
        * destruct p as [[? ?] ?]; cbn in Heqy.
          rewrite Hf in Heqy. cbn in Heqy.
          congruence.
  Qed.

  Lemma ignore_err_faithful {A} (c : codegen A) wt wl err :
    run_codegen (util.ignore c) wt wl = inl err ->
    run_codegen c wt wl = inl err.
  Proof.
    unfold util.ignore.
    intros Hi.
    apply wp_bind_err in Hi.
    destruct Hi as [? | (x & wt' & wl' & es & Hc & Hret)]; first done.
    cbn in Hret.
    congruence.
  Qed.

  Lemma ignore_cg_agree {A} (c : codegen A) wt wt' wl wl' es ret :
    run_codegen c wt wl = inr (ret, wt', wl', es) ->
    run_codegen (util.ignore c) wt wl = inr ((), wt', wl', es).
  Proof.
    destruct (run_codegen (util.ignore c) wt wl) as [err | [[[reti wti] wli] esi]] eqn:?.
    - apply ignore_err_faithful in Heqs.
      congruence.
    - intros.
      eapply wp_ignore in Heqs.
      destruct Heqs as (-> & ret' & Hc).
      congruence.
  Qed.

End CodeGen.
