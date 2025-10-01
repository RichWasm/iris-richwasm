Require Import iris.proofmode.tactics.

From stdpp Require Import list.
From RichWasm Require Import syntax typing util.
From RichWasm.compiler Require Import prelude codegen util.
From RichWasm.iris Require Import autowp gc.
From RichWasm.iris.logrel Require Import relations.

Module W := Wasm.operations.

Set Bullet Behavior "Strict Subproofs".

Section CodeGen.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!rwasm_gcG Σ}.

  Variable sr : store_runtime.
  Variable me : module_env.
  Variable F : function_ctx.
  Variable L : local_ctx.
  Variable WL : wlocal_ctx.

  Lemma wp_if_c {A B} s E i tf (c1 : codegen A) (c2 : codegen B) wl wl' es x y Φ (f: frame) :
    run_codegen (if_c tf c1 c2) wl = inr (x, y, wl', es) ->
    exists wl1 es1 es2,
    run_codegen c1 wl = inr (x, wl1, es1) /\
    run_codegen c2 wl1 = inr (y, wl', es2) /\
    ⊢ ↪[frame] f -∗
      ↪[RUN] -∗
      ((⌜i <> Wasm_int.int_zero i32m⌝ ∧
        ▷ (↪[frame] f -∗ ↪[RUN] -∗ WP [AI_basic (BI_block tf es1)] @ s; E {{ v, Φ v }})) ∨
       (⌜i = Wasm_int.int_zero i32m⌝ ∧
        ▷ (↪[frame] f -∗ ↪[RUN] -∗ WP [AI_basic (BI_block tf es2)] @ s; E {{ v, Φ v }}))) -∗
      WP to_e_list (BI_const (VAL_int32 i) :: es) @ s; E {{ v, Φ v }}.
  Proof.
    intros Hcomp.
    unfold if_c in Hcomp.

    apply run_codegen_bind_dist in Hcomp.
    destruct Hcomp as (x1 & wl1 & es1 & es2 & Hcomp1 & Hcomp2 & Hes).
    destruct x1 as [x' es1'].
    subst es.
    apply run_codegen_capture in Hcomp1.
    destruct Hcomp1 as [Hcomp1 ->].

    apply run_codegen_bind_dist in Hcomp2.
    destruct Hcomp2 as (x2 & wl2 & es3 & es4 & Hcomp2 & Hcomp3 & Hes).
    destruct x2 as [y' es2'].
    subst es2.

    apply run_codegen_capture in Hcomp2.
    destruct Hcomp2 as [Hcomp2 ->].

    cbn in Hcomp3.
    inversion Hcomp3.
    subst x' y' wl2 es4.
    clear Hcomp3.
    rename es1' into es1, es2' into es2.

    exists wl1, es1, es2.
    split; first assumption.
    split; first assumption.

    iIntros "Hfr Hrun Hbl".
    iSimpl.
    iDestruct "Hbl" as "[[%Hi Hbl] | [%Hi Hbl]]".
    - by iApply (wp_if_true with "[Hfr] [Hrun]"); auto.
     - by iApply (wp_if_false with "[Hfr] [Hrun]"); auto.
  Qed.

  (* Generic monad operations. *)
  Lemma wp_ret {A} (a: A) wl v wl' es :
    run_codegen (Monad.ret a) wl = inr (v, wl', es) ->
    v = a /\ wl' = wl /\ es = [].
  Proof.
    cbn.
    intros Hcg.
    inversion Hcg; subst; done.
  Qed.

  Lemma wp_mapM_nil {A B} (f: A -> codegen B) wl ys wl' es :
    run_codegen (mapM f []) wl = inr (ys, wl', es) ->
    wl' = wl /\
    ys = [] /\
    es = [].
  Proof.
    cbn.
    intros Hcg.
    inversion Hcg.
    done.
  Qed.
  
  Lemma wp_mapM_cons {A B} (f: A -> codegen B) wl yss wl' es x xs :
    run_codegen (mapM f (x :: xs)) wl = inr (yss, wl', es) ->
    ∃ ys_x wl_x es_x yss_xs wl_xs es_xs,
      run_codegen (f x) wl = inr (ys_x, wl_x, es_x) /\
      run_codegen (mapM f xs) wl_x = inr (yss_xs, wl_xs, es_xs) /\
      yss = ys_x :: yss_xs /\
      wl' = wl_xs /\
      es = es_x ++ es_xs.
  Proof.
    cbn.
    intros Hcg.
    inv_cg_bind Hcg res1 wl1 es_fx es2 Hfx Hcg1.
    inv_cg_bind Hcg1 res2 wl2 es_fxs es3 Hfxs Hcg2.
    cbn in Hcg2.
    inversion Hcg2.
    subst.
    repeat eexists; eauto.
    rewrite app_nil_r; eauto.
  Qed.
  
  Lemma wp_mapM_emit wl es xs wl' es' :
    run_codegen (mapM emit es) wl = inr (xs, wl', es') ->
    xs = repeat tt (length es) /\
    wl' = wl /\
    es' = es.
  Proof.
    revert es' xs.
    induction es; intros es' xs Hemit.
    - cbn in Hemit.
      inversion Hemit; subst.
      done.
    - apply wp_mapM_cons in Hemit.
      destruct Hemit as (ys_x & wl_x & es_x & yss_xs & wl_xs & es_xs & Hemit & Hemits & Hx & Hwl' & Hes').
      subst xs wl' es'.
      inv_cg_emit Hemit; subst.
      apply IHes in Hemits.
      destruct Hemits as (Hyss & Hwl_xs & Hes_xs).
      inversion Hes_xs; subst es_xs wl_xs.
      split; eauto.
      cbn.
      congruence.
  Qed.

  (* State monad operations. *) 
  Lemma wp_get wl v wl' es :
    run_codegen MonadState.get wl = inr (v, wl', es) ->
    v = wl /\
    wl' = wl /\
    es = [].
  Proof.
    unfold MonadState.get; cbn.
    intros Heq.
    inversion Heq; subst.
    tauto.
  Qed.

  Lemma wp_put wl v wl' wl'' es :
    run_codegen (MonadState.put wl') wl = inr (v, wl'', es) ->
    v = () /\
    wl'' = wl' /\
    es = [].
  Proof.
    unfold MonadState.put; cbn.
    intros Heq.
    inversion Heq; subst.
    tauto.
  Qed.
  
  (* Allocating locals. *)
  
  (* Monotone interpretation of a wlocal_ctx *)
  Definition interp_wl (wlocal_offset : nat) (wl : wlocal_ctx) (inst: instance) : frame -> Prop :=
    λ fr, ∃ vs vs__wl vs', fr = Build_frame (vs ++ vs__wl ++ vs') inst /\
                         length vs = wlocal_offset /\
                         result_type_interp wl vs__wl.

  Lemma wp_wlalloc fe ty wl wl' idx es :
    run_codegen (wlalloc fe ty) wl = inr (idx, wl', es) ->
    idx = Mk_localidx (fe_wlocal_offset fe + length wl) /\
    wl' = wl ++ [ty] /\
    es = [].
  Proof.
    unfold wlalloc.
    intros Hcg.
    inv_cg_bind Hcg res wl1 es_get es2 Hget Hcg1.
    inv_cg_bind Hcg1 res1 wl2 es_put es_ret Hput Hret.
    apply wp_get in Hget.
    apply wp_put in Hput.
    apply wp_ret in Hret.
    destruct Hget as (? & ? & ?).
    destruct Hput as (? & ? & ?).
    destruct Hret as (? & ? & ?).
    subst; done.
  Qed.

  Lemma wp_wlallocs fe tys wl idxs wl' es :
    run_codegen (mapM (wlalloc fe) tys) wl = inr (idxs, wl', es) ->
    idxs = imap (λ i _, Mk_localidx (fe_wlocal_offset fe + length wl + i)) tys /\
    wl' = wl ++ tys /\
    es = [].
  Proof.
    revert wl idxs wl' es.
    induction tys.
    - cbn; intros * Hcg.
      inversion Hcg.
      rewrite app_nil_r.
      done.
    - intros * Hcg.
      eapply (wp_mapM_cons (wlalloc fe)) in Hcg.
      destruct Hcg as (ys_a & wl_a & es_a & yss_tys & wl_tys  & es_tys & Hcg_a & Hcg_tys & Hidxs & Hwl' & Hes).
      subst.
      apply IHtys in Hcg_tys.
      destruct Hcg_tys as (Himap & Hwl_tys & Hes_tys); subst.
      apply wp_wlalloc in Hcg_a.
      destruct Hcg_a as (Hys_a & Hwl_a & Hes_a); subst.
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
  
  Lemma wp_save_stack1 ty :
    forall s E Φ inst fe wl idx wl' es fr (v: value),
      interp_wl (fe_wlocal_offset fe) wl' inst fr ->
      value_type_interp ty v ->
      run_codegen (save_stack1 fe ty) wl = inr (idx, wl', es) ->
      idx = W.Mk_localidx (fe_wlocal_offset fe + length wl) /\
      wl' = wl ++ [ty] /\
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
    inv_cg_bind Hcg res wl1 es1 es2 Hcg1 Hcg2.
    inv_cg_bind Hcg2 res2 wl2 es3 es4 Hcg2 Hcg3.
    subst.
    inv_cg_ret Hcg3; subst.
    apply wp_wlalloc in Hcg1.
    destruct Hcg1 as (Hres & Hwl1 & Hes1); subst res wl1 es1.
    inv_cg_emit Hcg2.
    subst es3 wl2 res2.
    split; auto.
    split; auto.
    iIntros "Hfr Hrun HΦ".
    cbn.
    iApply (wp_set_local with "[HΦ] [$Hfr]"); eauto.
    destruct Hwl as (locs & locs__wl & locs' & Hlocs & Hoff & Hlocsty).
    subst.
    cbn.
    apply Forall2_length in Hlocsty.
    rewrite !length_app.
    rewrite -Hlocsty -Hoff.
    rewrite !length_app.
    cbn.
    lia.
  Qed.
  
  (* Gross internal induction for save_stack_w proof. *)
  Lemma wp_save_stack_w_ind len : forall vs start fr Φ s E,
    length vs = len ->
    start + len <= length (f_locs fr) ->
    ⊢ ↪[frame] fr -∗
      ↪[RUN] -∗
      Φ (immV []) -∗
      WP W.v_to_e_list vs ++ to_e_list (rev (map W.BI_set_local (seq start len))) @ s; E
      {{ v, (Φ v ∗  ↪[RUN]) ∗
          ∃ f : frame,
          ↪[frame]f ∗
          ⌜∀ i, i ∉ seq start len -> f_locs f !! i = f_locs fr !! i⌝ ∗
          [∧ list] k↦i ∈ seq start len, ⌜f_locs f !! i = vs !! k⌝ }}.
  Proof.
    induction len; intros.
    - cbn; intros.
      destruct vs; cbn in H; try congruence.
      cbn.
      iIntros.
      iApply wp_nil_noctx.
      iFrame.
      repeat rewrite big_andL_pure; eauto.
    - iIntros "Hfr Hrun HΦ".
      rewrite -length_rev in H.
      destruct (rev vs) as [|v0 vs'] eqn:Hrev; cbn in H; [congruence|].
      assert (vs = rev vs' ++ [v0]).
      {
        apply rev_inj; by rewrite Hrev rev_unit rev_involutive.
      }
      subst vs.
      rewrite -map_rev.
      rewrite seq_S.
      rewrite rev_unit; cbn.
      unfold W.v_to_e_list.
      change @seq.map with map.
      rewrite map_app.
      cbn.
      match goal with
      | |- context [(?vs ++ [?v]) ++ ?e :: ?es] =>
          replace ((vs ++ [v]) ++ e :: es)
          with ((vs ++ ([v; e])) ++ es)
          by (do 2 rewrite -app_assoc; auto)
      end.
      set (Ψ := (λ w, ⌜w = immV (rev vs')⌝ ∗ 
                      ↪[RUN] ∗
                      ↪[frame] {| f_locs := seq.set_nth v0 (f_locs fr) (start + len) v0;
                                   f_inst := f_inst fr |})%I : val -> iProp Σ).
      iApply (wp_seq _ _ _ Ψ).
      iSplitR; first last;
        [iSplitR "HΦ"|].
      + iApply wp_val_app'.
        iSplitR; first last.
        {
          iApply (wp_wand with "[Hfr Hrun]").
          - iApply (wp_set_local with "[] [$] [$]").
            + lia.
            + fill_imm_pred.
          - iIntros (v) "((-> & Hrun) & Hfr)".
            cbn.
            rewrite seq.cats0.
            by iFrame.
        }
        iIntros "!> (%Heq & _ & _)"; congruence.
      + iIntros (w) "(-> & Hrun & Hfr)".
        cbn.
        rewrite map_rev.
        iApply (wp_wand with "[Hrun Hfr HΦ]").
        * iApply (IHlen with "[$] [$]"); eauto.
          -- rewrite length_rev; congruence.
          -- cbn.
             rewrite <- fmap_insert_set_nth by lia.
             rewrite length_insert.
             lia.
        * iIntros (v) "((HΦ & Hrun) & (%f & Hfr & Hbase & Hsaved))".
          cbn.
          iFrame.
          repeat rewrite big_andL_pure.
          iDestruct "Hbase" as "%Hbase".
          iDestruct "Hsaved" as "%Hsaved".
          iPureIntro.
          split; intros * Hget.
          -- rewrite -seq_S in Hget.
             rewrite elem_of_seq in Hget.
             rewrite Hbase; try (rewrite elem_of_seq; lia).
             destruct (f_locs fr !! i) eqn:Hfri.
             ++ erewrite set_nth_read_neq; try lia; eauto.
             ++ apply lookup_ge_None_1 in Hfri.
                apply lookup_ge_None_2.
                rewrite set_nth_length_eq; auto.
                rewrite -length_is_size.
                lia.
          -- apply lookup_app_Some in Hget.
             destruct Hget as [Hget|[Hlen Hget]].
             ++ apply lookup_seq in Hget.
                destruct Hget as [-> Hlen].
                rewrite lookup_app_l.
                erewrite Hsaved; eauto.
                rewrite lookup_seq; auto.
                rewrite length_rev; lia.
             ++ rewrite list_lookup_singleton in Hget.
                destruct (k - length _) eqn:Hidx; try congruence.
                rewrite length_seq in Hidx Hlen.
                inversion Hget; subst.
                assert (k = len) by lia.
                subst k.
                rewrite Hbase.
                rewrite set_nth_read.
                inversion H.
                rewrite lookup_app_r length_rev; eauto.
                by rewrite Nat.sub_diag.
                rewrite elem_of_seq.
                lia.
      + iIntros "(%Hneq & _)"; congruence.
  Qed.
  
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

  Lemma interp_wl_length offset wl inst fr :
    interp_wl offset wl inst fr ->
    offset + length wl <= length (f_locs fr).
  Proof.
    unfold interp_wl.
    intros (vs & vs' & vs'' & -> & Hlen & Htyp).
    eapply Forall2_length in Htyp.
    rewrite !length_app.
    lia.
  Qed.

  Lemma wp_save_stack_w tys :
    forall s E Φ inst fe wl idxs wl' es fr vs,
      run_codegen (save_stack_w fe tys) wl = inr (idxs, wl', es) ->
      interp_wl (fe_wlocal_offset fe) wl' inst fr ->
      result_type_interp tys vs ->
      idxs = map W.Mk_localidx (seq (fe_wlocal_offset fe + length wl) (length tys)) ∧
      wl' = wl ++ tys /\
      ⊢ ↪[frame] fr -∗
        ↪[RUN] -∗
        Φ (immV []) -∗
        WP (W.v_to_e_list vs ++ to_e_list es) @ s; E
           {{ v, Φ v ∗ ↪[RUN] ∗
                 ∃ f, ↪[frame] f  ∗
                      ⌜∀ i, i ∉ idxs -> f_locs f !! localimm i = f_locs fr !! localimm i⌝ ∗
                      [∧ list] k ↦ i ∈ idxs, ⌜f_locs f !! localimm i = vs !! k⌝ }}.
  Proof.
    intros * Hcg.
    unfold save_stack_w in Hcg.
    (* apply wps/inversion principles *)
    inv_cg_bind Hcg res wl1 es1 es2 Hcg1 Hcg2.
    inv_cg_bind Hcg2 res2 wl2 es3 es4 Hcg2 Hcg3.
    inv_cg_ret Hcg3; subst.
    apply wp_wlallocs in Hcg1.
    destruct Hcg1 as (Hres1 & Hwl1 & Hes1); subst.
    unfold set_locals_w in Hcg2.
    simpl in Hcg2.
    rewrite -rev_reverse in Hcg2.
    rewrite imap_seq in Hcg2.
    unfold mapM_ in Hcg2.
    do 2 rewrite mapM_comp in Hcg2.
    rewrite map_comp in Hcg2.
    rewrite rev_reverse in Hcg2.
    rewrite map_rev in Hcg2.
    rewrite -map_fmap in Hcg2.
    rewrite map_comp in Hcg2.
    rewrite Combinators.compose_assoc in Hcg2.
    rewrite localimm_Mk_localidx in Hcg2.
    rewrite Combinators.compose_id_right in Hcg2.
    inv_cg_bind Hcg2 res3 wl3 es5 es6 Hcg2 Hcg3.
    inv_cg_ret Hcg3; subst.
    apply wp_mapM_emit in Hcg2.
    destruct Hcg2 as (Hres2 & Hwl2 & Hes3); subst res3 wl3 es5.
    repeat rewrite app_nil_r app_nil_l app_nil_r.
    rewrite imap_seq.
    intros.
    split; auto.
    split; auto.
    iIntros "Hfr Hrun HΦ".
    iApply (wp_wand with "[Hfr Hrun HΦ]").
    iApply (wp_save_stack_w_ind with "[$] [$] [HΦ]").
    - symmetry. eapply Forall2_length; eauto.
    - apply interp_wl_length in H.
      rewrite length_app in H.
      lia.
    - eauto.
    - iIntros (v) "((HΦ & Hrun) & %f & Hfr & Hpre & Hvs)".
      repeat rewrite big_andL_pure; eauto.
      iFrame.
      iDestruct "Hvs" as "%Hvs".
      iDestruct "Hpre" as "%Hpre".
      iSplit.
      + iPureIntro.
        intros i Hi.
        destruct i.
        setoid_rewrite elem_of_list_fmap_inj in Hi;
          [| intros x y Hinj; by injection Hinj].
        by apply Hpre in Hi.
      + rewrite big_andL_pure.
        iPureIntro.
        intros k x Hkx.
        rewrite list_lookup_fmap in Hkx.
        rewrite fmap_Some in Hkx.
        destruct Hkx as (n & Hkx & ->).
        eauto.
  Qed.
  
  Lemma wp_ignore {A} (c: codegen A) wl ret wl' es :
    run_codegen (ignore c) wl = inr (ret, wl', es) ->
    ret = tt /\
    exists ret',
      run_codegen c wl = inr (ret', wl', es).
  Proof.
    intros Hcg.
    inv_cg_bind Hcg res' wl'' es1 es2 Hcg1 Hcg2.
    inv_cg_ret Hcg2.
    rewrite app_nil_r.
    eauto.
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
  
  Lemma wp_restore_stack_w idxs vs wl wl' es E ret f Φ :
    length idxs = length vs ->
    run_codegen (restore_stack idxs) wl = inr (ret, wl', es) ->
    ret = tt /\
    wl' = wl /\
    ⊢ 
    ↪[frame] f -∗
    ↪[RUN] -∗
    Φ (immV vs) -∗
    (* this condition appears in the postcondition of the save_stack wp lemma. *)
    ([∧ list] k ↦ i ∈ idxs, ⌜f_locs f !! localimm i = vs !! k⌝) -∗
    WP to_e_list es @ NotStuck; E {{ v, Φ v ∗ ↪[RUN] ∗ ↪[frame] f }}.
  Proof.
    unfold restore_stack.
    intros Hlen Hcg.
    unfold get_locals_w in Hcg.
    apply wp_ignore in Hcg.
    destruct Hcg as [-> [ret' Hcg]].
    do 2 rewrite mapM_comp in Hcg.
    apply wp_mapM_emit in Hcg.
    destruct Hcg as (-> & -> & ->).
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
      eauto.
  Qed.

End CodeGen.
