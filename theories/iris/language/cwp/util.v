Require Import RichWasm.iris.language.iris_wp_def.
Require Import RichWasm.iris.language.cwp.base.

Set Bullet Behavior "Strict Subproofs".

Section util.

  Context `{!wasmG Σ}.

  (* TODO: Duplicated from compat_lemmas/shared.v. *)
  Lemma to_val_v_to_e vs :
    to_val (v_to_e_list vs) = Some (immV vs).
  Proof.
    induction vs => //=.
    unfold to_val.
    unfold RichWasm.iris.language.iris.iris.to_val.
    rewrite (separate1 (AI_basic _)).
    rewrite map_app.
    rewrite -cat_app.
    rewrite merge_app.
    unfold to_val, RichWasm.iris.language.iris.iris.to_val in IHvs.
    destruct (merge_values_list _) eqn:Hvs => //.
    inversion IHvs; subst v.
    simpl. done.
  Qed.

  (* TODO: Duplicated from compat_lemmas/shared.v. *)
  Lemma push_const_lh_depth {i : nat} (lh : valid_holed i) w :
    lh_depth (lh_of_vh lh) = lh_depth (lh_of_vh (vh_push_const lh w)).
  Proof.
    induction lh;simpl;auto.
  Qed.

  (* TODO: Duplicated from compat_lemmas/shared.v. *)
  Lemma get_base_l_push_const {i : nat} (lh : valid_holed i) w :
    get_base_l (vh_push_const lh w) = (w ++ get_base_l lh) ∨
      get_base_l (vh_push_const lh w) = get_base_l lh.
  Proof.
    induction lh.
    { left. auto. }
    { simpl. by right. }
  Qed.

  (* TODO: Duplicated from compat_lemmas/shared.v. *)
  Lemma simple_get_base_l_push_const (lh : simple_valid_holed) w :
    simple_get_base_l (sh_push_const lh w) = (w ++ simple_get_base_l lh) ∨
    simple_get_base_l (sh_push_const lh w) = simple_get_base_l lh.
  Proof.
    induction lh.
    { left. auto. }
    { simpl. by right. }
  Qed.

  (* TODO: Duplicated from compat_lemmas/shared.v. *)
  Lemma to_e_list_app es1 es2 :
    to_e_list (es1 ++ es2) = to_e_list es1 ++ to_e_list es2.
  Proof.
    by rewrite to_e_list_cat cat_app.
  Qed.

  (* TODO: Duplicated from wp_codegen.v. *)
  Lemma map_comp {A B C} (f: A -> B) (g: B -> C) xs :
    map g (map f xs) = map (g ∘ f) xs.
  Proof.
    by apply map_map.
  Qed.

  (* TODO: Duplicated from compat_lemmas/shared.v. *)
  Lemma get_base_l_append {i : nat} (lh : valid_holed i) e :
    get_base_l (vh_append lh e) = get_base_l lh.
  Proof.
    induction lh;simpl;auto.
  Qed.

  (* TODO: Duplicated from compat_lemmas/shared.v. *)
  Lemma append_lh_depth {i : nat} (lh : valid_holed i) e :
    lh_depth (lh_of_vh lh) = lh_depth (lh_of_vh (vh_append lh e)).
  Proof.
    induction lh; simpl; auto.
  Qed.

  Lemma simple_get_base_l_append s es :
    simple_get_base_l (sh_append s (to_e_list es)) = simple_get_base_l s.
  Proof.
    induction s; first done.
    cbn. by rewrite <- IHs.
  Qed.

  Fixpoint set_base_l {i : nat} (vs : list value) (vh : valid_holed i) : valid_holed i :=
    match vh with
    | VH_base n _ es => VH_base n vs es
    | VH_rec _ vs0 n es1 lh' es2 => VH_rec vs0 n es1 (set_base_l vs lh') es2
    end.

  Fixpoint simple_set_base_l (vs : list value) (sh : simple_valid_holed) : simple_valid_holed :=
    match sh with
    | SH_base _ es => SH_base vs es
    | SH_rec vs0 n es1 sh' es2 => SH_rec vs0 n es1 (simple_set_base_l vs sh') es2
    end.

  Lemma set_base_l_depth {i : nat} vs (vh : valid_holed i) :
    lh_depth (lh_of_vh vh) = lh_depth (lh_of_vh (set_base_l vs vh)).
  Proof.
    induction vh.
    - done.
    - cbn. by rewrite IHvh.
  Qed.

  Lemma vfill_take_base {i : nat} (vh : valid_holed i) vs0 vs es :
    get_base_l vh = vs0 ++ vs ->
    vfill vh es = vfill (set_base_l vs0 vh) (seq.cat (v_to_e_list vs) es).
  Proof.
    intros Hbase.
    induction vh.
    - cbn. cbn in Hbase. rewrite Hbase.
      unfold v_to_e_list.
      change seq.map with (@map value administrative_instruction).
      rewrite map_app.
      change seq.cat with (@app administrative_instruction).
      rewrite <- app_assoc.
      by rewrite <- app_assoc.
    - cbn.
      do 3 f_equal.
      apply IHvh.
      by cbn in Hbase.
  Qed.

  Lemma sfill_take_base sh vs0 vs es :
    simple_get_base_l sh = vs0 ++ vs ->
    sfill sh es = sfill (simple_set_base_l vs0 sh) (seq.cat (v_to_e_list vs) es).
  Proof.
    intros Hbase.
    induction sh.
    - cbn. cbn in Hbase. rewrite Hbase.
      unfold v_to_e_list.
      change seq.map with (@map value administrative_instruction).
      rewrite map_app.
      change seq.cat with (@app administrative_instruction).
      rewrite <- app_assoc.
      by rewrite <- app_assoc.
    - cbn.
      do 3 f_equal.
      apply IHsh.
      by cbn in Hbase.
  Qed.

  (* TODO: Duplicated from get_base_vh_decrease. *)
  Lemma lh_depth_vh_decrease {m : nat} (vh : valid_holed (S m)) vh' :
    vh_decrease vh = Some vh' ->
    lh_depth (lh_of_vh vh') = lh_depth (lh_of_vh vh).
  Proof.
    set (n := S m) in vh.
    pose (Logic.eq_refl : n = S m) as Hn.
    change vh with (match Hn in _ = w return valid_holed w with
                    | Logic.eq_refl => vh end).
    clearbody n Hn.
    generalize dependent m.
    induction vh; intros m vh' Hn.
    - destruct n => //=.
      pose proof (eq_add_S _ _ Hn) as Hm.
      assert (Hn = f_equal S Hm) as Hproof.
      apply Eqdep.EqdepTheory.UIP.
      replace (vh_decrease (match Hn in _ = w return (valid_holed w) with
                            | Logic.eq_refl => VH_base (S n) l l0 end)) with
        (match Hm in _ = w return (option (valid_holed w)) with
         | Logic.eq_refl => vh_decrease (VH_base (S n) l l0) end);
        last by rewrite Hproof; destruct Hm.
      destruct Hm; simpl. intros H; inversion H; subst vh'.
      clear. destruct Hn. done.
    - pose proof (eq_add_S _ _ Hn) as Hm.
      assert (Hn = f_equal S Hm) as Hproof.
      apply Eqdep.EqdepTheory.UIP.
      replace (vh_decrease (match Hn in _ = w return (valid_holed w) with
                            | Logic.eq_refl => VH_rec l n0 l0 vh l1 end)) with
        (match Hm in _ = w return (option (valid_holed w)) with
         | Logic.eq_refl => vh_decrease (VH_rec l n0 l0 vh l1) end);
        last by rewrite Hproof ; destruct Hm.
      replace (get_base_l match Hn in (_ = w) return (valid_holed w) with
                 | Logic.eq_refl => VH_rec l n0 l0 vh l1
                 end) with
        (match Hm in _ = w return (list value) with
         | Logic.eq_refl => get_base_l (VH_rec l n0 l0 vh l1) end);
        last by rewrite Hproof; destruct Hm.
      destruct Hm => //=.
      destruct n => //=.
      destruct (vh_decrease vh) eqn:Hvh => //.
      intros H; inversion H; subst vh'.
      simpl.
      pose proof (eq_add_S _ _ Hn) as Hm.
      pose proof (eq_add_S _ _ Hm) as Hp.
      assert (Hm = f_equal S Hp) as Hproof'.
      apply Eqdep.EqdepTheory.UIP.
      specialize (IHvh n v Hm).
      rewrite IHvh.
      (* This is the only line that's different... *)
      { clear. destruct Hm. by destruct Hn. }
      replace (vh_decrease match Hm in (_ = w) return (valid_holed w) with
                 | Logic.eq_refl => vh
                 end) with
        (match Hp in (_ = w) return (option (valid_holed w)) with
         | Logic.eq_refl => vh_decrease vh end); last by rewrite Hproof'; clear; destruct Hp.
      rewrite Hvh. clear.
      assert (Hp = Logic.eq_refl).
      apply Eqdep.EqdepTheory.UIP.
      rewrite H. done.
  Qed.

  Lemma cons_lookup_sub_lt {A} i j x (xs : list A) :
    j < i ->
    (x :: xs) !! (i - j) = xs !! (i - S j).
  Proof.
    intros H.
    apply Nat.sub_gt in H.
    destruct (i - j) eqn:Hsub; first done.
    clear H.
    rewrite Nat.sub_succ_r.
    by rewrite Hsub.
  Qed.

  Definition is_basic_const (e : basic_instruction) : bool :=
    match e with
    | BI_const _ => true
    | _ => false
    end.

  Definition basic_const_list (es : list basic_instruction) : bool :=
    forallb is_basic_const es.

  Lemma const_list_map_basic vs :
    is_true (basic_const_list vs) ->
    is_true (const_list (map AI_basic vs)).
  Proof.
    intros Hvs.
    apply forallb_forall.
    intros e He.
    unfold is_true, basic_const_list in Hvs.
    rewrite forallb_forall in Hvs.
    apply in_map_iff in He.
    destruct He as (e' & <- & He').
    specialize Hvs with e'.
    by apply Hvs in He'.
  Qed.

End util.
