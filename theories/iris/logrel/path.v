From RichWasm Require Import
  syntax
  typing
  logrel.
From RichWasm.compiler Require Import
  memory.
From RichWasm.iris.logrel Require Import
  instr.kinding
  instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
(*Stuff to look at

typing

  resolves_path τ
  resolves_path τ π None pr ->
  pr.(pr_target) = SerT κser τval ->
  Forall (has_mono_size F) pr.(pr_prefix) ->
  has_ref_flag F τval GCRefs ->
  has_size F pr.(pr_target) σ ->

compiler

  off ← try_option EFail (path_offset fe τ π);
  ρ ← try_option EFail (type_rep fe.(fe_type_vars) τval);
  set_pointer_flags mr a off (repeat FlagInt (areps_size ιs))
  load mr fe μ con a off ιs
  store mr μ a off vs ιs
  set_pointer_flags mr a off (flat_map arep_flags ιs).
*)

Section PathFacts.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.
  Variable se : semantic_env (Σ:=Σ).

  Notation 𝕍 := (value_interp rti sr se).

  Lemma eval_rep_empty_ok_Some ρ :
    rep_ok kc_empty ρ ->
    is_Some (eval_rep EmptyEnv ρ).
  Proof.
    intros Hok.
    induction ρ using rep_ind.
    - inversion Hok as [K n Hidx HK Hn| | |].
      cbn in *; lia.
    - inversion Hok as [|K ρs' Hρs HK Hρs'| |].
      subst K ρs'.
      pose proof (List.Forall_and H Hρs) as H'.
      clear H Hρs.
      apply Forall_impl with (Q := is_Some ∘ eval_rep EmptyEnv) in H'.
      + rewrite <- mapM_is_Some in H'. by apply fmap_is_Some.
      + intros ρ [Hsome ?]. by apply Hsome.
    - inversion Hok as [| |K ρs' Hρs HK Hρs'|].
      subst K ρs'.
      pose proof (List.Forall_and H Hρs) as H'.
      clear H Hρs.
      apply Forall_impl with (Q := is_Some ∘ eval_rep EmptyEnv) in H'.
      + rewrite <- mapM_is_Some in H'. by apply fmap_is_Some.
      + intros ρ [Hsome ?]. by apply Hsome.
    - done.
  Qed.

  Lemma eval_size_empty_ok_Some σ :
    size_ok kc_empty σ ->
    is_Some (eval_size EmptyEnv σ).
  Proof.
    induction σ using size_ind; intros Hok.
    - inversion Hok. cbn in *; lia.
    - inversion Hok as [|K σs' Hσs HK Hσs'| | |].
      subst K σs'.
      pose proof (List.Forall_and H Hσs) as H'.
      clear H Hσs.
      apply Forall_impl with (Q := is_Some ∘ eval_size EmptyEnv) in H'.
      + rewrite <- mapM_is_Some in H'. by apply fmap_is_Some.
      + intros σ [Hsome ?]. by apply Hsome.
    - inversion Hok as [| |K σs' Hσs HK Hσs'| |].
      subst K σs'.
      pose proof (List.Forall_and H Hσs) as H'.
      clear H Hσs.
      apply Forall_impl with (Q := is_Some ∘ eval_size EmptyEnv) in H'.
      + rewrite <- mapM_is_Some in H'. by apply fmap_is_Some.
      + intros σ [Hsome ?]. by apply Hsome.
    - inversion Hok as [| | |K ρ' Hok_ρ HK Hρ'|].
      subst K ρ'.
      apply fmap_is_Some.
      by eapply eval_rep_empty_ok_Some.
    - done.
  Qed.

  Lemma has_mono_size_inv F τ :
    has_mono_size F τ ->
    ∃ σ ξ k,
      is_mono_size σ /\
      has_kind F τ (MEMTYPE σ ξ) /\
      eval_size EmptyEnv σ = Some k.
  Proof.
    intros Hmono.
    inversion Hmono as [F' τ' σ ξ Hkind Hsz HF' Hτ'].
    subst F' τ'.
    pose proof Hsz as Hev.
    unfold is_mono_size in Hev.
    eapply eval_size_empty_ok_Some in Hev.
    destruct Hev as [k Hev].
    repeat eexists; eauto.
  Qed.

  Definition get_path_words (off sz : nat) (ws : list word) : list word :=
    firstn sz (skipn off ws).

  Lemma get_path_words_all ws :
    get_path_words 0 (length ws) ws = ws.
  Proof.
    unfold get_path_words.
    by rewrite skipn_0 firstn_all.
  Qed.

  Definition update_path_words (off : nat) (ws ws' : list word) : list word :=
    (firstn off ws) ++ ws' ++ (skipn (length ws') (skipn off ws)).

  Lemma update_path_words_size off ws ws' :
    off + length ws' <= length ws ->
    length (update_path_words off ws ws') = length ws.
  Proof.
    intros H.
    unfold update_path_words.
    rewrite !length_app.
    rewrite length_take_le; last lia.
    rewrite drop_drop.
    rewrite length_drop.
    lia.
  Qed.

  Lemma update_path_words_all ws ws' :
    length ws' = length ws ->
    update_path_words 0 ws ws' = ws'.
  Proof.
    intros Hlens.
    unfold update_path_words.
    rewrite Hlens.
    rewrite take_0 app_nil_l.
    by rewrite drop_0 drop_all app_nil_r.
  Qed.

  Definition pr_expected (pr : path_result) (τ__π: option type) :=
    match τ__π with
    | Some τ__π' => τ__π'
    | None => pr.(pr_target)
    end.

  Definition type_sz (fe : function_env) (τ : type) : option nat :=
    σ ← type_size fe.(fe_type_vars) τ;
    eval_size se σ.

  Lemma mono_rep_eval_rep ρ :
    is_mono_rep ρ ->
    eval_rep se ρ = eval_rep EmptyEnv ρ.
  Proof.
    intros Hmono.
    induction ρ using rep_ind; inversion Hmono; subst; cbn in *.
    - lia.
    - f_equal.
      assert (Forall2 (λ x y, eval_rep se x = eval_rep EmptyEnv y) ρs ρs).
      {
        apply Forall_Forall2_diag.
        eapply Forall_impl.
        eapply Forall_and; split; [apply H | apply H2].
        intros ρ [Hevs Hsz]; cbn; eauto.
      }
      erewrite Forall2_mapM_ext; eauto.
    - f_equal.
      assert (Forall2 (λ x y, eval_rep se x = eval_rep EmptyEnv y) ρs ρs).
      {
        apply Forall_Forall2_diag.
        eapply Forall_impl.
        eapply Forall_and; split; [apply H | apply H2].
        intros ρ [Hevs Hsz]; cbn; eauto.
      }
      erewrite Forall2_mapM_ext; eauto.
    - done.
  Qed.

  Lemma mono_size_eval_emp σ :
    is_mono_size σ ->
    eval_size se σ = eval_size EmptyEnv σ.
  Proof.
    intros Hmono.
    induction σ using size_ind; inversion Hmono; subst; cbn in *.
    - lia.
    - assert (Forall2 (λ σ σ': Core.size, eval_size se σ = eval_size EmptyEnv σ') σs σs).
      {
        apply Forall_Forall2_diag.
        eapply Forall_impl.
        eapply Forall_and; split; [apply H | apply H2].
        intros σ [Hevs Hsz]; cbn; eauto.
      }
      erewrite Forall2_mapM_ext; eauto.
    - assert (Forall2 (λ σ σ': Core.size, eval_size se σ = eval_size EmptyEnv σ') σs σs).
      {
        apply Forall_Forall2_diag.
        eapply Forall_impl.
        eapply Forall_and; split; [apply H | apply H2].
        intros σ [Hevs Hsz]; cbn; eauto.
      }
      erewrite Forall2_mapM_ext; eauto.
    - by rewrite mono_rep_eval_rep.
    - done.
  Qed.

  Lemma has_kind_type_sz F τ σ ξ k :
    has_kind F τ (MEMTYPE σ ξ) ->
    is_mono_size σ ->
    sem_env_interp F se ->
    eval_size se σ = Some k ->
    type_sz (fe_of_context F) τ = Some k.
  Proof.
    intros Hk Hse Hev.
    unfold type_sz, type_size.
    pose proof (type_kind_has_kind_is_Some _ _ _ Hk) as (tk & Htk).
    rewrite Htk; cbn.
    eapply type_kind_has_kind_agree in Htk; eauto.
    by rewrite <- Htk.
  Qed.

  Lemma drop_list_sum_cat A (wss : list (list A)) ks :
    map length wss = ks ->
    drop (list_sum ks) (concat wss) = concat (drop (length ks) wss).
  Proof.
    revert wss.
    induction ks as [| k ks]; intros wss Hlen.
    - destruct wss; cbn in Hlen; done.
    - change (list_sum (k :: ks)) with (list_sum ([k] ++ ks)).
      rewrite list_sum_app; cbn [list_sum foldr].
      rewrite Nat.add_0_r -drop_drop.
      destruct wss as [|ws wss]; cbn in Hlen; inversion Hlen.
      subst k ks.
      cbn.
      rewrite drop_app_length.
      by rewrite IHks.
  Qed.

  Lemma drop_list_sum_cat' A (wss : list (list A)) ks :
    map length wss = ks ->
    drop (list_sum ks) (concat wss) = [].
  Proof.
    revert wss.
    induction ks as [| k ks]; intros wss Hlen.
    - destruct wss; cbn in Hlen; done.
    - change (list_sum (k :: ks)) with (list_sum ([k] ++ ks)).
      rewrite list_sum_app; cbn [list_sum foldr].
      rewrite Nat.add_0_r -drop_drop.
      destruct wss as [|ws wss]; cbn in Hlen; inversion Hlen.
      subst k ks.
      cbn.
      rewrite drop_app_length.
      by rewrite IHks.
  Qed.

  Lemma get_path_words_field F τs τ τs' σs ks off wss1 wss2 ws sz :
    mapM (type_size (fc_type_vars F)) (take (length τs) (τs ++ τ :: τs')) = Some σs ->
    length wss1 = length τs ->
    length wss2 = length τs' ->
    off + sz <= length ws ->
    mapM (eval_size EmptyEnv) σs = Some ks ->
    map length wss1 = ks ->
    length τs = length ks ->
    get_path_words (list_sum ks + off) sz (concat wss1 ++ ws ++ concat wss2) = get_path_words off sz ws.
  Proof.
    unfold get_path_words; intros Hσs Hws Hsz Hks Hwss Hτs.
    rewrite -drop_drop.
    intros Hts.
    rewrite -Hτs.
    rewrite drop_app drop_list_sum_cat'; last done.
    rewrite -length_concat Nat.sub_diag drop_0 app_nil_l.
    rewrite drop_app_le; last lia.
    rewrite take_app length_drop.
    replace (sz - (length ws - off)) with 0 by lia.
    by rewrite take_0 app_nil_r.
  Qed.

  Lemma take_list_sum_cat A (wss : list (list A)) j xs ks :
    map length wss = ks ->
    take (list_sum ks + j) (concat wss ++ xs) = concat wss ++ take j xs.
  Proof.
    revert wss.
    induction ks as [| k ks]; intros wss Hlen.
    - destruct wss; cbn in Hlen; done.
    - destruct wss as [|ws wss]; cbn in Hlen; inversion Hlen.
      change (list_sum (k :: ks)) with (list_sum ([k] ++ ks)).
      subst.
      simpl.
      rewrite -app_assoc.
      rewrite -Nat.add_assoc.
      rewrite take_app_add.
      rewrite -app_assoc.
      f_equal.
      by eapply IHks.
  Qed.

  Lemma update_path_words_field F ks wss1 ws' wss2 ws off τs τ τs' σs :
    mapM (type_size (fc_type_vars F)) (take (length τs) (τs ++ τ :: τs')) = Some σs ->
    length wss1 = length τs ->
    map length wss1 = ks ->
    length τs = length ks ->
    mapM (eval_size EmptyEnv) σs = Some ks ->
    off + length ws' <= length ws ->
    update_path_words (list_sum ks + off) (concat wss1 ++ ws ++ concat wss2) ws' =
      concat wss1 ++ update_path_words off ws ws' ++ concat wss2.
  Proof.
    unfold update_path_words; intros Hσs Hwss1 Hlens Hks Hszs Hoff.
    rewrite take_list_sum_cat; last done.
    rewrite -app_assoc; f_equal.
    rewrite take_app.
    rewrite -!app_assoc.
    f_equal.
    assert (Hoffws: off - length ws = 0) by lia.
    rewrite Hoffws take_0; cbn.
    f_equal.
    rewrite -Hlens -length_concat.
    rewrite drop_app_add.
    rewrite drop_app_le; last lia.
    rewrite drop_app_le; auto.
    rewrite length_drop.
    lia.
  Qed.

  Lemma val_interp_type_sz F τ ws :
    sem_env_interp F se ->
    has_mono_size F τ ->
    ⊢ 𝕍 τ (SWords ws) -∗
      ∃ sz, ⌜type_sz (fe_of_context F) τ = Some sz⌝ ∗
            ⌜length ws = sz⌝.
  Proof.
    iIntros (HF Hmono) "Hws".
    inversion Hmono as [F' τ' σ ξ Hκ Hsz]; subst.
    pose proof (has_kind_inv _ _ _ Hκ) as Hok.
    inversion Hok as [F' τ' κ' Ht Hk]; subst F' τ' κ'.
    eapply eval_kind_ok_Some in Hk; eauto.
    destruct Hk as [sκ Hev].
    pose proof (kinding_sound rti sr mr _ _ _ _ _ Hκ HF Hev) as [_ Hsv].
    iDestruct (Hsv with "Hws") as "%Hkind".
    destruct sκ; cbn in Hkind.
    - destruct Hkind as [[vs [Hcontra _]] _]; congruence.
    - cbn in Hev.
      eapply bind_Some in Hev; destruct Hev as (n' & Hevn & Hev).
      inversion Hev; subst n' r.
      destruct Hkind as [Hlen Href].
      iExists n.
      iPureIntro.
      split; last done.
      eapply has_kind_type_sz; eauto.
  Qed.

  Lemma has_kind_mem_size_agree_ind F τ κ :
    has_kind F τ κ ->
    ∀ σ σ' ξ,
      κ = MEMTYPE σ ξ ->
      type_size (fc_type_vars F) τ = Some σ' ->
      σ = σ'.
  Proof.
    intros Hkind.
    induction Hkind; intros * Hκ; (try by inversion Hκ); intros Hev; subst;
      try solve [
          try inversion Hκ; subst;
          cbn in Hev; congruence
        ].
    cbn in Hev.
    rewrite H in Hev.
    by inversion Hev.
  Qed.

  Lemma has_kind_mem_size_agree F τ ξ σ σ' :
    has_kind F τ (MEMTYPE σ ξ) ->
    type_size (fc_type_vars F) τ = Some σ' ->
    σ = σ'.
  Proof.
    intros.
    eapply has_kind_mem_size_agree_ind; eauto.
  Qed.

  Lemma has_kinds_mem_size_agree {F τs σs σs' ξs} :
    Forall3 (λ τ σ ξ, has_kind F τ (MEMTYPE σ ξ)) τs σs ξs ->
    mapM (type_size (fc_type_vars F)) τs = Some σs' ->
    σs = σs'.
  Proof.
    rewrite mapM_Some.
    intros Hkind.
    revert σs'.
    induction Hkind; intros * Hev.
    - inversion Hev; subst.
      done.
    - apply Forall2_cons_inv_l in Hev.
      destruct Hev as (σ' & σs'' & Htz & Hall & ->).
      f_equal; eauto using has_kind_mem_size_agree.
  Qed.

  Lemma eval_size_prod_inv σs n :
    eval_size se (ProdS σs) = Some n ->
    exists ns,
      mapM (eval_size se) σs = Some ns /\
      n = list_sum ns.
  Proof.
    apply fmap_Some.
  Qed.

  Lemma skind_mem_words_len n r ws :
    skind_has_svalue (SMEMTYPE n r) (SWords ws) ->
    n = length ws.
  Proof.
    cbn.
    tauto.
  Qed.

  Lemma inv_Forall2_elt_l {A B} {P : A -> B -> Prop} {xs1 x xs2 ys} :
    Forall2 P (xs1 ++ x :: xs2) ys ->
    ∃ ys1 y ys2,
      length ys1 = length xs1 /\
      length ys2 = length xs2 /\
      ys = ys1 ++ y :: ys2 /\
      Forall2 P xs1 ys1 /\
      P x y /\
      Forall2 P xs2 ys2.
  Proof.
    intros Hall.
    apply Forall2_app_inv_l in Hall.
    destruct Hall as (ys1 & ys' & Hxs1 & Hys' & ->).
    apply Forall2_cons_inv_l in Hys'.
    destruct Hys' as (y & ys2 & Hy & Hys2 & ->).
    repeat eexists; eauto using eq_sym, Forall2_length.
  Qed.

  Lemma inv_Forall2_elt_r {A B} {P : A -> B -> Prop} {xs1 x xs2 ys} :
    Forall2 P ys (xs1 ++ x :: xs2) ->
    ∃ ys1 y ys2,
      length ys1 = length xs1 /\
      length ys2 = length xs2 /\
      ys = ys1 ++ y :: ys2 /\
      Forall2 P ys1 xs1 /\
      P y x /\
      Forall2 P ys2 xs2.
  Proof.
    intros Hall.
    apply Forall2_app_inv_r in Hall.
    destruct Hall as (ys1 & ys' & Hxs1 & Hys' & ->).
    apply Forall2_cons_inv_r in Hys'.
    destruct Hys' as (y & ys2 & Hy & Hys2 & ->).
    repeat eexists; eauto using eq_sym, Forall2_length.
  Qed.

  Lemma inv_Forall2_elt {A B} {P : A -> B -> Prop} {xs1 x xs2 ys1 y ys2} :
    Forall2 P (xs1 ++ x :: xs2) (ys1 ++ y :: ys2) ->
    length xs1 = length ys1 ->
    length xs2 = length ys2 ->
    Forall2 P xs1 ys1 /\
    P x y /\
    Forall2 P xs2 ys2.
  Proof.
    intros Hall Hlen1 Hlen2.
    eapply Forall2_app_inv in Hall; eauto.
    rewrite Forall2_cons in Hall.
    tauto.
  Qed.

  Lemma inv_Forall3_elt_l {A B C} {P : A -> B -> C -> Prop} {xs1 x xs2 ys zs} :
    Forall3 P (xs1 ++ x :: xs2) ys zs ->
    ∃ ys1 y ys2 zs1 z zs2,
      length ys1 = length xs1 /\
      length ys2 = length xs2 /\
      length zs1 = length xs1 /\
      length zs2 = length xs2 /\
      ys = ys1 ++ y :: ys2 /\
      zs = zs1 ++ z :: zs2 /\
      Forall3 P xs1 ys1 zs1 /\
      P x y z /\
      Forall3 P xs2 ys2 zs2.
  Proof.
    intros Hall.
    apply Forall3_app_inv_l in Hall.
    destruct Hall as (ys1 & ys' & zs1 & zs' & -> & -> & Hxs1 & Hys').
    apply Forall3_cons_inv_l in Hys'.
    destruct Hys' as (y & ys2 & z & zs2 & -> & -> & HP & Hxs2).
    repeat eexists; eauto using eq_sym, Forall3_length_lr, Forall3_length_lm.
  Qed.

  Lemma inv_Forall3_elt_lm {A B C} {P : A -> B -> C -> Prop} {xs1 x xs2 ys1 y ys2 zs} :
    Forall3 P (xs1 ++ x :: xs2) (ys1 ++ y :: ys2) zs ->
    length xs1 = length ys1 ->
    length xs2 = length ys2 ->
    ∃ zs1 z zs2,
      length zs1 = length xs1 /\
      length zs2 = length xs2 /\
      zs = zs1 ++ z :: zs2 /\
      Forall3 P xs1 ys1 zs1 /\
      P x y z /\
      Forall3 P xs2 ys2 zs2.
  Proof.
    intros Hall Hlen_ys1 Hlen_ys2.
    apply Forall3_app_inv_l in Hall.
    destruct Hall as (ys1' & ys' & zs1 & zs' & Heq_ys & -> & Hxs1 & Hys').
    apply Forall3_cons_inv_l in Hys'.
    destruct Hys' as (y' & ys2' & z & zs2 & -> & -> & HP & Hxs2).
    apply Forall3_length_lm in Hxs1 as Hlen_ys1'.
    apply app_inj_1 in Heq_ys as [<- Heq_ys2]; last by rewrite <- Hlen_ys1'.
    inversion Heq_ys2.
    subst y' ys2'.
    clear Heq_ys2.
    repeat eexists; eauto using eq_sym, Forall3_length_lr, Forall3_length_lm.
  Qed.

  Lemma inv_Forall3_elt {A B C} {P : A -> B -> C -> Prop} {xs1 x xs2 ys1 y ys2 zs1 z zs2} :
    Forall3 P (xs1 ++ x :: xs2) (ys1 ++ y :: ys2) (zs1 ++ z :: zs2) ->
    length xs1 = length ys1 ->
    length xs2 = length ys2 ->
    length xs1 = length zs1 ->
    Forall3 P xs1 ys1 zs1 /\
    P x y z /\
    Forall3 P xs2 ys2 zs2.
  Proof.
    intros HP Hlen_ys1 Hlen_ys2 Hlen_zs1.
    apply Forall3_app_inv_l in HP as (ys1' & ys2' & zs1' & zs2' & Heq_ys & Heq_zs & HP1 & HP2).
    apply Forall3_length_lm in HP1 as Hlen_ys1'.
    apply Forall3_length_lr in HP1 as Hlen_zs1'.
    apply app_inj_1 in Heq_ys as [<- <-]; last by rewrite <- Hlen_ys1'.
    apply app_inj_1 in Heq_zs as [<- <-]; last by rewrite <- Hlen_zs1'.
    apply Forall3_cons_inv_l in HP2 as (y' & ys2' & z' & zs2' & Heq_y & Heq_z & HP & HP2).
    inversion Heq_y.
    by inversion Heq_z.
  Qed.

  Lemma option_mapM_cons {A B} (f : A -> option B) a l :
    mapM f (a :: l) = r ← f a; rs ← mapM f l; mret (r :: rs).
  Proof.
    reflexivity.
  Qed.

  Lemma option_mapM_app {A B} (f : A -> option B) (l1 l2 : list A) :
    mapM f (l1 ++ l2) = r1 ← mapM f l1; r2 ← mapM f l2; mret (r1 ++ r2).
  Proof.
    induction l1.
    - rewrite app_nil_l.
      cbn [mapM].
      unfold mret, mbind, MBind_Monad, MRet_Monad, flip.
      cbn.
      unfold option_ret.
      by setoid_rewrite bind_with_Some.
    - rewrite <- app_comm_cons.
      rewrite !option_mapM_cons.
      rewrite !option_bind_assoc.
      eapply option_bind_ext; last done.
      intros r.
      rewrite IHl1; cbn.
      rewrite !option_bind_assoc.
      eapply option_bind_ext; last done.
      intros rs1.
      cbn.
      rewrite !option_bind_assoc.
      unfold mret, option_ret.
      eapply option_bind_ext; last done.
      done.
  Qed.

  Lemma mapM_elt_Some {X Y} {f : X -> option Y} {xs1 x xs2 ys} :
    mapM f (xs1 ++ x :: xs2) = Some ys ->
    ∃ ys1 y ys2,
      mapM f xs1 = Some ys1 /\
      f x = Some y /\
      mapM f xs2 = Some ys2 /\
      ys = ys1 ++ y :: ys2.
  Proof.
    intros Hmap.
    rewrite option_mapM_app in Hmap.
    apply bind_Some in Hmap.
    destruct Hmap as (ys1 & Hys1 & Hmap).
    apply bind_Some in Hmap.
    destruct Hmap as (ys' & Hys' & Hyseq).
    unfold mret in Hyseq; inversion Hyseq.
    subst ys; clear Hyseq.
    cbn in Hys'.
    apply bind_Some in Hys'.
    destruct Hys' as (y & Hy & Hys').
    apply bind_Some in Hys'.
    destruct Hys' as (ys2 & Hys2 & Hys').
    inversion Hys'; subst.
    repeat eexists; eauto.
  Qed.

  Lemma list_sum_len_inv A ns :
    ∀ xs : list A,
    list_sum ns = length xs ->
    ∃ xss,
      Forall2 (λ xs n, length xs = n) xss ns /\
      xs = concat xss.
  Proof.
    induction ns; cbn; intros xs Hlen.
    - exists [].
      destruct xs; try inversion Hlen.
      done.
    - fold (list_sum ns) in Hlen.
      assert (Htake: length (take a xs) = a).
      {
        rewrite length_take.
        rewrite min_l; [exact eq_refl | lia].
      }
      rewrite -(take_drop a xs) length_app Htake in Hlen.
      rewrite Nat.add_cancel_l in Hlen.
      specialize (IHns _ Hlen).
      destruct IHns as (xss' & Hxss & Hcat).
      exists (take a xs :: xss').
      split; cbn.
      + constructor; eauto.
      + by rewrite -Hcat take_drop.
  Qed.

  Lemma skind_has_svalue_partition ns r ws:
    skind_has_svalue (SMEMTYPE (list_sum ns) r) (SWords ws) ->
    ∃ wss,
      Forall2 (λ ws n, skind_has_svalue (SMEMTYPE n r) (SWords ws)) wss ns /\
      ws = concat wss.
  Proof.
    unfold skind_has_svalue; cbn.
    intros [Hlen Hrep].
    eapply list_sum_len_inv in Hlen.
    destruct Hlen as (wss & Hlens & ->).
    rewrite Forall_concat in Hrep.
    exists wss.
    split; last done.
    assert (length wss = length ns) by eauto using Forall2_length.
    assert (Hptr2 : Forall2 (λ ws n, Forall (forall_ptr_word (ref_flag_ptr_interp r)) ws) wss ns).
    {
      eapply Forall2_impl.
      - eapply Forall_Forall2_l; eauto using Forall2_length.
        eapply Forall_impl; eauto.
        intros ws Hptrs ?.
        apply Hptrs.
      - done.
    }
    eapply util.Forall2_Forall in Hlens, Hptr2.
    pose proof (conj Hlens Hptr2) as Hconj.
    eapply Forall_and in Hconj.
    eapply Forall_Forall2; eauto using Forall2_length.
    eapply Forall_impl; first eapply Hconj.
    intros [ws n]; cbn; intros [Hlen Hflag].
    done.
  Qed.

  Lemma type_skinds_has_kinds_Some F τs κs :
    Forall2 (has_kind F) τs κs ->
    sem_env_interp F se ->
    ∀ sks,
      mapM (eval_kind se) κs = Some sks →
      mapM (type_skind se) τs = Some sks.
  Proof.
    intros Hkind. induction Hkind; intros Hse sks Hevs; first done.
    cbn in Hevs.
    apply bind_Some in Hevs.
    destruct Hevs as (sk & Hev & Hevs).
    apply bind_Some in Hevs.
    destruct Hevs as (sks' & Hevs & Heq).
    inversion Heq; subst sks; clear Heq; rename sks' into sks.
    eapply type_skind_has_kind_Some in Hev; eauto.
    apply bind_Some.
    exists sk.
    split; first done.
    apply bind_Some.
    exists sks.
    split; last done.
    by apply IHHkind.
  Qed.

  Lemma type_skinds_has_kinds_Some_mem F τs σs ξs ns :
    Forall3 (λ τ σ ξ, has_kind F τ (MEMTYPE σ ξ)) τs σs ξs ->
    sem_env_interp F se ->
    mapM (eval_size se) σs = Some ns →
    ∃ sks,
      mapM (type_skind se) τs = Some sks ∧
      Forall3 (λ sk n ξ, sk = SMEMTYPE n ξ) sks ns ξs.
  Proof.
    intros Hall.
    revert ns.
    induction Hall; intros ns Hse Hevs.
    - exists [].
      inversion Hevs; subst.
      cbn; split; eauto.
      constructor.
    - cbn in Hevs.
      apply bind_Some in Hevs.
      destruct Hevs as (n & Hsz & Hcont).
      apply bind_Some in Hcont.
      destruct Hcont as (ns' & Hszs & Hret).
      inversion Hret; subst ns; rename ns' into ns.
      assert (eval_kind se (MEMTYPE y z) = Some (SMEMTYPE n z)).
      {
        cbn.
        rewrite Hsz.
        done.
      }
      eapply IHHall in Hszs; eauto.
      destruct Hszs as (sks & Hmap & Hsks).
      exists (SMEMTYPE n z :: sks).
      split; eauto.
      + cbn [mapM].
        erewrite type_skind_has_kind_Some; eauto.
        rewrite Hmap.
        done.
      + by constructor.
  Qed.

  Lemma subskind_mem_inv_l sk n ξ :
    subskind_of sk (SMEMTYPE n ξ) ->
    ∃ ξ',
      sk = SMEMTYPE n ξ' /\
      ref_flag_le ξ' ξ.
  Proof.
    intros Hsk.
    inversion Hsk; subst.
    eexists; eauto.
  Qed.

  Lemma type_subskinds_mem_inv_l sks τs ns ξs :
    mapM (type_skind se) τs = Some sks ->
    Forall3 (λ sk n ξ, sk = SMEMTYPE n ξ) sks ns ξs ->
    sks = map (λ '(n, ξ), SMEMTYPE n ξ) (zip ns ξs) /\
    length ns = length ξs.
  Proof.
    intros Hsk Hsubs.
    revert Hsk.
    revert τs.
    induction Hsubs; intros τs Hsk.
    - split; eauto.
    - cbn.
      subst.
      f_equal.
      pose proof (length_mapM _ _ _ Hsk) as Hlens.
      destruct τs as [|τ τs]; first (cbn in Hlens; by inversion Hlens).
      cbn -[type_skind] in Hsk.
      apply bind_Some in Hsk.
      destruct Hsk as (sk & Hev & Hsk).
      apply bind_Some in Hsk.
      destruct Hsk as (sks & Hevs & Hret).
      inversion Hret.
      subst l sk.
      eapply IHHsubs in Hevs.
      destruct Hevs as [Hsks Hlen].
      split; eauto.
      f_equal; eauto.
  Qed.

  Definition ref_flag_lub2 (ξ1 ξ2 : ref_flag) : ref_flag :=
    match ξ1 with
    | NoRefs => ξ2
    | GCRefs =>
        match ξ2 with
        | NoRefs => GCRefs
        | _ => ξ2
        end
    | AnyRefs => AnyRefs
    end.

  Lemma type_interp_len F ws τ σ n ξ :
    sem_env_interp F se ->
    has_kind F τ (MEMTYPE σ ξ) ->
    eval_size se σ = Some n ->
    type_interp rti sr τ se (SWords ws) -∗
    ⌜n = length ws⌝.
  Proof.
    iIntros (Hse Hkind Hsz) "Hty".
    rewrite type_interp_eq.
    unfold add_skind_interp.
    iDestruct "Hty" as "(%sk & %Hsk & %Hsv & Hty)".
    eapply type_skind_has_kind_agree in Hkind; eauto;
      last (cbn; by rewrite Hsz).
    inversion Hkind; subst.
    cbn in Hsv.
    clear H.
    destruct Hsv as [H _].
    iPureIntro.
    done.
  Qed.

  Lemma type_interps_lens F wss τs σs ξs ns :
    sem_env_interp F se ->
    Forall3 (λ τ σ ξ, has_kind F τ (MEMTYPE σ ξ)) τs σs ξs ->
    mapM (eval_size se) σs = Some ns ->
    ([∗ list] ws;τ ∈ wss;τs, type_interp rti sr τ se (SWords ws)) -∗
    ⌜ns = map length wss⌝.
  Proof.
    intros Hse Hkinds.
    revert wss ns.
    induction Hkinds; iIntros (wss ns Hevs) "Htys".
    - iPoseProof (big_sepL2_nil_inv_r with "Htys") as "%Hnil".
      subst.
      inversion Hevs.
      done.
    - iPoseProof (big_sepL2_cons_inv_r with "Htys") as "(%ws & %wss' & -> & Hty & Htys)".
      cbn -[eval_size] in Hevs.
      apply bind_Some in Hevs.
      destruct Hevs as (n & Hev & Hevs).
      apply bind_Some in Hevs.
      destruct Hevs as (ns' & Hevs & Hret).
      inversion Hret; subst.
      rewrite map_cons.
      iPoseProof (IHHkinds with "Htys") as "%Hlens"; first by eauto.
      iPoseProof (type_interp_len with "Hty") as "%Hlen"; eauto.
      iPureIntro; congruence.
  Qed.

  Lemma concat_inj {A} (xss yss : list (list A)):
    map length xss = map length yss ->
    concat xss = concat yss ->
    xss = yss.
  Proof.
    revert yss; induction xss; intros yss Hlens Hcats.
    - destruct yss; by inversion Hlens.
    - cbn in *.
      destruct yss; first by inversion Hlens.
      cbn in *.
      inversion Hlens.
      pose proof (app_inj_1  _ _ _ _ ltac:(eassumption) Hcats) as [Hal Hxy].
      f_equal; by eauto.
  Qed.

  Lemma skind_has_svalues_lens wss ns ξ :
    Forall2 (λ ws n, skind_has_svalue (SMEMTYPE n ξ) (SWords ws)) wss ns ->
    ns = map length wss.
  Proof.
    intros Hs.
    induction Hs.
    - done.
    - cbn.
      eapply skind_mem_words_len in H; congruence.
  Qed.

  Lemma type_interp_struct_inv {F σs ξ τs1 τ τs2 ws} :
    sem_env_interp F se ->
    has_kind F (StructT (MEMTYPE (ProdS σs) ξ) (τs1 ++ τ :: τs2)) (MEMTYPE (ProdS σs) ξ) ->
    𝕍 (StructT (MEMTYPE (ProdS σs) ξ) (τs1 ++ τ :: τs2)) (SWords ws) -∗
    ∃ wss1 wsτ wss2 ξs1 ξτ ξs2 σs1 σ σs2 ns1 n ns2,
      ⌜ws = concat wss1 ++ wsτ ++ concat wss2⌝ ∗
      ⌜ref_flag_le (ref_flag_lub ξs1) ξ⌝ ∗
      ⌜ref_flag_le ξτ ξ⌝ ∗
      ⌜ref_flag_le (ref_flag_lub ξs2) ξ⌝ ∗
      ⌜type_skind se τ = Some (SMEMTYPE n ξτ)⌝ ∗
      ⌜length ns1 = length ξs1⌝ ∗
      ⌜length ns2 = length ξs2⌝ ∗
      ⌜mapM (type_skind se) τs1 = Some (map (λ '(n, ξ), SMEMTYPE n ξ) (zip ns1 ξs1))⌝ ∗
      ⌜mapM (type_skind se) τs2 = Some (map (λ '(n, ξ), SMEMTYPE n ξ) (zip ns2 ξs2))⌝ ∗
      ⌜σs = σs1 ++ σ :: σs2⌝ ∗
      ⌜eval_size se σ = Some n⌝ ∗
      ⌜mapM (eval_size se) σs1 = Some ns1⌝ ∗
      ⌜mapM (eval_size se) σs2 = Some ns2⌝ ∗
      ([∗ list] ws;τ ∈ wss1; τs1, type_interp rti sr τ se (SWords ws)) ∗
      ([∗ list] ws;τ ∈ wss2; τs2, type_interp rti sr τ se (SWords ws)) ∗
      𝕍 τ (SWords wsτ).
  Proof.
    intros Hse Hkind.
    inversion Hkind.
    subst.
    subst κ0.
    rename H1 into Hall.
    iIntros "Hstruct".
    rewrite value_interp_eq.
    iDestruct "Hstruct" as "(%sk & %Htsk & %Hskws & Hstruct)".
    cbn in Htsk.
    apply bind_Some in Htsk; destruct Htsk as (n & Htsk & Hout).
    inversion Hout; subst sk; clear Hout.
    apply bind_Some in Htsk; destruct Htsk as (ns & Htsk & Hout).
    inversion Hout; subst n; clear Hout.
    eapply inv_Forall3_elt_l in Hall.
    destruct Hall as (σs1 & σ & σs2 & ξs1 & ξ & ξs2 & Hlen1 & Hlen2 & Hlen3 & Hlen4 & Heqσs & Heqξs & Hkinds1 & Hτkind & Hkinds2).
    subst.
    eapply mapM_elt_Some in Htsk.
    destruct Htsk as (ns1 & n & ns2 & Hevns1 & Hevn & Hevns2 & ->).
    subst.
    pose proof (skind_has_svalue_partition _ _ _ Hskws) as (wss & Hwss & ->).
    eapply inv_Forall2_elt_r in Hwss.
    destruct Hwss as (wss1 & wst & wss2 & Hlens1 & Hlens2 & -> & Hsv1 & Hsv & Hsv2).
    iExists wss1, wst, wss2.
    eapply type_skind_has_kind_Some in Hτkind as Htsk; eauto;
      last (cbn; rewrite Hevn; done).
    pose proof Hkinds1 as Hkinds1'.
    eapply type_skinds_has_kinds_Some_mem in Hkinds1'; eauto.
    destruct Hkinds1' as (sks1 & Htsks1 & Hsubs1).
    pose proof Hsubs1 as Hsubs1'.
    eapply type_subskinds_mem_inv_l in Hsubs1'; last eauto.
    destruct Hsubs1' as [-> Hlen_ξs1].
    pose proof Hkinds2 as Hkinds2'.
    eapply type_skinds_has_kinds_Some_mem in Hkinds2'; eauto.
    destruct Hkinds2' as (sks2 & Htsks2 & Hsubs2).
    pose proof Hsubs2 as Hsubs2'.
    eapply type_subskinds_mem_inv_l in Hsubs2'; last eauto.
    destruct Hsubs2' as (-> & Hlen_ξs2).
    iExists ξs1, ξ, ξs2.
    iExists σs1, σ, σs2, ns1, n, ns2.
    iSplit; first iPureIntro.
    { apply concat_app. }
    iSplit; first iPureIntro.
    { apply ref_flag_lub_incl. by apply list_subseteq_app_l. }
    iSplit; first iPureIntro.
    { apply ref_flag_lub_ub. rewrite elem_of_app. right. apply list_elem_of_here. }
    iSplit; first iPureIntro.
    { apply ref_flag_lub_incl. apply list_subseteq_app_r. by apply list_subseteq_cons. }
    iSplit; first iPureIntro.
    { assumption. }
    iSplit; first (iPureIntro; done).
    iSplit; first (iPureIntro; done).
    iSplit; first (iPureIntro; done).
    iSplit; first (iPureIntro; done).
    iSplit; first (iPureIntro; done).
    iSplit; first (iPureIntro; done).
    iSplit; first (iPureIntro; done).
    iSplit; first (iPureIntro; done).
    cbn -[type_interp].
    iDestruct "Hstruct" as "(%wss' & %Hwss' & Hinterp)".
    iEval (rewrite map_app map_cons) in "Hinterp".
    iPoseProof (big_sepL2_app_inv_r with "Hinterp") as "(%ws1 & %ws2 & -> & Hws1 & Hrest)".
    iPoseProof (big_sepL2_cons_inv_r with "Hrest") as "(%ws2' & %ws3 & -> & Hws & Hws3)".
    setoid_rewrite big_sepL2_fmap_r.
    iAssert (⌜length wst = length ws2'⌝%I) as "%Hlenwst".
    {
      destruct Hsv as [<- _].
      iEval (setoid_rewrite type_interp_eq) in "Hws".
      iDestruct "Hws" as "(%sk & %Hkind' & %Hsv & Hws)".
      rewrite Htsk in Hkind'.
      inversion Hkind'; subst sk.
      destruct Hsv as [<- _]; done.
    }
    iAssert (⌜map length wss1 = map length ws1⌝%I) as "%Hlenseq1".
    {
      iPoseProof (type_interps_lens with "Hws1") as "%Hlensws1"; eauto.
      iPureIntro.
      pose proof (skind_has_svalues_lens _ _ _ Hsv1) as Hlenssv1; eauto.
      congruence.
    }
    iAssert (⌜map length wss2 = map length ws3⌝%I) as "%Hlenseq2".
    {
      iPoseProof (type_interps_lens with "Hws3") as "%Hlensws2"; eauto.
      iPureIntro.
      pose proof (skind_has_svalues_lens _ _ _ Hsv2) as Hlenssv2; eauto.
      congruence.
    }
    rewrite !concat_app !concat_cons in Hwss'.
    inversion Hwss' as [Hwss''].
    iAssert (⌜concat wss1 = concat ws1 /\ wst = ws2' /\ concat wss2 = concat ws3⌝%I) as "%Heq1".
    {
      eapply app_inj_1 in Hwss''.
      destruct Hwss'' as [A B].
      eapply app_inj_1 in B; eauto.
      rewrite !length_concat; congruence.
    }
    destruct Heq1 as [Heq1 [Heq Heq2]].
    assert (wss1 = ws1) by (eapply concat_inj; eauto).
    assert (wss2 = ws3) by (eapply concat_inj; eauto).
    subst ws1 ws3 ws2'.
    iFrame.
  Qed.

  Lemma opt_mapM_Some {X Y} (f : X -> option Y) xs ys :
    Forall2 (λ x y, f x = Some y) xs ys <-> mapM f xs = Some ys.
  Proof.
    split.
    - intros Hall. induction Hall.
      + done.
      + cbn.
        by rewrite H IHHall.
    - revert ys.
      induction xs; intros ys Hmap; cbn.
      + inversion Hmap; done.
      + cbn in Hmap; apply bind_Some in Hmap.
        destruct Hmap as (y & Hfy & Hmap).
        apply bind_Some in Hmap.
        destruct Hmap as (ys' & Hys' & Hret).
        inversion Hret; subst.
        constructor; eauto.
  Qed.

  Lemma eval_size_emptyenv {σ n} {se': @semantic_env Σ}  :
    eval_size EmptyEnv σ = Some n ->
    eval_size se' σ = Some n.
  Proof.
    revert n.
    assert (Hwork: ∀ σs ns,
        Forall (λ σ, ∀ n, eval_size EmptyEnv σ = Some n → eval_size se' σ = Some n) σs ->
        mapM (eval_size EmptyEnv) σs = Some ns ->
        mapM (eval_size se') σs = Some ns
      ).
    {
      intros * Hall Hev.
      apply opt_mapM_Some in Hev.
      apply opt_mapM_Some.
      by eapply Forall2_mini_impl_Forall.
    }
    induction σ using size_ind; cbn; intros * Hev.
    - congruence.
    - apply bind_Some in Hev.
      destruct Hev as (ns & Hev & Hns).
      eapply Hwork in Hev; last done.
      by rewrite Hev.
    - apply bind_Some in Hev.
      destruct Hev as (ns & Hev & Hns).
      eapply Hwork in Hev; last done.
      by rewrite Hev.
    - cbn in Hev.
      apply fmap_Some in Hev.
      destruct Hev as (reps & Hev & ->).
      erewrite eval_rep_emptyenv; eauto.
    - done.
  Qed.

  Lemma eval_sizes_emptyenv {σs ns} {se': @semantic_env Σ}  :
    mapM (eval_size EmptyEnv) σs = Some ns ->
    mapM (eval_size se') σs = Some ns.
  Proof.
    rewrite <- !opt_mapM_Some.
    intros Hall.
    eapply Forall2_impl; first eapply Hall.
    intros σ n; by eapply eval_size_emptyenv.
  Qed.

  Lemma type_interps_ref_flags F wss τs σs ξs ξs' :
    sem_env_interp F se ->
    ξs ⊆ ξs' ->
    Forall3 (λ τ σ ξ, has_kind F τ (MEMTYPE σ ξ)) τs σs ξs ->
    ([∗ list] ws;τ ∈ wss;τs, type_interp rti sr τ se (SWords ws)) -∗
    ⌜Forall (forall_ptr_word (ref_flag_ptr_interp (ref_flag_lub ξs'))) (concat wss)⌝.
  Proof.
    intros Hse Hsubs Hall.
    revert wss.
    induction Hall; iIntros (wss) "Ht".
    - by iPoseProof (big_sepL2_nil_inv_r with "Ht") as "->".
    - iPoseProof (big_sepL2_cons_inv_r with "Ht") as "(%ws & %wss' & -> & Hws & Hwss)".
      iEval (setoid_rewrite type_interp_eq) in "Hws".
      iEval (cbn).
      rewrite Forall_app.
      iSplit.
      + iDestruct "Hws" as "(%sk & %Htsk & %Hws & Hws)".
        assert (∃ n, eval_kind se (MEMTYPE y z) = Some (SMEMTYPE n z)) as (n & Hev).
        {
          eapply has_kind_inv in H.
          inversion H as [? ? ? _ Hok].
          subst.
          eapply eval_kind_ok_Some in Hok; eauto.
          destruct Hok as (sk' & Hev).
          cbn in Hev.
          apply bind_Some in Hev.
          destruct Hev as (n & Hevn & Heq).
          inversion Heq; subst sk'.
          exists n.
          cbn.
          by rewrite Hevn.
        }
        eapply type_skind_has_kind_agree in Htsk; eauto.
        inversion Htsk; subst.
        cbn in Hws.
        destruct Hws as [-> Hws].
        iPureIntro.
        eapply Forall_impl; first apply Hws.
        intros [w | w] Hw; last done.
        cbn in Hw.
        eapply ref_flag_ptr_interp_le; eauto.
        apply ref_flag_lub_ub.
        apply Hsubs.
        constructor.
      + iApply IHHall; eauto.
        intros elt Hin.
        apply Hsubs.
        by constructor.
  Qed.

  Lemma resolves_path_inv_sep τ π pr :
    resolves_path τ π None pr ->
    ∀ F off ρ σ ξ ξser sz,
      sem_env_interp F se ->
      path_offset (fe_of_context F) τ π = Some off ->
      Forall (has_mono_size F) pr.(pr_prefix) ->
      has_kind F τ (MEMTYPE σ ξ) ->
      has_kind F (pr.(pr_target)) (MEMTYPE (RepS ρ) ξser) ->
      eval_size EmptyEnv (RepS ρ) = Some sz ->
      ⊢ ∀ ws,
        𝕍 τ (SWords ws) -∗
        ⌜off + sz <= length ws⌝ ∗
        (𝕍 (pr.(pr_target)) (SWords (get_path_words off sz ws)) ∗
        ∀ ws',
           ⌜length ws' = sz⌝ -∗
           𝕍 (pr.(pr_target)) (SWords ws') -∗
           𝕍 τ (SWords (update_path_words off ws ws'))).
  Proof.
    intros Hr.
    remember None as tp eqn:Htp; revert Htp.
    induction Hr; intros Htp *; iIntros (Hse Hoff Hms Ht Htgt Hev ws) "Hws".
    - cbn [pr_target pr_prefix pr_replaced] in *.
      assert (off = 0).
      {
        cbn in Hoff.
        destruct τ; congruence.
      }
      cbn -[eval_size type_interp] in *.
      subst off.
      rewrite value_interp_eq -type_interp_eq.
      iPoseProof (type_interp_len _ _ _ _ _ _ Hse with "Hws") as "%Hsz"; [|by eapply eval_size_emptyenv, Hev|].
      eapply Htgt.
      subst sz.
      iSplit; first done.
      rewrite get_path_words_all.
      iFrame.
      iIntros (ws') "%Hlen Hty".
      rewrite update_path_words_all; eauto.
    - by inversion Htp.
    - cbn in Hoff.
      eapply bind_Some in Hoff; destruct Hoff as (σs & Htsz & Hoff).
      eapply bind_Some in Hoff; destruct Hoff as (ns & Hevsz & Hoff).
      eapply bind_Some in Hoff; destruct Hoff as (τ' & Hfind & Hoff).
      eapply bind_Some in Hoff; destruct Hoff as (k & Hpoff & Hsum).
      inversion Hsum; subst off.
      assert (τ' = τ).
      {
        replace i with (length τs0) in Hfind by eauto.
        rewrite list_lookup_middle in Hfind; congruence.
      }
      subst τ'.
      inversion Ht; subst.
      rename H2 into Hkinds.
      iPoseProof (type_interp_struct_inv Hse Ht with "Hws")
        as "(%wss1& %wst& %wss2& %rs1& %rt& %rs2& %σs1& %σt& %σs2& %ns1& %nt& %ns2& Hstruct)".
      iDestruct "Hstruct" as
        "(%Hws & %Hle1 & %Hlet & %Hle2 & Hstruct)".
      iDestruct "Hstruct" as
        "(%Htsk & %Hl1 & %Hl2 & %Htsk1 & %Htsk2 & %Hσs' & %Hevt & %Hev1 & %Hev2 & Hws1 & Hws2 & Hwst)".
      subst.
      assert (length τs0 = length σs1).
      {
        eapply length_mapM in Hev1, Htsk1.
        rewrite Hev1.
        rewrite length_map length_zip -Hl1 Nat.min_id in Htsk1.
        done.
      }
      assert (length τs' = length σs2).
      {
        eapply length_mapM in Hev2, Htsk2.
        rewrite Hev2.
        rewrite length_map length_zip -Hl2 Nat.min_id in Htsk2.
        done.
      }
      assert (length τs0 = length ns1).
      {
        apply length_mapM in Hev1.
        congruence.
      }
      iPoseProof (big_sepL2_length with "Hws1") as "%Hwss1ts1".
      iPoseProof (big_sepL2_length with "Hws2") as "%Hwss2ts2".
      pose proof (inv_Forall3_elt_lm Hkinds ltac:(done) ltac:(done))
        as (ξs1 & ξ & ξs2 & Hlen_ξs1 & Hlen_ξs2 & -> & Hkinds1 & Hkind & Hkinds2).
      iPoseProof (type_interps_lens with "Hws1") as "%Hlen1"; eauto.
      iPoseProof (type_interps_lens with "Hws2") as "%Hlen2"; eauto.
      assert (σs1 = σs).
      {
        rewrite take_app_length in Htsz.
        eapply has_kinds_mem_size_agree; eauto.
      }
      subst.
      rewrite Forall_app in Hms.
      destruct Hms as [Hps Hms'].
      pose proof Ht as Ht'.
      eapply type_kind_has_kind_agree in Ht' as <-; eauto.
      inversion Ht; subst.
      rename H4 into Hfields.
      rename H5 into Heq_lub.
      subst κ1.
      pose proof (inv_Forall3_elt_lm Hfields ltac:(eauto) ltac:(eauto))
        as (ξs1' & ξ' & ξs2' & Hlen_ξs1' & Hlen_ξs2' & -> & Hkinds1' & Hkindr & Hkinds2').
      pose proof Hse as IH'.
      eapply IHHr in IH'; eauto.
      iPoseProof (IH' with "Hwst") as "[%Hlen [Ht0 Hcont]]".
      rewrite !length_app !length_concat.
      assert (ns = map length wss1).
      {
        erewrite eval_sizes_emptyenv in Hev1; eauto.
        by inversion Hev1.
      }
      subst ns.
      iSplitR; first (iPureIntro; lia).
      setoid_rewrite get_path_words_field; eauto.
      iFrame.
      cbn.
      iIntros (ws') "%Hlenws Hws'".
      subst sz.
      setoid_rewrite update_path_words_field; eauto.
      unfold pr'.
      cbn [pr_replaced].
      iSpecialize ("Hcont" with "[//] Hws'").
      iEval (cbn; rewrite value_interp_eq).
      iExists _.
      iPoseProof "Hcont" as "Hcont'".
      iEval (rewrite type_interp_eq) in "Hcont'".
      iDestruct "Hcont'" as "(%skpr & %Htskr & %Hsv & Hval)".
      assert (Hevskr : eval_kind se (MEMTYPE σt ξ') = Some (SMEMTYPE nt ξ')).
      {
        cbn.
        by rewrite Hevt.
      }
      assert (∃ ξ0, skpr = SMEMTYPE nt ξ0 /\ ref_flag_le ξ0 ξ') as (ξ0 & -> & Hle0).
      {
        eapply type_skind_has_kind_agree in Htskr; try eapply Hkindr; eauto.
        inversion Htskr; subst.
        eexists.
        split; first done.
        apply ref_flag_le_refl.
      }
      iAssert (⌜Forall (forall_ptr_word (ref_flag_ptr_interp (ref_flag_lub (ξs1' ++ ξ' :: ξs2')))) (concat wss1)⌝%I) as "%Hwss1flag".
      {
        apply inv_Forall3_elt in Hfields; try eauto.
        destruct Hfields as (? & ? & ?).
        iApply type_interps_ref_flags; last iApply "Hws1".
        1, 3: done.
        by apply list_subseteq_app_l.
      }
      iAssert (⌜Forall (forall_ptr_word (ref_flag_ptr_interp (ref_flag_lub (ξs1' ++ ξ' :: ξs2')))) (concat wss2)⌝%I) as "%Hwss2flag".
      {
        apply inv_Forall3_elt in Hfields; try eauto.
        destruct Hfields as (? & ? & ?).
        iApply type_interps_ref_flags; last iApply "Hws2".
        1, 3: done.
        apply list_subseteq_app_r.
        by apply list_subseteq_cons.
      }
      iSplitR; [iPureIntro | iSplitR; first iPureIntro].
      + cbn.
        rewrite option_mapM_app Hev1; cbn.
        rewrite Hevt; cbn.
        rewrite Hev2; done.
      + cbn in Hsv.
        destruct Hsv as [Hlensv Hsv].
        cbn.
        split.
        * rewrite length_app length_concat list_sum_app.
          rewrite length_app -Hlensv.
          by rewrite length_concat.
        * do 2 rewrite Forall_app.
          split; first done.
          split; last done.
          eapply Forall_impl; first by apply Hsv.
          intros w Hw.
          destruct w; last done.
          eapply ref_flag_ptr_interp_le; eauto.
          apply ref_flag_le_trans with (ξ2 := ξ'); first done.
          apply ref_flag_lub_ub.
          rewrite elem_of_app.
          right.
          apply list_elem_of_here.
      + cbn.
        iExists (wss1 ++ update_path_words k wst ws' :: wss2).
        iSplitR; first by rewrite concat_app concat_cons.
        iApply big_sepL2_fmap_r.
        rewrite big_sepL2_app_same_length; last tauto.
        iFrame.
        setoid_rewrite type_interp_eq.
        iExists _; eauto.
  Qed.

End PathFacts.
