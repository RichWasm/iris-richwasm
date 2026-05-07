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
      has_kind F τ (MEMTYPE σ ξ) /\
      eval_size EmptyEnv σ = Some k.
  Proof.
    intros Hmono.
    inversion Hmono as [F' τ' σ ξ Hkind Hsz HF' Hτ'].
    subst F' τ'; clear Hmono.
    unfold is_mono_size in Hsz.
    eapply eval_size_empty_ok_Some in Hsz.
    destruct Hsz as [k Hsz].
    eauto.
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
    erewrite subkind_size_inv; eauto; cbn.
    by rewrite mono_size_eval_emp.
  Qed.

  Lemma split_concat_ws_field F τs1 τ τs2 σs ks wss :
    mapM (type_size (fc_type_vars F)) (take (length τs1) (τs1 ++ τ :: τs2)) = Some σs ->
    mapM (eval_size EmptyEnv) σs = Some ks ->
    ∃ (wss1 wss2 : list (list word)) (ws : list word)
      (ks1 ks2 : list nat) (k : nat),
      length wss1 = length τs1 /\
      length ks1 = length τs1 /\
      length wss2 = length τs2 /\
      length ks2 = length τs2 /\
      wss = wss1 ++ ws :: wss2 /\
      ks = ks1 ++ k :: ks2 /\
      map length wss1 = ks1 /\
      map length wss2 = ks2 /\
      length ws = k.
  Proof.
  Abort.

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
    get_path_words (list_sum ks + off) sz (concat (wss1 ++ ws :: wss2)) = get_path_words off sz ws.
  Proof.
    unfold get_path_words; intros Hσs Hws Hsz Hks Hwss Hτs.
    rewrite -drop_drop.
  Admitted.

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
    update_path_words (list_sum ks + off) (concat (wss1 ++ ws :: wss2)) ws' =
      concat wss1 ++ update_path_words off ws ws' ++ concat wss2.
  Proof.
    unfold update_path_words; intros Hσs Hwss1 Hlens Hks Hszs Hoff.
    rewrite !concat_app !concat_cons.
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
    iPoseProof (kinding_sound with "Hws") as "%Hkind"; eauto.
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

  Lemma val_interps_type_szs F τs wss :
    sem_env_interp F se ->
    Forall (has_mono_size F) τs ->
    ⊢ ([∗ list] ws;τ ∈ wss;τs, type_interp rti sr τ se (SWords ws)) -∗
      ∃ szs, ⌜mapM (type_sz (fe_of_context F)) τs = Some szs⌝ ∗
             ⌜map length wss = szs⌝.
  Proof.
  Admitted.

  Lemma type_szs_interchg F τs σs ns ns' :
    mapM (eval_size EmptyEnv) σs = Some ns ->
    mapM (type_sz (fe_of_context F)) τs = Some ns' ->
    mapM (type_size (fc_type_vars F)) τs = Some σs ->
    Forall (has_mono_size F) τs ->
    ns' = ns.
  Admitted.

  Lemma field_update_kind_bound F κ κ' τs1 τ τ' τs2 :
    has_kind F (StructT κ (τs1 ++ τ' :: τs2)) κ' ->
    sem_env_interp F se ->
    ∀ sk sk',
      type_skind se τ' = Some sk ->
      type_skind se (StructT κ (τs1 ++ τ :: τs2)) = Some sk' ->
      subskind_of sk sk'.
  Proof.
    intros Hkind.
    remember (StructT κ (τs1 ++ τ' :: τs2)) as S.
    revert HeqS.
  Admitted.

  Lemma struct_kind_weak_inv F S κ :
    has_kind F S κ ->
    ∀ κ' τs1 τs2 τ,
      S = StructT κ' (τs1 ++ τ :: τs2) ->
      ∃ κ, has_kind F τ κ.
  Proof.
    induction 1; intros * HS; try inversion HS.
    - subst.
      eapply Forall2_app_inv_l in H.
      destruct H as (σs1 & σs2 & _ & Hall & ->).
      eapply Forall2_cons_inv_l in Hall.
      destruct Hall as (σ & σs3 & Hτ & _ & ->).
      eauto.
    - subst; eauto.
  Qed.

  Lemma type_skind_size_agree F τ n r σ sz :
    type_skind se τ = Some (SMEMTYPE n r) ->
    type_size (fc_type_vars F) τ = Some σ ->
    eval_size EmptyEnv σ = Some sz ->
    n = sz.
  Proof.
  Admitted.

  Lemma resolves_path_sep_kinds F τ π τ__π pr :
    resolves_path τ π τ__π pr ->
    forall σ σexp σtgt sz off ξ szt r,
    sem_env_interp F se ->
    has_kind F τ (MEMTYPE σ ξ) ->
    eval_kind se (MEMTYPE σ ξ) = Some (SMEMTYPE szt r) ->
    Forall (has_mono_size F) pr.(pr_prefix) ->
    type_size F.(fc_type_vars) (pr_expected pr τ__π) = Some σexp ->
    eval_size EmptyEnv σexp = Some sz ->
    type_size F.(fc_type_vars) pr.(pr_target) = Some σtgt ->
    eval_size EmptyEnv σtgt = Some sz ->
    path_offset (fe_of_context F) τ π = Some off ->
    ∀ sk ws,
      type_skind se τ = Some sk ->
      skind_has_svalue sk (SWords ws) ->
      off + sz <= length ws /\
      (∃ sk_tgt,
          type_skind se (pr.(pr_target)) = Some sk_tgt /\
          skind_has_svalue sk_tgt (SWords (get_path_words off sz ws)) /\
          ∀ sk_exp ws',
            length ws' = sz ->
            type_skind se (pr_expected pr τ__π) = Some sk_exp /\
            skind_has_svalue sk_exp (SWords ws') ->
            ∃ sk_repl,
              type_skind se pr.(pr_replaced) = Some sk_repl /\
              skind_has_svalue sk_repl (SWords (update_path_words off ws ws'))).
  Proof.
    induction 1; intros * Hse Hτ Hskev Hpfx Hσexp Hszexp Hσtgt Htgtexp Hoff sk ws Hsk Hskws.
    - assert (off = 0) by (destruct τ; cbn in *; congruence).
      subst off; rewrite Nat.add_0_l.
      destruct sk.
      {
        cbn in Hskws.
        destruct Hskws as [Hareps Hatoms].
        destruct Hareps as (? & Hcontra & _).
        congruence.
      }
      pose proof Hskws as Hskws'.
      destruct Hskws' as [Hlen Hflags].
      cbn in Hlen.
      subst n.
      cbn in Hσexp, Hσtgt.
      assert (length ws = sz) by (eapply type_skind_size_agree; eauto).
      split; first lia.
      cbn [pr_target pr_expected pr_replaced].
      eexists.
      split; eauto.
      subst sz.
      rewrite !get_path_words_all.
      split; first done.
      intros sk_exp ws' Hlens [Htys Hsem].
      eexists; split; eauto.
      by rewrite update_path_words_all.
    - admit. (* similar to prev case *)
    - rewrite Forall_app in Hpfx.
      destruct Hpfx as [Hszτs0 Hszpr].
      cbn in Hoff.
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
      eapply type_skind_has_kind_Some in Hτ; eauto.
      destruct Hτ as (sk' & Htsk' & Hsub); eauto.
      inversion Hsub; subst.
      eapply IHresolves_path in Hpoff.
      admit.
  Admitted.

  Lemma resolves_path_sep F τ π τ__π pr sz off :
    resolves_path τ π τ__π pr ->
    sem_env_interp F se ->
    Forall (has_mono_size F) pr.(pr_prefix) ->
    has_mono_size F (pr_expected pr τ__π) ->
    has_mono_size F (pr.(pr_target)) ->
    type_sz (fe_of_context F) (pr_expected pr τ__π) = Some sz ->
    type_sz (fe_of_context F) (pr.(pr_target)) = Some sz ->
    path_offset (fe_of_context F) τ π = Some off ->
    (∃ κ, has_kind F pr.(pr_replaced) κ) ->
    ⊢ ∀ ws,
        𝕍 τ (SWords ws) -∗
        ⌜off + sz <= length ws⌝ ∗
        (𝕍 (pr.(pr_target)) (SWords (get_path_words off sz ws)) ∗
         ∀ ws',
           ⌜length ws' = sz⌝ -∗
           𝕍 (pr_expected pr τ__π) (SWords ws') -∗
           𝕍 pr.(pr_replaced) (SWords (update_path_words off ws ws'))).
  Proof.
    intros Hpath.
    revert sz off.
    induction Hpath;
      intros sz off HF Hmonos Hmono Hmono' Hsz Hsz' Hoff Hkind.
    - cbn in *.
      iIntros (ws) "Hτ".
      iPoseProof (val_interp_type_sz with "Hτ") as "(%szt & %Hszt & %Hlen)"; eauto.
      rewrite Hsz in Hszt; inversion Hszt; subst szt.
      assert (off = 0).
      {
        cbn in Hoff; destruct τ; congruence.
      }
      subst off.
      rewrite get_path_words_all.
      iFrame.
      iSplit; first (iPureIntro; lia).
      iIntros (ws' Hlens') "Hτ".
      iPoseProof (val_interp_type_sz with "Hτ") as "(%sz' & %Hszt' & %Hlen')"; eauto.
      rewrite update_path_words_all; [done | congruence].
    - cbn in *.
      iIntros (ws) "Hτ".
      iPoseProof (val_interp_type_sz with "Hτ") as "(%szt & %Hszt & %Hlen)"; eauto.
      rewrite Hsz' in Hszt; inversion Hszt; subst szt.
      assert (off = 0).
      {
        cbn in Hoff; destruct τ; congruence.
      }
      subst off.
      rewrite get_path_words_all.
      iFrame.
      iSplit; first (iPureIntro; lia).
      iIntros (ws' Hws') "Hτ".
      iPoseProof (val_interp_type_sz with "Hτ") as "(%sz' & %Hszt' & %Hlen')"; eauto.
      rewrite update_path_words_all; [done | congruence].
    - rewrite Forall_app in Hmonos.
      destruct Hmonos as [Hszτs0 Hszpr].
      cbn in Hoff.
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
      assert (∃ κ', has_kind F (pr_replaced pr) κ').
      {
        destruct Hkind as [κ' Hkind].
        eapply struct_kind_weak_inv; eauto.
      }
      eapply IHHpath in Hpoff; eauto.
      cbn in Hkind.
      iIntros (ws) "Hws".
      iEval (unfold value_interp; cbn -[add_skind_interp]) in "Hws".
      iDestruct "Hws" as "(%sκ & %Hevκ & %Hsv & %wss & %Hwss & Hws)".
      iPoseProof (big_sepL2_length with "Hws") as "%Hlenwss".
      assert (Hws': ∃ ws', wss !! i = Some ws').
      {
        eapply lookup_lt_is_Some_2.
        rewrite Hlenwss length_map length_app length_cons -H.
        apply Nat.lt_add_pos_r.
        lia.
      }
      destruct Hws' as [ws' Hwssi].
      iPoseProof (Hpoff $! ws') as "IH".
      rewrite big_sepL2_fmap_r.
      iPoseProof (big_sepL2_app_inv_r with "Hws") as "(%wss1 & %wss2' & -> & Hwss1  & Hwss2')".
      iPoseProof (big_sepL2_length with "Hwss1") as "%Hlenwss1".
      iPoseProof (big_sepL2_cons_inv_r with "Hwss2'") as "(%ws'' & %wss2 & -> & Hws' & Hwss2)".
      iPoseProof (big_sepL2_length with "Hwss2") as "%Hlenwss2".
      assert (ws'' = ws').
      {
        subst i.
        rewrite list_lookup_middle in Hwssi; first congruence.
        by symmetry.
      }
      subst ws''.
      subst i.
      rewrite take_app_length in Htsz.
      assert (length τs0 = length ns).
      {
        eapply length_mapM in Hevsz, Htsz.
        congruence.
      }
      assert (mapM (type_size (fc_type_vars F)) (take (length τs0) (τs0 ++ τ :: τs')) = Some σs).
      {
        by rewrite take_app_length.
      }
      iPoseProof (val_interps_type_szs with "Hwss1") as "(%ns' & %Hns' & %Hlenswss1)"; eauto.
      replace ns' with ns in *
        by (symmetry; eapply type_szs_interchg; eauto).
      iSpecialize ("IH" with "Hws'").
      iDestruct "IH" as "(%Hksz & Htgt & Hret)".
      iSplitR.
      {
        iPureIntro.
        inversion Hwss.
        rewrite length_concat map_app map_cons list_sum_app.
        simpl.
        rewrite Hlenswss1.
        lia.
      }
      inversion Hwss; subst ws; clear Hwss.
      change (pr_target pr') with (pr_target pr) in *.
      simpl (pr_replaced pr').
      rewrite length_map in Hlenwss.
      erewrite get_path_words_field; eauto.
      iFrame.
      iIntros (ws'' Hlens) "Hws''".
      iPoseProof (val_interp_type_sz with "Hws''") as "(%sz'' & %Hszt'' & %Hlen'')"; eauto.
      assert (k + length ws'' ≤ length ws') by congruence.
      erewrite update_path_words_field; eauto.
      iSpecialize ("Hret" with "[//] Hws''").
      unfold value_interp.
      cbn -[type_interp].
      rewrite !type_interp_eq.
      iDestruct "Hret" as "(%sk & %Htsk & %Hsvsk & Hret)".
      destruct sκ; inversion Hsv.
      {
        inversion H3.
        destruct H4.
        destruct H4.
        congruence.
      }
      assert (Hsubs: subskind_of sk (SMEMTYPE n r)).
      {
        destruct Hkind as [κ' Hkind].
        eapply field_update_kind_bound; eauto.
      }
      cbn in Hevκ.
      iExists _; iSplitR; first by iPureIntro.
      iSplitR.
      {
        iPureIntro.
        cbn in H2, H3.
        cbn.
        subst.
        split.
        - rewrite !concat_app.
          rewrite length_app.
          rewrite length_app.
          rewrite concat_cons length_app.
          rewrite length_app.
          f_equal.
          f_equal.
          by rewrite update_path_words_size.
        - destruct H4 as (wsx & Hinv & Hbefore).
          inversion Hinv; subst wsx; clear Hinv.
          eexists; split; first done.
          rewrite concat_app concat_cons in Hbefore.
          eapply Forall_app in Hbefore; destruct Hbefore as [Hbefore1 Hbefore2].
          eapply Forall_app in Hbefore2; destruct Hbefore2 as [Hbefore Hbefore3].
          eapply Forall_app.
          split; first done.
          eapply Forall_app.
          split; last done.
          destruct sk.
          {
            unfold has_areps in Hsvsk.
            destruct Hsvsk as (? &  ? & ? & ?).
            congruence.
          }
          destruct Hsvsk as (Hn & Hr0).
          cbn in Hr0.
          destruct Hr0 as (ws0 & Hws0eq & Hrefs).
          inversion Hws0eq; subst ws0.
          eapply Forall_impl.
          eauto.
          intros.
          destruct x; cbn in *; try done.
          eapply ref_flag_interp_le; eauto.
          by inversion Hsubs.
      }
      iExists (wss1 ++ (update_path_words k ws' ws'') :: wss2).
      iSplit.
      { by rewrite !concat_app. }
      rewrite big_sepL2_fmap_r.
      iApply (big_sepL2_app with "Hwss1").
      setoid_rewrite type_interp_eq.
      iFrame; eauto.
  Qed.

End PathFacts.
