From RichWasm Require Import
  syntax
  typing
  logrel.
From RichWasm.compiler Require Import
  memory.
From RichWasm.iris.logrel Require Import
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
    eval_size EmptyEnv σ.

  Lemma has_kind_type_sz F τ σ ξ k :
    has_kind F τ (MEMTYPE σ ξ) ->
    eval_size EmptyEnv σ = Some k ->
    type_sz (fe_of_context F) τ = Some k.
  Proof.
  Admitted.

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

  Lemma get_path_words_field F τs τ τs' σs ks off wss ws sz :
    mapM (type_size (fc_type_vars F)) (take (length τs) (τs ++ τ :: τs')) = Some σs ->
    wss !! length τs = Some ws ->
    mapM (eval_size EmptyEnv) σs = Some ks ->
    map length wss = ks ->
    length τs = length ks ->
    get_path_words (list_sum ks + off) sz (concat wss) = get_path_words off sz ws.
  Proof.
    unfold get_path_words; intros Hσs Hws Hks Hwss Hτs.
    rewrite -drop_drop.
    rewrite drop_list_sum_cat; last assumption.
    eapply drop_S in Hws.
    rewrite -Hτs Hws.
    cbn.
    rewrite drop_app.
    rewrite take_app.
    rewrite <- app_nil_r; f_equal.
    rewrite length_drop.
    admit.
  Admitted.

  Lemma resolves_path_sep F τ π τ__π pr sz :
    resolves_path τ π τ__π pr ->
    Forall (has_mono_size F) pr.(pr_prefix) ->
    type_sz (fe_of_context F) (pr_expected pr τ__π) = Some sz ->
    type_sz (fe_of_context F) (pr.(pr_target)) = Some sz ->
    exists off,
      path_offset (fe_of_context F) τ π = Some off /\
      ⊢ ∀ ws,
          𝕍 τ (SWords ws) -∗
          (𝕍 (pr.(pr_target)) (SWords (get_path_words off sz ws)) ∗
           ∀ ws',
             𝕍 (pr_expected pr τ__π) (SWords ws') -∗
             𝕍 pr.(pr_replaced) (SWords (update_path_words off ws ws'))).
  Proof.
    intros Hpath.
    revert sz.
    induction Hpath.
    - intros sz _ Hsz Hsz'.
      exists 0.
      split; first (destruct τ; done).
      iIntros (ws) "Hτ".
      assert (Hlen: length ws = sz).
      {
        admit.
      }
      rewrite <- Hlen, get_path_words_all.
      iFrame.
      iIntros (ws') "Hτ".
      assert (Hlen': length ws' = sz).
      {
        admit.
      }
      rewrite update_path_words_all; [done | congruence].
    - intros sz _ Hsz Hsz'.
      exists 0.
      split; first (destruct τ; done).
      iIntros (ws) "Hτ".
      assert (Hlen: length ws = sz).
      {
        admit.
      }
      rewrite <- Hlen, get_path_words_all.
      iFrame.
      iIntros (ws') "Hτ'".
      assert (Hlen': length ws' = sz).
      {
        admit.
      }
      rewrite update_path_words_all; [done | congruence].
    - intros sz Hszs Hsz Hsz'.
      rewrite Forall_app in Hszs.
      destruct Hszs as [Hszτs0 Hszpr].
      specialize (IHHpath sz Hszpr Hsz Hsz').
      destruct IHHpath as (off0 & Hoff0 & IH).
      assert (Hts: ∃ σs ks,
                 mapM (type_size (fc_type_vars F)) (take i (τs0 ++ τ :: τs')) = Some σs /\
                 mapM (eval_size EmptyEnv) σs = Some ks).
      {
        admit.
      }
      assert (Htsi: (τs0 ++ τ :: τs') !! i = Some τ).
      {
        rewrite -H lookup_app_r; [|eauto].
        by rewrite Nat.sub_diag.
      }
      destruct Hts as (σs & ks & Hσs & Hks).
      exists (list_sum ks + off0).
      cbn [path_offset].
      split.
      {
        rewrite Hσs; cbn.
        rewrite Hks; cbn.
        rewrite Htsi; cbn.
        rewrite Hoff0; cbn.
        done.
      }
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
      iPoseProof (IH $! ws') as "IH".
      rewrite big_sepL2_fmap_r.
      Search big_sepL2 app.
      iPoseProof (big_sepL2_app_inv_r with "Hws") as "(%wss1 & %wss2' & -> & Hwss1  & Hwss2')".
      iPoseProof (big_sepL2_cons_inv_r with "Hwss2'") as "(%ws'' & %wss2 & -> & Hws' & Hwss2)".
      assert (ws'' = ws').
      {
        admit.
      }
      subst ws''.
      iSpecialize ("IH" with "Hws'").
      iDestruct "IH" as "[Htgt Hret]".
      inversion Hwss; subst ws; clear Hwss.
      change (pr_target pr') with (pr_target pr) in *.
      simpl (pr_replaced pr').
      rewrite length_map in Hlenwss.
      subst i.
      erewrite get_path_words_field; eauto.
      + iFrame.
        iIntros (ws'') "Hws''".
        iSpecialize ("Hret" with "Hws''").
        cbn.
        iExists _.
        iSplitR.
        { admit. }
        iSplitR.
        { admit. }
        iExists (wss1 ++ (update_path_words off0 ws' ws'') :: wss2).
        iSplit.
        { admit. }
        rewrite big_sepL2_fmap_r.
        iApply (big_sepL2_app with "Hwss1").
        iFrame.
      + admit.
      + rewrite take_app_length in Hσs.
        apply length_mapM in Hσs, Hks.
        congruence.
  Admitted.

End PathFacts.
