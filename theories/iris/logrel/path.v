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
    match type_kind fe.(fe_type_vars) τ with
    | Some (MEMTYPE σ _) => eval_size EmptyEnv σ
    | _ => None
    end.

  Lemma has_kind_type_sz F τ σ ξ k :
    has_kind F τ (MEMTYPE σ ξ) ->
    eval_size EmptyEnv σ = Some k ->
    type_sz (fe_of_context F) τ = Some k.
  Proof.
  Admitted.

  Lemma resolves_path_sep F τ π τ__π pr :
    resolves_path τ π τ__π pr ->
    Forall (has_mono_size F) pr.(pr_prefix) ->
    has_mono_size F pr.(pr_target) ->
    exists off sz,
      path_offset (fe_of_context F) τ π = Some off /\
      type_sz (fe_of_context F) (pr.(pr_target)) = Some sz /\
      ⊢ ∀ ws,
          𝕍 τ (SWords ws) -∗
          𝕍 (pr.(pr_target)) (SWords (get_path_words off sz ws)) ∗
          ∀ ws',
            𝕍 (pr_expected pr τ__π) (SWords ws') -∗
            𝕍 pr.(pr_replaced) (SWords (update_path_words off ws ws')).
  Proof.
    intros Hpath.
    induction Hpath; cbn.
    - intros Hszs Hsz.
      eapply has_mono_size_inv in Hsz.
      destruct Hsz as (σ & ξ & k & Htgtkind & Htgtsz).
      exists 0, k.
      split; first by destruct τ.
      split; first by eapply has_kind_type_sz.
      iIntros (ws) "Hv".
      assert (Hws: length ws = k).
      { admit. }
      iSplitL "Hv".
      + by rewrite -Hws get_path_words_all.
      + iIntros (ws') "Hws'".
        assert (Hws': length ws' = k).
        { admit. }
        rewrite -Hws in Hws'.
        rewrite -> update_path_words_all by assumption.
        done.
    - intros Hszs Hsz.
      eapply has_mono_size_inv in Hsz.
      destruct Hsz as (σ & ξ & k & Htgtkind & Htgtsz).
      exists 0, k.
      split; first by destruct τ.
      split; first by eapply has_kind_type_sz.
      iIntros (ws) "Hv".
      assert (Hws: length ws = k).
      { admit. }
      iSplitL "Hv".
      + by rewrite -Hws get_path_words_all.
      + iIntros (ws') "Hws'".
        assert (Hws': length ws' = k).
        { admit. }
        rewrite -Hws in Hws'.
        rewrite -> update_path_words_all by assumption.
        done.
    - intros Hszs Hsz.
      admit.
  Admitted.

End PathFacts.
