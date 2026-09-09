(* Fundamental theorem for the kind system:
     well-kinded syntactic types are semantically well-kinded *)

Require Import RecordUpdate.RecordUpdate.
From iris.proofmode Require Import base proofmode classes.
From iris Require Import
          bi.bi
          bi.lib.fixpoint_banach.
Import bi.
From RichWasm Require Import layout syntax typing kinding_subst util.
From RichWasm.compiler Require Import prelude module codegen.
From RichWasm.iris Require Import autowp memory util wp_codegen lenient_wp logpred.
Require Import RichWasm.iris.logrel.
Require Import RichWasm.iris.logrel.env_props.
From stdpp Require Import list.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

(* Setting up Inhabited instances allows commuting existential quantifiers
   with later modalities, like this:

     ▷ (exists sk, P sk) ⊣⊢ exists sk, ▷ P sk

 *)
#[global]
Instance skind_inhabited : Inhabited skind :=
  populate (SVALTYPE [] NoRefs).

#[global]
Instance atom_inhabited : Inhabited atom :=
  populate (PtrA (PtrInt 0)).

Section kinding.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma ref_flag_ptr_interp_le ξ ξ' p :
    ref_flag_le ξ' ξ ->
    ref_flag_ptr_interp ξ' p ->
    ref_flag_ptr_interp ξ p.
  Proof.
    intros Hle Hinterp.
    by destruct ξ; destruct ξ'; destruct p.
  Qed.

  Lemma mapM_kind_rep_zip ρs ξs :
    length ρs = length ξs ->
    mapM kind_rep (zip_with VALTYPE ρs ξs) = Some ρs.
  Proof.
    revert ξs.
    induction ρs as [|ρ ρs IH]; intros [|ξ ξs] Hlen; try done.
    cbn in *.
    by erewrite IH by lia.
  Qed.

  Lemma mapM_kind_size_zip σs ξs :
    length σs = length ξs ->
    mapM kind_size (zip_with MEMTYPE σs ξs) = Some σs.
  Proof.
    revert ξs.
    induction σs as [|σ σs IH]; intros [|ξ ξs] Hlen; try done.
    cbn in *.
    by erewrite IH by lia.
  Qed.

  Lemma map_kind_ref_flag_zip_val ρs ξs :
    length ρs = length ξs ->
    map kind_ref_flag (zip_with VALTYPE ρs ξs) = ξs.
  Proof.
    revert ξs.
    induction ρs as [|ρ ρs IH]; intros [|ξ ξs] Hlen; try done.
    cbn in *.
    f_equal.
    apply IH; lia.
  Qed.

  Lemma map_kind_ref_flag_zip_mem σs ξs :
    length σs = length ξs ->
    map kind_ref_flag (zip_with MEMTYPE σs ξs) = ξs.
  Proof.
    revert ξs.
    induction σs as [|σ σs IH]; intros [|ξ ξs] Hlen; try done.
    cbn in *.
    f_equal.
    apply IH; lia.
  Qed.

  Lemma forall3_mapM_type_kind_val κs τs ρs ξs :
    Forall3 (fun τ ρ ξ => type_kind κs τ = Some (VALTYPE ρ ξ)) τs ρs ξs ->
    mapM (type_kind κs) τs = Some (zip_with VALTYPE ρs ξs).
  Proof.
    intros H.
    apply mapM_Some_2.
    induction H; cbn; constructor; auto.
  Qed.

  Lemma forall3_mapM_type_kind_mem κs τs σs ξs :
    Forall3 (fun τ σ ξ => type_kind κs τ = Some (MEMTYPE σ ξ)) τs σs ξs ->
    mapM (type_kind κs) τs = Some (zip_with MEMTYPE σs ξs).
  Proof.
    intros H.
    apply mapM_Some_2.
    induction H; cbn; constructor; auto.
  Qed.

  Lemma forall3_mapM_type_rep_val κs τs ρs ξs :
    Forall3 (fun τ ρ ξ => type_kind κs τ = Some (VALTYPE ρ ξ)) τs ρs ξs ->
    mapM (type_rep κs) τs = Some ρs.
  Proof.
    induction 1 as [| τ ρ ξ τs ρs ξs Hhd _ IH]; cbn; first done.
    unfold type_rep.
    rewrite Hhd; cbn.
    by rewrite IH.
  Qed.

  Lemma type_kind_has_kind_Some F τ κ :
    has_kind F τ κ ->
    type_kind F.(fc_type_vars) τ = Some κ.
  Proof using.
    intros H.
    induction H using has_kind_ind' with (P0 := λ _ _, True) (Pi := λ _ _, True).
    - done.
    - done.
    - done.
    - done.
    - done.
    - (* KSum *)
      cbn.
      match goal with
      | H : Forall3 (fun τ ρ ξ => type_kind _ τ = Some (VALTYPE ρ ξ)) _ _ _ |- _ =>
          pose proof (Forall3_length_lm _ _ _ _ H) as Hlm;
          pose proof (Forall3_length_lr _ _ _ _ H) as Hlr;
          erewrite (forall3_mapM_type_kind_val _ _ _ _ H)
      end.
      cbn.
      erewrite mapM_kind_rep_zip by lia.
      erewrite map_kind_ref_flag_zip_val by lia.
      done.
    - (* KVariant *)
      cbn.
      match goal with
      | H : Forall3 (fun τ σ ξ => type_kind _ τ = Some (MEMTYPE σ ξ)) _ _ _ |- _ =>
          pose proof (Forall3_length_lm _ _ _ _ H) as Hlm;
          pose proof (Forall3_length_lr _ _ _ _ H) as Hlr;
          erewrite (forall3_mapM_type_kind_mem _ _ _ _ H)
      end.
      cbn.
      erewrite mapM_kind_size_zip by lia.
      erewrite map_kind_ref_flag_zip_mem by lia.
      done.
    - (* KProd *)
      cbn.
      match goal with
      | H : Forall3 (fun τ ρ ξ => type_kind _ τ = Some (VALTYPE ρ ξ)) _ _ _ |- _ =>
          pose proof (Forall3_length_lm _ _ _ _ H) as Hlm;
          pose proof (Forall3_length_lr _ _ _ _ H) as Hlr;
          erewrite (forall3_mapM_type_kind_val _ _ _ _ H)
      end.
      cbn.
      erewrite mapM_kind_rep_zip by lia.
      erewrite map_kind_ref_flag_zip_val by lia.
      done.
    - (* KStruct *)
      cbn.
      match goal with
      | H : Forall3 (fun τ σ ξ => type_kind _ τ = Some (MEMTYPE σ ξ)) _ _ _ |- _ =>
          pose proof (Forall3_length_lm _ _ _ _ H) as Hlm;
          pose proof (Forall3_length_lr _ _ _ _ H) as Hlr;
          erewrite (forall3_mapM_type_kind_mem _ _ _ _ H)
      end.
      cbn.
      erewrite mapM_kind_size_zip by lia.
      erewrite map_kind_ref_flag_zip_mem by lia.
      done.
    - (* KRefVar *)
      cbn.
      match goal with
      | H : type_kind _ _ = Some (MEMTYPE _ _) |- _ => rewrite H
      end.
      done.
    - (* KRefMM *)
      cbn.
      match goal with
      | H : type_kind _ _ = Some (MEMTYPE _ _) |- _ => rewrite H
      end.
      done.
    - (* KRefGC *)
      cbn.
      match goal with
      | H : type_kind _ _ = Some (MEMTYPE _ _) |- _ => rewrite H
      end.
      done.
    - (* KCodeRef *)
      done.
    - (* KSer *)
      cbn.
      match goal with
      | H : type_kind _ _ = Some (VALTYPE _ _) |- _ => rewrite H
      end.
      done.
    - (* KPlug *)
      done.
    - (* KSpan *)
      done.
    - (* KRec *)
      done.
    - (* KExistsMem *)
      done.
    - (* KExistsRep *)
      done.
    - (* KExistsSize *)
      done.
    - (* KExistsType *)
      done.
    - (* KVar *)
      cbn.
      match goal with
      | H : fc_type_vars _ !! _ = Some _ |- _ => exact H
      end.
    - done.
    - done.
    - done.
    - done.
    - done.
    - done.
  Qed.

  Lemma type_kind_has_kind_is_Some F τ κ :
    has_kind F τ κ ->
    is_Some (type_kind F.(fc_type_vars) τ).
  Proof using.
    intros H.
    eexists.
    by eapply type_kind_has_kind_Some.
  Qed.

  Lemma type_kind_has_kind_agree F τ κ κ' :
    has_kind F τ κ ->
    type_kind F.(fc_type_vars) τ = Some κ' ->
    κ = κ'.
  Proof using.
    intros H Heq.
    pose proof (type_kind_has_kind_Some F τ κ H) as Heq'.
    rewrite Heq' in Heq.
    by inversion Heq.
  Qed.

  Lemma has_kind_agree F τ κ κ' :
    has_kind F τ κ →
    has_kind F τ κ' →
    κ = κ'.
  Proof.
    intros H1 H2.
    have Hsome := type_kind_has_kind_is_Some _ _ _ H1.
    destruct Hsome as [κ'' Hκ''].
    have Hsub1 := type_kind_has_kind_agree _ _ _ _ H1 Hκ''.
    have Hsub2 := type_kind_has_kind_agree _ _ _ _ H2 Hκ''.
    by rewrite Hsub2.
  Qed.

  Lemma has_kind_agree_f F τ ρ ξ σ ξ' :
    has_kind F τ (VALTYPE ρ ξ) →
    has_kind F τ (MEMTYPE σ ξ') →
    False.
  Proof.
    intros H1 H2.
    have H := has_kind_agree _ _ _ _ H1 H2.
    inversion H.
  Qed.

  Lemma subkind_rep_inv κ κ' :
    subkind_of κ κ' ->
    kind_rep κ = kind_rep κ'.
  Proof.
    by induction 1.
  Qed.

  Lemma subkind_size_inv κ κ' :
    subkind_of κ κ' ->
    kind_size κ = kind_size κ'.
  Proof.
    by induction 1.
  Qed.

  Lemma subkind_preserves_valtype κ ρ ξ :
    subkind_of κ (VALTYPE ρ ξ) ->
    exists ξ0, κ = VALTYPE ρ ξ0 /\ ref_flag_le ξ0 ξ.
  Proof.
    intros.
    inversion H.
    subst.
    by eexists.
  Qed.

  Lemma has_kind_ref_ty F κ' μ β τ :
    has_kind F (RefT μ β τ) κ' ->
    ∃ σ ξ,
      has_kind F τ (MEMTYPE σ ξ).
  Proof.
    intros Hkind.
    remember (RefT μ β τ) as τ0 eqn:Href.
    revert Href.
    revert μ.
    induction Hkind; intros μ' Href;
      try congruence.
    - inversion Href; subst.
      by exists σ, ξ.
    - inversion Href.
      subst.
      by exists σ, ξ.
    - inversion Href.
      subst.
      by exists σ, ξ.
  Qed.

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

  Lemma type_rep_has_kind_agree F τ ρ ξ :
    has_kind F τ (VALTYPE ρ ξ) ->
    type_rep F.(fc_type_vars) τ = Some ρ.
  Proof.
    intros Hκ.
    apply bind_Some.
    apply type_kind_has_kind_is_Some in Hκ as Htype_kind.
    destruct Htype_kind as [κ' Hκ'].
    eexists.
    split; first done.
    by pose proof (type_kind_has_kind_agree _ _ _ _ Hκ Hκ') as <-.
  Qed.

  Lemma subkind_subskind (se : semantic_env (Σ:=Σ)) κ κ' sκ sκ' :
    eval_kind se κ = Some sκ ->
    eval_kind se κ' = Some sκ' ->
    subkind_of κ κ' ->
    subskind_of sκ sκ'.
  Proof.
    intros Heval_κ Heval_κ' Hsubk.
    destruct κ.
    - inversion Hsubk.
      subst.
      apply bind_Some in Heval_κ as (ιs & Hιs & Hsκ).
      apply bind_Some in Heval_κ' as (ιs' & Hιs' & Hsκ').
      inversion Hsκ.
      inversion Hsκ'.
      rewrite Hιs in Hιs'.
      inversion Hιs'.
      by constructor.
    - inversion Hsubk.
      subst.
      apply bind_Some in Heval_κ as (n & Hn & Hsκ).
      apply bind_Some in Heval_κ' as (n' & Hn' & Hsκ').
      inversion Hsκ.
      inversion Hsκ'.
      rewrite Hn in Hn'.
      inversion Hn'.
      by constructor.
  Qed.

  Lemma eval_rep_ok_Some' K se ρ :
    kind_ctx_interp (Σ:=Σ) K se ->
    rep_ok K ρ ->
    is_Some (eval_rep se ρ).
  Proof.
    intros Hse Hok.
    induction ρ using rep_ind.
    - inversion Hok as [K' n Hidx HK Hn| | |]; subst K' n.
      destruct Hse as (_ & Hrepv & _).
      rewrite Hrepv in Hidx.
      apply list_lookup_lookup_total_lt in Hidx.
      by eexists.
    - inversion Hok as [|K' ρs' Hρs HK Hρs'| |].
      subst K' ρs'.
      pose proof (List.Forall_and H Hρs) as H'.
      clear H Hρs.
      apply Forall_impl with (Q := is_Some ∘ eval_rep se) in H'.
      + rewrite <- mapM_is_Some in H'. by apply fmap_is_Some.
      + intros ρ [Hsome ?]. by apply Hsome.
    - inversion Hok as [| |K' ρs' Hρs HK Hρs'|].
      subst K' ρs'.
      pose proof (List.Forall_and H Hρs) as H'.
      clear H Hρs.
      apply Forall_impl with (Q := is_Some ∘ eval_rep se) in H'.
      + rewrite <- mapM_is_Some in H'. by apply fmap_is_Some.
      + intros ρ [Hsome ?]. by apply Hsome.
    - done.
  Qed.

  Lemma eval_rep_ok_Some F se ρ :
    sem_env_interp (Σ:=Σ) F se ->
    rep_ok F.(fc_kind_ctx) ρ ->
    is_Some (eval_rep se ρ).
  Proof.
    intros [Hsek _] Hok.
    by eapply eval_rep_ok_Some'.
  Qed.

  Lemma eval_size_ok_Some' K se σ :
    kind_ctx_interp (Σ:=Σ) K se ->
    size_ok K σ ->
    is_Some (eval_size se σ).
  Proof.
    intros Hse Hok.
    induction σ using size_ind.
    - inversion Hok as [K' n Hidx HK Hn| | | |].
      subst K' n.
      destruct Hse as (_ & _ & Hsizev).
      rewrite Hsizev in Hidx.
      apply list_lookup_lookup_total_lt in Hidx.
      by eexists.
    - inversion Hok as [|K' σs' Hσs HK Hσs'| | |].
      subst K' σs'.
      pose proof (List.Forall_and H Hσs) as H'.
      clear H Hσs.
      apply Forall_impl with (Q := is_Some ∘ eval_size se) in H'.
      + rewrite <- mapM_is_Some in H'. by apply fmap_is_Some.
      + intros σ [Hsome ?]. by apply Hsome.
    - inversion Hok as [| |K' σs' Hσs HK Hσs'| |].
      subst K' σs'.
      pose proof (List.Forall_and H Hσs) as H'.
      clear H Hσs.
      apply Forall_impl with (Q := is_Some ∘ eval_size se) in H'.
      + rewrite <- mapM_is_Some in H'. by apply fmap_is_Some.
      + intros σ [Hsome ?]. by apply Hsome.
    - inversion Hok as [| | |K' ρ' Hok_ρ HK Hρ'|].
      subst K' ρ'.
      apply fmap_is_Some.
      by eapply eval_rep_ok_Some'.
    - done.
  Qed.

  Lemma eval_size_ok_Some F se σ :
    sem_env_interp (Σ:=Σ) F se ->
    size_ok F.(fc_kind_ctx) σ ->
    is_Some (eval_size se σ).
  Proof.
    intros [Hsek _] Hok.
    by eapply eval_size_ok_Some'.
  Qed.

  Lemma eval_kind_ok_Some' K se κ :
    kind_ctx_interp (Σ:=Σ) K se ->
    kind_ok K κ ->
    is_Some (eval_kind se κ).
  Proof.
    intros Hse Hok.
    destruct κ as [ρ ξ|].
    - inversion Hok as [K' ρ' ξ' Hok_ρ|].
      subst K' ρ' ξ'.
      cbn.
      by eapply eval_rep_ok_Some' in Hok_ρ as [ιs ->].
    - inversion Hok as [|K' σ ξ Hok_σ].
      subst K' σ ξ.
      cbn.
      by eapply eval_size_ok_Some' in Hok_σ as [n ->].
  Qed.

  Lemma eval_kind_ok_Some F se κ :
    sem_env_interp (Σ:=Σ) F se ->
    kind_ok F.(fc_kind_ctx) κ ->
    is_Some (eval_kind se κ).
  Proof.
    intros [Hsek _] Hok.
    by eapply eval_kind_ok_Some'.
  Qed.

  Lemma forall3_and_l {A B C} (P : A -> Prop) (Q : A -> B -> C -> Prop) xs ys zs :
    Forall P xs -> Forall3 Q xs ys zs -> Forall3 (fun x y z => P x /\ Q x y z) xs ys zs.
  Proof.
    intros HP HQ.
    induction HQ; inversion HP; subst; constructor; auto.
  Qed.

  Lemma forall3_forall_m {A B C} (Q : A -> B -> C -> Prop) (R : B -> Prop) xs ys zs :
    Forall3 Q xs ys zs -> (forall x y z, Q x y z -> R y) -> Forall R ys.
  Proof.
    intros HQ Himpl.
    induction HQ; constructor; eauto.
  Qed.

  Lemma mapM_skind_rep_zip (ιss : list (list atomic_rep)) ξs :
    length ιss = length ξs ->
    mapM skind_rep (zip_with SVALTYPE ιss ξs) = Some ιss.
  Proof.
    revert ξs.
    induction ιss as [|ιs ιss IH]; intros [|ξ ξs] Hlen; try done.
    cbn in *.
    by erewrite IH by lia.
  Qed.

  Lemma mapM_skind_size_zip (ns : list nat) ξs :
    length ns = length ξs ->
    mapM skind_size (zip_with SMEMTYPE ns ξs) = Some ns.
  Proof.
    revert ξs.
    induction ns as [|n ns IH]; intros [|ξ ξs] Hlen; try done.
    cbn in *.
    by erewrite IH by lia.
  Qed.

  Lemma map_skind_ref_flag_zip_val (ιss : list (list atomic_rep)) ξs :
    length ιss = length ξs ->
    map skind_ref_flag (zip_with SVALTYPE ιss ξs) = ξs.
  Proof.
    revert ξs.
    induction ιss as [|ιs ιss IH]; intros [|ξ ξs] Hlen; try done.
    cbn in *. f_equal. apply IH; lia.
  Qed.

  Lemma map_skind_ref_flag_zip_mem (ns : list nat) ξs :
    length ns = length ξs ->
    map skind_ref_flag (zip_with SMEMTYPE ns ξs) = ξs.
  Proof.
    revert ξs.
    induction ns as [|n ns IH]; intros [|ξ ξs] Hlen; try done.
    cbn in *. f_equal. apply IH; lia.
  Qed.

  Lemma forall3_mapM_type_skind_val (se : semantic_env (Σ:=Σ)) τs ρs ξs :
    Forall3 (fun τ ρ ξ =>
               forall sκ, eval_kind se (VALTYPE ρ ξ) = Some sκ -> type_skind_go se τ = Some sκ)
      τs ρs ξs ->
    forall ιss, mapM (eval_rep se) ρs = Some ιss ->
    mapM (type_skind_go se) τs = Some (zip_with SVALTYPE ιss ξs).
  Proof.
    induction 1 as [| τ ρ ξ τs ρs ξs Hhd _ IH]; intros ιss Hmap.
    - cbn in Hmap. inversion Hmap; subst. done.
    - cbn in Hmap.
      apply bind_Some in Hmap as (ι & Hι & Hmap).
      apply bind_Some in Hmap as (ιss' & Hιss' & Heq).
      inversion Heq; subst; clear Heq.
      cbn.
      erewrite Hhd; last (cbn; by rewrite Hι).
      by erewrite IH.
  Qed.

  Lemma forall3_mapM_type_skind_mem (se : semantic_env (Σ:=Σ)) τs σs ξs :
    Forall3 (fun τ σ ξ =>
               forall sκ, eval_kind se (MEMTYPE σ ξ) = Some sκ -> type_skind_go se τ = Some sκ)
      τs σs ξs ->
    forall ns, mapM (eval_size se) σs = Some ns ->
    mapM (type_skind_go se) τs = Some (zip_with SMEMTYPE ns ξs).
  Proof.
    induction 1 as [| τ σ ξ τs σs ξs Hhd _ IH]; intros ns Hmap.
    - cbn in Hmap. inversion Hmap; subst. done.
    - cbn in Hmap.
      apply bind_Some in Hmap as (n & Hn & Hmap).
      apply bind_Some in Hmap as (ns' & Hns' & Heq).
      inversion Heq; subst; clear Heq.
      cbn.
      erewrite Hhd; last (cbn; by rewrite Hn).
      by erewrite IH.
  Qed.

  Lemma type_skind_has_kind_Some_aux τ :
    forall F κ, has_kind F τ κ ->
    kind_ok F.(fc_kind_ctx) κ /\
    (forall (se : semantic_env (Σ:=Σ)) sκ, sem_env_interp F se -> eval_kind se κ = Some sκ -> type_skind_go se τ = Some sκ).
  Proof using.
    induction τ using type_ind with (Pi := fun _ => True) (P0 := fun _ => True).
    - (* VarT *)
      intros F κ Hκ.
      inversion Hκ; subst.
      match goal with
      | Hlook : fc_type_vars F !! _ = Some κ, Hok : kind_ok _ κ |- _ =>
          rename Hlook into Hlook_; rename Hok into Hok_
      end.
      split; [exact Hok_|].
      intros se sκ [_ Htys] Hsκ.
      edestruct (Forall2_lookup_l _ _ _ _ _ Htys Hlook_) as (y & Hy & Hprop).
      destruct y as [sκ' [sκT' T']].
      destruct Hprop as (Hev & _ & _).
      rewrite Hsκ in Hev.
      inversion Hev; subst.
      cbn. rewrite Hy. done.
    - (* I31T *)
      intros F κ Hκ.
      inversion Hκ; subst.
      split; [by repeat constructor|].
      intros se sκ Hse Hsκ. cbn in Hsκ |- *. exact Hsκ.
    - (* NumT *)
      intros F κ Hκ.
      inversion Hκ; subst;
        (split; [by repeat constructor|]);
        intros se sκ Hse Hsκ; cbn in Hsκ |- *; exact Hsκ.
    - (* SumT *)
      intros F κ Hκ.
      match goal with IH : Forall _ τs |- _ => rename IH into IHτs end.
      inversion Hκ; subst.
      match goal with
      | H1 : Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) _ _ _ |- _ => rename H1 into HF3
      end.
      pose proof (forall3_and_l _ _ _ _ _ IHτs HF3) as Hcomb.
      eapply Forall3_impl in Hcomb; last (intros ??? [HP Hhk]; exact (HP F (VALTYPE _ _) Hhk)).
      pose proof (forall3_forall_m _ (rep_ok F.(fc_kind_ctx)) _ _ _ Hcomb
                    (fun τ' ρ' ξ' p => kind_ok_rep_ok _ _ _ (proj1 p))) as Hrepoks.
      pose proof (Forall3_impl _ _ _ _ _ Hcomb (fun τ' ρ' ξ' p => proj2 p)) as Hsems.
      split; [by repeat constructor|].
      intros se sκ Hse Hsκ.
      cbn in Hsκ.
      apply bind_Some in Hsκ as (ιs & Hιs & Heq).
      inversion Heq; subst; clear Heq.
      cbn in Hιs.
      apply fmap_Some in Hιs as (ιss & Hιss & Hιseq).
      pose proof (Forall3_length_lm _ _ _ _ HF3) as Hlm.
      pose proof (Forall3_length_lr _ _ _ _ HF3) as Hlr.
      pose proof (length_mapM _ _ _ Hιss) as Hlen_ιss.
      pose proof (Forall3_impl _ _ _ _ _ Hsems (fun tau' rho' xi' p sk Heval => p se sk Hse Heval)) as Hsems_se.
      pose proof (forall3_mapM_type_skind_val se _ _ _ Hsems_se _ Hιss) as Hmm.
      cbn [type_skind_go].
      rewrite Hmm.
      cbn.
      erewrite mapM_skind_rep_zip by lia.
      erewrite map_skind_ref_flag_zip_val by lia.
      rewrite Hιseq.
      done.
    - (* VariantT *)
      intros F κ Hκ.
      match goal with IH : Forall _ τs |- _ => rename IH into IHτs end.
      inversion Hκ; subst.
      match goal with
      | H1 : Forall3 (fun τ σ ξ => has_kind F τ (MEMTYPE σ ξ)) _ _ _ |- _ => rename H1 into HF3
      end.
      pose proof (forall3_and_l _ _ _ _ _ IHτs HF3) as Hcomb.
      eapply Forall3_impl in Hcomb; last (intros ??? [HP Hhk]; exact (HP F (MEMTYPE _ _) Hhk)).
      pose proof (forall3_forall_m _ (size_ok F.(fc_kind_ctx)) _ _ _ Hcomb
                    (fun τ' σ' ξ' p => kind_ok_size_ok _ _ _ (proj1 p))) as Hsizeoks.
      pose proof (Forall3_impl _ _ _ _ _ Hcomb (fun τ' σ' ξ' p => proj2 p)) as Hsems.
      split; [by repeat constructor|].
      intros se sκ Hse Hsκ.
      cbn in Hsκ.
      apply bind_Some in Hsκ as (n & Hn & Heq).
      inversion Heq; subst; clear Heq.
      cbn in Hn.
      apply bind_Some in Hn as (ns & Hns & Hneq).
      inversion Hneq; subst; clear Hneq.
      pose proof (Forall3_length_lm _ _ _ _ HF3) as Hlm.
      pose proof (Forall3_length_lr _ _ _ _ HF3) as Hlr.
      pose proof (length_mapM _ _ _ Hns) as Hlen_ns.
      pose proof (Forall3_impl _ _ _ _ _ Hsems (fun tau' sigma' xi' p sk Heval => p se sk Hse Heval)) as Hsems_se.
      pose proof (forall3_mapM_type_skind_mem se _ _ _ Hsems_se _ Hns) as Hmm.
      cbn [type_skind_go].
      rewrite Hmm.
      cbn.
      erewrite mapM_skind_size_zip by lia.
      erewrite map_skind_ref_flag_zip_mem by lia.
      done.
    - (* ProdT *)
      intros F κ Hκ.
      match goal with IH : Forall _ τs |- _ => rename IH into IHτs end.
      inversion Hκ; subst.
      match goal with
      | H1 : Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) _ _ _ |- _ => rename H1 into HF3
      end.
      pose proof (forall3_and_l _ _ _ _ _ IHτs HF3) as Hcomb.
      eapply Forall3_impl in Hcomb; last (intros ??? [HP Hhk]; exact (HP F (VALTYPE _ _) Hhk)).
      pose proof (forall3_forall_m _ (rep_ok F.(fc_kind_ctx)) _ _ _ Hcomb
                    (fun τ' ρ' ξ' p => kind_ok_rep_ok _ _ _ (proj1 p))) as Hrepoks.
      pose proof (Forall3_impl _ _ _ _ _ Hcomb (fun τ' ρ' ξ' p => proj2 p)) as Hsems.
      split; [by repeat constructor|].
      intros se sκ Hse Hsκ.
      cbn in Hsκ.
      apply bind_Some in Hsκ as (ιs & Hιs & Heq).
      inversion Heq; subst; clear Heq.
      cbn in Hιs.
      apply fmap_Some in Hιs as (ιss & Hιss & Hιseq).
      pose proof (Forall3_length_lm _ _ _ _ HF3) as Hlm.
      pose proof (Forall3_length_lr _ _ _ _ HF3) as Hlr.
      pose proof (length_mapM _ _ _ Hιss) as Hlen_ιss.
      pose proof (Forall3_impl _ _ _ _ _ Hsems (fun tau' rho' xi' p sk Heval => p se sk Hse Heval)) as Hsems_se.
      pose proof (forall3_mapM_type_skind_val se _ _ _ Hsems_se _ Hιss) as Hmm.
      cbn [type_skind_go].
      rewrite Hmm.
      cbn.
      erewrite mapM_skind_rep_zip by lia.
      erewrite map_skind_ref_flag_zip_val by lia.
      rewrite Hιseq.
      done.
    - (* StructT *)
      intros F κ Hκ.
      match goal with IH : Forall _ τs |- _ => rename IH into IHτs end.
      inversion Hκ; subst.
      match goal with
      | H1 : Forall3 (fun τ σ ξ => has_kind F τ (MEMTYPE σ ξ)) _ _ _ |- _ => rename H1 into HF3
      end.
      pose proof (forall3_and_l _ _ _ _ _ IHτs HF3) as Hcomb.
      eapply Forall3_impl in Hcomb; last (intros ??? [HP Hhk]; exact (HP F (MEMTYPE _ _) Hhk)).
      pose proof (forall3_forall_m _ (size_ok F.(fc_kind_ctx)) _ _ _ Hcomb
                    (fun τ' σ' ξ' p => kind_ok_size_ok _ _ _ (proj1 p))) as Hsizeoks.
      pose proof (Forall3_impl _ _ _ _ _ Hcomb (fun τ' σ' ξ' p => proj2 p)) as Hsems.
      split; [by repeat constructor|].
      intros se sκ Hse Hsκ.
      cbn in Hsκ.
      apply bind_Some in Hsκ as (n & Hn & Heq).
      inversion Heq; subst; clear Heq.
      cbn in Hn.
      apply fmap_Some in Hn as (ns & Hns & Hneq).
      pose proof (Forall3_length_lm _ _ _ _ HF3) as Hlm.
      pose proof (Forall3_length_lr _ _ _ _ HF3) as Hlr.
      pose proof (length_mapM _ _ _ Hns) as Hlen_ns.
      pose proof (Forall3_impl _ _ _ _ _ Hsems (fun tau' sigma' xi' p sk Heval => p se sk Hse Heval)) as Hsems_se.
      pose proof (forall3_mapM_type_skind_mem se _ _ _ Hsems_se _ Hns) as Hmm.
      cbn [type_skind_go].
      rewrite Hmm.
      cbn.
      erewrite mapM_skind_size_zip by lia.
      erewrite map_skind_ref_flag_zip_mem by lia.
      rewrite Hneq.
      done.
    - (* RefT *)
      intros F κ Hκ.
      match goal with IH : (forall F κ, has_kind F ?t κ -> _) |- _ => rename IH into IHt end.
      inversion Hκ; subst;
        match goal with
        | Hchild : has_kind F _ (MEMTYPE ?σ ?ξ) |- _ =>
            split; [by repeat constructor|];
            intros se sκ Hse Hsκ;
            cbn in Hsκ; inversion Hsκ; subst;
            destruct (IHt F (MEMTYPE σ ξ) Hchild) as (Hkindok_child & Hsem_child);
            pose proof (kind_ok_size_ok _ _ _ Hkindok_child) as Hsizeok;
            destruct (eval_size_ok_Some F se σ Hse Hsizeok) as [n Hn];
            specialize (Hsem_child se (SMEMTYPE n ξ) Hse ltac:(cbn; by rewrite Hn));
            cbn [type_skind_go]; rewrite Hsem_child; cbn; done
        end.
    - (* CodeRefT *)
      intros F κ Hκ.
      inversion Hκ; subst.
      split; [by repeat constructor|].
      intros se sκ Hse Hsκ. cbn in Hsκ |- *. exact Hsκ.
    - (* SerT *)
      intros F κ Hκ.
      match goal with IH : (forall F κ, has_kind F ?t κ -> _) |- _ => rename IH into IHt end.
      inversion Hκ; subst.
      match goal with
      | Hc : has_kind F _ (VALTYPE ?ρ ?ξ) |- _ => rename Hc into Hchild
      end.
      destruct (IHt F (VALTYPE _ _) Hchild) as (Hkindok_child & Hsem_child).
      split; [by repeat constructor; eapply kind_ok_rep_ok; eauto|].
      intros se sκ Hse Hsκ.
      cbn in Hsκ.
      apply bind_Some in Hsκ as (n & Hn & Heq).
      inversion Heq; subst; clear Heq.
      cbn in Hn.
      apply fmap_Some in Hn as (ιs & Hιs & Hneq).
      specialize (Hsem_child se (SVALTYPE ιs _) Hse ltac:(cbn; by rewrite Hιs)).
      cbn [type_skind_go]. rewrite Hsem_child. cbn.
      by rewrite Hneq.
    - (* PlugT *)
      intros F κ Hκ.
      inversion Hκ; subst.
      match goal with H : rep_ok _ _ |- _ => rename H into Hrepok end.
      split; [by repeat constructor|].
      intros se sκ Hse Hsκ. cbn in Hsκ |- *. exact Hsκ.
    - (* SpanT *)
      intros F κ Hκ.
      inversion Hκ; subst.
      match goal with H : size_ok _ _ |- _ => rename H into Hsizeok end.
      split; [by repeat constructor|].
      intros se sκ Hse Hsκ. cbn in Hsκ |- *. exact Hsκ.
    - (* RecT *)
      intros F κnew Hκ.
      match goal with IH : (forall F κ, has_kind F ?t κ -> _) |- _ => rename IH into IHt end.
      inversion Hκ; subst.
      match goal with
      | Hchild : has_kind (F <| fc_type_vars ::= cons ?κ0 |>) _ ?κ0 |- _ =>
          destruct (IHt _ _ Hchild) as (Hkindok_child & _)
      end.
      split; [exact Hkindok_child|].
      intros se sκ Hse Hsκ. cbn in Hsκ |- *. exact Hsκ.
    - (* ExistsMemT *)
      intros F κnew Hκ.
      inversion Hκ; subst.
      match goal with H : kind_ok _ ?κ0 |- _ => rename H into Hkindok end.
      split; [exact Hkindok|].
      intros se sκ Hse Hsκ. cbn in Hsκ |- *. exact Hsκ.
    - (* ExistsRepT *)
      intros F κnew Hκ.
      inversion Hκ; subst.
      match goal with H : kind_ok _ ?κ0 |- _ => rename H into Hkindok end.
      split; [exact Hkindok|].
      intros se sκ Hse Hsκ. cbn in Hsκ |- *. exact Hsκ.
    - (* ExistsSizeT *)
      intros F κnew Hκ.
      inversion Hκ; subst.
      match goal with H : kind_ok _ ?κ0 |- _ => rename H into Hkindok end.
      split; [exact Hkindok|].
      intros se sκ Hse Hsκ. cbn in Hsκ |- *. exact Hsκ.
    - (* ExistsTypeT *)
      intros F κnew Hκ.
      inversion Hκ; subst.
      match goal with H : kind_ok _ κnew |- _ => rename H into Hkindok end.
      split; [exact Hkindok|].
      intros se sκ Hse Hsκ. cbn in Hsκ |- *. exact Hsκ.
    - done.
    - done.
    - done.
    - done.
    - done.
    - done.
  Qed.

  Lemma type_skind_has_kind_Some F se τ κ sκ :
    has_kind F τ κ ->
    sem_env_interp F se ->
    eval_kind se κ = Some sκ ->
    type_skind (Σ:=Σ) se τ = Some sκ.
  Proof using Σ.
    intros H Hse Hsκ.
    cbn.
    eapply (proj2 (type_skind_has_kind_Some_aux τ F κ H)); eauto.
  Qed.

  Lemma type_skind_has_kind_agree F se τ κ sκ sκ' :
    has_kind F τ κ ->
    sem_env_interp F se ->
    eval_kind se κ = Some sκ ->
    type_skind (Σ:=Σ) se τ = Some sκ' ->
    sκ = sκ'.
  Proof using Σ.
    intros Hκ Hse Hsκ Hsκ'.
    pose proof (type_skind_has_kind_Some F se τ κ sκ Hκ Hse Hsκ) as Heq.
    rewrite Heq in Hsκ'.
    by inversion Hsκ'.
  Qed.

  (* [type_kind]/[type_ok] analogues of [forall3_mapM_type_kind_val]/[_mem]:
     from the *function-equation* facts that [type_kind]'s own [mapM]-based
     recursive equations produce (rather than an already-packaged [Forall3],
     which is all [has_kind]'s aggregate constructors give for free), rebuild
     the pointwise [Forall3] relating each child type to its representation
     (resp. size) and ref-flag. *)
  Lemma type_kind_mapM_forall3_val κs τs :
    forall κs' ρs,
    mapM (type_kind κs) τs = Some κs' ->
    mapM kind_rep κs' = Some ρs ->
    Forall3 (fun τ ρ ξ => type_kind κs τ = Some (VALTYPE ρ ξ)) τs ρs (map kind_ref_flag κs').
  Proof.
    induction τs as [| τ τs IH]; intros κs' ρs Hmapk Hmapr.
    - cbn in Hmapk. apply Some_inj in Hmapk. subst κs'.
      cbn in Hmapr. apply Some_inj in Hmapr. subst ρs.
      constructor.
    - cbn in Hmapk.
      apply bind_Some in Hmapk as (κ0 & Htk & Hmapk).
      apply bind_Some in Hmapk as (κs0 & Hmapk & Heq).
      apply Some_inj in Heq. subst κs'.
      cbn in Hmapr.
      apply bind_Some in Hmapr as (ρ0 & Hkr & Hmapr).
      apply bind_Some in Hmapr as (ρs0 & Hmapr & Heq2).
      apply Some_inj in Heq2. subst ρs.
      destruct κ0 as [ρ1 ξ1 | ]; cbn in Hkr; [| discriminate].
      apply Some_inj in Hkr. subst ρ0.
      cbn.
      constructor; [exact Htk | exact (IH _ _ Hmapk Hmapr)].
  Qed.

  Lemma type_kind_mapM_forall3_mem κs τs :
    forall κs' σs,
    mapM (type_kind κs) τs = Some κs' ->
    mapM kind_size κs' = Some σs ->
    Forall3 (fun τ σ ξ => type_kind κs τ = Some (MEMTYPE σ ξ)) τs σs (map kind_ref_flag κs').
  Proof.
    induction τs as [| τ τs IH]; intros κs' σs Hmapk Hmaps.
    - cbn in Hmapk. apply Some_inj in Hmapk. subst κs'.
      cbn in Hmaps. apply Some_inj in Hmaps. subst σs.
      constructor.
    - cbn in Hmapk.
      apply bind_Some in Hmapk as (κ0 & Htk & Hmapk).
      apply bind_Some in Hmapk as (κs0 & Hmapk & Heq).
      apply Some_inj in Heq. subst κs'.
      cbn in Hmaps.
      apply bind_Some in Hmaps as (σ0 & Hks & Hmaps).
      apply bind_Some in Hmaps as (σs0 & Hmaps & Heq2).
      apply Some_inj in Heq2. subst σs.
      destruct κ0 as [| σ1 ξ1]; cbn in Hks; [discriminate |].
      apply Some_inj in Hks. subst σ0.
      cbn.
      constructor; [exact Htk | exact (IH _ _ Hmapk Hmaps)].
  Qed.

  (* [type_kind]/[type_ok] analogue of [type_skind_has_kind_Some_aux]: unlike
     [has_kind], [type_kind] is a pure recomputation with no built-in
     validity side-conditions (see [layout.v]), so an extra [type_ok]
     hypothesis (giving exactly the [rep_ok]/[size_ok] bounds facts that
     [has_kind]'s [KPlug]/[KSpan] rules bake in) is needed for this to hold. *)
  Lemma type_kind_type_ok_Some_aux τ :
    forall F κ, type_ok F τ -> type_kind F.(fc_type_vars) τ = Some κ ->
    kind_ok F.(fc_kind_ctx) κ /\
    (forall (se : semantic_env (Σ:=Σ)) sκ, sem_env_interp F se -> eval_kind se κ = Some sκ -> type_skind_go se τ = Some sκ).
  Proof using.
    induction τ using type_ind with (Pi := fun _ => True) (P0 := fun _ => True).
    - (* VarT *)
      intros F κ Hok Htk.
      inversion Hok; subst; clear Hok.
      match goal with
      | Hlook : fc_type_vars F !! _ = Some ?κ0, Hkok : kind_ok _ ?κ0 |- _ =>
          cbn in Htk; rewrite Hlook in Htk; apply Some_inj in Htk; subst κ0
      end.
      split; [assumption|].
      intros se sκ [_ Htys] Hsκ.
      match goal with
      | Hlook : fc_type_vars F !! _ = Some κ |- _ =>
          edestruct (Forall2_lookup_l _ _ _ _ _ Htys Hlook) as (y & Hy & Hprop)
      end.
      destruct y as [sκ' [sκT' T']].
      destruct Hprop as (Hev & _ & _).
      rewrite Hsκ in Hev.
      inversion Hev; subst.
      cbn. rewrite Hy. done.
    - (* I31T *)
      intros F κ Hok Htk.
      cbn in Htk. apply Some_inj in Htk. subst κ.
      split; [by repeat constructor|].
      intros se sκ Hse Hsκ. cbn in Hsκ |- *. exact Hsκ.
    - (* NumT *)
      intros F κ Hok Htk.
      cbn in Htk. apply Some_inj in Htk. subst κ.
      destruct nt as [[]|[]]; cbn;
        (split; [by repeat constructor|]);
        intros se sκ Hse Hsκ; cbn in Hsκ |- *; exact Hsκ.
    - (* SumT *)
      intros F κ Hok Htk.
      match goal with IH : Forall _ τs |- _ => rename IH into IHτs end.
      inversion Hok; subst; clear Hok.
      match goal with H : Forall (type_ok F) τs |- _ => rename H into Htoks end.
      cbn in Htk.
      apply bind_Some in Htk as (κs' & Hmapk & Htk).
      apply bind_Some in Htk as (ρs & Hmapr & Htk).
      apply Some_inj in Htk. subst κ.
      pose proof (type_kind_mapM_forall3_val _ _ _ _ Hmapk Hmapr) as HF3.
      pose proof (forall3_and_l _ _ _ _ _ Htoks HF3) as Hcomb0.
      pose proof (forall3_and_l _ _ _ _ _ IHτs Hcomb0) as Hcomb1.
      eapply Forall3_impl in Hcomb1;
        last (intros τ' ρ' ξ' (HIH & Htok' & Htk'); exact (HIH F (VALTYPE ρ' ξ') Htok' Htk')).
      pose proof (forall3_forall_m _ (rep_ok F.(fc_kind_ctx)) _ _ _ Hcomb1
                    (fun τ' ρ' ξ' p => kind_ok_rep_ok _ _ _ (proj1 p))) as Hrepoks.
      pose proof (Forall3_impl _ _ _ _ _ Hcomb1 (fun τ' ρ' ξ' p => proj2 p)) as Hsems.
      split; [by repeat constructor|].
      intros se sκ Hse Hsκ.
      cbn in Hsκ.
      apply bind_Some in Hsκ as (ιs & Hιs & Heq).
      apply Some_inj in Heq. subst sκ.
      cbn in Hιs.
      apply fmap_Some in Hιs as (ιss & Hιss & Hιseq).
      pose proof (Forall3_length_lm _ _ _ _ HF3) as Hlm.
      pose proof (Forall3_length_lr _ _ _ _ HF3) as Hlr.
      pose proof (length_mapM _ _ _ Hιss) as Hlen_ιss.
      pose proof (Forall3_impl _ _ _ _ _ Hsems (fun tau' rho' xi' p sk Heval => p se sk Hse Heval)) as Hsems_se.
      pose proof (forall3_mapM_type_skind_val se _ _ _ Hsems_se _ Hιss) as Hmm.
      cbn [type_skind_go].
      rewrite Hmm.
      cbn.
      erewrite mapM_skind_rep_zip by lia.
      erewrite map_skind_ref_flag_zip_val by lia.
      rewrite Hιseq.
      done.
    - (* VariantT *)
      intros F κ Hok Htk.
      match goal with IH : Forall _ τs |- _ => rename IH into IHτs end.
      inversion Hok; subst; clear Hok.
      match goal with H : Forall (type_ok F) τs |- _ => rename H into Htoks end.
      cbn in Htk.
      apply bind_Some in Htk as (κs' & Hmapk & Htk).
      apply bind_Some in Htk as (σs & Hmaps & Htk).
      apply Some_inj in Htk. subst κ.
      pose proof (type_kind_mapM_forall3_mem _ _ _ _ Hmapk Hmaps) as HF3.
      pose proof (forall3_and_l _ _ _ _ _ Htoks HF3) as Hcomb0.
      pose proof (forall3_and_l _ _ _ _ _ IHτs Hcomb0) as Hcomb1.
      eapply Forall3_impl in Hcomb1;
        last (intros τ' σ' ξ' (HIH & Htok' & Htk'); exact (HIH F (MEMTYPE σ' ξ') Htok' Htk')).
      pose proof (forall3_forall_m _ (size_ok F.(fc_kind_ctx)) _ _ _ Hcomb1
                    (fun τ' σ' ξ' p => kind_ok_size_ok _ _ _ (proj1 p))) as Hsizeoks.
      pose proof (Forall3_impl _ _ _ _ _ Hcomb1 (fun τ' σ' ξ' p => proj2 p)) as Hsems.
      split; [by repeat constructor|].
      intros se sκ Hse Hsκ.
      cbn in Hsκ.
      apply bind_Some in Hsκ as (n & Hn & Heq).
      apply Some_inj in Heq. subst sκ.
      cbn in Hn.
      apply bind_Some in Hn as (ns & Hns & Hneq).
      apply Some_inj in Hneq. subst n.
      pose proof (Forall3_length_lm _ _ _ _ HF3) as Hlm.
      pose proof (Forall3_length_lr _ _ _ _ HF3) as Hlr.
      pose proof (length_mapM _ _ _ Hns) as Hlen_ns.
      pose proof (Forall3_impl _ _ _ _ _ Hsems (fun tau' sigma' xi' p sk Heval => p se sk Hse Heval)) as Hsems_se.
      pose proof (forall3_mapM_type_skind_mem se _ _ _ Hsems_se _ Hns) as Hmm.
      cbn [type_skind_go].
      rewrite Hmm.
      cbn.
      erewrite mapM_skind_size_zip by lia.
      erewrite map_skind_ref_flag_zip_mem by lia.
      done.
    - (* ProdT *)
      intros F κ Hok Htk.
      match goal with IH : Forall _ τs |- _ => rename IH into IHτs end.
      inversion Hok; subst; clear Hok.
      match goal with H : Forall (type_ok F) τs |- _ => rename H into Htoks end.
      cbn in Htk.
      apply bind_Some in Htk as (κs' & Hmapk & Htk).
      apply bind_Some in Htk as (ρs & Hmapr & Htk).
      apply Some_inj in Htk. subst κ.
      pose proof (type_kind_mapM_forall3_val _ _ _ _ Hmapk Hmapr) as HF3.
      pose proof (forall3_and_l _ _ _ _ _ Htoks HF3) as Hcomb0.
      pose proof (forall3_and_l _ _ _ _ _ IHτs Hcomb0) as Hcomb1.
      eapply Forall3_impl in Hcomb1;
        last (intros τ' ρ' ξ' (HIH & Htok' & Htk'); exact (HIH F (VALTYPE ρ' ξ') Htok' Htk')).
      pose proof (forall3_forall_m _ (rep_ok F.(fc_kind_ctx)) _ _ _ Hcomb1
                    (fun τ' ρ' ξ' p => kind_ok_rep_ok _ _ _ (proj1 p))) as Hrepoks.
      pose proof (Forall3_impl _ _ _ _ _ Hcomb1 (fun τ' ρ' ξ' p => proj2 p)) as Hsems.
      split; [by repeat constructor|].
      intros se sκ Hse Hsκ.
      cbn in Hsκ.
      apply bind_Some in Hsκ as (ιs & Hιs & Heq).
      apply Some_inj in Heq. subst sκ.
      cbn in Hιs.
      apply fmap_Some in Hιs as (ιss & Hιss & Hιseq).
      pose proof (Forall3_length_lm _ _ _ _ HF3) as Hlm.
      pose proof (Forall3_length_lr _ _ _ _ HF3) as Hlr.
      pose proof (length_mapM _ _ _ Hιss) as Hlen_ιss.
      pose proof (Forall3_impl _ _ _ _ _ Hsems (fun tau' rho' xi' p sk Heval => p se sk Hse Heval)) as Hsems_se.
      pose proof (forall3_mapM_type_skind_val se _ _ _ Hsems_se _ Hιss) as Hmm.
      cbn [type_skind_go].
      rewrite Hmm.
      cbn.
      erewrite mapM_skind_rep_zip by lia.
      erewrite map_skind_ref_flag_zip_val by lia.
      rewrite Hιseq.
      done.
    - (* StructT *)
      intros F κ Hok Htk.
      match goal with IH : Forall _ τs |- _ => rename IH into IHτs end.
      inversion Hok; subst; clear Hok.
      match goal with H : Forall (type_ok F) τs |- _ => rename H into Htoks end.
      cbn in Htk.
      apply bind_Some in Htk as (κs' & Hmapk & Htk).
      apply bind_Some in Htk as (σs & Hmaps & Htk).
      apply Some_inj in Htk. subst κ.
      pose proof (type_kind_mapM_forall3_mem _ _ _ _ Hmapk Hmaps) as HF3.
      pose proof (forall3_and_l _ _ _ _ _ Htoks HF3) as Hcomb0.
      pose proof (forall3_and_l _ _ _ _ _ IHτs Hcomb0) as Hcomb1.
      eapply Forall3_impl in Hcomb1;
        last (intros τ' σ' ξ' (HIH & Htok' & Htk'); exact (HIH F (MEMTYPE σ' ξ') Htok' Htk')).
      pose proof (forall3_forall_m _ (size_ok F.(fc_kind_ctx)) _ _ _ Hcomb1
                    (fun τ' σ' ξ' p => kind_ok_size_ok _ _ _ (proj1 p))) as Hsizeoks.
      pose proof (Forall3_impl _ _ _ _ _ Hcomb1 (fun τ' σ' ξ' p => proj2 p)) as Hsems.
      split; [by repeat constructor|].
      intros se sκ Hse Hsκ.
      cbn in Hsκ.
      apply bind_Some in Hsκ as (n & Hn & Heq).
      apply Some_inj in Heq. subst sκ.
      cbn in Hn.
      apply fmap_Some in Hn as (ns & Hns & Hneq).
      pose proof (Forall3_length_lm _ _ _ _ HF3) as Hlm.
      pose proof (Forall3_length_lr _ _ _ _ HF3) as Hlr.
      pose proof (length_mapM _ _ _ Hns) as Hlen_ns.
      pose proof (Forall3_impl _ _ _ _ _ Hsems (fun tau' sigma' xi' p sk Heval => p se sk Hse Heval)) as Hsems_se.
      pose proof (forall3_mapM_type_skind_mem se _ _ _ Hsems_se _ Hns) as Hmm.
      cbn [type_skind_go].
      rewrite Hmm.
      cbn.
      erewrite mapM_skind_size_zip by lia.
      erewrite map_skind_ref_flag_zip_mem by lia.
      rewrite Hneq.
      done.
    - (* RefT *)
      intros F κ Hok Htk.
      match goal with IH : (forall F κ, type_ok F ?t -> type_kind _ ?t = Some κ -> _) |- _ => rename IH into IHt end.
      inversion Hok; subst; clear Hok.
      cbn in Htk.
      apply bind_Some in Htk as (κ0 & Htkc & Hmatch).
      destruct κ0 as [ρ0 ξ0 | σ0 ξ0]; [discriminate Hmatch |].
      apply Some_inj in Hmatch. subst κ.
      match goal with
      | Htokc : type_ok F ?t |- _ => destruct (IHt F (MEMTYPE σ0 ξ0) Htokc Htkc) as (Hkindok_child & Hsem_child)
      end.
      split; [by repeat constructor|].
      intros se sκ Hse Hsκ.
      cbn in Hsκ.
      apply Some_inj in Hsκ. subst sκ.
      pose proof (kind_ok_size_ok _ _ _ Hkindok_child) as Hsizeok.
      destruct (eval_size_ok_Some F se σ0 Hse Hsizeok) as [n Hn].
      specialize (Hsem_child se (SMEMTYPE n ξ0) Hse ltac:(cbn; by rewrite Hn)).
      cbn [type_skind_go]; rewrite Hsem_child; cbn; done.
    - (* CodeRefT *)
      intros F κ Hok Htk.
      cbn in Htk. apply Some_inj in Htk. subst κ.
      split; [by repeat constructor|].
      intros se sκ Hse Hsκ. cbn in Hsκ |- *. exact Hsκ.
    - (* SerT *)
      intros F κ Hok Htk.
      match goal with IH : (forall F κ, type_ok F ?t -> type_kind _ ?t = Some κ -> _) |- _ => rename IH into IHt end.
      inversion Hok; subst; clear Hok.
      cbn in Htk.
      apply bind_Some in Htk as (κ0 & Htkc & Hmatch).
      destruct κ0 as [ρ0 ξ0 | σ0 ξ0]; [| discriminate Hmatch].
      apply Some_inj in Hmatch. subst κ.
      match goal with
      | Htokc : type_ok F ?t |- _ => destruct (IHt F (VALTYPE ρ0 ξ0) Htokc Htkc) as (Hkindok_child & Hsem_child)
      end.
      split; [by repeat constructor; eapply kind_ok_rep_ok; eauto|].
      intros se sκ Hse Hsκ.
      cbn in Hsκ.
      apply bind_Some in Hsκ as (n & Hn & Heq).
      apply Some_inj in Heq. subst sκ.
      cbn in Hn.
      apply fmap_Some in Hn as (ιs & Hιs & Hneq).
      specialize (Hsem_child se (SVALTYPE ιs ξ0) Hse ltac:(cbn; by rewrite Hιs)).
      cbn [type_skind_go]. rewrite Hsem_child. cbn.
      by rewrite Hneq.
    - (* PlugT *)
      intros F κ Hok Htk.
      inversion Hok; subst; clear Hok.
      match goal with H : rep_ok _ _ |- _ => rename H into Hrepok end.
      cbn in Htk. apply Some_inj in Htk. subst κ.
      split; [by repeat constructor|].
      intros se sκ Hse Hsκ. cbn in Hsκ |- *. exact Hsκ.
    - (* SpanT *)
      intros F κ Hok Htk.
      inversion Hok; subst; clear Hok.
      match goal with H : size_ok _ _ |- _ => rename H into Hsizeok end.
      cbn in Htk. apply Some_inj in Htk. subst κ.
      split; [by repeat constructor|].
      intros se sκ Hse Hsκ. cbn in Hsκ |- *. exact Hsκ.
    - (* RecT *)
      intros F κnew Hok Htk.
      inversion Hok; subst; clear Hok.
      cbn in Htk. apply Some_inj in Htk. subst κnew.
      split.
      + match goal with H : kind_ok _ ?k |- kind_ok _ ?k => exact H end.
      + intros se sκ Hse Hsκ. cbn in Hsκ |- *. exact Hsκ.
    - (* ExistsMemT *)
      intros F κnew Hok Htk.
      inversion Hok; subst; clear Hok.
      cbn in Htk. apply Some_inj in Htk. subst κnew.
      split.
      + match goal with H : kind_ok _ ?k |- kind_ok _ ?k => exact H end.
      + intros se sκ Hse Hsκ. cbn in Hsκ |- *. exact Hsκ.
    - (* ExistsRepT *)
      intros F κnew Hok Htk.
      inversion Hok; subst; clear Hok.
      cbn in Htk. apply Some_inj in Htk. subst κnew.
      split.
      + match goal with H : kind_ok _ ?k |- kind_ok _ ?k => exact H end.
      + intros se sκ Hse Hsκ. cbn in Hsκ |- *. exact Hsκ.
    - (* ExistsSizeT *)
      intros F κnew Hok Htk.
      inversion Hok; subst; clear Hok.
      cbn in Htk. apply Some_inj in Htk. subst κnew.
      split.
      + match goal with H : kind_ok _ ?k |- kind_ok _ ?k => exact H end.
      + intros se sκ Hse Hsκ. cbn in Hsκ |- *. exact Hsκ.
    - (* ExistsTypeT *)
      intros F κnew Hok Htk.
      inversion Hok; subst; clear Hok.
      cbn in Htk. apply Some_inj in Htk. subst κnew.
      split.
      + match goal with H : kind_ok _ ?k |- kind_ok _ ?k => exact H end.
      + intros se sκ Hse Hsκ. cbn in Hsκ |- *. exact Hsκ.
    - done.
    - done.
    - done.
    - done.
    - done.
    - done.
  Qed.

  Lemma type_kind_type_ok_Some F se τ κ sκ :
    type_ok F τ ->
    type_kind F.(fc_type_vars) τ = Some κ ->
    sem_env_interp F se ->
    eval_kind se κ = Some sκ ->
    type_skind (Σ:=Σ) se τ = Some sκ.
  Proof using Σ.
    intros Htok Htk Hse Hsκ.
    cbn.
    eapply (proj2 (type_kind_type_ok_Some_aux τ F κ Htok Htk)); eauto.
  Qed.


  Lemma ref_flag_atoms_refine ξ ξ' sv :
    ref_flag_le ξ ξ' ->
    ref_flag_atoms_interp ξ sv ->
    ref_flag_atoms_interp ξ' sv.
  Proof.
    intros Hle Hos.
    destruct sv as [os | ]; cbn in Hos; last tauto.
    eapply Forall_impl; first done.
    intros o Ho.
    by destruct o; first (destruct ξ; destruct ξ'; destruct p).
  Qed.

  Lemma ref_flag_words_refine ξ ξ' sv :
    ref_flag_le ξ ξ' ->
    ref_flag_words_interp ξ sv ->
    ref_flag_words_interp ξ' sv.
  Proof.
    intros Hle Hws.
    destruct sv; cbn in Hws; first done.
    eapply Forall_impl; first done.
    intros w Hw.
    by destruct w; first (destruct ξ; destruct ξ'; destruct p).
  Qed.

  Lemma skind_as_type_refine sκ0 sκ :
    subskind_of sκ0 sκ ->
    forall sv, skind_has_svalue sκ0 sv -> skind_has_svalue sκ sv.
  Proof.
    intros Hsub sv Hskind.
    destruct sκ0 as [ιs ξ|n ξ].
    - inversion Hsub.
      subst.
      destruct Hskind as [Hareps Hrf].
      split; first done.
      by eapply ref_flag_atoms_refine.
    - inversion Hsub.
      subst.
      destruct Hskind as [Hssize Hrf].
      split; first done.
      by eapply ref_flag_words_refine.
  Qed.

  (* NOTE SAVE is this bad *)
  Lemma value_interp_var se t sκ sκ_T T :
    subskind_of sκ_T sκ ->
    lookup_type se t = Some (sκ, (sκ_T, T)) ->
    value_interp rti sr se (VarT t) ≡ (λne sv, ⌜skind_has_svalue sκ sv⌝ ∗ T sv)%I.
  Proof.
    unfold lookup_type.
    Opaque skind_has_svalue.
    cbn.
    intros Hsubs H sv.
    rewrite value_interp_eq; cbn.
    rewrite H.
    cbn.
    iSplit.
    - iIntros "(%sκ' & %Hsκ' & %Hskind & HT)".
      iFrame.
      iPureIntro.
      inversion Hsκ'.
      subst sκ'.
      done.
    - eauto.
  Qed.
  Transparent skind_has_svalue.

  Lemma prim_value_type_l ι v :
    has_prim ι v ->
    value_type_interp (translate_prim ι) v.
  Proof.
    intros H.
    by destruct ι; destruct v; try contradiction; eexists.
  Qed.

  Lemma prim_value_type_r ι v :
    value_type_interp (translate_prim ι) v ->
    has_prim ι v.
  Proof.
    intros H.
    destruct ι; destruct v; destruct H as [n H]; done.
  Qed.

  Lemma prim_value_type ι v :
    value_type_interp (translate_prim ι) v <->
    has_prim ι v.
  Proof.
    split.
    - apply prim_value_type_r.
    - apply prim_value_type_l.
  Qed.

  Lemma prims_result_type_l ιs vs :
    has_prims ιs vs ->
    result_type_interp (map translate_prim ιs) vs.
  Proof.
    revert vs.
    induction ιs; intros.
    - cbn.
      unfold result_type_interp.
      intros.
      inversion H.
      constructor.
    - inversion H; cbn; subst.
      constructor; cbn; eauto.
      + apply prim_value_type; eauto.
      + eapply IHιs; eauto.
  Qed.

  Lemma prims_result_type_r ιs vs :
    result_type_interp (map translate_prim ιs) vs ->
    has_prims ιs vs.
  Proof.
    revert vs.
    induction ιs; intros.
    - cbn.
      unfold result_type_interp.
      intros.
      inversion H.
      constructor.
    - inversion H; cbn; subst.
      constructor; cbn; eauto.
      + apply prim_value_type; eauto.
      + eapply IHιs; eauto.
  Qed.

  Lemma prims_result_type ιs vs :
    result_type_interp (map translate_prim ιs) vs <->
    has_prims ιs vs.
  Proof.
    split.
    - apply prims_result_type_r.
    - apply prims_result_type_l.
  Qed.

  Lemma value_interp_skind se τ sv :
    value_interp rti sr se τ sv -∗
    ⌜exists sκ, type_skind se τ = Some sκ /\ skind_has_svalue sκ sv⌝.
  Proof.
    iIntros "H".
    destruct τ;
      iDestruct "H" as "(% & % & % & _)";
      iPureIntro;
      by eexists.
  Qed.

  Lemma big_sepL2_value_interp_skind se τs oss :
    ([∗ list] τ;os ∈ τs;oss, value_interp rti sr se τ (SAtoms os)) -∗
    ⌜Forall2 (fun τ os => exists sκ, type_skind se τ = Some sκ /\ skind_has_svalue sκ (SAtoms os)) τs oss⌝.
  Proof.
    iIntros "H".
    rewrite Forall2_same_length_lookup.
    rewrite <- big_sepL2_pure.
    iDestruct (big_sepL2_length with "H") as "%Hlen".
    iApply (big_sepL2_wand with "[$]").
    iApply big_sepL2_intro; first done.
    iIntros "!> %k %τ %os %Hτ %Hos H".
    destruct τ;
      iDestruct "H" as "(% & %Hskind & %Hsvalue & _)";
      iPureIntro;
      by eexists.
  Qed.

  Lemma ref_flag_stype_interp_refine ξ ξ' T :
    ref_flag_le ξ ξ' ->
    ref_flag_stype_interp ξ T ->
    ref_flag_stype_interp (Σ:=Σ) ξ' T.
  Proof.
    intros Hξ HT.
    by destruct ξ; destruct ξ'.
  Qed.

  Notation refok sk T := (ref_flag_stype_interp (skind_ref_flag sk) T).

  Lemma srec_interp_pers_aux (T : semantic_type) sk (se : semantic_env (Σ := Σ)) :
    (∀ (Φ : leibnizO semantic_value -n> iPropO Σ),
       refok sk Φ →
       refok sk (T (se.1, (sk, (sk, add_skind_interp_closed sk Φ)) :: se.2))) →
    refok sk (fixpoint (skind_rec_interp1 sk T se)).
  Proof.
    intros.
    apply fixpoint_ind.
    - intros U V Huv Hu.
      unfold equiv in Huv.
      destruct (skind_ref_flag sk); cbn in Hu; try done; intros sv.
      * specialize (Huv sv).
        unfold Persistent.
        unfold Persistent in Hu.
        iIntros "H".
        setoid_rewrite <- Huv.
        by iApply Hu.
      * specialize (Huv sv).
        unfold Persistent.
        unfold Persistent in Hu.
        iIntros "H".
        setoid_rewrite <- Huv.
        by iApply Hu.
    - exists (λne (sv : leibnizO semantic_value), emp%I).
      destruct (skind_ref_flag sk); cbn; try done; typeclasses eauto.
    - intros T0 Hsk.
      cbn.
      destruct (skind_ref_flag sk); cbn; last done; intros sv.
      + eapply later_persistent; eapply H; done.
      + eapply later_persistent; eapply H; done.
    - destruct (skind_ref_flag sk); cbn; last done.
      + apply limit_preserving_forall => sv.
        apply limit_preserving_Persistent; solve_proper.
      + apply limit_preserving_forall => sv.
        apply limit_preserving_Persistent; solve_proper.
  Qed.

  Lemma add_skind_interp_pers τ (T : semantic_type) (se : semantic_env (Σ := Σ)) (sv : semantic_value) :
    Persistent (T se sv) →
    Persistent (add_skind_interp τ T se sv).
  Proof.
    intros H.
    unfold add_skind_interp.
    apply bi.exist_persistent; intros sk.
    apply bi.sep_persistent; first typeclasses eauto.
    apply bi.sep_persistent; first typeclasses eauto.
    done.
  Qed.

  Lemma ref_flag_interp_pers sk τ (T : semantic_type) (se : semantic_env (Σ := Σ)) :
    ref_flag_stype_interp sk (T se) →
    ref_flag_stype_interp sk (add_skind_interp τ T se).
  Proof.
    unfold ref_flag_stype_interp.
    destruct sk; last done; intros sv; eauto using add_skind_interp_pers.
  Qed.

  Lemma type_interp_equiv τ se :
    type_interp rti sr τ se ≡ add_skind_interp τ (pre_type_interp rti sr τ) se.
  Proof.
    intros sv.
    apply type_interp_eq.
  Qed.

  Lemma value_interp_equiv τ se :
    value_interp rti sr se τ ≡ add_skind_interp τ (pre_type_interp rti sr τ) se.
  Proof.
    intros sv.
    apply value_interp_eq.
  Qed.

  Instance ref_flag_stype_interp_proper_impl ξ :
    Proper (equiv ==> flip impl) (ref_flag_stype_interp (Σ := Σ) ξ).
  Proof.
    iIntros (t1 t2 Ht Ht1).
    destruct ξ; cbn in *; last done;
      intros sv; specialize (Ht sv); by rewrite Ht.
  Qed.

  Notation sval_ok sκ T := (∀ sv : leibnizO semantic_value, T sv ⊢ ⌜skind_has_svalue sκ sv⌝).

  Instance sval_ok_proper sκ :
    Proper (equiv ==> impl) (skind_has_stype (Σ := Σ) sκ).
  Proof.
    unfold skind_has_stype, refok, Persistent.
    intros t1 t2 Ht [Hp Hs]; destruct (skind_ref_flag sκ).
    - split; iIntros (sv) "Ht2"; setoid_rewrite <- (Ht sv);
        [by iApply Hp | by iApply Hs].
    - split; iIntros (sv) "Ht2"; setoid_rewrite <- (Ht sv);
        [by iApply Hp | by iApply Hs].
    - split; first done.
      iIntros (sv) "Ht2"; setoid_rewrite <- (Ht sv);
        by iApply Hs.
  Qed.

  Definition type_ctx_refs_interp (κs : list kind) (se : semantic_env (Σ := Σ)) : Prop :=
    Forall2
      (fun κ '(sκ, (sκT, T)) => eval_kind se κ = Some sκ /\ subskind_of sκT sκ /\ refok sκT T)
      κs
      (senv_types se).

  Definition sem_env_interp_refs F se :=
    kind_ctx_interp (fc_kind_ctx F) se ∧
    type_ctx_refs_interp (fc_type_vars F) se.

  Lemma type_ctx_interp_proj_refs tys se :
    type_ctx_interp tys se →
    type_ctx_refs_interp tys se.
  Proof.
    unfold type_ctx_interp, type_ctx_refs_interp.
    intros Hse.
    eapply Forall2_impl; first apply Hse.
    intros k [sk [sk_T T]] [Hev [Hsub [Hp Hs]]].
    tauto.
  Qed.

  Lemma sem_env_interp_proj_refs F se :
    sem_env_interp F se →
    sem_env_interp_refs F se.
  Proof.
    unfold sem_env_interp, sem_env_interp_refs.
    intros [Hk Ht].
    eauto using type_ctx_interp_proj_refs.
  Qed.

  Lemma sem_env_interp_refs_insert_type F (se : semantic_env (Σ:=Σ)) κ sκ sκ_T T :
    sem_env_interp_refs F se →
    eval_kind se κ = Some sκ →
    subskind_of sκ_T sκ ->
    refok sκ_T T →
    sem_env_interp_refs (F <| fc_type_vars ::= cons κ |>) (senv_insert_type sκ sκ_T T se).
  Proof.
    intros [Hkind Htypes] Hκ Hsubsk HT.
    split.
    - destruct Hkind as (Hmem & Hrep & Hsize).
      repeat split; cbn; done.
    - cbn [fc_type_vars].
      apply Forall2_cons.
      split.
      + split.
        * by eapply eval_kind_type_irrel.
        * done.
      + eapply Forall2_impl; [exact Htypes|].
        intros κ' [sκ' [sκ_T' T']] [Heval' HT'].
        split; [by eapply eval_kind_type_irrel | exact HT'].
  Qed.

  Lemma sem_env_interp_refs_insert_rep F se ιs :
    sem_env_interp_refs F se ->
    sem_env_interp_refs (add_rep_var F) (senv_insert_rep ιs se).
  Proof.
    Transparent senv_insert_rep.
    intros Hse.
    destruct Hse as ((h1 & h2 & h3) & h4).
    cbn in h1; cbn in h2; cbn in h3.
    repeat split; try done.
    + cbn.
      rewrite <- h2.
      done.
    + unfold type_ctx_interp.
      cbn.
      unfold type_ctx_refs_interp in h4.
      cbn in h4.
      apply Forall2_same_length_lookup_2.
      {
        unfold add_rep_var; cbn.
        unfold set.
        cbn.
        rewrite length_map.
        eapply Forall2_length; done.
      }
      intros *.
      destruct y as [sκ [sκ_T T]].
      intros.
      change (se.1.1.1, ιs::se.1.1.2, se.1.2, se.2) with (senv_insert_rep ιs se).
      pose proof (eval_kind_up_shift_rep_eq (Σ := Σ)).
      apply map_lookup_helper_backwards in H.
      destruct H as (K & lokp & ->).
      pose proof (Forall2_lookup_lr _ _ _ _ _ _ h4 lokp H0) as [? [? ?]].
      split; try done.
      by setoid_rewrite <- eval_kind_up_shift_rep_eq.
  Qed.

  Lemma sem_env_interp_refs_insert_size F se n :
    sem_env_interp_refs F se ->
    sem_env_interp_refs (add_size_var F) (senv_insert_size n se).
  Proof.
    Transparent senv_insert_size.
    intros Hse.
    destruct Hse as ((h1 & h2 & h3) & h4).
    cbn in h1; cbn in h2; cbn in h3.
    repeat split; try done.
    + cbn.
      rewrite <- h3.
      done.
    + unfold type_ctx_refs_interp.
      cbn.
      unfold type_ctx_interp in h4.
      cbn in h4.
      apply Forall2_same_length_lookup_2.
      {
        unfold add_rep_var; cbn.
        unfold set.
        cbn.
        rewrite length_map.
        eapply Forall2_length; done.
      }
      intros *.
      destruct y as [sκ [sκ_T T]].
      intros.
      change (se.1.1.1, se.1.1.2, n::se.1.2, se.2) with (senv_insert_size n se).
      apply map_lookup_helper_backwards in H.
      destruct H as (K & lokp & ->).
      setoid_rewrite <- (eval_kind_up_shift_size_eq).
      pose proof (Forall2_lookup_lr _ _ _ _ _ _ h4 lokp H0).
      cbn in H.
      done.
  Qed.


  Lemma sem_env_interp_refs_insert_mem F (se : semantic_env (Σ:=Σ)) μ :
    sem_env_interp_refs F se →
    sem_env_interp_refs (F <| fc_kind_ctx; kc_mem_vars ::= S |>) (senv_insert_mem μ se).
  Proof.
    intros [Hkind Htypes].
    destruct se as [[[m r] s] t].
    destruct F as [ret loc lab K tys]; destruct K.
    cbn -[senv_insert_mem] in *;  split.
    - destruct Hkind as (Hmem & Hrep & Hsize); cbn in *.
      repeat split; cbn; try done.
      congruence.
    - unfold set; cbn -[senv_insert_mem].
      unfold type_ctx_interp in *; cbn -[senv_insert_mem] in *.
      eapply Forall2_impl; [exact Htypes|].
      intros κ' [sκ' [sκ_T' T']] [Heval' HT'].
      split; eauto.
      by setoid_rewrite <- eval_kind_mem_irrel_eq.
  Qed.

  Lemma eval_kind_flags (se : semantic_env (Σ := Σ)) κ sκ :
    eval_kind se κ = Some sκ →
    kind_ref_flag κ = skind_ref_flag sκ.
  Proof.
    destruct κ; cbn; intros Hev.
    - apply bind_Some in Hev.
      destruct Hev as (ιs & Hιs & Hret).
      by inversion Hret.
    - apply bind_Some in Hev.
      destruct Hev as (n & Hn & Hret).
      by inversion Hret.
  Qed.

  Lemma refok_add_skind_closed sκ (T : leibnizO semantic_value -n> iPropO Σ) :
    refok sκ T →
    refok sκ (add_skind_interp_closed sκ T).
  Proof.
    unfold refok, add_skind_interp_closed.
    destruct (skind_ref_flag sκ); intros.
    - apply sep_persistent; typeclasses eauto.
    - apply sep_persistent; typeclasses eauto.
    - done.
  Qed.

  Lemma kinding_sound_ref_flag F se τ κ sκ :
    has_kind F τ κ ->
    sem_env_interp_refs F se ->
    eval_kind se κ = Some sκ ->
    refok sκ (value_interp rti sr se τ).
  Proof using Σ rti sr.
    intros Hκ.
    revert se sκ.
    induction Hκ using has_kind_ind' with (P0 := λ _ _, True) (Pi := λ _ _, True);
      try intros * Hse Hsκ.
    - (* I31T *)
      eapply ref_flag_stype_interp_refine; first apply least_ref_flag.
      intros ?.
      typeclasses eauto.
    - (* i32 *)
      eapply ref_flag_stype_interp_refine; first apply least_ref_flag.
      intros ?.
      typeclasses eauto.
    - (* i64 *)
      eapply ref_flag_stype_interp_refine; first apply least_ref_flag.
      intros ?.
      typeclasses eauto.
    - (* f32 *)
      eapply ref_flag_stype_interp_refine; first apply least_ref_flag.
      intros ?.
      typeclasses eauto.
    - (* f64 *)
      eapply ref_flag_stype_interp_refine; first apply least_ref_flag.
      intros ?.
      typeclasses eauto.
    - (* SumT *)
      setoid_rewrite type_interp_equiv.
      apply ref_flag_interp_pers.
      setoid_rewrite <- eval_kind_flags; last by eauto.
      cbn.

      subst κ.
      cbn in Hsκ.
      apply bind_Some in Hsκ.
      destruct Hsκ as (ιs & Hcat & Hret).
      apply fmap_Some in Hcat.
      destruct Hcat as (ιss & Hιss & ->).
      inversion Hret; subst sκ; clear Hret.

      unfold ref_flag_stype_interp.
      destruct (ref_flag_lub ξs) eqn:Hlub; last done.
      all: intros sv; cbn -[sum_interp_offset sum_interp_count type_arep];
        apply bi.exist_persistent; intros i;
        apply bi.exist_persistent; intros os;
        apply bi.exist_persistent; intros off;
        apply bi.exist_persistent; intros count;
        repeat (apply bi.sep_persistent; first typeclasses eauto);
        assert (Hmaplk : list_lookup i (map (type_interp rti sr) τs) = (type_interp rti sr) <$> (τs !! i))
          by apply list_lookup_fmap;
        rewrite Hmaplk;
        destruct (τs !! i) as [τ|] eqn:Hτ; cbn;
        last typeclasses eauto;
        (edestruct (Forall3_lookup_l _ _ _ _ _ _ H Hτ) as (ρ & ξ & Hρ & Hξ & Hrefok));
        (pose proof (util.mapM_lookup _ _ _ i Hιss) as Hlk);
        (rewrite Hρ in Hlk; cbn in Hlk);
        (pose proof (length_mapM _ _ _ Hιss) as Hlenρι);
        (assert (is_Some (ιss !! i)) as [ιsi Hιsi]
          by (apply lookup_lt_is_Some; rewrite <- Hlenρι; apply lookup_lt_is_Some; rewrite Hρ; done));
        (rewrite Hιsi in Hlk; cbn in Hlk);
        (specialize (Hrefok se (SVALTYPE ιsi ξ) ltac:(done) ltac:(cbn; by rewrite Hlk)));
        (unfold refok in Hrefok; cbn in Hrefok);
        (pose proof (ref_flag_lub_ub ξ ξs (list_elem_of_lookup_2 _ _ _ Hξ)) as Hub);
        (rewrite Hlub in Hub);
        (destruct ξ; eauto; last by inversion Hub).
    - (* VariantT *)
      setoid_rewrite type_interp_equiv.
      apply ref_flag_interp_pers.
      setoid_rewrite <- eval_kind_flags; last by eauto.
      cbn.

      subst κ.
      cbn in Hsκ.
      apply bind_Some in Hsκ.
      destruct Hsκ as (n & Hcat & Hret).
      apply bind_Some in Hcat.
      destruct Hcat as (ns & Hns & Hneq).
      inversion Hneq; subst n; clear Hneq.
      inversion Hret; subst sκ; clear Hret.

      unfold ref_flag_stype_interp.
      destruct (ref_flag_lub ξs) eqn:Hlub; last done.
      all: intros sv; cbn -[type_arep];
        apply bi.exist_persistent; intros i;
        apply bi.exist_persistent; intros ntag;
        apply bi.exist_persistent; intros ws;
        apply bi.exist_persistent; intros ws';
        repeat (apply bi.sep_persistent; first typeclasses eauto);
        assert (Hmaplk : list_lookup i (map (type_interp rti sr) τs) = (type_interp rti sr) <$> (τs !! i))
          by apply list_lookup_fmap;
        rewrite Hmaplk;
        destruct (τs !! i) as [τ|] eqn:Hτ; cbn;
        last typeclasses eauto;
        (edestruct (Forall3_lookup_l _ _ _ _ _ _ H Hτ) as (σ & ξ & Hσ & Hξ & Hrefok));
        (pose proof (util.mapM_lookup _ _ _ i Hns) as Hlk);
        (rewrite Hσ in Hlk; cbn in Hlk);
        (pose proof (length_mapM _ _ _ Hns) as Hlenσn);
        (assert (is_Some (ns !! i)) as [ni Hni]
          by (apply lookup_lt_is_Some; rewrite <- Hlenσn; apply lookup_lt_is_Some; rewrite Hσ; done));
        (rewrite Hni in Hlk; cbn in Hlk);
        (specialize (Hrefok se (SMEMTYPE ni ξ) ltac:(done) ltac:(cbn; by rewrite Hlk)));
        (unfold refok in Hrefok; cbn in Hrefok);
        (pose proof (ref_flag_lub_ub ξ ξs (list_elem_of_lookup_2 _ _ _ Hξ)) as Hub);
        (rewrite Hlub in Hub);
        (destruct ξ; eauto; last by inversion Hub).
    - (* ProdT *)
      setoid_rewrite type_interp_equiv.
      apply ref_flag_interp_pers.
      setoid_rewrite <- eval_kind_flags; last by eauto.
      cbn.

      subst κ.
      cbn in Hsκ.
      apply bind_Some in Hsκ.
      destruct Hsκ as (ιs & Hcat & Hret).
      apply fmap_Some in Hcat.
      destruct Hcat as (ιss & Hιss & ->).
      inversion Hret; subst sκ; clear Hret.
      pose proof (length_mapM _ _ _ Hιss) as Hlens1.
      pose proof (Forall3_length_lm _ _ _ _ H).
      pose proof (Forall3_length_lr _ _ _ _ H).

      unfold ref_flag_stype_interp.
      destruct (ref_flag_lub ξs) eqn:Hlub; last done.
      + intros sv.
        apply bi.exist_persistent; intros oss.
        apply bi.sep_persistent; first typeclasses eauto.
        rewrite big_sepL2_fmap_l.
        apply big_sepL2_persistent; intros k τ os Hτ Hos.
        assert (k < length τs).
        { by apply lookup_lt_is_Some. }
        assert (is_Some (ρs !! k)) as [ρ Hρ].
        { apply lookup_lt_is_Some; lia. }
        assert (is_Some (ξs !! k)) as [ξ Hξ].
        { apply lookup_lt_is_Some; lia. }
        assert (is_Some (ιss !! k)) as [ιs Hιs].
        { apply lookup_lt_is_Some; lia. }
        eapply Forall3_lookup_lmr in H; eauto.
        apply (util.mapM_lookup _ _ _ k) in Hιss.
        rewrite Hιs Hρ in Hιss; cbn in Hιss.
        specialize (H se (SVALTYPE ιs ξ) ltac:(done) ltac:(cbn; by rewrite Hιss)).
        unfold refok in H.
        cbn in H.
        pose proof (ref_flag_lub_ub ξ ξs (list_elem_of_lookup_2 _ _ _ Hξ)) as Hub.
        rewrite Hlub in Hub.
        destruct ξ; eauto; last by inversion Hub.
      + intros sv.
        apply bi.exist_persistent; intros oss.
        apply bi.sep_persistent; first typeclasses eauto.
        rewrite big_sepL2_fmap_l.
        apply big_sepL2_persistent; intros k τ os Hτ Hos.
        assert (k < length τs).
        { by apply lookup_lt_is_Some. }
        assert (is_Some (ρs !! k)) as [ρ Hρ].
        { apply lookup_lt_is_Some; lia. }
        assert (is_Some (ξs !! k)) as [ξ Hξ].
        { apply lookup_lt_is_Some; lia. }
        assert (is_Some (ιss !! k)) as [ιs Hιs].
        { apply lookup_lt_is_Some; lia. }
        eapply Forall3_lookup_lmr in H; eauto.
        apply (util.mapM_lookup _ _ _ k) in Hιss.
        rewrite Hιs Hρ in Hιss; cbn in Hιss.
        specialize (H se (SVALTYPE ιs ξ) ltac:(done) ltac:(cbn; by rewrite Hιss)).
        unfold refok in H.
        cbn in H.
        pose proof (ref_flag_lub_ub ξ ξs (list_elem_of_lookup_2 _ _ _ Hξ)) as Hub.
        rewrite Hlub in Hub.
        destruct ξ; eauto; last by inversion Hub.
    - (* StructT *)
      setoid_rewrite type_interp_equiv.
      apply ref_flag_interp_pers.
      setoid_rewrite <- eval_kind_flags; last by eauto.
      cbn.

      subst κ.
      cbn in Hsκ.
      apply bind_Some in Hsκ.
      destruct Hsκ as (ιs & Hcat & Hret).
      apply fmap_Some in Hcat.
      destruct Hcat as (ns & Hns & ->).
      inversion Hret; subst sκ; clear Hret.
      pose proof (length_mapM _ _ _ Hns) as Hlens1.
      pose proof (Forall3_length_lm _ _ _ _ H).
      pose proof (Forall3_length_lr _ _ _ _ H).

      unfold ref_flag_stype_interp.
      destruct (ref_flag_lub ξs) eqn:Hlub; last done.
      + intros sv.
        apply bi.exist_persistent; intros oss.
        apply bi.sep_persistent; first typeclasses eauto.
        rewrite big_sepL2_fmap_r.
        apply big_sepL2_persistent; intros k os τ Hos Hτ.
        assert (k < length τs).
        { by apply lookup_lt_is_Some. }
        assert (is_Some (σs !! k)) as [ρ Hρ].
        { apply lookup_lt_is_Some; lia. }
        assert (is_Some (ξs !! k)) as [ξ Hξ].
        { apply lookup_lt_is_Some; lia. }
        assert (is_Some (ns !! k)) as [n Hn].
        { apply lookup_lt_is_Some; lia. }
        eapply Forall3_lookup_lmr in H; eauto.
        apply (util.mapM_lookup _ _ _ k) in Hns.
        rewrite Hn Hρ in Hns; cbn in Hns.
        specialize (H se (SMEMTYPE n ξ) ltac:(done) ltac:(cbn; by rewrite Hns)).
        unfold refok in H.
        cbn in H.
        pose proof (ref_flag_lub_ub ξ ξs (list_elem_of_lookup_2 _ _ _ Hξ)) as Hub.
        rewrite Hlub in Hub.
        destruct ξ; eauto; last by inversion Hub.
      + intros sv.
        apply bi.exist_persistent; intros oss.
        apply bi.sep_persistent; first typeclasses eauto.
        rewrite big_sepL2_fmap_r.
        apply big_sepL2_persistent; intros k os τ Hos Hτ.
        assert (k < length τs).
        { by apply lookup_lt_is_Some. }
        assert (is_Some (σs !! k)) as [ρ Hρ].
        { apply lookup_lt_is_Some; lia. }
        assert (is_Some (ξs !! k)) as [ξ Hξ].
        { apply lookup_lt_is_Some; lia. }
        assert (is_Some (ns !! k)) as [n Hn].
        { apply lookup_lt_is_Some; lia. }
        eapply Forall3_lookup_lmr in H; eauto.
        apply (util.mapM_lookup _ _ _ k) in Hns.
        rewrite Hn Hρ in Hns; cbn in Hns.
        specialize (H se (SMEMTYPE n ξ) ltac:(done) ltac:(cbn; by rewrite Hns)).
        unfold refok in H.
        cbn in H.
        pose proof (ref_flag_lub_ub ξ ξs (list_elem_of_lookup_2 _ _ _ Hξ)) as Hub.
        rewrite Hlub in Hub.
        destruct ξ; eauto; last by inversion Hub.
    - (* RefT VarM *)
      subst κ.
      cbn in Hsκ; inversion Hsκ; subst.
      done.
    - (* RefT MemMM *)
      subst κ.
      cbn in Hsκ; inversion Hsκ.
      done.
    - (* RefT MemGC *)
      subst κ.
      cbn in Hsκ; inversion Hsκ.
      cbn.
      intros ?.
      destruct β; typeclasses eauto.
    - (* CodeRefT *)
      subst κ; cbn in Hsκ; inversion Hsκ; subst.
      intros ?.
      rewrite value_interp_eq.
      typeclasses eauto.
    - (* SerT *)
      subst κ.
      cbn in Hsκ.
      apply bind_Some in Hsκ.
      destruct Hsκ as (n & Hn & Hret).
      apply fmap_Some in Hn.
      destruct Hn as (ιs & Hιs & Hsum).
      inversion Hret; subst sκ.
      cbn.
      specialize (IHHκ se (SVALTYPE ιs ξ) Hse).
      cbn in IHHκ.
      rewrite Hιs in IHHκ.
      cbn in IHHκ.
      specialize (IHHκ eq_refl).
      unfold ref_flag_stype_interp.
      destruct ξ.
      * cbn in *.
        intros sv.
        setoid_rewrite value_interp_eq.
        apply add_skind_interp_pers.
        cbn.
        apply bi.exist_persistent; intros os.
        apply bi.sep_persistent; first typeclasses eauto.
        eapply IHHκ.
      * cbn in *.
        intros sv.
        setoid_rewrite value_interp_eq.
        apply add_skind_interp_pers.
        cbn.
        apply bi.exist_persistent; intros os.
        apply bi.sep_persistent; first typeclasses eauto.
        eapply IHHκ.
      * done.
    - (* PlugT *)
      eapply ref_flag_stype_interp_refine; first apply least_ref_flag.
      intros ?.
      typeclasses eauto.
    - eapply ref_flag_stype_interp_refine; first apply least_ref_flag.
      intros ?.
      typeclasses eauto.
    - (* RecT *)
      setoid_rewrite type_interp_equiv.
      apply ref_flag_interp_pers.
      cbn -[rec_interp].
      unfold rec_interp.
      cbn.
      rewrite Hsκ.
      apply srec_interp_pers_aux.
      intros T Ht.
      apply IHHκ; eauto.
      + apply sem_env_interp_refs_insert_type; eauto using subskind_of_refl, refok_add_skind_closed.
      + by apply eval_kind_type_irrel.
    - (* ExistsMemT *)
      rewrite value_interp_equiv.
      apply ref_flag_interp_pers.
      cbn.
      unfold refok.
      destruct (skind_ref_flag sκ) eqn:Hflag; last done.
      + intros sv.
        apply bi.exist_persistent; intros μ.
        specialize (IHHκ (μ :: se.1.1.1, se.1.1.2, se.1.2, se.2) sκ).
        unfold refok in IHHκ.
        rewrite Hflag in IHHκ.
        eapply IHHκ.
        * by eapply sem_env_interp_refs_insert_mem.
        * by setoid_rewrite <- eval_kind_mem_irrel_eq.
      + intros sv.
        apply bi.exist_persistent; intros μ.
        specialize (IHHκ (μ :: se.1.1.1, se.1.1.2, se.1.2, se.2) sκ).
        unfold refok in IHHκ.
        rewrite Hflag in IHHκ.
        eapply IHHκ.
        * by eapply sem_env_interp_refs_insert_mem.
        * by setoid_rewrite <- eval_kind_mem_irrel_eq.

    - (* ExistsRepT *)
      rewrite value_interp_equiv.
      apply ref_flag_interp_pers.
      cbn.
      unfold refok.
      destruct (skind_ref_flag sκ) eqn:Hflag; last done.
      + intros sv.
        apply bi.exist_persistent; intros ιs.
        specialize (IHHκ (se.1.1.1, ιs :: se.1.1.2, se.1.2, se.2) sκ).
        unfold refok in IHHκ.
        rewrite Hflag in IHHκ.
        eapply IHHκ.
        * by eapply sem_env_interp_refs_insert_rep.
        * by setoid_rewrite <- eval_kind_up_shift_rep_eq.
      + intros sv.
        apply bi.exist_persistent; intros ιs.
        specialize (IHHκ (se.1.1.1, ιs :: se.1.1.2, se.1.2, se.2) sκ).
        unfold refok in IHHκ.
        rewrite Hflag in IHHκ.
        eapply IHHκ.
        * by eapply sem_env_interp_refs_insert_rep.
        * by setoid_rewrite <- eval_kind_up_shift_rep_eq.
    - (* ExistsSizeT *)
      rewrite value_interp_equiv.
      apply ref_flag_interp_pers.
      cbn.
      unfold refok.
      destruct (skind_ref_flag sκ) eqn:Hflag; last done.
      + intros sv.
        apply bi.exist_persistent; intros n.
        specialize (IHHκ (se.1.1.1, se.1.1.2, n :: se.1.2, se.2) sκ).
        unfold refok in IHHκ.
        rewrite Hflag in IHHκ.
        eapply IHHκ.
        * by eapply sem_env_interp_refs_insert_size.
        * by setoid_rewrite <- eval_kind_up_shift_size_eq.
      + intros sv.
        apply bi.exist_persistent; intros n.
        specialize (IHHκ (se.1.1.1, se.1.1.2, n :: se.1.2, se.2) sκ).
        unfold refok in IHHκ.
        rewrite Hflag in IHHκ.
        eapply IHHκ.
        * by eapply sem_env_interp_refs_insert_size.
        * by setoid_rewrite <- eval_kind_up_shift_size_eq.
    - (* ExistsTypeT *)
      rewrite value_interp_equiv.
      apply ref_flag_interp_pers.
      pose proof H as Hevκ0.
      cbn -[senv_insert_type].
      unfold refok.
      destruct (skind_ref_flag sκ) eqn:Hflag; last done.
      + intros sv.
        unfold Persistent; iIntros "(%T' & %sk0 & %sk_T & %Hev & %Hsub & %Hst & Hty)".
        iExists T', sk0, sk_T.
        iSplit; first eauto.
        iSplit; first eauto.
        iSplit; first eauto.
        set (se' := senv_insert_type sk0 sk_T T' se).
        specialize (IHHκ se' sκ).
        unfold refok, Persistent in IHHκ.
        rewrite Hflag in IHHκ.
        iApply IHHκ; last done.
        * destruct Hst.
          apply sem_env_interp_refs_insert_type; eauto.
        * by apply eval_kind_type_irrel.
      + intros sv.
        unfold Persistent; iIntros "(%T' & %sk0 & %sk_T & %Hev & %Hsub & %Hst & Hty)".
        iExists T', sk0, sk_T.
        iSplit; first eauto.
        iSplit; first eauto.
        iSplit; first eauto.
        set (se' := senv_insert_type sk0 sk_T T' se).
        specialize (IHHκ se' sκ).
        unfold refok, Persistent in IHHκ.
        rewrite Hflag in IHHκ.
        iApply IHHκ; last done.
        * destruct Hst.
          apply sem_env_interp_refs_insert_type; eauto.
        * by apply eval_kind_type_irrel.
    - (* VarT *)
      cbn.
      setoid_rewrite value_interp_equiv.
      apply ref_flag_interp_pers.
      cbn.
      destruct Hse as [Hsek Hset].
      eapply Forall2_lookup in Hset.
      erewrite H in Hset.
      inversion Hset; subst.
      destruct y as [sk [skT T]].
      setoid_rewrite <- H2.
      destruct H3 as (Hev & Hsub & Hok).
      cbn.
      rewrite Hsκ in Hev; inversion Hev; subst.
      eapply ref_flag_stype_interp_refine; last done.
      inversion Hsub; subst; cbn; eauto.
    - done.
    - done.
    - done.
    - done.
    - done.
    - done.
  Qed.

  Lemma kinding_sound_svalue F se τ κ sκ sv :
    has_kind F τ κ ->
    sem_env_interp F se ->
    eval_kind se κ = Some sκ ->
    value_interp rti sr se τ sv ⊢ ⌜skind_has_svalue sκ sv⌝.
  Proof.
    iIntros (Hhas_kind Hse Heval_kind) "H".
    destruct τ;
      iDestruct "H" as "(% & % & % & _)";
      iPureIntro;
      (replace sκ0 with sκ in *; [done|by eapply type_skind_has_kind_agree]).
  Qed.

  Theorem kinding_sound F se τ κ sκ :
    has_kind F τ κ ->
    sem_env_interp F se ->
    eval_kind se κ = Some sκ ->
    skind_has_stype sκ (value_interp rti sr se τ).
  Proof.
    iIntros (Hhas_kind Hse Heval_kind).
    split.
    - eapply kinding_sound_ref_flag; eauto using sem_env_interp_proj_refs.
    - intros sv. eapply kinding_sound_svalue; eauto.
  Qed.

End kinding.
