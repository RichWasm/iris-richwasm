From mathcomp Require Import ssreflect.
From stdpp Require Import base list.
From RichWasm Require Import syntax typing util.
Require RichWasm.iris.logrel.
Require Import RecordUpdate.RecordUpdate.

Set Bullet Behavior "Strict Subproofs".

(* Begin renaming-index infrastructure: [idx_ren xi n n'] says a renaming
   [xi] maps every index below [n] to one below [n'] -- the precise
   condition under which [mem_ok]/[rep_ok]/[size_ok]/[kind_ok] (all of which
   bottom out in "index < count" checks) are preserved by renaming. *)
Definition idx_ren (xi : nat -> nat) (n n' : nat) : Prop :=
  forall i, i < n -> xi i < n'.

Lemma idx_ren_up xi n n' :
  idx_ren xi n n' -> idx_ren (unscoped.up_ren xi) (S n) (S n').
Proof.
  intros Hxi [|i] Hi; cbn; unfold core.funcomp; [lia|].
  assert (i < n) as Hi' by lia.
  specialize (Hxi i Hi'). lia.
Qed.

Lemma mem_ok_ren xi K K' m :
  idx_ren xi K.(kc_mem_vars) K'.(kc_mem_vars) ->
  mem_ok K m ->
  mem_ok K' (ren_memory xi m).
Proof.
  intros Hxi Hm.
  destruct Hm as [K m Hlt|K cm]; cbn.
  - apply OKVarM. by apply Hxi.
  - apply OKBaseM.
Qed.

Lemma rep_ok_ren xi K K' ρ :
  idx_ren xi K.(kc_rep_vars) K'.(kc_rep_vars) ->
  rep_ok K ρ ->
  rep_ok K' (ren_representation xi ρ).
Proof.
  intros Hxi Hρ.
  revert K K' Hxi Hρ.
  induction ρ using rep_ind; intros K K' Hxi Hρ; cbn; inversion Hρ; subst.
  - apply OKVarR. by apply Hxi.
  - apply OKSumR. rewrite Forall_fmap. apply Forall_forall; intros ρ0 Hin0.
    unfold compose. eapply Forall_forall in H; last exact Hin0.
    eapply Forall_forall in H2; last exact Hin0. eauto.
  - apply OKProdR. rewrite Forall_fmap. apply Forall_forall; intros ρ0 Hin0.
    unfold compose. eapply Forall_forall in H; last exact Hin0.
    eapply Forall_forall in H2; last exact Hin0. eauto.
  - apply OKAtomR.
Qed.

Lemma size_ok_ren xir xis K K' σ :
  idx_ren xir K.(kc_rep_vars) K'.(kc_rep_vars) ->
  idx_ren xis K.(kc_size_vars) K'.(kc_size_vars) ->
  size_ok K σ ->
  size_ok K' (ren_size xir xis σ).
Proof.
  intros Hxir Hxis Hσ.
  revert K K' Hxir Hxis Hσ.
  induction σ using size_ind; intros K K' Hxir Hxis Hσ; cbn; inversion Hσ; subst.
  - apply OKVarS. by apply Hxis.
  - apply OKSumS. rewrite Forall_fmap. apply Forall_forall; intros σ0 Hin0.
    unfold compose. eapply Forall_forall in H; last exact Hin0.
    eapply Forall_forall in H2; last exact Hin0. eauto.
  - apply OKProdS. rewrite Forall_fmap. apply Forall_forall; intros σ0 Hin0.
    unfold compose. eapply Forall_forall in H; last exact Hin0.
    eapply Forall_forall in H2; last exact Hin0. eauto.
  - apply OKRepS. by apply rep_ok_ren with (K:=K).
  - apply OKConstS.
Qed.

Lemma kind_ok_ren xir xis K K' κ :
  idx_ren xir K.(kc_rep_vars) K'.(kc_rep_vars) ->
  idx_ren xis K.(kc_size_vars) K'.(kc_size_vars) ->
  kind_ok K κ ->
  kind_ok K' (ren_kind xir xis κ).
Proof.
  intros Hxir Hxis Hκ.
  destruct Hκ as [K ρ ξ Hρ|K σ ξ Hσ]; cbn.
  - apply OKVALTYPE. by apply rep_ok_ren with (K:=K).
  - apply OKMEMTYPE. by apply size_ok_ren with (K:=K).
Qed.

(* Substitution analogues of [rep_ok_ren]/[size_ok_ren]/[kind_ok_ren]: instead
   of a renaming staying within index bounds, a substitution must map every
   in-range variable directly to an already-[_ok] term. *)
Lemma rep_ok_subst sub_r K K' ρ :
  (forall r, r < K.(kc_rep_vars) -> rep_ok K' (sub_r r)) ->
  rep_ok K ρ ->
  rep_ok K' (subst_representation sub_r ρ).
Proof.
  intros Hsub Hρ.
  revert K K' Hsub Hρ.
  induction ρ using rep_ind; intros K K' Hsub Hρ; cbn; inversion Hρ; subst.
  - by apply Hsub.
  - apply OKSumR. rewrite Forall_fmap. apply Forall_forall; intros ρ0 Hin0.
    unfold compose. eapply Forall_forall in H; last exact Hin0.
    eapply Forall_forall in H2; last exact Hin0. eauto.
  - apply OKProdR. rewrite Forall_fmap. apply Forall_forall; intros ρ0 Hin0.
    unfold compose. eapply Forall_forall in H; last exact Hin0.
    eapply Forall_forall in H2; last exact Hin0. eauto.
  - apply OKAtomR.
Qed.

Lemma size_ok_subst sub_r sub_s K K' σ :
  (forall r, r < K.(kc_rep_vars) -> rep_ok K' (sub_r r)) ->
  (forall s, s < K.(kc_size_vars) -> size_ok K' (sub_s s)) ->
  size_ok K σ ->
  size_ok K' (subst_size sub_r sub_s σ).
Proof.
  intros Hsubr Hsubs Hσ.
  revert K K' Hsubr Hsubs Hσ.
  induction σ using size_ind; intros K K' Hsubr Hsubs Hσ; cbn; inversion Hσ; subst.
  - by apply Hsubs.
  - apply OKSumS. rewrite Forall_fmap. apply Forall_forall; intros σ0 Hin0.
    unfold compose. eapply Forall_forall in H; last exact Hin0.
    eapply Forall_forall in H2; last exact Hin0. eauto.
  - apply OKProdS. rewrite Forall_fmap. apply Forall_forall; intros σ0 Hin0.
    unfold compose. eapply Forall_forall in H; last exact Hin0.
    eapply Forall_forall in H2; last exact Hin0. eauto.
  - apply OKRepS. by apply rep_ok_subst with (K:=K).
  - apply OKConstS.
Qed.

Lemma kind_ok_subst sub_r sub_s K K' κ :
  (forall r, r < K.(kc_rep_vars) -> rep_ok K' (sub_r r)) ->
  (forall s, s < K.(kc_size_vars) -> size_ok K' (sub_s s)) ->
  kind_ok K κ ->
  kind_ok K' (subst_kind sub_r sub_s κ).
Proof.
  intros Hsubr Hsubs Hκ.
  destruct Hκ as [K ρ ξ Hρ|K σ ξ Hσ]; cbn.
  - apply OKVALTYPE. by apply rep_ok_subst with (K:=K).
  - apply OKMEMTYPE. by apply size_ok_subst with (K:=K).
Qed.
(* End renaming-index infrastructure *)

(* Begin weakening lemmas *)
Lemma fc_kind_ctx_ty_update F upd :
  fc_kind_ctx (F <| fc_type_vars ::= upd |>) = fc_kind_ctx F.
Proof.
  by destruct F.
Qed.

Lemma fc_type_vars_get_upd F upd :
  fc_type_vars (F <| fc_type_vars ::= upd |>) = upd (fc_type_vars F).
Proof.
  done.
Qed.

Lemma has_kind_var_wk_ty F n κ κv :
  has_kind (F <| fc_type_vars ::= cons κv |>) (VarT (S n)) κ ↔ has_kind F (VarT n) κ.
Proof.
  split; intros Hk.
  - inversion Hk; subst.
    constructor.
    + destruct F; cbn in *; auto.
    + by rewrite fc_kind_ctx_ty_update in H2.
  - inversion Hk; subst.
    constructor.
    + by rewrite fc_type_vars_get_upd.
    + by rewrite fc_kind_ctx_ty_update.
Qed.

(* This lemma is not currently used anywhere *)
Lemma has_kind_wk_ty F τ κ κv :
  has_kind F τ κ ↔ has_kind (F <| fc_type_vars ::= cons κv |>) (ren_type id id id S τ) κ.
Proof.
Admitted.

(* End weakening lemmas *)
Ltac fold_subst :=
  fold subst_type subst_size subst_representation subst_function_type.

Lemma subkind_of_subst s__rep s__size κ κ' :
  subkind_of κ κ' ->
  subkind_of (subst_kind s__rep s__size κ)
             (subst_kind s__rep s__size κ').
Proof.
  intros Hle.
  by destruct Hle; constructor.
Qed.

Definition fc_ren (ξr ξs ξt : nat → nat) (F F' : function_ctx) : Prop :=
  ∀ t, fc_type_vars F' !! ξt t = ren_kind ξr ξs <$> fc_type_vars F !! t.

Lemma fc_ren_cons ξr ξs ξt F F' κ :
  fc_ren ξr ξs ξt F F' →
  fc_ren ξr ξs (unscoped.up_ren ξt)
    (F <| fc_type_vars ::= cons κ |>) (F' <| fc_type_vars ::= cons (ren_kind ξr ξs κ) |>).
Proof.
  intros HF [|t]; cbn; [done|apply HF].
Qed.

Lemma fc_ren_mem ξr ξs ξt F F' :
  fc_ren ξr ξs ξt F F' →
  fc_ren ξr ξs ξt (F <| fc_kind_ctx ::= set kc_mem_vars S |>) (F' <| fc_kind_ctx ::= set kc_mem_vars S |>).
Proof.
  intros HF t; cbn; apply HF.
Qed.

Lemma fc_ren_rep ξr ξs ξt F F' :
  fc_ren ξr ξs ξt F F' →
  fc_ren (unscoped.up_ren ξr) ξs ξt (add_rep_var F) (add_rep_var F').
Proof.
  intros HF t; unfold fc_ren in *; destruct F as [? ? ? ? tvs], F' as [? ? ? ? tvs'].
  unfold add_rep_var; cbn in *.
  rewrite !list_lookup_fmap HF.
  destruct (tvs !! t) as [κ|]; cbn; [f_equal|done].
  rewrite !renRen_kind.
  apply extRen_kind; intros n; done.
Qed.

Lemma fc_ren_size ξr ξs ξt F F' :
  fc_ren ξr ξs ξt F F' →
  fc_ren ξr (unscoped.up_ren ξs) ξt (add_size_var F) (add_size_var F').
Proof.
  intros HF t; unfold fc_ren in *; destruct F as [? ? ? ? tvs], F' as [? ? ? ? tvs'].
  unfold add_size_var; cbn in *.
  rewrite !list_lookup_fmap HF.
  destruct (tvs !! t) as [κ|]; cbn; [f_equal|done].
  rewrite !renRen_kind.
  apply extRen_kind; intros n; done.
Qed.

(* [ctx_ren xim xir xis xit F F'] bundles [fc_ren] (type-variable lookup /
   stored-kind compatibility) with the analogous "renaming stays in bounds"
   condition for the memory/rep/size variable *counts* in [fc_kind_ctx] --
   exactly what [mem_ok]/[rep_ok]/[size_ok]/[kind_ok] need to transport
   across a renaming ([mem_ok_ren] etc. above). This is the full
   "renaming-compatible contexts" relation a general [has_kind] renaming
   lemma needs. *)
Definition ctx_ren (ξm ξr ξs ξt : nat -> nat) (F F' : function_ctx) : Prop :=
  fc_ren ξr ξs ξt F F' /\
  idx_ren ξm F.(fc_kind_ctx).(kc_mem_vars) F'.(fc_kind_ctx).(kc_mem_vars) /\
  idx_ren ξr F.(fc_kind_ctx).(kc_rep_vars) F'.(fc_kind_ctx).(kc_rep_vars) /\
  idx_ren ξs F.(fc_kind_ctx).(kc_size_vars) F'.(fc_kind_ctx).(kc_size_vars).

Lemma ctx_ren_cons ξm ξr ξs ξt F F' κ :
  ctx_ren ξm ξr ξs ξt F F' ->
  ctx_ren ξm ξr ξs (unscoped.up_ren ξt)
    (F <| fc_type_vars ::= cons κ |>) (F' <| fc_type_vars ::= cons (ren_kind ξr ξs κ) |>).
Proof.
  intros (Hty & Hm & Hr & Hs).
  split; [|split; [|split]]; cbn; auto using fc_ren_cons.
Qed.

(* Pure weakening: [F] renamed by a single fresh type variable at the front
   is renaming-compatible with [F <| cons κ' |>], unconditionally. Needed to
   lift an already-established [has_kind F ... ] fact into a context with
   one more (unused) bound type variable. *)
Lemma ctx_ren_weaken1 F κ' :
  ctx_ren unscoped.id unscoped.id unscoped.id unscoped.shift F (F <| fc_type_vars ::= cons κ' |>).
Proof.
  split; [|split; [|split]]; cbn; rewrite ?fc_kind_ctx_ty_update.
  - unfold fc_ren; intros t; cbn. rewrite fc_type_vars_get_upd. cbn.
    destruct (fc_type_vars F !! t) eqn:E; cbn; [f_equal; by rewrite rinstId'_kind | done].
  - intros i Hi; exact Hi.
  - intros i Hi; exact Hi.
  - intros i Hi; exact Hi.
Qed.

(* Pure weakening by one fresh memory/rep/size variable, symmetric to
   [ctx_ren_weaken1] above. *)
Lemma ctx_ren_weaken_mem F :
  ctx_ren unscoped.shift unscoped.id unscoped.id unscoped.id F (add_mem_var F).
Proof.
  split; [|split;[|split]]; cbn.
  - unfold fc_ren, add_mem_var; intros t; cbn.
    destruct (fc_type_vars F !! t) eqn:E; cbn; [f_equal; by rewrite rinstId'_kind|done].
  - unfold idx_ren, add_mem_var, unscoped.shift; intros i Hi; destruct F, fc_kind_ctx; cbn in *; lia.
  - unfold idx_ren, add_mem_var; intros i Hi; destruct F, fc_kind_ctx; cbn in *; exact Hi.
  - unfold idx_ren, add_mem_var; intros i Hi; destruct F, fc_kind_ctx; cbn in *; exact Hi.
Qed.

Lemma ctx_ren_weaken_rep F :
  ctx_ren unscoped.id unscoped.shift unscoped.id unscoped.id F (add_rep_var F).
Proof.
  split; [|split;[|split]]; cbn.
  - unfold fc_ren, add_rep_var; intros t; cbn. by rewrite list_lookup_fmap.
  - unfold idx_ren, add_rep_var; intros i Hi; destruct F, fc_kind_ctx; cbn in *; exact Hi.
  - unfold idx_ren, add_rep_var, unscoped.shift; intros i Hi; destruct F, fc_kind_ctx; cbn in *; lia.
  - unfold idx_ren, add_rep_var; intros i Hi; destruct F, fc_kind_ctx; cbn in *; exact Hi.
Qed.

Lemma ctx_ren_weaken_size F :
  ctx_ren unscoped.id unscoped.id unscoped.shift unscoped.id F (add_size_var F).
Proof.
  split; [|split;[|split]]; cbn.
  - unfold fc_ren, add_size_var; intros t; cbn. by rewrite list_lookup_fmap.
  - unfold idx_ren, add_size_var; intros i Hi; destruct F, fc_kind_ctx; cbn in *; exact Hi.
  - unfold idx_ren, add_size_var; intros i Hi; destruct F, fc_kind_ctx; cbn in *; exact Hi.
  - unfold idx_ren, add_size_var, unscoped.shift; intros i Hi; destruct F, fc_kind_ctx; cbn in *; lia.
Qed.

Lemma ctx_ren_mem ξm ξr ξs ξt F F' :
  ctx_ren ξm ξr ξs ξt F F' ->
  ctx_ren (unscoped.up_ren ξm) ξr ξs ξt
    (F <| fc_kind_ctx ::= set kc_mem_vars S |>) (F' <| fc_kind_ctx ::= set kc_mem_vars S |>).
Proof.
  intros (Hty & Hm & Hr & Hs).
  split; [|split; [|split]]; cbn; destruct F, F', fc_kind_ctx, fc_kind_ctx0; cbn in *;
    auto using fc_ren_mem, idx_ren_up.
Qed.

Lemma ctx_ren_rep ξm ξr ξs ξt F F' :
  ctx_ren ξm ξr ξs ξt F F' ->
  ctx_ren ξm (unscoped.up_ren ξr) ξs ξt (add_rep_var F) (add_rep_var F').
Proof.
  intros (Hty & Hm & Hr & Hs).
  split; [|split; [|split]]; cbn; destruct F, F', fc_kind_ctx, fc_kind_ctx0; cbn in *;
    auto using fc_ren_rep, idx_ren_up.
Qed.

Lemma ctx_ren_size ξm ξr ξs ξt F F' :
  ctx_ren ξm ξr ξs ξt F F' ->
  ctx_ren ξm ξr (unscoped.up_ren ξs) ξt (add_size_var F) (add_size_var F').
Proof.
  intros (Hty & Hm & Hr & Hs).
  split; [|split; [|split]]; cbn; destruct F, F', fc_kind_ctx, fc_kind_ctx0; cbn in *;
    auto using fc_ren_size, idx_ren_up.
Qed.

Lemma Forall3_map_lm {A B A' B' C} (f : A -> A') (g : B -> B') (P : A' -> B' -> C -> Prop) l k k' :
  Forall3 (fun x y z => P (f x) (g y) z) l k k' ->
  Forall3 P (map f l) (map g k) k'.
Proof. induction 1; constructor; auto. Qed.

(* General renaming-preservation lemma for [has_kind]/[has_kind_ift]/
   [has_kind_ft], mutual via [has_kind_ind']. *)
Lemma has_kind_ren F τ κ :
  has_kind F τ κ ->
  forall F' ξim ξir ξis ξit, ctx_ren ξim ξir ξis ξit F F' ->
  has_kind F' (ren_type ξim ξir ξis ξit τ) (ren_kind ξir ξis κ).
Proof.
  intros H.
  induction H using has_kind_ind'
    with (P0 := fun F ϕ => forall F' ξim ξir ξis ξit, ctx_ren ξim ξir ξis ξit F F' ->
                      has_kind_ft F' (ren_function_type ξim ξir ξis ξit ϕ))
         (Pi := fun F ϕ => forall F' ξim ξir ξis ξit, ctx_ren ξim ξir ξis ξit F F' ->
                      has_kind_ift F' (ren_inner_function_type ξim ξir ξis ξit ϕ));
    intros F' ξim ξir ξis ξit Hctx; cbn; try (solve [constructor]).
  - (* KSum *)
    apply KSum, Forall3_map_lm, (Forall3_impl _ _ _ _ _ H); intros; eauto.
  - (* KVariant *)
    apply KVariant, Forall3_map_lm, (Forall3_impl _ _ _ _ _ H); intros; eauto.
  - (* KProd *)
    apply KProd, Forall3_map_lm, (Forall3_impl _ _ _ _ _ H); intros; eauto.
  - (* KStruct *)
    apply KStruct, Forall3_map_lm, (Forall3_impl _ _ _ _ _ H); intros; eauto.
  - (* KRefVar *)
    destruct Hctx as (Hty & Hm & Hr & Hs).
    apply (KRefVar _ _ _ _ (ren_size ξir ξis σ) ξ).
    + pose proof (mem_ok_ren ξim _ _ (VarM m) Hm H) as Hmem. cbn in Hmem. exact Hmem.
    + apply IHhas_kind. repeat split; auto.
  - (* KRefMM *)
    apply (KRefMM _ _ _ (ren_size ξir ξis σ) ξ). apply IHhas_kind. exact Hctx.
  - (* KRefGC *)
    apply (KRefGC _ _ _ (ren_size ξir ξis σ) ξ). apply IHhas_kind. exact Hctx.
  - (* KCodeRef *)
    apply KCodeRef. apply IHhas_kind. exact Hctx.
  - (* KSer *)
    apply (KSer _ _ (ren_representation ξir ρ) ξ). apply IHhas_kind. exact Hctx.
  - (* KPlug *)
    apply KPlug. destruct Hctx as (Hty & Hm & Hr & Hs).
    by apply rep_ok_ren with (K := fc_kind_ctx F).
  - (* KSpan *)
    apply KSpan. destruct Hctx as (Hty & Hm & Hr & Hs).
    by apply size_ok_ren with (K := fc_kind_ctx F).
  - (* KRec *)
    apply KRec. apply IHhas_kind. by apply ctx_ren_cons.
  - (* KExistsMem *)
    apply KExistsMem.
    + destruct Hctx as (Hty & Hm & Hr & Hs). by apply kind_ok_ren with (K := fc_kind_ctx F).
    + apply IHhas_kind. by apply ctx_ren_mem.
  - (* KExistsRep *)
    apply KExistsRep.
    + destruct Hctx as (Hty & Hm & Hr & Hs). by apply kind_ok_ren with (K := fc_kind_ctx F).
    + cbn [upRen_representation_memory upRen_representation_representation
             upRen_representation_size upRen_representation_type].
      assert (Heq : ren_kind unscoped.shift unscoped.id (ren_kind ξir ξis κ)
                  = ren_kind (unscoped.up_ren ξir) ξis (ren_kind unscoped.shift unscoped.id κ)).
      { rewrite !renRen_kind. apply extRen_kind.
        - intros n; unfold core.funcomp, unscoped.up_ren, unscoped.shift; done.
        - intros n; unfold core.funcomp; done. }
      rewrite Heq.
      apply IHhas_kind.
      by apply ctx_ren_rep.
  - (* KExistsSize *)
    apply KExistsSize.
    + destruct Hctx as (Hty & Hm & Hr & Hs). by apply kind_ok_ren with (K := fc_kind_ctx F).
    + cbn [upRen_size_memory upRen_size_representation upRen_size_size upRen_size_type].
      assert (Heq : ren_kind unscoped.id unscoped.shift (ren_kind ξir ξis κ)
                  = ren_kind ξir (unscoped.up_ren ξis) (ren_kind unscoped.id unscoped.shift κ)).
      { rewrite !renRen_kind. apply extRen_kind.
        - intros n; unfold core.funcomp; done.
        - intros n; unfold core.funcomp, unscoped.up_ren, unscoped.shift; done. }
      rewrite Heq.
      apply IHhas_kind.
      by apply ctx_ren_size.
  - (* KExistsType *)
    apply KExistsType.
    + destruct Hctx as (Hty & Hm & Hr & Hs). by apply kind_ok_ren with (K := fc_kind_ctx F).
    + destruct Hctx as (Hty & Hm & Hr & Hs). by apply kind_ok_ren with (K := fc_kind_ctx F).
    + apply IHhas_kind. by apply ctx_ren_cons.
  - (* KVar *)
    destruct Hctx as (Hty & Hm & Hr & Hs).
    apply KVar.
    + specialize (Hty t). rewrite H in Hty. cbn in Hty. by rewrite Hty.
    + by apply kind_ok_ren with (K := fc_kind_ctx F).
  - (* KMonoFun *)
    apply (KMonoFun _ _ _ (map (ren_kind ξir ξis) κs1) (map (ren_kind ξir ξis) κs2)).
    + apply Forall2_fmap, (Forall2_impl _ _ _ _ H); intros; eauto.
    + apply Forall2_fmap, (Forall2_impl _ _ _ _ H0); intros; eauto.
  - (* KInnerFun *)
    apply KInnerFun. apply IHhas_kind. exact Hctx.
  - (* KForallMem *)
    apply KForallMem. apply IHhas_kind. by apply ctx_ren_mem.
  - (* KForallRep *)
    apply KForallRep. apply IHhas_kind. by apply ctx_ren_rep.
  - (* KForallSize *)
    apply KForallSize. apply IHhas_kind. by apply ctx_ren_size.
  - (* KForallType *)
    apply KForallType.
    + destruct Hctx as (Hty & Hm & Hr & Hs). by apply kind_ok_ren with (K := fc_kind_ctx F).
    + apply IHhas_kind. by apply ctx_ren_cons.
Qed.

(* [ctx_subst_exact sub_m sub_r sub_s sub_t F' F] says a substitution out of
   [F'] into [F] is well-formed AND every type variable it replaces gets a
   witness of *exactly* its (substituted) expected kind -- no [subkind_of]
   slack. This is the "easy" substitution condition: it's enough for
   [has_kind_rec_subst] ([RecT]'s self-substitution always supplies an exact
   witness), but not for [function_type_inst]'s [FTInstType] (which allows a
   strictly smaller-kinded witness) -- that needs a genuinely harder,
   [subkind_of]-relaxed version left for later. *)
Definition ctx_subst_exact
  (sub_m : nat -> memory) (sub_r : nat -> representation) (sub_s : nat -> size) (sub_t : nat -> type)
  (F' F : function_ctx) : Prop :=
  (forall t κ, fc_type_vars F' !! t = Some κ -> has_kind F (sub_t t) (subst_kind sub_r sub_s κ)) /\
  (forall m, m < F'.(fc_kind_ctx).(kc_mem_vars) -> mem_ok F.(fc_kind_ctx) (sub_m m)) /\
  (forall r, r < F'.(fc_kind_ctx).(kc_rep_vars) -> rep_ok F.(fc_kind_ctx) (sub_r r)) /\
  (forall s, s < F'.(fc_kind_ctx).(kc_size_vars) -> size_ok F.(fc_kind_ctx) (sub_s s)).

Lemma ctx_subst_exact_cons sub_m sub_r sub_s sub_t F' F κ :
  kind_ok (fc_kind_ctx F') κ ->
  ctx_subst_exact sub_m sub_r sub_s sub_t F' F ->
  ctx_subst_exact (up_type_memory sub_m) (up_type_representation sub_r) (up_type_size sub_s)
    (up_type_type sub_t)
    (F' <| fc_type_vars ::= cons κ |>) (F <| fc_type_vars ::= cons (subst_kind sub_r sub_s κ) |>).
Proof.
  intros Hκok (Ht & Hm & Hr & Hs).
  split; [intros [|t] κ0 Heq | split; [|split]].
  - cbn in Heq |- *. injection Heq as <-.
    assert (Heq2 : subst_kind (up_type_representation sub_r) (up_type_size sub_s) κ
                  = subst_kind sub_r sub_s κ).
    { apply ext_kind; intros x; unfold up_type_representation, up_type_size, core.funcomp.
      - by rewrite rinstId'_representation.
      - by rewrite rinstId'_size. }
    rewrite Heq2.
    apply KVar; [done|]. rewrite fc_kind_ctx_ty_update.
    apply (kind_ok_subst sub_r sub_s (fc_kind_ctx F') (fc_kind_ctx F)); auto.
  - rewrite fc_type_vars_get_upd in Heq; cbn in Heq. cbn. unfold core.funcomp.
    assert (Heq3 : ren_kind unscoped.id unscoped.id (subst_kind sub_r sub_s κ0)
                 = subst_kind (up_type_representation sub_r) (up_type_size sub_s) κ0).
    { rewrite rinstId'_kind. apply ext_kind; intros x; unfold up_type_representation, up_type_size, core.funcomp.
      - by rewrite rinstId'_representation.
      - by rewrite rinstId'_size. }
    rewrite <- Heq3.
    apply (has_kind_ren _ _ _ (Ht t κ0 Heq) _ unscoped.id unscoped.id unscoped.id unscoped.shift).
    apply ctx_ren_weaken1.
  - intros m Hlt. rewrite fc_kind_ctx_ty_update; cbn; unfold up_type_memory, core.funcomp.
    apply (mem_ok_ren unscoped.id (fc_kind_ctx F) (fc_kind_ctx F));
      [intros i Hi; exact Hi | apply Hm; exact Hlt].
  - intros r Hlt. rewrite fc_kind_ctx_ty_update; cbn; unfold up_type_representation, core.funcomp.
    apply (rep_ok_ren unscoped.id (fc_kind_ctx F) (fc_kind_ctx F));
      [intros i Hi; exact Hi | apply Hr; exact Hlt].
  - intros s Hlt. rewrite fc_kind_ctx_ty_update; cbn; unfold up_type_size, core.funcomp.
    apply (size_ok_ren unscoped.id unscoped.id (fc_kind_ctx F) (fc_kind_ctx F));
      [intros i Hi; exact Hi | intros i Hi; exact Hi | apply Hs; exact Hlt].
Qed.

Lemma ctx_subst_exact_mem sub_m sub_r sub_s sub_t F' F :
  ctx_subst_exact sub_m sub_r sub_s sub_t F' F ->
  ctx_subst_exact (up_memory_memory sub_m) (up_memory_representation sub_r) (up_memory_size sub_s)
    (up_memory_type sub_t) (add_mem_var F') (add_mem_var F).
Proof.
  intros (Ht & Hm & Hr & Hs).
  split; [intros t κ0 Heq | split; [|split]].
  - unfold add_mem_var in Heq; cbn in Heq. unfold up_memory_type, core.funcomp.
    assert (Heq3 : ren_kind unscoped.id unscoped.id (subst_kind sub_r sub_s κ0)
                 = subst_kind (up_memory_representation sub_r) (up_memory_size sub_s) κ0).
    { rewrite rinstId'_kind. apply ext_kind; intros x; unfold up_memory_representation, up_memory_size, core.funcomp.
      - by rewrite rinstId'_representation.
      - by rewrite rinstId'_size. }
    rewrite <- Heq3.
    apply (has_kind_ren _ _ _ (Ht t κ0 Heq) _ unscoped.shift unscoped.id unscoped.id unscoped.id).
    apply ctx_ren_weaken_mem.
  - intros [|m] Hlt.
    + cbn; unfold up_memory_memory; cbn. apply OKVarM.
      unfold add_mem_var, unscoped.var_zero; destruct F, fc_kind_ctx; cbn; lia.
    + cbn; unfold up_memory_memory, core.funcomp; cbn.
      apply (mem_ok_ren unscoped.shift (fc_kind_ctx F) (fc_kind_ctx (add_mem_var F))).
      { unfold add_mem_var, unscoped.shift; destruct F, fc_kind_ctx; cbn; intros i Hi; lia. }
      apply Hm. unfold add_mem_var in Hlt; destruct F', fc_kind_ctx; cbn in Hlt |- *; lia.
  - intros r Hlt. unfold up_memory_representation, core.funcomp.
    apply (rep_ok_ren unscoped.id (fc_kind_ctx F) (fc_kind_ctx (add_mem_var F))).
    { unfold add_mem_var; destruct F, fc_kind_ctx; cbn; intros i Hi; exact Hi. }
    apply Hr. unfold add_mem_var in Hlt; destruct F', fc_kind_ctx; cbn in Hlt; exact Hlt.
  - intros s Hlt. unfold up_memory_size, core.funcomp.
    apply (size_ok_ren unscoped.id unscoped.id (fc_kind_ctx F) (fc_kind_ctx (add_mem_var F))).
    { unfold add_mem_var; destruct F, fc_kind_ctx; cbn; intros i Hi; exact Hi. }
    { unfold add_mem_var; destruct F, fc_kind_ctx; cbn; intros i Hi; exact Hi. }
    apply Hs. unfold add_mem_var in Hlt; destruct F', fc_kind_ctx; cbn in Hlt; exact Hlt.
Qed.

Lemma ctx_subst_exact_rep sub_m sub_r sub_s sub_t F' F :
  ctx_subst_exact sub_m sub_r sub_s sub_t F' F ->
  ctx_subst_exact (up_representation_memory sub_m) (up_representation_representation sub_r)
    (up_representation_size sub_s) (up_representation_type sub_t)
    (add_rep_var F') (add_rep_var F).
Proof.
  intros (Ht & Hm & Hr & Hs).
  split; [intros t κ0 Heq | split; [|split]].
  - unfold add_rep_var in Heq. rewrite fc_type_vars_get_upd in Heq. cbn in Heq.
    destruct F' as [? ? ? ? tvs]; cbn in Heq.
    rewrite list_lookup_fmap in Heq.
    destruct (tvs !! t) as [κ1|] eqn:E; cbn in Heq; [injection Heq as <-|discriminate].
    unfold up_representation_type, core.funcomp.
    (* [renSubst_kind]/[substRen_kind] (autosubst-generated) commute
       substitution past renaming in either order; combining both gives
       exactly the "lift a rep-substitution past a rep-shift" identity
       needed here (mirrors this session's discovery of the missing
       commutation lemma). *)
    assert (Heq3 : subst_kind (up_representation_representation sub_r) (up_representation_size sub_s)
                     (ren_kind unscoped.shift unscoped.id κ1)
                 = ren_kind unscoped.shift unscoped.id (subst_kind sub_r sub_s κ1)).
    { rewrite renSubst_kind. rewrite substRen_kind. reflexivity. }
    rewrite Heq3.
    eapply (has_kind_ren _ _ _ (Ht t κ1 E)).
    apply ctx_ren_weaken_rep.
  - intros m Hlt. unfold up_representation_memory, core.funcomp.
    apply (mem_ok_ren unscoped.id (fc_kind_ctx F) (fc_kind_ctx (add_rep_var F))).
    { unfold add_rep_var; destruct F, fc_kind_ctx; cbn; intros i Hi; exact Hi. }
    apply Hm. unfold add_rep_var in Hlt; destruct F', fc_kind_ctx; cbn in Hlt; exact Hlt.
  - intros [|r] Hlt.
    + cbn; unfold up_representation_representation; cbn. apply OKVarR.
      unfold add_rep_var, unscoped.var_zero; destruct F, fc_kind_ctx; cbn; lia.
    + cbn; unfold up_representation_representation, core.funcomp; cbn.
      apply (rep_ok_ren unscoped.shift (fc_kind_ctx F) (fc_kind_ctx (add_rep_var F))).
      { unfold add_rep_var, unscoped.shift; destruct F, fc_kind_ctx; cbn; intros i Hi; lia. }
      apply Hr. unfold add_rep_var in Hlt; destruct F', fc_kind_ctx; cbn in Hlt |- *; lia.
  - intros s Hlt. unfold up_representation_size, core.funcomp.
    apply (size_ok_ren unscoped.shift unscoped.id (fc_kind_ctx F) (fc_kind_ctx (add_rep_var F))).
    { unfold add_rep_var, unscoped.shift; destruct F, fc_kind_ctx; cbn; intros i Hi; lia. }
    { unfold add_rep_var; destruct F, fc_kind_ctx; cbn; intros i Hi; exact Hi. }
    apply Hs. unfold add_rep_var in Hlt; destruct F', fc_kind_ctx; cbn in Hlt; exact Hlt.
Qed.

(* Mirror image of [ctx_subst_exact_rep]: a size variable can't appear inside
   a representation, so [sub_r] passes through unchanged (like [sub_m] did
   for the rep case) and only [sub_s] gets the real shift-and-cons lift. *)
Lemma ctx_subst_exact_size sub_m sub_r sub_s sub_t F' F :
  ctx_subst_exact sub_m sub_r sub_s sub_t F' F ->
  ctx_subst_exact (up_size_memory sub_m) (up_size_representation sub_r)
    (up_size_size sub_s) (up_size_type sub_t)
    (add_size_var F') (add_size_var F).
Proof.
  intros (Ht & Hm & Hr & Hs).
  split; [intros t κ0 Heq | split; [|split]].
  - unfold add_size_var in Heq. rewrite fc_type_vars_get_upd in Heq. cbn in Heq.
    destruct F' as [? ? ? ? tvs]; cbn in Heq.
    rewrite list_lookup_fmap in Heq.
    destruct (tvs !! t) as [κ1|] eqn:E; cbn in Heq; [injection Heq as <-|discriminate].
    unfold up_size_type, core.funcomp.
    assert (Heq3 : subst_kind (up_size_representation sub_r) (up_size_size sub_s)
                     (ren_kind unscoped.id unscoped.shift κ1)
                 = ren_kind unscoped.id unscoped.shift (subst_kind sub_r sub_s κ1)).
    { rewrite renSubst_kind. rewrite substRen_kind. reflexivity. }
    rewrite Heq3.
    eapply (has_kind_ren _ _ _ (Ht t κ1 E)).
    apply ctx_ren_weaken_size.
  - intros m Hlt. unfold up_size_memory, core.funcomp.
    apply (mem_ok_ren unscoped.id (fc_kind_ctx F) (fc_kind_ctx (add_size_var F))).
    { unfold add_size_var; destruct F, fc_kind_ctx; cbn; intros i Hi; exact Hi. }
    apply Hm. unfold add_size_var in Hlt; destruct F', fc_kind_ctx; cbn in Hlt; exact Hlt.
  - intros r Hlt. unfold up_size_representation, core.funcomp.
    apply (rep_ok_ren unscoped.id (fc_kind_ctx F) (fc_kind_ctx (add_size_var F))).
    { unfold add_size_var; destruct F, fc_kind_ctx; cbn; intros i Hi; exact Hi. }
    apply Hr. unfold add_size_var in Hlt; destruct F', fc_kind_ctx; cbn in Hlt; exact Hlt.
  - intros [|s] Hlt.
    + cbn; unfold up_size_size; cbn. apply OKVarS.
      unfold add_size_var, unscoped.var_zero; destruct F, fc_kind_ctx; cbn; lia.
    + cbn; unfold up_size_size, core.funcomp; cbn.
      apply (size_ok_ren unscoped.id unscoped.shift (fc_kind_ctx F) (fc_kind_ctx (add_size_var F))).
      { unfold add_size_var; destruct F, fc_kind_ctx; cbn; intros i Hi; exact Hi. }
      { unfold add_size_var, unscoped.shift; destruct F, fc_kind_ctx; cbn; intros i Hi; lia. }
      apply Hs. unfold add_size_var in Hlt; destruct F', fc_kind_ctx; cbn in Hlt |- *; lia.
Qed.

Lemma Forall3_to_Forall_m {A B C} (P : A -> B -> C -> Prop) (Q : B -> Prop) l k k' :
  Forall3 P l k k' -> (forall x y z, P x y z -> Q y) -> Forall Q k.
Proof.
  intros H HPQ. induction H using Forall3_ind; constructor; eauto.
Qed.

(* Every kind that appears as the synthesized kind of *some* [has_kind]
   derivation is itself [kind_ok] -- [has_kind]'s own constructors don't
   carry this as an explicit premise everywhere ([KRec] notably doesn't),
   but it's always derivable via [has_kind_inv]/[has_kind_ok_kind_ok]. *)
Lemma has_kind_kind_ok F tau kappa : has_kind F tau kappa -> kind_ok (fc_kind_ctx F) kappa.
Proof.
  intros H.
  induction H using has_kind_ind' with (P0 := fun _ _ => True) (Pi := fun _ _ => True); cbn in *; auto.
  - apply OKVALTYPE; apply OKAtomR.
  - apply OKVALTYPE; apply OKAtomR.
  - apply OKVALTYPE; apply OKAtomR.
  - apply OKVALTYPE; apply OKAtomR.
  - apply OKVALTYPE; apply OKAtomR.
  - apply OKVALTYPE, OKSumR.
    eapply Forall3_to_Forall_m; [exact H|]. intros x y z Hk; inversion Hk; auto.
  - apply OKMEMTYPE, OKSumS.
    eapply Forall3_to_Forall_m; [exact H|]. intros x y z Hk; inversion Hk; auto.
  - apply OKVALTYPE, OKProdR.
    eapply Forall3_to_Forall_m; [exact H|]. intros x y z Hk; inversion Hk; auto.
  - apply OKMEMTYPE, OKProdS.
    eapply Forall3_to_Forall_m; [exact H|]. intros x y z Hk; inversion Hk; auto.
  - apply OKVALTYPE; apply OKAtomR.
  - apply OKVALTYPE; apply OKAtomR.
  - apply OKVALTYPE; apply OKAtomR.
  - apply OKVALTYPE; apply OKAtomR.
  - apply OKMEMTYPE, OKRepS. inversion IHhas_kind; auto.
  - apply OKVALTYPE; exact H.
  - apply OKMEMTYPE; exact H.
Qed.

(* The fully general substitution lemma for [has_kind]/[has_kind_ift]/
   [has_kind_ft]: if [F] is exactly substitution-compatible with [F']
   ([ctx_subst_exact]), substitution commutes with kind synthesis. Proved by
   strengthening the induction to also carry the *un-substituted* [has_kind]
   fact at every node ([has_kind_subst_exact_aux]) -- this is what lets the
   [KRec]/[KCodeRef]/etc. cases reconstruct a raw fact to feed
   [has_kind_kind_ok] or replay a constructor, since [has_kind_ind']'s own
   motive doesn't retain it. *)
Lemma has_kind_subst_exact_aux F tau kappa :
  has_kind F tau kappa ->
  has_kind F tau kappa /\
  (forall F' sub_m sub_r sub_s sub_t,
    (forall n, sub_m n = VarM n) ->
    ctx_subst_exact sub_m sub_r sub_s sub_t F F' ->
    has_kind F' (subst_type sub_m sub_r sub_s sub_t tau) (subst_kind sub_r sub_s kappa)).
Proof.
  intros H.
  induction H using has_kind_ind'
    with (P0 := fun F ϕ => has_kind_ft F ϕ /\
                  forall F' sub_m sub_r sub_s sub_t,
                  (forall n, sub_m n = VarM n) ->
                  ctx_subst_exact sub_m sub_r sub_s sub_t F F' ->
                  has_kind_ft F' (subst_function_type sub_m sub_r sub_s sub_t ϕ))
         (Pi := fun F ϕ => has_kind_ift F ϕ /\
                  forall F' sub_m sub_r sub_s sub_t,
                  (forall n, sub_m n = VarM n) ->
                  ctx_subst_exact sub_m sub_r sub_s sub_t F F' ->
                  has_kind_ift F' (subst_inner_function_type sub_m sub_r sub_s sub_t ϕ));
    try split.
  - constructor.
  - intros; cbn; constructor.
  - constructor.
  - intros; cbn; constructor.
  - constructor.
  - intros; cbn; constructor.
  - constructor.
  - intros; cbn; constructor.
  - constructor.
  - intros; cbn; constructor.
  - apply KSum. eapply Forall3_impl; [exact H|]. intros x y z Hxyz. exact (proj1 Hxyz).
  - intros F' sub_m sub_r sub_s sub_t Hsm Hctx.
    apply KSum, Forall3_map_lm, (Forall3_impl _ _ _ _ _ H).
    intros x y z Hxyz. exact (proj2 Hxyz F' sub_m sub_r sub_s sub_t Hsm Hctx).
  - apply KVariant. eapply Forall3_impl; [exact H|]. intros x y z Hxyz. exact (proj1 Hxyz).
  - intros F' sub_m sub_r sub_s sub_t Hsm Hctx.
    apply KVariant, Forall3_map_lm, (Forall3_impl _ _ _ _ _ H).
    intros x y z Hxyz. exact (proj2 Hxyz F' sub_m sub_r sub_s sub_t Hsm Hctx).
  - apply KProd. eapply Forall3_impl; [exact H|]. intros x y z Hxyz. exact (proj1 Hxyz).
  - intros F' sub_m sub_r sub_s sub_t Hsm Hctx.
    apply KProd, Forall3_map_lm, (Forall3_impl _ _ _ _ _ H).
    intros x y z Hxyz. exact (proj2 Hxyz F' sub_m sub_r sub_s sub_t Hsm Hctx).
  - apply KStruct. eapply Forall3_impl; [exact H|]. intros x y z Hxyz. exact (proj1 Hxyz).
  - intros F' sub_m sub_r sub_s sub_t Hsm Hctx.
    apply KStruct, Forall3_map_lm, (Forall3_impl _ _ _ _ _ H).
    intros x y z Hxyz. exact (proj2 Hxyz F' sub_m sub_r sub_s sub_t Hsm Hctx).
  - apply (KRefVar _ _ _ _ σ ξ); [exact H | exact (proj1 IHhas_kind)].
  - intros F' sub_m sub_r sub_s sub_t Hsm Hctx. cbn. rewrite (Hsm m). apply (KRefVar _ _ _ _ (subst_size sub_r sub_s σ) ξ).
    + rewrite <- (Hsm m). destruct Hctx as (Ht & Hm & Hr & Hs). apply Hm. inversion H; subst; done.
    + exact (proj2 IHhas_kind F' sub_m sub_r sub_s sub_t Hsm Hctx).
  - apply (KRefMM _ _ _ σ ξ). exact (proj1 IHhas_kind).
  - intros F' sub_m sub_r sub_s sub_t Hsm Hctx. cbn. apply (KRefMM _ _ _ (subst_size sub_r sub_s σ) ξ). exact (proj2 IHhas_kind F' sub_m sub_r sub_s sub_t Hsm Hctx).
  - apply (KRefGC _ _ _ σ ξ). exact (proj1 IHhas_kind).
  - intros F' sub_m sub_r sub_s sub_t Hsm Hctx. cbn. apply (KRefGC _ _ _ (subst_size sub_r sub_s σ) ξ). exact (proj2 IHhas_kind F' sub_m sub_r sub_s sub_t Hsm Hctx).
  - apply KCodeRef. exact (proj1 IHhas_kind).
  - intros F' sub_m sub_r sub_s sub_t Hsm Hctx. cbn. apply KCodeRef. exact (proj2 IHhas_kind F' sub_m sub_r sub_s sub_t Hsm Hctx).
  - apply (KSer _ _ ρ ξ). exact (proj1 IHhas_kind).
  - intros F' sub_m sub_r sub_s sub_t Hsm Hctx. cbn. apply (KSer _ _ (subst_representation sub_r ρ) ξ). exact (proj2 IHhas_kind F' sub_m sub_r sub_s sub_t Hsm Hctx).
  - apply KPlug. exact H.
  - intros F' sub_m sub_r sub_s sub_t Hsm Hctx. cbn. apply KPlug.
    destruct Hctx as (Ht & Hm & Hr & Hs). apply (rep_ok_subst sub_r (fc_kind_ctx F) (fc_kind_ctx F')); auto.
  - apply KSpan. exact H.
  - intros F' sub_m sub_r sub_s sub_t Hsm Hctx. cbn. apply KSpan.
    destruct Hctx as (Ht & Hm & Hr & Hs). apply (size_ok_subst sub_r sub_s (fc_kind_ctx F) (fc_kind_ctx F')); auto.
  - apply KRec. exact (proj1 IHhas_kind).
  - intros F' sub_m sub_r sub_s sub_t Hsm Hctx. cbn.
    assert (Heq2 : subst_kind (up_type_representation sub_r) (up_type_size sub_s) κ = subst_kind sub_r sub_s κ).
    { apply ext_kind; intros x; unfold up_type_representation, up_type_size, core.funcomp.
      - by rewrite rinstId'_representation.
      - by rewrite rinstId'_size. }
    assert (Hkok : kind_ok (fc_kind_ctx F) κ).
    { pose proof (has_kind_kind_ok _ _ _ (proj1 IHhas_kind)) as Hk.
      rewrite fc_kind_ctx_ty_update in Hk. exact Hk. }
    assert (Hgoal : has_kind (F' <| fc_type_vars ::= cons (subst_kind sub_r sub_s κ) |>)
                      (subst_type (up_type_memory sub_m) (up_type_representation sub_r) (up_type_size sub_s) (up_type_type sub_t) τ)
                      (subst_kind (up_type_representation sub_r) (up_type_size sub_s) κ)).
    { apply (proj2 IHhas_kind (F' <| fc_type_vars ::= cons (subst_kind sub_r sub_s κ) |>)
               (up_type_memory sub_m) (up_type_representation sub_r) (up_type_size sub_s) (up_type_type sub_t)).
      - intros n. unfold up_type_memory, core.funcomp. rewrite Hsm. done.
      - apply (ctx_subst_exact_cons sub_m sub_r sub_s sub_t F F' κ Hkok Hctx). }
    rewrite Heq2 in Hgoal.
    apply KRec. exact Hgoal.
  - apply KExistsMem; [exact H | exact (proj1 IHhas_kind)].
  - intros F' sub_m sub_r sub_s sub_t Hsm Hctx. cbn. apply KExistsMem.
    + destruct Hctx as (Ht & Hm & Hr & Hs). apply (kind_ok_subst sub_r sub_s (fc_kind_ctx F) (fc_kind_ctx F')); auto.
    + assert (Heq2 : subst_kind (up_memory_representation sub_r) (up_memory_size sub_s) κ = subst_kind sub_r sub_s κ).
      { apply ext_kind; intros x; unfold up_memory_representation, up_memory_size, core.funcomp.
        - by rewrite rinstId'_representation.
        - by rewrite rinstId'_size. }
      rewrite <- Heq2.
      apply (proj2 IHhas_kind (F' <| fc_kind_ctx ::= set kc_mem_vars S |>)
               (up_memory_memory sub_m) (up_memory_representation sub_r) (up_memory_size sub_s) (up_memory_type sub_t)).
      * intros n. unfold up_memory_memory. destruct n; cbn; [done|]. unfold core.funcomp. rewrite Hsm. done.
      * apply (ctx_subst_exact_mem sub_m sub_r sub_s sub_t F F' Hctx).
  - apply KExistsRep; [exact H | exact (proj1 IHhas_kind)].
  - intros F' sub_m sub_r sub_s sub_t Hsm Hctx. cbn. apply KExistsRep.
    + destruct Hctx as (Ht & Hm & Hr & Hs). apply (kind_ok_subst sub_r sub_s (fc_kind_ctx F) (fc_kind_ctx F')); auto.
    + assert (Heq3 : subst_kind (up_representation_representation sub_r) (up_representation_size sub_s)
                       (ren_kind unscoped.shift unscoped.id κ)
                   = ren_kind unscoped.shift unscoped.id (subst_kind sub_r sub_s κ)).
      { rewrite renSubst_kind. rewrite substRen_kind. reflexivity. }
      rewrite <- Heq3.
      apply (proj2 IHhas_kind (add_rep_var F')
               (up_representation_memory sub_m) (up_representation_representation sub_r) (up_representation_size sub_s) (up_representation_type sub_t)).
      * intros n. unfold up_representation_memory, core.funcomp. rewrite Hsm. done.
      * apply (ctx_subst_exact_rep sub_m sub_r sub_s sub_t F F' Hctx).
  - apply KExistsSize; [exact H | exact (proj1 IHhas_kind)].
  - intros F' sub_m sub_r sub_s sub_t Hsm Hctx. cbn. apply KExistsSize.
    + destruct Hctx as (Ht & Hm & Hr & Hs). apply (kind_ok_subst sub_r sub_s (fc_kind_ctx F) (fc_kind_ctx F')); auto.
    + assert (Heq3 : subst_kind (up_size_representation sub_r) (up_size_size sub_s)
                       (ren_kind unscoped.id unscoped.shift κ)
                   = ren_kind unscoped.id unscoped.shift (subst_kind sub_r sub_s κ)).
      { rewrite renSubst_kind. rewrite substRen_kind. reflexivity. }
      rewrite <- Heq3.
      apply (proj2 IHhas_kind (add_size_var F')
               (up_size_memory sub_m) (up_size_representation sub_r) (up_size_size sub_s) (up_size_type sub_t)).
      * intros n. unfold up_size_memory, core.funcomp. rewrite Hsm. done.
      * apply (ctx_subst_exact_size sub_m sub_r sub_s sub_t F F' Hctx).
  - apply KExistsType; [exact H | exact H0 | exact (proj1 IHhas_kind)].
  - intros F' sub_m sub_r sub_s sub_t Hsm Hctx. cbn.
    assert (Heq2 : subst_kind (up_type_representation sub_r) (up_type_size sub_s) κ = subst_kind sub_r sub_s κ).
    { apply ext_kind; intros x; unfold up_type_representation, up_type_size, core.funcomp.
      - by rewrite rinstId'_representation.
      - by rewrite rinstId'_size. }
    assert (Hgoal : has_kind (F' <| fc_type_vars ::= cons (subst_kind sub_r sub_s κ0) |>)
                      (subst_type (up_type_memory sub_m) (up_type_representation sub_r) (up_type_size sub_s) (up_type_type sub_t) τ)
                      (subst_kind (up_type_representation sub_r) (up_type_size sub_s) κ)).
    { apply (proj2 IHhas_kind (F' <| fc_type_vars ::= cons (subst_kind sub_r sub_s κ0) |>)
               (up_type_memory sub_m) (up_type_representation sub_r) (up_type_size sub_s) (up_type_type sub_t)).
      - intros n. unfold up_type_memory, core.funcomp. rewrite Hsm. done.
      - apply (ctx_subst_exact_cons sub_m sub_r sub_s sub_t F F' κ0 H Hctx). }
    rewrite Heq2 in Hgoal.
    destruct Hctx as (Ht & Hm & Hr & Hs).
    apply KExistsType.
    + apply (kind_ok_subst sub_r sub_s (fc_kind_ctx F) (fc_kind_ctx F')); auto.
    + apply (kind_ok_subst sub_r sub_s (fc_kind_ctx F) (fc_kind_ctx F')); auto.
    + exact Hgoal.
  - apply KVar; [exact H | exact H0].
  - intros F' sub_m sub_r sub_s sub_t Hsm Hctx. cbn. destruct Hctx as (Ht & Hm & Hr & Hs). apply Ht. exact H.
  - apply (KMonoFun _ _ _ κs1 κs2).
    + apply (Forall2_impl _ _ _ _ H); intros x y Hxy; exact (proj1 Hxy).
    + apply (Forall2_impl _ _ _ _ H0); intros x y Hxy; exact (proj1 Hxy).
  - intros F' sub_m sub_r sub_s sub_t Hsm Hctx. cbn.
    apply (KMonoFun _ _ _ (map (subst_kind sub_r sub_s) κs1) (map (subst_kind sub_r sub_s) κs2)).
    + apply Forall2_fmap, (Forall2_impl _ _ _ _ H); intros x y Hxy; exact (proj2 Hxy F' sub_m sub_r sub_s sub_t Hsm Hctx).
    + apply Forall2_fmap, (Forall2_impl _ _ _ _ H0); intros x y Hxy; exact (proj2 Hxy F' sub_m sub_r sub_s sub_t Hsm Hctx).
  - apply KInnerFun. exact (proj1 IHhas_kind).
  - intros F' sub_m sub_r sub_s sub_t Hsm Hctx. cbn. apply KInnerFun. exact (proj2 IHhas_kind F' sub_m sub_r sub_s sub_t Hsm Hctx).
  - apply KForallMem. exact (proj1 IHhas_kind).
  - intros F' sub_m sub_r sub_s sub_t Hsm Hctx. cbn. apply KForallMem.
    apply (proj2 IHhas_kind (F' <| fc_kind_ctx ::= set kc_mem_vars S |>)
             (up_memory_memory sub_m) (up_memory_representation sub_r) (up_memory_size sub_s) (up_memory_type sub_t)).
    + intros n. unfold up_memory_memory. destruct n; cbn; [done|]. unfold core.funcomp. rewrite Hsm. done.
    + apply (ctx_subst_exact_mem sub_m sub_r sub_s sub_t F F' Hctx).
  - apply KForallRep. exact (proj1 IHhas_kind).
  - intros F' sub_m sub_r sub_s sub_t Hsm Hctx. cbn. apply KForallRep.
    apply (proj2 IHhas_kind (add_rep_var F')
             (up_representation_memory sub_m) (up_representation_representation sub_r) (up_representation_size sub_s) (up_representation_type sub_t)).
    + intros n. unfold up_representation_memory, core.funcomp. rewrite Hsm. done.
    + apply (ctx_subst_exact_rep sub_m sub_r sub_s sub_t F F' Hctx).
  - apply KForallSize. exact (proj1 IHhas_kind).
  - intros F' sub_m sub_r sub_s sub_t Hsm Hctx. cbn. apply KForallSize.
    apply (proj2 IHhas_kind (add_size_var F')
             (up_size_memory sub_m) (up_size_representation sub_r) (up_size_size sub_s) (up_size_type sub_t)).
    + intros n. unfold up_size_memory, core.funcomp. rewrite Hsm. done.
    + apply (ctx_subst_exact_size sub_m sub_r sub_s sub_t F F' Hctx).
  - apply KForallType; [exact H | exact (proj1 IHhas_kind)].
  - intros F' sub_m sub_r sub_s sub_t Hsm Hctx. cbn. apply KForallType.
    + destruct Hctx as (Ht & Hm & Hr & Hs). apply (kind_ok_subst sub_r sub_s (fc_kind_ctx F) (fc_kind_ctx F')); auto.
    + apply (proj2 IHhas_kind (F' <| fc_type_vars ::= cons (subst_kind sub_r sub_s κ) |>)
               (up_type_memory sub_m) (up_type_representation sub_r) (up_type_size sub_s) (up_type_type sub_t)).
      * intros n. unfold up_type_memory, core.funcomp. rewrite Hsm. done.
      * apply (ctx_subst_exact_cons sub_m sub_r sub_s sub_t F F' κ H Hctx).
Qed.

Lemma has_kind_subst_exact F τ κ :
  has_kind F τ κ ->
  forall F' sub_m sub_r sub_s sub_t,
  (forall n, sub_m n = VarM n) ->
  ctx_subst_exact sub_m sub_r sub_s sub_t F F' ->
  has_kind F' (subst_type sub_m sub_r sub_s sub_t τ) (subst_kind sub_r sub_s κ).
Proof.
  intros H F' sub_m sub_r sub_s sub_t Hsm Hctx.
  exact (proj2 (has_kind_subst_exact_aux F τ κ H) F' sub_m sub_r sub_s sub_t Hsm Hctx).
Qed.

(* [has_kind_subst_exact] alone isn't enough for [RecT]'s self-substitution:
   its [ctx_subst_exact] hypothesis demands a [has_kind] witness for *every*
   type variable already in scope, not just the one actually being replaced
   -- and [has_kind]'s [KVar] rule checks [kind_ok] locally (at the lookup),
   so there is no invariant that an arbitrary [F]'s *other*, untouched type
   variables are individually well-kinded (leaf rules like [KI31] impose no
   constraint on [F] at all). So a *single-variable* substitution lemma is
   built separately below, tracking the substituted position as an explicit
   depth [d] rather than going through [ctx_subst_exact] -- its [KVar] case
   then only ever needs the [kind_ok] evidence already attached to the
   *current* variable-lookup node, never a fact about unrelated variables. *)

(* [ctx_subst_rec d kw F0 F] says [F0]'s type-variable list is exactly [F]'s
   with [kw] inserted at position [d] -- purely structural (a list-lookup
   equation), so unlike [ctx_subst_exact] it carries no [has_kind]/[kind_ok]
   content and needs no side condition to extend across a binder. *)
Definition ctx_subst_rec (d : nat) (kw : kind) (F0 F : function_ctx) : Prop :=
  fc_kind_ctx F0 = fc_kind_ctx F /\
  fc_type_vars F0 !! d = Some kw /\
  (forall t, t < d -> fc_type_vars F0 !! t = fc_type_vars F !! t) /\
  (forall t, fc_type_vars F0 !! (S (d + t)) = fc_type_vars F !! (d + t)).

Lemma ctx_subst_rec_base kw F :
  ctx_subst_rec 0 kw (F <| fc_type_vars ::= cons kw |>) F.
Proof.
  repeat split.
  intros t Hlt; lia.
Qed.

Lemma ctx_subst_rec_cons d kw F0 F k1 :
  ctx_subst_rec d kw F0 F ->
  ctx_subst_rec (S d) kw (F0 <| fc_type_vars ::= cons k1 |>) (F <| fc_type_vars ::= cons k1 |>).
Proof.
  intros (Hk & Hd & Hlt & Hge).
  repeat split.
  - by rewrite !fc_kind_ctx_ty_update.
  - by rewrite fc_type_vars_get_upd.
  - intros [|t] Ht; cbn; [done|]. rewrite !fc_type_vars_get_upd. apply Hlt. lia.
  - intros t. cbn. rewrite !fc_type_vars_get_upd. apply Hge.
Qed.

Lemma ctx_subst_rec_mem d kw F0 F :
  ctx_subst_rec d kw F0 F ->
  ctx_subst_rec d kw (add_mem_var F0) (add_mem_var F).
Proof.
  intros (Hk & Hd & Hlt & Hge).
  unfold add_mem_var.
  repeat split; cbn; auto.
  destruct F0, F; cbn in *; f_equal; exact Hk.
Qed.

Lemma ctx_subst_rec_rep d kw F0 F :
  ctx_subst_rec d kw F0 F ->
  ctx_subst_rec d (ren_kind unscoped.shift unscoped.id kw) (add_rep_var F0) (add_rep_var F).
Proof.
  intros (Hk & Hd & Hlt & Hge).
  unfold add_rep_var.
  repeat split; cbn.
  - destruct F0, F; cbn in *; f_equal; exact Hk.
  - rewrite list_lookup_fmap Hd. done.
  - intros t Ht. rewrite !list_lookup_fmap Hlt; [done|exact Ht].
  - intros t. rewrite !list_lookup_fmap Hge. done.
Qed.

Lemma ctx_subst_rec_size d kw F0 F :
  ctx_subst_rec d kw F0 F ->
  ctx_subst_rec d (ren_kind unscoped.id unscoped.shift kw) (add_size_var F0) (add_size_var F).
Proof.
  intros (Hk & Hd & Hlt & Hge).
  unfold add_size_var.
  repeat split; cbn.
  - destruct F0, F; cbn in *; f_equal; exact Hk.
  - rewrite list_lookup_fmap Hd. done.
  - intros t Ht. rewrite !list_lookup_fmap Hlt; [done|exact Ht].
  - intros t. rewrite !list_lookup_fmap Hge. done.
Qed.

(* [subst_rec_ok d w sub_t] says [sub_t] is exactly "substitute the type
   variable at depth [d] with [w], leave every other variable as itself" --
   again purely structural, matching [ctx_subst_rec]'s shape one binder at a
   time as [sub_t] gets lifted via [up_X_type]. *)
Definition subst_rec_ok (d : nat) (w : type) (sub_t : nat -> type) : Prop :=
  sub_t d = w /\
  (forall t, t < d -> sub_t t = VarT t) /\
  (forall t, sub_t (S (d + t)) = VarT (d + t)).

Lemma subst_rec_ok_base w :
  subst_rec_ok 0 w (unscoped.scons w VarT).
Proof.
  repeat split.
  intros t Hlt; lia.
Qed.

Lemma subst_rec_ok_cons d w sub_t :
  subst_rec_ok d w sub_t ->
  subst_rec_ok (S d) (ren_type unscoped.id unscoped.id unscoped.id unscoped.shift w) (up_type_type sub_t).
Proof.
  intros (Hd & Hlt & Hge).
  unfold up_type_type, core.funcomp.
  repeat split.
  - cbn. by rewrite Hd.
  - intros [|t] Ht; [done|]. cbn. rewrite Hlt; [done|lia].
  - intros t. cbn. rewrite Hge. done.
Qed.

Lemma subst_rec_ok_mem d w sub_t :
  subst_rec_ok d w sub_t ->
  subst_rec_ok d (ren_type unscoped.shift unscoped.id unscoped.id unscoped.id w) (up_memory_type sub_t).
Proof.
  intros (Hd & Hlt & Hge).
  unfold up_memory_type, core.funcomp.
  repeat split.
  - by rewrite Hd.
  - intros t Ht. rewrite Hlt; [done|exact Ht].
  - intros t. rewrite Hge. done.
Qed.

Lemma subst_rec_ok_rep d w sub_t :
  subst_rec_ok d w sub_t ->
  subst_rec_ok d (ren_type unscoped.id unscoped.shift unscoped.id unscoped.id w) (up_representation_type sub_t).
Proof.
  intros (Hd & Hlt & Hge).
  unfold up_representation_type, core.funcomp.
  repeat split.
  - by rewrite Hd.
  - intros t Ht. rewrite Hlt; [done|exact Ht].
  - intros t. rewrite Hge. done.
Qed.

Lemma subst_rec_ok_size d w sub_t :
  subst_rec_ok d w sub_t ->
  subst_rec_ok d (ren_type unscoped.id unscoped.id unscoped.shift unscoped.id w) (up_size_type sub_t).
Proof.
  intros (Hd & Hlt & Hge).
  unfold up_size_type, core.funcomp.
  repeat split.
  - by rewrite Hd.
  - intros t Ht. rewrite Hlt; [done|exact Ht].
  - intros t. rewrite Hge. done.
Qed.

Lemma Forall3_map_l {A B C A'} (f : A -> A') (P : A' -> B -> C -> Prop) l k k' :
  Forall3 (fun x y z => P (f x) y z) l k k' -> Forall3 P (map f l) k k'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma has_kind_single_subst_aux F0 τ κ :
  has_kind F0 τ κ ->
  forall d kw w Ftgt sub_m sub_r sub_s sub_t,
  (forall n, sub_m n = VarM n) ->
  (forall n, sub_r n = VarR n) ->
  (forall n, sub_s n = VarS n) ->
  subst_rec_ok d w sub_t ->
  ctx_subst_rec d kw F0 Ftgt ->
  has_kind Ftgt w kw ->
  has_kind Ftgt (subst_type sub_m sub_r sub_s sub_t τ) κ.
Proof.
  intros H.
  induction H using has_kind_ind'
    with (P0 := fun G ϕ => forall d kw w Ftgt sub_m sub_r sub_s sub_t,
                  (forall n, sub_m n = VarM n) -> (forall n, sub_r n = VarR n) -> (forall n, sub_s n = VarS n) ->
                  subst_rec_ok d w sub_t -> ctx_subst_rec d kw G Ftgt -> has_kind Ftgt w kw ->
                  has_kind_ft Ftgt (subst_function_type sub_m sub_r sub_s sub_t ϕ))
         (Pi := fun G ϕ => forall d kw w Ftgt sub_m sub_r sub_s sub_t,
                  (forall n, sub_m n = VarM n) -> (forall n, sub_r n = VarR n) -> (forall n, sub_s n = VarS n) ->
                  subst_rec_ok d w sub_t -> ctx_subst_rec d kw G Ftgt -> has_kind Ftgt w kw ->
                  has_kind_ift Ftgt (subst_inner_function_type sub_m sub_r sub_s sub_t ϕ));
    intros d kw w Ftgt sub_m sub_r sub_s sub_t Hsm Hsr Hss Hwt Hctx Hw; cbn.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - apply KSum, Forall3_map_l, (Forall3_impl _ _ _ _ _ H); intros x y z Hxyz; exact (Hxyz d kw w Ftgt sub_m sub_r sub_s sub_t Hsm Hsr Hss Hwt Hctx Hw).
  - apply KVariant, Forall3_map_l, (Forall3_impl _ _ _ _ _ H); intros x y z Hxyz; exact (Hxyz d kw w Ftgt sub_m sub_r sub_s sub_t Hsm Hsr Hss Hwt Hctx Hw).
  - apply KProd, Forall3_map_l, (Forall3_impl _ _ _ _ _ H); intros x y z Hxyz; exact (Hxyz d kw w Ftgt sub_m sub_r sub_s sub_t Hsm Hsr Hss Hwt Hctx Hw).
  - apply KStruct, Forall3_map_l, (Forall3_impl _ _ _ _ _ H); intros x y z Hxyz; exact (Hxyz d kw w Ftgt sub_m sub_r sub_s sub_t Hsm Hsr Hss Hwt Hctx Hw).
  - rewrite (Hsm m).
    apply (KRefVar _ _ _ _ σ ξ).
    + rewrite <- (proj1 Hctx). exact H.
    + exact (IHhas_kind d kw w Ftgt sub_m sub_r sub_s sub_t Hsm Hsr Hss Hwt Hctx Hw).
  - apply (KRefMM _ _ _ σ ξ). exact (IHhas_kind d kw w Ftgt sub_m sub_r sub_s sub_t Hsm Hsr Hss Hwt Hctx Hw).
  - apply (KRefGC _ _ _ σ ξ). exact (IHhas_kind d kw w Ftgt sub_m sub_r sub_s sub_t Hsm Hsr Hss Hwt Hctx Hw).
  - apply KCodeRef. exact (IHhas_kind d kw w Ftgt sub_m sub_r sub_s sub_t Hsm Hsr Hss Hwt Hctx Hw).
  - apply (KSer _ _ ρ ξ). exact (IHhas_kind d kw w Ftgt sub_m sub_r sub_s sub_t Hsm Hsr Hss Hwt Hctx Hw).
  - rewrite (ext_representation sub_r VarR Hsr ρ). rewrite instId'_representation.
    apply KPlug. destruct Hctx as (Hk & Hd & Hlt & Hge). rewrite <- Hk. exact H.
  - rewrite (ext_size sub_r sub_s VarR VarS Hsr Hss σ). rewrite instId'_size.
    apply KSpan. destruct Hctx as (Hk & Hd & Hlt & Hge). rewrite <- Hk. exact H.
  - rewrite (ext_kind sub_r sub_s VarR VarS Hsr Hss κ). rewrite instId'_kind.
    apply KRec.
    apply (IHhas_kind (S d) kw (ren_type unscoped.id unscoped.id unscoped.id unscoped.shift w) (Ftgt <| fc_type_vars ::= cons κ |>)
             (up_type_memory sub_m) (up_type_representation sub_r) (up_type_size sub_s) (up_type_type sub_t)).
    + exact (upId_type_memory sub_m Hsm).
    + exact (upId_type_representation sub_r Hsr).
    + exact (upId_type_size sub_s Hss).
    + exact (subst_rec_ok_cons d w sub_t Hwt).
    + exact (ctx_subst_rec_cons d kw F Ftgt κ Hctx).
    + pose proof (has_kind_ren _ _ _ Hw _ unscoped.id unscoped.id unscoped.id unscoped.shift (ctx_ren_weaken1 Ftgt κ)) as Hw'.
      rewrite rinstId'_kind in Hw'. exact Hw'.
  - rewrite (ext_kind sub_r sub_s VarR VarS Hsr Hss κ). rewrite instId'_kind.
    apply KExistsMem.
    + rewrite <- (proj1 Hctx). exact H.
    + apply (IHhas_kind d kw (ren_type unscoped.shift unscoped.id unscoped.id unscoped.id w) (add_mem_var Ftgt)
               (up_memory_memory sub_m) (up_memory_representation sub_r) (up_memory_size sub_s) (up_memory_type sub_t)).
      * exact (upId_memory_memory sub_m Hsm).
      * exact (upId_memory_representation sub_r Hsr).
      * exact (upId_memory_size sub_s Hss).
      * exact (subst_rec_ok_mem d w sub_t Hwt).
      * exact (ctx_subst_rec_mem d kw F Ftgt Hctx).
      * pose proof (has_kind_ren _ _ _ Hw _ unscoped.shift unscoped.id unscoped.id unscoped.id (ctx_ren_weaken_mem Ftgt)) as Hw'.
        rewrite rinstId'_kind in Hw'. exact Hw'.
  - rewrite (ext_kind sub_r sub_s VarR VarS Hsr Hss κ). rewrite instId'_kind.
    apply KExistsRep.
    + rewrite <- (proj1 Hctx). exact H.
    + apply (IHhas_kind d (ren_kind unscoped.shift unscoped.id kw) (ren_type unscoped.id unscoped.shift unscoped.id unscoped.id w) (add_rep_var Ftgt)
               (up_representation_memory sub_m) (up_representation_representation sub_r) (up_representation_size sub_s) (up_representation_type sub_t)).
      * exact (upId_representation_memory sub_m Hsm).
      * exact (upId_representation_representation sub_r Hsr).
      * exact (upId_representation_size sub_s Hss).
      * exact (subst_rec_ok_rep d w sub_t Hwt).
      * exact (ctx_subst_rec_rep d kw F Ftgt Hctx).
      * exact (has_kind_ren _ _ _ Hw _ unscoped.id unscoped.shift unscoped.id unscoped.id (ctx_ren_weaken_rep Ftgt)).
  - rewrite (ext_kind sub_r sub_s VarR VarS Hsr Hss κ). rewrite instId'_kind.
    apply KExistsSize.
    + rewrite <- (proj1 Hctx). exact H.
    + apply (IHhas_kind d (ren_kind unscoped.id unscoped.shift kw) (ren_type unscoped.id unscoped.id unscoped.shift unscoped.id w) (add_size_var Ftgt)
               (up_size_memory sub_m) (up_size_representation sub_r) (up_size_size sub_s) (up_size_type sub_t)).
      * exact (upId_size_memory sub_m Hsm).
      * exact (upId_size_representation sub_r Hsr).
      * exact (upId_size_size sub_s Hss).
      * exact (subst_rec_ok_size d w sub_t Hwt).
      * exact (ctx_subst_rec_size d kw F Ftgt Hctx).
      * exact (has_kind_ren _ _ _ Hw _ unscoped.id unscoped.id unscoped.shift unscoped.id (ctx_ren_weaken_size Ftgt)).
  - rewrite (ext_kind sub_r sub_s VarR VarS Hsr Hss κ). rewrite (ext_kind sub_r sub_s VarR VarS Hsr Hss κ0). rewrite !instId'_kind.
    apply KExistsType.
    + rewrite <- (proj1 Hctx). exact H.
    + rewrite <- (proj1 Hctx). exact H0.
    + apply (IHhas_kind (S d) kw (ren_type unscoped.id unscoped.id unscoped.id unscoped.shift w) (Ftgt <| fc_type_vars ::= cons κ0 |>)
               (up_type_memory sub_m) (up_type_representation sub_r) (up_type_size sub_s) (up_type_type sub_t)).
      * exact (upId_type_memory sub_m Hsm).
      * exact (upId_type_representation sub_r Hsr).
      * exact (upId_type_size sub_s Hss).
      * exact (subst_rec_ok_cons d w sub_t Hwt).
      * exact (ctx_subst_rec_cons d kw F Ftgt κ0 Hctx).
      * pose proof (has_kind_ren _ _ _ Hw _ unscoped.id unscoped.id unscoped.id unscoped.shift (ctx_ren_weaken1 Ftgt κ0)) as Hw'.
        rewrite rinstId'_kind in Hw'. exact Hw'.
  - destruct Hctx as (Hk & Hd & Hlt & Hge). destruct Hwt as (Hwd & Hwlt & Hwge).
    destruct (lt_eq_lt_dec t d) as [[Htlt|Heqd]|Htgt].
    + rewrite (Hwlt t Htlt). apply KVar.
      * rewrite <- (Hlt t Htlt). exact H.
      * rewrite <- Hk. exact H0.
    + subst t. rewrite Hwd. rewrite Hd in H. injection H as <-. exact Hw.
    + assert (Hex : exists t', t = S (d + t')).
      { exists (t - d - 1). lia. }
      destruct Hex as [t' ->].
      rewrite (Hwge t'). apply KVar.
      * rewrite <- (Hge t'). exact H.
      * rewrite <- Hk. exact H0.
  - apply (KMonoFun _ _ _ κs1 κs2).
    + apply Forall2_fmap_l, (Forall2_impl _ _ _ _ H); intros x y Hxy; exact (Hxy d kw w Ftgt sub_m sub_r sub_s sub_t Hsm Hsr Hss Hwt Hctx Hw).
    + apply Forall2_fmap_l, (Forall2_impl _ _ _ _ H0); intros x y Hxy; exact (Hxy d kw w Ftgt sub_m sub_r sub_s sub_t Hsm Hsr Hss Hwt Hctx Hw).
  - apply KInnerFun. exact (IHhas_kind d kw w Ftgt sub_m sub_r sub_s sub_t Hsm Hsr Hss Hwt Hctx Hw).
  - apply KForallMem.
    apply (IHhas_kind d kw (ren_type unscoped.shift unscoped.id unscoped.id unscoped.id w) (add_mem_var Ftgt)
             (up_memory_memory sub_m) (up_memory_representation sub_r) (up_memory_size sub_s) (up_memory_type sub_t)).
    + exact (upId_memory_memory sub_m Hsm).
    + exact (upId_memory_representation sub_r Hsr).
    + exact (upId_memory_size sub_s Hss).
    + exact (subst_rec_ok_mem d w sub_t Hwt).
    + exact (ctx_subst_rec_mem d kw F Ftgt Hctx).
    + pose proof (has_kind_ren _ _ _ Hw _ unscoped.shift unscoped.id unscoped.id unscoped.id (ctx_ren_weaken_mem Ftgt)) as Hw'.
      rewrite rinstId'_kind in Hw'. exact Hw'.
  - apply KForallRep.
    apply (IHhas_kind d (ren_kind unscoped.shift unscoped.id kw) (ren_type unscoped.id unscoped.shift unscoped.id unscoped.id w) (add_rep_var Ftgt)
             (up_representation_memory sub_m) (up_representation_representation sub_r) (up_representation_size sub_s) (up_representation_type sub_t)).
    + exact (upId_representation_memory sub_m Hsm).
    + exact (upId_representation_representation sub_r Hsr).
    + exact (upId_representation_size sub_s Hss).
    + exact (subst_rec_ok_rep d w sub_t Hwt).
    + exact (ctx_subst_rec_rep d kw F Ftgt Hctx).
    + exact (has_kind_ren _ _ _ Hw _ unscoped.id unscoped.shift unscoped.id unscoped.id (ctx_ren_weaken_rep Ftgt)).
  - apply KForallSize.
    apply (IHhas_kind d (ren_kind unscoped.id unscoped.shift kw) (ren_type unscoped.id unscoped.id unscoped.shift unscoped.id w) (add_size_var Ftgt)
             (up_size_memory sub_m) (up_size_representation sub_r) (up_size_size sub_s) (up_size_type sub_t)).
    + exact (upId_size_memory sub_m Hsm).
    + exact (upId_size_representation sub_r Hsr).
    + exact (upId_size_size sub_s Hss).
    + exact (subst_rec_ok_size d w sub_t Hwt).
    + exact (ctx_subst_rec_size d kw F Ftgt Hctx).
    + exact (has_kind_ren _ _ _ Hw _ unscoped.id unscoped.id unscoped.shift unscoped.id (ctx_ren_weaken_size Ftgt)).
  - rewrite (ext_kind sub_r sub_s VarR VarS Hsr Hss κ). rewrite instId'_kind.
    apply KForallType.
    + rewrite <- (proj1 Hctx). exact H.
    + apply (IHhas_kind (S d) kw (ren_type unscoped.id unscoped.id unscoped.id unscoped.shift w) (Ftgt <| fc_type_vars ::= cons κ |>)
               (up_type_memory sub_m) (up_type_representation sub_r) (up_type_size sub_s) (up_type_type sub_t)).
      * exact (upId_type_memory sub_m Hsm).
      * exact (upId_type_representation sub_r Hsr).
      * exact (upId_type_size sub_s Hss).
      * exact (subst_rec_ok_cons d w sub_t Hwt).
      * exact (ctx_subst_rec_cons d kw F Ftgt κ Hctx).
      * pose proof (has_kind_ren _ _ _ Hw _ unscoped.id unscoped.id unscoped.id unscoped.shift (ctx_ren_weaken1 Ftgt κ)) as Hw'.
        rewrite rinstId'_kind in Hw'. exact Hw'.
Qed.

(* [RecT]'s kind is a genuine binder annotation (unlike the aggregate/self
   kinds that used to be cached on other constructors), so unfolding a
   recursive type via self-substitution preserves its kind without needing
   any "refresh" pass. Falls out of [has_kind_single_subst_aux] at depth 0
   with the identity memory/rep/size substitutions -- deliberately NOT
   derived from [has_kind_subst_exact]/[ctx_subst_exact], since that would
   need every one of [F]'s own pre-existing type variables to be
   individually [kind_ok], which nothing guarantees (see the comment above
   [ctx_subst_rec]). *)
Lemma has_kind_rec_subst :
  ∀ τ F κ, let τrec := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
           has_kind F (RecT κ τ) κ -> has_kind F τrec κ.
Proof.
  intros τ F κ Hrec H.
  inversion H; subst.
  apply (has_kind_single_subst_aux (F <| fc_type_vars ::= cons κ |>) τ κ H4 0 κ (RecT κ τ) F VarM VarR VarS (unscoped.scons (RecT κ τ) VarT)).
  - done.
  - done.
  - done.
  - exact (subst_rec_ok_base (RecT κ τ)).
  - exact (ctx_subst_rec_base κ F).
  - exact H.
Qed.

(* [function_type_inst]/[inner_function_type_inst] no longer need a
   [refreshed_kinds] side condition to relate the substituted function type
   back to its kinding -- substitution is kind-transparent now. What remains
   is an ordinary (but real) kind-substitution lemma. Left admitted; see
   [has_kind_rec_subst] above for the same situation on plain types. *)
Lemma has_kind_ift_through_inst_iff F ϕ ϕ' ix :
  inner_function_type_inst F ix ϕ ϕ' ->
  (has_kind_ift F ϕ <-> has_kind_ift F ϕ').
Proof.
Admitted.

Lemma has_kind_ft_through_inst_iff F ϕ ϕ' ix :
  function_type_inst F ix ϕ ϕ' ->
  (has_kind_ft F ϕ <-> has_kind_ft F ϕ').
Proof.
Admitted.

Lemma has_kind_ft_through_inst F ϕ ϕ' ix :
  function_type_inst F ix ϕ ϕ' ->
  has_kind_ft F ϕ ->
  has_kind_ft F ϕ'.
Proof.
  intros.
  by apply (has_kind_ft_through_inst_iff F ϕ ϕ' ix H).
Qed.

Lemma has_kind_ft_through_inst_backwards F ϕ ϕ' ix :
  function_type_inst F ix ϕ ϕ' ->
  has_kind_ft F ϕ' ->
  has_kind_ft F ϕ.
Proof.
  intros.
  by apply (has_kind_ft_through_inst_iff F ϕ ϕ' ix H).
Qed.
