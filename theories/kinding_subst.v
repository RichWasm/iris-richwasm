From mathcomp Require Import ssreflect.
From stdpp Require Import base list.
From RichWasm Require Import syntax typing util.
Require RichWasm.iris.logrel.
Require Import RecordUpdate.RecordUpdate.

Set Bullet Behavior "Strict Subproofs".

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

Definition pw_id (ξ : nat -> nat) : Prop := forall n, ξ n = n.

Lemma pw_id_up ξ : pw_id ξ -> pw_id (unscoped.up_ren ξ).
Proof.
  intros H [|n]; unfold unscoped.up_ren, unscoped.scons, core.funcomp; cbn; by rewrite ?H.
Qed.

Lemma ren_memory_id ξ μ : pw_id ξ -> ren_memory ξ μ = μ.
Proof. intros H; rewrite (extRen_memory ξ unscoped.id H); apply rinstId'_memory. Qed.

Lemma ren_representation_id ξ ρ : pw_id ξ -> ren_representation ξ ρ = ρ.
Proof.
  intros H; rewrite (extRen_representation ξ unscoped.id H); apply rinstId'_representation.
Qed.

Lemma ren_size_id ξr ξs σ : pw_id ξr -> pw_id ξs -> ren_size ξr ξs σ = σ.
Proof.
  intros Hr Hs; rewrite (extRen_size ξr ξs unscoped.id unscoped.id Hr Hs); apply rinstId'_size.
Qed.

Lemma ren_kind_id ξr ξs κ : pw_id ξr -> pw_id ξs -> ren_kind ξr ξs κ = κ.
Proof.
  intros Hr Hs; rewrite (extRen_kind ξr ξs unscoped.id unscoped.id Hr Hs); apply rinstId'_kind.
Qed.

Definition kc_ren (ξm ξr ξs : nat -> nat) (K K' : kind_ctx) : Prop :=
  (forall n, n < kc_mem_vars K <-> ξm n < kc_mem_vars K') /\
  (forall n, n < kc_rep_vars K <-> ξr n < kc_rep_vars K') /\
  (forall n, n < kc_size_vars K <-> ξs n < kc_size_vars K').

Lemma Forall_map_iff {A B} (f : A -> B) (P : A -> Prop) (Q : B -> Prop) l :
  Forall (fun x => P x <-> Q (f x)) l -> Forall P l <-> Forall Q (map f l).
Proof.
  induction 1 as [|x l Hx Hl IH]; cbn; [done|].
  split; inversion 1; subst; constructor.
  - by apply Hx.
  - by apply IH.
  - by apply Hx.
  - by apply IH.
Qed.

Lemma mem_ok_ren ξm ξr ξs K K' μ :
  kc_ren ξm ξr ξs K K' -> mem_ok K μ <-> mem_ok K' (ren_memory ξm μ).
Proof.
  intros (Hm & _ & _); destruct μ as [n|c]; cbn.
  - split; inversion 1; subst; constructor; by apply Hm.
  - split; intros _; constructor.
Qed.

Lemma rep_ok_ren ξr K K' ρ :
  (forall n, n < kc_rep_vars K <-> ξr n < kc_rep_vars K') ->
  rep_ok K ρ <-> rep_ok K' (ren_representation ξr ρ).
Proof.
  intros Hr; induction ρ using rep_ind; cbn.
  - split; inversion 1; subst; constructor; by apply Hr.
  - split; inversion 1; subst; constructor.
    + by apply (proj1 (Forall_map_iff (ren_representation ξr) (rep_ok K) (rep_ok K') ρs H)).
    + by apply (proj2 (Forall_map_iff (ren_representation ξr) (rep_ok K) (rep_ok K') ρs H)).
  - split; inversion 1; subst; constructor.
    + by apply (proj1 (Forall_map_iff (ren_representation ξr) (rep_ok K) (rep_ok K') ρs H)).
    + by apply (proj2 (Forall_map_iff (ren_representation ξr) (rep_ok K) (rep_ok K') ρs H)).
  - split; intros _; constructor.
Qed.

Lemma size_ok_ren ξr ξs K K' σ :
  (forall n, n < kc_rep_vars K <-> ξr n < kc_rep_vars K') ->
  (forall n, n < kc_size_vars K <-> ξs n < kc_size_vars K') ->
  size_ok K σ <-> size_ok K' (ren_size ξr ξs σ).
Proof.
  intros Hr Hs; induction σ using size_ind; cbn.
  - split; inversion 1; subst; constructor; by apply Hs.
  - split; inversion 1; subst; constructor.
    + by apply (proj1 (Forall_map_iff (ren_size ξr ξs) (size_ok K) (size_ok K') σs H)).
    + by apply (proj2 (Forall_map_iff (ren_size ξr ξs) (size_ok K) (size_ok K') σs H)).
  - split; inversion 1; subst; constructor.
    + by apply (proj1 (Forall_map_iff (ren_size ξr ξs) (size_ok K) (size_ok K') σs H)).
    + by apply (proj2 (Forall_map_iff (ren_size ξr ξs) (size_ok K) (size_ok K') σs H)).
  - split; inversion 1; subst; constructor.
    + by apply (proj1 (rep_ok_ren ξr K K' ρ Hr)).
    + by apply (proj2 (rep_ok_ren ξr K K' ρ Hr)).
  - split; intros _; constructor.
Qed.

Lemma kind_ok_ren' ξr ξs K K' κ :
  (forall n, n < kc_rep_vars K <-> ξr n < kc_rep_vars K') ->
  (forall n, n < kc_size_vars K <-> ξs n < kc_size_vars K') ->
  kind_ok K κ <-> kind_ok K' (ren_kind ξr ξs κ).
Proof.
  intros Hr Hs; destruct κ as [ρ ξ|σ ξ]; cbn.
  - split; inversion 1; subst; constructor.
    + by apply (proj1 (rep_ok_ren ξr K K' ρ Hr)).
    + by apply (proj2 (rep_ok_ren ξr K K' ρ Hr)).
  - split; inversion 1; subst; constructor.
    + by apply (proj1 (size_ok_ren ξr ξs K K' σ Hr Hs)).
    + by apply (proj2 (size_ok_ren ξr ξs K K' σ Hr Hs)).
Qed.

Lemma kind_ok_ren ξm ξr ξs K K' κ :
  kc_ren ξm ξr ξs K K' -> kind_ok K κ <-> kind_ok K' (ren_kind ξr ξs κ).
Proof. intros (_ & Hr & Hs); by apply kind_ok_ren'. Qed.

Lemma kc_ren_mem ξm ξr ξs K K' :
  kc_ren ξm ξr ξs K K' ->
  kc_ren (unscoped.up_ren ξm) ξr ξs (set kc_mem_vars S K) (set kc_mem_vars S K').
Proof.
  intros (Hm & Hr & Hs); destruct K as [km kr ks], K' as [km' kr' ks'].
  split; [|split]; cbn in *; try done.
  intros [|n]; unfold unscoped.up_ren, unscoped.scons, core.funcomp; cbn.
  - split; intros _; lia.
  - specialize (Hm n); lia.
Qed.

Lemma kc_ren_rep ξm ξr ξs K K' :
  kc_ren ξm ξr ξs K K' ->
  kc_ren ξm (unscoped.up_ren ξr) ξs (set kc_rep_vars S K) (set kc_rep_vars S K').
Proof.
  intros (Hm & Hr & Hs); destruct K as [km kr ks], K' as [km' kr' ks'].
  split; [|split]; cbn in *; try done.
  intros [|n]; unfold unscoped.up_ren, unscoped.scons, core.funcomp; cbn.
  - split; intros _; lia.
  - specialize (Hr n); lia.
Qed.

Lemma kc_ren_size ξm ξr ξs K K' :
  kc_ren ξm ξr ξs K K' ->
  kc_ren ξm ξr (unscoped.up_ren ξs) (set kc_size_vars S K) (set kc_size_vars S K').
Proof.
  intros (Hm & Hr & Hs); destruct K as [km kr ks], K' as [km' kr' ks'].
  split; [|split]; cbn in *; try done.
  intros [|n]; unfold unscoped.up_ren, unscoped.scons, core.funcomp; cbn.
  - split; intros _; lia.
  - specialize (Hs n); lia.
Qed.

Definition ctx_ren (ξm ξr ξs ξt : nat -> nat) (F F' : function_ctx) : Prop :=
  fc_ren ξr ξs ξt F F' /\ kc_ren ξm ξr ξs (fc_kind_ctx F) (fc_kind_ctx F').

Lemma ctx_ren_cons ξm ξr ξs ξt F F' κ :
  ctx_ren ξm ξr ξs ξt F F' ->
  ctx_ren ξm ξr ξs (unscoped.up_ren ξt)
    (F <| fc_type_vars ::= cons κ |>) (F' <| fc_type_vars ::= cons (ren_kind ξr ξs κ) |>).
Proof.
  intros [H1 H2]; split; [by apply fc_ren_cons|].
  by rewrite !fc_kind_ctx_ty_update.
Qed.

Lemma ctx_ren_mem ξm ξr ξs ξt F F' :
  ctx_ren ξm ξr ξs ξt F F' ->
  ctx_ren (unscoped.up_ren ξm) ξr ξs ξt
    (F <| fc_kind_ctx ::= set kc_mem_vars S |>) (F' <| fc_kind_ctx ::= set kc_mem_vars S |>).
Proof.
  intros [H1 H2]; split; [by apply fc_ren_mem|].
  destruct F, F'; cbn in *; by apply kc_ren_mem.
Qed.

Lemma ctx_ren_rep ξm ξr ξs ξt F F' :
  ctx_ren ξm ξr ξs ξt F F' ->
  ctx_ren ξm (unscoped.up_ren ξr) ξs ξt (add_rep_var F) (add_rep_var F').
Proof.
  intros [H1 H2]; split; [by apply fc_ren_rep|].
  destruct F, F'; unfold add_rep_var; cbn in *; by apply kc_ren_rep.
Qed.

Lemma ctx_ren_size ξm ξr ξs ξt F F' :
  ctx_ren ξm ξr ξs ξt F F' ->
  ctx_ren ξm ξr (unscoped.up_ren ξs) ξt (add_size_var F) (add_size_var F').
Proof.
  intros [H1 H2]; split; [by apply fc_ren_size|].
  destruct F, F'; unfold add_size_var; cbn in *; by apply kc_ren_size.
Qed.

Lemma ren_kind_shift_rep ξr ξs κ :
  ren_kind (unscoped.up_ren ξr) ξs (ren_kind unscoped.shift unscoped.id κ) =
  ren_kind unscoped.shift unscoped.id (ren_kind ξr ξs κ).
Proof. rewrite !renRen_kind; apply extRen_kind; intros n; done. Qed.

Lemma ren_kind_shift_size ξr ξs κ :
  ren_kind ξr (unscoped.up_ren ξs) (ren_kind unscoped.id unscoped.shift κ) =
  ren_kind unscoped.id unscoped.shift (ren_kind ξr ξs κ).
Proof. rewrite !renRen_kind; apply extRen_kind; intros n; done. Qed.

Lemma Forall2_map_12 {A B A' B'} (f : A -> A') (g : B -> B') (P : A' -> B' -> Prop) l k :
  Forall2 (fun a b => P (f a) (g b)) l k -> Forall2 P (map f l) (map g k).
Proof. induction 1; cbn; constructor; auto. Qed.

Lemma Forall3_map_12 {A B C A' B'} (f : A -> A') (g : B -> B') (P : A' -> B' -> C -> Prop) l k k' :
  Forall3 (fun a b c => P (f a) (g b) c) l k k' -> Forall3 P (map f l) (map g k) k'.
Proof. induction 1; cbn; constructor; auto. Qed.

Lemma subkind_of_ren κ κ' :
  subkind_of κ κ' →
  ∀ ξr ξs,
    subkind_of (ren_kind ξr ξs κ) (ren_kind ξr ξs κ').
Proof.
  intros Hsub.
  inversion Hsub; subst; intros ξr ξs; cbn; by constructor.
Qed.

Lemma subkind_of_ren_inv κ' ξr ξs κ :
  subkind_of κ' (ren_kind ξr ξs κ) ->
  exists κ0, κ' = ren_kind ξr ξs κ0 /\ subkind_of κ0 κ.
Proof.
  destruct κ as [ρ ξ|σ ξ]; cbn; inversion 1; subst.
  - exists (VALTYPE ρ ξ0); split; [done|by constructor].
  - exists (MEMTYPE σ ξ0); split; [done|by constructor].
Qed.

Lemma has_kind_ren :
  forall F τ κ, has_kind F τ κ ->
  forall ξm ξr ξs ξt F', ctx_ren ξm ξr ξs ξt F F' ->
    has_kind F' (ren_type ξm ξr ξs ξt τ) (ren_kind ξr ξs κ).
Proof.
  apply (has_kind_ind'
           (fun F τ κ => forall ξm ξr ξs ξt F', ctx_ren ξm ξr ξs ξt F F' ->
                           has_kind F' (ren_type ξm ξr ξs ξt τ) (ren_kind ξr ξs κ))
           (fun F ϕ => forall ξm ξr ξs ξt F', ctx_ren ξm ξr ξs ξt F F' ->
                         has_kind_ift F' (ren_inner_function_type ξm ξr ξs ξt ϕ))
           (fun F ϕ => forall ξm ξr ξs ξt F', ctx_ren ξm ξr ξs ξt F F' ->
                         has_kind_ft F' (ren_function_type ξm ξr ξs ξt ϕ))).
  - intros F; cbv zeta; intros; by apply KI31.
  - intros F; cbv zeta; intros; by apply KI32.
  - intros F; cbv zeta; intros; by apply KI64.
  - intros F; cbv zeta; intros; by apply KF32.
  - intros F; cbv zeta; intros; by apply KF64.
  - intros F τs ρs ξs0 IH; cbv zeta; intros ξm ξr ξs ξt F' Hctx.
    apply KSum, Forall3_map_12, (Forall3_impl _ _ _ _ _ IH).
    intros τ ρ ξ Hτ; by apply Hτ.
  - intros F τs σs ξs0 IH; cbv zeta; intros ξm ξr ξs ξt F' Hctx.
    apply KVariant, Forall3_map_12, (Forall3_impl _ _ _ _ _ IH).
    intros τ σ ξ Hτ; by apply Hτ.
  - intros F τs ρs ξs0 IH; cbv zeta; intros ξm ξr ξs ξt F' Hctx.
    apply KProd, Forall3_map_12, (Forall3_impl _ _ _ _ _ IH).
    intros τ ρ ξ Hτ; by apply Hτ.
  - intros F τs σs ξs0 IH; cbv zeta; intros ξm ξr ξs ξt F' Hctx.
    apply KStruct, Forall3_map_12, (Forall3_impl _ _ _ _ _ IH).
    intros τ σ ξ Hτ; by apply Hτ.
  - intros F m β τ σ ξ Hm IH; cbv zeta; intros ξm ξr ξs ξt F' Hctx.
    apply KRefVar with (σ := ren_size ξr ξs σ) (ξ := ξ).
    + by apply (proj1 (mem_ok_ren ξm ξr ξs _ _ (VarM m) (proj2 Hctx))).
    + by apply IH.
  - intros F β τ σ ξ IH; cbv zeta; intros ξm ξr ξs ξt F' Hctx.
    apply KRefMM with (σ := ren_size ξr ξs σ) (ξ := ξ); by apply IH.
  - intros F β τ σ ξ IH; cbv zeta; intros ξm ξr ξs ξt F' Hctx.
    apply KRefGC with (σ := ren_size ξr ξs σ) (ξ := ξ); by apply IH.
  - intros F ϕ IH; cbv zeta; intros ξm ξr ξs ξt F' Hctx.
    apply KCodeRef; by apply IH.
  - intros F τ ρ ξ IH; cbv zeta; intros ξm ξr ξs ξt F' Hctx.
    apply KSer; by apply IH.
  - intros F ρ Hρ; cbv zeta; intros ξm ξr ξs ξt F' Hctx.
    apply KPlug; by apply (proj1 (rep_ok_ren ξr _ _ _ (proj1 (proj2 (proj2 Hctx))))).
  - intros F σ Hσ; cbv zeta; intros ξm ξr ξs ξt F' Hctx.
    apply KSpan.
    destruct Hctx as [? (? & Hr & Hsz)].
    by apply (proj1 (size_ok_ren ξr ξs _ _ _ Hr Hsz)).
  - intros F τ κ κbody Hok IH Hsub; cbv zeta; intros ξm ξr ξs ξt F' Hctx.
    eapply KRec; try by apply IH, ctx_ren_cons.
    + rewrite <- kind_ok_ren; eauto.
      apply Hctx.
    + by apply subkind_of_ren.
  - intros F τ κ Hok IH; cbv zeta; intros ξm ξr ξs ξt F' Hctx.
    apply KExistsMem.
    + by apply (proj1 (kind_ok_ren ξm ξr ξs _ _ _ (proj2 Hctx))).
    + by apply IH, ctx_ren_mem.
  - intros F τ κ Hok IH; cbv zeta; intros ξm ξr ξs ξt F' Hctx.
    apply KExistsRep.
    + by apply (proj1 (kind_ok_ren ξm ξr ξs _ _ _ (proj2 Hctx))).
    + rewrite -ren_kind_shift_rep; by apply IH, ctx_ren_rep.
  - intros F τ κ Hok IH; cbv zeta; intros ξm ξr ξs ξt F' Hctx.
    apply KExistsSize.
    + by apply (proj1 (kind_ok_ren ξm ξr ξs _ _ _ (proj2 Hctx))).
    + rewrite -ren_kind_shift_size; by apply IH, ctx_ren_size.
  - intros F τ κ0 κ Hok0 Hok IH; cbv zeta; intros ξm ξr ξs ξt F' Hctx.
    apply KExistsType.
    + by apply (proj1 (kind_ok_ren ξm ξr ξs _ _ _ (proj2 Hctx))).
    + by apply (proj1 (kind_ok_ren ξm ξr ξs _ _ _ (proj2 Hctx))).
    + by apply IH, ctx_ren_cons.
  - intros F t κ Hlook Hok ξm ξr ξs ξt F' Hctx.
    apply KVar.
    + by rewrite (proj1 Hctx t) Hlook.
    + by apply (proj1 (kind_ok_ren ξm ξr ξs _ _ _ (proj2 Hctx))).
  - intros F τs1 τs2 κs1 κs2 IH1 IH2 ξm ξr ξs ξt F' Hctx.
    apply (KMonoFun _ _ _ (map (ren_kind ξr ξs) κs1) (map (ren_kind ξr ξs) κs2)).
    + apply Forall2_map_12, (Forall2_impl _ _ _ _ IH1).
      intros τ κ Hτ; by apply Hτ.
    + apply Forall2_map_12, (Forall2_impl _ _ _ _ IH2).
      intros τ κ Hτ; by apply Hτ.
  - intros F ϕ IH ξm ξr ξs ξt F' Hctx.
    apply KInnerFun; by apply IH.
  - intros F ϕ IH ξm ξr ξs ξt F' Hctx.
    apply KForallMem; by apply IH, ctx_ren_mem.
  - intros F ϕ IH ξm ξr ξs ξt F' Hctx.
    apply KForallRep; by apply IH, ctx_ren_rep.
  - intros F ϕ IH ξm ξr ξs ξt F' Hctx.
    apply KForallSize; by apply IH, ctx_ren_size.
  - intros F κ ϕ Hok IH ξm ξr ξs ξt F' Hctx.
    apply KForallType.
    + by apply (proj1 (kind_ok_ren ξm ξr ξs _ _ _ (proj2 Hctx))).
    + by apply IH, ctx_ren_cons.
Qed.

Lemma pw_id_id : pw_id (@id nat).
Proof. by intros n. Qed.

Lemma pw_id_uid : pw_id unscoped.id.
Proof. by intros n. Qed.

Definition ctx_str (ξt : nat -> nat) (F F' : function_ctx) : Prop :=
  fc_kind_ctx F' = fc_kind_ctx F /\
  forall t, fc_type_vars F' !! ξt t = fc_type_vars F !! t.

Lemma ctx_str_cons ξt F F' κ :
  ctx_str ξt F F' ->
  ctx_str (unscoped.up_ren ξt)
    (F <| fc_type_vars ::= cons κ |>) (F' <| fc_type_vars ::= cons κ |>).
Proof.
  intros [Hk Hl]; split; [by rewrite !fc_kind_ctx_ty_update|].
  intros [|t]; unfold unscoped.up_ren, unscoped.scons, core.funcomp;
    rewrite !fc_type_vars_get_upd; cbn; [done|apply Hl].
Qed.

Lemma ctx_str_mem ξt F F' :
  ctx_str ξt F F' ->
  ctx_str ξt (F <| fc_kind_ctx ::= set kc_mem_vars S |>)
             (F' <| fc_kind_ctx ::= set kc_mem_vars S |>).
Proof.
  intros [Hk Hl]; split.
  - destruct F, F'; cbn in *; by rewrite Hk.
  - intros t; destruct F, F'; cbn in *; apply Hl.
Qed.

Lemma ctx_str_rep ξt F F' :
  ctx_str ξt F F' -> ctx_str ξt (add_rep_var F) (add_rep_var F').
Proof.
  intros [Hk Hl]; split.
  - destruct F, F'; unfold add_rep_var; cbn in *; by rewrite Hk.
  - intros t; destruct F as [? ? ? ? tvs], F' as [? ? ? ? tvs'];
      unfold add_rep_var; cbn in *.
    by rewrite !list_lookup_fmap Hl.
Qed.

Lemma ctx_str_size ξt F F' :
  ctx_str ξt F F' -> ctx_str ξt (add_size_var F) (add_size_var F').
Proof.
  intros [Hk Hl]; split.
  - destruct F, F'; unfold add_size_var; cbn in *; by rewrite Hk.
  - intros t; destruct F as [? ? ? ? tvs], F' as [? ? ? ? tvs'];
      unfold add_size_var; cbn in *.
    by rewrite !list_lookup_fmap Hl.
Qed.

Lemma Forall2_map_1_inv {A A' B} (f : A -> A') (P : A' -> B -> Prop) l k :
  Forall2 P (map f l) k -> Forall2 (fun a b => P (f a) b) l k.
Proof.
  revert k; induction l as [|a l IH]; intros k H; cbn in H;
    inversion H; subst; constructor; auto.
Qed.

Lemma Forall3_map_1_inv {A A' B C} (f : A -> A') (P : A' -> B -> C -> Prop) l k k' :
  Forall3 P (map f l) k k' -> Forall3 (fun a b c => P (f a) b c) l k k'.
Proof.
  revert k k'; induction l as [|a l IH]; intros k k' H; cbn in H;
    inversion H; subst; constructor; auto.
Qed.

Lemma Forall2_Forall_impl {A B} (P Q : A -> B -> Prop) (R : A -> Prop) l k :
  Forall2 P l k -> Forall R l -> (forall a b, R a -> P a b -> Q a b) -> Forall2 Q l k.
Proof.
  induction 1 as [|a b l k Hp Hall IH]; intros HR Himp; [constructor|].
  inversion HR; subst; constructor; [by apply Himp|by apply IH].
Qed.

Lemma Forall3_Forall_impl {A B C} (P Q : A -> B -> C -> Prop) (R : A -> Prop) l k k' :
  Forall3 P l k k' -> Forall R l -> (forall a b c, R a -> P a b c -> Q a b c) ->
  Forall3 Q l k k'.
Proof.
  induction 1 as [|a b c l k k' Hp Hall IH]; intros HR Himp; [constructor|].
  inversion HR; subst; constructor; [by apply Himp|by apply IH].
Qed.

Lemma Forall_mp {A} (P Q : A -> Prop) l :
  Forall (fun x => P x -> Q x) l -> Forall P l -> Forall Q l.
Proof. induction 1; inversion 1; subst; constructor; auto. Qed.

Lemma Forall_map_impl {A B} (f : A -> B) (P : A -> Prop) (Q : B -> Prop) l :
  Forall (fun x => P x -> Q (f x)) l -> Forall P l -> Forall Q (map f l).
Proof.
  induction 1 as [|x l Hx _ IH]; cbn; [done|].
  inversion 1; subst; constructor; auto.
Qed.

Lemma Forall2_map_1_strip {A A' B} (f : A -> A') (P : A' -> B -> Prop)
      (Q : A -> B -> Prop) (R : A -> Prop) l k :
  Forall2 P (map f l) k -> Forall R l ->
  (forall a b, R a -> P (f a) b -> Q a b) -> Forall2 Q l k.
Proof.
  intros H1 H2 H3.
  eapply Forall2_Forall_impl; [exact (Forall2_map_1_inv f P l k H1)|exact H2|exact H3].
Qed.

Lemma Forall3_map_1_strip {A A' B C} (f : A -> A') (P : A' -> B -> C -> Prop)
      (Q : A -> B -> C -> Prop) (R : A -> Prop) l k k' :
  Forall3 P (map f l) k k' -> Forall R l ->
  (forall a b c, R a -> P (f a) b c -> Q a b c) -> Forall3 Q l k k'.
Proof.
  intros H1 H2 H3.
  eapply Forall3_Forall_impl; [exact (Forall3_map_1_inv f P l k k' H1)|exact H2|exact H3].
Qed.

Lemma has_kind_ren_inv :
  (forall τ ξm ξr ξs ξt F F' κ,
      pw_id ξm -> pw_id ξr -> pw_id ξs -> ctx_str ξt F F' ->
      has_kind F' (ren_type ξm ξr ξs ξt τ) κ -> has_kind F τ κ) /\
  (forall ϕ ξm ξr ξs ξt F F',
      pw_id ξm -> pw_id ξr -> pw_id ξs -> ctx_str ξt F F' ->
      has_kind_ft F' (ren_function_type ξm ξr ξs ξt ϕ) -> has_kind_ft F ϕ) /\
  (forall ϕ ξm ξr ξs ξt F F',
      pw_id ξm -> pw_id ξr -> pw_id ξs -> ctx_str ξt F F' ->
      has_kind_ift F' (ren_inner_function_type ξm ξr ξs ξt ϕ) -> has_kind_ift F ϕ).
Proof.
  apply type_and_function_ind.
  - intros idx ξm ξr ξs ξt F F' κ Hm Hr Hs Hctx H.
    cbn [ren_type] in H; inversion H; subst.
    apply KVar.
    + by rewrite -(proj2 Hctx idx).
    + by rewrite -(proj1 Hctx).
  - intros κ0 ξm ξr ξs ξt F F' κ Hm Hr Hs Hctx H.
    cbn [ren_type] in H; rewrite (ren_kind_id ξr ξs κ0 Hr Hs) in H.
    by inversion H; subst; constructor.
  - intros κ0 nt ξm ξr ξs ξt F F' κ Hm Hr Hs Hctx H.
    cbn [ren_type] in H; rewrite (ren_kind_id ξr ξs κ0 Hr Hs) in H.
    by inversion H; subst; constructor.
  - intros κ0 τs IH ξm ξr ξs ξt F F' κ Hm Hr Hs Hctx H.
    cbn [ren_type] in H; rewrite (ren_kind_id ξr ξs κ0 Hr Hs) in H.
    inversion H; subst.
    apply KSum.
    eapply Forall3_map_1_strip; [eassumption|exact IH|].
    intros τ ρ ξ HR HP; by apply (HR ξm ξr ξs ξt F F' _ Hm Hr Hs Hctx HP).
  - intros κ0 τs IH ξm ξr ξs ξt F F' κ Hm Hr Hs Hctx H.
    cbn [ren_type] in H; rewrite (ren_kind_id ξr ξs κ0 Hr Hs) in H.
    inversion H; subst.
    apply KVariant.
    eapply Forall3_map_1_strip; [eassumption|exact IH|].
    intros τ σ ξ HR HP; by apply (HR ξm ξr ξs ξt F F' _ Hm Hr Hs Hctx HP).
  - intros κ0 τs IH ξm ξr ξs ξt F F' κ Hm Hr Hs Hctx H.
    cbn [ren_type] in H; rewrite (ren_kind_id ξr ξs κ0 Hr Hs) in H.
    inversion H; subst.
    apply KProd.
    eapply Forall3_map_1_strip; [eassumption|exact IH|].
    intros τ ρ ξ HR HP; by apply (HR ξm ξr ξs ξt F F' _ Hm Hr Hs Hctx HP).
  - intros κ0 τs IH ξm ξr ξs ξt F F' κ Hm Hr Hs Hctx H.
    cbn [ren_type] in H; rewrite (ren_kind_id ξr ξs κ0 Hr Hs) in H.
    inversion H; subst.
    apply KStruct.
    eapply Forall3_map_1_strip; [eassumption|exact IH|].
    intros τ σ ξ HR HP; by apply (HR ξm ξr ξs ξt F F' _ Hm Hr Hs Hctx HP).
  - intros κ0 μ β t IH ξm ξr ξs ξt F F' κ Hm Hr Hs Hctx H.
    cbn [ren_type] in H.
    rewrite (ren_kind_id ξr ξs κ0 Hr Hs) (ren_memory_id ξm μ Hm) in H.
    inversion H; subst.
    + eapply KRefVar; [by rewrite -(proj1 Hctx)|].
      by eapply (IH ξm ξr ξs ξt F F'); eauto.
    + eapply KRefMM.
      by eapply (IH ξm ξr ξs ξt F F'); eauto.
    + eapply KRefGC.
      by eapply (IH ξm ξr ξs ξt F F'); eauto.
  - intros κ0 ft IH ξm ξr ξs ξt F F' κ Hm Hr Hs Hctx H.
    cbn [ren_type] in H; rewrite (ren_kind_id ξr ξs κ0 Hr Hs) in H.
    inversion H; subst.
    apply KCodeRef.
    by eapply (IH ξm ξr ξs ξt F F'); eauto.
  - intros κ0 t IH ξm ξr ξs ξt F F' κ Hm Hr Hs Hctx H.
    cbn [ren_type] in H; rewrite (ren_kind_id ξr ξs κ0 Hr Hs) in H.
    inversion H; subst.
    eapply KSer.
    by eapply (IH ξm ξr ξs ξt F F'); eauto.
  - intros κ0 ρ ξm ξr ξs ξt F F' κ Hm Hr Hs Hctx H.
    cbn [ren_type] in H.
    rewrite (ren_kind_id ξr ξs κ0 Hr Hs) (ren_representation_id ξr ρ Hr) in H.
    inversion H; subst.
    apply KPlug.
    by rewrite -(proj1 Hctx).
  - intros κ0 σ ξm ξr ξs ξt F F' κ Hm Hr Hs Hctx H.
    cbn [ren_type] in H.
    rewrite (ren_kind_id ξr ξs κ0 Hr Hs) (ren_size_id ξr ξs σ Hr Hs) in H.
    inversion H; subst.
    apply KSpan.
    by rewrite -(proj1 Hctx).
  - intros κ0 t IH ξm ξr ξs ξt F F' κ Hm Hr Hs Hctx H.
    cbn [ren_type] in H; rewrite (ren_kind_id ξr ξs κ0 Hr Hs) in H.
    inversion H; subst.
    eapply KRec; last done.
    + by rewrite <- (proj1 Hctx).
    + eapply (IH ξm ξr ξs (unscoped.up_ren ξt) _ (F' <| fc_type_vars ::= cons κ |>));
        eauto using ctx_str_cons.
  - intros κ0 t IH ξm ξr ξs ξt F F' κ Hm Hr Hs Hctx H.
    cbn [ren_type] in H; rewrite (ren_kind_id ξr ξs κ0 Hr Hs) in H.
    inversion H; subst.
    apply KExistsMem; [by rewrite -(proj1 Hctx)|].
    eapply (IH (unscoped.up_ren ξm) ξr ξs ξt _
              (F' <| fc_kind_ctx ::= set kc_mem_vars S |>));
      eauto using ctx_str_mem, pw_id_up.
  - intros κ0 t IH ξm ξr ξs ξt F F' κ Hm Hr Hs Hctx H.
    cbn [ren_type] in H; rewrite (ren_kind_id ξr ξs κ0 Hr Hs) in H.
    inversion H; subst.
    apply KExistsRep; [by rewrite -(proj1 Hctx)|].
    eapply (IH ξm (unscoped.up_ren ξr) ξs ξt _ (add_rep_var F'));
      eauto using ctx_str_rep, pw_id_up.
  - intros κ0 t IH ξm ξr ξs ξt F F' κ Hm Hr Hs Hctx H.
    cbn [ren_type] in H; rewrite (ren_kind_id ξr ξs κ0 Hr Hs) in H.
    inversion H; subst.
    apply KExistsSize; [by rewrite -(proj1 Hctx)|].
    eapply (IH ξm ξr (unscoped.up_ren ξs) ξt _ (add_size_var F'));
      eauto using ctx_str_size, pw_id_up.
  - intros κ1 κ2 t IH ξm ξr ξs ξt F F' κ Hm Hr Hs Hctx H.
    cbn [ren_type] in H.
    rewrite (ren_kind_id ξr ξs κ1 Hr Hs) (ren_kind_id ξr ξs κ2 Hr Hs) in H.
    inversion H; subst.
    apply KExistsType; [by rewrite -(proj1 Hctx)|by rewrite -(proj1 Hctx)|].
    eapply (IH ξm ξr ξs (unscoped.up_ren ξt) _ (F' <| fc_type_vars ::= cons κ2 |>));
      eauto using ctx_str_cons.
  - intros τs1 τs2 IH1 IH2 ξm ξr ξs ξt F F' Hm Hr Hs Hctx H.
    cbn [ren_inner_function_type] in H.
    inversion H; subst.
    eapply KMonoFun.
    + eapply Forall2_map_1_strip; [eassumption|exact IH1|].
      intros τ κ HR HP; by apply (HR ξm ξr ξs ξt F F' _ Hm Hr Hs Hctx HP).
    + eapply Forall2_map_1_strip; [eassumption|exact IH2|].
      intros τ κ HR HP; by apply (HR ξm ξr ξs ξt F F' _ Hm Hr Hs Hctx HP).
  - intros κ0 ft IH ξm ξr ξs ξt F F' Hm Hr Hs Hctx H.
    cbn [ren_inner_function_type] in H.
    rewrite (ren_kind_id ξr ξs κ0 Hr Hs) in H.
    inversion H; subst.
    apply KForallType; [by rewrite -(proj1 Hctx)|].
    eapply (IH ξm ξr ξs (unscoped.up_ren ξt) _ (F' <| fc_type_vars ::= cons κ0 |>));
      eauto using ctx_str_cons.
  - intros ft IH ξm ξr ξs ξt F F' Hm Hr Hs Hctx H.
    cbn [ren_function_type] in H.
    inversion H; subst.
    apply KInnerFun.
    by eapply (IH ξm ξr ξs ξt F F'); eauto.
  - intros ft IH ξm ξr ξs ξt F F' Hm Hr Hs Hctx H.
    cbn [ren_function_type] in H.
    inversion H; subst.
    apply KForallMem.
    eapply (IH (unscoped.up_ren ξm) ξr ξs ξt _
              (F' <| fc_kind_ctx ::= set kc_mem_vars S |>));
      eauto using ctx_str_mem, pw_id_up.
  - intros ft IH ξm ξr ξs ξt F F' Hm Hr Hs Hctx H.
    cbn [ren_function_type] in H.
    inversion H; subst.
    apply KForallRep.
    eapply (IH ξm (unscoped.up_ren ξr) ξs ξt _ (add_rep_var F'));
      eauto using ctx_str_rep, pw_id_up.
  - intros ft IH ξm ξr ξs ξt F F' Hm Hr Hs Hctx H.
    cbn [ren_function_type] in H.
    inversion H; subst.
    apply KForallSize.
    eapply (IH ξm ξr (unscoped.up_ren ξs) ξt _ (add_size_var F'));
      eauto using ctx_str_size, pw_id_up.
Qed.

Lemma kc_ren_refl K : kc_ren (@id nat) (@id nat) (@id nat) K K.
Proof. unfold kc_ren; split; [|split]; intros n; reflexivity. Qed.

Lemma ctx_ren_wk F κv :
  ctx_ren (@id nat) (@id nat) (@id nat) S F (F <| fc_type_vars ::= cons κv |>).
Proof.
  split; [|by rewrite fc_kind_ctx_ty_update; apply kc_ren_refl].
  intros t; rewrite fc_type_vars_get_upd.
  replace ((κv :: fc_type_vars F) !! S t) with (fc_type_vars F !! t) by done.
  destruct (fc_type_vars F !! t) as [κ0|]; cbn [fmap option_fmap option_map]; [|done].
  by rewrite (ren_kind_id (@id nat) (@id nat) κ0 pw_id_id pw_id_id).
Qed.

Lemma ctx_str_wk F κv : ctx_str S F (F <| fc_type_vars ::= cons κv |>).
Proof.
  split; [by rewrite fc_kind_ctx_ty_update|].
  intros t; by rewrite fc_type_vars_get_upd.
Qed.

Lemma has_kind_wk_ty F τ κ κv :
  has_kind F τ κ ↔ has_kind (F <| fc_type_vars ::= cons κv |>) (ren_type id id id S τ) κ.
Proof.
  split; intros Hk.
  - rewrite -(ren_kind_id (@id nat) (@id nat) κ pw_id_id pw_id_id).
    by apply (has_kind_ren _ _ _ Hk), ctx_ren_wk.
  - eapply (proj1 has_kind_ren_inv τ (@id nat) (@id nat) (@id nat) S F
                  (F <| fc_type_vars ::= cons κv |>));
      eauto using pw_id_id, ctx_str_wk.
Qed.


(* End weakening lemmas *)
Ltac fold_subst :=
  fold subst_type subst_size subst_representation subst_function_type.

Lemma ref_flag_lub2_mono ξ1 ξ1' ξ2 ξ2' :
  ref_flag_le ξ1 ξ1' -> ref_flag_le ξ2 ξ2' ->
  ref_flag_le (ref_flag_lub2 ξ1 ξ2) (ref_flag_lub2 ξ1' ξ2').
Proof. by destruct ξ1, ξ1', ξ2, ξ2'. Qed.

Lemma ref_flag_lub_mono ξs ξs' :
  Forall2 ref_flag_le ξs ξs' -> ref_flag_le (ref_flag_lub ξs) (ref_flag_lub ξs').
Proof.
  induction 1 as [|ξ ξ' ξs ξs' Hle _ IH]; first done.
  by apply ref_flag_lub2_mono.
Qed.

Lemma subkind_of_subst s__rep s__size κ κ' :
  subkind_of κ κ' ->
  subkind_of (subst_kind s__rep s__size κ)
             (subst_kind s__rep s__size κ').
Proof.
  intros Hle.
  by destruct Hle; constructor.
Qed.

Lemma has_kind_type_kind F τ κ : has_kind F τ κ -> layout.type_kind (fc_type_vars F) τ = Some κ.
Proof. by inversion 1. Qed.


Definition refresh_det (τ : type) : Prop :=
  forall F κ τ', has_kind F τ κ -> refreshed_kinds F τ τ' -> τ = τ'.

Lemma refreshed_kinds_list {A} (mk : A -> ref_flag -> kind) F τs xs ξs :
  (forall x ξ x' ξ', mk x ξ = mk x' ξ' -> x = x' /\ ξ = ξ') ->
  Forall refresh_det τs ->
  Forall3 (fun τ x ξ => has_kind F τ (mk x ξ)) τs xs ξs ->
  forall τs' κs' xs' ξs',
    Forall2 (refreshed_kinds F) τs τs' ->
    Forall2 (fun τ κ => layout.type_kind (fc_type_vars F) τ = Some κ) τs' κs' ->
    Forall3 (fun κ x ξ => κ = mk x ξ) κs' xs' ξs' ->
    τs' = τs /\ xs' = xs /\ ξs' = ξs.
Proof.
  intros Hinj HIH H3; revert HIH.
  induction H3 as [|τ x ξ τs0 xs0 ξs0 Hk H3 IH];
    intros HIH τs' κs' xs' ξs' H2 Hmap H3'.
  - inversion H2; subst.
    inversion Hmap; subst.
    by inversion H3'.
  - inversion HIH as [|τa τsa Hhd HIH']; subst.
    inversion H2 as [|τb τb' τsb τsb' Hr H2']; subst.
    assert (Heqτ : τ = τb') by (by apply (Hhd F _ _ Hk Hr)).
    subst τb'.
    inversion Hmap as [|τc κc τsc κsc Htk Hmap']; subst.
    rewrite (has_kind_type_kind _ _ _ Hk) in Htk.
    injection Htk as <-.
    inversion H3' as [|κd xd ξd κsd xsd ξsd Heq H3'']; subst.
    apply Hinj in Heq as [-> ->].
    by edestruct (IH HIH' τsb' κsc xsd ξsd H2' Hmap' H3'') as (-> & -> & ->).
Qed.

Lemma refreshed_kinds_list_val F τs ρs ξs τs' κs' ρs' ξs' :
  Forall refresh_det τs ->
  Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs ρs ξs ->
  Forall2 (refreshed_kinds F) τs τs' ->
  mapM (layout.type_kind (fc_type_vars F)) τs' = Some κs' ->
  Forall3 (fun κ ρ ξ => κ = VALTYPE ρ ξ) κs' ρs' ξs' ->
  τs' = τs /\ ρs' = ρs /\ ξs' = ξs.
Proof.
  intros HIH H3 H2 Hmap H3'; apply mapM_Some in Hmap.
  eapply (refreshed_kinds_list VALTYPE);
    [by intros ???? [= -> ->]|exact HIH|exact H3|exact H2|exact Hmap|exact H3'].
Qed.

Lemma refreshed_kinds_list_mem F τs σs ξs τs' κs' σs' ξs' :
  Forall refresh_det τs ->
  Forall3 (fun τ σ ξ => has_kind F τ (MEMTYPE σ ξ)) τs σs ξs ->
  Forall2 (refreshed_kinds F) τs τs' ->
  mapM (layout.type_kind (fc_type_vars F)) τs' = Some κs' ->
  Forall3 (fun κ σ ξ => κ = MEMTYPE σ ξ) κs' σs' ξs' ->
  τs' = τs /\ σs' = σs /\ ξs' = ξs.
Proof.
  intros HIH H3 H2 Hmap H3'; apply mapM_Some in Hmap.
  eapply (refreshed_kinds_list MEMTYPE);
    [by intros ???? [= -> ->]|exact HIH|exact H3|exact H2|exact Hmap|exact H3'].
Qed.

Lemma refreshed_kinds_list2 F τs κs τs' :
  Forall refresh_det τs ->
  Forall2 (has_kind F) τs κs ->
  Forall2 (refreshed_kinds F) τs τs' ->
  τs = τs'.
Proof.
  intros HIH H2; revert HIH τs'.
  induction H2 as [|τ κ τs0 κs0 Hk H2 IH]; intros HIH τs' Hr.
  - by inversion Hr.
  - inversion HIH as [|τa τsa Hhd HIH']; subst.
    inversion Hr as [|τb τb' τsb τsb' Hrh Hrt]; subst.
    f_equal; [by apply (Hhd F κ)|by apply IH].
Qed.

Lemma refreshed_kinds_det :
  (forall τ, refresh_det τ) /\
  (forall ϕ F ϕ', has_kind_ft F ϕ -> refreshed_kinds_ft F ϕ ϕ' -> ϕ = ϕ') /\
  (forall ϕ F ϕ', has_kind_ift F ϕ -> refreshed_kinds_ift F ϕ ϕ' -> ϕ = ϕ').
Proof.
  apply type_and_function_ind.
  - intros idx F κ τ' Hk Hr; by inversion Hr; subst.
  - intros κ0 F κ τ' Hk Hr; by inversion Hk; subst; inversion Hr; subst.
  - intros κ0 nt F κ τ' Hk Hr; by inversion Hk; subst; inversion Hr; subst.
  - intros κ0 τs IH F κ τ' Hk Hr.
    inversion Hk; subst; inversion Hr; subst.
    by destruct (refreshed_kinds_list_val F τs _ _ _ _ _ _ IH H3 H1 H4 H6)
      as (-> & -> & ->).
  - intros κ0 τs IH F κ τ' Hk Hr.
    inversion Hk; subst; inversion Hr; subst.
    by destruct (refreshed_kinds_list_mem F τs _ _ _ _ _ _ IH H3 H1 H4 H6)
      as (-> & -> & ->).
  - intros κ0 τs IH F κ τ' Hk Hr.
    inversion Hk; subst; inversion Hr; subst.
    by destruct (refreshed_kinds_list_val F τs _ _ _ _ _ _ IH H3 H1 H4 H6)
      as (-> & -> & ->).
  - intros κ0 τs IH F κ τ' Hk Hr.
    inversion Hk; subst; inversion Hr; subst.
    by destruct (refreshed_kinds_list_mem F τs _ _ _ _ _ _ IH H3 H1 H4 H6)
      as (-> & -> & ->).
  - intros κ0 μ β t IH F κ τ' Hk Hr.
    inversion Hk; subst; inversion Hr; subst; f_equal; try done;
      by eapply IH; eauto.
  - intros κ0 ft IH F κ τ' Hk Hr.
    inversion Hk; subst; inversion Hr; subst; f_equal; try done;
      by eapply IH; eauto.
  - intros κ0 t IH F κ τ' Hk Hr.
    inversion Hk; subst; inversion Hr; subst.
    assert (t = τ'0) as <- by (by apply (IH F _ _ H3 H2)).
    rewrite (has_kind_type_kind _ _ _ H3) in H5.
    by injection H5 as <-.
  - intros κ0 ρ F κ τ' Hk Hr; by inversion Hk; subst; inversion Hr; subst.
  - intros κ0 σ F κ τ' Hk Hr; by inversion Hk; subst; inversion Hr; subst.
  - intros κ0 t IH F κ τ' Hk Hr.
    inversion Hk; subst; inversion Hr; subst.
    unfold refresh_det in IH.
    f_equal; by eapply IH.
  - intros κ0 t IH F κ τ' Hk Hr.
    inversion Hk; subst; inversion Hr; subst.
    unfold refresh_det in IH.
    assert (t = τ'0) as <- by (by apply (IH _ _ _ H4 H3)).
    rewrite (has_kind_type_kind _ _ _ H4) in H6.
    inversion H6; done.
  - intros κ0 t IH F κ τ' Hk Hr.
    inversion Hk; subst; inversion Hr; subst.
    assert (t = τ'0) as <- by (by eapply IH).
    match goal with H : layout.type_kind _ _ = Some _ |- _ =>
      rewrite (has_kind_type_kind _ _ _ H4) in H; injection H as H;
      apply (f_equal unshift_rep_kind) in H;
      rewrite !unshift_rep_kind_ren in H; by rewrite H
    end.
  - intros κ0 t IH F κ τ' Hk Hr.
    inversion Hk; subst; inversion Hr; subst.
    assert (t = τ'0) as <- by (by eapply IH).
    match goal with H : layout.type_kind _ _ = Some _ |- _ =>
      rewrite (has_kind_type_kind _ _ _ H4) in H; injection H as H;
      apply (f_equal unshift_size_kind) in H;
      rewrite !unshift_size_kind_ren in H; by rewrite H
    end.
  - intros κ1 κ2 t IH F κ τ' Hk Hr.
    inversion Hk; subst; inversion Hr; subst.
    assert (t = τ'0) as <- by (by apply (IH _ _ _ H6 H7)).
    rewrite (has_kind_type_kind _ _ _ H6) in H8.
    inversion H8; done.
  - intros τs1 τs2 IH1 IH2 F ϕ' Hk Hr.
    inversion Hk; subst; inversion Hr; subst.
    f_equal; by eapply refreshed_kinds_list2; eauto.
  - intros κ0 ft IH F ϕ' Hk Hr.
    inversion Hk; subst; inversion Hr; subst; f_equal; try done;
      by eapply IH; eauto.
  - intros ft IH F ϕ' Hk Hr.
    inversion Hk; subst; inversion Hr; subst; f_equal; try done;
      by eapply IH; eauto.
  - intros ft IH F ϕ' Hk Hr.
    inversion Hk; subst; inversion Hr; subst; f_equal; try done;
      by eapply IH; eauto.
  - intros ft IH F ϕ' Hk Hr.
    inversion Hk; subst; inversion Hr; subst; f_equal; try done;
      by eapply IH; eauto.
  - intros ft IH F ϕ' Hk Hr.
    inversion Hk; subst; inversion Hr; subst; f_equal; try done;
      by eapply IH; eauto.
Qed.

Lemma refreshed_kinds_has_kind F τ κ τ' :
  has_kind F τ κ →
  refreshed_kinds F τ τ' →
  τ = τ'.
Proof. exact (proj1 refreshed_kinds_det τ F κ τ'). Qed.


Lemma Forall3_specialize {X Y Z A : Type} {P : X → Y → Z → A → Prop} {xs ys zs} :
  ∀ a,
    Forall3 (λ x y z, forall a, P x y z a) xs ys zs →
    Forall3 (λ x y z, P x y z a) xs ys zs.
Proof.
  intros a H. revert a. induction H.
  - intros; constructor.
  - intros a; constructor; auto.
Qed.

Lemma mem_ok_mono K K' μ : kc_mem_vars K <= kc_mem_vars K' -> mem_ok K μ -> mem_ok K' μ.
Proof. intros Hle; inversion 1; subst; constructor; lia. Qed.

Lemma rep_ok_mono K K' ρ : kc_rep_vars K <= kc_rep_vars K' -> rep_ok K ρ -> rep_ok K' ρ.
Proof.
  intros Hle; induction ρ using rep_ind; inversion 1; subst;
    [apply OKVarR; lia|constructor|constructor|constructor]; eauto using Forall_mp.
Qed.

Lemma size_ok_mono K K' σ :
  kc_rep_vars K <= kc_rep_vars K' -> kc_size_vars K <= kc_size_vars K' ->
  size_ok K σ -> size_ok K' σ.
Proof.
  intros Hr Hs; induction σ using size_ind; inversion 1; subst;
    [apply OKVarS; lia|constructor|constructor|constructor|constructor];
    eauto using Forall_mp, rep_ok_mono.
Qed.

Lemma kind_ok_mono K K' κ :
  kc_rep_vars K <= kc_rep_vars K' -> kc_size_vars K <= kc_size_vars K' ->
  kind_ok K κ -> kind_ok K' κ.
Proof. intros Hr Hs; inversion 1; subst; constructor; eauto using rep_ok_mono, size_ok_mono. Qed.

Lemma kind_ok_kc K K' κ :
  kind_ok K κ ->
  kc_rep_vars K' = kc_rep_vars K -> kc_size_vars K' = kc_size_vars K ->
  kind_ok K' κ.
Proof. intros Hok Hr Hs; eapply kind_ok_mono; [| |exact Hok]; lia. Qed.

Lemma kind_ok_supkind_of K κ κ' : kind_ok K κ' -> subkind_of κ κ' -> kind_ok K κ.
Proof. intros H1 H2; induction H2; constructor; by inversion H1. Qed.

Lemma kc_ren_wk_mem K : kc_ren unscoped.shift (@id nat) (@id nat) K (set kc_mem_vars S K).
Proof.
  destruct K; unfold kc_ren, unscoped.shift, Datatypes.id; cbn; split; [|split]; intros n; lia.
Qed.

Lemma kc_ren_wk_rep K : kc_ren (@id nat) unscoped.shift (@id nat) K (set kc_rep_vars S K).
Proof.
  destruct K; unfold kc_ren, unscoped.shift, Datatypes.id; cbn; split; [|split]; intros n; lia.
Qed.

Lemma kc_ren_wk_size K : kc_ren (@id nat) (@id nat) unscoped.shift K (set kc_size_vars S K).
Proof.
  destruct K; unfold kc_ren, unscoped.shift, Datatypes.id; cbn; split; [|split]; intros n; lia.
Qed.

Lemma ctx_ren_wk_mem F :
  ctx_ren unscoped.shift (@id nat) (@id nat) (@id nat) F
    (F <| fc_kind_ctx ::= set kc_mem_vars S |>).
Proof.
  split.
  - intros t; destruct F as [? ? ? ? tvs]; cbn.
    destruct (tvs !! t) as [κ|]; cbn [fmap option_fmap option_map]; [|done].
    by rewrite (ren_kind_id (@id nat) (@id nat) κ pw_id_id pw_id_id).
  - destruct F; apply kc_ren_wk_mem.
Qed.

Lemma ctx_ren_wk_rep F :
  ctx_ren (@id nat) unscoped.shift (@id nat) (@id nat) F (add_rep_var F).
Proof.
  split.
  - intros t; destruct F as [? ? ? ? tvs]; unfold add_rep_var; cbn.
    by rewrite list_lookup_fmap.
  - destruct F; apply kc_ren_wk_rep.
Qed.

Lemma ctx_ren_wk_size F :
  ctx_ren (@id nat) (@id nat) unscoped.shift (@id nat) F (add_size_var F).
Proof.
  split.
  - intros t; destruct F as [? ? ? ? tvs]; unfold add_size_var; cbn.
    by rewrite list_lookup_fmap.
  - destruct F; apply kc_ren_wk_size.
Qed.

Definition sub_id_memory (σ : nat -> memory) : Prop := forall n, σ n = VarM n.
Definition sub_id_representation (σ : nat -> representation) : Prop := forall n, σ n = VarR n.
Definition sub_id_size (σ : nat -> size) : Prop := forall n, σ n = VarS n.

Lemma sub_id_up_memory_memory σ : sub_id_memory σ -> sub_id_memory (up_memory_memory σ).
Proof. intros H [|n]; unfold up_memory_memory, unscoped.scons, core.funcomp; cbn; by rewrite ?H. Qed.

Lemma sub_id_up_representation_memory σ :
  sub_id_memory σ -> sub_id_memory (up_representation_memory σ).
Proof. intros H n; unfold up_representation_memory, core.funcomp; by rewrite H. Qed.

Lemma sub_id_up_size_memory σ : sub_id_memory σ -> sub_id_memory (up_size_memory σ).
Proof. intros H n; unfold up_size_memory, core.funcomp; by rewrite H. Qed.

Lemma sub_id_up_type_memory σ : sub_id_memory σ -> sub_id_memory (up_type_memory σ).
Proof. intros H n; unfold up_type_memory, core.funcomp; by rewrite H. Qed.

Lemma subst_kind_id σr σs κ :
  sub_id_representation σr -> sub_id_size σs -> subst_kind σr σs κ = κ.
Proof. intros Hr Hs; by apply idSubst_kind. Qed.

Lemma subst_kind_up_type σr σs κ :
  subst_kind (up_type_representation σr) (up_type_size σs) κ = subst_kind σr σs κ.
Proof.
  apply ext_kind; intros n; unfold up_type_representation, up_type_size, core.funcomp.
  - apply rinstId'_representation.
  - apply rinstId'_size.
Qed.

Lemma subst_kind_up_mem σr σs κ :
  subst_kind (up_memory_representation σr) (up_memory_size σs) κ = subst_kind σr σs κ.
Proof.
  apply ext_kind; intros n; unfold up_memory_representation, up_memory_size, core.funcomp.
  - apply rinstId'_representation.
  - apply rinstId'_size.
Qed.

Lemma subst_kind_up_rep σr σs κ :
  subst_kind (up_representation_representation σr) (up_representation_size σs)
    (ren_kind unscoped.shift unscoped.id κ)
  = ren_kind unscoped.shift unscoped.id (subst_kind σr σs κ).
Proof. rewrite renSubst_kind substRen_kind; apply ext_kind; intros n; reflexivity. Qed.

Lemma subst_kind_up_size σr σs κ :
  subst_kind (up_size_representation σr) (up_size_size σs)
    (ren_kind unscoped.id unscoped.shift κ)
  = ren_kind unscoped.id unscoped.shift (subst_kind σr σs κ).
Proof. rewrite renSubst_kind substRen_kind; apply ext_kind; intros n; reflexivity. Qed.

Lemma subst_kind_scons_rep ρ κ :
  subst_kind (unscoped.scons ρ VarR) VarS (ren_kind unscoped.shift unscoped.id κ) = κ.
Proof.
  rewrite renSubst_kind -{2}(instId'_kind κ); apply ext_kind; intros n; reflexivity.
Qed.

Lemma subst_kind_scons_size σ κ :
  subst_kind VarR (unscoped.scons σ VarS) (ren_kind unscoped.id unscoped.shift κ) = κ.
Proof.
  rewrite renSubst_kind -{2}(instId'_kind κ); apply ext_kind; intros n; reflexivity.
Qed.

Lemma has_kind_kind_ok F τ κ : has_kind F τ κ -> kind_ok (fc_kind_ctx F) κ.
Proof. intros H; apply has_kind_inv in H; by inversion H. Qed.

Lemma fc_type_vars_kc_update F upd :
  fc_type_vars (F <| fc_kind_ctx ::= upd |>) = fc_type_vars F.
Proof. by destruct F. Qed.

Lemma fc_type_vars_add_rep F :
  fc_type_vars (add_rep_var F) = map (ren_kind unscoped.shift unscoped.id) (fc_type_vars F).
Proof. by destruct F. Qed.

Lemma fc_type_vars_add_size F :
  fc_type_vars (add_size_var F) = map (ren_kind unscoped.id unscoped.shift) (fc_type_vars F).
Proof. by destruct F. Qed.

Definition kc_subst (σm : nat -> memory) (σr : nat -> representation) (σs : nat -> size)
    (K K' : kind_ctx) : Prop :=
  (forall n, n < kc_mem_vars K -> mem_ok K' (σm n)) /\
  (forall n, n < kc_rep_vars K -> rep_ok K' (σr n)) /\
  (forall n, n < kc_size_vars K -> size_ok K' (σs n)).

Lemma mem_ok_subst σm σr σs K K' μ :
  kc_subst σm σr σs K K' -> mem_ok K μ -> mem_ok K' (subst_memory σm μ).
Proof.
  intros (Hm & _ & _) Hok; destruct μ; cbn; [|constructor].
  inversion Hok; subst; by apply Hm.
Qed.

Lemma rep_ok_subst σm σr σs K K' ρ :
  kc_subst σm σr σs K K' -> rep_ok K ρ -> rep_ok K' (subst_representation σr ρ).
Proof.
  intros (_ & Hr & _); induction ρ using rep_ind; cbn; inversion 1; subst;
    [by apply Hr|constructor|constructor|constructor]; eauto using Forall_map_impl.
Qed.

Lemma size_ok_subst σm σr σs K K' σ :
  kc_subst σm σr σs K K' -> size_ok K σ -> size_ok K' (subst_size σr σs σ).
Proof.
  intros Hkc; induction σ using size_ind; cbn; inversion 1; subst;
    [by apply (proj2 (proj2 Hkc))|constructor|constructor|constructor|constructor];
    eauto using Forall_map_impl, rep_ok_subst.
Qed.

Lemma kind_ok_subst σm σr σs K K' κ :
  kc_subst σm σr σs K K' -> kind_ok K κ -> kind_ok K' (subst_kind σr σs κ).
Proof.
  intros Hkc; destruct κ; inversion 1; subst; constructor;
    eauto using rep_ok_subst, size_ok_subst.
Qed.

Lemma kc_subst_type σm σr σs K K' :
  kc_subst σm σr σs K K' ->
  kc_subst (up_type_memory σm) (up_type_representation σr) (up_type_size σs) K K'.
Proof.
  intros (Hm & Hr & Hs); split; [|split]; intros n Hn;
    unfold up_type_memory, up_type_representation, up_type_size, core.funcomp.
  - rewrite (ren_memory_id _ _ pw_id_uid); by apply Hm.
  - rewrite (ren_representation_id _ _ pw_id_uid); by apply Hr.
  - rewrite (ren_size_id _ _ _ pw_id_uid pw_id_uid); by apply Hs.
Qed.

Lemma kc_subst_mem σm σr σs K K' :
  kc_subst σm σr σs K K' ->
  kc_subst (up_memory_memory σm) (up_memory_representation σr) (up_memory_size σs)
    (set kc_mem_vars S K) (set kc_mem_vars S K').
Proof.
  intros (Hm & Hr & Hs); split; [|split].
  - intros [|n] Hn; unfold up_memory_memory, unscoped.scons, core.funcomp; cbn.
    + apply OKVarM; destruct K'; cbn; unfold unscoped.var_zero; lia.
    + apply (proj1 (mem_ok_ren _ _ _ _ _ _ (kc_ren_wk_mem K'))), Hm.
      destruct K; cbn in *; lia.
  - intros n Hn; unfold up_memory_representation, core.funcomp.
    rewrite (ren_representation_id _ _ pw_id_uid).
    apply (rep_ok_mono K'); [by destruct K'|apply Hr; by destruct K].
  - intros n Hn; unfold up_memory_size, core.funcomp.
    rewrite (ren_size_id _ _ _ pw_id_uid pw_id_uid).
    apply (size_ok_mono K'); [by destruct K'|by destruct K'|apply Hs; by destruct K].
Qed.

Lemma kc_subst_rep σm σr σs K K' :
  kc_subst σm σr σs K K' ->
  kc_subst (up_representation_memory σm) (up_representation_representation σr)
    (up_representation_size σs) (set kc_rep_vars S K) (set kc_rep_vars S K').
Proof.
  intros (Hm & Hr & Hs); split; [|split].
  - intros n Hn; unfold up_representation_memory, core.funcomp.
    rewrite (ren_memory_id _ _ pw_id_uid).
    apply (mem_ok_mono K'); [by destruct K'|apply Hm; by destruct K].
  - intros [|n] Hn; unfold up_representation_representation, unscoped.scons, core.funcomp; cbn.
    + apply OKVarR; destruct K'; cbn; unfold unscoped.var_zero; lia.
    + apply (proj1 (rep_ok_ren _ _ _ _ (proj1 (proj2 (kc_ren_wk_rep K'))))), Hr.
      destruct K; cbn in *; lia.
  - intros n Hn; unfold up_representation_size, core.funcomp.
    destruct (kc_ren_wk_rep K') as (_ & Hrr & Hss).
    apply (proj1 (size_ok_ren _ _ _ _ _ Hrr Hss)).
    apply Hs; by destruct K.
Qed.

Lemma kc_subst_size σm σr σs K K' :
  kc_subst σm σr σs K K' ->
  kc_subst (up_size_memory σm) (up_size_representation σr) (up_size_size σs)
    (set kc_size_vars S K) (set kc_size_vars S K').
Proof.
  intros (Hm & Hr & Hs); split; [|split].
  - intros n Hn; unfold up_size_memory, core.funcomp.
    rewrite (ren_memory_id _ _ pw_id_uid).
    apply (mem_ok_mono K'); [by destruct K'|apply Hm; by destruct K].
  - intros n Hn; unfold up_size_representation, core.funcomp.
    rewrite (ren_representation_id _ _ pw_id_uid).
    apply (rep_ok_mono K'); [by destruct K'|apply Hr; by destruct K].
  - intros [|n] Hn; unfold up_size_size, unscoped.scons, core.funcomp; cbn.
    + apply OKVarS; destruct K'; cbn; unfold unscoped.var_zero; lia.
    + destruct (kc_ren_wk_size K') as (_ & Hrr & Hss).
      apply (proj1 (size_ok_ren _ _ _ _ _ Hrr Hss)), Hs.
      destruct K; cbn in *; lia.
Qed.

Definition kind_rel_ok (R : kind -> kind -> Prop) : Prop :=
  (forall κ, R κ κ) /\
  (forall ξr ξs κ κ', R κ κ' -> R (ren_kind ξr ξs κ) (ren_kind ξr ξs κ')).

Lemma kind_rel_ok_eq : kind_rel_ok eq.
Proof. split; [done|by intros ???? ->]. Qed.

Lemma kind_rel_ok_subkind : kind_rel_ok subkind_of.
Proof. split; [apply subkind_of_refl|intros; by apply subkind_of_ren]. Qed.

Definition ctx_rel (R : kind -> kind -> Prop)
    (σm : nat -> memory) (σr : nat -> representation) (σs : nat -> size) (σt : nat -> type)
    (F F' : function_ctx) : Prop :=
  kc_subst σm σr σs (fc_kind_ctx F) (fc_kind_ctx F') /\
  forall t κ, has_kind F (VarT t) κ ->
    exists κ', R κ' (subst_kind σr σs κ) /\ has_kind F' (σt t) κ'.

Lemma ctx_rel_cons R σm σr σs σt F F' κ0 :
  kind_rel_ok R ->
  ctx_rel R σm σr σs σt F F' ->
  ctx_rel R (up_type_memory σm) (up_type_representation σr) (up_type_size σs) (up_type_type σt)
    (F <| fc_type_vars ::= cons κ0 |>) (F' <| fc_type_vars ::= cons (subst_kind σr σs κ0) |>).
Proof.
  intros [Hrefl _] [Hkc Hv]; split; [rewrite !fc_kind_ctx_ty_update; by apply kc_subst_type|].
  intros [|t] κ Hk.
  - pose proof (has_kind_type_kind _ _ _ Hk) as Hlk.
    cbn [layout.type_kind] in Hlk; rewrite fc_type_vars_get_upd in Hlk; cbn in Hlk.
    injection Hlk as ->.
    pose proof (has_kind_kind_ok _ _ _ Hk) as Hok; rewrite fc_kind_ctx_ty_update in Hok.
    exists (subst_kind σr σs κ); split; [rewrite subst_kind_up_type; apply Hrefl|].
    apply KVar; [by rewrite fc_type_vars_get_upd|].
    rewrite fc_kind_ctx_ty_update; by eapply kind_ok_subst.
  - apply (proj1 (has_kind_var_wk_ty F t κ κ0)) in Hk.
    destruct (Hv t κ Hk) as (κ' & HR & Hk').
    exists κ'; split; [by rewrite subst_kind_up_type|].
    by apply (proj1 (has_kind_wk_ty F' (σt t) κ' _)).
Qed.

Lemma ctx_rel_mem R σm σr σs σt F F' :
  ctx_rel R σm σr σs σt F F' ->
  ctx_rel R (up_memory_memory σm) (up_memory_representation σr) (up_memory_size σs)
    (up_memory_type σt)
    (F <| fc_kind_ctx ::= set kc_mem_vars S |>) (F' <| fc_kind_ctx ::= set kc_mem_vars S |>).
Proof.
  intros [Hkc Hv]; split; [destruct F, F'; cbn in *; by apply kc_subst_mem|].
  intros t κ Hk.
  pose proof (has_kind_kind_ok _ _ _ Hk) as Hok.
  pose proof (has_kind_type_kind _ _ _ Hk) as Hlk.
  cbn [layout.type_kind] in Hlk; rewrite fc_type_vars_kc_update in Hlk.
  assert (Hk' : has_kind F (VarT t) κ).
  { apply KVar; [done|].
    apply (kind_ok_kc _ _ _ Hok); by destruct F as [? ? ? [km kr ks] ?]. }
  destruct (Hv t κ Hk') as (κ' & HR & Hk'').
  exists κ'; split; [by rewrite subst_kind_up_mem|].
  unfold up_memory_type, core.funcomp.
  rewrite -(ren_kind_id (@id nat) (@id nat) κ' pw_id_id pw_id_id).
  by apply (has_kind_ren _ _ _ Hk''), ctx_ren_wk_mem.
Qed.

Lemma ctx_rel_rep R σm σr σs σt F F' :
  kind_rel_ok R ->
  ctx_rel R σm σr σs σt F F' ->
  ctx_rel R (up_representation_memory σm) (up_representation_representation σr)
    (up_representation_size σs) (up_representation_type σt) (add_rep_var F) (add_rep_var F').
Proof.
  intros [_ Hren] [Hkc Hv]; split;
    [destruct F, F'; unfold add_rep_var; cbn in *; by apply kc_subst_rep|].
  intros t κ Hk.
  pose proof (has_kind_kind_ok _ _ _ Hk) as Hok.
  pose proof (has_kind_type_kind _ _ _ Hk) as Hlk.
  cbn [layout.type_kind] in Hlk.
  rewrite fc_type_vars_add_rep list_lookup_fmap in Hlk.
  destruct (fc_type_vars F !! t) as [κ0|] eqn:Ht;
    cbn [fmap option_fmap option_map] in Hlk; [|done].
  injection Hlk as <-.
  destruct (proj2 (ctx_ren_wk_rep F)) as (_ & Hrr & Hss).
  apply (proj2 (kind_ok_ren' _ _ _ _ κ0 Hrr Hss)) in Hok.
  assert (Hk0 : has_kind F (VarT t) κ0) by by apply KVar.
  destruct (Hv t κ0 Hk0) as (κ' & HR & Hk').
  exists (ren_kind unscoped.shift unscoped.id κ'); split;
    [rewrite subst_kind_up_rep; by apply Hren|].
  by apply (has_kind_ren _ _ _ Hk'), ctx_ren_wk_rep.
Qed.

Lemma ctx_rel_size R σm σr σs σt F F' :
  kind_rel_ok R ->
  ctx_rel R σm σr σs σt F F' ->
  ctx_rel R (up_size_memory σm) (up_size_representation σr) (up_size_size σs)
    (up_size_type σt) (add_size_var F) (add_size_var F').
Proof.
  intros [_ Hren] [Hkc Hv]; split;
    [destruct F, F'; unfold add_size_var; cbn in *; by apply kc_subst_size|].
  intros t κ Hk.
  pose proof (has_kind_kind_ok _ _ _ Hk) as Hok.
  pose proof (has_kind_type_kind _ _ _ Hk) as Hlk.
  cbn [layout.type_kind] in Hlk.
  rewrite fc_type_vars_add_size list_lookup_fmap in Hlk.
  destruct (fc_type_vars F !! t) as [κ0|] eqn:Ht;
    cbn [fmap option_fmap option_map] in Hlk; [|done].
  injection Hlk as <-.
  destruct (proj2 (ctx_ren_wk_size F)) as (_ & Hrr & Hss).
  apply (proj2 (kind_ok_ren' _ _ _ _ κ0 Hrr Hss)) in Hok.
  assert (Hk0 : has_kind F (VarT t) κ0) by by apply KVar.
  destruct (Hv t κ0 Hk0) as (κ' & HR & Hk').
  exists (ren_kind unscoped.id unscoped.shift κ'); split;
    [rewrite subst_kind_up_size; by apply Hren|].
  by apply (has_kind_ren _ _ _ Hk'), ctx_ren_wk_size.
Qed.

Lemma has_kind_subst_gen :
  (forall τ σm σr σs σt F F' κ,
      sub_id_memory σm -> ctx_rel eq σm σr σs σt F F' ->
      has_kind F τ κ -> has_kind F' (subst_type σm σr σs σt τ) (subst_kind σr σs κ)) /\
  (forall ϕ σm σr σs σt F F',
      sub_id_memory σm -> ctx_rel eq σm σr σs σt F F' ->
      has_kind_ft F ϕ -> has_kind_ft F' (subst_function_type σm σr σs σt ϕ)) /\
  (forall ϕ σm σr σs σt F F',
      sub_id_memory σm -> ctx_rel eq σm σr σs σt F F' ->
      has_kind_ift F ϕ -> has_kind_ift F' (subst_inner_function_type σm σr σs σt ϕ)).
Proof.
  apply type_and_function_ind.
  - intros t σm σr σs σt F F' κ Hm Hctx Hk.
    by destruct (proj2 Hctx _ _ Hk) as (κ' & -> & Hk').
  - intros κ0 σm σr σs σt F F' κ Hm Hctx Hk.
    by inversion Hk; subst; cbn; constructor.
  - intros κ0 nt σm σr σs σt F F' κ Hm Hctx Hk.
    by inversion Hk; subst; cbn; constructor.
  - intros κ0 τs IH σm σr σs σt F F' κ Hm Hctx Hk.
    inversion Hk; subst; cbn.
    apply KSum, Forall3_map_12.
    eapply Forall3_Forall_impl; [eassumption|exact IH|].
    intros τ ρ ξ HR HP; by apply (HR σm σr σs σt F F' _ Hm Hctx HP).
  - intros κ0 τs IH σm σr σs σt F F' κ Hm Hctx Hk.
    inversion Hk; subst; cbn.
    apply KVariant, Forall3_map_12.
    eapply Forall3_Forall_impl; [eassumption|exact IH|].
    intros τ σ ξ HR HP; by apply (HR σm σr σs σt F F' _ Hm Hctx HP).
  - intros κ0 τs IH σm σr σs σt F F' κ Hm Hctx Hk.
    inversion Hk; subst; cbn.
    apply KProd, Forall3_map_12.
    eapply Forall3_Forall_impl; [eassumption|exact IH|].
    intros τ ρ ξ HR HP; by apply (HR σm σr σs σt F F' _ Hm Hctx HP).
  - intros κ0 τs IH σm σr σs σt F F' κ Hm Hctx Hk.
    inversion Hk; subst; cbn.
    apply KStruct, Forall3_map_12.
    eapply Forall3_Forall_impl; [eassumption|exact IH|].
    intros τ σ ξ HR HP; by apply (HR σm σr σs σt F F' _ Hm Hctx HP).
  - intros κ0 μ β t IH σm σr σs σt F F' κ Hm Hctx Hk.
    inversion Hk; subst; cbn.
    + rewrite Hm.
      apply KRefVar with (σ := subst_size σr σs σ) (ξ := ξ);
        [|by apply (IH σm σr σs σt F F' (MEMTYPE σ ξ))].
      pose proof (mem_ok_subst _ _ _ _ _ _ (proj1 Hctx) H5) as Hmo.
      cbn in Hmo; by rewrite Hm in Hmo.
    + apply KRefMM with (σ := subst_size σr σs σ) (ξ := ξ);
        by apply (IH σm σr σs σt F F' (MEMTYPE σ ξ)).
    + apply KRefGC with (σ := subst_size σr σs σ) (ξ := ξ);
        by apply (IH σm σr σs σt F F' (MEMTYPE σ ξ)).
  - intros κ0 ft IH σm σr σs σt F F' κ Hm Hctx Hk.
    inversion Hk; subst; cbn.
    apply KCodeRef; by eapply IH; eauto.
  - intros κ0 t IH σm σr σs σt F F' κ Hm Hctx Hk.
    inversion Hk; subst; cbn.
    apply KSer; by apply (IH σm σr σs σt F F' (VALTYPE ρ ξ)).
  - intros κ0 ρ σm σr σs σt F F' κ Hm Hctx Hk.
    inversion Hk; subst; cbn.
    apply KPlug; by eapply rep_ok_subst; [apply Hctx|].
  - intros κ0 σ σm σr σs σt F F' κ Hm Hctx Hk.
    inversion Hk; subst; cbn.
    apply KSpan; by eapply size_ok_subst; [apply Hctx|].
  - intros κ0 t IH σm σr σs σt F F' κ Hm Hctx Hk.
    inversion Hk; subst; cbn.
    eapply KRec.
    + by eapply kind_ok_subst; [apply Hctx|].
    + eapply (IH (up_type_memory σm) (up_type_representation σr) (up_type_size σs)
                (up_type_type σt) (F <| fc_type_vars ::= cons κ |>)
                (F' <| fc_type_vars ::= cons (subst_kind σr σs κ) |>));
        eauto using sub_id_up_type_memory, ctx_rel_cons, kind_rel_ok_eq.
    + rewrite subst_kind_up_type; by apply subkind_of_subst.
  - intros κ0 t IH σm σr σs σt F F' κ Hm Hctx Hk.
    inversion Hk; subst; cbn.
    apply KExistsMem; [by eapply kind_ok_subst; [apply Hctx|]|].
    rewrite -subst_kind_up_mem.
    eapply (IH (up_memory_memory σm) (up_memory_representation σr) (up_memory_size σs)
              (up_memory_type σt) (F <| fc_kind_ctx ::= set kc_mem_vars S |>)
              (F' <| fc_kind_ctx ::= set kc_mem_vars S |>));
      eauto using sub_id_up_memory_memory, ctx_rel_mem.
  - intros κ0 t IH σm σr σs σt F F' κ Hm Hctx Hk.
    inversion Hk; subst; cbn.
    apply KExistsRep; [by eapply kind_ok_subst; [apply Hctx|]|].
    rewrite -subst_kind_up_rep.
    eapply (IH (up_representation_memory σm) (up_representation_representation σr)
              (up_representation_size σs) (up_representation_type σt)
              (add_rep_var F) (add_rep_var F'));
      eauto using sub_id_up_representation_memory, ctx_rel_rep, kind_rel_ok_eq.
  - intros κ0 t IH σm σr σs σt F F' κ Hm Hctx Hk.
    inversion Hk; subst; cbn.
    apply KExistsSize; [by eapply kind_ok_subst; [apply Hctx|]|].
    rewrite -subst_kind_up_size.
    eapply (IH (up_size_memory σm) (up_size_representation σr) (up_size_size σs)
              (up_size_type σt) (add_size_var F) (add_size_var F'));
      eauto using sub_id_up_size_memory, ctx_rel_size, kind_rel_ok_eq.
  - intros κ1 κ2 t IH σm σr σs σt F F' κ Hm Hctx Hk.
    inversion Hk; subst; cbn.
    apply KExistsType; [by eapply kind_ok_subst; [apply Hctx|]|by eapply kind_ok_subst; [apply Hctx|]|].
    rewrite -(subst_kind_up_type σr σs κ).
    eapply (IH (up_type_memory σm) (up_type_representation σr) (up_type_size σs)
              (up_type_type σt) (F <| fc_type_vars ::= cons κ2 |>)
              (F' <| fc_type_vars ::= cons (subst_kind σr σs κ2) |>));
      eauto using sub_id_up_type_memory, ctx_rel_cons, kind_rel_ok_eq.
  - intros τs1 τs2 IH1 IH2 σm σr σs σt F F' Hm Hctx Hk.
    inversion Hk; subst; cbn.
    apply (KMonoFun _ _ _ (map (subst_kind σr σs) κs1) (map (subst_kind σr σs) κs2)).
    + apply Forall2_map_12.
      eapply Forall2_Forall_impl; [eassumption|exact IH1|].
      intros τ κ HR HP; by apply (HR σm σr σs σt F F' _ Hm Hctx HP).
    + apply Forall2_map_12.
      eapply Forall2_Forall_impl; [eassumption|exact IH2|].
      intros τ κ HR HP; by apply (HR σm σr σs σt F F' _ Hm Hctx HP).
  - intros κ0 ft IH σm σr σs σt F F' Hm Hctx Hk.
    inversion Hk; subst; cbn.
    apply KForallType; [by eapply kind_ok_subst; [apply Hctx|]|].
    eapply (IH (up_type_memory σm) (up_type_representation σr) (up_type_size σs)
              (up_type_type σt) (F <| fc_type_vars ::= cons κ0 |>)
              (F' <| fc_type_vars ::= cons (subst_kind σr σs κ0) |>));
      eauto using sub_id_up_type_memory, ctx_rel_cons, kind_rel_ok_eq.
  - intros ft IH σm σr σs σt F F' Hm Hctx Hk.
    inversion Hk; subst; cbn.
    apply KInnerFun; by eapply IH; eauto.
  - intros ft IH σm σr σs σt F F' Hm Hctx Hk.
    inversion Hk; subst; cbn.
    apply KForallMem.
    eapply (IH (up_memory_memory σm) (up_memory_representation σr) (up_memory_size σs)
              (up_memory_type σt) (F <| fc_kind_ctx ::= set kc_mem_vars S |>)
              (F' <| fc_kind_ctx ::= set kc_mem_vars S |>));
      eauto using sub_id_up_memory_memory, ctx_rel_mem.
  - intros ft IH σm σr σs σt F F' Hm Hctx Hk.
    inversion Hk; subst; cbn.
    apply KForallRep.
    eapply (IH (up_representation_memory σm) (up_representation_representation σr)
              (up_representation_size σs) (up_representation_type σt)
              (add_rep_var F) (add_rep_var F'));
      eauto using sub_id_up_representation_memory, ctx_rel_rep, kind_rel_ok_eq.
  - intros ft IH σm σr σs σt F F' Hm Hctx Hk.
    inversion Hk; subst; cbn.
    apply KForallSize.
    eapply (IH (up_size_memory σm) (up_size_representation σr) (up_size_size σs)
              (up_size_type σt) (add_size_var F) (add_size_var F'));
      eauto using sub_id_up_size_memory, ctx_rel_size, kind_rel_ok_eq.
Qed.

(* The single-substitution form the callers below use: kinds are untouched and the type
   substitution is exact. *)
Definition ctx_subst (σt : nat -> type) (F F' : function_ctx) : Prop :=
  fc_kind_ctx F' = fc_kind_ctx F /\
  forall t κ, has_kind F (VarT t) κ -> has_kind F' (σt t) κ.

Lemma ctx_subst_rel σm σr σs σt F F' :
  sub_id_memory σm -> sub_id_representation σr -> sub_id_size σs ->
  ctx_subst σt F F' -> ctx_rel eq σm σr σs σt F F'.
Proof.
  intros Hm Hr Hs [Hkc Hv]; split.
  - rewrite Hkc; split; [|split]; intros n Hn; [rewrite Hm|rewrite Hr|rewrite Hs]; by constructor.
  - intros t κ Hk; exists κ; split; [by rewrite (subst_kind_id σr σs _ Hr Hs)|by apply Hv].
Qed.

Lemma has_kind_subst :
  (forall τ σm σr σs σt F F' κ,
      sub_id_memory σm -> sub_id_representation σr -> sub_id_size σs ->
      ctx_subst σt F F' ->
      has_kind F τ κ -> has_kind F' (subst_type σm σr σs σt τ) κ) /\
  (forall ϕ σm σr σs σt F F',
      sub_id_memory σm -> sub_id_representation σr -> sub_id_size σs ->
      ctx_subst σt F F' ->
      has_kind_ft F ϕ -> has_kind_ft F' (subst_function_type σm σr σs σt ϕ)) /\
  (forall ϕ σm σr σs σt F F',
      sub_id_memory σm -> sub_id_representation σr -> sub_id_size σs ->
      ctx_subst σt F F' ->
      has_kind_ift F ϕ -> has_kind_ift F' (subst_inner_function_type σm σr σs σt ϕ)).
Proof.
  destruct has_kind_subst_gen as (Hτ & Hft & Hift).
  split; [|split]; intros * Hm Hr Hs Hctx Hk.
  - rewrite -(subst_kind_id σr σs κ Hr Hs); by eapply Hτ; eauto using ctx_subst_rel.
  - by eapply Hft; eauto using ctx_subst_rel.
  - by eapply Hift; eauto using ctx_subst_rel.
Qed.

Lemma ctx_subst_scons F τv κv :
  has_kind F τv κv ->
  ctx_subst (unscoped.scons τv VarT) (F <| fc_type_vars ::= cons κv |>) F.
Proof.
  intros Hv; split; [by rewrite fc_kind_ctx_ty_update|].
  intros [|t] κ Hk.
  - pose proof (has_kind_type_kind _ _ _ Hk) as Hlk.
    cbn [layout.type_kind] in Hlk; rewrite fc_type_vars_get_upd in Hlk; cbn in Hlk.
    by injection Hlk as ->.
  - by apply (proj1 (has_kind_var_wk_ty F t κ κv)).
Qed.

Lemma has_kind_env_to_has_kind_subst τ : ∀ F τv κv κ τ',
  refreshed_kinds F (subst_type VarM VarR VarS (unscoped.scons τv VarT) τ) τ' →
  has_kind F τv κv →
  has_kind (F <| fc_type_vars ::= cons κv |>) τ κ →
  has_kind F τ' κ.
Proof.
  intros F τv κv κ τ' Hrefresh Hv Hkind.
  assert (Hsub : has_kind F (subst_type VarM VarR VarS (unscoped.scons τv VarT) τ) κ)
    by (eapply (proj1 has_kind_subst);
        [done|done|done|by apply (ctx_subst_scons F τv κv)|exact Hkind]).
  by rewrite -(refreshed_kinds_has_kind _ _ _ _ Hsub Hrefresh).
Qed.

Lemma has_kinds_env_to_has_kinds_subst τs : ∀ F τv κv κs τs',
  Forall2 (refreshed_kinds F) (map (subst_type VarM VarR VarS (unscoped.scons τv VarT)) τs) τs' →
  has_kind F τv κv →
  Forall2 (has_kind (F <| fc_type_vars ::= cons κv |>)) τs κs →
  Forall2 (has_kind F) τs' κs.
Proof.
  induction τs as [|τ τs IH]; intros F τv κv κs τs' Hrefresh Hv Hkind; cbn in Hrefresh.
  - by inversion Hrefresh; subst; inversion Hkind; subst; constructor.
  - inversion Hrefresh as [|a b l k Hhd Htl]; subst.
    inversion Hkind as [|a' b' l' k' Hkh Hkt]; subst.
    constructor.
    + exact (has_kind_env_to_has_kind_subst τ F τv κv _ _ Hhd Hv Hkh).
    + exact (IH F τv κv _ _ Htl Hv Hkt).
Qed.

Lemma needs_name_fwd ϕ F τ κ ϕ' :
  has_kind F τ κ →
  refreshed_kinds_ift F
    (subst_inner_function_type VarM VarR VarS (unscoped.scons τ VarT) ϕ) ϕ' →
  has_kind_ift (F <| fc_type_vars ::= cons κ |>) ϕ →
  has_kind_ift F ϕ'.
Proof.
  intros Ht Hrf Hk.
  assert (Hsub : has_kind_ift F
                   (subst_inner_function_type VarM VarR VarS (unscoped.scons τ VarT) ϕ)).
  { eapply (proj2 (proj2 has_kind_subst));
      [done|done|done|by apply (ctx_subst_scons F τ κ)|exact Hk]. }
  by rewrite -(proj2 (proj2 refreshed_kinds_det) _ _ _ Hsub Hrf).
Qed.

Lemma has_kind_ift_through_inst F ϕ ϕ' τ κ :
  inner_function_type_inst F (TypeI τ) (ForallTypeT κ ϕ) ϕ' →
  has_kind F τ κ →
  has_kind_ift F (ForallTypeT κ ϕ) →
  has_kind_ift F ϕ'.
Proof.
  intros Hinst Ht Hk.
  inversion Hinst as [F1 ϕ1 τ1 κ1 κ1' ϕ1' Ht1 Hsub Hrf]; subst.
  inversion Hk as [|F2 κ2 ϕ2 Hok Hk']; subst.
  eapply needs_name_fwd; [exact Ht|exact Hrf|exact Hk'].
Qed.

Lemma has_kind_ft_through_inst_type F ϕ ϕ' τ κ :
  function_type_inst F (TypeI τ) (InnerFunT (ForallTypeT κ ϕ)) ϕ' →
  has_kind F τ κ →
  has_kind_ft F (InnerFunT (ForallTypeT κ ϕ)) →
  has_kind_ft F ϕ'.
Proof.
  intros Hinst Ht Hk.
  inversion Hinst as [F1 ϕ1 ix1 ϕ1' Hi| | |]; subst.
  inversion Hk as [F2 ϕ2 Hk'| | |]; subst.
  apply KInnerFun.
  eapply has_kind_ift_through_inst; [exact Hi|exact Ht|exact Hk'].
Qed.

  (* copied from typechecker.v *)
Fixpoint get_all_lefts {A B : Type} (l: list (A + B)) : list A :=
  match l with
  | [] => []
  | a::l =>
      match a with
      | inl a => a:: get_all_lefts l
      | inr _ => get_all_lefts l
      end
  end.
Fixpoint get_all_rights {A B : Type} (l: list (A + B)) : list B :=
  match l with
  | [] => []
  | a::l =>
      match a with
      | inl _ => get_all_rights l
      | inr b => b :: get_all_rights l
      end
  end.
Definition kind_of_num (nt : num_type) : kind :=
  match nt with
  | IntT I32T => VALTYPE (AtomR I32R) NoRefs
  | IntT I64T => VALTYPE (AtomR I64R) NoRefs
  | FloatT F32T => VALTYPE (AtomR F32R) NoRefs
  | FloatT F64T => VALTYPE (AtomR F64R) NoRefs
  end.

Definition kind_of_node (F : function_ctx) (τ : type) : kind :=
  match τ with
  | VarT t => match F.(fc_type_vars) !! t with
             | Some κ => κ
             | None => VALTYPE (AtomR I32R) NoRefs
             end
  | I31T κ | NumT κ _ | SumT κ _ | VariantT κ _ | ProdT κ _ | StructT κ _
  | RefT κ _ _ _ | CodeRefT κ _ | SerT κ _ | PlugT κ _ | SpanT κ _
  | RecT κ _ | ExistsMemT κ _ | ExistsRepT κ _ | ExistsSizeT κ _
  | ExistsTypeT κ _ _ => κ
  end.

Definition get_rep_or_size κ :=
  match κ with
  | VALTYPE ρ _ => inl ρ
  | MEMTYPE σ _ => inr σ
  end.
(* rebuilds the cached kind annotations that [subst] leaves stale *)
Fixpoint refresh_kinds (F : function_ctx) (τ : type) : type :=
  match τ with
  | VarT t => VarT t
  | I31T _ => I31T (VALTYPE (AtomR PtrR) NoRefs)
  | NumT _ nt => NumT (kind_of_num nt) nt
  | SumT _ τs =>
      let τs' := map (refresh_kinds F) τs in
      let κs := map (kind_of_node F) τs' in
      SumT (VALTYPE (SumR (get_all_lefts (map get_rep_or_size κs)))
              (ref_flag_lub (map kind_ref_flag κs))) τs'
  | VariantT _ τs =>
      let τs' := map (refresh_kinds F) τs in
      let κs := map (kind_of_node F) τs' in
      VariantT (MEMTYPE (SumS (get_all_rights (map get_rep_or_size κs)))
                  (ref_flag_lub (map kind_ref_flag κs))) τs'
  | ProdT _ τs =>
      let τs' := map (refresh_kinds F) τs in
      let κs := map (kind_of_node F) τs' in
      ProdT (VALTYPE (ProdR (get_all_lefts (map get_rep_or_size κs)))
               (ref_flag_lub (map kind_ref_flag κs))) τs'
  | StructT _ τs =>
      let τs' := map (refresh_kinds F) τs in
      let κs := map (kind_of_node F) τs' in
      StructT (MEMTYPE (ProdS (get_all_rights (map get_rep_or_size κs)))
                 (ref_flag_lub (map kind_ref_flag κs))) τs'
  | RefT _ μ β τ =>
      let κ := match μ with
               | BaseM MemGC => VALTYPE (AtomR PtrR) GCRefs
               | _ => VALTYPE (AtomR PtrR) AnyRefs
               end in
      RefT κ μ β (refresh_kinds F τ)
  | CodeRefT _ ϕ => CodeRefT (VALTYPE (AtomR I32R) NoRefs) (refresh_kinds_ft F ϕ)
  | SerT _ τ =>
      let τ' := refresh_kinds F τ in
      let κ := match kind_of_node F τ' with
               | VALTYPE ρ ξ => MEMTYPE (RepS ρ) ξ
               | MEMTYPE σ ξ => MEMTYPE σ ξ
               end in
      SerT κ τ'
  | PlugT _ ρ => PlugT (VALTYPE ρ NoRefs) ρ
  | SpanT _ σ => SpanT (MEMTYPE σ NoRefs) σ
  | RecT κ τ => RecT κ (refresh_kinds (F <| fc_type_vars ::= cons κ |>) τ)
  | ExistsMemT _ τ =>
      let τ' := refresh_kinds (F <| fc_kind_ctx ::= set kc_mem_vars S |>) τ in
      let κ := kind_of_node ((F <| fc_kind_ctx ::= set kc_mem_vars S |>)) τ' in
      ExistsMemT κ τ'
  | ExistsRepT _ τ =>
      let τ' := refresh_kinds (add_rep_var F) τ in
      ExistsRepT (unshift_rep_kind (kind_of_node (add_rep_var F) τ')) τ'
  | ExistsSizeT _ τ =>
      let τ' := refresh_kinds (add_size_var F) τ in
      ExistsSizeT (unshift_size_kind (kind_of_node (add_size_var F) τ')) τ'
  | ExistsTypeT _ κ0 τ =>
      let τ' := refresh_kinds (F <| fc_type_vars ::= cons κ0 |>) τ in
      let κ := kind_of_node ((F <| fc_type_vars ::= cons κ0 |>)) τ' in
      ExistsTypeT κ κ0 τ'
  end
with refresh_kinds_ift (F : function_ctx) (ϕ : inner_function_type) : inner_function_type :=
       match ϕ with
       | MonoFunT τs1 τs2 => MonoFunT (map (refresh_kinds F) τs1) (map (refresh_kinds F) τs2)
       | ForallTypeT κ ϕ => ForallTypeT κ (refresh_kinds_ift (F <| fc_type_vars ::= cons κ |>) ϕ)
       end
with refresh_kinds_ft (F : function_ctx) (ϕ : Core.function_type) : Core.function_type :=
       match ϕ with
       | InnerFunT ϕ => InnerFunT (refresh_kinds_ift F ϕ)
       | ForallMemT ϕ => ForallMemT (refresh_kinds_ft (F <| fc_kind_ctx ::= set kc_mem_vars S |>) ϕ)
       | ForallRepT ϕ => ForallRepT (refresh_kinds_ft (add_rep_var F) ϕ)
       | ForallSizeT ϕ => ForallSizeT (refresh_kinds_ft (add_size_var F) ϕ)
       end.

(* copied from typechecker.v *)
Lemma refresh_kinds_eq_mod_kinds :
  (forall τ F, type_eq_mod_kinds (refresh_kinds F τ) τ) /\
    (forall ϕ F, function_type_eq_mod_kinds (refresh_kinds_ft F ϕ) ϕ) /\
    (forall ϕ F, inner_function_type_eq_mod_kinds (refresh_kinds_ift F ϕ) ϕ).
Proof.
  apply type_and_function_ind.
  - intros idx F; simpl; reflexivity.
  - intros κ F; simpl; exact I.
  - intros κ nt F; simpl; reflexivity.
  - intros κ ts IH F; simpl; induction IH as [|t ts' Hh Ht IHl]; simpl;
      [exact I | split; [apply Hh | exact IHl]].
  - intros κ ts IH F; simpl; induction IH as [|t ts' Hh Ht IHl]; simpl;
      [exact I | split; [apply Hh | exact IHl]].
  - intros κ ts IH F; simpl; induction IH as [|t ts' Hh Ht IHl]; simpl;
      [exact I | split; [apply Hh | exact IHl]].
  - intros κ ts IH F; simpl; induction IH as [|t ts' Hh Ht IHl]; simpl;
      [exact I | split; [apply Hh | exact IHl]].
  - intros κ μ β t IH F; simpl; split; [reflexivity | split; [reflexivity | apply IH]].
  - intros κ ft IH F; simpl; apply IH.
  - intros κ t IH F; simpl; apply IH.
  - intros κ ρ F; simpl; reflexivity.
  - intros κ σ F; simpl; reflexivity.
  - intros κ t IH F; simpl; apply IH.
  - intros κ t IH F; simpl; apply IH.
  - intros κ t IH F; simpl; apply IH.
  - intros κ t IH F; simpl; apply IH.
  - intros κ1 κ2 t IH F; simpl; split; [reflexivity | apply IH].
  - intros τs1 τs2 IH1 IH2 F; simpl; split;
      [ induction IH1 as [|t ts' Hh Ht IHl]; simpl; [exact I | split; [apply Hh | exact IHl]]
      | induction IH2 as [|t ts' Hh Ht IHl]; simpl; [exact I | split; [apply Hh | exact IHl]] ].
  - intros κ ft IH F; simpl; split; [reflexivity | apply IH].
  - done.
  - intros ft IH F; simpl; apply IH.
  - intros ft IH F; simpl; apply IH.
  - intros ft IH F; simpl; apply IH.
Qed.


Lemma kind_of_node_good F τ κ:
  has_kind F τ κ -> κ = kind_of_node F τ.
Proof.
  intros Hkind.
  induction Hkind using has_kind_ind' with (P0 := const (const True)) (Pi := const (const True));
    intros; cbn; try done; try (rewrite <- IHHkind; done).
  rewrite H. done.
Qed.

Lemma map_refresh_kinds_id F τs κs :
  Forall2 (has_kind F) τs κs →
  Forall (λ τ, ∀ F κ, has_kind F τ κ → τ = refresh_kinds F τ) τs →
  map (refresh_kinds F) τs = τs.
Proof.
  induction 1 as [|τ κ τs κs Hk _ IHl]; cbn; [done|].
  inversion 1 as [|? ? Hhd Htl]; subst.
  by rewrite -(Hhd _ _ Hk) (IHl Htl).
Qed.

Lemma refresh_kinds_id_val F τs ρs ξs :
  Forall3 (λ τ ρ ξ, has_kind F τ (VALTYPE ρ ξ)) τs ρs ξs →
  Forall (λ τ, ∀ F κ, has_kind F τ κ → τ = refresh_kinds F τ) τs →
  map (refresh_kinds F) τs = τs ∧
  get_all_lefts (map get_rep_or_size (map (kind_of_node F) τs)) = ρs ∧
  map kind_ref_flag (map (kind_of_node F) τs) = ξs.
Proof.
  induction 1 as [|τ ρ ξ τs ρs ξs Hk _ IHl]; cbn; [done|].
  inversion 1 as [|? ? Hhd Htl]; subst.
  destruct (IHl Htl) as (Hr & Hl & Hf).
  rewrite -(Hhd _ _ Hk) -(kind_of_node_good _ _ _ Hk) Hr.
  cbn; by rewrite Hl Hf.
Qed.

Lemma refresh_kinds_id_mem F τs σs ξs :
  Forall3 (λ τ σ ξ, has_kind F τ (MEMTYPE σ ξ)) τs σs ξs →
  Forall (λ τ, ∀ F κ, has_kind F τ κ → τ = refresh_kinds F τ) τs →
  map (refresh_kinds F) τs = τs ∧
  get_all_rights (map get_rep_or_size (map (kind_of_node F) τs)) = σs ∧
  map kind_ref_flag (map (kind_of_node F) τs) = ξs.
Proof.
  induction 1 as [|τ σ ξ τs σs ξs Hk _ IHl]; cbn; [done|].
  inversion 1 as [|? ? Hhd Htl]; subst.
  destruct (IHl Htl) as (Hr & Hl & Hf).
  rewrite -(Hhd _ _ Hk) -(kind_of_node_good _ _ _ Hk) Hr.
  cbn; by rewrite Hl Hf.
Qed.

Lemma refresh_kinds_id :
  (∀ τ F κ, has_kind F τ κ -> τ = refresh_kinds F τ) /\
    (∀ ϕ F, has_kind_ft F ϕ -> ϕ = refresh_kinds_ft F ϕ) /\
    (∀ iϕ F, has_kind_ift F iϕ -> iϕ = refresh_kinds_ift F iϕ).
Proof.
  apply type_and_function_ind.
  - done.
  - intros κ F κ0 Hk; by inversion Hk.
  - intros κ nt F κ0 Hk; by inversion Hk.
  - intros κ τs IH F κ0 Hk.
    inversion Hk; subst.
    destruct (refresh_kinds_id_val _ _ _ _ H3 IH) as (Hr & Hl & Hf).
    cbn; by rewrite Hr Hl Hf.
  - intros κ τs IH F κ0 Hk.
    inversion Hk; subst.
    destruct (refresh_kinds_id_mem _ _ _ _ H3 IH) as (Hr & Hl & Hf).
    cbn; by rewrite Hr Hl Hf.
  - intros κ τs IH F κ0 Hk.
    inversion Hk; subst.
    destruct (refresh_kinds_id_val _ _ _ _ H3 IH) as (Hr & Hl & Hf).
    cbn; by rewrite Hr Hl Hf.
  - intros κ τs IH F κ0 Hk.
    inversion Hk; subst.
    destruct (refresh_kinds_id_mem _ _ _ _ H3 IH) as (Hr & Hl & Hf).
    cbn; by rewrite Hr Hl Hf.
  - intros κ μ β τ IH F κ0 Hk.
    inversion Hk; subst; cbn; f_equal; by eapply IH.
  - intros κ ϕ IH F κ0 Hk.
    inversion Hk; subst; cbn; f_equal; by eapply IH.
  - intros κ τ IH F κ0 Hk.
    inversion Hk; subst; cbn.
    by rewrite -(IH _ _ H3) -(kind_of_node_good _ _ _ H3).
  - intros κ ρ F κ0 Hk; by inversion Hk.
  - intros κ σ F κ0 Hk; by inversion Hk.
  - intros κ τ IH F κ0 Hk.
    inversion Hk; subst; cbn.
    f_equal; by eapply IH.
  - intros κ τ IH F κ0 Hk.
    inversion Hk; subst; cbn.
    apply IH in H4 as Hnew.
    rewrite <- Hnew.
    by rewrite <- (kind_of_node_good _ _ _ H4).
  - intros κ τ IH F κ0 Hk.
    inversion Hk; subst; cbn.
    rewrite <- (IH _ _ H4), <- (kind_of_node_good _ _ _ H4).
    by rewrite unshift_rep_kind_ren.
  - intros κ τ IH F κ0 Hk.
    inversion Hk; subst; cbn.
    rewrite <- (IH _ _ H4), <- (kind_of_node_good _ _ _ H4).
    by rewrite unshift_size_kind_ren.
  - intros κ κv τ IH F κ0 Hk.
    inversion Hk; subst; cbn.
    apply IH in H6 as Hnew.
    rewrite <- Hnew.
    by rewrite <- (kind_of_node_good _ _ _ H6).
  - intros τs1 τs2 IH1 IH2 F Hk.
    inversion Hk; subst; cbn; f_equal; symmetry; by eapply map_refresh_kinds_id.
  - intros κ ϕ IH F Hk.
    inversion Hk; subst; cbn; f_equal; by eapply IH.
  - intros ϕ IH F Hk.
    inversion Hk; subst; cbn; f_equal; by eapply IH.
  - intros ϕ IH F Hk.
    inversion Hk; subst; cbn; f_equal; by eapply IH.
  - intros ϕ IH F Hk.
    inversion Hk; subst; cbn; f_equal; by eapply IH.
  - intros ϕ IH F Hk.
    inversion Hk; subst; cbn; f_equal; by eapply IH.
Qed.

Lemma kind_of_node_ren ξm ξr ξs ξt F F' τ :
  fc_ren ξr ξs ξt F F' →
  kind_of_node F' (ren_type ξm ξr ξs ξt τ) = ren_kind ξr ξs (kind_of_node F τ).
Proof.
  intros HF; destruct τ; cbn; try done.
  rewrite HF.
  by destruct (fc_type_vars F !! n).
Qed.

Lemma get_all_lefts_ren ξr ξs κs :
  get_all_lefts (map get_rep_or_size (map (ren_kind ξr ξs) κs)) =
  map (ren_representation ξr) (get_all_lefts (map get_rep_or_size κs)).
Proof.
  induction κs as [|[ρ ξ|σ ξ] κs IH]; cbn; [done|by rewrite IH|done].
Qed.

Lemma get_all_rights_ren ξr ξs κs :
  get_all_rights (map get_rep_or_size (map (ren_kind ξr ξs) κs)) =
  map (ren_size ξr ξs) (get_all_rights (map get_rep_or_size κs)).
Proof.
  induction κs as [|[ρ ξ|σ ξ] κs IH]; cbn; [done|done|by rewrite IH].
Qed.

Lemma kind_ref_flag_ren ξr ξs κs :
  map kind_ref_flag (map (ren_kind ξr ξs) κs) = map kind_ref_flag κs.
Proof.
  induction κs as [|[ρ ξ|σ ξ] κs IH]; cbn; [done|by rewrite IH|by rewrite IH].
Qed.

Definition refresh_ren_ok (τ : type) : Prop :=
  ∀ ξm ξr ξs ξt F F', fc_ren ξr ξs ξt F F' →
    refresh_kinds F' (ren_type ξm ξr ξs ξt τ) = ren_type ξm ξr ξs ξt (refresh_kinds F τ).

Lemma map_refresh_ren τs ξm ξr ξs ξt F F' :
  fc_ren ξr ξs ξt F F' →
  Forall refresh_ren_ok τs →
  map (refresh_kinds F') (map (ren_type ξm ξr ξs ξt) τs) =
  map (ren_type ξm ξr ξs ξt) (map (refresh_kinds F) τs).
Proof.
  intros HF IH; induction IH as [|τ τs Hτ _ IHτs]; cbn; [done|].
  by rewrite (Hτ _ _ _ _ _ _ HF) IHτs.
Qed.

Lemma map_kind_of_node_ren ξm ξr ξs ξt F F' τs :
  fc_ren ξr ξs ξt F F' →
  map (kind_of_node F') (map (ren_type ξm ξr ξs ξt) τs) = map (ren_kind ξr ξs) (map (kind_of_node F) τs).
Proof.
  intros HF; rewrite !map_map.
  apply map_ext; intros τ.
  by apply kind_of_node_ren.
Qed.

Lemma refresh_kinds_ren :
  (∀ τ, refresh_ren_ok τ) ∧
  (∀ ϕ ξm ξr ξs ξt F F', fc_ren ξr ξs ξt F F' →
     refresh_kinds_ft F' (ren_function_type ξm ξr ξs ξt ϕ) =
     ren_function_type ξm ξr ξs ξt (refresh_kinds_ft F ϕ)) ∧
  (∀ ϕ ξm ξr ξs ξt F F', fc_ren ξr ξs ξt F F' →
     refresh_kinds_ift F' (ren_inner_function_type ξm ξr ξs ξt ϕ) =
     ren_inner_function_type ξm ξr ξs ξt (refresh_kinds_ift F ϕ)).
Proof.
  apply type_and_function_ind.
  - done.
  - done.
  - intros κ nt; by destruct nt as [[|]|[|]].
  - intros κ τs IH ξm ξr ξs ξt F F' HF; cbn.
    rewrite (map_refresh_ren _ _ _ _ _ _ _ HF IH) (map_kind_of_node_ren _ _ _ _ _ _ _ HF).
    by rewrite get_all_lefts_ren kind_ref_flag_ren.
  - intros κ τs IH ξm ξr ξs ξt F F' HF; cbn.
    rewrite (map_refresh_ren _ _ _ _ _ _ _ HF IH) (map_kind_of_node_ren _ _ _ _ _ _ _ HF).
    by rewrite get_all_rights_ren kind_ref_flag_ren.
  - intros κ τs IH ξm ξr ξs ξt F F' HF; cbn.
    rewrite (map_refresh_ren _ _ _ _ _ _ _ HF IH) (map_kind_of_node_ren _ _ _ _ _ _ _ HF).
    by rewrite get_all_lefts_ren kind_ref_flag_ren.
  - intros κ τs IH ξm ξr ξs ξt F F' HF; cbn.
    rewrite (map_refresh_ren _ _ _ _ _ _ _ HF IH) (map_kind_of_node_ren _ _ _ _ _ _ _ HF).
    by rewrite get_all_rights_ren kind_ref_flag_ren.
  - intros κ μ β τ IH ξm ξr ξs ξt F F' HF; cbn.
    rewrite (IH _ _ _ _ _ _ HF).
    by destruct μ as [m|[|]].
  - intros κ ϕ IH ξm ξr ξs ξt F F' HF; cbn.
    by rewrite (IH _ _ _ _ _ _ HF).
  - intros κ τ IH ξm ξr ξs ξt F F' HF; cbn.
    rewrite (IH _ _ _ _ _ _ HF) (kind_of_node_ren _ _ _ _ _ _ _ HF).
    by destruct (kind_of_node F (refresh_kinds F τ)).
  - done.
  - done.
  - intros κ τ IH ξm ξr ξs ξt F F' HF; cbn.
    f_equal; apply IH, fc_ren_cons, HF.
  - intros κ τ IH ξm ξr ξs ξt F F' HF; cbn.
    rewrite (IH _ _ _ _ _ _ (fc_ren_mem _ _ _ _ _ HF)).
    by rewrite (kind_of_node_ren _ _ _ _ _ _ _ (fc_ren_mem _ _ _ _ _ HF)).
  - intros κ τ IH ξm ξr ξs ξt F F' HF; cbn.
    rewrite (IH _ _ _ _ _ _ (fc_ren_rep _ _ _ _ _ HF)).
    rewrite (kind_of_node_ren _ _ _ _ _ _ _ (fc_ren_rep _ _ _ _ _ HF)).
    by rewrite unshift_rep_kind_up_ren.
  - intros κ τ IH ξm ξr ξs ξt F F' HF; cbn.
    rewrite (IH _ _ _ _ _ _ (fc_ren_size _ _ _ _ _ HF)).
    rewrite (kind_of_node_ren _ _ _ _ _ _ _ (fc_ren_size _ _ _ _ _ HF)).
    by rewrite unshift_size_kind_up_ren.
  - intros κ κ0 τ IH ξm ξr ξs ξt F F' HF; cbn.
    rewrite (IH _ _ _ _ _ _ (fc_ren_cons _ _ _ _ _ _ HF)).
    by rewrite (kind_of_node_ren _ _ _ _ _ _ _ (fc_ren_cons _ _ _ _ _ _ HF)).
  - intros τs1 τs2 IH1 IH2 ξm ξr ξs ξt F F' HF; cbn.
    by rewrite (map_refresh_ren _ _ _ _ _ _ _ HF IH1) (map_refresh_ren _ _ _ _ _ _ _ HF IH2).
  - intros κ ϕ IH ξm ξr ξs ξt F F' HF; cbn.
    f_equal; apply IH, fc_ren_cons, HF.
  - intros ϕ IH ξm ξr ξs ξt F F' HF; cbn.
    f_equal; apply IH, HF.
  - intros ϕ IH ξm ξr ξs ξt F F' HF; cbn.
    f_equal; apply IH, fc_ren_mem, HF.
  - intros ϕ IH ξm ξr ξs ξt F F' HF; cbn.
    f_equal; apply IH, fc_ren_rep, HF.
  - intros ϕ IH ξm ξr ξs ξt F F' HF; cbn.
    f_equal; apply IH, fc_ren_size, HF.
Qed.

Lemma refresh_kinds_up_shift_type F κ τ :
  refresh_kinds (F <| fc_type_vars ::= cons κ |>)
    (ren_type unscoped.id unscoped.id unscoped.id unscoped.shift τ) =
  ren_type unscoped.id unscoped.id unscoped.id unscoped.shift (refresh_kinds F τ).
Proof.
  apply (proj1 refresh_kinds_ren); intros t.
  rewrite fc_type_vars_get_upd; cbn.
  destruct (fc_type_vars F !! t); cbn; [by rewrite rinstId'_kind|done].
Qed.

Lemma refresh_kinds_up_shift_mem F τ :
  refresh_kinds (F <| fc_kind_ctx ::= set kc_mem_vars S |>)
    (ren_type unscoped.shift unscoped.id unscoped.id unscoped.id τ) =
  ren_type unscoped.shift unscoped.id unscoped.id unscoped.id (refresh_kinds F τ).
Proof.
  apply (proj1 refresh_kinds_ren); intros t.
  destruct F as [? ? ? ? tvs]; cbn; unfold unscoped.id, Datatypes.id.
  destruct (tvs !! t); cbn; [by rewrite rinstId'_kind|done].
Qed.

Lemma refresh_kinds_up_shift_rep F τ :
  refresh_kinds (add_rep_var F) (ren_type unscoped.id unscoped.shift unscoped.id unscoped.id τ) =
  ren_type unscoped.id unscoped.shift unscoped.id unscoped.id (refresh_kinds F τ).
Proof.
  apply (proj1 refresh_kinds_ren); intros t.
  destruct F as [? ? ? ? tvs]; unfold add_rep_var; cbn.
  by rewrite list_lookup_fmap.
Qed.

Lemma refresh_kinds_up_shift_size F τ :
  refresh_kinds (add_size_var F) (ren_type unscoped.id unscoped.id unscoped.shift unscoped.id τ) =
  ren_type unscoped.id unscoped.id unscoped.shift unscoped.id (refresh_kinds F τ).
Proof.
  apply (proj1 refresh_kinds_ren); intros t.
  destruct F as [? ? ? ? tvs]; unfold add_size_var; cbn.
  by rewrite list_lookup_fmap.
Qed.

Lemma has_kind_rec_subst :
  (∀ τ F κ, let τrec := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
            has_kind F (RecT κ τ) κ -> ∃ κrec, subkind_of κrec κ ∧ has_kind F τrec κrec).
Proof.
  intros τ F κ; cbv zeta; intros Hrec.
  inversion Hrec; subst.
  exists κbody.
  split; first done.
  eapply (proj1 has_kind_subst); last eauto.
  - done.
  - done.
  - done.
  - by apply (ctx_subst_scons F (RecT κ τ) κ).
Qed.

Lemma type_kind_kind_of_node F τ κ :
  layout.type_kind (fc_type_vars F) τ = Some κ →
  kind_of_node F τ = κ.
Proof.
  destruct τ; cbn; try (intros H; congruence).
  destruct (fc_type_vars F !! n); intros H; congruence.
Qed.

Lemma mapM_type_kind_kind_of_node F τs κs :
  mapM (layout.type_kind (fc_type_vars F)) τs = Some κs →
  map (kind_of_node F) τs = κs.
Proof.
  intros Hm%mapM_Some_1.
  induction Hm as [|τ κ τs κs Hκ _ IH]; cbn; [done|].
  by rewrite (type_kind_kind_of_node _ _ _ Hκ) IH.
Qed.

Lemma val_kinds_annot κs ρs ξs :
  Forall3 (λ κ ρ ξ, κ = VALTYPE ρ ξ) κs ρs ξs →
  get_all_lefts (map get_rep_or_size κs) = ρs ∧ map kind_ref_flag κs = ξs.
Proof.
  induction 1 as [|κ ρ ξ κs ρs ξs -> _ [IH1 IH2]]; cbn; [done|].
  by rewrite IH1 IH2.
Qed.

Lemma mem_kinds_annot κs σs ξs :
  Forall3 (λ κ σ ξ, κ = MEMTYPE σ ξ) κs σs ξs →
  get_all_rights (map get_rep_or_size κs) = σs ∧ map kind_ref_flag κs = ξs.
Proof.
  induction 1 as [|κ σ ξ κs σs ξs -> _ [IH1 IH2]]; cbn; [done|].
  by rewrite IH1 IH2.
Qed.

Lemma map_refresh_kinds_refreshed F τs τs' :
  Forall (λ τ', ∀ F τ, refreshed_kinds F τ τ' → τ' = refresh_kinds F τ) τs' →
  Forall2 (refreshed_kinds F) τs τs' →
  map (refresh_kinds F) τs = τs'.
Proof.
  intros IH Hall.
  induction Hall as [|τ τ' τs τs' Hr _ IHl]; cbn; [done|].
  inversion IH as [|? ? Hhd Htl]; subst.
  by rewrite -(Hhd _ _ Hr) (IHl Htl).
Qed.

Lemma refreshed_kinds_refresh :
  (∀ τ' F τ, refreshed_kinds F τ τ' → τ' = refresh_kinds F τ) ∧
  (∀ ϕ' F ϕ, refreshed_kinds_ft F ϕ ϕ' → ϕ' = refresh_kinds_ft F ϕ) ∧
  (∀ ϕ' F ϕ, refreshed_kinds_ift F ϕ ϕ' → ϕ' = refresh_kinds_ift F ϕ).
Proof.
  apply type_and_function_ind.
  - intros t F τ Hr; by inversion Hr.
  - intros κ F τ Hr; by inversion Hr.
  - intros κ nt F τ Hr; by inversion Hr.
  - intros κ τs' IH F τ Hr.
    inversion Hr; subst.
    destruct (val_kinds_annot _ _ _ H5) as [Hl Hf].
    cbn; rewrite (map_refresh_kinds_refreshed _ _ _ IH H1).
    by rewrite (mapM_type_kind_kind_of_node _ _ _ H4) Hl Hf.
  - intros κ τs' IH F τ Hr.
    inversion Hr; subst.
    destruct (mem_kinds_annot _ _ _ H5) as [Hl Hf].
    cbn; rewrite (map_refresh_kinds_refreshed _ _ _ IH H1).
    by rewrite (mapM_type_kind_kind_of_node _ _ _ H4) Hl Hf.
  - intros κ τs' IH F τ Hr.
    inversion Hr; subst.
    destruct (val_kinds_annot _ _ _ H5) as [Hl Hf].
    cbn; rewrite (map_refresh_kinds_refreshed _ _ _ IH H1).
    by rewrite (mapM_type_kind_kind_of_node _ _ _ H4) Hl Hf.
  - intros κ τs' IH F τ Hr.
    inversion Hr; subst.
    destruct (mem_kinds_annot _ _ _ H5) as [Hl Hf].
    cbn; rewrite (map_refresh_kinds_refreshed _ _ _ IH H1).
    by rewrite (mapM_type_kind_kind_of_node _ _ _ H4) Hl Hf.
  - intros κ μ β τ' IH F τ Hr.
    inversion Hr; subst.
    cbn; rewrite -(IH _ _ H2).
    by destruct μ as [|[|]].
  - intros κ ϕ' IH F τ Hr.
    inversion Hr; subst.
    cbn; f_equal; by apply IH.
  - intros κ τ' IH F τ Hr.
    inversion Hr; subst.
    cbn; rewrite -(IH _ _ H3).
    by rewrite (type_kind_kind_of_node _ _ _ H4).
  - intros κ ρ F τ Hr; by inversion Hr.
  - intros κ σ F τ Hr; by inversion Hr.
  - intros κ τ' IH F τ Hr.
    inversion Hr; subst.
    cbn; f_equal; by apply IH.
  - intros κ τ' IH F τ Hr.
    inversion Hr; subst; cbn.
    apply IH in H3 as Hnew. rewrite <- Hnew.
    by rewrite (type_kind_kind_of_node _ _ _ H4).
  - intros κ τ' IH F τ Hr.
    inversion Hr; subst; cbn.
    match goal with H : refreshed_kinds _ _ _ |- _ => apply IH in H as Hnew end.
    rewrite <- Hnew.
    match goal with H : layout.type_kind _ _ = Some _ |- _ =>
      rewrite (type_kind_kind_of_node _ _ _ H) end.
    by rewrite unshift_rep_kind_ren.
  - intros κ τ' IH F τ Hr.
    inversion Hr; subst; cbn.
    match goal with H : refreshed_kinds _ _ _ |- _ => apply IH in H as Hnew end.
    rewrite <- Hnew.
    match goal with H : layout.type_kind _ _ = Some _ |- _ =>
      rewrite (type_kind_kind_of_node _ _ _ H) end.
    by rewrite unshift_size_kind_ren.
  - intros κ κv τ' IH F τ Hr.
    inversion Hr; subst; cbn.
    apply IH in H3 as Hnew. rewrite <- Hnew.
    by rewrite (type_kind_kind_of_node _ _ _ H5).
  - intros τs1' τs2' IH1 IH2 F ϕ Hr.
    inversion Hr; subst.
    cbn; f_equal; symmetry; by eapply map_refresh_kinds_refreshed.
  - intros κ ϕ' IH F ϕ Hr.
    inversion Hr; subst.
    cbn; f_equal; by apply IH.
  - intros ϕ' IH F ϕ Hr.
    inversion Hr; subst.
    cbn; f_equal; by apply IH.
  - intros ϕ' IH F ϕ Hr.
    inversion Hr; subst.
    cbn; f_equal; by apply IH.
  - intros ϕ' IH F ϕ Hr.
    inversion Hr; subst.
    cbn; f_equal; by apply IH.
  - intros ϕ' IH F ϕ Hr.
    inversion Hr; subst.
    cbn; f_equal; by apply IH.
Qed.

Lemma refreshed_kinds_refresh_kinds:
  (∀ τ F subm subr subs subt,
      let substed := subst_type subm subr subs subt τ in
      refreshed_kinds F substed τ ->
      τ = refresh_kinds F substed
  ) /\
  (∀ ϕ' F ϕ subm subr subs subt, let substed :=
    (subst_function_type subm subr subs subt ϕ) in
  refreshed_kinds_ft F substed ϕ' ->
  ϕ' = refresh_kinds_ft F substed) /\
  (∀ ϕ' F ϕ subm subr subs subt, let substed :=
    (subst_inner_function_type subm subr subs subt ϕ) in
  refreshed_kinds_ift F substed ϕ' ->
  ϕ' = refresh_kinds_ift F substed).
Proof.
  destruct refreshed_kinds_refresh as (Hτ & Hft & Hift).
  split; [|split]; intros; eauto.
Qed.

(* Instantiation preserves kinding.  Type and memory instantiation refresh their result
   and may lower ref flags (the witness only has a subkind of the bound; a memory variable
   becomes GC), so those two go through has_kind_subst_refresh: every node of the refreshed
   substitution instance has a subkind of the substituted original.  Representation and
   size instantiation do not refresh; they are exact and go through has_kind_subst_gen. *)

Definition subst_refresh_ok (τ : type) : Prop :=
  forall σm σr σs σt F F' κ,
    ctx_rel subkind_of σm σr σs σt F F' ->
    has_kind F τ κ ->
    exists κ', subkind_of κ' (subst_kind σr σs κ) /\
               has_kind F' (refresh_kinds F' (subst_type σm σr σs σt τ)) κ'.

Lemma subst_refresh_list_val σm σr σs σt F F' τs ρs ξs :
  ctx_rel subkind_of σm σr σs σt F F' ->
  Forall subst_refresh_ok τs ->
  Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs ρs ξs ->
  let τs' := map (refresh_kinds F') (map (subst_type σm σr σs σt) τs) in
  exists ξs',
    Forall2 ref_flag_le ξs' ξs /\
    Forall3 (fun τ ρ ξ => has_kind F' τ (VALTYPE ρ ξ)) τs' (map (subst_representation σr) ρs) ξs' /\
    get_all_lefts (map get_rep_or_size (map (kind_of_node F') τs'))
    = map (subst_representation σr) ρs /\
    map kind_ref_flag (map (kind_of_node F') τs') = ξs'.
Proof.
  intros Hctx HIH H3; cbv zeta.
  induction H3 as [|τ ρ ξ τs ρs ξs Hk _ IHl]; cbn; [exists []; repeat split; constructor|].
  inversion HIH as [|? ? Hhd Htl]; subst.
  destruct (Hhd _ _ _ _ _ _ _ Hctx Hk) as (κ' & Hsub & Hk').
  cbn in Hsub; inversion Hsub as [ρ0 ξ0 ξ1 Hle0|]; subst.
  destruct (IHl Htl) as (ξs' & Hle & H3' & Hl & Hf).
  exists (ξ0 :: ξs'); split; [by constructor|]; split; [by constructor|].
  rewrite -(kind_of_node_good _ _ _ Hk'); cbn.
  by rewrite Hl Hf.
Qed.

Lemma subst_refresh_list_mem σm σr σs σt F F' τs σs' ξs :
  ctx_rel subkind_of σm σr σs σt F F' ->
  Forall subst_refresh_ok τs ->
  Forall3 (fun τ σ ξ => has_kind F τ (MEMTYPE σ ξ)) τs σs' ξs ->
  let τs' := map (refresh_kinds F') (map (subst_type σm σr σs σt) τs) in
  exists ξs',
    Forall2 ref_flag_le ξs' ξs /\
    Forall3 (fun τ σ ξ => has_kind F' τ (MEMTYPE σ ξ)) τs' (map (subst_size σr σs) σs') ξs' /\
    get_all_rights (map get_rep_or_size (map (kind_of_node F') τs'))
    = map (subst_size σr σs) σs' /\
    map kind_ref_flag (map (kind_of_node F') τs') = ξs'.
Proof.
  intros Hctx HIH H3; cbv zeta.
  induction H3 as [|τ σ ξ τs σs0 ξs Hk _ IHl]; cbn; [exists []; repeat split; constructor|].
  inversion HIH as [|? ? Hhd Htl]; subst.
  destruct (Hhd _ _ _ _ _ _ _ Hctx Hk) as (κ' & Hsub & Hk').
  cbn in Hsub; inversion Hsub as [|σ0 ξ0 ξ1 Hle0]; subst.
  destruct (IHl Htl) as (ξs' & Hle & H3' & Hl & Hf).
  exists (ξ0 :: ξs'); split; [by constructor|]; split; [by constructor|].
  rewrite -(kind_of_node_good _ _ _ Hk'); cbn.
  by rewrite Hl Hf.
Qed.

Lemma subst_refresh_list2 σm σr σs σt F F' τs κs :
  ctx_rel subkind_of σm σr σs σt F F' ->
  Forall subst_refresh_ok τs ->
  Forall2 (has_kind F) τs κs ->
  exists κs',
    Forall2 (has_kind F') (map (refresh_kinds F') (map (subst_type σm σr σs σt) τs)) κs'.
Proof.
  intros Hctx HIH H2.
  induction H2 as [|τ κ τs κs Hk _ IHl]; cbn; [by exists []|].
  inversion HIH as [|? ? Hhd Htl]; subst.
  destruct (IHl Htl) as (κs' & H2').
  destruct (Hhd _ _ _ _ _ _ _ Hctx Hk) as (κ' & _ & Hk').
  exists (κ' :: κs'); by constructor.
Qed.

Lemma has_kind_subst_refresh :
  (forall τ, subst_refresh_ok τ) /\
  (forall ϕ σm σr σs σt F F',
      ctx_rel subkind_of σm σr σs σt F F' ->
      has_kind_ft F ϕ ->
      has_kind_ft F' (refresh_kinds_ft F' (subst_function_type σm σr σs σt ϕ))) /\
  (forall ϕ σm σr σs σt F F',
      ctx_rel subkind_of σm σr σs σt F F' ->
      has_kind_ift F ϕ ->
      has_kind_ift F' (refresh_kinds_ift F' (subst_inner_function_type σm σr σs σt ϕ))).
Proof.
  apply type_and_function_ind.
  - intros t σm σr σs σt F F' κ Hctx Hk.
    destruct (proj2 Hctx _ _ Hk) as (κ' & Hsub & Hk').
    exists κ'; split; [done|].
    cbn; by rewrite -(proj1 refresh_kinds_id _ _ _ Hk').
  - intros κ0 σm σr σs σt F F' κ Hctx Hk.
    inversion Hk; subst; cbn; eexists; split; [apply subkind_of_refl|constructor].
  - intros κ0 nt σm σr σs σt F F' κ Hctx Hk.
    inversion Hk; subst; cbn; eexists; (split; [apply subkind_of_refl|constructor]).
  - intros κ0 τs IH σm σr σs σt F F' κ Hctx Hk.
    inversion Hk; subst.
    match goal with H : Forall3 _ τs _ _ |- _ =>
      destruct (subst_refresh_list_val _ _ _ _ _ _ _ _ _ Hctx IH H) as (ξs' & Hle & H3' & Hl & Hf)
    end.
    cbn; rewrite Hl Hf.
    eexists; split; last by apply KSum.
    constructor; by apply ref_flag_lub_mono.
  - intros κ0 τs IH σm σr σs σt F F' κ Hctx Hk.
    inversion Hk; subst.
    match goal with H : Forall3 _ τs _ _ |- _ =>
      destruct (subst_refresh_list_mem _ _ _ _ _ _ _ _ _ Hctx IH H) as (ξs' & Hle & H3' & Hl & Hf)
    end.
    cbn; rewrite Hl Hf.
    eexists; split; last by apply KVariant.
    constructor; by apply ref_flag_lub_mono.
  - intros κ0 τs IH σm σr σs σt F F' κ Hctx Hk.
    inversion Hk; subst.
    match goal with H : Forall3 _ τs _ _ |- _ =>
      destruct (subst_refresh_list_val _ _ _ _ _ _ _ _ _ Hctx IH H) as (ξs' & Hle & H3' & Hl & Hf)
    end.
    cbn; rewrite Hl Hf.
    eexists; split; last by apply KProd.
    constructor; by apply ref_flag_lub_mono.
  - intros κ0 τs IH σm σr σs σt F F' κ Hctx Hk.
    inversion Hk; subst.
    match goal with H : Forall3 _ τs _ _ |- _ =>
      destruct (subst_refresh_list_mem _ _ _ _ _ _ _ _ _ Hctx IH H) as (ξs' & Hle & H3' & Hl & Hf)
    end.
    cbn; rewrite Hl Hf.
    eexists; split; last by apply KStruct.
    constructor; by apply ref_flag_lub_mono.
  - intros κ0 μ β t IH σm σr σs σt F F' κ Hctx Hk.
    inversion Hk; subst; cbn;
      match goal with H : has_kind F t (MEMTYPE _ _) |- _ =>
        destruct (IH _ _ _ _ _ _ _ Hctx H) as (κ' & Hsub & Hk')
      end;
      cbn in Hsub; inversion Hsub as [|σ0 ξ0 ξ1 Hle0]; subst.
    + match goal with H : mem_ok _ (VarM _) |- _ =>
        pose proof (mem_ok_subst _ _ _ _ _ _ (proj1 Hctx) H) as Hmo; cbn in Hmo
      end.
      revert Hmo; destruct (σm m) as [m'|[|]]; intros Hmo.
      * eexists; split; [apply subkind_of_refl|]; by eapply KRefVar.
      * eexists; split; [apply subkind_of_refl|]; by eapply KRefMM.
      * exists (VALTYPE (AtomR PtrR) GCRefs); split; [by constructor|]; by eapply KRefGC.
    + eexists; split; [apply subkind_of_refl|]; by eapply KRefMM.
    + eexists; split; [apply subkind_of_refl|]; by eapply KRefGC.
  - intros κ0 ft IH σm σr σs σt F F' κ Hctx Hk.
    inversion Hk; subst; cbn.
    eexists; split; [apply subkind_of_refl|].
    apply KCodeRef; by eapply IH; eauto.
  - intros κ0 t IH σm σr σs σt F F' κ Hctx Hk.
    inversion Hk; subst; cbn.
    match goal with H : has_kind F t (VALTYPE _ _) |- _ =>
      destruct (IH _ _ _ _ _ _ _ Hctx H) as (κ' & Hsub & Hk')
    end.
    cbn in Hsub; inversion Hsub as [ρ0 ξ0 ξ1 Hle0|]; subst.
    rewrite -(kind_of_node_good _ _ _ Hk').
    exists (MEMTYPE (RepS (subst_representation σr ρ)) ξ0); split; [by constructor|by apply KSer].
  - intros κ0 ρ σm σr σs σt F F' κ Hctx Hk.
    inversion Hk; subst; cbn.
    eexists; split; [apply subkind_of_refl|].
    apply KPlug; by eapply rep_ok_subst; [apply Hctx|].
  - intros κ0 σ σm σr σs σt F F' κ Hctx Hk.
    inversion Hk; subst; cbn.
    eexists; split; [apply subkind_of_refl|].
    apply KSpan; by eapply size_ok_subst; [apply Hctx|].
  - intros κ0 t IH σm σr σs σt F F' κ Hctx Hk.
    inversion Hk; subst; cbn.
    match goal with H : has_kind (F <| fc_type_vars ::= cons κ |>) t _ |- _ =>
      destruct (IH _ _ _ _ _ _ _ (ctx_rel_cons _ _ _ _ _ _ _ κ kind_rel_ok_subkind Hctx) H)
        as (κ' & Hsub & Hk')
    end.
    rewrite subst_kind_up_type in Hsub.
    exists (subst_kind σr σs κ); split; [apply subkind_of_refl|].
    eapply KRec; [by eapply kind_ok_subst; [apply Hctx|]|exact Hk'|].
    eapply subkind_of_trans; [exact Hsub|by apply subkind_of_subst].
  - intros κ0 t IH σm σr σs σt F F' κ Hctx Hk.
    inversion Hk; subst; cbn.
    match goal with H : has_kind _ t _ |- _ =>
      destruct (IH _ _ _ _ _ _ _ (ctx_rel_mem _ _ _ _ _ _ _ Hctx) H) as (κ' & Hsub & Hk')
    end.
    rewrite subst_kind_up_mem in Hsub.
    rewrite -(kind_of_node_good _ _ _ Hk').
    exists κ'; split; [done|].
    apply KExistsMem; [|done].
    apply (kind_ok_supkind_of _ _ (subst_kind σr σs κ)); [by eapply kind_ok_subst; [apply Hctx|]|done].
  - intros κ0 t IH σm σr σs σt F F' κ Hctx Hk.
    inversion Hk; subst; cbn -[add_rep_var].
    match goal with H : has_kind _ t _ |- _ =>
      destruct (IH _ _ _ _ _ _ _ (ctx_rel_rep _ _ _ _ _ _ _ kind_rel_ok_subkind Hctx) H)
        as (κ' & Hsub & Hk')
    end.
    rewrite subst_kind_up_rep in Hsub.
    destruct (subkind_of_ren_inv _ _ _ _ Hsub) as (κ1 & -> & Hsub1).
    rewrite -(kind_of_node_good _ _ _ Hk') unshift_rep_kind_ren.
    exists κ1; split; [done|].
    apply KExistsRep; [|done].
    apply (kind_ok_supkind_of _ _ (subst_kind σr σs κ)); [by eapply kind_ok_subst; [apply Hctx|]|done].
  - intros κ0 t IH σm σr σs σt F F' κ Hctx Hk.
    inversion Hk; subst; cbn -[add_size_var].
    match goal with H : has_kind _ t _ |- _ =>
      destruct (IH _ _ _ _ _ _ _ (ctx_rel_size _ _ _ _ _ _ _ kind_rel_ok_subkind Hctx) H)
        as (κ' & Hsub & Hk')
    end.
    rewrite subst_kind_up_size in Hsub.
    destruct (subkind_of_ren_inv _ _ _ _ Hsub) as (κ1 & -> & Hsub1).
    rewrite -(kind_of_node_good _ _ _ Hk') unshift_size_kind_ren.
    exists κ1; split; [done|].
    apply KExistsSize; [|done].
    apply (kind_ok_supkind_of _ _ (subst_kind σr σs κ)); [by eapply kind_ok_subst; [apply Hctx|]|done].
  - intros κ1 κ2 t IH σm σr σs σt F F' κ Hctx Hk.
    inversion Hk; subst; cbn.
    match goal with H : has_kind _ t _ |- _ =>
      destruct (IH _ _ _ _ _ _ _ (ctx_rel_cons _ _ _ _ _ _ _ κ2 kind_rel_ok_subkind Hctx) H)
        as (κ' & Hsub & Hk')
    end.
    rewrite subst_kind_up_type in Hsub.
    rewrite -(kind_of_node_good _ _ _ Hk').
    exists κ'; split; [done|].
    apply KExistsType; [by eapply kind_ok_subst; [apply Hctx|]| |done].
    apply (kind_ok_supkind_of _ _ (subst_kind σr σs κ)); [by eapply kind_ok_subst; [apply Hctx|]|done].
  - intros τs1 τs2 IH1 IH2 σm σr σs σt F F' Hctx Hk.
    inversion Hk; subst; cbn.
    match goal with H : Forall2 (has_kind F) τs1 _ |- _ =>
      destruct (subst_refresh_list2 _ _ _ _ _ _ _ _ Hctx IH1 H) as (κs1' & H1')
    end.
    match goal with H : Forall2 (has_kind F) τs2 _ |- _ =>
      destruct (subst_refresh_list2 _ _ _ _ _ _ _ _ Hctx IH2 H) as (κs2' & H2')
    end.
    by eapply KMonoFun.
  - intros κ0 ft IH σm σr σs σt F F' Hctx Hk.
    inversion Hk; subst; cbn.
    apply KForallType; [by eapply kind_ok_subst; [apply Hctx|]|].
    eapply (IH _ _ _ _ (F <| fc_type_vars ::= cons κ0 |>) _);
      [by apply ctx_rel_cons; [exact kind_rel_ok_subkind|exact Hctx]|done].
  - intros ft IH σm σr σs σt F F' Hctx Hk.
    inversion Hk; subst; cbn.
    apply KInnerFun; by eapply IH; eauto.
  - intros ft IH σm σr σs σt F F' Hctx Hk.
    inversion Hk; subst; cbn.
    apply KForallMem.
    eapply (IH _ _ _ _ (F <| fc_kind_ctx ::= set kc_mem_vars S |>) _);
      [by apply ctx_rel_mem|done].
  - intros ft IH σm σr σs σt F F' Hctx Hk.
    inversion Hk; subst; cbn.
    apply KForallRep.
    eapply (IH _ _ _ _ (add_rep_var F) _);
      [by apply ctx_rel_rep; [exact kind_rel_ok_subkind|exact Hctx]|done].
  - intros ft IH σm σr σs σt F F' Hctx Hk.
    inversion Hk; subst; cbn.
    apply KForallSize.
    eapply (IH _ _ _ _ (add_size_var F) _);
      [by apply ctx_rel_size; [exact kind_rel_ok_subkind|exact Hctx]|done].
Qed.

Lemma ctx_rel_inst_type F τ κ κ' :
  has_kind F τ κ' -> subkind_of κ' κ ->
  ctx_rel subkind_of VarM VarR VarS (unscoped.scons τ VarT)
    (F <| fc_type_vars ::= cons κ |>) F.
Proof.
  intros Ht Hsub; split.
  - rewrite fc_kind_ctx_ty_update; split; [|split]; intros n Hn; by constructor.
  - intros [|t] κ0 Hk.
    + pose proof (has_kind_type_kind _ _ _ Hk) as Hlk.
      cbn [layout.type_kind] in Hlk; rewrite fc_type_vars_get_upd in Hlk; cbn in Hlk.
      injection Hlk as ->.
      exists κ'; split; [by rewrite instId'_kind|done].
    + apply (proj1 (has_kind_var_wk_ty F t κ0 κ)) in Hk.
      exists κ0; split; [rewrite instId'_kind; apply subkind_of_refl|done].
Qed.

Lemma ctx_rel_inst_mem F μ :
  mem_ok (fc_kind_ctx F) μ ->
  ctx_rel subkind_of (unscoped.scons μ VarM) VarR VarS VarT
    (F <| fc_kind_ctx ::= set kc_mem_vars S |>) F.
Proof.
  intros Hμ; split.
  - split; [|split].
    + intros [|n] Hn; [done|].
      apply OKVarM; destruct F as [? ? ? [km kr ks] ?]; cbn in *; lia.
    + intros n Hn; apply OKVarR; by destruct F as [? ? ? [km kr ks] ?].
    + intros n Hn; apply OKVarS; by destruct F as [? ? ? [km kr ks] ?].
  - intros t κ Hk.
    exists κ; split; [rewrite instId'_kind; apply subkind_of_refl|].
    inversion Hk; subst.
    apply KVar; [done|].
    match goal with H : kind_ok _ κ |- _ =>
      apply (kind_ok_kc _ _ _ H); by destruct F as [? ? ? [km kr ks] ?]
    end.
Qed.

Lemma ctx_rel_inst_rep F ρ :
  rep_ok (fc_kind_ctx F) ρ ->
  ctx_rel eq VarM (unscoped.scons ρ VarR) VarS VarT (add_rep_var F) F.
Proof.
  intros Hρ; split.
  - split; [|split].
    + intros n Hn; apply OKVarM; by destruct F as [? ? ? [km kr ks] ?].
    + intros [|n] Hn; [done|].
      apply OKVarR; destruct F as [? ? ? [km kr ks] ?]; cbn in *; lia.
    + intros n Hn; apply OKVarS; by destruct F as [? ? ? [km kr ks] ?].
  - intros t κ Hk.
    inversion Hk; subst.
    match goal with H : fc_type_vars (add_rep_var F) !! t = Some κ |- _ =>
      rewrite fc_type_vars_add_rep list_lookup_fmap in H;
      destruct (fc_type_vars F !! t) as [κ0|] eqn:Ht; [|done];
      cbn [fmap option_fmap option_map] in H; injection H as <-
    end.
    exists κ0; split; [by rewrite subst_kind_scons_rep|].
    apply KVar; [done|].
    destruct (proj2 (ctx_ren_wk_rep F)) as (_ & Hrr & Hss).
    match goal with H : kind_ok _ (ren_kind _ _ κ0) |- _ =>
      by apply (proj2 (kind_ok_ren' _ _ _ _ κ0 Hrr Hss)) in H
    end.
Qed.

Lemma ctx_rel_inst_size F σ :
  size_ok (fc_kind_ctx F) σ ->
  ctx_rel eq VarM VarR (unscoped.scons σ VarS) VarT (add_size_var F) F.
Proof.
  intros Hσ; split.
  - split; [|split].
    + intros n Hn; apply OKVarM; by destruct F as [? ? ? [km kr ks] ?].
    + intros n Hn; apply OKVarR; by destruct F as [? ? ? [km kr ks] ?].
    + intros [|n] Hn; [done|].
      apply OKVarS; destruct F as [? ? ? [km kr ks] ?]; cbn in *; lia.
  - intros t κ Hk.
    inversion Hk; subst.
    match goal with H : fc_type_vars (add_size_var F) !! t = Some κ |- _ =>
      rewrite fc_type_vars_add_size list_lookup_fmap in H;
      destruct (fc_type_vars F !! t) as [κ0|] eqn:Ht; [|done];
      cbn [fmap option_fmap option_map] in H; injection H as <-
    end.
    exists κ0; split; [by rewrite subst_kind_scons_size|].
    apply KVar; [done|].
    destruct (proj2 (ctx_ren_wk_size F)) as (_ & Hrr & Hss).
    match goal with H : kind_ok _ (ren_kind _ _ κ0) |- _ =>
      by apply (proj2 (kind_ok_ren' _ _ _ _ κ0 Hrr Hss)) in H
    end.
Qed.

Lemma has_kind_ift_through_inst_forwards F ϕ ϕ' ix :
  inner_function_type_inst F ix ϕ ϕ' ->
  has_kind_ift F ϕ ->
  has_kind_ift F ϕ'.
Proof.
  intros Hinst Hk.
  inversion Hinst as [F1 ϕ1 τ κ κ' ϕ1' Ht Hsub Hrf]; subst.
  inversion Hk as [|F2 κ2 ϕ2 Hok Hk']; subst.
  rewrite (proj2 (proj2 refreshed_kinds_refresh) _ _ _ Hrf).
  eapply (proj2 (proj2 has_kind_subst_refresh)); [|exact Hk'].
  by eapply ctx_rel_inst_type.
Qed.

Lemma has_kind_ft_through_inst F ϕ ϕ' ix :
  function_type_inst F ix ϕ ϕ' ->
  has_kind_ft F ϕ ->
  has_kind_ft F ϕ'.
Proof.
  intros Hinst Hk; inversion Hinst; subst; inversion Hk; subst.
  - constructor; by eapply has_kind_ift_through_inst_forwards.
  - match goal with H : refreshed_kinds_ft _ _ _ |- _ =>
      rewrite (proj1 (proj2 refreshed_kinds_refresh) _ _ _ H)
    end.
    eapply (proj1 (proj2 has_kind_subst_refresh)); [by apply ctx_rel_inst_mem|done].
  - eapply (proj1 (proj2 has_kind_subst_gen)); [done|by apply ctx_rel_inst_rep|done].
  - eapply (proj1 (proj2 has_kind_subst_gen)); [done|by apply ctx_rel_inst_size|done].
Qed.

(* Context weakening: more variables in scope, the same bindings for the existing ones.
   has_kind_empty is what the module kinding invariant (module_ctx_ok) hands the compat
   lemmas. *)

Definition kc_le (K K' : kind_ctx) : Prop :=
  kc_mem_vars K <= kc_mem_vars K' /\
  kc_rep_vars K <= kc_rep_vars K' /\
  kc_size_vars K <= kc_size_vars K'.

Definition ctx_le (F F' : function_ctx) : Prop :=
  kc_le (fc_kind_ctx F) (fc_kind_ctx F') /\
  forall t κ, fc_type_vars F !! t = Some κ -> fc_type_vars F' !! t = Some κ.

Lemma ctx_le_cons F F' κ :
  ctx_le F F' -> ctx_le (F <| fc_type_vars ::= cons κ |>) (F' <| fc_type_vars ::= cons κ |>).
Proof.
  intros [Hkc Hv]; split; [by rewrite !fc_kind_ctx_ty_update|].
  intros [|t] κ0; rewrite !fc_type_vars_get_upd; [done|by apply Hv].
Qed.

Lemma ctx_le_mem F F' :
  ctx_le F F' ->
  ctx_le (F <| fc_kind_ctx ::= set kc_mem_vars S |>) (F' <| fc_kind_ctx ::= set kc_mem_vars S |>).
Proof.
  intros [(Hm & Hr & Hs) Hv]; split; [|by rewrite !fc_type_vars_kc_update].
  destruct F as [? ? ? [] ?], F' as [? ? ? [] ?]; unfold kc_le in *; cbn in *; split; [|split]; lia.
Qed.

Lemma ctx_le_rep F F' : ctx_le F F' -> ctx_le (add_rep_var F) (add_rep_var F').
Proof.
  intros [(Hm & Hr & Hs) Hv]; split.
  - destruct F as [? ? ? [] ?], F' as [? ? ? [] ?]; unfold add_rep_var, add_size_var, kc_le in *; cbn in *; split; [|split]; lia.
  - intros t κ; rewrite !fc_type_vars_add_rep !list_lookup_fmap.
    destruct (fc_type_vars F !! t) as [κ0|] eqn:Ht; [|done].
    by rewrite (Hv _ _ Ht).
Qed.

Lemma ctx_le_size F F' : ctx_le F F' -> ctx_le (add_size_var F) (add_size_var F').
Proof.
  intros [(Hm & Hr & Hs) Hv]; split.
  - destruct F as [? ? ? [] ?], F' as [? ? ? [] ?]; unfold add_rep_var, add_size_var, kc_le in *; cbn in *; split; [|split]; lia.
  - intros t κ; rewrite !fc_type_vars_add_size !list_lookup_fmap.
    destruct (fc_type_vars F !! t) as [κ0|] eqn:Ht; [|done].
    by rewrite (Hv _ _ Ht).
Qed.

Lemma kind_ok_le K K' κ : kc_le K K' -> kind_ok K κ -> kind_ok K' κ.
Proof. intros (_ & Hr & Hs); by apply kind_ok_mono. Qed.

Lemma has_kind_weaken F τ κ :
  has_kind F τ κ -> forall F', ctx_le F F' -> has_kind F' τ κ.
Proof.
  apply (has_kind_ind'
           (fun F τ κ => forall F', ctx_le F F' -> has_kind F' τ κ)
           (fun F ϕ => forall F', ctx_le F F' -> has_kind_ift F' ϕ)
           (fun F ϕ => forall F', ctx_le F F' -> has_kind_ft F' ϕ)).
  all: try (intros F0; cbv zeta; intros; by constructor).
  all: try (intros F0 τs xs ξs IH; cbv zeta; intros F' Hle;
            constructor; eapply Forall3_impl; [exact IH|]; intros; by eauto).
  - intros F0 m β τ0 σ ξ Hm IH; cbv zeta; intros F' Hle.
    eapply KRefVar; [|by apply IH].
    eapply mem_ok_mono; [apply Hle|done].
  - intros F0 β τ0 σ ξ IH; cbv zeta; intros F' Hle; eapply KRefMM; by apply IH.
  - intros F0 β τ0 σ ξ IH; cbv zeta; intros F' Hle; eapply KRefGC; by apply IH.
  - intros F0 ϕ IH; cbv zeta; intros F' Hle; apply KCodeRef; by apply IH.
  - intros F0 τ0 ρ ξ IH; cbv zeta; intros F' Hle; apply KSer; by apply IH.
  - intros F0 ρ Hρ; cbv zeta; intros F' Hle; apply KPlug.
    eapply rep_ok_mono; [apply Hle|done].
  - intros F0 σ Hσ; cbv zeta; intros F' Hle; apply KSpan.
    eapply size_ok_mono; [apply Hle|apply Hle|done].
  - intros F0 τ0 κ0 κbody Hok IH Hsub F' Hle.
    eapply KRec; [by eapply kind_ok_le; [apply Hle|]|by apply IH, ctx_le_cons|done].
  - intros F0 τ0 κ0 Hok IH F' Hle.
    apply KExistsMem; [by eapply kind_ok_le; [apply Hle|]|by apply IH, ctx_le_mem].
  - intros F0 τ0 κ0 Hok IH F' Hle.
    apply KExistsRep; [by eapply kind_ok_le; [apply Hle|]|by apply IH, ctx_le_rep].
  - intros F0 τ0 κ0 Hok IH F' Hle.
    apply KExistsSize; [by eapply kind_ok_le; [apply Hle|]|by apply IH, ctx_le_size].
  - intros F0 τ0 κ0 κ1 Hok0 Hok IH F' Hle.
    apply KExistsType;
      [by eapply kind_ok_le; [apply Hle|]|by eapply kind_ok_le; [apply Hle|]|by apply IH, ctx_le_cons].
  - intros F0 t κ0 Hlook Hok F' Hle.
    apply KVar; [by apply Hle|by eapply kind_ok_le; [apply Hle|]].
  - intros F0 τs1 τs2 κs1 κs2 IH1 IH2 F' Hle.
    apply (KMonoFun _ _ _ κs1 κs2); eapply Forall2_impl; [exact IH1| |exact IH2|]; by eauto.
  - intros F0 ϕ IH F' Hle; apply KInnerFun; by apply IH.
  - intros F0 ϕ IH F' Hle; apply KForallMem; by apply IH, ctx_le_mem.
  - intros F0 ϕ IH F' Hle; apply KForallRep; by apply IH, ctx_le_rep.
  - intros F0 ϕ IH F' Hle; apply KForallSize; by apply IH, ctx_le_size.
  - intros F0 κ0 ϕ Hok IH F' Hle.
    apply KForallType; [by eapply kind_ok_le; [apply Hle|]|by apply IH, ctx_le_cons].
Qed.

Lemma has_kind_ift_weaken ϕ : forall F F',
  ctx_le F F' -> has_kind_ift F ϕ -> has_kind_ift F' ϕ.
Proof.
  induction ϕ as [τs1 τs2|κ ϕ IH]; intros F F' Hle Hk; inversion Hk; subst.
  - eapply KMonoFun; (eapply Forall2_impl; try eassumption; intros; by eapply has_kind_weaken).
  - apply KForallType; [by eapply kind_ok_le; [apply Hle|]|by eapply IH; [apply ctx_le_cons|]].
Qed.

Lemma has_kind_ft_weaken ϕ : forall F F',
  ctx_le F F' -> has_kind_ft F ϕ -> has_kind_ft F' ϕ.
Proof.
  induction ϕ as [ϕ|ϕ IH|ϕ IH|ϕ IH]; intros F F' Hle Hk; inversion Hk; subst.
  - apply KInnerFun; by eapply has_kind_ift_weaken.
  - apply KForallMem; by eapply IH; [apply ctx_le_mem|].
  - apply KForallRep; by eapply IH; [apply ctx_le_rep|].
  - apply KForallSize; by eapply IH; [apply ctx_le_size|].
Qed.

Lemma ctx_le_empty F : ctx_le fc_empty F.
Proof. split; [unfold kc_le; cbn; split; [|split]; lia|by intros []]. Qed.

Lemma has_kind_empty :
  (forall τ κ, has_kind fc_empty τ κ -> forall F, has_kind F τ κ) /\
  (forall ϕ, has_kind_ft fc_empty ϕ -> forall F, has_kind_ft F ϕ) /\
  (forall ϕ, has_kind_ift fc_empty ϕ -> forall F, has_kind_ift F ϕ).
Proof.
  split; [|split]; intros;
    eauto using has_kind_weaken, has_kind_ft_weaken, has_kind_ift_weaken, ctx_le_empty.
Qed.
