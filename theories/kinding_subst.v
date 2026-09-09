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

(* [RecT]'s kind is a genuine binder annotation (unlike the aggregate/self
   kinds that used to be cached on other constructors), so unfolding a
   recursive type via self-substitution preserves its kind without needing
   any "refresh" pass -- this is exactly the kind of fact that used to need
   [refreshed_kinds]/[refresh_kinds] gymnastics for the OTHER constructors,
   but is straightforward here. Left admitted: it needs a genuine general
   substitution lemma for [has_kind] (threading through Sum/Variant/Prod/
   Struct's Forall3 premises and the context-extending Rec/ExistsX binders).
   Note this isn't a regression from the refactor -- the pre-refactor version
   of this lemma (`has_kind_rec_subst`, old kinding_subst.v) derived from
   `has_kind_subst_rec_helper`, which was *already* `Admitted` before the
   refactor; the substitution machinery for [has_kind] has never actually
   been proven in this codebase. *)
Lemma has_kind_rec_subst :
  ∀ τ F κ, let τrec := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
           has_kind F (RecT κ τ) κ -> has_kind F τrec κ.
Proof.
Admitted.

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
