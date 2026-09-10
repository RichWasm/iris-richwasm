(** [unpacked_existential] enters the binder without shifting the function context.

    Each case builds the inner context with [subst_function_ctx (up_X VarX) ...].  The [up_X]
    are typeclass methods of the autosubst output, and resolution picks, for every sort, a lift
    that is extensionally [VarX]: [up_memory VarM] and [up_representation VarR] resolve to the
    same-sort [up_X_X], which lifts a substitution under a binder of that sort and so fixes
    [VarX]; [up_size VarS] and [up_type VarT] resolve to cross-sort lifts
    ([Up_representation_size], [Up_memory_type]) that rename a sort [VarX] does not mention.
    None is the weakening [funcomp VarX shift] the rule needs, so [fc_labels] and [fc_return]
    are read inside the binder unshifted while [L], [τs1] and [τs2] are shifted by [ren_type].

    [unpack_forgets_witness] is the consequence: unpacking [∃α:κ. α] and branching to the
    unpack's own label types as [[∃α:κ. α] → [β]] for the enclosing type variable [β].  The
    compiler turns it into [block (i32 → i32) { br 0 }], so read semantically any κ-value is a
    β-value. *)

From stdpp Require Import list.
From RichWasm Require Import syntax typing.

Lemma up_memory_VarM n : up_memory VarM n = VarM n.
Proof. by destruct n. Qed.

Lemma up_representation_VarR n : up_representation VarR n = VarR n.
Proof. by destruct n. Qed.

Lemma up_size_VarS n : up_size VarS n = VarS n.
Proof. done. Qed.

Lemma up_type_VarT n : up_type VarT n = VarT n.
Proof. done. Qed.

Lemma map_id_ext {A} (f : A -> A) l : (forall a, f a = a) -> map f l = l.
Proof. intros H; induction l; cbn; congruence. Qed.

Lemma subst_function_ctx_id σm σr σs σt F :
  (forall n, σm n = VarM n) ->
  (forall n, σr n = VarR n) ->
  (forall n, σs n = VarS n) ->
  (forall n, σt n = VarT n) ->
  subst_function_ctx σm σr σs σt F = F.
Proof.
  intros Hm Hr Hs Ht.
  destruct F; unfold subst_function_ctx; cbn; f_equal.
  - apply map_id_ext; intros τ; by apply idSubst_type.
  - apply map_id_ext; intros [τs L]; f_equal; apply map_id_ext; intros τ; by apply idSubst_type.
  - apply map_id_ext; intros κ; by apply idSubst_kind.
Qed.

Lemma unpack_mem_ctx_id F : subst_function_ctx (up_memory VarM) VarR VarS VarT F = F.
Proof. apply subst_function_ctx_id; [exact up_memory_VarM | done..]. Qed.

Lemma unpack_rep_ctx_id F : subst_function_ctx VarM (up_representation VarR) VarS VarT F = F.
Proof. apply subst_function_ctx_id; [done | exact up_representation_VarR | done..]. Qed.

Lemma unpack_size_ctx_id F : subst_function_ctx VarM VarR (up_size VarS) VarT F = F.
Proof. apply subst_function_ctx_id; [done | done | exact up_size_VarS | done]. Qed.

Lemma unpack_type_ctx_id F : subst_function_ctx VarM VarR VarS (up_type VarT) F = F.
Proof. apply subst_function_ctx_id; [done.. | exact up_type_VarT]. Qed.

Definition κ32 : kind := VALTYPE (AtomR I32R) NoRefs.

(** One abstract type variable [β := VarT 0], nothing else in scope. *)
Definition F_β : function_ctx :=
  {| fc_return := [];
     fc_locals := [];
     fc_labels := [];
     fc_kind_ctx := kc_empty;
     fc_type_vars := [κ32] |}.

Definition M_empty : module_ctx := {| mc_functions := []; mc_table := [] |}.

Definition τ_ex : type := ExistsTypeT κ32 κ32 (VarT 0).

Definition ψ_unpack : instruction_type := InstrT [τ_ex] [VarT 0].

(** Inside the binder [VarT 0] is the unpacked [α] and the label pushed by [TUnpack] still
    reads [([VarT 0], [])], so [br 0] type checks against it. *)
Definition e_unpack : instruction :=
  IUnpack ψ_unpack [] [IBr (InstrT [VarT 0] [VarT 1]) 0].

Lemma kind_ok_κ32 K : kind_ok K κ32.
Proof. repeat constructor. Qed.

Lemma has_mono_rep_var F t :
  F.(fc_type_vars) !! t = Some κ32 -> has_mono_rep F (VarT t).
Proof.
  intros Ht.
  exists (AtomR I32R); split; [|constructor].
  econstructor; apply KVar; [exact Ht | apply kind_ok_κ32].
Qed.

Lemma unpack_forgets_witness :
  has_instruction_type M_empty F_β [] e_unpack ψ_unpack [].
Proof.
  unfold e_unpack, ψ_unpack.
  eapply TUnpack.
  - apply (UnpackType _ [] [] [] κ32 κ32 (VarT 0) [VarT 0]).
  - cbn.
    apply TSingleton.
    apply (TBr _ _ _ _ 0 [VarT 0] [] [VarT 1]); [done | constructor |].
    split; [split | split]; [.. | constructor | split; constructor].
    + repeat constructor; by apply has_mono_rep_var.
    + repeat constructor; by apply has_mono_rep_var.
  - split; [split | split]; [.. | constructor | split; constructor].
    + repeat constructor.
      exists (AtomR I32R); split; [|constructor].
      econstructor; apply KExistsType; [apply kind_ok_κ32.. |].
      apply KVar; [done | apply kind_ok_κ32].
    + repeat constructor; by apply has_mono_rep_var.
Qed.
