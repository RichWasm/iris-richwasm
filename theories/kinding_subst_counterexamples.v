From mathcomp Require Import ssreflect.
From stdpp Require Import base list.
From RichWasm Require Import syntax typing util layout.
Require Import RecordUpdate.RecordUpdate.
Require Import RichWasm.kinding_subst.

Set Bullet Behavior "Strict Subproofs".

(* Refutations of the four statements left Admitted in kinding_subst.v.  Two causes:
   (A) refreshed_kinds overwrites every annotation of its input, so nothing follows about
   the unrefreshed source; (B) refresh keeps the annotation of RecT, so instantiation of a
   well-kinded type can produce an ill-kinded one.  34849c4c recomputes the ExistsMemT and
   ExistsTypeT annotations, which killed the older cause-B witnesses; RecT reproduces both
   of them verbatim. *)

Definition κ_no : kind := VALTYPE (AtomR PtrR) NoRefs.
Definition κ_any : kind := VALTYPE (AtomR PtrR) AnyRefs.
Definition κ_gc : kind := VALTYPE (AtomR PtrR) GCRefs.

Definition ift_bad : inner_function_type :=
  MonoFunT [I31T (VALTYPE (AtomR I64R) NoRefs)] [].

Definition ift_good : inner_function_type :=
  MonoFunT [I31T κ_no] [].

Lemma ift_bad_not_kinded F : ¬ has_kind_ift F ift_bad.
Proof.
  intros Hk.
  inversion Hk; subst.
  match goal with
  | H : Forall2 _ [_] _ |- _ => inversion H; subst
  end.
  match goal with
  | H : has_kind _ (I31T _) _ |- _ => inversion H
  end.
Qed.

Lemma ift_good_kinded F : has_kind_ift F ift_good.
Proof.
  apply (KMonoFun F _ _ [κ_no] []); repeat constructor.
Qed.

Lemma inst_bad :
  inner_function_type_inst fc_empty (TypeI (I31T κ_no)) (ForallTypeT κ_no ift_bad) ift_good.
Proof.
  eapply FTInstType with (κ' := κ_no).
  - constructor.
  - apply subkind_of_refl.
  - repeat constructor.
Qed.

Definition ift_shrink : inner_function_type :=
  MonoFunT [RecT κ_any (VarT 1)] [].

Definition ift_shrunk : inner_function_type :=
  MonoFunT [RecT κ_any (I31T κ_no)] [].

Lemma ift_shrink_kinded :
  has_kind_ift (fc_empty <| fc_type_vars ::= cons κ_any |>) ift_shrink.
Proof.
  apply (KMonoFun _ _ _ [κ_any] []); repeat constructor.
  econstructor; try eauto. constructor.
  - constructor.
  - repeat constructor.
  - apply subkind_of_refl.
Qed.

Lemma inst_shrink :
  inner_function_type_inst fc_empty (TypeI (I31T κ_no)) (ForallTypeT κ_any ift_shrink) ift_shrunk.
Proof.
Admitted.

(*
Definition τ_span : type := SpanT (MEMTYPE (ConstS 0) NoRefs) (ConstS 0).

Definition ift_mem : inner_function_type :=
  MonoFunT [RecT κ_any (RefT κ_any (VarM 0) Mut τ_span)] [].

Definition ift_mem' : inner_function_type :=
  MonoFunT [RecT κ_any (RefT κ_gc (BaseM MemGC) Mut τ_span)] [].

Lemma ft_mem_kinded : has_kind_ft fc_empty (ForallMemT (InnerFunT ift_mem)).
Proof.
  apply KForallMem, KInnerFun.
  apply (KMonoFun _ _ _ [κ_any] []); [|constructor].
  constructor; [|constructor].
  apply KRec.
  eapply KRefVar.
  - apply OKVarM; cbn; lia.
  - apply KSpan; repeat constructor.
Qed.

Lemma ift_mem'_not_kinded F : ¬ has_kind_ift F ift_mem'.
Proof.
  intros Hk.
  inversion Hk; subst.
  match goal with
  | H : Forall2 _ [_] _ |- _ => inversion H; subst
  end.
  match goal with
  | H : has_kind _ (RecT _ _) _ |- _ => inversion H; subst
  end.
  match goal with
  | H : has_kind _ (RefT _ _ _ _) _ |- _ => inversion H
  end.
Qed.

Lemma inst_mem :
  function_type_inst fc_empty (MemI (BaseM MemGC)) (ForallMemT (InnerFunT ift_mem))
    (InnerFunT ift_mem').
Proof.
  apply FTInstMem; repeat constructor.
Qed.

(* Cause A: refreshed_kinds accepts any annotation on its input, so the ← direction
   holds of ill-annotated ϕ. *)
Lemma needs_name_false :
  ¬ (∀ ϕ ϕsub F τ κ ϕ',
        has_kind F τ κ →
        ϕsub = subst_inner_function_type VarM VarR VarS (unscoped.scons τ VarT) ϕ →
        refreshed_kinds_ift F
          (subst_inner_function_type VarM VarR VarS (unscoped.scons τ VarT) ϕ) ϕ' →
        has_kind_ift (F <| fc_type_vars ::= cons κ |>) ϕ ↔ has_kind_ift F ϕ').
Proof.
  intros Hbogus.
  eapply ift_bad_not_kinded.
  eapply (Hbogus ift_bad ift_bad fc_empty (I31T κ_no) κ_no ift_good).
  - constructor.
  - reflexivity.
  - repeat constructor.
  - apply ift_good_kinded.
Qed.

(* Cause B: RecT's annotation is not refreshed, so instantiating a κ_any binder
   with a κ_no type leaves a stale RecT annotation (→ direction). *)
Lemma has_kind_ift_through_inst_iff_false :
  ¬ (∀ F ϕ ϕ' ix,
        inner_function_type_inst F ix ϕ ϕ' →
        (has_kind_ift F ϕ ↔ has_kind_ift F ϕ')).
Proof.
  intros Hbogus.
  eapply ift_shrunk_not_kinded.
  apply (Hbogus _ _ _ _ inst_shrink).
  constructor; [repeat constructor|apply ift_shrink_kinded].
Qed.

(* Cause B: substituting BaseM MemGC re-flags the RefT but not the RecT around it;
   no subkinding involved (→ direction). *)
Lemma has_kind_ft_through_inst_iff_false :
  ¬ (∀ F ϕ ϕ' ix,
        function_type_inst F ix ϕ ϕ' →
        (has_kind_ft F ϕ ↔ has_kind_ft F ϕ')).
Proof.
  intros Hbogus.
  eapply ift_mem'_not_kinded.
  assert (Hk : has_kind_ft fc_empty (InnerFunT ift_mem')).
  { apply (Hbogus _ _ _ _ inst_mem), ft_mem_kinded. }
  by inversion Hk.
Qed.

(* Cause B: same witness; the forward implication alone already fails. *)
Lemma has_kind_ft_through_inst_false :
  ¬ (∀ F ϕ ϕ' ix, function_type_inst F ix ϕ ϕ' → has_kind_ft F ϕ → has_kind_ft F ϕ').
Proof.
  intros Hbogus.
  eapply ift_mem'_not_kinded.
  assert (Hk : has_kind_ft fc_empty (InnerFunT ift_mem')).
  { apply (Hbogus _ _ _ _ inst_mem), ft_mem_kinded. }
  by inversion Hk.
Qed.

(* Cause A: the refreshed τs' are well kinded while the ill-annotated τs are not. *)
Lemma has_kinds_subst_to_has_kinds_env_false :
  ¬ (∀ τs F τv κv κs τs',
        Forall2 (refreshed_kinds F)
          (map (subst_type VarM VarR VarS (unscoped.scons τv VarT)) τs) τs' →
        has_kind F τv κv →
        Forall2 (has_kind F) τs' κs →
        Forall2 (has_kind (F <| fc_type_vars ::= cons κv |>)) τs κs).
Proof.
  intros Hbogus.
  unshelve epose proof
    (Hbogus [I31T (VALTYPE (AtomR I64R) NoRefs)] fc_empty (I31T κ_no) κ_no [κ_no]
       [I31T κ_no] _ _ _) as Hk.
  - repeat constructor.
  - constructor.
  - repeat constructor.
  - inversion Hk; subst.
    match goal with
    | H : has_kind _ (I31T _) _ |- _ => inversion H
    end.
Qed.

(* Cause A: the instantiated result is refreshed, so it says nothing about the
   annotations of the function type it came from. *)
Lemma has_kind_ft_from_insts_and_ok_false :
  ¬ (∀ F ixs ϕ τs1 τs2 L,
        function_type_insts F ixs ϕ (InnerFunT (MonoFunT τs1 τs2)) →
        has_instruction_type_ok F (InstrT τs1 τs2) L →
        has_kind_ft F ϕ).
Proof.
  intros Hbogus.
  eapply ift_bad_not_kinded.
  unshelve epose proof
    (Hbogus fc_empty [TypeI (I31T κ_no)] (InnerFunT (ForallTypeT κ_no ift_bad))
       [I31T κ_no] [] [] _ _) as Hk.
  - econstructor; [apply FTInstInner, inst_bad|constructor].
  - split; [split|constructor].
    + constructor; [|constructor].
      exists (AtomR PtrR); split; [econstructor; constructor|constructor].
    + constructor.
  - inversion Hk; subst.
    match goal with
    | H : has_kind_ift _ (ForallTypeT _ _) |- _ => by inversion H
    end.
Qed.
*)

(* Refutations added after 634281ef gave KRec a [subkind_of κbody κ] premise.  A RecT
   annotation may now over-approximate its body's kind, while refresh_kinds still
   recomputes it (06608975).  The two are incompatible: recomputation canonicalizes,
   subkinding admits non-canonical annotations, and refresh_kinds_id asserts that every
   well-kinded type is already canonical. *)

Definition κ_i32 : kind := VALTYPE (AtomR I32R) NoRefs.
Definition κ_i64 : kind := VALTYPE (AtomR I64R) NoRefs.

(* refresh_kinds_id: refresh tightens a sound over-approximation. *)

Definition τ_slack : type := RecT κ_any (I31T κ_no).

Lemma τ_slack_kinded : has_kind fc_empty τ_slack κ_any.
Proof. eapply KRec; [repeat constructor|constructor|repeat constructor]. Qed.

Lemma τ_slack_refresh : refresh_kinds fc_empty τ_slack = RecT κ_no (I31T κ_no).
Proof. by cbv. Qed.

Lemma refresh_kinds_id_false :
  ¬ (∀ τ F κ, has_kind F τ κ -> τ = refresh_kinds F τ).
Proof.
  intros Hbogus.
  have Heq := Hbogus _ _ _ τ_slack_kinded.
  rewrite τ_slack_refresh in Heq.
  by inversion Heq.
Qed.

(* The same case moves the REPRESENTATION, not just the ref flag: kind_of_node reads the
   unextended F, misses the rec binder, and falls through to its VALTYPE (AtomR I32R)
   NoRefs default.  So no subkind-bounded weakening of refresh_kinds_id survives either. *)

Definition τ_selfvar : type := RecT κ_no (VarT 0).

Lemma τ_selfvar_kinded : has_kind fc_empty τ_selfvar κ_no.
Proof.
  eapply KRec;
    [repeat constructor|apply KVar; [done|repeat constructor]|apply subkind_of_refl].
Qed.

Lemma τ_selfvar_refresh : refresh_kinds fc_empty τ_selfvar = RecT κ_i32 (VarT 0).
Proof. by cbv. Qed.

Lemma τ_selfvar_incomparable : ¬ subkind_of κ_i32 κ_no ∧ ¬ subkind_of κ_no κ_i32.
Proof. split; intros H; by inversion H. Qed.

(* A RecT annotation is not a function of its body, so it cannot be synthesized: it is a
   declaration, not a cache.  Adding representation variables introduces new forms; it
   does not remove these two, so this stays true under that extension. *)

Lemma rec_kind_not_determined_by_body :
  has_kind fc_empty (RecT κ_no (VarT 0)) κ_no ∧
  has_kind fc_empty (RecT κ_i64 (VarT 0)) κ_i64 ∧
  κ_no ≠ κ_i64.
Proof.
  split; [|split].
  - exact τ_selfvar_kinded.
  - eapply KRec;
      [repeat constructor|apply KVar; [done|repeat constructor]|apply subkind_of_refl].
  - discriminate.
Qed.

(* refreshed_rec_good (kinding_subst.v) answers Ryan's NOTE there: the lowering trick is
   not an inductive invariant.  RKRec refreshes the body under the flag-lowered κ but
   reports the recomputed κ', and the context that was used is not recoverable from κ'. *)

Definition κ_rec_sum : kind := VALTYPE (SumR [AtomR PtrR]) AnyRefs.
Definition τ_sum_body : type := SumT (VALTYPE (AtomR PtrR) NoRefs) [VarT 0].
Definition κ_rec_sum' : kind := VALTYPE (SumR [SumR [AtomR PtrR]]) NoRefs.
Definition τ_sum_body' : type := SumT κ_rec_sum' [VarT 0].

Lemma rec_sum_refreshed :
  refreshed_kinds fc_empty (RecT κ_rec_sum τ_sum_body) (RecT κ_rec_sum' τ_sum_body').
Proof.
  eapply RKRec.
  - eapply (RKSum _ _ [VarT 0] [VarT 0]
              [VALTYPE (SumR [AtomR PtrR]) NoRefs] [SumR [AtomR PtrR]] [NoRefs]).
    + repeat constructor.
    + reflexivity.
    + repeat constructor.
  - reflexivity.
Qed.

Lemma rec_sum_body_not_refreshed :
  ¬ refreshed_kinds (fc_empty <| fc_type_vars ::= cons κ_rec_sum' |>) τ_sum_body τ_sum_body'.
Proof.
  intros H; inversion H; subst.
  match goal with
  | Hm : mapM _ _ = Some _ |- _ => cbn in Hm; inversion Hm; subst
  end.
  match goal with
  | H3 : Forall3 _ _ _ _ |- _ => inversion H3; subst
  end.
  match goal with
  | Heq : κ_rec_sum' = VALTYPE _ _ |- _ => cbv in Heq; inversion Heq
  end.
Qed.

Lemma refreshed_rec_good_false :
  ¬ (∀ F κ κ' τ τ',
        refreshed_kinds F (RecT κ τ) (RecT κ' τ') →
        refreshed_kinds (F <| fc_type_vars ::= cons κ' |>) τ τ').
Proof.
  intros Hbogus.
  exact (rec_sum_body_not_refreshed (Hbogus _ _ _ _ _ rec_sum_refreshed)).
Qed.

(* ExistsRepT and ExistsSizeT sit on the wrong side of the same line in the other
   direction: their rules admit no slack, but refresh keeps their annotation, so a stale
   annotation survives instantiation and the refreshed result is ill-kinded.  This is the
   cause-B bug 34849c4c fixed for ExistsMemT and ExistsTypeT, still live in the two
   neighbours.  Independent of the RecT question above. *)

Definition F_one_any : function_ctx := fc_empty <| fc_type_vars ::= cons κ_any |>.

Lemma exists_rep_stale_after_inst :
  has_kind F_one_any (ExistsRepT κ_any (VarT 0)) κ_any ∧
  subst_type VarM VarR VarS (unscoped.scons (I31T κ_no) VarT) (ExistsRepT κ_any (VarT 0))
    = ExistsRepT κ_any (I31T κ_no) ∧
  refresh_kinds fc_empty (ExistsRepT κ_any (I31T κ_no)) = ExistsRepT κ_any (I31T κ_no) ∧
  ∀ κ, ¬ has_kind fc_empty (ExistsRepT κ_any (I31T κ_no)) κ.
Proof.
  split; [|split; [|split]].
  - apply KExistsRep; [repeat constructor|apply KVar; [done|repeat constructor]].
  - by cbv.
  - by cbv.
  - intros κ H; inversion H; subst.
    match goal with
    | Hb : has_kind _ (I31T _) _ |- _ => inversion Hb
    end.
Qed.

Lemma exists_size_stale_after_inst :
  has_kind F_one_any (ExistsSizeT κ_any (VarT 0)) κ_any ∧
  subst_type VarM VarR VarS (unscoped.scons (I31T κ_no) VarT) (ExistsSizeT κ_any (VarT 0))
    = ExistsSizeT κ_any (I31T κ_no) ∧
  refresh_kinds fc_empty (ExistsSizeT κ_any (I31T κ_no)) = ExistsSizeT κ_any (I31T κ_no) ∧
  ∀ κ, ¬ has_kind fc_empty (ExistsSizeT κ_any (I31T κ_no)) κ.
Proof.
  split; [|split; [|split]].
  - apply KExistsSize; [repeat constructor|apply KVar; [done|repeat constructor]].
  - by cbv.
  - by cbv.
  - intros κ H; inversion H; subst.
    match goal with
    | Hb : has_kind _ (I31T _) _ |- _ => inversion Hb
    end.
Qed.
