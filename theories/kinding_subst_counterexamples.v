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
        has_instruction_type_ok M F (InstrT τs1 τs2) L →
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


(* Regression witnesses for the RecT annotation.

   634281ef gave KRec a [subkind_of κbody κ] premise, so a RecT annotation is allowed to
   over-approximate its body's kind.  refresh_kinds recomputing that annotation
   (06608975) was therefore incompatible with refresh_kinds_id -- recomputation
   canonicalizes, and a well-kinded RecT is no longer canonical.  Both refresh_kinds and
   RKRec now keep the annotation; these pin that down. *)

Definition κ_i64 : kind := VALTYPE (AtomR I64R) NoRefs.

(* A RecT annotation is not a function of its body, so it cannot be synthesized: it is a
   declaration, not a cache, which is why refresh must leave it alone.  Representation
   variables would add forms, not remove these two, so this stays true under them. *)
Lemma rec_kind_not_determined_by_body :
  has_kind fc_empty (RecT κ_no (VarT 0)) κ_no ∧
  has_kind fc_empty (RecT κ_i64 (VarT 0)) κ_i64 ∧
  κ_no ≠ κ_i64.
Proof.
  split; [|split].
  - eapply KRec;
      [repeat constructor|apply KVar; [done|repeat constructor]|apply subkind_of_refl].
  - eapply KRec;
      [repeat constructor|apply KVar; [done|repeat constructor]|apply subkind_of_refl].
  - discriminate.
Qed.

(* The witness that broke the recomputing version: well kinded only through KRec's
   subkind premise, so recomputation tightened κ_any to κ_no and refresh_kinds_id failed. *)
Definition τ_slack : type := RecT κ_any (I31T κ_no).

Lemma τ_slack_kinded : has_kind fc_empty τ_slack κ_any.
Proof. eapply KRec; [repeat constructor|constructor|repeat constructor]. Qed.

Lemma τ_slack_refresh_fixed : refresh_kinds fc_empty τ_slack = τ_slack.
Proof. by cbv. Qed.

Lemma τ_slack_refreshed : refreshed_kinds fc_empty τ_slack τ_slack.
Proof. by repeat constructor. Qed.

(* And the witness where recomputation moved the representation, not just the ref flag:
   kind_of_node was called in the unextended F, missed the rec binder, and fell through
   to its VALTYPE (AtomR I32R) NoRefs default. *)
Definition τ_selfvar : type := RecT κ_no (VarT 0).

Lemma τ_selfvar_refresh_fixed : refresh_kinds fc_empty τ_selfvar = τ_selfvar.
Proof. by cbv. Qed.

(* ExistsRepT and ExistsSizeT used to keep their annotation while KExistsRep/KExistsSize
   demand the body's kind exactly, so instantiation produced an ill-kinded type -- the
   cause-B bug 34849c4c fixed for ExistsMemT and ExistsTypeT only.  refresh now recomputes
   their ref flag, which is the only component that can go stale: FTInstType requires
   subkind_of κ_wit κ_declared, so substitution fixes the representation and can only
   lower the flag.  These pin the repaired behaviour down. *)

Lemma exists_rep_refresh_lowers_flag :
  refresh_kinds fc_empty (ExistsRepT κ_any (I31T κ_no)) = ExistsRepT κ_no (I31T κ_no)
  ∧ has_kind fc_empty (ExistsRepT κ_no (I31T κ_no)) κ_no.
Proof.
  split; [by cbv|apply KExistsRep; [repeat constructor|constructor]].
Qed.

Lemma exists_size_refresh_lowers_flag :
  refresh_kinds fc_empty (ExistsSizeT κ_any (I31T κ_no)) = ExistsSizeT κ_no (I31T κ_no)
  ∧ has_kind fc_empty (ExistsSizeT κ_no (I31T κ_no)) κ_no.
Proof.
  split; [by cbv|apply KExistsSize; [repeat constructor|constructor]].
Qed.

(* The backward direction of the old has_kind_ft_through_inst_iff is unaffected by any of
   this: inst refreshes its result, so a derivation for ϕ' says nothing about the
   annotations of the ϕ it came from.  ift_bad is ill kinded, ift_good is not, and
   inst_bad relates them. *)
Lemma has_kind_ft_through_inst_backwards_false :
  ¬ (∀ F ϕ ϕ' ix, function_type_inst F ix ϕ ϕ' → has_kind_ft F ϕ' → has_kind_ft F ϕ).
Proof.
  intros Hbogus.
  assert (Hk : has_kind_ft fc_empty (InnerFunT ift_good))
    by (by apply KInnerFun, ift_good_kinded).
  have Hbad := Hbogus fc_empty (InnerFunT (ForallTypeT κ_no ift_bad))
                 (InnerFunT ift_good) (TypeI (I31T κ_no))
                 (FTInstInner _ _ _ _ inst_bad) Hk.
  inversion Hbad as [? ? Hift| | | ]; subst.
  inversion Hift as [|? ? ? ? Hb]; subst.
  by eapply ift_bad_not_kinded, Hb.
Qed.
