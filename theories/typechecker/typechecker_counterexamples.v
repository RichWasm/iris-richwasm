From mathcomp Require Import ssreflect.
From stdpp Require Import base list.
From RichWasm Require Import syntax typing util.
Require Import RecordUpdate.RecordUpdate.
From RichWasm.typechecker Require Import typechecker.

Set Bullet Behavior "Strict Subproofs".

(* refresh_kinds_connect_has_kind_maybe is the sole assumption of
   has_module_type_checker_correct, and it is false.

   typechecker.v carries its own copy of refresh_kinds, which KEEPS the RecT annotation.
   typing.v's refreshed_kinds relation RECOMPUTES it (RKRec's type_kind side condition).
   Since 634281ef gave KRec a subkind premise, a well-kinded RecT may carry an
   over-approximating annotation, and then the two definitions disagree by construction:
   no derivation of refreshed_kinds relates the type to itself.

   This is a consequence of the same RecT divergence refuted in
   RichWasm.kinding_subst_counterexamples; fixing RKRec is a precondition for this
   assumption being provable at all. *)

Definition κ_no : kind := VALTYPE (AtomR PtrR) NoRefs.
Definition κ_any : kind := VALTYPE (AtomR PtrR) AnyRefs.
Definition τ_slack : type := RecT κ_any (I31T κ_no).

Lemma tc_refresh_keeps_annotation : typechecker.refresh_kinds fc_empty τ_slack = τ_slack.
Proof. by cbv. Qed.

Lemma tc_refresh_kinded : has_kind fc_empty (typechecker.refresh_kinds fc_empty τ_slack) κ_any.
Proof.
  rewrite tc_refresh_keeps_annotation.
  eapply KRec; [repeat constructor|constructor|repeat constructor].
Qed.

Lemma tc_refresh_not_refreshed : ¬ refreshed_kinds fc_empty τ_slack τ_slack.
Proof.
  intros H; inversion H; subst.
  match goal with
  | Hk : layout.type_kind _ _ = Some _ |- _ => cbv in Hk; inversion Hk
  end.
Qed.

Lemma refresh_kinds_connect_has_kind_maybe_false :
  ¬ (∀ τ F κ,
        has_kind F (typechecker.refresh_kinds F τ) κ →
        refreshed_kinds F τ (typechecker.refresh_kinds F τ)).
Proof.
  intros Hbogus.
  apply tc_refresh_not_refreshed.
  rewrite -{2}tc_refresh_keeps_annotation.
  exact (Hbogus _ _ _ tc_refresh_kinded).
Qed.
