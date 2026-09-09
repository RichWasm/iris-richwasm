From mathcomp Require Import ssreflect.
From stdpp Require Import base list.
From RichWasm Require Import syntax typing util.
Require Import RecordUpdate.RecordUpdate.
From RichWasm.typechecker Require Import typechecker.

Set Bullet Behavior "Strict Subproofs".

(* typechecker.v carries its own copy of refresh_kinds, which typing.v's refreshed_kinds
   relation has to agree with -- that agreement is refresh_kinds_connect_has_kind_maybe,
   the sole assumption of has_module_type_checker_correct.

   The two copies diverged on RecT: the typechecker kept the annotation while
   refreshed_kinds recomputed it, which made the assumption false once KRec gained its
   subkind premise.  Both keep it now.  These pin the case down so the divergence cannot
   silently return. *)

Definition κ_no : kind := VALTYPE (AtomR PtrR) NoRefs.
Definition κ_any : kind := VALTYPE (AtomR PtrR) AnyRefs.

(* Well kinded only through KRec's subkind premise: κ_no is the body's kind, κ_any the
   annotation.  This is the shape that broke. *)
Definition τ_slack : type := RecT κ_any (I31T κ_no).

Lemma τ_slack_kinded : has_kind fc_empty τ_slack κ_any.
Proof. eapply KRec; [repeat constructor|constructor|repeat constructor]. Qed.

Lemma tc_refresh_agrees_on_rec_slack :
  typechecker.refresh_kinds fc_empty τ_slack = τ_slack ∧
  refreshed_kinds fc_empty τ_slack τ_slack.
Proof. split; [by cbv|by repeat constructor]. Qed.
