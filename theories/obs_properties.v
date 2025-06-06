From RWasm Require Import obs.
From stdpp Require Import base orders.
Inductive obs_le : obs -> obs -> Prop :=
| RunBot: forall o, obs_le Run o
| BailRefl: obs_le Bail Bail
| CrashRefl: obs_le Crash Crash.
Definition obs_lt := strict obs_le.

Definition obs_eq_dec: EqDecision obs.
Proof.
  unfold EqDecision, Decision.
  decide equality.
Defined.

Proposition bail_neq_not_le o:
  o <> Bail ->
  ~ obs_le Bail o.
Proof.
  intros H H'.
  apply H.
  by inversion H'.
Qed.

Proposition crash_neq_not_le o:
  o <> Crash ->
  ~ obs_le Crash o.
Proof.
  intros H H'.
  apply H.
  by inversion H'.
Qed.

Definition obs_le_dec (o1 o2: obs) : Decision (obs_le o1 o2) :=
  match o1 as o1 return Decision (obs_le o1 o2) with
  | Run => left (RunBot o2)
  | Bail =>
      match obs_eq_dec o2 Bail with
      | left e => left (eq_ind_r _ BailRefl e)
      | right n => right (bail_neq_not_le _ n)
      end
  | Crash =>
      match obs_eq_dec o2 Crash with
      | left e => left (eq_ind_r _ CrashRefl e)
      | right n => right (crash_neq_not_le _ n)
      end
  end.

Instance obs_le_rd: RelDecision obs_le := obs_le_dec.

Program Instance obs_po: PartialOrder obs_le.
Next Obligation.
  split.
  - intros [| |]; constructor.
  - intros x y z Hxy Hyz.
    + inversion Hxy; inversion Hyz; subst; discriminate + constructor.
Qed.
Next Obligation.
  intros x y Hxy Hyx.
  inversion Hxy; inversion Hyx; congruence.
Qed.
