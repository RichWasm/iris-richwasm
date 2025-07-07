From Coq Require Import Program.Basics Program.Syntax.
From stdpp Require Import base option gmap.
Open Scope stdpp_scope.

Definition stateT (St : Type) (M : Type -> Type) (A : Type) : Type :=
 St -> M (prod St A).

Arguments stateT _ _ _ : clear implicits.

Section stateT_instances.

  Context {S : Type} {M : Type → Type}.
  Context `{!FMap M, !MBind M, !MRet M}.

  #[export]
  Instance stateT_FMap : FMap (stateT S M) :=
    λ A B f ma s, fmap (λ '(s', x), (s', f x)) (ma s).

  #[export]
  Instance stateT_MRet : MRet (stateT S M) :=
    λ A x s, mret (s, x).

  #[export]
  Instance stateT_MBind : MBind (stateT S M) :=
    λ A B f x s,
      mbind (λ '(s', a), f a s') (x s).

  #[export]
  Instance stateT_MJoin : MJoin (stateT S M) :=
    λ A mm s,
      mbind (λ '(s', m), m s') (mm s).
End stateT_instances.

Section stateT_throw.
  Context {S : Type} {E : Type} {M : Type → Type}.
  Context `{!MBind M, !MRet M, !MThrow E M}.

  #[export]
  Instance stateT_MThrow : MThrow E (stateT S M) :=
    λ A e _s, mthrow e.
End stateT_throw.

(** * Basic state primitives **)
Section stateT_ops.
  Context {S : Type} {M : Type → Type}.
  Context `{!MBind M, !MRet M}.

  Definition mget : stateT S M S :=
    λ s, mret (s, s).

  Definition mput (s' : S) : stateT S M unit :=
    λ _ , mret (s', tt).

  Definition mmodify (f : S → S) : stateT S M unit :=
    λ s, mret (f s, tt).

  Definition liftM {A} (m : M A) : stateT S M A :=
    λ st,
      x ← m;
      mret (st, x).
End stateT_ops.

