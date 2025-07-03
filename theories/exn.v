From stdpp Require Import base option list.

Set Universe Polymorphism.

Section exceptions.
  Variables (E: Type).

  Inductive exn (A : Type) : Type :=
  | Exn (e: E)
  | OK (a: A).
  Arguments Exn {A} e.
  Arguments OK {A} a.

  Definition exn_to_opt {A: Type} (c: exn A) : option A :=
    match c with
    | Exn _ => None
    | OK a => Some a
    end.

  Definition exn_map {A B: Type} (f: A -> B) (c: exn A) : exn B :=
    match c with
    | Exn e => Exn e
    | OK a => OK (f a)
    end.

  Definition exn_bind {A B: Type} (f: A -> exn B) (c: exn A) : exn B :=
    match c with
    | Exn e => Exn e
    | OK a => f a
    end.

  Definition exn_join {A: Type} (c: exn (exn A)) : exn A :=
    match c with
    | OK (OK a) => OK a
    | OK (Exn e)
    | Exn e => Exn e
    end.

End exceptions.

Arguments OK {E A} _.
Arguments Exn {E A} _.

#[export]
Instance exn_FMap {E} : FMap (exn E) := @exn_map E.

#[export]
Instance exn_MBind {E} : MBind (exn E) := @exn_bind E.

#[export]
Instance exn_MRet {E} : MRet (exn E) := @OK E.

#[export]
Instance exn_MJoin {E} : MJoin (exn E) := @exn_join E.

#[export]
Instance exn_throw {E} : MThrow E (exn E) := @Exn E.

Definition guard_opt {E A} (err: E) (c: option A) : exn E A :=
  match c with
  | Some a => mret a
  | None => mthrow err
  end.

Lemma fmap_OK {E A B} :
  forall (f: A -> B) (c: exn E A) (b: B),
    f <$> c = OK b <-> exists a: A, c = OK a /\ f a = b.
Proof.
Admitted.

Lemma mapM_OK {E A B} :
  ∀ (f : A → exn E B) (l: list A) (k: list B),
    mapM f l = OK k ↔ Forall2 (λ a b, f a = OK b) l k.
Proof.
Admitted.
