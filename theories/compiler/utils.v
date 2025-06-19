From Coq Require Import List Lists.List.
From stdpp Require Import base list decidable.

Section AddIfNotIn.
  Context `{EqDecision A}.

  Fixpoint add_if_not_in (x : A) (l : list A) : list A :=
    if bool_decide (x ∈ l) then l else x :: l.
End AddIfNotIn.

Fixpoint list_prefix {A} (rel : A → A → bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], _ => true
  | x1 :: xs1, x2 :: xs2 =>
      rel x1 x2 && list_prefix rel xs1 xs2
  | _, _ => false
  end.

(* built-in has reversed args *)
Fixpoint foldl' {A B} (f : A -> B -> B) (init : B) (l : list A) : B :=
  match l with
  | [] => init
  | x :: xs => let acc := f x init in foldl' f acc xs
  end.
