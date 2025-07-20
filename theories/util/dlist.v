Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.

Require Import ExtLib.Structures.Monoid.

Record dlist A := { apply_dlist : list A -> list A }.

Arguments Build_dlist {A} _.
Arguments apply_dlist {A} _.

Definition empty {A} : dlist A :=
  Build_dlist id.

Definition singleton {A} (x : A) : dlist A :=
  Build_dlist (cons x).

Definition cons {A} (x : A) (xs : dlist A) : dlist A :=
  Build_dlist (compose (cons x) (apply_dlist xs)).

Definition append {A} (xs : dlist A) (ys : dlist A) : dlist A :=
  Build_dlist (compose (apply_dlist xs) (apply_dlist ys)).

Definition concat {A} (xs : list (dlist A)) : dlist A :=
  fold_right append empty xs.

Definition of_list {A} (xs : list A) : dlist A :=
  Build_dlist (app xs).

Definition to_list {A} (xs : dlist A) : list A :=
  apply_dlist xs nil.

Definition Monoid_dlist {A} : Monoid (dlist A) :=
  {| monoid_plus := append;
     monoid_unit := empty |}.

Module Notation.

  Declare Scope dlist_scope.
  Delimit Scope dlist_scope with DL.
  Bind Scope dlist_scope with dlist.
  Local Open Scope dlist_scope.

  Infix "::" := cons : dlist_scope.

  Infix "++" := append : dlist_scope.

  Notation "[ ]" := empty : dlist_scope.

  Notation "[ x ]" := (x :: []) : dlist_scope.

  Notation "[ x1 ; x2 ; .. ; xn ]" := (x1 :: x2 :: .. [xn] ..) : dlist_scope.

End Notation.
