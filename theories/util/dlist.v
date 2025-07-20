Require Coq.Lists.List.
Require Import Coq.Program.Basics.
Local Open Scope program_scope.

Require Import ExtLib.Structures.Monoid.

Record dlist A := { apply_dlist : list A -> list A }.

Arguments Build_dlist {A} _.
Arguments apply_dlist {A} _.

Module DList.

  Definition nil {A} : dlist A :=
    Build_dlist id.

  Definition cons {A} (x : A) (xs : dlist A) : dlist A :=
    Build_dlist (cons x ∘ apply_dlist xs).

  Definition singleton {A} (x : A) : dlist A :=
    cons x nil.

  Definition append {A} (xs : dlist A) (ys : dlist A) : dlist A :=
    Build_dlist (apply_dlist xs ∘ apply_dlist ys).

  Definition flatten {A} (xs : list (dlist A)) : dlist A :=
    List.fold_right append nil xs.

  Definition of_list {A} (xs : list A) : dlist A :=
    Build_dlist (app xs).

  Definition to_list {A} (xs : dlist A) : list A :=
    apply_dlist xs List.nil.

  Definition Monoid_dlist {A} : Monoid (dlist A) :=
    {| monoid_plus := append;
      monoid_unit := nil |}.

End DList.

Module Notation.

  Declare Scope dlist_scope.
  Delimit Scope dlist_scope with DL.
  Bind Scope dlist_scope with dlist.
  Local Open Scope dlist_scope.

  Infix "::" := DList.cons : dlist_scope.

  Infix "++" := DList.append : dlist_scope.

  Notation "[ ]" := DList.nil : dlist_scope.

  Notation "[ x ]" := (x :: []) : dlist_scope.

  Notation "[ x1 ; x2 ; .. ; xn ]" := (x1 :: x2 :: .. [xn] ..) : dlist_scope.

End Notation.
