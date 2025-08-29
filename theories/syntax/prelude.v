Require Import Morphisms Setoid Relation_Definitions core unscoped.

Inductive path_component :=
| PCProj (n : nat)
| PCUnwrap.

Definition path := list path_component.
