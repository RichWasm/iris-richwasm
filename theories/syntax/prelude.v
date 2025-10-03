Require Import Morphisms Setoid Relation_Definitions core unscoped.

Inductive path_component :=
| PCProj (n : nat)
| PCSkip.

Definition path := list path_component.
