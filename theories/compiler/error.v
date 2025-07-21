Inductive error :=
  | EWrongTypeAnn
  | EGlobalIndexOutOfBounds (index : nat)
  | ELocalIndexOutOfBounds (index : nat)
  | ESizeIndexOutOfBounds (index : nat)
  | ETodo.
