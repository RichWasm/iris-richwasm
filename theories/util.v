From stdpp Require Import gmap list.

From ExtLib.Structures Require Import Functor Monads.

Global Instance MRet_Monad (M : Type -> Type) `(Monad M) : MRet M :=
  { mret := fun _ => ret }.

Global Instance MBind_Monad (M : Type -> Type) `(Monad M) : MBind M :=
  { mbind := fun _ _ => flip bind }.

Global Instance MJoin_Monad (M : Type -> Type) `(Monad M) : MJoin M :=
  { mjoin := fun _ => join }.

Global Instance FMap_Functor (F : Type -> Type) `(Functor F) : FMap F :=
  { fmap := fun _ _ => fmap }.

Definition nths_error {A : Type} (l : list A) (ixs : list nat) : option (list A) :=
  mapM (nth_error l) ixs.

Definition gmap_injective `{Countable K} {V} (m : gmap K V) :=
  ∀ k1 k2 v, m !! k1 = Some v -> m !! k2 = Some v -> k1 = k2.
