(* Accumulating state monad *)
(* Like a state monad with S = list A, but writes append to the state
   instead of replacing the state. *)

Require Import stdpp.base.

From ExtLib.Structures Require Import Functor Monads Monoid.

Require Import RichWasm.util.

Class MonadAccum (S : Type) (M : Type -> Type) `{Monad M} : Type :=
  { get : M S;
    acc : S -> M unit }.

Record accumT (S : Type) (M : Type -> Type) (A : Type) : Type :=
  mkAccumT { runAccumT : S -> M (A * S)%type }.

Arguments mkAccumT {_ _ _} _.
Arguments runAccumT {_ _ _} _ _.

Definition evalAccumT {S M A} `{Monad M} (m : accumT S M A) (s : S) : M A :=
  bind (runAccumT m s) $ fun x => ret (fst x).

Definition execAccumT {S M A} `{Monad M} (m : accumT S M A) (s : S) : M S :=
  bind (runAccumT m s) $ fun x => ret (snd x).

Definition gets {S M A} `{MonadAccum S M} (f : S -> A) : M A :=
  fmap f get.

Global Instance Monad_accumT {S M} `{Monoid S, Monad M} : Monad (accumT S M) :=
  { ret _ x := mkAccumT $ fun s => ret (x, monoid_unit);
    bind _ _ m1 m2 := mkAccumT $ fun s =>
      '(v, s') ← runAccumT m1 s;
      '(v, s'') ← runAccumT (m2 v) (monoid_plus s s');
      ret (v, monoid_plus s' s'') }.

Global Instance MonadAccum_accumT {S M} `{Monoid S, Monad M} : MonadAccum S (accumT S M) :=
  { get := mkAccumT $ fun s => ret (s, monoid_unit);
    acc s' := mkAccumT $ fun s => ret (tt, s') }.

Global Instance MonadT_accumT {S M} `{Monoid S, Monad M} : MonadT (accumT S M) M :=
  { lift _ c := mkAccumT $ fun s => t ← c; ret (t, monoid_unit) }.

Global Instance MonadExc_accumT {S M A} `{Monoid S, Monad M, MonadExc A M} :
  MonadExc A (accumT S M) :=
  { raise _ e := lift (raise e);
    catch _ body hnd := mkAccumT $ fun s =>
      catch (runAccumT body s) (fun e => runAccumT (hnd e) s) }.

Global Instance MonadZero_accumT {S M} `{Monoid S, Monad M, MonadZero M} : MonadZero (accumT S M) :=
  { mzero _ := lift mzero }.

Global Instance MonadFix_accumT {S M} `{MonadFix M} : MonadFix (accumT S M) :=
  { mfix _ _ r v := mkAccumT $ fun s =>
      mfix2 _ (fun r v s => runAccumT (mkAccumT (r v)) s) v s }.

Global Instance MonadPlus_accumT {S M} `{Monad M, MonadPlus M} : MonadPlus (accumT S M) :=
  { mplus _ _ a b := mkAccumT $ fun s =>
      res ← mplus (runAccumT a s) (runAccumT b s);
      match res with
      | inl (a, s') => ret (inl a, s')
      | inr (b, s') => ret (inr b, s')
      end }.

Global Instance MonadWriter_accumT {S M A} `{Monoid S, m : Monoid A, Monad M, @MonadWriter A m M} :
  @MonadWriter A m (accumT S M) :=
  { tell x := mkAccumT $ fun s => v ← tell x; ret (v, monoid_unit);
    listen A c := mkAccumT $ fun s => '(a, s', t) ← listen (runAccumT c s); ret (a, t, s');
    pass _ c := mkAccumT $ fun s => pass ('(x, f, s') ← runAccumT c s; ret (x, s', f)) }.
