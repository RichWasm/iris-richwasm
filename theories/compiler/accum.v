(* Accumulating state monad *)
(* Like a state monad with S = list A, but writes append to the state
   instead of replacing the state. *)

From stdpp Require Import base.
From ExtLib.Structures Require Import Functor Monads Monoid.

Class MonadAccum@{s d c} (S : Type@{s}) (m : Type@{d} -> Type@{c}) : Type :=
  { get : m (list S);
    acc : list S -> m unit }.

Section Accum.
  Variables 
    (S : Type)
    (m : Type -> Type).

  Record accumT (t: Type) : Type :=
    mkAccumT { runAccumT : list S -> m (t * list S)%type }.
  Arguments mkAccumT {t} _.
  Arguments runAccumT {t} _.

  Variable M : Monad m.

  Definition evalAccumT {t} (c : accumT t) (s : list S) : m t :=
    bind (runAccumT c s) (fun x => ret (fst x)).

  Definition execAccumT {t} (c : accumT t) (s : list S) : m (list S) :=
    bind (runAccumT c s) (fun x => ret (snd x)).

  Global Instance MonadAccum_accumT : MonadAccum S accumT :=
    { get := mkAccumT (fun s => ret (s, nil));
      acc := fun s' => mkAccumT (fun s => ret (tt, s')) }.

  Global Instance Monad_accumT : Monad accumT :=
  { ret := fun _ x => mkAccumT (fun s => @ret _ M _ (x, nil))
  ; bind := fun _ _ c1 c2 =>
    mkAccumT (fun s =>
      @bind _ M _ _ (runAccumT c1 s)
        (fun '(v, s') =>
           @bind _ M _ _ (runAccumT (c2 v) (s ++ s')) 
             (fun '(v, s'') => ret (v,s' ++ s''))))
  }.

  Global Instance MonadT_accumT : MonadT accumT m :=
  { lift := fun _ c => mkAccumT (fun s => bind c (fun t => ret (t, nil)))
  }.

  Global Instance Exc_accumT T (MR : MonadExc T m) : MonadExc T accumT :=
  { raise := fun _ e => lift (raise e)
  ; catch := fun _ body hnd =>
    mkAccumT (fun s => catch (runAccumT body s) (fun e => runAccumT (hnd e) s))
  }.

  Global Instance MonadZero_stateT (MR : MonadZero m) : MonadZero accumT :=
  { mzero _A := lift mzero
  }.

  Global Instance MonadFix_stateT (MF : MonadFix m) : MonadFix accumT :=
  { mfix := fun _ _ r v =>
    mkAccumT (fun s => mfix2 _ (fun r v s => runAccumT (mkAccumT (r v)) s) v s)
  }.

  Global Instance MonadPlus_stateT (MP : MonadPlus m) : MonadPlus accumT :=
  { mplus _A _B a b :=
      mkAccumT (fun s => bind (mplus (runAccumT a s) (runAccumT b s))
               (fun res => match res with
                             | inl (a,s') => ret (inl a, s')
                             | inr (b,s') => ret (inr b, s')
                           end))
  }.

  Global Instance MonadWriter_accumT T (Mon : Monoid T) (MR : MonadWriter Mon m) : MonadWriter Mon accumT :=
  { tell := fun x => mkAccumT (fun s => bind (tell x) (fun v => ret (v, nil)))
  ; listen := fun A (c: accumT A) =>
                mkAccumT (fun s => bind (listen (runAccumT c s))
                                         (fun x => let '(a,s',t) := x in ret (a,t,s')))
  ; pass := fun _ c =>
              mkAccumT (fun s => pass (bind (runAccumT c s)
                                      (fun '(x, f, s') => ret (x, s', f))))
  }.

End Accum.

Arguments mkAccumT {S m t} _.
Arguments runAccumT {S m t} _.
