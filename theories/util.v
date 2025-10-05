From stdpp Require Import gmap list.
From mathcomp.ssreflect Require seq.

From Wasm Require common stdpp_aux.
From ExtLib.Structures Require Import Functor Monads.

Global Instance MRet_Monad (M : Type -> Type) `(Monad M) : MRet M :=
  { mret := fun _ => ret }.

Global Instance MBind_Monad (M : Type -> Type) `(Monad M) : MBind M :=
  { mbind := fun _ _ => flip bind }.

Global Instance MJoin_Monad (M : Type -> Type) `(Monad M) : MJoin M :=
  { mjoin := fun _ => join }.

Global Instance FMap_Functor (F : Type -> Type) `(Functor F) : FMap F :=
  { fmap := fun _ _ => fmap }.

Definition try_option {M : Type -> Type} {E A : Type} `{Monad M, MonadExc E M}
  (e : E) (x : option A) : M A :=
  match x with
  | None => raise e
  | Some x' => ret x'
  end.

Definition ignore {M : Type -> Type} {A : Type} `{Monad M} (c : M A) : M unit :=
  c;; ret tt.

Definition mapM_ {M : Type -> Type} {A B : Type} `{Monad M} (f : A → M B) (l : list A) : M unit :=
  ignore (mapM f l).

Definition nths_error {A : Type} (l : list A) (ixs : list nat) : option (list A) :=
  mapM (nth_error l) ixs.

Definition gmap_injective `{Countable K} {V} (m : gmap K V) :=
  ∀ k1 k2 v, m !! k1 = Some v -> m !! k2 = Some v -> k1 = k2.

Lemma set_nth_length_eq {T} (x: T) (l: seq.seq T) (i: nat) (d: T) :
    i < seq.size l ->
    length (seq.set_nth x l i d) = length l.
Proof.
  intros.
  by rewrite seq.size_set_nth, common.maxn_nat_max, max_r.
Qed.

Lemma set_nth_gt (i: nat) :
  ∀ {A : Type} (l : seq.seq A) (x0 : A) (x : A),
    i >= length l ->
    seq.set_nth x0 l i x = l ++ seq.ncons (i - length l) x0 [x].
Proof.
  induction i; intros.
  - destruct l.
    + reflexivity.
    + inversion H.
  - destruct l; simpl.
    + reflexivity.
    + simpl in *.
      assert (Hi: i >= length l) by lia.
      rewrite IHi; auto.
Qed.

Lemma lt_ssrleq x y :
  x < y ->
  is_true (ssrnat.leq (S x) y).
Proof.
  destruct (@ssrnat.ltP x y); auto.
Qed.

Lemma set_nth_read_neq:
  ∀ {A : Type} (l : seq.seq A) (i j : nat) (x y : A),
    i <> j ->
    l !! j = Some y ->
    seq.set_nth x l i x !! j = Some y.
Proof.
  intros.
  destruct (Nat.lt_dec i (seq.size l)).
  - rewrite properties.update_list_at_is_set_nth.
    rewrite stdpp_aux.update_ne; auto.
    auto using lt_ssrleq.
  - rewrite set_nth_gt.
    + rewrite lookup_app_l; auto.
      apply lookup_lt_is_Some_1; auto.
    + replace @seq.size with @length in n; [lia | done].
Qed.
