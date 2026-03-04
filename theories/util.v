From stdpp Require Import gmap list.

From mathcomp Require Import eqtype boot.seq.

Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Monads.WriterMonad.
From ExtLib.Structures Require Import Functor Monads Monoid.

From Wasm Require common stdpp_aux.
Require Import Wasm.numerics.

Require Import RichWasm.syntax.

Inductive pointer_flag :=
| FlagPtr
| FlagInt.

Definition flag_of_i32 (n : i32) : pointer_flag :=
  if Wasm_int.Int32.eq n Wasm_int.Int32.zero
  then FlagInt
  else FlagPtr.

Definition i32_of_flag (f : pointer_flag) : i32 :=
  match f with
  | FlagInt => Wasm_int.Int32.zero
  | FlagPtr => Wasm_int.Int32.one
  end.

Definition arep_flags (ι : atomic_rep) : list pointer_flag :=
  match ι with
  | PtrR => [FlagPtr]
  | I32R => [FlagInt]
  | I64R => [FlagInt; FlagInt]
  | F32R => [FlagInt]
  | F64R => [FlagInt; FlagInt]
  end.

(* Unfortunately, ExtLib defines Monoid as a record.
   Make it behave like a typeclass, as God intended. *)
Existing Class Monoid.
Existing Instance Monoid_list_app.
Arguments monoid_unit {_ _}.
Arguments monoid_plus {_ _}.
Arguments writerT _ {_} _ _.

Global Instance Monoid_pair {A B} `{Monoid A, Monoid B} : Monoid (A * B) :=
  {| monoid_unit := (monoid_unit, monoid_unit);
     monoid_plus '(a1, b1) '(a2, b2) := (monoid_plus a1 a2, monoid_plus b1 b2) |}.

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

Definition option_last {A : Type} (a : option A) (b : option A) : option A :=
  match b with
  | None => a
  | _ => b
  end.

Definition nths_error {A : Type} (l : list A) (ixs : list nat) : option (list A) :=
  mapM (nth_error l) ixs.

Lemma nths_error_length {A : Type} (l l': list A) (ixs : list nat) :
  nths_error l ixs = Some l' ->
  length ixs = length l'.
Proof. apply length_mapM. Qed.

Lemma nths_error_exists {A B : Type} (l1 l1' : list A) (l2 : list B) (ixs : list nat) :
  length l1 = length l2 ->
  nths_error l1 ixs = Some l1' ->
  is_Some (nths_error l2 ixs).
Proof.
  intros Hlen Hnths_error.
  apply mapM_is_Some.
  rewrite <- (Forall_iff (λ i : nat, is_Some (nth_error l1 i))).
  2: {
    intros x; simpl.
    rewrite stdpp_aux.nth_error_lookup.
    rewrite lookup_lt_is_Some.
    rewrite Hlen.
    symmetry.
    rewrite stdpp_aux.nth_error_lookup.
    apply lookup_lt_is_Some.
  }
  apply mapM_is_Some.
  done.
Qed.

Lemma nths_error_zip {A B : Type} (l1 l1' : list A) (l2 l2' : list B) (ixs : list nat) :
  nths_error l1 ixs = Some l1' ->
  nths_error l2 ixs = Some l2' ->
  nths_error (base.zip l1 l2) ixs = Some (base.zip l1' l2').
Proof.
  intros H1 H2.
  apply mapM_Some.
  apply mapM_Some in H1, H2.
  revert l2' H2.
  induction H1 as [|i y1 ixs l1' Hi1 Hrest IH];
    intros l2' H2.
  - inversion H2; constructor.
  - inversion H2 as [|i' y2 ixs' l2'' Hi2 Hrest2]; subst.
    constructor.
    + rewrite stdpp_aux.nth_error_lookup.
      rewrite lookup_zip_Some.
      by do 2 rewrite <- stdpp_aux.nth_error_lookup.
    + apply IH; assumption.
Qed.

Lemma nths_error_Forall {A : Type} Φ (l l' : list A) (ixs : list nat) :
  Forall Φ l ->
  nths_error l ixs = Some l' ->
  Forall Φ l'.
Proof.
  revert l l'.
  induction ixs; intros l l' Hf Hnerr.
  - simpl in *.
    by inversion Hnerr.
  - simpl in *.
    simplify_option_eq.
    constructor.
    + rewrite Forall_lookup in Hf.
      eapply Hf.
      simplify_eq.
      by rewrite <- stdpp_aux.nth_error_lookup.
    + eapply IHixs; eauto.
Qed.

(* How is this not a lemma in stdpp? *)
Lemma Forall_Forall2 {A B : Type} (P : A → B → Prop) (l1 : list A) (l2 : list B) :
  length l1 = length l2 ->
  Forall (uncurry P) (base.zip l1 l2) ->
  Forall2 P l1 l2.
Proof.
  revert l2.
  induction l1 as [|x l1 IH]; intros l2 Hlen Hf.
  - destruct l2; simpl in *; first done.
    discriminate.
  - destruct l2 as [|y l2]; simpl in *; first discriminate.
    inversion Hlen as [Hlen'].
    inversion Hf as [|[x' y'] zs HPxy Hf_rest]; subst.
    auto.
Qed.

(* This direction is proven in stdpp, but requires l1 and l2 to be lists of the same type...*)
Lemma Forall2_Forall {A B} P (l1 : list A) (l2 : list B) :
  Forall2 P l1 l2 → Forall (uncurry P) (base.zip l1 l2).
Proof. induction 1; constructor; auto. Qed.

Lemma nths_error_Forall2 {A B : Type} (Φ : A -> B -> Prop) (l1 l1' : list A) (l2 l2' : list B) (ixs : list nat) :
  Forall2 Φ l1 l2 ->
  nths_error l1 ixs = Some l1' ->
  nths_error l2 ixs = Some l2' ->
  Forall2 Φ l1' l2'.
Proof.
  intros.
  apply Forall_Forall2.
  - apply nths_error_length in H0, H1.
    by rewrite <- H0, H1.
  - eapply (nths_error_Forall _ (base.zip l1 l2) _ ixs).
    + by apply Forall2_Forall.
    + by apply nths_error_zip.
Qed.

Lemma nths_error_Forall2_exists {A B : Type} (Φ : A -> B -> Prop) (l1 l1' : list A) (l2 : list B) (ixs : list nat) :
  Forall2 Φ l1 l2 ->
  nths_error l1 ixs = Some l1' ->
  ∃ l2', nths_error l2 ixs = Some l2' ∧ Forall2 Φ l1' l2'.
Proof.
  intros Hf2 Hnerr.
  apply (list_relations.Forall2_length) in Hf2 as Hlen.
  edestruct (nths_error_exists l1 l1' l2) as [l2' Hsome]; try done.
  exists l2'.
  split; first done.
  eapply nths_error_Forall2; done.
Qed.

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

Lemma set_nth_neq:
  ∀ {A : Type} (l : seq.seq A) (i j : nat) (x : A),
    i < length l ->
    i <> j ->
    seq.set_nth x l i x !! j = l !! j.
Proof.
  intros.
  rewrite properties.update_list_at_is_set_nth.
    rewrite stdpp_aux.update_ne; auto.
    auto using lt_ssrleq.
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
