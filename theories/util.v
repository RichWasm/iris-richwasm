From stdpp Require Import gmap list.

From mathcomp Require Import eqtype boot.seq.

Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Monads.WriterMonad.
From ExtLib.Structures Require Import Functor Monads Monoid.

From RichWasm.wasm Require common stdpp_aux.
Require Import RichWasm.wasm.numerics.

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

  Lemma flag_of_i32_left_inv (f : pointer_flag) : flag_of_i32 (i32_of_flag f) = f.
  Proof.
    destruct f; unfold i32_of_flag, flag_of_i32; done.
  Qed.

Definition arep_flags (ι : atomic_rep) : list pointer_flag :=
  match ι with
  | PtrR => [FlagPtr]
  | I32R => [FlagInt]
  | I64R => [FlagInt; FlagInt]
  | F32R => [FlagInt]
  | F64R => [FlagInt; FlagInt]
  end.

Definition set_flags_at (off : nat) (new_flags : list pointer_flag)
    (fs : list pointer_flag) : list pointer_flag :=
  list_inserts off new_flags fs.

Lemma set_flags_at_succ_cons (off : nat) (adding : list pointer_flag)
    (f : pointer_flag) (fs : list pointer_flag) :
  set_flags_at (S off) adding (f :: fs) = f :: set_flags_at off adding fs.
Proof.
  unfold set_flags_at. revert off.
  induction adding as [|a adding IH]; intros off; [done|].
  cbn [list_inserts]. rewrite (IH (S off)). done.
Qed.

Lemma set_flags_at_zero_cons (a : pointer_flag) (adding : list pointer_flag)
    (f : pointer_flag) (fs : list pointer_flag) :
  set_flags_at 0 (a :: adding) (f :: fs) = a :: set_flags_at 0 adding fs.
Proof.
  unfold set_flags_at. cbn [list_inserts].
  pose proof (set_flags_at_succ_cons 0 adding f fs) as H.
  unfold set_flags_at in H. rewrite H. done.
Qed.


  Lemma updating_flags (off : nat) (adding fs : list pointer_flag) :
    off + length adding ≤ length fs →
    ∃ fs1 fs_old fs2,
      fs = fs1 ++ fs_old ++ fs2 ∧
      set_flags_at off adding fs = fs1 ++ adding ++ fs2 ∧
      length fs_old = length adding ∧
      length fs1 = off.
  Proof.
    revert off adding.
    induction fs as [|f fs IH].
    - intros off adding Hlens.
      cbn in Hlens. destruct off; [|lia]. destruct adding; [|cbn in Hlens; lia].
      exists [], [], []. unfold set_flags_at. done.
    - intros off adding Hlens.
      destruct off.
      + destruct adding as [|a adding].
        * exists [], [], (f :: fs). unfold set_flags_at. done.
        * cbn in Hlens.
          specialize (IH 0 adding ltac:(lia)) as (fs1 & fs_old & fs2 & Hfs & Hset & Hlenold & Hlenfs1).
          assert (fs1 = []) as -> by (destruct fs1; [done | cbn in Hlenfs1; lia]).
          cbn in Hfs.
          exists [], (f :: fs_old), fs2.
          split; [rewrite Hfs; done |].
          split; [rewrite set_flags_at_zero_cons; rewrite Hset; done |].
          split; [cbn; lia | done].
      + cbn in Hlens.
        specialize (IH off adding ltac:(lia)) as (fs1 & fs_old & fs2 & Hfs & Hset & Hlenold & Hlenfs1).
        exists (f :: fs1), fs_old, fs2.
        split; [rewrite Hfs; done |].
        split; [rewrite set_flags_at_succ_cons; rewrite Hset; done |].
        split; [done | cbn; lia].
  Qed.


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

Definition nths_error_dup {A : Type} (l : list A) (ixs : list nat) : option (list A) :=
  mapM (nth_error l) ixs.

Definition nths_error {A : Type} (l : list A) (ixs : list nat) : option (list A) :=
  if NoDup_dec ixs
  then nths_error_dup l ixs
  else None.

Lemma nths_error_some_dup {A : Type} (l : list A) (ixs : list nat) (l' : list A) :
  nths_error l ixs = Some l' ->
  nths_error_dup l ixs = Some l'.
Proof.
  intros Hnerr.
  unfold nths_error in Hnerr.
  by destruct (NoDup_dec ixs) as [Hnodup | Hdup].
Qed.

Lemma nths_error_some_iff {A : Type} (l : list A) (ixs : list nat) (l' : list A) :
  nths_error l ixs = Some l' <->
  base.NoDup ixs /\ nths_error_dup l ixs = Some l'.
Proof.
  unfold nths_error.
  destruct (NoDup_dec ixs) as [Hnodup | Hdup].
  - split.
    + intro H. split; [exact Hnodup | exact H].
    + intros [_ H]. exact H.
  - split.
    + discriminate.
    + intros [Hnodup _]. contradiction.
Qed.

Lemma nths_error_dup_length {A : Type} (l l': list A) (ixs : list nat) :
  nths_error_dup l ixs = Some l' ->
  length ixs = length l'.
Proof. apply length_mapM. Qed.

Lemma nths_error_length {A : Type} (l l': list A) (ixs : list nat) :
  nths_error l ixs = Some l' ->
  length ixs = length l'.
Proof.
  intros Hnerr.
  eapply nths_error_dup_length.
  by apply nths_error_some_dup.
Qed.

Lemma nths_error_dup_exists {A B : Type} (l1 l1' : list A) (l2 : list B) (ixs : list nat) :
  length l1 = length l2 ->
  nths_error_dup l1 ixs = Some l1' ->
  is_Some (nths_error_dup l2 ixs).
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

Lemma nths_error_exists {A B : Type} (l1 l1' : list A) (l2 : list B) (ixs : list nat) :
  length l1 = length l2 ->
  nths_error l1 ixs = Some l1' ->
  is_Some (nths_error l2 ixs).
Proof.
  intros Hlen Hnths_error.
  apply nths_error_some_iff in Hnths_error as [Hnd Hnerrd].
  eapply nths_error_dup_exists in Hnerrd; try done.
  destruct Hnerrd as [x H].
  unfold is_Some.
  exists x.
  by rewrite nths_error_some_iff.
Qed.

Lemma nths_error_dup_zip {A B : Type} (l1 l1' : list A) (l2 l2' : list B) (ixs : list nat) :
  nths_error_dup l1 ixs = Some l1' ->
  nths_error_dup l2 ixs = Some l2' ->
  nths_error_dup (base.zip l1 l2) ixs = Some (base.zip l1' l2').
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

Lemma nths_error_zip {A B : Type} (l1 l1' : list A) (l2 l2' : list B) (ixs : list nat) :
  nths_error l1 ixs = Some l1' ->
  nths_error l2 ixs = Some l2' ->
  nths_error (base.zip l1 l2) ixs = Some (base.zip l1' l2').
Proof.
  intros Hner1 Hner2.
  apply nths_error_some_iff in Hner1 as [Hnd Hner1d].
  apply nths_error_some_iff in Hner2 as [_ Hner2d].
  rewrite nths_error_some_iff.
  split; first done.
  by apply nths_error_dup_zip.
Qed.

Lemma nths_error_dup_Forall {A : Type} Φ (l l' : list A) (ixs : list nat) :
  Forall Φ l ->
  nths_error_dup l ixs = Some l' ->
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

Lemma nths_error_Forall {A : Type} Φ (l l' : list A) (ixs : list nat) :
  Forall Φ l ->
  nths_error l ixs = Some l' ->
  Forall Φ l'.
Proof.
  intros HF Hnerr.
  apply nths_error_some_iff in Hnerr as [Hnd Hnerrd].
  by eapply nths_error_dup_Forall.
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

Lemma nths_error_dup_Forall2 {A B : Type} (Φ : A -> B -> Prop) (l1 l1' : list A) (l2 l2' : list B) (ixs : list nat) :
  Forall2 Φ l1 l2 ->
  nths_error_dup l1 ixs = Some l1' ->
  nths_error_dup l2 ixs = Some l2' ->
  Forall2 Φ l1' l2'.
Proof.
  intros.
  apply Forall_Forall2.
  - apply nths_error_dup_length in H0, H1.
    by rewrite <- H0, H1.
  - eapply (nths_error_dup_Forall _ (base.zip l1 l2) _ ixs).
    + by apply Forall2_Forall.
    + by apply nths_error_dup_zip.
Qed.


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

Lemma nths_error_dup_Forall2_exists {A B : Type} (Φ : A -> B -> Prop) (l1 l1' : list A) (l2 : list B) (ixs : list nat) :
  Forall2 Φ l1 l2 ->
  nths_error_dup l1 ixs = Some l1' ->
  ∃ l2', nths_error_dup l2 ixs = Some l2' ∧ Forall2 Φ l1' l2'.
Proof.
  intros Hf2 Hnerr.
  apply Forall2_length in Hf2 as Hlen.
  edestruct (nths_error_dup_exists l1 l1' l2) as [l2' Hsome]; try done.
  exists l2'.
  split; first done.
  eapply nths_error_dup_Forall2; done.
Qed.

Lemma nths_error_Forall2_exists {A B : Type} (Φ : A -> B -> Prop) (l1 l1' : list A) (l2 : list B) (ixs : list nat) :
  Forall2 Φ l1 l2 ->
  nths_error l1 ixs = Some l1' ->
  ∃ l2', nths_error l2 ixs = Some l2' ∧ Forall2 Φ l1' l2'.
Proof.
  intros Hf2 Hnerr.
  apply Forall2_length in Hf2 as Hlen.
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

Lemma sum_list_with_length_concat {A} (lls : list (list A)) :
  sum_list_with length lls = length (concat lls).
Proof.
  induction lls as [| hd tl IH]; simpl; try done.
  rewrite IH.
  rewrite length_app.
  lia.
Qed.

Lemma sum_list_with_list_sum {A} {f : A -> nat} {xs : list A} :
  sum_list_with f xs = list_sum (map f xs).
Proof.
  induction xs.
  - done.
  - cbn.
    by rewrite IHxs.
Qed.

Lemma sum_list_with_take_S_lookup {A} (f : A → nat) (l : list A) (i : nat) (x : A) :
  l !! i = Some x →
  sum_list_with f (list.take i l) + f x = sum_list_with f (list.take (S i) l).
Proof.
  intros Hlookup.
  rewrite (take_S_r _ _ _ Hlookup).
  rewrite sum_list_with_app.
  simpl. lia.
Qed.

Lemma sum_list_with_take_le {A} (f : A → nat) (l : list A) (i : nat) :
  sum_list_with f (list.take i l) ≤ sum_list_with f l.
Proof.
  rewrite <- (list.take_drop i l) at 2.
  rewrite sum_list_with_app.
  lia.
Qed.

Lemma Forall2_sum_list_with_length {A B} (f : A → nat) (g : B → nat) (l1 : list A) (l2 : list B) :
  Forall2 (λ x y, f x = g y) l1 l2 →
  sum_list_with f l1 = sum_list_with g l2.
Proof.
  induction 1 as [| x y l1' l2' Heq _ IH]; simpl; [reflexivity |].
  lia.
Qed.

Definition foldlM `{MRet M, MBind M} {A B: Type} : (A -> B -> M A) -> A -> list B -> M A :=
  λ f a l, foldl (λ acc b, mbind (λ a', f a' b) acc) (mret a) l.

Lemma concat_mjoin {A} (l : list (list A)) :
  concat l = base.mjoin l.
Proof.
  unfold mjoin.
  induction l; first done.
  cbn.
  by f_equal.
Qed.

Lemma Forall2_concat {A B} P (l1 : list (list A)) (l2 : list (list B)) :
  Forall2 (Forall2 P) l1 l2 ->
  Forall2 P (concat l1) (concat l2).
Proof.
  intros.
  rewrite !concat_mjoin.
  by apply Forall2_join.
Qed.

Lemma Forall2_mini_impl {A B : Type} (P Q: A → B → Prop) (l : list A) (k: list B):
  Forall2 P l k -> Forall2 (λ a b, P a b → Q a b) l k -> Forall2 Q l k.
Proof.
  generalize dependent k.
  induction l.
  - intros k HP Hall.
    destruct k; [done|by inversion HP].
  - intros k HP Hall.
    destruct k as [| b k]; [by inversion HP|].
    inversion HP; subst.
    inversion Hall; subst.
    apply Forall2_cons; auto.
Qed.

Lemma Forall2_mini_impl_Forall {A B : Type} (P Q: A → B → Prop) (l : list A) (k: list B):
  Forall2 P l k -> Forall (λ a, ∀ b, P a b → Q a b) l -> Forall2 Q l k.
Proof.
  intros H H'.
  eapply Forall2_mini_impl; try done.
  apply Forall_Forall2_l; last done.
  by apply Forall2_length in H.
Qed.

Lemma forall2_lookup_same {A B} (ls ls' : list A) (idxs : list B) (xs : list A) (j_excl : nat) (f: B -> nat) :
  (∀ j : B, f j ≠ j_excl → ls' !! f j = ls !! f j) ->
  Forall (λ i, f i ≠ j_excl) idxs ->
  Forall2 (λ (i : B) (v : A), ls  !! f i = Some v) idxs xs ->
  Forall2 (λ (i : B) (v : A), ls' !! f i = Some v) idxs xs.
Proof.
  intros Hsame Hnotin Hf.
  induction Hf.
  - constructor.
  - inversion Hnotin; subst.
    constructor.
    + rewrite Hsame; auto.
    + apply IHHf; auto.
Qed.

(* default to stdpp's list for the remainder *)
From stdpp Require Import list.

Lemma mapM_take {A B : Type} n (f : A → option B) (l : list A) (k : list B) :
  mapM f l = Some k →
  mapM f (take n l) = Some (take n k).
Proof.
  intros H.
  rewrite mapM_Some.
  apply Forall2_take.
  by apply mapM_Some.
Qed.

Lemma mapM_drop {A B : Type} n (f : A → option B) (l : list A) (k : list B) :
  mapM f l = Some k →
  mapM f (drop n l) = Some (drop n k).
Proof.
  intros H.
  rewrite mapM_Some.
  apply Forall2_drop.
  by apply mapM_Some.
Qed.

Lemma mapM_lookup {A B} f (l : list A) (k : list B) (i : nat) :
  mapM f l = Some k ->
  (l !! i) ≫= f = k !! i.
Proof.
  intros Hm%mapM_Some_1.
  destruct (l !! i) as [a|] eqn:Hl; simpl.
  - eapply Forall2_lookup_l in Hm as [b [-> Hab]]; eauto.
  - apply lookup_ge_None_1 in Hl.
    symmetry.
    apply lookup_ge_None_2.
    by rewrite <- (Forall2_length _ _ _ Hm).
Qed.

Lemma mapM_app {A B : Type} (f : A → option B) (l : list A) (k1 k2 : list B) :
  mapM f l = Some (k1 ++ k2) →
  ∃ l1 l2,
  l = l1 ++ l2 /\
  mapM f l1 = Some k1 /\
  mapM f l2 = Some k2.
Proof.
  intros H.
  exists (take (length k1) l), (drop (length k1) l).
  split; [by rewrite take_drop |].
  split.
  - erewrite mapM_take; [| exact H].
    by rewrite take_app_length.
  - erewrite mapM_drop; [| exact H].
    by rewrite drop_app_length.
Qed.

Lemma mapM_split {A B : Type} (f : A → option B) (l : list A) (b : B) (k1 k2 : list B) :
  mapM f l = Some (k1 ++ [b] ++ k2) →
  ∃ l1 l2 a,
  l = l1 ++ [a] ++ l2 /\
  mapM f l1 = Some k1 /\
  f a = Some b /\
  mapM f l2 = Some k2.
Proof.
  intros H.
  apply mapM_app in H as (l1 & lrest & Hl & Hk1 & Hrest).
  apply mapM_app in Hrest as (lmid & l2 & Hlrest & Hmid & Hk2).
  apply length_mapM in Hmid as Hlen.
  destruct lmid as [| a [| ? ?]]; try done.
  subst lrest.
  exists l1, l2, a.
  repeat split; try done.
  simpl in Hmid.
  apply bind_Some in Hmid as (b' & Hfa & Hsb).
  inversion Hsb.
  by subst b'.
Qed.


  Lemma zip_eq_seq_zip {A B} (s : list A) (t : list B) :
    zip s t = seq.zip s t.
  Proof.
    revert t. induction s as [|x s IH]; intros [|y t]; done || (cbn; by rewrite IH).
  Qed.

  Lemma zip_rcons {A B:Type} (ls:list A) l (ms: list B) m:
    length ls = length ms ->
    zip (seq.rcons ls l) (seq.rcons ms m) = seq.rcons (zip ls ms) (l, m).
  Proof.
    intros Hlen.
    rewrite !zip_eq_seq_zip.
    by apply seq.zip_rcons.
  Qed.

  Lemma rcons_app {X} : forall (xs : list X) x,
      seq.rcons xs x = xs ++ [x].
  Proof.
    induction xs; intros x.
    - reflexivity.
    - cbn.
      by rewrite IHxs.
  Qed.

  Lemma sum_list_with_rcons {X : Type} (f : X -> nat) (x : X) (xs : list X) :
    sum_list_with f (seq.rcons xs x) = f x + sum_list_with f xs.
  Proof.
    rewrite rcons_app.
    rewrite sum_list_with_app.
    cbn.
    lia.
  Qed.


  Lemma flat_map_rcons X Y (f : X -> list Y) xs x :
    flat_map f (seq.rcons xs x) = flat_map f xs ++ f x.
  Proof.
    revert x.
    induction xs; cbn; intros.
    - by apply app_nil_r.
    - by (rewrite <- app_assoc; rewrite IHxs).
  Qed.

  (* note: simple_fold_sum_list_with in load is just this lol *)
  Lemma seq_foldl_sum_list_with {A:Type} (start:nat) (ls:list A) (f:A → nat):
    seq.foldl (λ acc l, acc + f l) start ls = start + sum_list_with f ls.
  Proof.
    induction ls as [|ls l] using seq.last_ind.
    - cbn. lia.
    - cbn.
      rewrite seq.foldl_rcons.
      rewrite sum_list_with_rcons.
      lia.
  Qed.

  Lemma notin_seq_S start n i :
    i ∉ seq start n /\ i <> start + n
    <-> i ∉ seq start (S n).
  Proof.
    rewrite seq_S.
    set_solver.
  Qed.

  Lemma length_split {A:Type} (ls:list A) (a b:nat) :
    length ls = a + b -> ∃ ls1 ls2, ls = ls1 ++ ls2 /\ length ls1 = a /\ length ls2 = b.
  Proof.
    intros Hlen.
    exists (take a ls), (drop a ls).
    split; [by rewrite take_drop |].
    split.
    - rewrite length_take. lia.
    - rewrite length_drop. lia.
  Qed.

  Lemma len_ser32 ns :
    (length (flat_map datatypes.serialise_i32 ns) = 4 * length ns)%nat.
  Proof.
    induction ns.
    - done.
    - cbn.
      rewrite length_app.
      setoid_rewrite IHns.
      unfold datatypes.serialise_i32.
      rewrite Memdata.encode_int_length.
      cbn.
      lia.
  Qed.

  Lemma Forall_mapM_map_ext {A B:Type} (f g:A → option B) h (l: list A) :
    Forall (λ x, f x = g (h x)) l -> mapM f l = mapM g (map h l).
  Proof.
    revert l.
    induction l.
    - by cbn.
    - intros.
      apply Forall_cons_1 in H as [ha Hl].
      apply IHl in Hl.
      cbn.
      rewrite ha.
      rewrite Hl. done.
  Qed.
