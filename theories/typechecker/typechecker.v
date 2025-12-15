Require Import RecordUpdate.RecordUpdate.
From stdpp Require Import base list.
From Stdlib.Strings Require Import String.

From RichWasm Require Import layout syntax typing util.
Set Bullet Behavior "Strict Subproofs".

Definition type_error := string.
Definition ok := unit.
Definition type_checker_res := sum ok type_error.

Definition ok_term : type_checker_res := inl ().
Definition INR (s:string) : type_checker_res := inr s.



(* No matter how type_checker_res changes, this MUST stay the same *)
Definition check_ok In (func: In -> type_checker_res) (i: In) : bool :=
  match (func i) with
  | inl a => true
  | inr a => false
  end.

Definition check_ok_output (res: type_checker_res) : bool :=
  match res with
  | inl a => true
  | inr a => false
  end.

(* This is only true if ok is kept at unit. Unfortunately most of the proofs
 rely on this. *)
Lemma check_ok_true_to_prop In (func: In -> type_checker_res) (i:In) :
  check_ok In func i = true -> func i = ok_term.
Proof.
  intros. unfold ok_term.
  destruct (func i) eqn:H'.
  - unfold ok in o.
    assert (o = tt) by (by destruct o).
    subst; auto.
  - unfold check_ok in H.
    rewrite H' in H. inversion H.
Qed.
Lemma check_ok_output_true_to_prop (res: type_checker_res) :
  check_ok_output res = true -> res = ok_term.
Proof.
  intros. unfold ok_term.
  destruct (res) eqn:H'.
  - unfold ok in o.
    assert (o = tt) by (by destruct o).
    subst; auto.
  - unfold check_ok in H.
    simpl in H.
    inversion H.
Qed.

(* Helper function for converting between forall inductive hyp and foldr boolean version *)
Lemma Forall_foldr_bool_to_prop A (Pprop : A -> Prop) (Pbool : A -> bool) (l : list A) :
  (Forall (λ x:A, (Pbool x = true) -> Pprop x) l) ->
  (foldr (λ x:A, andb (Pbool x)) true l) = true ->
  Forall Pprop l.
Proof.
  intros HForall Hfoldr.
  apply Forall_fold_right.
  induction l; simpl; auto.
  - rewrite foldr_cons in Hfoldr; apply andb_prop in Hfoldr as [a_true l_true].
    apply Forall_cons_1 in HForall; destruct HForall as [a_prop l_prop].
    split; auto.
Qed.

(* Converting between _ = ok_term to check_ok = true *)
Lemma equal_okterm_to_checkok In (func: In -> type_checker_res) (Pbool : In -> Prop) :
  forall i:In,
    ((func i = ok_term -> Pbool i) ->
     (check_ok In func i = true -> Pbool i)).
Proof.
  intros. apply H.
  by apply check_ok_true_to_prop.
Qed.




(** WE BEGIN **)


(* mem_ok *)
Definition mem_ok_checker (k:kind_ctx) (mem:memory) : type_checker_res :=
  match mem with
  | BaseM cm => ok_term
  | VarM m =>
      if m <? k.(kc_mem_vars) then ok_term else INR "mem_ok error"
  end.

Lemma mem_ok_checker_correct (k:kind_ctx) (mem:memory) :
  (mem_ok_checker k mem = ok_term) -> mem_ok k mem.
Proof.
  intros.
  destruct mem.
  - apply OKVarM.
    simpl in H.
    destruct (n <? kc_mem_vars k) eqn:H'.
    + apply Nat.ltb_lt in H'. auto.
    + inversion H.
  - apply OKBaseM.
Qed.



(* rep_ok *)
Fixpoint rep_ok_checker (k:kind_ctx) (rep:representation) : type_checker_res :=
  match rep with
  | AtomR ι => ok_term
  | VarR r => if r <? k.(kc_rep_vars) then ok_term else INR "rep_ok error"
  | ProdR ρs =>
      if (foldr (λ i:representation, andb (check_ok representation (rep_ok_checker k) i)) true ρs)
           then ok_term else INR "rep_ok error"
  | SumR ρs =>
       if (foldr (λ i:representation, andb (check_ok representation (rep_ok_checker k) i)) true ρs)
           then ok_term else INR "rep_ok error"
 end.

Lemma rep_ok_checker_correct (k:kind_ctx) (rep:representation) :
  (rep_ok_checker k rep = ok_term) -> rep_ok k rep.
Proof.
  intros.
  induction rep using rep_ind.
  - apply OKVarR.
    simpl in H.
    destruct (idx <? kc_rep_vars k) eqn:H'.
    + apply Nat.ltb_lt in H'. auto.
    + inversion H.
  - apply OKSumR.
    simpl in H.
    destruct (foldr (λ i:representation, andb (check_ok representation (rep_ok_checker k) i)) true ρs) eqn:H'.
    + clear H.
      apply (Forall_impl _ (λ x, check_ok representation (rep_ok_checker k) x = true -> rep_ok k x)) in H0.
      * eapply Forall_foldr_bool_to_prop; [apply H0 | apply H'].
      * apply equal_okterm_to_checkok.
    + inversion H.
  - apply OKProdR.
    simpl in H.
    destruct (foldr (λ i:representation, andb (check_ok representation (rep_ok_checker k) i)) true ρs) eqn:H'.
    + clear H.
      apply (Forall_impl _ (λ x, check_ok representation (rep_ok_checker k) x = true -> rep_ok k x)) in H0.
      * eapply Forall_foldr_bool_to_prop; [apply H0 | apply H'].
      * apply equal_okterm_to_checkok.
    + inversion H.
  - apply OKAtomR.
Qed.



(* size_ok *)
Fixpoint size_ok_checker (k:kind_ctx) (s:size) : type_checker_res :=
  match s with
  | ConstS n => ok_term
  | VarS r => if r <? k.(kc_size_vars) then ok_term else INR "size_ok error"
  | RepS ρ => match (rep_ok_checker k ρ) with
              | inl _ => ok_term
              | err => err (* this allows propagation*)
                         (* you could also just ret rep_ok_checker. Idk which would be
                          better for future changeability. I'll do just ret later*)
              end
  | SumS σs =>
      if (foldr (λ i:size, andb (check_ok size (size_ok_checker k) i)) true σs)
           then ok_term else INR "size_ok error"
  | ProdS σs =>
      if (foldr (λ i:size, andb (check_ok size (size_ok_checker k) i)) true σs)
           then ok_term else INR "size_ok error"
  end.

Lemma size_ok_checker_correct (k:kind_ctx) (s:size) :
  (size_ok_checker k s = ok_term) -> size_ok k s.
Proof.
  intros.
  induction s using size_ind.
  - apply OKVarS.
    simpl in H.
    destruct (idx <? kc_size_vars k) eqn:H'.
    + apply Nat.ltb_lt in H'. auto.
    + inversion H.
  - apply OKSumS.
    simpl in H.
    destruct (foldr (λ i:size, andb (check_ok size (size_ok_checker k) i)) true σs) eqn:H'.
    + clear H.
      apply (Forall_impl _ (λ x, check_ok size (size_ok_checker k) x = true -> size_ok k x)) in H0.
      * eapply Forall_foldr_bool_to_prop; [apply H0 | apply H'].
      * apply equal_okterm_to_checkok.
    + inversion H.
  - apply OKProdS.
    simpl in H.
    destruct (foldr (λ i:size, andb (check_ok size (size_ok_checker k) i)) true σs) eqn:H'.
    + clear H.
      apply (Forall_impl _ (λ x, check_ok size (size_ok_checker k) x = true -> size_ok k x)) in H0.
      * eapply Forall_foldr_bool_to_prop; [apply H0 | apply H'].
      * apply equal_okterm_to_checkok.
    + inversion H.
  - apply OKRepS.
    simpl in H.
    destruct (rep_ok_checker k ρ) eqn:H'.
    + apply rep_ok_checker_correct.
      unfold ok in o.
      assert (o = tt) by (by destruct o).
      subst; auto.
    + inversion H.
  - apply OKConstS.
Qed.


(* kind_ok *)
Definition kind_ok_checker (k:kind_ctx) (ki: kind) : type_checker_res :=
  match ki with
  | (VALTYPE ρ χ δ) => rep_ok_checker k ρ
  | MEMTYPE σ δ => size_ok_checker k σ
  end.

Lemma kind_ok_checker_correct (k:kind_ctx) (ki:kind) :
  (kind_ok_checker k ki = ok_term) -> kind_ok k ki.
Proof.
  intros.
  destruct ki; simpl in H.
  - apply OKVALTYPE.
    apply rep_ok_checker_correct; auto.
  - apply OKMEMTYPE.
    apply size_ok_checker_correct; auto.
Qed.
