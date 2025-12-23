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

Hint Unfold ok_term : core.


(* No matter how type_checker_res changes, this MUST stay the same *)
Definition check_ok {In} (func: In -> type_checker_res) (i: In) : bool :=
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
Lemma check_ok_true_to_prop {In} (func: In -> type_checker_res) (i:In) :
  check_ok func i = true -> func i = ok_term.
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
Lemma equal_okterm_to_checkok {In} (func: In -> type_checker_res) (Pbool : In -> Prop) :
  forall i:In,
    ((func i = ok_term -> Pbool i) ->
     (check_ok func i = true -> Pbool i)).
Proof.
  intros. apply H.
  by apply check_ok_true_to_prop.
Qed.

(* A few tactics *)
Ltac solve_Forall_foldr HForall Hfoldr checker proper :=
  apply (Forall_impl _ (λ x, check_ok checker x = true -> proper x)) in HForall;
  [ eapply Forall_foldr_bool_to_prop; [apply HForall | apply Hfoldr] |
    ( (by apply equal_okterm_to_checkok) ||
      (intros; eapply equal_okterm_to_checkok; [ | eassumption ]; auto)) ].

Ltac destruct_on_if_equal resname :=
  match goal with
    | H:((if ?key then _ else _)=_) |- _ => destruct key eqn:resname
  end
.



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
      if (foldr (λ i:representation, andb (check_ok (rep_ok_checker k) i)) true ρs)
           then ok_term else INR "rep_ok error"
  | SumR ρs =>
       if (foldr (λ i:representation, andb (check_ok (rep_ok_checker k) i)) true ρs)
           then ok_term else INR "rep_ok error"
 end.

Lemma rep_ok_checker_correct (k:kind_ctx) (rep:representation) :
  (rep_ok_checker k rep = ok_term) -> rep_ok k rep.
Proof.
  intros.
  induction rep using rep_ind; simpl in H.
  - apply OKVarR.
    destruct_on_if_equal H'; [apply Nat.ltb_lt in H'; auto | inversion H].
  - apply OKSumR.
    destruct_on_if_equal Hfoldr; [solve_Forall_foldr H0 Hfoldr (rep_ok_checker k) (rep_ok k) | inversion H].
  - apply OKProdR.
    destruct_on_if_equal Hfoldr; [solve_Forall_foldr H0 Hfoldr (rep_ok_checker k) (rep_ok k) | inversion H].
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
      if (foldr (λ i:size, andb (check_ok (size_ok_checker k) i)) true σs)
           then ok_term else INR "size_ok error"
  | ProdS σs =>
      if (foldr (λ i:size, andb (check_ok (size_ok_checker k) i)) true σs)
           then ok_term else INR "size_ok error"
  end.

Lemma size_ok_checker_correct (k:kind_ctx) (s:size) :
  (size_ok_checker k s = ok_term) -> size_ok k s.
Proof.
  intros.
  induction s using size_ind; simpl in H.
  - apply OKVarS.
    destruct_on_if_equal H'; [apply Nat.ltb_lt in H'; auto | inversion H].
  - apply OKSumS.
    destruct_on_if_equal Hfoldr; [solve_Forall_foldr H0 Hfoldr (size_ok_checker k) (size_ok k) | inversion H].
  - apply OKProdS.
    destruct_on_if_equal Hfoldr; [solve_Forall_foldr H0 Hfoldr (size_ok_checker k) (size_ok k) | inversion H].
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


(* type_ok *)
Fixpoint type_ok_checker (F:function_ctx) (t:type) : type_checker_res :=
  match t with
  | VarT t => match (F.(fc_type_vars) !! t) with
              | Some κ => kind_ok_checker (F.(fc_kind_ctx)) κ
              | None => INR "type ok error"
              end
  | I31T κ => kind_ok_checker (F.(fc_kind_ctx)) κ
  | NumT κ ν => kind_ok_checker (F.(fc_kind_ctx)) κ
  | SumT κ τs | VariantT κ τs | ProdT κ τs | StructT κ τs
    => match (kind_ok_checker (F.(fc_kind_ctx)) κ) with
       | inl ()  =>
           if (foldr (λ t:type, andb (check_ok (type_ok_checker F) t)) true τs)
           then ok_term else INR "type ok error"
       | err => err
       end
  | RefT κ μ τ =>
      match (kind_ok_checker (F.(fc_kind_ctx)) κ) with
      | inl () =>
          match (mem_ok_checker (F.(fc_kind_ctx)) μ) with
          | inl () => type_ok_checker F τ
          | err => err
          end
      | err => err
      end
  | CodeRefT κ ft =>
      match (kind_ok_checker (F.(fc_kind_ctx)) κ) with
      | inl () => function_type_ok_checker F ft
      | err => err
      end
  | SerT κ τ =>
      match (kind_ok_checker (F.(fc_kind_ctx)) κ) with
      | inl () => type_ok_checker F τ
      | err => err
      end
  | PlugT κ ρ =>
      match (kind_ok_checker (F.(fc_kind_ctx)) κ) with
      | inl () => rep_ok_checker (F.(fc_kind_ctx)) ρ
      | err => err
      end
  | SpanT κ σ =>
      match (kind_ok_checker (F.(fc_kind_ctx)) κ) with
      | inl () => size_ok_checker (F.(fc_kind_ctx)) σ
      | err => err
      end
  | RecT κ τ =>
      match (kind_ok_checker (F.(fc_kind_ctx)) κ) with
      | inl () => type_ok_checker (F <| fc_type_vars ::= cons κ |>) τ
      | err => err
      end
  | ExistsMemT κ τ =>
      match (kind_ok_checker (F.(fc_kind_ctx)) κ) with
      | inl () => type_ok_checker (F <| fc_kind_ctx ::= set kc_mem_vars S |>) τ
      | err => err
      end
  | ExistsRepT κ τ =>
      match (kind_ok_checker (F.(fc_kind_ctx)) κ) with
      | inl () => type_ok_checker (F <| fc_kind_ctx ::= set kc_rep_vars S |>) τ
      | err => err
      end
  | ExistsSizeT κ τ =>
      match (kind_ok_checker (F.(fc_kind_ctx)) κ) with
      | inl () => type_ok_checker (F <| fc_kind_ctx ::= set kc_size_vars S |>) τ
      | err => err
      end
  | ExistsTypeT κ1 κ2 τ =>
     match (kind_ok_checker (F.(fc_kind_ctx)) κ1) with
     | inl () =>
         match (kind_ok_checker (F.(fc_kind_ctx)) κ2) with
         | inl () => type_ok_checker (F <| fc_type_vars ::= cons κ2 |>) τ
         | err => err
         end
     | err => err
     end
  end
    with function_type_ok_checker (F: function_ctx) (ft:function_type) : type_checker_res :=
      match ft with
      | MonoFunT τs1 τs2 =>
           if (foldr (λ t:type, andb (check_ok (type_ok_checker F) t)) true τs1)
           then
              if (foldr (λ t:type, andb (check_ok (type_ok_checker F) t)) true τs2)
              then ok_term
              else INR "function type ok error"
           else INR "function type ok error"
      | ForallMemT ϕ => function_type_ok_checker (F <| fc_kind_ctx ::= set kc_mem_vars S |>) ϕ
      | ForallRepT ϕ => function_type_ok_checker (F <| fc_kind_ctx ::= set kc_rep_vars S |>) ϕ
      | ForallSizeT ϕ => function_type_ok_checker (F <| fc_kind_ctx ::= set kc_size_vars S |>) ϕ
      | ForallTypeT κ ϕ =>
          match (kind_ok_checker (F.(fc_kind_ctx)) κ) with
          | inl () => function_type_ok_checker (F <| fc_type_vars ::= cons κ |>) ϕ
          | err => err
          end
      end.

Ltac destruct_match_kind_ok F κ o Hres HMatchKind :=
  destruct (kind_ok_checker (fc_kind_ctx F) κ) eqn:Hres; [ | inversion HMatchKind ];
  unfold ok in o; assert (o = tt) by (by destruct o); subst.

Ltac destruct_on_match_equal resname :=
  match goal with
  | H: ((match ?key with |_=>_ end) = _) |- _ => destruct key eqn:resname
  end.

Ltac stupid_unit o :=
  unfold ok in o; assert (HO: o = tt) by (by destruct o); subst.

Ltac destruct_match_unit Hmatch resname o :=
  destruct_on_match_equal resname; [stupid_unit o | inversion Hmatch].

Ltac my_auto :=
  match goal with
  | H: ((match ?key with |_=>_ end) = _) |- _ => destruct key eqn:?HMatch; [ | inversion H ]
  | H:((if ?key then _ else _)=_) |- _ => destruct key eqn:?HMatch; [ | inversion H ]
  | o:ok |- _ => stupid_unit o
  | H: (kind_ok_checker _ _ = inl ()) |- _ => apply kind_ok_checker_correct in H; auto
  | H: (kind_ok_checker _ _ = ok_term) |- _ => apply kind_ok_checker_correct in H; auto
  | H: (mem_ok_checker _ _ = inl ()) |- _ => apply mem_ok_checker_correct in H; auto
  | H: (mem_ok_checker _ _ = ok_term) |- _ => apply mem_ok_checker_correct in H; auto
  | H: (rep_ok_checker _ _ = inl ()) |- _ => apply rep_ok_checker_correct in H; auto
  | H: (rep_ok_checker _ _ = ok_term) |- _ => apply rep_ok_checker_correct in H; auto
  | H: (size_ok_checker _ _ = inl ()) |- _ => apply size_ok_checker_correct in H; auto
  | H: (size_ok_checker _ _ = ok_term) |- _ => apply size_ok_checker_correct in H; auto
end.

Ltac find_Forall_foldr checker prop :=
  match goal with
  | HForall: ((Forall _ _)), Hfoldr: (foldr _ _ _ = _) |- _ =>
      solve_Forall_foldr HForall Hfoldr checker prop
  end.

Lemma type_ok_checker_correct :
  (forall t F, (type_ok_checker F t = ok_term) -> type_ok F t) /\
  (forall ft F, function_type_ok_checker F ft = ok_term -> function_type_ok F ft).
Proof.

  Ltac auto_local F := repeat my_auto; try find_Forall_foldr (type_ok_checker F) (type_ok F); auto.

  apply type_and_function_ind.
  1-17, 19-22: intros; simpl in H; try simpl in H0;
    try(constructor; auto_local F). (* this solves a LOT of cases *)
  - (* The var case requires econstructor, which I didn't want to do in general *)
    auto_local F; econstructor; eassumption.
  - (* The monofun case has to be done manually bc my find_Forall_foldr isn't that smart *)
    intros; simpl in H. simpl in H1.
    repeat my_auto.
    constructor.
    + solve_Forall_foldr H HMatch (type_ok_checker F) (type_ok F); auto.
    + solve_Forall_foldr H0 HMatch0 (type_ok_checker F) (type_ok F); auto.

Qed.


(* Have to define an equality operator on representation and dropability *)
Fixpoint subkind_of_checker (κ1:kind) (κ2:kind) : type_checker_res :=
  match κ1, κ2 with
  | (VALTYPE ρ1 ImCopy δ1), (VALTYPE ρ2 ExCopy δ2) =>
      (* this true here is fake *)
      if true then ok_term else INR "not subkind"
  | _, _ => INR "no"
  end.
