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

Lemma type_ok_checker_correct_basic :
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

Lemma type_ok_checker_correct :
  ∀ t F, (type_ok_checker F t = ok_term) -> type_ok F t.
Proof.
  apply type_ok_checker_correct_basic.
Qed.

Lemma function_type_ok_checker_correct :
  ∀ ft F, function_type_ok_checker F ft = ok_term -> function_type_ok F ft.
Proof.
  apply type_ok_checker_correct_basic.
Qed.

Scheme Equality for copyability.
Scheme Equality for dropability.
Scheme Equality for atomic_rep.
Scheme Equality for base_memory.
Scheme Equality for memory.

Scheme Equality for list.


Fixpoint representation_beq (r1:representation) (r2:representation) : bool :=
  match r1, r2 with
  | VarR i1, VarR i2 => (i1 =? i2)
  | SumR r1s, SumR r2s => list_beq representation representation_beq r1s r2s
  | ProdR r1s, ProdR r2s => list_beq representation representation_beq r1s r2s
  | AtomR a1, AtomR a2 => atomic_rep_beq a1 a2
  | _, _ => false
  end.

Lemma representation_eq_convert :
  ∀ r1 r2, representation_beq r1 r2 = true <-> r1 = r2.
Proof.
  split; intros.
  - induction r1 using rep_ind; induction r2 using rep_ind; simpl in H; try inversion H.
    * apply Nat.eqb_eq in H; by subst.
    * (* okay this is doable, but not worth it rn *)
      admit.
    * admit.
    * (* doable almost certainly *) admit.
  - subst.
    induction r2 using rep_ind.
    * simpl. by apply Nat.eqb_eq.
    * simpl. (* it gotta be but not worth it rn honestly *)
Admitted.

Fixpoint size_beq (s1:size) (s2:size) : bool :=
  match s1, s2 with
  | VarS i1, VarS i2 => (i1 =? i2)
  | SumS s1s, SumS s2s => list_beq size size_beq s1s s2s
  | ProdS s1s, ProdS s2s => list_beq size size_beq s1s s2s
  | RepS r1, RepS r2 => representation_beq r1 r2
  | ConstS n1, ConstS n2 => (n1 =? n2)
  | _, _ => false
  end.

Lemma size_eq_convert :
  ∀ s1 s2, size_beq s1 s2 = true <-> s1 = s2.
Proof.
Admitted.

Fixpoint kind_beq (k1:kind) (k2:kind) : bool :=
  match k1, k2 with
  | VALTYPE r1 c1 d1, VALTYPE r2 c2 d2 =>
      andb (representation_beq r1 r2) (andb (copyability_beq c1 c2) (dropability_beq d1 d2))
  | MEMTYPE s1 d1, MEMTYPE s2 d2 =>
      andb (size_beq s1 s2) (dropability_beq d1 d2)
  | _, _ => false
  end.

Lemma kind_eq_convert :
  ∀ k1 k2, kind_beq k1 k2 = true <-> k1 = k2.
Proof. Admitted.

Lemma kind_neq_convert :
  ∀ k1 k2, kind_beq k1 k2 = false <-> k1 <> k2.
Proof.
  split; intros.
  (* there's some decidability lemmas that need to be done. This is fine to leave. *)
Admitted.


Definition mono_mem_checker (μ:memory) : type_checker_res :=
  match μ with
  | BaseM bm => ok_term
  | _ => INR "not monomem"
  end.

(* This is using the above custom representation and size *)
Definition subkind_of_checker (κ1:kind) (κ2:kind) : type_checker_res :=
  match κ1, κ2 with
  | (VALTYPE ρ1 ImCopy δ1), (VALTYPE ρ2 ExCopy δ2) =>
      if andb (representation_beq ρ1 ρ2) (dropability_beq δ1 δ2)
      then ok_term else INR "fail in subkind check"
  | (VALTYPE ρ1 ExCopy δ1), (VALTYPE ρ2 NoCopy δ2) =>
      if andb (representation_beq ρ1 ρ2) (dropability_beq δ1 δ2)
      then ok_term else INR "fail in subkind check"
  | (VALTYPE ρ1 χ1 ImDrop), (VALTYPE ρ2 χ2 ExDrop) =>
      if andb (representation_beq ρ1 ρ2) (copyability_beq χ1 χ2)
      then ok_term else INR "fail in subkind check"
  | (MEMTYPE σ1 ImDrop), (MEMTYPE σ2 ExDrop) =>
      if size_beq σ1 σ2
      then ok_term else INR "fail in subkind check"
  | _, _ => INR "no"
  end.


Lemma dropability_eq_convert :
  ∀ d1 d2, dropability_beq d1 d2 = true <-> d1 = d2.
Proof.
  split; intros.
  - by apply internal_dropability_dec_bl in H.
  - by apply internal_dropability_dec_lb in H.
Qed.

Lemma copyability_eq_convert :
  ∀ c1 c2, copyability_beq c1 c2 = true <-> c1 = c2.
Proof.
  split; intros;
    [by apply internal_copyability_dec_bl in H | by apply internal_copyability_dec_lb in H].
Qed.

Lemma memory_eq_convert :
  ∀ m1 m2, memory_beq m1 m2 = true <-> m1 = m2.
Proof. Admitted.


Ltac my_auto2 :=
  match goal with
  | H: ((match ?key with |_=>_ end) = _) |- _ => destruct key eqn:?HMatch; [ | inversion H ]; simpl in *
  | H: ((match ?key with |_=>_ end) = _) |- _ => destruct key eqn:?HMatch; [ inversion H | ]; simpl in *
  | H:((if ?key then _ else _)=_) |- _ => destruct key eqn:?HMatch; [ | inversion H ]
  | o:ok |- _ => stupid_unit o
  | H: ok_term = ok_term |- _ => clear H
  | H: (andb _ _ = true) |- _ => apply andb_prop in H; destruct H as [?H1 ?H2]
  | H: (_ && _ = true) |- _ => apply andb_prop in H; destruct H as [?H1 ?H2]
  | H: true = false |- _ => inversion H
  | H: false = true |- _ => inversion H
  | H: (representation_beq _ _ = true) |- _ => apply representation_eq_convert in H; subst; auto
  | H: (dropability_beq _ _ = true) |- _ => apply dropability_eq_convert in H; subst; auto
  | H: (copyability_beq _ _ = true) |- _ => apply copyability_eq_convert in H; subst; auto
  | H: (size_beq _ _ = true) |- _ => apply size_eq_convert in H; subst; auto
  | H: (kind_ok_checker _ _ = inl ()) |- _ => apply kind_ok_checker_correct in H; auto
  | H: (kind_ok_checker _ _ = ok_term) |- _ => apply kind_ok_checker_correct in H; auto
  | H: (mem_ok_checker _ _ = inl ()) |- _ => apply mem_ok_checker_correct in H; auto
  | H: (mem_ok_checker _ _ = ok_term) |- _ => apply mem_ok_checker_correct in H; auto
  | H: (rep_ok_checker _ _ = inl ()) |- _ => apply rep_ok_checker_correct in H; auto
  | H: (rep_ok_checker _ _ = ok_term) |- _ => apply rep_ok_checker_correct in H; auto
  | H: (size_ok_checker _ _ = inl ()) |- _ => apply size_ok_checker_correct in H; auto
  | H: (size_ok_checker _ _ = ok_term) |- _ => apply size_ok_checker_correct in H; auto
  | H: (type_ok_checker _ _ = inl ()) |- _ => apply type_ok_checker_correct in H; auto
  | H: (type_ok_checker _ _ = ok_term) |- _ => apply type_ok_checker_correct in H; auto
  | H: (function_type_ok_checker _ _ = inl ()) |- _ => apply function_type_ok_checker_correct in H; auto
  | H: (function_type_ok_checker _ _ = ok_term) |- _ => apply function_type_ok_checker_correct in H; auto
end.


Lemma subkind_of_checker_correct :
  ∀ k1 k2, subkind_of_checker k1 k2 = ok_term -> subkind_of k1 k2.
Proof.
  intros.
  destruct k1, k2;
    try destruct c, c0; try destruct d, d0; simpl in H; try inversion H;
    repeat my_auto2;
    try apply KSubValExCopy; try apply KSubValNoCopy; try apply KSubValExDrop; try apply KSubMemExDrop;
    repeat my_auto2.
  1-4: destruct c; simpl in *; inversion H.
Qed.

Definition has_kind_ok_checker (F:function_ctx) (t:type) (k:kind) : type_checker_res :=
  match (type_ok_checker F t) with
  | inl () => (kind_ok_checker (F.(fc_kind_ctx)) k)
  | err => err
  end.

Lemma has_kind_ok_checker_correct :
  ∀ F t k, has_kind_ok_checker F t k = ok_term -> has_kind_ok F t k.
Proof.
  intros. unfold has_kind_ok_checker in H. repeat my_auto2.
  constructor; auto.
Qed.



(* Time for has-kind oh boy oh boy *)


(* This function just grabs the kind out of the type *)
Definition grab_kind (F:function_ctx) (t:type) : option kind :=
  match t with
  | I31T k => Some k
  | NumT k _ => Some k
  | SumT k _ => Some k
  | VariantT k _ => Some k
  | ProdT k _ => Some k
  | StructT k _ => Some k
  | RefT k _ _ => Some k
  | CodeRefT k _ => Some k
  | SerT k _ => Some k
  | PlugT k _ => Some k
  | SpanT k _ => Some k
  | RecT k _ => Some k
  | ExistsMemT k _ => Some k
  | ExistsRepT k _ => Some k
  | ExistsSizeT k _ => Some k
  | ExistsTypeT k _ _ => Some k
  | VarT t => (F.(fc_type_vars)) !! t
  end.


(* A thing that helps with subkinding *)
Definition check_if_subkind (k1:kind) (k2:kind) : type_checker_res :=
  match k1, k2 with
  | VALTYPE ρ1 χ1 δ1, VALTYPE ρ2 χ2 δ2 =>
      if representation_beq ρ1 ρ2
      then
        match χ1, χ2 with
        | ImCopy, _
        | ExCopy, ExCopy
        | ExCopy, NoCopy
        | NoCopy, NoCopy =>
            match δ1, δ2 with
            | ImDrop, _
            | ExDrop, ExDrop => ok_term
            | _, _ => INR "not subkind"
            end
        | _, _ => INR "not subkind"
        end
      else INR "mismatch in representation for subkinds"
  | MEMTYPE σ1 δ1, MEMTYPE σ2 δ2 =>
      if size_beq σ1 σ2
      then
        match δ1, δ2 with
        | ImDrop, _
        | ExDrop, ExDrop => ok_term
        | _, _ => INR "not subkind"
        end
      else INR "mismatch in sizity for subkinds"
  | _, _ => INR "mismatch in general kind for subkind"
  end.

Lemma check_if_subkind_works_with_has_kind :
  ∀ F τ k1 k2,
    check_if_subkind k1 k2 = ok_term ->
    has_kind F τ k1 ->
    has_kind F τ k2.
Proof.
  intros.
  destruct k1, k2; simpl in H; inversion H.
  - repeat my_auto2. rename r0 into r.
    destruct c, c0, d, d0; simpl in *; auto; repeat my_auto2; try inversion H.
    (* Look I know this probably should be ltacable but I couldn't be bothered *)
    + apply (KSub _ _ (VALTYPE r NoCopy ImDrop) _); try constructor; auto.
    + apply (KSub _ _ (VALTYPE r ExCopy ExDrop) _); try constructor; auto.
    + apply (KSub _ _ (VALTYPE r ExCopy ExDrop) _); try constructor; auto.
      apply (KSub _ _ (VALTYPE r ExCopy ImDrop) _); try constructor; auto.
    + apply (KSub _ _ (VALTYPE r ExCopy ImDrop) _); try constructor; auto.
    + apply (KSub _ _ (VALTYPE r ExCopy ImDrop) _); try constructor; auto.
    + apply (KSub _ _ (VALTYPE r ExCopy ExDrop) _); try constructor; auto.
      apply (KSub _ _ (VALTYPE r ImCopy ExDrop) _); try constructor; auto.
    + apply (KSub _ _ (VALTYPE r ExCopy ExDrop) _); try constructor; auto.
      apply (KSub _ _ (VALTYPE r ExCopy ImDrop) _); try constructor; auto.
      apply (KSub _ _ (VALTYPE r ImCopy ImDrop) _); try constructor; auto.
    + apply (KSub _ _ (VALTYPE r ExCopy ImDrop) _); try constructor; auto.
      apply (KSub _ _ (VALTYPE r ImCopy ImDrop) _); try constructor; auto.
    + apply (KSub _ _ (VALTYPE r ImCopy ExDrop) _); try constructor; auto.
    + apply (KSub _ _ (VALTYPE r ExCopy ImDrop) _); try constructor; auto.
      apply (KSub _ _ (VALTYPE r ImCopy ImDrop) _); try constructor; auto.
    + apply (KSub _ _ (VALTYPE r ImCopy ImDrop) _); try constructor; auto.
    + apply (KSub _ _ (VALTYPE r ImCopy ImDrop) _); try constructor; auto.
  - repeat my_auto2.
    destruct d0; auto.
    apply (KSub _ _ (MEMTYPE s0 ImDrop) _); try constructor; auto.
Qed.



Fixpoint foldr2 {A B C : Type} (f : B → C → A → A) (a0 : A)
  (lB : list B) (lC : list C) :=
  match lB, lC with
  | b :: lB0, c :: lC0 => f b c (foldr2 f a0 lB0 lC0)
  | _, _ => a0
  end.


(* Check kind in a naive way. I guess. *)
Fixpoint has_kind_checker (F:function_ctx) (t:type) (k:kind) : type_checker_res :=
  match t with
  | VarT t =>
      match (F.(fc_type_vars)) !! t with
      | Some κ =>
          match kind_ok_checker (F.(fc_kind_ctx)) κ with
          | inl () => check_if_subkind κ k
          | err => err
          end
      | None => INR "variable not in there or smthn"
      end
  (* Numbers *)
  | I31T κ =>
      if (kind_beq κ (VALTYPE (AtomR PtrR) ImCopy ImDrop))
      then check_if_subkind κ k
      else INR "wrong kind for I31T"
    (* NumT *)
  | NumT κ (IntT I32T) =>
      if (kind_beq κ (VALTYPE (AtomR I32R) ImCopy ImDrop))
      then check_if_subkind κ k
      else INR "wrong kind for I32T"
  | NumT κ (IntT I64T) =>
      if (kind_beq κ (VALTYPE (AtomR I64R) ImCopy ImDrop) )
      then check_if_subkind κ k
      else INR "wrong kind for I64T"
  | NumT κ (FloatT F32T) =>
      if (kind_beq κ (VALTYPE (AtomR F32R) ImCopy ImDrop))
      then check_if_subkind κ k
      else INR "wrong kind for F32T"
  | NumT κ (FloatT F64T) =>
      if (kind_beq κ (VALTYPE (AtomR F64R) ImCopy ImDrop))
      then check_if_subkind κ k
      else INR "wrong kind for F64T"
  (* Sums and Prods *)
  | SumT κ τs =>
      match κ with
      | VALTYPE (SumR ρs) χ δ =>
          if foldr2
               (λ t:type, λ r:representation,
                  andb (check_ok_output (has_kind_checker F t (VALTYPE r χ δ)))
               ) true τs ρs
          then check_if_subkind κ k
          else INR "bad sum kind internals"
      | _ => INR "bad sum kind format"
      end
  | VariantT κ τs =>
      match κ with
      | MEMTYPE (SumS σs) δ =>
          if foldr2
               (λ t:type, λ s:size,
                  andb (check_ok_output (has_kind_checker F t (MEMTYPE s δ)))
               ) true τs σs
          then check_if_subkind κ k
          else INR "bad sum kind internals"
      | _ => INR "bad variant kind format"
      end
   | ProdT κ τs =>
      match κ with
      | VALTYPE (ProdR ρs) χ δ =>
          if foldr2
               (λ t:type, λ r:representation,
                  andb (check_ok_output (has_kind_checker F t (VALTYPE r χ δ)))
               ) true τs ρs
          then check_if_subkind κ k
          else INR "bad sum kind internals"
      | _ => INR "bad prod kind format"
      end
  | StructT κ τs =>
      match κ with
      | MEMTYPE (ProdS σs) δ =>
          if foldr2
               (λ t:type, λ s:size,
                  andb (check_ok_output (has_kind_checker F t (MEMTYPE s δ)))
               ) true τs σs
          then check_if_subkind κ k
          else INR "bad sum kind internals"
      | _ => INR "bad struct kind format"
      end
  (* References *)
  | RefT κ (BaseM MemGC) τ =>
      if (kind_beq κ (VALTYPE (AtomR PtrR) ExCopy ExDrop))
      then
        match grab_kind F τ with
          | Some innerk =>
              match innerk with
              | MEMTYPE σ δ =>
                  match has_kind_checker F τ (MEMTYPE σ δ) with
                  | inl () => check_if_subkind κ k
                  | err => err
                  end
              | _ => INR "you have a reft t where t isnt memtype"
              end
          | None => INR "i think you have a bad variable or smthn"
          end
      else INR "bad gc mem kind format"
  | RefT κ μ τ =>
      if (kind_beq κ (VALTYPE (AtomR PtrR) NoCopy ExDrop))
      then
        match mem_ok_checker (F.(fc_kind_ctx)) μ with
          | inl () =>
              match grab_kind F τ with
              | Some innerk =>
                  match innerk with
                  | MEMTYPE σ δ =>
                      match has_kind_checker F τ (MEMTYPE σ δ) with
                      | inl () => check_if_subkind κ k
                      | err => err
                      end
                  | _ => INR "you have ref t where t isnt memtype"
                  end
              | None => INR "i think you have a bad variable or smthn"
              end
          | err => err
          end
      else INR "bad ref kind format"
  | CodeRefT κ ϕ =>
      match κ with
      | VALTYPE (AtomR I32R) ImCopy ImDrop =>
          match function_type_ok_checker F ϕ with
          | inl () => check_if_subkind κ k
          | err => err
          end
      | _ => INR "bad coderef kind format"
      end
  (* Some weird ones I guess *)
  | SerT κ τ =>
      match κ with
      | MEMTYPE (RepS ρ) δ =>
          match has_kind_checker F τ (VALTYPE ρ ImCopy δ) with
          | inl () => check_if_subkind κ k
          | err => err
          end
      | _ => INR "bad ser kind format"
      end
  | PlugT κ ρ =>
      match κ with
      | VALTYPE ρ1 ImCopy ImDrop =>
          if representation_beq ρ ρ1
          then
            match rep_ok_checker (F.(fc_kind_ctx)) ρ with
            | inl () => check_if_subkind κ k
            | err => err
            end
          else INR "plug's rep doesn't match kind's rep"
      | _ => INR "bad plug kind format"
      end
  | SpanT κ σ =>
      match κ with
      | MEMTYPE σ1 ImDrop =>
          if size_beq σ σ1
          then
            match size_ok_checker (F.(fc_kind_ctx)) σ with
            | inl () => check_if_subkind κ k
            | err => err
            end
          else INR "span's size doesn't match kind's size"
      | _ => INR "bad span kind format"
      end
  | RecT κ τ =>
      match has_kind_checker (F <| fc_type_vars ::= cons κ |>) τ κ with
      | inl () => check_if_subkind κ k
      | err => err
      end
  | ExistsMemT κ τ =>
      match kind_ok_checker (F.(fc_kind_ctx)) κ with
      | inl () =>
          match has_kind_checker (F <| fc_kind_ctx ::= set kc_mem_vars S |>) τ κ with
          | inl () => check_if_subkind κ k
          | err => err
          end
      | err => err
      end
  | ExistsRepT κ τ =>
      match kind_ok_checker (F.(fc_kind_ctx)) κ with
      | inl () =>
          match has_kind_checker (F <| fc_kind_ctx ::= set kc_rep_vars S |>) τ κ with
          | inl () => check_if_subkind κ k
          | err => err
          end
      | err => err
      end
   | ExistsSizeT κ τ =>
      match kind_ok_checker (F.(fc_kind_ctx)) κ with
      | inl () =>
          match has_kind_checker (F <| fc_kind_ctx ::= set kc_size_vars S |>) τ κ with
          | inl () => check_if_subkind κ k
          | err => err
          end
      | err => err
      end
  | ExistsTypeT κ κ0 τ =>
      match kind_ok_checker (F.(fc_kind_ctx)) κ with
      | inl () =>
          match kind_ok_checker (F.(fc_kind_ctx)) κ0 with
          | inl () =>
              match has_kind_checker (F <| fc_type_vars ::= cons κ0 |>) τ κ with
              | inl () => check_if_subkind κ k
              | err => err
              end
          | err => err
          end
      | err => err
      end
  end.

Ltac my_auto3 :=
  match goal with
  | H: ((match ?key with |_=>_ end) = _) |- _ => destruct key eqn:?HMatch; try inversion H; simpl in *
  | H:((if ?key then _ else _)=_) |- _ => destruct key eqn:?HMatch; try inversion H; simpl in *
  | H: (kind_beq _ _ = true) |- _ => apply kind_eq_convert in H; subst; auto
  | o:ok |- _ => stupid_unit o
  | H: ok_term = ok_term |- _ => clear H
  | H: (andb _ _ = true) |- _ => apply andb_prop in H; destruct H as [?H1 ?H2]
  | H: (_ && _ = true) |- _ => apply andb_prop in H; destruct H as [?H1 ?H2]
  | H: true = false |- _ => inversion H
  | H: false = true |- _ => inversion H
  | H: (representation_beq _ _ = true) |- _ => apply representation_eq_convert in H; subst; auto
  | H: (dropability_beq _ _ = true) |- _ => apply dropability_eq_convert in H; subst; auto
  | H: (copyability_beq _ _ = true) |- _ => apply copyability_eq_convert in H; subst; auto
  | H: (size_beq _ _ = true) |- _ => apply size_eq_convert in H; subst; auto
  | H: (kind_ok_checker _ _ = inl ()) |- _ => apply kind_ok_checker_correct in H; auto
  | H: (kind_ok_checker _ _ = ok_term) |- _ => apply kind_ok_checker_correct in H; auto
  | H: (mem_ok_checker _ _ = inl ()) |- _ => apply mem_ok_checker_correct in H; auto
  | H: (mem_ok_checker _ _ = ok_term) |- _ => apply mem_ok_checker_correct in H; auto
  | H: (rep_ok_checker _ _ = inl ()) |- _ => apply rep_ok_checker_correct in H; auto
  | H: (rep_ok_checker _ _ = ok_term) |- _ => apply rep_ok_checker_correct in H; auto
  | H: (size_ok_checker _ _ = inl ()) |- _ => apply size_ok_checker_correct in H; auto
  | H: (size_ok_checker _ _ = ok_term) |- _ => apply size_ok_checker_correct in H; auto
  | H: (type_ok_checker _ _ = inl ()) |- _ => apply type_ok_checker_correct in H; auto
  | H: (type_ok_checker _ _ = ok_term) |- _ => apply type_ok_checker_correct in H; auto
  | H: (function_type_ok_checker _ _ = inl ()) |- _ => apply function_type_ok_checker_correct in H; auto
  | H: (function_type_ok_checker _ _ = ok_term) |- _ => apply function_type_ok_checker_correct in H; auto
  | H: (check_if_subkind _ _ = inl ()) |- _ =>
      try( by (eapply check_if_subkind_works_with_has_kind; try constructor; auto))
  | H: (check_if_subkind _ _ = ok_term) |- _ =>
      try( by (eapply check_if_subkind_works_with_has_kind; try constructor; auto))
  | H: (INR _ = ok_term) |- _ => inversion H
  | H: (INR _ = inl ()) |- _ => inversion H
end.

Opaque check_if_subkind.
Opaque mem_ok_checker.
(* this needs to not be unravelled by any tactics. Makes
 automation a lot easier *)


(* The stupid True is there bc idk how to make the induction work otherwise *)
Lemma has_kind_checker_correct_basic :
  (∀ t F k, has_kind_checker F t k = ok_term -> has_kind F t k) /\
  (∀ (ft:function_type) (F:function_ctx), True  ).
Proof.
  apply type_and_function_ind; intros; simpl in *; auto; repeat my_auto3.
  (* The following 4 (sums and prods) will rely on some foldr2 lemma *)
  (* I will do that later *)
  1-4: admit.

  (* then these actually need the simple inductive hyp *)
  1-4: match goal with
    | HSTAR: (has_kind_checker _ _ _ = _) |- _ => apply H in HSTAR
    end.
  1-2: eapply check_if_subkind_works_with_has_kind; [apply H0 | apply (KRef _ _ _ s d); auto].
  1: eapply check_if_subkind_works_with_has_kind; [apply H0 | apply (KRefGC _ _ s d); auto].

  (* Just ser *)
  eapply check_if_subkind_works_with_has_kind; [apply H0 | eapply KSer; apply HMatch1 ].

Admitted.

Lemma has_kind_checker_correct :
  ∀ F t k, has_kind_checker F t k = ok_term -> has_kind F t k.
Proof.
  pose proof has_kind_checker_correct_basic.
  destruct H; auto.
Qed.


(* Small things before pathing *)
Definition has_rep_checker F τ ρ : type_checker_res :=
  has_kind_checker F τ (VALTYPE ρ ImCopy ImDrop).

Lemma has_rep_checker_correct :
  ∀ F τ ρ, has_rep_checker F τ ρ = ok_term -> has_rep F τ ρ.
Proof.
  intros.
  unfold has_rep_checker in H.
  apply has_kind_checker_correct in H.
  apply (RepVALTYPE _ _ _ ImCopy ImDrop); auto.
Qed.

Definition grab_rep F τ : option representation :=
  match grab_kind F τ with
  | Some κ =>
      match κ with
      | VALTYPE ρ _ _ => Some ρ
      | _ => None
      end
  | None => None
  end.

Definition is_mono_rep_checker :=
  rep_ok_checker kc_empty.

Definition has_mono_rep_checker F τ : type_checker_res :=
  match grab_rep F τ with
  | Some ρ =>
      match has_rep_checker F τ ρ with
      | inl () => is_mono_rep_checker ρ
      | err => err
      end
  | None => INR "youre checking mono rep for something that is not valtype or smthn similar"
  end.

Lemma has_mono_rep_checker_correct :
  ∀ F τ, has_mono_rep_checker F τ = ok_term -> has_mono_rep F τ.
Proof.
  intros. unfold has_mono_rep_checker in H.
  repeat my_auto3.
  unfold is_mono_rep_checker in *.
  repeat my_auto3.
  apply has_rep_checker_correct in HMatch0.
  apply (MonoRep _ _ r); auto.
Qed.

Definition has_mono_rep_instr_checker F inst : type_checker_res :=
  match inst with
  | InstrT τs1 τs2 =>
      if (foldr (λ t:type, andb (check_ok (has_mono_rep_checker F) t)) true τs1)
      then
        if (foldr (λ t:type, andb (check_ok (has_mono_rep_checker F) t)) true τs2)
        then ok_term
        else INR "function type ok error"
      else INR "function type ok error"
  end.

Lemma has_mono_rep_instr_checker_correct :
  ∀ F inst, has_mono_rep_instr_checker F inst = ok_term -> has_mono_rep_instr F inst.
Proof.
  intros.
  unfold has_mono_rep_instr_checker in *.
  repeat my_auto3. pose proof has_mono_rep_checker_correct.
  split; [clear HMatch1 | clear HMatch0].
  - (* yeah this is true but I dont wanna prove it *)
    admit.
  - admit.
Admitted.

Definition grab_size F τ : option size :=
  match grab_kind F τ with
  | Some κ =>
      match κ with
      | MEMTYPE σ _ => Some σ
      | _ => None
      end
  | None => None
  end.

Definition has_size_checker F τ σ : type_checker_res :=
  has_kind_checker F τ (MEMTYPE σ ImDrop).

Lemma has_size_checker_correct :
  ∀ F τ σ, has_size_checker F τ σ = ok_term -> has_size F τ σ.
Proof.
  intros. unfold has_size_checker in H.
  apply has_kind_checker_correct in H.
  unfold has_size.
  by exists ImDrop.
Qed.

Definition is_mono_size_checker := size_ok_checker kc_empty.

Definition has_mono_size_checker F τ : type_checker_res :=
  match grab_size F τ with
  | Some σ =>
      match has_size_checker F τ σ with
      | inl () => is_mono_size_checker σ
      | err => err
      end
  | None => INR "youre checking mono size for something that is not memtype or smthn similar"
  end.

Lemma has_mono_size_checker_correct :
  ∀ F τ, has_mono_size_checker F τ = ok_term -> has_mono_size F τ.
Proof.
  intros.
  unfold has_mono_size_checker in *.
  repeat my_auto3.
  unfold is_mono_size_checker in *. unfold has_size_checker in *.
  repeat my_auto3. apply has_kind_checker_correct in HMatch0.
  by apply (MonoSizeMEMTYPE _ _ s ImDrop).
Qed.

Scheme Equality for primitive.

Definition type_rep_eq_prim_checker F τ ηs : type_checker_res :=
  match grab_rep F τ with
  | Some ρ =>
      match has_rep_checker F τ ρ with
      | inl () =>
          match eval_rep_prim EmptyEnv ρ with
          | Some ηs1 =>
              if list_beq primitive primitive_beq ηs ηs1
              then ok_term
              else INR "uh primitives don't match?"
          | None => INR "bad rep i think"
          end
      | err => err
      end
  | None => INR "um not valtype?"
  end.

Lemma type_rep_eq_prim_checker_correct :
  ∀ F τ ηs, type_rep_eq_prim_checker F τ ηs = ok_term -> type_rep_eq_prim F τ ηs.
Proof.
  intros.
  unfold type_rep_eq_prim_checker in H.
  repeat my_auto3.
  apply has_rep_checker_correct in HMatch0. rename l into ηs1.
  exists r. split; auto.
  (* give some theorems about list_beq, this is obvious *)
  admit.
Admitted.

(* NOTE: not a bit of confusing terminology. size_beq is actual equality.
 size_eq_checker will be about it evalling to the same n *)

Definition size_eq_checker σ1 σ2 : type_checker_res :=
  match eval_size EmptyEnv σ1 with
  | Some n1 =>
      match eval_size EmptyEnv σ2 with
      | Some n2 =>
          if n1 =? n2
          then ok_term
          else INR "unequal sizes"
      | None => INR "bad size"
      end
  | None => INR "bad size"
  end.

Lemma size_eq_checker_correct :
  ∀ σ1 σ2, size_eq_checker σ1 σ2 = ok_term -> size_eq σ1 σ2.
Proof.
  intros. unfold size_eq_checker in *.
  repeat my_auto3.
  apply Nat.eqb_eq in HMatch1; subst.
  econstructor; [apply HMatch | apply HMatch0].
Qed.

Definition size_leq_checker σ1 σ2 : type_checker_res :=
  match eval_size EmptyEnv σ1 with
  | Some n1 =>
      match eval_size EmptyEnv σ2 with
      | Some n2 =>
          if n1 <? n2
          then ok_term
          else INR "unequal sizes"
      | None => INR "bad size"
      end
  | None => INR "bad size"
  end.

Lemma size_leq_checker_correct :
  ∀ σ1 σ2, size_leq_checker σ1 σ2 = ok_term -> size_leq σ1 σ2.
Proof. (* easy *) Admitted.

Definition type_size_eq_checker F τ1 τ2 : type_checker_res :=
  match grab_size F τ1 with
  | Some σ1 =>
      match grab_size F τ2 with
      | Some σ2 =>
          match has_size_checker F τ1 σ1 with
          | inl () =>
              match has_size_checker F τ2 σ2 with
              | inl () => size_eq_checker σ1 σ2
              | err => err
              end
          | err => err
          end
      | None => INR "bad type for size"
      end
  | None => INR "bad type for size"
  end.

Lemma type_size_eq_checker_correct :
  ∀ F τ1 τ2, type_size_eq_checker F τ1 τ2 = ok_term -> type_size_eq F τ1 τ2.
Proof.
  intros. unfold type_size_eq_checker in H.
  repeat my_auto3.
  apply has_size_checker_correct in HMatch1, HMatch3.
  apply size_eq_checker_correct in H.
  exists s, s0. split; auto.
Qed.

Definition grab_copyability F τ : option copyability :=
  match grab_kind F τ with
  | Some (VALTYPE _ χ _) => Some χ
  | _ => None
  end.

Definition grab_dropability F τ : option dropability :=
  match grab_kind F τ with
  | Some (VALTYPE _ _ δ) => Some δ
  | Some (MEMTYPE _ δ) => Some δ
  | None => None
  end.

Definition has_copyability_checker F τ χ : type_checker_res :=
  match grab_rep F τ with
  | Some ρ => has_kind_checker F τ (VALTYPE ρ χ ImDrop)
  | None => INR "not valtype"
  end.

Lemma has_copyability_checker_correct :
  ∀ F τ χ, has_copyability_checker F τ χ = ok_term -> has_copyability F τ χ.
Proof.
  intros; unfold has_copyability_checker in *.
  repeat my_auto3.
  apply has_kind_checker_correct in H.
  apply (CopyVALTYPE _ _ r _ ImDrop); auto.
Qed.

Definition has_dropability_checker F τ δ : type_checker_res :=
  match grab_kind F τ with
  | Some κ =>
      match κ with
      | VALTYPE ρ _ _ => has_kind_checker F τ (VALTYPE ρ ImCopy δ)
      | MEMTYPE σ _ => has_kind_checker F τ (MEMTYPE σ δ)
      end
  | None => INR "bad kind"
  end.

Lemma has_dropability_checker_correct :
  ∀ F τ δ, has_dropability_checker F τ δ = ok_term -> has_dropability F τ δ.
Proof.
  unfold has_dropability_checker; intros. repeat my_auto3; apply has_kind_checker_correct in H.
  - by apply (DropVALTYPE _ _ r ImCopy _).
  - by apply (DropMEMTYPE _ _ s _).
Qed.



(* Resolves path, and some other more complicated stuff before has_instruction_type *)

Fixpoint get_list_of_reps (σs : list size) : option (list representation) :=
  match σs with
  | [] => Some []
  | (RepS ρ) :: σss =>
      match get_list_of_reps σss with
      | Some ρs => Some (ρ :: ρs)
      | None => None
      end
  | _ => None
  end.

Lemma get_list_of_reps_matches_map :
  (∀ σs ρs, get_list_of_reps σs = Some ρs <-> σs = (map RepS ρs)).
Proof.
  split; intros.
  - generalize dependent ρs.
    induction σs.
    + intros. simpl in H. inversion H; subst; simpl; auto.
    + intros.
      simpl in H.
      repeat my_auto3. subst.
      specialize (IHσs l). specialize (IHσs eq_refl).
      subst; auto.
  - generalize dependent ρs.
    induction σs.
    + intros. simpl in *.
      symmetry in H; apply map_eq_nil in H.
      by subst.
    + intros; simpl in *.
      symmetry in H.
      destruct ρs; [simpl in H; inversion H |].
      rewrite map_cons in H.
      inversion H; subst.
      specialize (IHσs ρs eq_refl).
      by rewrite IHσs.
Qed.


Scheme Equality for num_type.

Lemma num_type_eq_convert :
  ∀ nt1 nt2, num_type_beq nt1 nt2 = true <-> nt1 = nt2.
Proof. Admitted.

(* type beq. Oh boy. Let's go. *)
Fixpoint type_beq (τ1:type) (τ2:type) : bool :=
  match τ1, τ2 with
  | VarT i1, VarT i2 => i1 =? i2
  | I31T κ1, I31T κ2 => kind_beq κ1 κ2
  | NumT κ1 nt1, NumT κ2 nt2 => andb (kind_beq κ1 κ2) (num_type_beq nt1 nt2)
  | SumT κ1 τs1, SumT κ2 τs2
  | VariantT κ1 τs1, VariantT κ2 τs2
  | ProdT κ1 τs1, ProdT κ2 τs2
  | StructT κ1 τs1, StructT κ2 τs2 =>
      andb (kind_beq κ1 κ2) (list_beq type type_beq τs1 τs2)
  | RefT κ1 m1 τ1, RefT κ2 m2 τ2 =>
      andb (andb (kind_beq κ1 κ2) (memory_beq m1 m2)) (type_beq τ1 τ2)
  | CodeRefT κ1 ft1, CodeRefT κ2 ft2 =>
      andb (kind_beq κ1 κ2) (function_type_beq ft1 ft2)
  | SerT κ1 t1, SerT κ2 t2 => andb (kind_beq κ1 κ2) (type_beq t1 t2)
  | PlugT κ1 ρ1, PlugT κ2 ρ2 => andb (kind_beq κ1 κ2) (representation_beq ρ1 ρ2)
  | SpanT κ1 σ1, SpanT κ2 σ2 => andb (kind_beq κ1 κ2) (size_beq σ1 σ2)
  | RecT κ1 t1, RecT κ2 t2
  | ExistsMemT κ1 t1, ExistsMemT κ2 t2
  | ExistsRepT κ1 t1, ExistsRepT κ2 t2
  | ExistsSizeT κ1 t1, ExistsSizeT κ2 t2 =>
      andb (kind_beq κ1 κ2) (type_beq t1 t2)
  | ExistsTypeT κ11 κ12 t1, ExistsTypeT κ21 κ22 t2 =>
      andb (andb (kind_beq κ11 κ21) (kind_beq κ12 κ22)) (type_beq t1 t2)
  | _, _ => false
  end
with function_type_beq (fτ1:function_type) (fτ2:function_type) : bool :=
  match fτ1, fτ2 with
  | MonoFunT τs11 τs12, MonoFunT τs21 τs22 =>
      andb (list_beq type type_beq τs11 τs21) (list_beq type type_beq τs12 τs22)
  | ForallMemT ft1, ForallMemT ft2
  | ForallRepT ft1, ForallRepT ft2
  | ForallSizeT ft1, ForallSizeT ft2 => function_type_beq ft1 ft2
  | ForallTypeT κ1 ft1, ForallTypeT κ2 ft2 =>
      andb (kind_beq κ1 κ2) (function_type_beq ft1 ft2)
  | _, _ => false
  end.





(* I should prove these eventually. Mainly to convince myself that
list_beq will do what I want it to do. Although I think it's just fine.

 TODO *)
Lemma type_eq_convert :
  ∀ τ1 τ2, type_beq τ1 τ2 = true <-> τ1 = τ2.
Proof. Admitted.

Lemma function_type_eq_convert :
  ∀ ft1 ft2, function_type_beq ft1 ft2 = true <-> ft1 = ft2.
Proof. Admitted.

Ltac my_auto3_5 :=
  match goal with
  | H: ((match ?key with |_=>_ end) = _) |- _ => destruct key eqn:?HMatch; try inversion H; simpl in *
  | H:((if ?key then _ else _)=_) |- _ => destruct key eqn:?HMatch; try inversion H; simpl in *
  | H: (kind_beq _ _ = true) |- _ => apply kind_eq_convert in H; subst; auto
  | o:ok |- _ => stupid_unit o
  | H: ok_term = ok_term |- _ => clear H
  | H: (andb _ _ = true) |- _ => apply andb_prop in H; destruct H as [?H1 ?H2]
  | H: (_ && _ = true) |- _ => apply andb_prop in H; destruct H as [?H1 ?H2]
  | H: (_ =? _ = true) |- _ => apply Nat.eqb_eq in H; subst; auto
  | H: true = false |- _ => inversion H
  | H: false = true |- _ => inversion H
  | H: (num_type_beq _ _ = true) |- _ => apply num_type_eq_convert in H; subst; auto
  | H: (type_beq _ _ = true) |- _ => apply type_eq_convert in H; subst; auto
  | H: (function_type_beq _ _ = true) |- _ => apply function_type_eq_convert in H; subst; auto
  | H: (representation_beq _ _ = true) |- _ => apply representation_eq_convert in H; subst; auto
  | H: (dropability_beq _ _ = true) |- _ => apply dropability_eq_convert in H; subst; auto
  | H: (copyability_beq _ _ = true) |- _ => apply copyability_eq_convert in H; subst; auto
  | H: (size_beq _ _ = true) |- _ => apply size_eq_convert in H; subst; auto
  | H: (memory_beq _ _ = true) |- _ => apply memory_eq_convert in H; subst; auto
  | H: (kind_ok_checker _ _ = inl ()) |- _ => apply kind_ok_checker_correct in H; auto
  | H: (kind_ok_checker _ _ = ok_term) |- _ => apply kind_ok_checker_correct in H; auto
  | H: (mem_ok_checker _ _ = inl ()) |- _ => apply mem_ok_checker_correct in H; auto
  | H: (mem_ok_checker _ _ = ok_term) |- _ => apply mem_ok_checker_correct in H; auto
  | H: (rep_ok_checker _ _ = inl ()) |- _ => apply rep_ok_checker_correct in H; auto
  | H: (rep_ok_checker _ _ = ok_term) |- _ => apply rep_ok_checker_correct in H; auto
  | H: (size_ok_checker _ _ = inl ()) |- _ => apply size_ok_checker_correct in H; auto
  | H: (size_ok_checker _ _ = ok_term) |- _ => apply size_ok_checker_correct in H; auto
  | H: (type_ok_checker _ _ = inl ()) |- _ => apply type_ok_checker_correct in H; auto
  | H: (type_ok_checker _ _ = ok_term) |- _ => apply type_ok_checker_correct in H; auto
  | H: (function_type_ok_checker _ _ = inl ()) |- _ => apply function_type_ok_checker_correct in H; auto
  | H: (function_type_ok_checker _ _ = ok_term) |- _ => apply function_type_ok_checker_correct in H; auto
  | H: (has_kind_checker _ _ _ = ok_term) |- _ => apply has_kind_checker_correct in H; auto
  | H: (has_kind_checker _ _ _ = inl ()) |- _ => apply has_kind_checker_correct in H; auto
  | H: (check_if_subkind _ _ = inl ()) |- _ =>
      try( by (eapply check_if_subkind_works_with_has_kind; try constructor; auto))
  | H: (check_if_subkind _ _ = ok_term) |- _ =>
      try( by (eapply check_if_subkind_works_with_has_kind; try constructor; auto))
  | H: (INR _ = ok_term) |- _ => inversion H
  | H: (INR _ = inl ()) |- _ => inversion H
end.

(* This is an attempt without a double match for the sake of the proof later *)
Fixpoint type_eq_checker (F:function_ctx) (τ1:type) (τ2:type) :type_checker_res :=
  (* base cases *)
  match τ1 with
  | VarT _ =>
      match τ2 with
      | VarT _ => if type_beq τ1 τ2 then ok_term else INR "types not equal"
      | _ => INR "types note equal"
      end
  | I31T _ =>
      match τ2 with
      | I31T _ => if type_beq τ1 τ2 then ok_term else INR "types not equal"
      | _ => INR "types not equal"
      end
  | NumT _ _ =>
      match τ2 with
      | NumT _ _ => if type_beq τ1 τ2 then ok_term else INR "types not equal"
      | _ => INR "types note equal"
      end
  | CodeRefT _ _ =>
      match τ2 with
      | CodeRefT _ _ => if type_beq τ1 τ2 then ok_term else INR "types not equal"
      | _ => INR "types note equal"
      end
  | PlugT _ _ =>
      match τ2 with
      | PlugT _ _ => if type_beq τ1 τ2 then ok_term else INR "types not equal"
      | _ => INR "types note equal"
      end
  | SpanT _ _ =>
      match τ2 with
      | SpanT _ _ => if type_beq τ1 τ2 then ok_term else INR "types not equal"
      | _ => INR "types note equal"
      end
  (* Recursive cases *)
  | SumT κ1 τs1 =>
      match τ2 with
      | SumT κ2 τs2 =>
          if kind_beq κ1 κ2
          then
            match has_kind_checker F (SumT κ1 τs1) κ1 with
            | inl () =>
                if foldr2 (λ τ1, λ τ2, andb (check_ok_output (type_eq_checker F τ1 τ2))) true τs1 τs2
                then ok_term
                else INR "types not equal"
            | err => err
            end
          else INR "types not equal"
      | _ => INR "types not equal"
      end
  | VariantT κ1 τs1 =>
      match τ2 with
      | VariantT κ2 τs2 =>
          if kind_beq κ1 κ2
          then
            match has_kind_checker F (VariantT κ1 τs1) κ1 with
            | inl () =>
                if foldr2 (λ τ1, λ τ2, andb (check_ok_output (type_eq_checker F τ1 τ2))) true τs1 τs2
                then ok_term
                else INR "types not equal"
            | err => err
            end
          else INR "types not equal"
      | _ => INR "types not equal"
      end
  | ProdT κ1 τs1 =>
      match τ2 with
      | ProdT κ2 τs2 =>
          if kind_beq κ1 κ2
          then
            match has_kind_checker F (ProdT κ1 τs1) κ1 with
            | inl () =>
                if foldr2 (λ τ1, λ τ2, andb (check_ok_output (type_eq_checker F τ1 τ2))) true τs1 τs2
                then ok_term
                else INR "types not equal"
            | err => err
            end
          else INR "types not equal"
      | _ => INR "types not equal"
      end
  | RefT κ1 μ1 τ1 =>
      match τ2 with
      | RefT κ2 μ2 τ2 =>
          if andb (kind_beq κ1 κ2) (memory_beq μ1 μ2)
          then
            match has_kind_checker F (RefT κ1 μ1 τ1) κ1 with
            | inl () => type_eq_checker F τ1 τ2
            | err => err
            end
          else INR "types not equal"
      | _ => INR "types not equal"
      end
  | RecT κ1 τ1 =>
      match τ2 with
      | RecT κ2 τ2 =>
          if kind_beq κ1 κ2
          then
            match has_kind_checker F (RecT κ1 τ1) κ1 with
            | inl () => type_eq_checker F τ1 τ2
            | err => err
            end
          else INR "types not equal"
      | _ => INR "types not equal"
      end
  | ExistsMemT κ1 τ1 =>
      match τ2 with
      | ExistsMemT κ2 τ2 =>
          if kind_beq κ1 κ2
          then
            match has_kind_checker F (ExistsMemT κ1 τ1) κ1 with
            | inl () => type_eq_checker F τ1 τ2
            | err => err
            end
          else INR "types not equal"
      | _ => INR "types not equal"
      end
  | ExistsRepT κ1 τ1 =>
      match τ2 with
      | ExistsRepT κ2 τ2 =>
          if kind_beq κ1 κ2
          then
            match has_kind_checker F (ExistsRepT κ1 τ1) κ1 with
            | inl () => type_eq_checker F τ1 τ2
            | err => err
            end
          else INR "types not equal"
      | _ => INR "types not equal"
      end
  | ExistsSizeT κ1 τ1 =>
      match τ2 with
      | ExistsSizeT κ2 τ2 =>
          if kind_beq κ1 κ2
          then
            match has_kind_checker F (ExistsSizeT κ1 τ1) κ1 with
            | inl () => type_eq_checker F τ1 τ2
            | err => err
            end
          else INR "types not equal"
      | _ => INR "types not equal"
      end
  | ExistsTypeT κ1 κτ1 τ1 =>
      match τ2 with
      | ExistsTypeT κ2 κτ2 τ2 =>
          if andb (kind_beq κ1 κ2) (kind_beq κτ1 κτ2)
          then
            match has_kind_checker F (ExistsTypeT κ1 κτ1 τ1) κ1 with
            | inl () => type_eq_checker F τ1 τ2
            | err => err
            end
          else INR "types not equal"
      | _ => INR "types not equal"
      end
  | SerT κ1 τ1 =>
      match τ2 with
      | SerT κ2 τ2 =>
          if kind_beq κ1 κ2
          then
            match has_kind_checker F (SerT κ1 τ1) κ1 with
            | inl () => type_eq_checker F τ1 τ2
            | err => err
            end
          else INR "types not equal"
      | StructT κ2 τs2 =>
          match τ1 with
          | ProdT κp τs =>
              if kind_beq κ1 κ2
              then (* I now throw away κ' *)
                match κ1 with
                | MEMTYPE (ProdS σs) δ =>
                    match get_list_of_reps σs with
                    | Some ρs =>
                        if foldr2
                             (λ τ:type, λ ρ:representation,
                                   andb (check_ok_output (has_kind_checker F τ (VALTYPE ρ ImCopy δ)))
                             ) true τs ρs
                        then (* now just check that τs' equal to the monstrosity *)
                          if list_beq type type_beq τs2 ((zip_with (fun τ ρ => SerT (MEMTYPE (RepS ρ) δ) τ)) τs ρs)
                          then ok_term
                          else INR "types not_equal"
                        else INR "types not equal"
                    | None => INR "types not equal"
                    end
                | _ => INR "types not equal"
                end
              else INR "types not equal"

          | _ => INR "types not equal"
          end
      | _ => INR "types not equal"
      end
  | StructT κ1 τs1 =>
      match τ2 with
      | StructT κ2 τs2 =>
          if kind_beq κ1 κ2
          then
            match has_kind_checker F (StructT κ1 τs1) κ1 with
            | inl () =>
                if foldr2 (λ τ1, λ τ2, andb (check_ok_output (type_eq_checker F τ1 τ2))) true τs1 τs2
                then ok_term
                else INR "types not equal 1"
            | err => err
            end
          else INR "types not equal 2"
      | SerT κ2 τ2 =>
          match τ2 with
          | ProdT κp τs =>
              if kind_beq κ2 κ1
              then (* I now throw away κ' *)
                match κ2 with
                | MEMTYPE (ProdS σs) δ =>
                    match get_list_of_reps σs with
                    | Some ρs =>
                        if foldr2
                             (λ τ:type, λ ρ:representation,
                                   andb (check_ok_output (has_kind_checker F τ (VALTYPE ρ ImCopy δ)))
                             ) true τs ρs
                        then (* now just check that τs' equal to the monstrosity *)
                          if list_beq type type_beq τs1 ((zip_with (fun τ ρ => SerT (MEMTYPE (RepS ρ) δ) τ)) τs ρs)
                          then ok_term
                          else INR "types not_equal 3"
                        else INR "types not equal 4"
                    | None => INR "types not equal 5"
                    end
                | _ => INR "types not equal 6"
                end
              else INR "types not equal 7"
          | _ => INR "types not equal 8"
          end

      | _ => INR "types not equal HERE 9"
      end

  end.

(* I'm bad at everything so monomorphic *)
Lemma list_eq_convert_type :
  ∀ τs1 τs2, list_beq type type_beq τs1 τs2 = true <-> τs1 = τs2.
Proof. Admitted.
Lemma list_eq_convert_size :
  ∀ τs1 τs2, list_beq size size_beq τs1 τs2 = true <-> τs1 = τs2.
Proof. Admitted.


(* NOTE: the reason this has such a weird set up is because this
   is the only way I know how to use type_and_function_ind

  also NOTE: this is written more verbosely than ideal due to
  the automation slowing down a Lot without a bit of help.
 *)
Opaque has_kind_checker.

Lemma type_eq_checker_correct_basic :
  (∀ τ1,
     (∀ τ2, ∀ F, type_eq_checker F τ1 τ2 = ok_term -> type_eq F τ1 τ2)
  ) /\
  (∀ ft:function_type, True).
Proof.
  apply type_and_function_ind; auto; intros; destruct τ2.
  (* the goal of this big guy: filter all obvious ones. Does not include "obvious" Ser *)
  all:
    match goal with
    | |- (type_eq _ (VarT _) (VarT _)) => simpl in H; repeat my_auto3_5; apply TEqRefl
    | |- (type_eq _ (I31T _) (I31T _)) => simpl in H; repeat my_auto3_5; apply TEqRefl; auto
    | |- (type_eq _ (NumT _ _) (NumT _ _)) => simpl in H; repeat my_auto3_5; apply TEqRefl; repeat my_auto3_5
    | |- (type_eq _ (SumT _ _) (SumT _ _)) => idtac
    | |- (type_eq _ (VariantT _ _) (VariantT _ _)) => idtac
    | |- (type_eq _ (ProdT _ _) (ProdT _ _)) => idtac
    | |- (type_eq _ (StructT _ _) (StructT _ _)) => idtac
    | |- (type_eq _ (RefT _ _ _) (RefT _ _ _)) =>
        simpl in H0; repeat my_auto3_5; apply H in H0; apply TEqRef; auto
    | |- (type_eq _ (CodeRefT _ _) (CodeRefT _ _)) => simpl in *; repeat my_auto3_5; apply TEqRefl; auto
    | |- (type_eq _ (SerT _ _) (SerT _ _)) =>
        simpl in H0; repeat my_auto3_5; apply TEqSer; auto
    | |- (type_eq _ (StructT _ _) (SerT _ _)) => idtac
    | |- (type_eq _ (SerT _ _) (StructT _ _)) => idtac
    | |- (type_eq _ (SerT _ _) _) => simpl in H0; my_auto3_5
    | |- (type_eq _ (PlugT _ _) (PlugT _ _)) => simpl in *; repeat my_auto3_5; apply TEqRefl; auto
    | |- (type_eq _ (SpanT _ _) (SpanT _ _)) => simpl in *; repeat my_auto3_5; apply TEqRefl; auto
    | |- (type_eq _ (RecT _ _) (RecT _ _)) =>
        simpl in H0; repeat my_auto3_5; apply H in H0; apply TEqRec; auto
    | |- (type_eq _ (ExistsMemT _ _) (ExistsMemT _ _)) =>
        simpl in H0; repeat my_auto3_5; apply H in H0; apply TEqExMem; auto
    | |- (type_eq _ (ExistsRepT _ _) (ExistsRepT _ _)) =>
        simpl in H0; repeat my_auto3_5; apply H in H0; apply TEqExRep; auto
    | |- (type_eq _ (ExistsSizeT _ _) (ExistsSizeT _ _)) =>
        simpl in H0; repeat my_auto3_5; apply H in H0; apply TEqExSize; auto
    | |- (type_eq _ (ExistsTypeT _ _ _) (ExistsTypeT _ _ _)) =>
        simpl in H0; repeat my_auto3_5; apply H in H0; apply TEqExType; auto
    | _ => simpl in *; my_auto3_5
    end.

  all: idtac. (* this is here because doom emacs despises the match goal above *)

  (* ser struct case *)
  6: {
    simpl in H0. destruct t; simpl in H0; repeat my_auto3_5.
    apply get_list_of_reps_matches_map in HMatch2; subst.
    apply list_eq_convert_type in HMatch4; subst.
    apply list_eq_convert_size in H1; subst.
    apply (TEqSerProd _ _ l2 ImCopy d0 _).
    (* this then relies on some foldr2 lemmas *)
    admit.
  }
  (* struct ser case *)
  5: {

    simpl in H0. destruct τ2; simpl in H0; repeat my_auto3_5.
    apply get_list_of_reps_matches_map in HMatch2; subst.
    apply list_eq_convert_type in HMatch4; subst.
    apply list_eq_convert_size in H1; subst.
    apply TEqSym.
    apply (TEqSerProd _ _ l1 ImCopy d0 _).
    (* this then relies on some foldr2 lemmas *)
    admit.

  }
  (* All the rest of are foldr2 lemma reliant, so *)
  all: admit.

Admitted.


Lemma type_eq_checker_correct :
  ∀ F τ1 τ2, type_eq_checker F τ1 τ2 = ok_term -> type_eq F τ1 τ2.
Proof.
  pose proof type_eq_checker_correct_basic.
  destruct H as [H1 H2].
  intros.
  specialize (H1 τ1).
  auto.
Qed.


Definition path_result_beq (pres1 pres2:path_result) : bool :=
  andb (andb (list_beq type type_beq pres1.(pr_prefix) pres2.(pr_prefix))
             (type_beq pres1.(pr_target) pres2.(pr_target)))
             (type_beq pres1.(pr_replaced) pres2.(pr_replaced)).

Lemma path_result_eq_convert :
  ∀ pres1 pres2, path_result_beq pres1 pres2 = true <-> pres1 = pres2.
Proof.
  split; intros.
  - unfold path_result_beq in H.
    repeat my_auto3_5.
    apply list_eq_convert_type in H1.
    destruct pres1, pres2.
    simpl in *. subst.
    auto.
  - destruct pres1, pres2.
    inversion H; subst.
    unfold path_result_beq. simpl.
    apply andb_true_intro. split; [apply andb_true_intro; split |].
    + apply list_eq_convert_type. auto.
    + apply type_eq_convert; auto.
    + apply type_eq_convert; auto.
Qed.

Fixpoint resolves_path_checker
  (τ:type) (p:path) (oτ:option type) (pres:path_result) : type_checker_res :=
  match p with
  | [] =>
      match oτ with
      | Some τ' =>
          if path_result_beq pres (Build_path_result [] τ τ')
          then ok_term
          else INR "does not resolve path"
      | None =>
          if path_result_beq pres (Build_path_result [] τ τ)
          then ok_term
          else INR "does not resolve path"
      end
  | i :: p => (* this is INCORRECT but temporary to allow for proving base case TODO *)
      match τ with
      | StructT κ τs_full => resolves_path_checker τ p oτ pres
      | _ => INR "does not resolves path"
      end
  end.

Lemma resolves_path_checker_correct_basic :
  ∀ p τ oτ pres, resolves_path_checker τ p oτ pres = ok_term -> resolves_path τ p oτ pres.
Proof.
  intros p.
  induction p.
  - intros. unfold resolves_path_checker in H.
    destruct oτ; repeat my_auto3_5; apply path_result_eq_convert in HMatch; subst.
    + apply PathNilSome.
    + apply PathNilNone.
  -

Admitted.

Lemma resolves_path_checker_correct :
  ∀ τ p oτ pres, resolves_path_checker τ p oτ pres = ok_term -> resolves_path τ p oτ pres.
Proof. intros. apply resolves_path_checker_correct_basic. auto. Qed.


Definition grab_inner_ft (ft:function_type) : option function_type :=
  match ft with
  | ForallMemT ϕ
  | ForallRepT ϕ
  | ForallSizeT ϕ
  | ForallTypeT _ ϕ => Some ϕ
  | MonoFunT _ _ => None
  end.

Ltac my_auto4 :=
  match goal with
  | H: ((match ?key with |_=>_ end) = _) |- _ => destruct key eqn:?HMatch; try inversion H; simpl in *
  | H:((if ?key then _ else _)=_) |- _ => destruct key eqn:?HMatch; try inversion H; simpl in *
  | H: (kind_beq _ _ = true) |- _ => apply kind_eq_convert in H; subst; auto
  | o:ok |- _ => stupid_unit o
  | H: ok_term = ok_term |- _ => clear H
  | H: (andb _ _ = true) |- _ => apply andb_prop in H; destruct H as [?H1 ?H2]
  | H: (_ && _ = true) |- _ => apply andb_prop in H; destruct H as [?H1 ?H2]
  | H: true = false |- _ => inversion H
  | H: false = true |- _ => inversion H
  | H: (representation_beq _ _ = true) |- _ => apply representation_eq_convert in H; subst; auto
  | H: (dropability_beq _ _ = true) |- _ => apply dropability_eq_convert in H; subst; auto
  | H: (copyability_beq _ _ = true) |- _ => apply copyability_eq_convert in H; subst; auto
  | H: (size_beq _ _ = true) |- _ => apply size_eq_convert in H; subst; auto
  | H: (function_type_beq _ _ = true) |- _ => apply function_type_eq_convert in H; subst; auto
  | H: (type_beq _ _ = true) |- _ => apply type_eq_convert in H; subst; auto
  | H: (kind_ok_checker _ _ = inl ()) |- _ => apply kind_ok_checker_correct in H; auto
  | H: (kind_ok_checker _ _ = ok_term) |- _ => apply kind_ok_checker_correct in H; auto
  | H: (mem_ok_checker _ _ = inl ()) |- _ => apply mem_ok_checker_correct in H; auto
  | H: (mem_ok_checker _ _ = ok_term) |- _ => apply mem_ok_checker_correct in H; auto
  | H: (rep_ok_checker _ _ = inl ()) |- _ => apply rep_ok_checker_correct in H; auto
  | H: (rep_ok_checker _ _ = ok_term) |- _ => apply rep_ok_checker_correct in H; auto
  | H: (size_ok_checker _ _ = inl ()) |- _ => apply size_ok_checker_correct in H; auto
  | H: (size_ok_checker _ _ = ok_term) |- _ => apply size_ok_checker_correct in H; auto
  | H: (type_ok_checker _ _ = inl ()) |- _ => apply type_ok_checker_correct in H; auto
  | H: (type_ok_checker _ _ = ok_term) |- _ => apply type_ok_checker_correct in H; auto
  | H: (function_type_ok_checker _ _ = inl ()) |- _ => apply function_type_ok_checker_correct in H; auto
  | H: (function_type_ok_checker _ _ = ok_term) |- _ => apply function_type_ok_checker_correct in H; auto
  | H: (has_kind_checker _ _ _ = inl ()) |- _ => apply has_kind_checker_correct in H; auto
  | H: (has_kind_checker _ _ _ = ok_term) |- _ => apply has_kind_checker_correct in H; auto
  | H: (check_if_subkind _ _ = inl ()) |- _ =>
      try( by (eapply check_if_subkind_works_with_has_kind; try constructor; auto))
  | H: (check_if_subkind _ _ = ok_term) |- _ =>
      try( by (eapply check_if_subkind_works_with_has_kind; try constructor; auto))
end.

Definition function_type_inst_checker
  (F:function_ctx) (i:index) (ft1:function_type) (ft2:function_type) : type_checker_res :=
  match i with
  | MemI μ =>
      match ft1 with
      | ForallMemT ϕ =>
          if function_type_beq ft2 (subst_function_type (unscoped.scons μ VarM) VarR VarS VarT ϕ)
          then ok_term
          else INR "something not matching in function type inst checker"
      | _ => INR "bad function type inst"
      end
  | RepI ρ =>
      match ft1 with
      | ForallRepT ϕ =>
          if function_type_beq ft2 (subst_function_type VarM (unscoped.scons ρ VarR) VarS VarT ϕ)
          then ok_term
          else INR "something not matching in function type inst checker"
      | _ => INR "bad function type inst"
      end
  | SizeI σ =>
      match ft1 with
      | ForallSizeT ϕ =>
          if function_type_beq ft2 (subst_function_type VarM VarR (unscoped.scons σ VarS) VarT ϕ)
          then ok_term
          else INR "something not matching in function type inst checker"
      | _ => INR "bad function type inst"
      end
 | TypeI τ =>
       match ft1 with
      | ForallTypeT κ ϕ =>
          match has_kind_checker F τ κ with
          | inl () =>
              if function_type_beq ft2 (subst_function_type VarM VarR VarS (unscoped.scons τ VarT) ϕ)
              then ok_term
              else INR "something not matching in function type inst checker"
          | err => err
          end
      | _ => INR "bad function type inst"
      end
 end.


Lemma function_type_inst_checker_correct :
  ∀ F i ft1 ft2, function_type_inst_checker F i ft1 ft2 = ok_term -> function_type_inst F i ft1 ft2.
Proof.
  unfold function_type_inst_checker; intros.
  repeat my_auto4.
  all: constructor; auto.
Qed.

Definition grab_substed_ft F (ix:index) (ft1:function_type) : option function_type :=
  match ix with
  | MemI μ =>
      match ft1 with
      | ForallMemT ϕ => Some (subst_function_type (unscoped.scons μ VarM) VarR VarS VarT ϕ)
      | _ => None
      end
  | RepI ρ =>
      match ft1 with
      | ForallRepT ϕ => Some (subst_function_type VarM (unscoped.scons ρ VarR) VarS VarT ϕ)
      | _ => None
      end
  | SizeI σ =>
      match ft1 with
      | ForallSizeT ϕ => Some (subst_function_type VarM VarR (unscoped.scons σ VarS) VarT ϕ)
      | _ => None
      end
 | TypeI τ =>
       match ft1 with
      | ForallTypeT κ ϕ =>
          match has_kind_checker F τ κ with
          | inl () => Some (subst_function_type VarM VarR VarS (unscoped.scons τ VarT) ϕ)
          | _ => None
          end
      | _ => None
      end
  end.

Fixpoint function_type_insts_checker
      (F:function_ctx) (iss:list index) (ft1:function_type) (ft2:function_type) : type_checker_res :=
  match iss with
  | [] =>
      if function_type_beq ft1 ft2
      then ok_term
      else INR "not equal in function_type_insts_checker"
  | ix :: ixs =>
      match grab_substed_ft F ix ft1 with
      | Some ftinner =>
          match function_type_inst_checker F ix ft1 ftinner with
          | inl () => function_type_insts_checker F ixs ftinner ft2
          | err => err
          end
      | None => INR "can't find ϕ' for FTCons"
      end
  end.

Lemma function_type_insts_checker_correct :
  ∀ F iss ft1 ft2, function_type_insts_checker F iss ft1 ft2 = ok_term ->
                   function_type_insts F iss ft1 ft2.
Proof.
  intros F iss.
  induction iss; intros; unfold function_type_insts_checker in H; repeat my_auto4.
  - constructor.
  - apply function_type_inst_checker_correct in HMatch0.
    apply (FTCons _ _ f _ _ _); auto.
Qed.


(* TODO THIS IS SOMETHING I ACTUALLY AM UNSURE HOW TO DO *)
Definition packed_existential_checker (F:function_ctx) (τ1 τ2:type) : type_checker_res :=
  match τ2 with
  | ExistsMemT κ' τ' =>
      match has_kind_checker F τ' κ' with
      | inl () =>
          if true (* TODO HOW DO I GET THE MU OUT OF THERE *)
            (*list_beq τ1 (subst_type (unscoped.scons μ VarM) VarR VarS VarT τ')*)
          then ok_term
          else INR "bad packed existential"
      | err => err
      end
  | ExistsRepT κ' τ' => INR "incomplete"
  | ExistsSizeT κ' τ' => INR "incomplete"
  | ExistsTypeT κ' κ τ' => INR "incomplete"
  | _ => INR "trying to check existential type, but not existential"
  end.

Lemma packed_existential_checker_correct :
  ∀ F τ1 τ2, packed_existential_checker F τ1 τ2 = ok_term -> packed_existential F τ1 τ2.
Proof.

Admitted.

(* This one has the reverse list stuff which I'm unsure how to do exactly *)
Definition unpacked_existential_checker
 (F:function_ctx) (L1:local_ctx) (insts:list instruction) (instt : instruction_type) (L2:local_ctx)
 (F':function_ctx) (L1':local_ctx) (insts':list instruction) (instt': instruction_type) (L2':local_ctx)
  :=
  INR "incomplete".

Lemma unpacked_existential_checker_correct :
  ∀ F L1 insts instt L2 F' L1' insts' instt' L2',
    unpacked_existential_checker F L1 insts instt L2 F' L1' insts' instt' L2' = ok_term ->
    unpacked_existential F L2 insts instt L2 F' L1' insts' instt' L2'.
Proof. Admitted.

Definition local_ctx_ok_checker (F:function_ctx) (L:local_ctx) : type_checker_res :=
  if foldr2
       (λ t:type, λ p:list primitive,
             andb (check_ok_output (type_rep_eq_prim_checker F t p))
       ) true L (F.(fc_locals))
  then ok_term
  else INR "local context not ok".
Lemma local_ctx_ok_checker_correct :
  ∀ F L, local_ctx_ok_checker F L = ok_term -> local_ctx_ok F L.
Proof.
  (* this will be some foldr2 lemmas *)
Admitted.





(* And from here on, we move onto has_instruction_type stuff *)
Definition has_instruction_type_ok_checker F ψ L' : type_checker_res :=
  match has_mono_rep_instr_checker F ψ with
  | inl () => local_ctx_ok_checker F L'
  | err => err
  end.
Lemma has_instruction_type_ok_checker_correct :
  ∀ F ψ L', has_instruction_type_ok_checker F ψ L' = ok_term -> has_instruction_type_ok F ψ L'.
Proof.
  intros. unfold has_instruction_type_ok_checker in H.
  repeat my_auto3.
  apply has_mono_rep_instr_checker_correct in HMatch.
  clear H1 H2.
  apply local_ctx_ok_checker_correct in H.
  constructor; auto.
Qed.


(* NOTE: the reason I do InstrT [a] [b] for most of these is to speed up
   the automation in the proof. Using the if then else is faster than
   a match.
   It also allows me to use the type functions/variables, (like type_i32)
   rather than fully spelling out the type.
 *)
Definition has_instruction_type_cvt_checker cop ψ : type_checker_res :=
  match cop with
  | CWrap =>
      match ψ with
      | InstrT [a] [b] =>
          if andb (type_beq a type_i64) (type_beq b type_i32)
          then ok_term
          else INR "incorrect cvt instruction type"
      | _ => INR "incorrect cvt instruction type"
      end
  | CExtend _ =>
      match ψ with
      | InstrT [a] [b] =>
          if andb (type_beq a type_i32) (type_beq b type_i64)
          then ok_term
          else INR "incorrect cvt instruction type"
      | _ => INR "incorrect cvt instruction type"
      end
  | CTrunc vf vi _ =>
      match ψ with
      | InstrT [a] [b] =>
          if andb (type_beq a (float_type_type vf)) (type_beq b (int_type_type vi))
          then ok_term
          else INR "incorrect cvt instruction type"
      | _ => INR "incorrect cvt instruction type"
      end
  | CDemote =>
      match ψ with
      | InstrT [a] [b] =>
          if andb (type_beq a type_f64) (type_beq b type_f32)
          then ok_term
          else INR "incorrect cvt instruction type"
      | _ => INR "incorrect cvt instruction type"
      end
  | CPromote =>
      match ψ with
      | InstrT [a] [b] =>
          if andb (type_beq a type_f32) (type_beq b type_f64)
          then ok_term
          else INR "incorrect cvt instruction type"
      | _ => INR "incorrect cvt instruction type"
      end
  | CConvert vf vi _ =>
      match ψ with
      | InstrT [a] [b] =>
          if andb (type_beq a (int_type_type vf)) (type_beq b (float_type_type vi))
          then ok_term
          else INR "incorrect cvt instruction type"
      | _ => INR "incorrect cvt instruction type"
      end
  | CReinterpret (IntT I32T) =>
      match ψ with
      | InstrT [a] [b] =>
          if andb (type_beq a type_i32) (type_beq b type_f32)
          then ok_term
          else INR "incorrect cvt instruction type"
      | _ => INR "incorrect cvt instruction type"
      end
  | CReinterpret (IntT I64T) =>
      match ψ with
      | InstrT [a] [b] =>
          if andb (type_beq a type_i64) (type_beq b type_f64)
          then ok_term
          else INR "incorrect cvt instruction type"
      | _ => INR "incorrect cvt instruction type"
      end
  | CReinterpret (FloatT F32T) =>
      match ψ with
      | InstrT [a] [b] =>
          if andb (type_beq a type_f32) (type_beq b type_i32)
          then ok_term
          else INR "incorrect cvt instruction type"
      | _ => INR "incorrect cvt instruction type"
      end
  | CReinterpret (FloatT F64T) =>
      match ψ with
      | InstrT [a] [b] =>
          if andb (type_beq a type_f64) (type_beq b type_i64)
          then ok_term
          else INR "incorrect cvt instruction type"
      | _ => INR "incorrect cvt instruction type"
      end
  end.
Lemma has_instruction_type_cvt_checker_correct :
  ∀ cop ψ, has_instruction_type_cvt_checker cop ψ = ok_term -> has_instruction_type_cvt cop ψ.
Proof.
  intros. destruct cop; simpl in *; repeat my_auto4; subst; constructor.
Qed.

Definition has_instruction_type_num_checker ni ψ :=
  match ni with
  | IInt1 vi _ =>
      match ψ with
      | InstrT [a] [b] =>
          if andb (type_beq a (int_type_type vi)) (type_beq b (int_type_type vi))
          then ok_term
          else INR "incorrect num instruction type[<35;19;60M]"
      | _ => INR "incorrect num instruction type"
      end
  | IInt2 vi _ =>
      match ψ with
      | InstrT [a1; a2] [b] =>
          if andb (andb (type_beq a1 (int_type_type vi)) (type_beq a2 (int_type_type vi)))
                  (type_beq b (int_type_type vi))
          then ok_term
          else INR "incorrect num instruction type[<35;19;60M]"
      | _ => INR "incorrect num instruction type"
      end
  | IIntTest vi _ =>
      match ψ with
      | InstrT [a] [b] =>
          if andb (type_beq a (int_type_type vi)) (type_beq b type_i32)
          then ok_term
          else INR "incorrect num instruction type[<35;19;60M]"
      | _ => INR "incorrect num instruction type"
      end
  | IIntRel vi _ =>
      match ψ with
      | InstrT [a1; a2] [b] =>
          if andb (andb (type_beq a1 (int_type_type vi)) (type_beq a2 (int_type_type vi)))
                  (type_beq b type_i32)
          then ok_term
          else INR "incorrect num instruction type[<35;19;60M]"
      | _ => INR "incorrect num instruction type"
      end
  | IFloat1 vi _ =>
      match ψ with
      | InstrT [a] [b] =>
          if andb (type_beq a (float_type_type vi)) (type_beq b (float_type_type vi))
          then ok_term
          else INR "incorrect num instruction type[<35;19;60M]"
      | _ => INR "incorrect num instruction type"
      end
  | IFloat2 vi _ =>
      match ψ with
      | InstrT [a1; a2] [b] =>
          if andb (andb (type_beq a1 (float_type_type vi)) (type_beq a2 (float_type_type vi)))
                  (type_beq b (float_type_type vi))
          then ok_term
          else INR "incorrect num instruction type[<35;19;60M]"
      | _ => INR "incorrect num instruction type"
      end
  | IFloatRel vi _ =>
      match ψ with
      | InstrT [a1; a2] [b] =>
          if andb (andb (type_beq a1 (float_type_type vi)) (type_beq a2 (float_type_type vi)))
                  (type_beq b type_i32)
          then ok_term
          else INR "incorrect num instruction type[<35;19;60M]"
      | _ => INR "incorrect num instruction type"
      end
  | ICvt op => has_instruction_type_cvt_checker op ψ
  end.
Lemma has_instruction_type_num_checker_correct :
  ∀ ni ψ, has_instruction_type_num_checker ni ψ = ok_term -> has_instruction_type_num ni ψ.
Proof.
  intros. destruct ni; simpl in *; repeat my_auto4; subst; try constructor.
  apply has_instruction_type_cvt_checker_correct in H; auto.
Qed.

(* You know all the previous should have instead been using an instruction_type_beq. Oops.*)
Definition instruction_type_beq (inst1 inst2:instruction_type) : bool :=
  match inst1, inst2 with
  | InstrT τs11 τs12, InstrT τs21 τs22 =>
      andb (list_beq type type_beq τs11 τs21) (list_beq type type_beq τs12 τs22)
  end.
Lemma instruction_type_eq_convert :
  ∀ inst1 inst2, instruction_type_beq inst1 inst2 = true <-> inst1 = inst2.
Proof.
  split; intros; destruct inst1, inst2; unfold instruction_type_beq in *; simpl in *.
  - repeat my_auto3_5. apply list_eq_convert_type in H1, H2. subst; auto.
  - inversion H; subst.
    apply andb_true_intro; split; apply list_eq_convert_type; auto.
Qed.

About local_ctx.
Definition local_ctx_beq (L L':local_ctx) : bool := list_beq type type_beq L L'.
Lemma local_ctx_eq_convert :
  ∀ L L', local_ctx_beq L L' = true <-> L = L'.
Proof.
  split; intros; unfold local_ctx_beq in *.
  - apply list_eq_convert_type in H; subst; auto.
  - subst; apply list_eq_convert_type; auto.
Qed.

(* I'm going to do this really stupidly *)
Definition has_num_type_type (τ:type) : bool :=
  orb (orb (type_beq τ (NumT (VALTYPE (AtomR I32R) ImCopy ImDrop) (IntT I32T)))
           (type_beq τ (NumT (VALTYPE (AtomR I64R) ImCopy ImDrop) (IntT I64T))))
      (orb (type_beq τ (NumT (VALTYPE (AtomR F32R) ImCopy ImDrop) (FloatT F32T)))
           (type_beq τ (NumT (VALTYPE (AtomR F64R) ImCopy ImDrop) (FloatT F64T)))).
Lemma has_num_type_type_correct :
  ∀ τ, has_num_type_type τ = true <-> (∃ ν, τ = num_type_type ν).
Proof.
  split; intros; unfold has_num_type_type in *.
  - apply orb_true_iff in H; destruct H as [H | H]; apply orb_true_iff in H; destruct H as [H | H];
    apply type_eq_convert in H; subst.
    + exists (IntT I32T); auto.
    + exists (IntT I64T); auto.
    + exists (FloatT F32T); auto.
    + exists (FloatT F64T); auto.
  - repeat rewrite orb_true_iff.
    destruct H as [ν H].
    destruct ν; [destruct i | destruct f].
    + left; left. by apply type_eq_convert.
    + left; right. by apply type_eq_convert.
    + right; left. by apply type_eq_convert.
    + right; right. by apply type_eq_convert.
Qed.

Fixpoint check_recursion_single_inner (inst:instruction) : bool :=
  let fix check_recursion_list_inner insts : bool :=
    match insts with
    | [] => true
    | e :: es => andb (check_recursion_single_inner e) (check_recursion_list_inner es)
    end
  in
  match inst with
  | IUnreachable _ => false
  | IBlock _ _ es => check_recursion_list_inner es
  | _ => true
  end.

Fail Fixpoint check_recursion_single_outer (inst:instruction) : bool :=
  match inst with
  | IUnreachable _ => false
  | IBlock _ _ es => check_recursion_list_outer es
  | _ => true
  end
with check_recursion_list_outer insts : bool :=
  match insts with
  | [] => true
  | e :: es => andb (check_recursion_single_outer e) (check_recursion_list_outer es)
  end.


Fixpoint split_list_all_last {A:Type} (l:list A) : option (list A * A) :=
  match l with
  | [] => None
  | [a] => Some ([], a)
  | h :: rest =>
      match split_list_all_last rest with
      | Some (ll, last) => Some (h::ll, last)
      | None => None
      end
  end.

Lemma split_list_all_last_correct :
  ∀ (A:Type) (l ls:list A) (last:A),
    split_list_all_last l = Some (ls, last) -> l = ls ++ [last].
Proof.
  intros A l.
  induction l.
  - intros. simpl in H; inversion H.
  - intros.
    simpl in H.
    destruct l.
    + inversion H; subst.
      by rewrite app_nil_l.
    + my_auto4.
      clear H1.
      destruct p. inversion H. subst.
      specialize (IHl l0 last eq_refl).
      rewrite IHl. auto.
Qed.

Fixpoint list_suffix_helper (l1 l2: list type) (l1len l2len: nat) : option (list type) :=
  if l1len =? l2len
  then
    if list_beq type type_beq l1 l2
    then Some []
    else None
  else
    match l1, l1len with
    | h::rest, S n =>
        match list_suffix_helper rest l2 n l2len with
        | Some pr => Some (h::pr)
        | None => None
        end
    | _, _ => None
    end.

Definition list_suffix l1 l2 : option (list type) :=
  let l1len := Init.Datatypes.length l1 in
  let l2len := Init.Datatypes.length l2 in
  list_suffix_helper l1 l2 l1len l2len.

Lemma list_suffix_correct :
  ∀ lfull lpre lsuf,
    lfull = lpre ++ lsuf -> list_suffix lfull lsuf = Some lpre.
Proof.
  intros lfull.
  induction lfull.
  - intros.
    destruct lpre, lsuf; try inversion H.
    auto.
  - intros lprebig.
    destruct lprebig as [ | a' lpre ].
    + admit.
    + intros.
      inversion H; subst.
      specialize (IHlfull lpre lsuf eq_refl).
      (* yeah this is right *)
      admit.
Admitted.



(* Will need a mutually recursive have_instruction_type too *)
Fixpoint has_instruction_type_checker
    (M:module_ctx) (F:function_ctx) (L:local_ctx)
    (inst:instruction) (ψ:instruction_type) (L':local_ctx) {struct inst} : type_checker_res :=
  let fix have_instruction_type_checker
    (M:module_ctx) (F:function_ctx) (L:local_ctx)
    (insts:list instruction) (ψ:instruction_type) (L':local_ctx) {struct insts} : type_checker_res :=
    match insts with
    | [] =>
        if andb (instruction_type_beq ψ (InstrT [] [])) (local_ctx_beq L L')
        then local_ctx_ok_checker F L
        else INR "bad empty instructions type"
    (*| [e] => has_instruction_type_checker M F L e ψ L'*)
    | e :: es => (* NOTE THIS IS FUNDAMENTALLY INCORRECT!!! THIS IS TEMPORARY FOR CHECKING RECURSION *)
        match have_instruction_type_checker M F L es ψ L' with
        | inl () => has_instruction_type_checker M F L e ψ L'
        | err => err
        end
    end
  in

  match inst with
  (*  BASE CASES  *)
  | INop ψ_inner =>
      if andb (andb (instruction_type_beq ψ (InstrT [] []))
           (instruction_type_beq ψ_inner (InstrT [] []))) (local_ctx_beq L L')
      then has_instruction_type_ok_checker F ψ L
      else INR "incorrect instruction type for nop"
  | IUnreachable ψ_inner =>
      if instruction_type_beq ψ ψ_inner
      then has_instruction_type_ok_checker F ψ L'
      else INR "incorrect instruction type for unreachable"
  | ICopy ψ_inner =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match ψ with
        | InstrT [τ] [τ1;τ2] =>
            if andb (type_beq τ τ1) (type_beq τ1 τ2)
            then
              match has_copyability_checker F τ ExCopy with
              | inl () => has_instruction_type_ok_checker F ψ L
              | _ => INR "incorrect copyability for instruction type for copy"
              end
            else INR "incorrect instruction type for copy"
        | _ => INR "incorrect instruction type for copy"
        end
      else INR "incorrect instruction type for copy"
  | IDrop ψ_inner =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match ψ with
        | InstrT [τ] [] => has_instruction_type_ok_checker F ψ L
        | _ => INR "incorrect instruction type for drop"
        end
      else INR "incorrect instruction type for drop"
  | INum ψ_inner e =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match has_instruction_type_num_checker e ψ with
        | inl () => has_instruction_type_ok_checker F ψ L
        | err => err
        end
      else INR "incorrect instruction type for num"
  | INumConst ψ_inner n =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match ψ with
        | InstrT [] [τ] =>
            if has_num_type_type τ
            then has_instruction_type_ok_checker F ψ L
            else INR "incorrect instruction type for numconst"
        | _ => INR "incorrect instruction type for numconst"
        end
      else INR "incorrect instruction type for numconst"
  (* not base cases lmao *)
  | IBlock ψ_inner L_inner es =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L' L_inner)
      then (* this INCORRECT but just to check if the recursion goes through *)
        match ψ with
        | InstrT τs1 τs2 =>
            match have_instruction_type_checker M (F <| fc_labels ::= cons (τs2, L') |>) L es ψ L' with
            | inl () => has_instruction_type_ok_checker F ψ L'
            | err => err
            end
        end
      else INR "incorrect instruction type for block"
  | ILoop ψ_inner es =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match ψ with
        | InstrT τs1 τs2 =>
            match have_instruction_type_checker M (F <| fc_labels ::= cons (τs1, L) |>) L es ψ L with
            | inl () => has_instruction_type_ok_checker F ψ L
            | err => err
            end
        end
      else INR "incorrect instruction type for loop"
  | IIte ψ_inner L_inner es1 es2 =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L_inner L')
      then
        match ψ with
        | InstrT τs1_full τs2 =>
            match split_list_all_last τs1_full with
            | Some (τs1, τ) =>
                if type_beq τ type_i32
                then
                  match have_instruction_type_checker M (F <| fc_labels ::= cons (τs2, L') |>) L
                          es1 (InstrT τs1 τs2) L' with
                  | inl () =>
                      match have_instruction_type_checker M (F <| fc_labels ::= cons (τs2, L') |>) L
                          es2 (InstrT τs1 τs2) L' with
                      | inl () => has_instruction_type_ok_checker F ψ L'
                      | err => err
                      end
                  | err => err
                  end
                else INR "instruction type for ite does not have i32"
            | None => INR "instruction type for ite does not have i32"
            end
        end
      else INR "incorrect instruction type for ite"
  | IBr ψ_inner i =>
      if instruction_type_beq ψ ψ_inner
      then
        match F.(fc_labels) !! i with
        | Some (τs, L_inner) =>
            if local_ctx_beq L_inner L
            then (* okay now we have to ensure ts1_full is split correctly *)
              match ψ with
              | InstrT τs1_full τs2 =>
                  match list_suffix τs1_full τs with
                  | Some τs1 =>
                      if true (* if all ImDrop TODO *)
                      then has_instruction_type_ok_checker F ψ L'
                      else INR "incorrect instruction type for br"
                  | None => INR "incorrect instruction type for br"
                  end
              end
            else INR "incorrect instruction type for br"
        | None => INR "incorrect instruction type for br, something with fc labels"
        end
      else INR "incorrect instruction type for br"
  | IReturn ψ_inner =>
      if instruction_type_beq ψ ψ_inner
      then
        let τs := F.(fc_return) in
        match ψ with
        | InstrT τs1_full τs2 =>
            match list_suffix τs1_full τs with
            | Some τs1 =>
                if true (* if all ImDrop TODO *)
                then has_instruction_type_ok_checker F ψ L'
                else INR "incorrect instruction type for return"
            | None => INR "incorrect instruction type for return"
            end
        end
      else INR "incorrect instruction type for return"
  | ILocalGet ψ_inner i => (* note this is for both TLocalGetMove and TLocalGetCopy *)
      if andb (instruction_type_beq ψ ψ_inner) (true)
      then
        match L !! i with
        | Some τ =>
            match ψ with
            | InstrT [] [τ'] =>
                if type_beq τ τ'
                then
                  match has_copyability_checker F τ ImCopy with (* decision point *)
                  | inl () =>
                      if local_ctx_beq L L'
                      then has_instruction_type_ok_checker F ψ L
                      else INR "incorrect instruction type for local get"
                  | inr _ =>
                      match F.(fc_locals) !! i with
                      | Some ηs =>
                          if local_ctx_beq L' (<[ i := type_plug_prim ηs ]> L)
                          then has_instruction_type_ok_checker F ψ L'
                          else INR "incorrect instruction type for local get"
                      | None => INR "incorrect instruction type for local get"
                      end
                  end
                else INR "incorrect instruction type for local get"
            | InstrT _ _ => INR "incorrect instruction type for local get (shape not [] -> [τ])"
            end
        | None => INR "incorrect instruction type for local get (i not in local context)"
        end
      else INR "incorrect instruction type for local get"
  | ICodeRef ψ_inner i =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match ψ with
        | InstrT [] [τ'] =>
            match M.(mc_table) !! i with
            | Some ϕ =>
                if type_beq τ' (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop) ϕ)
                then has_instruction_type_ok_checker F ψ L
                else INR "incorrect instruction type for coderef"
            | None => INR "incorrect instruction type for coderef"
            end
        | InstrT _ _ => INR "incorrect instruction type for coderef (wrong shape)"
        end
      else INR "incorrect instruction type for coderef"
  | IInst ψ_inner ix =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match ψ with
        | InstrT [a] [b] =>
            match a, b with
            | CodeRefT κ ϕ, CodeRefT κ' ϕ' =>
                if andb (kind_beq κ (VALTYPE (AtomR I32R) ImCopy ImDrop)) (kind_beq κ κ')
                then
                  match function_type_inst_checker F ix ϕ ϕ' with
                  | inl () => has_instruction_type_ok_checker F ψ L
                  | err => err
                  end
                else INR "incorrect instruction type for IInst"
            | _, _ => INR "incorrect instruction type for IINst"
            end
        | _ => INR "incorrect instruction type for IInst (wrong shape)"
        end
      else INR "incorrect instruction type for IINst"
  | ICall ψ_inner i ixs =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match ψ with
        | InstrT τs1 τs2 =>
            match M.(mc_functions) !! i with
            | Some ϕ =>
                match function_type_insts_checker F ixs ϕ (MonoFunT τs1 τs2) with
                | inl () => has_instruction_type_ok_checker F ψ L
                | err => err
                end
            | None => INR "incorrect instruction type for call"
            end
        end
      else INR "incorrect instruction type for call"
  | ICallIndirect ψ_inner =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match ψ with
        | InstrT τs1_full τs2 =>
            match split_list_all_last τs1_full with
            | Some (τs1, τ) =>
                if type_beq τ (CodeRefT (VALTYPE (AtomR I32R) ImCopy ImDrop) (MonoFunT τs1 τs2))
                then has_instruction_type_ok_checker F ψ L
                else INR "incorrect instruction type for call indirect"
            | None => INR "incorrect instruction type for call indirect"
            end
        end
      else INR "incorrect instruction type for call indirect"
  | IInject ψ_inner i =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match ψ with
        | InstrT [τ'] [a] =>
            match a with
            | SumT κ τs =>
                match τs !! i with
                | Some τ =>
                    if type_beq τ' τ
                    then has_instruction_type_ok_checker F ψ L
                    else INR "incorrect instruction type for inject"
                | None => INR "incorrect instruction type for inject"
                end
            | _ => INR "incorrect instruction type for inject (wrong shape)"
            end
        | _ => INR "incorrect instruction type for inject (wrong shape)"
        end
      else INR "incorrect instruction type for inject"
  | IInjectNew ψ_inner i => INR "incomplete" (* TODO do i have smthn for zip_with already *)
  | ICase ψ_inner L_inner ess => INR "incomplete"
  | ICaseLoad ψ_inner cm L_inner ess => INR "incomplete"
  | IGroup ψ_inner =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match ψ with
        | InstrT τs [a] =>
            match a with
            | ProdT κ τs' =>
                if list_beq type type_beq τs τs'
                then has_instruction_type_ok_checker F ψ L
                else INR "incorrect instruction type for group"
            | _ => INR "incorrect instruction type for group (wrong shape)"
            end
        | _ => INR "incorrect instruction type for group (wrong shape)"
        end
      else INR "incorrect instruction type for group"
  | IUngroup ψ_inner =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match ψ with
        | InstrT [a] τs =>
            match a with
            | ProdT κ τs' =>
                if list_beq type type_beq τs τs'
                then has_instruction_type_ok_checker F ψ L
                else INR "incorrect instruction type for ungroup"
            | _ => INR "incorrect instruction type for ungroup (wrong shape)"
            end
        | _ => INR "incorrect instruction type for ungroup (wrong shape)"
        end
      else INR "incorrect instruction type for ungroup"
  | IFold ψ_inner =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match ψ with
        | InstrT [τ0] [a] =>
            match a with
            | RecT κ τ =>
                if type_beq τ0 (subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ)
                then has_instruction_type_ok_checker F ψ L
                else INR "incorrect instruction type for fold"
            | _ => INR "incorrect instruction type for fold (wrong shape)"
            end
        | _ => INR "incorrect instruction type for fold (wrong shape)"
        end
      else INR "incorrect instruction type for fold"
  | IUnfold ψ_inner =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match ψ with
        | InstrT [a] [τ0] =>
            match a with
            | RecT κ τ =>
                if type_beq τ0 (subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ)
                then has_instruction_type_ok_checker F ψ L
                else INR "incorrect instruction type for unfold"
            | _ => INR "incorrect instruction type for unfold (wrong shape)"
            end
        | _ => INR "incorrect instruction type for unfold (wrong shape)"
        end
      else INR "incorrect instruction type for unfold"
  | IPack ψ_inner =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match ψ with
        | InstrT [τ] [τ'] =>
            match packed_existential_checker F τ τ' with
            | inl () => has_instruction_type_ok_checker F ψ L
            | err => err
            end
        | _ => INR "incorrect instruction type for pack"
        end
      else INR "incorrect instruction type for pack"
  | IUnpack ψ_inner L_inner es => INR "incomplete"
  | ITag ψ_inner =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match ψ with
        | InstrT [a] [b] =>
            if andb (type_beq a type_i32) (type_beq b type_i31)
            then has_instruction_type_ok_checker F ψ L
            else INR "incorrect instruction type for tag"
        | _ => INR "incorrect instruction type for tag (wrong shape)"
        end
      else INR "incorrect instruction type for tag"
  | IUntag ψ_inner =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match ψ with
        | InstrT [b] [a] =>
            if andb (type_beq a type_i32) (type_beq b type_i31)
            then has_instruction_type_ok_checker F ψ L
            else INR "incorrect instruction type for untag"
        | _ => INR "incorrect instruction type for untag (wrong shape)"
        end
      else INR "incorrect instruction type for untag"
  | ICast ψ_inner =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match ψ with
        | InstrT [τ] [τ'] =>
            match type_eq_checker F τ τ' with
            | inl () => has_instruction_type_ok_checker F ψ L
            | err => err
            end
        | _ => INR "incorrect instruction type for cast (wrong shape)"
        end
      else INR "incorrect instruction type for cast"
  | INew ψ_inner =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match ψ with
        | InstrT [τ] [a] =>
            match a with
            | RefT κ μ (SerT κser τ') =>
                if type_beq τ τ'
                then
                  match mono_mem_checker μ with
                  | inl () => has_instruction_type_ok_checker F ψ L
                  | err => err
                  end
                else INR "incorrect instruction type for new"
            | _ => INR "incorrect instruction type for new (wrong shape)"
            end
        | _ => INR "incorrect instruction type for new (wrong shape)"
        end
      else INR "incorrect instruction type for new"
  | ILoad ψ_inner π cm => (* note this will be both TLoadCopy and TLoadMove *)
      INR "incomplete"
  | IStore ψ_inner π => (* note this will be both TStoreWeak and TStoreStrong *)
      INR "incomplete"
  | TSwap ψ_inner π =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then INR "incomplete"
      else INR "incorrect instruction type for swap"
  | _ => INR "incomplete"
  end.
(*
with have_instruction_type_checker
    (M:module_ctx) (F:function_ctx) (L:local_ctx)
    (insts:list instruction) (ψ:instruction_type) (L':local_ctx) {struct insts} : type_checker_res :=
  match insts with
  | [] =>
      if andb (instruction_type_beq ψ (InstrT [] [])) (local_ctx_beq L L')
      then local_ctx_ok_checker F L
      else INR "bad empty instructions type"
  (*| [e] => has_instruction_type_checker M F L e ψ L'*)
  | e :: es => (* NOTE THIS IS FUNDAMENTALLY INCORRECT!!! THIS IS TEMPORARY FOR STRUCTURE *)
      match has_instruction_type_checker M F L e ψ L' with
      | inl () => have_instruction_type_checker M F L es ψ L'
      | err => err
      end
  end.
  *)
Ltac my_auto5 :=
  match goal with
  | H: ((match ?key with |_=>_ end) = _) |- _ => destruct key eqn:?HMatch; try inversion H; simpl in *
  | H:((if ?key then _ else _)=_) |- _ => destruct key eqn:?HMatch; try inversion H; simpl in *
  | H: (kind_beq _ _ = true) |- _ => apply kind_eq_convert in H; subst; auto
  | o:ok |- _ => stupid_unit o
  | H: ok_term = ok_term |- _ => clear H
  | H: (andb _ _ = true) |- _ => apply andb_prop in H; destruct H as [?H1 ?H2]
  | H: (_ && _ = true) |- _ => apply andb_prop in H; destruct H as [?H1 ?H2]
  | H: true = false |- _ => inversion H
  | H: false = true |- _ => inversion H
  | H: (instruction_type_beq _ _ = true) |- _ => apply instruction_type_eq_convert in H; subst; auto
  | H: (local_ctx_beq _ _ = true) |- _ => apply local_ctx_eq_convert in H; subst; auto
  | H: (representation_beq _ _ = true) |- _ => apply representation_eq_convert in H; subst; auto
  | H: (dropability_beq _ _ = true) |- _ => apply dropability_eq_convert in H; subst; auto
  | H: (copyability_beq _ _ = true) |- _ => apply copyability_eq_convert in H; subst; auto
  | H: (size_beq _ _ = true) |- _ => apply size_eq_convert in H; subst; auto
  | H: (function_type_beq _ _ = true) |- _ => apply function_type_eq_convert in H; subst; auto
  | H: (type_beq _ _ = true) |- _ => apply type_eq_convert in H; subst; auto
  | H: (kind_ok_checker _ _ = inl ()) |- _ => apply kind_ok_checker_correct in H; auto
  | H: (kind_ok_checker _ _ = ok_term) |- _ => apply kind_ok_checker_correct in H; auto
  | H: (mem_ok_checker _ _ = inl ()) |- _ => apply mem_ok_checker_correct in H; auto
  | H: (mem_ok_checker _ _ = ok_term) |- _ => apply mem_ok_checker_correct in H; auto
  | H: (rep_ok_checker _ _ = inl ()) |- _ => apply rep_ok_checker_correct in H; auto
  | H: (rep_ok_checker _ _ = ok_term) |- _ => apply rep_ok_checker_correct in H; auto
  | H: (size_ok_checker _ _ = inl ()) |- _ => apply size_ok_checker_correct in H; auto
  | H: (size_ok_checker _ _ = ok_term) |- _ => apply size_ok_checker_correct in H; auto
  | H: (type_ok_checker _ _ = inl ()) |- _ => apply type_ok_checker_correct in H; auto
  | H: (type_ok_checker _ _ = ok_term) |- _ => apply type_ok_checker_correct in H; auto
  | H: (function_type_ok_checker _ _ = inl ()) |- _ => apply function_type_ok_checker_correct in H; auto
  | H: (function_type_ok_checker _ _ = ok_term) |- _ => apply function_type_ok_checker_correct in H; auto
  | H: (has_kind_checker _ _ _ = inl ()) |- _ => apply has_kind_checker_correct in H; auto
  | H: (has_kind_checker _ _ _ = ok_term) |- _ => apply has_kind_checker_correct in H; auto
  | H: (has_instruction_type_ok_checker _ _ _ = ok_term) |- _ => apply has_instruction_type_ok_checker_correct in H; auto
  | H: (has_instruction_type_ok_checker _ _ _ = inl ()) |- _ => apply has_instruction_type_ok_checker_correct in H; auto
  | H: (has_instruction_type_num_checker _ _ = ok_term) |- _ => apply has_instruction_type_num_checker_correct in H; auto
  | H: (has_instruction_type_num_checker _ _ = inl ()) |- _ => apply has_instruction_type_num_checker_correct in H; auto
  | H: (has_copyability_checker _ _ _ = ok_term) |- _ => apply has_copyability_checker_correct in H; auto
  | H: (has_copyability_checker _ _ _ = inl ()) |- _ => apply has_copyability_checker_correct in H; auto
  | H: (check_if_subkind _ _ = inl ()) |- _ =>
      try( by (eapply check_if_subkind_works_with_has_kind; try constructor; auto))
  | H: (check_if_subkind _ _ = ok_term) |- _ =>
      try( by (eapply check_if_subkind_works_with_has_kind; try constructor; auto))
end.


Lemma has_instruction_type_checker_correct :
  ∀ M F L inst ψ L',
    has_instruction_type_checker M F L inst ψ L' = ok_term ->
    has_instruction_type M F L inst ψ L'.
Proof.
  intros.
  destruct inst.
  - (* nop, using destruct inst, without have_instruction_type *)
    unfold has_instruction_type_checker in H.
    repeat my_auto5. by constructor.
  - (* unreachable, using destruct inst, without have-instruction_type*)
    unfold has_instruction_type_checker in H; repeat my_auto5; by constructor.
  - (* copy, using destruct inst, without have_instruction_type *)
    unfold has_instruction_type_checker in H; repeat my_auto5; by constructor.
  - (* drop, using destruct inst, without have_instruction_type *)
    unfold has_instruction_type_checker in H; repeat my_auto5; by constructor.
  - (* num, using destruct inst, withut have_instruction_type *)
    unfold has_instruction_type_checker in H; repeat my_auto5; by constructor.
  - (* numconst, using destruct inst, without have_instruction_type *)
    unfold has_instruction_type_checker in H; repeat my_auto5.
    apply has_num_type_type_correct in HMatch4. destruct HMatch4 as [ν HMatch4]; subst.
    by constructor.
  - admit.
  - admit.
  - Opaque have_instruction_type_checker.
    unfold has_instruction_type_checker in H; repeat my_auto5.
Admitted.

Definition has_function_type_checker
    (M:module_ctx) (mf:module_function) (ft:function_type) : type_checker_res :=
  INR "incomplete".
Lemma has_function_type_checker_correct :
  ∀ M mf ft, has_function_type_checker M mf ft = ok_term ->
             has_function_type M mf ft.
Proof. Admitted.

Definition has_module_type_checker (m:module) (mt:module_type) : type_checker_res :=
  INR "incomplete".
Lemma has_module_type_checker_correct :
  ∀ m mt, has_module_type_checker m mt = ok_term -> has_module_type m mt.
Proof. Admitted.
