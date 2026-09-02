Require Import RecordUpdate.RecordUpdate.
From stdpp Require Import base list.
From ExtLib Require Import Traversable.
From Stdlib.Strings Require Import String.

From mathcomp Require Import ssrfun ssrbool eqtype.
Require Import RichWasm.wasm.common.

From RichWasm Require Import layout syntax typing util.
From RichWasm.iris.logrel.instr Require Import kinding.
Set Bullet Behavior "Strict Subproofs".


Ltac clear_nils :=
    repeat rewrite <- ?app_assoc, -> ?app_nil_l, -> ?app_nil_r in *.

Inductive type_error :=
| NormalError: string -> type_error
| FrameError: string -> instruction_type -> instruction_type -> type_error
| LocalCtxSynthError: string -> local_ctx -> local_ctx -> list type_error -> type_error
| HasKindError: string -> list type_error -> type_error
.
Definition ok := unit.
Definition type_checker_res := sum ok (list type_error).

Definition ok_term : type_checker_res := inl ().
Definition INR (s:string) : type_checker_res := inr [(NormalError s)].

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

Lemma convert_foldr_to_Forall_check_ok
  {In: Type} (func : In -> type_checker_res) (Pbool : In -> Prop) (l : list In) :
  foldr (λ i, andb (check_ok (func) i)) true l = true ->
  (forall i, func i = ok_term -> Pbool i) ->
  Forall Pbool l.
Proof.
  generalize dependent l.
  induction l.
  - cbn. done.
  - intros Hfold.
    cbn in Hfold.
    apply andb_prop in Hfold; destruct Hfold as [?H1 ?H2].
    intros Hpbool.
    apply IHl in H2; try done.
    constructor; try done.
    eapply equal_okterm_to_checkok; try done.
    exact (Hpbool a).

Qed.


(** TACTICS **)
Ltac solve_Forall_foldr HForall Hfoldr checker proper :=
  apply (Forall_impl _ (λ x, check_ok checker x = true -> proper x)) in HForall;
  [ eapply Forall_foldr_bool_to_prop; [apply HForall | apply Hfoldr] |
    ( (by apply equal_okterm_to_checkok) ||
      (intros; eapply equal_okterm_to_checkok; [ | eassumption ]; auto)) ].

Ltac destruct_on_if_equal resname :=
  match goal with
    | H:((if ?key then _ else _)=_) |- _ => destruct key eqn:resname
  end.

Ltac stupid_unit o :=
  unfold ok in o; assert (HO: o = tt) by (by destruct o); subst.


Ltac structural_auto :=
   match goal with
  | H: (_ && _ = true) |- _ => apply andb_prop in H; destruct H as [?H1 ?H2]
  | o:ok |- _ => stupid_unit o
  | H: ok_term = ok_term |- _ => clear H
  | H: (andb _ _ = true) |- _ => apply andb_prop in H; destruct H as [?H1 ?H2]
  | H: true = false |- _ => inversion H
  | H: false = true |- _ => inversion H
  | H: ((match ?key with |_=>_ end) = _) |- _ => destruct key eqn:?HMatch; try inversion H; simpl in *
  | H:((if ?key then _ else _)=_) |- _ => destruct key eqn:?HMatch; try (inversion H; [idtac]; clear H); simpl in *
   end.




(** BOOLEAN EQUALITIES **)
(*
Scheme Equality for copyability.
Scheme Equality for dropability.*)

(*
Lemma copyability_eq_convert :
  ∀ c1 c2, copyability_beq c1 c2 = true <-> c1 = c2.
Proof.
  split; intros;
    [by apply internal_copyability_dec_bl in H | by apply internal_copyability_dec_lb in H].
Qed.
Lemma dropability_eq_convert :
  ∀ d1 d2, dropability_beq d1 d2 = true <-> d1 = d2.
Proof.
  split; intros;
   [by apply internal_dropability_dec_bl in H | by apply internal_dropability_dec_lb in H].
Qed.
*)
Lemma num_instruction_eq_convert :
  ∀ n1 n2, num_instruction_beq n1 n2 = true <-> n1 = n2.
Proof.
  split; intros;
    [by apply internal_num_instruction_dec_bl in H | by apply internal_num_instruction_dec_lb in H].
Qed.

Lemma ref_flag_eq_convert :
  ∀ ξ1 ξ2, ref_flag_beq ξ1 ξ2 = true <-> ξ1 = ξ2.
Proof.
  split; intros;
    [by apply internal_ref_flag_dec_bl in H | by apply internal_ref_flag_dec_lb in H].
Qed.


Ltac inner_solve Thing :=
  destruct Thing; [left; by f_equal | right; intros contra; by inversion contra].
Ltac list_solve Thing ListThing :=
  destruct Thing, ListThing;
  [(left; f_equal; done) | | | ];
  (right; intros contra; inversion contra; done).
Ltac double_thing Thing ListThing :=
  destruct Thing, ListThing;
  [(left; f_equal; done) | | | ];
  (right; intros contra; inversion contra; done).
Ltac triple_thing Thing Thing2 Thing3 :=
  destruct Thing, Thing2, Thing3;
  [(left; f_equal; done) | | | | | | | ];
  (right; intros contra; inversion contra; done).
Ltac quad_thing Thing Thing2 Thing3 Thing4 :=
  destruct Thing, Thing2, Thing3, Thing4;
  [(left; f_equal; done) | | | | | | | | | | | | | | | ];
  (right; intros contra; inversion contra; done).

Fixpoint rep_eq_dec (r1 r2 : representation) {struct r1} : {r1 = r2} + {r1 <> r2} :=
  let fix rep_eq_dec_list (lr1 lr2 : list representation) : {lr1 = lr2} + {lr1 <> lr2} :=
    match lr1, lr2 with
    | r1::lr1, r2::lr2 => ltac:(list_solve (rep_eq_dec r1 r2) (rep_eq_dec_list lr1 lr2))
    | [], [] => ltac:(left; done)
    | _, _ => ltac:(right; done)
    end in
  match r1, r2 with
  | VarR i1, VarR i2 => ltac:(inner_solve (Nat.eq_dec i1 i2))
  | SumR rs1, SumR rs2 => ltac:(inner_solve (rep_eq_dec_list rs1 rs2))
  | ProdR rs1, ProdR rs2 => ltac:(inner_solve (rep_eq_dec_list rs1 rs2))
  | AtomR o1, AtomR o2 => ltac:(inner_solve (atomic_rep_eq_dec o1 o2))
  | _, _ => ltac:(right; done)
  end.

Definition representation_eqb r1 r2 : bool := rep_eq_dec r1 r2.
Definition eqrepresentation_typeP : Equality.axiom representation_eqb :=
  eq_dec_Equality_axiom rep_eq_dec.

Definition representation_beq (r1:representation) (r2:representation) :=
  representation_eqb r1 r2.

Lemma representation_eq_convert :
  ∀ r1 r2, representation_beq r1 r2 = true <-> r1 = r2.
Proof.
  pose proof eqrepresentation_typeP.
  intros r1 r2.
  specialize (X r1 r2).
  symmetry.
  by apply reflect_iff.
Qed.

Fixpoint size_eq_dec (s1 s2 : size) {struct s1} : {s1 = s2} + {s1 <> s2} :=
  let fix size_eq_dec_list (lr1 lr2 : list size) : {lr1 = lr2} + {lr1 <> lr2} :=
    match lr1, lr2 with
    | r1::lr1, r2::lr2 => ltac:(list_solve (size_eq_dec r1 r2) (size_eq_dec_list lr1 lr2))
    | [], [] => ltac:(left; done)
    | _, _ => ltac:(right; done)
    end in
  match s1, s2 with
  | VarS i1, VarS i2 => ltac:(inner_solve (Nat.eq_dec i1 i2))
  | SumS rs1, SumS rs2 => ltac:(inner_solve (size_eq_dec_list rs1 rs2))
  | ProdS rs1, ProdS rs2 => ltac:(inner_solve (size_eq_dec_list rs1 rs2))
  | RepS rs1, RepS rs2 => ltac:(inner_solve (rep_eq_dec rs1 rs2))
  | ConstS i1, ConstS i2 => ltac:(inner_solve (Nat.eq_dec i1 i2))
  | _, _ => ltac:(right; done)
  end.

Definition size_beq (s1:size) (s2:size) : bool := size_eq_dec s1 s2.
Definition eqsize_typeP : Equality.axiom size_beq :=
  eq_dec_Equality_axiom size_eq_dec.

Lemma size_eq_convert :
  ∀ s1 s2, size_beq s1 s2 = true <-> s1 = s2.
Proof.
  pose proof eqsize_typeP.
  intros r1 r2.
  specialize (X r1 r2).
  symmetry.
  by apply reflect_iff.
Qed.

Fixpoint kind_beq (k1:kind) (k2:kind) : bool :=
  match k1, k2 with
  | VALTYPE r1 ξ1, VALTYPE r2 ξ2 =>
      andb (representation_beq r1 r2) (ref_flag_beq ξ1 ξ2)
  | MEMTYPE s1 ξ1, MEMTYPE s2 ξ2 =>
      andb (size_beq s1 s2) (ref_flag_beq ξ1 ξ2)
  | _, _ => false
  end.

Lemma kind_eq_convert :
  ∀ k1 k2, kind_beq k1 k2 = true <-> k1 = k2.
Proof.
  split.
  - intros. destruct k1, k2; simpl in H; try inversion H; clear H1; repeat structural_auto.
    * apply representation_eq_convert in H1.
      apply ref_flag_eq_convert in H2.
      subst; auto.
    * apply size_eq_convert in H1.
      apply ref_flag_eq_convert in H2.
      subst; auto.
  - intros; subst. destruct k2; simpl.
    * apply andb_true_intro; split; [|].
      + assert (H:r=r) by auto. apply representation_eq_convert in H. auto.
      + assert (H:r0=r0) by auto. apply internal_ref_flag_dec_lb in H. auto.
    * apply andb_true_intro; split.
      + assert (H:s=s) by auto. apply size_eq_convert in H; auto.
      + assert (H:r=r) by auto. apply internal_ref_flag_dec_lb in H; auto.
Qed.

Lemma kind_neq_convert :
  ∀ k1 k2, kind_beq k1 k2 = false <-> k1 <> k2.
Proof.
  pose proof kind_eq_convert.
  intros k1 k2; specialize (H k1 k2).
  split; intros.
  - intros contra; apply H in contra. rewrite H0 in contra; done.
  - apply Is_true_false_1.
    intros contra.
    rewrite Is_true_true in contra.
    apply H in contra; rewrite contra in H0; done.
  (* there's some decidability lemmas that would need to be done. This is fine to leave. *)
Qed.

Lemma kind_eq_dec (k1 k2 : kind) : {k1 = k2} + {k1 <> k2}.
Proof.
  destruct (kind_beq k1 k2) eqn:H.
  - apply kind_eq_convert in H; left; done.
  - apply kind_neq_convert in H; right; done.
Qed.


Lemma num_type_eq_convert :
  ∀ nt1 nt2, num_type_beq nt1 nt2 = true <-> nt1 = nt2.
Proof.
  split; intros;
    [by apply internal_num_type_dec_bl in H | by apply internal_num_type_dec_lb in H].
Qed.

Fixpoint type_eq_dec (τ1 τ2 : type) {struct τ1} : {τ1 = τ2} + {τ1 <> τ2} :=
  let fix type_eq_dec_list (lr1 lr2 : list type) : {lr1 = lr2} + {lr1 <> lr2} :=
    match lr1, lr2 with
    | r1::lr1, r2::lr2 => ltac:(list_solve (type_eq_dec r1 r2) (type_eq_dec_list lr1 lr2))
    | [], [] => ltac:(left; done)
    | _, _ => ltac:(right; done)
    end in
  match τ1, τ2 with
  | VarT i1, VarT i2 => ltac:(inner_solve (Nat.eq_dec i1 i2))
  | I31T κ1, I31T κ2 => ltac:(inner_solve (kind_eq_dec κ1 κ2))
  | NumT κ1 nt1, NumT κ2 nt2 =>
      ltac:(double_thing (kind_eq_dec κ1 κ2) (num_type_eq_dec nt1 nt2))
  | SumT κ1 τs1, SumT κ2 τs2
  | VariantT κ1 τs1, VariantT κ2 τs2
  | ProdT κ1 τs1, ProdT κ2 τs2
  | StructT κ1 τs1, StructT κ2 τs2 =>
      ltac:(double_thing (kind_eq_dec κ1 κ2) (type_eq_dec_list τs1 τs2))
  | RefT κ1 μ1 β1 τ1, RefT κ2 μ2 β2 τ2 =>
      ltac:(quad_thing (kind_eq_dec κ1 κ2) (memory_eq_dec μ1 μ2) (mutability_eq_dec β1 β2) (type_eq_dec τ1 τ2))
  | CodeRefT κ1 ft1, CodeRefT κ2 ft2 =>
      ltac:(double_thing (kind_eq_dec κ1 κ2) (function_type_eq_dec ft1 ft2))
  | SerT κ1 t1, SerT κ2 t2 =>
      ltac:(double_thing (kind_eq_dec κ1 κ2) (type_eq_dec t1 t2))
  | PlugT κ1 ρ1, PlugT κ2 ρ2 =>
      ltac:(double_thing (kind_eq_dec κ1 κ2) (rep_eq_dec ρ1 ρ2))
  | SpanT κ1 σ1, SpanT κ2 σ2 =>
      ltac:(double_thing (kind_eq_dec κ1 κ2) (size_eq_dec σ1 σ2))
  | RecT κ1 t1, RecT κ2 t2
  | ExistsMemT κ1 t1, ExistsMemT κ2 t2
  | ExistsRepT κ1 t1, ExistsRepT κ2 t2
  | ExistsSizeT κ1 t1, ExistsSizeT κ2 t2 =>
      ltac:(double_thing (kind_eq_dec κ1 κ2) (type_eq_dec t1 t2))
  | ExistsTypeT κ11 κ12 t1, ExistsTypeT κ21 κ22 t2 =>
      ltac:(triple_thing (kind_eq_dec κ11 κ21) (kind_eq_dec κ12 κ22) (type_eq_dec t1 t2))
  | _, _ => ltac:(right; done)
  end
with inner_function_type_eq_dec (fτ1:inner_function_type) (fτ2:inner_function_type) : {fτ1 = fτ2} + {fτ1 <> fτ2} :=
  let fix type_eq_dec_list (lr1 lr2 : list type) : {lr1 = lr2} + {lr1 <> lr2} :=
    match lr1, lr2 with
    | r1::lr1, r2::lr2 => ltac:(list_solve (type_eq_dec r1 r2) (type_eq_dec_list lr1 lr2))
    | [], [] => ltac:(left; done)
    | _, _ => ltac:(right; done)
    end in
  match fτ1, fτ2 with
  | MonoFunT τs11 τs12, MonoFunT τs21 τs22 =>
      ltac:(double_thing (type_eq_dec_list τs11 τs21) (type_eq_dec_list τs12 τs22))
  | ForallTypeT κ1 ft1, ForallTypeT κ2 ft2 =>
      ltac:(double_thing (kind_eq_dec κ1 κ2) (inner_function_type_eq_dec ft1 ft2))
  | _, _ => ltac:(right; done)
  end
with function_type_eq_dec (fτ1:function_type) (fτ2:function_type) : {fτ1 = fτ2} + {fτ1 <> fτ2} :=
  match fτ1, fτ2 with
  | InnerFunT ft1', InnerFunT ft2' =>
      ltac:(inner_solve (inner_function_type_eq_dec ft1' ft2'))
  | ForallMemT ft1, ForallMemT ft2
  | ForallRepT ft1, ForallRepT ft2
  | ForallSizeT ft1, ForallSizeT ft2 => ltac:(inner_solve (function_type_eq_dec ft1 ft2))
  | _, _ => ltac:(right; done)
  end.


Definition type_beq (s1:type) (s2:type) : bool := type_eq_dec s1 s2.
Definition eqtype_typeP : Equality.axiom type_beq :=
  eq_dec_Equality_axiom type_eq_dec.

Definition inner_function_type_beq (s1:inner_function_type) (s2:inner_function_type) : bool := inner_function_type_eq_dec s1 s2.
Definition eqinner_function_type_typeP : Equality.axiom inner_function_type_beq :=
  eq_dec_Equality_axiom inner_function_type_eq_dec.

Definition function_type_beq (s1:function_type) (s2:function_type) : bool := function_type_eq_dec s1 s2.
Definition eqfunction_type_typeP : Equality.axiom function_type_beq :=
  eq_dec_Equality_axiom function_type_eq_dec.

Lemma type_eq_convert :
  ∀ τ1 τ2, type_beq τ1 τ2 = true <-> τ1 = τ2.
Proof.
  pose proof eqtype_typeP.
  intros r1 r2.
  specialize (X r1 r2).
  symmetry.
  by apply reflect_iff.
Qed.

Lemma function_type_eq_convert :
  ∀ ft1 ft2, function_type_beq ft1 ft2 = true <-> ft1 = ft2.
Proof.
  pose proof eqfunction_type_typeP.
  intros r1 r2.
  specialize (X r1 r2).
  symmetry.
  by apply reflect_iff.
Qed.

Lemma inner_function_type_eq_convert :
  ∀ ft1 ft2, inner_function_type_beq ft1 ft2 = true <-> ft1 = ft2.
Proof.
  pose proof eqinner_function_type_typeP.
  intros r1 r2.
  specialize (X r1 r2).
  symmetry.
  by apply reflect_iff.
Qed.


Lemma mutability_eq_convert :
  ∀ τ1 τ2, mutability_beq τ1 τ2 = true <-> τ1 = τ2.
Proof.
  split; intros;
    [by apply internal_mutability_dec_bl in H | by apply internal_mutability_dec_lb in H].
Qed.

Lemma memory_eq_convert :
  ∀ m1 m2, memory_beq m1 m2 = true <-> m1 = m2.
Proof.
   split; intros;
    [by apply internal_memory_dec_bl in H | by apply internal_memory_dec_lb in H].
Qed.

(* I'm bad at everything so monomorphic *)
Lemma list_eq_convert_type :
  ∀ τs1 τs2, list_beq type type_beq τs1 τs2 = true <-> τs1 = τs2.
Proof.
  pose proof type_eq_convert.
  assert (∀ τ1 τ2, type_beq τ1 τ2 = true -> τ1 = τ2) by apply H.
  assert (∀ τ1 τ2, τ1 = τ2 -> type_beq τ1 τ2 = true) by apply H. clear H.
  intros *; split; intros.
  - pose proof (internal_list_dec_bl type type_beq H0 τs1 τs2).
    auto.
  - pose proof (internal_list_dec_lb type type_beq H1 τs1 τs2).
    auto.
Qed.
Lemma list_eq_convert_function_type :
  ∀ τs1 τs2, list_beq function_type function_type_beq τs1 τs2 = true <-> τs1 = τs2.
Proof.
  pose proof function_type_eq_convert.
  assert (∀ τ1 τ2, function_type_beq τ1 τ2 = true -> τ1 = τ2) by apply H.
  assert (∀ τ1 τ2, τ1 = τ2 -> function_type_beq τ1 τ2 = true) by apply H. clear H.
  intros *; split; intros.
  - pose proof (internal_list_dec_bl function_type function_type_beq H0 τs1 τs2).
    auto.
  - pose proof (internal_list_dec_lb function_type function_type_beq H1 τs1 τs2).
    auto.
Qed.
Lemma list_eq_convert_kind :
  ∀ τs1 τs2, list_beq kind kind_beq τs1 τs2 = true <-> τs1 = τs2.
Proof.
  pose proof kind_eq_convert.
  assert (∀ τ1 τ2, kind_beq τ1 τ2 = true -> τ1 = τ2) by apply H.
  assert (∀ τ1 τ2, τ1 = τ2 -> kind_beq τ1 τ2 = true) by apply H. clear H.
  intros *; split; intros.
  - pose proof (internal_list_dec_bl kind kind_beq H0 τs1 τs2).
    auto.
  - pose proof (internal_list_dec_lb kind kind_beq H1 τs1 τs2).
    auto.
Qed.
Lemma list_eq_convert_primitive :
  ∀ τs1 τs2, list_beq primitive primitive_beq τs1 τs2 = true <-> τs1 = τs2.
Proof.
  intros *; split; intros.
  - pose proof (internal_list_dec_bl primitive primitive_beq internal_primitive_dec_bl τs1 τs2).
    auto.
  - pose proof (internal_list_dec_lb primitive primitive_beq internal_primitive_dec_lb τs1 τs2).
    auto.
Qed.
Lemma list_eq_convert_representation :
  ∀ τs1 τs2, list_beq representation representation_beq τs1 τs2 = true <-> τs1 = τs2.
Proof.
  pose proof representation_eq_convert.
  assert (∀ τ1 τ2, representation_beq τ1 τ2 = true -> τ1 = τ2) by apply H.
  assert (∀ τ1 τ2, τ1 = τ2 -> representation_beq τ1 τ2 = true) by apply H. clear H.
  intros *; split; intros.
  - pose proof (internal_list_dec_bl representation representation_beq H0 τs1 τs2).
    auto.
  - pose proof (internal_list_dec_lb representation representation_beq H1 τs1 τs2).
    auto.
Qed.
Lemma list_eq_convert_size :
  ∀ τs1 τs2, list_beq size size_beq τs1 τs2 = true <-> τs1 = τs2.
Proof.
  pose proof size_eq_convert.
  assert (∀ τ1 τ2, size_beq τ1 τ2 = true -> τ1 = τ2) by apply H.
  assert (∀ τ1 τ2, τ1 = τ2 -> size_beq τ1 τ2 = true) by apply H. clear H.
  intros *; split; intros.
  - pose proof (internal_list_dec_bl size size_beq H0 τs1 τs2).
    auto.
  - pose proof (internal_list_dec_lb size size_beq H1 τs1 τs2).
    auto.
Qed.
Lemma list_eq_convert_list_primitive :
  ∀ l1 l2, list_beq (list primitive) (list_beq primitive primitive_beq) l1 l2 = true <-> l1 = l2.
Proof.
  pose proof list_eq_convert_primitive.
  assert (∀ τ1 τ2, list_beq primitive primitive_beq τ1 τ2 = true -> τ1 = τ2) by apply H.
  assert (∀ τ1 τ2, τ1 = τ2 -> list_beq primitive primitive_beq τ1 τ2 = true) by apply H. clear H.
  intros *; split; intros.
  - pose proof (internal_list_dec_bl (list primitive) (list_beq primitive primitive_beq) H0 l1 l2).
    auto.
  - pose proof (internal_list_dec_lb (list primitive) (list_beq primitive primitive_beq) H1 l1 l2).
    auto.
Qed.

Definition local_ctx_beq (L L':local_ctx) : bool := list_beq type type_beq L L'.
Lemma local_ctx_eq_convert :
  ∀ L L', local_ctx_beq L L' = true <-> L = L'.
Proof.
  split; intros; unfold local_ctx_beq in *.
  - apply list_eq_convert_type in H; subst; auto.
  - subst; apply list_eq_convert_type; auto.
Qed.
Definition module_type_beq (m1:module_type) (m2:module_type) : bool :=
  andb (list_beq function_type function_type_beq m1.(mt_imports) m2.(mt_imports))
       (list_beq function_type function_type_beq m1.(mt_exports) m2.(mt_exports)).
Lemma module_type_eq_convert :
  ∀ m1 m2, module_type_beq m1 m2 = true <-> m1 = m2.
Proof.
  pose proof list_eq_convert_function_type as HH.
  split; intros.
  - destruct m1, m2.
    unfold module_type_beq in H; cbn in H.
    repeat structural_auto.
    apply HH in H1; apply HH in H2. subst.
    done.
  - subst.
    destruct m2.
    unfold module_type_beq. cbn.
    assert (mt_imports = mt_imports) by done.
    assert (mt_exports = mt_exports) by done.
    apply HH in H; apply HH in H0.
    apply andb_true_intro. split; done.
Qed.

Definition instruction_type_beq (inst1 inst2:instruction_type) : bool :=
  match inst1, inst2 with
  | InstrT τs11 τs12, InstrT τs21 τs22 =>
      andb (list_beq type type_beq τs11 τs21) (list_beq type type_beq τs12 τs22)
  end.
Lemma instruction_type_eq_convert :
  ∀ inst1 inst2, instruction_type_beq inst1 inst2 = true <-> inst1 = inst2.
Proof.
  split; intros; destruct inst1, inst2; unfold instruction_type_beq in *; simpl in *.
  - repeat structural_auto. apply list_eq_convert_type in H1, H2. subst; auto.
  - inversion H; subst.
    apply andb_true_intro; split; apply list_eq_convert_type; auto.
Qed.
Lemma instruction_type_eq_dec (ϕ1 ϕ2 : instruction_type) : {ϕ1 = ϕ2} + {ϕ1 <> ϕ2}.
Proof.
  destruct (instruction_type_beq ϕ1 ϕ2) eqn:H.
  - apply instruction_type_eq_convert in H. left; done.
  - right. intros contra. apply instruction_type_eq_convert in contra. rewrite H in contra; done.
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
    repeat structural_auto.
    apply list_eq_convert_type in H1.
    apply type_eq_convert in H0, H2.
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

Definition kind_ctx_beq ah1 ah2 : bool :=
  (ah1.(kc_mem_vars) =? ah2.(kc_mem_vars)) &&
  (ah1.(kc_rep_vars) =? ah2.(kc_rep_vars)) &&
  (ah1.(kc_size_vars) =? ah2.(kc_size_vars)).
Lemma kind_ctx_eq_convert : ∀ ah1 ah2, kind_ctx_beq ah1 ah2 = true <-> ah1 = ah2.
Proof.
  intros ah1 ah2. destruct ah1, ah2. unfold kind_ctx_beq; cbn.
  split.
  - intros H.
    repeat structural_auto.
    apply Nat.eqb_eq in H1, H0, H2. subst. done.
  - intros H; inversion H; subst.
    apply andb_true_intro. split; [apply andb_true_intro; split|].
    all: by apply Nat.eqb_eq.
Qed.

Definition list_type_prod_local_ctx_beq (p1 p2 : (list type * local_ctx)) : bool :=
  let (lt1, L1):=p1 in let (lt2, L2):=p2 in (list_beq type type_beq lt1 lt2) && (local_ctx_beq L1 L2).
Lemma list_type_prod_local_ctx_eq_convert :
  ∀ p1 p2, list_type_prod_local_ctx_beq p1 p2 = true <-> p1 = p2.
Proof.
  intros p1 p2; destruct p1, p2; unfold list_type_prod_local_ctx_beq; cbn.
  split.
  - intros H; repeat structural_auto.
    apply list_eq_convert_type in H1; apply local_ctx_eq_convert in H2; subst; done.
  - intros H; inversion H; subst.
    apply andb_true_intro; split.
    + by apply list_eq_convert_type.
    + by apply local_ctx_eq_convert.
Qed.
Lemma list_eq_convert_list_type_prod_local_ctx :
  ∀ l1 l2, list_beq (list type * local_ctx) list_type_prod_local_ctx_beq l1 l2 = true <-> l1 = l2.
Proof.
  pose proof list_type_prod_local_ctx_eq_convert.
  assert (∀ τ1 τ2, list_type_prod_local_ctx_beq τ1 τ2 = true -> τ1 = τ2) by apply H.
  assert (∀ τ1 τ2, τ1 = τ2 -> list_type_prod_local_ctx_beq τ1 τ2 = true) by apply H. clear H.
  intros *; split; intros.
  - pose proof (internal_list_dec_bl (list type * local_ctx) list_type_prod_local_ctx_beq H0 l1 l2).
    auto.
  - pose proof (internal_list_dec_lb (list type * local_ctx) list_type_prod_local_ctx_beq H1 l1 l2).
    auto.
Qed.

Definition function_ctx_beq F1 F2 : bool :=
  (list_beq type type_beq F1.(fc_return) F2.(fc_return)) &&
  (list_beq (list primitive) (list_beq primitive primitive_beq) F1.(fc_locals) F2.(fc_locals)) &&
  (list_beq (list type * local_ctx) list_type_prod_local_ctx_beq
     F1.(fc_labels) F2.(fc_labels)) &&
  (kind_ctx_beq F1.(fc_kind_ctx) F2.(fc_kind_ctx)) &&
  (list_beq kind kind_beq F1.(fc_type_vars) F2.(fc_type_vars)).

Lemma function_ctx_eq_convert :
  ∀ F1 F2, function_ctx_beq F1 F2 = true <-> F1 = F2.
Proof.
  intros F1 F2; destruct F1, F2; unfold function_ctx_beq; cbn.
  split.
  - intros H; repeat structural_auto.
    apply list_eq_convert_type in H1.
    apply kind_ctx_eq_convert in H0.
    apply list_eq_convert_kind in H2.
    apply list_eq_convert_list_primitive in H4.
    apply list_eq_convert_list_type_prod_local_ctx in H3.
    subst; done.
  - intros H; inversion H; subst. clear H.
    Opaque kind_ctx_beq.
    repeat (apply andb_true_intro; split).
    + by apply list_eq_convert_type.
    + by apply list_eq_convert_list_primitive.
    + by apply list_eq_convert_list_type_prod_local_ctx.
    + by apply kind_ctx_eq_convert.
    + by apply list_eq_convert_kind.
    Transparent kind_ctx_beq.
Qed.

Definition index_eq_dec (ix1 ix2 : index) : {ix1 = ix2} + {ix1 <> ix2} :=
  match ix1, ix2 with
  | MemI m1, MemI m2 => ltac:(inner_solve (memory_eq_dec m1 m2))
  | RepI r1, RepI r2 => ltac:(inner_solve (rep_eq_dec r1 r2))
  | SizeI s1, SizeI s2 => ltac:(inner_solve (size_eq_dec s1 s2))
  | TypeI t1, TypeI t2 => ltac:(inner_solve (type_eq_dec t1 t2))
  | _, _ => ltac:(right; done)
  end.

Definition index_beq (ix1 ix2 : index) : bool := index_eq_dec ix1 ix2.
Definition eqindex_typeP : Equality.axiom index_beq :=
  eq_dec_Equality_axiom index_eq_dec.

Fixpoint instruction_eq_dec (e1 e2 : instruction) : {e1 = e2} + {e1 <> e2} :=
  let fix nat_eq_dec_list (lr1 lr2 : list nat) : {lr1 = lr2} + {lr1 <> lr2} :=
    match lr1, lr2 with
    | r1::lr1, r2::lr2 => ltac:(list_solve (Nat.eq_dec r1 r2) (nat_eq_dec_list lr1 lr2))
    | [], [] => ltac:(left; done)
    | _, _ => ltac:(right; done)
    end in
  let fix index_eq_dec_list (lr1 lr2 : list index) : {lr1 = lr2} + {lr1 <> lr2} :=
    match lr1, lr2 with
    | r1::lr1, r2::lr2 => ltac:(list_solve (index_eq_dec r1 r2) (index_eq_dec_list lr1 lr2))
    | [], [] => ltac:(left; done)
    | _, _ => ltac:(right; done)
    end in
  let fix type_eq_dec_list (lr1 lr2 : list type) : {lr1 = lr2} + {lr1 <> lr2} :=
    match lr1, lr2 with
    | r1::lr1, r2::lr2 => ltac:(list_solve (type_eq_dec r1 r2) (type_eq_dec_list lr1 lr2))
    | [], [] => ltac:(left; done)
    | _, _ => ltac:(right; done)
    end in
  let fix instruction_eq_dec_list (lr1 lr2 : list instruction) : {lr1 = lr2} + {lr1 <> lr2} :=
    match lr1, lr2 with
    | r1::lr1, r2::lr2 => ltac:(list_solve (instruction_eq_dec r1 r2) (instruction_eq_dec_list lr1 lr2))
    | [], [] => ltac:(left; done)
    | _, _ => ltac:(right; done)
    end in
  let fix instruction_list_eq_dec_list (lr1 lr2 : list (list instruction)) : {lr1 = lr2} + {lr1 <> lr2} :=
    match lr1, lr2 with
    | r1::lr1, r2::lr2 => ltac:(list_solve (instruction_eq_dec_list r1 r2) (instruction_list_eq_dec_list lr1 lr2))
    | [], [] => ltac:(left; done)
    | _, _ => ltac:(right; done)
    end in
 match e1, e2 with
 | INop ϕ1, INop ϕ2
 | IUnreachable ϕ1, IUnreachable ϕ2
 | ICopy ϕ1, ICopy ϕ2
 | IDrop ϕ1, IDrop ϕ2
 | IReturn ϕ1, IReturn ϕ2
 | ICallIndirect ϕ1, ICallIndirect ϕ2
 | IGroup ϕ1, IGroup ϕ2
 | IUngroup ϕ1, IUngroup ϕ2
 | IFold ϕ1, IFold ϕ2
 | IUnfold ϕ1, IUnfold ϕ2
 | IPack ϕ1, IPack ϕ2
 | ITag ϕ1, ITag ϕ2
 | IUntag ϕ1, IUntag ϕ2
 | ICast ϕ1, ICast ϕ2
 | INew ϕ1, INew ϕ2
   => ltac:(inner_solve (instruction_type_eq_dec ϕ1 ϕ2))
 | INum ϕ1 n1, INum ϕ2 n2 =>
     ltac:(double_thing (instruction_type_eq_dec ϕ1 ϕ2) (num_instruction_eq_dec n1 n2))
 | INumConst ϕ1 n1, INumConst ϕ2 n2 =>
     ltac:(double_thing (instruction_type_eq_dec ϕ1 ϕ2) (Int.Z_as_Int.eq_dec n1 n2))
 | IBr ϕ1 n1, IBr ϕ2 n2 =>
     ltac:(double_thing (instruction_type_eq_dec ϕ1 ϕ2) (Nat.eq_dec n1 n2))
 | ILocalGet ϕ1 cm1 n1, ILocalGet ϕ2 cm2 n2 =>
     ltac:(triple_thing (instruction_type_eq_dec ϕ1 ϕ2) (consumption_eq_dec cm1 cm2) (Nat.eq_dec n1 n2))
 | ILocalSet ϕ1 n1, ILocalSet ϕ2 n2
 | ICodeRef ϕ1 n1, ICodeRef ϕ2 n2
 | IInject ϕ1 n1, IInject ϕ2 n2
 | IInjectNew ϕ1 n1, IInjectNew ϕ2 n2 =>
     ltac:(double_thing (instruction_type_eq_dec ϕ1 ϕ2) (Nat.eq_dec n1 n2))
 | IUnpack ϕ1 τs1 es1, IUnpack ϕ2 τs2 es2
 | IBlock ϕ1 τs1 es1, IBlock ϕ2 τs2 es2 =>
     ltac:(triple_thing (instruction_type_eq_dec ϕ1 ϕ2) (type_eq_dec_list τs1 τs2) (instruction_eq_dec_list es1 es2))
 | ILoop ϕ1 es1, ILoop ϕ2 es2 =>
     ltac:(double_thing (instruction_type_eq_dec ϕ1 ϕ2) (instruction_eq_dec_list es1 es2))
 | IIte ϕ1 τs1 es11 es12, IIte ϕ2 τs2 es21 es22 =>
     ltac:(quad_thing (instruction_type_eq_dec ϕ1 ϕ2) (type_eq_dec_list τs1 τs2)
             (instruction_eq_dec_list es11 es21) (instruction_eq_dec_list es12 es22) )
 | IInst ϕ1 ix1, IInst ϕ2 ix2 =>
     ltac:(double_thing (instruction_type_eq_dec ϕ1 ϕ2) (index_eq_dec ix1 ix2))
 | ICall ϕ1 n1 ixs1, ICall ϕ2 n2 ixs2 =>
     ltac:(triple_thing (instruction_type_eq_dec ϕ1 ϕ2) (Nat.eq_dec n1 n2) (index_eq_dec_list ixs1 ixs2))
 | ICase ϕ1 τs1 ees1, ICase ϕ2 τs2 ees2 =>
     ltac:(triple_thing (instruction_type_eq_dec ϕ1 ϕ2) (type_eq_dec_list τs1 τs2)
          (instruction_list_eq_dec_list ees1 ees2))
 | ICaseLoad ϕ1 c1 τs1 ees1, ICaseLoad ϕ2 c2 τs2 ees2 =>
     ltac:(quad_thing (instruction_type_eq_dec ϕ1 ϕ2) (type_eq_dec_list τs1 τs2)
          (instruction_list_eq_dec_list ees1 ees2) (consumption_eq_dec c1 c2))
 | ILoad ϕ1 ns1 c1, ILoad ϕ2 ns2 c2 =>
     ltac:(triple_thing (instruction_type_eq_dec ϕ1 ϕ2) (nat_eq_dec_list ns1 ns2) (consumption_eq_dec c1 c2))
 | IStore ϕ1 ns1, IStore ϕ2 ns2
 | ISwap ϕ1 ns1, ISwap ϕ2 ns2 =>
     ltac:(double_thing (instruction_type_eq_dec ϕ1 ϕ2) (nat_eq_dec_list ns1 ns2))
 | _, _ => ltac:(right; done)
 end.

Definition instruction_beq (s1:instruction) (s2:instruction) : bool := instruction_eq_dec s1 s2.
Definition eqinstruction_typeP : Equality.axiom instruction_beq :=
  eq_dec_Equality_axiom instruction_eq_dec.

Lemma instruction_eq_convert :
  ∀ e1 e2, instruction_beq e1 e2 = true <-> e1 = e2.
Proof.
  pose proof eqinstruction_typeP.
  intros r1 r2.
  specialize (X r1 r2).
  symmetry.
  by apply reflect_iff.
Qed.

Lemma list_eq_convert_instruction :
  ∀ es1 es2, list_beq instruction instruction_beq es1 es2 = true <-> es1 = es2.
Proof.
  pose proof instruction_eq_convert.
  assert (∀ τ1 τ2, instruction_beq τ1 τ2 = true -> τ1 = τ2) by apply H.
  assert (∀ τ1 τ2, τ1 = τ2 -> instruction_beq τ1 τ2 = true) by apply H. clear H.
  intros *; split; intros.
  - pose proof (internal_list_dec_bl instruction instruction_beq H0 es1 es2).
    auto.
  - pose proof (internal_list_dec_lb instruction instruction_beq H1 es1 es2).
    auto.
Qed.

Ltac boolean_equality_auto :=
  match goal with
  | H: Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq  in H; subst; auto
  | H: (kind_beq _ _ = true) |- _ => apply kind_eq_convert in H; subst; auto
  | H: (instruction_type_beq _ _ = true) |- _ => apply instruction_type_eq_convert in H; subst; auto
  | H: (local_ctx_beq _ _ = true) |- _ => apply local_ctx_eq_convert in H; subst; auto
  | H: (representation_beq _ _ = true) |- _ => apply representation_eq_convert in H; subst; auto
  | H: (ref_flag_beq _ _ = true) |- _ => apply ref_flag_eq_convert in H; subst; auto
  | H: (size_beq _ _ = true) |- _ => apply size_eq_convert in H; subst; auto
  | H: (function_type_beq _ _ = true) |- _ => apply function_type_eq_convert in H; subst; auto
  | H: (inner_function_type_beq _ _ = true) |- _ => apply inner_function_type_eq_convert in H; subst; auto
  | H: (type_beq _ _ = true) |- _ => apply type_eq_convert in H; subst; auto
  | H: (instruction_type_beq _ _ = true) |- _ => apply instruction_type_eq_convert in H; subst; auto
  | H: (module_type_beq _ _ = true) |- _ => apply module_type_eq_convert in H; subst; auto
  | H: (memory_beq _ _ = true) |- _ => apply memory_eq_convert in H; subst; auto
  | H: (mutability_beq _ _ = true) |- _ => apply mutability_eq_convert in H; subst; auto
  | H: (num_type_beq _ _ = true) |- _ => apply num_type_eq_convert in H; subst; auto
  | H: (path_result_beq _ _ = true) |- _ => apply path_result_eq_convert in H; subst; auto
  | H: (list_beq type type_beq _ _ = true) |- _ => apply list_eq_convert_type in H; subst; auto
  | H: (list_beq size size_beq _ _ = true) |- _ => apply list_eq_convert_size in H; subst; auto
  | H: (list_beq representation representation_beq _ _ = true) |- _ =>
      apply list_eq_convert_representation in H; subst; auto
  | H: (list_beq primitive primitive_beq _ _ = true) |- _ =>
      apply list_eq_convert_primitive in H; subst; auto
  | H: (function_ctx_beq _ _ = true) |- _ => apply function_ctx_eq_convert in H; subst; auto
  | H: (instruction_beq _ _ = true) |- _ => apply instruction_eq_convert in H; subst; auto
  | H: (list_beq instruction instruction_beq _ _ = true) |- _ => apply list_eq_convert_instruction in H; subst; auto
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
    + Opaque split_list_all_last.
      structural_auto. clear H1.
      destruct p. inversion H. subst.
      specialize (IHl l0 last0 ltac:(auto)).
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
  let l1len := Datatypes.length l1 in
  let l2len := Datatypes.length l2 in
  list_suffix_helper l1 l2 l1len l2len.

Lemma list_suffix_helper_same :
  ∀ l, list_suffix_helper l l (Init.Datatypes.length l) (Init.Datatypes.length l) = Some [].
Proof.
  induction l.
  - cbn. done.
  - cbn.
    rewrite Nat.eqb_refl.
    assert (type_beq a a = true). { rewrite type_eq_convert. done. }
    rewrite H.
    assert (list_beq type type_beq l l = true). { rewrite list_eq_convert_type. done. }
    rewrite H0.
    cbn. done.
Qed.

Lemma list_suffix_helper_if_equal :
  ∀ lful lsuf,
    list_suffix_helper lful lsuf (Datatypes.length lful) (Datatypes.length lsuf) = Some []->
    lful = lsuf.
Proof.
  induction lful.
  - cbn. intros lsuf; destruct lsuf; cbn; try done.
  - intros lsuf_big Hbig.
    destruct lsuf_big as [|a2 lsuf]; cbn in Hbig.
    { structural_auto. }
    repeat structural_auto.
    repeat boolean_equality_auto.
Qed.


Lemma list_suffix_add_one :
  forall a lpre lsuf,
    list_suffix (lpre ++ lsuf) lsuf = Some (lpre) ->
    list_suffix (a :: lpre ++ lsuf) lsuf = Some (a :: lpre).
Proof.
  intros * H.
  destruct lsuf.
  - cbn. clear_nils.
    unfold list_suffix in H.
    cbn in H.
    rewrite H.
    done.
  - unfold list_suffix in *; cbn in *.
    rewrite length_app at 1. cbn.
    assert (Datatypes.length lpre + S (Datatypes.length lsuf) =? Datatypes.length lsuf = false). {
      cbn.
      rewrite Nat.eqb_neq.
      lia.
    }
    rewrite H0; cbn.
    rewrite H.
    done.
Qed.


Lemma list_suffix_correct_l :
  ∀ lfull lpre lsuf,
    lfull = lpre ++ lsuf -> list_suffix lfull lsuf = Some lpre.
Proof.
  intros lfull lpre.
  generalize dependent lfull.
  generalize dependent lpre.

  induction lpre.
  - intros lfull lsuf.
    clear_nils.
    intros H; subst.
    unfold list_suffix.
    apply list_suffix_helper_same.
  - intros lfull_big lsuf H.
    change ((?x::?y)++?z) with (x::(y++z)) in *.
    destruct lfull_big as [|a1 lfull]; [inversion H; done| inversion H; subst].
    specialize (IHlpre (lpre ++ lsuf) lsuf ltac:(auto)).
    apply list_suffix_add_one; done.
Qed.

Lemma list_suffix_correct_r :
  ∀ lfull lpre lsuf,
    list_suffix lfull lsuf = Some lpre -> lfull = lpre ++ lsuf.
Proof.
  intros lfull lpre.
  generalize dependent lfull.
  generalize dependent lpre.

  induction lpre.
  - intros lfull lsuf H.
    clear_nils.
    by apply list_suffix_helper_if_equal.
  - intros lfull_big lsuf H.
    change ((?x::?y)++?z) with (x::(y++z)) in *.
    destruct lfull_big as [|a1 lfull]; cbn in *; clear_nils; repeat structural_auto; subst.
    + destruct lsuf; cbn in HMatch1; try (by inversion HMatch1).
      apply IHlpre in HMatch0. clear_nils.
      subst. done.
    + rewrite <- HMatch1 in HMatch0.
      apply IHlpre in HMatch0.
      subst; done.
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
  | RepS ρ => rep_ok_checker k ρ
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
  induction s using size_ind; simpl in H; repeat structural_auto.
  - apply Nat.ltb_lt in HMatch; auto; by constructor.
  - apply OKSumS.
    solve_Forall_foldr H0 HMatch (size_ok_checker k) (size_ok k).
  - apply OKProdS.
    solve_Forall_foldr H0 HMatch (size_ok_checker k) (size_ok k).
  - apply OKRepS. apply rep_ok_checker_correct in H; auto.
  - apply OKConstS.
Qed.


(* kind_ok *)
Definition kind_ok_checker (k:kind_ctx) (ki: kind) : type_checker_res :=
  match ki with
  | (VALTYPE ρ ξ) => rep_ok_checker k ρ
  | MEMTYPE σ ξ => size_ok_checker k σ
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


Fixpoint combine_error_messages (l:list type_checker_res) : list type_error :=
  match l with
  | [] => []
  | r::rs =>
      match r with
      | inl () => combine_error_messages rs
      | inr l' => l' ++ combine_error_messages rs
      end
  end.

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
  | RefT κ μ β τ =>
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
      | inl () => type_ok_checker (add_rep_var F) τ
      | err => err
      end
  | ExistsSizeT κ τ =>
      match (kind_ok_checker (F.(fc_kind_ctx)) κ) with
      | inl () => type_ok_checker (add_size_var F) τ
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
    with inner_function_type_ok_checker (F: function_ctx) (ft:inner_function_type) : type_checker_res :=
      match ft with
      | MonoFunT τs1 τs2 =>
           if (foldr (λ t:type, andb (check_ok (type_ok_checker F) t)) true τs1)
           then
              if (foldr (λ t:type, andb (check_ok (type_ok_checker F) t)) true τs2)
              then ok_term
              (* yes this will redo it twice but I didn't want to mess up the proofs *)
                     (* fix later *)
              else
                let res2 := map (type_ok_checker F) τs2 in
                inr ([NormalError "function type ok error in τs2"] ++ combine_error_messages res2)
                (* INR ("function type ok error in τs2 (" ++ (combine_error_messages res2) ++ ")"%string) *)
           else
             let res1 := map (type_ok_checker F) τs1 in
             inr ([NormalError "function type ok error in τs1"] ++ combine_error_messages res1)
             (* INR ("function type ok error in τs1 (" ++ (combine_error_messages res1) ++ ")"%string) *)
      | ForallTypeT κ ϕ =>
          match (kind_ok_checker (F.(fc_kind_ctx)) κ) with
          | inl () => inner_function_type_ok_checker (F <| fc_type_vars ::= cons κ |>) ϕ
          | err => err
          end
      end
    with function_type_ok_checker (F: function_ctx) (ft:function_type) : type_checker_res :=
      match ft with
      | InnerFunT ϕ => inner_function_type_ok_checker F ϕ
      | ForallMemT ϕ => function_type_ok_checker (F <| fc_kind_ctx ::= set kc_mem_vars S |>) ϕ
      | ForallRepT ϕ => function_type_ok_checker (add_rep_var F) ϕ
      | ForallSizeT ϕ => function_type_ok_checker (add_size_var F) ϕ
      end.

Ltac destruct_match_kind_ok F κ o Hres HMatchKind :=
  destruct (kind_ok_checker (fc_kind_ctx F) κ) eqn:Hres; [ | inversion HMatchKind ];
  unfold ok in o; assert (o = tt) by (by destruct o); subst.

Ltac destruct_on_match_equal resname :=
  match goal with
  | H: ((match ?key with |_=>_ end) = _) |- _ => destruct key eqn:resname
  end.


Ltac destruct_match_unit Hmatch resname o :=
  destruct_on_match_equal resname; [stupid_unit o | inversion Hmatch].

Ltac my_auto :=
  try structural_auto; try boolean_equality_auto;
  try match goal with
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
  (forall ft F, function_type_ok_checker F ft = ok_term -> function_type_ok F ft) /\
  (forall ft F, inner_function_type_ok_checker F ft = ok_term -> inner_function_type_ok F ft).
Proof.

  Ltac auto_local F := repeat my_auto; try find_Forall_foldr (type_ok_checker F) (type_ok F); auto.

  apply type_and_function_ind;
    try by (intros; cbn in *; try constructor; auto_local F).
  - (* The var case requires econstructor, which I didn't want to do in general *)
    intros; cbn in *;
    auto_local F; econstructor; eassumption.
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

Lemma inner_function_type_ok_checker_correct :
  ∀ ft F, inner_function_type_ok_checker F ft = ok_term -> inner_function_type_ok F ft.
Proof.
  apply type_ok_checker_correct_basic.
Qed.


Definition mono_mem_checker (μ:memory) : type_checker_res :=
  match μ with
  | BaseM bm => ok_term
  | _ => INR "not monomem"
  end.

Lemma mono_mem_checker_correct :
  ∀ μ, (mono_mem_checker μ = ok_term) -> mono_mem μ.
Proof.
  intros. unfold mono_mem_checker in H; destruct μ.
  - inversion H.
  - by exists b.
Qed.

Definition subkind_of_checker (κ1:kind) (κ2:kind) : type_checker_res :=
  match κ1, κ2 with
  | VALTYPE ρ1 ξ1, VALTYPE ρ2 ξ2 =>
      if representation_beq ρ1 ρ2 && ref_flag_le ξ1 ξ2
      then ok_term
      else INR "fail in subkind check"
  | MEMTYPE σ1 ξ1, MEMTYPE σ2 ξ2 =>
      if size_beq σ1 σ2 && ref_flag_le ξ1 ξ2
      then ok_term
      else INR "fail in subkind check"
  | _, _ => INR "no"
  end.




Ltac my_auto2 :=
  try structural_auto; try boolean_equality_auto;
  try match goal with
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
  | H: (inner_function_type_ok_checker _ _ = inl ()) |- _ => apply inner_function_type_ok_checker_correct in H; auto
  | H: (inner_function_type_ok_checker _ _ = ok_term) |- _ => apply inner_function_type_ok_checker_correct in H; auto
end.


Lemma subkind_of_checker_correct :
  ∀ k1 k2, subkind_of_checker k1 k2 = ok_term -> subkind_of k1 k2.
Proof.
  intros.
  destruct k1, k2.
  2, 3: cbn in H; repeat structural_auto.
  2: destruct r, r0. 1: destruct r0, r2.
  all: simpl in H; try inversion H; repeat my_auto2; constructor.
  all: try done.
  by rewrite H2.
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





(* This function just grabs the kind out of the type *)
Definition grab_kind (F:function_ctx) (t:type) : option kind :=
  type_kind (F.(fc_type_vars)) t.



(* A thing that helps with subkinding *)

(* OBSOLETE *)
(* Definition check_if_subkind (k1:kind) (k2:kind) : type_checker_res := *)
(*   match k1, k2 with *)
(*   | VALTYPE ρ1 ξ1, VALTYPE ρ2 ξ2 => *)
(*       if representation_beq ρ1 ρ2 *)
(*       then *)
(*         match ξ1, ξ2 with *)
(*         | NoRefs, _ *)
(*         | GCRefs, GCRefs *)
(*         | GCRefs, AnyRefs *)
(*         | AnyRefs, AnyRefs => ok_term *)
(*         | GCRefs, NoRefs => INR "not subkind (gc no)" *)
(*         | AnyRefs, NoRefs => INR "not subkind (any no)" *)
(*         | AnyRefs, GCRefs => INR "not subkind (any gc)" *)
(*         end *)
(*       else INR "mismatch in representation for subkinds" *)
(*   | MEMTYPE σ1 ξ1, MEMTYPE σ2 ξ2 => *)
(*       if size_beq σ1 σ2 *)
(*       then *)
(*         match ξ1, ξ2 with *)
(*         | NoRefs, _ *)
(*         | GCRefs, GCRefs *)
(*         | GCRefs, AnyRefs *)
(*         | AnyRefs, AnyRefs => ok_term *)
(*         | GCRefs, NoRefs => INR "not subkind (gc no)" *)
(*         | AnyRefs, NoRefs => INR "not subkind (any no)" *)
(*         | AnyRefs, GCRefs => INR "not subkind (any gc)" *)
(*         end *)
(*       else INR "mismatch in sizity for subkinds" *)
(*   | _, _ => INR "mismatch in general kind for subkind" *)
(*   end. *)

(* Lemma check_if_subkind_works_with_has_kind : *)
(*   ∀ F τ k1 k2, *)
(*     check_if_subkind k1 k2 = ok_term -> *)
(*     has_kind F τ k1 -> *)
(*     has_kind F τ k2. *)
(* Proof. *)
(*   Ltac local_auto := eapply KSub; try constructor; auto. *)

(*   intros. *)
(*   destruct k1, k2; simpl in H; repeat my_auto2; subst; auto; try (inversion H). *)
(*   - destruct r2; auto; local_auto. *)
(*     + by instantiate (1 := NoRefs). *)
(*     + done. *)
(*     + by instantiate (1 := NoRefs). *)
(*     + done. *)
(*   - local_auto. *)
(*     + by instantiate (1 := GCRefs). *)
(*     + done. *)
(*   - destruct r0; auto; local_auto. *)
(*     + by instantiate (1 := NoRefs). *)
(*     + done. *)
(*     + by instantiate (1 := NoRefs). *)
(*     + done. *)
(*   - local_auto. *)
(*     + by instantiate (1 := GCRefs). *)
(*     + done. *)
(* Qed. *)


(* foldr2 does not check for equal list length *)
Fixpoint foldr2 {A B C : Type} (f : B → C → A → A) (a0 : A)
  (lB : list B) (lC : list C) :=
  match lB, lC with
  | b :: lB0, c :: lC0 => f b c (foldr2 f a0 lB0 lC0)
  | _, _ => a0
  end.

(* foldr2_bool has a param for equal list length base and unequal list length base *)
Fixpoint foldr2_bool {B C : Type} (f : B → C → bool → bool) (a_good : bool) (a_bad : bool)
  (lB : list B) (lC : list C) :=
  match lB, lC with
  | b :: lB0, c :: lC0 => f b c (foldr2_bool f a_good a_bad lB0 lC0)
  | [], [] => a_good
  | _, _ => a_bad
  end.
(* foldr2 lemmas location *)
(* this variation is particularly useful for after an induction *)
Lemma convert_foldr2_bool_to_Forall2_check_ok_output
  {In1 In2 : Type} (func: In1 -> In2 -> type_checker_res) (Pbool : In1 -> In2 -> Prop)
  (l1 : list In1) (l2 : list In2) :
  foldr2_bool (λ i1 i2, andb (check_ok_output (func i1 i2))) true false l1 l2 = true ->
  Forall (λ i1, ∀ i2, func i1 i2 = ok_term -> Pbool i1 i2) l1 ->
  Forall2 Pbool l1 l2.
Proof.
  generalize dependent l2.
  induction l1.
  - intros * Hfoldr Hall.
    cbn in Hfoldr.
    destruct l2; cbn in Hfoldr; try by inversion Hfoldr.
  - intros * Hfoldr Hall.
    destruct l2 as [|a2 l2]; try by (cbn in Hfoldr; inversion Hfoldr).
    cbn in Hfoldr.
    repeat my_auto2.
    constructor.
    + inversion Hall; subst.
      specialize (H3 a2).
      apply H3; try done.
      by apply check_ok_output_true_to_prop.
    + apply IHl1; try done.
      inversion Hall; subst; done.
Qed.

Lemma convert_foldr2_bool_to_Forall2_check_ok_output_pure_forall
  {In1 In2 : Type} (func: In1 -> In2 -> type_checker_res) (Pbool : In1 -> In2 -> Prop)
  (l1 : list In1) (l2 : list In2) :
  foldr2_bool (λ i1 i2, andb (check_ok_output (func i1 i2))) true false l1 l2 = true ->
  (∀ i1, ∀ i2, func i1 i2 = ok_term -> Pbool i1 i2) ->
  Forall2 Pbool l1 l2.
Proof.
  generalize dependent l2.
  induction l1.
  - intros * Hfoldr Hall.
    cbn in Hfoldr.
    destruct l2; cbn in Hfoldr; try by inversion Hfoldr.
  - intros * Hfoldr Hall.
    destruct l2 as [|a2 l2]; try by (cbn in Hfoldr; inversion Hfoldr).
    cbn in Hfoldr.
    repeat my_auto2.
    constructor.
    + specialize (Hall a a2).
      apply Hall; try done.
      by apply check_ok_output_true_to_prop.
    + apply IHl1; try done.
Qed.

Lemma flip_foldr2_bool {In1 In2 : Type} (func: In1 -> In2 -> type_checker_res) (l1 : list In1) (l2: list In2) :
  foldr2_bool (λ i1 i2, andb (check_ok_output (func i1 i2))) true false l1 l2 = true <->
    foldr2_bool (λ i2 i1, andb (check_ok_output (func i1 i2))) true false l2 l1 = true.
Proof.
  generalize dependent l2.
  induction l1; intros *; split; intros H; destruct l2 as [|a2 l2]; cbn in H; try by inversion H.
  - cbn.
    repeat my_auto.
    apply andb_true_intro.
    split; try done.
    eapply IHl1; try done.
  - cbn.
    repeat my_auto.
    apply andb_true_intro.
    split; try done.
    eapply IHl1; try done.
Qed.

Lemma convert_foldr2_bool_to_Forall2_check_ok_output_right_list
  {In1 In2 : Type} (func: In1 -> In2 -> type_checker_res) (Pbool : In1 -> In2 -> Prop)
  (l1 : list In1) (l2 : list In2) :
  foldr2_bool (λ i1 i2, andb (check_ok_output (func i1 i2))) true false l1 l2 = true ->
  Forall (λ i2, ∀ i1, func i1 i2 = ok_term -> Pbool i1 i2) l2 ->
  Forall2 Pbool l1 l2.
Proof.
  generalize dependent l1.
  induction l2.
  - intros * Hfoldr Hall.
    cbn in Hfoldr.
    destruct l1; cbn in Hfoldr; try by inversion Hfoldr.
  - intros * Hfoldr Hall.
    destruct l1 as [|a2 l1]; try by (cbn in Hfoldr; inversion Hfoldr).
    cbn in Hfoldr.
    repeat my_auto2.
    constructor.
    + inversion Hall; subst.
      specialize (H3 a2).
      apply H3; try done.
      by apply check_ok_output_true_to_prop.
    + apply IHl2; try done.
      inversion Hall; subst; done.
Qed.

Fixpoint all_left {A B : Type} (l: list (A + B)) : bool :=
  match l with
  | [] => true
  | a::l =>
      match a with
      | inl _ => true && all_left l
      | inr _ => false
      end
  end.

Fixpoint get_all_lefts {A B : Type} (l: list (A + B)) : list A :=
  match l with
  | [] => []
  | a::l =>
      match a with
      | inl a => a:: get_all_lefts l
      | inr _ => get_all_lefts l
      end
  end.
Fixpoint get_all_rights {A B : Type} (l: list (A + B)) : list B :=
  match l with
  | [] => []
  | a::l =>
      match a with
      | inl _ => get_all_rights l
      | inr b => b :: get_all_rights l
      end
  end.
Definition is_memtype κ : bool :=
  match κ with
  | MEMTYPE _ _ => true
  | _ => false
  end.
Definition is_valtype κ : bool :=
  match κ with
  | VALTYPE _ _ => true
  | _ => false
  end.
Definition get_rep_or_size κ :=
  match κ with
  | VALTYPE ρ _ => inl ρ
  | MEMTYPE σ _ => inr σ
  end.
(* this is basically identical to the old has_kind_checker *)
Fixpoint has_kind_synther (F:function_ctx) (t:type) : (kind + type_error) :=
  (* inr (NormalError "incomplete"). *)
  match t with
  | VarT t =>
      match (F.(fc_type_vars)) !! t with
      | Some κ =>
          match kind_ok_checker (F.(fc_kind_ctx)) κ with
          | inl () => inl κ
          | inr err => inr (HasKindError "" err)
          end
      | None => inr (HasKindError "variable not in there or smthn" [])
      end
  (* Numbers *)
  | I31T κ =>
      if (kind_beq κ (VALTYPE (AtomR PtrR) NoRefs))
      then inl κ
      else inr (HasKindError "wrong kind for I31T" [])
    (* NumT *)
  | NumT κ (IntT I32T) =>
      if (kind_beq κ (VALTYPE (AtomR I32R) NoRefs))
      then inl κ
      else inr (HasKindError "wrong kind for I32T" [])
  | NumT κ (IntT I64T) =>
      if (kind_beq κ (VALTYPE (AtomR I64R) NoRefs) )
      then inl κ
      else inr (HasKindError "wrong kind for I64T" [])
  | NumT κ (FloatT F32T) =>
      if (kind_beq κ (VALTYPE (AtomR F32R) NoRefs))
      then inl κ
      else inr (HasKindError "wrong kind for F32T" [])
  | NumT κ (FloatT F64T) =>
      if (kind_beq κ (VALTYPE (AtomR F64R) NoRefs))
      then inl κ
      else inr (HasKindError "wrong kind for F64T" [])
  (* Sums and Prods *)
  | SumT κ τs =>
      match κ with
      | VALTYPE (SumR ρs) ξ =>
          let results := map (has_kind_synther F) τs in
          if all_left results
          then
            let just_kinds := get_all_lefts results in
            if (* crazy list *)
              (* one: ensure outer ξ is least upper bind of the kind flags *)
              ref_flag_beq ξ (ref_flag_lub (map kind_ref_flag just_kinds)) &&
              (* two: ensure all internal kinds are valtypes *)
              (foldr andb true (map (is_valtype) just_kinds) ) &&
              (* three: ensure the reps actually map *)
              (list_beq representation representation_beq
                 ρs (get_all_lefts (map get_rep_or_size just_kinds)))
            then inl κ
            else inr (HasKindError "bad sum internals (either ξ not lub, or not all valtype, or ρs don't match)" [])
          else inr (HasKindError "in sum some inner types didn't synth"
                      (get_all_rights results))
      | _ => inr (HasKindError "bad sum kind format" [])
      end
  | VariantT κ τs =>
      match κ with
      | MEMTYPE (SumS σs) ξ =>
          let results := map (has_kind_synther F) τs in
          if all_left results
          then
            let just_kinds := get_all_lefts results in
            if (* crazy list *)
              (* one: ensure outer ξ is least upper bind of the kind flags *)
              ref_flag_beq ξ (ref_flag_lub (map kind_ref_flag just_kinds)) &&
              (* two: ensure all internal kinds are memtypes *)
              (foldr andb true (map (is_memtype) just_kinds) ) &&
              (* three: ensure the reps actually map *)
              (list_beq size size_beq
                 σs (get_all_rights (map get_rep_or_size just_kinds)))
            then inl κ
            else inr (HasKindError "bad variant internals (either ξ not lub, or not all memtype, or σs don't match)" [])
          else inr ( HasKindError "in variant some innter types didn't synth" (get_all_rights results))
      | _ => inr (HasKindError "bad variant kind format" [])
      end
  | ProdT κ τs =>
      match κ with
      | VALTYPE (ProdR ρs) ξ =>
          let results := map (has_kind_synther F) τs in
          if all_left results
          then
            let just_kinds := get_all_lefts results in
            if (* crazy list *)
              (* one: ensure outer ξ is least upper bind of the kind flags *)
              ref_flag_beq ξ (ref_flag_lub (map kind_ref_flag just_kinds)) &&
              (* two: ensure all internal kinds are valtypes *)
              (foldr andb true (map (is_valtype) just_kinds) ) &&
              (* three: ensure the reps actually map *)
              (list_beq representation representation_beq
                 ρs (get_all_lefts (map get_rep_or_size just_kinds)))
            then inl κ
            else inr (HasKindError "bad prod internals (either ξ not lub, or not all valtype, or ρs don't match)" [])
          else inr ( HasKindError "in prod some inner types didnt synth" (get_all_rights results))
      | _ => inr (HasKindError "bad sum kind format" [])
      end
  | StructT κ τs =>
      match κ with
      | MEMTYPE (ProdS σs) ξ =>
          let results := map (has_kind_synther F) τs in
          if all_left results
          then
            let just_kinds := get_all_lefts results in
            if (* crazy list *)
              (* one: ensure outer ξ is least upper bind of the kind flags *)
              ref_flag_beq ξ (ref_flag_lub (map kind_ref_flag just_kinds)) &&
              (* two: ensure all internal kinds are memtypes *)
              (foldr andb true (map (is_memtype) just_kinds) ) &&
              (* three: ensure the reps actually map *)
              (list_beq size size_beq
                 σs (get_all_rights (map get_rep_or_size just_kinds)))
            then inl κ
            else inr (HasKindError "bad struct internals (either ξ not lub, or not all memtype, or σs don't match)" [])
          else inr ( HasKindError "in struct some inner types didnt synth" (get_all_rights results))
      | _ => inr (HasKindError "bad variant kind format" [])
      end
  (* References *)
  | RefT κ (BaseM MemGC) β τ =>
      if (kind_beq κ (VALTYPE (AtomR PtrR) GCRefs))
      then
        match has_kind_synther F τ with
        | inl innerκ =>
            match innerκ with
            | MEMTYPE _ _ => inl κ
            | _ => inr (HasKindError "you have a reft t where t isn't memtype" [])
            end
        | err => err
        end
      else inr (HasKindError "bad gc mem kind format" [])
  | RefT κ μ β τ =>
      if (kind_beq κ (VALTYPE (AtomR PtrR) AnyRefs))
      then
        match mem_ok_checker (F.(fc_kind_ctx)) μ with
          | inl () =>
              match has_kind_synther F τ with
              | inl innerκ =>
                  match innerκ with
                  | MEMTYPE _ _ => inl κ
                  | _ => inr (HasKindError "you have a reft t where t isn't memtype" [])
                  end
              | err => err
              end
          | inr err => inr (HasKindError "" err)
          end
      else inr (HasKindError "bad ref kind format" [])
  | CodeRefT κ ϕ =>
      match κ with
      | VALTYPE (AtomR I32R) NoRefs =>
          match has_kind_ft_checker F ϕ with
          | inl () => inl κ
          | inr err => inr (HasKindError "" err)
          end
      | _ => inr ( HasKindError "bad coderef kind format" [])
      end
  | SerT κ τ =>
      match κ with
      | MEMTYPE (RepS ρ) ξ =>
          match has_kind_synther F τ with
          | inl (VALTYPE ρ' ξ') =>
              if (representation_beq ρ ρ') && (ref_flag_beq ξ ξ')
              then inl κ
              else inr (HasKindError "in ser t, outer kappa's ref and flag don't match inner" [])
          | inl (MEMTYPE _ _) => inr (HasKindError "you have a ser t where t isn't valtype" [])
          | err => err
          end
      | _ => inr (HasKindError "bad ser kind format" [])
      end
  | PlugT κ ρ =>
      match κ with
      | VALTYPE ρ1 NoRefs =>
          if representation_beq ρ ρ1
          then
            match rep_ok_checker (F.(fc_kind_ctx)) ρ with
            | inl () => inl κ
            | inr err => inr (HasKindError "" err)
            end
          else inr (HasKindError "plug's rep doesn't match kind's rep" [])
      | _ => inr (HasKindError "bad plug kind format" [])
      end
  | SpanT κ σ =>
      match κ with
      | MEMTYPE σ1 NoRefs =>
          if size_beq σ σ1
          then
            match size_ok_checker (F.(fc_kind_ctx)) σ with
            | inl () => inl κ
            | inr err => inr (HasKindError "" err)
            end
          else inr (HasKindError "span's size doesn't match kind's size" [])
      | _ => inr (HasKindError "bad span kind format" [])
      end
  | RecT κ τ =>
      match has_kind_synther (F <| fc_type_vars ::= cons κ |>) τ with
      | inl κ' =>
          if kind_beq κ κ'
          then inl κ
          else inr (HasKindError "synthed kind for t in reft not equal to outer kind" [])
      | err => err
      end
  | ExistsMemT κ τ =>
      match kind_ok_checker (F.(fc_kind_ctx)) κ with
      | inl () =>
          match has_kind_synther (F <| fc_kind_ctx ::= set kc_mem_vars S |>) τ with
          | inl κ' =>
              if kind_beq κ κ'
              then inl κ
              else inr (HasKindError "synthed kind for t in existsmem not equal to outer kind" [])
          | err => err
          end
      | inr err => inr (HasKindError "" err)
      end
  | ExistsRepT κ τ =>
      match kind_ok_checker (F.(fc_kind_ctx)) κ with
      | inl () =>
          match has_kind_synther (add_rep_var F) τ with
          | inl κ' =>
              if kind_beq (ren_kind unscoped.shift unscoped.id κ) κ'
              then inl κ
              else inr (HasKindError "synthed kind for t in existsrep not equal to outer kind" [])
          | err => err
          end
      | inr err => inr (HasKindError "" err)
      end
   | ExistsSizeT κ τ =>
      match kind_ok_checker (F.(fc_kind_ctx)) κ with
      | inl () =>
          match has_kind_synther (add_size_var F) τ with
          | inl κ' =>
              if kind_beq (ren_kind unscoped.id unscoped.shift κ) κ'
              then inl κ
              else inr (HasKindError "synthed kind for t in existssize not equal to outer kind" [])
          | err => err
          end
      | inr err => inr (HasKindError "" err)
      end
  | ExistsTypeT κ κ0 τ =>
      match kind_ok_checker (F.(fc_kind_ctx)) κ with
      | inl () =>
          match kind_ok_checker (F.(fc_kind_ctx)) κ0 with
          | inl () =>
              match has_kind_synther (F <| fc_type_vars ::= cons κ0 |>) τ with
              | inl κ' =>
                  if kind_beq κ κ'
                  then inl κ
                  else inr (HasKindError "synthed kind for t in existstype not equal to outer kind" [])
              | err => err
              end
          | inr err => inr (HasKindError "" err)
          end
      | inr err => inr (HasKindError "" err)
      end
  end
with has_kind_ift_checker (F:function_ctx) (ϕ:inner_function_type) : type_checker_res :=
  match ϕ with
  | MonoFunT τs1 τs2 =>
      let results1 := map (has_kind_synther F) τs1 in
      let results2 := map (has_kind_synther F) τs2 in
      if all_left results1
      then
        if all_left results2
        then ok_term
        else inr [HasKindError "in monofun some result types didn't synth" (get_all_rights results2)]
      else inr [HasKindError "in monofun some argument types didn't synth" (get_all_rights results1)]
  | ForallTypeT κ ϕ =>
      match kind_ok_checker (F.(fc_kind_ctx)) κ with
      | inl () => has_kind_ift_checker (F <| fc_type_vars ::= cons κ |>) ϕ
      | err => err
      end
  end
with has_kind_ft_checker (F:function_ctx) (ϕ:function_type) : type_checker_res :=
  match ϕ with
  | InnerFunT ϕ => has_kind_ift_checker F ϕ
  | ForallMemT ϕ => has_kind_ft_checker (F <| fc_kind_ctx ::= set kc_mem_vars S |>) ϕ
  | ForallRepT ϕ => has_kind_ft_checker (add_rep_var F) ϕ
  | ForallSizeT ϕ => has_kind_ft_checker (add_size_var F) ϕ
  end.

(* Check kind in a naive way. I guess. *)
Definition has_kind_checker (F:function_ctx) (t:type) (k:kind) : type_checker_res :=
  match has_kind_synther F t with
  | inl κ =>
      if kind_beq κ k
      then ok_term
      else INR "inner/synthesized kind not equal to what you're checking against"
  | inr err => inr [err]
  end.

Ltac my_auto3 :=
  try structural_auto; try boolean_equality_auto; try
  match goal with
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
  | H: (inl _ = inl _) |- _ => inversion H; subst; clear H
  | H: (inr _ = inr _) |- _ => inversion H; subst; clear H
  | H: (inl _ = inr _) |- _ => inversion H
  | H: (inr _ = inl _) |- _ => inversion H
  | H: (INR _ = ok_term) |- _ => inversion H
  | H: (INR _ = inl ()) |- _ => inversion H
end.

Opaque mem_ok_checker.
(* this needs to not be unravelled by any tactics. Makes
 automation a lot easier *)


Lemma all_left_Forall2_has_kind F τs :
  Forall (λ t, ∀ F κ, has_kind_synther F t = inl κ -> has_kind F t κ) τs ->
  all_left (map (has_kind_synther F) τs) = true ->
  Forall2 (has_kind F) τs (get_all_lefts (map (has_kind_synther F) τs)).
Proof.
  induction 1 as [|t τs Ht Hτs IH]; simpl; intros Hall; first constructor.
  destruct (has_kind_synther F t) eqn:Hsynth; simpl in Hall; last done.
  constructor; auto.
Qed.

Lemma convert_forall2_has_kind_to_forall3_has_valtype F τs (κs : list kind) :
  foldr andb true (map is_valtype κs) = true ->
  Forall2 (has_kind F) τs κs ->
  Forall3 (λ τ ρ ξ, has_kind F τ (VALTYPE ρ ξ)) τs (get_all_lefts (map get_rep_or_size κs))
    (map kind_ref_flag κs).
Proof.
  generalize dependent τs.
  induction κs as [|κ κs].
  - intros τs Hval Hkind.
    destruct τs; inversion Hkind.
    cbn.
    constructor.
  - intros τs Hval Hkind.
    destruct τs as [|τ τs]; inversion Hkind; subst.
    cbn in Hval.
    repeat my_auto3.
    specialize (IHκs τs H0 H4).
    cbn.
    destruct κ as [ρ ξ | σ ξ]; try inversion H1.
    cbn.
    constructor; try done.
Qed.

Lemma convert_forall2_has_kind_to_forall3_has_memtype F τs (κs : list kind) :
  foldr andb true (map is_memtype κs) = true ->
  Forall2 (has_kind F) τs κs ->
  Forall3 (λ τ σ ξ, has_kind F τ (MEMTYPE σ ξ)) τs (get_all_rights (map get_rep_or_size κs))
    (map kind_ref_flag κs).
Proof.
  generalize dependent τs.
  induction κs as [|κ κs].
  - intros τs Hval Hkind.
    destruct τs; inversion Hkind.
    cbn.
    constructor.
  - intros τs Hval Hkind.
    destruct τs as [|τ τs]; inversion Hkind; subst.
    cbn in Hval.
    repeat my_auto3.
    specialize (IHκs τs H0 H4).
    cbn.
    destruct κ as [ρ ξ | σ ξ]; try inversion H1.
    cbn.
    constructor; try done.
Qed.


Lemma has_kind_synther_correct_basic :
  (∀ t F k, has_kind_synther F t = inl k -> has_kind F t k) /\
  (∀ (ft:function_type) (F:function_ctx),
     has_kind_ft_checker F ft = ok_term -> has_kind_ft F ft) /\
  (∀ (ft:inner_function_type) (F:function_ctx),
     has_kind_ift_checker F ft = ok_term -> has_kind_ift F ft).
Proof.
  apply type_and_function_ind; unfold has_kind_checker in *; intros; simpl in *; auto;
    repeat my_auto3; try (by constructor).
  1: refine ?[SumT]. 2: refine ?[VariantT]. 3: refine ?[ProdT]. 4: refine ?[StructT].
  5: refine ?[RefTVar]. 6: refine ?[RefTMM]. 7: refine ?[RefTGC].
  8: refine ?[CodeRef]. 9: refine ?[SerT].
  10: refine ?[RecT]. 11: refine ?[ExistsMemT]. 12: refine ?[ExistsRepT].
  13: refine ?[ExistsSizeT]. 14: refine ?[ExistsTypeT].
  15: refine ?[MonoFun]. 16: refine ?[ForallType]. 17: refine ?[InnerFun].
  18: refine ?[ForallMem]. 19: refine ?[ForallRep]. 20: refine ?[ForallSize].

  [CodeRef]: constructor; by apply H.
  [MonoFun]: eapply KMonoFun; by apply all_left_Forall2_has_kind.
  [ForallType]: constructor; [done | by apply H].
  [InnerFun]: constructor; by apply H.
  [ForallMem]: constructor; by apply H.
  [ForallRep]: constructor; by apply H.
  [ForallSize]: constructor; by apply H.

  [SumT]: {
    constructor.
    pose proof all_left_Forall2_has_kind F τs H HMatch1.
    set (synthed_κs := (map (has_kind_synther F) τs)) in *.
    set (κs := get_all_lefts synthed_κs) in *.
    by apply convert_forall2_has_kind_to_forall3_has_valtype.
  }
  [VariantT]: {
    constructor.
    pose proof all_left_Forall2_has_kind F τs H HMatch1.
    set (synthed_κs := (map (has_kind_synther F) τs)) in *.
    set (κs := get_all_lefts synthed_κs) in *.
    by apply convert_forall2_has_kind_to_forall3_has_memtype.
  }
  [ProdT]: {
    constructor.
    pose proof all_left_Forall2_has_kind F τs H HMatch1.
    set (synthed_κs := (map (has_kind_synther F) τs)) in *.
    set (κs := get_all_lefts synthed_κs) in *.
    by apply convert_forall2_has_kind_to_forall3_has_valtype.
  }
  [StructT]: {
    constructor.
    pose proof all_left_Forall2_has_kind F τs H HMatch1.
    set (synthed_κs := (map (has_kind_synther F) τs)) in *.
    set (κs := get_all_lefts synthed_κs) in *.
    by apply convert_forall2_has_kind_to_forall3_has_memtype.
  }


  Ltac do_it IH :=
    match goal with
    | H: (has_kind_synther _ _ = _) |- _ => apply IH in H
    end.


  (* a few slightly special ones *)
  [RefTVar]: do_it H; eapply KRefVar; done.
  [RefTMM]: do_it H; eapply KRefMM; done.
  [RefTGC]: do_it H; eapply KRefGC; done.


  (* the rest are simple *)
  all: do_it H; by constructor.

Qed.

Lemma has_kind_synther_correct :
  (∀ t F k, has_kind_synther F t = inl k -> has_kind F t k).
Proof.
  pose proof has_kind_synther_correct_basic.
  by destruct H.
Qed.

Lemma has_kind_ft_checker_correct :
  ∀ ft F, has_kind_ft_checker F ft = ok_term -> has_kind_ft F ft.
Proof.
  by destruct has_kind_synther_correct_basic as (_ & ? & _).
Qed.

Lemma has_kind_ift_checker_correct :
  ∀ ft F, has_kind_ift_checker F ft = ok_term -> has_kind_ift F ft.
Proof.
  by destruct has_kind_synther_correct_basic as (_ & _ & ?).
Qed.

Lemma has_kind_checker_correct :
  ∀ F t k, has_kind_checker F t k = ok_term -> has_kind F t k.
Proof.
  pose proof has_kind_synther_correct.
  intros.
  unfold has_kind_checker in H0.
  my_auto3.
  clear H2.
  my_auto3.
Qed.


(* Small things before pathing *)
Definition has_rep_checker F τ ρ : type_checker_res :=
  match has_kind_synther F τ with
  | inl (VALTYPE ρ' _) =>
      if representation_beq ρ ρ' then ok_term else INR "checking rep, unmatching rep"
  | inl _ => INR "checking rep, but memtype"
  | inr err => inr [err]
  end.

Lemma has_rep_checker_correct :
  ∀ F τ ρ, has_rep_checker F τ ρ = ok_term -> has_rep F τ ρ.
Proof.
  intros.
  unfold has_rep_checker in H.
  my_auto3.
  apply has_kind_synther_correct in HMatch.
  clear H1.
  my_auto3. clear H1.
  my_auto3.
  by econstructor.
Qed.

Definition grab_rep F τ : option representation :=
  match grab_kind F τ with
  | Some κ =>
      match κ with
      | VALTYPE ρ _  => Some ρ
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
  unfold has_mono_rep.
  exists r; done.
Qed.

Definition has_mono_rep_instr_checker F inst : type_checker_res :=
  match inst with
  | InstrT τs1 τs2 =>
      if (foldr (λ t:type, andb (check_ok (has_mono_rep_checker F) t)) true τs1)
      then
        if (foldr (λ t:type, andb (check_ok (has_mono_rep_checker F) t)) true τs2)
        then ok_term
        else
          let res := map (has_mono_rep_checker F) τs2 in
          inr ([NormalError "mono rep instr checker error in τs2"] ++ combine_error_messages res)
          (* INR ("mono rep instr checker error in τs2 (" ++ (combine_error_messages res) ++ ")"%string ) *)
      else
        let res := map (has_mono_rep_checker F) τs1 in
        inr ([NormalError "mono rep instr checker error in τs2"] ++ combine_error_messages res)
        (* INR ("mono rep instr checker error in τs1 (" ++ (combine_error_messages res) ++ ")"%string ) *)
  end.

Lemma has_mono_rep_instr_checker_correct :
  ∀ F inst, has_mono_rep_instr_checker F inst = ok_term -> has_mono_rep_instr F inst.
Proof.
  intros.
  unfold has_mono_rep_instr_checker in *.
  repeat my_auto3. pose proof has_mono_rep_checker_correct.
  split; [clear HMatch1 | clear HMatch0].
  - (* yeah this is true but I dont wanna prove it *)
    eapply convert_foldr_to_Forall_check_ok; try done.
    exact (H F).
  - eapply convert_foldr_to_Forall_check_ok; try done.
    exact (H F).
Qed.

(* I think type_size can do this but oh well *)
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
  match has_kind_synther F τ with
  | inl (MEMTYPE σ' _) =>
      if size_beq σ σ' then ok_term else INR "checking size, unmatching size"
  | inl _ => INR "checking size, but VALTYPE"
  | inr err => inr [err]
  end.

Lemma has_size_checker_correct :
  ∀ F τ σ, has_size_checker F τ σ = ok_term -> has_size F τ σ.
Proof.
  intros. unfold has_size_checker in H.
  repeat my_auto3.
  apply has_kind_synther_correct in HMatch.
  by exists r.
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
  repeat my_auto3. apply has_kind_synther_correct in HMatch1.
  by apply (HasMonoSize _ _ s0 r).
Qed.


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
Qed.

(* NOTE:  a bit of confusing terminology. size_beq is actual equality.
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
  unfold size_eq.
  exists n0; done.
Qed.

Definition size_leq_checker σ1 σ2 : type_checker_res :=
  match eval_size EmptyEnv σ1 with
  | Some n1 =>
      match eval_size EmptyEnv σ2 with
      | Some n2 =>
          if n1 <=? n2
          then ok_term
          else INR "unequal sizes"
      | None => INR "bad size"
      end
  | None => INR "bad size"
  end.

Lemma size_leq_checker_correct :
  ∀ σ1 σ2, size_leq_checker σ1 σ2 = ok_term -> size_leq σ1 σ2.
Proof. (* easy *)
  intros. unfold size_leq_checker in *.
  repeat my_auto3.
  apply Nat.leb_le in HMatch1.
  by (exists n; exists n0).
Qed.

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
  apply has_size_checker_correct in HMatch1, HMatch2.
  apply size_eq_checker_correct in H.
  exists s, s0. split; auto.
Qed.

(*
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
*)
Definition grab_ref_flag F τ : option ref_flag :=
  match grab_kind F τ with
  | Some (VALTYPE _ ξ)
  | Some (MEMTYPE _ ξ) => Some ξ
  | None => None
  end.

(*
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
*)
Definition has_ref_flag_checker F τ ξ : type_checker_res :=
  match has_kind_synther F τ with
  | inl κ =>
      if ref_flag_le (kind_ref_flag κ) ξ
      then ok_term
      else INR "does not have ref flag (not less than)"
  | inr err => inr [err]
  end.
Lemma has_ref_flag_checker_correct :
  ∀ F τ ξ, has_ref_flag_checker F τ ξ = ok_term -> has_ref_flag F τ ξ.
Proof.
  unfold has_ref_flag_checker; intros.
  repeat my_auto3.
  apply has_kind_synther_correct in HMatch.
  exists k.
  split; [done|].
  rewrite HMatch0; done.
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
      specialize (IHσs l). specialize (IHσs ltac:(auto)).
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
      specialize (IHσs ρs ltac:(auto)).
      by rewrite IHσs.
Qed.



Ltac my_auto3_5 :=
  try structural_auto; try boolean_equality_auto; try
  match goal with
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
  | H: (inner_function_type_ok_checker _ _ = inl ()) |- _ => apply function_type_ok_checker_correct in H; auto
  | H: (inner_function_type_ok_checker _ _ = ok_term) |- _ => apply function_type_ok_checker_correct in H; auto
  | H: (has_kind_checker _ _ _ = ok_term) |- _ => apply has_kind_checker_correct in H; auto
  | H: (has_kind_checker _ _ _ = inl ()) |- _ => apply has_kind_checker_correct in H; auto
  | H: (INR _ = ok_term) |- _ => inversion H
  | H: (INR _ = inl ()) |- _ => inversion H
end.

(* to use in the future if sequence remains broken *)
Fixpoint my_sequence {A:Type} (l: list (option A)) : option (list A) :=
  match l with
  | [] => Some []
  | a::rest =>
      match my_sequence rest with
      | Some rest' =>
          match a with
          | Some a' => Some (a'::rest')
          | None => None
          end
      | None => None
      end
  end.
(* This is an attempt without a double match for the sake of the proof later *)
Fixpoint type_eq_checker (τ1:type) (τ2:type) :type_checker_res :=
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
            (* match has_kind_checker F (SumT κ1 τs1) κ1 with *)
            (* | inl () => *)
                if foldr2_bool (λ τ1, λ τ2, andb (check_ok_output (type_eq_checker τ1 τ2))) true false τs1 τs2
                then ok_term
                else INR "types not equal"
            (* | err => err *)
            (* end *)
          else INR "types not equal"
      | _ => INR "types not equal"
      end
  | VariantT κ1 τs1 =>
      match τ2 with
      | VariantT κ2 τs2 =>
          if kind_beq κ1 κ2
          then
            (* match has_kind_checker F (VariantT κ1 τs1) κ1 with *)
            (* | inl () => *)
                if foldr2_bool (λ τ1, λ τ2, andb (check_ok_output (type_eq_checker τ1 τ2))) true false τs1 τs2
                then ok_term
                else INR "types not equal"
            (* | err => err *)
            (* end *)
          else INR "types not equal"
      | _ => INR "types not equal"
      end
  | ProdT κ1 τs1 =>
      match τ2 with
      | ProdT κ2 τs2 =>
          if kind_beq κ1 κ2
          then
            (* match has_kind_checker F (ProdT κ1 τs1) κ1 with *)
            (* | inl () => *)
                if foldr2_bool (λ τ1, λ τ2, andb (check_ok_output (type_eq_checker τ1 τ2))) true false τs1 τs2
                then ok_term
                else INR "types not equal"
            (* | err => err *)
            (* end *)
          else INR "types not equal"
      | _ => INR "types not equal"
      end
  | RefT κ1 μ1 β1 τ1 =>
      match τ2 with
      | RefT κ2 μ2 β2 τ2 =>
          if andb (andb (kind_beq κ1 κ2) (memory_beq μ1 μ2)) (mutability_beq β1 β2)
          then
            (* match has_kind_checker F (RefT κ1 μ1 τ1) κ1 with *)
            (* | inl () => *)
                type_eq_checker τ1 τ2
            (* | err => err *)
            (* end *)
          else INR "types not equal"
      | _ => INR "types not equal"
      end
  | RecT κ1 τ1 =>
      match τ2 with
      | RecT κ2 τ2 =>
          if kind_beq κ1 κ2
          then
            (* match has_kind_checker F (RecT κ1 τ1) κ1 with *)
            (* | inl () => *)
                type_eq_checker τ1 τ2
            (* | err => err *)
            (* end *)
          else INR "types not equal"
      | _ => INR "types not equal"
      end
  | ExistsMemT κ1 τ1 =>
      match τ2 with
      | ExistsMemT κ2 τ2 =>
          if kind_beq κ1 κ2
          then
            (* match has_kind_checker F (ExistsMemT κ1 τ1) κ1 with *)
            (* | inl () => *)
                type_eq_checker τ1 τ2
            (* | err => err *)
            (* end *)
          else INR "types not equal"
      | _ => INR "types not equal"
      end
  | ExistsRepT κ1 τ1 =>
      match τ2 with
      | ExistsRepT κ2 τ2 =>
          if kind_beq κ1 κ2
          then
            (* match has_kind_checker F (ExistsRepT κ1 τ1) κ1 with *)
            (* | inl () => *)
                type_eq_checker τ1 τ2
            (* | err => err *)
            (* end *)
          else INR "types not equal"
      | _ => INR "types not equal"
      end
  | ExistsSizeT κ1 τ1 =>
      match τ2 with
      | ExistsSizeT κ2 τ2 =>
          if kind_beq κ1 κ2
          then
            (* match has_kind_checker F (ExistsSizeT κ1 τ1) κ1 with *)
            (* | inl () => *)
                type_eq_checker τ1 τ2
            (* | err => err *)
            (* end *)
          else INR "types not equal"
      | _ => INR "types not equal"
      end
  | ExistsTypeT κ1 κτ1 τ1 =>
      match τ2 with
      | ExistsTypeT κ2 κτ2 τ2 =>
          if andb (kind_beq κ1 κ2) (kind_beq κτ1 κτ2)
          then
            (* match has_kind_checker F (ExistsTypeT κ1 κτ1 τ1) κ1 with *)
            (* | inl () => *)
                type_eq_checker τ1 τ2
            (* | err => err *)
            (* end *)
          else INR "types not equal"
      | _ => INR "types not equal"
      end
  | SerT κ_ser τ_ser =>
      match τ2 with
      | SerT κ2 τ2 =>
          if kind_beq κ_ser κ2
          then type_eq_checker τ_ser τ2
          else INR "types not equal"
      | StructT κ_struct τs' =>
          match τ_ser with
          | ProdT κ_prod τs =>
              (* it just needs to be true that τs' is all SerT and that [inner τ] = τs *)
              let τs_o_toequal := map (λ t, match t with | SerT _ τ => Some τ | _ => None end) τs' in
              let o_τs_toequal := sequence τs_o_toequal in
              match o_τs_toequal with
              | Some τs_toequal =>
                  (* if (list_beq type type_beq τs τs_toequal) then ok_term else INR "type not equal" *)
                  if foldr2_bool (λ τ1, λ τ2, andb (check_ok_output (type_eq_checker τ1 τ2))) true false τs τs_toequal
                  then ok_term
                  else INR "types not equal"
              | None => INR "types not equal"
              end
          | _ => INR "types not equal"
          end
      | _ => INR "types not equal"
      end

  | StructT κ_struct τs' =>
      match τ2 with
      | StructT κ2 τs2 =>
          if kind_beq κ_struct κ2
          then
            if foldr2_bool (λ τ1, λ τ2, andb (check_ok_output (type_eq_checker τ1 τ2))) true false τs' τs2
            then ok_term
            else INR "types not equal 1"
          else INR "types not equal 2"
      | SerT κ_ser τ_ser =>
          match τ_ser with
          | ProdT κ_prod τs =>
              (* it just needs to be true that τs' is all SerT and that [inner τ] = τs *)
              let τs_o_toequal := map (λ t, match t with | SerT _ τ => Some τ | _ => None end) τs' in
              let o_τs_toequal := sequence τs_o_toequal in
              match o_τs_toequal with
              | Some τs_toequal =>
                  (* if (list_beq type type_beq τs τs_toequal) then ok_term else INR "type not equal" *)
                  if foldr2_bool (λ τ1, λ τ2, andb (check_ok_output (type_eq_checker τ2 τ1))) true false τs τs_toequal
                  then ok_term
                  else INR "types not equal"
              | None => INR "types not equal"
              end
          | _ => INR "types not equal"
          end

      | _ => INR "types not equal HERE 9"
      end

  end.



(* NOTE: the reason this has such a weird set up is because this
   is the only way I know how to use type_and_function_ind

  also NOTE: this is written more verbosely than ideal due to
  the automation slowing down a Lot without a bit of help.
 *)
Opaque has_kind_checker.

Lemma forall_unzip_sert :
  ∀ τs κs_ser, Datatypes.length τs = Datatypes.length κs_ser ->
  Forall (λ t, ∀ τ2, type_eq_checker t τ2 = ok_term -> type_eq t τ2) (zip_with SerT κs_ser τs) ->
  Forall (λ t, ∀ τ2, type_eq_checker t τ2 = ok_term -> type_eq t τ2) τs.
Proof.
  induction τs.
  - intros [|a b] Hlen; try inversion Hlen.
    cbn. done.
  - intros [|κ κs_ser] Hlen; try inversion Hlen.
    intros Hzipped.
    inversion Hzipped; subst.
    constructor; try by eapply IHτs.
    intros τ2.
    intros Hminieq.
    assert (type_eq_checker (SerT κ a) (SerT κ τ2) = ok_term). {
      cbn.
      (* this is true *)
      assert (kind_beq κ κ = true). {
        apply kind_eq_convert. done.
      }
      rewrite H.
      done.
    }
    apply H2 in H.
    inversion H; subst; try constructor.
    done.
Qed.

Lemma sequence_stupid_some {A:Type} (a:A) l:
  sequence (Some a :: l) =
    match sequence l with
    | Some ll => Some (a::ll)
    | None => None
    end.
Proof.
  cbn. done.
Qed.

Lemma sequence_stupid_none {A:Type} (l: list (option A)):
  sequence (None :: l) = None.
Proof.
  cbn. done.
Qed.

Lemma sequence_map_zip_with :
  ∀ τs_zipped τs,
  sequence (map (λ t, match t with |SerT _ τ => Some τ | _ => None end) τs_zipped) = Some τs ->
  ∃ κs_ser, τs_zipped = zip_with SerT κs_ser τs /\ Datatypes.length κs_ser = Datatypes.length τs.
Proof.
  induction τs_zipped.
  - intros τs Hseq; cbn in *; inversion Hseq; subst.
    exists []; cbn; split; done.
  - intros τs Hseq.
    Opaque sequence.
    cbn in Hseq.
    destruct a eqn:Ha; try by (cbn in Hseq; inversion Hseq).
    rewrite sequence_stupid_some in Hseq.
    repeat my_auto3.
    specialize (IHτs_zipped l ltac:(auto)).
    destruct IHτs_zipped as (κs_ser_small & Hzip & Hlen).
    exists (k :: κs_ser_small).
    cbn.
    subst. split; try done; lia.
Qed.

Lemma type_eq_refl_forall2 τs : Forall2 type_eq τs τs.
Proof.
  induction τs; try done.
  constructor; try done; constructor.
Qed.

Lemma type_eq_checker_correct_basic :
  (∀ τ1,
     (∀ τ2, type_eq_checker τ1 τ2 = ok_term -> type_eq τ1 τ2)
  ) /\
  (∀ ft:function_type, True) /\
  (∀ ft:inner_function_type, True).
Proof.
  apply type_and_function_ind; auto; intros; destruct τ2.
  (* the goal of this big guy: filter all obvious ones. Does not include "obvious" Ser *)
  all:
    try match goal with
    | |- (type_eq (VarT _) (VarT _)) => simpl in H; repeat my_auto3_5; inversion HMatch; subst; apply TEqRefl
    | |- (type_eq (I31T _) (I31T _)) => simpl in H; repeat my_auto3_5; inversion HMatch; subst; apply TEqRefl; auto
    | |- (type_eq (NumT _ _) (NumT _ _)) => simpl in H; repeat my_auto3_5; inversion HMatch; subst; apply TEqRefl; repeat my_auto3_5
    | |- (type_eq (SumT _ _) (SumT _ _)) => idtac
    | |- (type_eq (VariantT _ _) (VariantT _ _)) => idtac
    | |- (type_eq (ProdT _ _) (ProdT _ _)) => idtac
    | |- (type_eq (StructT _ _) (StructT _ _)) => idtac
    | |- (type_eq (RefT _ _ _) (RefT _ _ _)) =>
        simpl in H0; repeat my_auto3_5; apply H in H0; apply TEqRef; auto
    | |- (type_eq (CodeRefT _ _) (CodeRefT _ _)) => simpl in *; repeat my_auto3_5; inversion HMatch; subst; apply TEqRefl; auto
    | |- (type_eq (SerT _ _) (SerT _ _)) =>
        simpl in H0; repeat my_auto3_5; apply TEqSer; auto
    | |- (type_eq (StructT _ _) (SerT _ _)) => idtac
    | |- (type_eq (SerT _ _) (StructT _ _)) => idtac
    | |- (type_eq (SerT _ _) _) => simpl in H0; my_auto3_5
    | |- (type_eq (PlugT _ _) (PlugT _ _)) => simpl in *; repeat my_auto3_5; inversion HMatch; subst; apply TEqRefl; auto
    | |- (type_eq (SpanT _ _) (SpanT _ _)) => simpl in *; repeat my_auto3_5; inversion HMatch; subst; apply TEqRefl; auto
    | |- (type_eq (RecT _ _) (RecT _ _)) =>
        simpl in H0; repeat my_auto3_5; apply H in H0; apply TEqRec; auto
    | |- (type_eq (ExistsMemT _ _) (ExistsMemT _ _)) =>
        simpl in H0; repeat my_auto3_5; apply H in H0; apply TEqExMem; auto
    | |- (type_eq (ExistsRepT _ _) (ExistsRepT _ _)) =>
        simpl in H0; repeat my_auto3_5; apply H in H0; apply TEqExRep; auto
    | |- (type_eq (ExistsSizeT _ _) (ExistsSizeT _ _)) =>
        simpl in H0; repeat my_auto3_5; apply H in H0; apply TEqExSize; auto
    | |- (type_eq (ExistsTypeT _ _ _) (ExistsTypeT _ _ _)) =>
        simpl in H0; repeat my_auto3_5; apply H in H0; apply TEqExType; auto
    | _ => simpl in *; my_auto3_5
    end.

  all: idtac. (* this is here because doom emacs despises the match goal above *)
  1-4: cbn in H0; repeat my_auto3; constructor;
    eapply convert_foldr2_bool_to_Forall2_check_ok_output; try done.
  2: {
    repeat my_auto3.
    apply H in H0.
    constructor; done.
  }
  (* struct ser case *)
  (* there's annoying monad stuff in here *)
  1: {
    cbn in H0.
    repeat structural_auto. repeat boolean_equality_auto.
    rename τs into τs_zipped.
    rename l into τs'.
    rename l0 into τs.
    apply sequence_map_zip_with in HMatch0 as (κs_ser & Hzipped & Hlen).
    symmetry in Hlen.
    rewrite Hzipped in H.
    eapply forall_unzip_sert in Hlen as Hh; last exact H.
    rewrite Hzipped.
    constructor; try done.
    eapply convert_foldr2_bool_to_Forall2_check_ok_output; try done.
    by apply flip_foldr2_bool.
  }
  (* ser struct case *)
  1: {
    cbn in H0.
    Opaque type_eq_checker.
    repeat structural_auto. repeat boolean_equality_auto.
    Transparent type_eq_checker.
    rename l into τs_zipped.
    rename l1 into τs'.
    rename l0 into τs.
    apply sequence_map_zip_with in HMatch0 as (κs_ser & Hzipped & Hlen).
    symmetry in Hlen.
    rewrite Hzipped.
    constructor; try done.
    specialize (H (ProdT k0 τs')).
    assert (type_eq_checker (ProdT k0 τs) (ProdT k0 τs') = ok_term). {
      cbn.
      assert (kind_beq k0 k0 = true) by (rewrite kind_eq_convert; done).
      rewrite H0; rewrite HMatch1; done.
    }
    apply H in H0.
    inversion H0; subst; try done.
    apply type_eq_refl_forall2.
  }

Qed.

Lemma type_eq_checker_correct :
  ∀ τ1 τ2, type_eq_checker τ1 τ2 = ok_term -> type_eq τ1 τ2.
Proof.
  pose proof type_eq_checker_correct_basic.
  destruct H as [H1 H2].
  intros.
  specialize (H1 τ1).
  auto.
Qed.

Fixpoint split_into_three (τs:list type) (i:nat) : option (list type * type * list type) :=
  match i with
  | O =>
      match τs with
      | [] => None
      | τ :: τs' => Some ([], τ, τs')
      end
  | S n =>
      match τs with
      | [] => None
      | t :: ts =>
          match split_into_three ts n with
          | None => None
          | Some (τs0, τ, τs) => Some (t :: τs0, τ, τs)
          end
      end
  end.

Lemma split_into_three_correct :
  ∀ τs i τs0 τ τs',
    split_into_three τs i = Some (τs0, τ, τs') ->
    Init.Datatypes.length τs0 = i /\ τs = τs0 ++ τ :: τs'.
Proof.
  intros τs. induction τs.
  - intros. destruct i; simpl in H; try inversion H.
  - intros. destruct i; simpl in H.
    + inversion H; subst.
      split; auto.
    + structural_auto. clear H1.
      destruct p. destruct p.
      apply IHτs in HMatch. destruct HMatch as [HL Hyeah].
      inversion H.
      subst.
      split; auto.
Qed.

Fixpoint list_prefix (lfull lpre : list type) : option (list type) :=
  match lfull, lpre with
  | τ1 :: fullrest, τ2 :: prerest =>
      if type_beq τ1 τ2
      then list_prefix fullrest prerest
      else None
  | lfull, [] => Some lfull
  | _, _ => None
  end.

Lemma list_prefix_correct_for :
  ∀ lfull lpre lsuff,
    list_prefix lfull lpre = Some lsuff -> lfull = lpre ++ lsuff.
Proof.
  induction lfull.
  - intros. destruct lpre, lsuff; simpl in H; try inversion H. auto.
  - intros.
    destruct lpre.
    + simpl in *. inversion H; auto.
    + simpl in *. structural_auto. clear H1.
      apply IHlfull in H. boolean_equality_auto.
Qed.

Lemma list_prefix_correct_back :
  ∀ lfull lpre lsuff,
    lfull = lpre ++ lsuff -> list_prefix lfull lpre = Some lsuff.
Proof.
  induction lfull.
  - intros. destruct lpre, lsuff; try inversion H. auto.
  - intros.
    destruct lpre.
    + simpl. rewrite app_nil_l in H. subst; auto.
    + inversion H; subst.
      specialize (IHlfull lpre lsuff ltac:(auto)).
      simpl.
      assert (Stupid:t=t) by auto; apply type_eq_convert in Stupid.
      rewrite Stupid. auto.
Qed.

(* TODO: there was an update in resolves path that let's κ and κ' vary. Gotta understand and fix it *)
Fixpoint resolves_path_checker
  (τ:type) (p:path) (oτ:option type) (pr':path_result) : type_checker_res :=
  match p with
  | [] =>
      match oτ with
      | Some τ' =>
          if path_result_beq pr' (Build_path_result [] τ τ')
          then ok_term
          else INR "does not resolve path"
      | None =>
          if path_result_beq pr' (Build_path_result [] τ τ)
          then ok_term
          else INR "does not resolve path"
      end
  | i :: p =>
      match τ with
      | StructT κ τs_full =>
          match split_into_three τs_full i with
          | Some (τs0, τ_inner, τs') =>
              match list_prefix pr'.(pr_prefix) τs0 with
              | Some prprefix =>
                  match pr'.(pr_replaced) with
                  | StructT κ0 inner_τs =>
                      (* if kind_beq κ κ0 *)
                      (* then *)
                      match split_into_three inner_τs i with
                      | Some (τs0', prreplaced, τs'') =>
                          if andb (list_beq type type_beq τs0 τs0') (list_beq type type_beq τs' τs'')
                          then
                            let pr := {| pr_prefix := prprefix;
                                         pr_target := pr'.(pr_target);
                                         pr_replaced := prreplaced |} in
                            resolves_path_checker τ_inner p oτ pr
                          else INR "bad path resolution"
                      | None => INR "bad replacement or smthn"
                      end
                      (* else INR "bad path stuff" *)
                  | _ => INR "improper path replacement"
                  end
              | None => INR "can't prefix?"
              end
          | None => INR "does not resolve path"
          end
      | _ => INR "does not resolves path"
      end
  end.
Lemma resolves_path_checker_correct_basic :
  ∀ p τ oτ pres, resolves_path_checker τ p oτ pres = ok_term -> resolves_path τ p oτ pres.
Proof.
  intros p.
  induction p.
  - intros. unfold resolves_path_checker in H.
    destruct oτ; repeat my_auto3_5.
    + apply PathNilSome.
    + apply PathNilNone.
  - intros.
    simpl in H. Opaque resolves_path_checker.
    repeat structural_auto. subst.
    clear H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
    repeat boolean_equality_auto; subst.
    rename l into τs_full; rename a into i; rename l5 into τs0; rename l4 into τs'.
    rename l2 into prprefix. apply list_prefix_correct_for in HMatch3. rename l3 into oldprreplaced.
    apply split_into_three_correct in HMatch0, HMatch5. destruct HMatch0 as [Hlen Htsfull].
    destruct HMatch5 as [_ Holdpr].
    set (pr := {| pr_prefix := prprefix; pr_target := pr_target pres; pr_replaced := t0 |}).
    assert (Hmaybe : pres =
                       {| pr_prefix := τs0 ++ pr.(pr_prefix);
                          pr_target := pr.(pr_target);
                          pr_replaced := StructT k0 (τs0 ++ pr.(pr_replaced) :: τs')
                       |}
           ).
    {
      destruct pres. subst.
      simpl in *. subst. auto.
    }
    rewrite Htsfull. rewrite Hmaybe.
    apply (PathStruct pr i p oτ τs0 t τs' k); auto.

Qed.

Lemma resolves_path_checker_correct :
  ∀ τ p oτ pres, resolves_path_checker τ p oτ pres = ok_term -> resolves_path τ p oτ pres.
Proof. intros. apply resolves_path_checker_correct_basic. auto. Qed.

Fixpoint synth_resolving_path
  (τ:type) (p:path) (oτ:option type) : option path_result :=
  match p with
  | [] =>
      match oτ with
      | Some τ' => Some (Build_path_result [] τ τ')
      | None => Some (Build_path_result [] τ τ)
      end
  | i :: p =>
      match τ with
      | StructT κ τs_full =>
          match split_into_three τs_full i with
          | Some (τs0, τ_inner, τs') =>
              match synth_resolving_path τ_inner p oτ with
              | Some pr =>
                  let pr' :=
                    {| pr_prefix := τs0 ++ pr.(pr_prefix);
                      pr_target := pr.(pr_target);
                      pr_replaced := StructT κ (τs0 ++ pr.(pr_replaced) :: τs') |} in
                  Some pr'
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  end
.
Lemma synth_resolving_path_correct :
  ∀ p τ oτ pres, synth_resolving_path τ p oτ = Some pres -> resolves_path τ p oτ pres.
Proof.
  induction p.
  - intros. destruct oτ.
    + simpl in H. inversion H; subst. constructor.
    + simpl in H; inversion H; subst. constructor.
  - intros. simpl in H. repeat structural_auto. clear H H1 H2 H3 H4.
    apply IHp in HMatch3.
    apply split_into_three_correct in HMatch0. destruct HMatch0 as [Hlen Hsubs].
    subst.
    constructor; auto.
Qed.

(* This is hyper specific fixpoint, used for TStoreStrong *)
Fixpoint synth_resolving_with_outer_replaced_sert
  (τ:type) (p:path) (prreplaced:type) (τval:type) : option (path_result * kind) :=
  match p with
  | [] =>
      match prreplaced with
      | SerT κser τval_inner =>
          if type_beq τval τval_inner
          then Some (Build_path_result [] τ (SerT κser τval), κser)
          else None
      | _ => None
      end
  | i :: p =>
      match τ with
      | StructT κ τs_full =>
          match split_into_three τs_full i with
          | Some (τs0, τ_inner, τs') =>
              match prreplaced with
              | StructT κ' τs_full' =>
                  match split_into_three τs_full' i with
                  | Some (τs0', innerprreplaced, τs'') =>
                      if andb (list_beq type type_beq τs0 τs0')
                              (list_beq type type_beq τs' τs'')
                      then
                        match synth_resolving_with_outer_replaced_sert τ_inner p innerprreplaced τval with
                        | Some (pr, κser) =>
                            let pr' :=
                              {| pr_prefix := τs0 ++ pr.(pr_prefix);
                                pr_target := pr.(pr_target);
                                pr_replaced := StructT κ' (τs0 ++ pr.(pr_replaced) :: τs') |} in
                            Some (pr', κser)
                        | None => None
                        end
                      else None
                  | None => None
                  end
              | _ => None
              end
          | None => None
          end
      | _ => None
      end

  end.

Lemma synth_resolving_with_outer_replaced_sert_correct :
  ∀ p τ prreplaced τval pr κser,
    synth_resolving_with_outer_replaced_sert τ p prreplaced τval = Some (pr, κser) ->
    resolves_path τ p (Some (SerT κser τval)) pr /\ pr.(pr_replaced) = prreplaced.
Proof.
  induction p.
  - intros. destruct prreplaced; simpl in *; try inversion H. repeat structural_auto. split.
    + constructor.
    + boolean_equality_auto.
  - intros. simpl in H. repeat structural_auto.
    apply split_into_three_correct in HMatch0; destruct HMatch0 as [Hlen Htosubst].
    apply split_into_three_correct in HMatch4; destruct HMatch4 as [Hlen' Htosubst'].
    repeat boolean_equality_auto.
    apply IHp in HMatch7 as [ha hi].
    split.
    + constructor; auto.
    + subst; auto.
Qed.

(* This is hyper specific fixpoint, used for TLoadMove *)
Fixpoint synth_resolving_with_outer_replaced_spant
  (τ:type) (p:path) (prreplaced:type) (τval:type) : option (path_result * kind * size) :=
  match p with
  | [] =>
      match prreplaced with
      | SpanT (MEMTYPE σ NoRefs) σ0 =>
          if size_beq σ σ0
          then
            match τ with
            | SerT κser τval' =>
                if type_beq τval τval'
                then Some (Build_path_result [] τ (SpanT (MEMTYPE σ NoRefs) σ), κser, σ)
                else None
            | _ => None
            end
          else None
      | _ => None
      end
  | i :: p =>
      match τ with
      | StructT κ τs_full =>
          match split_into_three τs_full i with
          | Some (τs0, τ_inner, τs') =>
              match prreplaced with
              | StructT κ' τs_full' =>
                  match split_into_three τs_full' i with
                  | Some (τs0', innerprreplaced, τs'') =>
                      if andb (andb (list_beq type type_beq τs0 τs0') (true))
                              (list_beq type type_beq τs' τs'')
                      then
                        match synth_resolving_with_outer_replaced_spant τ_inner p innerprreplaced τval with
                        | Some (pr, κser, σ) =>
                            let pr' :=
                              {| pr_prefix := τs0 ++ pr.(pr_prefix);
                                pr_target := pr.(pr_target);
                                pr_replaced := StructT κ' (τs0 ++ pr.(pr_replaced) :: τs') |} in
                            Some (pr', κser, σ)
                        | None => None
                        end
                      else None
                  | None => None
                  end
              | _ => None
              end
          | None => None
          end
      | _ => None
      end

  end.

Lemma synth_resolving_with_outer_replaced_spant_correct :
  ∀ p τ prreplaced σ pr τval κser,
    synth_resolving_with_outer_replaced_spant τ p prreplaced τval = Some (pr, κser, σ) ->
    resolves_path τ p (Some (type_span σ)) pr /\ pr.(pr_replaced) = prreplaced /\ pr.(pr_target) = SerT κser τval.
Proof.
  induction p.
  - intros. destruct prreplaced; simpl in *; try inversion H. repeat structural_auto. split.
    + constructor.
    + repeat boolean_equality_auto.
  - intros. simpl in H. repeat structural_auto.
    apply split_into_three_correct in HMatch0; destruct HMatch0 as [Hlen Htosubst].
    apply split_into_three_correct in HMatch4; destruct HMatch4 as [Hlen' Htosubst'].
    repeat boolean_equality_auto.
    apply IHp in HMatch7 as [ha [hi ho]].
    split.
    + constructor; auto.
    + subst; auto.
Qed.



Ltac my_auto4 :=
  try structural_auto; try boolean_equality_auto; try
  match goal with
  | H: (split_list_all_last ?l = Some (_, _)) |- _ => apply split_list_all_last_correct in H; subst l
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
  | H: (inner_function_type_ok_checker _ _ = inl ()) |- _ => apply inner_function_type_ok_checker_correct in H; auto
  | H: (inner_function_type_ok_checker _ _ = ok_term) |- _ => apply inner_function_type_ok_checker_correct in H; auto
  | H: (has_kind_ft_checker _ _ = inl ()) |- _ => apply has_kind_ft_checker_correct in H; auto
  | H: (has_kind_ft_checker _ _ = ok_term) |- _ => apply has_kind_ft_checker_correct in H; auto
  | H: (has_kind_ift_checker _ _ = inl ()) |- _ => apply has_kind_ift_checker_correct in H; auto
  | H: (has_kind_ift_checker _ _ = ok_term) |- _ => apply has_kind_ift_checker_correct in H; auto
  | H: (has_kind_checker _ _ _ = inl ()) |- _ => apply has_kind_checker_correct in H; auto
  | H: (has_kind_checker _ _ _ = ok_term) |- _ => apply has_kind_checker_correct in H; auto
end.

Definition kind_of_node (F : function_ctx) (τ : type) : kind :=
  match τ with
  | VarT t => match F.(fc_type_vars) !! t with
              | Some κ => κ
              | None => VALTYPE (AtomR I32R) NoRefs
              end
  | I31T κ | NumT κ _ | SumT κ _ | VariantT κ _ | ProdT κ _ | StructT κ _
  | RefT κ _ _ _ | CodeRefT κ _ | SerT κ _ | PlugT κ _ | SpanT κ _
  | RecT κ _ | ExistsMemT κ _ | ExistsRepT κ _ | ExistsSizeT κ _
  | ExistsTypeT κ _ _ => κ
  end.

(* rebuilds the cached kind annotations that [subst] leaves stale *)
Fixpoint refresh_kinds (F : function_ctx) (τ : type) : type :=
  match τ with
  | VarT t => VarT t
  | I31T _ => I31T (VALTYPE (AtomR PtrR) NoRefs)
  | NumT _ nt => NumT (kind_of_num nt) nt
  | SumT _ τs =>
      let τs' := map (refresh_kinds F) τs in
      let κs := map (kind_of_node F) τs' in
      SumT (VALTYPE (SumR (get_all_lefts (map get_rep_or_size κs)))
                    (ref_flag_lub (map kind_ref_flag κs))) τs'
  | VariantT _ τs =>
      let τs' := map (refresh_kinds F) τs in
      let κs := map (kind_of_node F) τs' in
      VariantT (MEMTYPE (SumS (get_all_rights (map get_rep_or_size κs)))
                        (ref_flag_lub (map kind_ref_flag κs))) τs'
  | ProdT _ τs =>
      let τs' := map (refresh_kinds F) τs in
      let κs := map (kind_of_node F) τs' in
      ProdT (VALTYPE (ProdR (get_all_lefts (map get_rep_or_size κs)))
                     (ref_flag_lub (map kind_ref_flag κs))) τs'
  | StructT _ τs =>
      let τs' := map (refresh_kinds F) τs in
      let κs := map (kind_of_node F) τs' in
      StructT (MEMTYPE (ProdS (get_all_rights (map get_rep_or_size κs)))
                       (ref_flag_lub (map kind_ref_flag κs))) τs'
  | RefT _ μ β τ =>
      let κ := match μ with
               | BaseM MemGC => VALTYPE (AtomR PtrR) GCRefs
               | _ => VALTYPE (AtomR PtrR) AnyRefs
               end in
      RefT κ μ β (refresh_kinds F τ)
  | CodeRefT _ ϕ => CodeRefT (VALTYPE (AtomR I32R) NoRefs) (refresh_kinds_ft F ϕ)
  | SerT _ τ =>
      let τ' := refresh_kinds F τ in
      let κ := match kind_of_node F τ' with
               | VALTYPE ρ ξ => MEMTYPE (RepS ρ) ξ
               | MEMTYPE σ ξ => MEMTYPE σ ξ
               end in
      SerT κ τ'
  | PlugT _ ρ => PlugT (VALTYPE ρ NoRefs) ρ
  | SpanT _ σ => SpanT (MEMTYPE σ NoRefs) σ
  | RecT κ τ => RecT κ (refresh_kinds (F <| fc_type_vars ::= cons κ |>) τ)
  | ExistsMemT κ τ =>
      ExistsMemT κ (refresh_kinds (F <| fc_kind_ctx ::= set kc_mem_vars S |>) τ)
  | ExistsRepT κ τ =>
      ExistsRepT κ (refresh_kinds (add_rep_var F) τ)
  | ExistsSizeT κ τ =>
      ExistsSizeT κ (refresh_kinds (add_size_var F) τ)
  | ExistsTypeT κ κ0 τ =>
      ExistsTypeT κ κ0 (refresh_kinds (F <| fc_type_vars ::= cons κ0 |>) τ)
  end
with refresh_kinds_ift (F : function_ctx) (ϕ : inner_function_type) : inner_function_type :=
  match ϕ with
  | MonoFunT τs1 τs2 => MonoFunT (map (refresh_kinds F) τs1) (map (refresh_kinds F) τs2)
  | ForallTypeT κ ϕ => ForallTypeT κ (refresh_kinds_ift (F <| fc_type_vars ::= cons κ |>) ϕ)
  end
with refresh_kinds_ft (F : function_ctx) (ϕ : function_type) : function_type :=
  match ϕ with
  | InnerFunT ϕ => InnerFunT (refresh_kinds_ift F ϕ)
  | ForallMemT ϕ => ForallMemT (refresh_kinds_ft (F <| fc_kind_ctx ::= set kc_mem_vars S |>) ϕ)
  | ForallRepT ϕ => ForallRepT (refresh_kinds_ft (add_rep_var F) ϕ)
  | ForallSizeT ϕ => ForallSizeT (refresh_kinds_ft (add_size_var F) ϕ)
  end.

Lemma refresh_kinds_eq_mod_kinds :
  (forall τ F, type_eq_mod_kinds (refresh_kinds F τ) τ) /\
  (forall ϕ F, function_type_eq_mod_kinds (refresh_kinds_ft F ϕ) ϕ) /\
  (forall ϕ F, inner_function_type_eq_mod_kinds (refresh_kinds_ift F ϕ) ϕ).
Proof.
  apply type_and_function_ind.
  - intros idx F; simpl; reflexivity.
  - intros κ F; simpl; exact I.
  - intros κ nt F; simpl; reflexivity.
  - intros κ ts IH F; simpl; induction IH as [|t ts' Hh Ht IHl]; simpl;
      [exact I | split; [apply Hh | exact IHl]].
  - intros κ ts IH F; simpl; induction IH as [|t ts' Hh Ht IHl]; simpl;
      [exact I | split; [apply Hh | exact IHl]].
  - intros κ ts IH F; simpl; induction IH as [|t ts' Hh Ht IHl]; simpl;
      [exact I | split; [apply Hh | exact IHl]].
  - intros κ ts IH F; simpl; induction IH as [|t ts' Hh Ht IHl]; simpl;
      [exact I | split; [apply Hh | exact IHl]].
  - intros κ μ β t IH F; simpl; split; [reflexivity | split; [reflexivity | apply IH]].
  - intros κ ft IH F; simpl; apply IH.
  - intros κ t IH F; simpl; apply IH.
  - intros κ ρ F; simpl; reflexivity.
  - intros κ σ F; simpl; reflexivity.
  - intros κ t IH F; simpl; apply IH.
  - intros κ t IH F; simpl; apply IH.
  - intros κ t IH F; simpl; apply IH.
  - intros κ t IH F; simpl; apply IH.
  - intros κ1 κ2 t IH F; simpl; split; [reflexivity | apply IH].
  - intros τs1 τs2 IH1 IH2 F; simpl; split;
      [ induction IH1 as [|t ts' Hh Ht IHl]; simpl; [exact I | split; [apply Hh | exact IHl]]
      | induction IH2 as [|t ts' Hh Ht IHl]; simpl; [exact I | split; [apply Hh | exact IHl]] ].
  - intros κ ft IH F; simpl; split; [reflexivity | apply IH].
  - done.
  - intros ft IH F; simpl; apply IH.
  - intros ft IH F; simpl; apply IH.
  - intros ft IH F; simpl; apply IH.
Qed.

Definition inner_function_type_inst_checker
  (F:function_ctx) (i:index) (ft1:inner_function_type) (ft2:inner_function_type) : type_checker_res :=
  match i with
  | TypeI τ =>
    match ft1 with
    | ForallTypeT κ ϕ =>
        match has_kind_synther F τ with
        | inl κ' =>
            match subkind_of_checker κ' κ with
            | inl () =>
                if inner_function_type_beq ft2
                     (refresh_kinds_ift F (subst_inner_function_type VarM VarR VarS (unscoped.scons τ VarT) ϕ))
                then has_kind_ift_checker F ft2
                else INR "something not matching in function type inst checker"
            | err => err
            end
        | inr err => inr [err]
        end
    | _ => INR "bad function type inst"
    end
  | _ => INR "bad function type inst"
  end.

Definition function_type_inst_checker
  (F:function_ctx) (i:index) (ft1:function_type) (ft2:function_type) : type_checker_res :=
  match ft1 with
  | InnerFunT ft1' =>
      match ft2 with
      | InnerFunT ft2' => inner_function_type_inst_checker F i ft1' ft2'
      | _ => INR "bad function type inst"
      end
  | _ =>
    match i with
    | MemI μ =>
        match mem_ok_checker F.(fc_kind_ctx) μ with
        | inl () =>
            match ft1 with
            | ForallMemT ϕ =>
                if function_type_beq ft2 (refresh_kinds_ft F (subst_function_type (unscoped.scons μ VarM) VarR VarS VarT ϕ))
                then has_kind_ft_checker F ft2 (* note this isn't technically necessary, but helps *)
                else INR "something not matching in function type inst checker"
            | _ => INR "bad function type inst"
            end
        | err => err
        end
    | RepI ρ =>
        match rep_ok_checker F.(fc_kind_ctx) ρ with
        | inl () =>
            match ft1 with
            | ForallRepT ϕ =>
                if function_type_beq ft2 (subst_function_type VarM (unscoped.scons ρ VarR) VarS VarT ϕ)
                then ok_term
                else INR "something not matching in function type inst checker"
            | _ => INR "bad function type inst"
            end
        | err => err
        end
    | SizeI σ =>
        match size_ok_checker F.(fc_kind_ctx) σ with
        | inl () =>
            match ft1 with
            | ForallSizeT ϕ =>
                if function_type_beq ft2 (subst_function_type VarM VarR (unscoped.scons σ VarS) VarT ϕ)
                then ok_term
                else INR "something not matching in function type inst checker"
            | _ => INR "bad function type inst"
            end
        | err => err
        end
    | _ => INR "bad function type inst"
    end
 end.


Lemma kind_of_node_good F τ κ:
  has_kind F τ κ -> κ = kind_of_node F τ.
Proof.
  intros Hkind.
  induction Hkind using has_kind_ind' with (P0 := const (const True)) (Pi := const (const True));
    intros; cbn; try done; try (rewrite <- IHHkind; done).
  rewrite H. done.
Qed.

Lemma Forall3_by_lookup {A B C : Type} (P: A -> B -> C -> Prop) : ∀ l m r,
  Datatypes.length l = Datatypes.length m -> Datatypes.length m = Datatypes.length r ->
  (∀ i li mi ri, l !! i = Some li -> m !! i = Some mi -> r !! i = Some ri -> P li mi ri) ->
  Forall3 P l m r.
Proof.
  induction l as [|l1 l]; intros m r HLlm HLmr HP.
  - destruct m; try by inversion HLlm. destruct r; try by inversion HLmr.
    constructor.
  - destruct m as [|m1 m]; try by inversion HLlm.
    destruct r as [|r1 r]; try by inversion HLmr.
    cbn in HLlm; cbn in HLmr. inversion HLlm; inversion HLmr.
    specialize (IHl _ _ H0 H1); clear H0 H1 HLlm HLmr.
    constructor.
    + by specialize (HP 0 l1 m1 r1 ltac:(auto) ltac:(auto) ltac:(auto)).
    + apply IHl.
      intros i li mi ri Hli Hmi Hri.
      specialize (HP (S i) li mi ri).
      apply HP; cbn; auto.
Qed.

Lemma has_kind_type_kind :
  ∀ F τ κ, has_kind F τ κ -> type_kind (fc_type_vars F) τ = Some κ.
Proof.
    intros * Hkk.
    apply type_kind_has_kind_is_Some in Hkk as IsSome.
    inversion IsSome; subst.
    rewrite H. f_equal. symmetry.
    eapply type_kind_has_kind_agree; done.
Qed.


Lemma refresh_kinds_connect_has_kind_maybe :
  (∀ τ F κ, has_kind F (refresh_kinds F τ) κ -> refreshed_kinds F τ (refresh_kinds F τ)) /\
  (∀ ϕ F, has_kind_ft F (refresh_kinds_ft F ϕ) -> refreshed_kinds_ft F ϕ (refresh_kinds_ft F ϕ)) /\
    (∀ ϕ F, has_kind_ift F (refresh_kinds_ift F ϕ) -> refreshed_kinds_ift F ϕ (refresh_kinds_ift F ϕ)).
Proof.
  apply type_and_function_ind; intros *.
  - intros Hk; cbn in *; inversion Hk; subst. constructor.
  - intros Hk; cbn in *; inversion Hk; subst. constructor.
  - intros Hk; cbn in *; inversion Hk; subst; constructor.
  - intros IH * Hk. cbn in *. inversion Hk; subst.
    set (ρs' := (get_all_lefts
                   (map get_rep_or_size (map (kind_of_node F) (map (refresh_kinds F) τs))))) in *.
    set (κs' := zip_with VALTYPE ρs' ξs).
    apply RKSum with (κs':=κs').
    + apply Forall2_same_length_lookup_2.
      { symmetry; apply length_map. }
      intros i t rt Ht Hrt.
      pose proof (Forall_lookup_1 _ _ _ _ IH Ht).
      specialize (H F).
      apply map_lookup_helper_backwards in Hrt as Hrt'.
      destruct Hrt' as (tosub & torewr & Hrt').
      rewrite Ht in torewr; inversion torewr; subst tosub; clear torewr. subst.
      pose proof (Forall3_lookup_l _ _ _ _ _ _ H4 Hrt).
      repeat destruct H0. destruct H1.
      specialize (H _ H1).
      done.
    + apply mapM_Some_2.
      apply Forall2_same_length_lookup_2.
      {
        subst κs'.
        rewrite length_zip_with.
        rewrite <- (Forall3_length_lr _ _ _ _ H4).
        rewrite <- (Forall3_length_lm _ _ _ _ H4).
        lia.
      }
      intros i rt rk Hrt Hrk.
      pose proof (Forall3_lookup_l _ _ _ _ _ _ H4 Hrt).
      destruct H as (ρ & ξ & Hρ & Hξ & Htkind).
      apply has_kind_type_kind.
      assert (rk = VALTYPE ρ ξ). {
        subst κs'.
        rewrite lookup_zip_with in Hrk.
        rewrite Hρ in Hrk; rewrite Hξ in Hrk. cbn in Hrk.
        inversion Hrk; done.
      }
      subst. done.
    + apply Forall3_by_lookup.
      {
        subst κs'. rewrite length_zip_with.
        rewrite <- (Forall3_length_lm _ _ _ _ H4).
        rewrite <- (Forall3_length_lr _ _ _ _ H4).
        lia.
      }
      {
        rewrite <- (Forall3_length_lm _ _ _ _ H4).
        rewrite <- (Forall3_length_lr _ _ _ _ H4).
        lia.
      }
      intros i kk rr xx Hrk Hρ Hξ.
      subst κs'.
      rewrite lookup_zip_with in Hrk.
      rewrite Hρ in Hrk; rewrite Hξ in Hrk. cbn in Hrk.
      inversion Hrk; done.
  - intros IH * Hk. cbn in *. inversion Hk; subst.
    set (σs' := (get_all_rights
                   (map get_rep_or_size (map (kind_of_node F) (map (refresh_kinds F) τs))))) in *.
    set (κs' := zip_with MEMTYPE σs' ξs).
    apply RKVariant with (κs':=κs').
    + apply Forall2_same_length_lookup_2.
      { symmetry; apply length_map. }
      intros i t rt Ht Hrt.
      pose proof (Forall_lookup_1 _ _ _ _ IH Ht).
      specialize (H F).
      apply map_lookup_helper_backwards in Hrt as Hrt'.
      destruct Hrt' as (tosub & torewr & Hrt').
      rewrite Ht in torewr; inversion torewr; subst tosub; clear torewr. subst.
      pose proof (Forall3_lookup_l _ _ _ _ _ _ H4 Hrt).
      repeat destruct H0. destruct H1.
      specialize (H _ H1).
      done.
    + apply mapM_Some_2.
      apply Forall2_same_length_lookup_2.
      {
        subst κs'.
        rewrite length_zip_with.
        rewrite <- (Forall3_length_lr _ _ _ _ H4).
        rewrite <- (Forall3_length_lm _ _ _ _ H4).
        lia.
      }
      intros i rt rk Hrt Hrk.
      pose proof (Forall3_lookup_l _ _ _ _ _ _ H4 Hrt).
      destruct H as (ρ & ξ & Hρ & Hξ & Htkind).
      apply has_kind_type_kind.
      assert (rk = MEMTYPE ρ ξ). {
        subst κs'.
        rewrite lookup_zip_with in Hrk.
        rewrite Hρ in Hrk; rewrite Hξ in Hrk. cbn in Hrk.
        inversion Hrk; done.
      }
      subst. done.
    + apply Forall3_by_lookup.
      {
        subst κs'. rewrite length_zip_with.
        rewrite <- (Forall3_length_lm _ _ _ _ H4).
        rewrite <- (Forall3_length_lr _ _ _ _ H4).
        lia.
      }
      {
        rewrite <- (Forall3_length_lm _ _ _ _ H4).
        rewrite <- (Forall3_length_lr _ _ _ _ H4).
        lia.
      }
      intros i kk rr xx Hrk Hρ Hξ.
      subst κs'.
      rewrite lookup_zip_with in Hrk.
      rewrite Hρ in Hrk; rewrite Hξ in Hrk. cbn in Hrk.
      inversion Hrk; done.
  - intros IH * Hk. cbn in *. inversion Hk; subst.
    set (ρs' := (get_all_lefts
                   (map get_rep_or_size (map (kind_of_node F) (map (refresh_kinds F) τs))))) in *.
    set (κs' := zip_with VALTYPE ρs' ξs).
    apply RKProd with (κs':=κs').
    + apply Forall2_same_length_lookup_2.
      { symmetry; apply length_map. }
      intros i t rt Ht Hrt.
      pose proof (Forall_lookup_1 _ _ _ _ IH Ht).
      specialize (H F).
      apply map_lookup_helper_backwards in Hrt as Hrt'.
      destruct Hrt' as (tosub & torewr & Hrt').
      rewrite Ht in torewr; inversion torewr; subst tosub; clear torewr. subst.
      pose proof (Forall3_lookup_l _ _ _ _ _ _ H4 Hrt).
      repeat destruct H0. destruct H1.
      specialize (H _ H1).
      done.
    + apply mapM_Some_2.
      apply Forall2_same_length_lookup_2.
      {
        subst κs'.
        rewrite length_zip_with.
        rewrite <- (Forall3_length_lr _ _ _ _ H4).
        rewrite <- (Forall3_length_lm _ _ _ _ H4).
        lia.
      }
      intros i rt rk Hrt Hrk.
      pose proof (Forall3_lookup_l _ _ _ _ _ _ H4 Hrt).
      destruct H as (ρ & ξ & Hρ & Hξ & Htkind).
      apply has_kind_type_kind.
      assert (rk = VALTYPE ρ ξ). {
        subst κs'.
        rewrite lookup_zip_with in Hrk.
        rewrite Hρ in Hrk; rewrite Hξ in Hrk. cbn in Hrk.
        inversion Hrk; done.
      }
      subst. done.
    + apply Forall3_by_lookup.
      {
        subst κs'. rewrite length_zip_with.
        rewrite <- (Forall3_length_lm _ _ _ _ H4).
        rewrite <- (Forall3_length_lr _ _ _ _ H4).
        lia.
      }
      {
        rewrite <- (Forall3_length_lm _ _ _ _ H4).
        rewrite <- (Forall3_length_lr _ _ _ _ H4).
        lia.
      }
      intros i kk rr xx Hrk Hρ Hξ.
      subst κs'.
      rewrite lookup_zip_with in Hrk.
      rewrite Hρ in Hrk; rewrite Hξ in Hrk. cbn in Hrk.
      inversion Hrk; done.
  - intros IH * Hk. cbn in *. inversion Hk; subst.
    set (σs' := (get_all_rights
                   (map get_rep_or_size (map (kind_of_node F) (map (refresh_kinds F) τs))))) in *.
    set (κs' := zip_with MEMTYPE σs' ξs).
    apply RKStruct with (κs':=κs').
    + apply Forall2_same_length_lookup_2.
      { symmetry; apply length_map. }
      intros i t rt Ht Hrt.
      pose proof (Forall_lookup_1 _ _ _ _ IH Ht).
      specialize (H F).
      apply map_lookup_helper_backwards in Hrt as Hrt'.
      destruct Hrt' as (tosub & torewr & Hrt').
      rewrite Ht in torewr; inversion torewr; subst tosub; clear torewr. subst.
      pose proof (Forall3_lookup_l _ _ _ _ _ _ H4 Hrt).
      repeat destruct H0. destruct H1.
      specialize (H _ H1).
      done.
    + apply mapM_Some_2.
      apply Forall2_same_length_lookup_2.
      {
        subst κs'.
        rewrite length_zip_with.
        rewrite <- (Forall3_length_lr _ _ _ _ H4).
        rewrite <- (Forall3_length_lm _ _ _ _ H4).
        lia.
      }
      intros i rt rk Hrt Hrk.
      pose proof (Forall3_lookup_l _ _ _ _ _ _ H4 Hrt).
      destruct H as (ρ & ξ & Hρ & Hξ & Htkind).
      apply has_kind_type_kind.
      assert (rk = MEMTYPE ρ ξ). {
        subst κs'.
        rewrite lookup_zip_with in Hrk.
        rewrite Hρ in Hrk; rewrite Hξ in Hrk. cbn in Hrk.
        inversion Hrk; done.
      }
      subst. done.
    + apply Forall3_by_lookup.
      {
        subst κs'. rewrite length_zip_with.
        rewrite <- (Forall3_length_lm _ _ _ _ H4).
        rewrite <- (Forall3_length_lr _ _ _ _ H4).
        lia.
      }
      {
        rewrite <- (Forall3_length_lm _ _ _ _ H4).
        rewrite <- (Forall3_length_lr _ _ _ _ H4).
        lia.
      }
      intros i kk rr xx Hrk Hρ Hξ.
      subst κs'.
      rewrite lookup_zip_with in Hrk.
      rewrite Hρ in Hrk; rewrite Hξ in Hrk. cbn in Hrk.
      inversion Hrk; done.
  - intros IH * Hk.
    destruct μ; try destruct b.
    all: cbn in *.
    all: inversion Hk; subst.
    all: constructor.
    all: eapply IH; try done.
  - intros IH * Hk.
    cbn in *; inversion Hk; subst.
    constructor.
    eapply IH; try done.
  - intros IH * Hk.
    inversion Hk; subst.
    cbn in *.
    apply kind_of_node_good in H3 as Hnode.
    rewrite <- Hnode in Hk.
    rewrite <- Hnode in H.
    eapply RKSer.
    + eapply IH; try done.
    + rewrite <- Hnode.
      by apply has_kind_type_kind.
  - intros Hk; inversion Hk; subst; constructor.
  - intros Hk; inversion Hk; subst; constructor.
  - intros IH * Hk.
    inversion Hk; subst.
    apply IH in H3.
    by eapply RKRec.
  - intros IH * Hk.
    inversion Hk; subst.
    apply IH in H4.
    constructor; done.
  - intros IH * Hk.
    inversion Hk; subst.
    apply IH in H4.
    constructor; done.
  - intros IH * Hk.
    inversion Hk; subst.
    apply IH in H4.
    constructor; done.
  - intros IH * Hk.
    inversion Hk; subst.
    apply IH in H6.
    constructor; done.
  - intros IH1 IH2 F Hk.
    inversion Hk; subst.
    cbn.
    rename H2 into H1. rename H3 into H2.
    constructor.
    + apply Forall2_same_length_lookup_2.
      { symmetry. apply length_map. }
      intros i t rt Ht Hrt.
      pose proof (Forall_lookup_1 _ _ _ _ IH1 Ht).
      specialize (H F).
      apply map_lookup_helper_backwards in Hrt as Hrt'.
      destruct Hrt' as (tosub & torewr & Hrt').
      rewrite Ht in torewr; inversion torewr; subst tosub; clear torewr. subst.
      pose proof (Forall2_lookup_l _ _ _ _ _ H1 Hrt).
      repeat destruct H0.
      specialize (H _ H3).
      done.
    + apply Forall2_same_length_lookup_2.
      { symmetry. apply length_map. }
      intros i t rt Ht Hrt.
      pose proof (Forall_lookup_1 _ _ _ _ IH2 Ht).
      specialize (H F).
      apply map_lookup_helper_backwards in Hrt as Hrt'.
      destruct Hrt' as (tosub & torewr & Hrt').
      rewrite Ht in torewr; inversion torewr; subst tosub; clear torewr. subst.
      pose proof (Forall2_lookup_l _ _ _ _ _ H2 Hrt).
      repeat destruct H0.
      specialize (H _ H3).
      done.
  - intros IH F Hk.
    cbn in *.
    inversion Hk; subst.
    apply IH in H3.
    constructor; done.
  - intros IH F Hk.
    cbn in *.
    inversion Hk; subst.
    apply IH in H1.
    constructor; done.
  - intros IH F Hk.
    inversion Hk; subst.
    apply IH in H1.
    constructor; done.
  - intros IH F Hk.
    inversion Hk; subst.
    apply IH in H1.
    constructor; done.
  - intros IH F Hk.
    inversion Hk; subst.
    apply IH in H1.
    constructor; done.
Qed.

Lemma inner_function_type_inst_checker_correct :
  ∀ F i ft1 ft2,
    inner_function_type_inst_checker F i ft1 ft2 = ok_term ->
    inner_function_type_inst F i ft1 ft2.
Proof.
  unfold inner_function_type_inst_checker; intros.
  repeat my_auto4.
  clear H1 H2 H3 H4 H5.
  apply subkind_of_checker_correct in HMatch2.
  apply has_kind_synther_correct in HMatch1.
  destruct refresh_kinds_eq_mod_kinds as [_ [Hrefresh_ft Hrefresh_ift]].
  econstructor.
  all:eauto.
  apply refresh_kinds_connect_has_kind_maybe. done.
Qed.

Lemma function_type_inst_checker_correct :
  ∀ F i ft1 ft2, function_type_inst_checker F i ft1 ft2 = ok_term -> function_type_inst F i ft1 ft2.
Proof.
  unfold function_type_inst_checker; intros.
  destruct ft1.
  {
    destruct ft2; try by (inversion H).
    constructor.
    by eapply inner_function_type_inst_checker_correct.
  }
  - repeat my_auto4; subst; try by inversion H.
    clear H1 H2 H3.
    (* todo, add refreshing into mem stuff *)
    constructor; auto.
    by apply refresh_kinds_connect_has_kind_maybe.
  - repeat my_auto4; try inversion H.
    constructor; auto.
  - repeat my_auto4; try inversion H.
    constructor; auto.
Qed.

Definition grab_substed_ift F (ix:index) (ft1:inner_function_type) : option inner_function_type :=
  match ix with
  | TypeI τ =>
       match ft1 with
      | ForallTypeT κ ϕ =>
          (* NOTE: accept a strict-subkind witness, then refresh so the intermediate fed to the next instantiation is well-kinded. *)
          match has_kind_synther F τ with
          | inl κ' =>
              match subkind_of_checker κ' κ with
              | inl () =>
                  Some (refresh_kinds_ift F
                          (subst_inner_function_type VarM VarR VarS (unscoped.scons τ VarT) ϕ))
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

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
      | InnerFunT ϕ => InnerFunT <$> grab_substed_ift F (TypeI τ) ϕ
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

(* Note: *second* one has to be the one with vars *)
Definition memory_find_0 m1 m2 : option memory :=
  match m2 with
  | VarM n =>
      if (n =? 0) then Some m1 else None
  | _ => None
  end.

Definition rep_find_0 r1 r2 : option representation :=
  match r2 with
  | VarR n =>
      if (n =? 0) then Some r1 else None
  | _ => None
  end.

Definition size_find_0 s1 s2 : option size :=
  match s2 with
  | VarS n =>
      if (n =? 0) then Some s1 else None
  | _ => None
  end.

Definition kind_find_rep_0 k1 k2 : option representation :=
  match k1, k2 with
  | VALTYPE ρ1 _, VALTYPE ρ2 _ => rep_find_0 ρ1 ρ2
  | _, _ => None
  end.
Definition kind_find_size_0 k1 k2 : option size :=
  match k1, k2 with
  | MEMTYPE σ1 _, MEMTYPE σ2 _ => size_find_0 σ1 σ2
  | _, _ => None
  end.

(* NOTE: if there's a bug, it's in finding the substs stuff *)
Fixpoint traverse_type_find_memory_0 τ1 τ2 : option memory :=
  match τ1, τ2 with
  | RefT _ μ1 _ τa, RefT _ μ2 _ τb =>
      match memory_find_0 μ1 μ2 with
      | None => traverse_type_find_memory_0 τa τb
      | Some a => Some a
      end
  | SumT _ τs1, SumT _ τs2
  | VariantT _ τs1, VariantT _ τs2
  | ProdT _ τs1, ProdT _ τs2
  | StructT _ τs1, StructT _ τs2 => traverse_types_find_memory τs1 τs2
  | SerT _ τa, SerT _ τb
  | RecT _ τa, RecT _ τb
  | ExistsMemT _ τa, ExistsMemT _ τb
  | ExistsRepT _ τa, ExistsRepT _ τb
  | ExistsSizeT _ τa, ExistsSizeT _ τb
  | ExistsTypeT _ _ τa, ExistsTypeT _ _ τb => traverse_type_find_memory_0 τa τb
  | CodeRefT _ ϕ1, CodeRefT _ ϕ2 => traverse_function_type_find_memory ϕ1 ϕ2
  | _, _ => None
  end
with traverse_types_find_memory τs1 τs2 : option memory :=
  match τs1, τs2 with
  | [], _ => None
  | _, [] => None
  | t1::ts1, t2::ts2 =>
      (* f: type -> type -> option memory -> option memory *)
      foldr2 (λ t1:type, λ t2:type, λ acc:option memory,
        match acc with
        | None => traverse_type_find_memory_0 t1 t2
        | Some a => Some a
        end
        ) None τs1 τs2
  end
with traverse_inner_function_type_find_memory ϕ1 ϕ2 : option memory :=
  match ϕ1, ϕ2 with
  | MonoFunT τs11 τs12, MonoFunT τs21 τs22 =>
      match traverse_types_find_memory τs11 τs21 with
      | None => traverse_types_find_memory τs12 τs22
      | Some a => Some a
      end
  | ForallTypeT _ f1, ForallTypeT _ f2 => traverse_inner_function_type_find_memory f1 f2
  | _, _ => None
  end
with traverse_function_type_find_memory ϕ1 ϕ2 : option memory :=
  match ϕ1, ϕ2 with
  | InnerFunT ϕ1', InnerFunT ϕ2' => traverse_inner_function_type_find_memory ϕ1' ϕ2'
  | ForallMemT f1, ForallMemT f2
  | ForallRepT f1, ForallRepT f2
  | ForallSizeT f1, ForallSizeT f2 => traverse_function_type_find_memory f1 f2
  | _, _ => None
  end.

(* NOTE: if there's a bug, it's in finding the substs stuff *)
(* [d] = binders crossed, so the existential is [VarT d] and the witness shifts down by [d]. *)
Fixpoint traverse_type_find_type_0 (d : nat) τ1 τ2 : option type :=
  match τ1, τ2 with
  | _, VarT n =>
      if (n =? d)
      then Some (subst_type VarM VarR VarS (λ m : nat, VarT (m - d)) τ1)
      else None
  | SumT _ τs1, SumT _ τs2
  | VariantT _ τs1, VariantT _ τs2
  | ProdT _ τs1, ProdT _ τs2
  | StructT _ τs1, StructT _ τs2 => traverse_types_find_type d τs1 τs2
  | SerT _ τa, SerT _ τb
  | RefT _ _ _ τa, RefT _ _ _ τb
  | ExistsMemT _ τa, ExistsMemT _ τb
  | ExistsRepT _ τa, ExistsRepT _ τb
  | ExistsSizeT _ τa, ExistsSizeT _ τb => traverse_type_find_type_0 d τa τb
  | RecT _ τa, RecT _ τb
  | ExistsTypeT _ _ τa, ExistsTypeT _ _ τb => traverse_type_find_type_0 (S d) τa τb
  | CodeRefT _ ϕ1, CodeRefT _ ϕ2 => traverse_function_type_find_type d ϕ1 ϕ2
  | _, _ => None
  end
with traverse_types_find_type (d : nat) τs1 τs2 : option type :=
  match τs1, τs2 with
  | [], _ => None
  | _, [] => None
  | t1::ts1, t2::ts2 =>
      foldr2 (λ t1:type, λ t2:type, λ acc:option type,
        match acc with
        | None => traverse_type_find_type_0 d t1 t2
        | Some a => Some a
        end
        ) None τs1 τs2
  end
with traverse_inner_function_type_find_type (d : nat) ϕ1 ϕ2 : option type :=
  match ϕ1, ϕ2 with
  | MonoFunT τs11 τs12, MonoFunT τs21 τs22 =>
      match traverse_types_find_type d τs11 τs21 with
      | None => traverse_types_find_type d τs12 τs22
      | Some a => Some a
      end
  | ForallTypeT _ f1, ForallTypeT _ f2 => traverse_inner_function_type_find_type (S d) f1 f2
  | _, _ => None
  end
with traverse_function_type_find_type (d : nat) ϕ1 ϕ2 : option type :=
  match ϕ1, ϕ2 with
  | InnerFunT ϕ1', InnerFunT ϕ2' =>
      traverse_inner_function_type_find_type d ϕ1' ϕ2'
  | ForallMemT f1, ForallMemT f2
  | ForallRepT f1, ForallRepT f2
  | ForallSizeT f1, ForallSizeT f2 => traverse_function_type_find_type d f1 f2
  | _, _ => None
  end.

(* NOTE: if there's a bug, it's in finding the substs stuff *)
Fixpoint traverse_type_find_size_0 τ1 τ2 : option size :=
  match τ1, τ2 with
  | SpanT k1 s1, SpanT k2 s2 =>
      match size_find_0 s1 s2 with
      | Some a => Some a
      | None => kind_find_size_0 k1 k2
      end
  | I31T k1, I31T k2
  | NumT k1 _, NumT k2 _
  | PlugT k1 _, PlugT k2 _ => kind_find_size_0 k1 k2
  | SumT k1 τs1, SumT k2 τs2
  | VariantT k1 τs1, VariantT k2 τs2
  | ProdT k1 τs1, ProdT k2 τs2
  | StructT k1 τs1, StructT k2 τs2 =>
      match kind_find_size_0 k1 k2 with
      | Some a => Some a
      | None => traverse_types_find_size τs1 τs2
      end
  | SerT k1 τa, SerT k2 τb
  | RecT k1 τa, RecT k2 τb
  | RefT k1 _ _ τa, RefT k2 _ _ τb
  | ExistsMemT k1 τa, ExistsMemT k2 τb
  | ExistsRepT k1 τa, ExistsRepT k2 τb
  | ExistsSizeT k1 τa, ExistsSizeT k2 τb =>
      match kind_find_size_0 k1 k2 with
      | Some a => Some a
      | None => traverse_type_find_size_0 τa τb
      end
  | ExistsTypeT k11 k12 τa, ExistsTypeT k21 k22 τb =>
      match kind_find_size_0 k11 k21 with
      | Some a => Some a
      | None =>
          match kind_find_size_0 k12 k22 with
          | Some a => Some a
          | None => traverse_type_find_size_0 τa τb
          end
      end
  | CodeRefT k1 ϕ1, CodeRefT k2 ϕ2 =>
      match kind_find_size_0 k1 k2 with
      | Some a => Some a
      | None => traverse_function_type_find_size ϕ1 ϕ2
      end
  | _, _ => None
  end
with traverse_types_find_size τs1 τs2 : option size :=
  match τs1, τs2 with
  | [], _ => None
  | _, [] => None
  | t1::ts1, t2::ts2 =>
      (* f: type -> type -> option memory -> option memory *)
      foldr2 (λ t1:type, λ t2:type, λ acc:option size,
        match acc with
        | None => traverse_type_find_size_0 t1 t2
        | Some a => Some a
        end
        ) None τs1 τs2
  end
with traverse_inner_function_type_find_size ϕ1 ϕ2 : option size :=
  match ϕ1, ϕ2 with
  | MonoFunT τs11 τs12, MonoFunT τs21 τs22 =>
      match traverse_types_find_size τs11 τs21 with
      | None => traverse_types_find_size τs12 τs22
      | Some a => Some a
      end
  | ForallTypeT k1 f1, ForallTypeT k2 f2 =>
      match kind_find_size_0 k1 k2 with
      | Some a => Some a
      | None => traverse_inner_function_type_find_size f1 f2
      end
  | _, _ => None
  end
with traverse_function_type_find_size ϕ1 ϕ2 : option size :=
  match ϕ1, ϕ2 with
  | InnerFunT ϕ1', InnerFunT ϕ2' =>
      traverse_inner_function_type_find_size ϕ1' ϕ2'
  | ForallMemT f1, ForallMemT f2
  | ForallRepT f1, ForallRepT f2
  | ForallSizeT f1, ForallSizeT f2 =>
      traverse_function_type_find_size f1 f2
  | _, _ => None
  end.


(* NOTE: if there's a bug, it's in finding the substs stuff *)
Fixpoint traverse_type_find_rep_0 τ1 τ2 : option representation :=
  match τ1, τ2 with
  | PlugT k1 r1, PlugT k2 r2 =>
      match rep_find_0 r1 r2 with
      | Some a => Some a
      | None => kind_find_rep_0 k1 k2
      end
  | I31T k1, I31T k2
  | NumT k1 _, NumT k2 _
  | SpanT k1 _, SpanT k2 _ => kind_find_rep_0 k1 k2
  | SumT k1 τs1, SumT k2 τs2
  | VariantT k1 τs1, VariantT k2 τs2
  | ProdT k1 τs1, ProdT k2 τs2
  | StructT k1 τs1, StructT k2 τs2 =>
      match kind_find_rep_0 k1 k2 with
      | Some a => Some a
      | None => traverse_types_find_rep τs1 τs2
      end
  | SerT k1 τa, SerT k2 τb
  | RecT k1 τa, RecT k2 τb
  | RefT k1 _ _ τa, RefT k2 _ _ τb
  | ExistsMemT k1 τa, ExistsMemT k2 τb
  | ExistsRepT k1 τa, ExistsRepT k2 τb
  | ExistsSizeT k1 τa, ExistsSizeT k2 τb =>
      match kind_find_rep_0 k1 k2 with
      | Some a => Some a
      | None => traverse_type_find_rep_0 τa τb
      end
  | ExistsTypeT k11 k12 τa, ExistsTypeT k21 k22 τb =>
      match kind_find_rep_0 k11 k21 with
      | Some a => Some a
      | None =>
          match kind_find_rep_0 k12 k22 with
          | Some a => Some a
          | None => traverse_type_find_rep_0 τa τb
          end
      end
  | CodeRefT k1 ϕ1, CodeRefT k2 ϕ2 =>
      match kind_find_rep_0 k1 k2 with
      | Some a => Some a
      | None => traverse_function_type_find_rep ϕ1 ϕ2
      end
  | _, _ => None
  end
with traverse_types_find_rep τs1 τs2 : option representation :=
  match τs1, τs2 with
  | [], _ => None
  | _, [] => None
  | t1::ts1, t2::ts2 =>
      (* f: type -> type -> option rep -> option rep *)
      foldr2 (λ t1:type, λ t2:type, λ acc:option representation,
        match acc with
        | None => traverse_type_find_rep_0 t1 t2
        | Some a => Some a
        end
        ) None τs1 τs2
  end
with traverse_inner_function_type_find_rep ϕ1 ϕ2 : option representation :=
  match ϕ1, ϕ2 with
  | MonoFunT τs11 τs12, MonoFunT τs21 τs22 =>
      match traverse_types_find_rep τs11 τs21 with
      | None => traverse_types_find_rep τs12 τs22
      | Some a => Some a
      end
  | ForallTypeT k1 f1, ForallTypeT k2 f2 =>
      match kind_find_rep_0 k1 k2 with
      | Some a => Some a
      | None => traverse_inner_function_type_find_rep f1 f2
      end
  | _, _ => None
  end
with traverse_function_type_find_rep ϕ1 ϕ2 : option representation :=
  match ϕ1, ϕ2 with
  | InnerFunT ϕ1', InnerFunT ϕ2' =>
      traverse_inner_function_type_find_rep ϕ1' ϕ2'
  | ForallMemT f1, ForallMemT f2
  | ForallRepT f1, ForallRepT f2
  | ForallSizeT f1, ForallSizeT f2 =>
      traverse_function_type_find_rep f1 f2
  | _, _ => None
  end.

(* TODO man I should do some sort of proof about these find reps but oh well *)

(* Technically.... done? *)
Definition packed_existential_checker (F:function_ctx) (τ0 τ2:type) : type_checker_res :=
  match τ2 with
  | ExistsMemT κ' τ' =>
          match traverse_type_find_memory_0 τ0 τ' with
          | Some μ =>
              if type_beq τ0 ((subst_type (unscoped.scons μ VarM) VarR VarS VarT) τ')
              then ok_term
              else INR "something went wrong with packed mem"
          | None => INR "couldn't find μ for packed mem"
          end
  | ExistsRepT κ' τ' =>
          match traverse_type_find_rep_0 τ0 τ' with
          | Some ρ =>
              if type_beq τ0 ((subst_type VarM (unscoped.scons ρ VarR) VarS VarT) τ')
              then ok_term
              else INR "something went wrong with packed mem"
          | None => INR "couldn't find μ for packed mem"
          end
  | ExistsSizeT κ' τ' =>
          match traverse_type_find_size_0 τ0 τ' with
          | Some σ =>
              if type_beq τ0 ((subst_type VarM VarR (unscoped.scons σ VarS) VarT) τ')
              then ok_term
              else INR "something went wrong with packed mem"
          | None => INR "couldn't find μ for packed mem"
          end
  | ExistsTypeT κ_ex κ_max τ_in =>
          match traverse_type_find_type_0 0 τ0 τ_in with
          | Some τ_wit =>
              if type_beq τ0
                   (refresh_kinds F ((subst_type VarM VarR VarS (unscoped.scons τ_wit VarT)) τ_in))
              then
                match has_kind_synther F τ_wit with
                | inl κ_wit =>
                    match subkind_of_checker κ_wit κ_max with
                    | inl () =>
                        match has_kind_synther F τ0 with
                        | inl _ => ok_term
                        | inr err => inr [err]
                        end
                    | err => err
                    end
                | inr err => inr [err]
                end
              else INR "something went wrong with packed mem"
          | None => INR "couldn't find μ for packed mem"
          end
  | _ => INR "trying to check existential type, but not existential"
  end.

Lemma packed_existential_checker_correct :
  ∀ F τ1 τ2, packed_existential_checker F τ1 τ2 = ok_term -> packed_existential F τ1 τ2.
Proof.
  intros.
  destruct τ2; simpl in *; try (by inversion H); try (repeat my_auto4; by constructor).
  repeat my_auto4.
  apply has_kind_synther_correct in HMatch0, HMatch2.
  match goal with H : subkind_of_checker _ _ = _ |- _ => apply subkind_of_checker_correct in H end.
  destruct refresh_kinds_eq_mod_kinds as [Hrefresh _].
  eapply PackType; [exact HMatch0 | exact HMatch1 | exact HMatch2 | apply Hrefresh].
Qed.


(* This one has the reverse list stuff which I'm unsure how to do exactly *)
Definition unpacked_existential_checker
 (F:function_ctx) (L:local_ctx) (ϕ : instruction_type) (L':local_ctx)
 (F0_tocheck:function_ctx) (L_tocheck:local_ctx) (ϕ0: instruction_type) (L'_tocheck:local_ctx)
  :=
  match ϕ, ϕ0 with
  | InstrT τs1_full τs2, InstrT τs1_full_check τs2_check =>
      match split_list_all_last τs1_full with
      | Some (τs1, τex) =>
          match split_list_all_last τs1_full_check with
          | Some (τs1_check, τ) =>
              (* now we have to split on the τex *)
              match τex with
              | ExistsMemT κ τ_check =>
                  let F0 := subst_function_ctx (up_memory VarM) VarR VarS VarT F
                              <| fc_kind_ctx ::= set kc_mem_vars S |> in
                  let up := ren_type S id id id in
                  (* HUGE amount of equalities *)
                  if type_beq τ τ_check && local_ctx_beq L_tocheck (map up L) && local_ctx_beq L'_tocheck (map up L')
                     && list_beq type type_beq τs1_check (map up τs1) && list_beq type type_beq τs2_check (map up τs2)
                     && function_ctx_beq F0 F0_tocheck
                  then ok_term
                  else INR "something in unpacked existential didn't match up"
              | ExistsRepT κ τ_check =>
                  let F0 := add_rep_var (subst_function_ctx VarM (up_representation VarR) VarS VarT F)
                              in
                  let up := ren_type id S id id in
                  (* HUGE amount of equalities *)
                  if type_beq τ τ_check && local_ctx_beq L_tocheck (map up L) && local_ctx_beq L'_tocheck (map up L')
                     && list_beq type type_beq τs1_check (map up τs1) && list_beq type type_beq τs2_check (map up τs2)
                     && function_ctx_beq F0 F0_tocheck
                  then ok_term
                  else INR "something in unpacked existential didn't match up"
              | ExistsSizeT κ τ_check =>
                  let F0 := add_size_var (subst_function_ctx VarM VarR (up_size VarS) VarT F)
                              in
                  let up := ren_type id id S id in
                  (* HUGE amount of equalities *)
                  if type_beq τ τ_check && local_ctx_beq L_tocheck (map up L) && local_ctx_beq L'_tocheck (map up L')
                     && list_beq type type_beq τs1_check (map up τs1) && list_beq type type_beq τs2_check (map up τs2)
                     && function_ctx_beq F0 F0_tocheck
                  then ok_term
                  else INR "something in unpacked existential didn't match up"
              | ExistsTypeT κ κ0 τ_check =>
                  let F0 := subst_function_ctx VarM VarR VarS (up_type VarT) F <| fc_type_vars ::= cons κ0 |> in
                  let up := ren_type id id id S in
                  (* HUGE amount of equalities *)
                  if type_beq τ τ_check && local_ctx_beq L_tocheck (map up L) && local_ctx_beq L'_tocheck (map up L')
                     && list_beq type type_beq τs1_check (map up τs1) && list_beq type type_beq τs2_check (map up τs2)
                     && function_ctx_beq F0 F0_tocheck
                  then ok_term
                  else INR "something in unpacked existential didn't match up"
              | _ => INR "trying to check unpack existential, but last type not existential"
              end
          | None => INR "bad instruction in unpacked existential (empty) p2"
          end
      | None => INR "bad instruction in unpacked existential (empty)"
      end
  end.

Lemma unpacked_existential_checker_correct :
  ∀ F L ϕ L' F0 L_tocheck ϕ0 L'_tocheck,
    unpacked_existential_checker F L ϕ L' F0 L_tocheck ϕ0 L'_tocheck = ok_term ->
    unpacked_existential F L ϕ L' F0 L_tocheck ϕ0 L'_tocheck.
Proof.
  Opaque split_list_all_last.
  intros. unfold unpacked_existential_checker in H.
  repeat my_auto4.
  - apply UnpackMem.
  - apply UnpackRep.
  - apply UnpackSize.
  - apply UnpackType.
Qed.

Definition unpacked_existential_getter F L ϕ L' :
  option (function_ctx * local_ctx * instruction_type * local_ctx) :=
  match ϕ with
  | InstrT τs1_full τs2 =>
      match split_list_all_last τs1_full with
      | Some (τs1, τex) =>
          (* now we have to split on the τex *)
          match τex with
          | ExistsMemT κ τ =>
              let F0 := subst_function_ctx (up_memory VarM) VarR VarS VarT F
                          <| fc_kind_ctx ::= set kc_mem_vars S |> in
              let up := ren_type S id id id in
              let L0 := (map up L) in
              let L'0 := (map up L') in
              let ϕ0 := InstrT (map up τs1 ++ [τ]) (map up τs2) in
              Some (F0, L0, ϕ0, L'0)
          | ExistsRepT κ τ =>
              let F0 := add_rep_var (subst_function_ctx VarM (up_representation VarR) VarS VarT F)
                           in
              let up := ren_type id S id id in
              let L0 := (map up L) in
              let L'0 := (map up L') in
              let ϕ0 := InstrT (map up τs1 ++ [τ]) (map up τs2) in
              Some (F0, L0, ϕ0, L'0)
          | ExistsSizeT κ τ =>
              let F0 := add_size_var (subst_function_ctx VarM VarR (up_size VarS) VarT F)
                           in
              let up := ren_type id id S id in
              let L0 := (map up L) in
              let L'0 := (map up L') in
              let ϕ0 := InstrT (map up τs1 ++ [τ]) (map up τs2) in
              Some (F0, L0, ϕ0, L'0)
          | ExistsTypeT κ κ0 τ =>
              let F0 := subst_function_ctx VarM VarR VarS (up_type VarT) F <| fc_type_vars ::= cons κ0 |> in
              let up := ren_type id id id S in
              let L0 := (map up L) in
              let L'0 := (map up L') in
              let ϕ0 := InstrT (map up τs1 ++ [τ]) (map up τs2) in
              Some (F0, L0, ϕ0, L'0)
          | _ => None
          end
      | None => None
      end
  end.

Lemma unpacked_existential_getter_correct :
  ∀ F L ϕ L' F0 L0 ϕ0 L'0,
    unpacked_existential_getter F L ϕ L' = Some (F0, L0, ϕ0, L'0) ->
    unpacked_existential F L ϕ L' F0 L0 ϕ0 L'0.
Proof.
  intros. unfold unpacked_existential_getter in H.
  repeat my_auto4; subst.
  - apply UnpackMem.
  - apply UnpackRep.
  - apply UnpackSize.
  - apply UnpackType.
Qed.


Definition local_ctx_ok_checker (F:function_ctx) (L:local_ctx) : type_checker_res :=
  (* let res := zip_with (type_rep_eq_prim_checker F) L F.(fc_locals) in *)
  (* let folded := foldr (λ r, andb (check_ok_output r)) true res in *)
  (* if folded *)
  if foldr2_bool (λ τ1, λ τ2, andb (check_ok_output (type_rep_eq_prim_checker F τ1 τ2))) true false L F.(fc_locals)
  then ok_term
  else
   let res := zip_with (type_rep_eq_prim_checker F) L F.(fc_locals) in (* just for the error message *)
   inr ([NormalError "local ctx not ok"] ++ combine_error_messages res).

Lemma local_ctx_ok_checker_correct :
  ∀ F L, local_ctx_ok_checker F L = ok_term -> local_ctx_ok F L.
Proof.
  intros * H.
  unfold local_ctx_ok.
  pose proof (type_rep_eq_prim_checker_correct F).
  eapply convert_foldr2_bool_to_Forall2_check_ok_output_pure_forall; last done.
  unfold local_ctx_ok_checker in H.
  repeat my_auto3_5. done.
Qed.





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
  apply local_ctx_ok_checker_correct in H.
  split; auto.
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


(* I'm going to do this really stupidly *)
Definition has_num_type_type (τ:type) : bool :=
  orb (orb (type_beq τ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T)))
           (type_beq τ (NumT (VALTYPE (AtomR I64R) NoRefs) (IntT I64T))))
      (orb (type_beq τ (NumT (VALTYPE (AtomR F32R) NoRefs) (FloatT F32T)))
           (type_beq τ (NumT (VALTYPE (AtomR F64R) NoRefs) (FloatT F64T)))).
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




(*Definition get_instruction_type_arity (ψ:instruction_type) : nat * nat :=
  match ψ with
  | InstrT τs1 τs2 => (Init.Datatypes.length τs1, Init.Datatypes.length τs2)
  end.*)

(* inl means no error. None just means can't synth (uncreachable,
   break, return). inr means error in synthesizing (possible in
   local set and get).

   VERY BIG NOTE: THIS DOES NOT ACTUALLY CHECK IF THIS IS THE
   CORRECT L'. JUST SYNTHESIZES WHAT IT WOULD HAVE TO BE IF
   IT IS CORRECT.

 *)
Definition synth_possible_resulting_local_ctx F (inst:instruction) (L:local_ctx) : (option local_ctx) + type_error :=
  match inst with
  | INop _ => inl (Some L)
  | IUnreachable _ => inl None
  | ICopy _
  | IDrop _
  | INum _ _
  | INumConst _ _ => inl (Some L)
  | IBlock _ L' _ => inl (Some L')
  | ILoop _ _ => inl (Some L)
  | IIte _ L' _ _ => inl (Some L')
  | IBr _ _
  | IReturn _ => inl None
  | ILocalGet ψ cm i =>
      match ψ with
      | InstrT [] [τ] =>
          match cm with
          | Copy => inl (Some L)
          | Move =>
              match F.(fc_locals) !! i with
              | Some ηs => inl (Some (<[ i := type_plug_prim ηs ]> L))
              | _ => inr (NormalError "NO")
              end
          end
      | _ => inr (NormalError "NO")
      end
  | ILocalSet ψ i =>
      match ψ with
      | InstrT [τ] [] => inl (Some (<[ i := τ ]> L))
      | _ => inr (NormalError "NO")
      end
  | ICodeRef _ _
  | IInst _ _
  | ICall _ _ _
  | ICallIndirect _
  | IInject _ _
  | IInjectNew _ _ => inl (Some L)
  | ICase _ L' _
  | ICaseLoad _ _ L' _ => inl (Some L')
  | IGroup _
  | IUngroup _
  | IFold _
  | IUnfold _
  | IPack _ => inl (Some L)
  | IUnpack _ L' _ => inl (Some L')
  | ITag _
  | IUntag _
  | ICast _
  | INew _
  | ILoad _ _ _
  | IStore _ _
  | ISwap _ _ => inl (Some L)
  end.


(* this is the old version with arity. just list_suffix is the same
                let (e_n1, e_n2) := get_instruction_type_arity e_ψ in
                let (es_n1, es_n2) := get_instruction_type_arity ψ in
                if es_n1 <? e_n1
                then INR "instruction has more arguments than large have_instruction type has"
                else
                  if es_n1 =? e_n1
                  then (* equal arity case *)
                    match e_ψ, ψ with
                    | InstrT τs1_e τs2_e, InstrT τs1_es τs2_es =>
                        if list_beq type type_beq τs1_e τs1_es
                        then have_instruction_type_checker M F L_e es (InstrT τs2_e τs2_es) L'
                        else INR "instruction arguments do not match large have_instruction arguments (exact case)"
                    end
                  else (* frame rule case *)
                    match e_ψ, ψ with
                    | InstrT τs1_e τs2_e, InstrT τs1_es τs2_es =>
                        match list_suffix τs1_es τs1_e with (* ts1_es = ts_pref ++ ts1_e*)
                        | Some τs_pref => have_instruction_type_checker M F L_e es (InstrT (τs_pref ++ τs2_e) τs2_es) L'
                        | None => INR "can't frame out (multiple instructions)"
                        end
                    end *)



Fixpoint unzip_sert (τs:list type) : option ((list kind) * (list type)) :=
  match τs with
  | [] => Some ([], [])
  | τ :: τs =>
      match τ with
      | SerT k t =>
          match unzip_sert τs with
          | Some (ks, ts) => Some (k::ks, t::ts)
          | None => None
          end
      | _ => None
      end
  end.

Lemma unzip_sert_correct :
  ∀ τs' κs τs, unzip_sert τs' = Some (κs, τs) ->
               τs' = zip_with SerT κs τs /\ Datatypes.length κs = Datatypes.length τs.
Proof.
  induction τs'.
  - simpl. intros; inversion H. auto.
  - intros. simpl in H. destruct a; try (by inversion H).
    structural_auto. destruct p. clear H1.
    inversion H. subst.
    specialize (IHτs' l l0 ltac:(auto)).
    destruct IHτs' as (h11 & h122).
    subst.
    split; auto.
    cbn; lia.
Qed.

(* Will need a mutually recursive have_instruction_type too *)
Fixpoint has_instruction_type_checker
    (M:module_ctx) (F:function_ctx) (L:local_ctx)
    (inst:instruction) (ψ:instruction_type) (L':local_ctx) {struct inst} : type_checker_res :=
  let fix have_instruction_type_checker
    (M:module_ctx) (F:function_ctx) (L:local_ctx)
    (insts:list instruction) (ψ:instruction_type) (L':local_ctx) {struct insts} : type_checker_res :=
    match insts with
    | [] =>
        if (local_ctx_beq L L')
        then
          match ψ with
          | InstrT τs1 τs2 =>
              if list_beq type type_beq τs1 τs2
              then (* Oh and monorep *)
                if foldr (λ t:type, andb (check_ok_output (has_mono_rep_checker F t))) true τs1
                then local_ctx_ok_checker F L
                else INR "bad empty instruction type (can't frame non mono rep)"
              else INR "bad empty instructions type (not empties or frame)"
          end
        else INR "bad empty instructions type (local contexts don't match)"
    | [e] =>
        let e_ψ := proj_instr_ty e in
        match has_instruction_type_checker M F L e e_ψ L' with
        | inl () => (* now just to check if we need to frame stuff out *)
            match e_ψ, ψ with
            | InstrT τs1_e τs2_e, InstrT τs1_es τs2_es =>
                match list_suffix τs1_es τs1_e, list_suffix τs2_es τs2_e with
                | Some τs1_pref, Some τs2_pref =>
                    (* ts1_es = ts1_pref ++ ts1_e, ts2_es = ts2_pref ++ ts2_e*)
                    (* just need to check that ts1_pref = ts2_pref *)
                    if list_beq type type_beq τs1_pref τs2_pref
                    then (* oh and monorep *)
                      if foldr (λ t:type, andb (check_ok_output (has_mono_rep_checker F t))) true τs1_pref
                      then ok_term
                      else inr [(FrameError "non mono rep" e_ψ ψ)]
                    else inr [(FrameError "single instruction" e_ψ ψ)]
                | _, _ => inr [(FrameError "inner instruction type doesn't match" e_ψ ψ)]
                end
            end
        | err => err
        end
    | e :: es =>
        let e_ψ := proj_instr_ty e in
        match synth_possible_resulting_local_ctx F e L with
        | inr _ => INR "this is either local get/set that is bad, so error?"
        | inl None => INR "the type checker does not support break/return/unreachable in the middle of a block"
        | inl (Some L_e) =>
            match has_instruction_type_checker M F L e e_ψ L_e with
            | inl () =>
                match e_ψ, ψ with
                | InstrT τs1_e τs2_e, InstrT τs1_es τs2_es =>
                    match list_suffix τs1_es τs1_e with (* τs1_es = τs_pref ++ τs1_es *)
                    | Some τs_pref => (* framed have to be mono rep *)
                        if foldr (λ t:type, andb (check_ok_output (has_mono_rep_checker F t))) true τs_pref
                        then have_instruction_type_checker M F L_e es (InstrT (τs_pref ++ τs2_e) τs2_es) L'
                        else INR "can't frame out non mono rep"
                    | None => INR "instruction has more arguments than large have_instruction type has, or can't frame out"
                    end
                end
            | err => err
            end
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
              match has_ref_flag_checker F τ GCRefs with
              | inl () => has_instruction_type_ok_checker F ψ L
              | _ => INR "incorrect copyability for instruction type for copy"
              end
            else INR "incorrect instruction type for copy"
        | _ => INR "incorrect instruction type for copy"
        end
      else INR "incorrect instruction type for copy"
  | IDrop ψ_inner =>
      if (instruction_type_beq ψ ψ_inner)
      then
        if (local_ctx_beq L L')
        then
          match ψ with
          | InstrT [τ] [] => has_instruction_type_ok_checker F ψ L
          | _ => INR "incorrect instruction type for drop (bad shape)"
          end
        else INR "incorrect instruction type for drop (local ctxs not equal)"
      else INR "incorrect instruction type for drop (inner ψ not equal to outer ψ)"
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
                      if foldr (λ t:type, andb (check_ok_output (has_ref_flag_checker F t NoRefs))) true τs1
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
                if foldr (λ t:type, andb (check_ok_output (has_ref_flag_checker F t NoRefs))) true τs1
                then has_instruction_type_ok_checker F ψ L'
                else INR "incorrect instruction type for return"
            | None => INR "incorrect instruction type for return"
            end
        end
      else INR "incorrect instruction type for return"
  | ILocalGet ψ_inner cm i => (* note this is for both TLocalGetMove and TLocalGetCopy *)
      if andb (instruction_type_beq ψ ψ_inner) (true)
      then
        match L !! i with
        | Some τ =>
            match ψ with
            | InstrT [] [τ'] =>
                if type_beq τ τ'
                then
                  match cm with (* decision point *)
                  | Copy =>
                      match has_ref_flag_checker F τ NoRefs with
                      | inl () =>
                          if local_ctx_beq L L'
                          then has_instruction_type_ok_checker F ψ L
                          else INR "incorrect instruction type for local get"
                      | inr a => inr a
                      end
                  | Move =>
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
  | ILocalSet ψ_inner i =>
      if (instruction_type_beq ψ ψ_inner)
      then
        match L !! i with
        | Some τ0 =>
            match has_ref_flag_checker F τ0 NoRefs with
            | inl () =>
                match ψ with
                | InstrT [τ] [] =>
                    let Ltrue := <[ i := τ ]> L in
                    if local_ctx_beq L' Ltrue
                    then has_instruction_type_ok_checker F ψ L'
                    else INR "incorrect instruction type for local set (bad resulting local context)"
                | _ => INR "incorrect instruction type for local set (shape not [τ] -> [])"
                end
            | err => err
            end
        | None => INR "bad instruction type for local set (not enough locals)"
        end
      else INR "incorrection instruction type for local set"
  | ICodeRef ψ_inner i =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match ψ with
        | InstrT [] [τ'] =>
            match M.(mc_table) !! i with
            | Some ϕ =>
                if type_beq τ' (CodeRefT (VALTYPE (AtomR I32R) NoRefs) ϕ)
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
                if andb (kind_beq κ (VALTYPE (AtomR I32R) NoRefs)) (kind_beq κ κ')
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
                match function_type_insts_checker F ixs ϕ (InnerFunT (MonoFunT τs1 τs2)) with
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
                if type_beq τ (CodeRefT (VALTYPE (AtomR I32R) NoRefs) (InnerFunT (MonoFunT τs1 τs2)))
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
  | IInjectNew ψ_inner i =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match ψ with
        | InstrT [τ] [ref] =>
            match ref with
            | RefT κr μ Imm (VariantT κv τs') =>
                match unzip_sert τs' with
                | Some (κs, τs) =>
                    match τs !! i with
                    | Some τ' =>
                        if type_beq τ τ'
                        then
                          match mono_mem_checker μ with
                          | inl () => has_instruction_type_ok_checker F ψ L
                          | err => err
                          end
                        else INR "incorrect instruction type for inject new (not matching injections?)"
                    | None => INR "incorrect instruction type for inject new (i out of bounds)"
                    end
                | None => INR "incorrect instruction type for inject new (variant is not all sered or smthn)"
                end
            | _ => INR "inocrrect instruction type for inject new (result isn't proper ref shape)"
            end
        | _ => INR "inocrrect instruction type for inject new (wrong shape)"
        end
      else INR "incorrect instruction type for inject new"
  | ICase ψ_inner L_inner ess =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L_inner L')
      then
        match ψ with
        | InstrT [τ] τs' =>
            match τ with
            | SumT κ τs =>
                let F' := F <| fc_labels ::= cons (τs', L') |> in
                if foldr2_bool
                     (λ es, λ t:type,
                           andb (check_ok_output
                                   (have_instruction_type_checker M F' L es (InstrT [t] τs') L'))
                     ) true false ess τs
                then has_instruction_type_ok_checker F ψ L'
                else INR "incorrect instruction type for case (failed looping check)"
            | _ => INR "incorrect instruction type for case (not casing on sum)"
            end
        | _ => INR "incorrect isntruction type for case (wrong shape)"
        end
      else INR "incorrect instruction type for case"
  | ICaseLoad ψ_inner cm L_inner ess => (* note: both TCaseLoadCopy and TCaseLoadMove *)
      (* some of the shared things before casing on cm *)
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L_inner L')
      then (* oh that's it, τs_ser needs to be gotten out of ψ lmao *)
        match cm with (* DECISION POINT *)
        | Copy => (* TCaseLoadCopy *)
            match ψ with
            | InstrT [τ1] (τ2::τs') =>
                match τ1 with
                | RefT κr μ Imm (VariantT κv τs_ser) =>
                    match τ2 with
                    | RefT κr0 μ0 Imm (VariantT κv0 τs'0) =>
                        (* a bunch of variables have to be equal *)
                        if andb (kind_beq κr κr0) (andb (kind_beq κv κv0)
                                  (andb (memory_beq μ μ0) (list_beq type type_beq τs_ser τs'0)))
                        then
                          match unzip_sert τs_ser with
                          | Some (κs, τs) =>
                              let F' := F <| fc_labels ::= cons (τs', L') |> in
                              if foldr (λ t:type, andb (check_ok_output (has_ref_flag_checker F t GCRefs))) true τs
                              then
                                if foldr2_bool
                                     (λ es, λ t:type,
                                         andb (check_ok_output
                                                 (have_instruction_type_checker M F' L es (InstrT [t] τs') L'))
                                     ) true false ess τs
                                then has_instruction_type_ok_checker F ψ L'
                                else INR "incorrect instruction type for caseloadcopy (failed looping check)"
                              else INR "incorrect instruction type for caseloadcopy (potentially copying mm refs)"
                          | None => INR "incorrect instruction type for caseloadcopy (τs_ser isn't all SerT)"
                          end
                        else INR "incorrect instruction type for caseloadcopy (input/output don't match)"
                    | _ => INR "incorrect instruction type for caseloadcopy (wrong output shape)"
                    end
                | _ => INR "incorrect instruction type for caseloadcopy (wrong input shape)"
                end
            | _ => INR "incorrect instruction type for caseloadcopy (wrong shape)"
            end
        | Move => (* TCaseLoadMove *)
            match ψ with
            | InstrT [τ1] τs' =>
                match τ1 with
                | RefT κr (BaseM MemMM) Imm (VariantT κv τs_ser) =>
                    match unzip_sert τs_ser with
                    | Some (κs, τs) =>
                        let F' := F <| fc_labels ::= cons (τs', L') |> in
                        if foldr2_bool
                             (λ es, λ t:type,
                                 andb (check_ok_output
                                         (have_instruction_type_checker M F' L es (InstrT [t] τs') L'))
                             ) true false ess τs
                        then has_instruction_type_ok_checker F ψ L'
                        else INR "incorrect instruction type for caseloadmove (failed looping check)"
                    | None => INR "incorrect instruction type for caseloadmove (τs_ser isn't all SerT)"
                    end
                | _ => INR "incorrect instruction type for caselaodmove (wrong input shape)"
                end
            | _ => INR "incorrect instruction type for caseloadmove (wrong shape)"
            end
        end
      else INR "incorrect instruction type for caseload (either version)"
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
  | IUnpack ψ_inner L_inner es => (* SAVE *)
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L_inner L')
      then
        match ψ with
        | InstrT τs1 τs2 =>
            let F' := F <| fc_labels ::= cons (τs2, L') |> in
            match unpacked_existential_getter F' L ψ L' with
            | Some (F0', L0, ψ0, L0') =>
                (* ISSUE RIGHT HERE: the es should be es0 TODO but bad fixpoint  *)
                match have_instruction_type_checker M F0' L0 es ψ0 L0' with
                | inl () => has_instruction_type_ok_checker F ψ L'
                | err => err
                end
            | None => INR "incorrect instruction type for unpack (can't construct unpacked)"
            end
        end
      else INR "incorrect instruction type for unpack"
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
            match type_eq_checker τ τ' with
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
            | RefT κ μ _ (SerT κser τ') =>
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
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match cm with (* DECISION POINT *)
        | Copy => (* load copy *)
            match ψ with
            | InstrT [τ1] [τ2;τval] =>
                if type_beq τ1 τ2
                then
                  match τ1 with
                  | RefT κ μ _ τ =>
                      match synth_resolving_path τ π None with
                      | Some pr =>
                          match pr.(pr_target) with
                          | SerT κser τval0 =>
                              if type_beq τval τval0
                              then
                                match has_ref_flag_checker F τval GCRefs with
                                | inl () =>
                                    if (foldr (λ t:type, andb (check_ok_output (has_mono_size_checker F t))) true (pr.(pr_prefix)))
                                    then has_instruction_type_ok_checker F ψ L
                                    else INR "incorrect instruction type for load copy (prefix not all mono size)"
                                | inr a => inr a
                                end
                              else INR "incorrect instruction type for load copy (target type not equal to instr type) "
                          | _ => INR "incorrect instruction type for load copy (path result target not SerT)"
                          end
                      | None => INR "incorrect instruction type for load copy (couldn't synth path)"
                      end
                  | _ => INR "incorrect instruction type for load copy (not ref)"
                  end
                else INR "incorrect instruction type for load copy (input output not equal)"
            | _ => INR "incorrect instruction type for load copy (wrong shape)"
            end
        | Move => (* load move *)
            match ψ with
            | InstrT [τ1] [τ2; τval] =>
                match τ1 with
                | RefT κ (BaseM MemMM) Mut τ =>
                    match τ2 with
                    | RefT κ' (BaseM MemMM) Mut prreplaced =>
                        match synth_resolving_with_outer_replaced_spant τ π prreplaced τval with
                        | Some (pr, κser, σ) =>
                            (* from this, we know prreplace = pr.pr_replaced; pr.pr_target = SerT κser τval *)
                            match has_size_checker F pr.(pr_target) σ with
                            | inl () =>
                                if (foldr (λ t:type, andb (check_ok_output (has_mono_size_checker F t))) true (pr.(pr_prefix)))
                                    then has_instruction_type_ok_checker F ψ L
                                    else INR "incorrect instruction type for load move (prefix not all mono size)"
                            | inr a => inr a
                            end
                        | _ => INR "incorrect instruction type for load move (couldn't synth path)"
                        end
                    | _ => INR "incorrect instruction type for load move (output not mm ref)"
                    end
                | _ => INR "incorrect instruction type for load move (input not mm ref)"
                end
            | _ => INR "incorrect instruction type for load move (wrong shape)"
            end
        end
      else INR "incorrect instruction type for load"
  | IStore ψ_inner π => (* note this will be both TStoreWeak and TStoreStrong *)
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match ψ with
        | InstrT [reft1; τval] [reft2] =>
            if type_beq reft1 reft2 (* true = store weak *) (* false = store strong *)
            then (* store weak *)
              match reft1 with
              | RefT κ μ Mut τ =>
                  match synth_resolving_path τ π None with
                  | Some pr =>
                      match has_ref_flag_checker F pr.(pr_target) GCRefs with
                      | inl () =>
                          match pr.(pr_target) with
                          | SerT κser τval_inner =>
                              if type_beq τval τval_inner
                              then
                                if (foldr (λ t:type, andb (check_ok_output (has_mono_size_checker F t))) true (pr.(pr_prefix)))
                                then has_instruction_type_ok_checker F ψ L
                                else INR "incorrect instruction type for weak store (prefix not all mono size)"
                              else INR "incorrect instruction type for weak store (target ser bad inner type)"
                          | _ => INR "inocrrect instruction type for weak store (target not ser)"
                          end
                      | err => err
                      end
                  | None => INR "incorrect instruction type for weak store (can't synth path)"
                  end
              | _ => INR "incorrect instruction type for weak store (not ref type)"
              end
            else (* store strong. Note: SerT kser tval = pr.(pr_replaced) *)
              match reft1 with (* doing this in steps for automation. Might not help anyway lol *)
              | RefT κ (BaseM MemMM) Mut τ =>
                  match reft2 with
                  | RefT κ' (BaseM MemMM) Mut prreplaced =>
                      if true
                      then (* we can finally start doing things omg *)
                        match synth_resolving_with_outer_replaced_sert τ π prreplaced τval  with
                        | Some (pr, κser) =>
                            match has_ref_flag_checker F pr.(pr_target) GCRefs with
                            | inl () =>
                                match grab_size F pr.(pr_target) with
                                | Some σ =>
                                    match grab_rep F τval with
                                    | Some ρ =>
                                        match eval_size EmptyEnv σ, eval_rep_size EmptyEnv ρ with
                                        | Some n1, Some n2 =>
                                            if andb (n1 =? n2) (foldr (λ t:type, andb (check_ok_output (has_mono_size_checker F t))) true (pr.(pr_prefix)))
                                            then has_instruction_type_ok_checker F ψ L
                                            else INR "incorrect instruction type for strong store (prefix not all mono size)"
                                        | _, _ => INR "inc instr type for strong store (unmatching sizes)"
                                        end
                                    | None => INR "inc instr type for strong store"
                                    end
                                | None => INR "inc instr type for strong store"
                                end
                            | err => err
                            end
                        | None => INR "incorrect instruction type for strong store (can't synth path)"
                        end
                      else INR "incorrect instruction type for strong store (stored types don't match)"
                  | _ => INR "inocrrect instruction type for strong store (second not ref with sert)"
                  end
              | _ => INR "incorrect instruction type for strong store (first not ref)"
              end
        | _ => INR "incorrect instruction type for store (wrong shape)"
        end
      else INR "incorrection instruction type for store (both types)"
  | ISwap ψ_inner π =>
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match ψ with
        | InstrT τs1 τs2 =>
            if list_beq type type_beq τs1 τs2
            then
              match τs1 with (* note: doing this in multiple steps for automation purposes *)
              | [reff; τval] =>
                  match reff with
                  | RefT κ μ Mut τ =>
                      match synth_resolving_path τ π None with
                      | Some pr => (* now to match that pr has the right things *)
                          match pr.(pr_target) with
                          | SerT κser τval_inner =>
                              if type_beq τval τval_inner
                              then
                                if (foldr (λ t:type, andb (check_ok_output (has_mono_size_checker F t))) true (pr.(pr_prefix)))
                                then has_instruction_type_ok_checker F ψ L
                                else INR "improper synthesized path target"
                              else INR "improper synthesized path target"
                          | _ => INR "improper synthesized path target"
                          end
                      | None => INR "couldn't synthesize path"
                      end
                  | _ => INR "bad instruction type for swap (first arg not ref)"
                  end
              | _ => INR "bad instruction type for swap (wrong shape)"
              end
            else INR "bad instruction type for swap"
        end
      else INR "incorrect instruction type for swap"
  end.


(* TODO at the end make sure this is a direct copy of above *)
Fixpoint have_instruction_type_checker
    (M:module_ctx) (F:function_ctx) (L:local_ctx)
    (insts:list instruction) (ψ:instruction_type) (L':local_ctx) {struct insts} : type_checker_res :=
    match insts with
    | [] =>
        if (local_ctx_beq L L')
        then
          match ψ with
          | InstrT τs1 τs2 =>
              if list_beq type type_beq τs1 τs2
              then
                if foldr (λ t:type, andb (check_ok_output (has_mono_rep_checker F t))) true τs1
                then local_ctx_ok_checker F L
                else INR "bad empty instruction type (can't frame non mono rep)"
              else INR "bad empty instructions type (not empties or frame)"
          end
        else INR "bad empty instructions type (local contexts don't match)"
    | [e] =>
        let e_ψ := proj_instr_ty e in
        match has_instruction_type_checker M F L e e_ψ L' with
        | inl () => (* now just to check if we need to frame stuff out *)
            match e_ψ, ψ with
            | InstrT τs1_e τs2_e, InstrT τs1_es τs2_es =>
                match list_suffix τs1_es τs1_e, list_suffix τs2_es τs2_e with
                | Some τs1_pref, Some τs2_pref =>
                    (* ts1_es = ts1_pref ++ ts1_e, ts2_es = ts2_pref ++ ts2_e*)
                    (* just need to check that ts1_pref = ts2_pref *)
                    if list_beq type type_beq τs1_pref τs2_pref
                    then (* oh and monorep *)
                      if foldr (λ t:type, andb (check_ok_output (has_mono_rep_checker F t))) true τs1_pref
                      then ok_term
                      else inr [(FrameError "non mono rep" e_ψ ψ)]
                    else inr [(FrameError "single instruction" e_ψ ψ)]
                | _, _ => inr [(FrameError "inner instruction type doesn't match" e_ψ ψ)]
                end
            end
        | err => err
        end
    | e :: es =>
        let e_ψ := proj_instr_ty e in
        match synth_possible_resulting_local_ctx F e L with
        | inr _ => INR "this is either local get/set that is bad, so error?"
        | inl None => INR "the type checker does not support break/return/unreachable in the middle of a block"
        | inl (Some L_e) =>
            match has_instruction_type_checker M F L e e_ψ L_e with
            | inl () =>
                match e_ψ, ψ with
                | InstrT τs1_e τs2_e, InstrT τs1_es τs2_es =>
                    match list_suffix τs1_es τs1_e with (* τs1_es = τs_pref ++ τs1_es *)
                    | Some τs_pref =>
                        if foldr (λ t:type, andb (check_ok_output (has_mono_rep_checker F t))) true τs_pref
                        then have_instruction_type_checker M F L_e es (InstrT (τs_pref ++ τs2_e) τs2_es) L'
                        else INR "can't frame out non mono rep"
                    | None => INR "instruction has more arguments than large have_instruction type has, or can't frame out"
                    end
                end
            | err => err
            end
        end
    end.


(** Demonstration of the annoyance of rocq fixpoint checker **)

(* Outer on just instruction, inner fixpoint. Works. *)
Fixpoint test1 e :=
  let fix test1_list es :=
    match es with
    | [] => True
    | e::es => test1 e /\ test1_list es
    end in
  match e with
  | IUnreachable _ => False
  | IBlock _ _ es => test1_list es
  | _ => True
  end.

(* Mutual recursion. Fails. *)
Fail Fixpoint test2 e :=
  match e with
  | IUnreachable _ => False
  | IBlock _ _ es => test2_list es
  | _ => True
  end
with test2_list es :=
  match es with
  | [] => True
  | e::es => test2 e /\ test2_list es
  end.

(* Outer in list instruction, inner fixpoint on instruction. Fails. *)
Fail Fixpoint test3_list es :=
  let test3 e :=
    match e with
    | IUnreachable _ => False
    | IBlock _ _ bs => test3_list bs
    | _ => True
    end in
  match es with
  | [] => True
  | e::es => test3 e /\ test3_list es
  end.

(* Also just mutual recursion, but testing flipping them jic. Fails obviously. *)
Fail Fixpoint test4_list es :=
  match es with
  | [] => True
  | e::es => test4 e /\ test4_list es
  end
with test4 e :=
  match e with
  | IUnreachable _ => False
  | IBlock _ _ bs => test4_list bs
  | _ => True
  end.

Fail Fixpoint test5 ns :=
  match ns with
  | [] => true
  | n::ns => (n =? 5) && test5 (map (λ x,x) ns)
  end.



Section InstructionMind.

  Variables
    (P1: instruction -> Prop)
    (P2: list instruction -> Prop)
    (HNop : ∀ ψ, P1 (INop ψ))
    (HUnreachable: ∀ ψ, P1 (IUnreachable ψ))
    (HCopy: ∀ ψ, P1 (ICopy ψ))
    (HDrop: ∀ ψ, P1 (IDrop ψ))
    (HNum: ∀ ψ ni, P1 (INum ψ ni))
    (HNumConst: ∀ ψ n, P1 (INumConst ψ n))
    (HBlock : ∀ ψ τs es, P2 es -> P1 (IBlock ψ τs es))
    (HLoop : ∀ ψ es, P2 es -> P1 (ILoop ψ es))
    (HIte: ∀ ψ τs es1 es2, P2 es1 -> P2 es2 -> P1 (IIte ψ τs es1 es2))
    (HBr: ∀ ψ n, P1 (IBr ψ n))
    (HReturn: ∀ ψ, P1 (IReturn ψ))
    (HLocalGet: ∀ ψ cm n, P1 (ILocalGet ψ cm n))
    (HLocalSet: ∀ ψ n, P1 (ILocalSet ψ n))
    (HCodeRef: ∀ ψ n, P1 (ICodeRef ψ n))
    (HInst: ∀ ψ ix, P1 (IInst ψ ix))
    (HCall: ∀ ψ n ixs, P1 (ICall ψ n ixs))
    (HCallIndirect: ∀ ψ, P1 (ICallIndirect ψ))
    (HInject: ∀ ψ n, P1 (IInject ψ n))
    (HInjectNew: ∀ ψ n, P1 (IInjectNew ψ n))
    (HCase: ∀ ψ τs ess, Forall P2 ess -> P1 (ICase ψ τs ess))
    (HCaseLoad: ∀ ψ c τs ess, Forall P2 ess -> P1 (ICaseLoad ψ c τs ess))
    (HGroup : ∀ ψ, P1 (IGroup ψ))
    (HUngroup: ∀ ψ, P1 (IUngroup ψ))
    (HFold: ∀ ψ, P1 (IFold ψ))
    (HUnfold: ∀ ψ, P1 (IUnfold ψ))
    (HPack: ∀ ψ, P1 (IPack ψ))
    (HUnpack: ∀ ψ τs es, P2 es -> P1 (IUnpack ψ τs es))
    (HTag: ∀ ψ, P1 (ITag ψ))
    (HUntag: ∀ ψ, P1 (IUntag ψ))
    (HCast: ∀ ψ, P1 (ICast ψ))
    (HNew: ∀ ψ, P1 (INew ψ))
    (HLoad: ∀ ψ ns c, P1 (ILoad ψ ns c))
    (HStore: ∀ ψ ns, P1 (IStore ψ ns))
    (HSwap: ∀ ψ ns, P1 (ISwap ψ ns))

    (HEmpty: P2 [])
    (HFull: ∀ e es, P1 e -> P2 es -> P2 (e::es) )
    .
    Fixpoint instruction_ind (e:instruction) : P1 e :=
      let fix list_instruction_ind (bs:list instruction) : P2 bs :=
      match bs with
      | [] => HEmpty
      | e::es => HFull e es (instruction_ind e) (list_instruction_ind es)
      end in

      let fix list_list_instruction_ind (bss:list (list instruction)) : Forall P2 bss :=
        match bss with
        | [] => ListDef.Forall_nil _
        | es :: ess =>
            ListDef.Forall_cons _ _ _ (list_instruction_ind es) (list_list_instruction_ind ess)
        end in
      match e with
      | INop ψ => HNop ψ
      | IUnreachable ψ => HUnreachable ψ
      | ICopy ψ => HCopy ψ
      | IDrop ψ => HDrop ψ
      | INum ψ ni => HNum ψ ni
      | INumConst ψ n => HNumConst ψ n
      | IBlock ψ τs es => HBlock ψ τs es (list_instruction_ind es)
      | ILoop ψ es => HLoop ψ es (list_instruction_ind es)
      | IIte ψ τs es1 es2 =>
          HIte ψ τs es1 es2
            (list_instruction_ind es1) (list_instruction_ind es2)
      | IBr ψ n => HBr ψ n
      | IReturn ψ => HReturn ψ
      | ILocalGet ψ cm n => HLocalGet ψ cm n
      | ILocalSet ψ n => HLocalSet ψ n
      | ICodeRef ψ n => HCodeRef ψ n
      | IInst ψ ix => HInst ψ ix
      | ICall ψ n ixs => HCall ψ n ixs
      | ICallIndirect ψ => HCallIndirect ψ
      | IInject ψ n => HInject ψ n
      | IInjectNew ψ n => HInjectNew ψ n
      | ICase ψ τs ess => HCase ψ τs ess (list_list_instruction_ind ess)
      | ICaseLoad ψ c τs ess => HCaseLoad ψ c τs ess (list_list_instruction_ind ess)
      | IGroup ψ => HGroup ψ
      | IUngroup ψ => HUngroup ψ
      | IFold ψ => HFold ψ
      | IUnfold ψ => HUnfold ψ
      | IPack ψ => HPack ψ
      | IUnpack ψ τs es => HUnpack ψ τs es (list_instruction_ind es)
      | ITag ψ => HTag ψ
      | IUntag ψ => HUntag ψ
      | ICast ψ => HCast ψ
      | INew ψ => HNew ψ
      | ILoad ψ ns c => HLoad ψ ns c
      | IStore ψ ns => HStore ψ ns
      | ISwap ψ ns => HSwap ψ ns
      end
    .
    Fixpoint list_instruction_ind es : P2 es :=
      match es with
      | [] => HEmpty
      | e :: es => HFull e es (instruction_ind e) (list_instruction_ind es)
      end.


  
End InstructionMind.

Ltac structural_auto_2 :=
   match goal with
  | H: (_ && _ = true) |- _ => apply andb_prop in H; destruct H as [?H1 ?H2]
  | o:ok |- _ => stupid_unit o
  | H: ok_term = ok_term |- _ => clear H
  | H: (andb _ _ = true) |- _ => apply andb_prop in H; destruct H as [?H1 ?H2]
  | H: true = false |- _ => inversion H
  | H: false = true |- _ => inversion H
  | H: ((match ?key with |_=>_ end) = _) |- _ =>
      destruct key eqn:?HMatch; try inversion H; simpl in *; clear H
  | H:((if ?key then _ else _)=_) |- _ => destruct key eqn:?HMatch; try (inversion H; [idtac]; clear H); simpl in *
   end.
Ltac boolean_equality_auto_2 :=
  match goal with
  | H: (kind_beq ?x _ = true) |- _ => apply kind_eq_convert in H; subst x; auto
  | H: (instruction_type_beq ?x _ = true) |- _ => apply instruction_type_eq_convert in H; subst x; auto
  | H: (local_ctx_beq ?x _ = true) |- _ => apply local_ctx_eq_convert in H; subst x; auto
  | H: (representation_beq ?x _ = true) |- _ => apply representation_eq_convert in H; subst x; auto
  | H: (ref_flag_beq ?x _ = true) |- _ => apply ref_flag_eq_convert in H; subst x; auto
  | H: (size_beq ?x _ = true) |- _ => apply size_eq_convert in H; subst x; auto
  | H: (function_type_beq ?x _ = true) |- _ => apply function_type_eq_convert in H; subst x; auto
  | H: (inner_function_type_beq ?x _ = true) |- _ => apply inner_function_type_eq_convert in H; subst x; auto
  | H: (type_beq ?x _ = true) |- _ => apply type_eq_convert in H; subst x; auto
  | H: (instruction_type_beq ?x _ = true) |- _ => apply instruction_type_eq_convert in H; subst x; auto
  | H: (module_type_beq ?x _ = true) |- _ => apply module_type_eq_convert in H; subst x; auto
  | H: (memory_beq ?x _ = true) |- _ => apply memory_eq_convert in H; subst x; auto
  | H: (num_type_beq ?x _ = true) |- _ => apply num_type_eq_convert in H; subst x; auto
  | H: (path_result_beq ?x _ = true) |- _ => apply path_result_eq_convert in H; subst x; auto
  | H: (list_beq type type_beq ?x _ = true) |- _ => apply list_eq_convert_type in H; subst x; auto
  | H: (list_beq size size_beq ?x _ = true) |- _ => apply list_eq_convert_size in H; subst x; auto
  | H: (function_ctx_beq ?x _ = true) |- _ => apply function_ctx_eq_convert in H; subst x; auto
  end.

Lemma foldr_to_Forall {A} (Pbool: A → bool) (Pprop: A -> Prop) (l : list A) :
  (foldr (λ x:A, andb (Pbool x)) true l) = true ->
  (∀ x, (Pbool x = true) ->  Pprop x) ->
  Forall Pprop l.
Proof.
  intros Hfoldr Hprop.
  apply Forall_fold_right.
  induction l; simpl; auto.
  rewrite foldr_cons in Hfoldr. apply andb_prop in Hfoldr as [a_true l_true].
  auto.
Qed.

Lemma test_foldr F l2 :
  foldr (λ t:type, andb (check_ok_output (has_ref_flag_checker F t NoRefs))) true l2 = true ->
  Forall (fun τ => has_ref_flag F τ NoRefs) l2.
Proof.
  intros.
  apply (foldr_to_Forall (λ t:type, check_ok_output (has_ref_flag_checker F t NoRefs))
           (fun t => has_ref_flag F t NoRefs) l2 ); auto.
  intros. apply check_ok_output_true_to_prop in H0.
  apply has_ref_flag_checker_correct in H0; auto.
Qed.


Ltac my_auto5 :=
  try structural_auto_2; try boolean_equality_auto_2; try
  match goal with
  | H: (synth_resolving_path _ _ _ = Some _) |- _ => apply synth_resolving_path_correct in H; auto
  | H: (synth_resolving_with_outer_replaced_sert _ _ _ _ = Some (_, _)) |- _ =>
      apply synth_resolving_with_outer_replaced_sert_correct in H; destruct H as [H1 H2]; auto
  | H: (synth_resolving_with_outer_replaced_spant _ _ _ _ = Some (_, _, _)) |- _ =>
      apply synth_resolving_with_outer_replaced_spant_correct in H; destruct H as [H1 [H2 H3]]; auto
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
  | H: (function_type_inst_checker _ _ _ _ = inl ()) |- _ => apply function_type_inst_checker_correct in H; auto
  | H: (function_type_inst_checker _ _ _ _ = ok_term) |- _ => apply function_type_inst_checker_correct in H; auto
  | H: (function_type_insts_checker _ _ _ _ = inl ()) |- _ => apply function_type_insts_checker_correct in H; auto
  | H: (function_type_insts_checker _ _ _ _ = ok_term) |- _ => apply function_type_insts_checker_correct in H; auto
  | H: (has_kind_checker _ _ _ = inl ()) |- _ => apply has_kind_checker_correct in H; auto
  | H: (has_kind_checker _ _ _ = ok_term) |- _ => apply has_kind_checker_correct in H; auto
  | H: (has_instruction_type_ok_checker _ _ _ = ok_term) |- _ => apply has_instruction_type_ok_checker_correct in H; auto
  | H: (has_instruction_type_ok_checker _ _ _ = inl ()) |- _ => apply has_instruction_type_ok_checker_correct in H; auto
  | H: (has_instruction_type_num_checker _ _ = ok_term) |- _ => apply has_instruction_type_num_checker_correct in H; auto
  | H: (has_instruction_type_num_checker _ _ = inl ()) |- _ => apply has_instruction_type_num_checker_correct in H; auto
  | H: (has_ref_flag_checker _ _ _ = ok_term) |- _ => apply has_ref_flag_checker_correct in H; auto
  | H: (has_ref_flag_checker _ _ _ = inl ()) |- _ => apply has_ref_flag_checker_correct in H; auto
  | H: (has_num_type_type _ = true) |- _ => apply has_num_type_type_correct in H; destruct H as [ν H]; subst; auto
  | H: (check_ok_output _ = true) |- _ => apply check_ok_output_true_to_prop in H
  | H: (list_suffix ?x _ = Some _) |- _ => apply list_suffix_correct_r in H; subst x
  | H: (split_into_three ?τ _ = Some (_, _, _)) |- _ => apply split_into_three_correct in H; destruct H as [H1 H2]; subst τ
  | H: (split_list_all_last ?l = Some (_, _)) |- _ => apply split_list_all_last_correct in H; subst l
  | H: (unzip_sert ?l = Some (_, _)) |- _ => apply unzip_sert_correct in H; destruct H as [H ?Hlengood]; subst l
  | H: (mono_mem_checker _ = ok_term) |- _ => apply mono_mem_checker_correct in H; auto
  | H: (mono_mem_checker _ = inl ()) |- _ => apply mono_mem_checker_correct in H; auto
  | H: (type_eq_checker _ _ = inl ()) |- _ => apply type_eq_checker_correct in H; auto
  | H: (type_eq_checker _ _ = ok_term) |- _ => apply type_eq_checker_correct in H; auto
  | H: (has_mono_size_checker _ _ = ok_term) |- _ => apply has_mono_size_checker_correct in H; auto
  | H: (has_mono_size_checker _ _ = inl ()) |- _ => apply has_mono_size_checker_correct in H; auto
  | H: (has_mono_rep_checker _ _ = ok_term) |- _ => apply has_mono_rep_checker_correct in H; auto
  | H: (has_mono_rep_checker _ _ = inl ()) |- _ => apply has_mono_rep_checker_correct in H; auto
  | H: (local_ctx_ok_checker _ _ = ok_term) |- _ => apply local_ctx_ok_checker_correct in H; auto
  | H: (local_ctx_ok_checker _ _ = inl ()) |- _ => apply local_ctx_ok_checker_correct in H; auto
  | H: (has_size_checker _ _ _ = inl ()) |- _ => apply has_size_checker_correct in H; auto
  | H: (has_size_checker _ _ _ = ok_term) |- _ => apply has_size_checker_correct in H; auto
  | H: (packed_existential_checker _ _ _ = inl ()) |- _ => apply packed_existential_checker_correct in H; auto
  | H: (packed_existential_checker _ _ _ = ok_term) |- _ => apply packed_existential_checker_correct in H; auto
  | H: (unpacked_existential_checker _ _ _ _ _ _ _ _ = inl ()) |- _ => apply unpacked_existential_checker_correct in H; auto
  | H: (unpacked_existential_checker _ _ _ _ _ _ _ _ = ok_term) |- _ => apply unpacked_existential_checker_correct in H; auto
  | H: (unpacked_existential_getter _ _ _ _ = Some (_, _, _, _)) |- _ => apply unpacked_existential_getter_correct in H; auto
end.
(* Great. Now through tactics. Let's think *)
Lemma test_foldr2 F l2 :
  foldr (λ t:type, andb (check_ok_output (has_ref_flag_checker F t NoRefs))) true l2 = true ->
  Forall (fun τ => has_ref_flag F τ NoRefs) l2.
Proof.
  intros.

  apply (foldr_to_Forall
          (λ t:type, check_ok_output (has_ref_flag_checker F t NoRefs))
          (fun t => has_ref_flag F t NoRefs) l2
        ) in H; [|intros; repeat my_auto5].

  auto.
Qed.

Lemma framing_helper :
  ∀ M F L es τs_pref τs1 τs2 L',
    foldr (λ t:type, andb (check_ok_output (has_mono_rep_checker F t))) true τs_pref = true ->
    have_instruction_type M F L es (InstrT τs1 τs2) L' ->
    have_instruction_type M F L es (InstrT (τs_pref ++ τs1) (τs_pref ++ τs2)) L'.
Proof.
  induction τs_pref.
  - intros. repeat rewrite app_nil_l. done.
  - intros.
    rewrite foldr_cons in H. repeat my_auto5.
    apply TFrame; auto.
Qed.

Lemma grab_rep_has_kind F τ κ ρ :
  grab_rep F τ = Some ρ ->
  has_kind F τ κ ->
  ∃ ξ, κ = VALTYPE ρ ξ.
Proof.
  intros Hgrab Hkind.
  inversion Hkind; subst; cbn in *; try done; inversion Hgrab; subst; try (eexists; done).
  all: destruct κ; try done.
  all: inversion Hgrab; subst.
  all: try (eexists; done).
  - clear H3.
    unfold grab_rep in H2. unfold grab_kind in H2.
    cbn in H2.
    rewrite H in H2.
    inversion H2; subst.
    eexists; done.
  - clear H3.
    unfold grab_rep in H2. unfold grab_kind in H2.
    cbn in H2.
    rewrite H in H2. done.
Qed.

Lemma grab_size_has_kind F τ κ σ :
  grab_size F τ = Some σ ->
  has_kind F τ κ ->
  ∃ ξ, κ = MEMTYPE σ ξ.
Proof.
  intros Hgrab Hkind.
  inversion Hkind; subst; cbn in *; try done; inversion Hgrab; subst; try (eexists; done).
  all: destruct κ; try done.
  all: inversion Hgrab; subst.
  all: try (eexists; done).
  - clear H3.
    unfold grab_size in H2. unfold grab_kind in H2.
    cbn in H2.
    rewrite H in H2. done.
  - clear H3.
    unfold grab_size in H2. unfold grab_kind in H2.
    cbn in H2.
    rewrite H in H2.
    inversion H2; subst.
    eexists; done.
Qed.


Ltac convert_foldr Pbool Pprop l H :=
  apply (foldr_to_Forall Pbool Pprop l) in H; [|intros; repeat my_auto5].



Lemma has_instruction_type_checker_correct :
  ∀ inst M F L ψ L',
    has_instruction_type_checker M F L inst ψ L' = ok_term ->
    has_instruction_type M F L inst ψ L'.
Proof.
  Opaque have_instruction_type_checker.
  intros inst.

  set ( hitc :=
(fix have_instruction_type_checker
    (M:module_ctx) (F:function_ctx) (L:local_ctx)
    (insts:list instruction) (ψ:instruction_type) (L':local_ctx) {struct insts} : type_checker_res :=
    match insts with
    | [] =>
        if (local_ctx_beq L L')
        then
          match ψ with
          | InstrT τs1 τs2 =>
              if list_beq type type_beq τs1 τs2
              then
                if foldr (λ t:type, andb (check_ok_output (has_mono_rep_checker F t))) true τs1
                then local_ctx_ok_checker F L
                else INR "bad empty instruction type (can't frame non mono rep)"
              else INR "bad empty instructions type (not empties or frame)"
          end
        else INR "bad empty instructions type (local contexts don't match)"
    | [e] =>
        let e_ψ := proj_instr_ty e in
        match has_instruction_type_checker M F L e e_ψ L' with
        | inl () => (* now just to check if we need to frame stuff out *)
            match e_ψ, ψ with
            | InstrT τs1_e τs2_e, InstrT τs1_es τs2_es =>
                match list_suffix τs1_es τs1_e, list_suffix τs2_es τs2_e with
                | Some τs1_pref, Some τs2_pref =>
                    (* ts1_es = ts1_pref ++ ts1_e, ts2_es = ts2_pref ++ ts2_e*)
                    (* just need to check that ts1_pref = ts2_pref *)
                    if list_beq type type_beq τs1_pref τs2_pref
                    then (* oh and monorep *)
                      if foldr (λ t:type, andb (check_ok_output (has_mono_rep_checker F t))) true τs1_pref
                      then ok_term
                      else inr [(FrameError "non mono rep" e_ψ ψ)]
                    else inr [(FrameError "single instruction" e_ψ ψ)]
                | _, _ => inr [(FrameError "inner instruction type doesn't match" e_ψ ψ)]
                end
            end
        | err => err
        end
    | e :: es =>
        let e_ψ := proj_instr_ty e in
        match synth_possible_resulting_local_ctx F e L with
        | inr _ => INR "this is either local get/set that is bad, so error?"
        | inl None => INR "the type checker does not support break/return/unreachable in the middle of a block"
        | inl (Some L_e) =>
            match has_instruction_type_checker M F L e e_ψ L_e with
            | inl () =>
                match e_ψ, ψ with
                | InstrT τs1_e τs2_e, InstrT τs1_es τs2_es =>
                    match list_suffix τs1_es τs1_e with (* τs1_es = τs_pref ++ τs1_es *)
                    | Some τs_pref =>
                        if foldr (λ t:type, andb (check_ok_output (has_mono_rep_checker F t))) true τs_pref
                        then have_instruction_type_checker M F L_e es (InstrT (τs_pref ++ τs2_e) τs2_es) L'
                        else INR "can't frame out non mono rep"
                    | None => INR "instruction has more arguments than large have_instruction type has, or can't frame out"
                    end
                end
            | err => err
            end
        end
    end
)
    ) in *.

  induction inst using instruction_ind with
    (P2 := fun insts => ∀ M F L ψ L', hitc M F L insts ψ L' = ok_term ->
    have_instruction_type M F L insts ψ L').

  1: refine ?[Nop]. 2: refine ?[Unreachable]. 3: refine ?[Copy]. 4: refine ?[Drop]. 5: refine ?[Num].
  6: refine ?[NumConst]. 7: refine ?[Block]. 8: refine ?[Loop]. 9: refine ?[Ite]. 10: refine ?[Br].
  11: refine ?[Return]. 12: refine ?[LocalGet]. 13: refine ?[LocalSet]. 14: refine ?[CodeRef]. 15: refine ?[Inst].
  16: refine ?[Call]. 17: refine ?[CallIndirect]. 18: refine ?[Inject]. 19: refine ?[InjectNew]. 20: refine ?[Case].
  21: refine ?[CaseLoad]. 22: refine ?[Group]. 23: refine ?[Ungroup]. 24: refine ?[Fold]. 25: refine ?[Unfold].
  26: refine ?[Pack]. 27: refine ?[Unpack]. 28: refine ?[Tag]. 29: refine ?[Untag]. 30: refine ?[Cast].
  31: refine ?[New]. 32: refine ?[Load]. 33: refine ?[Store]. 34: refine ?[Swap].
  35: refine ?[Nil]. 36: refine ?[Cons].

  Ltac shred := intros; simpl in *; repeat my_auto5; by constructor.
  Ltac eshred := intros; simpl in *; repeat my_auto5; by econstructor.
  Ltac half_shred := intros; simpl in *; repeat my_auto5.

  [Pack]: shred.
  [Unpack]: {
    Opaque unpacked_existential_getter.
    half_shred.
    apply IHinst in HMatch4.
    by econstructor.
  }

  (* Have instr cases *)
  [Nil]: {
    half_shred.
    rename L' into L; rename l0 into τs. subst.
    convert_foldr
      (λ t:type, check_ok_output (has_mono_rep_checker F t ))
      (fun t => has_mono_rep F t) τs HMatch0.
    induction τs.
    - by constructor.
    - apply Forall_cons_1 in HMatch0 as [Ha Hτs].
      apply IHτs in Hτs.
      eapply TFrame; done.
  }

  [Cons]: {
    Opaque have_instruction_type_checker.
    Opaque synth_possible_resulting_local_ctx.
    Opaque has_instruction_type_checker.

    destruct es. (* don't need induction! *)
    - (* singleton case, which is unique bc of break and the like *)
      clear IHinst0. (* just clogs proof state up *)
      half_shred.
      apply IHinst in HMatch.
      subst.
      apply framing_helper; auto.
      apply TSingleton; auto.

    - (* actual cons case *)
      (* shred infinite loops lol *)
      intros.
      rename i into e.
      simpl in H.

      (* the goal is to get hitc (e :: es) out of H. *)
      do 8 (structural_auto_2).
      rename l into L_inst.
      rename l0 into τs1_inst; rename l1 into τs2_inst;
      rename l2 into τs1_full; rename l3 into τs2_full;
      rename l4 into τs1_inst_pref.
      apply list_suffix_correct_r in HMatch3.
      apply IHinst in HMatch1.

      change (?x::?r) with ([x]++r).
      apply TApp with (L2:=L_inst) (τs2:= τs1_inst_pref ++ τs2_inst).
      * subst τs1_full.
        apply framing_helper; auto.
        apply TSingleton; auto.
      * apply IHinst0. auto.

  }

  Transparent has_instruction_type_checker.
  (* Some of the ones that need the IH. *)
  [Block]: {
    half_shred.
    apply IHinst in HMatch0.
    by constructor.
  }
  [Loop]: {
    half_shred.
    apply IHinst in HMatch0.
    by constructor.
  }
  [Ite]: {
    half_shred.
    apply IHinst in HMatch0.
    apply IHinst0 in HMatch.
    by constructor.
  }

  (* The IH + foldr2 lemma folks *)
  [Case]: {
    half_shred.
    subst.
    constructor; try done.
    fold hitc in HMatch3.
    apply flip_foldr2_bool in HMatch3.
    eapply convert_foldr2_bool_to_Forall2_check_ok_output_right_list; try exact HMatch3.
    (* I'm sure there's a way to make the following less jank but it's okay for now *)
    eapply Forall_impl; first exact H.
    intros x MiniF t; apply MiniF.
  }
  [CaseLoad]: {
    half_shred.
    - (* case load copy *)
      fold hitc in HMatch12.
      convert_foldr
        (λ t:type, check_ok_output (has_ref_flag_checker F t GCRefs))
        (fun t => has_ref_flag F t GCRefs) l5 HMatch10.
      subst.
      constructor; try done.
      apply flip_foldr2_bool in HMatch12.
      eapply convert_foldr2_bool_to_Forall2_check_ok_output_right_list; try exact HMatch12.
      (* I'm sure there's a way to make the following less jank but it's okay for now *)
      eapply Forall_impl; first exact H.
      intros x MiniF t; apply MiniF.
    - (* case load move *)
      subst.
      fold hitc in HMatch8.
      constructor; try done.
      apply flip_foldr2_bool in HMatch8.
      eapply convert_foldr2_bool_to_Forall2_check_ok_output_right_list; try exact HMatch8.
      (* I'm sure there's a way to make the following less jank but it's okay for now *)
      eapply Forall_impl; first exact H.
      intros x MiniF t; apply MiniF.
  }

  (* All the basic ones *)
  [Nop]: shred.
  [Unreachable]: shred.
  [Copy]: shred.
  [Drop]: shred.
  [Num]: shred.
  [NumConst]: shred.
  [LocalGet]: shred.
  [Group]: shred.
  [Ungroup]: shred.
  [Fold]: shred.
  [Unfold]: shred.
  [Tag]: shred.
  [Untag]: shred.
  [CodeRef]: shred.
  [Inst]: shred.
  [CallIndirect]: shred.
  [Inject]: shred.
  [InjectNew]: shred.
  [Cast]: shred.
  [New]: shred.

  (* Next, almost basic *)
  [Call]: eshred.
  [LocalSet]: eshred.



  (* Some of the ones with pure foldr *)
  [Br]: {
    half_shred.
    convert_foldr
      (λ t:type, check_ok_output (has_ref_flag_checker F t NoRefs))
      (fun t => has_ref_flag F t NoRefs) l2 HMatch2.
    by constructor.
  }
  [Return]: {
    half_shred.
    convert_foldr
      (λ t:type, check_ok_output (has_ref_flag_checker F t NoRefs))
      (fun t => has_ref_flag F t NoRefs) l1 HMatch0.
    by constructor.
  }
  [Load]: {
    half_shred.
    - (* GC case *)
      convert_foldr
        (λ t:type, check_ok_output (has_mono_size_checker F t))
        (fun t => has_mono_size F t) (pr_prefix p) HMatch.
      by eapply TLoadCopy.
    - (* MM case *)
      convert_foldr
        (λ t:type, check_ok_output (has_mono_size_checker F t))
        (fun t => has_mono_size F t) (pr_prefix p1) HMatch.
      by eapply TLoadMove.
  }
  [Store]: {
    half_shred.
    - (* store weak case *)
      convert_foldr
        (λ t:type, check_ok_output (has_mono_size_checker F t))
        (fun t => has_mono_size F t) (pr_prefix p) HMatch0.
      rewrite <- HMatch in HMatch8.
      by eapply TStoreWeak.
    - (* store strong case *)
      convert_foldr
        (λ t:type, check_ok_output (has_mono_size_checker F t))
        (fun t => has_mono_size F t) (pr_prefix p0) H3.
      apply Nat.eqb_eq in H2; subst.
      rewrite <- HMatch1 in HMatch2.
      inversion HMatch14. rename x into κtarg. destruct H as [hkindtarg href].
      pose proof grab_size_has_kind _ _ _ _ HMatch hkindtarg.
      destruct H as [ξ ->].
      eapply TStoreStrong; try done.
      1: econstructor; done.
      assert (exists κ, has_kind F t0 κ) as [κ Ht0]. {
        (* this is basically quarantine hell using has_instruction_type_ok *)
        clear - H0.
        inversion H0.
        inversion H.
        inversion H2; subst.
        inversion H7; subst.
        inversion H8; subst.
        destruct H4 as [hi _].
        inversion hi; subst.
        eexists; done.
      }
      pose proof grab_rep_has_kind _ _ _ _ HMatch0 Ht0 as [ξ0 ->].
      eexists; done.
  }
  [Swap]: {
    half_shred.
    convert_foldr
      (λ t:type, check_ok_output (has_mono_size_checker F t))
      (fun t => has_mono_size F t) (pr_prefix p) HMatch7.
    by econstructor.
  }
Qed.

Lemma have_instruction_type_checker_correct :
  ∀ insts M F L ψ L',
    have_instruction_type_checker M F L insts ψ L' = ok_term ->
    have_instruction_type M F L insts ψ L'.
Proof.
  induction insts.
  Transparent have_instruction_type_checker.
  - half_shred.
    rename L' into L; rename l0 into τs. subst.
    convert_foldr
      (λ t:type, check_ok_output (has_mono_rep_checker F t ))
      (fun t => has_mono_rep F t) τs HMatch0.
    induction τs.
    + by constructor.
    + apply Forall_cons_1 in HMatch0 as [Ha Hτs].
      apply IHτs in Hτs.
      eapply TFrame; done.
  - destruct insts.
    + clear IHinsts.
      half_shred.
      apply has_instruction_type_checker_correct in HMatch.
      apply framing_helper; auto.
      apply TSingleton; auto.
    + intros. rename i into e; simpl in H.
      do 8 (structural_auto_2).
      rename l into L_inst.
      rename l0 into τs1_inst; rename l1 into τs2_inst;
      rename l2 into τs1_full; rename l3 into τs2_full;
      rename l4 into τs1_inst_pref.
      apply list_suffix_correct_r in HMatch3.
      apply has_instruction_type_checker_correct in HMatch1.

      change (?x::?r) with ([x]++r).
      apply TApp with (L2:=L_inst) (τs2:= τs1_inst_pref ++ τs2_inst).
      * subst τs1_full.
        apply framing_helper; auto.
        apply TSingleton; auto.
      * apply IHinsts. auto.
Qed.

Fixpoint synth_possible_resulting_local_ctx_insts F insts L : (option local_ctx) + type_error :=
  match insts with
  | [] => inl (Some L)
  | [i] =>
      match synth_possible_resulting_local_ctx F i L with
      | inl (Some L') => inl (Some L')
      | inl (None) => inl (Some L) (* IF LAST INSTR IS BREAK/RETURN, JUST KEEP SAME LOCAL CTX *)
      | inr a => inr a
      end
  | i :: rest =>
      match synth_possible_resulting_local_ctx F i L with
      | inl (Some L') => synth_possible_resulting_local_ctx_insts F rest L'
      | inl (None) => inl (None) (* IF BREAK/RETURN IN THE MIDDLE, FAIL *)
      | inr a => inr a
      end
  end.

Definition body_has_mono_type_checker
  (M : module_ctx)
  (K : kind_ctx)
  (mf_locs : list representation)
  (body : list instruction)
  (κs : list kind)
  (τs1 τs2 : list type)
  : type_checker_res :=
  match mapM (eval_rep_prim EmptyEnv) mf_locs with
  | Some ηss_L =>
      let tempF := Build_function_ctx [] [] [] K κs in
      match mapM (grab_rep tempF) τs1 with
      | Some ρs_P =>
          if foldr2_bool (λ t, λ r, andb (check_ok_output (has_rep_checker tempF t r))) true false τs1 ρs_P
          then
            match mapM (eval_rep_prim EmptyEnv) ρs_P with
            | Some ηss_P =>
                let tempF2 := Build_function_ctx τs2 (ηss_P ++ ηss_L) [] K κs in
                let L := τs1 ++ map type_plug_prim ηss_L in
                let ψ := InstrT [] τs2 in
                match synth_possible_resulting_local_ctx_insts tempF2 body L with
                | inl (Some L') =>
                    let F := tempF2 <| fc_labels := [(τs2, L')] |> in
                    let res := map (λ t, has_ref_flag_checker F t NoRefs) L' in (* used for errors *)
                    let folded := foldr (λ r, andb (check_ok (λ t, has_ref_flag_checker F t NoRefs) r)) true L' in
                    if folded
                    then have_instruction_type_checker M F L body ψ L'
                    else
                      inr ([LocalCtxSynthError "your resulting locals aren't all nonrefs"
                              L L' (combine_error_messages res)])
                (* inr ([NormalError "your resulting locals aren't all nonrefs"] ++ combine_error_messages res) *)
                (* INR ("your resulting locals aren't all norefs (" ++ *)
                (*           (combine_error_messages res) ++ ")"%string) *)
                | inl None => INR "don't know how to deal with breaks and stuff yet for synthing local ctx"
                | inr a => INR "error in synthing local ctx (e.g. bad local get/set)"
                end
            | None => INR "AAAAAAAAAAAAA"
            end
          else INR "nnnnnn"
      | None => INR "aaaaaa"
      end
  | None => INR "can't give function type"
  end.

Lemma grab_rep_in_messed_up_F :
  ∀ ϕ_out ηss_P ηss_L K ϕ_type_vars ϕ_in ρs_P,
    let halfF := Build_function_ctx [] [] [] K ϕ_type_vars in
    let fullF := Build_function_ctx ϕ_out (ηss_P ++ ηss_L) [] K ϕ_type_vars in
    grab_rep halfF ϕ_in = Some ρs_P <-> grab_rep fullF ϕ_in = Some ρs_P.
Proof.
  split; intros.
  all: unfold grab_rep in *; unfold grab_kind in *.
  all: cbn in *; auto.
Qed.

Lemma mapM_grab_rep_in_messed_up_F :
  ∀ ϕ_out ηss_P ηss_L K ϕ_type_vars ϕ_in ρs_P,
    let halfF := Build_function_ctx [] [] [] K ϕ_type_vars in
    let fullF := Build_function_ctx ϕ_out (ηss_P ++ ηss_L) [] K ϕ_type_vars in
    mapM (grab_rep halfF) ϕ_in = Some ρs_P <-> mapM (grab_rep fullF) ϕ_in = Some ρs_P.
Proof.
  split; intros.
  all: unfold grab_rep, grab_kind in *.
  all: cbn in *.
  all: done.
Qed.

Lemma body_has_mono_type_checker_correct :
  ∀ M K mf_locs body κs τs1 τs2,
    body_has_mono_type_checker M K mf_locs body κs τs1 τs2 = ok_term ->
    body_has_ifun_type M K mf_locs body κs (MonoFunT τs1 τs2).
Proof.
  intros * H.
  unfold body_has_mono_type_checker in H.
  repeat my_auto5; subst.
  rename l2 into L'.
  rename l into ηss_L.
  rename l0 into ρs_P.
  rename l1 into ηss_P.
  (* let's slowly get everything that's necessary *)
  eapply TMono.
  5: by apply have_instruction_type_checker_correct.
  all: try done.
  - pose proof (has_rep_checker_correct (Build_function_ctx [] [] [] K κs)).
    eapply convert_foldr2_bool_to_Forall2_check_ok_output_pure_forall; try done.
  - set (F := (Build_function_ctx τs2 (ηss_P ++ ηss_L) [(τs2, L')] K κs)) in *.
    pose proof (has_ref_flag_checker_correct F).
    specialize H with (ξ:=NoRefs).
    eapply convert_foldr_to_Forall_check_ok; try done.
Qed.

Fixpoint body_has_ifun_type_checker
  (M : module_ctx)
  (K : kind_ctx)
  (mf_locs : list representation)
  (body : list instruction)
  (κs : list kind) (ϕ : inner_function_type)
  : type_checker_res :=
  match ϕ with
  | MonoFunT τs1 τs2 => body_has_mono_type_checker M K mf_locs body κs τs1 τs2
  | ForallTypeT κ ϕ => body_has_ifun_type_checker M K mf_locs body (κ :: κs) ϕ
  end.

Lemma body_has_ifun_type_checker_correct :
  ∀ ϕ M K mf_locs body κs,
    body_has_ifun_type_checker M K mf_locs body κs ϕ = ok_term ->
    body_has_ifun_type M K mf_locs body κs ϕ.
Proof.
  induction ϕ.
  - intros * H.
    by apply body_has_mono_type_checker_correct.
  - intros * H.
    cbn in H.
    apply IHϕ in H.
    by constructor.
Qed.


Fixpoint body_has_fun_type_checker
  (M : module_ctx)
  (mf_locs : list representation)
  (body : list instruction)
  (K : kind_ctx)
  (ϕ : function_type)
  : type_checker_res :=
  match ϕ with
  | InnerFunT ϕ =>
    body_has_ifun_type_checker M K mf_locs body [] ϕ
  | ForallMemT ϕ =>
    body_has_fun_type_checker M mf_locs body (K <| kc_mem_vars ::= S |>) ϕ
  | ForallRepT ϕ =>
    body_has_fun_type_checker M mf_locs body (K <| kc_rep_vars ::= S |>) ϕ
  | ForallSizeT ϕ =>
    body_has_fun_type_checker M mf_locs body (K <| kc_size_vars ::= S |>) ϕ
  end.

Lemma body_has_fun_type_checker_correct :
  ∀ ϕ M K mf_locs body,
    body_has_fun_type_checker M mf_locs body K ϕ = ok_term ->
    body_has_fun_type M mf_locs body K ϕ.
Proof.
  induction ϕ.
  all: intros * H; constructor.
  all: cbn in H.
  all: try by apply body_has_ifun_type_checker_correct.
  all: by apply IHϕ in H.
Qed.

Definition has_function_type_checker
    (M:module_ctx) (mf:module_function) : type_checker_res :=
  body_has_fun_type_checker M mf.(mf_locals) mf.(mf_body) kc_empty mf.(mf_type).


Lemma has_function_type_checker_correct :
  ∀ M mf, has_function_type_checker M mf = ok_term ->
          has_function_type M mf.
Proof.
  intros.
  by apply body_has_fun_type_checker_correct.
Qed.


Definition has_module_type_checker (m:module) (mt:module_type) : type_checker_res :=
  let ϕs := m.(m_imports) ++ map mf_type m.(m_functions) in
  match nths_error ϕs m.(m_table) with
  | Some table =>
      match nths_error ϕs (map me_desc m.(m_exports)) with
      | Some exports =>
          if module_type_beq mt (Build_module_type m.(m_imports) exports)
          then
            let M := Build_module_ctx ϕs table in
            let res := map (λ mf, has_function_type_checker M mf) m.(m_functions) in
            let folded := foldr (λ r, andb (check_ok (λ mf, has_function_type_checker M mf) r)) true (m.(m_functions)) in
            if folded
            then ok_term
            else
              inr ([NormalError "can't module check"] ++ combine_error_messages res)
              (* INR ("can't module check: " ++ (combine_error_messages res)) *)
          else INR "suggested module type not equal to what it needs to be"
      | None => INR "bad exports"
      end
  | None => INR "bad table"
  end
.
Lemma has_module_type_checker_correct :
  ∀ m mt, has_module_type_checker m mt = ok_term -> has_module_type m mt.
Proof.
  intros.
  Opaque has_function_type_checker. Opaque module_type_beq.
  unfold has_module_type_checker in H.
  repeat my_auto5.
  rename l into table.
  rename l0 into exports.
  apply (TModule m table exports); auto.
  pose proof (has_function_type_checker_correct
                (Build_module_ctx (m_imports m ++ map mf_type (m_functions m)) (table))).
  eapply convert_foldr_to_Forall_check_ok; try done.
Qed.
Print Assumptions has_module_type_checker_correct.

Definition synth_module_type (m:module) : option module_type :=
  let ϕs := m.(m_imports) ++ map mf_type m.(m_functions) in
      match nths_error ϕs (map me_desc m.(m_exports)) with
      | Some exports =>
          Some (Build_module_type m.(m_imports) exports)
      | None => None
      end.

Definition has_module_type_checker_with_synth (m:module) : type_checker_res :=
  match synth_module_type m with
  | Some mt => has_module_type_checker m mt
  | None => INR "couldn't synthesize module type"
  end.
