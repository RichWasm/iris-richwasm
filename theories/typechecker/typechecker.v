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
Scheme Equality for ref_flag.
Scheme Equality for atomic_rep.
Scheme Equality for base_memory.
Scheme Equality for memory.
Scheme Equality for list.
Scheme Equality for num_type.
Scheme Equality for primitive.
Scheme Equality for num_instruction.
Scheme Equality for consumption.


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
  ∀ n1 n2, num_instruction_beq n1 n2 = true <-> n1 = n2. Proof. Admitted.

Lemma ref_flag_eq_convert :
  ∀ ξ1 ξ2, ref_flag_beq ξ1 ξ2 = true <-> ξ1 = ξ2.
Proof.
  split; intros;
    [by apply internal_ref_flag_dec_bl in H | by apply internal_ref_flag_dec_lb in H].
Qed.

Fixpoint representation_beq (r1:representation) (r2:representation) : bool :=
  match r1, r2 with
  | VarR i1, VarR i2 => (i1 =? i2)
  | SumR r1s, SumR r2s => list_beq representation representation_beq r1s r2s
  | ProdR r1s, ProdR r2s => list_beq representation representation_beq r1s r2s
  | AtomR a1, AtomR a2 => atomic_rep_beq a1 a2
  | _, _ => false
  end.

Lemma representation_eq_convert_forward :
  ∀ r1, (∀ r2, representation_beq r1 r2 = true -> r1 = r2).
Proof.
  induction r1 using rep_ind.
  * intros; destruct r2; simpl in H; try inversion H. apply Nat.eqb_eq in H; by subst.
  * intros. destruct r2; simpl in H0; try inversion H0. clear H2.
    pose proof internal_list_dec_bl as ToUse.
    specialize (ToUse representation representation_beq).

    (* I'm confused actually. To use internal_list_dec_bl, I need to
       have a proof of representation_beq r1 r2 = true -> r1 = r2, but the
       IH is specific to ρs.
       TODO *)
Admitted.

Lemma representation_eq_convert_backward :
  ∀ r1 r2, r1 = r2 -> representation_beq r1 r2 = true.
Proof.
  intros; subst.
  induction r2 using rep_ind.
  * simpl. apply Nat.eqb_refl.
  * simpl.
    (* Hm once again a similar issue. *)
Admitted.

Lemma representation_eq_convert :
  ∀ r1 r2, representation_beq r1 r2 = true <-> r1 = r2.
Proof.
  split; [apply representation_eq_convert_forward | apply representation_eq_convert_backward].
Qed.

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
  (* Same issue happens here *)
Admitted.

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
  (* fix to deal with ref flag
  - intros. destruct k1, k2; simpl in H; try inversion H; clear H1; repeat structural_auto.
    * apply representation_eq_convert in H1.
      apply copyability_eq_convert in H0.
      apply internal_dropability_dec_bl in H2. subst; auto.
    * apply size_eq_convert in H1.
      apply internal_dropability_dec_bl in H2. subst; auto.
  - intros; subst. destruct k2; simpl.
    * apply andb_true_intro; split; [|apply andb_true_intro; split].
      + assert (H:r=r) by auto. apply representation_eq_convert in H. auto.
      + assert (H:c=c) by auto. apply copyability_eq_convert in H; auto.
      + assert (H:d=d) by auto. apply internal_dropability_dec_lb in H. auto.
    * apply andb_true_intro; split.
      + assert (H:s=s) by auto. apply size_eq_convert in H; auto.
      + assert (H:d=d) by auto. apply internal_dropability_dec_lb in H; auto.
*)
Admitted.

Lemma kind_neq_convert :
  ∀ k1 k2, kind_beq k1 k2 = false <-> k1 <> k2.
Proof.
  split; intros.
  (* there's some decidability lemmas that would need to be done. This is fine to leave. *)
Admitted.


Lemma num_type_eq_convert :
  ∀ nt1 nt2, num_type_beq nt1 nt2 = true <-> nt1 = nt2.
Proof.
  split; intros;
    [by apply internal_num_type_dec_bl in H | by apply internal_num_type_dec_lb in H].
Admitted.

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


Lemma memory_eq_convert :
  ∀ m1 m2, memory_beq m1 m2 = true <-> m1 = m2.
Proof.
   split; intros;
    [by apply internal_memory_dec_bl in H | by apply internal_memory_dec_lb in H].
Qed.

(* I'm bad at everything so monomorphic *)
Lemma list_eq_convert_type :
  ∀ τs1 τs2, list_beq type type_beq τs1 τs2 = true <-> τs1 = τs2.
Proof. Admitted.
Lemma list_eq_convert_size :
  ∀ τs1 τs2, list_beq size size_beq τs1 τs2 = true <-> τs1 = τs2.
Proof. Admitted.
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
  split; intros.
  - destruct m1, m2.
    unfold module_type_beq in H.
    (* yup the things that are equal are equal *)
    admit.
  - subst.
    destruct m2.
    unfold module_type_beq. cbn.
    (* yup it's equal *)
    admit.
    (* to complete this, it's a list_beq thing *)
Admitted.
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

Definition function_ctx_beq F1 F2 : bool :=
  (list_beq type type_beq F1.(fc_return) F2.(fc_return)) &&
  (list_beq (list primitive) (list_beq primitive primitive_beq) F1.(fc_locals) F2.(fc_locals)) &&
  (list_beq (list type * local_ctx)
     (λ p1, λ p2, let (lt1, L1):=p1 in let (lt2, L2):=p2 in
        (list_beq type type_beq lt1 lt2) && (local_ctx_beq L1 L2))
     F1.(fc_labels) F2.(fc_labels)) &&
  (kind_ctx_beq F1.(fc_kind_ctx) F2.(fc_kind_ctx)) &&
  (list_beq kind kind_beq F1.(fc_type_vars) F2.(fc_type_vars)).

Lemma function_ctx_eq_convert :
  ∀ F1 F2, function_ctx_beq F1 F2 = true <-> F1 = F2.
Proof. Admitted.

Definition index_beq ix1 ix2 :=
  match ix1, ix2 with
  | MemI m1, MemI m2 => memory_beq m1 m2
  | RepI r1, RepI r2 => representation_beq r1 r2
  | SizeI s1, SizeI s2 => size_beq s1 s2
  | TypeI t1, TypeI t2 => type_beq t1 t2
  | _, _ => false
  end.

Fixpoint instruction_beq e1 e2 : bool :=
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
   => instruction_type_beq ϕ1 ϕ2
 | INum ϕ1 n1, INum ϕ2 n2 => instruction_type_beq ϕ1 ϕ2 && num_instruction_beq n1 n2
 | INumConst ϕ1 n1, INumConst ϕ2 n2
 | IBr ϕ1 n1, IBr ϕ2 n2
 | ILocalGet ϕ1 n1, ILocalGet ϕ2 n2
 | ILocalSet ϕ1 n1, ILocalSet ϕ2 n2
 | ICodeRef ϕ1 n1, ICodeRef ϕ2 n2
 | IInject ϕ1 n1, IInject ϕ2 n2
 | IInjectNew ϕ1 n1, IInjectNew ϕ2 n2
   => instruction_type_beq ϕ1 ϕ2 && (n1 =? n2)
 | IUnpack ϕ1 τs1 es1, IUnpack ϕ2 τs2 es2
 | IBlock ϕ1 τs1 es1, IBlock ϕ2 τs2 es2 =>
     instruction_type_beq ϕ1 ϕ2 && (list_beq type type_beq τs1 τs2) && (list_beq instruction instruction_beq es1 es2)
 | ILoop ϕ1 es1, ILoop ϕ2 es2 =>
     instruction_type_beq ϕ1 ϕ2 && (list_beq instruction instruction_beq es1 es2)
 | IIte ϕ1 τs1 es11 es12, IIte ϕ2 τs2 es21 es22 =>
     instruction_type_beq ϕ1 ϕ2 && (list_beq type type_beq τs1 τs2)
     && (list_beq instruction instruction_beq es11 es21)
     && (list_beq instruction instruction_beq es12 es22)
 | IInst ϕ1 ix1, IInst ϕ2 ix2 => instruction_type_beq ϕ1 ϕ2 && index_beq ix1 ix2
 | ICall ϕ1 n1 ixs1, ICall ϕ2 n2 ixs2 =>
     instruction_type_beq ϕ1 ϕ2 && (n1 =? n2) && (list_beq index index_beq ixs1 ixs2)
 | ICase ϕ1 τs1 ees1, ICase ϕ2 τs2 ees2 =>
     instruction_type_beq ϕ1 ϕ2 && (list_beq type type_beq τs1 τs2) &&
       (list_beq (list instruction) (list_beq instruction instruction_beq) ees1 ees2)
 | ICaseLoad ϕ1 c1 τs1 ees1, ICaseLoad ϕ2 c2 τs2 ees2 =>
     instruction_type_beq ϕ1 ϕ2 && (list_beq type type_beq τs1 τs2) &&
       (list_beq (list instruction) (list_beq instruction instruction_beq) ees1 ees2) && consumption_beq c1 c2
 | ILoad ϕ1 ns1 c1, ILoad ϕ2 ns2 c2 =>
     instruction_type_beq ϕ1 ϕ2 && (list_beq nat Nat.eqb ns1 ns2) && consumption_beq c1 c2
 | IStore ϕ1 ns1, IStore ϕ2 ns2
 | ISwap ϕ1 ns1, ISwap ϕ2 ns2 =>
     instruction_type_beq ϕ1 ϕ2 && (list_beq nat Nat.eqb ns1 ns2)
 | _, _ => false
 end.

Lemma instruction_eq_convert :
  ∀ e1 e2, instruction_beq e1 e2 = true <-> e1 = e2. Proof. Admitted.

Lemma list_eq_convert_instruction :
  ∀ es1 es2, list_beq instruction instruction_beq es1 es2 = true <-> es1 = es2. Proof. Admitted.

Ltac boolean_equality_auto :=
  match goal with
  | H: (kind_beq _ _ = true) |- _ => apply kind_eq_convert in H; subst; auto
  | H: (instruction_type_beq _ _ = true) |- _ => apply instruction_type_eq_convert in H; subst; auto
  | H: (local_ctx_beq _ _ = true) |- _ => apply local_ctx_eq_convert in H; subst; auto
  | H: (representation_beq _ _ = true) |- _ => apply representation_eq_convert in H; subst; auto
  | H: (ref_flag_beq _ _ = true) |- _ => apply ref_flag_eq_convert in H; subst; auto
  | H: (size_beq _ _ = true) |- _ => apply size_eq_convert in H; subst; auto
  | H: (function_type_beq _ _ = true) |- _ => apply function_type_eq_convert in H; subst; auto
  | H: (type_beq _ _ = true) |- _ => apply type_eq_convert in H; subst; auto
  | H: (instruction_type_beq _ _ = true) |- _ => apply instruction_type_eq_convert in H; subst; auto
  | H: (module_type_beq _ _ = true) |- _ => apply module_type_eq_convert in H; subst; auto
  | H: (memory_beq _ _ = true) |- _ => apply memory_eq_convert in H; subst; auto
  | H: (num_type_beq _ _ = true) |- _ => apply num_type_eq_convert in H; subst; auto
  | H: (path_result_beq _ _ = true) |- _ => apply path_result_eq_convert in H; subst; auto
  | H: (list_beq type type_beq _ _ = true) |- _ => apply list_eq_convert_type in H; subst; auto
  | H: (list_beq size size_beq _ _ = true) |- _ => apply list_eq_convert_size in H; subst; auto
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
      specialize (IHl l0 last0 eq_refl).
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

Lemma list_suffix_correct_l :
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
      (* yeah this is right, I just need theorems about lengths of lists *)
      admit.
Admitted.

Lemma list_suffix_correct_r :
  ∀ lfull lpre lsuf,
    list_suffix lfull lsuf = Some lpre -> lfull = lpre ++ lsuf.
Proof.
  intros lfull; induction lfull.
  - intros; simpl in *. destruct lpre, lsuf; try inversion H. auto.
  - intros lprebig.
    destruct lprebig as [ | a' lpre ].
    + intros lsuf Hlsuf.
      admit.
    + (* yeah this is fine too *) admit.
Admitted.




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
  | (VALTYPE ρ1 NoRefs), (VALTYPE ρ2 GCRefs) =>
      if (representation_beq ρ1 ρ2)
      then ok_term else INR "fail in subkind check"
  | (VALTYPE ρ1 GCRefs), (VALTYPE ρ2 AnyRefs) =>
      if (representation_beq ρ1 ρ2)
      then ok_term else INR "fail in subkind check"
  | (MEMTYPE σ1 NoRefs), (MEMTYPE σ2 GCRefs) =>
      if size_beq σ1 σ2
      then ok_term else INR "fail in subkind check"
  | (MEMTYPE σ1 GCRefs), (MEMTYPE σ2 AnyRefs) =>
      if size_beq σ1 σ2
      then ok_term else INR "fail in subkind check"
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
end.


Lemma subkind_of_checker_correct :
  ∀ k1 k2, subkind_of_checker k1 k2 = ok_term -> subkind_of k1 k2.
Proof.
  intros.
  destruct k1, k2.
  2, 3: cbn in H; repeat structural_auto.
  2: destruct r, r0. 1: destruct r0, r2.
  all: simpl in H; try inversion H; repeat my_auto2; constructor.
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
Definition check_if_subkind (k1:kind) (k2:kind) : type_checker_res :=
  match k1, k2 with
  | VALTYPE ρ1 ξ1, VALTYPE ρ2 ξ2 =>
      if representation_beq ρ1 ρ2
      then
        match ξ1, ξ2 with
        | NoRefs, _
        | GCRefs, GCRefs
        | GCRefs, AnyRefs
        | AnyRefs, AnyRefs => ok_term
        | _, _ => INR "not subkind"
        end
      else INR "mismatch in representation for subkinds"
  | MEMTYPE σ1 ξ1, MEMTYPE σ2 ξ2 =>
      if size_beq σ1 σ2
      then
        match ξ1, ξ2 with
        | NoRefs, _
        | GCRefs, GCRefs
        | GCRefs, AnyRefs
        | AnyRefs, AnyRefs => ok_term
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
  Ltac local_auto := eapply KSub; try constructor; auto.
  
  intros.
  destruct k1, k2; simpl in H; repeat my_auto2; subst; auto; try (inversion H).
  - destruct r2; auto; local_auto. local_auto.
  - local_auto.
  - destruct r0; auto; local_auto. local_auto.
  - local_auto.
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
      if (kind_beq κ (VALTYPE (AtomR PtrR) NoRefs))
      then check_if_subkind κ k
      else INR "wrong kind for I31T"
    (* NumT *)
  | NumT κ (IntT I32T) =>
      if (kind_beq κ (VALTYPE (AtomR I32R) NoRefs))
      then check_if_subkind κ k
      else INR "wrong kind for I32T"
  | NumT κ (IntT I64T) =>
      if (kind_beq κ (VALTYPE (AtomR I64R) NoRefs) )
      then check_if_subkind κ k
      else INR "wrong kind for I64T"
  | NumT κ (FloatT F32T) =>
      if (kind_beq κ (VALTYPE (AtomR F32R) NoRefs))
      then check_if_subkind κ k
      else INR "wrong kind for F32T"
  | NumT κ (FloatT F64T) =>
      if (kind_beq κ (VALTYPE (AtomR F64R) NoRefs))
      then check_if_subkind κ k
      else INR "wrong kind for F64T"
  (* Sums and Prods *)
  | SumT κ τs =>
      match κ with
      | VALTYPE (SumR ρs) ξ =>
          if foldr2
               (λ t:type, λ r:representation,
                  andb (check_ok_output (has_kind_checker F t (VALTYPE r ξ)))
               ) true τs ρs
          then check_if_subkind κ k
          else INR "bad sum kind internals"
      | _ => INR "bad sum kind format"
      end
  | VariantT κ τs =>
      match κ with
      | MEMTYPE (SumS σs) ξ =>
          if foldr2
               (λ t:type, λ s:size,
                  andb (check_ok_output (has_kind_checker F t (MEMTYPE s ξ)))
               ) true τs σs
          then check_if_subkind κ k
          else INR "bad sum kind internals"
      | _ => INR "bad variant kind format"
      end
   | ProdT κ τs =>
      match κ with
      | VALTYPE (ProdR ρs) ξ =>
          if foldr2
               (λ t:type, λ r:representation,
                  andb (check_ok_output (has_kind_checker F t (VALTYPE r ξ)))
               ) true τs ρs
          then check_if_subkind κ k
          else INR "bad sum kind internals"
      | _ => INR "bad prod kind format"
      end
  | StructT κ τs =>
      match κ with
      | MEMTYPE (ProdS σs) ξ =>
          if foldr2
               (λ t:type, λ s:size,
                  andb (check_ok_output (has_kind_checker F t (MEMTYPE s ξ)))
               ) true τs σs
          then check_if_subkind κ k
          else INR "bad sum kind internals"
      | _ => INR "bad struct kind format"
      end
  (* References *)
  | RefT κ (BaseM MemGC) τ =>
      if (kind_beq κ (VALTYPE (AtomR PtrR) GCRefs))
      then
        match grab_kind F τ with
          | Some innerk =>
              match innerk with
              | MEMTYPE σ ξ =>
                  match has_kind_checker F τ (MEMTYPE σ ξ) with
                  | inl () => check_if_subkind κ k
                  | err => err
                  end
              | _ => INR "you have a reft t where t isnt memtype"
              end
          | None => INR "i think you have a bad variable or smthn"
          end
      else INR "bad gc mem kind format"
  | RefT κ μ τ =>
      if (kind_beq κ (VALTYPE (AtomR PtrR) AnyRefs))
      then
        match mem_ok_checker (F.(fc_kind_ctx)) μ with
          | inl () =>
              match grab_kind F τ with
              | Some innerk =>
                  match innerk with
                  | MEMTYPE σ ξ =>
                      match has_kind_checker F τ (MEMTYPE σ ξ) with
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
      | VALTYPE (AtomR I32R) NoRefs =>
          match function_type_ok_checker F ϕ with
          | inl () => check_if_subkind κ k
          | err => err
          end
      | _ => INR "bad coderef kind format"
      end
  (* Some weird ones I guess *)
  | SerT κ τ =>
      match κ with
      | MEMTYPE (RepS ρ) ξ =>
          match has_kind_checker F τ (VALTYPE ρ ξ) with
          | inl () => check_if_subkind κ k
          | err => err
          end
      | _ => INR "bad ser kind format"
      end
  | PlugT κ ρ =>
      match κ with
      | VALTYPE ρ1 NoRefs =>
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
      | MEMTYPE σ1 NoRefs =>
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
  1-3: match goal with
    | HSTAR: (has_kind_checker _ _ _ = _) |- _ => apply H in HSTAR
    end.

  1-2: eapply check_if_subkind_works_with_has_kind; [apply H0 | apply (KRef _ _ _ s r); auto].
  1: eapply check_if_subkind_works_with_has_kind; [apply H0 | apply (KRefGC _ _ s r); auto].


Admitted.

Lemma has_kind_checker_correct :
  ∀ F t k, has_kind_checker F t k = ok_term -> has_kind F t k.
Proof.
  pose proof has_kind_checker_correct_basic.
  destruct H; auto.
Qed.


(* Small things before pathing *)
Definition has_rep_checker F τ ρ : type_checker_res :=
  has_kind_checker F τ (VALTYPE ρ NoRefs).

Lemma has_rep_checker_correct :
  ∀ F τ ρ, has_rep_checker F τ ρ = ok_term -> has_rep F τ ρ.
Proof.
  intros.
  unfold has_rep_checker in H.
  apply has_kind_checker_correct in H.
  apply (RepVALTYPE _ _ _ NoRefs); auto.
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

Lemma grab_rep_correct :
  ∀ F τ ρ, grab_rep F τ = Some ρ -> has_rep F τ ρ.
Proof.
  intros.
  unfold grab_rep in H; repeat structural_auto.
  eapply RepVALTYPE.
  unfold grab_kind in *.
  subst.
  (* need to prove grab_kind correct later. Mechanical *)
Admitted.

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
  has_kind_checker F τ (MEMTYPE σ NoRefs).

Lemma has_size_checker_correct :
  ∀ F τ σ, has_size_checker F τ σ = ok_term -> has_size F τ σ.
Proof.
  intros. unfold has_size_checker in H.
  apply has_kind_checker_correct in H.
  unfold has_size.
  by exists NoRefs.
Qed.

Definition grab_size_correct :
  ∀ F τ σ, grab_size F τ = Some σ -> has_size F τ σ.
Proof.
  intros.
  unfold grab_size in H; repeat structural_auto. subst.
  exists r.
  (* prove grab_kind correct later *)
Admitted.

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
  by apply (MonoSizeMEMTYPE _ _ s NoRefs).
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
  (* give some theorems about list_beq, this is obvious *)
  admit.
Admitted.

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
  apply Nat.eqb_eq in HMatch1; subst.
  econstructor; [apply HMatch | apply HMatch0].
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
  match grab_kind F τ with
  | Some κ =>
      match κ with
      | VALTYPE ρ _ => has_kind_checker F τ (VALTYPE ρ ξ)
      | MEMTYPE σ _ => has_kind_checker F τ (MEMTYPE σ ξ)
      end
  | None => INR "bad kind"
  end.
Lemma has_ref_flag_checker_correct :
  ∀ F τ ξ, has_ref_flag_checker F τ ξ = ok_term -> has_ref_flag F τ ξ.
Proof.
  unfold has_ref_flag_checker; intros. repeat my_auto3; apply has_kind_checker_correct in H.
  - by eapply MemtypeHasRefFlag; auto.
  - by eapply ValtypeHasRefFlag; auto.
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
                | MEMTYPE (ProdS σs) ξ =>
                    match get_list_of_reps σs with
                    | Some ρs =>
                        if foldr2
                             (λ τ:type, λ ρ:representation,
                                   andb (check_ok_output (has_kind_checker F τ (VALTYPE ρ ξ)))
                             ) true τs ρs
                        then (* now just check that τs' equal to the monstrosity *)
                          if list_beq type type_beq τs2 ((zip_with (fun τ ρ => SerT (MEMTYPE (RepS ρ) ξ) τ)) τs ρs)
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
                | MEMTYPE (ProdS σs) ξ =>
                    match get_list_of_reps σs with
                    | Some ρs =>
                        if foldr2
                             (λ τ:type, λ ρ:representation,
                                   andb (check_ok_output (has_kind_checker F τ (VALTYPE ρ ξ)))
                             ) true τs ρs
                        then (* now just check that τs' equal to the monstrosity *)
                          if list_beq type type_beq τs1 ((zip_with (fun τ ρ => SerT (MEMTYPE (RepS ρ) ξ) τ)) τs ρs)
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

  (* struct ser case *)
  6: {
    simpl in H0. destruct τ2; simpl in H0; repeat my_auto3_5.
    apply get_list_of_reps_matches_map in HMatch1; subst.
    apply TEqSym.
    apply (TEqSerProd _ _ l1 r _).
    (* this then relies on some foldr2 lemmas *)
    admit.
  }
  (* ser struct case *)
  6: {
    Opaque has_kind_checker.
    simpl in H0. destruct t; simpl in H0; repeat my_auto3_5.
    apply get_list_of_reps_matches_map in HMatch1; subst.
    apply (TEqSerProd _ _ l2 r _).
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
      specialize (IHlfull lpre lsuff eq_refl).
      simpl.
      assert (Stupid:t=t) by auto; apply type_eq_convert in Stupid.
      rewrite Stupid. auto.
Qed.

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
                      if kind_beq κ κ0
                      then
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
                      else INR "bad path stuff"
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
    apply split_into_three_correct in HMatch0, HMatch6. destruct HMatch0 as [Hlen Htsfull].
    destruct HMatch6 as [_ Holdpr]. rename k0 into k.
    set (pr := {| pr_prefix := prprefix; pr_target := pr_target pres; pr_replaced := t0 |}).
    assert (Hmaybe : pres =
                       {| pr_prefix := τs0 ++ pr.(pr_prefix);
                          pr_target := pr.(pr_target);
                          pr_replaced := StructT k (τs0 ++ pr.(pr_replaced) :: τs')
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
                      if andb (andb (list_beq type type_beq τs0 τs0') (kind_beq κ κ'))
                              (list_beq type type_beq τs' τs'')
                      then
                        match synth_resolving_with_outer_replaced_sert τ_inner p innerprreplaced τval with
                        | Some (pr, κser) =>
                            let pr' :=
                              {| pr_prefix := τs0 ++ pr.(pr_prefix);
                                pr_target := pr.(pr_target);
                                pr_replaced := StructT κ (τs0 ++ pr.(pr_replaced) :: τs') |} in
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
                      if andb (andb (list_beq type type_beq τs0 τs0') (kind_beq κ κ'))
                              (list_beq type type_beq τs' τs'')
                      then
                        match synth_resolving_with_outer_replaced_spant τ_inner p innerprreplaced τval with
                        | Some (pr, κser, σ) =>
                            let pr' :=
                              {| pr_prefix := τs0 ++ pr.(pr_prefix);
                                pr_target := pr.(pr_target);
                                pr_replaced := StructT κ (τs0 ++ pr.(pr_replaced) :: τs') |} in
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



Definition grab_inner_ft (ft:function_type) : option function_type :=
  match ft with
  | ForallMemT ϕ
  | ForallRepT ϕ
  | ForallSizeT ϕ
  | ForallTypeT _ ϕ => Some ϕ
  | MonoFunT _ _ => None
  end.

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
  | RefT _ m1 τa, RefT _ m2 τb =>
      match memory_find_0 m1 m2 with
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
with traverse_function_type_find_memory ϕ1 ϕ2 : option memory :=
  match ϕ1, ϕ2 with
  | MonoFunT τs11 τs12, MonoFunT τs21 τs22 =>
      match traverse_types_find_memory τs11 τs21 with
      | None => traverse_types_find_memory τs12 τs22
      | Some a => Some a
      end
  | ForallMemT f1, ForallMemT f2
  | ForallRepT f1, ForallRepT f2
  | ForallSizeT f1, ForallSizeT f2
  | ForallTypeT _ f1, ForallTypeT _ f2 => traverse_function_type_find_memory f1 f2
  | _, _ => None
  end.

(* NOTE: if there's a bug, it's in finding the substs stuff *)
Fixpoint traverse_type_find_type_0 τ1 τ2 : option type :=
  match τ1, τ2 with
  | _, VarT n => if (n =? 0) then Some τ1 else None
  | SumT _ τs1, SumT _ τs2
  | VariantT _ τs1, VariantT _ τs2
  | ProdT _ τs1, ProdT _ τs2
  | StructT _ τs1, StructT _ τs2 => traverse_types_find_type τs1 τs2
  | SerT _ τa, SerT _ τb
  | RecT _ τa, RecT _ τb
  | RefT _ _ τa, RefT _ _ τb
  | ExistsMemT _ τa, ExistsMemT _ τb
  | ExistsRepT _ τa, ExistsRepT _ τb
  | ExistsSizeT _ τa, ExistsSizeT _ τb
  | ExistsTypeT _ _ τa, ExistsTypeT _ _ τb => traverse_type_find_type_0 τa τb
  | CodeRefT _ ϕ1, CodeRefT _ ϕ2 => traverse_function_type_find_type ϕ1 ϕ2
  | _, _ => None
  end
with traverse_types_find_type τs1 τs2 : option type :=
  match τs1, τs2 with
  | [], _ => None
  | _, [] => None
  | t1::ts1, t2::ts2 =>
      (* f: type -> type -> option memory -> option memory *)
      foldr2 (λ t1:type, λ t2:type, λ acc:option type,
        match acc with
        | None => traverse_type_find_type_0 t1 t2
        | Some a => Some a
        end
        ) None τs1 τs2
  end
with traverse_function_type_find_type ϕ1 ϕ2 : option type :=
  match ϕ1, ϕ2 with
  | MonoFunT τs11 τs12, MonoFunT τs21 τs22 =>
      match traverse_types_find_type τs11 τs21 with
      | None => traverse_types_find_type τs12 τs22
      | Some a => Some a
      end
  | ForallMemT f1, ForallMemT f2
  | ForallRepT f1, ForallRepT f2
  | ForallSizeT f1, ForallSizeT f2
  | ForallTypeT _ f1, ForallTypeT _ f2 => traverse_function_type_find_type f1 f2
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
  | RefT k1 _ τa, RefT k2 _ τb
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
with traverse_function_type_find_size ϕ1 ϕ2 : option size :=
  match ϕ1, ϕ2 with
  | MonoFunT τs11 τs12, MonoFunT τs21 τs22 =>
      match traverse_types_find_size τs11 τs21 with
      | None => traverse_types_find_size τs12 τs22
      | Some a => Some a
      end
  | ForallMemT f1, ForallMemT f2
  | ForallRepT f1, ForallRepT f2
  | ForallSizeT f1, ForallSizeT f2 =>
      traverse_function_type_find_size f1 f2
  | ForallTypeT k1 f1, ForallTypeT k2 f2 =>
      match kind_find_size_0 k1 k2 with
      | Some a => Some a
      | None => traverse_function_type_find_size f1 f2
      end
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
  | RefT k1 _ τa, RefT k2 _ τb
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
with traverse_function_type_find_rep ϕ1 ϕ2 : option representation :=
  match ϕ1, ϕ2 with
  | MonoFunT τs11 τs12, MonoFunT τs21 τs22 =>
      match traverse_types_find_rep τs11 τs21 with
      | None => traverse_types_find_rep τs12 τs22
      | Some a => Some a
      end
  | ForallMemT f1, ForallMemT f2
  | ForallRepT f1, ForallRepT f2
  | ForallSizeT f1, ForallSizeT f2 =>
      traverse_function_type_find_rep f1 f2
  | ForallTypeT k1 f1, ForallTypeT k2 f2 =>
      match kind_find_rep_0 k1 k2 with
      | Some a => Some a
      | None => traverse_function_type_find_rep f1 f2
      end
  | _, _ => None
  end.

(* TODO man I should do some sort of proof about these find reps but oh well *)

(* Technically.... done? *)
Definition packed_existential_checker (F:function_ctx) (τ0 τ2:type) : type_checker_res :=
  match τ2 with
  | ExistsMemT κ' τ' =>
      match has_kind_checker F τ' κ' with
      | inl () =>
          match traverse_type_find_memory_0 τ0 τ' with
          | Some μ =>
              if type_beq τ0 ((subst_type (unscoped.scons μ VarM) VarR VarS VarT) τ')
              then ok_term
              else INR "something went wrong with packed mem"
          | None => INR "couldn't find μ for packed mem"
          end
      | err => err
      end
  | ExistsRepT κ' τ' =>
      match has_kind_checker F τ' κ' with
      | inl () =>
          match traverse_type_find_rep_0 τ0 τ' with
          | Some ρ =>
              if type_beq τ0 ((subst_type VarM (unscoped.scons ρ VarR) VarS VarT) τ')
              then ok_term
              else INR "something went wrong with packed mem"
          | None => INR "couldn't find μ for packed mem"
          end
      | err => err
      end
  | ExistsSizeT κ' τ' =>
      match has_kind_checker F τ' κ' with
      | inl () =>
          match traverse_type_find_size_0 τ0 τ' with
          | Some σ =>
              if type_beq τ0 ((subst_type VarM VarR (unscoped.scons σ VarS) VarT) τ')
              then ok_term
              else INR "something went wrong with packed mem"
          | None => INR "couldn't find μ for packed mem"
          end
      | err => err
      end
  | ExistsTypeT κ' κ τ' =>
      match has_kind_checker F τ' κ' with
      | inl () =>
          match traverse_type_find_type_0 τ0 τ' with
          | Some τ =>
              if type_beq τ0 ((subst_type VarM VarR VarS (unscoped.scons τ VarT) ) τ')
              then has_kind_checker F τ κ
              else INR "something went wrong with packed mem"
          | None => INR "couldn't find μ for packed mem"
          end
      | err => err
      end
  | _ => INR "trying to check existential type, but not existential"
  end.

Lemma packed_existential_checker_correct :
  ∀ F τ1 τ2, packed_existential_checker F τ1 τ2 = ok_term -> packed_existential F τ1 τ2.
Proof.
  intros.
  destruct τ2; simpl in *; try (by inversion H); try (repeat my_auto4; by constructor).
Qed.


(* This one has the reverse list stuff which I'm unsure how to do exactly *)
Definition unpacked_existential_checker
 (F:function_ctx) (L:local_ctx) (es:list instruction) (ϕ : instruction_type) (L':local_ctx)
 (F0_tocheck:function_ctx) (L_tocheck:local_ctx) (es0:list instruction) (ϕ0: instruction_type) (L'_tocheck:local_ctx)
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
                  let es0_check := map (subst_instruction (up_memory VarM) VarR VarS VarT) es in
                  let up := subst_type (up_memory VarM) VarR VarS VarT in
                  (* HUGE amount of equalities *)
                  if type_beq τ τ_check && local_ctx_beq L_tocheck (map up L) && local_ctx_beq L'_tocheck (map up L')
                     && list_beq type type_beq τs1_check (map up τs1) && list_beq type type_beq τs2_check (map up τs2)
                     && function_ctx_beq F0 F0_tocheck && list_beq instruction instruction_beq es0 es0_check
                  then ok_term
                  else INR "something in unpacked existential didn't match up"
              | ExistsRepT κ τ_check =>
                  let F0 := subst_function_ctx VarM (up_representation VarR) VarS VarT F
                              <| fc_kind_ctx ::= set kc_rep_vars S |> in
                  let es0_check := map (subst_instruction VarM (up_representation VarR) VarS VarT) es in
                  let up := subst_type VarM (up_representation VarR) VarS VarT in
                  (* HUGE amount of equalities *)
                  if type_beq τ τ_check && local_ctx_beq L_tocheck (map up L) && local_ctx_beq L'_tocheck (map up L')
                     && list_beq type type_beq τs1_check (map up τs1) && list_beq type type_beq τs2_check (map up τs2)
                     && function_ctx_beq F0 F0_tocheck && list_beq instruction instruction_beq es0 es0_check
                  then ok_term
                  else INR "something in unpacked existential didn't match up"
              | ExistsSizeT κ τ_check =>
                  let F0 := subst_function_ctx VarM VarR (up_size VarS) VarT F
                              <| fc_kind_ctx ::= set kc_size_vars S |> in
                  let es0_check := map (subst_instruction VarM VarR (up_size VarS) VarT) es in
                  let up := subst_type VarM VarR (up_size VarS) VarT in
                  (* HUGE amount of equalities *)
                  if type_beq τ τ_check && local_ctx_beq L_tocheck (map up L) && local_ctx_beq L'_tocheck (map up L')
                     && list_beq type type_beq τs1_check (map up τs1) && list_beq type type_beq τs2_check (map up τs2)
                     && function_ctx_beq F0 F0_tocheck && list_beq instruction instruction_beq es0 es0_check
                  then ok_term
                  else INR "something in unpacked existential didn't match up"
              | ExistsTypeT κ κ0 τ_check =>
                  let F0 := subst_function_ctx VarM VarR VarS (up_type VarT) F <| fc_type_vars ::= cons κ0 |> in
                  let es0_check := map (subst_instruction VarM VarR VarS (up_type VarT)) es in
                  let up := subst_type VarM VarR VarS (up_type VarT) in
                  (* HUGE amount of equalities *)
                  if type_beq τ τ_check && local_ctx_beq L_tocheck (map up L) && local_ctx_beq L'_tocheck (map up L')
                     && list_beq type type_beq τs1_check (map up τs1) && list_beq type type_beq τs2_check (map up τs2)
                     && function_ctx_beq F0 F0_tocheck && list_beq instruction instruction_beq es0 es0_check
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
  ∀ F L es ϕ L' F0 L_tocheck es0 ϕ0 L'_tocheck,
    unpacked_existential_checker F L es ϕ L' F0 L_tocheck es0 ϕ0 L'_tocheck = ok_term ->
    unpacked_existential F L es ϕ L' F0 L_tocheck es0 ϕ0 L'_tocheck.
Proof.
  Opaque split_list_all_last.
  intros. unfold unpacked_existential_checker in H.
  repeat my_auto4.
  - apply UnpackMem.
  - apply UnpackRep.
  - apply UnpackSize.
  - apply UnpackType.
Qed.

Definition unpacked_existential_getter F L es ϕ L' :
  option (function_ctx * local_ctx * (list instruction) * instruction_type * local_ctx) :=
  match ϕ with
  | InstrT τs1_full τs2 =>
      match split_list_all_last τs1_full with
      | Some (τs1, τex) =>
          (* now we have to split on the τex *)
          match τex with
          | ExistsMemT κ τ =>
              let F0 := subst_function_ctx (up_memory VarM) VarR VarS VarT F
                          <| fc_kind_ctx ::= set kc_mem_vars S |> in
              let es0 := map (subst_instruction (up_memory VarM) VarR VarS VarT) es in
              let up := subst_type (up_memory VarM) VarR VarS VarT in
              let L0 := (map up L) in
              let L'0 := (map up L') in
              let ϕ0 := InstrT (map up τs1 ++ [τ]) (map up τs2) in
              Some (F0, L0, es0, ϕ0, L'0)
          | ExistsRepT κ τ =>
              let F0 := subst_function_ctx VarM (up_representation VarR) VarS VarT F
                          <| fc_kind_ctx ::= set kc_rep_vars S |> in
              let es0 := map (subst_instruction VarM (up_representation VarR) VarS VarT) es in
              let up := subst_type VarM (up_representation VarR) VarS VarT in
              let L0 := (map up L) in
              let L'0 := (map up L') in
              let ϕ0 := InstrT (map up τs1 ++ [τ]) (map up τs2) in
              Some (F0, L0, es0, ϕ0, L'0)
          | ExistsSizeT κ τ =>
              let F0 := subst_function_ctx VarM VarR (up_size VarS) VarT F
                          <| fc_kind_ctx ::= set kc_size_vars S |> in
              let es0 := map (subst_instruction VarM VarR (up_size VarS) VarT) es in
              let up := subst_type VarM VarR (up_size VarS) VarT in
              let L0 := (map up L) in
              let L'0 := (map up L') in
              let ϕ0 := InstrT (map up τs1 ++ [τ]) (map up τs2) in
              Some (F0, L0, es0, ϕ0, L'0)
          | ExistsTypeT κ κ0 τ =>
              let F0 := subst_function_ctx VarM VarR VarS (up_type VarT) F <| fc_type_vars ::= cons κ0 |> in
              let es0 := map (subst_instruction VarM VarR VarS (up_type VarT)) es in
              let up := subst_type VarM VarR VarS (up_type VarT) in
              let L0 := (map up L) in
              let L'0 := (map up L') in
              let ϕ0 := InstrT (map up τs1 ++ [τ]) (map up τs2) in
              Some (F0, L0, es0, ϕ0, L'0)
          | _ => None
          end
      | None => None
      end
  end.

Lemma unpacked_existential_getter_correct :
  ∀ F L es ϕ L' F0 L0 es0 ϕ0 L'0,
    unpacked_existential_getter F L es ϕ L' = Some (F0, L0, es0, ϕ0, L'0) ->
    unpacked_existential F L es ϕ L' F0 L0 es0 ϕ0 L'0.
Proof.
  intros. unfold unpacked_existential_getter in H.
  repeat my_auto4; subst.
  - apply UnpackMem.
  - apply UnpackRep.
  - apply UnpackSize.
  - apply UnpackType.
Qed.


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
  | ILocalGet ψ i =>
      match ψ with
      | InstrT [] [τ] =>
          match has_ref_flag_checker F τ NoRefs with
          | inl () => inl (Some L)
          | _ =>
              match F.(fc_locals) !! i with
              | Some ηs => inl (Some (<[ i := type_plug_prim ηs ]> L))
              | _ => inr "NO"%string
              end
          end
      | _ => inr "NO"%string
      end
  | ILocalSet ψ i =>
      match ψ with
      | InstrT [τ] [] => inl (Some (<[ i := τ ]> L))
      | _ => inr "NO"%string
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



Definition test ψ :=
  match ψ with
  | InstrT [a] b::b' => ok_term
  | _ => INR "no"
  end.
Print type_span.

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
  ∀ τs' κs τs, unzip_sert τs' = Some (κs, τs) -> τs' = zip_with SerT κs τs.
Proof.
  induction τs'.
  - simpl. intros; inversion H. auto.
  - intros. simpl in H. destruct a; try (by inversion H).
    structural_auto. destruct p. clear H1.
    inversion H. subst.
    specialize (IHτs' l l0 eq_refl). subst.
    auto.
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
                      else INR "can't frame out (can't frame non mono rep)"
                    else INR "can't frame out (single instruction)"
                | _, _ => INR "inner instruction type doesn't match"
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
  | ILocalGet ψ_inner i => (* note this is for both TLocalGetMove and TLocalGetCopy *)
      if andb (instruction_type_beq ψ ψ_inner) (true)
      then
        match L !! i with
        | Some τ =>
            match ψ with
            | InstrT [] [τ'] =>
                if type_beq τ τ'
                then
                  match has_ref_flag_checker F τ NoRefs with (* decision point *)
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
                if type_beq τ (CodeRefT (VALTYPE (AtomR I32R) NoRefs) (MonoFunT τs1 τs2))
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
            | RefT κr μ (VariantT κv τs') =>
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
                if foldr2
                     (λ t:type, λ es,
                           andb (check_ok_output
                                   (have_instruction_type_checker M F' L es (InstrT [t] τs') L'))
                     ) true τs ess
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
                | RefT κr μ (VariantT κv τs_ser) =>
                    match τ2 with
                    | RefT κr0 μ0 (VariantT κv0 τs'0) =>
                        (* a bunch of variables have to be equal *)
                        if andb (kind_beq κr κr0) (andb (kind_beq κv κv0)
                                  (andb (memory_beq μ μ0) (list_beq type type_beq τs' τs'0)))
                        then
                          match unzip_sert τs_ser with
                          | Some (κs, τs) =>
                              let F' := F <| fc_labels ::= cons (τs', L') |> in
                              if foldr (λ t:type, andb (check_ok_output (has_ref_flag_checker F t GCRefs))) true τs
                              then
                                if foldr2
                                     (λ t:type, λ es,
                                         andb (check_ok_output
                                                 (have_instruction_type_checker M F' L es (InstrT [t] τs') L'))
                                     ) true τs ess
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
                | RefT κr (BaseM MemMM) (VariantT κv τs_ser) =>
                    match unzip_sert τs_ser with
                    | Some (κs, τs) =>
                        let F' := F <| fc_labels ::= cons (τs', L') |> in
                        if foldr2
                             (λ t:type, λ es,
                                 andb (check_ok_output
                                         (have_instruction_type_checker M F' L es (InstrT [t] τs') L'))
                             ) true τs ess
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
            match unpacked_existential_getter F' L es ψ L' with
            | Some (F0', L0, es0, ψ0, L0') =>
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
      if andb (instruction_type_beq ψ ψ_inner) (local_ctx_beq L L')
      then
        match cm with (* DECISION POINT *)
        | Copy => (* load copy *)
            match ψ with
            | InstrT [τ1] [τ2;τval] =>
                if type_beq τ1 τ2
                then
                  match τ1 with
                  | RefT κ μ τ =>
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
                | RefT κ (BaseM MemMM) τ =>
                    match τ2 with
                    | RefT κ' (BaseM MemMM) prreplaced =>
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
              | RefT κ μ τ =>
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
              | RefT κ (BaseM MemMM) τ =>
                  match reft2 with
                  | RefT κ' (BaseM MemMM) prreplaced =>
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
                  | RefT κ μ τ =>
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


(* TODO at the end make sure this is a direct copy of above. TODO NOTE IT IS NOT RIGHT NOW REMEMBER *)
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
              then local_ctx_ok_checker F L
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
                    then ok_term
                    else INR "can't frame out (single instruction)"
                | _, _ => INR "inner instruction type doesn't match"
                end
            end
        | err => err
        end
    | e :: es =>
        let e_ψ := proj_instr_ty e in
        match synth_possible_resulting_local_ctx F e L with
        | inr _ => INR "this is either local get/set that is bad, so error?"
        | inl None => INR "the instr we're processing is either uncklereachable, break, or return, with more commands to follow. unsure how to deal with rn TODO"
        | inl (Some L_e) =>
            match has_instruction_type_checker M F L e e_ψ L_e with
            | inl () =>
                match e_ψ, ψ with
                | InstrT τs1_e τs2_e, InstrT τs1_es τs2_es =>
                    match list_suffix τs1_es τs1_e with (* τs1_es = τs_pref ++ τs1_e *)
                    | Some τs_pref => have_instruction_type_checker M F L_e es (InstrT (τs_pref ++ τs2_e) τs2_es) L'
                    | None => INR "instruction has more arguments than large have_instruction type has, or can't frame out"
                    end
                end
            | err => err
            end
        end
    end.


Locate subst_type.
(*** Demonstration of the annoyance of rocq fixpoint checker ***)

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

Fixpoint test5 ns :=
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
    (HLocalGet: ∀ ψ n, P1 (ILocalGet ψ n))
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
      | ILocalGet ψ n => HLocalGet ψ n
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
  | H: (check_if_subkind _ _ = inl ()) |- _ =>
      try( by (eapply check_if_subkind_works_with_has_kind; try constructor; auto))
  | H: (check_if_subkind _ _ = ok_term) |- _ =>
      try( by (eapply check_if_subkind_works_with_has_kind; try constructor; auto))
  | H: (check_ok_output _ = true) |- _ => apply check_ok_output_true_to_prop in H
  | H: (list_suffix ?x _ = Some _) |- _ => apply list_suffix_correct_r in H; subst x
  | H: (split_into_three ?τ _ = Some (_, _, _)) |- _ => apply split_into_three_correct in H; destruct H as [H1 H2]; subst τ
  | H: (split_list_all_last ?l = Some (_, _)) |- _ => apply split_list_all_last_correct in H; subst l
  | H: (unzip_sert ?l = Some (_, _)) |- _ => apply unzip_sert_correct in H; subst l
  | H: (mono_mem_checker _ = ok_term) |- _ => apply mono_mem_checker_correct in H; auto
  | H: (mono_mem_checker _ = inl ()) |- _ => apply mono_mem_checker_correct in H; auto
  | H: (type_eq_checker _ _ _ = inl ()) |- _ => apply type_eq_checker_correct in H; auto
  | H: (type_eq_checker _ _ _ = ok_term) |- _ => apply type_eq_checker_correct in H; auto
  | H: (has_mono_size_checker _ _ = ok_term) |- _ => apply has_mono_size_checker_correct in H; auto
  | H: (has_mono_size_checker _ _ = inl ()) |- _ => apply has_mono_size_checker_correct in H; auto
  | H: (has_mono_rep_checker _ _ = ok_term) |- _ => apply has_mono_rep_checker_correct in H; auto
  | H: (has_mono_rep_checker _ _ = inl ()) |- _ => apply has_mono_rep_checker_correct in H; auto
  | H: (local_ctx_ok_checker _ _ = ok_term) |- _ => apply local_ctx_ok_checker_correct in H; auto
  | H: (local_ctx_ok_checker _ _ = inl ()) |- _ => apply local_ctx_ok_checker_correct in H; auto
  | H: (has_size_checker _ _ _ = inl ()) |- _ => apply has_size_checker_correct in H; auto
  | H: (has_size_checker _ _ _ = ok_term) |- _ => apply has_size_checker_correct in H; auto
  | H: (grab_size _ _ = Some _) |- _ => apply grab_size_correct in H; auto
  | H: (grab_rep _ _ = Some _) |- _ => apply grab_rep_correct in H; auto
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
                      else INR "can't frame out (can't frame non mono rep)"
                    else INR "can't frame out (single instruction)"
                | _, _ => INR "inner instruction type doesn't match"
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
  Ltac clear_nils :=
    repeat rewrite <- ?app_assoc, -> ?app_nil_l, -> ?app_nil_r in *.

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
    (* this needs a foldr2+Forall2 lemma, but it should just work *)
    admit.
  }
  [CaseLoad]: {
    half_shred.
    - (* case load copy *)
      convert_foldr
        (λ t:type, check_ok_output (has_ref_flag_checker F t GCRefs))
        (fun t => has_ref_flag F t GCRefs) l5 HMatch8.
      (* foldr2+Forall2 lemma, then should be good *)
      admit.
    - (* case load move *)
      subst.
      (* similar foldr2+Forall2 lemma. Slight concert: rocq "simplified" hitc a bit. Hopefully no issue *)
      admit.
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
      rewrite <- HMatch in HMatch7.
      by eapply TStoreWeak.
    - (* store strong case *)
      convert_foldr
        (λ t:type, check_ok_output (has_mono_size_checker F t))
        (fun t => has_mono_size F t) (pr_prefix p0) H3.
      apply Nat.eqb_eq in H2; subst.
      rewrite <- HMatch1 in HMatch2.
      by eapply TStoreStrong.
  }
  [Swap]: {
    half_shred.
    convert_foldr
      (λ t:type, check_ok_output (has_mono_size_checker F t))
      (fun t => has_mono_size F t) (pr_prefix p) HMatch6.
    by econstructor.
  }


  (* Existentials are INCOMPLETE *)
  [Pack]: admit.
  [Unpack]: admit.






Admitted.


Lemma have_instruction_type_checker_correct :
  ∀ M F L insts ψ L',
    have_instruction_type_checker M F L insts ψ L' = ok_term ->
    have_instruction_type M F L insts ψ L'.
Proof. Admitted.

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

Definition has_function_type_checker
    (M:module_ctx) (mf:module_function) (ft:function_type) : type_checker_res :=
  if function_type_beq mf.(mf_type) ft
  then
    let ϕ := flatten_function_type mf.(mf_type) in
    let K := kc_of_fft ϕ in
    match mapM (eval_rep_prim EmptyEnv) mf.(mf_locals) with
    | Some ηss =>
        let F := Build_function_ctx ϕ.(fft_out) ηss [] K ϕ.(fft_type_vars) in
        let L := map type_plug_prim ηss in
        let ψ := InstrT ϕ.(fft_in) ϕ.(fft_out) in
        match synth_possible_resulting_local_ctx_insts F (mf.(mf_body)) L with
        | inl (Some L') =>
            if (foldr (λ t:type, andb (check_ok_output (has_ref_flag_checker F t NoRefs))) true L')
            then have_instruction_type_checker M F L mf.(mf_body) ψ L'
            else INR "bad"
        | inl None => INR "don't know how to deal with breaks and stuff yet for synthing local ctx"
        | inr a => INR "error in synthing local ctx (e.g. bad local get/set)"
        end
    | None => INR "can't give function type"
    end
  else INR "bad".
Lemma has_function_type_checker_correct :
  ∀ M mf ft, has_function_type_checker M mf ft = ok_term ->
             has_function_type M mf ft.
Proof.
  intros.
  Opaque have_instruction_type_checker.
  unfold has_function_type_checker in H.
  repeat my_auto5.
  rename l into ηss. rename l0 into L'. boolean_equality_auto.
  apply (TFunction M mf ηss L'); auto.
  - admit. (* just a foldr lemma *)
  - by apply have_instruction_type_checker_correct in H1.
Admitted.



Definition has_module_type_checker (m:module) (mt:module_type) : type_checker_res :=
  let ϕs := m.(m_imports) ++ map mf_type m.(m_functions) in
  match nths_error ϕs m.(m_table) with
  | Some table =>
      match nths_error ϕs (map me_desc m.(m_exports)) with
      | Some exports =>
          if module_type_beq mt (Build_module_type m.(m_imports) exports)
          then
            let M := Build_module_ctx ϕs table in
            if (foldr (λ mf, andb (check_ok_output (has_function_type_checker M mf mf.(mf_type))))
                      true m.(m_functions))
            then ok_term
            else INR "function types don't equal"
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
  (* and this is just a foldr lemma *)

Admitted.

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
