Set Universe Polymorphism.
From Coq Require Import Numbers.BinNums ZArith List FSets.FMapPositive.
From stdpp Require Import list.

From RichWasm.util Require Import tactics list debruijn ensemble map.
From RichWasm Require Import subst term.

Module M := PositiveMap.

(* Conversion from [Size] to [nat] *)

Fixpoint size_closed (s : Size) : Prop :=
  match s with
  | SizeVar _ => False
  | SizePlus s1 s2 => size_closed s1 /\ size_closed s2
  | SizeConst i => True
  end.

Definition sizes_closed (ss : list Size) : Prop :=
  List.Forall size_closed ss.

Definition to_size (s : Size) (H : size_closed s) : nat.
  induction s.
  - inversion H.
  - inversion H. exact (IHs1 H0 + IHs2 H1).
  - exact c.
Defined.


Definition to_sizes (ss : list Size) (H : sizes_closed ss) : list nat.
  induction ss.
  + exact [].
  + assert (Hs : size_closed a).
    { inversion H. eassumption. } 
    assert (Hss : sizes_closed ss).
    { inversion H. eassumption. } 
    exact (to_size a Hs :: (IHss Hss)).
Defined.

Section TypeSize.

  Fixpoint size_to_nat (s : Size) : option nat :=
    match s with
    | SizeVar _ => None
    | SizePlus s1 s2 =>
      match size_to_nat s1 with
      | Some n1 =>
        match size_to_nat s2 with
        | Some n2 => Some (n1 + n2)
        | None => None
        end
      | None => None
      end
    | SizeConst i => Some i
    end.


  Definition fold_size (s : list (option Size)) : option Size :=
    fold_right
      (fun (o1 o2 : option Size) =>
         s1 ← o1; s2 ← o2; mret (SizePlus s1 s2)) (mret (SizeConst 0)) s.

  Fixpoint sizeOfType (T : list (Size * Qual * HeapableConstant)) (ty : Typ) : option Size :=
    match ty with
    | Num nt =>
      match nt with
      | Int _ i32 | Float f32 => Some (SizeConst 1)
      | Int _ i64 | Float f64 => Some (SizeConst 2)
      end
    | TVar a => 
        '(sz, _, _) ← T !! a;
        mret sz
    | OwnR _
    | CapT _ _ _
    | Unit => Some (SizeConst 1)
    | ProdT ts => fold_size (map (sizeOfType T) ts)
    | CoderefT _ => Some (SizeConst 2)
    | PtrT _ 
    | RefT _ _ _ => Some (SizeConst 1)
    | Rec q t =>
      let bogus := SizeConst 0 in
      sizeOfType ((bogus, q, Heapable) :: T) t
      (*
      if rec_var_under_ref_typ t 0
      then let bogus := SizeConst 0 in sizeOfType ((bogus, q) :: T) t
      else None
       *)
    | ExLoc _ t => sizeOfType T t
    end.

  Fixpoint model_satisfies_context_from_idx 
           {A B}
           (leq : B -> B -> Prop)
           (lift_model : (nat -> B) -> (A -> B))
           (model : nat -> B)
           (ctx : list (list A * list A))
           (idx : nat) :=
    match ctx with
    | [] => True
    | (lst1, lst2) :: ctx' =>
      Forall
        (fun obj =>
           leq (lift_model model obj) (model idx))
        lst1 /\
      Forall
        (fun obj =>
           leq (model idx) (lift_model model obj))
        lst2 /\
      model_satisfies_context_from_idx
        leq
        lift_model
        model
        ctx'
        (Datatypes.S idx)
    end.

  Definition model_satisfies_context
             {A B}
             (leq : B -> B -> Prop)
             (lift_model : (nat -> B) -> (A -> B))
             (model : nat -> B)
             (ctx : list (list A * list A)) :=
    model_satisfies_context_from_idx leq lift_model model ctx 0.

  Inductive list_sub {T}: list T -> list T -> Prop :=
      | L_nil: forall L, list_sub [] L
      | L_cons: forall x L L',
          list_sub L L' ->
          list_sub (x::L) (x::L').

  Lemma list_sub_model_gen : forall {A B leq lift_model model ctx ctx' idx},
      @model_satisfies_context_from_idx A B leq lift_model model ctx' idx ->
      list_sub ctx ctx' ->
      model_satisfies_context_from_idx leq lift_model model ctx idx.
  Proof.
    induction ctx; [ constructor | ].
    intros.
    destruct_prs.
    match goal with
    | [ H : list_sub _ _ |- _ ] => inversion H; subst
    end.
    simpl in *.
    destructAll.
    do 2 ltac:(split; auto).
    eauto.
  Qed.

  Lemma list_sub_model : forall {A B leq lift_model model ctx ctx'},
      @model_satisfies_context A B leq lift_model model ctx' ->
      list_sub ctx ctx' ->
      model_satisfies_context leq lift_model model ctx.
  Proof.
    unfold model_satisfies_context.
    intros.
    eapply list_sub_model_gen; eauto.
  Qed.

  Definition ctx_imp_leq
             {A B}
             (leq : B -> B -> Prop)
             (lift_model : (nat -> B) -> (A -> B))
             (ctx : list (list A * list A))
             (obj1 : A)
             (obj2 : A) :=
    forall (model : nat -> B),
      model_satisfies_context leq lift_model model ctx ->
      leq (lift_model model obj1) (lift_model model obj2).

  Lemma list_sub_ctx_imp_leq : forall {A B leq lift_model ctx ctx' obj1 obj2},
      @ctx_imp_leq A B leq lift_model ctx obj1 obj2 ->
      list_sub ctx ctx' ->
      @ctx_imp_leq A B leq lift_model ctx' obj1 obj2.
  Proof.
    unfold ctx_imp_leq.
    intros.
    eapply H.
    eapply list_sub_model; eauto.
  Qed.
  
  Lemma ctx_imp_leq_refl : forall {A B} {leq : B -> B -> Prop} {lift_model ctx obj},
      (forall obj', leq obj' obj') ->
      @ctx_imp_leq A B leq lift_model ctx obj obj.
  Proof.
    unfold ctx_imp_leq.
    intros.
    eauto.
  Qed.

  Lemma ctx_imp_leq_trans : forall {A B} {leq : B -> B -> Prop} {lift_model ctx obj1 obj2 obj3},
      (forall obj1' obj2' obj3',
          leq obj1' obj2' ->
          leq obj2' obj3' ->
          leq obj1' obj3') ->
      @ctx_imp_leq A B leq lift_model ctx obj1 obj2 ->
      @ctx_imp_leq A B leq lift_model ctx obj2 obj3 ->
      @ctx_imp_leq A B leq lift_model ctx obj1 obj3.
  Proof.
    unfold ctx_imp_leq.
    intros.
    repeat match goal with
           | [ H : forall _, _ -> _,
               H' : model_satisfies_context _ _ _ _ |- _ ] =>
             specialize (H _ H')
           end.
    eauto.
  Qed.

  (* A solver is needed for that *)
  Axiom SizeLeq : list (list Size * list Size) -> Size -> Size -> option bool.

  Fixpoint interp_size (model : nat -> nat) (sz : Size) :=
    match sz with
    | SizeVar v => model v
    | SizeConst c => c
    | SizePlus sz1 sz2 =>
      (interp_size model sz1) + (interp_size model sz2)
    end.

  Axiom SizeLeq_desc : forall C q1 q2,
      SizeLeq C q1 q2 = Some true <->
      ctx_imp_leq Peano.le interp_size C q1 q2.
  
  Theorem SizeLeq_Refl : forall C s, SizeLeq C s s = Some true.
  Proof.
    intros.
    rewrite SizeLeq_desc.
    eapply ctx_imp_leq_refl; eauto.
  Qed.

  Theorem SizeLeq_Trans :
    forall C q1 q2 q3,
      SizeLeq C q1 q2 = Some true ->
      SizeLeq C q2 q3 = Some true ->
      SizeLeq C q1 q3 = Some true.
  Proof.
    do 4 intro.
    repeat rewrite SizeLeq_desc.
    eapply ctx_imp_leq_trans; eauto.
    exact Nat.le_trans.
  Qed.

  Lemma size_to_nat_interp_size : forall {sz c model},
      size_to_nat sz = Some c ->
      interp_size model sz = c.
  Proof.
    induction sz; intros; simpl in *.
    - inversion H.
    - destruct (size_to_nat sz1); destruct (size_to_nat sz2).
      all:
        match goal with
        | [ H : _ = Some _ |- _ ] => inversion H; subst
        end.
      eauto.
    - inversion H; subst; auto.
  Qed.

  Theorem SizeLeq_Const : forall sz1 sz2 c1 c2,
      size_to_nat sz1 = Some c1 ->
      size_to_nat sz2 = Some c2 ->
      SizeLeq [] sz1 sz2 = Some true ->
      c1 <= c2.
  Proof.
    do 4 intro.
    rewrite SizeLeq_desc.
    intros.
    unfold ctx_imp_leq in *.
    match goal with
    | [ H : forall _, _ -> _ |- _ ] =>
      specialize (H (fun _ => 0))
    end.
    match goal with
    | [ H : ?A -> _ |- _ ] =>
      let H' := fresh "H" in
      assert (H' : A); [ | specialize (H H') ]
    end.
    { constructor. }
    match goal with
    | [ H : ?A <= _ |- ?B <= _ ] =>
      let H' := fresh "H" in
      assert (H' : A = B)
    end.
    { apply size_to_nat_interp_size; auto. }
    match goal with
    | [ H : _ <= ?A |- _ <= ?B ] =>
      let H' := fresh "H" in
      assert (H' : A = B)
    end.
    { apply size_to_nat_interp_size; auto. }
    subst; auto.
  Qed.

  Lemma size_to_nat_None_unbounded : forall {sz bound},
      size_to_nat sz = None ->
      exists model,
        interp_size model sz >= bound.
  Proof.
    induction sz.
    - intros.
      exists (fun _ => bound).
      simpl; auto.
    - intros.
      simpl in *.
      remember (size_to_nat sz1) as obj.
      generalize (eq_sym Heqobj).
      destruct obj.
      -- intros.
         remember (size_to_nat sz2) as obj2.
         generalize (eq_sym Heqobj2).
         destruct obj2.
         --- inversion H.
         --- intros.
             specialize (IHsz2 bound eq_refl).
             destructAll.
             match goal with
             | [ H : interp_size ?A _ >= _ |- _ ] =>
               exists A
             end.
             unfold Peano.ge.
             eapply Nat.le_trans; [ | apply Nat.le_add_l ].
             auto.
      -- intros.
         specialize (IHsz1 bound eq_refl).
         destructAll.
         match goal with
         | [ H : interp_size ?A _ >= _ |- _ ] =>
           exists A
         end.
         unfold Peano.ge.
         eapply Nat.le_trans; [ | apply Nat.le_add_r ].
         auto.
    - intros; simpl in *.
      inversion H.
  Qed.

  Theorem SizeLeq_right_closed_imp_left_closed : forall sz1 sz2 c2,
      size_to_nat sz2 = Some c2 ->
      SizeLeq [] sz1 sz2 = Some true ->
      exists c1,
        size_to_nat sz1 = Some c1.
  Proof.
    do 3 intro.
    rewrite SizeLeq_desc.
    unfold ctx_imp_leq.
    intros.
    remember (size_to_nat sz1) as obj.
    generalize (eq_sym Heqobj); destruct obj; eauto.
    let H' := fresh "H" in
    intro H'; apply (size_to_nat_None_unbounded (bound:=Datatypes.S c2)) in H'.
    destructAll.
    match goal with
    | [ H : interp_size ?F _ >= _, H' : forall _, _ -> _ |- _ ] =>
      specialize (H' F)
    end.
    match goal with
    | [ H : ?A -> _ |- _ ] =>
      let H' := fresh "H" in
      assert (H' : A); [ | specialize (H H') ]
    end.
    { constructor. }
    match goal with
    | [ H : size_to_nat ?SZ = Some _,
        H' : _ <= interp_size _ ?SZ |- _ ] =>
      erewrite (size_to_nat_interp_size (sz:=SZ)) in H'; eauto
    end.
    unfold Peano.ge in *.
    match goal with
    | [ H : _ <= ?A, H' : ?A <= _ |- _ ] =>
      specialize (Nat.le_trans _ _ _ H H')
    end.
    intros.
    exfalso; eapply Nat.nle_succ_diag_l; eauto.
  Qed.

  Theorem SizeLeq_Bottom : forall C s, SizeLeq C (SizeConst 0) s = Some true.
  Proof.
    intros.
    rewrite SizeLeq_desc.
    unfold ctx_imp_leq.
    intros.
    simpl.
    apply Peano.le_0_n.
  Qed.

  Theorem SizeLeq_leq :
    forall s1 s2 n1 n2 s,
      size_to_nat s1 = Some n1 ->
      size_to_nat s2 = Some n2 ->
      n1 <= n2 ->
      SizeLeq s s1 s2 = Some true.
  Proof.
    intros.
    rewrite SizeLeq_desc.
    unfold ctx_imp_leq.
    intros.
    erewrite size_to_nat_interp_size; [ | eauto ].
    erewrite size_to_nat_interp_size; [ | eauto ].
    auto.
  Qed.

  Theorem SizeLeq_Bigger_Ctx : forall C C' s1 s2,
      SizeLeq C s1 s2 = Some true ->
      list_sub C C' ->
      SizeLeq C' s1 s2 = Some true.
  Proof.
    do 4 intro.
    repeat rewrite SizeLeq_desc.
    apply list_sub_ctx_imp_leq.
  Qed.

End TypeSize.


Record Module_Ctx :=
  { func   : list FunType;
    global : list GlobalType;
    table  : list FunType;
  }.

Definition Local_Ctx := list (Typ * Size).

Record Function_Ctx :=
  { label  : list (list Typ * Local_Ctx);
    rettyp : option (list Typ);
    (* Type variables and their constraints *)
    qual   : list (list Qual * list Qual);
    size   : list (list Size * list Size);
    type   : list (Size * Qual * HeapableConstant);
    location : list Qual;
    linear : plist Qual;
  }.

Definition typ_var_qual (C: Function_Ctx) (α: term.var) :=
  '(_, q, _) ← C.(type) !! α;
  mret q.

Definition loc_var_qual (C: Function_Ctx) (ρ: term.var) :=
  C.(location) !! ρ.

Definition heapable (f : Function_Ctx) :=
  map (fun '(_, _, hc) => hc) (type f).

(* Shifting in environments *)

Definition subst'_local_ctx (su : Subst' Kind) : Local_Ctx -> Local_Ctx :=
  map (fun '(t, s) => (subst'_typ su t, subst'_size su s)).

(* TODO for some reason map_prod_subst'ok doesn't get applied automatically
   despite being in OKDB *)
Lemma subst'_local_ctx_ok : subst'_ok subst'_local_ctx.
Proof. unfold subst'_local_ctx; apply map_prod_subst'_ok; pose_ok_proofs; auto. Qed.
Global Hint Resolve subst'_local_ctx_ok : OKDB.
Tactic Notation "pose_ok_proofs'" := pose_ok_proofs'; pose proof subst'_local_ctx_ok.
Ltac pose_ok_proofs ::= pose_ok_proofs'.

Instance BindExtLocalCtx : BindExt Kind Local_Ctx := ltac:(mkBindExt).

Definition subst'_function_ctx (su : Subst' Kind) (ctx : Function_Ctx) : Function_Ctx :=
  {| label :=
       map (fun '(ts, lctx) => (subst'_typs su ts, subst'_local_ctx su lctx)) (label ctx);
     rettyp := option_map (subst'_typs su) (rettyp ctx);
     qual := map (fun '(qs1, qs2) => (subst'_quals su qs1, subst'_quals su qs2)) (qual ctx);
     size := map (fun '(ss1, ss2) => (subst'_sizes su ss1, subst'_sizes su ss2)) (size ctx);
     type := map (fun '(s, q, hc) => (subst'_size su s, subst'_qual su q, hc)) (type ctx);
     location := location ctx;
     linear := pmap (subst'_qual su) (linear ctx) |}.


Lemma function_ctx_eq : forall {F F'},
    label F = label F' ->
    rettyp F = rettyp F' ->
    qual F = qual F' ->
    size F = size F' ->
    type F = type F' ->
    location F = location F' ->
    linear F = linear F' ->
    F = F'.
Proof.
  intros.
  destruct F; destruct F'; subst; simpl in *.
  repeat match goal with
         | [ H : _ = _ |- _ ] => rewrite H; clear H
         end.
  auto.
Qed.

Lemma subst'_label_function_ctx_ok :
  subst'_ok
    (fun su =>
       (map
          (fun '(ts, lctx) =>
             (subst'_typs su ts, subst'_local_ctx su lctx)))).
Proof.
  apply map_prod_subst'_ok.
  - apply subst'_typs_ok.
  - apply subst'_local_ctx_ok.
Qed.

Lemma subst'_ret_function_ctx_ok :
  subst'_ok
    (fun su =>
       (option_map (subst'_typs su))).
Proof.
  apply option_map_subst'_ok.
  apply subst'_typs_ok.
Qed.

Lemma subst'_qual_function_ctx_ok :
  subst'_ok
    (fun su =>
       (map
          (fun '(qs0, qs1) =>
             (subst'_quals su qs0, subst'_quals su qs1)))).
Proof.
  apply map_prod_subst'_ok; apply subst'_quals_ok.
Qed.

Lemma subst'_size_function_ctx_ok :
  subst'_ok
    (fun su =>
       (map
          (fun '(szs0, szs1) =>
             (subst'_sizes su szs0, subst'_sizes su szs1)))).
Proof.
  apply map_prod_subst'_ok; apply subst'_sizes_ok.
Qed.

Lemma subst'_type_function_ctx_ok :
  subst'_ok
    (fun su =>
       (@map
          (Size * Qual * HeapableConstant)
          _
          (fun '(s, q, hc) =>
             (subst'_size su s, subst'_qual su q, hc)))).
Proof.
  apply map_prod_subst'_ok_hc.
  - apply subst'_size_ok.
  - apply subst'_qual_ok.
Qed.

Lemma subst'_linear_function_ctx_ok :
  subst'_ok (fun su => (pmap (subst'_qual su))).
Proof.
  apply pmap_subst'_ok.
  apply subst'_qual_ok.
Qed.

Lemma subst'_function_ctx_ok : subst'_ok subst'_function_ctx.
Proof.
  Ltac use_eq1 lem :=
    specialize lem;
    unfold subst'_ok;
    unfold subst'_ok_at;
    intros;
    match goal with
    | [ H : forall _, _ /\ _ |- _ = ?X ] =>
      specialize (H X); destruct H as [H]; rewrite H; auto
    end.
  Ltac use_eq2 lem :=
    specialize lem;
    unfold subst'_ok;
    unfold subst'_ok_at;
    intros;
    match goal with
    | [ H : forall _, _ /\ _ |- _ = _ _ ?X ] =>
      specialize (H X); destruct H as [_ H]; rewrite H; auto
    end.
  
  unfold subst'_ok.
  intros.
  unfold subst'_ok_at.
  split.
  - unfold subst'_function_ctx.
    apply function_ctx_eq; simpl in *; auto.
    -- use_eq1 subst'_label_function_ctx_ok.
    -- use_eq1 subst'_ret_function_ctx_ok.
    -- use_eq1 subst'_qual_function_ctx_ok.
    -- use_eq1 subst'_size_function_ctx_ok.
    -- use_eq1 subst'_type_function_ctx_ok.
    -- use_eq1 subst'_linear_function_ctx_ok.
  - intros.
    unfold subst'_function_ctx.
    apply function_ctx_eq; simpl in *; auto.
    -- use_eq2 subst'_label_function_ctx_ok.
    -- use_eq2 subst'_ret_function_ctx_ok.
    -- use_eq2 subst'_qual_function_ctx_ok.
    -- use_eq2 subst'_size_function_ctx_ok.
    -- use_eq2 subst'_type_function_ctx_ok.
    -- use_eq2 subst'_linear_function_ctx_ok.
Qed.

Global Hint Resolve subst'_function_ctx_ok : OKDB.
Tactic Notation "pose_ok_proofs'" := pose_ok_proofs'; pose proof subst'_function_ctx_ok.
Ltac pose_ok_proofs ::= pose_ok_proofs'.

Instance BindExtFunctionCtx : BindExt Kind Function_Ctx := ltac:(mkBindExt).

(* Empty Ctxes *)
Definition empty_Module_Ctx : Module_Ctx := Build_Module_Ctx [] [] [].
Definition empty_Function_Ctx : Function_Ctx := Build_Function_Ctx [] None [] [] [] [] (Single_p (QualConst Unrestricted)).

(* Setters for Ctx *)
Definition update_label_ctx (lab : list (list Typ * Local_Ctx)) (C : Function_Ctx) : Function_Ctx :=
  let 'Build_Function_Ctx _ r q s t l lin := C in
  Build_Function_Ctx lab r q s t l lin.

Definition update_ret_ctx (r : option (list Typ)) (C : Function_Ctx) : Function_Ctx :=
  let 'Build_Function_Ctx lab _ q s t l lin := C in
  Build_Function_Ctx lab r q s t l lin.

Definition update_qual_ctx (q : list (list Qual * list Qual)) (C : Function_Ctx) : Function_Ctx :=
  let 'Build_Function_Ctx lab r _ s t l lin := C in
  Build_Function_Ctx lab r q s t l lin.

Definition update_size_ctx (s : list (list Size * list Size)) (C : Function_Ctx) : Function_Ctx :=
  let 'Build_Function_Ctx lab r q _ t l lin := C in
  Build_Function_Ctx lab r q s t l lin.

Definition update_type_ctx (t : list (Size * Qual * HeapableConstant)) (C : Function_Ctx) : Function_Ctx :=
  let 'Build_Function_Ctx lab r q s _ l lin := C in
  Build_Function_Ctx lab r q s t l lin.

(* TODO check what this is for *)
Definition update_location_ctx (l : list Qual) (C : Function_Ctx) : Function_Ctx :=
  let 'Build_Function_Ctx lab r q s t _ lin := C in
  Build_Function_Ctx lab r q s t l lin.

Definition update_linear_ctx (lin : plist Qual) (C : Function_Ctx) : Function_Ctx :=
  let 'Build_Function_Ctx lab r q s t l _ := C in
  Build_Function_Ctx lab r q s t l lin.

Definition HeapTyping := M.t HeapType.

Definition SplitHeapTyping (H1 H2 H3 : HeapTyping) : Prop :=
  Dom_ht H1 :|: Dom_ht H2 <--> Dom_ht H3 /\
  (forall l t, get_heaptype l H3 = Some t ->
               (get_heaptype l H1 = Some t /\ get_heaptype l H2 = None) /\
               (get_heaptype l H1 = None /\ get_heaptype l H2 = Some t)).             

Inductive ExactlyInOne : bool -> Ptr -> HeapType -> list HeapTyping -> Prop :=
| FoundNil :
    forall l ht, 
      ExactlyInOne true l ht []
| InHead :
    forall l ht H Hs, 
      get_heaptype l H = Some ht ->
      ExactlyInOne true l ht Hs ->
      ExactlyInOne false l ht (H :: Hs)
| NotInHead :    
    forall b l ht H Hs, 
      get_heaptype l H = None ->
      ExactlyInOne b l ht Hs ->
      ExactlyInOne b l ht (H :: Hs).
     
Definition SplitHeapTypings (Hs : list HeapTyping) (H : HeapTyping) : Prop :=
  Union_list (map Dom_ht Hs) <--> Dom_ht H /\
  (forall l ht, get_heaptype l H = Some ht -> ExactlyInOne false l ht Hs). 


Definition Empty_HeapTyping (H : HeapTyping) : Prop :=
  Dom_ht H <--> Ensembles.Empty_set _. 
  
Fixpoint nth_upd {A} (l : list A) (i : nat) (a : A) :=
  match l with
  | nil => l
  | cons x l =>
    match i with
    | 0 => a :: l
    | Datatypes.S i => x :: nth_upd l i a
    end
  end.

Definition get_localtype (l : nat) (loc : Local_Ctx) :=
  nth_error loc l.

Definition set_localtype (l : nat) (tau : Typ) (sz : Size) (loc : Local_Ctx) : Local_Ctx :=
  nth_upd loc l (tau, sz).

Definition InstanceTyping := list Module_Ctx. 

Record StoreTyping :=
  { InstTyp : InstanceTyping;
    LinTyp  : HeapTyping;
    UnrTyp : HeapTyping
  }.

Definition SplitStoreTypings (Ss : list StoreTyping) (S : StoreTyping) : Prop :=
  Forall (fun S' => InstTyp S = InstTyp S' /\ UnrTyp S = UnrTyp S') Ss /\
  let Hs := map LinTyp Ss in
  SplitHeapTypings Hs (LinTyp S).

Definition EmptyLinHeapTyping (S : StoreTyping) : Prop :=
  Empty_HeapTyping (LinTyp S).

Section QualLt.

  (* Definition Leq (c1 c2 : QaulConstant) : bool := *)
  (*   match c1, c2 with *)
  (*   | Unrestricted, _ => true *)
  (*   | Affine, Affine => true *)
  (*   | Affine, Linear => true *)
  (*   | _, Linear => true *)
  (*   | _, _ => false *)
  (*   end. *)

  (* Definition find_qual (m : M.t UseConstant) (q : Use) : option UseConstant := *)
  (*   match q with *)
  (*   | UseVar x => M.find x m *)
  (*   | UseConst x => Some x *)
  (*   end. *)


  (* Definition QualLeq (m : M.t UseConstant) (q1 q2 : Use) : Prop := *)
  (*   match q1, q2 with *)
  (*   | UseConst c1, UseConst c2 => Leq c1 c2 = true *)
  (*   | UseVar x, UseConst c2 => *)
  (*     match M.find x m with *)
  (*     | Some c1 => Leq c1 c2 = true *)
  (*     | None => False *)
  (*     end *)
  (*   | _, UseVar _ => False                        *)
  (*   end. *)

  (* A solver is needed for that *) 

  (* Zoe: If more axioms are needed we could have a separate interface for that at some point *)

 
  Definition qual_ctx : Type :=
    list (list Qual * list Qual).

  Section qual_leq.

    Variable (bounds: qual_ctx).

    Inductive qual_leq : Qual -> Qual -> Prop :=
    | QualLeqBot: forall q, qual_leq Unrestricted q
    | QualLeqTop: forall q, qual_leq q Linear
    | QualLeqJoinL: forall q qs,
        (forall q0, In q0 qs -> qual_leq q0 q) ->
        qual_leq (QualJoin qs) q
    | QualLeqJoinR: forall q q0 qs,
        In q0 qs ->
        qual_leq q q0 ->
        qual_leq q (QualJoin qs)
    | QualLeqRefl: forall q, qual_leq q q
    | QualLeqTrans: forall q1 q2 q3, qual_leq q1 q2 -> qual_leq q2 q3 -> qual_leq q1 q3
    | QualLeqUB: forall q1 q1' lbs ubs q2,
        bounds !! q1 = Some (lbs, ubs) ->
        List.In q1' ubs ->
        qual_leq q1' q2 ->
        qual_leq (QualVar q1) q2
    | QualLeqLB: forall q1 lbs ubs q2' q2,
        bounds !! q2 = Some (lbs, ubs) ->
        List.In q2' lbs ->
        qual_leq q1 q2' ->
        qual_leq q1 (QualVar q2).

  End qual_leq.

  Axiom QualLeq : list (list Qual * list Qual) -> Qual -> Qual -> option bool.

  Definition le_qualconst qc1 qc2 :=
    match qc1, qc2 with
    | Unrestricted, _ => True
    | _, Linear => True
    | _, _ => False
    end.

  Definition qual_const_join (p q: QualConstant) : QualConstant :=
    match p with
    | Unrestricted => q
    | Linear => Linear
    end.

  Fixpoint interp_qual (model : nat -> QualConstant) (q : Qual) :=
    match q with
    | QualVar v => model v
    | QualJoin qs => fold_left qual_const_join (map (interp_qual model) qs) Unrestricted
    | QualConst c => c
    end.

  Axiom QualLeq_desc : forall C q1 q2,
      QualLeq C q1 q2 = Some true <->
      ctx_imp_leq le_qualconst interp_qual C q1 q2.

  Theorem qual_leq_sound_and_complete: forall C q1 q2,
      qual_leq C q1 q2 <->
      ctx_imp_leq le_qualconst interp_qual C q1 q2.
  Proof.
  Admitted.

  Theorem QualLeq_Top : forall C q, QualLeq C q Linear = Some true.
  Proof.
    intros.
    rewrite QualLeq_desc.
    unfold ctx_imp_leq.
    intros.
    simpl; unfold le_qualconst.
    destruct (interp_qual model q); auto.
  Qed.

  Theorem QualLeq_Refl : forall C q, QualLeq C q q = Some true. 
  Proof.
    intros.
    rewrite QualLeq_desc.
    eapply ctx_imp_leq_refl; eauto.
    intros.
    destruct obj'; simpl; auto.
  Qed.

  Theorem QualLeq_Trans :
    forall C q1 q2 q3,
      QualLeq C q1 q2 = Some true ->
      QualLeq C q2 q3 = Some true ->
      QualLeq C q1 q3 = Some true.
  Proof.
    do 4 intro.
    repeat rewrite QualLeq_desc.
    eapply ctx_imp_leq_trans; eauto.
    intros.
    destruct obj1'; destruct obj2'; destruct obj3'; simpl in *; auto.
  Qed.

  Theorem QualLeq_Bigger_Ctx : forall C C' q1 q2,
      QualLeq C q1 q2 = Some true ->
      list_sub C C' ->
      QualLeq C' q1 q2 = Some true.
  Proof.
    do 4 intro.
    repeat rewrite QualLeq_desc.
    apply list_sub_ctx_imp_leq.
  Qed.

  Lemma eq_dec_nat : forall a b : nat,
      a = b \/ a <> b.
  Proof.
    intros.
    specialize (OrderedTypeEx.Nat_as_OT.eq_dec a b).
    intros.
    case H; eauto.
  Qed.

End QualLt.


(*
  Inductive RecQualValidTyp : Qual -> term.var -> Typ -> Prop :=
   | RecQualValidQualT : forall q x pt qpt,
       RecQualValidTyp q qpt x pt ->
       RecQualValidTyp q x (QualT pt qpt)
   with RecQualValidTyp : Qual -> Qual -> term.var -> Typ -> Prop :=
   | RecQualValidNum : forall q qpt x n,
       RecQualValidTyp q qpt x (Num n)
   | RecQualValidTVarSame : forall q qpt x xpt,
       x = xpt -> q = qpt ->
       RecQualValidTyp q qpt x (TVar xpt)
   | RecQualValidTVarOther : forall q qpt x xpt,
       x <> xpt ->
       RecQualValidTyp q qpt x (TVar xpt)
   | RecQualValidUnit : forall q qpt x,
       RecQualValidTyp q qpt x Unit
   | RecQualValidProdT : forall q qpt x taus,
       Forall (RecQualValidTyp q x) taus ->
       RecQualValidTyp q qpt x (ProdT taus)
   | RecQualValidCoderefT : forall q qpt x chi,
       RecQualValidTyp q qpt x (CoderefT chi)
   | RecQualValidRec : forall qα q qpt x tau,
       RecQualValidTyp q (x + 1) tau ->
       RecQualValidTyp q qpt x (Rec qα tau)
   | RecQualValidPtr : forall q qpt x l,
       RecQualValidTyp q qpt x (PtrT l)
   | RecQualValidExLoc : forall q qpt x tau,
       RecQualValidTyp q x tau ->
       RecQualValidTyp q qpt x (ExLoc tau)
   | RecQualValidOwnR : forall q qpt x l,
       RecQualValidTyp q qpt x (OwnR l)
   | RecQualValidCapT : forall q qpt x c l ht,
       RecQualValidHeapType q x ht ->
       RecQualValidTyp q qpt x (CapT c l ht)
   | RecQualValidRefT : forall q qpt x c l ht,
       RecQualValidHeapType q x ht ->
       RecQualValidTyp q qpt x (RefT c l ht)
   with RecQualValidHeapType : Qual -> term.var -> HeapType -> Prop :=
   | RecQualValidVariant : forall q x taus,
       Forall (RecQualValidTyp q x) taus ->
       RecQualValidHeapType q x (VariantType taus)
   | RecQualValidStruct : forall q x tauszs taus szs,
       split tauszs = (taus, szs) ->
       Forall (RecQualValidTyp q x) taus ->
       RecQualValidHeapType q x (StructType tauszs)
   | RecQualValidArray : forall q x tau,
       RecQualValidTyp q x tau ->
       RecQualValidHeapType q x (ArrayType tau)
   | RecQualValidEx : forall qα q x sz tau,
       RecQualValidTyp q (x + 1) tau ->
       RecQualValidHeapType q x (Ex sz qα tau).
  *)

  Inductive RecVarUnderRefTyp : Typ -> term.var -> bool -> Prop :=
  | RecVarUnderRefRef : forall c l ht v,
      RecVarUnderRefTyp (RefT c l ht) v true
  | RecVarUnderRefCap : forall c l ht v,
      RecVarUnderRefTyp (CapT c l ht) v true
  | RecVarUnderRefVar : forall v1 v2,
      RecVarUnderRefTyp (TVar v1) v2 (negb (Nat.eqb v1 v2))
  | RecVarUnderRefNum : forall n v,
      RecVarUnderRefTyp (Num n) v true
  | RecVarUnderRefUnit : forall v,
      RecVarUnderRefTyp Unit v true
  | RecVarUnderRefProd : forall v taus,
      Forall (fun typ => RecVarUnderRefTyp typ v true) taus ->
      RecVarUnderRefTyp (ProdT taus) v true
  | RecVarUnderRefCoderef : forall ft v,
      RecVarUnderRefTyp (CoderefT ft) v true
  | RecVarUnderRefRec : forall qa v tau,
      RecVarUnderRefTyp tau (v + 1) true ->
      RecVarUnderRefTyp (Rec qa tau) v true
  | RecVarUnderRefPtr : forall l v,
      RecVarUnderRefTyp (PtrT l) v true
  | RecVarUnderRefExLoc : forall v q tau,
      RecVarUnderRefTyp tau v true ->
      RecVarUnderRefTyp (ExLoc q tau) v true
  | RecVarUnderRefOwn : forall l v,
      RecVarUnderRefTyp (OwnR l) v true.

  Lemma RecVarUnderRefTypProd_iff taus v :
    RecVarUnderRefTyp (ProdT taus) v true <->
    Forall (fun typ => RecVarUnderRefTyp typ v true) taus.
  Proof.
    induction taus; cbn; [split; inversion 1; subst; now constructor|].
    split; inversion 1; subst.
    - inv H1; constructor; auto.
    - constructor; auto.
  Qed.

  Lemma Forall_cons_iff {A} (P : A -> Prop) (x : A) xs :
    Forall P (x :: xs) <-> P x /\ Forall P xs.
  Proof. split; inversion 1; subst; constructor; auto. Qed.

  Fixpoint rec_var_under_ref_typ t v :=
    match t with
    | Num _ => true
    | TVar x => negb (Nat.eqb x v)
    | Unit => true
    | ProdT ts => forallb (fun t => rec_var_under_ref_typ t v) ts
    | CoderefT x => true
    | Rec _ t => rec_var_under_ref_typ t (v + 1)
    | PtrT _ => true
    | ExLoc _ t => rec_var_under_ref_typ t v
    | OwnR _ => true
    | CapT _ _ _ => true
    | RefT _ _ _ => true
    end.
  
  Fixpoint RecVarUnderRefTyp_spec t v {struct t} :
    RecVarUnderRefTyp t v true <-> rec_var_under_ref_typ t v = true.
  Proof.
    destruct t; cbn; try (split; [reflexivity|intros[]]); try solve [constructor].
    + split; [inversion 1; subst; reflexivity|intros <-; constructor].
    + rewrite RecVarUnderRefTypProd_iff.
      induction τ__s; [cbn; split; [reflexivity|constructor] |].
      cbn; rewrite Forall_cons_iff, Bool.andb_true_iff, IHτ__s, RecVarUnderRefTyp_spec.
      reflexivity.
    + split; [inversion 1; subst|constructor]; apply RecVarUnderRefTyp_spec; assumption.
    + split; [inversion 1; subst|constructor]; apply RecVarUnderRefTyp_spec; assumption.
  Qed.


  (* adds variables and constraints and shifts appropriately *)
  Definition add_constraint (C : Function_Ctx) (quant : KindVar) : Function_Ctx :=
    match quant with
    | LOC q => subst_ext (weak SLoc) (update_location_ctx (q :: location C) C)
    | QUAL qs qs' => subst_ext (weak SQual) (update_qual_ctx ((qs, qs') :: qual C) C)
    | SIZE sz sz' => subst_ext (weak SSize) (update_size_ctx ((sz, sz') :: size C) C)
    | TYPE sz q hc => subst_ext (weak STyp) (update_type_ctx ((sz, q, hc) :: type C) C)
    end.

  Definition add_constraints (C : Function_Ctx) (quants : list KindVar) : Function_Ctx :=
    fold_left add_constraint quants C.

  Definition LocQual (C: Function_Ctx) (loc: Loc) : option Qual :=
    match loc with
    | LocV ρ => loc_var_qual C ρ
    | LocP _ mem => mret $ mem_qual mem
    end.

  Fixpoint TypQual (C: Function_Ctx) (ty: Typ) : option Qual :=
    match ty with
    | Num _
    | Unit
    | CoderefT _
    | PtrT _ => mret (Unrestricted: Qual)
    | TVar α => typ_var_qual C α
    | ProdT tys => quals ← (mapM (TypQual C) tys); mret (QualJoin quals)
    | Rec q _ => mret q
    | ExLoc q ty => TypQual (add_constraint C (LOC q)) ty
    | OwnR loc
    | CapT _ loc _ 
    | RefT _ loc _ => LocQual C loc
    end.

  Definition TypQualLeq (C : Function_Ctx) (t : Typ) (q : Qual) :=
    q' ← (TypQual C t);
    QualLeq (qual C) q' q.

  Definition TypQualGeq (C : Function_Ctx) (t : Typ) (q : Qual) :=
    q' ← (TypQual C t);
    QualLeq (qual C) q q'.
  
Section Validity.

  Inductive QualValid : list (list Qual * list Qual) -> Qual -> Prop :=
  | QualConstValid :
      forall C q const, q = QualConst const -> QualValid C q
  | QualVarValid :
      forall C q var constraint,
        q = QualVar var ->
        nth_error C var = Some constraint ->
        QualValid C q.

  Inductive LocValid : list Qual -> Loc -> Prop :=
  | LocPValid :
      forall C l ptr qual, l = LocP ptr qual -> LocValid C l
  | LocVValid :
      forall C l var,
        l = LocV var ->
        var < length C ->
        LocValid C l.

  Inductive SizeValid : list (list Size * list Size) -> Size -> Prop :=
  | SizeConstValid :
      forall C sz n,
        sz = SizeConst n -> SizeValid C sz
  | SizePlusValid :
      forall C sz1 sz2 sz3,
        sz1 = SizePlus sz2 sz3 ->
        SizeValid C sz2 ->
        SizeValid C sz3 ->
        SizeValid C sz1
  | SizeVarValid :
      forall C sz var constraint,
        sz = SizeVar var ->
        nth_error C var = Some constraint ->
        SizeValid C sz.

  Definition KindVarValid C kv :=
    match kv with
    | LOC q => True
    | QUAL qs1 qs2 => Forall (QualValid (qual C)) qs1 /\ Forall (QualValid (qual C)) qs2
    | SIZE ss1 ss2 => Forall (SizeValid (size C)) ss1 /\ Forall (SizeValid (size C)) ss2
    | TYPE s q hc => SizeValid (size C) s /\ QualValid (qual C) q
    end.
  
  Inductive KindVarsValid : Function_Ctx -> list KindVar -> Prop :=
  | KindVarsValidNil : forall C, KindVarsValid C []
  | KindVarsValidCons : forall C kv kvs, KindVarValid C kv ->
                                 KindVarsValid (add_constraint C kv) kvs ->
                                 KindVarsValid C (kv :: kvs).
  
  (* Presupposes the Function_Ctx argument is valid *)
  Inductive TypeValid: Function_Ctx -> Typ -> Prop :=
  | TNumValid :
      forall C n,
        TypeValid C (Num n)
  | TVarValid :
      forall C q a sz hc,
        nth_error (type C) a = Some (sz, q, hc) ->
        TypeValid C (TVar a)
  | TRecValid :
      forall C qa q p sz,
        QualValid (qual C) qa ->
        TypQualLeq C p q = Some true ->
        sizeOfType (type C) (Rec qa p) = Some sz ->
        SizeValid (size C) sz ->
        RecVarUnderRefTyp p 0 true ->
        TypeValid (subst_ext (weak STyp) (add_constraint C (TYPE sz qa Heapable))) p ->
        TypeValid C (Rec qa p)
  | TUnitValid :
      forall C,
        TypeValid C Unit
  | TProdValid :
      forall C taus,
        Forall (TypeValid C) taus ->
        TypeValid C (ProdT taus)
  | TCoderefValid :
      forall C ft,
        FunTypeValid C ft ->
        TypeValid C (CoderefT ft)
  | TPtrValid :
      forall C l,
        LocValid (location C) l ->
        TypeValid C (PtrT l)
  | TCapValid :
      forall C c l psi,
        LocValid (location C) l ->
        HeapTypeValid C psi ->
        TypeValid C (CapT c l psi)
  | TRefValid :
      forall C q c l psi,
        QualValid (qual C) q ->
        LocValid (location C) l ->
        HeapTypeValid C psi ->
        TypeValid C (RefT c l psi)
  | TExLocValid :
      forall C ty q,
        QualValid (qual C) q ->
        TypQualLeq C ty q = Some true ->
        TypeValid (subst_ext (weak SLoc) (add_constraint C (LOC q))) ty ->
        TypeValid C (ExLoc q ty)
  | TOwnValid :
      forall C l q,
        QualValid (qual C) q ->
        QualLeq (qual C) Linear q  = Some true ->
        LocValid (location C) l ->
        TypeValid C (OwnR l)
  with FunTypeValid : Function_Ctx -> FunType -> Prop :=
  | FunTValid :
      forall C quants arr,
        KindVarsValid C quants ->
        ArrowTypeValid (add_constraints C quants) arr ->
        FunTypeValid C (FunT quants arr)
  with ArrowTypeValid : Function_Ctx -> ArrowType -> Prop :=
  | ArrowValid :
      forall C ts1 ts2,
        Forall (TypeValid C) ts1 ->
        Forall (TypeValid C) ts2 ->
        ArrowTypeValid C (Arrow ts1 ts2)
  with HeapTypeValid : Function_Ctx -> HeapType -> Prop :=
  | VariantValid :
      forall taus C,
        Forall (TypeValid C) taus ->
        HeapTypeValid C (VariantType taus)
  | StructValid :
      forall tausizes C,
        Forall (fun tausize => exists sz, sizeOfType (type C) (fst tausize) = Some sz /\
                                   SizeValid (size C) (snd tausize) /\
                                   SizeValid (size C) sz /\
                                   TypeValid C (fst tausize) /\
                                   SizeLeq (size C) sz (snd tausize) = Some true) tausizes ->
        HeapTypeValid C (StructType tausizes)
  | ArrayValid :
      forall qp p C,
        TypeValid C p ->
        QualLeq (qual C) qp Unrestricted = Some true ->
        HeapTypeValid C (ArrayType p)
  | ExValid :
      forall C qα sz tau,
        SizeValid (size C) sz ->
        QualValid (qual C) qα ->
        TypeValid (subst_ext (weak STyp) (update_type_ctx ((sz, qα, Heapable) :: type C) C)) tau ->
        HeapTypeValid C (Ex sz qα tau).

  (*
  Definition HeapTypeUnrestricted: Function_Ctx -> HeapType -> Prop :=
  | VariantUnrestricted :
      forall taus C,
        Forall (fun '(QualT _ q) => QualValid (qual C) q /\ QualLeq (qual C) q Unrestricted = Some true) taus ->
        HeapTypeUnrestricted C (VariantType taus)
  | StructUnrestricted :
      forall tausizes C,
        Forall (fun '(QualT _ q, _) => QualValid (qual C) q /\ QualLeq (qual C) q Unrestricted = Some true) tausizes ->
        HeapTypeUnrestricted C (StructType tausizes)
  | ArrayUnrestricted :
      forall qp p C,
        QualValid (qual C) qp ->
        QualLeq (qual C) qp Unrestricted = Some true ->
        HeapTypeUnrestricted C (ArrayType (QualT p qp))
  | ExUnrestricted :
      forall C qα sz p q,
        QualValid (qual C) qα ->
        QualValid (qual C) q ->
        QualLeq (qual C) qα Unrestricted = Some true ->
        QualLeq (qual C) q Unrestricted = Some true ->
        HeapTypeUnrestricted C (Ex sz qα (QualT p q)).
*)
  (*

  Section ValidInd.
    
  Context (TypeValid': Function_Ctx -> Typ -> Prop)
          (HeapTypeValid' : Function_Ctx -> HeapType -> Prop)
          (ArrowTypeValid' : Function_Ctx -> ArrowType -> Prop)
          (FunTypeValid' : Function_Ctx -> FunType -> Prop).

  Context
    (TNumValid :
      forall C q n,
        QualValid (qual C) q ->
        TypeValid' C (QualT (Num n) q))
    (TVarValid :
      forall C q a qa sz hc,
        QualValid (qual C) q ->
        QualValid (qual C) qa ->
        nth_error (type C) a = Some (sz, qa, hc) ->
        QualLeq (qual C) qa q = Some true ->
        TypeValid' C (QualT (TVar a) q))
    (TRecValid :
      forall C qa q qp p sz,
        QualValid (qual C) q ->
        QualValid (qual C) qa ->
        QualValid (qual C) qp ->
        QualLeq (qual C) qp q = Some true ->
        QualLeq (qual C) qp qa = Some true ->
        RecVarUnderRefTyp p 0 true ->
        sizeOfTyp (type C) (Rec qa (QualT p qp)) = Some sz ->
        SizeValid (size C) sz ->
        TypeValid' (subst_ext (weak STyp) (update_type_ctx ((sz, qa, Heapable) :: type C) C)) (QualT p qp) ->
        TypeValid' C (QualT (Rec qa (QualT p qp)) q))
    (TUnitValid :
      forall C q,
        QualValid (qual C) q ->
        TypeValid' C (QualT Unit q))
    (TProdValid :
      forall C taus q,
        QualValid (qual C) q ->
        Forall (fun '(QualT _ qi) => QualLeq (qual C) qi q = Some true) taus ->
        Forall (TypeValid' C) taus ->
        TypeValid' C (QualT (ProdT taus) q))
    (TCoderefValid :
      forall C ft q,
        QualValid (qual C) q ->
        FunTypeValid' C ft ->
        TypeValid' C (QualT (CoderefT ft) q))
    (TPtrValid :
      forall C q l,
        QualValid (qual C) q ->
        LocValid (location C) l ->
        TypeValid' C (QualT (PtrT l) q))
    (TCapValid :
      forall C q c l psi,
        QualValid (qual C) q ->
        LocValid (location C) l ->
        HeapTypeValid' C psi ->
        TypeValid' C (QualT (CapT c l psi) q))
    (TRefValid :
      forall C q c l psi,
        QualValid (qual C) q ->
        LocValid (location C) l ->
        HeapTypeValid' C psi ->
        TypeValid' C (QualT (RefT c l psi) q))
    (TExLocValid :
      forall C qp p q,
        QualValid (qual C) q ->
        QualLeq (qual C) qp q = Some true ->
        TypeValid' (subst_ext (weak SLoc) (update_location_ctx (location C + 1) C)) (QualT p qp) ->
        TypeValid' C (QualT (ExLoc (QualT p qp)) q))
    (TOwnValid :
      forall C l q,
        QualValid (qual C) q ->
        QualLeq (qual C) Linear q  = Some true ->
        LocValid (location C) l ->
        TypeValid' C (QualT (OwnR l) q))
    (VariantValid :
      forall taus C,
        Forall (TypeValid' C) taus ->
        HeapTypeValid' C (VariantType taus))
    (StructValid :
      forall tausizes C,
        Forall (fun tausize => exists sz, sizeOfType (type C) (fst tausize) = Some sz /\
                                          SizeValid (size C) (snd tausize) /\
                                          SizeValid (size C) sz /\
                                          TypeValid' C (fst tausize) /\
                                          SizeLeq (size C) sz (snd tausize) = Some true) tausizes ->
        HeapTypeValid' C (StructType tausizes))
    (ArrayValid :
      forall qp p C,
        TypeValid' C (QualT p qp) ->
        QualLeq (qual C) qp Unrestricted = Some true ->
        HeapTypeValid' C (ArrayType (QualT p qp)))
    (ExValid :
       forall C qα sz tau,
         SizeValid (size C) sz ->
         QualValid (qual C) qα ->
        TypeValid' (subst_ext (weak STyp) (update_type_ctx ((sz, qα, Heapable) :: type C) C)) tau ->
        HeapTypeValid' C (Ex sz qα tau))
    (ArrowValid :
      forall C ts1 ts2,
        Forall (TypeValid' C) ts1 ->
        Forall (TypeValid' C) ts2 ->
        ArrowTypeValid' C (Arrow ts1 ts2))
    (FunTValid :
      forall C quants arr,
        KindVarsValid C quants ->
        ArrowTypeValid' (add_constraints C quants) arr ->
        FunTypeValid' C (FunT quants arr)).

  (* To temporarily hide IHs from eauto *)
  Inductive Trivial : Prop := MkTrivial.
  Definition sealed (P : Prop) : Prop := Trivial -> P.
  (* These proofs need to compute so termination checker can see unseal (seal IH_proof) = IH_proof *)
  Definition seal (P : Prop) : P -> sealed P := fun prf => fun _ => prf.
  Definition unseal (P : Prop) : sealed P -> P := fun prf => prf MkTrivial.
  (* Test hiding from eauto *)
  Goal False -> False. Proof. intros H; clear - H. apply seal in H. Fail solve [eauto]. Abort.
  (* Test unseal ∘ seal = id *)
  Goal forall (P : Prop) (prf : P), unseal P (seal P prf) = prf. Proof. intros. exact eq_refl. Abort.
  
  Fixpoint TypeValid_ind' F t (Hty : TypeValid F t) {struct Hty} : TypeValid' F t
  with HeapTypeValid_ind' F t (Hty : HeapTypeValid F t) {struct Hty} : HeapTypeValid' F t
  with ArrowTypeValid_ind' F t (Hty : ArrowTypeValid F t) {struct Hty} : ArrowTypeValid' F t
  with FunTypeValid_ind' F t (Hty : FunTypeValid F t) {struct Hty} : FunTypeValid' F t.
  Proof.
    all: destruct Hty;
        try (apply seal in TypeValid_ind';
             apply seal in HeapTypeValid_ind';
             apply seal in ArrowTypeValid_ind';
             apply seal in FunTypeValid_ind';
             multimatch goal with
             (* Somewhere in the context, there's a suitable assumption *)
             | H : forall _, _ |- _ =>
               solve [
                 (* Apply it and solve side conditions by using the stuff that was inside Hty *)
                 eapply H; eauto;
                 (* Now, it should be safe to apply induction hypothesis where needed *)
                 apply unseal in TypeValid_ind';
                 apply unseal in HeapTypeValid_ind';
                 apply unseal in ArrowTypeValid_ind';
                 apply unseal in FunTypeValid_ind';
                 eauto;
                 (* Some cases have recursive occurrences of
                    the typing judgment under Forall. Solve by nested induction *)
                 match goal with
                 | H : Forall _ ?taus |- Forall _ ?taus =>
                   clear - H TypeValid_ind' HeapTypeValid_ind'
                             ArrowTypeValid_ind' FunTypeValid_ind';
                   induction H; constructor; try solve [eauto|firstorder eauto]
                 end]
             end).
  Qed.
  
  Corollary TypesValid_ind' :
    (forall F t, TypeValid F t -> TypeValid' F t) /\
    (forall F t, HeapTypeValid F t -> HeapTypeValid' F t) /\
    (forall F t, ArrowTypeValid F t -> ArrowTypeValid' F t) /\
    (forall F t, FunTypeValid F t -> FunTypeValid' F t).
  Proof.
    repeat split; intros; [apply TypeValid_ind'|apply HeapTypeValid_ind'|apply ArrowTypeValid_ind'|apply FunTypeValid_ind']; auto.
  Qed.

  Scheme TypeValid_mind := Induction for TypeValid Sort Prop
    with HeapTypeValid_mind := Induction for HeapTypeValid Sort Prop
    with ArrowTypeValid_mind := Induction for ArrowTypeValid Sort Prop
    with FunTypeValid_mind := Induction for FunTypeValid Sort Prop.

  End ValidInd.
*)
  
End Validity.


Definition EmptyArrow tau : ArrowType := Arrow [] [tau].

Definition EmptyRes tau : ArrowType := Arrow [tau] [].


Section Typing.

  Definition NumLen (n : NumType) :=
    match n with
    | Int _ i32 | Float f32 => 2 ^ 32
    | Int _ i64 | Float f64 => 2 ^ 64
    end.

  Fixpoint NoCapsTyp (F : list HeapableConstant) (tau : Typ) : bool :=
    match tau with
      | Num _
      | Unit
      | CoderefT _
      | PtrT _
      | OwnR _
      | RefT _ _ _ => true
      | TVar n =>
        (match List.nth_error F n with
         | None => false
         | Some Heapable => true
         | Some NotHeapable => false
        end)
      | ProdT taus => forallb (NoCapsTyp F) taus
      | Rec _ tau => NoCapsTyp (Heapable :: F) tau
      | ExLoc _ tau => NoCapsTyp F tau
      | CapT _ _ _ => false
    end.

  Definition NoCapsHeapType (F : list HeapableConstant) (ht : HeapType) : bool :=
    match ht with
    | VariantType taus => forallb (NoCapsTyp F) taus
    | StructType tis => forallb (NoCapsTyp F) (fst (split tis))
    | ArrayType tau => NoCapsTyp F tau
    | Ex s q tau => NoCapsTyp (Heapable :: F) tau
    end.
    
  Inductive InstIndValid : Function_Ctx -> FunType -> Index -> Prop :=
  | LocIndValid :
      forall l F rest tf q,
        LocValid (location F) l ->
        LocQual F l = Some q ->
        InstIndValid F (FunT (LOC q :: rest) tf) (LocI l)
  | TypeInstValid : 
      forall c l sz psi q F rest tf hc,
        TypeValid F (RefT c l psi) ->
        InstIndValid F (FunT ((TYPE sz q hc) :: rest) tf) (TypI (RefT c l psi))
  | QualInstValid :
      forall q qs1 qs2 F rest tf,
        QualValid (qual F) q ->
        Forall (fun q' => QualValid (qual F) q' /\ QualLeq (qual F) q' q = Some true) qs1 ->
        Forall (fun q' => QualValid (qual F) q' /\ QualLeq (qual F) q q' = Some true) qs2 ->
        InstIndValid F (FunT ((QUAL qs1 qs2) :: rest) tf) (QualI q)
  | SizeInstValid :
      forall sz szs1 szs2 F rest tf,
        SizeValid (size F) sz ->
        Forall (fun sz' => SizeValid (size F) sz' /\ SizeLeq (size F) sz' sz = Some true) szs1 ->
        Forall (fun sz' => SizeValid (size F) sz' /\ SizeLeq (size F) sz sz' = Some true) szs2 ->
        InstIndValid F (FunT ((SIZE szs1 szs2) :: rest) tf) (SizeI sz).

  Definition InstInd (ft : FunType) (i : Index) : option FunType :=
    match ft, i with
    | FunT (LOC q :: rest) tf, (LocI l) => Some (subst_ext (ext subst.SLoc l id) (FunT rest tf))
    | FunT ((QUAL q1s q2s) :: rest) tf, (QualI q) => Some (subst_ext (ext subst.SQual q id) (FunT rest tf))
    | FunT ((SIZE sz1s sz2s) :: rest) tf, (SizeI s) => Some (subst_ext (ext subst.SSize s id) (FunT rest tf))
    | FunT ((TYPE size q hc) :: rest) tf, (TypI p) => Some (subst_ext (ext subst.STyp p id) (FunT rest tf))
    | _, _ => None
    end.

  Inductive InstIndsValid : Function_Ctx -> FunType -> list Index -> Prop :=
  | InstIndsValidNil :
      forall F chi,
        InstIndsValid F chi []
  | InstIndsValidCons :
      forall F chi chi' f r,
        InstIndValid F chi f ->
        InstInd chi f = Some chi' ->
        InstIndsValid F chi' r ->
        InstIndsValid F chi (f :: r).

  Definition InstInds (ft : FunType) (is : list Index) : option FunType :=
    fold_left (fun ft i =>
                 match ft with
                 | None => None
                 | Some ft => InstInd ft i
              end) is (Some ft).
  
  Fixpoint ReplaceAtIdx {A : Type} (i : nat) (l : list A) (new : A) : option (list A * A) :=
    match i, l with
      | 0, old :: rest => Some (new :: rest, old)
      | Datatypes.S _, first :: rest =>
          '(rest, old) ← (ReplaceAtIdx (i - 1) rest new);
          mret (first :: rest, old)
      | _, _ => None
    end.

  Definition uint32T : Typ := Num (Int U i32).
  Definition uint64T : Typ := Num (Int U i64).
  Definition int32T : Typ := Num (Int U i32).
  Definition int64T : Typ := Num (Int U i64).
  Definition float32T : Typ := Num (Float f32).
  Definition float64T : Typ := Num (Float f64).

  (* Note: This is O(n^2) where n the lize of local_type. *)
  Fixpoint add_local_effects (L : Local_Ctx) (tl : LocalEffect) : Local_Ctx :=
    match tl with
    | [] => L
    | (i, tau) :: tl =>
      match get_localtype i L with
      | Some (_tau, size) => add_local_effects (set_localtype i tau size L) tl
      | None => add_local_effects L tl
      end
    end.

  Definition empty_LinTyp (s : StoreTyping) :=
    match s with
    | Build_StoreTyping i l u => Build_StoreTyping i (M.empty _) u
    end.

  Inductive RoomForStrongUpdates : N -> HeapType -> Prop :=
  | NoUpdateTypeFits : forall l ht,
      match ht with
      | VariantType _ => True
      | ArrayType _ => True
      | Ex _ _ _ => True
      | StructType _ => False
      end ->
      RoomForStrongUpdates l ht
  | StructTypeFits : forall tauszs taus szs l,
      split tauszs = (taus, szs) ->
      ((fold_left (fun acc sz =>
                    match (size_to_nat sz) with
                    | None => acc
                    | Some n => acc + (N.of_nat n)
                    end) szs (N.of_nat 0)) <= l)%N ->
      RoomForStrongUpdates l (StructType tauszs).

  Definition LCEffEqual
             C (L : Local_Ctx) (L' : Local_Ctx) :=
    Forall2
      (fun '(t0, sz0) '(t1, sz1) =>
         t0 = t1 /\
         SizeLeq C sz0 sz1 = Some true /\
         SizeLeq C sz1 sz0 = Some true)
      L L'.

  Lemma LCEffEqual_refl : forall C L,
      LCEffEqual C L L.
  Proof.
    intros.
    unfold LCEffEqual.
    apply forall2_nth_error_inv; auto.
    intros.
    destruct_prs.
    match goal with
    | [ H : ?A = _, H' : ?A = _ |- _ ] =>
      rewrite H in H'; inversion H'; subst
    end.
    split; auto.
    split; apply SizeLeq_Refl.
  Qed.

  Lemma LCEffEqual_sym : forall {C L L'},
      LCEffEqual C L L' ->
      LCEffEqual C L' L.
  Proof.
    unfold LCEffEqual.
    intros.
    apply forall2_nth_error_inv; [ | apply eq_sym; eapply Forall2_length; eauto ].
    intros.
    destruct_prs.
    match goal with
    | [ H : Forall2 _ ?L1 ?L2,
        H' : nth_error ?L1 _ = Some _,
        H'' : nth_error ?L2 _ = Some _ |- _ ] =>
      specialize (forall2_nth_error _ _ _ _ _ _ H H' H'')
    end.
    intros; simpl in *; destructAll; eauto.
  Qed.

  Lemma LCEffEqual_trans : forall {C L1 L2 L3},
      LCEffEqual C L1 L2 ->
      LCEffEqual C L2 L3 ->
      LCEffEqual C L1 L3.
  Proof.
    unfold LCEffEqual.
    intros.
    apply forall2_nth_error_inv; [ | eapply eq_trans; eapply Forall2_length; eauto ].
    intros.
    match goal with
    | [ H : Forall2 _ ?L1 ?L2,
        H' : nth_error ?L1 ?IDX = Some _ |- _ ] =>
      let H0 := fresh "H" in
      assert (H0 : exists v, nth_error L2 IDX = Some v);
      [ remember (nth_error L2 IDX) as obj | ]
    end.
    { generalize (eq_sym Heqobj); case obj; intros; eauto.
      rewrite nth_error_None in *.
      match goal with
      | [ H : Forall2 _ ?L1 ?L2,
          H' : nth_error ?L1 ?IDX = Some _ |- _ ] =>
        let H0 := fresh "H" in
        assert (H0 : IDX < length L1);
        [ apply nth_error_Some; rewrite H';
          intro H''; inversion H'' | ];
        let H1 := fresh "H" in
        assert (H1 : length L1 = length L2);
        [ eapply Forall2_length; eauto | ];
        rewrite H1 in H0;
        let H2 := fresh "H" in
        assert (H2 : IDX < IDX);
        [ eapply Nat.lt_le_trans; eauto | ];
        apply Nat.lt_irrefl in H2; exfalso; auto
      end. }
    destructAll.
    destruct_prs.
    match goal with
    | [ H : Forall2 _ ?L1 ?L2,
        H''' : Forall2 _ ?L2 ?L3,
        H' : nth_error ?L1 _ = Some _,
        H'' : nth_error ?L2 _ = Some _,
        H'''' : nth_error ?L3 _ = Some _ |- _ ] =>
      specialize (forall2_nth_error _ _ _ _ _ _ H H' H'');
      specialize (forall2_nth_error _ _ _ _ _ _ H''' H'' H'''')
    end.
    intros; simpl in *; destructAll; subst.
    split; auto.
    split; eapply SizeLeq_Trans; eauto.
  Qed.

  Definition LocalCtxValid (F : Function_Ctx) (L : Local_Ctx) :=
    Forall (fun '(tau, sz) => TypeValid F tau /\ SizeValid (size F) sz) L.

  Inductive LocalSig : Type :=
  | LSig (L: Local_Ctx) (L': Local_Ctx).

  Definition TyAnn : Type :=
    ArrowType * LocalSig.

  Definition instr_ann {A: Type} (inst: instr A) : A :=
    match inst with
    | INumConst ann _ _
    | IUnit ann
    | INum ann _
    | IUnreachable ann
    | INop ann
    | IDrop ann
    | IBlock ann _ _ _
    | ILoop ann _ _
    | IIte ann _ _ _ _
    | IBr ann _
    | IBrIf ann _
    | IBrTable ann _ _
    | IRet ann
    | IGetLocal ann _ _
    | ISetLocal ann _
    | IGetGlobal ann _
    | ISetGlobal ann _
    | ICoderef ann _
    | ICallIndirect ann _
    | ICall ann _ _
    | IRecFold ann _
    | IRecUnfold ann
    | IGroup ann _
    | IUngroup ann
    | ICapSplit ann
    | ICapJoin ann
    | IRefDemote ann
    | IMemPack ann _
    | IMemUnpack ann _ _ _
    | IStructMalloc ann _ _
    | IStructFree ann
    | IStructGet ann _
    | IStructSet ann _
    | IStructSwap ann _
    | IVariantMalloc ann _ _ _
    | IVariantCase ann _ _ _ _ _
    | IArrayMalloc ann _
    | IArrayGet ann
    | IArraySet ann
    | IArrayFree ann
    | IExistPack ann _ _ _
    | IExistUnpack ann _ _ _ _ _
    | IRefSplit ann
    | IRefJoin ann
    | IQualify ann _ =>
        ann
    end.

  Definition instr_type (i: instr TyAnn) : ArrowType :=
    (instr_ann i).1.
    
  Definition instr_lsig (i: instr TyAnn) : LocalSig :=
    (instr_ann i).2.

  Definition float_type_width : FloatType -> nat.
  Admitted.

  Definition int_type_width : IntType -> nat.
  Admitted.

  Inductive cvt_typ : CvtOp -> NumType -> NumType -> Prop :=
  | TWrap: forall s, cvt_typ Wrap (Int s i64) (Int s i32)
  | TExtend: forall s, cvt_typ (Extend s) (Int s i32) (Int s i64)
  | TTrunc: forall i f s, cvt_typ (Trunc i f s) (Float f) (Int s i)
  | TTruncSat: forall i f s, cvt_typ (TruncSat i f s) (Float f) (Int s i)
  | TDemote: cvt_typ Demote (Float f64) (Float f32)
  | TPromote: cvt_typ Promote (Float f32) (Float f64)
  | TConvert: forall f i s, cvt_typ (Convert f i s) (Int s i) (Float f)
  | TReinterpretFI: forall s f i,
      float_type_width f = int_type_width i ->
      cvt_typ (ReinterpretFI f i) (Float f) (Int s i)
  | TReinterpretIF: forall s f i,
      float_type_width f = int_type_width i ->
      cvt_typ (ReinterpretIF i f) (Int s i) (Float f)
  | TReinterpretII: forall s s' i,
      cvt_typ (ReinterpretII i s s') (Int s i) (Int s' i).

  Inductive HasTypeNumInstr : NumInstr -> ArrowType -> Prop :=
  | IuTyp: forall s i op,
      HasTypeNumInstr (Iu i op) (Arrow [Num (Int s i)] [Num (Int s i)])
  | IbTyp: forall s i op,
      HasTypeNumInstr (Ib i op) (Arrow [Num (Int s i); Num (Int s i)] [Num (Int s i)])
  | FuTyp: forall f op,
      HasTypeNumInstr (Fu f op) (Arrow [Num (Float f)] [Num (Float f)])
  | FbTyp: forall f op,
      HasTypeNumInstr (Fb f op) (Arrow [Num (Float f); Num (Float f)] [Num (Float f)])
  | ItTyp: forall s i op,
      HasTypeNumInstr (It i op) (Arrow [Num (Int s i)] [Num (Int U i32)])
  | IrTyp: forall s i op,
      HasTypeNumInstr (It i op) (Arrow [Num (Int s i); Num (Int s i)] [Num (Int U i32)])
  | FrTyp: forall f op,
      HasTypeNumInstr (Fr f op) (Arrow [Num (Float f); Num (Float f)] [Num (Int U i32)])
  | CvtITyp: forall op t t',
      cvt_typ op t t' ->
      HasTypeNumInstr (Cvt op) (Arrow [Num t] [Num t']).

  Inductive HasTypeInstr :
    Module_Ctx -> Function_Ctx ->
    Local_Ctx -> instr TyAnn -> ArrowType -> Local_Ctx -> Prop :=
  | NumConstTyp :
      forall C F L nt c,
        LocalCtxValid F L ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (INumConst (EmptyArrow (Num nt), LSig L L) nt c) (EmptyArrow (Num nt)) L
  | UnitTyp :
      forall C F L,
        LocalCtxValid F L ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (IUnit (Arrow [] [], LSig L L)) (Arrow [] []) L
  | NumInstrTyp:
    forall C F L ni tf,
      HasTypeNumInstr ni tf ->
      HasTypeInstr C F L (INum (tf, LSig L L) ni) tf L
  | UnreachableType :
      forall S C F L L' taus1 taus2 tl,
        M.is_empty (LinTyp S) = true ->
        LocalCtxValid F L ->
        L' = add_local_effects L tl ->
        LocalCtxValid F L' ->
        Forall (TypeValid F) taus1 ->
        Forall (TypeValid F) taus2 ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (IUnreachable (Arrow taus1 taus2, LSig L L')) (Arrow taus1 taus2) L'
  | NopTyp :
      forall C F L,
        LocalCtxValid F L ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (INop (Arrow [] [], LSig L L)) (Arrow [] []) L
  | DropTyp :
      forall C F L t,
        LocalCtxValid F L ->
        TypeValid F t ->
        TypQualLeq F t Unrestricted = Some true ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (IDrop (Arrow [t] [], LSig L L)) (Arrow [t] []) L
  | BlockTyp :
      forall C F L tl taus1 taus2 es L'',
        let tf := Arrow taus1 taus2 in
        let L' := add_local_effects L tl in
        let F1 := update_label_ctx ((taus2, L'') :: (label F)) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
        HasTypeInstrs C F2 L es tf L' ->
        LCEffEqual (size F) L' L'' ->
        LocalCtxValid F L'' ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (IBlock (tf, LSig L L') tf tl es) tf L'
  | LoopTyp :
      forall C F L taus1 taus2 es,
        let tf := Arrow taus1 taus2 in
        (* let L' := add_local_effects L tl in *)
        let F1 := update_label_ctx ((taus1, L) :: (label F)) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
        HasTypeInstrs C F2 L es tf L ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (ILoop (tf, LSig L L) tf es) tf L
  | ITETyp :
      forall C F L tl taus1 taus2 es1 es2 L'',
        let tf := Arrow taus1 taus2 in
        let L' := add_local_effects L tl in
        let F1 := update_label_ctx ((taus2, L'') :: (label F)) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
        HasTypeInstrs C F2 L es1 tf L' ->
        HasTypeInstrs C F2 L es2 tf L' ->
        LCEffEqual (size F) L' L'' ->
        LocalCtxValid F L'' ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (IIte (Arrow (taus1 ++ [uint32T]) taus2, LSig L L') tf tl es1 es2) (Arrow (taus1 ++ [uint32T]) taus2) L'
  | BrTyp :
      forall C F L i taus1 taus1' taus2 tl,
        nth_error (label F) i = Some (taus1', L) ->
        Forall (fun tau => TypQualLeq F tau Unrestricted = Some true) taus1 ->                
        (forall j, j <= i ->
                   exists q, nth_error_plist (linear F) j = Some q /\
                        QualValid (qual F) q /\
                        QualLeq (qual F) q Unrestricted = Some true) ->
        LocalCtxValid F L ->
        Forall (TypeValid F) (taus1 ++ taus1') ->
        Forall (TypeValid F) taus2 ->
        LocalCtxValid F (add_local_effects L tl) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (IBr (Arrow (taus1 ++ taus1') taus2,
                                LSig L (add_local_effects L tl)) i)
          (Arrow (taus1 ++ taus1') taus2) (add_local_effects L tl)
  | Br_ifTyp :
      forall C F L i taus,
        nth_error (label F) i = Some (taus, L) ->
        (* Forall (fun tau => TypQualLeq F tau Unrestricted = Some true) taus ->                 *)
        (forall j, j <= i ->
                   exists q, nth_error_plist (linear F) j = Some q /\
                        QualValid (qual F) q /\
                        QualLeq (qual F) q Unrestricted = Some true) ->
        LocalCtxValid F L ->
        Forall (TypeValid F) taus ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (IBrIf (Arrow (taus ++ [uint32T]) taus, LSig L L) i) (Arrow (taus ++ [uint32T]) taus) L
  | Br_tableTyp :
      forall C F L is taus1 taus1' taus2 tl k,
        Forall (fun i => nth_error (label F) i = Some (taus1', L)) (is ++ [k]) ->
        Forall (fun tau => TypQualLeq F tau Unrestricted = Some true) taus1 ->
        let i := list_max (is ++ [k]) in
        (forall j, j <= i ->
                   exists q, nth_error_plist  (linear F) j = Some q /\
                        QualValid (qual F) q /\
                        QualLeq (qual F) q Unrestricted = Some true) ->
        LocalCtxValid F L ->
        Forall (TypeValid F) (taus1 ++ taus1' ++ [uint32T]) ->
        Forall (TypeValid F) taus2 ->
        LocalCtxValid F (add_local_effects L tl) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (IBrTable (Arrow (taus1 ++ taus1' ++ [uint32T]) taus2,
                                LSig L (add_local_effects L tl)) is k) (Arrow (taus1 ++ taus1' ++ [uint32T]) taus2) (add_local_effects L tl)
  | RetTyp :
      forall C F L taus1 taus1' taus2 tl,
        rettyp F = Some taus1' ->
        Forall (fun '(t, sz) => TypQualLeq F t Unrestricted = Some true) L ->
        Forall (fun tau => TypQualLeq F tau Unrestricted = Some true) taus1 ->
        Forall_plist (fun q => QualValid (qual F) q /\ QualLeq (qual F) q Unrestricted = Some true) (linear F) ->
        LocalCtxValid F L ->
        Forall (TypeValid F) (taus1 ++ taus1') ->
        Forall (TypeValid F) taus2 ->
        LocalCtxValid F (add_local_effects L tl) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (IRet (Arrow (taus1 ++ taus1') taus2, LSig L (add_local_effects L tl)))
          (Arrow (taus1 ++ taus1') taus2) (add_local_effects L tl)
  | GetlocalTyp :
      forall C F L i q t sz b taunew,
        nth_error L i = Some (t, sz) ->
        (b = true -> TypQualLeq F t Unrestricted = Some true) ->
        (b = false -> TypQualGeq F t Linear = Some true) ->
        (b = true -> taunew = t) ->
        (b = false -> taunew = Unit) ->
        TypQual F t = Some q ->
        LocalCtxValid F L ->
        TypeValid F taunew ->
        TypeValid F t ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (IGetLocal (EmptyArrow t, LSig L (set_localtype i taunew sz L)) i q)
          (EmptyArrow t) (set_localtype i taunew sz L)
  | SetlocalTyp :
      forall C F L i t sz tau tausz,
        nth_error L i = Some (t, sz) ->
        TypQualLeq F t Unrestricted = Some true ->
        Some tausz = sizeOfType (type F) tau ->
        SizeValid (size F) tausz ->
        SizeLeq (size F) tausz sz = Some true ->
        LocalCtxValid F L ->
        TypeValid F tau ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (ISetLocal (EmptyRes tau, LSig L (set_localtype i tau sz L)) i) (EmptyRes tau) (set_localtype i tau sz L)
  | GetglobalTyp :
      forall C F L i mut tau,
        nth_error (global C) i = Some (GT mut tau) ->
        LocalCtxValid F L ->
        (* Since this comes from the module context, the type should be valid under an empty function context *)
        TypeValid empty_Function_Ctx tau ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (IGetGlobal (EmptyArrow tau, LSig L L) i) (EmptyArrow tau) L
  | SetglobalTyp :
      forall C F L i tau,
        nth_error (global C) i = Some (GT true tau) ->
        TypQualLeq F tau Unrestricted = Some true ->
        LocalCtxValid F L ->
        (* Since this comes from the module context, the type should be valid under an empty function context *)
        TypeValid empty_Function_Ctx tau ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (ISetGlobal (EmptyRes tau, LSig L L) i) (EmptyRes tau) L
  | CoderefTTyp :
      forall C F L i chi,
        nth_error (table C) i = Some chi ->
        LocalCtxValid F L ->
        (* Since this comes from the module context, the type should be valid under an empty function context *)
        TypeValid empty_Function_Ctx (CoderefT chi) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (ICoderef (EmptyArrow (CoderefT chi), LSig L L) i) (EmptyArrow (CoderefT chi)) L
  | Call_indirectTyp : (* typeset *)
      forall C F L chi is taus1 taus2,
        InstInds chi is = Some (FunT [] (Arrow taus1 taus2)) ->
        LocalCtxValid F L ->
        Forall (TypeValid F) taus1 ->
        TypeValid F (CoderefT chi) ->
        Forall (TypeValid F) taus2 ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (ICallIndirect (Arrow (taus1 ++ [CoderefT chi]) taus2, LSig L L) is) (Arrow (taus1 ++ [CoderefT chi]) taus2) L
  | Call : (* typeset *)
      forall C F L i is chi taus1 taus2,
        nth_error (func C) i = Some chi ->
        (* Since this comes from the module context, the type should be valid under an empty function context *)
        FunTypeValid empty_Function_Ctx chi ->
        InstInds chi is = Some (FunT [] (Arrow taus1 taus2)) ->
        InstIndsValid F chi is ->
        LocalCtxValid F L ->
        Forall (TypeValid F) taus1 ->
        Forall (TypeValid F) taus2 ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (ICall (Arrow taus1 taus2, LSig L L) i is) (Arrow taus1 taus2) L
  | RecFoldType : (* typeset *)
      forall C F L tau rec,
        LocalCtxValid F L ->
        TypeValid F rec ->
        TypeValid F (subst_ext (Kind:=Kind) (ext STyp rec id) tau) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (IRecFold (Arrow [subst_ext (Kind:=Kind) (ext STyp rec id) tau] [rec], LSig L L) rec)
                           (Arrow [subst_ext (Kind:=Kind) (ext STyp rec id) tau] [rec]) L
  | RecUnfoldType : (* typeset *)
      forall C F L tau rec,
        LocalCtxValid F L ->
        TypeValid F rec ->
        TypeValid F (subst_ext (Kind:=Kind) (ext STyp rec id) tau) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (IRecUnfold (Arrow [rec] [subst_ext (Kind:=Kind) (ext STyp rec id) tau], LSig L L))
                           (Arrow [rec] [subst_ext (Kind:=Kind) (ext STyp rec id) tau]) L
  | GroupType : (* typeset *)
      forall C F L i taus,
        length taus = i ->
        LocalCtxValid F L ->
        TypeValid F (ProdT taus) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (IGroup (Arrow taus [ProdT taus], LSig L L) i)
                           (Arrow taus [ProdT taus]) L
  | UngroupTyp : (* typeset *)
      forall C F L taus,
        LocalCtxValid F L ->
        TypeValid F (ProdT taus) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (IUngroup (Arrow [ProdT taus] taus, LSig L L)) (Arrow [ProdT taus] taus) L
  | CapSplitTyp :
      forall C F L l ht,
        LocalCtxValid F L ->
        LocQual F l = Some (QualConst Linear) ->
        TypeValid F (CapT W l ht) ->
        TypeValid F (OwnR l) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (ICapSplit (Arrow [CapT W l ht] [CapT R l ht; OwnR l], LSig L L))
                           (Arrow [CapT W l ht] [CapT R l ht; OwnR l])
                           L
  | CapJoinTyp :
      forall C F L l ht,
        LocalCtxValid F L ->
        LocQual F l = Some (QualConst Linear) ->
        TypeValid F (CapT W l ht) ->
        TypeValid F (OwnR l) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (ICapJoin (Arrow [CapT R l ht; OwnR l] [CapT W l ht], LSig L L))
                           (Arrow [CapT R l ht; OwnR l] [CapT W l ht])
                           L
  | RefDemoteTyp : (* typeset *)
      forall C F L l ht,
        LocalCtxValid F L ->
        LocQual F l = Some (QualConst Unrestricted) ->
        TypeValid F (RefT W l ht) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (IRefDemote (Arrow [RefT W l ht] [RefT R l ht], LSig L L))
                           (Arrow [RefT W l ht] [RefT R l ht])
                           L
  | MemPackTyp :
      forall C F L tau taurho q l,
        subst_ext (Kind:=Kind) (ext SLoc l id) taurho = tau ->
        LocalCtxValid F L ->
        TypeValid F tau ->
        TypeValid F (ExLoc q taurho) ->
        LocValid (location F) l ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (IMemPack (Arrow [tau] [ExLoc q taurho], LSig L L) l)
                           (Arrow [tau] [ExLoc q taurho])
                           L
  | MemUnpackTyp :
      forall C F L taus1 taus2 qrho taurho es tl L'',
        let tf := Arrow taus1 taus2 in
        let tf' := Arrow (taus1 ++ [ExLoc qrho taurho]) taus2 in
        let L' := add_local_effects L tl in
        let F1 := update_label_ctx ((taus2, L'') :: (label F)) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
        let F3 := subst_ext (weak SLoc) (update_location_ctx (qrho :: location F) F2) in
        HasTypeInstrs
          C F3
          (subst_ext (weak SLoc) L)
          es
          (Arrow (subst_ext (weak SLoc) taus1 ++ [taurho]) (subst_ext (weak SLoc) taus2))
          (subst_ext (weak SLoc) L') ->
        LCEffEqual (size F) L' L'' ->
        LocalCtxValid F L'' ->
        LocalCtxValid F L ->
        Forall (TypeValid F) taus1 ->
        TypeValid F (ExLoc qrho taurho) ->
        Forall (TypeValid F) taus2 ->
        LocalCtxValid F L' ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (IMemUnpack (tf', LSig L L') tf tl es) tf' L'
  | StructMallocTyp : (* typeset *)
      forall C F L szs q taus,
        Forall2 (fun tau sz => exists tausz, sizeOfType (type F) tau = Some tausz /\
                   SizeValid (size F) tausz /\
                   SizeLeq (size F) tausz sz = Some true) taus szs ->
        Forall (SizeValid (size F)) szs ->
        forallb (NoCapsTyp (heapable F)) taus = true ->
        QualValid (qual F) q ->
        let psi := StructType (combine (subst_ext (Kind:=Kind) (weak SLoc) taus) szs) in
        let tf := Arrow taus [ExLoc q (RefT W (LocV 0) psi)] in
        LocalCtxValid F L ->
        Forall (TypeValid F) taus ->
        TypeValid F (ExLoc q (RefT W (LocV 0) psi)) ->
        QualValid (qual F) (get_hd (linear F)) ->
        HasTypeInstr C F L (IStructMalloc (tf, LSig L L) szs q) tf L
  | StructFreeTyp : (* typeset *)
      forall C F L tauszs l,
        TypQualGeq F (RefT W l (StructType tauszs)) Linear = Some true ->
        Forall (fun '(tau, _) => TypQualLeq F tau Unrestricted = Some true) tauszs ->
        LocalCtxValid F L ->
        TypeValid F (RefT W l (StructType tauszs)) ->
        QualValid (qual F) (get_hd (linear F)) ->
        let tf := Arrow [RefT W l (StructType tauszs)] [] in 
        HasTypeInstr C F L (IStructFree (tf, LSig L L)) tf L
  | TStructGet : forall C F L n taus szs tau l cap,
      let psi := StructType (combine taus szs) in
      length taus = length szs ->
      nth_error taus n = Some tau ->
      TypQualLeq F tau Unrestricted = Some true ->
      LocalCtxValid F L ->
      TypeValid F (RefT cap l psi) ->
      TypeValid F tau ->
      QualValid (qual F) (get_hd (linear F)) ->
      HasTypeInstr C F L (IStructGet (Arrow [RefT cap l psi] [RefT cap l psi; tau], LSig L L) n)
        (Arrow [RefT cap l psi] [RefT cap l psi; tau])
        L
  | StructSetTyp :
      forall C F L taus szs tau taus' l n tau_old sz tau_sz,
        let psi := StructType (combine taus szs) in
        length taus = length szs ->
        ReplaceAtIdx n taus tau = Some (taus', tau_old) ->
        TypQualLeq F tau_old Unrestricted = Some true ->
        nth_error szs n = Some sz ->
        sizeOfType (type F) tau = Some tau_sz ->
        SizeValid (size F) tau_sz ->
        SizeLeq (size F) tau_sz sz = Some true ->
        TypeValid F tau ->
        NoCapsTyp (heapable F) tau = true ->
        (TypQualGeq F tau Linear = Some true \/
         tau = tau_old) ->
        let psi' := StructType (combine taus' szs) in
        LocalCtxValid F L ->
        TypeValid F (RefT W l psi) ->
        TypeValid F (RefT W l psi') ->
        QualValid (qual F) (get_hd (linear F)) ->
        let tf := Arrow [RefT W l psi; tau]
                        [RefT W l psi'] in
        HasTypeInstr C F L (IStructSet (tf, LSig L L) n) tf L
  | StructSwapTyp :
      forall C F L taus szs tau taus' l n tau_old sz tau_sz,
        let psi := StructType (combine taus szs) in
        length taus = length szs ->
        ReplaceAtIdx n taus tau = Some (taus', tau_old) ->
        nth_error szs n = Some sz ->
        sizeOfType (type F) tau = Some tau_sz ->
        SizeValid (size F) tau_sz ->
        SizeLeq (size F) tau_sz sz = Some true ->
        TypeValid F tau ->
        NoCapsTyp (heapable F) tau = true ->
        (TypQualGeq F tau Linear = Some true \/
         tau = tau_old) ->
        let psi' := StructType (combine taus' szs) in
        LocalCtxValid F L ->
        TypeValid F (RefT W l psi) ->
        TypeValid F (RefT W l psi') ->
        TypeValid F tau_old ->
        QualValid (qual F) (get_hd (linear F)) ->
        let tf := Arrow [RefT W l psi; tau] [RefT W l psi'; tau_old] in
        HasTypeInstr C F L (IStructSwap (tf, LSig L L) n)
                           tf 
                           L
  | VariantMallocTyp : (* typeset *)
      forall C F L n taus q tau,
        Forall (TypeValid F) taus ->
        QualValid (qual F) q ->
        nth_error taus n = Some tau ->
        TypQualLeq F tau q = Some true ->
        forallb (NoCapsTyp (heapable F)) taus = true ->
        let psi := VariantType (subst_ext (Kind:=Kind) (weak SLoc) taus) in
        LocalCtxValid F L ->
        TypeValid F (ExLoc q (RefT W (LocV 0) psi)) ->
        QualValid (qual F) (get_hd (linear F)) ->
                           let tf := (Arrow [tau] [ExLoc q (RefT W (LocV 0) psi)]) in 
        HasTypeInstr C F L (IVariantMalloc (tf, LSig L L) n taus q)
                     tf
                           L
  | VariantCaseTypUnr : 
      forall C F L taus1 taus2 tausv q' q qv cap l es tl L'',
        QualLeq (qual F) qv q' = Some true ->
        QualLeq (qual F) (get_hd (linear F)) q' = Some true ->
        let tf := Arrow taus1 taus2 in
        let L' := add_local_effects L tl in
        let F1 := update_label_ctx ((taus2, L'') :: (label F)) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (set_hd q' (linear F))) F1 in
        Forall2 (fun es tau => HasTypeInstrs C F2 L es (Arrow (taus1 ++ [tau]) taus2) L') es tausv ->
        Forall (fun tau => TypQualLeq F tau Unrestricted = Some true) tausv ->
        QualLeq (qual F) q Unrestricted = Some true ->
        QualValid (qual F) q ->
        QualValid (qual F) qv ->
        QualValid (qual F) q' ->
        QualValid (qual F) (get_hd (linear F)) ->
        LCEffEqual (size F) L' L'' ->
        LocalCtxValid F L ->
        LocalCtxValid F L'' ->
        Forall (TypeValid F) taus1 ->
        Forall (TypeValid F) taus2 ->
        LocQual F l = Some qv ->
        TypeValid F (RefT cap l (VariantType tausv)) ->
        LocalCtxValid F L' ->
        QualValid (qual F) (get_hd (linear F)) ->
        let tf' := Arrow (taus1 ++ [RefT cap l (VariantType tausv)])
               ([RefT cap l (VariantType tausv)] ++ taus2) in
        HasTypeInstr C F L (IVariantCase (tf', LSig L L') q (VariantType tausv) tf tl es) tf' L'
  | VariantCaseTypLin : (* typeset *)
      forall C F L taus1 taus2 tausv q qv l es tl L'',
        let tf := Arrow taus1 taus2 in
        let L' := add_local_effects L tl in
        let F1 := update_label_ctx ((taus2, L'') :: (label F)) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
        Forall2 (fun es tau => HasTypeInstrs C F2 L es (Arrow (taus1 ++ [tau]) taus2) L') es tausv ->
        QualLeq (qual F) Linear q = Some true ->
        QualLeq (qual F) Linear qv = Some true ->
        QualValid (qual F) q ->
        QualValid (qual F) qv ->
        LCEffEqual (size F) L' L'' ->
        LocalCtxValid F L ->
        LocalCtxValid F L'' ->
        Forall (TypeValid F) taus1 ->
        LocQual F l = Some qv ->
        TypeValid F (RefT W l (VariantType tausv)) ->
        Forall (TypeValid F) taus2 ->
        LocalCtxValid F L' ->
        QualValid (qual F) (get_hd (linear F)) ->
        let tf' := Arrow (taus1 ++ [RefT W l (VariantType tausv)]) taus2 in 
        HasTypeInstr C F L (IVariantCase (tf', LSig L L') q (VariantType tausv) tf tl es) tf' L'
  | ArrayMallocTyp : (* typeset *)
      forall C F L tau q,
        let psi := (ArrayType (subst_ext (Kind:=Kind) (weak SLoc) tau)) in
        QualValid (qual F) q ->
        NoCapsTyp (heapable F) tau = true ->
        TypQualLeq F tau Unrestricted = Some true ->
        LocalCtxValid F L ->
        TypeValid F tau ->
        TypeValid F uint32T  ->
        TypeValid F (ExLoc q (RefT W (LocV 0) psi)) ->
        QualValid (qual F) (get_hd (linear F)) ->
        let tf := Arrow [tau; uint32T] [ExLoc q (RefT W (LocV 0) psi)] in
        HasTypeInstr C F L (IArrayMalloc (tf, LSig L L) q) tf L
  | ArrayGetTyp : (* typeset *)
      forall C F L cap l tau,
        TypQualLeq F tau Unrestricted = Some true ->
        LocalCtxValid F L ->
        TypeValid F (RefT cap l (ArrayType tau)) ->
        TypeValid F tau ->
        QualValid (qual F) (get_hd (linear F)) ->
        let tf := Arrow [RefT cap l (ArrayType tau); uint32T] [RefT cap l (ArrayType tau); tau] in
        HasTypeInstr C F L (IArrayGet (tf, LSig L L)) tf L
  | ArraySetTyp : (* typeset *)
      forall C F L l tau,
        TypQualLeq F tau Unrestricted = Some true ->
        NoCapsTyp (heapable F) tau = true ->
        LocalCtxValid F L ->
        TypeValid F (RefT W l (ArrayType tau)) ->
        TypeValid F tau ->
        QualValid (qual F) (get_hd (linear F)) ->
        let tf := Arrow [RefT W l (ArrayType tau); uint32T; tau] [RefT W l (ArrayType tau)] in
        HasTypeInstr C F L (IArraySet (tf, LSig L L)) tf L
  | ArrayFreeTyp : (* typeset *)
      forall C F L tau q l,
        TypQualLeq F tau Unrestricted = Some true ->
        LocQual F l = Some q ->
        QualValid (qual F) q ->
        QualLeq (qual F) Linear q = Some true ->
        LocalCtxValid F L ->
        TypeValid F (RefT W l (ArrayType tau)) ->
        QualValid (qual F) (get_hd (linear F)) ->
        let tf := Arrow [RefT W l (ArrayType tau)] [] in 
        HasTypeInstr C F L (IArrayFree (tf, LSig L L)) tf L
  | ExistPackTyp :
      forall C F L tau htau sz q szp,
        TypQual F tau = Some q ->
        TypQualLeq F htau q = Some true ->
        QualValid (qual F) q ->
        sizeOfType (type F) tau = Some szp ->
        SizeLeq (size F) szp sz = Some true ->
        SizeValid (size F) szp ->
        SizeValid (size F) sz ->
        TypeValid F tau ->
        TypeValid (subst_ext (weak subst.STyp) (update_type_ctx ((sz, q, Heapable) :: (type F)) F)) htau ->
        NoCapsTyp (heapable F) tau = true ->
        NoCapsTyp (heapable (update_type_ctx ((sz, q, Heapable) :: (type F)) F)) htau = true ->
        let tau' := subst_ext (Kind:=Kind) (ext STyp tau id) htau in
        let psi := Ex sz q (subst_ext (Kind:=Kind) (weak SLoc) htau) in
        LocalCtxValid F L ->
        TypeValid F tau' ->
        TypeValid F (ExLoc q (RefT W (LocV 0) psi)) ->
        QualValid (qual F) (get_hd (linear F)) ->
        let tf := Arrow [tau'] [ExLoc q (RefT W (LocV 0) psi)] in 
        HasTypeInstr C F L (IExistPack (tf, LSig L L) tau (Ex sz q htau) q) tf L
  | ExistUnpackTypUnr : (* typeset *)
      forall C F L cap taus1 taus2 tau q' q qv l es tl sz qα q_ex L'',
        let tf := Arrow taus1 taus2 in
        let L' := add_local_effects L tl in
        let F1 := update_label_ctx ((taus2, L'') :: (label F)) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (set_hd q' (linear F))) F1 in
        let F3 := subst_ext (weak STyp) (update_type_ctx ((sz, qα, Heapable) :: (type F2)) F2) in
        HasTypeInstrs C F3 (subst_ext (weak STyp) L) es
                           (Arrow (subst_ext (weak STyp) taus1 ++ [tau])
                                  (subst_ext (weak STyp) taus2)) (subst_ext (weak STyp) L') ->
        TypQual F tau = Some q_ex ->
        QualLeq (qual F) q_ex Unrestricted = Some true ->
        QualLeq (qual F) q Unrestricted = Some true ->
        QualLeq (qual F) qv q' = Some true ->
        QualLeq (qual F) (get_hd (linear F)) q' = Some true ->
        QualValid (qual F) q ->
        QualValid (qual F) qv ->
        QualValid (qual F) q' ->
        QualValid (qual F) (get_hd (linear F)) ->
        LCEffEqual (size F) L' L'' ->
        LocalCtxValid F L ->
        LocalCtxValid F L'' ->
        Forall (TypeValid F) taus1 ->
        Forall (TypeValid F) taus2 ->
        LocQual F l = Some qv ->
        TypeValid F (RefT cap l (Ex sz qα tau)) ->
        LocalCtxValid F L' ->
        QualValid (qual F) (get_hd (linear F)) ->
        let tf' := Arrow (taus1 ++ [RefT cap l (Ex sz qα tau)]) ([RefT cap l (Ex sz qα tau)] ++ taus2) in
        HasTypeInstr C F L (IExistUnpack (tf', LSig L L') q (Ex sz qα tau) tf tl es) tf' L'
  | ExistUnpackTypLin : (* typeset *)
      forall C F L taus1 taus2 tau q qv l es tl sz qα L'',
        let tf := Arrow taus1 taus2 in
        let L' := add_local_effects L tl in
        let F1 := update_label_ctx ((taus2, L'') :: (label F)) F in
        let F2 := update_linear_ctx (Cons_p (QualConst Unrestricted) (linear F)) F1 in
        let F3 := subst_ext (weak STyp)  (update_type_ctx ((sz, qα, Heapable) :: (type F2)) F2) in
        HasTypeInstrs C F3 (subst_ext (weak STyp) L) es
                           (Arrow (subst_ext (weak STyp) taus1 ++ [tau])
                                  (subst_ext (weak STyp) taus2)) (subst_ext (weak STyp) L') ->
        QualLeq (qual F) Linear q = Some true ->
        QualLeq (qual F) Linear qv = Some true ->
        QualValid (qual F) q ->
        QualValid (qual F) qv ->
        LCEffEqual (size F) L' L'' ->
        LocalCtxValid F L ->
        LocalCtxValid F L'' ->
        Forall (TypeValid F) taus1 ->
        Forall (TypeValid F) taus2 ->
        LocQual F l = Some qv ->
        TypeValid F (RefT W l (Ex sz qα tau)) ->
        LocalCtxValid F L' ->
        QualValid (qual F) (get_hd (linear F)) ->
        let tf := Arrow (taus1 ++ [RefT W l (Ex sz qα tau)]) taus2 in
        HasTypeInstr C F L (IExistUnpack (tf, LSig L L') q (Ex sz qα tau) tf tl es) tf L'
  | RefSplitTyp : (* typeset *)
      forall C F L cap l ht,
        TypQualLeq F (RefT cap l ht) Linear = Some true ->
        LocalCtxValid F L ->
        TypeValid F (RefT cap l ht) ->
        TypeValid F (CapT cap l ht) ->
        TypeValid F (PtrT l) ->
        QualValid (qual F) (get_hd (linear F)) ->
        let tf := Arrow [RefT cap l ht] [CapT cap l ht; PtrT l] in
        HasTypeInstr C F L (IRefSplit (tf, LSig L L)) tf L
  | RefJoinTyp : (* typeset *)
      forall C F L cap l ht,
        LocalCtxValid F L ->
        TypeValid F (RefT cap l ht) ->
        TypeValid F (CapT cap l ht) ->
        TypeValid F (PtrT l) ->
        QualValid (qual F) (get_hd (linear F)) ->
        let tf := Arrow [CapT cap l ht; PtrT l] [RefT cap l ht] in
        HasTypeInstr C F L (IRefJoin (tf, LSig L L)) tf L
  with HasTypeInstrs :
    Module_Ctx -> Function_Ctx ->
    Local_Ctx -> list (instr TyAnn) -> ArrowType -> Local_Ctx -> Prop :=
  | EmptyTyp: forall C F L ts,
      LocalCtxValid F L ->
      Forall (TypeValid F) ts ->
      QualValid (qual F) (get_hd (linear F)) ->
      HasTypeInstrs C F L [] (Arrow ts ts) L
  | ConsTyp :
      forall C F L1 L2 L3 es e tau1 tau2 tau3,
      HasTypeInstr C F L1 e (Arrow tau1 tau2) L2 ->
      HasTypeInstrs C F L2 es (Arrow tau2 tau3) L3 ->
      HasTypeInstrs C F L1 (e :: es) (Arrow tau1 tau3) L3
  | FrameTyp : 
      forall C F L L' qf es taus taus1 taus2 Flin_hd,
        get_hd (linear F) = Flin_hd ->
        Forall (fun t => exists q,
          TypQual F t = Some q /\
          QualLeq (qual F) q qf = Some true) taus ->
        QualLeq (qual F) Flin_hd qf = Some true ->
        let F' := update_linear_ctx (set_hd qf (linear F)) F in
        HasTypeInstrs C F' L es (Arrow taus1 taus2) L' ->
        QualValid (qual F) (get_hd (linear F)) ->
        QualValid (qual F) qf ->
        Forall (TypeValid F) taus ->
        HasTypeInstrs C F L es (Arrow (taus ++ taus1) (taus ++ taus2)) L'
  | ChangeBegLocalTyp :  (* typeset *)
      forall C F L L1 es taus1 taus2 L',
        LocalCtxValid F L1 ->
        LCEffEqual (size F) L L1 ->
        HasTypeInstrs C F L es (Arrow taus1 taus2) L' ->
        HasTypeInstrs C F L1 es (Arrow taus1 taus2) L'
  | ChangeEndLocalTyp :  (* typeset *)
      forall C F L es taus1 taus2 L' L1,
        LocalCtxValid F L1 ->
        LCEffEqual (size F) L' L1 ->
        HasTypeInstrs C F L es (Arrow taus1 taus2) L' ->
        HasTypeInstrs C F L es (Arrow taus1 taus2) L1
  .

  Scheme HasTypeInstr_mind := Induction for HasTypeInstr Sort Prop
    with HasTypeInstrs_mind := Induction for HasTypeInstrs Sort Prop.

  Inductive HasTypeGlob (C: Module_Ctx) : Glob TyAnn -> GlobalType -> list ex -> Prop :=
  | GlobMutTyp :
      forall pt es,
        HasTypeInstrs C empty_Function_Ctx [] es (Arrow [] [pt]) [] ->
        HasTypeGlob C (GlobMut pt es) (GT true pt) []
  | GlobTyp :
      forall ex pt es,
        HasTypeInstrs C empty_Function_Ctx [] es (Arrow [] [pt]) [] ->
        HasTypeGlob C (GlobEx ex pt es) (GT false pt) ex
  | GlobIm :
      forall ex pt im,
        HasTypeGlob C (GlobIm ex pt im) (GT false pt) ex.

  Definition combine_i {A} (xs : list A) : list (A * nat) :=
    (fix aux (xs : list A) (i : nat) :=
         match xs with
         | nil => []
         | cons x xs => (x, i) :: aux xs (i + 1)
         end) xs 0.

  Definition glob_typ {A} (g : Glob A) :=
    match g with
    | GlobMut pt es => GT true pt
    | GlobEx ex pt es => GT false pt
    | term.GlobIm ex pt im => GT false pt
    end.

  Definition fun_typ {A} (f : Func A) : FunType :=
    match f with
    | Fun x_ ft _ _ => ft
    end.

  Definition table_types (tb : Table) (tfs : list FunType) :=
    (fix aux tb :=
       match tb with
       | nil => []
       | cons t tb =>
         let tf :=
             match nth_error tfs t with
             | None => FunT [] (Arrow [] []) (* perhaps needs some WF so that always exists *)
             | Some tf => tf
             end
         in tf :: aux tb
       end) tb.
  
      
  (* Module Instances are typed in the empty store typing *)
  (*
  Inductive HasTypeInstance (I : InstanceTyping) : MInst -> Module_Ctx -> Prop :=
  | InstT :
      forall cls gs ts fts1 tgs fts2,
        Forall2 (fun c ft => HasTypeClosure (EmptyStoreTyping I) c ft) cls fts1 ->
        Forall2 (fun c ft => HasTypeClosure (EmptyStoreTyping I) c ft) ts fts2 ->
        
        Forall2 (fun '(mut, v) tg => exists pt, HasTypeValue (EmptyStoreTyping I)
                                                         empty_Function_Ctx v (QualT pt Unrestricted)
                                            /\ tg = GT mut pt) gs tgs ->
        let C := Build_Module_Ctx fts1 tgs fts2 in
        HasTypeInstance I (Build_MInst cls gs ts) C.
*)
                 
End Typing.
