From stdpp Require Import base decidable.
From Coq Require Import Numbers.BinNums NArith List.

Require Import RichWasm.syntax RichWasm.util.debruijn.

Import ListNotations.

Inductive ind : Set :=
| SMem
| SRep
| SSize
| SType.

Instance ind_eq_dec : EqDecision ind := ltac:(solve_decision).

Definition skind (i: ind) :=
  match i with
  | SMem => memory
  | SRep => representation
  | SSize => size
  | SType => type
  end.

#[global]
Instance Varskind : Var skind :=
  fun i =>
  match i with
  | SMem => MemVar
  | SRep => VarR
  | SSize => VarS
  | SType => VarT
  end.

Definition subst'_memory (su : Subst' skind) (l : memory) : memory :=
  match l with
  | MemVar x => get_var' SMem x su
  | _ => l
  end.

Fixpoint subst'_representation (su : Subst' skind) (ρ : representation) : representation :=
  match ρ with 
  | VarR x => get_var' SRep x su
  | SumR ρs => SumR (map (subst'_representation su) ρs)
  | ProdR ρs => ProdR (map (subst'_representation su) ρs)
  | PrimR rep => PrimR rep
  end.

Fixpoint subst'_size (su : Subst' skind) (σ : size) : size :=
  match σ with
  | VarS x => get_var' SSize x su
  | SumS σs => SumS (map (subst'_size su) σs)
  | ProdS σs => ProdS (map (subst'_size su) σs)
  | RepS ρ => RepS (subst'_representation su ρ)
  | ConstS c => ConstS c
  end.

Definition subst'_sizity (su: Subst' skind) (ζ: sizity) : sizity :=
  match ζ with
  | Sized σ => Sized (subst'_size su σ)
  | Unsized => Unsized
  end.

Definition subst'_kind (su : Subst' skind) (κ: kind) : kind :=
  match κ with
  | VALTYPE ρ γ => VALTYPE (subst'_representation su ρ) γ
  | MEMTYPE ζ μ γ => MEMTYPE (subst'_sizity su ζ) (subst'_memory su μ) γ
  end.

Definition subst'_quant (su : Subst' skind) (q : quantifier) : quantifier :=
  match q with
  | QMem => QMem
  | QRep => QRep
  | QSize => QSize
  | QType κ => QType (subst'_kind su κ)
  end.

Definition skind_of_quant q :=
  match q with
  | QMem => SMem
  | QRep => SRep
  | QSize => SSize
  | QType κ => SType
  end.

Definition under_quant' (q : quantifier) : Subst' skind -> Subst' skind :=
  under' (skind_of_quant q).

Fixpoint subst'_quants (su : Subst' skind) (kvs : list quantifier) : list quantifier :=
  match kvs with
  | [] => []
  (** quantifiers is a telescope, not parallel binding: each var is in
       scope for all kinds that occur later in the list *)
  | kv :: kvs => subst'_quant su kv :: subst'_quants (under_quant' kv su) kvs
  end.

(* foldl and foldr are equivalent here; see debruijn.under_comm *)
Fixpoint under_quants' (kvs : list quantifier) (su : Subst' skind) :=
  match kvs with
  | [] => su
  | kv :: kvs => under_quant' kv (under_quants' kvs su)
  end.

Fixpoint subst'_type (su : Subst' skind) (t : type) {struct t} : type :=
  match t with
  | VarT x => get_var' SType x su
  | NumT ν => NumT ν
  | SumT τs => SumT (map (subst'_type su) τs)
  | ProdT τs => ProdT (map (subst'_type su) τs)
  | ArrayT τ => ArrayT (subst'_type su τ)
  | RefT μ τ => RefT (subst'_memory su μ) (subst'_type su τ)
  | GCPtrT τ => GCPtrT (subst'_type su τ)
  | CodeRefT ϕ => CodeRefT (subst'_function_type su ϕ)
  | RepT ρ τ => RepT (subst'_representation su ρ) (subst'_type su τ)
  | PadT σ τ => PadT (subst'_size su σ) (subst'_type su τ)
  | SerT τ => SerT (subst'_type su τ)
  | ExT δ τ => ExT (subst'_quant su δ) (subst'_type (under' (skind_of_quant δ) su) τ)
  | RecT τ => RecT (subst'_type (under' SType su) τ)
  end
with subst'_arrow_type (su : Subst' skind) (χ : arrow_type) {struct χ} : arrow_type :=
  match χ with
  | ArrowT ts1 ts2 =>
    ArrowT
      (map (subst'_type su) ts1)
      (map (subst'_type su) ts2)
  end
with subst'_function_type (su : Subst' skind) (ϕ : function_type) {struct ϕ} : function_type :=
  match ϕ with
  | FunT δs χ =>
    FunT (subst'_quants su δs)
         (subst'_arrow_type (under_quants' δs su) χ)
  end.

Definition subst'_rwasm (i : ind) : Subst' skind -> skind i -> skind i :=
  match i with
  | SMem => subst'_memory
  | SRep => subst'_representation
  | SSize => subst'_size
  | SType => subst'_type
  end.

(** Solves easy subst'_ok obligations
    TODO is this really the right automation for this thing *)
Ltac subst'_ok n :=
  let e := fresh "e" with f := fresh "f" with g := fresh "g" in
  intros e; split; [|intros f g]; induction e; cbn; crush n.

#[global]
Instance BindVar_rwasm : BindVar skind.
Proof. refine {| subst' := subst'_rwasm |}; abstract (intros []; reflexivity). Defined.

Lemma subst'_memory_ok : subst'_ok subst'_memory. 
Proof. subst'_ok 5. Qed.

Lemma subst'_representation_ok : subst'_ok subst'_representation.
Proof. 
  (* TODO: Need nested induction scheme to deal with [list representation] subgoals. *)
  intros e.
  split; [|intros f g]; induction e; cbn; try crush 15; auto.
Admitted.

Lemma subst'_size_ok : subst'_ok subst'_size. 
Proof. 
  (* TODO: Need nested/mutual induction scheme to deal with [list size] and [representation] subgoals. *)
  intros e.
  split; [|intros f g]; induction e; cbn; try crush 15; auto.
Admitted.

Global Hint Resolve subst'_memory_ok subst'_representation_ok subst'_size_ok : OKDB.
Tactic Notation "pose_ok_proofs'" :=
  pose_ok_proofs';
  pose proof subst'_memory_ok;
  pose proof subst'_representation_ok;
  pose proof subst'_size_ok.
Ltac pose_ok_proofs ::= pose_ok_proofs'.

Lemma map_pair_eta {A B} (xys : list (A * B)) : xys = combine (map fst xys) (map snd xys).
Proof. induction xys as [| [x y] ? ?]; cbn in *; congruence. Qed.

Lemma map_combine {A B C D} (f : A -> C) (g : B -> D) (xs : list A)
  : forall ys, map (fun '(x, y) => (f x, g y)) (combine xs ys) = combine (map f xs) (map g ys).
Proof. induction xs; destruct ys; cbn; intuition congruence. Qed.

Lemma Forall_comp_map {A B} (P : B -> Prop) (f : A -> B) xs :
  Forall (fun x => P (f x)) xs ->
  Forall P (map f xs).
Proof. induction xs; cbn; auto; inversion 1; intuition eauto. Qed.

Lemma subst'_sizity_ok : subst'_ok subst'_sizity.
Proof.
Admitted.
Global Hint Resolve subst'_sizity_ok : OKDB.
Tactic Notation "pose_ok_proofs'" := pose_ok_proofs'; pose proof subst'_sizity_ok.
Ltac pose_ok_proofs ::= pose_ok_proofs'.

Lemma subst'_kind_ok : subst'_ok subst'_kind.
Proof.
  intros k1; intros_ok_at; destruct k1; cbn; now simpl_ok.
Qed.
Global Hint Resolve subst'_kind_ok : OKDB.
Tactic Notation "pose_ok_proofs'" := pose_ok_proofs'; pose proof subst'_kind_ok.
Ltac pose_ok_proofs ::= pose_ok_proofs'.

Lemma subst'_quant_ok : subst'_ok subst'_quant.
Proof. intros kv; intros_ok_at; destruct kv; cbn; now simpl_ok. Qed.
Global Hint Resolve subst'_quant_ok : OKDB.
Tactic Notation "pose_ok_proofs'" := pose_ok_proofs'; pose proof subst'_quant_ok.
Ltac pose_ok_proofs ::= pose_ok_proofs'.

Lemma under_quant'_var' kv : under_quant' kv var' = var'.
Proof. destruct kv; cbn; unfold under_quant'; cbn; now autorewrite with SubstDB. Qed.

Lemma under_quants'_var' kvs : under_quants' kvs var' = var'.
Proof. induction kvs; cbn; auto. now rewrite IHkvs, under_quant'_var'. Qed.

Lemma under_quant'_comp' kv f g :
  under_quant' kv (f ∙' g) = under_quant' kv f ∙' under_quant' kv g.
Proof. destruct kv; unfold under_quant'; cbn; now autorewrite with SubstDB. Qed.

Lemma under_quants'_comp' kvs f g :
  under_quants' kvs (f ∙' g) = under_quants' kvs f ∙' under_quants' kvs g.
Proof. induction kvs; cbn; [auto|now rewrite IHkvs, under_quant'_comp']. Qed.

Lemma under_quant'_subst'_quant s kv t :
  under_quant' (subst'_quant s kv) t = under_quant' kv t.
Proof. destruct kv; reflexivity. Qed.

Lemma under_quants'_subst'_quants s kvs t :
  under_quants' (subst'_quants s kvs) t = under_quants' kvs t.
Proof.
  revert s; induction kvs; intros s; [easy|].
  cbn; now rewrite !IHkvs, under_quant'_subst'_quant.
Qed.

Hint Rewrite
     under_quants'_var' under_quant'_var'
     under_quant'_comp' under_quants'_comp'
     under_quant'_subst'_quant under_quants'_subst'_quants
  : SubstDB.

Lemma subst'_quants_ok : subst'_ok subst'_quants.
Proof. intros qs; split; induction qs; intros; cbn; now simpl_ok. Qed.
Global Hint Resolve subst'_quants_ok : OKDB.
Tactic Notation "pose_ok_proofs'" := pose_ok_proofs'; pose proof subst'_quants_ok.
Ltac pose_ok_proofs ::= pose_ok_proofs'.

Lemma subst'_type_mut_ok
  : subst'_ok subst'_type /\
    subst'_ok subst'_function_type /\
    subst'_ok subst'_arrow_type.
Proof.
  (* TODO : mutual induction principle. *)
  (*
  apply Typ_Fun_Arrow_Heap_ind.
  all: intros; intros_ok_at; elim_ok_at; cbn; try now simpl_ok.
  Local Ltac Forall_fst :=
    match goal with
    | H : Forall ?P _ |- _ =>
      replace P with (fun ts => subst'_ok_at subst'_typ (@fst _ Size ts)) in H
        by (apply fext; intros [??]; reflexivity);
      apply Forall_comp_map in H
    end.
  (* TODO clean up the reasoning in these proofs *)
  - rewrite (map_pair_eta l), map_combine.
    replace (subst'_size var') with (fun s : Size => s) by (feql; now simpl_ok).
    rewrite map_id; repeat feql.
    Forall_fst. now simpl_ok.
  - rewrite map_map; cbn; f_equal.
    rewrite (map_pair_eta l), map_combine.
    match goal with
    | |- context [map ?fn (combine _ _)] =>
      replace fn with (fun '(x, y) => (subst'_typ f (subst'_typ g x), subst'_size f (subst'_size g y)))
        by (let xy := fresh in fext xy; now destruct xy)
    end.
    rewrite (map_combine
               (fun t => subst'_typ f (subst'_typ g t))
               (fun s => subst'_size f (subst'_size g s))).
    f_equal; [|feql; now simpl_ok].
    Forall_fst. rewrite <- map_map. now simpl_ok.
*)
Admitted.

Corollary subst'_type_ok : subst'_ok subst'_type. Proof. apply subst'_type_mut_ok. Qed.
Corollary subst'_function_type_ok : subst'_ok subst'_function_type. Proof. apply subst'_type_mut_ok. Qed.
Corollary subst'_arrow_type_ok : subst'_ok subst'_arrow_type. Proof. apply subst'_type_mut_ok. Qed.
Global Hint Resolve
     subst'_type_ok
     subst'_function_type_ok
     subst'_arrow_type_ok
  : OKDB.
Tactic Notation "pose_ok_proofs'" :=
  pose_ok_proofs';
  pose proof subst'_type_ok;
  pose proof subst'_function_type_ok;
  pose proof subst'_arrow_type_ok.
Ltac pose_ok_proofs ::= pose_ok_proofs'.

#[global]
Instance BindRWasm : Bind skind. Proof. apply mkBind; destruct i; auto with OKDB. Defined.

Ltac mkBindExt := eapply mkBindExt; eauto with OKDB.

#[global]
Instance BindExtMem : BindExt skind memory := ltac:(mkBindExt).
#[global]
Instance BindExtRep : BindExt skind representation := ltac:(mkBindExt).
#[global]
Instance BindExtSize : BindExt skind size := ltac:(mkBindExt).
#[global]
Instance BindExtType : BindExt skind type := ltac:(mkBindExt).
#[global]
Instance BindExtQuant : BindExt skind quantifier := ltac:(mkBindExt).
#[global]
Instance BindExtQuants : BindExt skind (list quantifier) := ltac:(mkBindExt).

#[global]
Instance BindExtFunType : BindExt skind function_type := ltac:(mkBindExt).
#[global]
Instance BindExtArrowType : BindExt skind arrow_type := ltac:(mkBindExt).

Definition subst'_types s := map (subst'_type s).

Lemma subst'_types_ok : subst'_ok subst'_types.
Proof. unfold subst'_types. auto with OKDB. Qed.
Global Hint Resolve subst'_types_ok : OKDB.
Tactic Notation "pose_ok_proofs'" := pose_ok_proofs'; pose proof subst'_types_ok.
Ltac pose_ok_proofs ::= pose_ok_proofs'.

#[global]
Instance BindExtTypes : BindExt skind (list type) := ltac:(mkBindExt).

Definition subst'_index (su : Subst' skind) (ix : index) : index :=
  match ix with
  | MemI μ => MemI (subst'_memory su μ)
  | RepI ρ => RepI (subst'_representation su ρ)
  | SizeI σ => SizeI (subst'_size su σ)
  | TypeI τ => TypeI (subst'_type su τ)
  end.

Lemma subst'_index_ok : subst'_ok subst'_index.
Proof. intros []; intros_ok_at; cbn; now simpl_ok. Qed.
Global Hint Resolve subst'_index_ok : OKDB.
Tactic Notation "pose_ok_proofs'" := pose_ok_proofs'; pose proof subst'_index_ok.
Ltac pose_ok_proofs ::= pose_ok_proofs'.

#[global]
Instance BindExtIndex : BindExt skind index := ltac:(mkBindExt).

Definition subst'_indices s := map (subst'_index s).

Lemma subst'_indices_ok : subst'_ok subst'_indices.
Proof. unfold subst'_indices; auto with OKDB. Qed.
Global Hint Resolve subst'_indices_ok : OKDB.
Tactic Notation "pose_ok_proofs'" := pose_ok_proofs'; pose proof subst'_indices_ok.
Ltac pose_ok_proofs ::= pose_ok_proofs'.

#[global]
Instance BindExtIndices : BindExt skind (list index) := ltac:(mkBindExt).

Definition subst'_local_effect su : local_effect -> local_effect :=
  map (fun '(n, t) => (n, subst'_type su t)).

Lemma subst'_local_effect_ok : subst'_ok subst'_local_effect.
Proof. intros nts; split; (induction nts as [|[??]??]; [easy|cbn; intros; now simpl_ok]). Qed.
Global Hint Resolve subst'_local_effect_ok : OKDB.
Tactic Notation "pose_ok_proofs'" := pose_ok_proofs'; pose proof subst'_local_effect_ok.
Ltac pose_ok_proofs ::= pose_ok_proofs'.

#[global]
Instance BindExtLocal_Effect : BindExt skind local_effect := ltac:(mkBindExt).

Definition quants_of_function_type (ft : function_type) : list quantifier :=
  let 'FunT qs _ := ft in qs.

Fixpoint subst'_instr {A : Type} (su : Subst' skind) (i : instr A) {struct i} : instr A :=
  i.

Lemma under_quants'_quants_of_function_type_subst'_function_type s fty t :
  under_quants' (quants_of_function_type (subst'_function_type s fty)) t
  = under_quants' (quants_of_function_type fty) t.
Proof. destruct fty; unfold quants_of_function_type; cbn; now autorewrite with SubstDB. Qed.
Hint Rewrite under_quants'_quants_of_function_type_subst'_function_type : SubstDB.

Definition subst_index {A} `{BindExt _ skind A} (i : index) : A -> A :=
  match i with
  | MemI l => subst_ext (Kind:=skind) (ext SMem l id)
  | RepI s => subst_ext (Kind:=skind) (ext SRep s id)
  | SizeI q => subst_ext (Kind:=skind) (ext SSize q id)
  | TypeI pt => subst_ext (Kind:=skind) (ext SType pt id)
  end.

Fixpoint subst_indices {A} `{BindExt _ skind A} (ixs : list index) (e : A) : A :=
  match ixs with
  | [] => e
  | ix :: ixs => subst_index ix (subst_indices ixs e)
  end.

(** Reasoning about subst *)

Definition under_quant (kv : quantifier) : Subst skind -> Subst skind :=
  under (skind_of_quant kv).

Fixpoint under_quants (kvs : list quantifier) (su : Subst skind) :=
  match kvs with
  | [] => su
  | kv :: kvs => under_quant kv (under_quants kvs su)
  end.

Lemma under_quant'_under_quant kv s :
  under_quant' kv (subst'_of s) = subst'_of (under_quant kv s).
Proof.
  unfold under_quant', under_quant.
  destruct kv; cbn; autorewrite with SubstDB; try reflexivity; typeclasses eauto.
Qed.
Hint Rewrite under_quant'_under_quant : SubstDB.

Lemma under_quants'_under_quants kvs s :
  under_quants' kvs (subst'_of s) = subst'_of (under_quants kvs s).
Proof.
  induction kvs; cbn; autorewrite with SubstDB; [easy|].
  rewrite IHkvs; autorewrite with SubstDB; reflexivity.
Qed.
Hint Rewrite under_quants'_under_quants : SubstDB.

Lemma subst_ProdT (su : Subst skind) ts :
  subst SType su (ProdT ts) = ProdT (map (subst_ext su) ts).
Proof eq_refl.
Hint Rewrite subst_ProdT : SubstDB.

Lemma subst_SumT (su : Subst skind) ts :
  subst SType su (SumT ts) = SumT (map (subst_ext su) ts).
Proof eq_refl.
Hint Rewrite subst_SumT : SubstDB.

Lemma subst_ArrayT (su : Subst skind) τ :
  subst SType su (ArrayT τ) = ArrayT (subst SType su τ).
Proof eq_refl.
Hint Rewrite subst_ArrayT : SubstDB.

Lemma subst_RefT (su : Subst skind) μ τ:
  subst SType su (RefT μ τ) = RefT (subst SMem su μ) (subst SType su τ).
Proof eq_refl.
Hint Rewrite subst_RefT : SubstDB.

Lemma subst_GCPtrT (su : Subst skind) τ:
  subst SType su (GCPtrT τ) = GCPtrT (subst SType su τ).
Proof eq_refl.
Hint Rewrite subst_GCPtrT : SubstDB.

Lemma subst_CodeRefT (su : Subst skind) ft :
  subst SType su (CodeRefT ft) = CodeRefT (subst_ext su ft).
Proof eq_refl.
Hint Rewrite subst_CodeRefT : SubstDB.

Lemma subst_RepT (su : Subst skind) ρ τ:
  subst SType su (RepT ρ τ) = RepT (subst SRep su ρ) (subst SType su τ).
Proof eq_refl.
Hint Rewrite subst_RepT : SubstDB.

Lemma subst_PadT (su : Subst skind) σ τ:
  subst SType su (PadT σ τ) = PadT (subst SSize su σ) (subst SType su τ).
Proof eq_refl.
Hint Rewrite subst_PadT : SubstDB.

Lemma subst_SerT (su : Subst skind) τ:
  subst SType su (SerT τ) = SerT (subst SType su τ).
Proof eq_refl.
Hint Rewrite subst_SerT : SubstDB.

Lemma subst_RecT (su : Subst skind) τ :
  subst SType su (RecT τ) = RecT (subst_ext (under SType su) τ).
Proof. cbn; autorewrite with SubstDB; [reflexivity|typeclasses eauto]. Qed.
Hint Rewrite subst_RecT : SubstDB.

Lemma subst_ExT (su : Subst skind) δ τ :
  subst SType su (ExT δ τ) = ExT (subst_ext su δ) (subst_ext (under (skind_of_quant δ) su) τ).
Proof. cbn; autorewrite with SubstDB; [reflexivity | typeclasses eauto]. Qed.
Hint Rewrite subst_ExT : SubstDB.

Lemma subst_ArrowT (su : Subst skind) ts ts' :
  subst_ext su (ArrowT ts ts') = ArrowT (map (subst_ext su) ts) (map (subst_ext su) ts').
Proof eq_refl.
Hint Rewrite subst_ArrowT : SubstDB.

Lemma subst_FunT (su : Subst skind) δs χ :
  subst_ext su (FunT δs χ) = FunT (subst_ext su δs) (subst_ext (under_quants δs su) χ).
Proof. cbn; autorewrite with SubstDB; reflexivity. Qed.
Hint Rewrite subst_FunT : SubstDB.

