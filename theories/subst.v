From Coq Require Import Numbers.BinNums NArith List.

Require Import RWasm.term RWasm.debruijn.

Import ListNotations.

Inductive Ind := SLoc | SQual | SSize | STyp.

#[global]
Instance EqI : Eq Ind := ltac:(intros i j; decide equality).

Definition Kind i :=
  match i with
  | SLoc => Loc
  | SQual => Qual
  | SSize => Size
  | STyp => Typ
  end.

#[global]
Instance VarKind : Var Kind :=
  fun i =>
  match i with
  | SLoc => LocV
  | SQual => QualVar
  | SSize => SizeVar
  | STyp => TVar
  end.

Definition subst'_loc (su : Subst' Kind) (l : Loc) : Loc :=
  match l with
  | LocV x => get_var' SLoc x su
  | _ => l
  end.

Definition subst'_qual (su : Subst' Kind) (q : Qual) : Qual :=
  match q with 
  | QualVar x => get_var' SQual x su
  | _ => q
  end.

Fixpoint subst'_size (su : Subst' Kind) (s : Size) : Size :=
  match s with
  | SizeVar x => get_var' SSize x su
  | SizePlus s1 s2 => SizePlus (subst'_size su s1) (subst'_size su s2)
  | SizeConst _ => s
  end.

Definition subst'_quals (su : Subst' Kind) := map (subst'_qual su).
Definition subst'_sizes (su : Subst' Kind) := map (subst'_size su).

Definition subst'_kindvar (su : Subst' Kind) (kv : KindVar) : KindVar :=
  match kv with
  | LOC q => LOC (subst'_qual su q)
  | QUAL qs rs => QUAL (subst'_quals su qs) (subst'_quals su rs)
  | SIZE ss ts => SIZE (subst'_sizes su ss) (subst'_sizes su ts)
  | TYPE s q hc => TYPE (subst'_size su s) (subst'_qual su q) hc
  end.

Definition kind_of_kindvar kv :=
  match kv with
  | LOC _ => SLoc
  | QUAL _ _ => SQual
  | SIZE _ _ => SSize
  | TYPE _ _ _ => STyp
  end.

Definition under_kindvar' (kv : KindVar) : Subst' Kind -> Subst' Kind :=
  under' (kind_of_kindvar kv).

Fixpoint subst'_kindvars (su : Subst' Kind) (kvs : list KindVar) : list KindVar :=
  match kvs with
  | [] => []
  (** KindVars is a telescope, not parallel binding: each var is in
       scope for all kinds that occur later in the list *)
  | kv :: kvs => subst'_kindvar su kv :: subst'_kindvars (under_kindvar' kv su) kvs
  end.

(* foldl and foldr are equivalent here; see debruijn.under_comm *)
Fixpoint under_kindvars' (kvs : list KindVar) (su : Subst' Kind) :=
  match kvs with
  | [] => su
  | kv :: kvs => under_kindvar' kv (under_kindvars' kvs su)
  end.

Fixpoint subst'_typ (su : Subst' Kind) (t : Typ) {struct t} : Typ :=
  match t with
  | Num _ => t
  | TVar x => get_var' STyp x su
  | Unit => t
  | ProdT ts => ProdT (map (subst'_typ su) ts)
  | CoderefT ft => CoderefT (subst'_funtype su ft)
  | Rec q t => Rec (subst'_qual su q) (subst'_typ (under' STyp su) t)
  | PtrT l => PtrT (subst'_loc su l)
  | ExLoc q t => ExLoc (subst'_qual su q) (subst'_typ (under' SLoc su) t)
  | OwnR l => OwnR (subst'_loc su l)
  | CapT c l ht => CapT c (subst'_loc su l) (subst'_heaptype su ht)
  | RefT c l ht => RefT c (subst'_loc su l) (subst'_heaptype su ht)
  end
with subst'_heaptype (su : Subst' Kind) (ht : HeapType) {struct ht} : HeapType :=
  match ht with
  | VariantType ts => VariantType (map (subst'_typ su) ts)
  | StructType tss =>
    StructType (map (fun '(t, s) => (subst'_typ su t, subst'_size su s)) tss)
  | ArrayType t => ArrayType (subst'_typ su t)
  | Ex s q t => Ex (subst'_size su s) (subst'_qual su q) (subst'_typ (under' STyp su) t)
  end
with subst'_arrowtype (su : Subst' Kind) (t : ArrowType) {struct t} : ArrowType :=
  match t with
  | Arrow ts1 ts2 =>
    Arrow
      (map (subst'_typ su) ts1)
      (map (subst'_typ su) ts2)
  end
with subst'_funtype (su : Subst' Kind) (t : FunType) {struct t} : FunType :=
  match t with
  | FunT kvs arrow =>
    FunT (subst'_kindvars su kvs)
         (subst'_arrowtype (under_kindvars' kvs su) arrow)
  end.

Definition subst'_rwasm (i : Ind) : Subst' Kind -> Kind i -> Kind i :=
  match i with
  | SLoc => subst'_loc
  | SQual => subst'_qual
  | SSize => subst'_size
  | STyp => subst'_typ
  end.

(** Solves easy subst'_ok obligations
    TODO is this really the right automation for this thing *)
Ltac subst'_ok n :=
  let e := fresh "e" with f := fresh "f" with g := fresh "g" in
  intros e; split; [|intros f g]; induction e; cbn; crush n.

#[global]
Instance BindVar_rwasm : BindVar Kind.
Proof. refine {| subst' := subst'_rwasm |}; abstract (intros []; reflexivity). Defined.

Lemma subst'_loc_ok : subst'_ok subst'_loc. Proof. subst'_ok 5. Qed.
Lemma subst'_qual_ok : subst'_ok subst'_qual. Proof. subst'_ok 5. Qed.
Lemma subst'_size_ok : subst'_ok subst'_size. Proof. subst'_ok 5. Qed.
Global Hint Resolve subst'_loc_ok subst'_qual_ok subst'_size_ok : OKDB.
Tactic Notation "pose_ok_proofs'" :=
  pose_ok_proofs';
  pose proof subst'_loc_ok;
  pose proof subst'_qual_ok;
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

Lemma subst'_quals_ok : subst'_ok subst'_quals.
Proof. intros qs; intros_ok_at; induction qs; cbn; now simpl_ok. Qed.
Global Hint Resolve subst'_quals_ok : OKDB.
Tactic Notation "pose_ok_proofs'" := pose_ok_proofs'; pose proof subst'_quals_ok.
Ltac pose_ok_proofs ::= pose_ok_proofs'.

Lemma subst'_sizes_ok : subst'_ok subst'_sizes.
Proof. intros qs; intros_ok_at; induction qs; cbn; now simpl_ok. Qed.
Global Hint Resolve subst'_sizes_ok : OKDB.
Tactic Notation "pose_ok_proofs'" := pose_ok_proofs'; pose proof subst'_sizes_ok.
Ltac pose_ok_proofs ::= pose_ok_proofs'.

Lemma subst'_kindvar_ok : subst'_ok subst'_kindvar.
Proof. intros kv; intros_ok_at; destruct kv; cbn; now simpl_ok. Qed.
Global Hint Resolve subst'_kindvar_ok : OKDB.
Tactic Notation "pose_ok_proofs'" := pose_ok_proofs'; pose proof subst'_kindvar_ok.
Ltac pose_ok_proofs ::= pose_ok_proofs'.

Lemma under_kindvar'_var' kv : under_kindvar' kv var' = var'.
Proof. destruct kv; cbn; unfold under_kindvar'; cbn; now autorewrite with SubstDB. Qed.

Lemma under_kindvars'_var' kvs : under_kindvars' kvs var' = var'.
Proof. induction kvs; cbn; auto. now rewrite IHkvs, under_kindvar'_var'. Qed.

Lemma under_kindvar'_comp' kv f g :
  under_kindvar' kv (f ∙' g) = under_kindvar' kv f ∙' under_kindvar' kv g.
Proof. destruct kv; unfold under_kindvar'; cbn; now autorewrite with SubstDB. Qed.

Lemma under_kindvars'_comp' kvs f g :
  under_kindvars' kvs (f ∙' g) = under_kindvars' kvs f ∙' under_kindvars' kvs g.
Proof. induction kvs; cbn; [auto|now rewrite IHkvs, under_kindvar'_comp']. Qed.

Lemma under_kindvar'_subst'_kindvar s kv t :
  under_kindvar' (subst'_kindvar s kv) t = under_kindvar' kv t.
Proof. destruct kv; reflexivity. Qed.

Lemma under_kindvars'_subst'_kindvars s kvs t :
  under_kindvars' (subst'_kindvars s kvs) t = under_kindvars' kvs t.
Proof.
  revert s; induction kvs; intros s; [easy|].
  cbn; now rewrite !IHkvs, under_kindvar'_subst'_kindvar.
Qed.

Hint Rewrite
     under_kindvars'_var' under_kindvar'_var'
     under_kindvar'_comp' under_kindvars'_comp'
     under_kindvar'_subst'_kindvar under_kindvars'_subst'_kindvars
  : SubstDB.

Lemma subst'_kindvars_ok : subst'_ok subst'_kindvars.
Proof. intros qs; split; induction qs; intros; cbn; now simpl_ok. Qed.
Global Hint Resolve subst'_kindvars_ok : OKDB.
Tactic Notation "pose_ok_proofs'" := pose_ok_proofs'; pose proof subst'_kindvars_ok.
Ltac pose_ok_proofs ::= pose_ok_proofs'.

Lemma subst'_typ_mut_ok
  : subst'_ok subst'_typ /\
    subst'_ok subst'_funtype /\
    subst'_ok subst'_arrowtype /\
    subst'_ok subst'_heaptype.
Proof.
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
Qed.

Corollary subst'_typ_ok : subst'_ok subst'_typ. Proof. apply subst'_typ_mut_ok. Qed.
Corollary subst'_funtype_ok : subst'_ok subst'_funtype. Proof. apply subst'_typ_mut_ok. Qed.
Corollary subst'_arrowtype_ok : subst'_ok subst'_arrowtype. Proof. apply subst'_typ_mut_ok. Qed.
Corollary subst'_heaptype_ok : subst'_ok subst'_heaptype. Proof. apply subst'_typ_mut_ok. Qed.
Global Hint Resolve
     subst'_typ_ok
     subst'_typ_ok
     subst'_funtype_ok
     subst'_arrowtype_ok
     subst'_heaptype_ok
  : OKDB.
Tactic Notation "pose_ok_proofs'" :=
  pose_ok_proofs';
  pose proof subst'_typ_ok;
  pose proof subst'_typ_ok;
  pose proof subst'_funtype_ok;
  pose proof subst'_arrowtype_ok;
  pose proof subst'_heaptype_ok.
Ltac pose_ok_proofs ::= pose_ok_proofs'.

#[global]
Instance BindRWasm : Bind Kind. Proof. apply mkBind; destruct i; auto with OKDB. Defined.

Ltac mkBindExt := eapply mkBindExt; eauto with OKDB.

#[global]
Instance BindExtLoc : BindExt Kind Loc := ltac:(mkBindExt).
#[global]
Instance BindExtQual : BindExt Kind Qual := ltac:(mkBindExt).
#[global]
Instance BindExtQuals : BindExt Kind (list Qual) := ltac:(mkBindExt).
#[global]
Instance BindExtSize : BindExt Kind Size := ltac:(mkBindExt).
#[global]
Instance BindExtSizes : BindExt Kind (list Size) := ltac:(mkBindExt).
#[global]
Instance BindExtKindVar : BindExt Kind KindVar := ltac:(mkBindExt).
#[global]
Instance BindExtKindVars : BindExt Kind (list KindVar) := ltac:(mkBindExt).

#[global]
Instance BindExtTyp : BindExt Kind Typ := ltac:(mkBindExt).
#[global]
Instance BindExtFunType : BindExt Kind FunType := ltac:(mkBindExt).
#[global]
Instance BindExtArrowType : BindExt Kind ArrowType := ltac:(mkBindExt).
#[global]
Instance BindExtHeapType : BindExt Kind HeapType := ltac:(mkBindExt).

Definition subst'_typs s := map (subst'_typ s).

Lemma subst'_typs_ok : subst'_ok subst'_typs.
Proof. unfold subst'_typs. auto with OKDB. Qed.
Global Hint Resolve subst'_typs_ok : OKDB.
Tactic Notation "pose_ok_proofs'" := pose_ok_proofs'; pose proof subst'_typs_ok.
Ltac pose_ok_proofs ::= pose_ok_proofs'.

#[global]
Instance BindExtTypes : BindExt Kind (list Typ) := ltac:(mkBindExt).

Definition subst'_index (su : Subst' Kind) (ix : Index) : Index :=
  match ix with
  | LocI l => LocI (subst'_loc su l)
  | SizeI s => SizeI (subst'_size su s)
  | QualI q => QualI (subst'_qual su q)
  | TypI p => TypI (subst'_typ su p)
  end.

Lemma subst'_index_ok : subst'_ok subst'_index.
Proof. intros []; intros_ok_at; cbn; now simpl_ok. Qed.
Global Hint Resolve subst'_index_ok : OKDB.
Tactic Notation "pose_ok_proofs'" := pose_ok_proofs'; pose proof subst'_index_ok.
Ltac pose_ok_proofs ::= pose_ok_proofs'.

#[global]
Instance BindExtIndex : BindExt Kind Index := ltac:(mkBindExt).

Definition subst'_indices s := map (subst'_index s).

Lemma subst'_indices_ok : subst'_ok subst'_indices.
Proof. unfold subst'_indices; auto with OKDB. Qed.
Global Hint Resolve subst'_indices_ok : OKDB.
Tactic Notation "pose_ok_proofs'" := pose_ok_proofs'; pose proof subst'_indices_ok.
Ltac pose_ok_proofs ::= pose_ok_proofs'.

#[global]
Instance BindExtIndices : BindExt Kind (list Index) := ltac:(mkBindExt).

Definition subst'_localeffect su : LocalEffect -> LocalEffect :=
  map (fun '(n, t) => (n, subst'_typ su t)).

Lemma subst'_localeffect_ok : subst'_ok subst'_localeffect.
Proof. intros nts; split; (induction nts as [|[??]??]; [easy|cbn; intros; now simpl_ok]). Qed.
Global Hint Resolve subst'_localeffect_ok : OKDB.
Tactic Notation "pose_ok_proofs'" := pose_ok_proofs'; pose proof subst'_localeffect_ok.
Ltac pose_ok_proofs ::= pose_ok_proofs'.

#[global]
Instance BindExtLocalEffect : BindExt Kind LocalEffect := ltac:(mkBindExt).

Definition kindvars_of_funtype (ft : FunType) : list KindVar :=
  let 'FunT kvs _ := ft in kvs.

Fixpoint subst'_instruction {A : Type} (su : Subst' Kind) (i : instr A) {struct i} : instr A :=
  match i with
  | INumConst _ _ _ => i
  | IUnit _ => i
  | INum _ _ => i
  | IUnreachable _ => i
  | INop _ => i
  | IDrop _ => i
  | ISelect _ => i
  | IBlock ann arr leffs insns =>
    IBlock ann
           (subst'_arrowtype su arr)
           (subst'_localeffect su leffs)
           (map (subst'_instruction su) insns)
  | ILoop ann arr insns =>
    ILoop ann
          (subst'_arrowtype su arr)
          (map (subst'_instruction su) insns)
  | IIte ann arr leffs insns1 insns2 =>
    IIte ann
         (subst'_arrowtype su arr)
         (subst'_localeffect su leffs)
         (map (subst'_instruction su) insns1)
         (map (subst'_instruction su) insns2)
  | IBr _ _ => i
  | IBrIf _ _ => i
  | IBrTable _ _ _ => i
  | IRet _ => i
  | IGetLocal ann n q => IGetLocal ann n (subst'_qual su q)
  | ISetLocal _ _ => i
  | ITeeLocal _ _ => i
  | IGetGlobal _ _ => i
  | ISetGlobal _ _ => i
  | ICoderef _ _ => i
  | IInst ann insts => IInst ann (subst'_indices su insts)
  | ICallIndirect _ => i
  | ICall ann n insts => ICall ann n (subst'_indices su insts)
  | IRecFold ann t => IRecFold ann (subst'_typ su t)
  | IRecUnfold _ => i
  | IGroup ann n q => IGroup ann n (subst'_qual su q)
  | IUngroup _ => i
  | ICapSplit _ => i
  | ICapJoin _ => i
  | IRefDemote _ => i
  | IMemPack ann l => IMemPack ann (subst'_loc su l)
  | IMemUnpack ann arr leff l_insns =>
    (* l_insns binds a new location *)
    IMemUnpack ann
               (subst'_arrowtype su arr)
               (subst'_localeffect su leff)
               (map (subst'_instruction (under' SLoc su)) l_insns)
  | IStructMalloc ann ss q => IStructMalloc ann (subst'_sizes su ss) (subst'_qual su q)
  | IStructFree _ => i
  | IStructGet _ _ => i
  | IStructSet _ _ => i
  | IStructSwap _ _ => i
  | IVariantMalloc ann n ts q =>
    IVariantMalloc ann n (subst'_typs su ts) (subst'_qual su q)
  | IVariantCase ann q tausv arr leff insnss =>
    IVariantCase ann
                 (subst'_qual su q)
                 (subst'_heaptype su tausv)
                 (subst'_arrowtype su arr)
                 (subst'_localeffect su leff)
                 (map (map (subst'_instruction su)) insnss)
  | IArrayMalloc ann q => IArrayMalloc ann (subst'_qual su q)
  | IArrayGet _ => i
  | IArraySet _ => i
  | IArrayFree _ => i
  | IExistPack ann t ht q =>
    IExistPack ann
               (subst'_typ su t)
               (subst'_heaptype su ht)
               (subst'_qual su q)
  | IExistUnpack ann q ex arr leff α_insns =>
    (* α_insns binds a new type variable *)
    IExistUnpack ann
                 (subst'_qual su q)
                 (subst'_heaptype su ex)
                 (subst'_arrowtype su arr)
                 (subst'_localeffect su leff)
                 (map (subst'_instruction (under' STyp su)) α_insns)
  | IRefSplit _ => i
  | IRefJoin _ => i
  | IQualify ann q => IQualify ann (subst'_qual su q)
  end.

Lemma under_kindvars'_kindvars_of_funtype_subst'_funtype s fty t :
  under_kindvars' (kindvars_of_funtype (subst'_funtype s fty)) t
  = under_kindvars' (kindvars_of_funtype fty) t.
Proof. destruct fty; unfold kindvars_of_funtype; cbn; now autorewrite with SubstDB. Qed.
Hint Rewrite under_kindvars'_kindvars_of_funtype_subst'_funtype : SubstDB.

Definition subst_index {A} `{BindExt _ Kind A} (i : Index) : A -> A :=
  match i with
  | LocI l => subst_ext (Kind:=Kind) (ext SLoc l id)
  | SizeI s => subst_ext (Kind:=Kind) (ext SSize s id)
  | QualI q => subst_ext (Kind:=Kind) (ext SQual q id)
  | TypI pt => subst_ext (Kind:=Kind) (ext STyp pt id)
  end.

Fixpoint subst_indices {A} `{BindExt _ Kind A} (ixs : list Index) (e : A) : A :=
  match ixs with
  | [] => e
  | ix :: ixs => subst_index ix (subst_indices ixs e)
  end.

(** Reasoning about subst *)

Definition under_kindvar (kv : KindVar) : Subst Kind -> Subst Kind :=
  under (kind_of_kindvar kv).

Fixpoint under_kindvars (kvs : list KindVar) (su : Subst Kind) :=
  match kvs with
  | [] => su
  | kv :: kvs => under_kindvar kv (under_kindvars kvs su)
  end.

Lemma under_kindvar'_under_kindvar kv s :
  under_kindvar' kv (subst'_of s) = subst'_of (under_kindvar kv s).
Proof.
  unfold under_kindvar', under_kindvar.
  destruct kv; cbn; autorewrite with SubstDB; try reflexivity; typeclasses eauto.
Qed.
Hint Rewrite under_kindvar'_under_kindvar : SubstDB.

Lemma under_kindvars'_under_kindvars kvs s :
  under_kindvars' kvs (subst'_of s) = subst'_of (under_kindvars kvs s).
Proof.
  induction kvs; cbn; autorewrite with SubstDB; [easy|].
  rewrite IHkvs; autorewrite with SubstDB; reflexivity.
Qed.
Hint Rewrite under_kindvars'_under_kindvars : SubstDB.

Lemma subst_ProdT (su : Subst Kind) ts :
  subst STyp su (ProdT ts) = ProdT (map (subst_ext su) ts).
Proof eq_refl.
Hint Rewrite subst_ProdT : SubstDB.

Lemma subst_CoderefT (su : Subst Kind) ft :
  subst STyp su (CoderefT ft) = CoderefT (subst_ext su ft).
Proof eq_refl.
Hint Rewrite subst_CoderefT : SubstDB.

Lemma subst_Rec (su : Subst Kind) q t0 :
  subst STyp su (Rec q t0) = Rec (subst SQual su q) (subst_ext (under STyp su) t0).
Proof. cbn; autorewrite with SubstDB; [reflexivity|typeclasses eauto]. Qed.
Hint Rewrite subst_Rec : SubstDB.

Lemma subst_PtrT (su : Subst Kind) l :
  subst STyp su (PtrT l) = PtrT (subst SLoc su l).
Proof eq_refl.
Hint Rewrite subst_PtrT : SubstDB.

Lemma subst_ExLoc (su : Subst Kind) q t0 :
  subst STyp su (ExLoc q t0) = ExLoc (subst SQual su q) (subst_ext (under SLoc su) t0).
Proof. cbn; autorewrite with SubstDB; [reflexivity | typeclasses eauto]. Qed.
Hint Rewrite subst_ExLoc : SubstDB.

Lemma subst_OwnR (su : Subst Kind) l :
  subst STyp su (OwnR l) = OwnR (subst SLoc su l).
Proof eq_refl.
Hint Rewrite subst_OwnR : SubstDB.

Lemma subst_CapT (su : Subst Kind) c loc ht :
  subst STyp su (CapT c loc ht)
  = CapT c (subst SLoc su loc) (subst_ext su ht).
Proof eq_refl.
Hint Rewrite subst_CapT : SubstDB.

Lemma subst_RefT (su : Subst Kind) c loc ht :
  subst STyp su (RefT c loc ht)
  = RefT c (subst SLoc su loc) (subst_ext su ht).
Proof eq_refl.
Hint Rewrite subst_RefT : SubstDB.

Lemma subst_VariantType (su : Subst Kind) ts :
  subst_ext su (VariantType ts)
  = VariantType (map (subst_ext su) ts).
Proof eq_refl.
Hint Rewrite subst_VariantType : SubstDB.

Lemma subst_StructType (su : Subst Kind) tss :
  subst_ext su (StructType tss)
  = StructType (map (fun '(t, s) => (subst_ext su t, subst SSize su s)) tss).
Proof eq_refl.
Hint Rewrite subst_StructType : SubstDB.

Lemma subst_ArrayType (su : Subst Kind) t :
  subst_ext su (ArrayType t)
  = ArrayType (subst_ext su t).
Proof eq_refl.
Hint Rewrite subst_ArrayType : SubstDB.

Lemma subst_Ex (su : Subst Kind) s q t :
  subst_ext su (Ex s q t) = Ex (subst SSize su s) (subst SQual su q) (subst_ext (under STyp su) t).
Proof. cbn; autorewrite with SubstDB; [reflexivity|typeclasses eauto]. Qed.
Hint Rewrite subst_Ex : SubstDB.

Lemma subst_Arrow (su : Subst Kind) ts ts' :
  subst_ext su (Arrow ts ts') = Arrow (map (subst_ext su) ts) (map (subst_ext su) ts').
Proof eq_refl.
Hint Rewrite subst_Arrow : SubstDB.

Lemma subst_FunT (su : Subst Kind) kvs ft :
  subst_ext su (FunT kvs ft) = FunT (subst_ext su kvs) (subst_ext (under_kindvars kvs su) ft).
Proof. cbn; autorewrite with SubstDB; reflexivity. Qed.
Hint Rewrite subst_FunT : SubstDB.

