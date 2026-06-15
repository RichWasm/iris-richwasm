Require Import stdpp.list.

Require Import RecordUpdate.RecordUpdate.

From RichWasm Require Import layout syntax util.

Set Bullet Behavior "Strict Subproofs".

Record module_ctx :=
  { mc_functions : list function_type;
    mc_table : list function_type }.

Arguments module_ctx : clear implicits.

Definition local_ctx := list type.

Record kind_ctx :=
  { kc_mem_vars : nat;
    kc_rep_vars : nat;
    kc_size_vars : nat }.

Definition kc_empty : kind_ctx :=
  {| kc_mem_vars := 0;
     kc_rep_vars := 0;
     kc_size_vars := 0 |}.

Definition kc_of_fft (fft : flat_function_type) : kind_ctx :=
  {| kc_mem_vars := fft.(fft_mem_vars);
     kc_rep_vars := fft.(fft_rep_vars);
     kc_size_vars := fft.(fft_size_vars) |}.

Record function_ctx :=
  { fc_return : list type;
    fc_locals : list (list primitive);
    fc_labels : list (list type * local_ctx);
    fc_kind_ctx : kind_ctx;
    fc_type_vars : list kind }.

Arguments function_ctx : clear implicits.

Definition fc_empty : function_ctx :=
  {| fc_return := [];
     fc_locals := [];
     fc_labels := [];
     fc_kind_ctx := kc_empty;
     fc_type_vars := [] |}.

Definition fc_clear_kind (F : function_ctx) : function_ctx :=
  {| fc_return := F.(fc_return);
     fc_locals := F.(fc_locals);
     fc_labels := F.(fc_labels);
     fc_kind_ctx := kc_empty;
     fc_type_vars := F.(fc_type_vars) |}.

Definition subst_function_ctx
  (s__mem : nat -> memory) (s__rep : nat -> representation) (s__size : nat -> size) (s__type : nat -> type)
  (F : function_ctx) :
  function_ctx :=
  let sub := subst_type s__mem s__rep s__size s__type in
  {| fc_return := map sub F.(fc_return);
     fc_locals := F.(fc_locals);
     fc_labels := map (fun '(τs, L) => (map sub τs, map sub L)) F.(fc_labels);
     fc_kind_ctx := F.(fc_kind_ctx);
     fc_type_vars := map (subst_kind s__rep s__size) F.(fc_type_vars) |}.

Inductive mem_ok : kind_ctx -> memory -> Prop :=
| OKVarM K m :
  m < K.(kc_mem_vars) ->
  mem_ok K (VarM m)
| OKBaseM K cm :
  mem_ok K (BaseM cm).

Inductive rep_ok : kind_ctx -> representation -> Prop :=
| OKVarR K r :
  r < K.(kc_rep_vars) ->
  rep_ok K (VarR r)
| OKSumR K ρs :
  Forall (rep_ok K) ρs ->
  rep_ok K (SumR ρs)
| OKProdR K ρs :
  Forall (rep_ok K) ρs ->
  rep_ok K (ProdR ρs)
| OKAtomR K ι :
  rep_ok K (AtomR ι).

Inductive size_ok : kind_ctx -> size -> Prop :=
| OKVarS K s :
  s < K.(kc_size_vars) ->
  size_ok K (VarS s)
| OKSumS K σs :
  Forall (size_ok K) σs ->
  size_ok K (SumS σs)
| OKProdS K σs :
  Forall (size_ok K) σs ->
  size_ok K (ProdS σs)
| OKRepS K ρ :
  rep_ok K ρ ->
  size_ok K (RepS ρ)
| OKConstS K n :
  size_ok K (ConstS n).

Inductive kind_ok : kind_ctx -> kind -> Prop :=
| OKVALTYPE K ρ ξ :
  rep_ok K ρ ->
  kind_ok K (VALTYPE ρ ξ)
| OKMEMTYPE K σ ξ :
  size_ok K σ ->
  kind_ok K (MEMTYPE σ ξ).

Inductive type_ok : function_ctx -> type -> Prop :=
| OKVarT F t κ :
  F.(fc_type_vars) !! t = Some κ ->
  kind_ok F.(fc_kind_ctx) κ ->
  type_ok F (VarT t)
| OKI31T F κ :
  kind_ok F.(fc_kind_ctx) κ ->
  type_ok F (I31T κ)
| OKNumT F κ ν :
  kind_ok F.(fc_kind_ctx) κ ->
  type_ok F (NumT κ ν)
| OKSumT F κ τs :
  kind_ok F.(fc_kind_ctx) κ ->
  Forall (type_ok F) τs ->
  type_ok F (SumT κ τs)
| OKVariantT F κ τs :
  kind_ok F.(fc_kind_ctx) κ ->
  Forall (type_ok F) τs ->
  type_ok F (VariantT κ τs)
| OKProdT F κ τs :
  kind_ok F.(fc_kind_ctx) κ ->
  Forall (type_ok F) τs ->
  type_ok F (ProdT κ τs)
| OKStructT F κ τs :
  kind_ok F.(fc_kind_ctx) κ ->
  Forall (type_ok F) τs ->
  type_ok F (StructT κ τs)
| OKRefT F κ μ β τ :
  kind_ok F.(fc_kind_ctx) κ ->
  mem_ok F.(fc_kind_ctx) μ ->
  type_ok F τ ->
  type_ok F (RefT κ μ β τ)
| OKCodeRefT F κ ϕ :
  kind_ok F.(fc_kind_ctx) κ ->
  function_type_ok F ϕ ->
  type_ok F (CodeRefT κ ϕ)
| OKSerT F κ τ :
  kind_ok F.(fc_kind_ctx) κ ->
  type_ok F τ ->
  type_ok F (SerT κ τ)
| OKPlugT F κ ρ :
  kind_ok F.(fc_kind_ctx) κ ->
  rep_ok F.(fc_kind_ctx) ρ ->
  type_ok F (PlugT κ ρ)
| OKSpanT F κ σ :
  kind_ok F.(fc_kind_ctx) κ ->
  size_ok F.(fc_kind_ctx) σ ->
  type_ok F (SpanT κ σ)
| OKRecT F κ τ :
  kind_ok F.(fc_kind_ctx) κ ->
  type_ok (F <| fc_type_vars ::= cons κ |>) τ ->
  type_ok F (RecT κ τ)
| OKExistsMemT F κ τ :
  kind_ok F.(fc_kind_ctx) κ ->
  type_ok (F <| fc_kind_ctx ::= set kc_mem_vars S |>) τ ->
  type_ok F (ExistsMemT κ τ)
| OKExistsRepT F κ τ :
  kind_ok F.(fc_kind_ctx) κ ->
  type_ok (F <| fc_kind_ctx ::= set kc_rep_vars S |>) τ ->
  type_ok F (ExistsRepT κ τ)
| OKExistsSizeT F κ τ :
  kind_ok F.(fc_kind_ctx) κ ->
  type_ok (F <| fc_kind_ctx ::= set kc_size_vars S |>) τ ->
  type_ok F (ExistsSizeT κ τ)
| OKExistsType F κ κ0 τ :
  kind_ok F.(fc_kind_ctx) κ ->
  kind_ok F.(fc_kind_ctx) κ0 ->
  type_ok (F <| fc_type_vars ::= cons κ0 |>) τ ->
  type_ok F (ExistsTypeT κ κ0 τ)

with function_type_ok : function_ctx -> function_type -> Prop :=
| OKMonoFunT F τs1 τs2 :
  Forall (type_ok F) τs1 ->
  Forall (type_ok F) τs2 ->
  function_type_ok F (MonoFunT τs1 τs2)
| OKForallMemT F ϕ :
  function_type_ok (F <| fc_kind_ctx ::= set kc_mem_vars S |>) ϕ ->
  function_type_ok F (ForallMemT ϕ)
| OKForallRepT F ϕ :
  function_type_ok (F <| fc_kind_ctx ::= set kc_rep_vars S |>) ϕ ->
  function_type_ok F (ForallRepT ϕ)
| OKForallSizeT F ϕ :
  function_type_ok (F <| fc_kind_ctx ::= set kc_size_vars S |>) ϕ ->
  function_type_ok F (ForallSizeT ϕ)
| OKForallTypeT F κ ϕ :
  kind_ok F.(fc_kind_ctx) κ ->
  function_type_ok (F <| fc_type_vars ::= cons κ |>) ϕ ->
  function_type_ok F (ForallTypeT κ ϕ).

Definition mono_mem (μ : memory) : Prop := exists bm, μ = BaseM bm.

Definition ref_flag_le (ξ ξ' : ref_flag) : bool :=
  match ξ, ξ' with
  | NoRefs, _
  | GCRefs, GCRefs
  | GCRefs, AnyRefs
  | AnyRefs, AnyRefs => true
  | _, _ => false
  end.

Lemma ref_flag_le_refl ξ : ref_flag_le ξ ξ.
Proof.
  by destruct ξ.
Qed.

Lemma ref_flag_le_trans ξ1 ξ2 ξ3 : ref_flag_le ξ1 ξ2 -> ref_flag_le ξ2 ξ3 -> ref_flag_le ξ1 ξ3.
Proof.
  intros H12 H23.
  by destruct ξ1; destruct ξ2; destruct ξ3.
Qed.

Lemma ref_flag_le_total ξ ξ' : ref_flag_le ξ ξ' ∨ ref_flag_le ξ' ξ.
Proof.
  destruct ξ, ξ'; simpl; auto.
Qed.

Lemma least_ref_flag ξ : ref_flag_le NoRefs ξ.
Proof.
  by destruct ξ.
Qed.

Definition ref_flag_lub2 (ξ1 ξ2 : ref_flag) : ref_flag :=
  match ξ1 with
  | NoRefs => ξ2
  | GCRefs =>
      match ξ2 with
      | NoRefs => GCRefs
      | _ => ξ2
      end
  | AnyRefs => AnyRefs
  end.

Lemma ref_flag_lub2_least ξ1 ξ2 ξ' :
  ref_flag_le ξ1 ξ' ->
  ref_flag_le ξ2 ξ' ->
  ref_flag_le (ref_flag_lub2 ξ1 ξ2) ξ'.
Proof.
  destruct ξ1, ξ2; done.
Qed.

Lemma ref_flag_lub2_ub ξ1 ξ2 :
  ref_flag_le ξ1 (ref_flag_lub2 ξ1 ξ2) /\ ref_flag_le ξ2 (ref_flag_lub2 ξ1 ξ2).
Proof.
  by split; destruct ξ1; destruct ξ2.
Qed.

Definition ref_flag_lub (ξs : list ref_flag) : ref_flag :=
  foldr ref_flag_lub2 NoRefs ξs.

Lemma ref_flag_lub_least ξ' ξs :
  Forall (fun ξ => ref_flag_le ξ ξ') ξs ->
  ref_flag_le (ref_flag_lub ξs) ξ'.
Proof.
  generalize dependent ξ'.
  induction ξs; intros ξ' Hs.
  - done.
  - inversion Hs; subst; cbn in *.
    eapply ref_flag_lub2_least; by eauto.
Qed.

Lemma ref_flag_lub_ub ξ ξs :
  ξ ∈ ξs ->
  ref_flag_le ξ (ref_flag_lub ξs).
Proof.
  induction ξs as [| ξ0 ξs IH]; intros Hin.
  - inversion Hin.
  - destruct (ref_flag_lub2_ub ξ0 (ref_flag_lub ξs)) as [Hub1 Hub2].
    apply elem_of_cons in Hin as [-> | Hin].
    + apply Hub1.
    + eapply ref_flag_le_trans; eauto.
Qed.

Lemma ref_flag_lub_incl ξs ξs' :
  ξs ⊆ ξs' ->
  ref_flag_le (ref_flag_lub ξs) (ref_flag_lub ξs').
Proof.
  intros Hsub.
  apply ref_flag_lub_least, Forall_forall.
  intros ξ Hin.
  apply ref_flag_lub_ub; auto.
Qed.

Inductive subkind_of : kind -> kind -> Prop :=
| KSubVal ρ ξ ξ' :
  ref_flag_le ξ ξ' ->
  subkind_of (VALTYPE ρ ξ) (VALTYPE ρ ξ')
| KSubMem σ ξ ξ' :
  ref_flag_le ξ ξ' ->
  subkind_of (MEMTYPE σ ξ) (MEMTYPE σ ξ').

Lemma subkind_of_refl κ : subkind_of κ κ.
Proof.
  destruct κ; constructor; apply ref_flag_le_refl.
Qed.

Lemma subkind_of_trans κ1 κ2 κ3 : subkind_of κ1 κ2 -> subkind_of κ2 κ3 -> subkind_of κ1 κ3.
Proof.
  intros H12 H23.
  by destruct κ1; destruct κ2; destruct κ3;
    inversion H12; inversion H23;
    subst; constructor; eapply ref_flag_le_trans.
Qed.

Inductive subskind_of : skind -> skind -> Prop :=
| SKSubVal ιs ξ ξ' :
  ref_flag_le ξ ξ' ->
  subskind_of (SVALTYPE ιs ξ) (SVALTYPE ιs ξ')
| SKSubMem n ξ ξ' :
  ref_flag_le ξ ξ' ->
  subskind_of (SMEMTYPE n ξ) (SMEMTYPE n ξ').

Lemma subskind_of_refl κ : subskind_of κ κ.
Proof.
  destruct κ; constructor; apply ref_flag_le_refl.
Qed.

Lemma subskind_of_trans κ1 κ2 κ3 : subskind_of κ1 κ2 -> subskind_of κ2 κ3 -> subskind_of κ1 κ3.
Proof.
  intros H12 H23.
  by destruct κ1; destruct κ2; destruct κ3;
    inversion H12; inversion H23;
    subst; constructor; eapply ref_flag_le_trans.
Qed.

Inductive has_kind_ok : function_ctx -> type -> kind -> Prop :=
| OKHasKind F τ κ :
  type_ok F τ ->
  kind_ok F.(fc_kind_ctx) κ ->
  has_kind_ok F τ κ.

Inductive has_kind : function_ctx -> type -> kind -> Prop :=
| KI31 F :
  let κ := VALTYPE (AtomR PtrR) NoRefs in
  has_kind F (I31T κ) κ
| KI32 F :
  let κ := VALTYPE (AtomR I32R) NoRefs in
  has_kind F (NumT κ (IntT I32T)) κ
| KI64 F :
  let κ := VALTYPE (AtomR I64R) NoRefs in
  has_kind F (NumT κ (IntT I64T)) κ
| KF32 F :
  let κ := VALTYPE (AtomR F32R) NoRefs in
  has_kind F (NumT κ (FloatT F32T)) κ
| KF64 F :
  let κ := VALTYPE (AtomR F64R) NoRefs in
  has_kind F (NumT κ (FloatT F64T)) κ
| KSum F τs ρs ξs :
  Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs ρs ξs ->
  let κ := VALTYPE (SumR ρs) (ref_flag_lub ξs) in
  has_kind F (SumT κ τs) κ
| KVariant F τs σs ξs :
  Forall3 (fun τ σ ξ => has_kind F τ (MEMTYPE σ ξ)) τs σs ξs ->
  let κ := MEMTYPE (SumS σs) (ref_flag_lub ξs) in
  has_kind F (VariantT κ τs) κ
| KProd F τs ρs ξs :
  Forall3 (fun τ ρ ξ => has_kind F τ (VALTYPE ρ ξ)) τs ρs ξs ->
  let κ := VALTYPE (ProdR ρs) (ref_flag_lub ξs) in
  has_kind F (ProdT κ τs) κ
| KStruct F τs σs ξs :
  Forall3 (fun τ σ ξ => has_kind F τ (MEMTYPE σ ξ)) τs σs ξs ->
  let κ := MEMTYPE (ProdS σs) (ref_flag_lub ξs) in
  has_kind F (StructT κ τs) κ
| KRefVar F m β τ σ ξ :
  mem_ok F.(fc_kind_ctx) (VarM m) ->
  has_kind F τ (MEMTYPE σ ξ) ->
  let κ := VALTYPE (AtomR PtrR) AnyRefs in
  has_kind F (RefT κ (VarM m) β τ) κ
| KRefMM F β τ σ ξ :
  has_kind F τ (MEMTYPE σ ξ) ->
  let κ := VALTYPE (AtomR PtrR) AnyRefs in
  has_kind F (RefT κ (BaseM MemMM) β τ) κ
| KRefGC F β τ σ ξ :
  has_kind F τ (MEMTYPE σ ξ) ->
  let κ := VALTYPE (AtomR PtrR) GCRefs in
  has_kind F (RefT κ (BaseM MemGC) β τ) κ
| KCodeRef F ϕ :
  function_type_ok F ϕ ->
  let κ := VALTYPE (AtomR I32R) NoRefs in
  has_kind F (CodeRefT κ ϕ) κ
| KSer F τ ρ ξ :
  has_kind F τ (VALTYPE ρ ξ) ->
  let κ := MEMTYPE (RepS ρ) ξ in
  has_kind F (SerT κ τ) κ
| KPlug F ρ :
  rep_ok F.(fc_kind_ctx) ρ ->
  let κ := VALTYPE ρ NoRefs in
  has_kind F (PlugT κ ρ) κ
| KSpan F σ :
  size_ok F.(fc_kind_ctx) σ ->
  let κ := MEMTYPE σ NoRefs in
  has_kind F (SpanT κ σ) κ
| KRec F τ κ :
  has_kind (F <| fc_type_vars ::= cons κ |>) τ κ ->
  has_kind F (RecT κ τ) κ
| KExistsMem F τ κ :
  kind_ok F.(fc_kind_ctx) κ ->
  has_kind (F <| fc_kind_ctx ::= set kc_mem_vars S |>) τ κ ->
  has_kind F (ExistsMemT κ τ) κ
| KExistsRep F τ κ :
  kind_ok F.(fc_kind_ctx) κ ->
  has_kind (F <| fc_kind_ctx ::= set kc_rep_vars S |>) τ κ ->
  has_kind F (ExistsRepT κ τ) κ
| KExistsSize F τ κ :
  kind_ok F.(fc_kind_ctx) κ ->
  has_kind (F <| fc_kind_ctx ::= set kc_size_vars S |>) τ κ ->
  has_kind F (ExistsSizeT κ τ) κ
| KExistsType F τ κ0 κ :
  kind_ok F.(fc_kind_ctx) κ0 ->
  kind_ok F.(fc_kind_ctx) κ ->
  has_kind (F <| fc_type_vars ::= cons κ0 |>) τ κ ->
  has_kind F (ExistsTypeT κ κ0 τ) κ
| KVar F t κ :
  F.(fc_type_vars) !! t = Some κ ->
  kind_ok F.(fc_kind_ctx) κ ->
  has_kind F (VarT t) κ.

Section HasKindInd.

  Variable P : function_ctx -> type -> kind -> Prop.

  Hypotheses
      (HI31 : forall F, let κ := VALTYPE (AtomR PtrR) NoRefs in
                   P F (I31T κ) κ)
      (HI32 : forall F, let κ := VALTYPE (AtomR I32R) NoRefs in
                   P F (NumT κ (IntT I32T)) κ)
      (HI64 : forall F, let κ := VALTYPE (AtomR I64R) NoRefs in
                   P F (NumT κ (IntT I64T)) κ)
      (HF32 : forall F, let κ := VALTYPE (AtomR F32R) NoRefs in
                   P F (NumT κ (FloatT F32T)) κ)
      (HF64 : forall F, let κ := VALTYPE (AtomR F64R) NoRefs in
                   P F (NumT κ (FloatT F64T)) κ)
      (HSum : forall F τs ρs ξs, Forall3 (fun τ ρ ξ => P F τ (VALTYPE ρ ξ)) τs ρs ξs ->
                            let κ := VALTYPE (SumR ρs) (ref_flag_lub ξs) in
                            P F (SumT κ τs) κ)
      (HVariant : forall F τs σs ξs, Forall3 (fun τ σ ξ => P F τ (MEMTYPE σ ξ)) τs σs ξs ->
                                let κ := MEMTYPE (SumS σs) (ref_flag_lub ξs) in
                                P F (VariantT κ τs) κ)
      (HProd : forall F τs ρs ξs, Forall3 (fun τ ρ ξ => P F τ (VALTYPE ρ ξ)) τs ρs ξs ->
                             let κ := VALTYPE (ProdR ρs) (ref_flag_lub ξs) in
                             P F (ProdT κ τs) κ)
      (HStruct : forall F τs σs ξs, Forall3 (fun τ σ ξ => P F τ (MEMTYPE σ ξ)) τs σs ξs ->
                               let κ := MEMTYPE (ProdS σs) (ref_flag_lub ξs) in
                               P F (StructT κ τs) κ)
      (HRefVar : forall F m β τ σ ξ, mem_ok F.(fc_kind_ctx) (VarM m) ->
                                P F τ (MEMTYPE σ ξ) ->
                                let κ := VALTYPE (AtomR PtrR) AnyRefs in
                                P F (RefT κ (VarM m) β τ) κ)
      (HRefMM : forall F β τ σ ξ, P F τ (MEMTYPE σ ξ) ->
                             let κ := VALTYPE (AtomR PtrR) AnyRefs in
                             P F (RefT κ (BaseM MemMM) β τ) κ)
      (HRefGC : forall F β τ σ ξ, P F τ (MEMTYPE σ ξ) ->
                             let κ := VALTYPE (AtomR PtrR) GCRefs in
                             P F (RefT κ (BaseM MemGC) β τ) κ)
      (HCodeRef : forall F ϕ, function_type_ok F ϕ ->
                         let κ := VALTYPE (AtomR I32R) NoRefs in
                         P F (CodeRefT κ ϕ) κ)
      (HSer : forall F τ ρ ξ, P F τ (VALTYPE ρ ξ) ->
                           let κ := MEMTYPE (RepS ρ) ξ in
                           P F (SerT κ τ) κ)
      (HPlug : forall F ρ, rep_ok F.(fc_kind_ctx) ρ ->
                      let κ := VALTYPE ρ NoRefs in
                      P F (PlugT κ ρ) κ)
      (HSpan : forall F σ, size_ok F.(fc_kind_ctx) σ ->
                      let κ := MEMTYPE σ NoRefs in
                      P F (SpanT κ σ) κ)
      (HRec : forall F τ κ, P (F <| fc_type_vars ::= cons κ |>) τ κ ->
                       P F (RecT κ τ) κ)
      (HExistsMem : forall F τ κ, kind_ok F.(fc_kind_ctx) κ ->
                             P (F <| fc_kind_ctx ::= set kc_mem_vars S |>) τ κ ->
                             P F (ExistsMemT κ τ) κ)
      (HExistsRep : forall F τ κ, kind_ok F.(fc_kind_ctx) κ ->
                             P (F <| fc_kind_ctx ::= set kc_rep_vars S |>) τ κ ->
                             P F (ExistsRepT κ τ) κ)
      (HExistsSize : forall F τ κ, kind_ok F.(fc_kind_ctx) κ ->
                              P (F <| fc_kind_ctx ::= set kc_size_vars S |>) τ κ ->
                              P F (ExistsSizeT κ τ) κ)
      (HExistsType : forall F τ κ0 κ, kind_ok F.(fc_kind_ctx) κ0 ->
                                 kind_ok F.(fc_kind_ctx) κ ->
                                 P (F <| fc_type_vars ::= cons κ0 |>) τ κ ->
                                 P F (ExistsTypeT κ κ0 τ) κ)
      (HVar : forall F t κ, F.(fc_type_vars) !! t = Some κ ->
                       kind_ok F.(fc_kind_ctx) κ ->
                       P F (VarT t) κ).

  Fixpoint has_kind_ind' (F : function_ctx) (τ : type) (κ : kind) (H : has_kind F τ κ) : P F τ κ :=
    match H with
    | KI31 F => HI31 F
    | KI32 F => HI32 F
    | KI64 F => HI64 F
    | KF32 F => HF32 F
    | KF64 F => HF64 F
    | KSum F τs ρs ξs H1 =>
        HSum F τs ρs ξs (Forall3_impl _ _ _ _ _ H1 (fun τ ρ ξ => has_kind_ind' _ _ _))
    | KVariant F τs σs ξs H1 =>
        HVariant F τs σs ξs (Forall3_impl _ _ _ _ _ H1 (fun τ σ ξ => has_kind_ind' _ _ _))
    | KProd F τs ρs ξs H1 H2 =>
        HProd F τs ρs ξs (Forall3_impl _ _ _ _ _ H1 (fun τ ρ ξ => has_kind_ind' _ _ _))
    | KStruct F τs σs ξs H1 =>
        HStruct F τs σs ξs (Forall3_impl _ _ _ _ _ H1 (fun τ σ ξ => has_kind_ind' _ _ _))
    | KRefVar F m β τ σ ξ H1 H2 => HRefVar F m β τ σ ξ H1 (has_kind_ind' _ _ _ H2)
    | KRefMM F β τ σ ξ H1 => HRefMM F β τ σ ξ (has_kind_ind' _ _ _ H1)
    | KRefGC F β τ σ ξ H1 => HRefGC F β τ σ ξ (has_kind_ind' _ _ _ H1)
    | KCodeRef F ϕ H1 => HCodeRef F ϕ H1
    | KSer F τ ρ ξ H1 => HSer F τ ρ ξ (has_kind_ind' _ _ _ H1)
    | KPlug F ρ H1 => HPlug F ρ H1
    | KSpan F σ H1 => HSpan F σ H1
    | KRec F τ κ H1 => HRec F τ κ (has_kind_ind' _ _ _ H1)
    | KExistsMem F τ κ H1 H2 => HExistsMem F τ κ H1 (has_kind_ind' _ _ _ H2)
    | KExistsRep F τ κ H1 H2 => HExistsRep F τ κ H1 (has_kind_ind' _ _ _ H2)
    | KExistsSize F τ κ H1 H2 => HExistsSize F τ κ H1 (has_kind_ind' _ _ _ H2)
    | KExistsType F τ κ0 κ H1 H2 H3 => HExistsType F τ κ0 κ H1 H2 (has_kind_ind' _ _ _ H3)
    | KVar F t κ H1 H2 => HVar F t κ H1 H2
    end.

End HasKindInd.

Lemma kind_ok_subkind_of F κ κ' : kind_ok F κ -> subkind_of κ κ' -> kind_ok F κ'.
Proof.
  intros H1 H2.
  induction H2; repeat constructor; by inversion H1.
Qed.

Lemma has_kind_inv F τ κ : has_kind F τ κ -> has_kind_ok F τ κ.
Proof.
  intros H.
  induction H using has_kind_ind'; repeat constructor; try inversion IHhas_kind; try done.
  13: by inversion H.
  13, 14: by inversion H0.
  13: by econstructor.
  all: apply Forall_forall; intros ? Hin; apply list_elem_of_lookup in Hin as [??].
  - by eapply Forall3_lookup_m in H as (?&?&?&?&H); first (inversion H; inversion H4).
  - by eapply Forall3_lookup_l in H as (?&?&?&?&H); first inversion H.
  - by eapply Forall3_lookup_m in H as (?&?&?&?&H); first (inversion H; inversion H4).
  - by eapply Forall3_lookup_m in H as (?&?&?&?&H); first (inversion H; inversion H4).
  - by eapply Forall3_lookup_l in H as (?&?&?&?&H); first inversion H.
  - by eapply Forall3_lookup_m in H as (?&?&?&?&H); first (inversion H; inversion H4).
  - by eapply Forall3_lookup_m in H as (?&?&?&?&H); first (inversion H; inversion H4).
  - by eapply Forall3_lookup_l in H as (?&?&?&?&H); first inversion H.
  - by eapply Forall3_lookup_m in H as (?&?&?&?&H); first (inversion H; inversion H4).
  - by eapply Forall3_lookup_m in H as (?&?&?&?&H); first (inversion H; inversion H4).
  - by eapply Forall3_lookup_l in H as (?&?&?&?&H); first inversion H.
  - by eapply Forall3_lookup_m in H as (?&?&?&?&H); first (inversion H; inversion H4).
Qed.

Inductive has_rep : function_ctx -> type -> representation -> Prop :=
| HasRep F τ ρ ξ :
  has_kind F τ (VALTYPE ρ ξ) ->
  has_rep F τ ρ.

Definition is_mono_rep : representation -> Prop :=
  rep_ok kc_empty.

Definition has_mono_rep (F : function_ctx) (τ : type) : Prop :=
  exists ρ, has_rep F τ ρ /\ is_mono_rep ρ.
  
Definition has_mono_rep_instr (F : function_ctx) '(InstrT τs1 τs2 : instruction_type) : Prop :=
  Forall (has_mono_rep F) τs1 /\ Forall (has_mono_rep F) τs2.

Definition has_size (F : function_ctx) (τ : type) (σ : size) : Prop :=
  exists ξ, has_kind F τ (MEMTYPE σ ξ).

Definition is_mono_size : size -> Prop :=
  size_ok kc_empty.

Inductive has_mono_size : function_ctx -> type -> Prop :=
| HasMonoSize F τ σ ξ :
  has_kind F τ (MEMTYPE σ ξ) ->
  is_mono_size σ ->
  has_mono_size F τ.

Definition type_rep_eq_prim (F : function_ctx) (τ : type) (ηs : list primitive) : Prop :=
  exists ρ, has_rep F τ ρ /\ eval_rep_prim EmptyEnv ρ = Some ηs.

Definition size_eq (σ1 σ2 : size) : Prop :=
  exists n, eval_size EmptyEnv σ1 = Some n /\ eval_size EmptyEnv σ2 = Some n.

Definition size_leq (σ1 σ2 : size) : Prop :=
  exists n m, eval_size EmptyEnv σ1 = Some n /\ eval_size EmptyEnv σ2 = Some m /\ n <= m.

Definition type_size_eq (F : function_ctx) (τ1 τ2 : type) : Prop :=
  exists σ1 σ2, has_size F τ1 σ1 /\ has_size F τ2 σ2 /\ size_eq σ1 σ2.

Definition has_ref_flag (F : function_ctx) (τ : type) (ξ : ref_flag) : Prop :=
  exists κ, has_kind F τ κ /\ ref_flag_le (kind_ref_flag κ) ξ.

Record path_result :=
  { pr_prefix : list type;
    pr_target : type;
    pr_replaced : type }.

Inductive resolves_path : type -> path -> option type -> path_result -> Prop :=
| PathNilNone τ :
  resolves_path τ [] None (Build_path_result [] τ τ)
| PathNilSome τ τ' :
  resolves_path τ [] (Some τ') (Build_path_result [] τ τ')
| PathStruct pr i π τ__π τs0 τ τs' κ κ' :
  length τs0 = i ->
  resolves_path τ π τ__π pr ->
  let pr' :=
    {| pr_prefix := τs0 ++ pr.(pr_prefix);
       pr_target := pr.(pr_target);
       pr_replaced := StructT κ' (τs0 ++ pr.(pr_replaced) :: τs') |}
  in
  resolves_path (StructT κ (τs0 ++ τ :: τs')) (i :: π) τ__π pr'.

Inductive type_eq : type -> type -> Prop :=
| TEqRefl τ :
  type_eq τ τ
| TEqSum κ τs τs' :
  Forall2 type_eq τs τs' ->
  type_eq (SumT κ τs) (SumT κ τs')
| TEqVariant κ τs τs' :
  Forall2 type_eq τs τs' ->
  type_eq (VariantT κ τs) (VariantT κ τs')
| TEqProd κ τs τs' :
  Forall2 type_eq τs τs' ->
  type_eq (ProdT κ τs) (ProdT κ τs')
| TEqStruct κ τs τs' :
  Forall2 type_eq τs τs' ->
  type_eq (StructT κ τs) (StructT κ τs')
| TEqRef κ μ β τ τ' :
  type_eq τ τ' ->
  type_eq (RefT κ μ β τ) (RefT κ μ β τ')
| TEqSer κ τ τ' :
  type_eq τ τ' ->
  type_eq (SerT κ τ) (SerT κ τ')
| TEqRec κ τ τ' :
  type_eq τ τ' ->
  type_eq (RecT κ τ) (RecT κ τ')
| TEqExMem κ τ τ' :
  type_eq τ τ' ->
  type_eq (ExistsMemT κ τ) (ExistsMemT κ τ')
| TEqExRep κ τ τ' :
  type_eq τ τ' ->
  type_eq (ExistsRepT κ τ) (ExistsRepT κ τ')
| TEqExSize κ τ τ' :
  type_eq τ τ' ->
  type_eq (ExistsSizeT κ τ) (ExistsSizeT κ τ')
| TEqExType κ κτ τ τ' :
  type_eq τ τ' ->
  type_eq (ExistsTypeT κ κτ τ) (ExistsTypeT κ κτ τ')
| TEqSerProd κ_ser κ_prod κ_struct κs_ser τs τs' :
  Forall2 type_eq τs τs' ->
  type_eq (SerT κ_ser (ProdT κ_prod τs)) (StructT κ_struct (zip_with SerT κs_ser τs'))
| TEqProdSer κ_ser κ_prod κ_struct κs_ser τs τs' :
  Forall2 type_eq τs τs' ->
  type_eq (StructT κ_struct (zip_with SerT κs_ser τs)) (SerT κ_ser (ProdT κ_prod τs')).

(* NOTE: structural equality up to cached kind annotations, which [subst] can't refresh --
   a strict-subkind instantiation leaves them stale (ref-flags are literals, not vars). *)
Fixpoint type_eq_mod_kinds (τ1 τ2 : type) {struct τ1} : Prop :=
  let fix types_eq (τs1 τs2 : list type) {struct τs1} : Prop :=
    match τs1, τs2 with
    | [], [] => True
    | σ1 :: τs1, σ2 :: τs2 => type_eq_mod_kinds σ1 σ2 /\ types_eq τs1 τs2
    | _, _ => False
    end in
  match τ1, τ2 with
  | VarT i1, VarT i2 => i1 = i2
  | I31T _, I31T _ => True
  | NumT _ nt1, NumT _ nt2 => nt1 = nt2
  | SumT _ τs1, SumT _ τs2 => types_eq τs1 τs2
  | VariantT _ τs1, VariantT _ τs2 => types_eq τs1 τs2
  | ProdT _ τs1, ProdT _ τs2 => types_eq τs1 τs2
  | StructT _ τs1, StructT _ τs2 => types_eq τs1 τs2
  | RefT _ μ1 β1 τ1, RefT _ μ2 β2 τ2 => μ1 = μ2 /\ β1 = β2 /\ type_eq_mod_kinds τ1 τ2
  | CodeRefT _ ϕ1, CodeRefT _ ϕ2 => function_type_eq_mod_kinds ϕ1 ϕ2
  | SerT _ τ1, SerT _ τ2 => type_eq_mod_kinds τ1 τ2
  | PlugT _ ρ1, PlugT _ ρ2 => ρ1 = ρ2
  | SpanT _ σ1, SpanT _ σ2 => σ1 = σ2
  | RecT _ τ1, RecT _ τ2 => type_eq_mod_kinds τ1 τ2
  | ExistsMemT _ τ1, ExistsMemT _ τ2 => type_eq_mod_kinds τ1 τ2
  | ExistsRepT _ τ1, ExistsRepT _ τ2 => type_eq_mod_kinds τ1 τ2
  | ExistsSizeT _ τ1, ExistsSizeT _ τ2 => type_eq_mod_kinds τ1 τ2
  | ExistsTypeT _ κ01 τ1, ExistsTypeT _ κ02 τ2 => κ01 = κ02 /\ type_eq_mod_kinds τ1 τ2
  | _, _ => False
  end
with function_type_eq_mod_kinds (ϕ1 ϕ2 : function_type) {struct ϕ1} : Prop :=
  let fix types_eq (τs1 τs2 : list type) {struct τs1} : Prop :=
    match τs1, τs2 with
    | [], [] => True
    | σ1 :: τs1, σ2 :: τs2 => type_eq_mod_kinds σ1 σ2 /\ types_eq τs1 τs2
    | _, _ => False
    end in
  match ϕ1, ϕ2 with
  | MonoFunT τs11 τs12, MonoFunT τs21 τs22 =>
      types_eq τs11 τs21 /\ types_eq τs12 τs22
  | ForallMemT ϕ1, ForallMemT ϕ2 => function_type_eq_mod_kinds ϕ1 ϕ2
  | ForallRepT ϕ1, ForallRepT ϕ2 => function_type_eq_mod_kinds ϕ1 ϕ2
  | ForallSizeT ϕ1, ForallSizeT ϕ2 => function_type_eq_mod_kinds ϕ1 ϕ2
  | ForallTypeT κ1 ϕ1, ForallTypeT κ2 ϕ2 => κ1 = κ2 /\ function_type_eq_mod_kinds ϕ1 ϕ2
  | _, _ => False
  end.

Inductive function_type_inst : function_ctx -> index -> function_type -> function_type -> Prop :=
| FTInstMem F ϕ μ :
  mem_ok F.(fc_kind_ctx) μ ->
  let ϕ' := subst_function_type (unscoped.scons μ VarM) VarR VarS VarT ϕ in
  function_type_inst F (MemI μ) (ForallMemT ϕ) ϕ'
| FTInstRep F ϕ ρ :
  rep_ok F.(fc_kind_ctx) ρ ->
  let ϕ' := subst_function_type VarM (unscoped.scons ρ VarR) VarS VarT ϕ in
  function_type_inst F (RepI ρ) (ForallRepT ϕ) ϕ'
| FTInstSize F ϕ σ :
  size_ok F.(fc_kind_ctx) σ ->
  let ϕ' := subst_function_type VarM VarR (unscoped.scons σ VarS) VarT ϕ in
  function_type_inst F (SizeI σ) (ForallSizeT ϕ) ϕ'
| FTInstType F ϕ τ κ κ' ϕ' :
  has_kind F τ κ' ->
  subkind_of κ' κ ->
  (* NOTE: the raw subst is ill-kinded under a strict-subkind instantiation *)
  function_type_ok F ϕ' ->
  function_type_eq_mod_kinds ϕ'
    (subst_function_type VarM VarR VarS (unscoped.scons τ VarT) ϕ) ->
  function_type_inst F (TypeI τ) (ForallTypeT κ ϕ) ϕ'.

Inductive function_type_insts : function_ctx -> list index -> function_type -> function_type -> Prop :=
| FTNil F ϕ :
  function_type_insts F [] ϕ ϕ
| FTCons F ϕ ϕ' ϕ'' ix ixs :
  function_type_inst F ix ϕ ϕ' ->
  function_type_insts F ixs ϕ' ϕ'' ->
  function_type_insts F (ix :: ixs) ϕ ϕ''.

Inductive packed_existential : function_ctx -> type -> type -> Prop :=
| PackMem F μ τ' κ' :
  let τ0 := subst_type (unscoped.scons μ VarM) VarR VarS VarT τ' in
  packed_existential F τ0 (ExistsMemT κ' τ')
| PackRep F ρ τ' κ' :
  let τ0 := subst_type VarM (unscoped.scons ρ VarR) VarS VarT τ' in
  packed_existential F τ0 (ExistsRepT κ' τ')
| PackSize F σ τ' κ' :
  let τ0 := subst_type VarM VarR (unscoped.scons σ VarS) VarT τ' in
  packed_existential F τ0 (ExistsSizeT κ' τ')
(* NOTE: same as FTInstType -- [τ0] is the well-kinded type with the raw subst's shape. *)
| PackType F τ_wit τ_in κ_wit κ_max κ_ex τ0 :
  has_kind F τ_wit κ_wit ->
  subkind_of κ_wit κ_max ->
  type_ok F τ0 ->
  type_eq_mod_kinds τ0
    (subst_type VarM VarR VarS (unscoped.scons τ_wit VarT) τ_in) ->
  packed_existential F τ0 (ExistsTypeT κ_ex κ_max τ_in).

Inductive unpacked_existential :
  function_ctx -> local_ctx -> instruction_type -> local_ctx ->
  function_ctx -> local_ctx -> instruction_type -> local_ctx ->
  Prop :=
| UnpackMem F L L' τs1 κ τ τs2 :
  let F0 :=
    subst_function_ctx (up_memory VarM) VarR VarS VarT F <| fc_kind_ctx ::= set kc_mem_vars S |>
  in
  let up := ren_type S id id id in
  unpacked_existential
    F L (InstrT (τs1 ++ [ExistsMemT κ τ]) τs2) L'
    F0 (map up L) (InstrT (map up τs1 ++ [τ]) (map up τs2)) (map up L')
| UnpackRep F L L' τs1 κ τ τs2 :
  let F0 :=
    subst_function_ctx VarM (up_representation VarR) VarS VarT F <| fc_kind_ctx ::= set kc_rep_vars S |>
  in
  let up := ren_type id S id id in
  unpacked_existential
    F L (InstrT (τs1 ++ [ExistsRepT κ τ]) τs2) L'
    F0 (map up L) (InstrT (map up τs1 ++ [τ]) (map up τs2)) (map up L')
| UnpackSize F L L' τs1 κ τ τs2 :
  let F0 :=
    subst_function_ctx VarM VarR (up_size VarS) VarT F <| fc_kind_ctx ::= set kc_size_vars S |>
  in
  let up := ren_type id id S id in
  unpacked_existential
    F L (InstrT (τs1 ++ [ExistsSizeT κ τ]) τs2) L'
    F0 (map up L) (InstrT (map up τs1 ++ [τ]) (map up τs2)) (map up L')
| UnpackType F L L' τs1 κ κ0 τ τs2 :
  let F0 := subst_function_ctx VarM VarR VarS (up_type VarT) F <| fc_type_vars ::= cons κ0 |> in
  let up := ren_type id id id S in
  unpacked_existential
    F L (InstrT (τs1 ++ [ExistsTypeT κ κ0 τ]) τs2) L'
    F0 (map up L) (InstrT (map up τs1 ++ [τ]) (map up τs2)) (map up L').

Definition local_ctx_ok (F : function_ctx) (L : local_ctx) : Prop :=
  Forall2 (type_rep_eq_prim F) L F.(fc_locals).

Definition has_instruction_type_ok (F : function_ctx) (ψ : instruction_type) (L' : local_ctx) : Prop :=
  has_mono_rep_instr F ψ /\ local_ctx_ok F L'.

Inductive has_instruction_type_cvt : conversion_op -> instruction_type -> Prop :=
| TWrapC :
  has_instruction_type_cvt CWrap (InstrT [type_i64] [type_i32])
| TExtend s :
  has_instruction_type_cvt (CExtend s) (InstrT [type_i32] [type_i64])
| TTrunc νf νi s :
  has_instruction_type_cvt (CTrunc νf νi s) (InstrT [float_type_type νf] [int_type_type νi])
| TDemote :
  has_instruction_type_cvt CDemote (InstrT [type_f64] [type_f32])
| TPromote :
  has_instruction_type_cvt CPromote (InstrT [type_f32] [type_f64])
| TConvert νi νf s :
  has_instruction_type_cvt (CConvert νi νf s) (InstrT [int_type_type νi] [float_type_type νf])
| TReinterpretI32 :
  has_instruction_type_cvt (CReinterpret (IntT I32T)) (InstrT [type_i32] [type_f32])
| TReinterpretI64 :
  has_instruction_type_cvt (CReinterpret (IntT I64T)) (InstrT [type_i64] [type_f64])
| TReinterpretF32 :
  has_instruction_type_cvt (CReinterpret (FloatT F32T)) (InstrT [type_f32] [type_i32])
| TReinterpretF64 :
  has_instruction_type_cvt (CReinterpret (FloatT F64T)) (InstrT [type_f64] [type_i64]).

Inductive has_instruction_type_num : num_instruction -> instruction_type -> Prop :=
| TInt1 νi op :
  let τ := int_type_type νi in
  has_instruction_type_num (IInt1 νi op) (InstrT [τ] [τ])
| TInt2 νi op :
  let τ := int_type_type νi in
  has_instruction_type_num (IInt2 νi op) (InstrT [τ; τ] [τ])
| TIntTest νi op :
  let τ := int_type_type νi in
  has_instruction_type_num (IIntTest νi op) (InstrT [τ] [type_i32])
| TIntRel νi op :
  let τ := int_type_type νi in
  has_instruction_type_num (IIntRel νi op) (InstrT [τ; τ] [type_i32])
| TFloat1 νf op :
  let τ := float_type_type νf in
  has_instruction_type_num (IFloat1 νf op) (InstrT [τ] [τ])
| TFloat2 νf op :
  let τ := float_type_type νf in
  has_instruction_type_num (IFloat2 νf op) (InstrT [τ; τ] [τ])
| TFloatRel νf op :
  let τ := float_type_type νf in
  has_instruction_type_num (IFloatRel νf op) (InstrT [τ; τ] [type_i32])
| TCvt op ψ :
  has_instruction_type_cvt op ψ ->
  has_instruction_type_num (ICvt op) ψ.

Inductive has_instruction_type :
  module_ctx -> function_ctx -> local_ctx -> instruction -> instruction_type -> local_ctx -> Prop :=
| TNop M F L :
  let ψ := InstrT [] [] in
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (INop ψ) ψ L
| TUnreachable M F L L' ψ :
  has_instruction_type_ok F ψ L' ->
  has_instruction_type M F L (IUnreachable ψ) ψ L'
| TCopy M F L τ :
  let ψ := InstrT [τ] [τ; τ] in
  has_ref_flag F τ GCRefs ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (ICopy ψ) ψ L
| TDrop M F L τ :
  let ψ := InstrT [τ] [] in
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IDrop ψ) ψ L
| TNum M F L e ψ :
  has_instruction_type_num e ψ ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (INum ψ e) ψ L
| TNumConst M F L ν n :
  let ψ := InstrT [] [num_type_type ν] in
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (INumConst ψ n) ψ L
| TBlock M F L L' τs1 τs2 es :
  let F' := F <| fc_labels ::= cons (τs2, L') |> in
  let ψ := InstrT τs1 τs2 in
  have_instruction_type M F' L es ψ L' ->
  has_instruction_type_ok F ψ L' ->
  has_instruction_type M F L (IBlock ψ L' es) ψ L'
| TLoop M F L τs1 τs2 es :
  let F' := F <| fc_labels ::= cons (τs1, L) |> in
  let ψ := InstrT τs1 τs2 in
  have_instruction_type M F' L es ψ L ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (ILoop ψ es) ψ L
| TIte M F L L' τs1 τs2 es1 es2 :
  let F' := F <| fc_labels ::= cons (τs2, L') |> in
  let ψ := InstrT (τs1 ++ [type_i32]) τs2 in
  have_instruction_type M F' L es1 (InstrT τs1 τs2) L' ->
  have_instruction_type M F' L es2 (InstrT τs1 τs2) L' ->
  has_instruction_type_ok F ψ L' ->
  has_instruction_type M F L (IIte ψ L' es1 es2) ψ L'
| TBr M F L L' i τs τs1 τs2 :
  let ψ := InstrT (τs1 ++ τs) τs2 in
  F.(fc_labels) !! i = Some (τs, L) ->
  Forall (fun τ => has_ref_flag F τ NoRefs) τs1 ->
  has_instruction_type_ok F ψ L' ->
  has_instruction_type M F L (IBr ψ i) ψ L'
| TReturn M F L L' τs τs1 τs2 :
  let ψ := InstrT (τs1 ++ τs) τs2 in
  F.(fc_return) = τs ->
  Forall (fun τ => has_ref_flag F τ NoRefs) τs1 ->
  has_instruction_type_ok F ψ L' ->
  has_instruction_type M F L (IReturn ψ) ψ L'
| TLocalGetCopy M F L i τ :
  let ψ := InstrT [] [τ] in
  L !! i = Some τ ->
  has_ref_flag F τ NoRefs ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (ILocalGet ψ Copy i) ψ L
| TLocalGetMove M F L i τ ηs :
  let ψ := InstrT [] [τ] in
  let L' := <[ i := type_plug_prim ηs ]> L in
  F.(fc_locals) !! i = Some ηs ->
  L !! i = Some τ ->
  has_instruction_type_ok F ψ L' ->
  has_instruction_type M F L (ILocalGet ψ Move i) ψ L'
| TLocalSet M F L i τ τ0 :
  let ψ := InstrT [τ] [] in
  let L' := <[ i := τ ]> L in
  L !! i = Some τ0 ->
  has_ref_flag F τ0 NoRefs ->
  has_instruction_type_ok F ψ L' ->
  has_instruction_type M F L (ILocalSet ψ i) ψ L'
| TCodeRef M F L i ϕ :
  let τ := CodeRefT (VALTYPE (AtomR I32R) NoRefs) ϕ in
  let ψ := InstrT [] [τ] in
  M.(mc_table) !! i = Some ϕ ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (ICodeRef ψ i) ψ L
| TInst M F L ix ϕ ϕ' :
  let κ := VALTYPE (AtomR I32R) NoRefs in
  let ψ := InstrT [CodeRefT κ ϕ] [CodeRefT κ ϕ'] in
  function_type_inst F ix ϕ ϕ' ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IInst ψ ix) ψ L
| TCall M F L i ixs ϕ τs1 τs2 :
  let ψ := InstrT τs1 τs2 in
  M.(mc_functions) !! i = Some ϕ ->
  function_type_insts F ixs ϕ (MonoFunT τs1 τs2) ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (ICall ψ i ixs) ψ L
| TCallIndirect M F L τs1 τs2 :
  let κ := VALTYPE (AtomR I32R) NoRefs in
  let ψ := InstrT (τs1 ++ [CodeRefT κ (MonoFunT τs1 τs2)]) τs2 in
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (ICallIndirect ψ) ψ L
| TInject M F L i τ τs κ :
  let ψ := InstrT [τ] [SumT κ τs] in
  τs !! i = Some τ ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IInject ψ i) ψ L
| TInjectNew M F L i μ τ τs κr κv κs :
  let τs' := zip_with SerT κs τs in
  let ψ := InstrT [τ] [RefT κr μ Imm (VariantT κv τs')] in
  τs !! i = Some τ ->
  mono_mem μ ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IInjectNew ψ i) ψ L
| TCase M F L L' ess τs τs' κ :
  let F' := F <| fc_labels ::= cons (τs', L') |> in
  let ψ := InstrT [SumT κ τs] τs' in
  Forall2 (fun τ es => have_instruction_type M F' L es (InstrT [τ] τs') L') τs ess ->
  has_instruction_type_ok F ψ L' ->
  has_instruction_type M F L (ICase ψ L' ess) ψ L'
| TCaseLoadCopy M F L L' ess τs τs' κr κv κs μ :
  let F' := F <| fc_labels ::= cons (τs', L') |> in
  let τs_ser := zip_with SerT κs τs in
  let ψ := InstrT [RefT κr μ Imm (VariantT κv τs_ser)] (RefT κr μ Imm (VariantT κv τs_ser) :: τs') in
  Forall (fun τ => has_ref_flag F τ GCRefs) τs ->
  Forall2 (fun τ es => have_instruction_type M F' L es (InstrT [τ] τs') L') τs ess ->
  has_instruction_type_ok F ψ L' ->
  has_instruction_type M F L (ICaseLoad ψ Copy L' ess) ψ L'
| TCaseLoadMove M F L L' ess τs τs' κr κv κs :
  let F' := F <| fc_labels ::= cons (τs', L') |> in
  let τs_ser := zip_with SerT κs τs in
  let ψ := InstrT [RefT κr (BaseM MemMM) Imm (VariantT κv τs_ser)] τs' in
  Forall2 (fun τ es => have_instruction_type M F' L es (InstrT [τ] τs') L') τs ess ->
  has_instruction_type_ok F ψ L' ->
  has_instruction_type M F L (ICaseLoad ψ Move L' ess) ψ L'
| TGroup M F L τs κ :
  let ψ := InstrT τs [ProdT κ τs] in
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IGroup ψ) ψ L
| TUngroup M F L τs κ :
  let ψ := InstrT [ProdT κ τs] τs in
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IUngroup ψ) ψ L
| TFold M F L τ κ :
  let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
  let ψ := InstrT [τ0] [RecT κ τ] in
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IFold ψ) ψ L
| TUnfold M F L τ κ :
  let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
  let ψ := InstrT [RecT κ τ] [τ0] in
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IUnfold ψ) ψ L
| TPack M F L τ τ' :
  let ψ := InstrT [τ] [τ'] in
  packed_existential F τ τ' ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IPack ψ) ψ L
| TUnpack M F F0' L L' L0 L0' es τs1 τs2 ψ0 :
  let F' := F <| fc_labels ::= cons (τs2, L') |> in
  let ψ := InstrT τs1 τs2 in
  unpacked_existential F' L ψ L' F0' L0 ψ0 L0' ->
  have_instruction_type M F0' L0 es ψ0 L0' ->
  has_instruction_type_ok F ψ L' ->
  has_instruction_type M F L (IUnpack ψ L' es) ψ L'
| TTag M F L :
  let ψ := InstrT [type_i32] [type_i31] in
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (ITag ψ) ψ L
| TUntag M F L :
  let ψ := InstrT [type_i31] [type_i32] in
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IUntag ψ) ψ L
| TCast M F L τ τ' :
  let ψ := InstrT [τ] [τ'] in
  type_eq τ τ' ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (ICast ψ) ψ L
| TNew M F L μ β τ κ κser :
  let ψ := InstrT [τ] [RefT κ μ β (SerT κser τ)] in
  mono_mem μ ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (INew ψ) ψ L
| TLoadCopy M F L π μ β τ τval pr κ κser :
  let ψ := InstrT [RefT κ μ β τ] [RefT κ μ β τ; τval] in
  has_ref_flag F τval GCRefs ->
  resolves_path τ π None pr ->
  pr.(pr_target) = SerT κser τval ->
  Forall (has_mono_size F) pr.(pr_prefix) ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (ILoad ψ π Copy) ψ L
| TLoadMove M F L π τ τval κ κ' κser σ pr :
  let ψ := InstrT [RefT κ (BaseM MemMM) Mut τ] [RefT κ' (BaseM MemMM) Mut pr.(pr_replaced); τval] in
  resolves_path τ π (Some (type_span σ)) pr ->
  has_size F pr.(pr_target) σ ->
  pr.(pr_target) = SerT κser τval ->
  Forall (has_mono_size F) pr.(pr_prefix) ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (ILoad ψ π Move) ψ L
| TStoreWeak M F L π μ τ τval pr κ κser :
  let ψ := InstrT [RefT κ μ Mut τ; τval] [RefT κ μ Mut τ] in
  resolves_path τ π None pr ->
  has_ref_flag F pr.(pr_target) GCRefs ->
  pr.(pr_target) = SerT κser τval ->
  Forall (has_mono_size F) pr.(pr_prefix) ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IStore ψ π) ψ L
| TStoreStrong M F L π τ τval pr σ ρ κ κ' κser :
  let ψ := InstrT [RefT κ (BaseM MemMM) Mut τ; τval] [RefT κ' (BaseM MemMM) Mut pr.(pr_replaced)] in
  resolves_path τ π (Some (SerT κser τval)) pr ->
  has_ref_flag F pr.(pr_target) GCRefs ->
  has_size F pr.(pr_target) σ ->
  has_rep F τval ρ ->
  eval_size EmptyEnv σ = eval_rep_size EmptyEnv ρ ->
  Forall (has_mono_size F) pr.(pr_prefix) ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (IStore ψ π) ψ L
| TSwap M F L π τ τval pr κ κser μ :
  let ψ := InstrT [RefT κ μ Mut τ; τval] [RefT κ μ Mut τ; τval] in
  resolves_path τ π None pr ->
  Forall (has_mono_size F) pr.(pr_prefix) ->
  pr.(pr_target) = SerT κser τval ->
  has_instruction_type_ok F ψ L ->
  has_instruction_type M F L (ISwap ψ π) ψ L

with have_instruction_type :
  module_ctx -> function_ctx -> local_ctx -> list instruction -> instruction_type -> local_ctx -> Prop :=
| TNil M F L :
  local_ctx_ok F L ->
  have_instruction_type M F L [] (InstrT [] []) L
| TApp M F L1 L2 L3 es es' τs1 τs2 τs3 :
  have_instruction_type M F L1 es (InstrT τs1 τs2) L2 ->
  have_instruction_type M F L2 es' (InstrT τs2 τs3) L3 ->
  have_instruction_type M F L1 (es ++ es') (InstrT τs1 τs3) L3
| TSingleton M F L L' e ψ :
  has_instruction_type M F L e ψ L' ->
  have_instruction_type M F L [e] ψ L'
| TFrame M F L L' es τ τs1 τs2 :
  has_mono_rep F τ ->
  have_instruction_type M F L es (InstrT τs1 τs2) L' ->
  have_instruction_type M F L es (InstrT (τ :: τs1) (τ :: τs2)) L'.

Section HasHaveInstructionTypeMind.

  Variables
    (P1 : module_ctx -> function_ctx -> local_ctx -> instruction -> instruction_type -> local_ctx -> Prop)
      (P2 : module_ctx -> function_ctx -> local_ctx -> list instruction -> instruction_type -> local_ctx ->
            Prop).

  Hypotheses
    (HNop : forall M F L,
        let ψ := InstrT [] [] in
        has_instruction_type_ok F ψ L ->
        P1 M F L (INop ψ) ψ L)
      (HUnreachable : forall M F L L' ψ,
          has_instruction_type_ok F ψ L' ->
          P1 M F L (IUnreachable ψ) ψ L')
      (HCopy : forall M F L τ,
          let ψ := InstrT [τ] [τ; τ] in
          has_ref_flag F τ GCRefs ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (ICopy ψ) ψ L)
      (HDrop : forall M F L τ,
          let ψ := InstrT [τ] [] in
          has_instruction_type_ok F ψ L ->
          P1 M F L (IDrop ψ) ψ L)
      (HNum : forall M F L e ψ,
          has_instruction_type_num e ψ ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (INum ψ e) ψ L)
      (HNumConst : forall M F L ν n,
          let ψ := InstrT [] [num_type_type ν] in
          has_instruction_type_ok F ψ L ->
          P1 M F L (INumConst ψ n) ψ L)
      (HBlock : forall M F L L' τs1 τs2 es,
          let F' := F <| fc_labels ::= cons (τs2, L') |> in
          let ψ := InstrT τs1 τs2 in
          P2 M F' L es ψ L' ->
          has_instruction_type_ok F ψ L' ->
          P1 M F L (IBlock ψ L' es) ψ L')
      (HLoop : forall M F L τs1 τs2 es,
          let F' := F <| fc_labels ::= cons (τs1, L) |> in
          let ψ := InstrT τs1 τs2 in
          P2 M F' L es ψ L ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (ILoop ψ es) ψ L)
      (HIte : forall M F L L' τs1 τs2 es1 es2,
          let F' := F <| fc_labels ::= cons (τs2, L') |> in
          let ψ := InstrT (τs1 ++ [type_i32]) τs2 in
          P2 M F' L es1 (InstrT τs1 τs2) L' ->
          P2 M F' L es2 (InstrT τs1 τs2) L' ->
          has_instruction_type_ok F ψ L' ->
          P1 M F L (IIte ψ L' es1 es2) ψ L')
      (HBr : forall M F L L' i τs τs1 τs2,
          let ψ := InstrT (τs1 ++ τs) τs2 in
          F.(fc_labels) !! i = Some (τs, L) ->
          Forall (fun τ => has_ref_flag F τ NoRefs) τs1 ->
          has_instruction_type_ok F ψ L' ->
          P1 M F L (IBr ψ i) ψ L')
      (HReturn : forall M F L L' τs τs1 τs2,
          let ψ := InstrT (τs1 ++ τs) τs2 in
          F.(fc_return) = τs ->
          Forall (fun τ => has_ref_flag F τ NoRefs) τs1 ->
          has_instruction_type_ok F ψ L' ->
          P1 M F L (IReturn ψ) ψ L')
      (HLocalGetCopy : forall M F L i τ,
          let ψ := InstrT [] [τ] in
          L !! i = Some τ ->
          has_ref_flag F τ NoRefs ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (ILocalGet ψ Copy i) ψ L)
      (HLocalGetMove : forall M F L i τ ηs,
          let ψ := InstrT [] [τ] in
          let L' := <[ i := type_plug_prim ηs ]> L in
          F.(fc_locals) !! i = Some ηs ->
          L !! i = Some τ ->
          has_instruction_type_ok F ψ L' ->
          P1 M F L (ILocalGet ψ Move i) ψ L')
      (HLocalSet : forall M F L i τ τ0,
          let ψ := InstrT [τ] [] in
          let L' := <[ i := τ ]> L in
          L !! i = Some τ0 ->
          has_ref_flag F τ0 NoRefs ->
          has_instruction_type_ok F ψ L' ->
          P1 M F L (ILocalSet ψ i) ψ L')
      (HCodeRef : forall M F L i ϕ,
          let τ := CodeRefT (VALTYPE (AtomR I32R) NoRefs) ϕ in
          let ψ := InstrT [] [τ] in
          M.(mc_table) !! i = Some ϕ ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (ICodeRef ψ i) ψ L)
      (HInst : forall M F L ix ϕ ϕ',
          let κ := VALTYPE (AtomR I32R) NoRefs in
          let ψ := InstrT [CodeRefT κ ϕ] [CodeRefT κ ϕ'] in
          function_type_inst F ix ϕ ϕ' ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (IInst ψ ix) ψ L)
      (HCall : forall M F L i ixs ϕ τs1 τs2,
          let ψ := InstrT τs1 τs2 in
          M.(mc_functions) !! i = Some ϕ ->
          function_type_insts F ixs ϕ (MonoFunT τs1 τs2) ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (ICall ψ i ixs) ψ L)
      (HCallIndirect : forall M F L τs1 τs2,
          let κ := VALTYPE (AtomR I32R) NoRefs in
          let ψ := InstrT (τs1 ++ [CodeRefT κ (MonoFunT τs1 τs2)]) τs2 in
          has_instruction_type_ok F ψ L ->
          P1 M F L (ICallIndirect ψ) ψ L)
      (HInject : forall M F L i τ τs κ,
          let ψ := InstrT [τ] [SumT κ τs] in
          τs !! i = Some τ ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (IInject ψ i) ψ L)
      (HInjectNew : forall M F L i μ τ τs κr κv κs,
          let τs' := zip_with SerT κs τs in
          let ψ := InstrT [τ] [RefT κr μ Imm (VariantT κv τs')] in
          τs !! i = Some τ ->
          mono_mem μ ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (IInjectNew ψ i) ψ L)
      (HCase : forall M F L L' ess τs τs' κ,
          let F' := F <| fc_labels ::= cons (τs', L') |> in
          let ψ := InstrT [SumT κ τs] τs' in
          Forall2 (fun τ es => P2 M F' L es (InstrT [τ] τs') L') τs ess ->
          has_instruction_type_ok F ψ L' ->
          P1 M F L (ICase ψ L' ess) ψ L')
      (HCaseLoadCopy : forall M F L L' ess τs τs' κr κv κs μ,
          let F' := F <| fc_labels ::= cons (τs', L') |> in
          let τs_ser := zip_with SerT κs τs in
          let ψ :=
            InstrT [RefT κr μ Imm (VariantT κv τs_ser)] (RefT κr μ Imm (VariantT κv τs_ser) :: τs') in
          Forall (fun τ => has_ref_flag F τ GCRefs) τs ->
          Forall2 (fun τ es => P2 M F' L es (InstrT [τ] τs') L') τs ess ->
          has_instruction_type_ok F ψ L' ->
          P1 M F L (ICaseLoad ψ Copy L' ess) ψ L')
      (HCaseLoadMove : forall M F L L' ess τs τs' κr κv κs,
          let F' := F <| fc_labels ::= cons (τs', L') |> in
          let τs_ser := zip_with SerT κs τs in
          let ψ := InstrT [RefT κr (BaseM MemMM) Imm (VariantT κv τs_ser)] τs' in
          Forall2 (fun τ es => P2 M F' L es (InstrT [τ] τs') L') τs ess ->
          has_instruction_type_ok F ψ L' ->
          P1 M F L (ICaseLoad ψ Move L' ess) ψ L')
      (HGroup : forall M F L τs κ,
          let ψ := InstrT τs [ProdT κ τs] in
          has_instruction_type_ok F ψ L ->
          P1 M F L (IGroup ψ) ψ L)
      (HUngroup : forall M F L τs κ,
          let ψ := InstrT [ProdT κ τs] τs in
          has_instruction_type_ok F ψ L ->
          P1 M F L (IUngroup ψ) ψ L)
      (HFold : forall M F L τ κ,
          let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
          let ψ := InstrT [τ0] [RecT κ τ] in
          has_instruction_type_ok F ψ L ->
          P1 M F L (IFold ψ) ψ L)
      (HUnfold : forall M F L τ κ,
          let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
          let ψ := InstrT [RecT κ τ] [τ0] in
          has_instruction_type_ok F ψ L ->
          P1 M F L (IUnfold ψ) ψ L)
      (HPack : forall M F L τ τ',
          let ψ := InstrT [τ] [τ'] in
          packed_existential F τ τ' ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (IPack ψ) ψ L)
      (HUnpack : forall M F F0' L L' L0 L0' es τs1 τs2 ψ0,
          let F' := F <| fc_labels ::= cons (τs2, L') |> in
          let ψ := InstrT τs1 τs2 in
          unpacked_existential F' L ψ L' F0' L0 ψ0 L0' ->
          P2 M F0' L0 es ψ0 L0' ->
          has_instruction_type_ok F ψ L' ->
          P1 M F L (IUnpack ψ L' es) ψ L')
      (HTag : forall M F L,
          let ψ := InstrT [type_i32] [type_i31] in
          has_instruction_type_ok F ψ L ->
          P1 M F L (ITag ψ) ψ L)
      (HUntag : forall M F L,
          let ψ := InstrT [type_i31] [type_i32] in
          has_instruction_type_ok F ψ L ->
          P1 M F L (IUntag ψ) ψ L)
      (HCast : forall M F L τ τ',
          let ψ := InstrT [τ] [τ'] in
          type_eq τ τ' ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (ICast ψ) ψ L)
      (HNew : forall M F L μ β τ κ κser,
          let ψ := InstrT [τ] [RefT κ μ β (SerT κser τ)] in
          mono_mem μ ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (INew ψ) ψ L)
      (HLoadCopy : forall M F L π μ β τ τval pr κ κser,
          let ψ := InstrT [RefT κ μ β τ] [RefT κ μ β τ; τval] in
          has_ref_flag F τval GCRefs ->
          resolves_path τ π None pr ->
          pr.(pr_target) = SerT κser τval ->
          Forall (has_mono_size F) pr.(pr_prefix) ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (ILoad ψ π Copy) ψ L)
      (HLoadMove : forall M F L π τ τval κ κ' κser σ pr,
          let ψ :=
            InstrT [RefT κ (BaseM MemMM) Mut τ] [RefT κ' (BaseM MemMM) Mut pr.(pr_replaced); τval] in
          resolves_path τ π (Some (type_span σ)) pr ->
          has_size F pr.(pr_target) σ ->
          pr.(pr_target) = SerT κser τval ->
          Forall (has_mono_size F) pr.(pr_prefix) ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (ILoad ψ π Move) ψ L)
      (HStoreWeak : forall M F L π μ τ τval pr κ κser,
          let ψ := InstrT [RefT κ μ Mut τ; τval] [RefT κ μ Mut τ] in
          resolves_path τ π None pr ->
          has_ref_flag F pr.(pr_target) GCRefs ->
          pr.(pr_target) = SerT κser τval ->
          Forall (has_mono_size F) pr.(pr_prefix) ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (IStore ψ π) ψ L)
      (HStoreStrong : forall M F L π τ τval pr σ ρ κ κ' κser,
          let ψ :=
            InstrT [RefT κ (BaseM MemMM) Mut τ; τval] [RefT κ' (BaseM MemMM) Mut pr.(pr_replaced)] in
          resolves_path τ π (Some (SerT κser τval)) pr ->
          has_ref_flag F pr.(pr_target) GCRefs ->
          has_size F pr.(pr_target) σ ->
          has_rep F τval ρ ->
          eval_size EmptyEnv σ = eval_rep_size EmptyEnv ρ ->
          Forall (has_mono_size F) pr.(pr_prefix) ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (IStore ψ π) ψ L)
      (HSwap : forall M F L π τ τval pr κ κser μ,
          let ψ := InstrT [RefT κ μ Mut τ; τval] [RefT κ μ Mut τ; τval] in
          resolves_path τ π None pr ->
          Forall (has_mono_size F) pr.(pr_prefix) ->
          pr.(pr_target) = SerT κser τval ->
          has_instruction_type_ok F ψ L ->
          P1 M F L (ISwap ψ π) ψ L)
      (HNil : forall M F L,
          local_ctx_ok F L ->
          P2 M F L [] (InstrT [] []) L)
      (HApp : forall M F L1 L2 L3 es es' τs1 τs2 τs3,
          P2 M F L1 es (InstrT τs1 τs2) L2 ->
          P2 M F L2 es' (InstrT τs2 τs3) L3 ->
          P2 M F L1 (es ++ es') (InstrT τs1 τs3) L3)
      (HSingleton : forall M F L L' e ψ,
          P1 M F L e ψ L' ->
          P2 M F L [e] ψ L')
      (HFrame : forall M F L L' es τ τs1 τs2,
          has_mono_rep F τ ->
          P2 M F L es (InstrT τs1 τs2) L' ->
          P2 M F L es (InstrT (τ :: τs1) (τ :: τs2)) L').

  Fixpoint has_instruction_type_mind
    (M : module_ctx) (F : function_ctx) (L : local_ctx)
    (e : instruction)
    (ψ : instruction_type) (L' : local_ctx)
    (H : has_instruction_type M F L e ψ L') :
    P1 M F L e ψ L' :=
    match H with
    | TNop M F L H1 => HNop M F L H1
    | TUnreachable M F L L' ψ H1 => HUnreachable M F L L' ψ H1
    | TCopy M F L τ H1 H2 => HCopy M F L τ H1 H2
    | TDrop M F L τ H1 => HDrop M F L τ H1
    | TNum M F L e ψ H1 H2 => HNum M F L e ψ H1 H2
    | TNumConst M F L ν n H1 => HNumConst M F L ν n H1
    | TBlock M F L L' τs1 τs2 es H1 H2 =>
        HBlock M F L L' τs1 τs2 es (have_instruction_type_mind _ _ _ _ _ _ H1) H2
    | TLoop M F L τs1 τs2 es H1 H2 =>
        HLoop M F L τs1 τs2 es (have_instruction_type_mind _ _ _ _ _ _ H1) H2
    | TIte M F L L' τs1 τs2 es1 es2 H1 H2 H3 =>
        HIte M F L L' τs1 τs2 es1 es2
          (have_instruction_type_mind _ _ _ _ _ _ H1)
          (have_instruction_type_mind _ _ _ _ _ _ H2)
          H3
    | TBr M F L L' i τs τs1 τs2 H1 H2 H3 => HBr M F L L' i τs τs1 τs2 H1 H2 H3
    | TReturn M F L L' τs τs1 τs2 H1 H2 H3 => HReturn M F L L' τs τs1 τs2 H1 H2 H3
    | TLocalGetCopy M F L i τ H1 H2 H3 => HLocalGetCopy M F L i τ H1 H2 H3
    | TLocalGetMove M F L i τ ηs H1 H2 H3 => HLocalGetMove M F L i τ ηs H1 H2 H3
    | TLocalSet M F L i τ H1 H2 H3 H4 => HLocalSet M F L i τ H1 H2 H3 H4
    | TCodeRef M F L i ϕ H1 H2 => HCodeRef M F L i ϕ H1 H2
    | TInst M F L ix ϕ ϕ' H1 H2 => HInst M F L ix ϕ ϕ' H1 H2
    | TCall M F L i ixs ϕ τs1 τs2 H1 H2 H3 => HCall M F L i ixs ϕ τs1 τs2 H1 H2 H3
    | TCallIndirect M F L τs1 τs2 H1 => HCallIndirect M F L τs1 τs2 H1
    | TInject M F L i τ τs κ H1 H2 => HInject M F L i τ τs κ H1 H2
    | TInjectNew M F L i μ τ τs κr κv H1 H2 H3 H4 => HInjectNew M F L i μ τ τs κr κv H1 H2 H3 H4
    | TCase M F L L' ess τs τs' κ H1 H2 =>
        HCase M F L L' ess τs τs' κ
          (Forall2_impl _ _ _ _ H1 (fun τ es => have_instruction_type_mind _ _ _ _ _ _))
          H2
    | TCaseLoadCopy M F L L' ess τs τs' κr κv κs μ H1 H2 H3 =>
        HCaseLoadCopy M F L L' ess τs τs' κr κv κs μ
          H1
          (Forall2_impl _ _ _ _ H2 (fun τ es => have_instruction_type_mind _ _ _ _ _ _))
          H3
    | TCaseLoadMove M F L L' ess τs τs' κr κv κs H1 H2 =>
        HCaseLoadMove M F L L' ess τs τs' κr κv κs
          (Forall2_impl _ _ _ _ H1 (fun τ es => have_instruction_type_mind _ _ _ _ _ _))
          H2
    | TGroup M F L τs κ H1 => HGroup M F L τs κ H1
    | TUngroup M F L τs κ H1 => HUngroup M F L τs κ H1
    | TFold M F L τs κ H1 => HFold M F L τs κ H1
    | TUnfold M F L τ κ H1 => HUnfold M F L τ κ H1
    | TPack M F L τ τ' H1 H2 => HPack M F L τ τ' H1 H2
    | TUnpack M F F0' L L' L0 L0' es τs1 τs2 ψ0 H1 H2 H3 =>
        HUnpack M F F0' L L' L0 L0' es τs1 τs2 ψ0 H1
          (have_instruction_type_mind _ _ _ _ _ _ H2)
          H3
    | TTag M F L H1 => HTag M F L H1
    | TUntag M F L H1 => HUntag M F L H1
    | TCast M F L τ τ' H1 H2 => HCast M F L τ τ' H1 H2
    | TNew M F L μ β τ κ κser H1 H2 => HNew M F L μ β τ κ κser H1 H2
    | TLoadCopy M F L π μ β τ τval pr κ κser H1 H2 H3 H4 H5 =>
        HLoadCopy M F L π μ β τ τval pr κ κser H1 H2 H3 H4 H5
    | TLoadMove M F L π τ τval κ κ' κser σ pr H1 H2 H3 H4 H5 =>
        HLoadMove M F L π τ τval κ κ' κser σ pr H1 H2 H3 H4 H5
    | TStoreWeak M F L π μ τ τval pr κ κser H1 H2 H3 H4 H5 =>
        HStoreWeak M F L π μ τ τval pr κ κser H1 H2 H3 H4 H5
    | TStoreStrong M F L π τ τval pr σ ρ κ κ' κser H1 H2 H3 H4 H5 H6 H7 =>
        HStoreStrong M F L π τ τval pr σ ρ κ κ' κser H1 H2 H3 H4 H5 H6 H7
    | TSwap M F L π τ τval pr κ κser μ H1 H2 H3 H4 => HSwap M F L π τ τval pr κ κser μ H1 H2 H3 H4
    end

  with have_instruction_type_mind
    (M : module_ctx) (F : function_ctx) (L : local_ctx)
    (es : list instruction)
    (ψ : instruction_type) (L' : local_ctx)
    (H : have_instruction_type M F L es ψ L') :
    P2 M F L es ψ L' :=
    match H with
    | TNil M F L H1 => HNil M F L H1
    | TApp M F L1 L2 L3 es es' τs1 τs2 τs3 H1 H2 =>
        HApp M F L1 L2 L3 es es' τs1 τs2 τs3
          (have_instruction_type_mind _ _ _ _ _ _ H1)
          (have_instruction_type_mind _ _ _ _ _ _ H2)
    | TSingleton M F L L' e ψ H =>
        HSingleton M F L L' e ψ (has_instruction_type_mind _ _ _ _ _ _ H)
    | TFrame M F L L' es τ τs1 τs2 H1 H2 =>
       HFrame M F L L' es τ τs1 τs2 H1 (have_instruction_type_mind _ _ _ _ _ _ H2)
    end.

End HasHaveInstructionTypeMind.

Lemma have_instruction_type_inv M F L e ψ L' :
  have_instruction_type M F L e ψ L' -> has_instruction_type_ok F ψ L'.
Proof.
  intros H.
  induction H using have_instruction_type_mind with
    (P1 := fun _ F _ _ ψ L' => has_instruction_type_ok F ψ L');
    try assumption; repeat constructor; try assumption.
  - inversion IHhave_instruction_type. by inversion H.
  - inversion IHhave_instruction_type0. by inversion H.
  - by inversion IHhave_instruction_type0.
  - inversion IHhave_instruction_type. by inversion H0.
  - inversion IHhave_instruction_type. by inversion H0.
  - by inversion IHhave_instruction_type.
Qed.

Inductive has_function_type : module_ctx -> module_function -> function_type -> Prop :=
| TFunction M mf ηss_L ηss_P ρs_P L' :
  let ϕ := flatten_function_type mf.(mf_type) in
  let K := kc_of_fft ϕ in
  let F := {| fc_return := ϕ.(fft_out);
              fc_locals := ηss_P ++ ηss_L;
              fc_labels := [(ϕ.(fft_out), L')];
              fc_kind_ctx := K;
              fc_type_vars := ϕ.(fft_type_vars) |} in
  let L := ϕ.(fft_in) ++ map type_plug_prim ηss_L in
  let ψ := InstrT [] ϕ.(fft_out) in
  mapM (eval_rep_prim EmptyEnv) mf.(mf_locals) = Some ηss_L ->
  Forall2 (has_rep F) ϕ.(fft_in) ρs_P ->
  mapM (eval_rep_prim EmptyEnv) ρs_P = Some ηss_P ->
  Forall (fun τ => has_ref_flag F τ NoRefs) L' ->
  have_instruction_type M F L mf.(mf_body) ψ L' ->
  has_function_type M mf mf.(mf_type).

Inductive has_module_type : module -> module_type -> Prop :=
| TModule m table exports :
  let ϕs := m.(m_imports) ++ map mf_type m.(m_functions) in
  nths_error ϕs m.(m_table) = Some table ->
  nths_error ϕs (map me_desc m.(m_exports)) = Some exports ->
  let M := Build_module_ctx ϕs table in
  Forall (fun mf => has_function_type M mf mf.(mf_type)) m.(m_functions) ->
  has_module_type m (Build_module_type m.(m_imports) exports).
