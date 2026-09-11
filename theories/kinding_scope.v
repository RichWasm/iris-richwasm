From mathcomp Require Import ssreflect.
From stdpp Require Import base list.
From RichWasm Require Import syntax typing util.
Require Import RecordUpdate.RecordUpdate.
Require Import RichWasm.kinding_subst.

Set Bullet Behavior "Strict Subproofs".

(* Which variables a substitution is allowed to move, for a type that is well formed either
   before or after it. [subst_agree] takes the well-formedness of the substituted type, so it
   sees that everything the substitution put at a variable is in scope; [subst_id] takes it of
   the source type, so it only sees that the source's own variables are in scope. *)

Definition mem_sub_agree (K : kind_ctx) (σ σ' : nat -> memory) : Prop :=
  forall n, mem_ok K (σ n) -> σ n = σ' n.

Definition rep_sub_agree (K : kind_ctx) (σ σ' : nat -> representation) : Prop :=
  forall n, rep_ok K (σ n) -> σ n = σ' n.

Definition size_sub_agree (K : kind_ctx) (σ σ' : nat -> size) : Prop :=
  forall n, size_ok K (σ n) -> σ n = σ' n.

Lemma mem_ok_kc K K' μ : kc_mem_vars K = kc_mem_vars K' -> mem_ok K μ -> mem_ok K' μ.
Proof. intros H; apply mem_ok_mono; lia. Qed.

Lemma rep_ok_kc K K' ρ : kc_rep_vars K = kc_rep_vars K' -> rep_ok K ρ -> rep_ok K' ρ.
Proof. intros H; apply rep_ok_mono; lia. Qed.

Lemma size_ok_kc K K' σ :
  kc_rep_vars K = kc_rep_vars K' -> kc_size_vars K = kc_size_vars K' ->
  size_ok K σ -> size_ok K' σ.
Proof. intros Hr Hs; apply size_ok_mono; lia. Qed.

Lemma map_agree_of_Forall {A B} (f g : A -> B) (Q : B -> Prop) l :
  Forall (fun x => Q (f x) -> f x = g x) l -> Forall Q (map f l) -> map f l = map g l.
Proof.
  induction 1 as [|x l Hx Hl IH]; [done|].
  cbn; inversion 1; subst; f_equal; auto.
Qed.

(* Agreement transports along pointwise-equal substitutions. *)
Lemma mem_sub_agree_pw K σ1 σ1' σ2 σ2' :
  (forall n, σ2 n = σ1 n) -> (forall n, σ2' n = σ1' n) ->
  mem_sub_agree K σ1 σ1' -> mem_sub_agree K σ2 σ2'.
Proof. intros H2 H2' Hag n Hok; rewrite H2 H2'; apply Hag; by rewrite -H2. Qed.

Lemma rep_sub_agree_pw K σ1 σ1' σ2 σ2' :
  (forall n, σ2 n = σ1 n) -> (forall n, σ2' n = σ1' n) ->
  rep_sub_agree K σ1 σ1' -> rep_sub_agree K σ2 σ2'.
Proof. intros H2 H2' Hag n Hok; rewrite H2 H2'; apply Hag; by rewrite -H2. Qed.

Lemma size_sub_agree_pw K σ1 σ1' σ2 σ2' :
  (forall n, σ2 n = σ1 n) -> (forall n, σ2' n = σ1' n) ->
  size_sub_agree K σ1 σ1' -> size_sub_agree K σ2 σ2'.
Proof. intros H2 H2' Hag n Hok; rewrite H2 H2'; apply Hag; by rewrite -H2. Qed.

Lemma up_representation_memory_id σ n : up_representation_memory σ n = σ n.
Proof. unfold up_representation_memory, core.funcomp; apply rinstId'_memory. Qed.

Lemma up_size_memory_id σ n : up_size_memory σ n = σ n.
Proof. unfold up_size_memory, core.funcomp; apply rinstId'_memory. Qed.

Lemma up_type_memory_id σ n : up_type_memory σ n = σ n.
Proof. unfold up_type_memory, core.funcomp; apply rinstId'_memory. Qed.

Lemma up_memory_representation_id σ n : up_memory_representation σ n = σ n.
Proof. unfold up_memory_representation, core.funcomp; apply rinstId'_representation. Qed.

Lemma up_size_representation_id σ n : up_size_representation σ n = σ n.
Proof. unfold up_size_representation, core.funcomp; apply rinstId'_representation. Qed.

Lemma up_type_representation_id σ n : up_type_representation σ n = σ n.
Proof. unfold up_type_representation, core.funcomp; apply rinstId'_representation. Qed.

Lemma up_memory_size_id σ n : up_memory_size σ n = σ n.
Proof. unfold up_memory_size, core.funcomp; apply rinstId'_size. Qed.

Lemma up_type_size_id σ n : up_type_size σ n = σ n.
Proof. unfold up_type_size, core.funcomp; apply rinstId'_size. Qed.

(* mem_sub_agree under each of the four binders. *)
Lemma mem_sub_agree_up_mem K σ σ' :
  mem_sub_agree K σ σ' ->
  mem_sub_agree (set kc_mem_vars S K) (up_memory_memory σ) (up_memory_memory σ').
Proof.
  intros Hag [|n]; unfold up_memory_memory, unscoped.scons, core.funcomp; cbn; [done|].
  intros Hok.
  f_equal; apply Hag.
  by eapply (proj2 (mem_ok_ren _ _ _ _ _ _ (kc_ren_wk_mem K))).
Qed.

Lemma mem_sub_agree_up_rep K σ σ' :
  mem_sub_agree K σ σ' ->
  mem_sub_agree (set kc_rep_vars S K) (up_representation_memory σ) (up_representation_memory σ').
Proof.
  intros Hag n Hok.
  rewrite !up_representation_memory_id; rewrite up_representation_memory_id in Hok.
  apply Hag; eapply mem_ok_kc; [|exact Hok]; by destruct K.
Qed.

Lemma mem_sub_agree_up_size K σ σ' :
  mem_sub_agree K σ σ' ->
  mem_sub_agree (set kc_size_vars S K) (up_size_memory σ) (up_size_memory σ').
Proof.
  intros Hag n Hok.
  rewrite !up_size_memory_id; rewrite up_size_memory_id in Hok.
  apply Hag; eapply mem_ok_kc; [|exact Hok]; by destruct K.
Qed.

Lemma mem_sub_agree_up_type K σ σ' :
  mem_sub_agree K σ σ' -> mem_sub_agree K (up_type_memory σ) (up_type_memory σ').
Proof. apply mem_sub_agree_pw; intros n; apply up_type_memory_id. Qed.

(* rep_sub_agree under each of the four binders. *)
Lemma rep_sub_agree_up_rep K σ σ' :
  rep_sub_agree K σ σ' ->
  rep_sub_agree (set kc_rep_vars S K) (up_representation_representation σ)
    (up_representation_representation σ').
Proof.
  intros Hag [|n]; unfold up_representation_representation, unscoped.scons, core.funcomp;
    cbn; [done|].
  intros Hok.
  f_equal; apply Hag.
  by eapply (proj2 (rep_ok_ren _ _ _ _ (proj1 (proj2 (kc_ren_wk_rep K))))).
Qed.

Lemma rep_sub_agree_up_mem K σ σ' :
  rep_sub_agree K σ σ' ->
  rep_sub_agree (set kc_mem_vars S K) (up_memory_representation σ) (up_memory_representation σ').
Proof.
  intros Hag n Hok.
  rewrite !up_memory_representation_id; rewrite up_memory_representation_id in Hok.
  apply Hag; eapply rep_ok_kc; [|exact Hok]; by destruct K.
Qed.

Lemma rep_sub_agree_up_size K σ σ' :
  rep_sub_agree K σ σ' ->
  rep_sub_agree (set kc_size_vars S K) (up_size_representation σ) (up_size_representation σ').
Proof.
  intros Hag n Hok.
  rewrite !up_size_representation_id; rewrite up_size_representation_id in Hok.
  apply Hag; eapply rep_ok_kc; [|exact Hok]; by destruct K.
Qed.

Lemma rep_sub_agree_up_type K σ σ' :
  rep_sub_agree K σ σ' -> rep_sub_agree K (up_type_representation σ) (up_type_representation σ').
Proof. apply rep_sub_agree_pw; intros n; apply up_type_representation_id. Qed.

(* size_sub_agree under each of the four binders. *)
Lemma size_sub_agree_up_size K σ σ' :
  size_sub_agree K σ σ' ->
  size_sub_agree (set kc_size_vars S K) (up_size_size σ) (up_size_size σ').
Proof.
  intros Hag [|n]; unfold up_size_size, unscoped.scons, core.funcomp; cbn; [done|].
  intros Hok.
  f_equal; apply Hag.
  destruct (kc_ren_wk_size K) as (_ & Hr & Hs).
  by eapply (proj2 (size_ok_ren _ _ _ _ _ Hr Hs)).
Qed.

Lemma size_sub_agree_up_rep K σ σ' :
  size_sub_agree K σ σ' ->
  size_sub_agree (set kc_rep_vars S K) (up_representation_size σ) (up_representation_size σ').
Proof.
  intros Hag n Hok.
  unfold up_representation_size, core.funcomp in Hok |- *.
  f_equal; apply Hag.
  destruct (kc_ren_wk_rep K) as (_ & Hr & Hs).
  by eapply (proj2 (size_ok_ren _ _ _ _ _ Hr Hs)).
Qed.

Lemma size_sub_agree_up_mem K σ σ' :
  size_sub_agree K σ σ' ->
  size_sub_agree (set kc_mem_vars S K) (up_memory_size σ) (up_memory_size σ').
Proof.
  intros Hag n Hok.
  rewrite !up_memory_size_id; rewrite up_memory_size_id in Hok.
  apply Hag; eapply size_ok_kc; [| |exact Hok]; by destruct K.
Qed.

Lemma size_sub_agree_up_type K σ σ' :
  size_sub_agree K σ σ' -> size_sub_agree K (up_type_size σ) (up_type_size σ').
Proof. apply size_sub_agree_pw; intros n; apply up_type_size_id. Qed.

(* Agreement lifts from substitutions to the things they act on. *)
Lemma subst_memory_agree K σ σ' μ :
  mem_sub_agree K σ σ' -> mem_ok K (subst_memory σ μ) ->
  subst_memory σ μ = subst_memory σ' μ.
Proof. intros Hag; destruct μ as [n|c]; cbn; [by apply Hag|done]. Qed.

Lemma subst_representation_agree K σ σ' ρ :
  rep_sub_agree K σ σ' -> rep_ok K (subst_representation σ ρ) ->
  subst_representation σ ρ = subst_representation σ' ρ.
Proof.
  intros Hag; induction ρ using rep_ind; cbn.
  - by apply Hag.
  - intros Hok; inversion Hok; subst; f_equal; by eapply map_agree_of_Forall.
  - intros Hok; inversion Hok; subst; f_equal; by eapply map_agree_of_Forall.
  - done.
Qed.

Lemma subst_size_agree K σr σr' σs σs' σ :
  rep_sub_agree K σr σr' -> size_sub_agree K σs σs' -> size_ok K (subst_size σr σs σ) ->
  subst_size σr σs σ = subst_size σr' σs' σ.
Proof.
  intros Har Has; induction σ using size_ind; cbn.
  - by apply Has.
  - intros Hok; inversion Hok; subst; f_equal; by eapply map_agree_of_Forall.
  - intros Hok; inversion Hok; subst; f_equal; by eapply map_agree_of_Forall.
  - intros Hok; inversion Hok; subst; f_equal; by eapply subst_representation_agree.
  - done.
Qed.

Lemma subst_kind_agree K σr σr' σs σs' κ :
  rep_sub_agree K σr σr' -> size_sub_agree K σs σs' -> kind_ok K (subst_kind σr σs κ) ->
  subst_kind σr σs κ = subst_kind σr' σs' κ.
Proof.
  intros Har Has; destruct κ as [ρ ξ|σ ξ]; cbn; inversion 1; subst; f_equal.
  - by eapply subst_representation_agree.
  - by eapply subst_size_agree.
Qed.

Definition subst_agree_ok (τ : type) : Prop :=
  forall F σm σm' σr σr' σs σs' σt,
    type_ok F (subst_type σm σr σs σt τ) ->
    mem_sub_agree (fc_kind_ctx F) σm σm' ->
    rep_sub_agree (fc_kind_ctx F) σr σr' ->
    size_sub_agree (fc_kind_ctx F) σs σs' ->
    subst_type σm σr σs σt τ = subst_type σm' σr' σs' σt τ.

Definition subst_agree_ok_ft (ϕ : function_type) : Prop :=
  forall F σm σm' σr σr' σs σs' σt,
    function_type_ok F (subst_function_type σm σr σs σt ϕ) ->
    mem_sub_agree (fc_kind_ctx F) σm σm' ->
    rep_sub_agree (fc_kind_ctx F) σr σr' ->
    size_sub_agree (fc_kind_ctx F) σs σs' ->
    subst_function_type σm σr σs σt ϕ = subst_function_type σm' σr' σs' σt ϕ.

Definition subst_agree_ok_ift (ϕ : inner_function_type) : Prop :=
  forall F σm σm' σr σr' σs σs' σt,
    inner_function_type_ok F (subst_inner_function_type σm σr σs σt ϕ) ->
    mem_sub_agree (fc_kind_ctx F) σm σm' ->
    rep_sub_agree (fc_kind_ctx F) σr σr' ->
    size_sub_agree (fc_kind_ctx F) σs σs' ->
    subst_inner_function_type σm σr σs σt ϕ = subst_inner_function_type σm' σr' σs' σt ϕ.

Lemma map_subst_agree F σm σm' σr σr' σs σs' σt τs :
  Forall subst_agree_ok τs ->
  Forall (type_ok F) (map (subst_type σm σr σs σt) τs) ->
  mem_sub_agree (fc_kind_ctx F) σm σm' ->
  rep_sub_agree (fc_kind_ctx F) σr σr' ->
  size_sub_agree (fc_kind_ctx F) σs σs' ->
  map (subst_type σm σr σs σt) τs = map (subst_type σm' σr' σs' σt) τs.
Proof.
  intros Hag Hoks Ham Har Has.
  induction Hag as [|τ τs Hτ Hτs IH]; [done|].
  cbn in Hoks |- *; inversion Hoks; subst.
  f_equal; [by apply (Hτ F σm σm' σr σr' σs σs' σt)|by apply IH].
Qed.

Lemma subst_agree :
  (forall τ, subst_agree_ok τ) /\
  (forall ϕ, subst_agree_ok_ft ϕ) /\
  (forall ϕ, subst_agree_ok_ift ϕ).
Proof.
  apply type_and_function_ind.
  - done.
  - intros κ F *; cbn; intros Hok Ham Har Has.
    inversion Hok; subst.
    rewrite (subst_kind_agree _ _ _ _ _ _ Har Has); last done.
    done.
  - intros κ nt F *; cbn; intros Hok Ham Har Has.
    inversion Hok; subst.
    rewrite (subst_kind_agree _ _ _ _ _ _ Har Has); last done.
    done.
  - intros κ τs IH F *; cbn; intros Hok Ham Har Has.
    inversion Hok; subst.
    rewrite (subst_kind_agree _ _ _ _ _ _ Har Has); last done.
    f_equal; by eapply map_subst_agree.
  - intros κ τs IH F *; cbn; intros Hok Ham Har Has.
    inversion Hok; subst.
    rewrite (subst_kind_agree _ _ _ _ _ _ Har Has); last done.
    f_equal; by eapply map_subst_agree.
  - intros κ τs IH F *; cbn; intros Hok Ham Har Has.
    inversion Hok; subst.
    rewrite (subst_kind_agree _ _ _ _ _ _ Har Has); last done.
    f_equal; by eapply map_subst_agree.
  - intros κ τs IH F *; cbn; intros Hok Ham Har Has.
    inversion Hok; subst.
    rewrite (subst_kind_agree _ _ _ _ _ _ Har Has); last done.
    f_equal; by eapply map_subst_agree.
  - intros κ μ β τ IH F *; cbn; intros Hok Ham Har Has.
    inversion Hok; subst.
    rewrite (subst_kind_agree _ _ _ _ _ _ Har Has); last done.
    rewrite (subst_memory_agree _ _ _ _ Ham); last done.
    f_equal; by eapply (IH _ _ _ _ _ _ _ _).
  - intros κ ϕ IH F *; cbn; intros Hok Ham Har Has.
    inversion Hok; subst.
    rewrite (subst_kind_agree _ _ _ _ _ _ Har Has); last done.
    f_equal; by eapply (IH _ _ _ _ _ _ _ _).
  - intros κ τ IH F *; cbn; intros Hok Ham Har Has.
    inversion Hok; subst.
    rewrite (subst_kind_agree _ _ _ _ _ _ Har Has); last done.
    f_equal; by eapply (IH _ _ _ _ _ _ _ _).
  - intros κ ρ F *; cbn; intros Hok Ham Har Has.
    inversion Hok; subst.
    rewrite (subst_kind_agree _ _ _ _ _ _ Har Has); last done.
    f_equal; by eapply subst_representation_agree.
  - intros κ σ F *; cbn; intros Hok Ham Har Has.
    inversion Hok; subst.
    rewrite (subst_kind_agree _ _ _ _ _ _ Har Has); last done.
    f_equal; by eapply subst_size_agree.
  - intros κ τ IH F *; cbn; intros Hok Ham Har Has.
    inversion Hok as [| | | | | | | | | | | |? ? ? Hκ Hτ| | | |]; subst.
    rewrite (subst_kind_agree _ _ _ _ _ _ Har Has); last done.
    f_equal.
    eapply (IH _ _ _ _ _ _ _ _); [exact Hτ| | |]; rewrite fc_kind_ctx_ty_update.
    + by apply mem_sub_agree_up_type.
    + by apply rep_sub_agree_up_type.
    + by apply size_sub_agree_up_type.
  - intros κ τ IH F *; cbn; intros Hok Ham Har Has.
    inversion Hok as [| | | | | | | | | | | | |? ? ? Hκ Hτ| | |]; subst.
    rewrite (subst_kind_agree _ _ _ _ _ _ Har Has); last done.
    f_equal.
    eapply (IH _ _ _ _ _ _ _ _); [exact Hτ| | |]; destruct F; cbn in *.
    + by apply mem_sub_agree_up_mem.
    + by apply rep_sub_agree_up_mem.
    + by apply size_sub_agree_up_mem.
  - intros κ τ IH F *; cbn; intros Hok Ham Har Has.
    inversion Hok as [| | | | | | | | | | | | | |? ? ? Hκ Hτ| |]; subst.
    rewrite (subst_kind_agree _ _ _ _ _ _ Har Has); last done.
    f_equal.
    eapply (IH _ _ _ _ _ _ _ _); [exact Hτ| | |]; destruct F; cbn in *.
    + by apply mem_sub_agree_up_rep.
    + by apply rep_sub_agree_up_rep.
    + by apply size_sub_agree_up_rep.
  - intros κ τ IH F *; cbn; intros Hok Ham Har Has.
    inversion Hok as [| | | | | | | | | | | | | | |? ? ? Hκ Hτ|]; subst.
    rewrite (subst_kind_agree _ _ _ _ _ _ Har Has); last done.
    f_equal.
    eapply (IH _ _ _ _ _ _ _ _); [exact Hτ| | |]; destruct F; cbn in *.
    + by apply mem_sub_agree_up_size.
    + by apply rep_sub_agree_up_size.
    + by apply size_sub_agree_up_size.
  - intros κ κ0 τ IH F *; cbn; intros Hok Ham Har Has.
    inversion Hok as [| | | | | | | | | | | | | | | |? ? ? ? Hκ Hκ0 Hτ]; subst.
    rewrite (subst_kind_agree _ _ _ _ _ _ Har Has Hκ).
    rewrite (subst_kind_agree _ _ _ _ _ _ Har Has Hκ0).
    f_equal.
    eapply (IH _ _ _ _ _ _ _ _); [exact Hτ| | |]; rewrite fc_kind_ctx_ty_update.
    + by apply mem_sub_agree_up_type.
    + by apply rep_sub_agree_up_type.
    + by apply size_sub_agree_up_type.
  - intros τs1 τs2 IH1 IH2 F *; cbn; intros Hok Ham Har Has.
    inversion Hok; subst.
    f_equal; by eapply map_subst_agree.
  - intros κ ϕ IH F *; cbn; intros Hok Ham Har Has.
    inversion Hok as [|? ? ? Hκ Hϕ]; subst.
    rewrite (subst_kind_agree _ _ _ _ _ _ Har Has Hκ).
    f_equal.
    eapply (IH _ _ _ _ _ _ _ _); [exact Hϕ| | |]; rewrite fc_kind_ctx_ty_update.
    + by apply mem_sub_agree_up_type.
    + by apply rep_sub_agree_up_type.
    + by apply size_sub_agree_up_type.
  - intros ϕ IH F *; cbn; intros Hok Ham Har Has.
    inversion Hok; subst.
    f_equal; by eapply (IH _ _ _ _ _ _ _ _).
  - intros ϕ IH F *; cbn; intros Hok Ham Har Has.
    inversion Hok as [| | |? ? Hϕ]; subst.
    f_equal.
    eapply (IH _ _ _ _ _ _ _ _); [exact Hϕ| | |]; destruct F; cbn in *.
    + by apply mem_sub_agree_up_mem.
    + by apply rep_sub_agree_up_mem.
    + by apply size_sub_agree_up_mem.
  - intros ϕ IH F *; cbn; intros Hok Ham Har Has.
    inversion Hok as [|? ? Hϕ| |]; subst.
    f_equal.
    eapply (IH _ _ _ _ _ _ _ _); [exact Hϕ| | |]; destruct F; cbn in *.
    + by apply mem_sub_agree_up_rep.
    + by apply rep_sub_agree_up_rep.
    + by apply size_sub_agree_up_rep.
  - intros ϕ IH F *; cbn; intros Hok Ham Har Has.
    inversion Hok as [| |? ? Hϕ|]; subst.
    f_equal.
    eapply (IH _ _ _ _ _ _ _ _); [exact Hϕ| | |]; destruct F; cbn in *.
    + by apply mem_sub_agree_up_size.
    + by apply rep_sub_agree_up_size.
    + by apply size_sub_agree_up_size.
Qed.

(* --- deciding the ok predicates --- *)

Lemma forallb_Forall_iff {A} (f : A -> bool) (Q : A -> Prop) l :
  Forall (fun x => f x = true <-> Q x) l -> (forallb f l = true <-> Forall Q l).
Proof.
  induction 1 as [|x l Hx Hl IH]; cbn.
  - split; [by constructor|done].
  - by rewrite andb_true_iff Hx IH Forall_cons.
Qed.

Fixpoint rep_okb (K : kind_ctx) (ρ : representation) : bool :=
  match ρ with
  | VarR n => bool_decide (n < kc_rep_vars K)
  | SumR ρs => forallb (rep_okb K) ρs
  | ProdR ρs => forallb (rep_okb K) ρs
  | AtomR _ => true
  end.

Lemma rep_okb_iff K ρ : rep_okb K ρ = true <-> rep_ok K ρ.
Proof.
  induction ρ using rep_ind; cbn.
  - rewrite bool_decide_eq_true; split; [by constructor|by inversion 1].
  - rewrite (forallb_Forall_iff _ (rep_ok K) _ H); split; [by constructor|by inversion 1].
  - rewrite (forallb_Forall_iff _ (rep_ok K) _ H); split; [by constructor|by inversion 1].
  - split; [by constructor|done].
Qed.

Fixpoint size_okb (K : kind_ctx) (σ : size) : bool :=
  match σ with
  | VarS n => bool_decide (n < kc_size_vars K)
  | SumS σs => forallb (size_okb K) σs
  | ProdS σs => forallb (size_okb K) σs
  | RepS ρ => rep_okb K ρ
  | ConstS _ => true
  end.

Lemma size_okb_iff K σ : size_okb K σ = true <-> size_ok K σ.
Proof.
  induction σ using size_ind; cbn.
  - rewrite bool_decide_eq_true; split; [by constructor|by inversion 1].
  - rewrite (forallb_Forall_iff _ (size_ok K) _ H); split; [by constructor|by inversion 1].
  - rewrite (forallb_Forall_iff _ (size_ok K) _ H); split; [by constructor|by inversion 1].
  - rewrite rep_okb_iff; split; [by constructor|by inversion 1].
  - split; [by constructor|done].
Qed.

(* --- substitution is the identity on closed types --- *)

Definition sub_scope_type (F : function_ctx) (σ : nat -> type) : Prop :=
  forall n, n < length (fc_type_vars F) -> σ n = VarT n.

Lemma sub_id_up_memory_representation σ :
  sub_id_representation σ -> sub_id_representation (up_memory_representation σ).
Proof. intros H n; rewrite up_memory_representation_id; apply H. Qed.

Lemma sub_id_up_size_representation σ :
  sub_id_representation σ -> sub_id_representation (up_size_representation σ).
Proof. intros H n; rewrite up_size_representation_id; apply H. Qed.

Lemma sub_id_up_type_representation σ :
  sub_id_representation σ -> sub_id_representation (up_type_representation σ).
Proof. intros H n; rewrite up_type_representation_id; apply H. Qed.

Lemma sub_id_up_representation_representation σ :
  sub_id_representation σ -> sub_id_representation (up_representation_representation σ).
Proof.
  intros H [|n]; unfold up_representation_representation, unscoped.scons, core.funcomp;
    cbn; [done|].
  by rewrite H.
Qed.

Lemma sub_id_up_memory_size σ : sub_id_size σ -> sub_id_size (up_memory_size σ).
Proof. intros H n; rewrite up_memory_size_id; apply H. Qed.

Lemma sub_id_up_type_size σ : sub_id_size σ -> sub_id_size (up_type_size σ).
Proof. intros H n; rewrite up_type_size_id; apply H. Qed.

Lemma sub_id_up_representation_size σ : sub_id_size σ -> sub_id_size (up_representation_size σ).
Proof.
  intros H n; unfold up_representation_size, core.funcomp; by rewrite H.
Qed.

Lemma sub_id_up_size_size σ : sub_id_size σ -> sub_id_size (up_size_size σ).
Proof.
  intros H [|n]; unfold up_size_size, unscoped.scons, core.funcomp; cbn; [done|].
  by rewrite H.
Qed.

Lemma sub_scope_type_up_type F σ κ :
  sub_scope_type F σ -> sub_scope_type (add_type_var F κ) (up_type_type σ).
Proof.
  intros H [|n]; unfold up_type_type, unscoped.scons, core.funcomp; cbn; [done|].
  destruct F; cbn; intros Hn.
  assert (Hσ : σ n = VarT n) by (apply (H n); cbn; lia).
  by rewrite Hσ.
Qed.

Lemma sub_scope_type_up_mem F σ :
  sub_scope_type F σ ->
  sub_scope_type (add_mem_var F) (up_memory_type σ).
Proof.
  intros H n; unfold up_memory_type, core.funcomp.
  destruct F; cbn; intros Hn.
  assert (Hσ : σ n = VarT n) by (apply (H n); cbn; lia).
  by rewrite Hσ.
Qed.

Lemma sub_scope_type_up_rep F σ :
  sub_scope_type F σ -> sub_scope_type (add_rep_var F) (up_representation_type σ).
Proof.
  intros H n; unfold up_representation_type, add_rep_var, core.funcomp.
  destruct F; cbn; rewrite length_map; intros Hn.
  assert (Hσ : σ n = VarT n) by (apply (H n); cbn; lia).
  by rewrite Hσ.
Qed.

Lemma sub_scope_type_up_size F σ :
  sub_scope_type F σ -> sub_scope_type (add_size_var F) (up_size_type σ).
Proof.
  intros H n; unfold up_size_type, add_size_var, core.funcomp.
  destruct F; cbn; rewrite length_map; intros Hn.
  assert (Hσ : σ n = VarT n) by (apply (H n); cbn; lia).
  by rewrite Hσ.
Qed.

Definition subst_id_ok (τ : type) : Prop :=
  forall F σm σr σs σt,
    type_ok F τ ->
    sub_id_memory σm -> sub_id_representation σr -> sub_id_size σs -> sub_scope_type F σt ->
    subst_type σm σr σs σt τ = τ.

Definition subst_id_ok_ft (ϕ : function_type) : Prop :=
  forall F σm σr σs σt,
    function_type_ok F ϕ ->
    sub_id_memory σm -> sub_id_representation σr -> sub_id_size σs -> sub_scope_type F σt ->
    subst_function_type σm σr σs σt ϕ = ϕ.

Definition subst_id_ok_ift (ϕ : inner_function_type) : Prop :=
  forall F σm σr σs σt,
    inner_function_type_ok F ϕ ->
    sub_id_memory σm -> sub_id_representation σr -> sub_id_size σs -> sub_scope_type F σt ->
    subst_inner_function_type σm σr σs σt ϕ = ϕ.

Lemma map_subst_id F σm σr σs σt τs :
  Forall subst_id_ok τs ->
  Forall (type_ok F) τs ->
  sub_id_memory σm -> sub_id_representation σr -> sub_id_size σs -> sub_scope_type F σt ->
  map (subst_type σm σr σs σt) τs = τs.
Proof.
  intros Hids Hoks Hm Hr Hs Ht.
  induction Hids as [|τ τs Hτ Hτs IH]; [done|].
  inversion Hoks; subst.
  cbn; f_equal; [by apply (Hτ F σm σr σs σt)|by apply IH].
Qed.

Lemma subst_id :
  (forall τ, subst_id_ok τ) /\
  (forall ϕ, subst_id_ok_ft ϕ) /\
  (forall ϕ, subst_id_ok_ift ϕ).
Proof.
  apply type_and_function_ind.
  - intros t F *; intros Hok Hm Hr Hs Ht.
    inversion Hok; subst; cbn.
    by apply Ht, lookup_lt_Some with (x := κ).
  - intros κ F *; intros Hok Hm Hr Hs Ht; cbn.
    by rewrite subst_kind_id.
  - intros κ nt F *; intros Hok Hm Hr Hs Ht; cbn.
    by rewrite subst_kind_id.
  - intros κ τs IH F *; intros Hok Hm Hr Hs Ht; cbn.
    inversion Hok; subst.
    rewrite (subst_kind_id _ _ _ Hr Hs).
    f_equal; by eapply map_subst_id.
  - intros κ τs IH F *; intros Hok Hm Hr Hs Ht; cbn.
    inversion Hok; subst.
    rewrite (subst_kind_id _ _ _ Hr Hs).
    f_equal; by eapply map_subst_id.
  - intros κ τs IH F *; intros Hok Hm Hr Hs Ht; cbn.
    inversion Hok; subst.
    rewrite (subst_kind_id _ _ _ Hr Hs).
    f_equal; by eapply map_subst_id.
  - intros κ τs IH F *; intros Hok Hm Hr Hs Ht; cbn.
    inversion Hok; subst.
    rewrite (subst_kind_id _ _ _ Hr Hs).
    f_equal; by eapply map_subst_id.
  - intros κ μ β τ IH F *; intros Hok Hm Hr Hs Ht; cbn.
    inversion Hok; subst.
    rewrite (subst_kind_id _ _ _ Hr Hs).
    rewrite (idSubst_memory _ Hm).
    f_equal; by eapply IH.
  - intros κ ϕ IH F *; intros Hok Hm Hr Hs Ht; cbn.
    inversion Hok; subst.
    rewrite (subst_kind_id _ _ _ Hr Hs).
    f_equal; by eapply IH.
  - intros κ τ IH F *; intros Hok Hm Hr Hs Ht; cbn.
    inversion Hok; subst.
    rewrite (subst_kind_id _ _ _ Hr Hs).
    f_equal; by eapply IH.
  - intros κ ρ F *; intros Hok Hm Hr Hs Ht; cbn.
    inversion Hok; subst.
    rewrite (subst_kind_id _ _ _ Hr Hs).
    by rewrite (idSubst_representation _ Hr).
  - intros κ σ F *; intros Hok Hm Hr Hs Ht; cbn.
    inversion Hok; subst.
    rewrite (subst_kind_id _ _ _ Hr Hs).
    by rewrite (idSubst_size _ _ Hr Hs).
  - intros κ τ IH F *; intros Hok Hm Hr Hs Ht; cbn.
    inversion Hok as [| | | | | | | | | | | |? ? ? Hκ Hτ| | | |]; subst.
    rewrite (subst_kind_id _ _ _ Hr Hs).
    f_equal.
    eapply (IH _ _ _ _ _ Hτ);
      auto using sub_id_up_type_memory, sub_id_up_type_representation, sub_id_up_type_size,
        sub_scope_type_up_type.
  - intros κ τ IH F *; intros Hok Hm Hr Hs Ht; cbn.
    inversion Hok as [| | | | | | | | | | | | |? ? ? Hκ Hτ| | |]; subst.
    rewrite (subst_kind_id _ _ _ Hr Hs).
    f_equal.
    eapply (IH _ _ _ _ _ Hτ);
      auto using sub_id_up_memory_memory, sub_id_up_memory_representation, sub_id_up_memory_size,
        sub_scope_type_up_mem.
  - intros κ τ IH F *; intros Hok Hm Hr Hs Ht; cbn.
    inversion Hok as [| | | | | | | | | | | | | |? ? ? Hκ Hτ| |]; subst.
    rewrite (subst_kind_id _ _ _ Hr Hs).
    f_equal.
    eapply (IH _ _ _ _ _ Hτ);
      auto using sub_id_up_representation_memory, sub_id_up_representation_representation,
        sub_id_up_representation_size, sub_scope_type_up_rep.
  - intros κ τ IH F *; intros Hok Hm Hr Hs Ht; cbn.
    inversion Hok as [| | | | | | | | | | | | | | |? ? ? Hκ Hτ|]; subst.
    rewrite (subst_kind_id _ _ _ Hr Hs).
    f_equal.
    eapply (IH _ _ _ _ _ Hτ);
      auto using sub_id_up_size_memory, sub_id_up_size_representation, sub_id_up_size_size,
        sub_scope_type_up_size.
  - intros κ κ0 τ IH F *; intros Hok Hm Hr Hs Ht; cbn.
    inversion Hok as [| | | | | | | | | | | | | | | |? ? ? ? Hκ Hκ0 Hτ]; subst.
    rewrite !(subst_kind_id _ _ _ Hr Hs).
    f_equal.
    eapply (IH _ _ _ _ _ Hτ);
      auto using sub_id_up_type_memory, sub_id_up_type_representation, sub_id_up_type_size,
        sub_scope_type_up_type.
  - intros τs1 τs2 IH1 IH2 F *; intros Hok Hm Hr Hs Ht; cbn.
    inversion Hok; subst.
    f_equal; by eapply map_subst_id.
  - intros κ ϕ IH F *; intros Hok Hm Hr Hs Ht; cbn.
    inversion Hok as [|? ? ? Hκ Hϕ]; subst.
    rewrite (subst_kind_id _ _ _ Hr Hs).
    f_equal.
    eapply (IH _ _ _ _ _ Hϕ);
      auto using sub_id_up_type_memory, sub_id_up_type_representation, sub_id_up_type_size,
        sub_scope_type_up_type.
  - intros ϕ IH F *; intros Hok Hm Hr Hs Ht; cbn.
    inversion Hok; subst.
    f_equal; by eapply IH.
  - intros ϕ IH F *; intros Hok Hm Hr Hs Ht; cbn.
    inversion Hok as [| | |? ? Hϕ]; subst.
    f_equal.
    eapply (IH _ _ _ _ _ Hϕ);
      auto using sub_id_up_memory_memory, sub_id_up_memory_representation, sub_id_up_memory_size,
        sub_scope_type_up_mem.
  - intros ϕ IH F *; intros Hok Hm Hr Hs Ht; cbn.
    inversion Hok as [|? ? Hϕ| |]; subst.
    f_equal.
    eapply (IH _ _ _ _ _ Hϕ);
      auto using sub_id_up_representation_memory, sub_id_up_representation_representation,
        sub_id_up_representation_size, sub_scope_type_up_rep.
  - intros ϕ IH F *; intros Hok Hm Hr Hs Ht; cbn.
    inversion Hok as [| |? ? Hϕ|]; subst.
    f_equal.
    eapply (IH _ _ _ _ _ Hϕ);
      auto using sub_id_up_size_memory, sub_id_up_size_representation, sub_id_up_size_size,
        sub_scope_type_up_size.
Qed.

(* --- corollaries --- *)

Lemma has_kind_type_ok F τ κ : has_kind F τ κ -> type_ok F τ.
Proof. intros Hk; apply has_kind_inv in Hk; by inversion Hk. Qed.

Lemma Forall2_type_ok F τs κs : Forall2 (has_kind F) τs κs -> Forall (type_ok F) τs.
Proof. induction 1; [done|]; constructor; [by eapply has_kind_type_ok|done]. Qed.

Lemma has_kind_ift_ok F ϕ : has_kind_ift F ϕ -> inner_function_type_ok F ϕ.
Proof.
  revert F; induction ϕ as [τs1 τs2|κ ϕ IH]; intros F Hk; inversion Hk; subst.
  - constructor; by eapply Forall2_type_ok.
  - constructor; [done|by apply IH].
Qed.

Lemma has_kind_ft_ok F ϕ : has_kind_ft F ϕ -> function_type_ok F ϕ.
Proof.
  revert F; induction ϕ as [ϕ|ϕ IH|ϕ IH|ϕ IH]; intros F Hk; inversion Hk; subst;
    constructor; auto using has_kind_ift_ok.
Qed.

Lemma subst_type_closed τ σm σr σs σt : type_ok fc_empty τ -> subst_type σm σr σs σt τ = τ.
Proof.
  intros Hok.
  have Hid : subst_type VarM VarR VarS σt τ = τ.
  { eapply (proj1 subst_id τ fc_empty VarM VarR VarS σt Hok); intros n; try done.
    cbn; lia. }
  have Hag : subst_type VarM VarR VarS σt τ = subst_type σm σr σs σt τ.
  { eapply (proj1 subst_agree τ fc_empty VarM σm VarR σr VarS σs σt).
    - by rewrite Hid.
    - intros n Hn; inversion Hn; cbn in *; lia.
    - intros n Hn; inversion Hn; cbn in *; lia.
    - intros n Hn; inversion Hn; cbn in *; lia. }
  by rewrite -Hag Hid.
Qed.

Lemma subst_function_type_closed ϕ σm σr σs σt :
  function_type_ok fc_empty ϕ -> subst_function_type σm σr σs σt ϕ = ϕ.
Proof.
  intros Hok.
  have Hid : subst_function_type VarM VarR VarS σt ϕ = ϕ.
  { eapply (proj1 (proj2 subst_id) ϕ fc_empty VarM VarR VarS σt Hok); intros n; try done.
    cbn; lia. }
  have Hag : subst_function_type VarM VarR VarS σt ϕ = subst_function_type σm σr σs σt ϕ.
  { eapply (proj1 (proj2 subst_agree) ϕ fc_empty VarM σm VarR σr VarS σs σt).
    - by rewrite Hid.
    - intros n Hn; inversion Hn; cbn in *; lia.
    - intros n Hn; inversion Hn; cbn in *; lia.
    - intros n Hn; inversion Hn; cbn in *; lia. }
  by rewrite -Hag Hid.
Qed.

Lemma pack_mem_witness F τ μ κ :
  has_kind F (subst_type (unscoped.scons μ VarM) VarR VarS VarT τ) κ ->
  exists μ0,
    mem_ok (fc_kind_ctx F) μ0 /\
    subst_type (unscoped.scons μ VarM) VarR VarS VarT τ
    = subst_type (unscoped.scons μ0 VarM) VarR VarS VarT τ.
Proof.
  intros Hk.
  destruct μ as [n|c]; [destruct (decide (n < kc_mem_vars (fc_kind_ctx F))) as [Hlt|Hlt]|].
  - exists (VarM n); split; [by constructor|done].
  - exists (BaseM MemGC); split; [by constructor|].
    eapply (proj1 subst_agree τ F _ _ VarR VarR VarS VarS VarT);
      [by eapply has_kind_type_ok| |done|done].
    intros [|m] Hokm; cbn in *; [by inversion Hokm|done].
  - exists (BaseM c); split; [by constructor|done].
Qed.

Lemma pack_rep_witness F τ ρ κ :
  has_kind F (subst_type VarM (unscoped.scons ρ VarR) VarS VarT τ) κ ->
  exists ρ0,
    rep_ok (fc_kind_ctx F) ρ0 /\
    subst_type VarM (unscoped.scons ρ VarR) VarS VarT τ
    = subst_type VarM (unscoped.scons ρ0 VarR) VarS VarT τ.
Proof.
  intros Hk.
  destruct (rep_okb (fc_kind_ctx F) ρ) eqn:Hb.
  - exists ρ; split; [by apply rep_okb_iff|done].
  - exists (AtomR I32R); split; [by constructor|].
    eapply (proj1 subst_agree τ F VarM VarM _ _ VarS VarS VarT);
      [by eapply has_kind_type_ok|done| |done].
    intros [|m] Hokm; cbn in *; [|done].
    by rewrite -(rep_okb_iff (fc_kind_ctx F) ρ) Hb in Hokm.
Qed.

Lemma pack_size_witness F τ σ κ :
  has_kind F (subst_type VarM VarR (unscoped.scons σ VarS) VarT τ) κ ->
  exists σ0,
    size_ok (fc_kind_ctx F) σ0 /\
    subst_type VarM VarR (unscoped.scons σ VarS) VarT τ
    = subst_type VarM VarR (unscoped.scons σ0 VarS) VarT τ.
Proof.
  intros Hk.
  destruct (size_okb (fc_kind_ctx F) σ) eqn:Hb.
  - exists σ; split; [by apply size_okb_iff|done].
  - exists (ConstS 0); split; [by constructor|].
    eapply (proj1 subst_agree τ F VarM VarM VarR VarR _ _ VarT);
      [by eapply has_kind_type_ok|done|done|].
    intros [|m] Hokm; cbn in *; [|done].
    by rewrite -(size_okb_iff (fc_kind_ctx F) σ) Hb in Hokm.
Qed.
