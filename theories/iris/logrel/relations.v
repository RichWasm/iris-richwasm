From mathcomp Require Import eqtype seq.

Require Import iris.proofmode.tactics.

From RichWasm Require Import syntax typing.
From RichWasm.compiler Require Import codegen types util.
From RichWasm.iris Require Import gc num_reprs util.
Require Import RichWasm.iris.logrel.util.
Require Import RichWasm.util.debruijn.
Require Import RichWasm.iris.language.lenient_wp.
Require Import RichWasm.iris.language.logpred.
Require Wasm.iris.logrel.iris_logrel.
Import uPred.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Relations.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!rwasm_gcG Σ}.

  Variable sr : store_runtime.

  Definition ns_func (x : N) : namespace := nroot .@ "rwf" .@ x.
  Definition ns_ref (x : N) : namespace := nroot .@ "rwr" .@ x.
  Inductive sem_val :=
  | SVMem (bs: bytes)
  | SVVal (v: val).

  Definition sem_type := sem_val -> iProp Σ.
  Notation SVR := (leibnizO sem_val -n> iPropO Σ).
  Definition sem_typeO := SVR.
  Notation VR := (leibnizO val -n> iPropO Σ).
  Notation WsR := (leibnizO (list value) -n> iPropO Σ).
  Notation VVsR := (leibnizO vblock -n> iPropO Σ).
  Notation FR := (leibnizO frame -n> iPropO Σ).
  Notation HVR_mm := (leibnizO bytes -n> iPropO Σ).
  Notation HVR_gc := (leibnizO vblock -n> iPropO Σ).
  Notation ClR := (leibnizO function_closure -n> iPropO Σ).
  Notation ER := (leibnizO (lholed * list administrative_instruction) -n> iPropO Σ).

  Implicit Type L : leibnizO local_ctx.
  Implicit Type WL : leibnizO wlocal_ctx.

  Implicit Type sv : leibnizO sem_val.
  Implicit Type v : leibnizO val.
  Implicit Type ws : leibnizO (list value).
  Implicit Type vvs : leibnizO vblock.
  Implicit Type bs : leibnizO bytes.
  Implicit Type f : leibnizO frame.
  Implicit Type cl : leibnizO function_closure.
  Implicit Type lh_es : leibnizO (lholed * list administrative_instruction).

  Implicit Type τ : leibnizO type.
  Implicit Type τs : leibnizO (list type).
  Implicit Type ϕ : leibnizO function_type.
  Implicit Type χ : leibnizO arrow_type.
  
  Definition sem_kind := sem_type -> iProp Σ.
  Notation KR := (sem_typeO -n> iPropO Σ).
  
  Definition prim_repr_interp (ι : primitive_rep) (w: value) : Prop :=
    match ι with
    | PtrR => ∃ i, w = VAL_int32 i
    | I32R => ∃ i, w = VAL_int32 i
    | I64R => ∃ i, w = VAL_int64 i
    | F32R => ∃ f: f32, w = VAL_float32 f
    | F64R => ∃ f: f64, w = VAL_float64 f
    end.
    
  (*
  Fixpoint repr_val_interp (ρ: representation) (ws: list value) {struct ρ} : Prop :=
    match ρ with
    | VarR n => False
    | SumR ρs => False
    | ProdR ρs => ∃ wss, ws = flatten wss /\ reprs_vals_interp ρs wss
    | PrimR ι => ∃ w, ws = [w] /\ prim_repr_interp ι w
    end
  with reprs_vals_interp (ρs: list representation) (wss : list (list value)) {struct ρs} : Prop :=
    match ρs with
    | [], [] => True
    | ρ::ρs', ws::wss' => repr_val_interp ρ ws /\ reprs_vals_interp ρs' wss'
    | _, _ => False
    end.
    | cons ρ ρs => repr_val_interp ρ
    end
    Forall2 repr_val_interp ρs.


  Definition repr_interp (ρ : representation) : sem_kind :=
    match ρ with
    | VarR n => _
    | SumR ρs => _
    | ProdR ρs => λ T, ∀ v, T v -> ∃ vs, v = flatten vs /\ Forall2 (repr_interp) ρs 
    | PrimR ι => λ T, ∀ v, T v -> ∃v0, v = [v0] /\ prim_repr_interp v0
    end
    

  Definition kind_interp (κ : kind) : sem_kind := 
    match κ with
    | VALTYPE ρ γ =>
        λ T, ∀ v, 
    | MEMTYPE ζ μ γ => 
        λ T, 
*)  

  Definition relations : Type :=
    (* Physical Value *)
    (leibnizO type -n> WsR) *
    (* Virtual Value *)
    (leibnizO type -n> VVsR) *
    (* Frame *)
    (leibnizO local_ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FR) *
    (* Expression *)
    (leibnizO (list type) -n> leibnizO function_ctx -n> leibnizO local_ctx -n>
       leibnizO wlocal_ctx -n> leibnizO instance -n> ER).

  Definition relations_value_phys (rs : relations) : leibnizO type -n> WsR :=
    rs.1.1.1.

  Definition relations_value_virt (rs : relations) : leibnizO type -n> VVsR :=
    rs.1.1.2.

  Definition relations_frame (rs : relations) :
    leibnizO local_ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FR :=
    rs.1.2.

  Definition relations_expr (rs : relations) :
    leibnizO (list type) -n> leibnizO function_ctx -n> leibnizO local_ctx -n>
      leibnizO wlocal_ctx -n> leibnizO instance -n> ER :=
    rs.2.

  Definition interp_frame_0 (rs : relations) :
    leibnizO local_ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FR.
  Admitted.

  Definition interp_expr_0 (rs : relations) :
    leibnizO (list type) -n> leibnizO function_ctx -n> leibnizO local_ctx -n>
      leibnizO wlocal_ctx -n> leibnizO instance -n> ER.
  Admitted.

  Definition rels_0 (rs : relations) : relations.
  Admitted.

  Instance Contractive_rels_0 : Contractive rels_0.
  Admitted.

  Definition rels : relations := fixpoint rels_0.

  Definition interp_value_phys : leibnizO type -n> WsR := relations_value_phys rels.

  Definition interp_value_virt : leibnizO type -n> VVsR := relations_value_virt rels.

  Definition interp_frame :
    leibnizO local_ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FR :=
    relations_frame rels.

  Definition interp_expr :
    leibnizO (list type) -n> leibnizO function_ctx -n> leibnizO local_ctx -n>
      leibnizO wlocal_ctx -n> leibnizO instance -n> ER :=
    relations_expr rels.

  Lemma rels_eq : rels ≡ rels_0 rels.
  Proof. apply fixpoint_unfold. Qed.

  (*
  Lemma interp_value_phys_eq τ ws :
    interp_value_phys τ ws ⊣⊢ interp_value_phys_0 rels τ ws.
  Proof.
    do 2 f_equiv.
    transitivity (rels_0 rels).1.1.1.
    - apply rels_eq.
    - reflexivity.
  Qed.

  Lemma interp_value_virt_eq τ vvs :
    interp_value_virt τ vvs ⊣⊢ interp_value_virt_0 rels τ vvs.
  Proof.
    do 2 f_equiv.
    transitivity (rels_0 rels).1.1.2.
    - apply rels_eq.
    - reflexivity.
  Qed.

  Lemma interp_expr_eq τs F L WL i e :
    interp_expr τs F L WL i e ⊣⊢ interp_expr_0 rels τs F L WL i e.
  Proof.
    do 6 f_equiv.
    transitivity (rels_0 rels).2.
    - apply rels_eq.
    - reflexivity.
  Qed.

  Lemma interp_frame_eq L WL i f :
    interp_frame L WL i f ⊣⊢ interp_frame_0 rels L WL i f.
  Proof.
    do 4 f_equiv.
    transitivity (rels_0 rels).1.2.
    - apply rels_eq.
    - reflexivity.
  Qed.

*)
  Opaque relations_value_phys.
  Opaque relations_value_virt.
  Opaque relations_frame.
  Opaque relations_expr.

  Definition interp_val (τs : list type) : VR. Admitted.

  Definition interp_stack (τs : list type) : VR. Admitted.

  Definition interp_inst (M : module_ctx) (inst : instance) : iProp Σ :=
    True.

  Definition interp_ctx (L L' : local_ctx) (F : function_ctx) (inst : instance) (lh : lholed) :
    iProp Σ :=
    True.

  Definition semantic_typing
    (M : module_ctx)
    (F : function_ctx)
    (L : local_ctx)
    (WL : wlocal_ctx)
    (es : list administrative_instruction)
    (τa : arrow_type)
    (L' : local_ctx) :
    iProp Σ :=
    let '(ArrowT τs1 τs2) := τa in
    ∀ inst lh,
    interp_inst M inst ∗ interp_ctx L L' F inst lh -∗
    ∀ f vs,
    interp_stack τs1 vs ∗ interp_frame L WL inst f ∗ ↪[frame] f -∗
    interp_expr τs2 F L' WL inst (lh, of_val vs ++ es).

End Relations.
