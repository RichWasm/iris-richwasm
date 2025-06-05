From stdpp Require Import base fin_maps.
From RWasm Require Import typing term annotated_term subst debruijn.
Module RT := RWasm.term.
Module R := RWasm.annotated_term.
Module T := RWasm.typing.

From mathcomp Require Import ssreflect ssrbool eqtype seq.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import list.
From iris.prelude Require Import options.

From Wasm.iris.helpers Require Export iris_properties.
From Wasm.iris.language Require Export iris_atomicity.
From Wasm.iris.rules Require Export iris_rules.
From Wasm.iris.logrel Require iris_logrel.

Import uPred.

Set Bullet Behavior "Strict Subproofs".

Definition rf : string := "rfN".
Definition rt : string := "rtN".
Definition rm : string := "rmN".
Definition rg : string := "rgN".
Definition rfN (a : N) : namespace := nroot .@ rf .@ a.
Definition rtN (a b: N) : namespace := nroot .@ rt .@ a .@ b.
Definition rmN (a: N) : namespace := nroot .@ rm .@ a.
Definition rgN (a: N) : namespace := nroot .@ rg .@ a.

Definition rwmem := N.of_nat 0.

Ltac solve_iprop_ne :=
 repeat (apply exist_ne +
         apply intuitionistically_ne +
         apply or_ne +
         apply sep_ne +
         apply and_ne +
         apply wp_ne +
         apply inv_ne +
         auto +
         (rewrite /pointwise_relation; intros) +
         apply forall_ne + apply wand_ne).
Local Obligation Tactic := try solve_proper.

Class Read := {
  read_value : RT.Typ -> bytes -> list value;
  read_tag : bytes -> nat;
}.

Section logrel.

Context `{!wasmG Σ, !logrel_na_invs Σ, !Read}.
Variable (GC_MEM: immediate).
Variable (LIN_MEM: immediate).
Variable (mems_diff: GC_MEM <> LIN_MEM).

Record stack := Stack { stack_values : list value }.
Canonical Structure stackO := leibnizO stack.

Notation VR := ((leibnizO val) -n> iPropO Σ).
Notation WR := ((leibnizO value) -n> iPropO Σ).
Notation WsR := (stackO -n> iPropO Σ).
Notation FR := ((leibnizO frame) -n> iPropO Σ).
Notation HR := ((leibnizO bytes) -n> iPropO Σ).
Notation ClR := ((leibnizO function_closure) -n> iPropO Σ).

(* locals exclusive to webassembly (compiler-generated temporaries, etc) *)
Definition wlocal_ctx := seq.seq value_type.

Definition relations : Type := 
  (* interp_value *)
  (leibnizO RT.Typ -n> WsR) *
  (* interp_frame *)
  (leibnizO T.Local_Ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FR) * 
  (* interp_expr *)
  (leibnizO (list RT.Typ) -n>
   leibnizO T.Function_Ctx -n>
   leibnizO T.Local_Ctx -n>
   leibnizO wlocal_ctx -n>
   leibnizO instance -n>
   leibnizO (lholed * list administrative_instruction) -n>
   iPropO Σ).

Canonical Structure relationsO : ofe := Ofe relations (@prod_ofe_mixin (prodO _ _) _ : OfeMixin relations).

Program Definition rels_value : relationsO -n> _ :=
  λne (r: relationsO), r.1.1.

Program Definition rels_frame : relationsO -n> _ :=
  λne (r: relationsO), r.1.2.

Definition rels_expr :
  relationsO -n>
  leibnizO (list RT.Typ) -n>
  leibnizO T.Function_Ctx -n>
  leibnizO T.Local_Ctx -n>
  leibnizO wlocal_ctx -n>
  leibnizO instance -n>
  leibnizO (lholed * list administrative_instruction) -n>
  iPropO Σ :=
  λne (r: relationsO), snd r.

Global Instance relations_inhabited : Inhabited relationsO.
Proof.
  apply populate.
  unfold relationsO, relations.
  exact (λne _ _, ⌜true⌝%I,
         λne _ _ _ _, ⌜true⌝%I,
         λne _ _ _ _ _ _, ⌜true⌝%I).
Qed.

Program Definition interp_heap_value_variant : relationsO -n> leibnizO (list RT.Typ) -n> HR :=
  λne (rs : relationsO) (τs : leibnizO (list RT.Typ)) (bs : leibnizO bytes), (
    ∃ bs_tag bs_payload bs_rest,
    ⌜bs = bs_tag ++ bs_payload ++ bs_rest⌝ ∗
    let tag := read_tag bs_tag in
    ∃ τ,
    ⌜τs !! tag = Some τ⌝ ∗
    let ws := read_value τ bs_payload in
    rels_value rs τ (Stack ws)
  )%I.

Program Definition interp_heap_value_struct : relationsO -n> leibnizO (list (RT.Typ * RT.Size)) -n> HR :=
  λne (rs : relationsO) (fs : leibnizO (list (RT.Typ * RT.Size))) (bs : leibnizO bytes), (
    ∃ (bss : list bytes) (bs_rest : bytes),
      ⌜bs = flatten bss ++ bs_rest⌝ ∗
      [∗ list] f;fbs ∈ fs;bss,
        let '(τ, sz) := f in
        let ws := read_value τ fbs in
        rels_value rs τ (Stack ws)
  )%I.
Next Obligation.
  solve_proper_prepare.
  solve_iprop_ne.
  apply big_sepL2_ne; intros.
  destruct y1.
  solve_iprop_ne.
  apply H0.
Qed.

Program Definition interp_heap_value_array : relationsO -n> leibnizO RT.Typ -n> HR :=
  (λne (rs : relationsO) (τ : leibnizO RT.Typ) (bs : leibnizO bytes), ∃ bss bs_rest,
    ⌜bs = flatten bss ++ bs_rest⌝ ∗
    [∗ list] ebs ∈ bss,
      let ws := read_value τ ebs in
      rels_value rs τ (Stack ws))%I.
Opaque interp_heap_value_array.

Definition interp_heap_value : relationsO -> leibnizO RT.HeapType -n> HR :=
  λ (rs: relationsO), λne (Ψ : leibnizO RT.HeapType),
  match Ψ with
  | RT.VariantType τs => interp_heap_value_variant rs τs
  | RT.StructType fields => interp_heap_value_struct rs fields
  | RT.ArrayType τ => interp_heap_value_array rs τ
  | RT.Ex _ _ _ => λne _ , ⌜False⌝%I (* TODO *)
  end.
Instance interp_heap_value_ne : NonExpansive interp_heap_value.
Proof.
  Opaque interp_heap_value_struct.
  intros n rs rs' Hrs Ψ bs.
  destruct Ψ; solve_proper.
  Transparent interp_heap_value_struct.
Qed.

Definition interp_pre_value_unit : WsR := λne ws, ⌜∃ z, head (stack_values ws) = Some (VAL_int32 z)⌝%I.

Definition interp_values (rs : relations) : leibnizO (list RT.Typ) -n> WsR :=
  λne (τs : leibnizO (list RT.Typ)) ws, (∃ wss ws_rest,
    ⌜stack_values ws = flatten wss ++ ws_rest⌝ ∗
    [∗ list] τ;ws ∈ τs;wss, rels_value rs τ (Stack ws)
  )%I.

Definition interp_pre_value_num : leibnizO RT.NumType -n> WsR :=
  λne (np : leibnizO RT.NumType) ws,
    match np with
    | RT.Int _ RT.i32 => ⌜∃ z, head (stack_values ws) = Some (VAL_int32 z)⌝%I
    | RT.Int _ RT.i64 => ⌜∃ z, head (stack_values ws) = Some (VAL_int64 z)⌝%I
    | RT.Float RT.f32 => ⌜∃ z, head (stack_values ws) = Some (VAL_float32 z)⌝%I
    | RT.Float RT.f64 => ⌜∃ z, head (stack_values ws) = Some (VAL_float64 z)⌝%I
    end.

Definition function_type_args : leibnizO RT.FunType -> leibnizO (seq.seq RT.Typ) :=
  λ tf,
    match tf with
    | RT.FunT _ (Arrow ts _) => ts
    end.
Instance function_type_args_ne :  NonExpansive function_type_args.
Proof. solve_proper. Qed.

Definition function_type_rets : leibnizO RT.FunType -> leibnizO (seq.seq RT.Typ) :=
  λ tf,
    match tf with
    | RT.FunT _ (Arrow _ ts) => ts
    end.
Instance function_type_rets_ne :  NonExpansive function_type_rets.
Proof. solve_proper. Qed.

Definition interp_closure : relationsO -> leibnizO RT.FunType -n> ClR :=
  λ rs,
    λne (tf: leibnizO RT.FunType) (cl: leibnizO function_closure),
    let t1 := function_type_args tf in
    let t2 := function_type_rets tf in
    match cl with
    | FC_func_native inst (Tf wt1 wt2) tlocs es => (<pers> ⌜False⌝)%I
    | FC_func_host _ _ => ⌜false⌝%I
    end.
Instance interp_closure_rels_ne: NonExpansive (interp_closure) := ltac:(solve_proper).

Definition interp_pre_value_coderef (rs : relationsO) : leibnizO RT.FunType -n> WsR :=
  λne tf ws, (
    ∃ (n : i32) cl,
    let n' := (Z.to_N (Wasm_int.Int32.unsigned n)) in
    na_inv logrel_nais (rfN n') (
      ⌜head (stack_values ws) = Some (VAL_int32 n)⌝ ∗
      n' ↦[wf] cl ∗
      ▷ interp_closure rs tf cl
    )
  )%I.
Instance interp_pre_value_coderef_contractive: Contractive interp_pre_value_coderef :=
  ltac:(solve_contractive).

Definition interp_pre_value_exloc (rs : relationsO) : leibnizO RT.Typ -n> WsR :=
  λne (τ : leibnizO RT.Typ) ws, (∃ ℓ c, ▷ rels_value rs (subst_ext (ext SLoc (LocP ℓ c) id) τ) ws)%I.

Definition interp_pre_value_ref_own
  (rs : relationsO)
: _ -n> _ -n> _ -n> iPropO Σ :=
  λne (sz : leibnizO RT.Size) (ψ : leibnizO RT.HeapType) (z : leibnizO i32),
    ⌜true⌝%I.

Definition interp_value_0 (rs : relations) : leibnizO RT.Typ -n> WsR :=
  λne (τ: leibnizO RT.Typ), λne vs,
    match τ with
    | RT.Num _ => ⌜False⌝
    | RT.TVar _ => ⌜False⌝
    | RT.Unit => ⌜False⌝
    | RT.ProdT _ => ⌜False⌝
    | RT.CoderefT _ => ⌜False⌝
    | RT.Rec _ _ => ⌜False⌝
    | RT.PtrT _ => ⌜False⌝
    | RT.ExLoc _ _ => ⌜False⌝
    | RT.OwnR _ => ⌜False⌝
    | RT.CapT _ _ _ => ⌜False⌝
    | RT.RefT cap (LocP ℓ LinMem) ψ =>
        ∃ bs,
          N.of_nat LIN_MEM ↦[wms][ℓ] bs ∗
          interp_heap_value rs ψ bs
    | RT.RefT _ _ _ => ⌜False⌝
    end%I.

Definition interp_frame_0 (rs : relations) : leibnizO T.Local_Ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FR :=
  λne (L: leibnizO T.Local_Ctx) 
      (WL: leibnizO wlocal_ctx)
      (i: leibnizO instance)
      (f: leibnizO frame),
    (∃ vs wvs: list value, 
        ⌜f = Build_frame (vs ++ wvs) i⌝ ∗ 
        (* not right, throws out sizes with (map fst L) *)
        ▷ interp_values rs (map fst L) (Stack vs) ∗
        iris_logrel.interp_val WL (immV wvs))%I.


Locate "WP".


Search wp Proper.
Check wp_ne.
Locate "λne".
Check OfeMor.

Program Definition interp_expr_0 (rs : relations) :
  leibnizO (list RT.Typ) -n>
  leibnizO T.Function_Ctx -n>
  leibnizO T.Local_Ctx -n>
  leibnizO wlocal_ctx -n>
  leibnizO instance -n>
  leibnizO (lholed * (seq.seq administrative_instruction)) -n>
  iPropO Σ :=
  λne ts C L WL i '(lh, e),
    (WP e {{ w, ∃ vs, ⌜w = immV vs⌝ ∗
                      interp_values rs ts (Stack vs) ∗
                      ∃ f, rels_frame rs L WL i f }})%I.

Definition rels_0 (rs : relations) : relations :=
  (interp_value_0 rs,
   interp_frame_0 rs,
   interp_expr_0 rs).

Instance rels_contractive : Contractive rels_0.
Proof.
Admitted.

Definition rels : relations := fixpoint rels_0.

Notation interp_value := (rels_value rels).
Notation interp_frame := (rels_frame rels).
Notation interp_expr := (rels_expr rels).

Lemma rels_eq :
  rels ≡ rels_0 rels.
Proof.
  apply fixpoint_unfold.
Qed.

Lemma interp_value_eq τs vs :
  interp_value τs vs ⊣⊢ interp_value_0 rels τs vs.
Proof.
  do 2 f_equiv.
  transitivity (rels_0 rels).1.1.
  - apply rels_eq.
  - reflexivity.
Qed.
Opaque rels_value.

Lemma interp_expr_eq ts F L WL i e :
  interp_expr ts F L WL i e ⊣⊢ interp_expr_0 rels ts F L WL i e.
Proof.
  do 6 f_equiv.
  transitivity (snd (rels_0 rels)).
  - apply rels_eq.
  - reflexivity.
Qed.
Opaque rels_expr.

Lemma interp_frame_eq L WL i f :
  interp_frame L WL i f ⊣⊢ interp_frame_0 rels L WL i f.
Proof.
  do 4 f_equiv.
  transitivity (rels_0 rels).1.2.
  - apply rels_eq.
  - reflexivity.
Qed.
Opaque rels_frame.

Definition interp_val (τs : list RT.Typ) : VR :=
  λne (v : leibnizO val), (
    ⌜v = trapV⌝ ∨ ∃ ws, ⌜v = immV ws⌝ ∗ interp_values rels τs (Stack ws)
  )%I.

Definition interp_inst
  (S: T.StoreTyping) 
  (C: T.Module_Ctx) 
  (inst: instance)
  : iProp Σ :=
  ⌜true⌝%I.

Definition interp_ctx
  (L L': T.Local_Ctx)
  (F: T.Function_Ctx) 
  (inst: instance)
  (lh: lholed)
  : iProp Σ :=
  ⌜true⌝%I.

Definition semantic_typing  :
  T.StoreTyping -> T.Module_Ctx -> T.Function_Ctx ->
  T.Local_Ctx -> wlocal_ctx ->
  list administrative_instruction ->
  RT.ArrowType -> T.Local_Ctx ->
  iProp Σ :=
  (λ S C F L WL es '(Arrow τs1 τs2) L',
    ∀ inst lh,
      interp_inst S C inst ∗ interp_ctx L L' F inst lh -∗
      ∀ f vs,
        ↪[frame] f ∗
        interp_val τs1 vs ∗ 
        (* frame points to F ∗ *)
        interp_frame L WL inst f -∗
        interp_expr τs2 F L' WL inst (lh, (of_val vs ++ es)))%I.

Require Import RWasm.compile.
Lemma sniff_test S C F L cap l ℓ sgn τ eff es :
  l = LocP ℓ LinMem ->
  τ = RefT cap l (StructType [(Num (Int sgn RT.i32), SizeConst 1)]) ->
  eff = Arrow [τ] [τ; Num (Int sgn RT.i32)] ->
  compile_instr [] 0 0 1 (Instr (StructGet 0) eff) = Some es ->
  ⊢ semantic_typing S C F L [T_i32] (to_e_list es) eff L.
Proof.
  intros Hl Hτ Heff.
  subst eff l.
  intros Hcomp.
  unfold compile_instr in Hcomp.
  rewrite Hτ in Hcomp.
  cbn in Hcomp.
  apply Some_inj in Hcomp.
  unfold semantic_typing.
  iIntros "%inst %lh [Hinst Hctx] %f %vs (Hfr & Hval & Hloc)".
  rewrite interp_expr_eq.
  rewrite interp_frame_eq.
  unfold interp_val.
  iClear "Hloc".
  iDestruct "Hval" as "[Htrap | (%vs' & %Hvs'eq & Hval)]".
  - admit.
  - rewrite -> Hτ.
    cbn.
    iDestruct "Hval" as "(%wss & %ws_rest & %Hvs' & Hval)".
    Locate "[∗".
    iPoseProof (big_sepL2_length with "[$Hval]") as "%Hlens".
    destruct wss as [|ws wss]; cbn in Hlens; try discriminate Hlens.
    destruct wss; cbn in Hlens; try discriminate Hlens.
    rewrite big_sepL2_singleton.
    setoid_rewrite interp_value_eq.
    iEval (cbn) in "Hval".
    iDestruct "Hval" as "(%bs & Hptr & %bss & %bs_rest & %Hconcat & Hfields)".
    iPoseProof (big_sepL2_length with "[$Hfields]") as "%Hflens".
    destruct bss as [|bs' bss]; try discriminate Hflens.
    destruct bss; try discriminate Hflens.
    rewrite big_sepL2_singleton.
    setoid_rewrite interp_value_eq.
    admit.
Abort.

End logrel.
