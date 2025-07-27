From mathcomp Require Import eqtype seq.

Require Import iris.proofmode.tactics.

From RichWasm Require subst term typing.
From RichWasm.compiler Require Import codegen types util.
From RichWasm.iris Require Import gc num_reprs util.
Require Import RichWasm.iris.logrel.util.
Require Import RichWasm.util.debruijn.
Import uPred.

Module R. Include RichWasm.subst <+ RichWasm.term <+ RichWasm.typing. End R.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Relations.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.

  Variable sr : store_runtime.

  Obligation Tactic := try solve_proper.

  Definition ns_func (x : N) : namespace := nroot .@ "rwf" .@ x.

  Notation VR := (leibnizO val -n> iPropO Σ).
  Notation WsR := (leibnizO (list value) -n> iPropO Σ).
  Notation FR := (leibnizO frame -n> iPropO Σ).
  Notation HVmmR := (leibnizO bytes -n> iPropO Σ).
  Notation HVgcR := (leibnizO (list vval) -n> iPropO Σ).
  Notation ClR := (leibnizO function_closure -n> iPropO Σ).
  Notation ER := (leibnizO (lholed * list administrative_instruction) -n> iPropO Σ).

  Implicit Types L : leibnizO R.Local_Ctx.
  Implicit Types WL : leibnizO wlocal_ctx.

  Implicit Types v : leibnizO val.
  Implicit Types f : leibnizO frame.
  Implicit Types cl : leibnizO function_closure.
  Implicit Types i : leibnizO instance.

  Implicit Types τf : leibnizO R.FunType.

  Definition relations : Type :=
    (* Physical Value *)
    (leibnizO R.Typ -n> WsR) *
    (* Frame *)
    (leibnizO R.Local_Ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FR) *
    (* Expression *)
    (leibnizO (list R.Typ) -n>
     leibnizO R.Function_Ctx -n>
     leibnizO R.Local_Ctx -n>
     leibnizO wlocal_ctx -n>
     leibnizO instance -n>
     ER).

  Canonical Structure relationsO : ofe := Ofe relations (@prod_ofe_mixin (prodO _ _) _).

  Program Definition relations_value_phys : relationsO -n> leibnizO R.Typ -n> WsR :=
    λne rs, rs.1.1.

  Program Definition relations_frame :
    relationsO -n> leibnizO R.Local_Ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FR :=
    λne rs, rs.1.2.

  Definition relations_expr :
    relationsO -n>
    leibnizO (list R.Typ) -n>
    leibnizO R.Function_Ctx -n>
    leibnizO R.Local_Ctx -n>
    leibnizO wlocal_ctx -n>
    leibnizO instance -n>
    ER :=
    λne rs, snd rs.

  Program Definition interp_heap_value_mm_variant : relationsO -n> leibnizO (list R.Typ) -n> HVmmR :=
    λne rs τs bs, (
      ∃ bs_tag bs_data,
      ⌜bs = bs_tag ++ bs_data⌝ ∗
      ∃ tag tag_i32 τ,
      ⌜wasm_deserialise bs_tag T_i32 = VAL_int32 tag_i32⌝ ∗
      ⌜nat_repr tag tag_i32⌝ ∗
      ⌜τs !! tag = Some τ⌝ ∗
      relations_value_phys rs τ (deserialize_values bs_data τ)
    )%I.

  Program Definition interp_heap_value_mm_struct :
    relationsO -n> leibnizO (list (R.Typ * R.Size)) -n> HVmmR :=
    λne rs fs bs, (
      ∃ bss,
      ⌜bs = flatten bss⌝ ∗
      [∗ list] '(τ, sz); bs' ∈ fs; bss,
      ⌜length bs' = (4 * R.interp_size (const 0) sz)%nat⌝ ∗
      relations_value_phys rs τ (deserialize_values bs' τ)
    )%I.
  Final Obligation.
    solve_proper_prepare.
    solve_iprop_ne.
    apply big_sepL2_ne; intros.
    destruct y1.
    solve_iprop_ne.
    do 4 Morphisms.f_equiv.
    apply H.
  Qed.

  Program Definition interp_heap_value_mm_array : relationsO -n> leibnizO R.Typ -n> HVmmR :=
    λne rs τ bs, (
      ∃ bs_len bs_elems,
      ⌜bs = bs_len ++ flatten bs_elems⌝ ∗
      ∃ len len_i32,
      ⌜wasm_deserialise bs_len T_i32 = VAL_int32 len_i32⌝ ∗
      ⌜nat_repr len len_i32⌝ ∗
      ⌜len = length bs_elems⌝ ∗
      [∗ list] bs_elem ∈ bs_elems,
      relations_value_phys rs τ (deserialize_values bs_elem τ)
    )%I.

  Definition interp_heap_value_mm_ex :
    relationsO -n> leibnizO R.Size -n> leibnizO R.Qual -n> leibnizO R.Typ -n> HVmmR :=
    λne rs sz q τ bs, False%I.

  Program Definition interp_heap_value_mm (rs : relations) : leibnizO R.HeapType -n> HVmmR :=
    λne Ψ,
    match Ψ with
    | R.VariantType τs => interp_heap_value_mm_variant rs τs
    | R.StructType fs => interp_heap_value_mm_struct rs fs
    | R.ArrayType τ => interp_heap_value_mm_array rs τ
    | R.Ex sz q τ => interp_heap_value_mm_ex rs sz q τ
    end.

  Definition interp_closure (rs : relations) : leibnizO R.FunType -n> ClR :=
    λne τf cl,
    let '(R.FunT _ (R.Arrow τ1 τ2)) := τf in
    match cl with
    | FC_func_native inst (Tf ts1 ts2) ts_local es => False%I
    | FC_func_host _ _ => False%I
    end.

  Program Definition interp_value_phys_coderef (rs : relations) : leibnizO R.FunType -n> WsR :=
    λne tf ws, (
      ∃ n,
      ⌜ws = [VAL_int32 n]⌝ ∗
      ∃ cl,
      ▷ interp_closure rs tf cl ∗
      let n' := Z.to_N (Wasm_int.Int32.unsigned n) in
      na_inv logrel_nais (ns_func n') (n' ↦[wf] cl)
    )%I.

  Definition interp_value_phys_exloc (rs : relations) : leibnizO R.Typ -n> WsR :=
    λne τ ws, (
      ∃ ℓ c, ▷ relations_value_phys rs (subst_ext (ext R.SLoc (R.LocP ℓ c) id) τ) ws
    )%I.

  Program Definition interp_value_phys_ref_mm (rs : relations) (p : R.Ptr) (ψ : R.HeapType) : WsR :=
    λne ws, (
      ∃ bs l32,
      ⌜ws = [VAL_int32 l32]⌝ ∗
      ⌜ptr_repr (R.LocP p R.LinMem) l32⌝ ∗
      N.of_nat sr.(sr_mem_mm) ↦[wms][p] bs ∗
      interp_heap_value_mm rs ψ bs
    )%I.

  Program Definition interp_values_phys (rs : relations) : leibnizO (list R.Typ) -n> WsR :=
    λne τs ws, (
      ∃ wss, ⌜ws = flatten wss⌝ ∗ [∗ list] τ; ws' ∈ τs; wss, relations_value_phys rs τ ws'
    )%I.

  Program Definition interp_value_phys_0 (rs : relations) : leibnizO R.Typ -n> WsR :=
    λne τ ws,
    match τ with
    | R.Num (R.Int _ R.i32) => ∃ n, ⌜ws = [VAL_int32 n]⌝
    | R.Num (R.Int _ R.i64) => ∃ n, ⌜ws = [VAL_int64 n]⌝
    | R.Num (R.Float R.f32) => ∃ n, ⌜ws = [VAL_float32 n]⌝
    | R.Num (R.Float R.f64) => ∃ n, ⌜ws = [VAL_float64 n]⌝
    | R.TVar _ => False
    | R.Unit => ∃ n, ⌜ws = [VAL_int32 n]⌝
    | R.ProdT τs => interp_values_phys rs τs ws
    | R.CoderefT tf => interp_value_phys_coderef rs tf ws
    | R.Rec _ _ => False
    | R.PtrT _ => False
    | R.ExLoc _ τ => interp_value_phys_exloc rs τ ws
    | R.OwnR _ => ⌜nilp ws⌝
    | R.CapT _ _ _ => ⌜nilp ws⌝
    | R.RefT _ (R.LocP p R.LinMem) ψ => interp_value_phys_ref_mm rs p ψ ws
    | R.RefT _ (R.LocP p R.GCMem) ψ => False
    | R.RefT _ (R.LocV _) _ => False
    end%I.

  Definition interp_frame_0 (rs : relations) :
    leibnizO R.Local_Ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FR :=
    λne L WL i f, (
      ↪[frame] f ∗
      ∃ ws_l ws_wl : list value,
      ⌜f = Build_frame (ws_l ++ ws_wl) i⌝ ∗
      (* TODO: not right, throws out sizes with (map fst L) *)
      ▷ interp_values_phys rs (map fst L) ws_l ∗
      iris_logrel.interp_val WL (immV ws_wl)
    )%I.

  Program Definition interp_expr_0 (rs : relations) :
    leibnizO (list R.Typ) -n>
    leibnizO R.Function_Ctx -n>
    leibnizO R.Local_Ctx -n>
    leibnizO wlocal_ctx -n>
    leibnizO instance -n>
    ER :=
    λne τs C L WL i '(lh, e), (
      WP e {{ v, ∃ ws, ⌜v = immV ws⌝ ∗
                       interp_values_phys rs τs ws ∗
                       ∃ f, relations_frame rs L WL i f }}
    )%I.

  Definition rels_0 (rs : relations) : relations :=
    (interp_value_phys_0 rs, interp_frame_0 rs, interp_expr_0 rs).

  Instance Contractive_rels_0 : Contractive rels_0.
  Admitted.

  Definition rels : relations := fixpoint rels_0.

  Notation interp_value_phys := (relations_value_phys rels).
  Notation interp_frame := (relations_frame rels).
  Notation interp_expr := (relations_expr rels).

  Lemma rels_eq : rels ≡ rels_0 rels.
  Proof. apply fixpoint_unfold. Qed.

  Lemma interp_value_phys_eq τs vs :
    interp_value_phys τs vs ⊣⊢ interp_value_phys_0 rels τs vs.
  Proof.
    do 2 f_equiv.
    transitivity (rels_0 rels).1.1.
    - apply rels_eq.
    - reflexivity.
  Qed.

  Opaque relations_value_phys.

  Lemma interp_expr_eq τs F L WL i e :
    interp_expr τs F L WL i e ⊣⊢ interp_expr_0 rels τs F L WL i e.
  Proof.
    do 6 f_equiv.
    transitivity (snd (rels_0 rels)).
    - apply rels_eq.
    - reflexivity.
  Qed.

  Opaque relations_expr.

  Lemma interp_frame_eq L WL i f :
    interp_frame L WL i f ⊣⊢ interp_frame_0 rels L WL i f.
  Proof.
    do 4 f_equiv.
    transitivity (rels_0 rels).1.2.
    - apply rels_eq.
    - reflexivity.
  Qed.

  Opaque relations_frame.

  Definition interp_val (τs : list R.Typ) : VR :=
    λne v, (⌜v = trapV⌝ ∨ ∃ ws, ⌜v = immV ws⌝ ∗ interp_values_phys rels τs ws)%I.

  Definition interp_inst (M : R.Module_Ctx) (inst : instance) : iProp Σ :=
    True.

  Definition interp_ctx (L L' : R.Local_Ctx) (F : R.Function_Ctx) (inst : instance) (lh : lholed) :
    iProp Σ :=
    True.

  Definition semantic_typing
    (M : R.Module_Ctx)
    (F : R.Function_Ctx)
    (L : R.Local_Ctx)
    (WL : wlocal_ctx)
    (es : list administrative_instruction)
    (τa : R.ArrowType)
    (L' : R.Local_Ctx) :
    iProp Σ :=
    let '(R.Arrow τs1 τs2) := τa in
    ∀ inst lh,
    interp_inst M inst ∗ interp_ctx L L' F inst lh -∗
    ∀ f vs,
    interp_val τs1 vs ∗ interp_frame L WL inst f -∗
    interp_expr τs2 F L' WL inst (lh, of_val vs ++ es).

End Relations.
