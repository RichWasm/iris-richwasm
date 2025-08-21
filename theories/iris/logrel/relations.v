From mathcomp Require Import eqtype seq.

Require Import iris.proofmode.tactics.

From RichWasm Require subst term typing.
From RichWasm.compiler Require Import codegen types util.
From RichWasm.iris Require Import gc num_reprs util.
Require Import RichWasm.iris.logrel.util.
Require Import RichWasm.util.debruijn.
Require Import RichWasm.iris.language.lenient_wp.
Require Import RichWasm.iris.language.logpred.
Require Wasm.iris.logrel.iris_logrel.
Import uPred.

Module R. Include RichWasm.subst <+ RichWasm.term <+ RichWasm.typing. End R.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Relations.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!rwasm_gcG Σ}.

  Variable sr : store_runtime.

  Definition ns_func (x : N) : namespace := nroot .@ "rwf" .@ x.
  Definition ns_ref (x : N) : namespace := nroot .@ "rwr" .@ x.

  Notation VR := (leibnizO val -n> iPropO Σ).
  Notation WsR := (leibnizO (list value) -n> iPropO Σ).
  Notation VVsR := (leibnizO vblock -n> iPropO Σ).
  Notation FR := (leibnizO frame -n> iPropO Σ).
  Notation HVR_mm := (leibnizO bytes -n> iPropO Σ).
  Notation HVR_gc := (leibnizO vblock -n> iPropO Σ).
  Notation ClR := (leibnizO function_closure -n> iPropO Σ).
  Notation ER := (leibnizO (lholed * list administrative_instruction) -n> iPropO Σ).

  Implicit Type L : leibnizO R.Local_Ctx.
  Implicit Type WL : leibnizO wlocal_ctx.

  Implicit Type v : leibnizO val.
  Implicit Type ws : leibnizO (list value).
  Implicit Type vvs : leibnizO vblock.
  Implicit Type bs : leibnizO bytes.
  Implicit Type f : leibnizO frame.
  Implicit Type cl : leibnizO function_closure.
  Implicit Type lh_es : leibnizO (lholed * list administrative_instruction).
  Implicit Type i : leibnizO instance.

  Implicit Type τ : leibnizO R.Typ.
  Implicit Type τs : leibnizO (list R.Typ).
  Implicit Type τf : leibnizO R.FunType.

  Definition relations : Type :=
    (* Physical Value *)
    (leibnizO R.Typ -n> WsR) *
    (* Virtual Value *)
    (leibnizO R.Typ -n> VVsR) *
    (* Frame *)
    (leibnizO R.Local_Ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FR) *
    (* Expression *)
    (leibnizO (list R.Typ) -n> leibnizO R.Function_Ctx -n> leibnizO R.Local_Ctx -n>
       leibnizO wlocal_ctx -n> leibnizO instance -n> ER).

  Definition relations_value_phys (rs : relations) : leibnizO R.Typ -n> WsR :=
    rs.1.1.1.

  Definition relations_value_virt (rs : relations) : leibnizO R.Typ -n> VVsR :=
    rs.1.1.2.

  Definition relations_frame (rs : relations) :
    leibnizO R.Local_Ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FR :=
    rs.1.2.

  Definition relations_expr (rs : relations) :
    leibnizO (list R.Typ) -n> leibnizO R.Function_Ctx -n> leibnizO R.Local_Ctx -n>
      leibnizO wlocal_ctx -n> leibnizO instance -n> ER :=
    rs.2.

  Definition interp_heap_value_mm_variant (rs : relations) (τs : list R.Typ) : HVR_mm :=
    λne bs,
      (∃ bs_tag bs_data,
       ⌜bs = bs_tag ++ bs_data⌝ ∗
       ∃ tag tag_i32 τ,
       ⌜wasm_deserialise bs_tag T_i32 = VAL_int32 tag_i32⌝ ∗
       ⌜nat_repr tag tag_i32⌝ ∗
       ⌜nth_error τs tag = Some τ⌝ ∗
       ⌜length bs_data = (4 * type_words τ)%nat⌝ ∗
       relations_value_phys rs τ (deserialize_values bs_data τ))%I.

  Definition interp_heap_value_mm_struct (rs : relations) (fs : list (R.Typ * R.Size)) : HVR_mm :=
    λne bs,
      (∃ bss,
       ⌜bs = flatten bss⌝ ∗
       [∗ list] '(τ, sz); bs' ∈ fs; bss,
       ⌜length bs' = (4 * R.interp_size (const 0) sz)%nat⌝ ∗
       relations_value_phys rs τ (deserialize_values bs' τ))%I.

  Definition interp_heap_value_mm_array (rs : relations) (τ : R.Typ) : HVR_mm :=
    λne bs,
      (∃ bs_len bs_elems,
       ⌜bs = bs_len ++ flatten bs_elems⌝ ∗
       ∃ len len_i32,
       ⌜wasm_deserialise bs_len T_i32 = VAL_int32 len_i32⌝ ∗
       ⌜nat_repr len len_i32⌝ ∗
       ⌜len = length bs_elems⌝ ∗
       [∗ list] bs_elem ∈ bs_elems,
       ⌜length bs_elem = (4 * type_words τ)%nat⌝ ∗
       relations_value_phys rs τ (deserialize_values bs_elem τ))%I.

  Definition interp_heap_value_mm_ex (rs : relations) (sz : R.Size) (q : R.Qual) (τ : R.Typ) :
    HVR_mm :=
    λne bs, False%I.

  Definition interp_heap_value_mm (rs : relations) (Ψ : R.HeapType) : HVR_mm :=
    match Ψ with
    | R.VariantType τs => interp_heap_value_mm_variant rs τs
    | R.StructType fs => interp_heap_value_mm_struct rs fs
    | R.ArrayType τ => interp_heap_value_mm_array rs τ
    | R.Ex sz q τ => interp_heap_value_mm_ex rs sz q τ
    end.

  Definition interp_heap_value_gc_variant (rs : relations) (τs : list R.Typ) : HVR_gc :=
    λne vvs,
      (∃ n vvs' τ,
       ⌜vvs = intVV n :: vvs'⌝ ∗
       ⌜nth_error τs (Z.to_nat n) = Some τ⌝ ∗
       relations_value_virt rs τ vvs')%I.

  Definition interp_heap_value_gc_struct (rs : relations) (fs : list (R.Typ * R.Size)) : HVR_gc :=
    λne vvs,
      (∃ vvss,
       ⌜vvs = flatten vvss⌝ ∗
       [∗ list] '(τ, sz); vvs' ∈ fs; vvss,
       ⌜length vvs' = R.interp_size (const 0) sz⌝ ∗
       relations_value_virt rs τ vvs')%I.

  Definition interp_heap_value_gc_array (rs : relations) (τ : R.Typ) : HVR_gc :=
    λne vvs,
      (∃ n vvs_elems,
       ⌜vvs = intVV n :: flatten vvs_elems⌝ ∗
       ⌜n = length vvs_elems⌝ ∗
       [∗ list] vvs_elem ∈ vvs_elems,
       ⌜length vvs_elem = type_words τ⌝ ∗
       relations_value_virt rs τ vvs_elem)%I.

  Definition interp_heap_value_gc_ex (rs : relations) (sz : R.Size) (q : R.Qual) (τ : R.Typ) :
    HVR_gc :=
    λne vvs, False%I.

  Definition interp_heap_value_gc (rs : relations) (Ψ : R.HeapType) : HVR_gc :=
    match Ψ with
    | R.VariantType τs => interp_heap_value_gc_variant rs τs
    | R.StructType fs => interp_heap_value_gc_struct rs fs
    | R.ArrayType τ => interp_heap_value_gc_array rs τ
    | R.Ex sz q τ => interp_heap_value_gc_ex rs sz q τ
    end.

  Definition interp_closure (rs : relations) (τf : R.FunType) : ClR :=
    λne cl,
      let '(R.FunT _ (R.Arrow τ1 τ2)) := τf in
      match cl with
      | FC_func_native inst (Tf ts1 ts2) ts_local es => False%I
      | FC_func_host _ _ => False%I
      end.

  Definition interp_value_phys_coderef (rs : relations) (tf : R.FunType) : WsR :=
    λne ws,
      (∃ n,
       ⌜ws = [VAL_int32 n]⌝ ∗
       ∃ cl,
       ▷ interp_closure rs tf cl ∗
       let n' := Z.to_N (Wasm_int.Int32.unsigned n) in
       na_inv logrel_nais (ns_func n') (n' ↦[wf] cl))%I.

  Definition interp_value_phys_exloc (rs : relations) (τ : R.Typ) : WsR :=
    λne ws,
      (∃ ℓ c, ▷ relations_value_phys rs (subst_ext (ext R.SLoc (R.LocP ℓ c) id) τ) ws)%I.

  Definition interp_value_phys_ref_mm (rs : relations) (p : R.Ptr) (Ψ : R.HeapType) : WsR :=
    λne ws,
      (∃ bs l32,
       ⌜ws = [VAL_int32 l32]⌝ ∗
       ⌜ptr_repr (R.LocP p R.LinMem) l32⌝ ∗
       N.of_nat sr.(sr_mem_mm) ↦[wms][p] bs ∗
       (* TODO: Allocation token. *)
       interp_heap_value_mm rs Ψ bs)%I.

  Definition interp_value_phys_ref_gc (rs : relations) (p : R.Ptr) (Ψ : R.HeapType) : WsR :=
    λne ws,
      (∃ a',
       ⌜ws = [VAL_int32 a']⌝ ∗
       let a := Z.to_N (Wasm_int.Int32.unsigned a') in
       (* TODO: Why is the rhs of ↦root a nat instead of an N? *)
       a ↦root N.to_nat p ∗
       na_inv logrel_nais (ns_ref p)
         (∃ blk, N.to_nat p ↦vblk blk ∗ interp_heap_value_gc rs Ψ blk))%I.

  Definition interp_values_phys (rs : relations) (τs : list R.Typ) : WsR :=
    λne ws,
      (∃ wss,
       ⌜ws = flatten wss⌝ ∗
       [∗ list] τ; ws' ∈ τs; wss, relations_value_phys rs τ ws')%I.

  Definition interp_value_virt_coderef (rs : relations) (τf : R.FunType) : VVsR :=
    λne vvs,
      (∃ n,
       ⌜vvs = [intVV n]⌝ ∗
       ∃ cl,
       ▷ interp_closure rs τf cl ∗
       let n' := Z.to_N n in
       na_inv logrel_nais (ns_func n') (n' ↦[wf] cl))%I.

  Definition interp_value_virt_exloc (rs : relations) (τ : R.Typ) : VVsR :=
    λne vvs, False%I.

  Definition interp_value_virt_ref_mm (rs : relations) (p : R.Ptr) (Ψ : R.HeapType) : VVsR :=
    λne vvs,
      (∃ bs a,
       ⌜vvs = [ptrVV (mmVP a)]⌝ ∗
       ⌜ptr_repr' (R.LocP p R.LinMem) a⌝ ∗
       N.of_nat sr.(sr_mem_mm) ↦[wms][p] bs ∗
       (* TODO: Allocation token. *)
       interp_heap_value_mm rs Ψ bs)%I.

  Definition interp_value_virt_ref_gc (rs : relations) (p : R.Ptr) (Ψ : R.HeapType) : VVsR :=
    λne vvs,
      (∃ l,
       ⌜vvs = [ptrVV (gcVP l)]⌝ ∗
       na_inv logrel_nais (ns_ref p)
         (∃ blk, l ↦vblk blk ∗ interp_heap_value_gc rs Ψ blk))%I.

  Definition interp_values_virt (rs : relations) (τs : list R.Typ) : VVsR :=
    λne vvs,
      (∃ vvss,
       ⌜vvs = flatten vvss⌝ ∗
       [∗ list] τ; vvs' ∈ τs; vvss, relations_value_virt rs τ vvs')%I.

  Definition interp_value_phys_0 (rs : relations) : leibnizO R.Typ -n> WsR :=
    λne τ ws,
      match τ with
      | R.Num (R.Int _ R.i32) => ∃ n, ⌜ws = [VAL_int32 n]⌝
      | R.Num (R.Int _ R.i64) => ∃ n, ⌜ws = [VAL_int64 n]⌝
      | R.Num (R.Float R.f32) => ∃ n, ⌜ws = [VAL_float32 n]⌝
      | R.Num (R.Float R.f64) => ∃ n, ⌜ws = [VAL_float64 n]⌝
      | R.TVar _ => False
      | R.Unit => ⌜nilp ws⌝
      | R.ProdT τs => interp_values_phys rs τs ws
      | R.CoderefT tf => interp_value_phys_coderef rs tf ws
      | R.Rec _ _ => False
      | R.PtrT _ => False
      | R.ExLoc _ τ => interp_value_phys_exloc rs τ ws
      | R.OwnR _ => ⌜nilp ws⌝
      | R.CapT _ _ _ => ⌜nilp ws⌝
      | R.RefT _ (R.LocP p R.LinMem) Ψ => interp_value_phys_ref_mm rs p Ψ ws
      | R.RefT _ (R.LocP p R.GCMem) Ψ => interp_value_phys_ref_gc rs p Ψ ws
      | R.RefT _ (R.LocV _) _ => False
      end%I.

  Definition interp_value_virt_0 (rs : relations) : leibnizO R.Typ -n> VVsR :=
    λne τ vvs,
      match τ with
      | R.Num (R.Int _ R.i32) => ∃ n, ⌜vvs = [intVV n]⌝
      | R.Num (R.Int _ R.i64) => ∃ n1 n2, ⌜vvs = [intVV n1; intVV n2]⌝
      | R.Num (R.Float R.f32) => ∃ n, ⌜vvs = [intVV n]⌝
      | R.Num (R.Float R.f64) => ∃ n1 n2, ⌜vvs = [intVV n1; intVV n2]⌝
      | R.TVar _ => False
      | R.Unit => ⌜nilp vvs⌝
      | R.ProdT τs => interp_values_virt rs τs vvs
      | R.CoderefT tf => interp_value_virt_coderef rs tf vvs
      | R.Rec _ _ => False
      | R.PtrT _ => False
      | R.ExLoc _ τ => interp_value_virt_exloc rs τ vvs
      | R.OwnR _ => ⌜nilp vvs⌝
      | R.CapT _ _ _ => ⌜nilp vvs⌝
      | R.RefT _ (R.LocP p R.LinMem) Ψ => interp_value_virt_ref_mm rs p Ψ vvs
      | R.RefT _ (R.LocP p R.GCMem) Ψ => interp_value_virt_ref_gc rs p Ψ vvs
      | R.RefT _ (R.LocV _) _ => False
      end%I.

  Definition interp_frame_0 (rs : relations) :
    leibnizO R.Local_Ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FR :=
    λne L WL i f,
      (∃ ns ws szs,
       ⌜f = Build_frame (map VAL_int32 ns ++ ws) i⌝ ∗
       (* TODO: This should be the upper bound of the sizes, but we need the size context.
                Are size expressions open or closed here? *)
       ⌜mapM (eval_closed_size ∘ snd) L = Some szs⌝ ∗
       ([∗ list] τ; ns' ∈ map fst L; reshape szs ns,
          relations_value_phys rs τ (deserialize_values (flat_map serialise_i32 ns') τ)) ∗
       iris_logrel.interp_val WL (iris.immV ws))%I.

  Program Definition interp_expr_0 (rs : relations) :
    leibnizO (list R.Typ) -n> leibnizO R.Function_Ctx -n> leibnizO R.Local_Ctx -n>
      leibnizO wlocal_ctx -n> leibnizO instance -n> ER :=
    λne τs C L WL i lh_es,
      let '(lh, es) := lh_es in
      @lenient_wp _ wasmG0 NotStuck top es
        ({| lp_val := λ vs, interp_values_phys rs τs vs ∗ ↪[RUN];
           lp_trap := ⌜True⌝%I;
           lp_br := fun _ => ↪[RUN];
           lp_ret := fun _ => ↪[RUN];
           lp_host := fun _ _ _ _ => ↪[RUN];
           lp_fr := λ f, relations_frame rs L WL i f;
         |})%I.
  
  Definition rels_0 (rs : relations) : relations :=
    (interp_value_phys_0 rs, interp_value_virt_0 rs, interp_frame_0 rs, interp_expr_0 rs).

  Instance Contractive_rels_0 : Contractive rels_0.
  Admitted.

  Definition rels : relations := fixpoint rels_0.

  Definition interp_value_phys : leibnizO R.Typ -n> WsR := relations_value_phys rels.

  Definition interp_value_virt : leibnizO R.Typ -n> VVsR := relations_value_virt rels.

  Definition interp_frame :
    leibnizO R.Local_Ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FR :=
    relations_frame rels.

  Definition interp_expr :
    leibnizO (list R.Typ) -n> leibnizO R.Function_Ctx -n> leibnizO R.Local_Ctx -n>
      leibnizO wlocal_ctx -n> leibnizO instance -n> ER :=
    relations_expr rels.

  Lemma rels_eq : rels ≡ rels_0 rels.
  Proof. apply fixpoint_unfold. Qed.

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

  Opaque relations_value_phys.
  Opaque relations_value_virt.
  Opaque relations_frame.
  Opaque relations_expr.

  Definition interp_val (τs : list R.Typ) : VR :=
    λne v, (⌜v = trapV⌝ ∗ ↪[BAIL] ∨ 
            ∃ ws, ⌜v = immV ws⌝ ∗ interp_values_phys rels τs ws)%I.

  Definition interp_stack (τs : list R.Typ) : VR :=
    λne v, ((⌜v = trapV⌝ ∗ ↪[BAIL]) ∨ 
            (∃ ws, ⌜v = immV ws⌝ ∗ interp_values_phys rels τs ws ∗ ↪[RUN]))%I.

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
    interp_stack τs1 vs ∗ interp_frame L WL inst f ∗ ↪[frame] f -∗
    interp_expr τs2 F L' WL inst (lh, of_val vs ++ es).

End Relations.
