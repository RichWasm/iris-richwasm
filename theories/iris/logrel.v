From mathcomp Require Import ssreflect ssrbool eqtype seq.

From stdpp Require Import base fin_maps option list.

From ExtLib.Structures Require Import Monads.
From ExtLib.Data.Monads Require Import StateMonad.

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

From RichWasm Require Import subst term typing.
From RichWasm.compiler Require Import codegen instrs modules types util.
From RichWasm.iris Require Import autowp num_reprs util.
From RichWasm.util Require Import debruijn stdpp_extlib.

Module RT := RichWasm.term.
Module T := RichWasm.typing.

Import uPred.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "1".

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

Ltac fill_vals_pred' vs :=
  instantiate ( 1 := (λ w, ⌜w = vs⌝ ∗ _)%I).

Ltac curry_hyps :=
  iRevert "∗";
  rewrite ? wand_curry.

Ltac fill_goal :=
  match goal with
  | |- environments.envs_entails _ ?E =>
      is_evar E;
      curry_hyps;
      try (iApply wand_refl; solve_constraints);
      instantiate (1:= ⌜True⌝%I); done
  end.

Ltac fill_vals_pred :=
  match goal with
  | |- environments.envs_entails _ (?g ?vs) =>
      fill_vals_pred' vs; iSplitR; [done | fill_goal]
  end.

Definition typ_size (t: value_type) : nat :=
  match t with
  | T_i32
  | T_f32 => 4
  | T_i64
  | T_f64 => 8
  end.

Fixpoint wasm_deser_list (bs: bytes) (vt: list value_type) : list value :=
  match vt with
  | vt :: vts =>
      wasm_deserialise (take (typ_size vt) bs) vt :: wasm_deser_list (drop (typ_size vt) bs) vts
  | [] => []
  end.

Definition read_value (τ: RT.Typ) (bs: bytes) : list value :=
  let vt := translate_type τ in
  wasm_deser_list bs vt.

Section logrel.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.

  Variable sr : store_runtime.

  Record stack := Stack { stack_values : list value }.
  Canonical Structure stackO := leibnizO stack.

  Notation VR := ((leibnizO val) -n> iPropO Σ).
  Notation WR := ((leibnizO value) -n> iPropO Σ).
  Notation WsR := (stackO -n> iPropO Σ).
  Notation FR := ((leibnizO frame) -n> iPropO Σ).
  Notation HR := ((leibnizO bytes) -n> iPropO Σ).
  Notation ClR := ((leibnizO function_closure) -n> iPropO Σ).

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
      ∃ bs_tag bs_data bs',
      ⌜bs = bs_tag ++ bs_data ++ bs'⌝ ∗
      let tagv := wasm_deserialise bs_tag T_i32 in
      ∃ tag tagi τ,
      ⌜tagv = VAL_int32 tagi⌝ ∗
      ⌜nat_repr tag tagi⌝ ∗
      ⌜τs !! tag = Some τ⌝ ∗
      let ws := read_value τ bs_data in
      rels_value rs τ (Stack ws)
    )%I.

  Program Definition interp_heap_value_struct : relationsO -n> leibnizO (list (RT.Typ * RT.Size)) -n> HR :=
    λne (rs : relationsO) (fs : leibnizO (list (RT.Typ * RT.Size))) (bs : leibnizO bytes), (
      ∃ (bss : list bytes) (bs_rest : bytes),
        ⌜bs = flatten bss ++ bs_rest⌝ ∗
        [∗ list] f;fbs ∈ fs;bss,
          let '(τ, sz) := f in
          let ws := read_value τ fbs in
          ∃ sz',
            ⌜sz = SizeConst sz'⌝ ∗
            ⌜length fbs = (4 * sz')%nat⌝ ∗
            rels_value rs τ (Stack ws)
    )%I.
  Next Obligation.
    solve_proper_prepare.
    solve_iprop_ne.
    apply big_sepL2_ne; intros.
    destruct y1.
    solve_iprop_ne.
    do 4 Morphisms.f_equiv.
    apply H.
  Qed.

  Program Definition interp_heap_value_array : relationsO -n> leibnizO RT.Typ -n> HR :=
    (λne (rs : relationsO) (τ : leibnizO RT.Typ) (bs : leibnizO bytes), ∃ bss bs_rest,
        (* needs size here *)
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
    λne (τs : leibnizO (list RT.Typ)) ws, (∃ wss,
      ⌜stack_values ws = flatten wss⌝ ∗
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

  Definition word_aligned (n: N) : Prop :=
    (4 | n)%N.

  Definition ptr_repr (l: RT.Loc) (i: i32) : Prop :=
    match l with
    | RT.LocV v => False
    | RT.LocP ℓ GCMem =>
        N_repr (ℓ+1) i /\ word_aligned ℓ
    | RT.LocP ℓ LinMem =>
        N_repr ℓ i /\ word_aligned ℓ
    end.

  Definition interp_value_0 (rs : relations) : leibnizO RT.Typ -n> WsR :=
    λne (τ: leibnizO RT.Typ), λne vs,
      let 'Stack vs := vs in
      match τ with
      | RT.Num (RT.Int _ RT.i32) => ⌜∃ i, vs = [VAL_int32 i]⌝
      | RT.Num (RT.Int _ RT.i64) => ⌜∃ i, vs = [VAL_int64 i]⌝
      | RT.Num (RT.Float RT.f32) => ⌜∃ f, vs = [VAL_float32 f]⌝
      | RT.Num (RT.Float RT.f64) => ⌜∃ f, vs = [VAL_float64 f]⌝
      | RT.TVar _ => ⌜False⌝
      | RT.Unit => ⌜False⌝
      | RT.ProdT τs => ∃ vss, ⌜vs = flatten vss⌝ ∗ [∗ list] τ;vs ∈ τs;vss, rels_value rs τ (Stack vs)
      | RT.CoderefT _ => ⌜False⌝
      | RT.Rec _ _ => ⌜False⌝
      | RT.PtrT _ => ⌜False⌝
      | RT.ExLoc _ _ => ⌜False⌝
      | RT.OwnR _ => ⌜False⌝
      | RT.CapT _ _ _ => ⌜False⌝
      | RT.RefT cap (LocP ℓ LinMem) ψ =>
          ∃ bs l32,
            ⌜vs = [VAL_int32 l32]⌝ ∗
            ⌜ptr_repr (LocP ℓ LinMem) l32⌝ ∗
            N.of_nat sr.(sr_mem_mm) ↦[wms][ℓ] bs ∗
            interp_heap_value rs ψ bs
      | RT.RefT _ _ _ => ⌜False⌝
      end%I.

  Definition interp_frame_0 (rs : relations) : leibnizO T.Local_Ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FR :=
    (λne (L: leibnizO T.Local_Ctx)
         (WL: leibnizO wlocal_ctx)
         (i: leibnizO instance)
         (f: leibnizO frame),
       ↪[frame] f ∗
       ∃ vs wvs: list value,
           ⌜f = Build_frame (vs ++ wvs) i⌝ ∗
           (* not right, throws out sizes with (map fst L) *)
           ▷ interp_values rs (map fst L) (Stack vs) ∗
           iris_logrel.interp_val WL (immV wvs))%I.

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
    T.Module_Ctx -> T.Function_Ctx ->
    T.Local_Ctx -> wlocal_ctx ->
    list administrative_instruction ->
    RT.ArrowType -> T.Local_Ctx ->
    iProp Σ :=
    (λ C F L WL es '(Arrow τs1 τs2) L',
      ∀ inst lh,
        interp_inst C inst ∗
        interp_ctx L L' F inst lh -∗
        ∀ f vs,
          interp_val τs1 vs ∗
          (* frame points to F ∗ *)
          interp_frame L WL inst f -∗
          interp_expr τs2 F L' WL inst (lh, (of_val vs ++ es)))%I.

  Lemma seq_map_map {A B} (f : A -> B) (l : list A) : seq.map f l = map f l.
  Admitted.

  Lemma Forall3_to_zip12
    {X Y Z: Type}
    (R: X -> Y -> Z -> Prop)
    xs ys zs :
    Forall3 R xs ys zs ->
    Forall2 (fun '(x, y) z => R x y z) (zip xs ys) zs.
  Admitted.

  Lemma Forall3_to_zip23
    {X Y Z: Type}
    (R: X -> Y -> Z -> Prop)
    xs ys zs :
    Forall3 R xs ys zs ->
    Forall2 (fun x '(y, z) => R x y z) xs (zip ys zs).
  Admitted.

  Lemma Forall3_from_zip12
    {X Y Z: Type}
    (R: X -> Y -> Z -> Prop)
    xs ys zs :
    length xs = length ys ->
    Forall2 (fun '(x, y) z => R x y z) (zip xs ys) zs ->
    Forall3 R xs ys zs.
  Proof.
  Admitted.

  Lemma Forall2_Forall3_mp2
    {A B C D : Type}
    (R : A -> B -> Prop)
    (P : C -> B -> D -> Prop)
    (l1 : list A)
    (l2 : list B)
    (l3 : list C)
    (l4 : list D) :
    Forall2 R l1 l2 ->
    Forall3 (fun x y z => forall a, R y a -> P x a z) l3 l1 l4 ->
    Forall3 (fun x a z => P x a z) l3 l2 l4.
  Proof.
  Admitted.

  Lemma compiler_wctx_mono M F es es' wl wl' x :
    run_codegen (compile_instrs M F es) wl = inr (x, wl', es') ->
    wl `prefix_of` wl'.
  Proof.
  Admitted.

  Lemma compat_struct_get M F L me fe ty cap l hty taus szs i es wl wl' :
    hty = StructType (combine taus szs) ->
    HasTypeInstr M F L
      (IStructGet (Arrow [RefT cap l hty] [RefT cap l hty; ty], LSig L L) i)
      (Arrow [RefT cap l hty] [RefT cap l hty; ty]) L ->
    run_codegen (compile_instr me fe
                   (IStructGet (Arrow [RefT cap l hty] [RefT cap l hty; ty], LSig L L) i)) wl =
    inr (tt, wl', es) ->
    ⊢ semantic_typing M F L [] (to_e_list es) (Arrow [RefT cap l hty] [RefT cap l hty; ty]) L.
  Proof.
    intros -> Htype Hcomp.
    iIntros "%inst %lh [Hinst Hctx] %f %vs [Hval Hfr]".
    rewrite interp_expr_eq.
    rewrite interp_frame_eq.
    iDestruct "Hval" as "[-> | (%vs' & -> & Hval)]".
    - (* trap *)
      admit.
    - iDestruct "Hval" as "(%vss & %Hvs' & Hval)".
      simpl in Hvs'. subst vs'.
      iPoseProof (big_sepL2_length with "[$Hval]") as "%Hlens".
      destruct vss as [|vs vss]; cbn in Hlens; first discriminate Hlens.
      destruct vss; cbn in Hlens; try discriminate Hlens. clear Hlens.
      rewrite big_sepL2_singleton.
      setoid_rewrite interp_value_eq.
      cbn.
      setoid_rewrite app_nil_r.
      destruct l; first by iExFalso.

      (* Break the compiler apart. *)
      unfold compile_instr, compile_struct_get in Hcomp.
      apply run_codegen_bind_dist in Hcomp.
      destruct Hcomp as (x1 & wl1 & es1 & es2 & Hcomp1 & Hcomp2 & Hes).
      cbn in Hcomp1.
      inversion Hcomp1.
      apply run_codegen_bind_dist in Hcomp2.
      destruct Hcomp2 as (field_ty & wl2 & es3 & es4 & Hcomp2 & Hcomp3 & Hes2).
      apply run_codegen_bind_dist in Hcomp3.
      destruct Hcomp3 as (offset & wl3 & es5 & es6 & Hcomp3 & Hcomp4 & Hes4).
      apply run_codegen_bind_dist in Hcomp4.
      destruct Hcomp4 as (x4 & wl4 & es7 & es8 & Hcomp4 & Hcomp5 & Hes6).
      cbn in Hcomp4.
      inversion Hcomp4.
      apply run_codegen_bind_dist in Hcomp5.
      destruct Hcomp5 as (x5 & wl5 & es9 & es10 & Hcomp5 & Hcomp6 & Hes8).
      apply run_codegen_bind_dist in Hcomp6.
      destruct Hcomp6 as (val & wl6 & es11 & es12 & Hcomp6 & Hcomp7 & Hes10).
      apply run_codegen_bind_dist in Hcomp7.
      destruct Hcomp7 as (x7 & wl7 & es13 & es14 & Hcomp7 & Hcomp8 & Hes12).
      cbn in Hcomp7.
      inversion Hcomp7.
      apply run_codegen_bind_dist in Hcomp8.
      destruct Hcomp8 as (x8 & wl8 & es15 & es16 & Hcomp8 & Hcomp9 & Hes14).
      subst x1 x4 x7 wl1 wl4 wl7 es es1 es2 es4 es6 es7 es8 es10 es12 es13 es14.
      destruct x5, x8 as [[] []].
      clear Hcomp4 Hcomp7.
      iSimpl.

      destruct m.
      + (* GC *)
        admit.
      + (* MM *)
        admit.
  Admitted.

  Theorem fundamental_property M F L L' me fe es es' tf wl wl' :
    HasTypeInstrs M F L es tf L' ->
    run_codegen (compile_instrs me fe es) wl = inr (tt, wl', es') ->
    ⊢ semantic_typing M F L wl' (to_e_list es') tf L'.
  Proof.
    intros Htyp Hcomp.
    generalize dependent es'.
    induction Htyp using HasTypeInstrs_mind with (P := fun C F L e ta L' _ =>
      forall es',
      run_codegen (compile_instr me fe e) wl = inr (tt, wl', es') ->
      ⊢ semantic_typing C F L [] (to_e_list es') ta L');
    intros es' Hcomp.
    - (* INumConst *)
      admit.
    - (* IUnit *)
      admit.
    - (* INum *)
      admit.
    - (* IUnreachable *)
      admit.
    - (* INop *)
      admit.
    - (* IDrop *)
      admit.
    - (* IBlock *)
      admit.
    - (* ILoop *)
      admit.
    - (* IIte *)
      admit.
    - (* IBr *)
      admit.
    - (* IBrIf *)
      admit.
    - (* IBrTable *)
      admit.
    - (* IRet *)
      admit.
    - (* IGetLocal *)
      admit.
    - (* ISetLocal *)
      admit.
    - (* IGetGlobal *)
      admit.
    - (* ISetGlobal *)
      admit.
    - (* ICoderef *)
      admit.
    - (* ICallIndirect *)
      admit.
    - (* ICall *)
      admit.
    - (* IRecFold *)
      admit.
    - (* IRecUnfold *)
      admit.
    - (* IGroup *)
      admit.
    - (* IUngroup *)
      admit.
    - (* ICapSplit *)
      admit.
    - (* ICapJoin *)
      admit.
    - (* IRefDemote *)
      admit.
    - (* IMemPack *)
      admit.
    - (* IMemUnpack *)
      admit.
    - (* IStructMalloc *)
      admit.
    - (* IStructFree *)
      admit.
    - (* IStructGet *)
      eapply compat_struct_get with (i := n).
      + reflexivity.
      + apply TStructGet; assumption.
      + exact Hcomp.
    - (* IStructSet *)
      admit.
    - (* IStructSwap *)
      admit.
    - (* IVariantMalloc *)
      admit.
    - (* IVariantCase - Unrestricted *)
      admit.
    - (* IVariantCase - Linear *)
      admit.
    - (* IArrayMalloc *)
      admit.
    - (* IArrayGet *)
      admit.
    - (* IArraySet *)
      admit.
    - (* IArrayFree *)
      admit.
    - (* IExistPack *)
      admit.
    - (* IExistUnpack - Unrestricted *)
      admit.
    - (* IExistUnpack - Linear *)
      admit.
    - (* IRefSplit *)
      admit.
    - (* IRefJoin *)
      admit.
    - (* Empty *)
      admit.
    - (* Cons *)
      admit.
  Admitted.

  Notation "{{{{ P }}}} es {{{{ v , Q }}}}" :=
    (□ ∀ Φ, P -∗ (∀ v : iris.val, Q -∗ Φ v) -∗ WP (es : iris.expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).

  Notation "{{{{ P }}}} es @ E {{{{ v , Q }}}}" :=
    (□ ∀ Φ, P -∗ (∀ v : iris.val, Q -∗ Φ v) -∗ (WP (es : iris.expr) @ NotStuck ; E {{ v, Φ v }}))%I (at level 50).

  Definition if_spec tf e_then e_else k φ ψ f : ⊢
    {{{{ ⌜k ≠ Wasm_int.int_zero i32m⌝ ∗ φ ∗ ↪[frame] f }}}}
      [AI_basic (BI_block tf e_then)]
    {{{{ w, ψ w }}}} -∗
    {{{{ ⌜k = Wasm_int.int_zero i32m⌝ ∗ φ ∗ ↪[frame] f }}}}
      [AI_basic (BI_block tf e_else)]
    {{{{ w, ψ w }}}} -∗
    {{{{ φ ∗ ↪[frame] f }}}}
      to_e_list [BI_const (VAL_int32 k); BI_if tf e_then e_else]
    {{{{ w, ψ w }}}}.
  Proof.
    iIntros "#Hthen #Helse !>" (Φ) "[Hφ Hfr] HΦ".
    destruct (k == Wasm_int.int_zero i32m) eqn:Heq; move/eqP in Heq.
    - iApply (wp_if_false with "[$Hfr]") => //.
      iIntros "!> Hfr".
      iApply ("Helse" with "[$Hfr $Hφ //] [$]").
    - iApply (wp_if_true with "[$Hfr]") => //.
      iIntros "!> Hfr".
      iApply ("Hthen" with "[$Hfr $Hφ //] [$]").
  Qed.

  Lemma wp_take_drop {E ϕ es} n:
    WP es @ E {{ w, ϕ w }} ⊣⊢
    WP (take n es) ++ (drop n es) @ E {{ w, ϕ w }}.
  Proof.
    by rewrite (take_drop n es).
  Qed.

  Lemma even_iff_land1:
    forall p: positive,
      ((2 | p) <-> Pos.land p 1 = 0%N)%positive.
  Proof using.
    clear Σ logrel_na_invs0 wasmG0 sr.
    induction p; (split; [intros Hdiv| intros Hand]).
    - destruct Hdiv as [p' Hp'].
      lia.
    - unfold Pos.land in Hand.
      lia.
    - reflexivity.
    - exists p.
      lia.
    - inversion Hdiv.
      lia.
    - inversion Hand.
  Qed.

  Lemma odd_iff_land1:
    forall p: positive,
      (¬(2 | p) <-> Pos.land p 1 = 1%N)%positive.
  Proof using.
    clear Σ logrel_na_invs0 wasmG0 sr.
    induction p; (split; [intros Hdiv| intros Hand]).
    - reflexivity.
    - intros [d Hdiv].
      lia.
    - exfalso; apply Hdiv.
      exists p; lia.
    - inversion Hand.
    - reflexivity.
    - intros [d Hdiv].
      lia.
  Qed.

  Lemma gc_ptr_parity ℓ l32:
    ptr_repr (LocP ℓ GCMem) l32 ->
    wasm_bool (Wasm_int.Int32.eq Wasm_int.Int32.zero (Wasm_int.Int32.iand l32 (Wasm_int.Int32.repr 1))) = Wasm_int.int_zero i32m.
  Proof.
    clear Σ logrel_na_invs0 wasmG0 sr.
    unfold ptr_repr, word_aligned, Wasm_int.Int32.iand, Wasm_int.Int32.and, Z.land.
    intros [Hrepr Hdiv].
    cbn.
    assert (¬ (2 | Wasm_int.Int32.unsigned l32))%Z.
    {
      destruct Hrepr as [Hbdd Hconv].
      destruct l32; cbn in *.
      rewrite -(Z2N.id intval); [| lia].
      rewrite -Hconv.
      rewrite N2Z.inj_add.
      cbn.
      intros [ℓ' Hev].
      destruct Hdiv; subst ℓ.
      lia.
    }
    destruct (Wasm_int.Int32.unsigned l32) as [|p32|q32] eqn:Hl32.
    - destruct Hrepr as [Hbdd Hconv].
      destruct l32; cbn in *.
      rewrite Hl32 in Hconv.
      lia.
    - replace (Pos.land p32 1) with 1%N; [done |].
      symmetry.
      eapply odd_iff_land1.
      by rewrite Z.divide_Zpos in H.
    - destruct Hrepr as [Hbdd Hconv].
      destruct l32; cbn in *.
      rewrite Hl32 in Hconv.
      lia.
  Qed.

  Lemma lin_ptr_parity ℓ l32:
    ptr_repr (LocP ℓ LinMem) l32 ->
    wasm_bool (Wasm_int.Int32.eq Wasm_int.Int32.zero (Wasm_int.Int32.iand l32 (Wasm_int.Int32.repr 1))) <> Wasm_int.int_zero i32m.
  Proof.
    clear Σ logrel_na_invs0 wasmG0 sr.
    unfold ptr_repr, word_aligned, Wasm_int.Int32.iand, Wasm_int.Int32.and, Z.land.
    intros [Hrepr Hdiv].
    cbn.
    assert (2 | Wasm_int.Int32.unsigned l32)%Z.
    {
      destruct Hrepr as [Hbdd Hconv].
      destruct l32; cbn in *.
      destruct Hdiv as [d Hdiv].
      exists (Z.of_N d * 2)%Z.
      lia.
    }
    destruct (Wasm_int.Int32.unsigned l32) as [|p32|q32] eqn:Hl32.
    - done.
    - replace (Pos.land p32 1) with 0%N; [done |].
      symmetry.
      eapply even_iff_land1.
      by rewrite Z.divide_Zpos in H.
    - destruct l32; cbn in *; lia.
  Qed.

  Definition gc_bit_set_spec E ref_tmp ins outs gc_branch lin_branch wl wl' es ψ f ℓ l32 :
    f.(f_locs) !! ref_tmp = Some (VAL_int32 l32) ->
    ptr_repr (LocP ℓ GCMem) l32 ->
    run_codegen (emit (BI_get_local ref_tmp);;
                 if_gc_bit (W.Tf ins outs)
                   (tell gc_branch)
                   (tell lin_branch);;
                 ret tt)
                wl = inr (wl', es) ->
    ⊢ ↪[frame] f -∗
      ▷ (↪[frame] f -∗ WP [AI_basic (BI_block (Tf ins outs) gc_branch)] @ E {{ w, ψ w }}) -∗
      WP to_e_list es @ E {{ w, ψ w }}.
  Proof.
    intros Href Hrepr Hcomp.
    iIntros "Hfr Hbranch".

    cbn in Hcomp.
    inversion Hcomp.
    subst wl' es.
    clear Hcomp.
    rewrite !app_nil_r.

    iAssert emp%I as "HΦ";[done|].
    next_wp.
    {
      iApply (wp_wand with "[Hfr]").
      {
        iApply (wp_get_local with "[] [$Hfr]"); eauto.
        fill_imm_pred.
      }
      iIntros (v) "(%Hv & Hfr)".
      iFrame.
      iExists [VAL_int32 l32].
      iSplit; [auto|].
      iSplit; [auto|].
      fill_vals_pred.
    }
    cbn.
    iDestruct select (_ ∗ _)%I as "(%Hv & Hφ)".
    inversion Hv; clear Hv; subst v.
    next_wp.
    {
      iApply (wp_binop with "[$Hfr]").
      eauto.
      iIntros "!>".
      iExists _.
      iSplit; [auto|].
      iSplit; [auto|].
      fill_vals_pred.
    }
    cbn.
    iDestruct select (_ ∗ _)%I as "(%Hv & Hφ)".
    inversion Hv; clear Hv; subst v.
    next_wp.
    {
      iApply (wp_testop_i32 with "[$Hfr]").
      eauto.
      iIntros "!>".
      iExists _.
      iSplit; [eauto|].
      iSplit; [eauto|].
      fill_vals_pred.
    }
    {
      cbn.
      iDestruct select (_ ∗ _)%I as "(%Hv & Hφ)".
      inversion Hv; subst v; clear Hv.
      apply gc_ptr_parity in Hrepr.
      rewrite Hrepr.
      iApply (wp_if_false with "[$Hfr]").
      auto.
      iIntros "!> Hfr".
      iApply ("Hφ" with "[$]").
    }
    - iIntros "((%vs & %Heq & _) & _)"; congruence.
    - iIntros "((%vs & %Heq & _) & _)"; congruence.
    - iIntros "((%vs & %Heq & _) & _)"; congruence.
  Qed.

  Lemma read_value_deserialize_i32 sgn b i:
    read_value (Num (Int sgn RT.i32)) b = [VAL_int32 i] ->
    wasm_deserialise b T_i32 = VAL_int32 i.
  Proof.
  Admitted.

  Definition gc_bit_not_set_spec E ref_tmp ins outs gc_branch lin_branch wl wl' es es' ψ f ℓ l32 :
    f.(f_locs) !! ref_tmp = Some (VAL_int32 l32) ->
    ptr_repr (LocP ℓ LinMem) l32 ->
    run_codegen (emit (BI_get_local ref_tmp);;
                 if_gc_bit (W.Tf ins outs)
                   (tell gc_branch)
                   (tell lin_branch);;
                 ret tt)
                wl = inr (wl', es) ->
    to_e_list es = es' ->
    ⊢ ↪[frame] f -∗
      ▷(↪[frame] f -∗ WP [AI_basic (BI_block (Tf ins outs) lin_branch)] @ E {{ w, ψ w }}) -∗
      WP es' @ E {{ w, ψ w }}.
  Proof.
    intros Href Hrepr Hcomp Hes.
    iIntros "Hfr Hφ".

    cbn in Hcomp.
    inversion Hcomp.
    subst wl' es.
    clear Hcomp.
    subst es'.
    rewrite !app_nil_r.

    cbn.
    iAssert emp%I as "HΦ"; [done|].
    next_wp.
    {
      iApply (wp_wand with "[Hfr]").
      {
        iApply (wp_get_local with "[] [$Hfr]"); eauto.
        fill_imm_pred.
      }
      iIntros (v) "(%Hv & Hfr)".
      iFrame.
      iExists [VAL_int32 l32].
      iSplit; [auto|].
      iSplit; [auto|].
      fill_vals_pred.
    }
    cbn.
    iDestruct select (_ ∗ _)%I as "(%Hv & Hφ)".
    inversion Hv; clear Hv; subst v.
    next_wp.
    {
      iApply (wp_binop with "[$Hfr]").
      eauto.
      iIntros "!>".
      iExists _.
      iSplit; [auto|].
      iSplit; [auto|].
      fill_vals_pred.
    }
    cbn.
    iDestruct select (_ ∗ _)%I as "(%Hv & Hφ)".
    inversion Hv; clear Hv; subst v.
    next_wp.
    {
      iApply (wp_testop_i32 with "[$Hfr]").
      eauto.
      iIntros "!>".
      iExists _.
      iSplit; [eauto|].
      iSplit; [eauto|].
      fill_vals_pred.
    }
    {
      cbn.
      iDestruct select (_ ∗ _)%I as "(%Hv & Hφ)".
      inversion Hv; subst v; clear Hv.
      pose proof (lin_ptr_parity _ _ Hrepr) as Hnz.
      iApply (wp_if_true with "[$Hfr]").
      apply Hnz.
      iIntros "!> Hfr".
      iApply ("Hφ" with "[$]").
    }
    - iIntros "((%vs & %Heq & _) & _)"; congruence.
    - iIntros "((%vs & %Heq & _) & _)"; congruence.
    - iIntros "((%vs & %Heq & _) & _)"; congruence.
  Qed.

  Lemma byte_div_repr b bs:
    Integers.Byte.repr (Integers.Byte.unsigned b + Memdata.int_of_bytes bs * 256) = b.
  Proof.
  Admitted.

  Lemma byte_div_skip b bs:
    ((Integers.Byte.unsigned b + Memdata.int_of_bytes bs * 256) `div` 256)%Z = Memdata.int_of_bytes bs.
  Proof.
  Admitted.

  Lemma encode_decode_int :
    forall sz bs,
      length bs = sz ->
      Memdata.encode_int sz (Memdata.decode_int bs) = bs.
  Proof.
    clear Σ logrel_na_invs0 wasmG0 sr.
    induction sz; intros bs Hlen.
    - destruct bs; simpl in Hlen; try lia.
      reflexivity.
    - destruct bs as [| b bs]; inversion Hlen.
      revert IHsz.
      unfold Memdata.encode_int, Memdata.decode_int.
      unfold Memdata.rev_if_be.
      Transparent Archi.big_endian.
      unfold Archi.big_endian.
      Opaque Archi.big_endian.
      intros IH.
      cbn.
      f_equal.
      + apply byte_div_repr.
      + rewrite <- IH by auto.
        rewrite byte_div_skip.
        congruence.
  Qed.

End logrel.
