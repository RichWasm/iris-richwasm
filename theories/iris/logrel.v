From stdpp Require Import base fin_maps.
From RWasm Require Import typing term subst debruijn num_repr autowp compile iris.util.
Module RT := RWasm.term.
Module T := RWasm.typing.

Unset Universe Checking.

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
  match compile_typ τ with
  | Some vt => wasm_deser_list bs vt
  | None => []
  end.

Class Read := {
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
          N.of_nat LIN_MEM ↦[wms][ℓ] bs ∗
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
      interp_inst S C inst ∗
      interp_ctx L L' F inst lh -∗
      ∀ f vs,
        interp_val τs1 vs ∗ 
        (* frame points to F ∗ *)
        interp_frame L WL inst f -∗
        interp_expr τs2 F L' WL inst (lh, (of_val vs ++ es)))%I.

Require Import RWasm.compile.

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

Lemma sniff_tuple Ss S C F L WL vs wes τs :
  compile_value (Prod vs) = Some wes ->
  SplitStoreTypings Ss S ->
  Forall3 (fun S' 'v t =>
             forall ve, compile_value v = Some ve ->
             ⊢ semantic_typing S' C F L [] (to_e_list (map BI_const ve)) (rwasm.Arrow [] [t]) L)
          Ss vs τs ->
  ⊢ semantic_typing S C F L WL (to_e_list (map BI_const wes)) (Arrow [] [ProdT τs]) L.
Proof.
  intros Hcomp HSs Hsem.
  iIntros.
  iIntros (inst lh) "[Hinst Hctx] %f %vs' (Hval & Hframe)".
  rewrite interp_expr_eq.
  unfold interp_expr_0.
  cbn.
  iDestruct "Hval" as "[-> | (%ws & -> & %wss & -> & Hvalue)]".
  - admit.
  - cbn.
    rewrite big_sepL2_nil_inv_l. iDestruct "Hvalue" as "->".
    cbn.
    unfold compile_value in Hcomp. apply fmap_Some in Hcomp.
    destruct Hcomp as [wess [Hcomp ->]].
    fold compile_value in Hcomp.
    apply mapM_Some in Hcomp.
    iApply wp_value.
    + instantiate (1 := immV (flatten wess)). unfold IntoVal. cbn.
      unfold v_to_e_list. unfold to_e_list.
      rewrite !seq_map_map. by rewrite map_map.
    + iFrame.
      iExists (flatten wess). iSplitR; first done.
      iExists [flatten wess]. iSplitR.
      { cbn. by rewrite cats0. }
      cbn. iFrame.
      rewrite interp_value_eq. cbn.
      iExists wess. iSplitR; first done.
      apply (Forall2_Forall3_mp2 _ _ _ _ _ _ Hcomp) in Hsem.
      clear Hcomp.
      cbn beta in Hsem.
      assert (Hwt: length wess = length τs).
      {
        rewrite -(Forall3_length_lm _ _ _ _ Hsem).
        rewrite -(Forall3_length_lr _ _ _ _ Hsem).
        done.
      }
      rewrite big_sepL2_flip.
      rewrite big_sepL2_alt.
      iSplit; [done|].
      apply Forall3_to_zip23 in Hsem.
      replace wess with (fst <$> (zip wess τs))
        by (rewrite fst_zip; [done | lia]).
      unfold semantic_typing in  Hsem.
      eapply Forall2_impl in Hsem.
      instantiate (1 := λ S '(wes, τ), ⊢ (interp_inst S C inst ∗ interp_ctx L L F inst (LH_base [] []) -∗ ?[Q'])%I) in Hsem.
      2:intros S0 [wes τ] P; iApply P.
      admit.

Admitted.

Theorem fundamental_property_value S C F L v vs τ ta :
  HasTypeValue S F v τ ->
  ta = rwasm.Arrow [] [τ] ->
  compile_value v = Some vs ->
  ⊢ semantic_typing S C F L [] (to_e_list (map BI_const vs)) ta L.
Proof.
  intros Htyp Hta Hcomp.
  subst ta.
  generalize dependent vs.
  induction Htyp using HasTypeValue_ind'.
  - admit.
  - admit.
  - intros vs' Hcomp.
    apply fmap_Some in Hcomp.
    fold compile_value in Hcomp.
    destruct Hcomp as [vs'' [Hcomp ->]].
    apply sniff_tuple with (Ss := Ss) (vs := vs).
    3: assumption.
    + cbn. by rewrite Hcomp.
    + assumption.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Theorem fundamental_property S C F L e es tf L' :
  HasTypeInstr S C F L e tf L' ->
  compile_instr [] 0 GC_MEM LIN_MEM e = Some es ->
  ⊢ semantic_typing S C F L [] (to_e_list es) tf L'.
Proof.
  intros Htyp Hcomp.
  induction Htyp.
  - cbn in Hcomp. apply fmap_Some in Hcomp.
    destruct Hcomp as [vs' [Hcomp ->]].
    by apply fundamental_property_value with (v := v) (τ := t).
  - admit.
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
  clear H GC_MEM LIN_MEM mems_diff.
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
  clear H GC_MEM LIN_MEM mems_diff.
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
  clear GC_MEM LIN_MEM mems_diff.
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
    by rewrite Z.divide_Zpos in H0.
  - destruct Hrepr as [Hbdd Hconv].
    destruct l32; cbn in *.
    rewrite Hl32 in Hconv.
    lia.
Qed.

Lemma lin_ptr_parity ℓ l32:
  ptr_repr (LocP ℓ LinMem) l32 ->
  wasm_bool (Wasm_int.Int32.eq Wasm_int.Int32.zero (Wasm_int.Int32.iand l32 (Wasm_int.Int32.repr 1))) <> Wasm_int.int_zero i32m.
Proof.
  clear GC_MEM LIN_MEM mems_diff.
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
    by rewrite Z.divide_Zpos in H0.
  - destruct l32; cbn in *; lia.
Qed.

Check wp_if_true.
Definition gc_bit_set_spec E ref_tmp ins outs gc_branch lin_branch ψ f ℓ l32 :
  f.(f_locs) !! ref_tmp = Some (VAL_int32 l32) ->
  ptr_repr (LocP ℓ GCMem) l32 ->
  ⊢ ↪[frame] f -∗
    ▷(↪[frame] f -∗ WP [AI_basic (BI_block (Tf ins outs) gc_branch)] @ E {{ w, ψ w }}) -∗
    WP to_e_list (if_gc_bit_set ref_tmp ins outs gc_branch lin_branch) @ E {{ w, ψ w }}.
Proof.
  intros Href Hrepr.
  iIntros "Hfr Hbranch".
  Print next_wp.
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

Definition gc_bit_not_set_spec E ref_tmp ins outs gc_branch lin_branch ψ f ℓ l32 :
  f.(f_locs) !! ref_tmp = Some (VAL_int32 l32) ->
  ptr_repr (LocP ℓ LinMem) l32 ->
  ⊢ ↪[frame] f -∗
    ▷(↪[frame] f -∗ WP [AI_basic (BI_block (Tf ins outs) lin_branch)] @ E {{ w, ψ w }}) -∗
    WP to_e_list (if_gc_bit_set ref_tmp ins outs gc_branch lin_branch) @ E {{ w, ψ w }}.
Proof.
  intros Href Hrepr.
  iIntros "Hfr Hφ".
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
Search Memdata.encode_int.

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
  clear GC_MEM LIN_MEM mems_diff.
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

Lemma sniff_test S C F L cap l ℓ sgn τ eff es :
  l = LocP ℓ LinMem ->
  τ = RefT cap l (StructType [(Num (Int sgn RT.i32), SizeConst 1)]) ->
  eff = Arrow [τ] [τ; Num (Int sgn RT.i32)] ->
  compile_instr [] 0 0 1 (RT.StructGet eff 0) = Some es ->
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
  iIntros "%inst %lh [Hinst Hctx] %f %vs (Hval & Hfi)".
  rewrite interp_expr_eq.
  rewrite interp_frame_eq.
  unfold interp_val.
  iDestruct "Hval" as "[Htrap | (%vs' & %Hvs'eq & Hval)]".
  - admit. (* Should prove a lemma about traps being in interp_expr. *)
  - rewrite -> Hτ.
    cbn.
    (* First we collect the facts we need from the context. *)
    iDestruct "Hval" as "(%wss & %Hvs' & Hval)".
    iPoseProof (big_sepL2_length with "[$Hval]") as "%Hlens".
    destruct wss as [|ws wss]; cbn in Hlens; try discriminate Hlens.
    destruct wss; cbn in Hlens; try discriminate Hlens.
    clear Hlens.
    subst vs vs'.
    rewrite big_sepL2_singleton.
    setoid_rewrite interp_value_eq.
    iEval (cbn) in "Hval".
    iDestruct "Hval" as "(%bs & %l32 & -> & %Hrep & Hbs & %bss & %bs_rest & %Hconcat & Hfields)".
    pose proof Hrep as Hrep'.
    destruct Hrep' as [Hlrep Hlalign].
    simpl flatten.
    simpl of_val.
    rewrite <- Hcomp.
    simpl to_e_list. simpl app.
    iPoseProof (big_sepL2_length with "[$Hfields]") as "%Hflens".
    destruct_length_eqn Hflens.
    rewrite big_sepL2_singleton.
    setoid_rewrite interp_value_eq.
    iEval (cbn) in "Hfields".
    iDestruct "Hfields" as "(%sz' & %Hsz' & %Hlenbs & %i & %Hi)".
    inversion Hsz'; subst sz'.
    (* Now we analyze the behavior of the compiled code. *)
    iAssert (⌜True⌝)%I as "HΦ". (* work around a bug in next_wp *)
    { done. }
    iDestruct "Hfi" as "[Hfr Hfi]".

Tactic Notation "seq_sz" constr(Hs) constr(n) constr(m) :=
  autowp.wp_chomp n; iApply
   (wp_seq _ _ _ (λ w, ((∃ vs, ⌜w = immV vs⌝ ∗ ⌜length vs = m⌝ ∗ _ vs) ∗  ↪[frame]_)%I));
   iSplitR
  ;
  first 
  last.

Tactic Notation "next_wp'" constr(Hs) :=
  match get_shp with
  | Shape _ _ _ 0 => fail
  | Shape 0 ?use ?outs (Datatypes.S ?rest) =>
      seq_sz Hs use outs; [ iRename select ( ↪[frame]_) into "Hfr"; iSplitR Hs |  ];
       [  | iIntros ( w ) "((%vs & -> & % & ?) & Hfr)"; destruct_length_eqn' |  ]
  | Shape ?to_skip ?use ?outs 0 =>
      skip_sz to_skip
  | Shape ?to_skip ?use ?outs (Datatypes.S ?rest) =>
      seq_sz Hs use outs; [ iRename select ( ↪[frame]_) into "Hfr"; iSplitR Hs |  ];
       [  | iIntros ( w ) "((%vs & -> & % & ?) & Hfr)"; destruct_length_eqn' |  ] ; first 
  skip_sz to_skip
  | Unknown => fail
  end.

    next_wp' "HΦ Hinst Hctx Hfi Hbs".
    {
      iApply (wp_tee_local with "[$Hfr]").
      iIntros "!> Hfr".
      let e := get_shp in idtac e.
      next_wp.
      {
        iApply (wp_wand with "[Hfr]").
        - iApply (wp_set_local with "[] [$Hfr]").
          + admit. (* need frame relation to say there's a slot *)
          + fill_imm_pred.
        - iIntros (v) "(-> & Hfr)".
          iFrame.
          iExists _.
          iSplit; [|iSplit]; try done.
          fill_vals_pred.
      }
      - iIntros "!> ((%vs & %contra & _) & _)". discriminate.
    }
    cbn beta.
    iDestruct select (_ ∗ _)%I as "(%Hv & Hptr)".
    inversion Hv. subst v.
    skip_sz 1.
    iApply (gc_bit_not_set_spec with "[$Hfr]");
      [by rewrite set_nth_read | eauto |].
    {
      iIntros "!> Hfr".
      rewrite -(app_nil_l [AI_basic _]).
      iApply (wp_block with "[$Hfr]") => //.
      iIntros "!> Hfr".
      iApply wp_wasm_empty_ctx.
      iApply wp_label_push_nil.
      iApply wp_ctx_bind; [done|].
      iClear "Hptr".
      next_wp' "Hinst Hctx Hfi Hbs".
      { 
        iApply wp_get_local; eauto.
        by rewrite set_nth_read.
        iIntros "!>".
        iExists _.
        iSplit; auto.
        iSplit; auto.
        fill_vals_pred.
      }
      cbn beta; iDestruct select (_ ∗ _)%I as "(%Hv' & _)".
      inversion Hv'; subst v; clear Hv'.
      next_wp' "Hinst Hctx Hfi".
      { 
        iApply (wp_binop with "[$Hfr] [Hbs]").
        eauto.
        iIntros "!>". iExists _.
        iSplit; auto.
        iSplit; auto.
        fill_vals_pred.
      }
      cbn beta; iDestruct select (_ ∗ _)%I as "(%Hv' & Hbs)".
      inversion Hv'; subst v; clear Hv'.
      assert (i = Wasm_int.Int32.repr (Memdata.decode_int (take 4 b))).
      {
        by inversion Hi.
      }

      assert (Hℓ: ℓ = (Wasm_int.N_of_uint i32m (Wasm_int.Int32.iadd l32 (Wasm_int.Int32.repr 0%nat)) + 0)%N).
      {
        rewrite N.add_0_r.
        unfold Wasm_int.Int32.iadd; rewrite Wasm_int.Int32.add_zero.
        erewrite <- N_repr_uint; done.
      }
      subst bs.
      replace (flatten [b]) with b by (cbn; by rewrite seq.cats0).
      rewrite wms_app; [|eauto].
      iDestruct "Hbs" as "[Hb Hbs]".
      destruct b as [| b0 [| b1 [| b2 [| b3 [| b4]]]]]; cbn in Hlenbs; try lia.
      assert (Hbits: bits (VAL_int32 i) = [b0; b1; b2; b3]).
      {
        unfold bits.
        subst.
        unfold serialise_i32.
        rewrite Wasm_int.Int32.unsigned_repr_eq.
        rewrite OrdersEx.Z_as_OT.mod_small.
        simpl take.
        by rewrite encode_decode_int.
        simpl take.
        unfold Memdata.decode_int.
        apply Memdata.int_of_bytes_range.
      }
      simpl flatten.
      iEval (rewrite Hℓ -Hbits) in "Hb".
      iApply (wp_wand with "[Hb Hfr]").
      {
        iApply wp_load; try iFrame.
        - done.
        - cbn.
          admit. (* need interp_frame to say where LIN_MEM and GC_MEM are! or interp_inst? *)
        - fill_imm_pred.
      }
      cbn beta.
      iIntros (v) "[[-> Hb] Hfr]".
      iEval (rewrite -Hℓ) in "Hb".
      simpl of_val.
      unfold wp_wasm_ctx.
      iIntros (LI) "%Hfill".
      cbn in Hfill.
      move/eqseqP in Hfill.
      subst LI.
      iApply (wp_wand with "[Hfr]").
      iApply (wp_label_value with "[$Hfr]"); eauto.
      fill_imm_pred.
      iIntros (v) "[-> Hfr]".
      iExists _.
      iCombine "Hb" "Hbs" as "Hbs".
      iEval (rewrite Hbits) in "Hbs".
      rewrite -wms_app.
      iSplit; auto.
      {
        iSplitR "Hfr Hfi".
        - iExists [[VAL_int32 l32]; [VAL_int32 i]].
          iSplit =>//.
          rewrite !big_sepL2_cons.
          iSplitL; [| by eauto].
          iEval (cbn).
          iExists _.
          iExists _.
          iFrame.
          iSplit; eauto.
          iSplit; eauto.
          iExists _. iExists _. iSplit;
            [iPureIntro; f_equal; by instantiate (1:= [[b0;b1;b2;b3]])|].
          cbn.
          iFrame.
          iExists _.
          iSplit; [by eauto|].
          iSplit; [done|].
          rewrite Hi interp_value_eq; eauto.
        - iDestruct "Hfi" as "(%vs & %ws & -> & Hfi)".
          iExists _.
          rewrite interp_frame_eq.
          cbn.
          iFrame.
          iExists _. iExists _.
          iSplit; eauto.
          + iPureIntro.
            f_equal.
            admit. (* frame stuff *)
          + admit. (* more frame stuff *)
      }
      reflexivity.
      admit. (* trap condition *)
      admit. (* trap condition *)
    }
    admit. (* trap condition *)
    admit. (* trap condition *)
Admitted.

End logrel.
