From Stdlib Require Import List.
Import ListNotations.
Require Import Stdlib.Program.Basics.
Local Open Scope program_scope.

From stdpp Require Import list_misc list_monad.

From ExtLib.Data Require Import List PPair.
From ExtLib.Data.Monads Require Import EitherMonad StateMonad WriterMonad.
From ExtLib.Structures Require Import Monoid Monads.

From Wasm Require datatypes_properties.

From RichWasm Require Import syntax util.
From RichWasm.compiler Require Import prelude accum.

Module W := Wasm.datatypes_properties.

Definition wtype_ctx : Type := list W.function_type.

Definition wlocal_ctx : Type := list W.value_type.

Definition codegen : Type -> Type := accumT (wtype_ctx * wlocal_ctx) (writerT W.expr (sum error)).

Definition run_codegen {A : Type} (c : codegen A) (wt : wtype_ctx) (wl : wlocal_ctx) :
  error + A * wtype_ctx * wlocal_ctx * W.expr :=
  match runWriterT (runAccumT c (wt, wl)) with
  | inl e => inl e
  | inr x => inr (x.(pfst).1, x.(pfst).2.1, x.(pfst).2.2, x.(psnd))
  end.

Definition wtinsert (tf : W.function_type) : codegen W.typeidx :=
  '(wt, _) ← get;
  match list_find (W.function_type_eqb tf) wt with
  | Some (i, _) => ret (W.Mk_typeidx i)
  | None => acc ([tf], []);; ret (W.Mk_typeidx (length wt))
  end.

Definition wlalloc (fe : function_env) (t : W.value_type) : codegen W.localidx :=
  '(_, wl) ← get;
  acc ([], [t]);;
  ret (W.Mk_localidx (fe_wlocal_offset fe + length wl)).

Definition emit (e : W.basic_instruction) : codegen unit := tell [e].

Definition emit_all : W.expr -> codegen unit := tell.

Definition get_locals_w : list W.localidx -> codegen unit :=
  mapM_ (emit ∘ W.BI_get_local ∘ localimm).

Definition set_locals_w : list W.localidx -> codegen unit :=
  mapM_ (emit ∘ W.BI_set_local ∘ localimm) ∘ @rev _.

Definition get_globals_w : list W.globalidx -> codegen unit :=
  mapM_ (emit ∘ W.BI_get_global ∘ globalimm).

Definition set_globals_w : list W.globalidx -> codegen unit :=
  mapM_ (emit ∘ W.BI_set_global ∘ globalimm) ∘ @rev _.

Definition save_stack1 (fe : function_env) (ty : W.value_type) : codegen W.localidx :=
  i ← wlalloc fe ty;
  emit (W.BI_set_local (localimm i));;
  ret i.

Definition save_stack_w (fe : function_env) (tys : W.result_type) : codegen (list W.localidx) :=
  ixs ← mapM (wlalloc fe) tys;
  set_locals_w ixs;;
  ret ixs.

Definition save_stack (fe : function_env) (ιs : list primitive_rep) : codegen (list W.localidx) :=
  save_stack_w fe (map translate_prim_rep ιs).

Definition restore_stack : list W.localidx -> codegen unit := get_locals_w.

Definition capture {A : Type} (c : codegen A) : codegen (A * W.expr) :=
  censor (const []) (listen c).

Definition block_c {A : Type} (tf : W.function_type) (c : codegen A) : codegen A :=
  '(x, es) ← capture c;
  emit (W.BI_block tf es);;
  ret x.

Definition loop_c {A : Type} (tf : W.function_type) (c : codegen A) : codegen A :=
  '(x, es) ← capture c;
  emit (W.BI_loop tf es);;
  ret x.

Definition if_c {A B : Type} (tf : W.function_type) (thn : codegen A) (els : codegen B) :
  codegen (A * B) :=
  '(x1, es1) ← capture thn;
  '(x2, es2) ← capture els;
  emit (W.BI_if tf es1 es2);;
  ret (x1, x2).

Definition case_blocks (result : W.result_type) (cases : list (nat -> codegen unit)) : codegen unit :=
  let fix go depth cases :=
    match cases with
    | [] =>
        block_c (W.Tf [W.T_i32] [])
          (block_c (W.Tf [] result) (emit (W.BI_br_table (seq 1 depth) 0));;
           emit W.BI_unreachable)
    | c :: cases' =>
        block_c (W.Tf [W.T_i32] result)
          (go (depth + 1) cases';;
           c depth;;
           emit (W.BI_br depth))
    end
  in
  go 0 cases.

Lemma runWriterT_sum_bind_dist {A B L E}
  (m : Monoid L)
  (c : writerT L (sum E) A)
  (f : A -> writerT L (sum E) B)
  (x : B)
  (l : L) :
  runWriterT (c ≫= f) = inr (ppair x l) ->
  exists x1 l1 l2,
  runWriterT c = inr (ppair x1 l1) /\
  runWriterT (f x1) = inr (ppair x l2) /\
  l = monoid_plus l1 l2.
Proof.
  intros H.
  unfold runWriterT, mbind, MBind_Monad, flip, bind, Monad_writerT, bind, EitherMonad.Monad_either in H.
  destruct c.
  cbn in H.
  destruct runWriterT; first congruence.
  exists p.(pfst).
  exists p.(psnd).
  destruct (f p.(pfst)).
  cbn in H.
  destruct runWriterT; first congruence.
  cbn.
  exists p0.(psnd).
  split; first reflexivity.
  split.
  - inversion H. reflexivity.
  - congruence.
Qed.

Lemma runWriterT_runAccumT_sum_bind_dist {E L S A B}
  (m : Monoid L)
  (mS : Monoid S)
  (mL : MonoidLaws m)
  (c : accumT S (writerT L (sum E)) A)
  (f : A -> accumT S (writerT L (sum E)) B)
  (s s' : S)
  (l : L)
  (x : B) :
  runWriterT (runAccumT (c ≫= f) s) = inr (ppair (x, s') l) ->
  exists x1 s1 s2 l1 l2,
  runWriterT (runAccumT c s) = inr (ppair (x1, s1) l1) /\
  runWriterT (runAccumT (f x1) (monoid_plus s s1)) = inr (ppair (x, s2) l2) /\
  s' = monoid_plus s1 s2 /\
  l = monoid_plus l1 l2.
Proof.
  intros H.
  unfold mbind, MBind_Monad, runStateT, flip, bind, Monad_stateT in H.
  apply runWriterT_sum_bind_dist in H.
  destruct H as ([x1 s1] & l1 & l2 & H1 & H2 & H3).
  apply runWriterT_sum_bind_dist in H2.
  destruct H2 as ([x2 s2] & l3 & l4 & ? & ? & ?).
  exists x1, s1, s2, l1, l2.
  split; first assumption.
  cbn in *.
  inversion H0; subst.
  split; [|split].
  - rewrite H.
    by rewrite monoid_runit.
  - auto.
  - auto.
Qed.

Lemma run_codegen_def {A} (c : codegen A) wt wt' wl wl' x es:
  run_codegen c wt wl = inr (x, wt', wl', es) <->
  runWriterT (runAccumT c (wt, wl)) = inr (ppair (x, (wt', wl')) es).
Proof.
  split.
  {
    intros H.
    unfold run_codegen in H.
    destruct (runWriterT (runAccumT c (wt, wl))); first congruence.
    inversion H.
    destruct p. destruct pfst. destruct p.
    reflexivity.
  }
  {
    intros H.
    unfold run_codegen.
    destruct (runWriterT (runAccumT c (wt, wl))); first congruence.
    inversion H.
    reflexivity.
  }
Qed.

Global Instance MonoidLaws_list {T} : MonoidLaws (@Monoid_list_app T).
Proof.
  split.
  - intros xs ys zs.
    symmetry. apply app_assoc.
  - intros xs.
    apply eq_refl.
  - intros xs.
    apply app_nil_r.
Qed.

Lemma run_codegen_bind_dist {A B} (c : codegen A) (f : A -> codegen B) wt wt' wl wl' es x :
  run_codegen (c ≫= f) wt wl = inr (x, wt', wl', es) ->
  exists x1 wt1 wt2 wl1 wl2 es1 es2,
    run_codegen c wt wl = inr (x1, wt1, wl1, es1) /\
      run_codegen (f x1) (wt ++ wt1) (wl ++ wl1) = inr (x, wt2, wl2, es2) /\
      wt' = wt1 ++ wt2 /\
      wl' = wl1 ++ wl2 /\
      es = es1 ++ es2.
Proof.
  intros H.
  rewrite run_codegen_def in H.
  apply runWriterT_runAccumT_sum_bind_dist in H; [|by typeclasses eauto].
  destruct H as (x1 & [wt1 wl1] & [wt2 wl2] & l1 & l2 & H1 & H2 & Hwl' & Hes).
  inversion Hwl'.
  exists x1, wt1, wt2, wl1, wl2, l1, l2.
  rewrite !run_codegen_def.
  repeat split; assumption.
Qed.

Lemma run_codegen_try_option_inr {A} (c: option A) e x wt wt' wl wl' es :
  run_codegen (try_option e c) wt wl = inr (x, wt', wl', es) ->
  c = Some x /\ wt' = [] /\ wl' = [] /\ es = [].
Proof.
  intros H.
  destruct c; cbn in H; [|congruence].
  inversion H; auto.
Qed.

Lemma run_codegen_capture {A} (c : codegen A) wt wt' wl wl' es es' x :
  run_codegen (capture c) wt wl = inr (x, es', wt', wl', es) ->
  run_codegen c wt wl = inr (x, wt', wl', es') /\ es = [].
Proof.
  intros H.
  unfold run_codegen.
  unfold capture, censor, pass, listen, MonadWriter_accumT in H.
  unfold listen in H.
  cbn in H.
  unfold pass in H.
  cbn in H.
  unfold run_codegen in *.
  cbn in H.
  destruct (runWriterT (runAccumT c (wt, wl))); first congruence.
  cbn in H.
  destruct p.
  cbn in *.
  destruct pfst.
  cbn in H.
  inversion H.
  subst a psnd wt' wl' es.
  clear H.
  destruct p.
  rewrite !app_nil_r.
  split; reflexivity.
Qed.

Lemma run_codegen_ret {A} (a : A) wt wt' wl wl' x es :
  run_codegen (mret a) wt wl = inr (x, wt', wl', es) ->
  x = a /\ wt' = [] /\ wl' = [] /\ es = [].
Proof.
  intros Hret.
  inversion Hret.
  auto.
Qed.

Lemma run_codegen_emit wt wl e x wt' wl' es' :
  run_codegen (emit e) wt wl = inr (x, wt', wl', es') ->
  x = tt /\
    wt' = [] /\
    wl' = [] /\
    es' = [e].
Proof.
  intros Hemit.
  inversion Hemit.
  auto.
Qed.

Lemma run_codegen_emit_all wt wl es x wt' wl' es' :
  run_codegen (emit_all es) wt wl = inr (x, wt', wl', es') ->
  x = tt /\
    wt' = [] /\
    wl' = [] /\
    es' = es.
Proof.
  intros Hemit.
  inversion Hemit.
  rewrite app_nil_r in *.
  auto.
Qed.

Ltac inv_cg_try_option Hrun :=
  let Heq1 := fresh "Heq_some" in
  let Heq2 := fresh "Heq_wt" in
  let Heq3 := fresh "Heq_wl" in
  let Heq4 := fresh "Heq_nil" in
  apply run_codegen_try_option_inr in Hrun;
  destruct Hrun as (Heq1 & Heq2 & Heq3 & Heq4);
  rewrite ?Heq1, ?Heq2, ?Heq3, ?Heq4 in *.

Ltac inv_cg_bind Hbind res wt1 wt2 wl1 wl2 es1 es2 Hcg1 Hcg2 :=
  let Hwteq := fresh "Hwt_app_eq" in
  let Hwleq := fresh "Hwl_app_eq" in
  let Heseq := fresh "Hes_app_eq" in
  apply run_codegen_bind_dist in Hbind;
  destruct Hbind as (res & wt1 & wt2 & wl1 & wl2 & es1 & es2 & Hcg1 & Hcg2 & Hwteq & Hwleq & Heseq);
  rewrite ?Heseq, ?Hwteq, ?Hwleq in *.

Ltac inv_cg_ret Hret :=
  let Hretval := fresh "Hretval" in
  let Hwt := fresh "Hwt" in
  let Hwl := fresh "Hwl" in
  let Hes := fresh "Hes" in
  apply run_codegen_ret in Hret;
  destruct Hret as (Hretval & Hwt & Hwl & Hes);
  rewrite ?Hretval, ?Hwt, ?Hwl, ?Hes in *.

Ltac inv_cg_emit Hemit :=
  let Hretval := fresh "Hretval" in
  let Hwt := fresh "Hwt" in
  let Hwl := fresh "Hwl" in
  let Hes := fresh "Hes" in
  apply run_codegen_emit in Hemit;
  destruct Hemit as (Hretval & Hwt & Hwl & Hes);
  rewrite ?Hretval, ?Hwt, ?Hwl, ?Hes in *.

Ltac inv_cg_emit_all Hemit :=
  let Hretval := fresh "Hretval" in
  let Hwt := fresh "Hwt" in
  let Hwl := fresh "Hwl" in
  let Hes := fresh "Hes" in
  apply run_codegen_emit_all in Hemit;
  destruct Hemit as (Hretval & Hwt & Hwl & Hes);
  rewrite ?Hretval, ?Hwt, ?Hwl, ?Hes in *.

Example emit_ret_test wt wl w x y z :
  run_codegen (emit W.BI_nop;;
               mret 7) wt wl = inr (w, x, y, z) ->
  w = 7 /\ x = [] /\ y = [] /\ z = [W.BI_nop].
Proof.
  intros Hrun.
  inv_cg_bind Hrun res wt1 wt2 wl1 wl2 es1 es2 Hemit Hret.
  inv_cg_emit Hemit.
  inv_cg_ret Hret.
  rewrite app_nil_r.
  repeat split; exact eq_refl.
Qed.
