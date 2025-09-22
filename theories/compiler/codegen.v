From Stdlib Require Import List.
Import ListNotations.
Require Import Stdlib.Program.Basics.
Local Open Scope program_scope.

Require Import stdpp.base.

From ExtLib.Data Require Import List.
From ExtLib.Data.Monads Require Import EitherMonad StateMonad WriterMonad.
From ExtLib.Structures Require Import Monoid Monads.

From Wasm Require datatypes.

Require Import RichWasm.compiler.util.
Require Import RichWasm.util.

Module W := Wasm.datatypes.

Notation wlocal_ctx := (list W.value_type) (only parsing).

Record codegen (A : Type) :=
  { uncodegen : stateT wlocal_ctx
                       (writerT (@Monoid_list_app W.basic_instruction)
                                (sum error))
                       A }.

Arguments Build_codegen {A} _.
Arguments uncodegen {A} _.

Existing Instance Monad_stateT.

Global Instance Monad_codegen : Monad codegen :=
  { ret := fun _ => Build_codegen ∘ ret;
    bind := fun _ _ c f => Build_codegen (uncodegen c ≫= uncodegen ∘ f) }.

Global Instance MonadExc_codegen : MonadExc error codegen :=
  { raise := fun _ => Build_codegen ∘ raise;
    catch := fun _ b h => Build_codegen (catch (uncodegen b) (uncodegen ∘ h)) }.

Global Instance MonadState_codegen : MonadState wlocal_ctx codegen :=
  { get := Build_codegen get;
    put := Build_codegen ∘ put }.

Global Instance MonadWriter_codegen : MonadWriter (@Monoid_list_app W.basic_instruction) codegen :=
  { tell := Build_codegen ∘ tell;
    listen := fun _ => Build_codegen ∘ listen ∘ uncodegen;
    (* Work around broken implementation of `pass` in ExtLib.
       https://github.com/rocq-community/coq-ext-lib/issues/153 *)
    pass := fun _ c => Build_codegen (mkStateT (fun s =>
      pass ('(x, f, s) ← runStateT (uncodegen c) s;
            ret (x, s, f)))) }.

Definition lift_error {A} (c : error + A) : codegen A :=
  Build_codegen (lift (lift c)).

Definition try_option {A} (e : error) (x : option A) : codegen A :=
  match x with
  | None => raise e
  | Some x' => ret x'
  end.

Definition ignore {A} (c : codegen A) : codegen unit :=
  c;;
  ret tt.

Definition run_codegen {A} (c : codegen A) (wl : wlocal_ctx) : error + A * wlocal_ctx * W.expr :=
  match runWriterT (runStateT (uncodegen c) wl) with
  | inl e => inl e
  | inr x => inr (PPair.pfst x, PPair.psnd x)
  end.

Definition emit (e : W.basic_instruction) : codegen unit := tell [e].

Definition emit_all : W.expr -> codegen unit := tell.

Definition capture {A} (c : codegen A) : codegen (A * W.expr) :=
  censor (const []) (listen c).

Definition block_c {A} (tf : W.function_type) (c : codegen A) : codegen A :=
  '(x, es) ← capture c;
  emit (W.BI_block tf es);;
  ret x.

Definition loop_c {A} (tf : W.function_type) (c : codegen A) : codegen A :=
  '(x, es) ← capture c;
  emit (W.BI_loop tf es);;
  ret x.

Definition if_c {A B} (tf : W.function_type) (thn : codegen A) (els : codegen B) : codegen (A * B) :=
  '(x1, es1) ← capture thn;
  '(x2, es2) ← capture els;
  emit (W.BI_if tf es1 es2);;
  ret (x1, x2).

Lemma runWriterT_sum_bind_dist {A B L E}
  (m : Monoid L)
  (c : writerT m (sum E) A)
  (f : A -> writerT m (sum E) B)
  (x : B)
  (l l1 : L) :
  runWriterT (c ≫= f) = inr (PPair.ppair x l) ->
  exists x1 l1 l2,
  runWriterT c = inr (PPair.ppair x1 l1) /\
  runWriterT (f x1) = inr (PPair.ppair x l2) /\
  l = m.(monoid_plus) l1 l2.
Proof.
  intros H.
  unfold runWriterT, mbind, MBind_Monad, flip, bind, Monad_writerT, bind, EitherMonad.Monad_either in H.
  destruct c.
  cbn in H.
  destruct runWriterT; first congruence.
  exists (PPair.pfst p).
  exists (PPair.psnd p).
  destruct (f (PPair.pfst p)).
  cbn in H.
  destruct runWriterT; first congruence.
  cbn.
  exists (PPair.psnd p0).
  split; first reflexivity.
  split.
  - inversion H. reflexivity.
  - congruence.
Qed.

Lemma runWriterT_runStateT_sum_bind_dist {E L S A B}
  (m : Monoid L)
  (c : stateT S (writerT m (sum E)) A)
  (f : A -> stateT S (writerT m (sum E)) B)
  (s s' : S)
  (l : L)
  (x : B) :
  runWriterT (runStateT (c ≫= f) s) = inr (PPair.ppair (x, s') l) ->
  exists x1 s1 l1 l2,
  runWriterT (runStateT c s) = inr (PPair.ppair (x1, s1) l1) /\
  runWriterT (runStateT (f x1) s1) = inr (PPair.ppair (x, s') l2) /\
  l = m.(monoid_plus) l1 l2.
Proof.
  intros H.
  unfold mbind, MBind_Monad, runStateT, flip, bind, Monad_stateT in H.
  apply runWriterT_sum_bind_dist in H.
  destruct H as (x1 & l1 & l2 & H1 & H2 & H3).
  - destruct x1 as [x1 s1].
    exists x1.
    exists s1.
    exists l1.
    exists l2.
    split; first assumption.
    split; assumption.
  - apply l.
Qed.

Lemma run_codegen_def {A} (c : codegen A) wl wl' x es:
  run_codegen c wl = inr (x, wl', es) <->
  runWriterT (runStateT (uncodegen c) wl) = inr (PPair.ppair (x, wl') es).
Proof.
  split.
  {
    intros H.
    unfold run_codegen in H.
    destruct (runWriterT (runStateT (uncodegen c) wl)); first congruence.
    inversion H.
    reflexivity.
  }
  {
    intros H.
    unfold run_codegen.
    destruct (runWriterT (runStateT (uncodegen c) wl)); first congruence.
    inversion H.
    reflexivity.
  }
Qed.

Lemma run_codegen_bind_dist {A B} (c : codegen A) (f : A -> codegen B) wl wl' es x :
  run_codegen (c ≫= f) wl = inr (x, wl', es) ->
  exists x1 wl1 es1 es2,
  run_codegen c wl = inr (x1, wl1, es1) /\
  run_codegen (f x1) wl1 = inr (x, wl', es2) /\
  es = es1 ++ es2.
Proof.
  intros H.
  rewrite run_codegen_def in H.
  apply runWriterT_runStateT_sum_bind_dist in H.
  destruct H as (x1 & s1 & l1 & l2 & H1 & H2 & H3).
  exists x1, s1, l1, l2.
  rewrite !run_codegen_def.
  split.
  - assumption.
  - split.
    + assumption.
    + unfold monoid_plus, Monoid_list_app in H3.
      assumption.
Qed.

Lemma run_codegen_lift_error_inr {A} c wl wl' es (x : A) :
  run_codegen (lift_error c) wl = inr (x, wl', es) ->
  c = inr x /\ wl' = wl /\ es = [].
Proof.
  intros H.
  destruct c; cbn in H; first congruence.
  inversion H.
  split; first reflexivity.
  split; reflexivity.
Qed.

Lemma run_codegen_capture {A} (c : codegen A) wl wl' es es' x :
  run_codegen (capture c) wl = inr (x, es', wl', es) ->
  run_codegen c wl = inr (x, wl', es') /\ es = [].
Proof.
  intros H.
  unfold run_codegen in *.
  cbn in H.
  destruct (runWriterT (runStateT (uncodegen c) wl)); first congruence.
  cbn in H.
  destruct p.
  cbn in *.
  destruct pfst.
  cbn in H.
  inversion H.
  subst a psnd l es.
  clear H.
  split; reflexivity.
Qed.

Ltac inv_cg_bind Hbind res wl es1 es2 Hgen1 Hgen2 :=
  let Heseq := fresh "Hes_app_eq" in
  apply run_codegen_bind_dist in Hbind;
  destruct Hbind as (res & wl & es1 & es2 & Hgen1 & Hgen2 & Heseq);
  rewrite Heseq.
