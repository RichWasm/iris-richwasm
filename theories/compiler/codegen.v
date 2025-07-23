From Coq Require Import List.
Import ListNotations.
Require Import Coq.Program.Basics.
Local Open Scope program_scope.

From ExtLib.Data.Monads Require Import StateMonad WriterMonad.
From ExtLib.Structures Require Import Monads.
Import MonadNotation.
Local Open Scope monad.

From Wasm Require datatypes.

From RichWasm Require term.
From RichWasm.compiler Require Import types util.
Require Import RichWasm.util.dlist.
Import RichWasm.util.dlist.Notation.

Module R := RichWasm.term.
Module W := Wasm.datatypes.

Notation wlocal_ctx := (list W.value_type) (only parsing).

Notation dexpr := (dlist W.basic_instruction).

Record codegen (A : Type) :=
  { uncodegen : stateT wlocal_ctx
                       (writerT (@DList.Monoid_dlist W.basic_instruction)
                                (sum error))
                       A }.

Arguments Build_codegen {A} _.
Arguments uncodegen {A} _.

Existing Instance Monad_stateT.

Global Instance Monad_codegen : Monad codegen :=
  { ret := fun _ => Build_codegen ∘ ret;
    bind := fun _ _ c f => Build_codegen (uncodegen c >>= uncodegen ∘ f) }.

Global Instance MonadExc_codegen : MonadExc error codegen :=
  { raise := fun _ => Build_codegen ∘ raise;
    catch := fun _ b h => Build_codegen (catch (uncodegen b) (uncodegen ∘ h)) }.

Global Instance MonadState_codegen : MonadState wlocal_ctx codegen :=
  { get := Build_codegen get;
    put := Build_codegen ∘ put }.

Global Instance MonadWriter_codegen : MonadWriter (@DList.Monoid_dlist W.basic_instruction) codegen :=
  { tell := Build_codegen ∘ tell;
    listen := fun _ => Build_codegen ∘ listen ∘ uncodegen;
    (* Work around broken implementation of `pass` in ExtLib.
       https://github.com/rocq-community/coq-ext-lib/issues/153 *)
    pass := fun _ c => Build_codegen (mkStateT (fun s =>
      pass ('(x, f, s) <- runStateT (uncodegen c) s;;
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

Definition run_codegen (c : codegen unit) (wl : wlocal_ctx) : error + wlocal_ctx * W.expr :=
  match runWriterT (runStateT (uncodegen c) wl) with
  | inl e => inl e
  | inr x => inr (snd (PPair.pfst x), DList.to_list (PPair.psnd x))
  end.

Definition emit (e : W.basic_instruction) : codegen unit :=
  tell (DList.singleton e).

Definition capture {A} (c : codegen A) : codegen (A * dexpr) :=
  censor (const []%DL) (listen c).

Definition block_c {A} (tf : W.function_type) (c : codegen A) : codegen A :=
  '(x, es) <- capture c;;
  emit (W.BI_block tf (DList.to_list es));;
  ret x.

Definition loop_c {A} (tf : W.function_type) (c : codegen A) : codegen A :=
  '(x, es) <- capture c;;
  emit (W.BI_loop tf (DList.to_list es));;
  ret x.

Definition if_c {A B} (tf : W.function_type) (thn : codegen A) (els : codegen B) : codegen (A * B) :=
  '(x1, es1) <- capture thn;;
  '(x2, es2) <- capture els;;
  emit (W.BI_if tf (DList.to_list es1) (DList.to_list es2));;
  ret (x1, x2).
