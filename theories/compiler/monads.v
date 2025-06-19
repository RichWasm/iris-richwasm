From stdpp Require Import base strings gmap gmultiset fin_sets decidable list.
From Wasm Require datatypes.
From RWasm Require Import exn state.
From RWasm Require Export exn state.

Module wasm := datatypes.

(* TODO: these need a better home. *)
Global Instance wasm_value_type_eq_dec : EqDecision wasm.value_type.
Proof. solve_decision. Defined.

Global Instance wasm_result_type_eq_dec : EqDecision wasm.result_type.
Proof. solve_decision. Defined.

Global Instance wasm_function_type_eq_dec : EqDecision wasm.function_type.
Proof. solve_decision. Defined.

Global Instance option_wasm_value_type_eq_dec : EqDecision (option wasm.value_type).
Proof. solve_decision. Defined.

(* ExtLib has its own state monad but it doens't play nicely with stdpp *)
Definition state (S A : Type) : Type := S -> (S * A).

(* Not great but ok for now *)
Inductive Err :=
| err (msg: string).

(* The compiler monad. *)
#[global]
Definition M := exn Err.

Definition mlookup_with_msg {A} (idx: nat) (lst: list A) (msg: string) : M A :=
  match list_lookup idx lst with
  | Some x => mret x
  | None => mthrow (err msg)
  end.

Definition lift_optionM `{!MRet M, !MRet M} {A} (oa : option A) (error : string) : M A :=
  match oa with
  | Some x => mret x
  | None => mthrow (err error)
  end.

Section TempLocals.

  Record TempLocals := {
    tl_start : nat;
    tl_next  : nat;
    tl_types : gmap nat wasm.value_type;
    tl_free  : gset nat
  }.

  Definition new_tl (start : nat) : TempLocals :=
    {| tl_start := start; tl_next := start; tl_types := ∅; tl_free := ∅ |}.
  Definition InstM := stateT TempLocals M.
  Definition liftM {A} (m : M A) : InstM A :=
    λ st,
      x ← m;
      mret (st, x).
  Definition modify_st (f : TempLocals → TempLocals) : InstM unit := mmodify f.
  Definition get_st : InstM TempLocals               := mget.
  Definition put_st : TempLocals → InstM unit        := mput.
  Definition fresh_local (ty : wasm.value_type) : InstM wasm.immediate :=
    st ← get_st;
    let reusable := filter (λ i, tl_types st !! i = Some ty) (elements (tl_free st)) in
    match reusable with
    | i :: _ =>
      let st' :=
        {| tl_start := tl_start st;
           tl_next  := tl_next st;
           tl_types := tl_types st;
           tl_free  := tl_free st ∖ {[ i ]} |} in
      put_st st';;
      mret i
    | [] =>
      let i := tl_next st in
      let st' :=
        {| tl_start := tl_start st;
           tl_next  := S i;
           tl_types := <[ i := ty ]> (tl_types st);
           tl_free  := tl_free st |} in
      put_st st';;
      mret i
    end.
  Definition free_local (i : wasm.immediate) : InstM unit :=
    modify_st (λ st, {| tl_start := tl_start st;
                        tl_next  := tl_next  st;
                        tl_types := tl_types st;
                        tl_free  := tl_free  st ∪ {[ i ]} |}).
End TempLocals.

Section Example.

  Definition example_computation : InstM (nat * nat * nat) :=
    i1 ← fresh_local wasm.T_i32;
    i2 ← fresh_local wasm.T_f64;
    free_local i1;;
    i3 ← fresh_local wasm.T_i32;
    mret (i1, i2, i3).

  Definition run_example :=
    match example_computation (new_tl 5) with
    | OK (st, (i1, i2, i3)) => Some (st, i1, i2, i3)
    | _ => None
    end.

  Lemma example_properties :
    match run_example with
    | Some (st, i1, i2, i3) =>
        tl_types st !! i1 = Some wasm.T_i32 /\
        tl_types st !! i2 = Some wasm.T_f64 /\
        i3 = i1
    | None => False
    end.
  Proof.
    unfold run_example, example_computation.
    repeat split.
  Qed.

End Example.

Lemma stateT_bind_OK_inv
      {S A B}
      (m : stateT S (exn Err) A)
      (f : A → stateT S (exn Err) B)
      (s : S) (st' : S) (b : B) :
  (m ≫= f) s = @OK Err (S * B) (st', b) →
  ∃ st1 a, m s = OK Err (S * A) (st1, a) ∧ f a st1 = OK Err (S * B) (st', b).
Proof.
  unfold mbind, stateT_MBind; simpl.
  destruct (m s) as [e | [st1 a]] eqn:Hm; simpl.
  - intros H. discriminate H.
  - intros H. exists st1, a. split; [rewrite <- Hm | exact H]. reflexivity.
Qed.

Lemma fresh_local_preserves_tl_types ty st st' i :
  fresh_local ty st = mret (st', i) →
  tl_types st' !! i = Some ty
  /\
  (∀ j t, tl_types st !! j = Some t → tl_types st' !! j = Some t).
Proof.
  unfold fresh_local, get_st; cbn.
  intro Hrun.
    remember (filter (λ j, tl_types st !! j = Some ty)
                   (elements (tl_free st))) as reusable eqn:Heq.
  destruct reusable as [k |] eqn:Hr; cbn in Hrun.
    - admit.
    - admit.
Admitted.

(* TODO: this feels like it should already exist in stdpp *)
Section monadic_fold.
  Context {M : Type → Type}.
  Context `{!MBind M, !MRet M}.

  Fixpoint foldrM {A B} (f : A → B → M B) (init : B) (l : list A) : M B :=
    match l with
    | [] => mret init
    | x :: xs => foldrM f init xs ≫= fun acc => f x acc
    end.

  Fixpoint foldlM {A B} (f : A → B → M B) (init : B) (l : list A) : M B :=
    match l with
    | [] => mret init
    | x :: xs => f x init ≫= fun acc => foldlM f acc xs
    end.
End monadic_fold.

(* built-in has reversed args *)
Fixpoint foldl' {A B} (f : A -> B -> B) (init : B) (l : list A) : B :=
  match l with
  | [] => init
  | x :: xs => let acc := f x init in foldl' f acc xs
  end.
