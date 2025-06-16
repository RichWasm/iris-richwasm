From stdpp Require Import base strings gmap gmultiset fin_sets decidable.
From Wasm Require datatypes.
From RWasm Require Import exn state.
From RWasm Require Export exn state.
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

Module wasm := datatypes.
Section TempLocals.

  Context `{!EqDecision wasm.value_type}.

  #[global]
  Instance wasm_value_type_eq_dec : EqDecision wasm.value_type.
  Proof.
    unfold EqDecision.
    intros x y.
    destruct x; destruct y;
      (left; reflexivity) || (right; discriminate).
  Defined.

  Record TempLocals := {
    tl_start : nat;
    tl_next  : nat;
    tl_types : gmap nat datatypes.value_type;
    tl_free  : gset nat
  }.

  Definition new_tl (start : nat) : TempLocals :=
    {| tl_start := start; tl_next := start; tl_types := ∅; tl_free := ∅ |}.
  Definition InstM := stateT TempLocals M.
  Definition get_st  : InstM TempLocals               := mget.
  Definition put_st  : TempLocals → InstM unit        := mput.
  Definition modify_st (f : TempLocals → TempLocals)  : InstM unit := mmodify f.
  Definition lift_M {A} (m : M A) : InstM A :=
    λ st,
      x ← m;
      mret (st, x).
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
  Context `{!EqDecision wasm.value_type}.

  Let st0 : TempLocals :=
    {| tl_start := 5;
       tl_next := 5;
       tl_types := ∅;
       tl_free := ∅ |}.

  Let tmp1 := match fresh_local wasm.T_i32 st0 with | OK (st1, i1) => (st1, i1) | _ => (st0, 0) end.
  Let st1 := fst tmp1.
  Let i1 := snd tmp1.

  Let tmp2 := match fresh_local wasm.T_f64 st1 with | OK (st2, i2) => (st2, i2) | _ => (st1, 0) end.
  Let st2 := fst tmp2.
  Let i2 := snd tmp2.

  Let tmp3 := match free_local i1 st2 with | OK (s,_) => s | _ => st2 end.
  Let st3 := tmp3.

  Let tmp4 := match fresh_local wasm.T_i32 st3 with | OK (st4, i3) => (st4, i3) | _ => (st3, 0) end.
  Let st4 := fst tmp4.
  Let i3 := snd tmp4.

  Goal True.
    assert (tl_types st4 !! i1 = Some wasm.T_i32) by (cbn; reflexivity).
    assert (tl_types st4 !! i2 = Some wasm.T_f64) by (cbn; reflexivity).
    assert (tl_types st4 !! i3 = Some wasm.T_i32)by (cbn; reflexivity).
    assert (i3 = i1) by reflexivity.

    exact I.
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

