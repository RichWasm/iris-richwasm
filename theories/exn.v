From stdpp Require Import base option.

Set Universe Polymorphism.

Section exceptions.
  Variables (E: Type).

  Inductive exn (A : Type) : Type :=
  | Err (e: E)
  | OK (a: A).
  Arguments Err {A} e.
  Arguments OK {A} a.

  Definition exn_to_opt {A: Type} (c: exn A) : option A :=
    match c with
    | Err _ => None
    | OK a => Some a
    end.

  Definition exn_map {A B: Type} (f: A -> B) (c: exn A) : exn B :=
    match c with
    | Err e => Err e
    | OK a => OK (f a)
    end.

  Definition exn_bind {A B: Type} (f: A -> exn B) (c: exn A) : exn B :=
    match c with
    | Err e => Err e
    | OK a => f a
    end.

  Definition exn_join {A: Type} (c: exn (exn A)) : exn A :=
    match c with
    | OK (OK a) => OK a
    | OK (Err e)
    | Err e => Err e
    end.

End exceptions.


#[export]
Instance exn_FMap {E} : FMap (exn E) := @exn_map E.

#[export]
Instance exn_MBind {E} : MBind (exn E) := @exn_bind E.

#[export]
Instance exn_MRet {E} : MRet (exn E) := @OK E.

#[export]
Instance exn_MJoin {E} : MJoin (exn E) := @exn_join E.

#[export]
Instance exn_throw {E} : MThrow E (exn E) := @Err E.

Definition guard_opt {E A} (err: E) (c: option A) : exn E A :=
  match c with
  | Some a => mret a
  | None => mthrow err
  end.
