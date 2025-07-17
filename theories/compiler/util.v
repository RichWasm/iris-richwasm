From stdpp Require Import base strings gmap gmultiset fin_sets decidable list.
From Wasm Require datatypes.
From RichWasm.util Require Import exn state.

Module W := datatypes.

(* TODO: these need a better home. *)
Global Instance wasm_value_type_eq_dec : EqDecision W.value_type.
Proof. solve_decision. Defined.

Global Instance wasm_result_type_eq_dec : EqDecision W.result_type.
Proof. solve_decision. Defined.

Global Instance wasm_function_type_eq_dec : EqDecision W.function_type.
Proof. solve_decision. Defined.

Global Instance option_wasm_value_type_eq_dec : EqDecision (option W.value_type).
Proof. solve_decision. Defined.

Global Instance wasm_value_type_countable : Countable W.value_type.
Proof.
  refine
    (inj_countable'
       (λ vt, match vt with | W.T_i32 => 0 | W.T_i64 => 1 | W.T_f32 => 2 | W.T_f64 => 3 end)
       (λ n, match n with | 0 => W.T_i32 | 1 => W.T_i64 | 2 => W.T_f32 | _ => W.T_f64 (* keeps surjective *) end)
       _).
  by intros []; simpl.
Qed.
Global Instance wasm_function_type_countable : Countable W.function_type.
Proof.
  refine
    (inj_countable'
       (λ ft : W.function_type, match ft with W.Tf ins outs => (ins, outs) end)
       (λ p, let (ins, outs) := p in W.Tf ins outs)
       _).
  by intros []; simpl.
Qed.

(* Not great but ok for now *)
Inductive err :=
| Err (msg : string)
| Todo.

Definition mlookup_with_msg {A} (idx: nat) (lst: list A) (msg: string) : exn err A :=
  match list_lookup idx lst with
  | Some x => mret x
  | None => mthrow (Err msg)
  end.

Definition err_opt {A} (oa : option A) (error : string) : exn err A :=
  guard_opt (Err error) oa.
