Require Import stdpp.base.
Require Import stdpp.list.
Require Import stdpp.list_basics.
Require Import RichWasm.syntax.
Require Import RichWasm.typing.
Require Import RichWasm.iris.memory.

Definition get_path_words (off sz : nat) (ws : list word) : list word :=
  firstn sz (skipn off ws).

Definition update_path_words (off : nat) (ws ws' : list word) : list word :=
  (firstn off ws) ++ ws' ++ (skipn (length ws') (skipn off ws)).

Definition pr_expected (pr : path_result) (τ__π: option type) :=
  match τ__π with
  | Some τ__π' => τ__π'
  | None => pr.(pr_target)
  end.

Lemma update_get_path_id off sz ws :
  sz + off ≤ length ws ->
  update_path_words off ws (get_path_words off sz ws) = ws.
Proof.
  etransitivity; last apply (take_drop off ws).
  unfold update_path_words.
  f_equal.
  etransitivity; last apply (take_drop sz (drop off ws)).
  f_equal.
  unfold get_path_words.
  rewrite length_take, length_drop.
  f_equal; lia.
Qed.
