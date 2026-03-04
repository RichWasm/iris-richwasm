From RichWasm.iris.language Require Import iris_wp_def.

(* TODO: Duplicated in relations.v. *)
Fixpoint simple_get_base_l (svh : simple_valid_holed) : list value :=
  match svh with
  | SH_base vs _ => vs
  | SH_rec _ _ _ svh' _ => simple_get_base_l svh'
  end.

Definition vh_depth {i : nat} (vh : valid_holed i) : nat :=
  lh_depth (lh_of_vh vh).
