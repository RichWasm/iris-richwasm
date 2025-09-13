From RichWasm.syntax Require Export modules rw.

Definition primitive_rep_eq_dec (ι1 ι2 : primitive_rep) : {ι1 = ι2} + {ι1 <> ι2}.
  destruct ι1, ι2; try (left; reflexivity); try (right; congruence).
Defined.
