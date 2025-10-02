From RichWasm.syntax Require Export module rw.

Definition primitive_rep_eq_dec (ι1 ι2 : primitive_rep) : {ι1 = ι2} + {ι1 <> ι2}.
  decide equality.
Defined.
