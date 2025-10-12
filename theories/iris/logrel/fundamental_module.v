Require Import RichWasm.typing.
Require Import RichWasm.compiler.module.
Require Import RichWasm.iris.rules.iris_rules.
Require Import RichWasm.iris.logrel.relations_module.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Fundamental.

  Context `{Σ : gFunctors}.

  Theorem fundamental_module m m' ω :
    has_module_type m ω ->
    run_modgen (compile_module m) mod_empty = inr (tt, m') ->
    ⊢ @has_module_type_sem Σ m' ω.
  Admitted.

End Fundamental.
