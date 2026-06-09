From iris.proofmode Require Export base proofmode classes.

Require Import RichWasm.typing.
Require Import RichWasm.compiler.module.
Require Import RichWasm.iris.host.iris_host.
Require Import RichWasm.iris.rules.iris_rules.
From RichWasm.iris Require Import logrel memory util.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Fundamental.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.
  Context `{!hvisG Σ}.
  Context `{!hmsG Σ}.
  Context `{!hasG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.

  Theorem fundamental_module m m' mt :
    has_module_type m mt ->
    run_modgen (compile_module m) mod_empty = inr (tt, m') ->
    ⊢ module_interp rti sr mt m'.
  Proof.
    iIntros (Hmt Hmg ???) "Hmod Himps %Hlen_exps Hexps Hfr Hrun".
    iApply (instantiation_spec_operational_start with "[$] [$] [-]").
    - admit.
    - admit.
    - admit.
    - iFrame.
      admit.
    - iIntros (?) "Hfr Hrun (Hmod & Himp & %inst & Hpost & Hhost)".
      iApply wp_lift_wasm.
      change [AI_invoke idnstart] with ([] ++ [AI_invoke idnstart]).
      iApply (wp_invoke_native with "[$] [$]").
      + done.
      + by instantiate (1 := []).
      + done.
      + admit.
      + iIntros "!> (Hfr & Hrun & Hstart)".
        admit.
  Admitted.

End Fundamental.
