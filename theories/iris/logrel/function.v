From iris.proofmode Require Export base proofmode classes.

From RichWasm Require Import syntax typing.
From RichWasm.compiler Require Import prelude module.
Require Import RichWasm.iris.host.iris_host.
Require Import RichWasm.iris.rules.iris_rules.
From RichWasm.iris Require Import logrel memory util.

Module W := RichWasm.wasm.datatypes.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section function.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.

  Theorem fundamental_function mr M wt wt' wtf mf mf' ϕ :
    has_function_type M mf ϕ ->
    compile_function wt mf = inr (wt', mf') ->
    ⊢ has_func_type_sem rti sr mr M (wt ++ wt' ++ wtf) mf' ϕ.
  Proof.
    iIntros (Hϕ Hcf ?? Htf) "#Hinst".
    inversion Hϕ.
    subst M0 mf0 ϕ ϕ0 ϕ1.
    set (ϕ := mf.(mf_type)) in *.
    set (fft := flatten_function_type ϕ) in *.
    rename H into Hηss_L.
    rename H0 into Hρs_P.
    rename H1 into Hηss_P.
    rename H3 into Hψ.
    rename H2 into HL'.
    destruct tf as [ts1 ts2].
    rewrite closure_interp_eq.

    (* TODO: By induction on ϕ, build up an se such that sem_env_interp F se.
             Then use the fundamental theorem for instruction typing to show that the body of the
             function is well-behaved. *)
  Admitted.

End function.
