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

  Lemma bind_inr {A B C} (mx : A + B) (f : B -> A + C) (y : C) :
    mx ≫= f = inr y ↔ ∃ x : B, mx = inr x /\ f x = inr y.
  Proof.
    split.
    - intros H. destruct mx; first inversion H. by exists b.
    - by intros (x & -> & Hfx).
  Qed.

  Theorem fundamental_module m m' mt :
    has_module_type m mt ->
    compile_module m = inr m' ->
    ⊢ module_interp rti sr mt m'.
  Proof.
    iIntros (Hmt Hm ???) "Hmod Himps %Hlen_exps Hexps Hfr Hrun".
    apply bind_inr in Hm as ([wt imps] & Himps_try & Hm).
    destruct (user_imports rt_types m.(module.m_imports)) as [[wt' imps']|] eqn:Himps;
      last inversion Himps_try.
    inversion Himps_try.
    subst wt' imps'.
    clear Himps_try.
    apply bind_inr in Hm as ([wt' defs] & Hdefs & Hm).
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
