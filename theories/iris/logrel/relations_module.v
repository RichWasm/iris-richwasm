Require Import RichWasm.compiler.prelude.
From RichWasm.iris Require Import memory util.
Require Import RichWasm.iris.logrel.relations.
Require Import RichWasm.iris.host.iris_host.
Require Import RichWasm.syntax.

Section Relations.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.
  Context `{!wasmG Σ}.
  Context `{!hvisG Σ}.
  Context `{!hmsG Σ}.
  Context `{!hasG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.

  (* TODO *)
  Definition module_interp (ω : module_type) (mr : module_runtime) (m : W.module) : iProp Σ :=
    (∀ i imports exports,
       i ↪[mods] m -∗
       (* TODO: Assert that indices in the module point to the global runtime funcaddrs. *)
       ([∗ list] i ↦ ϕ ∈ ω.(mt_imports),
          ∃ bs j cl,
            N.of_nat i ↪[vis] Build_module_export bs (MED_func j) ∗
              N.of_nat (funcimm j) ↦[wf] cl ∗
              closure_interp rti sr senv_empty ϕ cl ∗
              ⌜imports !! (funcimm mr.(mr_func_user) + i)%nat = Some (N.of_nat (funcimm j))⌝) -∗
       ([∗ list] i ↦ '_ ∈ ω.(mt_exports),
          ∃ bs j,
            N.of_nat i ↪[vis] Build_module_export bs (MED_func j) ∗
              ⌜exports !! i = Some (N.of_nat (funcimm j))⌝) -∗
       WP (([ID_instantiate exports i imports], []) : host_expr) @ top
          {{ v, ⌜v = immHV []⌝ ∗
                  i ↪[mods] m ∗
                  ([∗ list] i ↦ ϕ ∈ ω.(mt_exports),
                     ∃ j cl, (* TODO: same j as precond *)
                       N.of_nat (funcimm j) ↦[wf] cl ∗
                         closure_interp rti sr senv_empty ϕ cl) }})%I.

  (* TODO *)
  Definition has_module_type_sem (m : W.module) (ω : module_type) : iProp Σ :=
    True%I.

End Relations.
