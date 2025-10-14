Require Import RichWasm.compiler.prelude.
From RichWasm.iris Require Import gc util.
Require Import RichWasm.iris.logrel.relations.
Require Import RichWasm.iris.host.iris_host.
Require Import RichWasm.syntax.

Section Relations.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!RichWasmGCG Σ}.
  Context `{!wasmG Σ}.
  Context `{!hvisG Σ}.
  Context `{!hmsG Σ}.
  Context `{!hasG Σ}.

  Variable sr : store_runtime.
  Variable gci : gc_invariant Σ.

  (* TODO *)
  Definition module_interp (ω : module_type) (mr : module_runtime) (m : W.module) : iProp Σ :=
    (∀ i,
       i ↪[mods] m -∗
       let exports := [] in (* TODO *)
       let imports := [] in (* TODO *)
       WP (([ID_instantiate exports i imports], []) : host_expr) @ top
          {{ v, ⌜v = immHV []⌝ ∗
                i ↪[mods] m ∗
                (* TODO: Relate instance to imports/exports. *)
                ∃ M inst, instance_interp sr mr gci M inst }})%I.

  (* TODO *)
  Definition has_module_type_sem (m : W.module) (ω : module_type) : iProp Σ :=
    True%I.

End Relations.
