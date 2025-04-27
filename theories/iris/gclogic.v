From Wasm.iris.rules Require Import iris_rules.

Notation vloc := nat (only parsing).

Inductive vval :=
  | Vint : Z -> vval
  | Vloc : vloc -> vval.

Inductive vblock_tag :=
  | TagDefault
  | TagNoScan.

Notation vblock := (vblock_tag * list vval)%type.

Notation vstore := (gmap vloc vblock).

Notation addr := (N * N)%type (only parsing).

Notation addr_map := (gmap vloc addr).

Class rwasm_gcG Σ := Rwasm_gcG {
  gcG_vstoreG :: ghost_mapG Σ vloc vblock;
  gcG_vstore : gname;
}.

(* TODO *)
Definition serialize_vblock (vblk : vblock) : bytes :=
  [].

(* TODO *)
Definition GC_correct (ζ : vstore) (Θ : addr_map) : Prop := True.

Section GCtoken.

Context `{wasmG Σ}.
Context `{rwasm_gcG Σ}.

Definition GC (θ : addr_map) : iProp Σ :=
  ∃ (ζ : vstore),
  ghost_map_auth gcG_vstore 1 ζ ∗
  ([∗ map] ℓ ↦ '(m, i); vblk ∈ θ; ζ, m ↦[wms][i] serialize_vblock vblk) ∗
  (* TODO: Include authoritative roots map. *)
  ⌜GC_correct ζ θ⌝.

End GCtoken.
