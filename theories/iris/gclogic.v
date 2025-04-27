From Wasm.iris.rules Require Import iris_rules.

(* TODO: Notation for:
   - Store pointers: ℓ ↦vblk b
   - Root pointers: a ↦root ℓ
 *)

Notation vloc := nat (only parsing).

Inductive vval :=
  | Vint : Z -> vval
  | Vloc : vloc -> vval.

Inductive vblock_tag :=
  | TagDefault
  | TagNoScan.

Record vblock := {
  tag : vblock_tag;
  vals : list vval;
}.

Notation vstore := (gmap vloc vblock).

Notation addr := N (only parsing).

Notation addr_map := (gmap vloc addr).

Notation word := (eqtype.Equality.sort i32).

Definition code_int (z : Z) : word :=
  Wasm_int.int_of_Z i32m (2 * z + 1).

Definition code_addr (a : addr) : word :=
  Wasm_int.int_of_Z i32m (Z.of_N a).

Inductive repr_vval : addr_map -> vval -> word -> Prop :=
  | repr_vint θ z :
      repr_vval θ (Vint z) (code_int z)
  | repr_vloc θ ℓ a :
      θ !! ℓ = Some a ->
      repr_vval θ (Vloc ℓ) (code_addr a).

Definition serialize_word (w : word) : bytes :=
  serialise_i32 w.

(* TODO *)
Definition serialize_vblock (blk : vblock) : bytes :=
  [].

Definition roots_are_live (θ : addr_map) (roots : gmap addr vval) : Prop :=
  ∀ a ℓ, roots !! a = Some (Vloc ℓ) -> ℓ ∈ dom θ.

Definition gmap_inj `{Countable K} {V} (m : gmap K V) :=
  ∀ k1 k2 v, m !! k1 = Some v -> m !! k2 = Some v -> k1 = k2.

Definition GC_correct (ζ : vstore) (θ : addr_map) : Prop :=
  gmap_inj θ /\
  ∀ ℓ blk ℓ',
  ℓ ∈ dom θ ->
  ζ !! ℓ = Some blk ->
  Vloc ℓ' ∈ blk.(vals) ->
  ℓ' ∈ dom θ.

Class rwasm_gcG Σ := Rwasm_gcG {
  gcG_vstoreG :: ghost_mapG Σ vloc vblock;
  gcG_rootsG :: ghost_mapG Σ addr vval;
  gcG_vstore : gname;
  gcG_roots : gname;
}.

Section GCtoken.

Context `{wasmG Σ}.
Context `{rwasm_gcG Σ}.

Definition GC (θ : addr_map) : iProp Σ :=
  ∃ (ζ : vstore) (roots : gmap addr vval) (mem : N),
  ghost_map_auth gcG_vstore 1 ζ ∗
  ghost_map_auth gcG_roots 1 roots ∗
  ([∗ map] ℓ ↦ a; blk ∈ θ; ζ, mem ↦[wms][a] serialize_vblock blk) ∗
  ([∗ map] a ↦ u ∈ roots, ∃ bs w, mem ↦[wms][a] bs ∗ ⌜bs = serialize_word w⌝ ∗ ⌜repr_vval θ u w⌝) ∗
  ⌜roots_are_live θ roots⌝ ∗
  ⌜GC_correct ζ θ⌝.

End GCtoken.
