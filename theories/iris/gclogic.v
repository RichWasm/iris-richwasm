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

Notation addr := (N * N)%type (only parsing).

Notation addr_map := (gmap vloc addr).

Definition code_int (z : Z) : value :=
  VAL_int64 (Wasm_int.int_of_Z i64m (2 * z + 1)).

Definition code_addr '((m, i) : addr) : value :=
  let to_int64 := Wasm_int.int_of_Z i64m in
  let low := to_int64 (Z.of_N i) in
  let high := Wasm_int.Int64.shl (to_int64 (Z.of_N m)) (to_int64 (Z.of_nat 32)) in
  VAL_int64 (Wasm_int.Int64.add low high).

Inductive repr_vval : addr_map -> vval -> value -> Prop :=
  | repr_vint θ z :
      repr_vval θ (Vint z) (code_int z)
  | repr_vloc θ ℓ a :
      θ !! ℓ = Some a ->
      repr_vval θ (Vloc ℓ) (code_addr a).

(* TODO *)
Definition serialize_vblock (blk : vblock) : bytes :=
  [].

Definition roots_are_live (θ : addr_map) (roots : gmap addr vval) : Prop :=
  ∀ a ℓ, roots !! a = Some (Vloc ℓ) -> ℓ ∈ dom θ.

Definition gmap_inj `{Countable K} {V} (m : gmap K V) :=
  ∀ k1 k2 v, m !! k1 = Some v → m !! k2 = Some v → k1 = k2.

Definition GC_correct (ζ : vstore) (θ : addr_map) : Prop :=
  gmap_inj θ ∧
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
  ∃ (ζ : vstore) (roots : gmap addr vval),
    ghost_map_auth gcG_vstore 1 ζ ∗
    ghost_map_auth gcG_roots 1 roots ∗
    ([∗ map] ℓ ↦ '(m, i); blk ∈ θ; ζ, m ↦[wms][i] serialize_vblock blk) ∗
    ([∗ map] '(m, i) ↦ u ∈ roots, ∃ bs v, m ↦[wms][i] bs ∗ ⌜bs = bits v⌝ ∗ ⌜repr_vval θ u v⌝) ∗
    ⌜roots_are_live θ roots⌝ ∗
    ⌜GC_correct ζ θ⌝.

End GCtoken.
