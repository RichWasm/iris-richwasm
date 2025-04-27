From Wasm.iris.rules Require Import iris_rules.

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

Definition serialize_word (w : word) : bytes :=
  serialise_i32 w.

Definition serialize_nat_32 (n : nat) : bytes :=
  serialise_i32 (Wasm_int.int_of_Z i32m (Z.of_nat n)).

Definition serialize_vblock_tag (t : vblock_tag) : byte :=
  match t with
  | TagDefault => #00%byte
  | TagNoScan => #01%byte
  end.

Inductive repr_vval : addr_map -> vval -> word -> Prop :=
  | RVint θ z :
      repr_vval θ (Vint z) (code_int z)
  | RVloc θ ℓ a :
      θ !! ℓ = Some a ->
      repr_vval θ (Vloc ℓ) (code_addr a).

Inductive repr_vblock : addr_map -> vblock -> bytes -> Prop :=
  | RVblock θ blk ws tag_b length_bs data_bs :
      Forall (curry (repr_vval θ)) (combine blk.(vals) ws) ->
      tag_b = serialize_vblock_tag blk.(tag) ->
      length_bs = serialize_nat_32 (length blk.(vals)) ->
      data_bs = flat_map serialize_word ws ->
      repr_vblock θ blk (tag_b :: take 31 length_bs ++ data_bs).

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

Notation "ℓ ↦vblk{ dq } b" := (ℓ ↪[gcG_vstore]{dq} b)%I
  (at level 20, format "ℓ ↦vblk{ dq } b") : bi_scope.
Notation "ℓ ↦vblk b" := (ℓ ↪[gcG_vstore] b)%I
  (at level 20, format "ℓ ↦vblk b") : bi_scope.

Notation "a ↦root{ dq } u" := (a ↪[gcG_roots]{dq} u)%I
  (at level 20, format "a ↦root{ dq } u") : bi_scope.
Notation "a ↦root u" := (a ↪[gcG_roots] u)%I
  (at level 20, format "a ↦root u") : bi_scope.

Section GCtoken.

Context `{wasmG Σ}.
Context `{rwasm_gcG Σ}.

Definition GC (θ : addr_map) : iProp Σ :=
  ∃ (ζ : vstore) (roots : gmap addr vval) (mem : N),
  ghost_map_auth gcG_vstore 1 ζ ∗
  ghost_map_auth gcG_roots 1 roots ∗
  ([∗ map] ℓ ↦ a; blk ∈ θ; ζ, ∃ bs, mem ↦[wms][a] bs ∗ ⌜repr_vblock θ blk bs⌝) ∗
  ([∗ map] a ↦ u ∈ roots, ∃ bs w, mem ↦[wms][a] bs ∗ ⌜bs = serialize_word w⌝ ∗ ⌜repr_vval θ u w⌝) ∗
  ⌜roots_are_live θ roots⌝ ∗
  ⌜GC_correct ζ θ⌝.

End GCtoken.
