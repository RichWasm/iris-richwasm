From stdpp Require Import gmap.

From mathcomp Require Import eqtype.

From iris.proofmode Require Import base tactics classes.

From RichWasm Require Import syntax util iris.util.
From RichWasm.iris.rules Require Import iris_rules proofmode.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Definition location := N.

Definition address := N.

Inductive pointer :=
| PtrInt (n : Z)
| PtrMM (a : address)
| PtrGC (ℓ : location)
| PtrRoot (a : address).

Inductive word :=
| WordInt (n : Z)
| WordPtr (p : pointer).

Inductive word_kind :=
| IntWord
| PtrWord.

Inductive rep_value :=
| PtrV (i : i32)
| I32V (i : i32)
| I64V (i : i64)
| F32V (f : f32)
| F64V (f : f64).

Class richwasmG (Σ : gFunctors) :=
  { rw_mm_layouts : gname;
    rw_mm_layoutsG :: ghost_mapG Σ address (list word_kind);
    rw_mm_objects : gname;
    rw_mm_objectsG :: ghost_mapG Σ address (list word);
    rw_gc_layouts : gname;
    rw_gc_layoutsG :: ghost_mapG Σ location (list word_kind);
    rw_gc_objects : gname;
    rw_gc_objectsG :: ghost_mapG Σ location (list word);
    rw_gc_roots : gname;
    rw_gc_rootsG :: ghost_mapG Σ address location }.

Notation "a ↦mml{ q } l" :=
  (a ↪[rw_mm_layouts]{q} l)%I (at level 20, format "a  ↦mml{ q }  l") : bi_scope.
Notation "a ↦mml l" := (a ↪[rw_mm_layouts] l)%I (at level 20, format "a  ↦mml  l") : bi_scope.

Notation "a ↦mmo{ q } o" :=
  (a ↪[rw_mm_objects]{q} o)%I (at level 20, format "a  ↦mmo{ q }  o") : bi_scope.
Notation "a ↦mmo o" := (a ↪[rw_mm_objects] o)%I (at level 20, format "a  ↦mmo  o") : bi_scope.

Notation "ℓ ↦gcl{ q } l" :=
  (ℓ ↪[rw_gc_layouts]{q} l)%I (at level 20, format "ℓ  ↦gcl{ q }  l") : bi_scope.
Notation "ℓ ↦gcl l" := (ℓ ↪[rw_gc_layouts] l)%I (at level 20, format "ℓ  ↦gcl  l") : bi_scope.

Notation "ℓ ↦gco{ q } o" :=
  (ℓ ↪[rw_gc_objects]{q} o)%I (at level 20, format "ℓ  ↦gco{ q }  o") : bi_scope.
Notation "ℓ ↦gco o" := (ℓ ↪[rw_gc_objects] o)%I (at level 20, format "ℓ  ↦gco  o") : bi_scope.

Notation "a ↦gcr{ q } ℓ" :=
  (a ↪[rw_gc_roots]{q} ℓ)%I (at level 20, format "a  ↦gcr{ q }  ℓ") : bi_scope.
Notation "a ↦gcr ℓ" := (a ↪[rw_gc_roots] ℓ)%I (at level 20, format "a  ↦gcr  ℓ") : bi_scope.

Definition mm_object_map : Type := gmap address (list word).

Definition mm_layout_map : Type := gmap address (list word_kind).

Definition gc_object_map : Type := gmap location (list word).

Definition gc_layout_map : Type := gmap location (list word_kind).

Definition gc_address_map : Type := gmap location address.

Definition gc_root_map : Type := gmap address location.

Definition rt_invariant (Σ : gFunctors) : Type :=
  mm_layout_map -> mm_object_map -> gc_layout_map -> gc_object_map -> gc_root_map -> iProp Σ.

Definition to_rep_value (ι : primitive_rep) (v : value) : option rep_value :=
  match ι, v with
  | PtrR, VAL_int32 i => Some (PtrV i)
  | I32R, VAL_int32 i => Some (I32V i)
  | I64R, VAL_int64 i => Some (I64V i)
  | F32R, VAL_float32 f => Some (F32V f)
  | F64R, VAL_float64 f => Some (F64V f)
  | _, _ => None
  end.

Definition to_rep_values (ιs : list primitive_rep) (vs : list value) : option (list rep_value) :=
  mapM (fun '(ι, v) => to_rep_value ι v) (zip ιs vs).

Definition word_has_kind (k : word_kind) (w : word) : bool :=
  match k, w with
  | IntWord, WordInt _ => true
  | PtrWord, WordPtr _ => true
  | _, _ => false
  end.

Definition kinds_of_pointer_map (m : i64) (n : nat) : list word_kind :=
  map
    (fun b : bool => if b then PtrWord else IntWord)
    (take n (reverse (Wasm_int.Int64.convert_to_bits m))).

Definition index_address (i : nat) : N := N.of_nat (4 * i).

Inductive repr_pointer : N -> gc_address_map -> pointer -> Z -> Prop :=
| ReprPtrInt gc_heap_off θ n :
  repr_pointer gc_heap_off θ (PtrInt n) (2 * n)
| ReprPtrMM gc_heap_off θ a :
  (a `mod` 4 = 0)%N ->
  repr_pointer gc_heap_off θ (PtrMM a) (Z.of_N a - 3)
| ReprPtrGC gc_heap_off θ ℓ a :
  θ !! ℓ = Some a ->
  (a `mod` 4 = 0)%N ->
  (a >= gc_heap_off)%N ->
  repr_pointer gc_heap_off θ (PtrGC ℓ) (Z.of_N a - 1)
| ReprPtrRoot gc_heap_off θ a :
  (a `mod` 4 = 0)%N ->
  (a < gc_heap_off)%N ->
  repr_pointer gc_heap_off θ (PtrRoot a) (Z.of_N a - 1).

Inductive repr_word : N -> gc_address_map -> word -> Z -> Prop :=
| ReprWordInt gc_heap_off θ n :
  repr_word gc_heap_off θ (WordInt n) n
| ReprWordPtr gc_heap_off θ p n :
  repr_pointer gc_heap_off θ p n ->
  repr_word gc_heap_off θ (WordPtr p) n.

Inductive repr_double_word : word -> word -> Z -> Prop :=
| ReprDoubleWordInt n1 n2 m :
  repr_word 0 ∅ (WordInt n1) n1 ->
  repr_word 0 ∅ (WordInt n2) n2 ->
  (Wasm_int.Int32.Z_mod_modulus n1 + n2 ≪ 32)%Z = m ->
  repr_double_word (WordInt n1) (WordInt n2) m.

Definition repr_list_word (gc_heap_off : N) (θ : gc_address_map) (ws : list word) (ns : list Z) :
  Prop :=
  Forall2 (repr_word gc_heap_off θ) ws ns.

Definition repr_location_index (θ : gc_address_map) (ℓ : location) (i : nat) (a : Z) : Prop :=
  exists a0, θ !! ℓ = Some a0 /\ a = Z.of_N (a0 + index_address i).

Definition repr_location (θ : gc_address_map) (ℓ : location) (a : Z) : Prop :=
  repr_location_index θ ℓ 0 a.

Inductive ser_value : N -> rep_value -> list word -> Prop :=
| SerPtr gc_heap_off p n :
  repr_pointer gc_heap_off ∅ p n ->
  ser_value gc_heap_off (PtrV (Wasm_int.int_of_Z i32m n)) [WordPtr p]
| SerI32 gc_heap_off n :
  ser_value gc_heap_off (I32V (Wasm_int.int_of_Z i32m n)) [WordInt n]
| SerI64 gc_heap_off n w1 w2 :
  repr_double_word w1 w2 n ->
  ser_value gc_heap_off (I64V (Wasm_int.int_of_Z i64m n)) [w1; w2]
| SerF32 gc_heap_off i f n :
  ser_value gc_heap_off (I32V i) [WordInt n] ->
  serialise_i32 i = serialise_f32 f ->
  ser_value gc_heap_off (F32V f) [WordInt n]
| SerF64 gc_heap_off i f n1 n2 :
  ser_value gc_heap_off (I64V i) [WordInt n1; WordInt n2] ->
  serialise_i64 i = serialise_f64 f ->
  ser_value gc_heap_off (F64V f) [WordInt n1; WordInt n2].

Section Token.

  Context `{wasmG Σ}.
  Context `{richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.

  Definition mm_object_layout (mml : mm_layout_map) (mmo : mm_object_map) : Prop :=
    map_Forall (fun a '(ks, ws) => Forall2 word_has_kind ks ws) (map_zip mml mmo).

  Definition mm_object_memory (mmo : mm_object_map) : iProp Σ :=
    (* TODO: Seems like this will never allow MM memory owned by the GC to be reclaimed. *)
    [∗ map] a ↦ ws ∈ mmo,
      ∃ bs ns,
        N.of_nat sr.(sr_mem_mm) ↦[wms][a] bs ∗
          ⌜bs = flat_map serialize_Z_i32 ns⌝ ∗
          ⌜repr_list_word sr.(sr_gc_heap_off) ∅ ws ns⌝.

  Inductive mm_closed_reach_from : mm_object_map -> gc_root_map -> word -> Prop :=
  | MMClosedReachInt mmo gcr n :
    mm_closed_reach_from mmo gcr (WordInt n)
  | MMClosedReachPtrInt mmo gcr n :
    mm_closed_reach_from mmo gcr (WordPtr (PtrInt n))
  | MMClosedReachPtrMM mmo gcr a ws :
    mmo !! a = Some ws ->
    Forall (mm_closed_reach_from mmo gcr) ws ->
    mm_closed_reach_from mmo gcr (WordPtr (PtrMM a))
  | MMClosedReachPtrRoot mmo gcr a :
    a ∈ dom gcr ->
    mm_closed_reach_from mmo gcr (WordPtr (PtrRoot a)).

  Definition gc_object_layout (gcl : gc_layout_map) (gco : gc_object_map) : Prop :=
    map_Forall (fun ℓ '(ks, ws) => Forall2 word_has_kind ks ws) (map_zip gcl gco).

  Definition gc_object_memory (θ : gc_address_map) (gco : gc_object_map) : iProp Σ :=
    [∗ map] ℓ ↦ a; ws ∈ θ; gco,
      ∃ bs ns,
        N.of_nat sr.(sr_mem_gc) ↦[wms][a] bs ∗
          ⌜bs = flat_map serialize_Z_i32 ns⌝ ∗
          ⌜repr_list_word sr.(sr_gc_heap_off) θ ws ns⌝.

  Definition gc_root_memory (θ : gc_address_map) (gcr : gc_root_map) : iProp Σ :=
    [∗ map] a ↦ ℓ ∈ gcr,
      ∃ bs n,
        N.of_nat sr.(sr_mem_gc) ↦[wms][a] bs ∗ ⌜bs = serialize_Z_i32 n⌝ ∗ ⌜repr_location θ ℓ n⌝.

  Definition gc_closed_reach
    (mmo : mm_object_map) (gco : gc_object_map) (gcr : gc_root_map) (θ : gc_address_map) : Prop :=
    map_Forall
      (fun ℓ ws =>
         ℓ ∈ dom θ ->
         Forall (fun w => match w with
                       | WordInt _ => True
                       | WordPtr (PtrInt _) => True
                       | WordPtr (PtrMM a) =>
                           match mmo !! a with
                           | None => False
                           | Some ws => Forall (mm_closed_reach_from mmo gcr) ws
                           end
                       | WordPtr (PtrGC ℓ') => ℓ' ∈ dom θ
                       | WordPtr (PtrRoot a) => a ∈ dom gcr
                       end)
                ws)
      gco.

  Definition gc_live_roots (θ : gc_address_map) (gcr : gc_root_map) : Prop :=
    map_Forall (fun _ ℓ => ℓ ∈ dom θ) gcr.

  (* TODO: MM memory resources. *)
  Definition rt_token (θ : gc_address_map) : iProp Σ :=
    ∃ mml mmo gcl gco gcr,
      ghost_map_auth rw_mm_layouts (1/2) mml ∗
        ghost_map_auth rw_mm_objects 1 mmo ∗
        ghost_map_auth rw_gc_layouts (1/2) gcl ∗
        ghost_map_auth rw_gc_objects 1 gco ∗
        ghost_map_auth rw_gc_roots (1/2) gcr ∗
        rti mml mmo gcl gco gcr ∗
        ⌜mm_object_layout mml mmo⌝ ∗
        mm_object_memory mmo ∗
        ⌜gmap_injective θ⌝ ∗
        ⌜gc_closed_reach mmo gco gcr θ⌝ ∗
        ⌜gc_object_layout gcl gco⌝ ∗
        gc_object_memory θ gco ∗
        gc_root_memory θ gcr ∗
        ⌜gc_live_roots θ gcr⌝.

End Token.

Section Rules.

  Context `{wasmG Σ}.
  Context `{richwasmG Σ}.

  Variable sr : store_runtime.

  Lemma byte_eqm_mod (n : Z) (m : Z) :
    (n `mod` 256 = m `mod` 256)%Z ->
    Integers.Byte.eqm n m.
  Admitted.

  Lemma serialise_split_i64 k1 k2 :
    serialise_i32 (Wasm_int.int_of_Z i32m k1) ++
    serialise_i32 (Wasm_int.int_of_Z i32m k2) =
    serialise_i64 (Wasm_int.int_of_Z i64m (Wasm_int.Int32.Z_mod_modulus k1 + k2 ≪ 32)).
  Proof.
    unfold serialise_i32, serialise_i64, Memdata.encode_int.
    Transparent Archi.big_endian.
    cbn.

    rewrite !Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite !Wasm_int.Int64.Z_mod_modulus_eq.
    f_equal; last f_equal; last f_equal; last f_equal; last f_equal; last f_equal; last f_equal; last f_equal.
    all: apply Integers.Byte.eqm_samerepr; apply byte_eqm_mod.
    - rewrite <- Znumtheory.Zmod_div_mod; try done; last by exists (two_power_nat (32 - 8)).
      rewrite <- Znumtheory.Zmod_div_mod; try done; last by exists (two_power_nat (64 - 8)).
      rewrite Z.add_mod; last done.
      rewrite Z.shiftl_mul_pow2; last done.
      rewrite Z.mul_mod; last done.
      rewrite (Znumtheory.Zdivide_mod (2 ^ 32)); last by exists (two_power_nat (32 - 8)).
      rewrite Z.mul_0_r.
      rewrite Z.mod_0_l; last done.
      rewrite Z.add_0_r.
      rewrite Z.mod_mod; last done.
      rewrite <- Znumtheory.Zmod_div_mod; try done; last by exists (two_power_nat (32 - 8)).
    - replace Wasm_int.Int32.modulus with (256 * 2 ^ 24)%Z; last done.
      replace Wasm_int.Int64.modulus with (256 * 2 ^ 56)%Z; last done.
      rewrite !Zaux.Zdiv_mod_mult; try done.

      rewrite <- Znumtheory.Zmod_div_mod; try done; last by exists (two_power_nat (32 - 2 * 8)).
      rewrite <- Znumtheory.Zmod_div_mod; try done; last by exists (two_power_nat (64 - 2 * 8)).
      rewrite Z.shiftl_mul_pow2; last done.
      replace (k2 * 2 ^ 32)%Z with ((k2 * 2 ^ 24) * 256)%Z; last lia.
      rewrite Z_div_plus; last done.

      rewrite Z.add_mod; last done.
      rewrite Z.mul_mod; last done.
      rewrite (Znumtheory.Zdivide_mod (2 ^ 24)); last by exists (two_power_nat (32 - 2 * 8)).
      rewrite Z.mul_0_r.
      rewrite Z.mod_0_l; last done.
      rewrite Z.add_0_r.
      rewrite <- Znumtheory.Zmod_div_mod; try done.
      rewrite Zaux.Zdiv_mod_mult; try done.
      rewrite <- Znumtheory.Zmod_div_mod; try done; last by exists (two_power_nat (32 - 2 * 8)).
    - replace Wasm_int.Int32.modulus with (256 * (256 * 2 ^ 16))%Z; last done.
      replace Wasm_int.Int64.modulus with (256 * (256 * 2 ^ 48))%Z; last done.
      rewrite !Zaux.Zdiv_mod_mult; try done.

      rewrite <- Znumtheory.Zmod_div_mod; try done; last by exists (two_power_nat (32 - 3 * 8)).
      rewrite <- Znumtheory.Zmod_div_mod; try done; last by exists (two_power_nat (64 - 3 * 8)).
      rewrite Z.shiftl_mul_pow2; last done.
      replace (k2 * 2 ^ 32)%Z with (((k2 * 2 ^ 16) * 256) * 256)%Z; last lia.
      rewrite !Z_div_plus; try done.

      rewrite Z.add_mod; last done.
      rewrite Z.mul_mod; last done.
      rewrite (Znumtheory.Zdivide_mod (2 ^ 16)); last by exists (two_power_nat (32 - 3 * 8)).
      rewrite Z.mul_0_r.
      rewrite Z.mod_0_l; last done.
      rewrite Z.add_0_r.
      rewrite Zaux.Zdiv_mod_mult; try done.
      rewrite Zaux.Zdiv_mod_mult; try done.
      rewrite <- Znumtheory.Zmod_div_mod; try done.
      rewrite <- Znumtheory.Zmod_div_mod; try done; last by exists (two_power_nat (16 - 8)).
    - replace Wasm_int.Int32.modulus with (256 * (256 * (256 * 2 ^ 8)))%Z; last done.
      replace Wasm_int.Int64.modulus with (256 * (256 * (256 * 2 ^ 40)))%Z; last done.
      rewrite !Zaux.Zdiv_mod_mult; try done.

      rewrite <- Znumtheory.Zmod_div_mod; try done.
      rewrite <- Znumtheory.Zmod_div_mod; try done; last by exists (two_power_nat (64 - 4 * 8)).
      rewrite Z.shiftl_mul_pow2; last done.
      replace (k2 * 2 ^ 32)%Z with ((((k2 * 2 ^ 8) * 256) * 256) * 256)%Z; last lia.
      rewrite !Z_div_plus; try done.

      rewrite Z.add_mod; last done.
      rewrite Z.mul_mod; last done.
      rewrite (Znumtheory.Zdivide_mod (2 ^ 8)); last by exists (two_power_nat (32 - 4 * 8)).
      rewrite Z.mul_0_r.
      rewrite Z.mod_0_l; last done.
      rewrite Z.add_0_r.
      rewrite Z.mod_mod; last done.

      rewrite Zaux.Zdiv_mod_mult; try done.
      rewrite Zaux.Zdiv_mod_mult; try done.
      rewrite Zaux.Zdiv_mod_mult; try done.
      by rewrite Z.mod_mod; last done.
    - replace Wasm_int.Int64.modulus with (256 * (256 * (256 * (256 * 2 ^ 32))))%Z; last done.
      rewrite !Zaux.Zdiv_mod_mult; try done.

      rewrite <- Znumtheory.Zmod_div_mod; try done; last by exists (two_power_nat (32 - 8)).
      rewrite <- Znumtheory.Zmod_div_mod; try done; last by exists (two_power_nat (64 - 5 * 8)).
      rewrite Z.shiftl_mul_pow2; try done.
      replace (k2 * 2 ^ 32)%Z with ((((k2 * 256) * 256) * 256) * 256)%Z; last lia.
      rewrite !Z_div_plus; try done.

      rewrite Z.add_mod; try done.
      rewrite Z.div_div; try done.
      rewrite Z.div_div; try done.
      rewrite Z.div_div; try done.
      rewrite Z.mod_div; last done.
      rewrite Z.mod_0_l; last done.
      rewrite Z.add_0_l.
      rewrite Z.mod_mod; done.
    - replace Wasm_int.Int64.modulus with (256 * (256 * (256 * (256 * 2 ^ 32))))%Z; last done.
      rewrite !Zaux.Zdiv_mod_mult; try done.

      replace (2 ^ 32)%Z with (256 * 2 ^ 24)%Z; last reflexivity.
      rewrite Zaux.Zdiv_mod_mult; try done.

      rewrite <- Znumtheory.Zmod_div_mod; try done; last by exists (two_power_nat (32 - 2 * 8)).
      rewrite Z.shiftl_mul_pow2; try done.
      replace (k2 * 2 ^ 32)%Z with ((((k2 * 256) * 256) * 256) * 256)%Z; last lia.
      rewrite !Z_div_plus; try done.

      rewrite Z.div_div; try done.
      rewrite Z.div_div; try done.
      rewrite Z.div_div; try done.
      rewrite Z.mod_div; last done.
      rewrite Z.add_0_l.

      replace Wasm_int.Int32.modulus with (256 * 2 ^ 24)%Z; last done.
      rewrite Zaux.Zdiv_mod_mult; try done.
      rewrite <- Znumtheory.Zmod_div_mod; try done; last by exists (two_power_nat (24 - 8)).
    - replace Wasm_int.Int64.modulus with (256 * (256 * (256 * (256 * 2 ^ 32))))%Z; last done.
      rewrite !Zaux.Zdiv_mod_mult; try done.

      replace (2 ^ 32)%Z with (256 * (256 * 2 ^ 16))%Z; last reflexivity.
      rewrite Zaux.Zdiv_mod_mult; try done.
      rewrite Zaux.Zdiv_mod_mult; try done.

      rewrite <- Znumtheory.Zmod_div_mod; try done; last by exists (two_power_nat (32 - 3 * 8)).
      rewrite Z.shiftl_mul_pow2; try done.
      replace (k2 * 2 ^ 32)%Z with ((((k2 * 256) * 256) * 256) * 256)%Z; last lia.
      rewrite !Z_div_plus; try done.

      rewrite Z.div_div; try done.
      rewrite Z.div_div; try done.
      rewrite Z.div_div; try done.
      rewrite Z.div_div; try done.
      rewrite Z.div_div; try done.
      rewrite Z.mod_div; last done.
      rewrite Z.add_0_l.

      replace Wasm_int.Int32.modulus with ((256 * 256) * 2 ^ 16)%Z; last done.
      rewrite Zaux.Zdiv_mod_mult; try done.
      rewrite <- Znumtheory.Zmod_div_mod; try done; last by exists (two_power_nat (24 - 2 * 8)).
    - replace Wasm_int.Int64.modulus with (256 * (256 * (256 * (256 * 2 ^ 32))))%Z; last done.
      rewrite !Zaux.Zdiv_mod_mult; try done.

      replace (2 ^ 32)%Z with (256 * (256 * (256 * 256)))%Z; last reflexivity.
      rewrite Zaux.Zdiv_mod_mult; try done.
      rewrite Zaux.Zdiv_mod_mult; try done.
      rewrite Zaux.Zdiv_mod_mult; try done.

      rewrite <- Znumtheory.Zmod_div_mod; try done.
      rewrite Z.shiftl_mul_pow2; try done.
      replace (k2 * 2 ^ 32)%Z with ((((k2 * 256) * 256) * 256) * 256)%Z; last lia.
      rewrite !Z_div_plus; try done.

      rewrite Z.div_div; try done.
      rewrite Z.div_div; try done.
      rewrite Z.div_div; try done.
      rewrite Z.div_div; try done.
      rewrite Z.div_div; try done.
      rewrite Z.div_div; try done.
      rewrite Z.div_div; try done.
      rewrite Z.mod_div; last done.
      rewrite Z.add_0_l.

      replace Wasm_int.Int32.modulus with ((256 * (256 * 256)) * 256)%Z; last done.
      rewrite Zaux.Zdiv_mod_mult; try done.
      rewrite Z.mod_mod; done.

    Opaque Archi.big_endian.
  Qed.

  Lemma wms_app n bs1 :
    forall ℓ sz1 bs2,
    sz1 = N.of_nat (length bs1) ->
    n ↦[wms][ℓ] (bs1 ++ bs2) ⊣⊢ n ↦[wms][ℓ] bs1 ∗ n ↦[wms][ℓ + sz1] bs2.
  Proof.
    unfold mem_block_at_pos.
    intros.
    rewrite big_opL_app.
    repeat (f_equiv; try lia).
  Qed.

  Lemma list_pluck : forall (A : Type) i (l : list A),
    i < length l ->
    exists l1 x l2,
    l !! i = Some x /\
    length l1 = i /\
    l = l1 ++ x :: l2.
  Admitted.

  Lemma list_pluck_2 {A : Type} i (l : list A) :
    i + 1 < length l ->
    exists l1 x1 x2 l2,
    l !! i = Some x1 /\
    l !! (i + 1) = Some x2 /\
    length l1 = i /\
    l = l1 ++ x1 :: x2 :: l2.
  Admitted.

  Lemma flat_map_singleton : forall (A B : Type) (f : A -> list B) (x : A),
    f x = flat_map f [x].
  Proof.
    intros A B f x. simpl. rewrite app_nil_r. reflexivity.
  Qed.

  Lemma deserialise_serialise_i32 : forall i,
    wasm_deserialise (serialise_i32 i) T_i32 = VAL_int32 i.
  Proof.
    intros i. replace (serialise_i32 i) with (bits (VAL_int32 i)).
    - rewrite deserialise_bits.
      + reflexivity.
      + reflexivity.
    - unfold bits. reflexivity.
  Qed.

  Lemma deserialise_serialise_i64 : forall i,
    wasm_deserialise (serialise_i64 i) T_i64 = VAL_int64 i.
  Proof.
    intros i. replace (serialise_i64 i) with (bits (VAL_int64 i)).
    - rewrite deserialise_bits.
      + reflexivity.
      + reflexivity.
    - unfold bits. reflexivity.
  Qed.

  Lemma pointer_offset_eqn_Z2N : forall i n m,
    Z.of_N n = (Wasm_int.Int32.unsigned i + Z.of_N m)%Z ->
    n = (Wasm_int.N_of_uint i32m i + m)%N.
  Proof.
    intros i n m.
    rewrite <- (Z2N.id (Wasm_int.Int32.unsigned _)); last apply Wasm_int.Int32.unsigned_range.
    rewrite <- N2Z.inj_add. apply N2Z.inj.
  Qed.

  Ltac solve_i32_bytes_len len :=
    try rewrite <- flat_map_app;
    rewrite -> flat_map_constant_length with (c := 4);
    [ try rewrite length_app; rewrite len; unfold index_address; unfold serialise_i32;
      try rewrite Memdata.encode_int_length;
      cbn; lia
    | auto ].

  (* TODO: What would happen if the ∃ k was pulled up to a lemma parameter, and
           repr_vval θ vv k was an assumption? *)
  Lemma wp_load_i32_gc
      (s : stuckness) (E : coPset) (F : frame) (memidx : immediate)
      (rti : rt_invariant Σ) (θ : gc_address_map)
      (i : i32) (ℓ : location) (ws : list word)
      (j : nat) (off : static_offset) (w : word) :
    F.(f_inst).(inst_memory) !! memidx = Some sr.(sr_mem_gc) ->
    repr_location_index θ ℓ j (Wasm_int.Z_of_uint i32m i + Z.of_N off) ->
    ws !! j = Some w ->
    rt_token rti sr θ ∗ ℓ ↦gco ws ∗ ↪[frame] F ∗ ↪[RUN] ⊢
    WP [AI_basic (BI_const (VAL_int32 i)); AI_basic (BI_load memidx T_i32 None N.zero off)]
       @ s; E
       {{ v, ∃ n,
            ⌜v = immV [VAL_int32 (Wasm_int.int_of_Z i32m n)]⌝ ∗
              ⌜repr_word sr.(sr_gc_heap_off) θ w n⌝ ∗
              rt_token rti sr θ ∗
              ℓ ↦gco ws ∗
              ↪[RUN] ∗
              ↪[frame] F }}.
  Admitted.

  Lemma wp_load_i64_gc
      (s : stuckness) (E : coPset) (F : frame) (memidx : immediate)
      (rti : rt_invariant Σ) (θ : gc_address_map)
      (i : i32) (ℓ : location) (ws : list word)
      (j : nat) (off : static_offset) (n1 n2 : Z) :
    F.(f_inst).(inst_memory) !! memidx = Some sr.(sr_mem_gc) ->
    repr_location_index θ ℓ j (Wasm_int.Z_of_uint i32m i + Z.of_N off) ->
    ws !! j = Some (WordInt n1) ->
    ws !! (j + 1) = Some (WordInt n2) ->
    rt_token rti sr θ ∗ ℓ ↦gco ws ∗ ↪[RUN] ∗ ↪[frame] F ⊢
    WP [AI_basic (BI_const (VAL_int32 i)); AI_basic (BI_load memidx T_i64 None N.zero off)]
       @ s; E
       {{ v, ∃ n,
            ⌜v = immV [VAL_int64 (Wasm_int.int_of_Z i64m n)]⌝ ∗
              ⌜repr_double_word (WordInt n1) (WordInt n2) n⌝ ∗
              rt_token rti sr θ ∗
              ℓ ↦gco ws ∗
              ↪[RUN] ∗
              ↪[frame] F }}.
  Admitted.

  Lemma wp_store_i32_gc
      (s : stuckness) (E : coPset) (F : frame) (memidx : immediate)
      (rti : rt_invariant Σ) (θ : gc_address_map)
      (i k : i32) (ℓ : location) (ws : list word)
      (j : nat) (off : static_offset) (w : word) :
    F.(f_inst).(inst_memory) !! memidx = Some sr.(sr_mem_gc) ->
    repr_location_index θ ℓ j (Wasm_int.Z_of_uint i32m i + Z.of_N off) ->
    j < length ws ->
    repr_word sr.(sr_gc_heap_off) θ w (Wasm_int.Z_of_uint i32m k) ->
    rt_token rti sr θ ∗ ℓ ↦gco ws ∗ ↪[RUN] ∗ ↪[frame] F ⊢
    WP [AI_basic (BI_const (VAL_int32 i));
        AI_basic (BI_const (VAL_int32 k));
        AI_basic (BI_store memidx T_i32 None N.zero off)]
       @ s; E
       {{ v, ⌜v = immV []⌝ ∗
             rt_token rti sr θ ∗
             ℓ ↦gco <[ j := w ]> ws ∗
             ↪[RUN] ∗ ↪[frame] F }}.
  Admitted.

  (* TODO: wp_loadroot *)

  (* TODO: wp_duproot *)

End Rules.
