From mathcomp Require Import eqtype.
From stdpp Require Import gmap.
From iris.proofmode Require Import base tactics classes.
From RichWasm.iris.rules Require Import iris_rules proofmode.

Set Bullet Behavior "Strict Subproofs".

Definition gmap_injective `{Countable K} {V} (m : gmap K V) :=
  ∀ k1 k2 v, m !! k1 = Some v -> m !! k2 = Some v -> k1 = k2.

Section Model.

  Variable heap_start : N.

  Definition location := nat.

  Definition address := N.

  Inductive pointer :=
  | PtrMM (δ : address)
  | PtrGC (ℓ : location)
  | PtrRoot (δ : address).

  Inductive word :=
  | WordInt (n : Z)
  | WordPtr (p : pointer).

  Inductive word_kind :=
  | IntWord
  | PtrWord.

  Record object_signature :=
    { os_prefix : list word_kind;
      os_element : list word_kind;
      os_count : nat }.

  Definition signature_map : Type := gmap location object_signature.

  Definition object : Type := list word.

  Definition object_map : Type := gmap location object.

  Definition address_map : Type := gmap location address.

  Definition root_map : Type := gmap address location.

  Definition gc_invariant (Σ : gFunctors) : Type := signature_map -> object_map -> root_map -> iProp Σ.

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

  Definition serialize_Z_i32 : Z -> bytes := serialise_i32 ∘ Wasm_int.int_of_Z i32m.

  Definition index_address (i : nat) : N := N.of_nat (4 * i).

  Inductive repr_pointer : address_map -> pointer -> Z -> Prop :=
  | ReprPtrMM θ δ :
    (δ `mod` 2 = 0)%N ->
    repr_pointer θ (PtrMM δ) (Z.of_N δ)
  | ReprPtrGC θ ℓ δ :
    θ !! ℓ = Some δ ->
    (δ `mod` 2 = 1)%N ->
    (δ >= heap_start)%N ->
    repr_pointer θ (PtrGC ℓ) (Z.of_N (δ - 1))
  | ReprPtrRoot θ δ :
    (δ `mod` 2 = 1)%N ->
    (δ < heap_start)%N ->
    repr_pointer θ (PtrRoot δ) (Z.of_N δ).

  Inductive repr_word : address_map -> word -> Z -> Prop :=
  | ReprWordInt θ n :
    repr_word θ (WordInt n) n
  | ReprWordPtr θ p n :
    repr_pointer θ p n ->
    repr_word θ (WordPtr p) n.

  Inductive repr_double_word : address_map -> word -> word -> Z -> Prop :=
  | ReprDoubleWordInt θ n1 n2 m :
    repr_word θ (WordInt n1) n1 ->
    repr_word θ (WordInt n2) n2 ->
    (Wasm_int.Int32.Z_mod_modulus n1 + n2 ≪ 32)%Z = m ->
    repr_double_word θ (WordInt n1) (WordInt n2) m.

  Definition repr_object (θ : address_map) (o : object) (ns : list Z) : Prop :=
    Forall2 (repr_word θ) o ns.

  Inductive repr_location_index : address_map -> location -> nat -> Z -> Prop :=
  | ReprLocElem θ ℓ i δ0 δ :
    θ !! ℓ = Some δ0 ->
    δ = Z.of_N (δ0 + index_address i) ->
    repr_location_index θ ℓ i δ.

  Class RichWasmGCG (Σ : gFunctors) :=
    { gc_signatures : gname;
      gc_signatures_G :: ghost_mapG Σ location object_signature;
      gc_objects : gname;
      gc_objects_G :: ghost_mapG Σ location (list word);
      gc_roots : gname;
      gc_roots_G :: ghost_mapG Σ address location }.

End Model.

Notation "ℓ ↦sig{ q } s" :=
  (ℓ ↪[gc_signatures]{q} s)%I (at level 20, format "ℓ  ↦sig{ q }  s") : bi_scope.

Notation "ℓ ↦sig s" := (ℓ ↪[gc_signatures] s)%I (at level 20, format "ℓ  ↦sig  s") : bi_scope.

Notation "ℓ ↦obj{ q } o" :=
  (ℓ ↪[gc_objects]{q} o)%I (at level 20, format "ℓ  ↦obj{ q }  o") : bi_scope.

Notation "ℓ ↦obj o" := (ℓ ↪[gc_objects] o)%I (at level 20, format "ℓ  ↦obj  o") : bi_scope.

Notation "δ ↦root{ q } ℓ" :=
  (δ ↪[gc_roots]{q} ℓ)%I (at level 20, format "δ  ↦root{ q }  ℓ") : bi_scope.

Notation "δ ↦root ℓ" := (δ ↪[gc_roots] ℓ)%I (at level 20, format "δ  ↦root  ℓ") : bi_scope.

Section Token.

  Context `{wasmG Σ}.
  Context `{RichWasmGCG Σ}.

  Variable heap_start : N.

  Definition consistent_objects_memory (m : memaddr) (θ : address_map) (os : object_map) : iProp Σ :=
    [∗ map] ℓ ↦ δ; o ∈ θ; os,
    ∃ bs ns,
    N.of_nat m ↦[wms][δ] bs ∗
    ⌜bs = flat_map serialize_Z_i32 ns⌝ ∗
    ⌜repr_object heap_start θ o ns⌝.

  Definition consistent_roots_memory (m : memaddr) (θ : address_map) (rs : root_map) : iProp Σ :=
    [∗ map] δ ↦ ℓ ∈ rs,
    ∃ bs n,
    N.of_nat m ↦[wms][δ] bs ∗
    ⌜bs = serialize_Z_i32 n⌝ ∗
    ⌜repr_location_index θ ℓ 0 n⌝.

  Definition consistent_objects_signatures (ss : signature_map) (os : object_map) : Prop :=
    map_Forall
      (fun ℓ '(s, o) =>
         length o =? length s.(os_prefix) + s.(os_count) * length s.(os_element) /\
           Forall (curry word_has_kind) (combine (concat (repeat s.(os_element) s.(os_count))) o))
      (map_zip ss os).

  Definition consistent_reachable_addresses (os : object_map) (θ : address_map) : Prop :=
    gmap_injective θ /\
    ∀ ℓ ℓ' o,
    ℓ ∈ dom θ ->
    os !! ℓ = Some o ->
    WordPtr (PtrGC ℓ') ∈ o ->
    ℓ' ∈ dom θ.

  Definition live_roots (θ : address_map) (rs : root_map) : Prop :=
    ∀ δ ℓ, rs !! δ = Some ℓ -> ℓ ∈ dom θ.

  Definition gc_token (inv : gc_invariant Σ) (m : memaddr) (θ : address_map) : iProp Σ :=
    ∃ (ss : signature_map) (os : object_map) (rs : root_map),
    inv ss os rs ∗
    ghost_map_auth gc_signatures (1/2) ss ∗
    ghost_map_auth gc_objects 1 os ∗
    ghost_map_auth gc_roots (1/2) rs ∗
    consistent_objects_memory m θ os ∗
    consistent_roots_memory m θ rs ∗
    ⌜consistent_objects_signatures ss os⌝ ∗
    ⌜consistent_reachable_addresses os θ⌝ ∗
    ⌜live_roots θ rs⌝.

End Token.

Section Rules.

  Context `{wasmG Σ}.
  Context `{RichWasmGCG Σ}.

  Variable heap_start : N.

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

  Lemma repr_object_index : forall θ o w ns i,
    o !! i = Some w ->
    repr_object heap_start θ o ns ->
    exists n, repr_word heap_start θ w n /\ ns !! i = Some n.
  Admitted.

  Lemma repr_object_index_double : forall θ o n1 n2 ns i,
    o !! i = Some (WordInt n1) ->
    o !! (i + 1) = Some (WordInt n2) ->
    repr_object heap_start θ o ns ->
    exists n,
    repr_double_word heap_start θ (WordInt n1) (WordInt n2) n /\
    ns !! i = Some n1 /\
    ns !! (i + 1) = Some n2.
  Admitted.

  Ltac solve_i32_bytes_len len :=
    try rewrite <- flat_map_app;
    rewrite -> flat_map_constant_length with (c := 4);
    [ try rewrite length_app; rewrite len; unfold index_address; unfold serialise_i32;
      try rewrite Memdata.encode_int_length;
      cbn; lia
    | auto ].

  Definition alloc_gc_spec
    (E : coPset) (inv : gc_invariant Σ) (m : memaddr)
    (finst : instance) (fid : nat) (fts : list value_type) (fes : list basic_instruction) :
    iProp Σ :=
    □ ∀ (F : frame) (θ : address_map) (prefix_sz count elem_sz : i32) (prefix_map elem_map : i64),
    let alloc_gc_func :=
      N.of_nat fid ↦[wf] FC_func_native finst (Tf [T_i32; T_i64; T_i32; T_i32; T_i64] [T_i32]) fts fes
    in
    let sig :=
      {| os_prefix := kinds_of_pointer_map prefix_map (Wasm_int.nat_of_uint i32m prefix_sz);
         os_count := Wasm_int.nat_of_uint i32m count;
         os_element := kinds_of_pointer_map elem_map (Wasm_int.nat_of_uint i32m elem_sz) |}
    in
    gc_token heap_start inv m θ ∗
    alloc_gc_func ∗
    ↪[frame] F -∗
    WP [AI_basic (BI_const (VAL_int32 prefix_sz));
        AI_basic (BI_const (VAL_int64 prefix_map));
        AI_basic (BI_const (VAL_int32 count));
        AI_basic (BI_const (VAL_int32 elem_sz));
        AI_basic (BI_const (VAL_int64 elem_map));
        AI_invoke fid]
       @ E
       {{ v, (⌜v = trapV⌝ ∨
              ∃ θ' ℓ n obj,
              ⌜v = immV [VAL_int32 (Wasm_int.int_of_Z i32m n)]⌝ ∗ ⌜repr_location_index θ' ℓ 0 n⌝ ∗
              gc_token heap_start inv m θ' ∗ ℓ ↦sig sig ∗ ℓ ↦obj obj ∗
              alloc_gc_func) ∗
             ↪[frame] F }}%I.

  (* TODO: What would happen if the ∃ k was pulled up to a lemma parameter, and
   * repr_vval θ vv k was an assumption? *)
  Lemma wp_load_i32_gc
      (s : stuckness) (E : coPset) (F : frame) (memidx : immediate)
      (m : memaddr) (θ : address_map) (inv : gc_invariant Σ)
      (i : i32) (ℓ : location) (obj : object)
      (j : nat) (off : static_offset) (w : word) :
    F.(f_inst).(inst_memory) !! memidx = Some m ->
    repr_location_index θ ℓ j (Wasm_int.Z_of_uint i32m i + Z.of_N off) ->
    obj !! j = Some w ->
    gc_token heap_start inv m θ ∗ ℓ ↦obj obj ∗ ↪[frame] F ∗ ↪[RUN] ⊢
    WP [AI_basic (BI_const (VAL_int32 i)); AI_basic (BI_load memidx T_i32 None N.zero off)]
       @ s; E
       {{ v, (∃ n, ⌜v = immV [VAL_int32 (Wasm_int.int_of_Z i32m n)]⌝ ∗ ⌜repr_word heap_start θ w n⌝) ∗
             gc_token heap_start inv m θ ∗ ℓ ↦obj obj ∗ ↪[RUN] ∗ ↪[frame] F }}.
  Admitted.

  Lemma wp_load_i64_gc
      (s : stuckness) (E : coPset) (F : frame) (memidx : immediate)
      (m : memaddr) (θ : address_map) (inv : gc_invariant Σ)
      (i : i32) (ℓ : location) (obj : object)
      (j : nat) (off : static_offset) (n1 n2 : Z) :
    F.(f_inst).(inst_memory) !! memidx = Some m ->
    repr_location_index θ ℓ j (Wasm_int.Z_of_uint i32m i + Z.of_N off) ->
    obj !! j = Some (WordInt n1) ->
    obj !! (j + 1) = Some (WordInt n2) ->
    gc_token heap_start inv m θ ∗ ℓ ↦obj obj ∗ ↪[RUN] ∗ ↪[frame] F ⊢
    WP [AI_basic (BI_const (VAL_int32 i)); AI_basic (BI_load memidx T_i64 None N.zero off)]
       @ s; E
       {{ v, (∃ n, ⌜v = immV [VAL_int64 (Wasm_int.int_of_Z i64m n)]⌝ ∗
                   ⌜repr_double_word heap_start θ (WordInt n1) (WordInt n2) n⌝) ∗
             gc_token heap_start inv m θ ∗ ℓ ↦obj obj ∗ ↪[RUN] ∗ ↪[frame] F }}.
  Admitted.

  Lemma wp_store_i32_gc
      (s : stuckness) (E : coPset) (F : frame) (memidx : immediate)
      (m : memaddr) (θ : address_map) (inv : gc_invariant Σ)
      (i k : i32) (ℓ : location) (obj : object)
      (j : nat) (off : static_offset) (w : word) :
    F.(f_inst).(inst_memory) !! memidx = Some m ->
    repr_location_index θ ℓ j (Wasm_int.Z_of_uint i32m i + Z.of_N off) ->
    j < length obj ->
    repr_word heap_start θ w (Wasm_int.Z_of_uint i32m k) ->
    gc_token heap_start inv m θ ∗ ℓ ↦obj obj ∗ ↪[RUN] ∗ ↪[frame] F ⊢
    WP [AI_basic (BI_const (VAL_int32 i));
        AI_basic (BI_const (VAL_int32 k));
        AI_basic (BI_store memidx T_i32 None N.zero off)]
       @ s; E
       {{ v, ⌜v = immV []⌝ ∗
             gc_token heap_start inv m θ ∗
             ℓ ↦obj <[ j := w ]> obj ∗
             ↪[RUN] ∗ ↪[frame] F }}.
  Admitted.

  Definition spec_registerroot
      (E : coPset) (inv : gc_invariant Σ) (m : memaddr)
      (finst : instance) (fid : nat) (fts : list value_type) (fes : list basic_instruction)
      : iProp Σ :=
    □ ∀ (F : frame) (θ : address_map) (ℓ : location) (i : i32),
    gc_token heap_start inv m θ ∗ ⌜repr_location_index θ ℓ 0 (Wasm_int.Z_of_uint i32m i)⌝ ∗
    N.of_nat fid ↦[wf] FC_func_native finst (Tf [T_i32] [T_i32]) fts fes ∗ ↪[RUN] ∗ ↪[frame] F -∗
    WP [AI_basic (BI_const (VAL_int32 i)); AI_invoke fid]
       @ E
       {{ v, (⌜v = trapV⌝ ∨
              ∃ n,
              ⌜v = immV [VAL_int32 n]⌝ ∗
              Wasm_int.N_of_uint i32m n ↦root ℓ ∗
              gc_token heap_start inv m θ ∗
              N.of_nat fid ↦[wf] FC_func_native finst (Tf [T_i32] [T_i32]) fts fes) ∗
             ↪[RUN] ∗ ↪[frame] F }}%I.

  Definition spec_unregisterroot
      (E : coPset) (inv : gc_invariant Σ) (m : memaddr)
      (finst : instance) (fid : nat) (fts : list value_type) (fes : list basic_instruction)
      : iProp Σ :=
    □ ∀ (F : frame) (θ : address_map) (n : i32) (ℓ : location),
    gc_token heap_start inv m θ ∗ Wasm_int.N_of_uint i32m n ↦root ℓ ∗
    N.of_nat fid ↦[wf] FC_func_native finst (Tf [T_i32] [T_i32]) fts fes ∗ ↪[frame] F -∗
    WP [AI_basic (BI_const (VAL_int32 n)); AI_invoke fid]
       @ E
       {{ v, ∃ n,
          ⌜v = immV [VAL_int32 (Wasm_int.int_of_Z i32m n)]⌝ ∗
          ⌜repr_location_index θ ℓ 0 n⌝ ∗
          gc_token heap_start inv m θ ∗
          N.of_nat fid ↦[wf] FC_func_native finst (Tf [T_i32] [T_i32]) fts fes ∗
          ↪[RUN] ∗ ↪[frame] F }}%I.

  (* TODO: wp_loadroot *)

  (* TODO: wp_duproot *)

End Rules.
