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
| PtrHeap (μ : smemory) (ℓ : location).

Inductive root_pointer :=
| RootInt (n : Z)
| RootHeap (μ : smemory) (a : address).

Inductive rep_value :=
| PtrV (r : pointer)
| I32V (n : i32)
| I64V (n : i64)
| F32V (n : f32)
| F64V (n : f64).

Inductive word :=
| WordPtr (p : pointer)
| WordInt (n : Z).

Definition address_map : Type := gmap location (smemory * address).
Definition root_map : Type := gmap address location.
Definition layout_map : Type := gmap location (list pointer_flag).
Definition heap_map : Type := gmap location (list word).

Definition rt_invariant (Σ : gFunctors) : Type :=
  address_map -> root_map -> layout_map -> iProp Σ.

Class richwasmG (Σ : gFunctors) :=
  { rw_addr : gname;
    rw_addrG :: ghost_mapG Σ location (smemory * address);
    rw_root : gname;
    rw_rootG :: ghost_mapG Σ address location;
    rw_layout : gname;
    rw_layoutG :: ghost_mapG Σ location (list pointer_flag);
    rw_heap : gname;
    rw_heapG :: ghost_mapG Σ location (list word) }.

Notation "ℓ ↦addr{ q } a" :=
  (ℓ ↪[rw_addr]{q} a)%I (at level 20, format "ℓ  ↦addr{ q }  a") : bi_scope.
Notation "ℓ ↦addr a" := (ℓ ↪[rw_addr] a)%I (at level 20, format "ℓ  ↦addr  a") : bi_scope.

Notation "a ↦root{ q } ℓ" :=
  (a ↪[rw_root]{q} ℓ)%I (at level 20, format "a  ↦root{ q }  ℓ") : bi_scope.
Notation "a ↦root ℓ" := (a ↪[rw_root] ℓ)%I (at level 20, format "a  ↦root  ℓ") : bi_scope.

Notation "ℓ ↦layout{ q } fs" :=
  (ℓ ↪[rw_layout]{q} fs)%I (at level 20, format "ℓ  ↦layout{ q }  fs") : bi_scope.
Notation "ℓ ↦layout fs" := (ℓ ↪[rw_layout] fs)%I (at level 20, format "ℓ  ↦layout  fs") : bi_scope.

Notation "ℓ ↦heap{ q } ws" :=
  (ℓ ↪[rw_heap]{q} ws)%I (at level 20, format "ℓ  ↦heap{ q }  ws") : bi_scope.
Notation "ℓ ↦heap ws" := (ℓ ↪[rw_heap] ws)%I (at level 20, format "ℓ  ↦heap  ws") : bi_scope.

Definition word_has_flag (f : pointer_flag) (w : word) : bool :=
  match f, w with
  | FlagPtr, WordPtr _ => true
  | FlagInt, WordInt _ => true
  | _, _ => false
  end.

Definition tag_address (μ : smemory) (a : address) : Z :=
  match μ with
  | MemMM => Z.of_N a - 3
  | MemGC => Z.of_N a - 1
  end.

Definition index_address (i : nat) : N := N.of_nat (4 * i).

Inductive repr_pointer : address_map -> pointer -> Z -> Prop :=
| ReprPtrInt θ n :
  repr_pointer θ (PtrInt n) (2 * n)
| RepPtrHeap θ ℓ μ a :
  θ !! ℓ = Some (μ, a) ->
  (a `mod` 4 = 0)%N ->
  repr_pointer θ (PtrHeap μ ℓ) (tag_address μ a).

Inductive repr_root_pointer : root_pointer -> Z -> Prop :=
| ReprRootInt n :
  repr_root_pointer (RootInt n) (2 * n)
| ReprRootHeap μ a :
  (a `mod` 4 = 0)%N ->
  repr_root_pointer (RootHeap μ a) (tag_address μ a).

Definition rep_serialize (rv : rep_value) : list word :=
  match rv with
  | PtrV p => [WordPtr p]
  | I32V n => [WordInt (Wasm_int.Z_of_uint i32m n)]
  | I64V n =>
      let n' := Wasm_int.Z_of_uint i64m n in
      [WordInt (Wasm_int.Int32.Z_mod_modulus n'); WordInt (n' ≫ 32)%Z]
  | F32V n => [WordInt (Integers.Int.intval (Wasm_float.FloatSize32.to_bits n))]
  | F64V n =>
      let n' := Integers.Int64.intval (Wasm_float.FloatSize64.to_bits n) in
      [WordInt (Wasm_int.Int32.Z_mod_modulus n'); WordInt (n' ≫ 32)%Z]
  end.

Section Token.

  Context `{wasmG Σ}.
  Context `{richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.

  Definition word_interp (θ : address_map) (μ : smemory) (w : word) (n : Z) : iProp Σ :=
    match w with
    | WordInt m => ⌜n = m⌝
    | WordPtr p =>
        match μ, p with
        | MemMM, PtrHeap MemGC ℓ => ∃ a, ⌜repr_root_pointer (RootHeap MemGC a) n⌝ ∗ a ↦root ℓ
        | _, _ => ⌜repr_pointer θ p n⌝
        end
    end.

  Definition locations (w : word) : list location :=
    match w with
    | WordInt _
    | WordPtr (PtrInt _) => []
    | WordPtr (PtrHeap _ ℓ) => [ℓ]
    end.

  Definition rt_memaddr (μ : smemory) : N :=
    match μ with
    | MemMM => N.of_nat sr.(sr_mem_mm)
    | MemGC => N.of_nat sr.(sr_mem_gc)
    end.

  Definition own_addr_gc (θ : address_map) : iProp Σ :=
    [∗ map] ℓ ↦ '(μ, a) ∈ θ, ⌜μ = MemGC⌝ -∗ ℓ ↦addr (MemGC, a).

  Definition own_addr_mm (θ : address_map) (hm : heap_map) : iProp Σ :=
    [∗ map] '_ ↦ ws ∈ hm,
      [∗ list] ℓ ∈ flat_map locations ws,
        ∃ a, ⌜θ !! ℓ = Some (MemMM, a)⌝ -∗ ℓ ↦addr (MemMM, a).

  Definition root_ok (θ : address_map) : root_map -> Prop :=
    map_Forall (fun _ ℓ => exists a, θ !! ℓ = Some (MemGC, a)).

  Definition root_memory (θ : address_map) (rm : root_map) : iProp Σ :=
    [∗ map] ar ↦ ℓ ∈ rm,
      ∃ bs ah,
        ⌜θ !! ℓ = Some (MemGC, Z.to_N ah)⌝ ∗
          ⌜repr_pointer θ (PtrHeap MemGC ℓ) ah⌝ ∗
          ⌜bs = serialize_Z_i32 ah⌝ ∗
          N.of_nat sr.(sr_mem_gc) ↦[wms][ar] bs.

  Definition heap_ok (θ : address_map) (lm : layout_map) (hm : heap_map) : Prop :=
    map_Forall2 (const (Forall2 word_has_flag)) lm hm /\
      map_Forall (fun ℓ => Forall (fun ℓ' => ℓ' ∈ dom hm) ∘ flat_map locations) hm /\
      map_Forall2 (fun ℓ _ => Forall (fun ℓ' => ℓ' ∈ dom θ) ∘ flat_map locations) θ hm.

  Definition heap_memory (θ : address_map) (hm : heap_map) : iProp Σ :=
    [∗ map] ℓ ↦ '(μ, a); ws ∈ θ; hm,
      ∃ bs ns,
        rt_memaddr μ ↦[wms][a] bs ∗
          ⌜bs = flat_map serialize_Z_i32 ns⌝ ∗
          big_sepL2 (const (word_interp θ μ)) ws ns.

  Definition rt_token (θ : address_map) : iProp Σ :=
    ∃ rm lm hm,
      ghost_map_auth rw_addr (1/2) θ ∗
        ghost_map_auth rw_root (1/2) rm ∗
        ghost_map_auth rw_layout (1/2) lm ∗
        ghost_map_auth rw_heap 1 hm ∗
        rti θ rm lm ∗
        ⌜gmap_injective θ⌝ ∗
        own_addr_mm θ hm ∗
        own_addr_gc θ ∗
        ⌜root_ok θ rm⌝ ∗
        root_memory θ rm ∗
        ⌜heap_ok θ lm hm⌝ ∗
        heap_memory θ hm.

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

  (* TODO: wp_load_i32 *)
  (* TODO: wp_load_i64 *)
  (* TODO: wp_store_i32 *)
  (* TODO: wp_loadroot *)
  (* TODO: wp_duproot *)

End Rules.
