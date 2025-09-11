From mathcomp Require Import eqtype.
From stdpp Require Import gmap.
From iris.proofmode Require Import base tactics classes.
From RichWasm.iris.rules Require Import iris_rules proofmode.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Definition gmap_injective `{Countable K} {V} (m : gmap K V) :=
  ∀ k1 k2 v, m !! k1 = Some v -> m !! k2 = Some v -> k1 = k2.

Section Model.

  Variable heap_start : N.

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

  Record object_layout :=
    { ol_prefix : list word_kind;
      ol_element : list word_kind;
      ol_count : nat }.

  Definition layout_map : Type := gmap location object_layout.

  Definition address_map : Type := gmap location address.

  Definition root_map : Type := gmap address location.

  Definition object_map : Type := gmap location (list word).

  Definition gc_invariant (Σ : gFunctors) : Type := layout_map -> object_map -> root_map -> iProp Σ.

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
  | ReprPtrInt θ n :
    repr_pointer θ (PtrInt n) (2 * n + 1)
  | ReprPtrMM θ a :
    (a `mod` 4 = 0)%N ->
    repr_pointer θ (PtrMM a) (Z.of_N a)
  | ReprPtrGC θ ℓ a :
    θ !! ℓ = Some a ->
    (a `mod` 4 = 0)%N ->
    (a >= heap_start)%N ->
    repr_pointer θ (PtrGC ℓ) (Z.of_N (a + 2))
  | ReprPtrRoot θ a :
    (a `mod` 4 = 0)%N ->
    (a < heap_start)%N ->
    repr_pointer θ (PtrRoot a) (Z.of_N (a + 2)).

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

  Definition repr_list_word (θ : address_map) (ws : list word) (ns : list Z) : Prop :=
    Forall2 (repr_word θ) ws ns.

  Inductive repr_location_index : address_map -> location -> nat -> Z -> Prop :=
  | ReprLocElem θ ℓ i a0 a :
    θ !! ℓ = Some a0 ->
    a = Z.of_N (a0 + index_address i) ->
    repr_location_index θ ℓ i a.

  Class RichWasmGCG (Σ : gFunctors) :=
    { gc_layouts : gname;
      gc_layouts_G :: ghost_mapG Σ location object_layout;
      gc_objects : gname;
      gc_objects_G :: ghost_mapG Σ location (list word);
      gc_roots : gname;
      gc_roots_G :: ghost_mapG Σ address location }.

End Model.

Notation "ℓ ↦gcl{ q } l" :=
  (ℓ ↪[gc_layouts]{q} l)%I (at level 20, format "ℓ  ↦gcl{ q }  l") : bi_scope.

Notation "ℓ ↦gcl l" := (ℓ ↪[gc_layouts] l)%I (at level 20, format "ℓ  ↦gcl  l") : bi_scope.

Notation "ℓ ↦gco{ q } ws" :=
  (ℓ ↪[gc_objects]{q} ws)%I (at level 20, format "ℓ  ↦gco{ q }  ws") : bi_scope.

Notation "ℓ ↦gco ws" := (ℓ ↪[gc_objects] ws)%I (at level 20, format "ℓ  ↦gco  ws") : bi_scope.

Notation "a ↦gcr{ q } ℓ" :=
  (a ↪[gc_roots]{q} ℓ)%I (at level 20, format "a  ↦gcr{ q }  ℓ") : bi_scope.

Notation "a ↦gcr ℓ" := (a ↪[gc_roots] ℓ)%I (at level 20, format "a  ↦gcr  ℓ") : bi_scope.

Section Token.

  Context `{wasmG Σ}.
  Context `{RichWasmGCG Σ}.

  Variable heap_start : N.

  Definition consistent_objects_memory (m : memaddr) (θ : address_map) (wss : object_map) : iProp Σ :=
    [∗ map] ℓ ↦ a; ws ∈ θ; wss,
    ∃ bs ns,
    N.of_nat m ↦[wms][a] bs ∗
    ⌜bs = flat_map serialize_Z_i32 ns⌝ ∗
    ⌜repr_list_word heap_start θ ws ns⌝.

  Definition consistent_roots_memory (m : memaddr) (θ : address_map) (rs : root_map) : iProp Σ :=
    [∗ map] a ↦ ℓ ∈ rs,
    ∃ bs n,
    N.of_nat m ↦[wms][a] bs ∗
    ⌜bs = serialize_Z_i32 n⌝ ∗
    ⌜repr_location_index θ ℓ 0 n⌝.

  Definition consistent_objects_layouts (ls : layout_map) (wss : object_map) : Prop :=
    map_Forall
      (fun ℓ '(l, ws) =>
         length ws =? length l.(ol_prefix) + l.(ol_count) * length l.(ol_element) /\
           Forall (curry word_has_kind) (combine (concat (repeat l.(ol_element) l.(ol_count))) ws))
      (map_zip ls wss).

  Definition consistent_reachable_addresses (wss : object_map) (θ : address_map) : Prop :=
    gmap_injective θ /\
    ∀ ℓ ℓ' ws,
    ℓ ∈ dom θ ->
    wss !! ℓ = Some ws ->
    WordPtr (PtrGC ℓ') ∈ ws ->
    ℓ' ∈ dom θ.

  Definition live_roots (θ : address_map) (rs : root_map) : Prop :=
    ∀ a ℓ, rs !! a = Some ℓ -> ℓ ∈ dom θ.

  Definition gc_token (inv : gc_invariant Σ) (m : memaddr) (θ : address_map) : iProp Σ :=
    ∃ (ls : layout_map) (wss : object_map) (rs : root_map),
    inv ls wss rs ∗
    ghost_map_auth gc_layouts (1/2) ls ∗
    ghost_map_auth gc_objects 1 wss ∗
    ghost_map_auth gc_roots (1/2) rs ∗
    consistent_objects_memory m θ wss ∗
    consistent_roots_memory m θ rs ∗
    ⌜consistent_objects_layouts ls wss⌝ ∗
    ⌜consistent_reachable_addresses wss θ⌝ ∗
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
    let l :=
      {| ol_prefix := kinds_of_pointer_map prefix_map (Wasm_int.nat_of_uint i32m prefix_sz);
         ol_count := Wasm_int.nat_of_uint i32m count;
         ol_element := kinds_of_pointer_map elem_map (Wasm_int.nat_of_uint i32m elem_sz) |}
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
              ∃ θ' ℓ n ws,
              ⌜v = immV [VAL_int32 (Wasm_int.int_of_Z i32m n)]⌝ ∗ ⌜repr_location_index θ' ℓ 0 n⌝ ∗
              gc_token heap_start inv m θ' ∗ ℓ ↦gcl l ∗ ℓ ↦gco ws ∗
              alloc_gc_func) ∗
             ↪[frame] F }}%I.

  (* TODO: What would happen if the ∃ k was pulled up to a lemma parameter, and
   * repr_vval θ vv k was an assumption? *)
  Lemma wp_load_i32_gc
      (s : stuckness) (E : coPset) (F : frame) (memidx : immediate)
      (m : memaddr) (θ : address_map) (inv : gc_invariant Σ)
      (i : i32) (ℓ : location) (ws : list word)
      (j : nat) (off : static_offset) (w : word) :
    F.(f_inst).(inst_memory) !! memidx = Some m ->
    repr_location_index θ ℓ j (Wasm_int.Z_of_uint i32m i + Z.of_N off) ->
    ws !! j = Some w ->
    gc_token heap_start inv m θ ∗ ℓ ↦gco ws ∗ ↪[frame] F ∗ ↪[RUN] ⊢
    WP [AI_basic (BI_const (VAL_int32 i)); AI_basic (BI_load memidx T_i32 None N.zero off)]
       @ s; E
       {{ v, (∃ n, ⌜v = immV [VAL_int32 (Wasm_int.int_of_Z i32m n)]⌝ ∗ ⌜repr_word heap_start θ w n⌝) ∗
             gc_token heap_start inv m θ ∗ ℓ ↦gco ws ∗ ↪[RUN] ∗ ↪[frame] F }}.
  Admitted.

  Lemma wp_load_i64_gc
      (s : stuckness) (E : coPset) (F : frame) (memidx : immediate)
      (m : memaddr) (θ : address_map) (inv : gc_invariant Σ)
      (i : i32) (ℓ : location) (ws : list word)
      (j : nat) (off : static_offset) (n1 n2 : Z) :
    F.(f_inst).(inst_memory) !! memidx = Some m ->
    repr_location_index θ ℓ j (Wasm_int.Z_of_uint i32m i + Z.of_N off) ->
    ws !! j = Some (WordInt n1) ->
    ws !! (j + 1) = Some (WordInt n2) ->
    gc_token heap_start inv m θ ∗ ℓ ↦gco ws ∗ ↪[RUN] ∗ ↪[frame] F ⊢
    WP [AI_basic (BI_const (VAL_int32 i)); AI_basic (BI_load memidx T_i64 None N.zero off)]
       @ s; E
       {{ v, (∃ n, ⌜v = immV [VAL_int64 (Wasm_int.int_of_Z i64m n)]⌝ ∗
                   ⌜repr_double_word heap_start θ (WordInt n1) (WordInt n2) n⌝) ∗
             gc_token heap_start inv m θ ∗ ℓ ↦gco ws ∗ ↪[RUN] ∗ ↪[frame] F }}.
  Admitted.

  Lemma wp_store_i32_gc
      (s : stuckness) (E : coPset) (F : frame) (memidx : immediate)
      (m : memaddr) (θ : address_map) (inv : gc_invariant Σ)
      (i k : i32) (ℓ : location) (ws : list word)
      (j : nat) (off : static_offset) (w : word) :
    F.(f_inst).(inst_memory) !! memidx = Some m ->
    repr_location_index θ ℓ j (Wasm_int.Z_of_uint i32m i + Z.of_N off) ->
    j < length ws ->
    repr_word heap_start θ w (Wasm_int.Z_of_uint i32m k) ->
    gc_token heap_start inv m θ ∗ ℓ ↦gco ws ∗ ↪[RUN] ∗ ↪[frame] F ⊢
    WP [AI_basic (BI_const (VAL_int32 i));
        AI_basic (BI_const (VAL_int32 k));
        AI_basic (BI_store memidx T_i32 None N.zero off)]
       @ s; E
       {{ v, ⌜v = immV []⌝ ∗
             gc_token heap_start inv m θ ∗
             ℓ ↦gco <[ j := w ]> ws ∗
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
              Wasm_int.N_of_uint i32m n ↦gcr ℓ ∗
              gc_token heap_start inv m θ ∗
              N.of_nat fid ↦[wf] FC_func_native finst (Tf [T_i32] [T_i32]) fts fes) ∗
             ↪[RUN] ∗ ↪[frame] F }}%I.

  Definition spec_unregisterroot
      (E : coPset) (inv : gc_invariant Σ) (m : memaddr)
      (finst : instance) (fid : nat) (fts : list value_type) (fes : list basic_instruction)
      : iProp Σ :=
    □ ∀ (F : frame) (θ : address_map) (n : i32) (ℓ : location),
    gc_token heap_start inv m θ ∗ Wasm_int.N_of_uint i32m n ↦gcr ℓ ∗
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
