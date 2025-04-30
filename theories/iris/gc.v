From mathcomp Require Import eqtype.
From iris.proofmode Require Import base tactics classes.
From Wasm.iris.rules Require Import iris_rules.

Set Bullet Behavior "Strict Subproofs".

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

Definition code_int (z : Z) : i32 :=
  Wasm_int.int_of_Z i32m (2 * z + 1).

Definition code_addr (a : addr) : i32 :=
  Wasm_int.int_of_Z i32m (Z.of_N a).

Definition serialize_i32s (l : list i32) : bytes :=
  flat_map serialise_i32 l.

Definition serialize_nat_32 (n : nat) : bytes :=
  serialise_i32 (Wasm_int.int_of_Z i32m (Z.of_nat n)).

Inductive repr_vval : addr_map -> vval -> i32 -> Prop :=
  | RVint θ z :
      repr_vval θ (Vint z) (code_int z)
  | RVloc θ ℓ a :
      θ !! ℓ = Some a ->
      (Z.of_N a < Wasm_int.Int32.modulus)%Z ->
      repr_vval θ (Vloc ℓ) (code_addr a).

Inductive repr_vblock : addr_map -> vblock -> list i32 -> Prop :=
  | RVblock θ blk ks :
      length ks = length blk.(vals) ->
      Forall (curry (repr_vval θ)) (combine blk.(vals) ks) ->
      repr_vblock θ blk ks.

Definition vblock_offset (i : nat) : N := N.of_nat (4 * i).

Inductive repr_vloc_offset : addr_map -> vloc -> nat -> i32 -> Prop :=
  | RVloc_offset θ ℓ i a a' :
      θ !! ℓ = Some a ->
      a' = (a + vblock_offset i)%N ->
      (Z.of_N a' < Wasm_int.Int32.modulus)%Z ->
      repr_vloc_offset θ ℓ i (code_addr a').

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
  (at level 20, format "ℓ  ↦vblk  b") : bi_scope.

Notation "a ↦root{ dq } u" := (a ↪[gcG_roots]{dq} u)%I
  (at level 20, format "a ↦root{ dq } u") : bi_scope.
Notation "a ↦root u" := (a ↪[gcG_roots] u)%I
  (at level 20, format "a  ↦root  u") : bi_scope.

Section GCtoken.

Context `{wasmG Σ}.
Context `{rwasm_gcG Σ}.

Definition GC (m : memaddr) (θ : addr_map) : iProp Σ :=
  ∃ (ζ : vstore) (roots : gmap addr vval),
  ghost_map_auth gcG_vstore 1 ζ ∗
  ghost_map_auth gcG_roots 1 roots ∗
  ([∗ map] ℓ ↦ a; blk ∈ θ; ζ, ∃ bs ks, N.of_nat m ↦[wms][a] bs ∗ ⌜bs = serialize_i32s ks⌝ ∗ ⌜repr_vblock θ blk ks⌝) ∗
  ([∗ map] a ↦ vv ∈ roots, ∃ bs k, N.of_nat m ↦[wms][a] bs ∗ ⌜bs = serialise_i32 k⌝ ∗ ⌜repr_vval θ vv k⌝) ∗
  ⌜roots_are_live θ roots⌝ ∗
  ⌜GC_correct ζ θ⌝.

End GCtoken.

Section GCrules.

Context `{wasmG Σ}.
Context `{rwasm_gcG Σ}.

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
  exists l1 x l2, l !! i = Some x /\ length l1 = i /\ l = l1 ++ x :: l2.
Admitted.

Lemma repr_vblock_index : forall θ blk u ks i,
  blk.(vals) !! i = Some u ->
  repr_vblock θ blk ks ->
  exists w, repr_vval θ u w /\ ks !! i = Some w.
Proof.
  intros θ blk u ks i Hi Hblk. inversion Hblk. subst.
  assert (exists w, In (u, w) (combine (vals blk) ks)).
  - admit.
  - destruct H3 as [w Hw].
    exists w. split.
    + change (repr_vval θ u w) with (curry (repr_vval θ) (u, w)).
      eapply List.Forall_forall.
      * exact H2.
      * assumption.
    + admit.
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

(* TODO: wp_alloc_gc *)

Lemma wp_load_gc
    (s : stuckness) (E : coPset) (m : memaddr) (θ : addr_map)
    (i : i32) (ℓ : vloc) (blk : vblock)
    (off1 off2 : nat) (off2b : static_offset) (vv : vval)
    (F : frame) :
  F.(f_inst).(inst_memory) !! 0 = Some m ->
  repr_vloc_offset θ ℓ off1 i ->
  blk.(vals) !! (off1 + off2) = Some vv ->
  vblock_offset off2 = off2b ->
  GC m θ ∗ ℓ ↦vblk blk ∗ ↪[frame] F ⊢
  WP [AI_basic (BI_const (VAL_int32 i)); AI_basic (BI_load T_i32 None N.zero off2b)]
     @ s; E
     {{ w, (∃ k, ⌜w = immV [VAL_int32 k]⌝ ∗ ⌜repr_vval θ vv k⌝) ∗
           GC m θ ∗ ℓ ↦vblk blk ∗ ↪[frame] F }}.
Proof.
  iIntros (Em Hk Eu Hoff) "(HGC & Hℓ & HF)".
  iDestruct "HGC" as (ζ roots) "(Hζ & Hroots & Hζmem & Hrootsmem & %Hlive & %GCOK)".
  inversion Hk as [θ' ℓ' off1' a a' Eθℓ Ea' Ha32 Eθ' Eℓ' Eoff1' Ei]. subst.
  iDestruct (ghost_map_lookup with "Hζ Hℓ") as "%Eζℓ".
  iDestruct (big_sepM2_lookup_acc _ _ _ _ _ _ Eθℓ Eζℓ with "Hζmem") as "[(%bs & %ws & Ha & %Hbs & %Hws) Hζmem]".
  inversion Hws as [θ' blk' vbs Hwslen Hvals Evbs Eθ' Ews]. subst.
  pose proof (lookup_lt_Some _ _ _ Eu) as Hilt. rewrite <- Hwslen in Hilt.
  destruct (list_pluck _ _ _ Hilt) as [ws1 [wsi [ws2 [Hwsi [Hws1len Ews]]]]]. rewrite Ews.
  (* wsi = w *)
  destruct (repr_vblock_index θ blk vv ws (off1 + off2) Eu Hws) as [w [Huw Hwi]].
  assert (w = wsi) by congruence. subst wsi.
  unfold serialize_i32s.
  rewrite flat_map_app. rewrite (separate1 w). rewrite flat_map_app. simpl. rewrite app_nil_r.
  rewrite (wms_app _ _ _ (vblock_offset (off1 + off2))). rewrite (wms_app _ (serialise_i32 w) _ 4).
  iDestruct "Ha" as "(Ha1 & Hai & Ha2)".
  (* add the loaded wms into the postcondition *)
  iApply (wp_wand _ _ _ (λ w0, ((∃ w', ⌜w0 = immV [VAL_int32 w']⌝ ∗ ⌜repr_vval θ vv w'⌝) ∗
  N.of_nat m ↦[wms][Wasm_int.N_of_uint i32m (code_addr (a + vblock_offset off1)) + vblock_offset off2] serialise_i32 w) ∗
                               ↪[frame] F)%I
          with "[HF Hai] [Hζ Hroots Hrootsmem Hℓ Ha1 Ha2 Hζmem]").
  - iApply wp_load_deserialize.
    + unfold serialise_i32. rewrite Memdata.encode_int_length. reflexivity.
    + assumption.
    + unfold code_addr. rewrite deserialise_serialise_i32. cbn.
      rewrite Wasm_int.Int32.Z_mod_modulus_id.
      * rewrite N2Z.id. replace (vblock_offset (off1 + off2)) with ((vblock_offset off1 + vblock_offset off2)%N).
        -- rewrite N.add_assoc. iFrame. by iExists w.
        -- unfold vblock_offset. lia.
      * lia.
  - iIntros (v) "[[HΦ Hai] HF]". iFrame "∗ %". iCombine "Ha1 Hai" as "Ha1".
    unfold code_addr. cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; last lia. rewrite N2Z.id.
    rewrite <- (N.add_assoc _ (vblock_offset off1) _). rewrite <- wms_app; last first.
    { rewrite (@flat_map_constant_length _ _ 4).
      - rewrite Hws1len. unfold vblock_offset. lia.
      - intros x Hx. unfold serialise_i32. rewrite Memdata.encode_int_length. reflexivity. }
    iCombine "Ha1 Ha2" as "Ha". rewrite <- N.add_assoc. rewrite <- wms_app; last first.
    { rewrite length_app. rewrite (@flat_map_constant_length _ _ 4).
      - rewrite Hws1len. unfold serialise_i32. rewrite Memdata.encode_int_length. unfold vblock_offset. lia.
      - intros x Hx. unfold serialise_i32. rewrite Memdata.encode_int_length. reflexivity. }
    replace (serialise_i32 w) with (flat_map serialise_i32 [w]) by (rewrite <- flat_map_singleton; reflexivity).
    rewrite <- !flat_map_app. rewrite <- app_assoc. rewrite <- separate1. rewrite <- Ews.
    iAssert ⌜repr_vblock θ blk ws⌝%I as "Hws".
    { done. }
    iApply "Hζmem". iExists (flat_map serialise_i32 ws), _. iFrame. auto.
  - unfold serialise_i32. rewrite Memdata.encode_int_length. reflexivity.
  - unfold vblock_offset. rewrite (@flat_map_constant_length _ _ 4).
    + rewrite Hws1len. lia.
    + intros x Hx. unfold serialise_i32. rewrite Memdata.encode_int_length. reflexivity.
Qed.

Lemma wp_store_gc
    (s : stuckness) (E : coPset) (m : memaddr) (θ : addr_map)
    (i k : i32) (ℓ : vloc) (blk blk' : vblock)
    (off1 off2 : nat) (off2b : static_offset) (vv : vval)
    (F : frame) :
  F.(f_inst).(inst_memory) !! 0 = Some m ->
  repr_vloc_offset θ ℓ off1 i ->
  vblock_offset off2 = off2b ->
  off1 + off2 < length blk.(vals) ->
  repr_vval θ vv k ->
  blk' = Build_vblock blk.(tag) (<[ off1 + off2 := vv ]> blk.(vals)) ->
  GC m θ ∗ ℓ ↦vblk blk ∗ ↪[frame] F ⊢
  WP [AI_basic (BI_const (VAL_int32 i));
      AI_basic (BI_const (VAL_int32 k));
      AI_basic (BI_store T_i32 None N.zero off2b)]
     @ s; E
     {{ w, ⌜w = immV []⌝ ∗ GC m θ ∗ ℓ ↦vblk blk' ∗ ↪[frame] F }}.
Admitted.

(* TODO: wp_registerroot_gc *)
(* TODO: wp_unregisterroot_gc *)

End GCrules.
