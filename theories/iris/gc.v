From mathcomp Require Import eqtype.
From iris.proofmode Require Import base tactics classes.
From Wasm.iris.host Require Import iris_host.
From Wasm.iris.rules Require Import iris_rules proofmode.

Set Bullet Behavior "Strict Subproofs".

Notation vloc := nat (only parsing).

Notation addr := N (only parsing).

Inductive vptr :=
  | gcVP : vloc -> vptr
  | mmVP : addr -> vptr.

Inductive vval :=
  | intVV : Z -> vval
  | ptrVV : vptr -> vval.

Inductive vkind :=
  | ptrVK
  | nonptrVK.

Definition has_vkind (vk : vkind) (vv : vval) : Prop :=
  match vk, vv with
  | ptrVK, ptrVV _ => True
  | nonptrVK, intVV _ => True
  | _, _ => False
  end.

Definition ptrmap_to_vkinds (ptrmap : i64) (size : nat) : list vkind :=
  map (fun b : bool => if b then ptrVK else nonptrVK)
      (take size (reverse (Wasm_int.Int64.convert_to_bits ptrmap))).

Record vheader := {
  count : nat;
  elem : list vkind;
}.

Notation vblock := (list vval).

Notation vinfo := (gmap vloc vheader).

Notation vstore := (gmap vloc vblock).

Notation addr_map := (gmap vloc addr).

Notation root_map := (gmap addr vloc).

Notation gc_inv Σ := (vinfo -> vstore -> root_map -> iProp Σ).

Definition serialize_z (i : Z) : bytes :=
  serialise_i32 (Wasm_int.int_of_Z i32m i).

Definition serialize_zs (l : list Z) : bytes :=
  flat_map serialize_z l.

Inductive repr_vptr : addr_map -> vptr -> Z -> Prop :=
  | gcptrR θ ℓ a :
      θ !! ℓ = Some a ->
      (a `mod` 2 = 0)%N ->
      repr_vptr θ (gcVP ℓ) (Z.of_N (a + 1))
  | mmptrR θ a :
      (a `mod` 2 = 0)%N ->
      repr_vptr θ (mmVP a) (Z.of_N a).

Inductive repr_vval : addr_map -> vval -> Z -> Prop :=
  | intR θ i :
      repr_vval θ (intVV i) i
  | vptrR θ vp i :
      repr_vptr θ vp i ->
      repr_vval θ (ptrVV vp) i.

Inductive repr_vblock : addr_map -> vblock -> list Z -> Prop :=
  | vblockR θ blk ks :
      length ks = length blk ->
      Forall (curry (repr_vval θ)) (combine blk ks) ->
      repr_vblock θ blk ks.

Definition vblock_offset (i : nat) : N := N.of_nat (4 * i).

Inductive repr_vloc : addr_map -> vloc -> nat -> Z -> Prop :=
  | vlocR θ ℓ i a a' :
      θ !! ℓ = Some a ->
      a' = Z.of_N (a + vblock_offset i) ->
      repr_vloc θ ℓ i a'.

Class rwasm_gcG Σ := Rwasm_gcG {
  gcG_vinfoG :: ghost_mapG Σ vloc vheader;
  gcG_vstoreG :: ghost_mapG Σ vloc vblock;
  gcG_rootsG :: ghost_mapG Σ addr vloc;
  gcG_vinfo : gname;
  gcG_vstore : gname;
  gcG_roots : gname;
}.

Notation "ℓ ↦vhdr{ dq } b" := (ℓ ↪[gcG_vinfo]{dq} b)%I
  (at level 20, format "ℓ ↦vhdr{ dq } b") : bi_scope.
Notation "ℓ ↦vhdr b" := (ℓ ↪[gcG_vinfo] b)%I
  (at level 20, format "ℓ  ↦vhdr  b") : bi_scope.

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

Definition blocks_match_memory (m : memaddr) (θ : addr_map) (ζ : vstore) : iProp Σ :=
  [∗ map] ℓ ↦ a; blk ∈ θ; ζ, ∃ bs zs,
  N.of_nat m ↦[wms][a] bs ∗
  ⌜bs = serialize_zs zs⌝ ∗
  ⌜repr_vblock θ blk zs⌝.

Definition roots_match_memory (m : memaddr) (θ : addr_map) (roots : root_map) : iProp Σ :=
  [∗ map] a ↦ ℓ ∈ roots, ∃ bs z,
  N.of_nat m ↦[wms][a] bs ∗
  ⌜bs = serialize_z z⌝ ∗
  ⌜repr_vloc θ ℓ 0 z⌝.

Definition headers_match_blocks (info : vinfo) (ζ : vstore) : Prop :=
  map_Forall
    (fun ℓ '(hdr, blk) =>
       length blk =? hdr.(count) * length hdr.(elem) /\
       Forall (curry has_vkind) (combine (concat (repeat hdr.(elem) hdr.(count))) blk))
    (map_zip info ζ).

Definition roots_live (θ : addr_map) (roots : gmap addr vloc) : Prop :=
  ∀ a ℓ, roots !! a = Some ℓ -> ℓ ∈ dom θ.

Definition gmap_inj `{Countable K} {V} (m : gmap K V) :=
  ∀ k1 k2 v, m !! k1 = Some v -> m !! k2 = Some v -> k1 = k2.

Definition reachability_ok (ζ : vstore) (θ : addr_map) : Prop :=
  gmap_inj θ /\
  ∀ ℓ blk ℓ',
  ℓ ∈ dom θ ->
  ζ !! ℓ = Some blk ->
  ptrVV (gcVP ℓ') ∈ blk ->
  ℓ' ∈ dom θ.

(* This should be defined as part of runtime module instantiation and be opaque to clients. *)
Definition GC_inv (m : memaddr) (info : vinfo) (roots : root_map) : iProp Σ :=
  ghost_map_auth gcG_vinfo (1/2) info ∗
  ghost_map_auth gcG_roots (1/2) roots ∗
  ∃ len, N.of_nat m ↦[wmlength] len.

Definition GC (I : gc_inv Σ) (m : memaddr) (θ : addr_map) : iProp Σ :=
  ∃ (info : vinfo) (ζ : vstore) (roots : root_map),
  I info ζ roots ∗
  ghost_map_auth gcG_vinfo (1/2) info ∗
  ghost_map_auth gcG_vstore 1 ζ ∗
  ghost_map_auth gcG_roots (1/2) roots ∗
  blocks_match_memory m θ ζ ∗
  roots_match_memory m θ roots ∗
  ⌜headers_match_blocks info ζ⌝ ∗
  ⌜roots_live θ roots⌝ ∗
  ⌜reachability_ok ζ θ⌝.

End GCtoken.

Section GCrules.

Context `{wasm : wasmG Σ}.
Context `{rwasm : rwasm_gcG Σ}.

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
  blk !! i = Some u ->
  repr_vblock θ blk ks ->
  exists w, repr_vval θ u w /\ ks !! i = Some w.
Proof.
  intros θ blk u ks i Hi Hblk. inversion Hblk. subst.
  assert (exists w, In (u, w) (combine blk ks)).
  - admit.
  - destruct H1 as [w Hw].
    exists w. split.
    + change (repr_vval θ u w) with (curry (repr_vval θ) (u, w)).
      eapply List.Forall_forall.
      * exact H0.
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
  [ try rewrite length_app; rewrite len; unfold vblock_offset; unfold serialise_i32;
    try rewrite Memdata.encode_int_length;
    cbn; lia
  | auto ].

Definition spec_alloc_gc
    (E : coPset) (I : gc_inv Σ) (m : memaddr)
    (finst : instance) (fid : nat) (fts : list value_type) (fes : list basic_instruction)
    : iProp Σ :=
  □ ∀ (F : frame) (θ : addr_map) (count size : i32) (ptrmap : i64),
  let hdr := {| count := Wasm_int.nat_of_uint i32m count;
                elem := ptrmap_to_vkinds ptrmap (Wasm_int.nat_of_uint i32m size) |} in
  GC I m θ ∗
  N.of_nat fid ↦[wf] FC_func_native finst (Tf [T_i32; T_i32; T_i64] [T_i32]) fts fes ∗
  ↪[frame] F -∗
  WP [AI_basic (BI_const (VAL_int32 count));
      AI_basic (BI_const (VAL_int32 size));
      AI_basic (BI_const (VAL_int64 ptrmap));
      AI_invoke fid]
     @ E
     {{ w,
        (⌜w = trapV⌝ ∨
         ∃ θ' ℓ z blk,
         ⌜w = immV [VAL_int32 (Wasm_int.int_of_Z i32m z)]⌝ ∗ ⌜repr_vloc θ' ℓ 0 z⌝ ∗
         GC I m θ' ∗ ℓ ↦vhdr hdr ∗ ℓ ↦vblk blk ∗
         N.of_nat fid ↦[wf] FC_func_native finst (Tf [T_i32] [T_i32]) fts fes) ∗
        ↪[frame] F }}%I.

Lemma wp_load_gc
    (s : stuckness) (E : coPset) (F : frame) (memidx: immediate)
    (m : memaddr) (θ : addr_map) (I : gc_inv Σ)
    (i : i32) (ℓ : vloc) (blk : vblock)
    (j : nat) (off : static_offset) (vv : vval) :
  F.(f_inst).(inst_memory) !! memidx = Some m ->
  repr_vloc θ ℓ j (Wasm_int.Z_of_uint i32m i + Z.of_N off) ->
  blk !! j = Some vv ->
  GC I m θ ∗ ℓ ↦vblk blk ∗ ↪[frame] F ⊢
  WP [AI_basic (BI_const (VAL_int32 i)); AI_basic (BI_load memidx T_i32 None N.zero off)]
     @ s; E
     {{ w, (∃ k, ⌜w = immV [VAL_int32 (Wasm_int.int_of_Z i32m k)]⌝ ∗ ⌜repr_vval θ vv k⌝) ∗
           GC I m θ ∗ ℓ ↦vblk blk ∗ ↪[frame] F }}.
Proof.
  iIntros (Hmem Hrepr_loc Hvv)
    "((%info & %ζ & %roots & HGCI & HGvinfo & HGvstore & HGroots & Hvmem & Hrmem & %Hheaders & %Hroots & %Hreach) & Hℓ & HF)".
  inversion Hrepr_loc as [θ' ℓ' off' a a' Hθℓ Hi Hθ' Hℓ' Hoff' Ha']. subst.
  symmetry in Hi. apply pointer_offset_eqn_Z2N in Hi.
  iDestruct (ghost_map_lookup with "HGvstore Hℓ") as "%Hζℓ".
  iDestruct (big_sepM2_lookup_acc _ _ _ _ _ _ Hθℓ Hζℓ with "Hvmem") as
    "[(%bs & %ks & Ha & %Hbs & %Hrepr_blk) Hvmem]".
  inversion Hrepr_blk as [θ' blk' ks' Hlen_ks' Hvals Hθ' Hblk' Hks']. subst.
  pose proof (lookup_lt_Some _ _ _ Hvv) as Hoff. rewrite <- Hlen_ks' in Hoff.

  (* Pull out the physical value in the vblock repr corresponding to the offset. *)
  destruct (list_pluck _ _ _ Hoff) as [ks1 [ki [ks2 [Hki [Hlen_ks1 Hks]]]]]. rewrite Hks.
  destruct (repr_vblock_index θ blk vv ks j Hvv Hrepr_blk) as [k [Hrepr_vv' Hk']].
  assert (k = ki) by congruence. subst ki.

  (* Pull out the bytes in the vblock points-to corresponding to the offset. *)
  unfold serialize_zs. rewrite flat_map_app. rewrite (separate1 k). rewrite flat_map_app.
  simpl. rewrite app_nil_r.
  rewrite (wms_app _ _ _ (vblock_offset j)). rewrite Hi.
  rewrite (wms_app _ (serialize_z k) _ 4).
  iDestruct "Ha" as "(Ha & Ha_off & Ha_rest)".

  set ptr := (Wasm_int.N_of_uint i32m i + off)%N.
  set post := (λ w,
    ((∃ k', ⌜w = immV [VAL_int32 (Wasm_int.int_of_Z i32m k')]⌝ ∗ ⌜repr_vval θ vv k'⌝) ∗
     N.of_nat m ↦[wms][ptr] serialize_z k) ∗ ↪[frame] F
  )%I.
  iApply (wp_wand _ _ _ post with "[HF Ha_off] [HGCI HGvinfo HGvstore HGroots Hrmem Hℓ Ha Ha_rest Hvmem]").
  - (* Load the value from memory. *)
    iApply wp_load_deserialize; auto. rewrite deserialise_serialise_i32. iFrame. by iExists k.
  - (* Show that the intermediate postcondition implies the original postcondition. *)
    iIntros (v) "[[HΦ Ha_off] HF]". iFrame "∗ %". iCombine "Ha Ha_off" as "Ha".
    unfold ptr. rewrite <- Hi. rewrite <- wms_app; last (solve_i32_bytes_len Hlen_ks1).
    replace (serialize_z k) with (flat_map serialize_z [k]) by (by rewrite flat_map_singleton).
    iCombine "Ha Ha_rest" as "Ha". rewrite <- N.add_assoc.
    rewrite <- wms_app; last (solve_i32_bytes_len Hlen_ks1).
    rewrite <- !flat_map_app. rewrite <- app_assoc. rewrite <- separate1. rewrite <- Hks.
    iApply "Hvmem". iExists _, _. by iFrame.
  - auto.
  - solve_i32_bytes_len Hlen_ks1.
Qed.

Lemma wp_store_gc
    (s : stuckness) (E : coPset) (F : frame) (memidx: immediate)
    (m : memaddr) (θ : addr_map) (I : gc_inv Σ)
    (i k : i32) (ℓ : vloc) (blk : vblock)
    (j : nat) (off : static_offset) (vv : vval) :
  F.(f_inst).(inst_memory) !! memidx = Some m ->
  repr_vloc θ ℓ j (Wasm_int.Z_of_uint i32m i + Z.of_N off) ->
  j < length blk ->
  repr_vval θ vv (Wasm_int.Z_of_uint i32m k) ->
  GC I m θ ∗ ℓ ↦vblk blk ∗ ↪[frame] F ⊢
  WP [AI_basic (BI_const (VAL_int32 i));
      AI_basic (BI_const (VAL_int32 k));
      AI_basic (BI_store memidx T_i32 None N.zero off)]
     @ s; E
     {{ w, ⌜w = immV []⌝ ∗ GC I m θ ∗ ℓ ↦vblk <[ j := vv ]> blk ∗ ↪[frame] F }}.
Admitted.

Definition spec_registerroot_gc
    (E : coPset) (I : gc_inv Σ) (m : memaddr)
    (finst : instance) (fid : nat) (fts : list value_type) (fes : list basic_instruction)
    : iProp Σ :=
  □ ∀ (F : frame) (θ : addr_map) (ℓ : vloc) (i : i32),
  GC I m θ ∗ ⌜repr_vloc θ ℓ 0 (Wasm_int.Z_of_uint i32m i)⌝ ∗
  N.of_nat fid ↦[wf] FC_func_native finst (Tf [T_i32] [T_i32]) fts fes ∗ ↪[frame] F -∗
  WP [AI_basic (BI_const (VAL_int32 i)); AI_invoke fid]
     @ E
     {{ w,
        (⌜w = trapV⌝ ∨
         ∃ k,
         ⌜w = immV [VAL_int32 k]⌝ ∗ Wasm_int.N_of_uint i32m k ↦root ℓ ∗ GC I m θ ∗
         N.of_nat fid ↦[wf] FC_func_native finst (Tf [T_i32] [T_i32]) fts fes) ∗
        ↪[frame] F }}%I.

(* TODO: wp_loadroot_gc *)

Definition spec_unregisterroot_gc
    (E : coPset) (I : gc_inv Σ) (m : memaddr)
    (finst : instance) (fid : nat) (fts : list value_type) (fes : list basic_instruction)
    : iProp Σ :=
  □ ∀ (F : frame) (θ : addr_map) (k : i32) (ℓ : vloc),
  GC I m θ ∗ Wasm_int.N_of_uint i32m k ↦root ℓ ∗
  N.of_nat fid ↦[wf] FC_func_native finst (Tf [T_i32] [T_i32]) fts fes ∗ ↪[frame] F -∗
  WP [AI_basic (BI_const (VAL_int32 k)); AI_invoke fid]
     @ E
     {{ w, ∃ n,
        ⌜w = immV [VAL_int32 (Wasm_int.int_of_Z i32m n)]⌝ ∗ ⌜repr_vloc θ ℓ 0 n⌝ ∗
        GC I m θ ∗
        N.of_nat fid ↦[wf] FC_func_native finst (Tf [T_i32] [T_i32]) fts fes ∗ ↪[frame] F }}%I.

End GCrules.

Section GCexample.

Context `{!wasmG Σ, !rwasm_gcG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ, !logrel_na_invs Σ}.

Definition i32const (n:Z) := BI_const (VAL_int32 (Wasm_int.int_of_Z i32m n)).
Definition i64const (n:Z) := BI_const (VAL_int64 (Wasm_int.int_of_Z i64m n)).
Definition value_of_int (n:Z) := VAL_int32 (Wasm_int.int_of_Z i32m n).

Definition gc_init :=
  [ i32const 0;
    BI_drop ].

Definition gc_alloc :=
  [ i32const 0 ].

Definition gc_registerroot :=
  [ i32const 0 ].

Definition gc_unregisterroot :=
  [ i32const 0 ].

Definition gc_module :=
  {| mod_types := [
       Tf [] [];
       Tf [T_i32] [T_i32];
       Tf [T_i32; T_i32; T_i64] [T_i32]
     ];
     mod_funcs := [
      {| modfunc_type := Mk_typeidx 0;
         modfunc_locals := [];
         modfunc_body := gc_init |};
      {| modfunc_type := Mk_typeidx 2;
         modfunc_locals := [];
         modfunc_body := gc_alloc |};
      {| modfunc_type := Mk_typeidx 1;
         modfunc_locals := [];
         modfunc_body := gc_registerroot |};
      {| modfunc_type := Mk_typeidx 1;
         modfunc_locals := [];
         modfunc_body := gc_unregisterroot |}
    ];
    mod_tables := [];
    mod_mems := [ {| lim_min := 0%N; lim_max := None |} ];
    mod_globals := [];
    mod_elem := [];
    mod_data := [];
    mod_start := Some (Build_module_start (Mk_funcidx 0));
    mod_imports := [];
    mod_exports := [
      {| modexp_name := String.list_byte_of_string "gc_mem";
         modexp_desc := MED_mem (Mk_memidx 0) |};
      {| modexp_name := String.list_byte_of_string "gc_alloc";
         modexp_desc := MED_func (Mk_funcidx 0) |};
      {| modexp_name := String.list_byte_of_string "gc_registerroot";
         modexp_desc := MED_func (Mk_funcidx 1) |};
      {| modexp_name := String.list_byte_of_string "gc_unregisterroot";
         modexp_desc := MED_func (Mk_funcidx 2) |}
    ]
  |}.

Definition main :=
  [ i32const 1;
    i32const 2;
    i64const 0;
    BI_call 1;
    BI_drop ].
    (*BI_set_global 0 ].*)

Definition client_module :=
  {| mod_types := [
       Tf [] [];
       Tf [T_i32] [T_i32];
       Tf [T_i32; T_i32; T_i64] [T_i32]
    ];
    mod_funcs := [
      {| modfunc_type := Mk_typeidx 0;
         modfunc_locals := [T_i32];
         modfunc_body := main |}
    ];
    mod_tables := [];
    mod_mems := [];
    mod_globals := [
      {| modglob_type := {| tg_t := T_i32; tg_mut := MUT_mut |};
         modglob_init := [i32const 0] |}
    ];
    mod_elem := [];
    mod_data := [];
    mod_start := Some {| modstart_func := Mk_funcidx 3 |};
    mod_imports := [
      {| imp_module := String.list_byte_of_string "RichWasm";
         imp_name := String.list_byte_of_string "gc_alloc";
         imp_desc := ID_func 2 |};
      {| imp_module := String.list_byte_of_string "RichWasm";
         imp_name := String.list_byte_of_string "gc_registerroot";
         imp_desc := ID_func 1 |};
      {| imp_module := String.list_byte_of_string "RichWasm";
         imp_name := String.list_byte_of_string "gc_unregisterroot";
         imp_desc := ID_func 1 |}
    ];
    mod_exports := [
      {| modexp_name := String.list_byte_of_string "answer";
         modexp_desc := MED_global (Mk_globalidx 0) |}
    ]
  |}.

Definition own_vis_pointers (exp_addrs : list N) : iProp Σ :=
   [∗ list] exp_addr ∈ exp_addrs, (∃ mexp, exp_addr ↪[vis] mexp).

Definition func_types :=
  [Tf [T_i32; T_i32; T_i64] [T_i32];
   Tf [T_i32] [T_i32];
   Tf [T_i32] [T_i32]].

Definition expts := fmap ET_func func_types.

Definition gc_spec (E : coPset) (exp_addrs : list N) (gc_mod_addr : N) : iProp Σ :=
  gc_mod_addr ↪[mods] gc_module ∗
  ∃ (I : gc_inv Σ)
    (inst0 : instance)
    (name0 name1 name2 name3 name4 : name)
    (idm0 : nat)
    (idf0 idf1 idf2 idf3 : nat)
    (f0 f1 f2 f3 : list basic_instruction)
    (l0 l1 l2 l3 : list value_type),
  let inst_vis :=
       [ {| modexp_name := name0; modexp_desc := MED_mem (Mk_memidx idm0) |};
         {| modexp_name := name1; modexp_desc := MED_func (Mk_funcidx idf0) |};
         {| modexp_name := name2; modexp_desc := MED_func (Mk_funcidx idf1) |};
         {| modexp_name := name3; modexp_desc := MED_func (Mk_funcidx idf2) |};
         {| modexp_name := name4; modexp_desc := MED_func (Mk_funcidx idf3) |} ] in
  let inst_map :=
        list_to_map (zip (fmap N.of_nat [idf0; idf1; idf2; idf3])
                         [FC_func_native inst0 (Tf [] []) l0 f0;
                          FC_func_native inst0 (Tf [T_i32; T_i32; T_i64] [T_i32]) l1 f1;
                          FC_func_native inst0 (Tf [T_i32] [T_i32]) l2 f2;
                          FC_func_native inst0 (Tf [T_i32] [T_i32]) l3 f3]) in
  import_resources_host exp_addrs inst_vis ∗
  import_resources_wasm_typecheck_sepL2 inst_vis expts inst_map ∅ ∅ ∅ ∗
  ⌜NoDup (modexp_desc <$> inst_vis)⌝ ∗
  ⌜NoDup [idf0; idf1; idf2; idf3]⌝ ∗
  GC I idm0 gmap_empty ∗
  spec_alloc_gc E I idm0 inst0 idf1 l1 f1 ∗
  spec_registerroot_gc E I idm0 inst0 idf2 l2 f2 ∗
  spec_unregisterroot_gc E I idm0 inst0 idf3 l3 f3.

Lemma instantiate_gc_spec `{!logrel_na_invs Σ}
    (s : stuckness) (E : coPset) (Φ : host_val -> iProp Σ)
    (exp_addrs : list N) (gc_mod_addr : N)
    (es : list host_e) (vs : list administrative_instruction) :
  length exp_addrs = 5 ->
  gc_mod_addr ↪[mods] gc_module -∗
  own_vis_pointers exp_addrs -∗
  (gc_spec E exp_addrs gc_mod_addr -∗ WP (es, []) : host_expr @ E {{ v, Φ v }}) -∗
  WP (ID_instantiate exp_addrs gc_mod_addr [] :: es, vs) : host_expr
     @ s; E
     {{ v, Φ v }}.
Admitted.

Lemma module_typing_client :
  module_typing client_module expts [ET_glob {| tg_t := T_i32; tg_mut := MUT_mut |}].
Admitted.

Lemma module_restrictions_client : module_restrictions client_module.
Admitted.

Definition client_instantiate_para (vis_addrs : list N) (gc_mod_addr client_mod_addr : N) :=
  [ ID_instantiate (take 5 vis_addrs) gc_mod_addr [];
    ID_instantiate (drop 5 vis_addrs) client_mod_addr (take 5 vis_addrs) ].

Lemma instantiate_client_spec E (vis_addrs : list N) (gc_mod_addr client_mod_addr : N) :
  length vis_addrs = 6 ->
  ↪[frame] empty_frame -∗
  gc_mod_addr ↪[mods] gc_module -∗
  client_mod_addr ↪[mods] client_module -∗
  own_vis_pointers vis_addrs -∗
  WP (client_instantiate_para vis_addrs gc_mod_addr client_mod_addr, []) : host_expr
     @ E
     {{ v, ⌜v = trapHV⌝ ∨ ⌜v = immHV []⌝ }}.
Proof.
  iIntros (Hvisaddrlen) "Hf Hmodgc Hmodcl Hvis".
  do 7 (destruct vis_addrs => //); clear Hvisaddrlen.
  rewrite separate5.
  iDestruct (big_sepL_app with "Hvis") as "(Hvis & (Hvis5 & _))".

  iApply (instantiate_gc_spec with "Hmodgc [Hvis]") => //.
  iIntros "(Hmod0 &%&%&%&%&%&%&%&%&%&%&%&%&%&%&%&%&%&%&%&%& Himport & Himp_type & %Hnodup & %Hfnodup & HGC & #Hspec0 & #Hspec1 & #Hspec2)".
  iApply (instantiation_spec_operational_start with "Hf [Hmodcl Himport Himp_type Hvis5]").
  2: exact module_typing_client.
  2: exact module_restrictions_client.
  1: by unfold client_module.
  {
    unfold instantiation_resources_pre. iFrame.
    unfold export_ownership_host => /=.
    unfold instantiation_resources_pre_wasm.
    rewrite irwt_nodup_equiv => //.
    iFrame "Himp_type".
    repeat iSplit.
    - iPureIntro. unfold module_elem_bound_check_gmap. by simpl.
    - iPureIntro. unfold module_data_bound_check_gmap. by simpl.
    - done.
    - done.
  }

  iIntros (idnstart) "Hf Hres".
  unfold instantiation_resources_post.
  iDestruct "Hres" as "(Hmod1 & Himphost & Hres)".
  iDestruct "Hres" as (inst) "[Hres Hexphost]".
  iDestruct "Hres" as (g_inits t_inits m_inits gms wts wms) "(Himpwasm & %Hinst & -> & -> & %Hbound & -> & -> & %Hbound' & Hginit & -> & Hexpwasm)".
  destruct Hinst as (Hinsttype & Hinstfunc & Hinsttab & Hinstmem & Hinstglob & Hstart).
  unfold module_inst_resources_wasm, module_export_resources_host => /=.
  destruct inst => /=.
  iDestruct "Hexpwasm" as "(Hexpwf & Hexpwt & Hexpwm & Hexpwg)".
  unfold module_inst_resources_func, module_inst_resources_tab,
  module_inst_resources_mem, module_inst_resources_glob => /=.
  unfold big_sepL2 => /=.
  do 4 (destruct inst_funcs as [| ? inst_funcs]; first by iExFalso; iExact "Hexpwf").
  simpl.
  iDestruct "Hexpwf" as "[Hwfcl Hexpwf]".
  destruct inst_funcs; last by iExFalso.
  destruct inst_memory; last by iExFalso; iExact "Hexpwm".

  destruct inst_globs as [| g inst_globs];
    first by destruct g_inits; iExFalso; iExact "Hexpwg".
  destruct inst_globs;
    last by destruct g_inits; iExFalso; iDestruct "Hexpwg" as "[_ Habs]";
    iExact "Habs".
  iApply wp_lift_wasm.
  cbn in Hstart.
  destruct (PeanoNat.Nat.eq_dec f6 idnstart); last done.
  subst f6.
  rewrite -(app_nil_l [AI_invoke idnstart]).
  iApply (wp_invoke_native with "Hf [Hwfcl]").
  { done. }
  { by instantiate (1 := []). }
  { done. }
  { simpl in Hinsttype. by subst inst_types. }

  iIntros "!> [Hf Hwfcl]".
  iApply (wp_frame_bind with "Hf"); first done.
  iIntros "Hf".
  rewrite -(app_nil_l [AI_basic _]).
  iApply (wp_block with "Hf"); try done.

  iIntros "!> Hf".
  iApply (wp_label_bind with "[-]"); last first.
  {
    iPureIntro. unfold lfilled, lfill.
    instantiate (6 := []). simpl.
    rewrite app_nil_r. done.
  }

  set inst := {| inst_types := inst_types;
                 inst_funcs := [f; f4; f5; idnstart];
                 inst_tab := inst_tab;
                 inst_memory := [];
                 inst_globs := [g] |} in Hinstglob, Hinstmem, Hinsttab, Hinstfunc.

  (* Split the function resources. *)
  unfold import_resources_host, import_resources_wasm_typecheck, import_func_wasm_check, import_func_resources.
  iDestruct "Himpwasm" as "[[Himpwf %Hfunc_check] (Himptab & Himpmem & Himpglob)]".
  rewrite !NoDup_cons in Hfnodup.
  rewrite !not_elem_of_cons in Hfnodup.
  rewrite !big_sepM_insert.
  2: auto.
  2, 3, 4: rewrite !lookup_insert_None; rewrite !Nat2N.inj_iff; intuition.
  iDestruct "Himpwf" as "(Hf0 & Hf1 & Hf2 & Hf3 & _)".
  cbn in Hinstfunc. apply prefix_length_eq in Hinstfunc; last auto.
  replace f4 with idf1 by congruence.

  cbn in *.
  rewrite (separate1 (AI_basic (BI_call 1))).
  iApply (wp_wand with "[Hf Hf1 HGC]").
  {
    set fr := {|
                  f_locs := [VAL_int32 Wasm_int.Int32.zero];
                  f_inst :=
                    {|
                      inst_types := inst_types;
                      inst_funcs := [f; idf1; f5; idnstart];
                      inst_tab := inst_tab;
                      inst_memory := [];
                      inst_globs := [g]
                    |}
                |}.
    set post1 := (∃ θ' ℓ blk, GC I idm0 θ' ∗ ℓ ↦vhdr {|
                    count := Z.to_nat 1;
                    elem :=
                      ptrmap_to_vkinds (Wasm_int.Int64.repr 0) (Z.to_nat 2) |} ∗
                                      ℓ ↦vblk blk ∗
                    N.of_nat idf1 ↦[wf] FC_func_native inst0 (Tf [T_i32] [T_i32]) l1 f1)%I.
    iApply (wp_seq_can_trap_same_empty_ctx
      (λ w, ⌜w = trapV⌝ ∨ post1)%I (λ w, ∃ c, ⌜w = immV [c]⌝ ∗ post1)%I _ _
      ([AI_basic (i32const 1); AI_basic (i32const 2); AI_basic (i64const 0); AI_basic (BI_call 1)])
      [AI_basic BI_drop]
      fr
    ).
    iSplitR "Hf Hf1 HGC"; last iSplitR "Hf Hf1 HGC"; last iSplitR "Hf1 HGC"; last iSplitL "Hf1 HGC".
    4: {
      iIntros "Hf".
      iApply (wp_wand with "[Hf1 HGC Hf]").
      {
        build_ctx [AI_basic (BI_call 1)].
        iApply (wp_call_ctx with "[$]").
        2: {
          iIntros "!> Hf".
          deconstruct_ctx.
          iApply "Hspec0".
          iFrame.
        }
        done.
      }
      iIntros (v) "[[-> | (% & % & % & % & -> & %Hℓz & HGC & Hℓhdr & Hℓblk & Hf1)] Hf]".
      - iFrame. by iLeft.
      - iFrame. iRight. iExists (VAL_int32 (Wasm_int.Int32.repr z)). iFrame. done.
    }
    3: done.
    {
      iIntros "(% & %contra & Hpost)". congruence.
    }
    2: {
      iIntros (w) "[(% & -> & Hpost) Hf]". simpl.
      iApply (wp_drop with "Hf").
      iModIntro.
      by iRight.
    }
    simpl. by iLeft.
  }

  iIntros (v) "[[-> | (% & % & % & HGC & Hℓhdr & Hℓblk & Hf1)] Hf]".
  {
    iApply (wp_wand_ctx with "[Hf]").
    {
      simpl. rewrite <- (app_nil_r [AI_trap]). rewrite <- (app_nil_l [AI_trap]). rewrite <- app_assoc.
      by iApply (wp_trap_ctx with "Hf").
    }

    iIntros (v) "[-> Hf]".
    iExists _. iFrame.
    iIntros "Hf".
    simpl.
    rewrite <- (app_nil_r [AI_trap]). rewrite <- (app_nil_l [AI_trap]). rewrite <- app_assoc.
    iApply (wp_wand_ctx _ _ ([] ++ [AI_trap] ++ []) with "[Hf]").
    - by iApply (wp_trap_ctx with "Hf").
    - iIntros (v) "[-> Hf]". simpl.
      admit.
    - iPureIntro.
      admit.
  }

  iApply (wp_val_return with "[Hf]").
  - admit.
  - done.
  - iIntros "Hf".
    admit.
Admitted.

End GCexample.
