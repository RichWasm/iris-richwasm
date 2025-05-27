From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From Wasm.iris.host Require Export iris_host.
From Wasm.iris.logrel Require Export iris_fundamental_helpers.
From RWasm.iris.allocator.function Require Export allocator_specs.
From RWasm.iris.allocator Require Export malloc_impl.
From Wasm Require Export type_checker_reflects_typing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac invert_cllookup H n :=
  let k := fresh "k" in
  let Hind := fresh "Hind" in
  let Hcl := fresh "Hcl" in
  destruct H as ((k & Hind & Hcl) & _); assert (k = n) as ->; first (by eapply NoDup_lookup => //); inversion Hcl; subst; clear Hcl Hind.

Ltac resolve_cl_lookup n :=
  iExists _; iFrame; iSplit => //; iPureIntro; rewrite list_to_map_zip_lookup => //; exists n; try done.
   
Set Bullet Behavior "Strict Subproofs".


Section AllocModule.

Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ}. 

Definition malloc_typ := Tf [T_i32] [T_i32].
Definition free_typ := Tf [T_i32] [].

Definition alloc_module :=
  {|
    mod_types := [malloc_typ; free_typ];
    mod_funcs := [
      {|
        modfunc_type := Mk_typeidx 0; (* i32 -> i32 *)
        modfunc_locals := [T_i32; T_i32; T_i32; T_i32];
        modfunc_body := malloc 0
      |};
      {|
        modfunc_type := Mk_typeidx 1; (* i32 -> [] *)
        modfunc_locals := [];
        modfunc_body := free 0
      |}
    ];
    mod_tables := [];
    mod_mems := [ {| lim_min := 0%N ; lim_max := None |} ];
    mod_globals := [];
    mod_elem := [];
    mod_data := [];
    mod_start := None;
    mod_imports := [];
    mod_exports := [
      {|
        modexp_name := String.list_byte_of_string "malloc" ;
        modexp_desc := MED_func (Mk_funcidx 0)
      |};
      {|
        modexp_name := String.list_byte_of_string "free" ;
        modexp_desc := MED_func (Mk_funcidx 1)
      |}
    ]
  |}.

Definition alloc_imports : list extern_t := [].
Definition alloc_exports : list extern_t := [
    ET_func malloc_typ;
    ET_func free_typ
].

Proposition alloc_module_typed:
  module_typing alloc_module alloc_imports alloc_exports.
Proof.
  unfold alloc_imports, alloc_exports, alloc_module.
  exists [malloc_typ; free_typ].
  exists nil.
  simpl.
  repeat match goal with 
         | |- is_true true => done
         | |- _ /\ _ => split
         | |- Forall2 _ (_ :: _) (_ :: _) => rewrite -> Forall2_cons_iff
         | |- Forall2 _ [] [] => done
         | |- Forall _ [] => done
         end;
    try done.
  - (* function typing: malloc *)
    cbn.
    split; first done.
    split; first done.
    cbn.
    unfold malloc_typ, free_typ.
    unfold malloc, malloc_body.
    by apply/b_e_type_checker_reflects_typing.
  - (* function typing: free *) 
    cbn.
    split; first done.
    split; first done.
    by apply/b_e_type_checker_reflects_typing.
Qed.

Definition own_vis_pointers (exp_addrs: list N): iProp Σ :=
   ([∗ list] exp_addr ∈ exp_addrs, (∃ mexp, exp_addr ↪[vis] mexp)).

Lemma own_vis_pointers_nodup (exp_addrs: list N):
  own_vis_pointers exp_addrs -∗
  ⌜ NoDup exp_addrs ⌝.
Proof.
  iInduction (exp_addrs) as [|e] "IH"; unfold own_vis_pointers => //=; first by iIntros; rewrite NoDup_nil.
  iIntros "(Hexp & Hexps)".
  iDestruct "Hexp" as (?) "Hexp".
  rewrite NoDup_cons.
  iDestruct ("IH" with "Hexps") as "%Hnodup".
  iSplit => //.
  iIntros "%Hin".
  apply elem_of_list_lookup in Hin.
  destruct Hin as [i Hin].
  iDestruct (big_sepL_lookup with "Hexps") as "Hcontra" => //.
  iDestruct "Hcontra" as (?) "Hcontra".
  by iDestruct (ghost_map_elem_ne with "Hexp Hcontra") as "%".
Qed.

(* The similar result does *not* hold for tables and memories, because wtblock and wmblock are not necessarily
   exclusive resources. *)
Lemma module_inst_resources_func_nodup ms inst addrs:
  module_inst_resources_func ms inst addrs -∗
  ⌜ NoDup addrs ⌝.
Proof.
  move: ms inst.
  iInduction (addrs) as [|a] "IH"; unfold module_inst_resources_func; iIntros (ms inst) "Hw" => //=; first by rewrite NoDup_nil.
  iDestruct (big_sepL2_length with "Hw") as "%Hlen".
  destruct ms => //=.
  iDestruct "Hw" as "(Hf & Hw)".
  rewrite NoDup_cons.
  iDestruct ("IH" with "Hw") as "%Hnodup".
  iSplit => //.
  iIntros "%Hin".
  apply elem_of_list_lookup in Hin.
  destruct Hin as [i Hin].
  assert (exists m', ms !! i = Some m') as Hm.
  { apply lookup_lt_Some in Hin.
    simpl in Hlen.
    replace (length addrs) with (length ms) in Hin; last by inversion Hlen.
    destruct (ms !! i) eqn:Hl; try by eexists.
    apply lookup_ge_None in Hl; lia.
  }
  destruct Hm as [? Hm].
  iDestruct (big_sepL2_lookup with "Hw") as "Hcontra" => //; last by iDestruct (pointsto_ne with "Hf Hcontra") as "%".
Qed.

Section instantiation.
  Variables (exp_addrs: list N) (mod_addr : N).

  Definition alloc_instantiate : host_expr := 
    ([ ID_instantiate exp_addrs mod_addr [] ], []).

  Theorem instantiate_allocator_spec s E:
    ⌜length exp_addrs = 2⌝ ∗
    ⌜NoDup exp_addrs⌝ ∗
    mod_addr ↪[mods] alloc_module ∗
    own_vis_pointers exp_addrs
    ⊢ WP alloc_instantiate @ s;E {{λ w, ⌜w = immHV []⌝ ∗ mod_addr ↪[mods] alloc_module }}.
  Proof.
    iIntros "(%Hexplen & %Hdisj & Hmod & Hvis)".
    iApply (weakestpre.wp_strong_mono s _ E with "[Hmod Hvis]") => //.
    iApply instantiation_spec_operational_no_start; try iFrame; auto.
    - apply alloc_module_typed.
    - admit.
    - iSplit.
      eauto.
      unfold import_resources_host. auto.
      unfold alloc_imports.
      unfold instantiation_resources_pre_wasm; eauto.
      repeat iSplit; try iPureIntro;
        unfold import_func_resources, import_tab_resources, import_mem_resources, import_glob_resources;
        try done;
        try by constructor.
    - unfold instantiation_resources_post.
      unfold instantiation_resources_post_wasm.
      iIntros (w) "(-> & Hmod & Himp & %inst & Hexp)".
      cbn.
      admit.
  Admitted.
End instantiation.

End AllocModule.
