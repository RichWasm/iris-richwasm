From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From Wasm.iris.host Require Export iris_host.
From Wasm.iris.logrel Require Export iris_fundamental_helpers.
From RWasm.iris.allocator.function Require Export allocator_specs.
From RWasm.iris.allocator Require Export malloc_impl spec.
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


Definition init_typ := Tf [] [].

Definition alloc_module :=
  {|
    mod_types := [malloc_typ; free_typ; init_typ];
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
      |};
      {|
        modfunc_type := Mk_typeidx 2; (* [] -> [] *)
        modfunc_locals := [];
        modfunc_body := init 0;
      |}
    ];
    mod_tables := [];
    mod_mems := [ {| lim_min := 0%N ; lim_max := None |} ];
    mod_globals := [];
    mod_elem := [];
    mod_data := [];
    mod_start := Some {| modstart_func := Mk_funcidx 2 |};
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
  exists [malloc_typ; free_typ; init_typ].
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
  - (* function typing: init *) 
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
    ↪[frame] empty_frame ∗
    own_vis_pointers exp_addrs
    ⊢ WP alloc_instantiate @ s;E
         {{λ w, ⌜w = immHV []⌝ ∗ mod_addr ↪[mods] alloc_module ∗
                ∃ (fid0 fid1: nat) (name0 name1: name) (body0 body1: seq.seq basic_instruction)
                  (mem: N)
                  (inst: instance)
                  (local_typs0 local_typs1 : list value_type)
                  (alloc_tok: N -> N -> iProp Σ)
                  (alloc_inv: N -> iProp Σ),
                  let inst_vis : seq.seq module_export := map (λ '(name, fid),
                                         {| modexp_name := name;
                                            modexp_desc := MED_func (Mk_funcidx fid) |})
                                      [(name0, fid0); (name1, fid1)] in
                  let inst_map := list_to_map (zip (map N.of_nat [fid0; fid1])
                                                 [(FC_func_native inst malloc_typ local_typs0 body0) ;
                                                  (FC_func_native inst free_typ local_typs1 body1)]) in
                  ⌜NoDup [fid0; fid1]⌝ ∗
                  alloc_inv mem ∗
                  import_resources_host exp_addrs inst_vis ∗
                  import_resources_wasm_typecheck_sepL2 inst_vis alloc_exports inst_map ∅ ∅ ∅ ∗
                  spec_malloc alloc_tok alloc_inv E fid0 inst local_typs0 body0 ∗
                  spec_free alloc_tok alloc_inv E fid1 inst local_typs1 body1
         }}.
  Proof.
    iIntros "(%Hexplen & %Hdisj & Hmod & Hfr & Hvis)".
    iApply (weakestpre.wp_strong_mono s _ E with "[Hmod Hfr Hvis]") => //.
    iApply (instantiation_spec_operational_start with "[Hfr] [Hmod Hvis]"); try iFrame; auto.
    - apply alloc_module_typed.
    - admit.
    - iSplitL.
      eauto.
      unfold import_resources_host. auto.
      unfold alloc_imports.
      unfold instantiation_resources_pre_wasm; eauto.
      repeat iSplit; try iPureIntro;
        unfold import_func_resources, import_tab_resources, import_mem_resources, import_glob_resources;
        try done;
        try by constructor.
    - iIntros (idnstart) "Hfr".
      unfold instantiation_resources_post.
      unfold instantiation_resources_post_wasm.
      iIntros "(Hmod & Himp & %inst & Hinst & Hhost)".
      iDestruct "Hinst" as "(%g_inits & %tab_allocs & %mem_allocs & %glob_allocs & %wts' & %wms' & Hinst)".
      iDestruct "Hinst" as "(Htype & %Himports & %Htaballoc & %Hwts' & %Hmodbound & %Hmemalloc & H')".
      iDestruct "H'" as "(%Hwms' & %Hmodbound' & %Hglobinit & %Hgloballoc & Hinstrsc)".
      iDestruct "Hinstrsc" as "(Hfuncs & Hrest)".
      destruct Himports as (Himp_types & Himp_ext_func & Himp_ext_tab & Himp_ext_mem & Himp_ext_glob & Himp_check_start).
      subst.
      rewrite drop_0.
      iPoseProof (big_sepL2_length with "[$Hfuncs]") as "%Hfuncslen".
      cbn in Hfuncslen.
      unfold check_start in Himp_check_start.
      destruct (inst_funcs inst) as [| f0 [| f1 [| f2 [| ?]]]]; try (vm_compute in Hfuncslen; discriminate).
      iEval (cbn) in "Hfuncs".
      iDestruct "Hfuncs" as "(Hfmalloc & Hffree & Hfstart & _)".
      rewrite !Himp_types.
      simpl mod_types; simpl nth.
      simpl in Himp_check_start.
      move/eqP in Himp_check_start.
      replace idnstart with f2 by congruence.
      iApply wp_lift_wasm.
      change [AI_invoke f2]
      with ([] ++ [AI_invoke f2])%list.
      {
        iApply (wp_invoke_native with "[$Hfr] [$Hfstart]") =>//.
        iIntros "!> (Hfr & Hfstart)".
        cbn.
        iApply (wp_frame_bind with "[$Hfr]") =>//.
        iIntros "Hfr".
        rewrite <- (app_nil_l [AI_basic _]).
        iApply (wp_block with "[$Hfr]") =>//.
        iIntros "!> Hfr".
        iApply wp_build_ctx.
        {
          constructor.
          apply/lfilledP.
          rewrite <- (app_nil_l [AI_label _ _ _]).
          econstructor =>//.
          rewrite <- (app_nil_r (to_e_list _)).
          eapply LfilledBase =>//.
        }
        admit. (* proof about init() goes here *)
      }
    -
      (*iIntros (w) "(-> & Hinv) !>".
      iSplit; eauto.
      iApply wp_invoke_native.
      Set Printing All.
      unfold wp.
      iApply wp_invoke_native.
      iApply instantiation_spec_operational_no_start.
      iModIntro.
      iFrame.
      iSplit; first done.
      iExists 0, 1.
      iExists (String.list_byte_of_string "malloc"), (String.list_byte_of_string "free").
      iExists (malloc 0), (free 0).
      iExists 0%N.
      iExists _.
      iExists [T_i32; T_i32; T_i32; T_i32].
      iExists [].
      iExists alloc_tok.
      iExists alloc_inv.
      iSplitR.
      { iPureIntro.
        rewrite equiv_NoDupEff.
        vm_compute.
        intuition discriminate.
      }
      iSplitR.
      {
        unfold alloc_inv.
        iExists ∅ ([], []).
        

        auto.
      unfold module_inst_resources_wasm.
      iDestruct "Hinstrsc" as "(Hfuncs & Htabs & Hmems & Hglobs)".
      simpl mod_funcs.
      unfold module_inst_resources_func.
      simpl.
      unfold alloc_module.
      cbn delta [mod_exports].
      subst.
      admit.
*)
  Admitted.
End instantiation.

End AllocModule.
