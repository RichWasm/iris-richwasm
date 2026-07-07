Require Import Stdlib.ZArith.ZArith.

Require Import stdpp.base.

From iris.proofmode Require Import base classes proofmode.

From RichWasm.named_props Require Import named_props custom_syntax.
Require Import RichWasm.wasm.datatypes.
From RichWasm.iris Require Import language.cwp logrel memory runtime util.
Require Import RichWasm.syntax.
Require Import RichWasm.iris.logrel.load_common.
Require Import RichWasm.iris.logrel.store_common.
Require Import RichWasm.iris.logrel.logrel_properties.

Set Bullet Behavior "Strict Subproofs".

Section dup.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.

  Definition dup_type : Core.function_type :=
    InnerFunT (ForallTypeT (VALTYPE (AtomR PtrR) GCRefs)
                 (MonoFunT
                    [VarT 0]
                    [RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                       (StructT (MEMTYPE (ProdS [RepS (AtomR PtrR); RepS (AtomR PtrR)]) GCRefs)
                          [SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0);
                           SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0)])])).

  Definition instance_import (i : nat) (ϕ : Core.function_type) (inst : instance) : iProp Σ :=
    ∃ j cl,
      ⌜inst.(inst_funcs) !! i = Some j⌝ ∗
        closure_interp rti sr ϕ senv_empty cl ∗
        na_inv logrel_nais (ns_fun (N.of_nat j)) (N.of_nat j ↦[wf] cl).

  Definition instance_ok (inst : instance) : iProp Σ :=
    "%Hgcmem" ∷ ⌜inst.(inst_memory) !! 0 = Some sr.(sr_mem_gc)⌝ ∗
    "#Hgcalloc" ∷
      instance_rt_func_interp (Mk_funcidx 0) sr.(sr_func_gcalloc) (spec_gcalloc rti sr) inst ∗
    "#Hregisterroot" ∷
      instance_rt_func_interp (Mk_funcidx 1) sr.(sr_func_registerroot) (spec_registerroot rti sr) inst ∗
    "#Hdup" ∷ instance_import 2 dup_type inst.

  Definition body : list basic_instruction :=
    [
      BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat 1)));
      BI_call 0; (* gcalloc *)
      BI_tee_local 0; (* ref *)
      BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat 20)));
      BI_store 0 T_i32 None 0%N 1%N; (* gcmem *)
      BI_get_local 0; (* ref *)
      BI_call 1; (* registerroot *)
      BI_call 2; (* dup *)
      BI_drop
    ].


  Definition example inst : function_closure := FC_func_native inst (Tf [] []) [T_i32] body.

  Theorem example_dup_safe inst :
    instance_ok inst ⊢ closure_interp rti sr (InnerFunT (MonoFunT [] [])) senv_empty (example inst).
  Proof.
    iIntros "@".
    rewrite closure_interp_eq.
    iSplitR; first done.
    iSplitR; first done.
    iIntros "!> !> %%% Hvs1 Hos1 Hrt Hown Hfr Hrun".

    (* step 1 some things are empty *)
    change (values_interp1 (map (type_interp rti sr) []) senv_empty os1) with
      (values_interp rti sr senv_empty [] os1).
    iEval (cbn) in "Hos1".
    iDestruct "Hos1" as "(%fake_oss & -> & bigsep)".
    iPoseProof (big_sepL2_length with "[$bigsep]") as "%hlen1".
    destruct fake_oss; [|cbn in hlen1; inversion hlen1].
    iEval (cbn) in "Hvs1".
    iPoseProof (big_sepL2_length with "[$Hvs1]") as "%hlen2".
    destruct vs1; [|cbn in hlen2; inversion hlen2].
    clear_nils.
    iClear "Hvs1 bigsep". clear hlen1 hlen2.

    (* gcalloc *)
    cwp_chomp 2.
    iApply (cwp_seq with "[Hown Hrt Hfr Hrun]").
    {
      iDestruct "Hgcalloc" as "(%cl & %Hgcalloc_spec & %Hgcalloc_idx & Hgcalloc)".
      iApply fupd_cwp.
      iMod (na_inv_acc with "Hgcalloc Hown") as "(>Hgcalloc_cl & Hown & Hclose)".
      1, 2: done.
      iAssert ((▷ N.of_nat sr.(sr_func_gcalloc) ↦[wf] cl ={⊤}=∗ na_own logrel_nais ⊤)%I)
        with "[Hclose Hown]" as "Hclose".
      { iIntros "Hcl". iApply "Hclose". iFrame. }

      iApply (cwp_wand with "[Hgcalloc_cl Hrt Hfr Hrun]");
        first iApply (Hgcalloc_spec with "Hgcalloc_cl Hrt Hfr Hrun").
      1, 2: done.
      iIntros "!> %% H".
      (* iSpecialize ("Hclose" with "[$]"). *)
      iDestruct "H" as
        "(<- & Hcl & (%θ' & %ℓ & %ta & %ta32 & %ws & -> &
        Htarepr & Hptrrepr & Hrt' & Hlayout & Hheap))".
      iSpecialize ("Hclose" with "Hcl").
      instantiate (1:= (λ fr' vs',
          ∃ θ' ℓ ta ta32 ws cl,
            ⌜vs' = [VAL_int32 ta32]⌝ ∗
            ⌜fr' = {| prelude.W.f_locs := n_zeros [T_i32]; prelude.W.f_inst := inst |}⌝ ∗
            ⌜numerics.N_i32_repr ta ta32⌝ ∗
            ⌜repr_pointer θ' (PtrHeap MemGC ℓ) ta⌝ ∗
            rt_token rti sr lpall θ' ∗
            ℓ ↦layout repeat util.FlagInt (Wasm_int.nat_of_uint i32m (Wasm_int.Int32.repr 1%nat)) ∗
            ℓ ↦heap ws ∗
            (|={⊤}=> na_own logrel_nais ⊤)
            )%I).
      iExists _, _, _, _, _, _.
      iFrame.
      done.
    }
    iIntros (f vs) "H Hfr Hrun".
    clear θ.
    iDestruct "H" as "(%θ & %ℓ & %ta & %ta32 & %ws & %cl & -> & -> & %Hrepr & %Hreprptr
    & Hrt & Hℓ_fs & Hℓ_ws & Hown)".
    iApply fupd_cwp.
    iMod "Hown".
    iModIntro. (* yayyyy *)

    cwp_chomp 2.
    (* bi tee local *)
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      pose proof cwp_local_tee.
      specialize H with (i:=0) (v:=VAL_int32 ta32).
      iApply (H with "[] [$] [$]").
      1: cbn; lia.
      cbn.
      now instantiate
        (1:= (λ f v,
            ⌜f = {| prelude.W.f_locs := [VAL_int32 ta32]; prelude.W.f_inst := inst |}⌝ ∗
             ⌜v = [VAL_int32 ta32]⌝)%I).
    }
    iIntros (f v) "(-> & ->) Hfr Hrun".


    iEval (cbn) in "Hℓ_fs".
    change (repeat util.FlagInt (Z.to_nat (Wasm_int.Int32.Z_mod_modulus 1%nat)))
      with [util.FlagInt].
    iAssert (⌜∃ w, ws = [w]⌝%I) with "[Hrt Hℓ_fs Hℓ_ws]" as "%hi". {
      (* by peeking into runtime token *)
      open_rt "Hrt".
      iCombine "Hℓ_ws Hheap" gives "%Hhm".
      iCombine "Hℓ_fs Hlayout" gives "%Hlm".
      iPureIntro.
      unfold layout_ok in Hlayoutok.
      specialize (Hlayoutok ℓ).
      rewrite Hhm in Hlayoutok.
      rewrite Hlm in Hlayoutok.
      inversion Hlayoutok; subst.
      specialize (H1 ltac:(auto)).
      apply Forall2_length in H1.
      destruct ws as [|w [|g h]]; cbn in H1; inversion H1; try done.
      eexists; done.
    }
    destruct hi as (w & ->).
    inversion Hreprptr; subst.


    assert (0 + 1 ≤ length [w]) by (cbn; lia).

    (** store the number *)
    cwp_chomp 3.
    iApply (cwp_seq with "[Hfr Hrun Hrt Hℓ_ws Hℓ_fs]"). {
      open_rt "Hrt".
      iCombine "Hℓ_ws Hheap" gives "%Hhm".
      cbn in Hrepr.
      iPoseProof (heap_memory_dom_eq with "Hheapmem") as "%Hdomθhm".
      iPoseProof (heap_memory_delete sr ℓ _ _ [w] with "Hheapmem") as
        "(HR & Hheapcont)"; eauto.
      iCombine "Hℓ_fs Hlayout" gives "%Hlm".
      set (k:= (a-1)%N) in *.
      iDestruct "HR" as "(%ns & %ns32 & %Nsn32repr & Hwms & WordInterp)".
      iEval (cbn) in "Hwms".
      pose proof (cwp_store) as cw.
      specialize cw with (off:=1%N) (k:=k) (a:=0%N).
      assert (HAK: a = (k+1)%N). {
        subst k.
        assert (4 <= a)%N by (by eapply mod_bound_nonzero). lia.
      }
      rewrite HAK.
      (* I need some lengths about ns from words interp *)
      iPoseProof (big_sepL2_length with "[$WordInterp]") as "%hlenns".
      destruct ns as [|n [|o b]];
        cbn in hlenns; inversion hlenns; try done; clear hlenns.
      apply Forall2_length in Nsn32repr as ns32len.
      destruct ns32 as [|n32 [|o b]];
        cbn in ns32len; inversion ns32len; try done; clear ns32len.

      iApply fupd_cwp.
      iMod (ghost_map_update [WordInt 20%N] with "Hheap Hℓ_ws") as "[Hheap' Hpt']".
      iApply (cwp_store with "[$Hwms] [-Hfr Hrun] [$] [$]"); try done.


      iModIntro.
      iIntros "Hphysnew".
      rewrite <- HAK.
      subst k. (* cool don't wanna worry about it *)
      iEval (cbn [bits]) in "Hphysnew".

      (* need to use the heapcont *)

      (* temporary: *)
      assert (Hreprnew: N_i32_repr 20%N (Wasm_int.Int32.repr 20%nat)). {
        unfold N_i32_repr.
        cbn.
        rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia.
        done.
      }
      iAssert (words_interp θ MemGC [WordInt 20%N] [20%N]) as "newword". {
        cbn.
        done.
      }
      iSpecialize ("Hheapcont" $! [WordInt 20%N]).
      iAssert (heap_memory sr θ (<[ℓ:=[WordInt 20]]> hm)) with "[Hphysnew Hheapcont newword]"
        as "Hnewheap". {
        iApply "Hheapcont".
        iExists [20%N], [Wasm_int.Int32.repr 20%nat].
        iFrame "∗". iFrame "#".
        iPureIntro.
        apply Forall2_cons; split; done.
      }
      iAssert (rt_token rti sr lpall θ) with
        "[Haddr Hroot Hlayout Hrti Hrootmem Hheap' Hnewheap]" as "Hrt". {
        unfold rt_token.
        iExists rm, lm, (<[ℓ:=[WordInt 20%N]]> hm).
        iFrame.
        iSplitR; first done. iSplitR; first done.
        iPureIntro.
        eapply heap_ok_update_weak; try done.
        intros _.
        constructor; try done.
      }
      iClear "WordInterp". (* old words don't want them back *)
      clear dependent hm. clear dependent lm. clear Hinj.
      clear dependent rm.
      instantiate (1:= (λ f' v',
            ⌜f' = {| W.f_locs := [VAL_int32 ta32]; W.f_inst := inst |}⌝ ∗ ⌜v' = []⌝ ∗
            words_interp θ MemGC [WordInt 20] [20%N] ∗
            ℓ ↦layout [FlagInt] ∗
            ℓ ↦heap [WordInt 20] ∗
            rt_token rti sr lpall θ
                       )%I).
      iFrame.
      iFrame "#".
      done.
    }
    (* yayyyyy we stored a number! *)
    iIntros (f v) "(-> & -> & Hnewword & Hℓ_fs & Hℓ_ws & Hrt) Hfr Hrun".
    clear_nils.

    (* at this point, we can start constructing the val and word interp dup will need *)
    set (τ_num := (SerT (MEMTYPE (RepS (AtomR I32R)) NoRefs)
                      (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T)))).
    set (τ := RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Mut τ_num).
    iPoseProof (na_inv_alloc logrel_nais ⊤ (ns_ref ℓ)
            (∃ ws : leibnizO (list word), ℓ ↦layout [FlagInt] ∗ ℓ ↦heap ws ∗
              ▷ type_interp rti sr τ_num senv_empty (SWords ws))) as "maybe".
    iSpecialize ("maybe" with "[Hℓ_fs Hℓ_ws Hnewword]"). {
      iModIntro.
      iExists [WordInt 20].
      iFrame.
      cbn.
      unfold τ_num.
      iModIntro.
      rewrite type_interp_eq.
      cbn.
      iExists (SMEMTYPE 1 NoRefs).
      iSplitR; first done.
      iSplitR; first (iPureIntro; split; try done; constructor; try done).
      (* Compute (flat_map serialize_atom [I32A (Wasm_int.Int32.repr 20%nat)]). *)
      iExists [I32A (Wasm_int.Int32.repr 20%nat)].
      iSplitR; first (cbn; done).
      rewrite type_interp_eq.
      cbn.
      iExists (SVALTYPE [I32R] NoRefs); iSplitR; first done.
      iSplitL; last done.
      iPureIntro.
      split; try repeat constructor.
      unfold has_areps.
      eexists; split; first done.
      apply Forall2_cons; split; try done.
    }
    iApply fupd_cwp.
    iMod "maybe".
    iModIntro.
    iDestruct "maybe" as "#valinterp".

    clear cl.
    (* i need to get local real quick *)
    cwp_chomp 1.
    iApply (cwp_seq with "[Hfr Hrun]"). {
      iApply (cwp_local_get with "[] [$] [$]").
      { cbn. done. }
      iModIntro.
      now instantiate
        (1:= (λ f v,
            ⌜f = {| prelude.W.f_locs := [VAL_int32 ta32]; prelude.W.f_inst := inst |}⌝ ∗
             ⌜v = [VAL_int32 ta32]⌝)%I).
    }
    iIntros (f v) "(-> & ->) Hfr Hrun".

    (* reg root *)
    cwp_chomp 2.
    iApply (cwp_seq with "[Hown Hrt Hfr Hrun]").
    {
      iDestruct "Hregisterroot" as "(%cl & %Hreg_spec & %Hreg_idx & Hreg)".
      iApply fupd_cwp.
      iMod (na_inv_acc with "Hreg Hown") as "(>Hreg_cl & Hown & Hclose)".
      1, 2: done.
      iAssert ((▷ N.of_nat sr.(sr_func_registerroot) ↦[wf] cl ={⊤}=∗ na_own logrel_nais ⊤)%I)
        with "[Hclose Hown]" as "Hclose".
      { iIntros "Hcl". iApply "Hclose". iFrame. }

      cbn in Hreg_idx.
      iApply (cwp_wand with "[Hreg_cl Hrt Hfr Hrun]");
        first iApply (Hreg_spec with "Hreg_cl Hrt Hfr Hrun").
      1, 2, 3: cbn; done.
      iIntros "!> %% H".
      iDestruct "H" as
        "(<- & Hcl & Hrt & (%ar & %tar & %tar32 & -> & newreprtar & reprroot & Hroot))".
      iSpecialize ("Hclose" with "Hcl").
      instantiate (1:= (λ fr' vs',
          ∃ ar tar tar32,
            ⌜vs' = [VAL_int32 tar32]⌝ ∗
            ⌜fr' = {| W.f_locs := [VAL_int32 ta32]; W.f_inst := inst |}⌝ ∗
            ⌜numerics.N_i32_repr tar tar32⌝ ∗
            ⌜repr_root_pointer (RootHeap MemGC ar) tar⌝ ∗
            rt_token rti sr lpall θ ∗
            ar ↦root ℓ ∗
            (|={⊤}=> na_own logrel_nais ⊤)
            )%I).
      iExists _, _, _.
      iFrame.
      done.
    }
    iIntros (f v) "(%ar & %tar & %tar32 & -> & -> & %Nreprtar & %repr_root &
    Hrt & Har_root & Hown) Hfr Hrun".
    iApply fupd_cwp.
    iMod "Hown"; iModIntro.

    (* time for the dup call! *)
    cwp_chomp 2.
    iApply (cwp_seq with "[-]").
    {
      unfold instance_import.
      unfold instance_rt_func_interp.
      iDestruct "Hdup" as "(%j & %cl & %Hreg_idx & Hcl & Hdup)".
      iApply fupd_cwp.
      iMod (na_inv_acc with "Hdup Hown") as "(Hdup_cl & Hown & Hclose)".
      1, 2: done.
      iAssert ((▷ N.of_nat j ↦[wf] cl ={⊤}=∗ na_own logrel_nais ⊤)%I)
        with "[Hclose Hown]" as "Hclose".
      { iIntros "Hcl2". iApply "Hclose". iFrame. }

      (* okay we pretty much have what we need. we just need to
       (a) show cl is FC_func_native (Tf ts1 ts2)*)
      (* this will involve unraveling hcl a bit *)
      unfold dup_type.
      rewrite closure_interp_eq.
      iEval (cbn) in "Hcl".
      (* and here is where we need to instantiate the type var! *)
      (* our type var is ref gc mut -> i32 (although actually i31 more acc)
       but it doesn't actually make any difference. mut/imm also no diff. fun! *)
      (* in the other example, you would not inst with value_interp *)
      iDestruct "Hcl" as "#Hcl".
      iSpecialize ("Hcl" $! (SVALTYPE [PtrR] GCRefs) (SVALTYPE [PtrR] GCRefs)
                     (value_interp rti sr senv_empty τ)).
      iSpecialize ("Hcl" $! eq_refl).
      iSpecialize ("Hcl" $! ltac:(by apply subskind_of_refl)).
      iAssert (⌜skind_has_stype (SVALTYPE [PtrR] GCRefs)
                 (value_interp rti sr senv_empty τ)⌝%I) as "#temp".
      {
        (* in the other proof, this will change *)
        iPureIntro.
        eapply (kinding_sound rti sr fc_empty senv_empty _ (VALTYPE (AtomR PtrR) GCRefs) _);
          try done.
        - subst τ_num τ.
          repeat econstructor.
        - unfold sem_env_interp. unfold kind_ctx_interp, type_ctx_interp.
          cbn.
          split; first done.
          constructor.
      }
      iSpecialize ("Hcl" with "temp"). iClear "temp".

      rewrite inner_closure_interp_eq.
      unfold inner_closure_interp'.
      unfold mono_closure_interp.

      (* it's long and scary but we can do it :) *)
      destruct cl as [ist [ts1 ts2] tlocs es | o b]; try done.
      iDestruct "Hcl" as "(%trans1 & %trans2 & rest)".
      cbn in trans1.
      inversion trans1; subst; clear trans1.
      cbn in trans2.
      inversion trans2; subst; clear trans2.
      iDestruct "rest" as "#Hcl".
      set (res_type := [RefT (VALTYPE (AtomR PtrR) GCRefs)
          (BaseM MemGC) Imm
          (StructT
            (MEMTYPE (ProdS [RepS (AtomR PtrR); RepS (AtomR PtrR)])
                GCRefs)
            [SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0);
              SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0)])]) in *.
      iAssert ((atoms_interp [PtrA (PtrHeap MemGC ℓ)] [VAL_int32 tar32])%I)
        with "[Har_root]" as "atom_interp_to_use". {
        iClear "Hcl".
        cbn.
        iSplitL; last done.
        iExists tar, tar32.
        iSplitR; first done; iSplitR; first done.
        iExists ((RootHeap MemGC ar)).
        iSplitR; first done.
        cbn. iFrame.
      }
      iSpecialize ("Hcl" $! [VAL_int32 tar32] [PtrA (PtrHeap MemGC ℓ)] θ).
      (* we're gonna have to do an actual, got it *)
      iAssert (values_interp1 (map (type_interp rti sr) [VarT 0])
               ([], [], [],
                [(SVALTYPE [PtrR] GCRefs,
                  (SVALTYPE [PtrR] GCRefs, value_interp rti sr senv_empty τ))])
               [PtrA (PtrHeap MemGC ℓ)])
        with "[]" as "values_interp_to_use". {
        cbn.
        iClear "Hcl".
        iExists [[PtrA (PtrHeap MemGC ℓ)]].
        iSplitR; first done.
        cbn.
        iSplitL; last done.
        rewrite type_interp_eq.
        cbn.
        iExists (SVALTYPE [PtrR] GCRefs).
        iSplitR; first done.
        iSplitR; first iPureIntro.
        {
          split; econstructor; try constructor; try done.
          apply Forall2_cons; split; last done.
          done.
        }
        unfold τ.
        rewrite value_interp_eq.
        cbn.
        iExists (SVALTYPE [PtrR] GCRefs).
        iSplitR; first done.
        iSplitR; first iPureIntro.
        {
          split; econstructor; try constructor; try done.
          apply Forall2_cons; split; last done.
          done.
        }
        iExists ℓ, [FlagInt]. iSplitR; first done.
        iFrame "#".
      }
       iModIntro.
      change ([?x;?y]) with ([x]++[y]).
      iApply (cwp_call with "[$] [$] [$] [-]"); try by (cbn; done).
      {
        change ([BI_const (VAL_int32 tar32)]) with (to_consts [VAL_int32 tar32]).
        apply has_values_to_consts.
      }
      iModIntro.
      iIntros "Hfr Hrun Hdup_cl".
      iSpecialize ("Hclose" with "Hdup_cl").
      iApply fupd_cwp.
      iMod "Hclose". iModIntro.
      iRename "Hclose" into "Hown".

      iSpecialize ("Hcl" with "[$] [$] [$] [$] [$] [$]").
      Opaque atoms_interp. Opaque values_interp1.
      Opaque atom_interp.
      cbn.
      instantiate (1:= (λ (_ : frame) (vs2 : leibnizO (list value)),
                        (∃ os2 : leibnizO (list atom), atoms_interp os2 vs2 ∗
                           values_interp1
                             [type_interp rti sr
                                (RefT (VALTYPE (AtomR PtrR) GCRefs)
                                   (BaseM MemGC) Imm
                                   (StructT
                                      (MEMTYPE (ProdS [RepS (AtomR PtrR); RepS (AtomR PtrR)])
                                         GCRefs)
                                      [SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0);
                                       SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0)]))]
                             ([], [], [],
                              [(SVALTYPE [PtrR] GCRefs,
                                (SVALTYPE [PtrR] GCRefs, value_interp rti sr senv_empty τ))])
                             os2) ∗
                        (∃ θ' : address_map, rt_token rti sr lpall θ') ∗
                        na_own logrel_nais ⊤)%I).
      cbn.
      iApply (cwp_wand with "[Hcl]"); first iApply "Hcl".
      iIntros (f v) "(Hatom & Hrt & Hown)".
      iFrame "Hrt". iFrame "Hown".
      (* almost iframeable, but need that length v = 1 which isn't hard *)
      iDestruct "Hatom" as "(%os2 & Hoa & Hval)".
      Transparent values_interp1.
      fold res_type.
      clear res_type.
      set (res_type := (RefT (VALTYPE (AtomR PtrR) GCRefs) (BaseM MemGC) Imm
                   (StructT (MEMTYPE (ProdS [RepS (AtomR PtrR); RepS (AtomR PtrR)]) GCRefs)
                      [SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0);
                       SerT (MEMTYPE (RepS (AtomR PtrR)) GCRefs) (VarT 0)]))).
      change (values_interp1 [type_interp rti sr res_type] ?s os2) with
        (values_interp rti sr s [res_type] os2).
      rewrite values_interp_one_eq.
      unfold res_type.
      iPoseProof (value_interp_ref_sz with "[$Hval]") as "%hlen".
      destruct os2 as [|o [|g h]]; cbn in hlen; inversion hlen; try done; clear hlen.
      iPoseProof (big_sepL2_length with "[$Hoa]") as "%hlen2".
      destruct v as [|v [|g h]]; cbn in hlen2; inversion hlen2; try done; clear hlen2.
      iSplitL; try done.
      iExists [o].
      iFrame.
      fold res_type.
      change (values_interp1 [type_interp rti sr res_type] ?s [o]) with
        (values_interp rti sr s [res_type] [o]).
      rewrite values_interp_one_eq.
      done.
    }
    (* just drop left! *)
    iIntros (f v) "H Hfr Hrun".
    iDestruct "H" as "((%os2 & Hoa & Hval) & Hrt & Hown)".
    change (values_interp1 [type_interp rti sr ?t] ?s os2) with
      (values_interp rti sr s [t] os2).
    rewrite values_interp_one_eq.
    iPoseProof (value_interp_ref_sz with "[$Hval]") as "%hlen".
    destruct os2 as [|o [| g h]]; cbn in hlen; inversion hlen; try done; clear hlen.
    iPoseProof (big_sepL2_length with "[$Hoa]") as "%hlen2".
    destruct v as [|v [|g h]]; cbn in hlen2; inversion hlen2; try done; clear hlen2.

    cwp_chomp 2.
    iApply (cwp_drop with "[$] [$] [-]").
    iModIntro; cbn.
    Transparent atoms_interp. Transparent atom_interp.
    iFrame.
    iExists [].
    iSplitR; first (cbn; done).
    iExists [].
    iSplitR; first done.
    cbn.
    done.
    Unshelve.
    done.
  Qed.

End dup.
