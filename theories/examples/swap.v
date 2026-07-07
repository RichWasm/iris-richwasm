Require Import Stdlib.ZArith.ZArith.

Require Import stdpp.base.

From iris.proofmode Require Import base classes proofmode.

From RichWasm.named_props Require Import named_props custom_syntax.
Require Import RichWasm.wasm.datatypes.
From RichWasm.iris Require Import language.cwp logrel memory runtime util.
Require Import RichWasm.syntax.
Require Import RichWasm.iris.logrel.logrel_properties.

Set Bullet Behavior "Strict Subproofs".

Section swap.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.

  Variable mem_id : N.
  Variable alloc_id : nat.

  Definition swap_type : Core.function_type :=
    InnerFunT (ForallTypeT (VALTYPE (AtomR I32R) AnyRefs)
                 (ForallTypeT (VALTYPE (AtomR I32R) AnyRefs)
                    (MonoFunT [VarT 1; VarT 0] [VarT 0; VarT 1]))).

  Definition alloc_spec (cl : function_closure) : Prop :=
    forall s E B R f i v,
      f.(f_inst).(inst_funcs) !! i = Some alloc_id ->
      N.of_nat alloc_id ↦[wf] cl -∗
      ↪[frame] f -∗
      ↪[RUN] -∗
      CWP [BI_const (VAL_int32 v); BI_call i] @ s; E UNDER B; R
          {{ f'; vs, ⌜f = f'⌝ ∗ N.of_nat alloc_id ↦[wf] cl ∗
                     ∃ a, ⌜vs = [VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N a))]⌝ ∗
                          mem_id ↦[wms][a] serialise_i32 v }}.

  Definition alloc_import (i : nat) (spec : function_closure -> Prop) (inst : instance) : iProp Σ :=
    ∃ cl,
      ⌜inst.(inst_funcs) !! i = Some alloc_id⌝ ∗
      ⌜alloc_spec cl⌝ ∗
      na_inv logrel_nais (ns_fun (N.of_nat alloc_id)) (N.of_nat alloc_id ↦[wf] cl).

  Definition instance_import (i : nat) (ϕ : Core.function_type) (inst : instance) : iProp Σ :=
    ∃ j cl,
      ⌜inst.(inst_funcs) !! i = Some j⌝ ∗
      closure_interp rti sr ϕ senv_empty cl ∗
      na_inv logrel_nais (ns_fun (N.of_nat j)) (N.of_nat j ↦[wf] cl).

  Definition instance_ok (inst : instance) : iProp Σ :=
    "#Halloc" ∷ alloc_import 0 alloc_spec inst ∗
    "#Hswap" ∷ instance_import 1 swap_type inst.

  Definition body : list basic_instruction :=
    [
      BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat 7)));
      BI_call 0; (* alloc *)
      BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat 42)));
      BI_call 0; (* alloc *)
      BI_call 1; (* swap *)
      BI_drop;
      BI_drop
    ].

  Definition example inst : function_closure := FC_func_native inst (Tf [] []) [] body.

  (* the custom sem type is parameterized by what is stored *)
  Definition custom_sem_type (n:nat) : (leibnizO semantic_value -n> iPropO Σ) :=
      (λne (sv:leibnizO semantic_value) , ∃ a a32, ⌜sv = SAtoms [I32A a32]⌝ ∗ ⌜a32 = Wasm_int.Int32.repr (Z.of_N a)⌝
             ∗ mem_id↦[wms][a]serialise_i32 (Wasm_int.Int32.repr n))%I.

  Lemma custom_good (n:nat) : skind_has_stype (SVALTYPE [I32R] AnyRefs) (custom_sem_type n).
  Proof.
    unfold skind_has_stype.
    split.
    - cbn. done.
    - intros sv. iIntros "H".
      unfold custom_sem_type.
      iDestruct "H" as "(%a & %a32 & -> & rest)".
      cbn.
      iPureIntro.
      split; repeat constructor.
      unfold has_areps.
      eexists; split; first done.
      apply Forall2_cons; split; try constructor.
  Qed.

  Theorem example_swap_safe inst :
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
    unfold body.
    iEval (cbn) in "Hfr".


    (* custom alloc *)
    cwp_chomp 2.
    iApply (cwp_seq with "[Hown Hrt Hfr Hrun]").
    {
      iDestruct "Halloc" as "(%cl & %Hgcalloc_idx & %Hgcalloc_spec & Hgcalloc)".
      iApply fupd_cwp.
      iMod (na_inv_acc with "Hgcalloc Hown") as "(>Hgcalloc_cl & Hown & Hclose)".
      1, 2: done.
      iAssert ((▷ N.of_nat alloc_id ↦[wf] cl ={⊤}=∗ na_own logrel_nais ⊤)%I)
        with "[Hclose Hown]" as "Hclose".
      { iIntros "Hcl". iApply "Hclose". iFrame. }

      iApply (cwp_wand with "[Hgcalloc_cl Hfr Hrun]");
        first iApply (Hgcalloc_spec with "Hgcalloc_cl Hfr Hrun").
      1: done.
      iIntros "!> %% H".
      (* iSpecialize ("Hclose" with "[$]"). *)
      iDestruct "H" as "(<- & Hgcalloc_cl & (%a & -> & mem_phys))".
      iSpecialize ("Hclose" with "Hgcalloc_cl").
      instantiate (1:= (λ fr' vs',
          ∃ a,
            ⌜vs' = [VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N a))]⌝ ∗
            ⌜fr' = {| prelude.W.f_locs := []; prelude.W.f_inst := inst |}⌝ ∗
            rt_token rti sr lpall θ ∗
            mem_id↦[wms][a]serialise_i32 (Wasm_int.Int32.repr 7%nat) ∗
            (|={⊤}=> na_own logrel_nais ⊤)
            )%I).
      iExists _.
      iFrame.
      done.
    }
    iIntros (f vs) "H Hfr Hrun".
    iDestruct "H" as "(%a1 & -> & -> & Hrt & Hmem1 & Hown)".
    iApply fupd_cwp.
    iMod "Hown".
    iModIntro.

    (* chomp 3 in order for seq to keep the const somewhere for call 1. Custom alloc again *)
    cwp_chomp 3.
    iApply (cwp_seq with "[Hown Hrt Hfr Hrun]").
    {
      cwp_chomp 1.
      iApply cwp_val_app.
      {
        change ([BI_const ?x]) with (to_consts [x]).
        apply has_values_to_consts.
      }
      iDestruct "Halloc" as "(%cl & %Hgcalloc_idx & %Hgcalloc_spec & Hgcalloc)".
      iApply fupd_cwp.
      iMod (na_inv_acc with "Hgcalloc Hown") as "(>Hgcalloc_cl & Hown & Hclose)".
      1, 2: done.
      iAssert ((▷ N.of_nat alloc_id ↦[wf] cl ={⊤}=∗ na_own logrel_nais ⊤)%I)
        with "[Hclose Hown]" as "Hclose".
      { iIntros "Hcl". iApply "Hclose". iFrame. }

      iApply (cwp_wand with "[Hgcalloc_cl Hfr Hrun]");
        first iApply (Hgcalloc_spec with "Hgcalloc_cl Hfr Hrun").
      1: done.
      iIntros "!> %% H".
      (* iSpecialize ("Hclose" with "[$]"). *)
      iDestruct "H" as "(<- & Hgcalloc_cl & (%a & -> & mem_phys))".
      iSpecialize ("Hclose" with "Hgcalloc_cl").
      unfold fvs_combine.
      change ([?x]++[?y]) with ([x;y]).
      instantiate (1:= (λ fr' vs',
          ∃ a,
            ⌜vs' = [VAL_int32 (Wasm_int.Int32.repr (Z.of_N a1)); VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N a))]⌝ ∗
            ⌜fr' = {| prelude.W.f_locs := []; prelude.W.f_inst := inst |}⌝ ∗
            rt_token rti sr lpall θ ∗
            mem_id↦[wms][a]serialise_i32 (Wasm_int.Int32.repr 42%nat) ∗
            (|={⊤}=> na_own logrel_nais ⊤)
            )%I).
      iExists _.
      iFrame.
      done.
    }
    iIntros (f vs) "H Hfr Hrun".
    iDestruct "H" as "(%a2 & -> & -> & Hrt & Hmem2 & Hown)".
    iApply fupd_cwp.
    iMod "Hown".
    iModIntro.

    (* for convenience *)
    set (a1_32:=(Wasm_int.Int32.repr (Z.of_N a1))).
    set (a2_32:=(Wasm_int.Int32.repr (Z.of_N a2))).

    (* time for call of swap *)
    cwp_chomp 3.
    iApply (cwp_seq with "[-]"). {

      iDestruct "Hswap" as "(%j & %cl & %Hreg_idx & Hcl & Hswap)".
      iApply fupd_cwp.
      iMod (na_inv_acc with "Hswap Hown") as "(Hswap_cl & Hown & Hclose)".
      1, 2: done.
      iAssert ((▷ N.of_nat j ↦[wf] cl ={⊤}=∗ na_own logrel_nais ⊤)%I)
        with "[Hclose Hown]" as "Hclose".
      { iIntros "Hcl2". iApply "Hclose". iFrame. }

      (* we need to instantiate the closure_interp twice with the custom semantic value *)

      unfold swap_type.
      rewrite closure_interp_eq.
      iEval (cbn) in "Hcl".
      iDestruct "Hcl" as "#Hcl".
      iSpecialize ("Hcl" $! (SVALTYPE [I32R] AnyRefs) (SVALTYPE [I32R] AnyRefs)).
      iSpecialize ("Hcl" $! (custom_sem_type 7)).
      iSpecialize ("Hcl" $! eq_refl).
      iSpecialize ("Hcl" $! ltac:(by apply subskind_of_refl)).
      iSpecialize ("Hcl" $! ltac:(by apply custom_good)).

      (* nice - one more time *)
      rewrite inner_closure_interp_eq.
      unfold inner_closure_interp'.
      unfold forall_type_interp.

      iSpecialize ("Hcl" $! (SVALTYPE [I32R] AnyRefs) (SVALTYPE [I32R] AnyRefs) (custom_sem_type 42)
                     eq_refl ltac:(by apply subskind_of_refl) ltac:(by apply custom_good)).

      rewrite inner_closure_interp_eq.
      unfold inner_closure_interp'.
      unfold mono_closure_interp.

      (* it's long and scary but we can do it :) *)
      destruct cl as [ist [ts1 ts2] tlocs es | o b].
      2: {
        cbn.
        iDestruct "Hcl" as "#Hcl".
        done. (* that was silly *)
      }
      iDestruct "Hcl" as "(%trans1 & %trans2 & rest)".
      cbn in trans1.
      inversion trans1; subst; clear trans1.
      cbn in trans2.
      inversion trans2; subst; clear trans2.
      iDestruct "rest" as "#Hcl".

      iAssert (values_interp1 (map (type_interp rti sr) [VarT 1; VarT 0])
                (senv_insert_type (SVALTYPE [I32R] AnyRefs) (SVALTYPE [I32R] AnyRefs) (custom_sem_type 42)
                   ([], [], [], [(SVALTYPE [I32R] AnyRefs, (SVALTYPE [I32R] AnyRefs, (custom_sem_type 7)))]))
                [I32A ((Wasm_int.Int32.repr (Z.of_N a1)));I32A (Wasm_int.Int32.repr (Z.of_N a2))])
        with "[Hmem1 Hmem2]" as "Hvalues". {
        iClear "Hcl".
        cbn.
        iExists [[I32A a1_32];[I32A a2_32]].
        iSplitR; first done.
        cbn.
        iSplitL "Hmem1".
        2: iSplitL; try done.
        all: rewrite type_interp_eq; cbn.
        all: iExists (SVALTYPE [I32R] AnyRefs); iSplitR; first done.
        all: iSplitR.
        1,3: iPureIntro; split; repeat constructor; try done.
        1-2: eexists; split; first done; try constructor; done.
        all: iFrame.
        all: iExists _; iSplitR; first done; done.
      }
      (* note: os1 = [I32A a1_32; I32A a2_32] *)

      iAssert ((atoms_interp [I32A a1_32; I32A a2_32] [VAL_int32 a1_32; VAL_int32 a2_32])%I)
        with "[]" as "atom_interp_to_use". {
        iClear "Hcl".
        cbn.
        done.
      }
      (* and with that, vs1 := [VAL_int32 a1_32; VAL_int32 a2_32] *)
      iSpecialize ("Hcl" $! [VAL_int32 a1_32; VAL_int32 a2_32]  [I32A a1_32; I32A a2_32] θ).

      iModIntro.
      change ([?x;?y;?z]) with ([x;y]++[z]).
      iApply (cwp_call with "[$] [$] [$] [-]"); try by (cbn; done).
      {
        change ([BI_const ?x; BI_const ?y]) with (to_consts [x;y]).
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
                           values_interp1 [type_interp rti sr (VarT 0); type_interp rti sr (VarT 1)]
                             ([], [], [],
                              [(SVALTYPE [I32R] AnyRefs, (SVALTYPE [I32R] AnyRefs, custom_sem_type 42));
                               (SVALTYPE [I32R] AnyRefs, (SVALTYPE [I32R] AnyRefs, custom_sem_type 7))])
                             os2) ∗
                        (∃ θ' : address_map, rt_token rti sr lpall θ') ∗ na_own logrel_nais ⊤)%I).
      cbn.
      iApply (cwp_wand with "[Hcl]"); first iApply "Hcl".
      iIntros (f v) "(Hatom & Hrt & Hown)".
      iFrame "Hrt". iFrame "Hown".
      (* almost iframeable, but need that length v = 1 which isn't hard *)
      iDestruct "Hatom" as "(%os2 & Hoa & Hval)".
      iAssert (⌜length v = 2⌝%I) with "[Hoa Hval]" as "%hlen". {
        change (values_interp1 [type_interp rti sr ?x; type_interp rti sr ?y] ?s ?o) with
          (values_interp rti sr s [x;y] o).
        iPoseProof (values_interp_cons_l with "[$Hval]") as "(%o1 & %o2 & -> & Hval1 & Hval2)".
        rewrite values_interp_one_eq.
        rewrite !value_interp_eq.
        cbn -[atoms_interp].
        iDestruct "Hval1" as "(%sκ & %toinv & _ & (%a & %a32 & %toinv2 & _))".
        inversion toinv; subst; clear toinv; inversion toinv2; subst; clear toinv2.
        iDestruct "Hval2" as "(%sκ & %toinv & _ & (%a22 & %a232 & %toinv2 & _))".
        inversion toinv; subst; clear toinv; inversion toinv2; subst; clear toinv2.
        iPoseProof (big_sepL2_length with "[$Hoa]") as "%hlen".
        cbn in hlen.
        done.
      }
      iFrame.
      done.
    (* note that, ideally, you wouldn't do cwp_wand in such a basic manner. You would add one some of these length v facts
     but oh well. *)

    }
    (* just 2 drops left! *)
    iIntros (f v) "H Hfr Hrun".
    iDestruct "H" as "((%os2 & Hoa & Hval) & Hrt & Hown)".
    clear dependent a1.
    clear dependent a2.

    (* first redo a bit of the work from the length v lmao *)
    change (values_interp1 [type_interp rti sr ?x; type_interp rti sr ?y] ?s ?o) with
      (values_interp rti sr s [x;y] o).
    iPoseProof (values_interp_cons_l with "[$Hval]") as "(%o1 & %o2 & -> & Hval2 & Hval1)".
    rewrite values_interp_one_eq.
    rewrite !value_interp_eq.
    cbn -[atoms_interp].
    iDestruct "Hval2" as "(%sκ & %toinv & %sksv1 & (%a2 & %a2_32 & %toinv2 & %Ha2_32 & Hmem2))".
    inversion toinv; subst; clear toinv; inversion toinv2; subst; clear toinv2.
    iDestruct "Hval1" as "(%sκ & %toinv & _ & (%a1 & %a1_32 & %toinv2 & %Ha1_32 & Hmem1))".
    inversion toinv; subst; clear toinv; inversion toinv2; subst; clear toinv2.

    iEval (cbn) in "Hoa".
    iPoseProof (atoms_interp_cons_l with "Hoa") as "(%v2 & %v1 & -> & Hoa2 & Hoa1)".
    rewrite atoms_interp_one_inv.
    iDestruct "Hoa1" as "(%v & -> & Hoa1)".
    Transparent atom_interp.
    iEval (cbn) in "Hoa1"; iEval (cbn) in "Hoa2".
    iDestruct "Hoa2" as "->"; iDestruct "Hoa1" as "->".

    (* NOTE: here, you can see that the values have indeed been switched! *)

    cwp_chomp 3.
    iApply (cwp_seq with "[Hfr Hrun]"). {
      cwp_chomp 1.
      iApply cwp_val_app.
      {
        change [BI_const ?x] with (to_consts [x]).
        apply has_values_to_consts.
      }
      iApply (cwp_drop with "[$] [$] [-]").
      unfold fvs_combine.
      iModIntro.
      clear_nils.

      now instantiate
        (1:= (λ f' v,
            ⌜f' = f⌝ ∗
             ⌜v = [VAL_int32 (Wasm_int.Int32.repr (Z.of_N a2))]⌝)%I).
    }
    iIntros (ft v) "(-> & ->) Hfr Hrun".
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
    (* note: slightly scary that nothing happened with the memories? Probably fine? *)
  Qed.

End swap.
