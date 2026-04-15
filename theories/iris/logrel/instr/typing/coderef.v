Require Import RichWasm.iris.logrel.instr.typing.common.
From mathcomp Require Import ssrbool eqtype.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section coderef.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma empty_closure_interp se ϕ cl :
    closure_interp rti sr senv_empty ϕ cl -∗
    closure_interp rti sr se ϕ cl.
  Proof.
    (* This seems true? TODO *)
    iIntros "H".
    cbn.

  Admitted.

  Lemma compat_coderef M F L wt wt' wtf wl wl' wlf es' i ϕ :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let τ := CodeRefT (VALTYPE (AtomR I32R) NoRefs) ϕ in
    let ψ := InstrT [] [τ] in
    M.(mc_table) !! i = Some ϕ ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ICodeRef ψ i)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmas τ ψ Htable Hok Hcg.
    cbn in Hcg; inversion Hcg; subst; clear Hcg.

    iIntros (??????????) "@@@@@@@@@@".

    (* For fun, lots of things are [] *)
    iPoseProof (values_interp_nil_l with "[$Hos]") as "->".
    iPoseProof (atoms_interp_nil_l with "[$Hvs]") as "->".
    apply Is_true_true in H0; apply all2_size in H0.
    cbn in H0. destruct evs; [|cbn in H0; inversion H0]; clear H0.
    iClear "Hvs Hos". (* delete later if anything *)
    clear_nils.

    (* Plan of attack! *)
    (* first, cwp_seq to get first bi_const out of there *)
    (* one more cwp_seq to isolate get_global *)
    (* then run the get_global through cwp_global_get *)
    (* the has_values evs vs will give me back a const *)
    (* put everything back together *)
    (* then we can do cwp_binop *)


    (* First, we have some things we have to do some before evars are
       introducted. *)

    (* This is used for first goal of cwp_global_get *)
    iDestruct "Hinst" as
      "(%HInstTypes & #HRunInterp & #HFuncInterp & #HTableInterp & %HMM & %HGC)".
    iDestruct "HTableInterp" as "(%HInstTab &
      (%i_off & %off & #HTableEntryInterp & %HInstGlobs & #HWGInvariant))".

    (* this is necessary for a post condition later *)
      (* okay so if I don't have the True there, temp has type iProp Σ
         however, I need temp to have type iPropI Σ. ∗ True forces
         it to be iPropI Σ.
         now, I don't get why this works. And this is a bit ugly. But
         it's hopefully harmless and hopefully one day made better
       *)
    set (temp := (N.of_nat i_off ↦[wg] {| W.g_mut := MUT_mut; W.g_val := VAL_int32 (Wasm_int.int_of_Z i32m off) |} ∗ True)%I).

    (* Opening the invariant before the seq *)
    iApply fupd_cwp.
    iMod (na_inv_acc with "HWGInvariant Hown") as "(>Hwg & Hown & HcloseWG)".
    1,2: done.
    iModIntro.

    change ([?x;?y;?z]) with ([x;y]++[z]).
    iApply (cwp_seq with "[Hfr Hrun Hwg]").
    {

      change ([?x;?y]) with ([x]++[y]).
      iApply cwp_val_app.

      { (* prove has_values evs vs *)
        instantiate (1:=[(instruction.W.VAL_int32 (Wasm_int.Int32.repr i))]).
        cbn; auto.
        rewrite andb_true_r.
        apply Is_true_true.
        by apply/eqP.
      }

      (* okay so if I don't have the True there, temp has type iProp Σ
         however, I need temp to have type iPropI Σ. ∗ True forces
         it to be iPropI Σ.
         now, I don't get why this works. And this is a bit ugly. But
         it's hopefully harmless and hopefully one day made better
       *)
      unfold fvs_combine.
      instantiate (1 :=
        (λ f' vs', (⌜f'=fr⌝ ∗
                    ⌜vs' = [instruction.W.VAL_int32 (Wasm_int.Int32.repr i)] ++
                             [VAL_int32 (Wasm_int.Int32.repr off)]⌝ ∗
                    temp)%I)).


      iApply (cwp_wand with "[Hfr Hrun Hwg]").
      {
        (* cwp_global_get has six goals:
           1. exactly HInstGlobs
           2. autos to get gval, which is v
           3. the invariant Hwg (framed out)
           4. The post conidtion applied to v
           5. frame resource (framed out)
           6. run resource (framed out)
           so only 3 goals will show up
           I have a guess to the post condition rn
         *)
        iApply (cwp_global_get with "[$Hwg] [] [$Hfr] [$Hrun]").
        - by apply HInstGlobs.
        - done.
        - (* this might need to change *)
          by instantiate
            (1 := (λ f' v', (⌜f' = fr⌝ ∗ ⌜v' = [VAL_int32 (Wasm_int.Int32.repr off)]⌝)%I)).
      }

      iIntros (f v) "((-> & ->) & Hwg)".
      (* I need to make sure Hwg is incorporated somehow *)
      iSplitR; auto.
      iSplitR; auto.
      iFrame.
    }
    unfold temp.

    iIntros (??) "Pre Hfr Hrun".
    iDestruct "Pre" as "(-> & -> & Hwg & _)".

    (* closing invariants *)
    iApply fupd_cwp.
    iMod ("HcloseWG" with "[$Hown $Hwg]") as "Hown".
    iModIntro.

    change (to_consts ([?x]++[?y])) with
      ([instruction.W.BI_const x; instruction.W.BI_const y]).
    change ([?x;?y]++[?z]) with ([x;y;z]).

    iApply (cwp_binop with "[$Hfr] [$Hrun]"); auto.

    (* and now. to prove the result is normal? smthn like that *)
    iModIntro; iFrame.
    iSplitR; auto.
    unfold τ.

    (* hm. I'm a bit suspicious. Might be okay? *)
    iExists [I32A _].
    iSplitR; last first.
    - iEval (cbn).
      iFrame; auto.
    - iEval (cbn).
      iExists [[_]].
      iSplit; auto.
      iEval (cbn).
      iSplit; auto.
      iApply value_interp_eq.
      iEval (cbn).
      iExists (SVALTYPE [I32R] NoRefs).
      iSplitR; auto.
      iSplitR.
      + iSplitR.
        * iPureIntro.
          econstructor.
          split; auto.
          apply Forall2_cons; split; [|by apply Forall2_nil].
          econstructor; auto.
        * iPureIntro.
          econstructor; auto. split; auto.
          apply Forall_singleton. econstructor.
      + clear temp.
        (* In this section, we need to prove ϕ interp *)
        (* all info about ϕ is in table_entry_interp *)
        iPoseProof ((big_sepL_lookup _ _ _ _ Htable) with "HTableEntryInterp")
          as "Hϕ".
        iEval (unfold table_entry_interp) in "Hϕ".
        (* TODO I think table_entry_interp needs a clause about off+i less than 2^32 *)
        iDestruct "Hϕ" as "(%i' & %cl & #Hclosure & #Hwt & #Hwf)".

        (* now let's go *)
        iExists _.
        iExists (Wasm_int.Int32.iadd (Wasm_int.Int32.repr i) (Wasm_int.Int32.repr off)).
        iExists i' , cl.
        iSplitR; [auto|iSplitR;[auto|]].

        (* I'm scared. One goal autos *)
        iSplitR; [|iSplitR]; auto.
        * iApply (empty_closure_interp with "[$Hclosure]").
        *
          assert (Hopefully: N.of_nat (off+i) =
                               Wasm_int.N_of_uint i32m
                                   (Wasm_int.Int32.iadd (Wasm_int.Int32.repr i)
                                      (Wasm_int.Int32.repr off))
                 ). {
            cbn.
            rewrite Nat.add_comm.
            (* uhm we need off + i to be guaranteed less than 32 modulus somewhere *)
            (* this is NOT true currectly TODO *)
            admit.
          }
          rewrite <- Hopefully. auto.

  Admitted.

End coderef.
