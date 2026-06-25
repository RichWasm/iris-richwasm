Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.case_ptr.
Require Import RichWasm.iris.logrel.roots.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section drop.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_drop M F L wt wt' wtf wl wl' wlf τ es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl  in
    let ψ := InstrT [τ] [] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IDrop ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros * Hty Hcg.
    unfold WT, WL; clear WT WL.
    iIntros (se fr os vs evs θ B R).
    repeat iIntros "@".
    inv_cg_bind Hcg ρ wt1 wt1' wl1 wl1' es_nil es1 Htype_rep Hcg.
    inv_cg_bind Hcg ιs wt2 wt2' wl2 wl2' es_nil' es_drops Heval_rep Hdrop.
    inv_cg_try_option Heval_rep; rename Heq_some into Hρ.
    inv_cg_try_option Htype_rep; rename Heq_some into Htype_rep.
    subst; clear_nils.

    (* Kinding quarantine goes here! *)
    rewrite values_interp_one_eq.
    iAssert (⌜Forall2 has_arep ιs os /\ has_areps ιs (SAtoms os)
             /\ (∃ ξ,
                   type_skind se τ = Some (SVALTYPE ιs ξ) /\
                   has_kind F τ (VALTYPE ρ ξ)
               )⌝%I)
      with "[Hvs Hos]" as "%KindingQuarantine". {
      rewrite value_interp_eq.
      iEval (cbn -[pre_type_interp type_skind]) in "Hos".
      iDestruct "Hos" as "(%sκ_temp & %Htypeskindtemp & %Harepsoon & pre)".
      iPureIntro.

      assert (∃ ξ_τ, has_kind F τ (VALTYPE ρ ξ_τ)). {
        inversion Hty; clear Hty; subst.
        inversion H; clear H; subst.
        clear H2.
        inversion H1; clear H1; subst; clear H4.
        destruct H3 as (?ρ & ?Hrep & ?Hmono).
        cbn in Htype_rep.
        inversion Hrep; subst; clear Hrep.
        exists ξ.
        apply type_rep_has_kind_agree in H as H'.
        rewrite H' in Htype_rep; inversion Htype_rep; subst.
        done.
      }
      destruct H as (ξ & Hkindτ).


      destruct sκ_temp; try (inversion Harepsoon; done).
      assert (ιs = l /\ ξ = r) as (<- & <-). {
        pose proof (type_skind_eval_rep_emptyenv se F ρ _ _ τ _ _
                      Hkindτ Hse Hρ Htypeskindtemp).
        done.
      }
      (* note we can get ref_flag_interp if we need it here *)
      destruct Harepsoon as (Hareps & Hforallatomref).

      repeat split.
      - unfold has_areps in Hareps.
        destruct Hareps as (os' & toinvert & yes).
        inversion toinvert; subst; done.
      - done.
      - exists ξ; done.
    }
    destruct KindingQuarantine as (Harep & Hareps & (ξ & Htypeskindτ & Hkindτ)).


    (* TODO: mapM_ drop1 *)
  Admitted.

  Lemma cwp_drop1_nonptr fe ι wt wl ret wt' wl' es_drop1:
    ι <> PtrR ->
    run_codegen (drop1 mr fe ι) wt wl = inr (ret, wt', wl', es_drop1) ->
    ret = () /\ wt' = [] /\ wl' = [] /\
      ∀ s E f v L R Φ,
        ↪[frame] f -∗
        ↪[RUN] -∗
        ▷ Φ f [] -∗
        CWP BI_const v :: es_drop1 @ s; E UNDER L; R {{ Φ }}.
  Proof.
    intros Hι Hcg.
    assert (ret = () /\ wt' = [] /\ wl' = [] /\ es_drop1 = [BI_drop]) as (-> & -> & -> & ->). {
      destruct ι; try contradiction; cbn in Hcg; inversion Hcg; subst; done.
    }
    do 3 (split; first done).
    intros *.
    iIntros "Hfr Hrun HΦ".
    iApply (cwp_drop with "[$] [$] [$]").
  Qed.

  (* note: i'm not having HΦ give back unreg and free because they're goddam
     persistent. idk why we've been doing this the whole time *)
  Lemma cwp_drop1_ptr fe wt wl ret wt' wl' es_drop1:
    run_codegen (drop1 mr fe PtrR) wt wl = inr (ret, wt', wl', es_drop1) ->
    ret = () /\ wt' = [] /\ wl' = [W.T_i32] /\
    ∀ s E f L R Φ n32 ptr θ,
    let ix := fe_wlocal_offset fe + length wl in
    let f' := ({| W.f_locs := <[ix:=VAL_int32 n32]> (f_locs f); W.f_inst := f_inst f |}) in
    ⊢ "Hf"      ∷ ↪[frame] f -∗
      "Hrun"    ∷ ↪[RUN] -∗
      "%Hfsz"   ∷ ⌜fe_wlocal_offset fe + length wl < length (f_locs f)⌝ -∗
      "%nsfree" ∷ ⌜↑ns_fun (N.of_nat (sr_func_free sr)) ⊆ E⌝ -∗
      "%nsunr"  ∷ ⌜↑ns_fun (N.of_nat (sr_func_unregisterroot sr)) ⊆ E⌝ -∗
      "Hrt"     ∷ rt_token rti sr lpall θ -∗
      "Hown"    ∷ na_own logrel_nais E -∗
      "Hunreg"  ∷ instance_rt_func_interp (mr_func_unregisterroot mr) (sr_func_unregisterroot sr) (runtime.spec_unregisterroot rti sr) (f_inst f) -∗
      "Hfree"   ∷ instance_rt_func_interp (mr_func_free mr) (sr_func_free sr) (runtime.spec_free rti sr) (f_inst f) -∗
      "Hat"     ∷ atom_interp (PtrA ptr) (VAL_int32 n32) -∗
      "HΦ"      ∷ ((∃ θ', rt_token rti sr lpall θ') -∗
                    na_own logrel_nais E -∗
                    Φ f' []) -∗
      CWP BI_const (VAL_int32 n32) :: es_drop1 @ s; E UNDER L; R {{ Φ }}.
  Proof.
    intros Hcg.
    unfold drop1 in Hcg.
    inv_cg_bind Hcg idx ?wt ?wt ?wl ?wl es_save1 ?rest Hsave1 Hcg.
    cbn in Hsave1; inversion Hsave1; subst.
    set (ix := fe_wlocal_offset fe + length wl) in *.
    set (idx := prelude.W.Mk_localidx ix) in *.
    clear Hsave1.
    inv_cg_bind Hcg r ?wt ?wt ?wl ?wl es_caseptr es_ignore Hcaseptr Hignore.
    cbn in Hignore; inversion Hignore; subst; clear Hignore.
    destruct r. destruct u. destruct p. destruct u; destruct u0.

    assert (wt0 = [] /\ wl0 = []) as (-> & ->). {
      cbn in Hcaseptr.
      inversion Hcaseptr; subst; done.
      (* note that if build time ever becomes annoying I can push this off till later *)
    }
    clear_nils.
    do 3 (split; first done).

    (** ------------- SET LOCAL -------------- *)
    intros *. repeat (iIntros "@").
    change (?x::[?y] ++ ?z) with ([x;y] ++ z).
    iApply (cwp_seq with "[Hf Hrun]"). {
      iApply (cwp_local_set with "[] [$] [$]"); first done.
      now instantiate (1:= λ f'' v'',
            ⌜f'' = f'
            /\ v'' = []⌝%I).
    }
    iIntros (f'' v') "(-> & ->) Hf Hrun".
    clear_nils.
    assert (Hfidx: f_locs f' !! localimm idx = Some (VAL_int32 n32)). {
      unfold f'; cbn.
      rewrite list_lookup_insert_eq; done.
    }


    (** ------------- DROPPING --------------- *)

    eapply cwp_case_ptr in Hcaseptr.
    destruct Hcaseptr as (?&?&?&?&?&?&?&?&?& Hempty & Hmm & Hgc & hwt & hwl & Hspec).
    cbn in Hempty; inversion Hempty; subst; clear Hempty.
    inv_cg_bind Hmm () ?wt ?wt ?wl ?wl esgetlocmm esmm Hgetlocmm Hmm.
    unfold memory.drop_ptr in Hmm.
    cbn in Hgetlocmm; inversion Hgetlocmm; subst; clear Hgetlocmm.
    inv_cg_bind Hgc () ?wt ?wt ?wl ?wl esgetlocgc esgc Hgetlocgc Hgc.
    unfold memory.drop_ptr in Hgc.
    cbn in Hgetlocgc; inversion Hgetlocgc; subst; clear Hgetlocgc.
    (* I could cbn, but I don't want to get rid of the codegens, so *)
    assert (wt1 = [] /\ wt2 = [] /\ wl1 = [] /\ wl2 = []) as (-> & -> & -> & ->). {
      cbn in Hmm, Hgc.
      inversion Hmm; inversion Hgc; subst; done.
    }

    (* a bit of atom_interp massaging *)
    iPoseProof (atom_interp_ptr_shaped with "[$Hat]") as "Hat".
    iDestruct "Hat" as "(%n & %n32' & %Nrepr & %toinvert & %ptrshaped & Hat)".
    iDestruct "Hat" as "(%rp & %reproot & Hat)".
    inversion toinvert; subst n32'; clear toinvert.

    (* time to use the spec! *)
    specialize (Hspec [] [] ptr n n32 ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto)).
    clear_nils; clear hwt hwl.
    iApply (Hspec with "[$] [$] [//]").
    iModIntro. iIntros "Hf Hrun". clear Hspec.

    (* here we finally go into cases :) *)
    destruct ptr; [|destruct μ].
    - (* Ptr Int *)
      iApply (cwp_nil with "[$] [$]").
      iApply ("HΦ" with "[$] [$]").
    - (** ------------- Ptr MemMM ---------------- *)
      apply (cwp_free mr sr rti) in Hmm.
      destruct Hmm as (_ & _ & _ & Hmm).
      destruct rp; try done.
      destruct μ; try done.
      iEval (cbn) in "Hat".
      specialize Hmm with (fr:=f') (ℓ:=ℓ) (a:=a) (ta:=n) (ta32:=n32).

      (* step 1: get local *)
      iApply (cwp_seq with "[Hf Hrun]"). {
        iApply (cwp_local_get with "[] [$] [$]"); try done.
        iModIntro.
        now instantiate (1:= λ f'' v'', ⌜f'' = f' /\ v'' = [VAL_int32 n32]⌝%I).
      }
      iIntros (f'' v'') "(-> & ->) Hf Hrun".

      (* step 2: use the spec *)
      iApply (Hmm with "[$] [$] [$] [//] [$] [$] [$] [-]"); try done.
      { apply has_values_to_consts. }
      iIntros "Hrt Hown Hfree".
      iApply ("HΦ" with "[$] [$]").
    - (** ------------- Ptr MemGC ---------------- *)
      apply (wp_unregisterroot rti sr) in Hgc.
      destruct Hgc as (_ & _ & _ & Hgc).
      destruct rp; try done.
      destruct μ; try done.
      iEval (cbn) in "Hat".
      specialize Hgc with (ar:=a) (tar:=n) (tar32:=n32).

      (* step 1: get local *)
      iApply (cwp_seq with "[Hf Hrun]"). {
        iApply (cwp_local_get with "[] [$] [$]"); try done.
        iModIntro.
        now instantiate (1:= λ f'' v'', ⌜f'' = f' /\ v'' = [VAL_int32 n32]⌝%I).
      }
      iIntros (f'' v'') "(-> & ->) Hf Hrun".

      (* step 2: use the spec *)
      iApply (Hgc with "[$] [Hfree HΦ] [$] [$] [//] [$] [$] [$]"); try done.
      { apply Is_true_true. apply has_values_to_consts. }
      iIntros "Hrt Hown Hunreg".
      iApply ("HΦ" with "[$] [$]").
  Qed.




End drop.
