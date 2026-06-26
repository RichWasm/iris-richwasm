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


  Lemma cwp_drop1_nonptr fe ι wt wl ret wt' wl' es_drop1:
    ι <> PtrR ->
    run_codegen (drop1 mr fe ι) wt wl = inr (ret, wt', wl', es_drop1) ->
    ret = () /\ wt' = [] /\ wl' = [] /\
      ∀ s E f L R Φ v,
        ↪[frame] f -∗
        ↪[RUN] -∗
        Φ f [] -∗
        CWP BI_const v :: es_drop1 @ s; E UNDER L; R {{ Φ }}.
  Proof.
    intros Hι Hcg.
    assert (ret = () /\ wt' = [] /\ wl' = [] /\ es_drop1 = [BI_drop]) as (-> & -> & -> & ->). {
      destruct ι; try contradiction; cbn in Hcg; inversion Hcg; subst; done.
    }
    do 3 (split; first done).
    intros *.
    iIntros "Hfr Hrun HΦ".
    iApply (cwp_drop with "[$] [$] [-]").
    iModIntro. done.
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
      "#Hunreg" ∷ instance_rt_func_interp (mr_func_unregisterroot mr) (sr_func_unregisterroot sr) (runtime.spec_unregisterroot rti sr) (f_inst f) -∗
      "#Hfree"  ∷ instance_rt_func_interp (mr_func_free mr) (sr_func_free sr) (runtime.spec_free rti sr) (f_inst f) -∗
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
        iClear "Hunreg Hfree".
        iApply (cwp_local_get with "[] [$] [$]"); try done.
        iModIntro.
        now instantiate (1:= λ f'' v'', ⌜f'' = f' /\ v'' = [VAL_int32 n32]⌝%I).
      }
      iIntros (f'' v'') "(-> & ->) Hf Hrun".

      (* step 2: use the spec *)
      iApply (Hmm with "[$] [$] [$] [//] [$] [$] [$] [-]"); try done.
      { apply has_values_to_consts. }
      iIntros "Hrt Hown _".
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
        iClear "Hfree Hunreg".
        iApply (cwp_local_get with "[] [$] [$]"); try done.
        iModIntro.
        now instantiate (1:= λ f'' v'', ⌜f'' = f' /\ v'' = [VAL_int32 n32]⌝%I).
      }
      iIntros (f'' v'') "(-> & ->) Hf Hrun".

      (* step 2: use the spec *)
      iApply (Hgc with "[$] [Hfree HΦ] [$] [$] [//] [$] [$] [$]"); try done.
      { apply Is_true_true. apply has_values_to_consts. }
      iIntros "Hrt Hown _".
      iApply ("HΦ" with "[$] [$]").
  Qed.

  Fixpoint only_ptr_atoms (os:list atom) :=
    (* @filter atom atom (λ o, match o with | PtrA _ => True | _ => False end) os. *)
    match os with
    | (PtrA p)::os => (PtrA p)::(only_ptr_atoms os)
    | _::os => only_ptr_atoms os
    | [] => []
    end.
  Fixpoint only_ptr_rep (ιs:list atomic_rep) :=
    match ιs with
    | PtrR::ιs => PtrR::(only_ptr_rep ιs)
    | _::ιs => only_ptr_rep ιs
    | [] => []
    end.

  Lemma only_ptr_rep_rcons ιs ι:
    only_ptr_rep (seq.rcons ιs ι) =
      only_ptr_rep ιs ++ (λ r, match r with | PtrR => [PtrR] | _ => [] end) ι.
  Proof.
    induction ιs as [| ι' ιs].
    - cbn. done.
    - cbn.
      rewrite !IHιs.
      cbn.
      destruct ι'; cbn; done.
  Qed.


  Lemma cwp_drop_state ιs :
    ∀ fe wt wl wt' wl' es_drops,
    run_codegen (mapM_ (drop1 mr fe) (rev ιs)) wt wl = inr ((), wt', wl', es_drops) ->
    wt' = [] /\ wl' = repeat (W.T_i32) (length (only_ptr_rep ιs)).
  Proof.
    induction ιs as [| ιs ι] using seq.last_ind; intros * Hcg.
    - cbn in Hcg. cbn.
      inversion Hcg; subst; done.
    - rewrite rcons_app in Hcg.
      rewrite rev_unit in Hcg.
      apply wp_mapM__cons in Hcg.
      destruct Hcg as (?r&?wt&?wl&?es&?wt&?wl&?es & Hι & Hιs & _ & hwt' & hwl' & hes_drops).

      destruct (atomic_rep_eq_dec ι PtrR).
      + subst ι.
        apply cwp_drop1_ptr in Hι.
        destruct Hι as (-> & -> & -> & _).
        apply IHιs in Hιs.
        destruct Hιs as (-> & ->).
        rewrite only_ptr_rep_rcons.
        change ([?x] ++ ?y) with (x::y) in hwl'.
        rewrite repeat_cons in hwl'.
        change ([W.T_i32]) with (repeat W.T_i32 1) in hwl'.
        rewrite <- repeat_app in hwl'.
        rewrite length_app; cbn.
        clear_nils.
        done.
      + apply cwp_drop1_nonptr in Hι; try done.
        destruct Hι as (-> & -> & -> & _).
        apply IHιs in Hιs.
        destruct Hιs as (-> & ->).
        rewrite only_ptr_rep_rcons.
        assert ((match ι with | PtrR => [PtrR] | _ => [] end) = []). { destruct ι; try done. }
        rewrite H.
        clear_nils.
        done.
  Qed.


  Lemma cwp_drop ιs :
    ∀ fe wt wl wt' wl' es_drops,
    run_codegen (mapM_ (drop1 mr fe) (rev ιs)) wt wl = inr ((), wt', wl', es_drops) ->
    wt' = [] /\ wl' = repeat (W.T_i32) (length (only_ptr_rep ιs)) /\
    ∀ s E f L R Φ θ vs os,
    let ixs := seq (fe_wlocal_offset fe + length wl) (length wl') in
    let os_ptr := only_ptr_atoms os in
    ⊢ "Hf"      ∷ ↪[frame] f -∗
      "Hrun"    ∷ ↪[RUN] -∗
      "%Hfsz"   ∷ ⌜fe_wlocal_offset fe + length wl + length wl' ≤ length (f_locs f)⌝ -∗
      "%nsfree" ∷ ⌜↑ns_fun (N.of_nat (sr_func_free sr)) ⊆ E⌝ -∗
      "%nsunr"  ∷ ⌜↑ns_fun (N.of_nat (sr_func_unregisterroot sr)) ⊆ E⌝ -∗
      "Hrt"     ∷ rt_token rti sr lpall θ -∗
      "Hown"    ∷ na_own logrel_nais E -∗
      "#Hunreg" ∷ instance_rt_func_interp (mr_func_unregisterroot mr) (sr_func_unregisterroot sr) (runtime.spec_unregisterroot rti sr) (f_inst f) -∗
      "#Hfree"  ∷ instance_rt_func_interp (mr_func_free mr) (sr_func_free sr) (runtime.spec_free rti sr) (f_inst f) -∗
      "Hat"     ∷ atoms_interp os vs -∗
      "%Harep"  ∷ ⌜Forall2 has_arep ιs os⌝ -∗
      "HΦ"      ∷ (∀ f' vs_wl', ⌜frame_rel (λ i:nat, i ∉ ixs) f f'⌝ -∗
                    ⌜(Forall2 (λ i v, f_locs f' !! i = Some v) ixs vs_wl')⌝ -∗
                    ⌜result_type_interp wl' vs_wl'⌝ -∗
                    (∃ θ', rt_token rti sr lpall θ') -∗
                    na_own logrel_nais E -∗
                    Φ f' []) -∗
      CWP to_consts vs ++ es_drops @ s; E UNDER L; R {{ Φ }}.
  Proof.
    induction ιs as [| ιs ι] using seq.last_ind; intros * Hcg.
    - cbn in Hcg.
      inversion Hcg; subst; clear Hcg.
      do 2 (split; first done).
      intros *. intros os_ptr.
      repeat (iIntros "@").
      clear_nils.
      apply Forall2_length in Harep as lenos.
      destruct os; cbn in lenos; try inversion lenos; clear lenos.
      iPoseProof (big_sepL2_length with "[$Hat]") as "%lenvs".
      destruct vs; cbn in lenvs; try inversion lenvs; clear lenvs.
      cbn.
      iApply (cwp_nil with "[$] [$]").
      iSpecialize ("HΦ" $! f []).
      iApply ("HΦ" with "[//] [//] [%] [$] [$]").
      constructor.
    - (* first, state stuff real quick *)
      apply cwp_drop_state in Hcg as Hcg_state.
      destruct Hcg_state as (-> & ->).
      do 2 (split; first done).
      (* now actually do stuff *)
      rewrite rcons_app in Hcg.
      rewrite rev_unit in Hcg.
      apply wp_mapM__cons in Hcg.
      destruct Hcg as (rι&wtι&wlι&esι&wtιs&wlιs&esιs &
                         Hι & Hιs & _ & hwt' & hwl' & hes_drops).
      subst.
      destruct wtι; try inversion hwt'; destruct wtιs; try inversion hwt'.
      clear_nils; clear H hwt'.
      (* specialize IHιs *)
      specialize (IHιs fe wt (wl ++ wlι) [] wlιs esιs Hιs).
      destruct IHιs as (_ & hwlιs & IHιs). (* keeping wlιs folded for now *)

      (* start iris proof! goal is to separate to_consts vs into
        to_consts vsιs ++ to_consts [vι] *)
      intros * os_ptr.
      repeat (iIntros "@").
      (* splitting time. first Harep to split os, then Hat to split vs *)
      rewrite rcons_app in Harep.
      apply Forall2_app_inv_l in Harep.
      destruct Harep as (osιs & osι & Hosιs & Hoι & ->).
      apply Forall2_length in Hoι as osιlen.
      destruct osι as [|o [|a b]]; try inversion osιlen; clear osιlen.
      iPoseProof (atoms_interp_app_l with "[$Hat]") as
        "(%vsιs & %vsι & -> & Hatιs & Hatι)".
      iPoseProof (big_sepL2_length with "[$Hatι]") as "%lenvs".
      destruct vsι as [|v [|a b]]; try inversion lenvs; clear lenvs.
      assert (to_consts (vsιs ++ [v]) = to_consts vsιs ++ to_consts [v]). {
        unfold to_consts. by rewrite map_app.
      }
      rewrite H; clear H.

      (* time to do some sequencing. I *think* the strat will be all consts
         and esι in seq, then inside that do drop1 *)
      (* or hm maybe actually I do destruct ι PtrR first... yeah okay let's do that now *)
      destruct (atomic_rep_eq_dec ι PtrR).
      + (* ι = PtrR *)
        subst ι.
        apply (cwp_drop1_ptr) in Hι.
        destruct Hι as (-> & _ & hwlι & Hι).
        (* step 1: drat out as much info from o and v as possible *)
        inversion Hoι; subst.
        clear Hoι; rename H2 into Hoι; clear H4.
        destruct o; try inversion Hoι.
        iEval (unfold atoms_interp) in "Hatι".
        Opaque atom_interp.
        iEval (cbn) in "Hatι".
        Transparent atom_interp.
        iDestruct "Hatι" as "(Hatι & _)".
        iAssert (⌜∃ n32, v = VAL_int32 n32⌝%I) with "[Hatι]" as "%hv". {
          iDestruct "Hatι" as "(%n & %n32 & _ & %this & _)".
          iPureIntro; exists n32; exact this.
        }
        destruct hv as (n32 & ->).

        (* step 2: actually cwp_seq *)
        set (f':= ({|
                      W.f_locs := <[fe_wlocal_offset fe + length wl:=VAL_int32 n32]> (f_locs f);
                      W.f_inst := f_inst f
                    |})).
        rewrite app_assoc.
        iApply (cwp_seq with "[Hf Hrun Hrt Hown Hatι]"). {
          rewrite <- app_assoc.
          iApply cwp_val_app; first apply has_values_to_consts.
          unfold fvs_combine.
          iApply (Hι with "[$] [$] [%] [//] [//] [$] [$] [//] [//] [$] [-]"). {
            rewrite rcons_app in Hfsz.
            rewrite hwl' in Hfsz.
            rewrite length_app in Hfsz; cbn in Hfsz.
            lia.
          }
          iIntros "Hrt Hown".
          clear_nils.
          let Q := open_constr:(_ : iProp Σ) in
          instantiate (1 :=
            (λ f'' vs'',
              ⌜f'' = f'⌝ ∗ ⌜vs'' = vsιs⌝ ∗ Q)%I
            ).
          cbn.
          iSplitR; first done. iSplitR; first done.
          iAccu.
        }

        (* step 3: IH *)
        iIntros (f0 vs0) "(-> & -> & Hrt & Hown) Hf Hrun".
        clear θ; iDestruct "Hrt" as "(%θ & Hrt)".
        clear Hι. move IHιs at bottom.
        iApply (IHιs with "[$] [$] [%] [//] [//] [$] [$] [//] [//] [$] [//] [-]"). {
          rewrite !length_repeat. rewrite length_repeat in Hfsz.
          rewrite only_ptr_rep_rcons in Hfsz.
          rewrite length_app in Hfsz.
          unfold f'; cbn.
          rewrite length_insert.
          cbn in Hfsz.
          rewrite length_app; cbn.
          lia.
        }
        clear IHιs θ.
        iIntros (f'' vs_wl) "%Hfr_f'_f'' %Hf''locs %Hresinterp Hrt Hown".
        iSpecialize ("HΦ" $! f'' ((VAL_int32 n32)::vs_wl)).
        iApply ("HΦ" with "[%] [%] [%] [$] [$]").
        (* all we have to do now is a BUNCH of frame manipulation *)
        * (* combine frame rels *)
          assert (frame_rel (λ i, i ∉ ixs) f f'). {
            apply (frame_rel_mask_mono (λ i, i ≠ fe_wlocal_offset fe + length wl)).
            - intros i Hiixs.
              subst ixs.
              intros contra.
              apply Hiixs.
              apply elem_of_seq.
              subst i.
              rewrite length_repeat.
              rewrite only_ptr_rep_rcons.
              rewrite length_app; cbn.
              lia.
            - unfold f'.
              split; last done.
              unfold mask_locs_eq. cbn.
              intros i Hiixs.
              rewrite list_lookup_insert_ne; try done.
          }
          assert (frame_rel (λ i, i ∉ ixs) f' f''). {
            eapply frame_rel_mask_mono; last exact Hfr_f'_f''.
            cbn.
            intros i Hiixs.
            unfold ixs in Hiixs.
            rewrite only_ptr_rep_rcons in Hiixs.
            rewrite length_repeat; rewrite length_repeat in Hiixs.
            rewrite length_app; rewrite length_app in Hiixs; cbn; cbn in Hiixs.
            rewrite elem_of_seq. rewrite elem_of_seq in Hiixs.
            lia.
          }
          eapply frame_rel_trans; first exact H; done.
        * (* frame locs *)
          assert (ixs = (fe_wlocal_offset fe + length wl)::
                          (seq (fe_wlocal_offset fe + length (wl ++ [W.T_i32]))
                             (length (repeat W.T_i32 (length (only_ptr_rep ιs)))))). {
            unfold ixs.
            rewrite !length_repeat.
            rewrite only_ptr_rep_rcons.
            rewrite !length_app; cbn.
            symmetry.
            cbn.
            rewrite Nat.add_assoc.
            rewrite !Nat.add_1_r.
            apply cons_seq.
          }
          rewrite H.
          constructor; last done.
          set (i := fe_wlocal_offset fe + length wl) in *.
          assert (f_locs f'' !! i = f_locs f' !! i). {
            destruct Hfr_f'_f'' as (this & _).
            unfold mask_locs_eq in this.
            symmetry.
            apply this.
            rewrite elem_of_seq.
            unfold i. rewrite !length_app. cbn. lia.
          }
          rewrite H0.
          unfold f'.
          apply list_lookup_insert_eq.
          rewrite rcons_app in Hfsz; rewrite hwl' in Hfsz; cbn in Hfsz.
          lia.
        * (* result type interp *)
          rewrite only_ptr_rep_rcons.
          rewrite length_app.
          rewrite repeat_app. cbn.
          rewrite <- repeat_cons.
          constructor; last done.
          cbn.
          exists n32; done.

      + (* ι <> PtrR *)
        assert (HR: only_ptr_rep (seq.rcons ιs ι) = only_ptr_rep ιs). {
          rewrite only_ptr_rep_rcons.
          destruct ι; cbn; clear_nils; try done.
        }
        rewrite <- rcons_app in hwl'.
        rewrite HR in hwl'.
        rewrite HR in Hfsz.
        rewrite HR.

        apply cwp_drop1_nonptr in Hι; try done.
        destruct Hι as (-> & _ & -> & Hι).
        clear_nils.
      
        rewrite app_assoc.
        rewrite app_assoc.
        iApply (cwp_seq with "[Hf Hrun]"). {
          rewrite <- app_assoc.
          iApply cwp_val_app; first apply has_values_to_consts.
          unfold fvs_combine.
          iApply (Hι with "[$] [$]").
          clear_nils.
          instantiate (1 :=
            (λ f'' vs'',
              ⌜f'' = f⌝ ∗ ⌜vs'' = vsιs⌝)%I
            ).
          cbn.
          done.
        }
        iIntros (f'' vs_wl) "(-> & ->) Hfr Hrun".
        move IHιs at bottom.
        subst ixs. rewrite !HR.
        rewrite hwl' in Hfsz.
        specialize IHιs with (os:=osιs) (vs:=vsιs).
        iApply (IHιs with "[$] [$] [//] [//] [//] [$] [$] [//] [//] [$] [//] [-]").
        iIntros (f'' vs_wl) "%Hfr_f'_f'' %Hf''locs %Hresinterp Hrt Hown".
        iSpecialize ("HΦ" $! f'' vs_wl).
        iApply ("HΦ" with "[%] [%] [%] [$] [$]"); try (rewrite hwl'; done).
  Qed.


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

    apply (cwp_drop) in Hdrop.
    destruct Hdrop as (-> & Hwl2' & Hdrop_spec).
    apply has_values_to_consts_inv in Hevs; subst evs.

    iAssert (⌜fe_wlocal_offset fe + length wl + length wl2' <= length (f_locs fr)⌝%I)
      with "[Hframe]" as "%Hlocslen". {
      iPoseProof (frame_interp_locs_len with "[$Hframe]") as "%Hlenmini".
      iPureIntro.
      rewrite fe_wlocal_offset_length.
      rewrite !length_app in Hlenmini.
      rewrite Hlenmini.
      lia.
    }

    iApply (Hdrop_spec with "[$] [$] [//] [%] [%] [$] [$] [] [] [$] [//]").
    { solve_ndisj. }
    { solve_ndisj. }
    { by iDestruct "Hinst" as "(_ & (_ & _ & _ & this & _ & that) & _)". }
    { by iDestruct "Hinst" as "(_ & (_ & _ & _ & this & _ & that) & _)". }
    iIntros (fr' vs_wl) " %Hframerel  %Hnewidxs %Hresinterp Hrt Hown".
    iPoseProof (frame_interp_update_frame with "[$Hframe]") as "Hframe".
    4: exact Hframerel.
    all: try done.
    { rewrite fe_wlocal_offset_length. done. }
    iFrame.
    iSplitR.
    - (* frame stuff, only one level should be fine *)
      iPureIntro.
      eapply frame_rel_mask_mono; last exact Hframerel.
      intros i Hlm; cbn; unfold lmask in Hlm; unfold wlmask in Hlm.
      rewrite elem_of_seq.
      rewrite !fe_wlocal_offset_length in Hlm.
      rewrite !sum_list_with_length_concat.
      lia.
    - iExists [].
      cbn.
      iSplitR; try done.
      iExists [].
      cbn; done.
  Qed.




End drop.
