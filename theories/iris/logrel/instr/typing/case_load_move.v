Require Import RichWasm.iris.logrel.instr.typing.common.
From RichWasm.iris.logrel Require Import case_ptr roots load_copy.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section case_load_move.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_case_load_move M F L L' wt wt' wtf wl wl' wlf ess es' τs τs' κr κv κs :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let F' := F <| fc_labels ::= cons (τs', L') |> in
    let τs_ser := zip_with SerT κs τs in
    let ψ := InstrT [RefT κr (BaseM MemMM) Imm (VariantT κv τs_ser)] τs' in
    length κs = length τs ->
    Forall2
      (fun τ es =>
         (forall wt wt' wtf wl wl' wlf es',
            let fe' := fe_of_context F' in
            let WT := wt ++ wt' ++ wtf in
            let WL := wl ++ wl' ++ wlf in
            let lmask := wlmask fe' wl in
            run_codegen (compile_instrs mr fe' es) wt wl = inr ((), wt', wl', es') ->
           ⊢ have_instr_type_sem rti sr mr M F' L WT WL lmask es' (InstrT [τ] τs') L'))
      τs ess ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ICaseLoad ψ Move L' ess)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L'.
  Proof.
    iIntros (??????? Hlen_κs_τs IH Hok Hcg ????????) "@@@@@@@@@@@@".
    destruct κv.
    { admit. } (* contradiction *)
    destruct τs'.
    { admit. } (* contradiction *)
    destruct τs'; first last.
    { admit. } (* contradiction *)

    cbn in Hcg.
    inv_cg_bind Hcg n ?wt ?wt ?wl ?wl ?es ?es Hn Hcg.
    inv_cg_bind Hcg ts ?wt ?wt ?wl ?wl ?es ?es Hts Hcg.
    destruct (Wasm_int.Int32.modulus <? length τs_ser)%Z eqn:Hlength; first done.
    rewrite Z.ltb_ge in Hlength.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hret Hcg.
    inv_cg_ret Hret.
    inv_cg_bind Hcg x ?wt ?wt ?wl ?wl ?es ?es Hx Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hsetx Hcg.
    inv_cg_bind Hcg [[] [[] []]] ?wt ?wt ?wl ?wl ?es ?es Hcg Hret.
    inv_cg_try_option Hn.
    inv_cg_try_option Hts.
    apply wp_wlalloc in Hx as (-> & -> & -> & ->).
    inv_cg_emit Hsetx.
    inv_cg_ret Hret.
    subst wt0 wl0 es wt2 wl2 es1 wt9 wl9 es8 wt7 wl7 es6 wt5 wl5 es4 es2 es0 es' wt3 wl3 wt1 wl1 wt' wl' wt4 wl4 es3 wt8 wl8 es7 wt11 wl11 es10.
    clear Hretval Hretval0 Hretval1.
    clear_nils.

    rewrite values_interp_one_eq.
    iDestruct (value_interp_ref_sz with "Hos") as "%Hos".
    destruct (list_singleton_reflect os); last contradiction.
    rename x into o.
    subst os.
    clear Hos.
    rewrite atoms_interp_one_inv.
    iDestruct "Hvs" as "(% & % & Hvs)".
    subst vs.
    rewrite has_values_iff_to_consts in Hevs.
    cbn in Hevs.
    subst evs.

    set x := fe_wlocal_offset fe + length wl.

    rewrite app_assoc.
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      iApply (cwp_local_set with "[] [$Hfr] [$Hrun]").
      - admit.
      - by instantiate (1 := fun fr' vs => (⌜fr' = Build_frame (<[ x := v ]> fr.(f_locs)) fr.(f_inst)⌝ ∗
                                           ⌜vs = []⌝)%I).
    }

    iIntros (??) "[-> ->] Hfr Hrun".
    rewrite value_interp_eq.
    iDestruct "Hos" as "(% & % & % & % & % & % & % & Hℓ & Href)".
    inversion H1.
    subst o.
    clear H1.
    iDestruct "Hvs" as "(% & % & % & -> & % & % & Hrp)".
    inversion H2.
    { iDestruct "Hrp" as "[]". }
    subst rp n0.
    destruct μ; first last.
    { iDestruct "Hrp" as "[]". }
    unfold root_pointer_interp.

    apply cwp_case_ptr in Hcg as (? & ? & ? & ? & ? & ? & ? & ? & ? &
                                    Hcg_unr & Hcg_mm & Hcg_gc & -> & -> & Hcwp).
    iApply (Hcwp with "[$Hfr] [$Hrun]").
    { by instantiate (1 := []). }
    { done. }
    {
      instantiate (2 := PtrHeap MemMM ℓ).
      instantiate (1 := tag_address MemMM a).
      by constructor.
    }
    { done. }
    { iPureIntro. admit. }
    iIntros "!> Hfr Hrun".
    clear Hcwp Hcg_gc.

    rewrite type_interp_eq.
    iDestruct "Href" as "(% & % & % & % & % & % & % & % & % & Hτ)".
    inversion H8.
    subst ws.
    clear H8.
    destruct (list_lookup i (map (type_interp rti sr) τs_ser)) as [T|] eqn:HT; first last.
    { by rewrite HT. }
    rewrite HT.
    apply map_lookup_helper_backwards in HT as (τ & Hτ & ->).
    assert (i < length τs_ser) as Hi_lt.
    { apply lookup_lt_is_Some. by eexists. }

    inv_cg_emit Hcg_unr.
    inv_cg_bind Hcg_mm [] ?wt ?wt ?wl ?wl ?es ?es Hcg_root Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_tag Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_case Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_flags Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_ptr Hcg_free.
    inv_cg_emit Hcg_ptr.
    subst x0 x3 x6 wt8 wl8 es7 wt7 wl7 es6 wt5 wl5 es4 wt3 wl3 es2 wt1 wl1 es0 x1 x4 x7.
    clear Hretval Hretval0.
    clear_nils.

    apply wp_root_to_heap_mm in Hcg_root as (_ & -> & -> & ->).
    rewrite app_nil_l.
    iApply (cwp_seq with "[-Hτ Hframe]").
    {
      iApply fupd_cwp.
      iMod (na_inv_acc with "Hℓ Hown") as "(>[Hlayout Hheap] & Hown & Hclose)".
      { done. }
      { done. }
      iModIntro.
      iApply (wp_load1_copy_mm with "[$Hfr] [$Hrun] [$Hheap] [$Hrp] [$Hown] [$Hrt]").
      - done.
      - by iDestruct "Hinst" as "(_ & (_ & _ & _ & _ & H & _) & _)".
      - done.
      - solve_ndisj.
      - iPureIntro. cbn. lia.
      - by instantiate (1 := I32A (Wasm_int.int_of_Z i32m (Z.of_nat i))).
      - iPureIntro. cbn. rewrite take_0. do 2 f_equal. rewrite <- H7.
        rewrite Wasm_int.Int32.Z_mod_modulus_id.
        { rewrite <- Z_nat_N. by rewrite Nat2Z.id. }
        split; first lia. rewrite Nat2Z.inj_lt in Hi_lt.
        eapply Z.lt_le_trans; [apply Hi_lt|apply Hlength].
      - done.
      - admit.
      - iPureIntro. apply list_lookup_insert_eq. cbn. admit.
      - done.
      - done.
      - done.
      - done.
      - by iDestruct "Hinst" as "(_ & _ & _ & _ & H & _)".
      - by iDestruct "Hinst" as "(_ & _ & _ & _ & _ & H)".
      - iIntros (???) "@@@@@@@@".
        iClear "Hregf".
        iSpecialize ("Ho" with "[//]").
        iSpecialize ("Hclose" with "[Hlayout Hptr Hown]"); first iFrame.
        iDestruct "Ho" as "->".
        instantiate (1 := fun f vs => (⌜vs = [VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat i))]⌝ ∗
                                      ℓ ↦addr (MemMM, a) ∗
                                      rt_token rti sr lpall θ ∗
                                      |={⊤}=> na_own logrel_nais ⊤)%I).
        by iFrame.
    }

    apply Forall2_length in IH as Hlen_τs_ess.
    assert (length τs = length τs_ser) as Hlen_τs_ser.
    { by rewrite length_zip_with Hlen_κs_τs Nat.min_id. }

    iIntros (??) "(-> & Haddr & Hrt & Hown) Hf Hrun".
    clear Hcg_tag.
    iApply fupd_cwp.
    iMod "Hown".
    iModIntro.
    rewrite app_assoc.
    iApply (cwp_seq with "[-]").
    {
      eapply cwp_case_switch in Hcg_case as (wt_c & wt_c' & wl_c & wl_c' & es_c & Hcg_case & Hes3);
        first last.
      { apply map_lookup_helper_forwards. admit. }
      { by rewrite length_map -compile_cases_length -Hlen_τs_ess Hlen_τs_ser. }
      iApply (Hes3 with "[$Hf] [$Hrun]").
      { admit. }
      { done. }
      { apply Is_true_true. apply has_values_to_consts. }
      { admit. }
      iIntros "Hfr Hrun".
      admit.
    }

    iIntros (??) "HΦ Hf Hrun".
    iApply cwp_val_app; first apply has_values_to_consts.
    iApply (cwp_seq with "[-]").
    {
      (* set_pointer_flags *)
      instantiate (1 := fun f vs => ⌜vs = []⌝%I).
      admit.
    }

    iIntros (??) "-> Hf Hrun".
    rewrite app_nil_l.
    iApply (cwp_seq with "[-]").
    {
      iApply (cwp_local_get with "[] [$Hf] [$Hrun]"); admit.
    }

    iIntros (??) "HΦ Hf Hrun".
    (* free *)
  Admitted.

End case_load_move.
