Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.store_common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section inject_new.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_inject_new M F L wt wt' wtf wl wl' wlf es' μ i τ τs κr κv κs :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let τs' := zip_with SerT κs τs in
    let ψ := InstrT [τ] [RefT κr μ Imm (VariantT κv τs')] in
    τs !! i = Some τ ->
    mono_mem μ ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IInjectNew ψ i)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    iIntros (?????? Hτ [bm ->] [[Hτ_mono Href_mono] HL_ok] Hcg ????????) "@@@@@@@@@@@@".
    rewrite Forall_singleton in Hτ_mono.
    destruct Hτ_mono as (ρ & Hτρ & Hρ_mono).
    inversion Hτρ.
    rename H into Hτ_kind.
    subst F0 τ0 ρ0.
    destruct κv as [|σ ξ']; first inversion Hcg.

    inv_cg_bind Hcg ρ' ?wt ?wt ?wl ?wl ?es ?es Hcg_rep Hcg.
    inv_cg_try_option Hcg_rep.
    rename Heq_some into Hρ'.
    inv_cg_bind Hcg ιs ?wt ?wt ?wl ?wl ?es ?es Hcg_arep Hcg.
    inv_cg_try_option Hcg_arep.
    rename Heq_some into Hιs.
    inv_cg_bind Hcg n ?wt ?wt ?wl ?wl ?es ?es Hcg_n Hcg.
    inv_cg_try_option Hcg_n.
    rename Heq_some into Hn.
    inv_cg_bind Hcg xs ?wt ?wt ?wl ?wl ?es ?es Hcg_save Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_alloc Hcg.
    inv_cg_bind Hcg laddr ?wt ?wt ?wl ?wl ?es ?es Hcg_laddr Hcg.
    apply wp_wlalloc in Hcg_laddr as (Hladdr & -> & -> & ->).
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_set_laddr Hcg.
    inv_cg_emit Hcg_set_laddr.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_flags Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_tag Hcg.
    inv_cg_emit Hcg_tag.
    inv_cg_bind Hcg ltag ?wt ?wt ?wl ?wl ?es ?es Hcg_ltag Hcg.
    apply wp_wlalloc in Hcg_ltag as (Hltag & -> & -> & ->).
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_set_ltag Hcg.
    inv_cg_emit Hcg_set_ltag.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_store_tag Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_store Hcg.
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl ?es ?es Hcg_get_laddr Hcg_regroot.
    inv_cg_emit Hcg_get_laddr.
    subst wt0 wl0 es wt2 wl2 es1 wt4 wl4 es3 wt9 wl9 wt10 wl10 es9 wt15 wl15 es14 wt16 wl16 wt17
      wl17 es16 wt24 wl24 es23 wt23 wl23 es22 wt21 wl21 es20 wt19 wl19 es18 wt18 wl18 es17 es15 wt14
      wl14 es13 wt12 wl12 es11 wt11 wl11 es8 es10 wt7 wl7 es6 wt5 wl5 es4 wt3 wl3 es2 wt1 wl1 es0
      wt' wl' es'.
    clear_nils.
    clear Hretval Hretval0 Hretval1 Hretval2.

    apply type_rep_has_kind_agree in Hτ_kind as H.
    rewrite Hρ' in H.
    inversion H.
    subst ρ'.
    clear H.

    rewrite values_interp_one_eq value_interp_eq -type_interp_eq.
    iDestruct (type_interp_skind_svalue with "Hos") as "(%sκ & %Hsκ & %Hsv)".
    apply eval_rep_emptyenv with (se := se) in Hιs as Hιs_se.
    apply eval_kind_of_eval_rep with (ξ := ξ) in Hιs_se as Heval_kind.
    pose proof (type_skind_has_kind_agree _ _ _ _ _ _ Hτ_kind Hse Heval_kind Hsκ) as <-.
    iDestruct (type_interp_implies_has_areps with "Hos") as "%Hos"; first done.
    iDestruct (result_type_interp_of_atoms_interp with "Hvs") as "%Hvs"; first done.
    iDestruct (frame_interp_wl_interp with "Hframe") as "%HWL".

    rewrite app_assoc.
    eapply cwp_save_stack_w in Hcg_save as (-> & -> & -> & Hes5); first last.
    { by rewrite length_map length_map. }
    { by apply Is_true_true. }
    { by rewrite map_map. }
    { subst WL. by rewrite !app_nil_l -!app_assoc in HWL. }
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      iApply (Hes5 with "[$Hfr] [$Hrun]").
      iIntros (?) "[%Hfrel %Hlocs]".
      by instantiate
           (1 := fun f vs' =>
                   (⌜frame_rel (fun i => i ∉ seq (fe_wlocal_offset fe + length wl) (length ιs)) fr f⌝ ∗
                      ⌜Forall2 (fun i v => f_locs f !! localimm i = Some v)
                         (map Mk_localidx (seq (fe_wlocal_offset fe + length wl) (length ιs))) vs⌝ ∗
                   ⌜vs' = []⌝)%I).
    }

    iIntros (??) "(%Hfrel & %Hlocs & ->) Hfr Hrun".
    clear Hes5.
    destruct bm.
    - inv_cg_ret Hcg_regroot.
      subst wt25 wl25 es24.
      clear Hretval.
      rewrite app_nil_r.

      eapply cwp_alloc_mm in Hcg_alloc as (_ & -> & -> & Hes7).
      rewrite app_assoc.
      iApply (cwp_seq with "[-Hvs Hos Hframe]").
      {
        iApply (Hes7 with "[$Hfr] [$Hrun] [] [$Hown] [$Hrt]").
        - done.
        - destruct Hfrel as [_ <-]. by iDestruct "Hinst" as "(_ & [H _] & _)".
        - iIntros "[% Hrt] Hown _" (?????) "%Hta32 %Hta Haddr Hlayout Hheap".
          instantiate
            (1 := fun f' vs' =>
                    (∃ θ' ℓ a ta ta32 ws,
                        ⌜f' = f⌝ ∗
                          ⌜vs' = [VAL_int32 ta32]⌝ ∗
                          ⌜N_i32_repr ta ta32⌝ ∗
                          ⌜repr_root_pointer (RootHeap MemMM a) ta⌝ ∗
                          rt_token rti sr lpall θ' ∗
                          na_own logrel_nais ⊤ ∗
                          ℓ ↦addr (MemMM, a) ∗
                          ℓ ↦layout repeat FlagInt n ∗
                          ℓ ↦heap ws)%I).
          iExists _, _, _, _, _, _.
          by iFrame.
      }

      clear Hes7.
      iIntros (??)
        "(% & % & % & % & % & % & <- & -> & %Hta32 & %Hta & Hrt & Hown & Haddr & Hlayout & Hheap)
         Hf Hrun".
      rewrite app_assoc.
      iApply (cwp_seq with "[Hf Hrun]").
      {
        iApply (cwp_local_set with "[] [$Hf] [$Hrun]").
        - admit.
        - by instantiate
               (1 := fun f' vs' =>
                       (⌜f' = f0 <| f_locs ::= <[ localimm laddr := VAL_int32 ta32 ]> |>⌝ ∗
                          ⌜vs' = []⌝)%I).
      }

      iIntros (??) "[-> ->] Hf Hrun".
      eapply cwp_set_pointer_flags in Hcg_flags as (_ & -> & -> & Hes12).
      rewrite app_assoc.
      iApply (cwp_seq with "[Hrt Hown Hlayout Hf Hrun]").
      {
        iDestruct (rt_token_lpall _ _ (fun ℓ' => ℓ <> ℓ') with "Hrt") as "Hrt".
        iApply (Hes12 with "[$Hlayout] [$Hrt] [] [$Hown] [$Hf] [$Hrun]").
        - done.
        - by intros H.
        - admit.
        - rewrite list_lookup_insert_eq; first done. admit.
        - done.
        - unfold set. destruct Hfrel as [_ <-]. by iDestruct "Hinst" as "(_ & (_ & _ & H & _) & _)".
        - iIntros "Hlayout Hrt _ Hown _".
          instantiate
            (1 := fun f' vs' =>
                    (⌜f' = f0 <| f_locs ::= <[ localimm laddr := VAL_int32 ta32 ]> |>⌝ ∗
                       ⌜vs' = []⌝ ∗
                       ℓ ↦layout set_flags_at 1 (flat_map arep_flags ιs) (repeat FlagInt n) ∗
                       rt_token rti sr (fun ℓ' => ℓ <> ℓ') θ' ∗
                       na_own logrel_nais ⊤)%I).
          by iFrame.
      }

      clear Hes12.
      iIntros (??) "(-> & -> & Hlayout & Hrt & Hown) Hf Hrun".
      rewrite app_nil_l app_assoc.
      iApply (cwp_seq with "[Hf Hrun]").
      {
        iApply (cwp_local_set with "[] [$Hf] [$Hrun]").
        - admit.
        - by instantiate
               (1 := fun f' vs' =>
                       (⌜f' = f0 <| f_locs ::= <[ localimm laddr := VAL_int32 ta32 ]> |>
                                 <| f_locs ::= <[ localimm ltag := VAL_int32 (Wasm_int.int_of_Z i32m i) ]> |>⌝ ∗
                          ⌜vs' = []⌝)%I).
      }

      iIntros (??) "[-> ->] Hf Hrun".
      eapply wp_store1_mm_strong in Hcg_store_tag as (_ & -> & -> & Hes19).
      rewrite app_assoc.
      iApply (cwp_seq with "[Haddr Hheap Hrt Hf Hrun]").
      {
        iApply (Hes19 with "[$Hf] [$Hrun] [$Hheap] [$Haddr] [] [$Hrt]").
        - iPureIntro. by intros H.
        - iPureIntro. instantiate (1 := ta32). unfold set. cbn.
          rewrite list_lookup_insert_ne; first rewrite list_lookup_insert_eq; first done.
          + admit.
          + admit.
        - iPureIntro. unfold set. cbn. rewrite list_lookup_insert_eq; first done.
          admit.
        - inversion Hta. by subst ta.
        - by inversion Hta.
        - by inversion Hta.
        - admit.
        - by instantiate (1 := I32A (Wasm_int.Int32.repr i)).
        - done.
        - unfold set. destruct Hfrel as [_ <-]. by iDestruct "Hinst" as "(_ & _ & _ & _ & H & _)".
        - done.
        - iIntros "Hheap Haddr Hrt".
          instantiate
            (1 := fun f' vs' =>
                    (⌜f' = f0 <| f_locs ::= <[ localimm laddr := VAL_int32 ta32 ]> |>
                              <| f_locs ::= <[ localimm ltag := VAL_int32 (Wasm_int.int_of_Z i32m i)]> |>⌝ ∗
                       ⌜vs' = []⌝ ∗
                       ℓ ↦heap path.update_path_words 0 ws (serialize_atom (I32A (Wasm_int.Int32.repr i))) ∗
                       ℓ ↦addr (MemMM, a) ∗
                       rt_token rti sr (λ ℓ' : location, ℓ ≠ ℓ') θ')%I).
          by iFrame.
      }

      clear Hes19.
      destruct Hos as (os' & Hos' & Hos).
      inversion Hos'.
      subst os'.
      clear Hos'.
      iIntros (??) "(-> & -> & Hheap & Haddr & Hrt) Hf Hrun".
      rewrite app_nil_l.
      eapply wp_store_strong_mm in Hcg_store as (_ & -> & -> & Hes21); last first.
      { admit. }
      iApply (cwp_seq with "[Hheap Haddr Hrt Hf Hrun]").
      {
        iApply (Hes21 with "[$Hf] [$Hrun] [$Hheap] [$Haddr] [] [$Hrt]").
        - iPureIntro. by intro.
        - iPureIntro. unfold set.
          rewrite list_lookup_insert_ne; first rewrite list_lookup_insert_eq; first done.
          + admit.
          + admit.
        - admit.
        - inversion Hta. by subst ta.
        - by inversion Hta.
        - by inversion Hta.
        - admit.
        - done.
        - done.
        - unfold set. destruct Hfrel as [_ <-]. by iDestruct "Hinst" as "(_ & _ & _ & _ & H & _)".
        - admit.
        - iIntros "Hheap Haddr Hrt".
          instantiate
            (1 := fun f' vs' =>
                    (⌜f' = f0 <| f_locs ::= <[ localimm laddr := VAL_int32 ta32 ]> |>
                              <| f_locs ::= <[ localimm ltag := VAL_int32 (Wasm_int.int_of_Z i32m i) ]> |>⌝ ∗
                     ⌜vs' = []⌝ ∗
                     ℓ ↦heap path.update_path_words 1
                               (path.update_path_words 0 ws
                                  (serialize_atom (I32A (Wasm_int.Int32.repr i))))
                               (concat (map serialize_atom os)) ∗
                     ℓ ↦addr (MemMM, a) ∗
                     rt_token rti sr (λ ℓ' : location, ℓ ≠ ℓ') θ')%I).
          by iFrame.
      }

      clear Hes21.
      iIntros (??) "(-> & -> & Hheap & Haddr & Hrt) Hf Hrun".
      rewrite app_nil_l.
      iApply (cwp_local_get with "[-Hf Hrun] [$Hf] [$Hrun]").
      {
        unfold set.
        rewrite list_lookup_insert_ne; first rewrite list_lookup_insert_eq; first done.
        - admit.
        - admit.
      }

      iModIntro.
      iSplitR; last iSplitL "Hframe"; last iSplitR "Hrt Hown"; last iSplitL "Hrt"; last done.
      + admit.
      + admit.
      + iExists [I32A ta32]. iSplitL; last by cbn. admit.
      + iExists θ'. admit.
    - admit.
  Admitted.

End inject_new.
