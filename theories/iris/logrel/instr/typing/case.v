Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.util.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section case.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  (* TODO: this should probably be a definition in the compiler. *)
  Definition compile_cases :=
    (fix compile_cases
    (fe : function_env) (ess : list (list instruction)) {struct ess} : list (codegen ()) :=
      match ess with
      | [] => []
      | es :: ess' =>
          mapM_ (compile_instr mr fe) es :: compile_cases fe ess'
      end).

  Lemma compile_cases_length fe ess :
    length ess = length $ compile_cases fe ess.
  Proof.
    induction ess as [|? ? IH]; [done | simpl; rewrite IH; done].
  Qed.

  Lemma compile_cases_app fe ess1 ess2 :
    (fix compile_cases fe ess := match ess with
     | [] => [] | es :: ess' => mapM_ (compile_instr mr fe) es :: compile_cases fe ess'
     end) fe (ess1 ++ ess2) =
    (fix compile_cases fe ess := match ess with
     | [] => [] | es :: ess' => mapM_ (compile_instr mr fe) es :: compile_cases fe ess'
     end) fe ess1 ++
    (fix compile_cases fe ess := match ess with
     | [] => [] | es :: ess' => mapM_ (compile_instr mr fe) es :: compile_cases fe ess'
     end) fe ess2.
  Proof.
    induction ess1; simpl; [done | by rewrite IHess1].
  Qed.

  Lemma compat_case_blocks_fail F wt wt' (tag_idx : nat) tag wl_ret wl wl' ρs_sum
    val_localidxs vs_res
    (ess : list (list instruction)) es_fail_cases (start : nat) fr B R τ_res :
    let fe := fe_of_context F in
    let tag_localidx := Mk_localidx tag_idx in
    (tag < start ∨ tag ≥ start + length ess) ->
    f_locs fr !! tag_idx = Some (VAL_int32 (Wasm_int.Int32.repr tag)) ->
    prelude.translate_type (fe_type_vars fe) τ_res = Some wl_ret ->
    (tag < Wasm_int.Int32.modulus)%Z ->
    (length ρs_sum <= Wasm_int.Int32.modulus)%Z ->
    (length ess <= length ρs_sum)%Z ->
    length vs_res = length wl_ret ->
    run_codegen
      (case_blocks_blocks start tag_localidx wl_ret
         (map (λ c i,
            try_option EFail (ρs_sum !! i)
            ≫= λ ρ, try_option EFail (inject_sum_rep EmptyEnv ρs_sum ρ)
            ≫= λ ixs', (try_option EFail (nths_error val_localidxs ixs')
                         ≫= get_locals_w)
            ≫= λ _, c)
            (compile_cases fe ess)))
      wt wl =
    inr ((), wt', wl', es_fail_cases) ->
    ⊢
    ↪[frame]fr -∗
    ↪[RUN] -∗
    CWP to_consts vs_res ++ es_fail_cases
      UNDER B; R
      {{ fr'; vs', ⌜fr' = fr⌝ ∗ ⌜vs' = vs_res⌝ }}.
  Proof.
    revert start wt wl wt' wl' es_fail_cases.
    induction ess as [| es_hd ess IH]; intros start wt wl wt' wl' es_fail_cases fe tag_localidx
        Hrange Htag_lookup Htranslate Htag_lt Hlen_lt Hlen_le Hvs_len Hcg.
    - (* base case: no blocks *)
      simpl in Hcg.
      inv_cg_ret Hcg; subst.
      iIntros "Hfr Hrun".
      rewrite app_nil_r.
      iApply (cwp_val with "[$] [$]").
      1: apply has_values_to_consts.
      done.
    - (* inductive case *)
      simpl compile_cases in Hcg.
      rewrite map_cons in Hcg.
      change (run_codegen
        (case_block tag_localidx wl_ret
           (λ i, try_option EFail (ρs_sum !! i)
                 ≫= λ ρ, try_option EFail (inject_sum_rep EmptyEnv ρs_sum ρ)
                 ≫= λ ixs', (try_option EFail (nths_error val_localidxs ixs')
                              ≫= get_locals_w)
                 ≫= λ _, mapM_ (compile_instr mr fe) es_hd) start ;;
         case_blocks_blocks (S start) tag_localidx wl_ret
           (map (λ c i,
              try_option EFail (ρs_sum !! i)
              ≫= λ ρ, try_option EFail (inject_sum_rep EmptyEnv ρs_sum ρ)
              ≫= λ ixs', (try_option EFail (nths_error val_localidxs ixs')
                           ≫= get_locals_w)
              ≫= λ _, c)
              (compile_cases fe ess)))
        wt wl = inr ((), wt', wl', es_fail_cases)) in Hcg.
      apply run_codegen_bind_dist in Hcg as
        (x1 & wt1 & wt2 & wl1 & wl2 & es1 & es2 & Hcg_hd & Hcg_tl & -> & -> & ->).

      (* Case es_i *)
      inv_cg_bind Hcg_hd ?pair ?wt ?wt ?wl ?wl ?es ?es Hcase_es_i Hcase_es_i_block.
      destruct pair, u.
      inv_cg_emit Hcase_es_i_block; subst.
      apply run_codegen_capture in Hcase_es_i as [Hcase_es_i ->].

      inv_cg_bind Hcase_es_i [] ?wt ?wt ?wl ?wl ?es ?es Hget_tag Hcase_es_i.
      inv_cg_emit Hget_tag; subst.

      inv_cg_bind Hcase_es_i [] ?wt ?wt ?wl ?wl ?es ?es Htag0 Hcase_es_i.
      inv_cg_emit Htag0; subst.

      inv_cg_bind Hcase_es_i [] ?wt ?wt ?wl ?wl ?es ?es Hcompare_tag Hcase_es_i.
      inv_cg_emit Hcompare_tag; subst.

      inv_cg_bind Hcase_es_i [] ?wt ?wt ?wl ?wl ?es ?es Hbr_case Hcase_es_i.
      inv_cg_emit Hbr_case; subst.

      inv_cg_bind Hcase_es_i [] ?wt ?wt ?wl ?wl es_drop_i ?es Hdrop_consts_i Hcase_es_i.
      apply run_codegen_drop_consts in Hdrop_consts_i as H.
      destruct H as (_ & -> & -> & _).

      inv_cg_bind Hcase_es_i ρ_casei ?wt ?wt ?wl ?wl ?es ?es Hlookup Hcase_es_i.
      inv_cg_try_option Hlookup; subst.

      inv_cg_bind Hcase_es_i case_i_sum_locals ?wt ?wt ?wl ?wl ?es ?es Hinject Hcase_es_i.
      inv_cg_try_option Hinject; subst.

      inv_cg_bind Hcase_es_i [] ?wt wt_case_i ?wl wl_case_i ?es es_case_i Hget_locals_i Hcase_es_i.
      inv_cg_bind Hget_locals_i case_i_val_idxs ?wt wt_get_locals_i ?wl wl_get_locals_i ?es es_get_locals_i Hnths_error Hget_locals_i.
      inv_cg_try_option Hnths_error; subst.

      destruct (run_codegen_get_locals _ _ _ _ _ _ _ Hget_locals_i) as ([] & -> & ->).

      (* clean up *)
      clear_nils.
      simplify_eq.

      assert (tag ≠ start) as Hneq.
      {
        destruct Hrange as [Hlt | Hge]; simpl in *; lia.
      }

      assert (start < Wasm_int.Int32.modulus)%Z as Hlt_start.
      {
        destruct Hrange as [Hlt | Hge]; simpl in *.
        - apply lookup_lt_Some in Heq_some. lia.
        - lia.
      }

      iIntros "Hfr Hrun".
      rewrite app_assoc.
      iApply (cwp_seq with "[Hfr Hrun]").
      {
        instantiate (1 := λ f' v, (⌜v = vs_res⌝ ∗ ⌜f' = fr⌝)%I).
        iApply (cwp_block with "[$] [$]"); auto.
        { apply is_consts_to_consts. }
        { by rewrite length_map. }
        iIntros "!> Hf Hrun".

        iEval (do 3 rewrite app_assoc).
        iApply (cwp_seq with "[Hf Hrun]").
        {
          iEval (do 2 rewrite -app_assoc).
          iApply cwp_val_app; first apply has_values_to_consts.

          (* Get tag from local *)
          rewrite (separate1 (prelude.W.BI_get_local _)).
          iApply (cwp_seq with "[Hf Hrun]").
          {
            iApply (cwp_local_get with "[] [$] [$]"); first apply Htag_lookup.
            by instantiate (1 := λ f' v, (⌜v = [_]⌝ ∗ ⌜f' = fr⌝)%I).
          }
          iIntros (?fr w) "(-> & ->) Hf Hrun".
          iSimpl.

          (* compare tag with case number: start *)
          rewrite separate3.
          iApply (cwp_seq with "[Hf Hrun]").
          {
            iApply (cwp_relop with "[$] [$]"); first done.
            iSimpl.
            rewrite Wasm_int.Int32.eq_false.
            2: {
              intro Heq.
              apply Hneq.
              apply Nat2Z.inj.
              apply Wasm_int.Int32.repr_inv; [lia | lia | exact Heq].
            }
            iSimpl.
            by instantiate (1 := λ f' v, (⌜v = [_]⌝ ∗ ⌜f' = fr⌝)%I).
          }
          iIntros (?fr w) "(-> & ->) Hf Hrun".
          iSimpl.
          iApply (cwp_val with "[$] [$]").
          - by instantiate (1 := [(VAL_int32 Wasm_int.Int32.one)]).
          - unfold fvs_combine.
            by instantiate (1 := λ f' v, (⌜v = _ ++ [_]⌝ ∗ ⌜f' = fr⌝)%I).
        }
        iIntros (?fr w) "(-> & ->) Hf Hrun".

        iEval (rewrite app_assoc).

        iApply (cwp_seq with "[-]").
        2: {
          instantiate (1 := λ f vs, False%I).
          by iIntros.
        }
        unfold to_consts.
        rewrite map_app.
        rewrite -app_assoc.
        replace (map BI_const [VAL_int32 Wasm_int.Int32.one] ++ [prelude.W.BI_br_if 0])
        with [BI_const (VAL_int32 Wasm_int.Int32.one); prelude.W.BI_br_if 0]; last done.

        iApply (cwp_br_if_nonzero with "[$] [$]"); try done.
        1: apply has_values_to_consts.
        by rewrite length_map.
      }
      iIntros (?fr w) "(-> & ->) Hfr Hrun".
      iApply (IH (S start) with "[$] [$]"); try done.
      + destruct Hrange as [Hlt | Hge]; simpl in *.
        * left. lia.
        * right. lia.
      + simpl in Hlen_le. lia.
  Qed.

  Lemma compat_case_block_success M F L wt wt_case_tag wtf tag_idx (tag : nat)
    wl_ret B R se L' wl wl_case_tag wlf
    (τs: list type) τ_tag τ_res case_tag_os_payload val_localidxs vs_payload vs_res
    ιs_tag ιs ixs
    ρs_sum fr_saved_and_tag θ os_payload es_tag_cg (ess_pre : list (list instruction))
    (es_tag : list instruction) :
    let F' := F <| fc_labels ::= cons ([τ_res], L') |> in
    let fe := fe_of_context F in
    let lmask := wlmask fe wl in
    let tag_localidx := Mk_localidx tag_idx in
    f_locs fr_saved_and_tag !! tag_idx = Some (VAL_int32 (Wasm_int.Int32.repr tag)) ->
    prelude.translate_type (fe_type_vars fe) τ_res = Some wl_ret ->
    τs !! tag = Some τ_tag ->
    length ess_pre = tag ->
    length vs_res = length wl_ret ->
    length τs = length ρs_sum ->
    τs !! tag = Some τ_tag ->
    type_arep se τ_tag = Some ιs_tag ->
    tail <$> eval_rep se (SumR ρs_sum) = Some ιs ->
    inject_sum_arep ιs ιs_tag = Some ixs ->
    nths_error os_payload ixs = Some case_tag_os_payload ->
    Forall (λ i : prelude.W.localidx, localimm i ≠ tag_idx) val_localidxs ->
    Forall2
      (λ (i : prelude.W.localidx) (v : value),
         f_locs fr_saved_and_tag !! localimm i = Some v)
       val_localidxs vs_payload ->
    sem_env_interp F se ->
    run_codegen
      (case_block tag_localidx wl_ret
         (λ i,
            try_option EFail (ρs_sum !! i)
            ≫= λ ρ, try_option EFail (inject_sum_rep EmptyEnv ρs_sum ρ)
            ≫= λ ixs', (try_option EFail (nths_error val_localidxs ixs')
                         ≫= get_locals_w)
            ≫= λ _, mapM_ (compile_instr mr fe) es_tag)
         (length ess_pre))
      wt wl =
    inr ((), wt_case_tag, wl_case_tag, es_tag_cg) ->
    (∀ (wt wt' wtf : list prelude.W.function_type) (wl wl' wlf : list prelude.W.value_type)
        (es' : prelude.W.expr),
        let fe' := fe_of_context F' in
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        let lmask := wlmask fe wl in
        run_codegen (compile_instrs mr fe' es_tag) wt wl = inr ((), wt', wl', es')
        → ⊢ have_instr_type_sem rti sr mr M F' L WT WL lmask es'
          (InstrT [τ_tag] [τ_res]) L') ->
    ⊢
    instance_interp rti sr mr M (wt ++ wt_case_tag ++ wtf) fr_saved_and_tag.(f_inst) -∗
    labels_interp rti sr se F.(typing.fc_locals) fr_saved_and_tag (wl ++ wl_case_tag ++ wlf) lmask (fc_labels F) B -∗
    return_interp rti sr se (fc_return F) R -∗
    rt_token rti sr θ -∗
    ▷ value_interp rti sr se τ_tag (SAtoms case_tag_os_payload) -∗
    atoms_interp os_payload vs_payload -∗
    frame_interp rti sr se F.(typing.fc_locals) L (wl ++ wl_case_tag ++ wlf) fr_saved_and_tag -∗
    ↪[frame]fr_saved_and_tag -∗
    ↪[RUN] -∗
      CWP to_consts vs_res ++ es_tag_cg
        UNDER B; R
        {{ fr'; vs',
              ⌜length vs' = length wl_ret⌝ ∗
              ⌜frame_rel lmask fr_saved_and_tag fr'⌝ ∗
              frame_interp rti sr se F.(typing.fc_locals) L' (wl ++ wl_case_tag ++ wlf) fr' ∗
              ∃ (os' : leibnizO (list atom)) (θ : address_map),
               values_interp rti sr se [τ_res] os' ∗ atoms_interp os' vs' ∗
               rt_token rti sr θ
        }}.
  Proof.
    intros F' fe lmask tag_localidx Hlookup_saved_and_tag Htranslate_type_fe Ht_lookup_tag Heq Hvs_res_len Htyp_rep_len Hlookup_typs Htype_arep Heval_rep Hinject_sum_arep Hnerr_os Htag_not_val_localidx Hsaved Hsem Hcg_tag Hsem_es_tag.
    iIntros "#Hinst #Hlabels #Hreturn Hrt Hvalue_interp_os_tag Hatoms_interp_payload Hframe_saved_and_tag Hfr Hrun".

    (* Case es_tag *)
    inv_cg_bind Hcg_tag ?pair ?wt ?wt ?wl ?wl ?es ?es Hcase_es_tag Hcase_es_tag_block.
    destruct pair, u.
    inv_cg_emit Hcase_es_tag_block; subst.
    apply run_codegen_capture in Hcase_es_tag as [Hcase_es_tag ->].

    inv_cg_bind Hcase_es_tag [] ?wt ?wt ?wl ?wl ?es ?es Hget_tag Hcase_es_tag.
    inv_cg_emit Hget_tag; subst.

    inv_cg_bind Hcase_es_tag [] ?wt ?wt ?wl ?wl ?es ?es Htag0 Hcase_es_tag.
    inv_cg_emit Htag0; subst.

    inv_cg_bind Hcase_es_tag [] ?wt ?wt ?wl ?wl ?es ?es Hcompare_tag Hcase_es_tag.
    inv_cg_emit Hcompare_tag; subst.

    inv_cg_bind Hcase_es_tag [] ?wt ?wt ?wl ?wl ?es ?es Hbr_case Hcase_es_tag.
    inv_cg_emit Hbr_case; subst.

    inv_cg_bind Hcase_es_tag [] ?wt ?wt ?wl ?wl es_drop_tag ?es Hdrop_consts_tag Hcase_es_tag.
    apply run_codegen_drop_consts in Hdrop_consts_tag as H.
    destruct H as (_ & -> & -> & _).

    inv_cg_bind Hcase_es_tag ρ_case_tag ?wt ?wt ?wl ?wl ?es ?es Hlookup Hcase_es_tag.
    inv_cg_try_option Hlookup; subst.

    inv_cg_bind Hcase_es_tag case_tag_sum_locals ?wt ?wt ?wl ?wl ?es ?es Hinject Hcase_es_tag.
    inv_cg_try_option Hinject; subst.

    inv_cg_bind Hcase_es_tag [] ?wt wt_case_tag ?wl wl_case_tag ?es es_case_tag Hget_locals_tag Hcase_es_tag.
    inv_cg_bind Hget_locals_tag case_tag_val_idxs ?wt wt_get_locals_tag ?wl wl_get_locals_tag ?es es_get_locals_tag Hnths_error Hget_locals_tag.
    inv_cg_try_option Hnths_error; subst.

    destruct (run_codegen_get_locals _ _ _ _ _ _ _ Hget_locals_tag) as ([] & -> & ->).

    (* clean up *)
    clear_nils.
    simplify_eq.

    iDestruct (Hsem_es_tag _ _ wtf _ _ wlf _ Hcase_es_tag) as "Hsem_es_tag".

    iApply (cwp_block with "[$] [$]"); auto.
    { apply is_consts_to_consts. }
    { by rewrite length_map. }
    iIntros "!> Hf Hrun".

    iEval (do 4 rewrite app_assoc).
    iApply (cwp_seq with "[Hf Hrun]").
    {
      iEval (do 3 rewrite -app_assoc).
      iApply cwp_val_app; first apply has_values_to_consts.

      (* Get tag from local *)
      rewrite (separate1 (prelude.W.BI_get_local _)).
      iApply (cwp_seq with "[Hf Hrun]").
      {
        iApply (cwp_local_get with "[] [$] [$]"); first apply Hlookup_saved_and_tag.
        by instantiate (1 := λ f v, (⌜v = [_]⌝ ∗ ⌜f = fr_saved_and_tag⌝)%I).
      }
      iIntros (?fr w) "(-> & ->) Hf Hrun".
      iSimpl.

      (* compare tag with case number: i *)
      rewrite separate3.
      iApply (cwp_seq with "[Hf Hrun]").
      {
        iApply (cwp_relop with "[$] [$]"); first done.
        iSimpl.
        by instantiate (1 := λ f v, (⌜v = [_]⌝ ∗ ⌜f = fr_saved_and_tag⌝)%I).
      }
      iIntros (?fr w) "(-> & ->) Hf Hrun".
      iSimpl.
      iApply (cwp_br_if_zero with "[$] [$]").
      - by rewrite Wasm_int.Int32.eq_true.
      - instantiate (1 := λ f v, (⌜v = vs_res⌝ ∗ ⌜f = fr_saved_and_tag⌝)%I).
        unfold fvs_combine.
        by rewrite app_nil_r.
    }
    iIntros (?fr w) "(-> & ->) Hf Hrun".

    (* drop default values *)
    rewrite (app_assoc (to_consts _)).
    iApply (cwp_seq with "[Hf Hrun]").
    {
      instantiate (1 := λ f vs, (⌜f = fr_saved_and_tag⌝ ∗ ⌜vs = []⌝)%I).
      eapply cwp_drop_consts in Hdrop_consts_tag as (_ & _ & _ & Hdrop_consts_tag).
      - iDestruct (Hdrop_consts_tag with "[$] [$] []") as "Hdrop_consts_tag".
        2: iApply "Hdrop_consts_tag".
        done.
      - by rewrite length_map.
      - apply is_consts_to_consts.
    }
    iIntros (?fr w) "(-> & ->) Hf Hrun".
    iSimpl.

    edestruct (util.nths_error_exists val_localidxs case_tag_val_idxs vs_payload case_tag_sum_locals (Forall2_length _ _ _ Hsaved)) as [case_tag_vs_payload Hnerr_payload_ctag]; try done.

    assert (Forall2 (λ (i : prelude.W.localidx) (v : value), f_locs fr_saved_and_tag !! localimm i = Some v)
      case_tag_val_idxs case_tag_vs_payload) as Hf_case_tag.
    {
      pose proof (util.nths_error_Forall2 _ val_localidxs case_tag_val_idxs vs_payload case_tag_vs_payload case_tag_sum_locals Hsaved Heq_some1 Hnerr_payload_ctag) as Hf_case_tag.
      eapply forall2_lookup_same.
      3: done.
      - intros. instantiate (1 := tag_idx) in H.
        reflexivity.
      - eapply (util.nths_error_Forall _ val_localidxs); done.
    }

    (* get locals corresponding to payload of sum *)
    eapply cwp_restore_stack_w in Hget_locals_tag; eauto using Forall2_length.
    destruct Hget_locals_tag as (_ & _ & _ & Hget_locals_tag).
    iDestruct (Hget_locals_tag with "[$] [$] []") as "Hget_locals_tag"; clear Hget_locals_tag; first done.

    iApply (cwp_seq with "[Hget_locals_tag]").
    1: iApply "Hget_locals_tag".
    iIntros (?fr w) "(-> & ->) Hf Hrun".

    assert (prelude.translate_types (fc_type_vars F) [τ_res] = Some wl_ret) as Htranslate_types_single.
    {
      subst fe.
      unfold fe_of_context, fe_type_vars in Htranslate_type_fe.
      unfold prelude.translate_types.
      simpl.
      rewrite Htranslate_type_fe.
      simpl.
      by rewrite app_nil_r.
    }

    (* Reason about case 1 code *)
    iApply (cwp_wand with "[-]").
    {
      iApply ("Hsem_es_tag" with "[//] [] [$] [] [] [Hatoms_interp_payload] [Hvalue_interp_os_tag] [Hframe_saved_and_tag] [$] [$] [$]").
      + instantiate (1 := case_tag_vs_payload); iPureIntro; simpl; rewrite has_values_iff_to_consts; done.
      + subst F'.
        replace (fc_labels (F <| fc_labels ::= cons ([τ_res], L') |>)) with
            (([τ_res], L') :: fc_labels F); last done.
            iSimpl. iApply labels_interp_cons; try done.
            iIntros "!>" (fr' vs') "(%Hfrel & Hframe & (%os & Hvalues & Hatoms) & [%Θ Hrt])".
            iDestruct (atoms_interp_length with "Hatoms") as "<-".
            iDestruct (translate_types_comp_interp_length with "Hvalues") as "<-"; try done.
            by iFrame.
      + done.
      + instantiate (1 := case_tag_os_payload). (* TODO: should be provable, but might be a little annoying *)
        (* assert (case_tag_sum_locals = ixs) as ->. *)
        (* { *)
        (*   unfold inject_sum_rep in Heq_some0. *)
        (*   apply bind_Some in Heq_some0. *)
        (*   destruct Heq_some0 as [ιs' [H_tail H_rest]]. *)
        (*   apply bind_Some in H_rest. *)
        (*   destruct H_rest as [ιs_tag' [H_eval H_inject]]. *)
        (**)
        (*   apply eval_rep_emptyenv with (se:=se) in H_eval. *)
        (*   apply fmap_Some in H_tail. *)
        (*   destruct H_tail as [full_list [H_eval_sum H_tail_eq]]. *)
        (*   apply eval_rep_emptyenv with (se := se) in H_eval_sum. *)
        (*   have H_tail' : tail <$> eval_rep se (SumR ρs_sum) = Some ιs' by *)
        (*   rewrite H_eval_sum; simpl; rewrite H_tail_eq; reflexivity. *)
        (*   rewrite H_tail' in Heval_rep. *)
        (*   simplify_eq. *)
        (*   admit. *)
        (* } *)
        admit.
        (*
          has_instruction_type_ok F (InstrT [SumT (VALTYPE (SumR ρs_sum) rf) τs] [τ_res]) L'
          type_skind se (SumT (VALTYPE (SumR ρs_sum) rf) τs) = Some κ

          length τs = length ρs_sum
          ρs_sum !! tag = Some ρ_case_tag
          τs     !! tag = Some τ_tag

          eval_rep  se ρ_case_tag = Some ιs_tag'
          type_arep se τ_tag      = Some ιs_tag

           ιs_tag' = ιs_tag
         *)


        (*
          has_instruction_type_ok F (InstrT [SumT (VALTYPE (SumR ρs_sum) rf) τs] [τ_res]) L'
          type_skind se (SumT (VALTYPE (SumR ρs_sum) rf) τs) = Some κ

          tail <$> eval_rep se (SumR ρs_sum) = Some ιs'
          tail <$> eval_rep se (SumR ρs_sum) = Some ιs

          length τs = length ρs_sum
          ρs_sum !! tag = Some ρ_case_tag
          τs     !! tag = Some τ_tag

          eval_rep  se ρ_case_tag = Some ιs_tag'
          type_arep se τ_tag      = Some ιs_tag

          inject_sum_arep ιs' ιs_tag' = Some case_tag_sum_locals
          inject_sum_arep ιs  ιs_tag  = Some ixs


          case_tag_sum_locals =?= ixs
        *)

        (* TODO
           Goal:
           tag < length τs
           length τs = length (ess_pre ++ es_tag :: ess_post)
           tag = length ess_pre


            length τs = length ρs_sum

            τs !! tag = Some τ_tag
            type_arep se τ_tag = Some ιs_tag
            ρs_sum !! tag = Some ρ_case_tag

            tail <$> eval_rep se (SumR ρs_sum) = Some ιs

            inject_sum_arep         ιs     ιs_tag     = Some ixs
            inject_sum_rep EmptyEnv ρs_sum ρ_case_tag = Some case_tag_sum_locals


            nths_error vs_payload case_tag_sum_locals = Some case_tag_vs_payload
            nths_error os_payload ixs                 = Some case_tag_os_payload

            case_tag_sum_locals =?= ixs

            atoms_interp os_payload vs_payload
            --------------------------------------∗
            atoms_interp case_tag_os_payload case_tag_vs_payload

         *)
      + by iApply values_interp_one_eq.
      + done.
    }
    iIntros (f vs) "(%Hfrel & Hframe & (%os' & Hvalues & Hatoms) & [%θ' Hrt])".

    iDestruct (atoms_interp_length with "Hatoms") as "<-".
    iDestruct (translate_types_comp_interp_length with "Hvalues") as "<-"; try done.
    by iFrame.
  Admitted.

  Lemma compat_case M F L L' wt wt' wtf wl wl' wlf es' ess τs τs' κ :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let F' := F <| fc_labels ::= cons (τs', L') |> in
    let ψ := InstrT [SumT κ τs] τs' in
    Forall2
      (fun τ es =>
         (forall wt wt' wtf wl wl' wlf es',
            let fe' := fe_of_context F' in
            let WT := wt ++ wt' ++ wtf in
            let WL := wl ++ wl' ++ wlf in
            let lmask := wlmask fe wl in
            run_codegen (compile_instrs mr fe' es) wt wl = inr ((), wt', wl', es') ->
            ⊢ have_instr_type_sem rti sr mr M F' L WT WL lmask es' (InstrT [τ] τs') L'))
      τs ess ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ICase ψ L' ess)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L'.
  Proof.
    intros fe WT WL lmask F' Ψ Hforall Hok Hcg.
    subst Ψ.
    cbn [compile_instr] in Hcg.
    destruct κ as [ ρ rf | ]; last inversion Hcg.
    destruct ρ  as [ | ρs_sum | | ]; try done.
    destruct τs' as [ | τ_res τs' ]; first done.
    destruct τs'; last done.

    inv_cg_bind Hcg wl_ret ?wt ?wt ?wl ?wl ?es ?es Hres_type Hcg.
    inv_cg_try_option Hres_type; subst.

    destruct (Wasm_int.Int32.modulus <? length ρs_sum)%Z eqn:Hcmp; first inversion Hcg.
    inv_cg_bind Hcg ?units ?wt ?wt ?wl ?wl ?es es_case1 Hret Hcg.
    inv_cg_ret Hret; subst.
    apply Z.ltb_ge in Hcmp.

    inv_cg_bind Hcg ρs_atom ?wt ?wt ?wl ?wl ?es ?es Hιs Hcg.
    inv_cg_try_option Hιs; subst.
    inv_cg_bind Hcg val_localidxs wt_save ?wt wl_save ?wl es_save ?es Hsave Hcg.
    repeat rewrite app_nil_r in Hsave.

    (* Save tag *)
    inv_cg_bind Hcg tag_localidx ?wt ?wt ?wl ?wl ?es ?es HsaveTag Hcg.
    unfold save_stack1 in HsaveTag.
    inv_cg_bind HsaveTag ?tl ?wt ?wt ?wl ?wl ?es ?es Halloc_tag HsaveTag.
    apply wp_wlalloc in Halloc_tag as [Hlocal_tag_idx [-> [-> ->]]].
    inv_cg_bind HsaveTag [] ?wt ?wt ?wl ?wl es_set_tag ?es HsetTag HretTagIdx.
    inv_cg_emit HsetTag; subst.
    inv_cg_ret HretTagIdx; subst.

    clear_nils.
    set (tag_idx := (fe_wlocal_offset fe + length (wl ++ wl_save))).
    set (tag_localidx := Mk_localidx tag_idx).
    replace (Mk_localidx (fe_wlocal_offset fe + length (wl ++ wl_save))) with tag_localidx in *; last done.

    (* Put default result values on stack *)
    inv_cg_bind Hcg [] ?wt ?wt ?wl ?wl es_create_defaults ?es Hcreate_defaults Hcg.
    apply run_codegen_create_defaults in Hcreate_defaults as H.
    destruct H as (_ & -> & -> & _).

    subst WT WL.
    clear_nils.
    simplify_eq.

    (* Iris Proof *)
    iIntros (? ? ? ? ? ? ? ?) "%Hsem %Hhas_values #Hinst #Hlabels #Hreturn Hrvs Hvs Hframe Hrt Hfr Hrun".

    (* Our values are in the value interpretation for our specific SumT *)
    (* This means that the values represent the tag and the payload. *)
    iDestruct (values_interp_one_eq with "Hvs") as "Hvs".
    iDestruct (value_interp_eq with "Hvs") as "Hvs".
    unfold value_interp0, value_se_interp0.
    iDestruct "Hvs" as "(%κ & %Hkind_sum & Hskind_as_type & Hsum_interp)".
    (*unfold type_skind in Hkind_sum.*)
    iDestruct "Hsum_interp" as (tag os_payload case_tag_os_payload τ_tag ιs ιs_tag ixs  HSAtoms Htag_type_lookup Htag_type_arep Heval_rep_tail Hinject_sum_arep Hnerr_tag_os_payload) "Hvalue_interp_os_tag".
    simplify_eq.

    apply lookup_lt_Some in Htag_type_lookup as Htag_size_bound.
    assert (length τs = length ρs_sum) as Htyp_rep_len.
    {
      inversion Hok; subst.
      unfold has_mono_rep_instr in H.
      destruct H as [H _].
      simpl in H.
      rewrite Forall_singleton in H.
      inversion H; subst.
      inversion H1; subst.
      apply has_kind_SumT_inv in H3 as (rf' & HF2).
      by eapply Forall2_length.
    }
    assert (tag < Wasm_int.Int32.modulus)%Z as Htag_in_i32_bound.
    { rewrite Htyp_rep_len in Htag_size_bound. eapply Z.lt_le_trans; last done. by apply Nat2Z.inj_lt. }
    assert (length τs = length ess) as Hess_typ_len; first by eapply List.Forall2_length.

    iDestruct (big_sepL2_length with "Hrvs") as "%Hlen".
    destruct vs as [|v_tag vs_payload]; first inversion Hlen.
    clear Hlen.
    iDestruct (atoms_interp_cons with "Hrvs") as "[-> Hatoms_interp_payload]".

    iPoseProof (frame_interp_wl_interp with "Hframe") as "%Hwl"; first done.
    rewrite list_extra.cons_app in Hhas_values.
    apply has_values_app_inv in Hhas_values as (e_tag & es_payload & -> & Hhv_tag & Hhvs_payload).

    (* tag is an index into τs, so we must have: *)
    (* τs = τs_pre ++ [τ_tag] ++ τs_post *)
    (* ess = ess_pre ++ [es_tag] ++ ess_post *)
    apply list_elem_of_split_length in Htag_type_lookup as H.
    destruct H as (τs_pre & τs_post & Hτs_eq & Htag_len).

    rewrite Hτs_eq in Hforall.
    apply Forall2_app_inv_l in Hforall as
      (ess_pre & ess_rest & Hforall_pre & Hforall_rest & ->).
    apply Forall2_cons_inv_l in Hforall_rest as
      (es_tag & ess_post & Hforall_tag & Hforall_post & ->).
    apply Forall2_length in Hforall_pre as Hess_pre_τs_pre.
    apply Forall2_length in Hforall_post as Hess_post_τs_post.
    clear Hforall_pre Hforall_post.

    destruct κ; last first.
    {
      unfold skind_as_type_interp, ssize_interp.
      iDestruct "Hskind_as_type" as "[[] _]".
    }
    unfold type_skind, eval_kind in Hkind_sum.
    apply bind_Some in Hkind_sum.
    destruct Hkind_sum as (l' & Heval & Hret).
    unfold eval_rep in Heval.

    apply bind_Some in Heval.
    destruct Heval as (l''' & Heval' & Hret').
    inversion Hret'; subst l'.
    clear Hret'.
    inversion Hret; subst l r.
    clear Hret.

    unfold skind_as_type_interp.
    iDestruct "Hskind_as_type" as "[%Hhas_areps %Href]".
    apply has_areps_cons in Hhas_areps as [Hhas_areps Hhas_arep].

    apply eval_rep_emptyenv with (se:=se) in Heq_some0.
    rewrite Heq_some0 in Heval_rep_tail.
    simpl in Heval_rep_tail.
    inversion Heval_rep_tail as [Hιs_atom_tail].

    iAssert (⌜result_type_interp (map translate_prim (map arep_to_prim (tail ρs_atom))) vs_payload⌝%I) as "%Hres_type_vs_payload".
    {
      (* TODO: result_type_interp *)
      admit.
    }

    (* save payload *)
    eapply cwp_save_stack_w in Hsave; eauto.
    destruct Hsave as (Hval_localidxs_seq & -> & Hwl_save & Hsave).
    rewrite (app_assoc (e_tag ++ _)).
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      rewrite <- (app_assoc e_tag).
      instantiate (1 := λ fr' vs, (
        ∃ val_idxs,
        ⌜vs = [VAL_int32 (Wasm_int.Int32.repr tag)]⌝ ∗
        ⌜frame_rel (λ i, i ∉ val_idxs) fr fr'⌝ ∗
        ⌜Forall2 (fun i v => f_locs fr' !! localimm i = Some v) val_localidxs vs_payload⌝ ∗
        ⌜val_idxs = seq (fe_wlocal_offset fe + length wl) (length wl_save)⌝ ∗
        ⌜val_localidxs = map prelude.W.Mk_localidx val_idxs⌝
        )%I).
      iApply cwp_val_app; first done.
      iApply (Hsave with "[$] [$]").
      iIntros (f' [Hfsame Hfchanged]).
      unfold fvs_combine.
      subst val_localidxs wl_save.
      auto.
    }
    iIntros (fr_saved w) "(%val_idxs & -> & %Hfrel_fr_saved & %Hsaved & %Hval_idxs_seq & %Hval_localidxs) Hfr Hrun".
    clear Hsave.

    iPoseProof (frame_interp_update_frame' with "Hframe") as "Hframe_saved".
    2, 3, 5: done.
    { subst val_idxs fe. by rewrite fe_wlocal_offset_length. }
    { by subst wl_save. }

    iDestruct (frame_interp_wl_interp with "Hframe_saved") as "%Hwl_saved"; first done.
    pose proof (interp_wl_length _ _ _ Hwl_saved) as Hfr_saved_locs_len.

    assert (tag_idx < length (f_locs fr_saved)) as Htag_in_fr_saved.
    {
      subst tag_idx.
      simpl.
      eapply Nat.lt_le_trans; last done.
      - rewrite app_assoc.
        subst fe.
        instantiate (1 := F).
        repeat rewrite length_app.
        lias.
    }

    (* Store tag *)
    rewrite (app_assoc (map _ _)).
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      instantiate (1 := λ fr' vs, (
        ⌜vs = []⌝ ∗
        ⌜frame_rel (λ j, j ≠ tag_idx) fr_saved fr'⌝ ∗
        ⌜f_locs fr' !! tag_idx = Some (VAL_int32 (Wasm_int.Int32.repr tag))⌝
        )%I).
      iApply (cwp_local_set with "[] [$] [$]"); first done.
      iSplit; first done.
      iSplit.
      - iPureIntro.
        split; last done.
        intros j Hneq.
        simpl.
        rewrite list_lookup_insert_ne; [reflexivity | lia].
      - iSimpl.
        iPureIntro.
        rewrite list_lookup_insert_eq; try done.
    }
    iIntros (fr_saved_and_tag w) "(-> & %Hfrel_fr_saved_and_tag & %Hsaved_and_tag) Hfr Hrun".
    clear_nils.

    (* relate starting frame fr and fr_saved_and_tag *)
    pose proof (frame_rel_mask_trans_combine _ _ _ _ _ Hfrel_fr_saved Hfrel_fr_saved_and_tag) as Hfrel_fr_and_fr_saved_and_tag.
    simpl in Hfrel_fr_and_fr_saved_and_tag.

    assert (frame_rel lmask fr fr_saved_and_tag) as Hfrel_lmask_saved_and_tag.
    {
      eapply frame_rel_mask_mono; [| exact Hfrel_fr_and_fr_saved_and_tag].
      intros i [Hi_lo Hi_hi].
      split.
      + rewrite Hval_idxs_seq.
        intro Hin. apply elem_of_seq in Hin. lia.
      + unfold tag_idx. rewrite length_app. lia.
    }
    pose proof Hfrel_fr_and_fr_saved_and_tag as [_ ->].
    iDestruct (labels_interp_mono _ _ _ _ _ fr_saved_and_tag _ _ _ _ with "Hlabels") as "Hlabels'"; first done.
    {
      instantiate (1 := (wlmask (fe_of_context F') (wl ++ wl_save ++ [prelude.W.T_i32]))).
      intros i [Hi_lo Hi_hi].
      simpl.
      split.
      + exact Hi_lo.
      + rewrite -fe_of_context_labels.
        rewrite !length_app. simpl.
        subst fe.
        lia.
    }

    assert (Forall2 (λ (i : prelude.W.localidx) (v : value), f_locs fr_saved_and_tag !! localimm i = Some v)
      val_localidxs vs_payload) as Hfr_saved_and_tag_payload.
    {
      eapply forall2_lookup_same.
      3: done.
      - intros j Hneq. instantiate (1 := tag_idx) in Hneq.
        destruct Hfrel_fr_saved_and_tag as [-> _]; done.
      - subst val_idxs val_localidxs tag_idx.
        rewrite length_app Nat.add_assoc.
        subst wl_save.
        apply map_seq_forall_localidx_neq.
    }

    iEval (rewrite app_assoc) in "Hframe_saved".
    iPoseProof (frame_interp_update_frame' with "Hframe_saved") as "Hframe_saved_and_tag".
    5: {
      instantiate (1 := fr_saved_and_tag).
      instantiate (1 := [tag_idx]).
      eapply frame_rel_mask_mono; last done.
      intros i H ->.
      destruct H. by rewrite list_elem_of_singleton.
    }
    all: try done.
    2: {
      simpl.
      instantiate (1 := [_]).
      by apply Forall2_cons.
    }
    2: {
      apply Forall2_cons; split; last done.
      by eexists.
    }
    {
      subst tag_idx val_idxs fe.
      by rewrite fe_wlocal_offset_length.
    }

    (* Create defaults *)
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      eapply cwp_create_defaults in Hcreate_defaults as (_ & _ & _ & Hcreate_defaults).
      iDestruct (Hcreate_defaults with "[$] [$] []") as "Hcreate_defaults".
      {
        by instantiate (1 := λ f vs, (⌜f = fr_saved_and_tag⌝ ∗ ⌜vs = (map default_of_value_type wl_ret)⌝)%I).
      }
      iApply "Hcreate_defaults".
    }
    iIntros (??) "[-> ->] Hfr Hrun".

    rewrite compile_cases_app in Hcg.
    rewrite map_app in Hcg.
    rewrite map_cons in Hcg.
    rewrite separate1 in Hcg.
    apply run_codegen_case_blocks_blocks_app in Hcg as (wt_pre & wt_tag & wt_post & wl_pre & wl_tag & wl_post & es_pre & es_tag_cg & es_post & Hcg_pre & Hcg_tag & Hcg_post & -> & -> & ->).

    replace (length (map _ _)) with (length ess_pre) in Hcg_tag, Hcg_post.
    2: {
      rewrite length_map.
      apply compile_cases_length.
    }
    rewrite Nat.add_0_l in Hcg_tag, Hcg_post.

    (* Reason about ess_pre *)
    iEval (rewrite app_assoc).
    iApply (cwp_seq with "[Hfr Hrun]").
    {
      iApply (compat_case_blocks_fail F wt wt_pre tag_idx tag
      wl_ret (wl ++ wl_save ++ [prelude.W.T_i32]) wl_pre
      ρs_sum val_localidxs (map default_of_value_type wl_ret)
      ess_pre es_pre 0 fr_saved_and_tag B R τ_res with "[$] [$]").
      1: right; rewrite Nat.add_0_l; lia.
      1, 2, 3, 4, 7: done.
      1: lia.
      by rewrite length_map.
    }
    iIntros (?fr w) "(-> & ->) Hfr Hrun".

    iDestruct (labels_interp_mono _ _ _ _ _ fr_saved_and_tag _ _ _ _ with "Hlabels") as "Hlabels'''"; first done.
    {
      instantiate (1 := (wlmask (fe_of_context F') (wl ++ wl_save ++ [prelude.W.T_i32] ++ wl_pre))).
      intros i [Hi_lo Hi_hi].
      simpl.
      split.
      + exact Hi_lo.
      + rewrite -fe_of_context_labels.
        rewrite !length_app. simpl.
        subst fe.
        lia.
    }

    (* Reason about es_tag *)
    iEval (rewrite app_assoc).
    iApply (cwp_seq with "[-]").
    {
      (* TODO: clean up application *)
      iApply (compat_case_block_success M F L
      (wt ++ wt_pre) wt_tag (wt_post ++ wtf)
      tag_idx tag
      wl_ret B R se L'
      ((wl ++ wl_save ++ [prelude.W.T_i32]) ++ wl_pre) wl_tag (wl_post ++ wlf)
      τs τ_tag τ_res case_tag_os_payload val_localidxs vs_payload _
      _ _ _
      ρs_sum fr_saved_and_tag θ
      os_payload
      es_tag_cg
      ess_pre es_tag with "[] [Hlabels'] [$] [$] [$] [$] [Hframe_saved_and_tag] [$] [$]").
      - done.
      - done.
      - done.
      - lia.
      - by rewrite length_map.
      - done.
      - done.
      - done.
      - by rewrite Heq_some0.
      - done.
      - done.
      - rewrite Hval_localidxs.
        subst val_idxs tag_idx.
        rewrite length_app Nat.add_assoc.
        apply map_seq_forall_localidx_neq.
      - done.
      - done.
      - apply Hcg_tag.
      - apply Hforall_tag.

      - by repeat rewrite app_assoc.
      - by repeat rewrite app_assoc.
      - by repeat rewrite app_assoc.
    }
    iIntros (f_es_case_tag vs) "(%Hlen_vs & %Hfrel_new & Hframe & %os & %θ' & Hos & Hvs & Hrt) Hfr Hrun".

    (* Reason about ess_post *)
    iApply (cwp_wand with "[Hfr Hrun]").
    {
      iApply (compat_case_blocks_fail with "[$] [$]").
      1: left.
      8: apply Hcg_post.
      all: try done.
      all: try lias.
      2: { rewrite -Hess_post_τs_post -Htyp_rep_len. subst τs. rewrite length_app. lias. }
      rewrite -Hsaved_and_tag.
      destruct Hfrel_new as [Hmask _].
      symmetry.
      apply Hmask.
      subst tag_idx fe.
      unfold wlmask.
      repeat rewrite length_app.
      lias.
    }
    iIntros (??) "(-> & ->)".
    iEval (repeat rewrite -app_assoc) in "Hframe".
    iEval (repeat rewrite -app_assoc).
    iFrame.
    iPureIntro.
    unfold lmask.
    eapply frame_rel_trans.
    + eapply frame_rel_mask_mono; [| exact Hfrel_lmask_saved_and_tag].
      intros i [Hi_lo Hi_hi]. unfold lmask, wlmask. split; exact Hi_lo || exact Hi_hi.
    + eapply frame_rel_wlmask_mono; [| exact Hfrel_new].
      rewrite length_app. rewrite length_app. lia.
  Admitted.

End case.
