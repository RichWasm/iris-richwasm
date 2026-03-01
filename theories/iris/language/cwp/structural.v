Require Import iris.proofmode.tactics.

Require Import RichWasm.iris.helpers.prelude.iris_wasm_lang_properties.
From RichWasm.iris.language Require Import iris_wp_def lenient_wp logpred lwp_structural lwp_trap.
From RichWasm.iris.language.cwp Require Import base def util.

Set Bullet Behavior "Strict Subproofs".

Section structural.

  Context `{!wasmG Σ}.

  Lemma cwp_nil s E (f : frame) L R Φ :
    ↪[frame] f -∗ ↪[RUN] -∗ Φ f [] -∗ CWP [] @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros "Hf Hrun HΦ".
    iApply lenient_wp_nil.
    iFrame.
  Qed.

  Lemma cwp_val s E f vs L R Φ :
    ↪[frame] f -∗ ↪[RUN] -∗ Φ f vs -∗ CWP (map BI_const vs) @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros "Hf Hrun HΦ".
    iApply lenient_wp_value.
    - instantiate (1 := immV vs).
      unfold IntoVal.
      cbn.
      unfold v_to_e_list, to_e_list.
      change (@seq.map value _) with (@map value administrative_instruction).
      change (@seq.map basic_instruction _) with (@map basic_instruction administrative_instruction).
      by rewrite map_map.
    - iFrame.
  Qed.

  Lemma cwp_val_app E vs es L R Φ :
    CWP es @ E UNDER L; R {{ fvs_combine Φ vs }} -∗
    CWP (map BI_const vs ++ es) @ E UNDER L; R {{ Φ }}.
  Proof.
    iIntros "Hes".
    unfold cwp_wasm, to_e_list.
    change seq.map with (@map basic_instruction administrative_instruction).
    rewrite map_app.
    rewrite map_map.
    iApply lenient_wp_val_app; first apply to_val_v_to_e.
    iApply lenient_wp_wand; last iApply "Hes".
    iIntros (lv) "(%f & Hfr & Hfr_inv & HΦ)".
    iExists f.
    iFrame.
    destruct lv.
    - done.
    - done.
    - iDestruct "HΦ" as "[Hrun HΦ]".
      iFrame.
      unfold lp_br, cwp_post_lp, cwp_post_br, lp_combine, lp_br, vh_depth.
      rewrite <- push_const_lh_depth.
      destruct (L !! (i - lh_depth (lh_of_vh lh))); last done.
      destruct p as [n P].
      iDestruct "HΦ" as "(%vs0 & %vs1 & %Hbase & %Hlen & HP)".
      pose proof (get_base_l_push_const lh vs) as [Hbase' | Hbase'].
      + iExists (vs ++ vs0), vs1.
        iFrame.
        iPureIntro.
        split; last done.
        rewrite Hbase'.
        rewrite Hbase.
        by rewrite app_assoc.
      + iExists vs0, vs1.
        iFrame.
        iPureIntro.
        split; last done.
        rewrite Hbase'.
        by rewrite Hbase.
    - iDestruct "HΦ" as "[Hrun HΦ]".
      iFrame.
      unfold lp_ret, cwp_post_lp, cwp_post_ret, lp_combine, lp_ret.
      destruct R; last done.
      destruct r as [n P].
      iDestruct "HΦ" as "(%vs0 & %vs1 & %Hbase & %Hlen & HP)".
      pose proof (simple_get_base_l_push_const s vs) as [Hbase' | Hbase'].
      + iExists (vs ++ vs0), vs1.
        iFrame.
        iPureIntro.
        split; last done.
        rewrite Hbase'.
        rewrite Hbase.
        by rewrite app_assoc.
      + iExists vs0, vs1.
        iFrame.
        iPureIntro.
        split; last done.
        rewrite Hbase'.
        by rewrite Hbase.
    - done.
  Qed.

  Lemma cwp_seq s E es1 es2 L R Φ1 Φ2 :
    CWP es1 @ E UNDER L; R {{ Φ1 }} -∗
    (∀ f vs,
     Φ1 f vs -∗ ↪[frame] f -∗ ↪[RUN] -∗
     CWP map BI_const vs ++ es2 @ s; E UNDER L; R {{ Φ2 }}) -∗
    CWP es1 ++ es2 @ s; E UNDER L; R {{ Φ2 }}.
  Proof.
    iIntros "Hes1 Hes2".
    unfold cwp_wasm.
    rewrite to_e_list_app.
    iApply (lenient_wp_seq with "[$Hes1] [] [Hes2]").
    - done.
    - cbn.
      iIntros (w f) "Hw Hf _".
      destruct w.
      + cbn.
        unfold v_to_e_list, to_e_list.
        change @seq.map with @map.
        setoid_rewrite map_app.
        setoid_rewrite map_comp.
        iDestruct "Hw" as "[Hrun HΦ1]".
        iApply ("Hes2" with "[$] [$] [$]").
      + simpl iris.of_val.
        change [AI_trap] with ([] ++ [AI_trap]).
        rewrite <- app_assoc.
        iApply (lwp_trap with "[] [] [$Hf]"); auto.
      + rewrite of_val_br_app_r.
        iApply lenient_wp_value; first done.
        iDestruct "Hw" as "[Hrun Hbr]".
        iExists f; iFrame.
        cbn.
        unfold cwp_post_br.
        rewrite get_base_l_append.
        unfold vh_depth.
        by rewrite <- append_lh_depth.
      + rewrite of_val_ret_app_r.
        iApply lenient_wp_value; first done.
        iDestruct "Hw" as "[Hrun Hret]".
        iExists f; iFrame.
        cbn.
        destruct R; [|done].
        destruct r as [Pre Post].
        unfold cwp_post_ret.
        by rewrite simple_get_base_l_append.
      + cbn.
        iDestruct "Hw" as "[? ?]".
        done.
  Qed.

  Lemma cwp_weak_take_labels s E es n L R Φ :
    CWP es @ s; E UNDER take n L; R {{ Φ }} -∗
    CWP es @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros "Hwp".
    iApply (lwp_wand with "Hwp").
    iIntros (lv) "HΦ".
    destruct lv; try done.
    iDestruct "HΦ" as "(%f & Hfr & _ & Hrun & HΦ)".
    unfold cwp_post_lp, denote_logpred, lp_fr_inv, lp_noframe, lp_br, cwp_post_br.
    iFrame.
    destruct (take n L !! _) eqn:Htake; last done.
    destruct p as [n' P].
    iDestruct "HΦ" as "(%vs0 & %vs' & %Hbase & %Hlen & HP)".
    apply lookup_take_Some in Htake as [HLi Hn].
    rewrite HLi.
    iFrame.
    by iExists vs0.
  Qed.

  Lemma cwp_weak_no_return s E es L R Φ :
    CWP es @ s; E UNDER L; None {{ Φ }} -∗
    CWP es @ s; E UNDER L; R {{ Φ }}.
  Proof.
    iIntros "Hes".
    iApply (lwp_wand with "Hes").
    iIntros (lv) "HΦ".
    destruct lv; try done.
    by iDestruct "HΦ" as "(%f & Hf & _ & Hrun & HΦ)".
  Qed.

End structural.
