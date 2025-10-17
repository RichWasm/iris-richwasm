Require Import RecordUpdate.RecordUpdate.

From iris.proofmode Require Import base tactics classes.

From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import prelude codegen instruction module.
From RichWasm.iris Require Import autowp memory util wp_codegen.
From RichWasm.iris.language Require Import lenient_wp lwp_pure lwp_structural logpred.
From RichWasm.iris.logrel Require Import relations fundamental_kinding.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Fundamental.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  (* This should be moved to the logpred module. *)
  Definition lp_wand' Φ1 Φ2 : iProp Σ :=
    ∀ lv, denote_logpred Φ1 lv -∗ denote_logpred Φ2 lv.

  (* This should be moved to the lwp_structural module. *)
  Lemma lwp_wand s E es Φ Ψ :
    ⊢ lp_wand' Φ Ψ -∗
      lenient_wp s E es Φ -∗
      lenient_wp s E es Ψ.
  Proof.
    unfold lp_wand', lenient_wp.
    iIntros "Hwand HΦ".
    iApply (wp_wand with "[$] [$]").
  Qed.

  Lemma compat_nop M F L wl wl' wlf es' :
    let fe := fe_of_context F in
    let ψ := InstrT [] [] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (INop ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Proof.
    (* This is currently following the compat_copy lemma very closely *)
    intros fe ψ Hok Hcompile.
    inv_cg_emit Hcompile; subst.
    rewrite app_nil_l.
    unfold have_instruction_type_sem.
    destruct ψ eqn:Hψ.
    inversion Hψ; subst l l0.
    iIntros (? ? ? ? ? ?) "Henv Hinst Hlf".
    iIntros (? ?) "Hvs Hframe Hframeinv Hfr Hrun".
    unfold expr_interp.
    iDestruct "Hvs" as "(%vss & %Hconcat & Hvs)".
    iPoseProof (big_sepL2_length with "[$Hvs]") as "%Hlens".
    destruct vss, vs; cbn in Hconcat, Hlens; try congruence.
    iApply (lenient_wp_nop with "[$] [$] [Hframe] [Hframeinv]").
    - done.
    - done.
    - cbn. 
      iFrame.
      iExists [].
      iSplit; done.
  Qed.

  Lemma compat_unreachable M F L L' wl wl' wlf ψ es' :
    let fe := fe_of_context F in
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (IUnreachable ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L'.
  Admitted.

  Lemma eval_rep_subst_eq ρ ιs s__rep :
    eval_rep ρ = Some ιs ->
    subst_representation s__rep ρ = ρ.
  Proof.
  Admitted.

  Lemma compat_copy M F L wl wl' wlf τ es' :
    let fe := fe_of_context F in
    let ψ := InstrT [τ] [τ; τ] in
    has_copyability F τ ExCopy ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ICopy ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Proof.
    intros fe ψ Hcopy Hok Hcompile.
    unfold compile_instr in Hcompile.
    inv_cg_bind Hcompile ρ wl1 wl1' es_nil es1 Htype_rep Hcompile.
    inv_cg_bind Hcompile ιs wl2 wl2' es_nil' es2 Heval_rep Hcompile.
    unfold have_instruction_type_sem.
    destruct ψ eqn:Hψ.
    inversion Hψ; subst l l0.
    iIntros (? ? ? ? ? ?) "%Henv #Hinst #Hlh".
    iIntros (fr vs) "Hvs Hframe Hfrinv Hfr Hrun".
    unfold expr_interp.
    cbn.
    inv_cg_try_option Htype_rep.
    inv_cg_try_option Heval_rep.
    rewrite app_nil_l.
    inversion Hcopy as [F' τ' ρ' χ ? Hhas_kind HF' Hτ' Hχ].
    subst F' τ'.
    pose proof (kinding_sound rti sr mr F s__mem s__rep s__size se _ _ Hhas_kind) as Hhas_kind_sem.
    pose proof (Hhas_kind_sem Henv) as Hskind.
    destruct Hskind as [Hrefine Hcopyable].
    cbn in Hcopyable.
    assert (ρ' = ρ).
    {
      apply type_rep_has_kind_agree in Hhas_kind.
      rewrite Heq_some in Hhas_kind.
      congruence.
    }
    subst ρ'.
    iDestruct "Hvs" as "(%vss & %Hconcat & Hvs)".
    iPoseProof (big_sepL2_length with "[$Hvs]") as "%Hlens".
    destruct vss as [|vs' [|vs'' vss]]; cbn in Hlens, Hconcat; try congruence.
    rewrite app_nil_r in Hconcat; subst vs'.
    rewrite big_sepL2_singleton.
    iApply (lwp_wand with "[Hframe]"); last first.
    - erewrite eval_rep_subst_eq in Hcopyable; eauto.
      rewrite Heq_some0 in Hcopyable.
      iApply (Hcopyable with "[] [] [] [] [] [$Hfr] [$Hrun] [$Hvs]").
      + unfold is_copy_operation.
        iPureIntro.
        eexists.
        split.
        * by setoid_rewrite Hcompile.
        * by rewrite app_nil_l.
      + admit.
      + admit.
      + admit.
      + admit.
    - admit.
  Admitted.

  Lemma compat_drop M F L wl wl' wlf τ es' :
    let fe := fe_of_context F in
    let ψ := InstrT [τ] [] in
    has_dropability F τ ExDrop ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IDrop ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Admitted.

  Lemma compat_num M F L wl wl' wlf ψ e es' :
    let fe := fe_of_context F in
    has_instruction_type_num e ψ ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (INum ψ e)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Admitted.

  Lemma compat_num_const M F L wl wl' wlf n ν es' :
    let fe := fe_of_context F in
    let ψ := InstrT [] [num_type_type ν] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (INumConst ψ n)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Proof.
    intros fe ψ Hok Hcompile. cbn in Hcompile.
    (* Immediately, we must destruct ν *)
    destruct ν; cbn in Hcompile; inversion Hcompile.
    (* From here on out, we have an integer case and a float case (until we split
       further into 32/64 *)

    (* Some basic intros, unfolds, proving empty lists empty *)
    all: unfold have_instruction_type_sem;
      iIntros (? ? ? ? ? ?) "Henv Hinst Hlh";
      iIntros (fr vs) "Hvs Hframe Hfrinv Hfr Hrun";
      unfold expr_interp; cbn;
      iDestruct "Hvs" as "(%vss & %Hconcat & Hvs)";
      iPoseProof (big_sepL2_length with "[$Hvs]") as "%Hlens";
      destruct vss, vs; cbn in Hconcat, Hlens; try congruence; cbn;
      clear Hconcat Hlens.
    (* Now it's time to actually apply lenient_wp *)
    all: iApply lenient_wp_value.
    (* In int case, instantiate value with int value. Float in float case *)
    (* Automatics don't work great here *)
    1: by instantiate (1 := (immV [(value_of_Z (translate_num_type (IntT i)) n)])%I).
    2: by instantiate (1 := (immV [(value_of_Z (translate_num_type (FloatT f)) n)])%I).

    all: unfold denote_logpred; iFrame.
    (* iExists _ doesn't work great here *)
    1: iExists [[value_of_Z (translate_num_type (IntT i)) n]].
    2: iExists [[value_of_Z (translate_num_type (FloatT f)) n]].
    all: cbn; iFrame; iSplitR; try (by iPureIntro).

    (* Now, all we need to do is to prove value_interps! *)
    (* Dig into fixpoint one step *)
    all: iApply value_interp_eq; cbn.
    (* Get the obvious kind, then the rest is proving kind interp is right *)
    all: iExists _.
    all: iSplitR; try auto; iSplitL; try auto; cbn.
    all: iPureIntro.
    all: apply Forall2_cons_iff.
    all: split; try (by apply Forall2_nil).
    (* Finally, we have to destruct i and f to get the 32/64 info! *)
    1: destruct i.
    3: destruct f.
    all: eexists; done.
  Qed.

  Lemma compat_block M F L L' wl wl' wlf τs1 τs2 es es' :
    let fe := fe_of_context F in
    let F' := F <| fc_labels ::= cons (τs2, L') |> in
    let ψ := InstrT τs1 τs2 in
    has_instruction_type_ok F ψ L' ->
    (forall wl wl' wlf es',
        let fe' := fe_of_context F' in
        run_codegen (compile_instrs mr fe' es) wl = inr ((), wl', es') ->
        ⊢ have_instruction_type_sem rti sr mr M F' L (wl ++ wl' ++ wlf) (to_e_list es') ψ L') ->
    run_codegen (compile_instr mr fe (IBlock ψ L' es)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L'.
  Admitted.


  Lemma compat_loop M F L wl wl' wlf es es' τs1 τs2 :
    let fe := fe_of_context F in
    let F' := F <| fc_labels ::= cons (τs1, L) |> in
    let ψ := InstrT τs1 τs2 in
    has_instruction_type_ok F ψ L ->
    (forall wl wl' wlf es',
        let fe' := fe_of_context F' in
        run_codegen (compile_instrs mr fe' es) wl = inr ((), wl', es') ->
        ⊢ have_instruction_type_sem rti sr mr M F' L (wl ++ wl' ++ wlf) (to_e_list es') ψ L) ->
    run_codegen (compile_instr mr fe (ILoop ψ es)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Admitted.

  Fixpoint replace_base {n} (vh: valid_holed n) vs :=
    match vh with
    | VH_base n _ es => VH_base n vs es
    | VH_rec n b c d vh e => VH_rec b c d (replace_base vh vs) e
    end.

  Lemma lfilled_get_replace_base {n} (vh: valid_holed n) es vs1 vs2:
    get_base_l vh = vs1 ++ vs2 ->
    lh_depth (lh_of_vh vh) = n ->
    is_true (lfilled n (lh_of_vh (replace_base vh vs1))
               (seq.cat (v_to_e_list vs2) es) (vfill vh es)).
  Proof.
    induction vh => //=.
    - intros -> <-.
      unfold lfilled, lfill => //=.
      rewrite v_to_e_is_const_list /=.
      rewrite -v_to_e_cat.
      repeat rewrite cat_app.
      repeat rewrite app_assoc.
      done.
    - intros Hbase Hdepth.
      apply eq_add_S in Hdepth.
      specialize (IHvh Hbase Hdepth).
      unfold lfilled, lfill; fold lfill.
      rewrite v_to_e_is_const_list.
      unfold lfilled in IHvh.
      destruct (lfill _ _ _) => //.
      apply b2p in IHvh as <-.
      done.
  Qed. 

  Lemma translate_types_app ks t1s t2s res :
    translate_types ks (t1s ++ t2s) = Some res ->
    exists res1 res2, translate_types ks t1s = Some res1 /\
                   translate_types ks t2s = Some res2 /\
                   res = res1 ++ res2.
  Proof.
    generalize dependent res. 
    induction t1s => //=.
    - intros res Htrans. exists [], res. done.
    - intros res Htrans.
      unfold translate_types in Htrans.
      simpl in Htrans.
      destruct (translate_type ks a) eqn:Ha; simpl in Htrans => //. 
      destruct (mapM (translate_type ks) (t1s ++ t2s)) eqn:Htrans';
        simpl in Htrans => //. 
      inversion Htrans; subst res.
      edestruct IHt1s as (res1 & res2 & Htrans1 & Htrans2 & Hres).
      + unfold translate_types.
        rewrite Htrans'.
        simpl. done.
      + exists (l ++ res1), res2.
        repeat split => //=.
        * rewrite /translate_types /=.
          unfold translate_types in Htrans1.
          destruct (mapM (translate_type ks) t1s) eqn:Htrans1' => //. 
          rewrite Ha /=.
          simpl in Htrans1. inversion Htrans1; subst res1 => //.
        * rewrite Hres app_assoc //.
  Qed.

(*  Lemma translate_subst ks a ts smem srep ssize st:
    translate_type ks a = Some ts ->
    exists ts', translate_type ks (subst_type smem srep ssize st a) = Some ts' /\
             length ts = length ts'.
  Proof.
    unfold translate_type.
    destruct (type_rep ks a) eqn:Ha => //=. 
    destruct a => //=.
    - 
  
  Lemma eval_rep_subst_length srep r :
    length (eval_rep r) = length (eval_rep (subst_representation srep r)). 


  Lemma value_interp_length ts se F smem srep ssize a vs :
    translate_type (fc_type_vars F) a = Some ts ->
    (subst_env_interp sr F smem srep ssize se ∗
       value_interp sr mr se (subst_type smem srep ssize VarT a) (SValues vs)
       ⊢ ⌜ length vs = length ts ⌝)%I.
  Proof.
    iIntros (Ha) "[Hse Ha]".
    unfold subst_env_interp.
    iDestruct "Hse" as "(%Hse & Hse)".
    unfold sem_env_interp. 
    iDestruct (value_interp_eq with "Ha") as "Ha".
    unfold value_interp0.
    simpl.
    unfold translate_type in Ha.
    unfold type_rep in Ha.
    unfold type_kind in Ha.
    iDestruct "Ha" as (κ) "(%Hkind & Hkind & Ha)".
    destruct a => //=.
    - destruct (fc_type_vars F !! n) eqn:Hksn; last done.
      simpl in Ha.
      unfold kind_rep in Ha.
      destruct k => //=.
      simpl in Ha.
      simpl in Hkind.
      unfold type_var_interp.
      rewrite -nth_error_lookup in Hkind.
      rewrite nth_error_map in Hkind.
      destruct (nth_error se n) eqn:Hsen; last by rewrite Hsen in Hkind.
      destruct o. rewrite Hsen /= in Hkind.
      inversion Hkind; subst o; clear Hkind.
      erewrite nth_error_nth.
      2:{ rewrite nth_error_map. rewrite Hsen. done. }
      rewrite nth_error_lookup in Hsen.
      iDestruct (big_sepL2_lookup _ _ _ _ _ _ Hsen Hksn with "Hse") as "[%Heq _]".
      simpl in Heq; subst κ. 
      simpl.
      iDestruct "Hkind" as "%Hkind".
      destruct Hkind as (vs0 & Heq & Hrepr).
      inversion Heq; subst vs0; clear Heq.
      unfold representation_interp0 in Hrepr.
      destruct Hrepr as (ιs & Hιs & Hιvs).
      unfold translate_rep in Ha.
      iPureIntro.
      apply Forall2_length in Hιvs.
      rewrite -Hιvs.
      destruct (eval_rep r) eqn:Hr; last done.
      simpl in Ha.
      inversion Ha; subst ts.
      rewrite length_map.

      
      Check eval_rep.
      
      
      unfold subst_representation in Hιs. 

      unfold nth. 
      iClear "Hkind".  clear. 
      
      
      Set Printing All. 
      rewrite map_nth. 
      simpl in H
      Search (nth_error (map _ _) _).
      Search (map _ _ !! _).
      
    all: destruct (ks !! n) eqn:Hksn; last done.
    all: simpl in Ha.
    all: simpl in Hkind.
    all: inversion Hkind; subst κ; clear Hkind.
    all: unfold kind_as_type_interp.
    all: destruct k => //=.
    all: simpl in Ha.
    all: iDestruct "Hkind" as %Hkind.
    all: destruct Hkind as (vs' & Hvs & Hrep).
    all: inversion Hvs; subst vs'; clear Hvs.
    - iPureIntro.
      destruct r => //=.
      all: rewrite /translate_rep /= in Ha.
      all: simpl in Hrep.
      + induction l.
        * simpl in Hrep, Ha.
          inversion Ha; subst ts => //=.
          unfold representation_interp0 in Hrep.
          destruct Hrep as (ιs & Hιs & Hl1).
          simpl in Hιs.
          inversion Hιs; subst ιs.
          inversion Hl1; subst.
          inversion H3; subst. done.
        * simpl in Ha.
          destruct (eval_rep a) eqn:Ha'; last done.
          simpl in Ha.
          destruct (mapM eval_rep l) eqn:Hl; last done.
          simpl in Ha.
          inversion Ha; subst ts; clear Ha.
          simpl in IHl.
          unfold representation_interp0 in Hrep.
          destruct Hrep as (ιs & Hιs & Hvs).
          simpl in Hιs.
          destruct (eval_rep (subst_representation srep a)) eqn:Ha''; last done.
          simpl in Hιs.
          destruct (mapM eval_rep (map (subst_representation srep) l)) eqn:Hl'; last done.
          simpl in Hιs.
          inversion Hιs; subst ιs.
          unfold representation_interp0 in IHl.
          simpl in IHl.
          rewrite Hl' /= in IHl.
          apply IHl.
          -- eexists. split; first done.
             
       *)   

      
  
  Lemma translate_types_length_subst ks ts res vs se smem srep ssize :
    translate_types ks ts = Some res ->
    (([∗ list] y1;y2 ∈ map (subst_type smem srep ssize VarT) ts;vs, 
       value_interp rti sr se y1 (SValues y2))
       ⊢ ⌜ length res = list_sum (map length vs) ⌝)%I.
  Proof.
  Admitted. 
(*    generalize dependent vs. generalize dependent res. 
    induction ts; iIntros (res vs Hres) "H".
    { destruct vs; last done.
      rewrite /translate_types /= in Hres.
      inversion Hres; subst; done. }
    rewrite /translate_types /= in Hres.
    destruct (translate_type ks a) eqn:Ha; last done.
    destruct (mapM (translate_type ks) ts) eqn:Htrans; last done.
    simpl in Hres.
    inversion Hres; subst res; clear Hres.
    destruct vs; first done.
    iDestruct "H" as "[Ha H]".
    iDestruct (IHts with "H") as "%IH".
    { rewrite /translate_types Htrans //. }
    iClear "H".
 *)

  Lemma translate_types_length ks ts res vs se:
    translate_types ks ts = Some res ->
    (([∗ list] y1;y2 ∈ ts;vs, 
       value_interp rti sr se y1 (SValues y2))
       ⊢ ⌜ length res = list_sum (map length vs) ⌝)%I.
  Proof.
    iIntros (H) "H".
    iApply (translate_types_length_subst _ _ _ _ _ _ _ _ H).
    instantiate (1 := VarS).
    instantiate (1 := VarR).
    instantiate (1 := VarM).
    replace (map (subst_type VarM VarR VarS VarT) ts) with ts; first done.
    clear. induction ts => //=.
    rewrite instId'_type -IHts //. 
  Qed.
  
  Lemma length_lholeds_bef_aft se l lh bef aft:
    length_lholeds rti sr se l lh <->
      length_lholeds rti sr se l (lh_bef_aft bef lh aft).
  Proof.
    induction lh => //=.
    { destruct l => //=. }
    destruct l => //=.
  Qed. 
  
  Lemma length_lholeds_app se l1 l2 lh1 lh2:
    length_lholeds rti sr se l1 lh1 ->
    length_lholeds rti sr se l2 lh2 ->
    length_lholeds rti sr se (l1 ++ l2) (lh_plug lh2 lh1).
  Proof.
    generalize dependent l1.
    induction lh1 => //=.
    - destruct l1 ; last by destruct p.
      intros _ H.
      apply length_lholeds_bef_aft => //. 
    - destruct l3 => //=.
      destruct p.
      intros [Hn Hlh1] Hlh2.
      split; last by apply IHlh1.
      exact Hn.
  Qed. 

    Lemma lholed_valid_plug lh1 lh2:
    lholed_valid lh1 -> lholed_valid lh2 -> lholed_valid (lh_plug lh2 lh1).
  Proof.
    induction lh1; first destruct lh2 => //=.
    - intros ??; by apply const_list_concat.
    - intros ? [??]. split => //. 
      by apply const_list_concat.
    - intros [??] ?. split => //.
      apply IHlh1 => //.
  Qed.

      
  Lemma to_val_v_to_e vs :
    to_val (v_to_e_list vs) = Some (immV vs).
  Proof.
    induction vs => //=.
    unfold to_val.
    unfold RichWasm.iris.language.iris.iris.to_val.
    rewrite (separate1 (AI_basic _)).
    rewrite map_app.
    rewrite -cat_app.
    rewrite merge_app.
    unfold to_val, RichWasm.iris.language.iris.iris.to_val in IHvs.
    destruct (merge_values_list _) eqn:Hvs => //.
    inversion IHvs; subst v.
    simpl. done.
  Qed. 

    Fixpoint pull_base_l_drop_len {i : nat} (vh : valid_holed i) (len : nat) :=
  match vh with
  | VH_base j vs es => (VH_base j (take len vs) es, drop len vs)
  | @VH_rec j vs m es' lh' es => let '(lh'',l1) := pull_base_l_drop_len lh' len in
                             (@VH_rec j vs m es' lh'' es,l1)
  end.

  Lemma vfill_pull_base_l_take_len {i : nat} (vh : valid_holed i) (len : nat) es vh' vs :
    pull_base_l_drop_len vh len = (vh', vs) ->
    vfill vh es = vfill vh' (((λ x : value, AI_basic (BI_const x)) <$> vs) ++ es).
  Proof.
    intros Heq.
    induction vh.
    { simpl in *. simplify_eq. simpl.
      rewrite -!app_assoc. repeat rewrite v_to_e_is_fmap. rewrite fmap_take fmap_drop.
      rewrite (app_assoc (take _ _)).
      rewrite (take_drop len ((λ x : value, AI_basic (BI_const x)) <$> l)). auto. }
    { simpl in *.
      destruct (pull_base_l_drop_len vh len) eqn:Heq'.
      simplify_eq. simpl. f_equiv. f_equiv.
      erewrite IHvh;eauto. 
    }
  Qed.

  
  Lemma lh_depth_pull_base_l_take_len {i : nat} (vh : valid_holed i) (len : nat) vh' vs :
    pull_base_l_drop_len vh len = (vh', vs) ->
    lh_depth (lh_of_vh vh) = lh_depth (lh_of_vh vh').
  Proof.
    intros Heq.
    induction vh;simpl in *;simplify_eq;auto.
    destruct (pull_base_l_drop_len vh len) eqn:Heq'.
    simplify_eq. simpl. erewrite IHvh;eauto.
  Qed.
   Lemma length_pull_base_l_take_len {i : nat} (vh : valid_holed i) (len : nat) vh' vs vs' :
    get_base_l vh = vs' ->
    pull_base_l_drop_len vh len = (vh', vs) ->
    length vs = length vs' - len.
  Proof.
    intros Hbase Hpull.
    induction vh;simpl in *;simplify_eq.
    { rewrite length_drop. auto. }
    { destruct (pull_base_l_drop_len vh len) eqn:Heq'.
      simplify_eq. simpl. erewrite IHvh;eauto. }
  Qed.

  
  Lemma compat_ite M F L L' wl wl' wlf es1 es2 es' τs1 τs2 :
    let fe := fe_of_context F in
    let F' := F <| fc_labels ::= cons (τs2, L') |> in
    let ψ := InstrT (τs1 ++ [type_i32]) τs2 in
    has_instruction_type_ok F ψ L' ->
    (forall wl wl' wlf es',
        let fe := fe_of_context F' in
        run_codegen (compile_instrs mr fe es1) wl = inr ((), wl', es') ->
        ⊢ have_instruction_type_sem rti sr mr M F' L (wl ++ wl' ++ wlf) (to_e_list es') (InstrT τs1 τs2) L') ->
    (forall wl wl' wlf es',
        let fe := fe_of_context F' in
        run_codegen (compile_instrs mr fe es2) wl = inr ((), wl', es') ->
        ⊢ have_instruction_type_sem rti sr mr M F' L (wl ++ wl' ++ wlf) (to_e_list es') (InstrT τs1 τs2) L') ->
    run_codegen (compile_instr mr fe (IIte ψ L' es1 es2)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L'.
  Proof.
    intros fe F' ψ Hok Hthen Helse Hcodegen.
    iIntros (smem srep ssize se inst lh) "%Hsubst #Hinst #Hctxt".
    iIntros (fr vs) "Hvss Hvsl Hfrinv Hfr Hrun".
    iDestruct "Hvss" as (vss) "(-> & Hvss)".
    iDestruct "Hvsl" as (vsl' vswl') "(-> & Hlocs)".
    iDestruct "Hfrinv" as (vsl vswl) "(-> & %Hlocs & %Hrestype & Htok)".
    rewrite map_app.
    iDestruct (big_sepL2_app_inv_l with "Hvss") as (vss1 vssi32) "(-> & Hvss1 & Hvssi32)".
    destruct vssi32; first done.
    iDestruct "Hvssi32" as "[Hvssi32 Hvoid]".
    destruct vssi32; last done.
    iClear "Hvoid".
    iDestruct (value_interp_eq with "Hvssi32") as "Hvssi32".
    iSimpl in "Hvssi32".
    iDestruct "Hvssi32" as (κ) "(%Heq & Hκ & _)".
    inversion Heq; subst κ; clear Heq.
    iSimpl in "Hκ".
    iDestruct "Hκ" as "%Hκ".

(*    destruct vswl; last by inversion Hrestype. *)
    destruct o as [|v vs]; inversion Hκ; subst; clear Hκ. 
    destruct vs as [|v' vs]; inversion H4; subst; clear H4.
    unfold primitive_rep_interp in H2.
    destruct H2 as [n ->].

(*    inversion Hok; subst.
    destruct H as [Hτs1 Hτs2].
    apply Forall_app in Hτs1 as [Hτs1 Hi32].
    inversion Hi32; subst.
    inversion H2; subst.
    inversion H; subst.
    inversion H4; subst. *)
    


    replace (compile_instr mr fe (IIte ψ L' es1 es2))
      with (compile_ite fe ψ (compile_instrs mr fe es1) (compile_instrs mr fe es2))
      in Hcodegen; last done.
    remember (compile_instrs mr fe es1) as compes1.
    remember (compile_instrs mr fe es2) as compes2.
    Opaque if_c. 
    simpl in Hcodegen. 


    inv_cg_bind Hcodegen ρ1 wl1 wl1' es_nil es1' Htype_rep Hcodegen.
    inv_cg_try_option Htype_rep.
    subst wl1 es_nil.
    rewrite app_nil_l in Hes_app_eq; subst es1'. 
    inv_cg_bind Hcodegen ρ2 wl2 wl2' es_nil es1' Htype_rep Hcodegen.
    inv_cg_try_option Htype_rep.
    subst wl2 es_nil.
    rewrite app_nil_l in Hes_app_eq; subst es1'. 

    inv_cg_bind Hcodegen ρ3 wl3 wl3' es_nil es1' Hcodegen Hend.
    rewrite /run_codegen /= in Hend.
    inversion Hend; subst wl3' es1'; clear Hend.
    rewrite app_nil_r in Hes_app_eq; subst es_nil.
    destruct ρ3.
    destruct u, u0. 
    
    Transparent if_c.
    rewrite /if_c in Hcodegen.
    subst wl1' wl' wl2'.
    rewrite !app_nil_r !app_nil_l.

    inv_cg_bind Hcodegen ρ3 wl1 wl1' es_nil es1' Hes1 Hcodegen.
    destruct ρ3. destruct u.
    subst es'.
    inv_cg_bind Hcodegen ρ3 wl2 wl2' es_nil' es2' Hes2 Hcodegen.
    destruct ρ3. destruct u.
    subst es1'.
    rewrite /run_codegen /= in Hcodegen.
    inversion Hcodegen; subst wl1' wl2' es2'; clear Hcodegen.
    apply run_codegen_capture in Hes1 as [Hes1 ->].
    apply run_codegen_capture in Hes2 as [Hes2 ->].

(*    unfold compile_instrs in Hthen.
    destruct u, u0. *)
    subst compes1 compes2.
    rewrite !app_nil_r in Hes1.
    rewrite !app_nil_r in Hes2.
    apply (Hthen _ _ (wl2 ++ wlf)) in Hes1; eauto.
    apply (Helse _ _ wlf) in Hes2; eauto.
    rewrite <- !app_assoc in Hes2.

    rewrite removelast_last in Heq_some.

    iDestruct (big_sepL2_length with "Hvss1") as "%Hlen1".
    (* iDestruct (big_sepL2_length with "Hvss0") as "%Hlen0". *)
    rewrite length_map in Hlen1.
(*    rewrite length_map in Hlen0. *)
    iDestruct (translate_types_length_subst _ _ _ _ _ _ _ _ Heq_some with "Hvss1") as "%Hlen1'".
    
    
    iSimpl.
    subst wl3.
    rewrite -> !app_nil_r in *.
    rewrite -> !app_nil_l in *.
    unfold lenient_wp.
    rewrite concat_app.
    rewrite -v_to_e_cat.
    rewrite cat_app -app_assoc.
    iSimpl.
    iApply wp_wasm_empty_ctx.
    rewrite <- (app_assoc _ [AI_basic _]).
    cbn.
    rewrite (separate2 (AI_basic _)).
    iApply wp_base_push; first by apply v_to_e_is_const_list.
    destruct (value_eq_dec (VAL_int32 n) (VAL_int32 (Wasm_int.int_zero i32m))).
    - (* n is false *)
      inversion e; subst.
      iApply (wp_if_false_ctx with "Hfr Hrun") => //.
      iIntros "!> Hfr Hrun".
      iApply wp_base_pull.
      iSimpl.
      iApply wp_wasm_empty_ctx.
      iApply (wp_block with "Hfr Hrun") => //.
      { apply v_to_e_is_const_list. }
      { rewrite v_to_e_length.
        rewrite length_concat.
        done. }
      iIntros "!> Hfr Hrun".
      iApply (wp_label_bind with "[-]").
      2:{ iPureIntro. instantiate (5 := []).
          rewrite /lfilled /lfill /= app_nil_r //. }
      iApply (wp_wand with "[-]").
      + iApply (Hes2 with "[%] Hinst [Hctxt] [$Hvss1] [Hlocs] [$Htok] Hfr Hrun"); first assumption; cycle 1.
        * done.
        * admit.
          (* iExists _,_. iSplit; first done.
          iSimpl. Search vsl. unfold locals_inv_interp in Hlocs.  *)
        * iExists _, _. iSplit; first done.
          iSplit; first done.
          iPureIntro. rewrite app_assoc app_assoc -(app_assoc wl) -app_assoc.
          exact Hrestype. 
        * instantiate (1 := (* push_base lh (length ρ2) [] [] []). *)
                         lh_plug (LH_rec _ _ _ (LH_base _ _) _) lh).  
          iDestruct "Hctxt" as "(%Hbase & %Hlength & %Hvalid & Hconts)".
          repeat iSplitR.
          all: try iPureIntro.
          -- apply base_is_empty_plug => //.
          -- eapply length_lholeds_app => //.
             split => //. 
             iIntros (?) "(%vss & -> & Hvss)".
             iDestruct (translate_types_length with "Hvss") as "%H".
             ++ exact Heq_some0.
             ++ rewrite length_concat -H. done. 
          -- apply lholed_valid_plug => //=.
             split => //. 
             apply v_to_e_is_const_list.
          -- iSimpl. iSplitR; last first. 
             ++ iApply (big_sepL_impl with "Hconts").
                iIntros "!>" (k [ts ctx] Hk) "#Hcont".
                unfold continuation_interp.
                iDestruct "Hcont" as (j es0 es es' lh' lh'') "(%Hlayer & %Hdepth & %Hminus & #Hcont)".
                iExists _,_,_,_,_,_.
                repeat iSplitR.
                1-3: iPureIntro.
                ** rewrite lh_depth_plug. simpl.
                   replace (lh_depth lh + 1 - S (S k)) with (lh_depth lh - S k); last lia.
                   apply get_layer_plug_shallow.
                   exact Hlayer. 
                ** rewrite lh_depth_plug. simpl.
                   replace (lh_depth lh + 1 - S (S k)) with
                     (lh_depth lh - S k); first exact Hdepth.
                   lia. 
                ** apply lh_minus_plug. done.
                ** iIntros "!>" (vs fr) "Hvs Hfr Hrun Hframe Hframe'".
                   iDestruct ("Hcont" with "Hvs Hfr Hrun Hframe Hframe'") as (τs') "Hexp".
                   iExists τs'.
                   done.

             ++ iExists _, _, _, _,_, _.
               iSplit.
               { iPureIntro.
                 rewrite lh_depth_plug /= Nat.add_sub.
                 apply get_layer_plug_precise => //. } 
               iSplit; first iSimpl.
               { (* instantiate (5 := lh). *)
                 rewrite lh_depth_plug /= Nat.add_sub //. }
               iSplit.
               { iPureIntro. 
                 erewrite lh_plug_minus => //. }
               iIntros "!>" (vs fr) "Hvs Hfr Hrun Hframe Hframe'".
               iExists _.
               unfold expr_interp.
               iSimpl.
               unfold lenient_wp.
               do 3 instantiate (2 := []).
               rewrite app_nil_r app_nil_r /=.

               iApply wp_value.
               { apply of_to_val. unfold language.to_val.
                 simpl. apply to_val_v_to_e. } 
               rewrite /denote_logpred /=.
               iFrame.
(*             iApply (big_sepL_impl with "Hconts").
             iIntros "!>" (k [ts ctx] Hk) "#Hcont".
             unfold continuation_interp.
             iDestruct "Hcont" as (j es0 es es' lh' lh'') "(%Hlayer & %Hdepth & %Hminus & #Hcont)".
             iExists _,_,_,_,_,_.
             repeat iSplitR.
             1-3: iPureIntro.
             ++ rewrite lh_depth_plug. simpl.
                replace (lh_depth lh + 1 - S (S k)) with (lh_depth lh - S k); last lia.
                apply get_layer_plug_shallow.
                exact Hlayer. 
             ++ rewrite lh_depth_plug. simpl.
                replace (lh_depth lh + 1 - S (S k)) with
                  (lh_depth lh - S k); first exact Hdepth.
                lia. 
             ++ apply lh_minus_plug. done.
             ++ iIntros "!>" (vs fr) "Hvs Hfr Hframe".
                iDestruct ("Hcont" with "Hvs Hfr Hframe") as (τs') "Hexp".
                iExists τs'.
                done.
        * done.
        * iExists _, _. iSplit; first done. iSplit; first done.
          rewrite <- !app_assoc in Hrestype.
          iPureIntro. exact Hrestype. *)

      + iIntros (v) "H".
        rewrite /denote_logpred /lp_noframe /=.
        iIntros (LI HLI).
        apply lfilled_Ind_Equivalent in HLI; inversion HLI; subst.
        inversion H8; subst.
        clear HLI H7 H8 H1.
        iSimpl.

        destruct v.
        * (* immV case *)
          iDestruct "H" as "(%fr & Hfr & (%vssl & %vswl0 & -> & %Hlocs' & %Hrestype' & Htok) & (%vssl' & %vswl0' & %Heq & Hlocs) & Hrun & %vss & -> & Hvss)".
          inversion Heq.
          
(*          edestruct const_list_to_val as [vs Hvs]; first by apply v_to_e_is_const_list. *)
          iApply (wp_wand with "[Hfr Hrun]").
          { iApply (wp_label_value with "Hfr Hrun").
            - rewrite seq.cats0. rewrite to_of_val. done.
            - by instantiate (1 := λ v, ⌜ v = immV _ ⌝%I). }
          iIntros (v) "[[-> Hrun] Hfr]".
          iFrame.
          iSplit. 
          -- iExists _,_. iSplit; first done.
             admit. (* must show that the terms in H0 are equal *) 
          -- iSplit; last done. iExists _. done. (* iSplit; first done.
          by iFrame. *)   
        * (* trapV case *)
          iDestruct "H" as "(%fr & Hfr & (%vssl & %vswl0' & -> & % & % & Htok) & Hbail & _)".
          iApply (wp_wand with "[Hfr]").
          { iApply (wp_label_trap with "Hfr") => //.
            instantiate (1 := λ v, ⌜ v = trapV ⌝%I) => //. }
          iIntros (v) "[-> Hfr]".
          iFrame.
          iExists _,_. iSplit; first done. done. 
(*          by iFrame. *)
        * (* brV case *)
          iDestruct "H" as "(%fr & Hfr & (%vssl & %vswl0' & -> & %Hlocs' & %Hrestype' & Htok) & Hrun & Hbr)".
          iDestruct (br_interp_eq with "Hbr") as "Hbr".
          unfold br_interp0. iSimpl in "Hbr".
          iDestruct "Hbr" as (k p lh' lh'' τs es0 es es' vs0 vs) "(%Hgetbase & %Hdepth & %Hlabels & %Hlayer & %Hdepth' & %Hminus & (%vss2 & -> & Hvss2) & Hbr)".
          iDestruct (big_sepL2_length with "Hvss2") as "%Hlen2".
          (* iDestruct (translate_types_length with "Hvss2") as "%Hlen2'".
          ; first exact Heqtrans2. *)
          (* may need to first progress in wp before yielding frame *)
          iDestruct ("Hbr" with "Hfr [Hvss2] [$Htok]") as "Hbr".
          { iExists _,_. iSplit; first done. admit. } 
          { iExists _,_. iSplit; first done. done. } 
          unfold lenient_wp_ctx.
          (* iDestruct ("Hbr" with "[]") as "Hbr".
          { iPureIntro. 
            rewrite lh_depth_plug /=. *)

          (* Hmmmm this next part should work… *) 
(*          iDestruct wp_value_fupd as "[H _]"; 
            last iMod ("H" with "Hbr") as "Hbr".
          { unfold IntoVal. apply of_to_val.
            unfold language.to_val. simpl. 
            rewrite (separate1 (AI_basic _)).
            apply to_val_br_eq. }
          iClear "H".
          unfold denote_logpred.
          iSimpl in "Hbr".
          iDestruct "Hbr" as "(Hbr & %fr & Hfr & %vssl' & %vswl'' & -> & Hlocs & Hrestype' & Htok)". *)
          destruct (decide (i = p)).
          -- (* targetting this exact block *)
            subst p. 
            destruct (pull_base_l_drop_len lh0 (length (vs0 ++ concat vss2) - length ρ2)) eqn:Hpb.
            rewrite seq.cats0.
            unfold of_val. 
            erewrite vfill_pull_base_l_take_len.
            2:{ exact Hpb. }
            pose proof (vfill_to_lfilled v ((v_to_e_list l1) ++ [AI_basic (BI_br i)])) as [Hle Hfill].
            erewrite <- lh_depth_pull_base_l_take_len in Hfill;[|eauto]. 
            rewrite -e0 in Hfill.
            rewrite -e0 Nat.sub_diag /= in Hlabels.
            rewrite -e0 Nat.sub_diag. 
            inversion Hlabels; subst τs2; clear Hlabels. 
            iApply (wp_br with "[] Hrun").
            3: exact Hfill.
            ++ apply v_to_e_is_const_list. 
            ++ rewrite length_fmap.
               eapply length_pull_base_l_take_len in Hpb;[|eauto]. rewrite Hpb.
               assert (length (vs0 ++ concat vss2) >= length ρ2);[|lia].
               admit. 
(*               rewrite Hlen2. lia. } *)
            ++ admit.
            ++ iNext. iIntros "Hf Hrun".
               rewrite app_nil_r.
               iApply wp_value.
               { apply of_to_val. apply to_val_v_to_e. }
               iFrame.
               admit. 
(*          -- (* targetting this exact block *)
            rewrite lh_depth_plug /= Nat.add_sub in Hdepth' Hlayer.
            replace iris_lfilled_properties.get_layer with get_layer in Hlayer; last done
            erewrite get_layer_plug_precise in Hlayer.
            3: done.
            2:{ admit. }
            inversion Hlayer; subst; clear Hlayer.
            simpl in Hlabels.
            inversion Hlabels; subst; clear Hlabels. 
            assert (j = p) as ->.
            { 
            assert (i = p) as ->.
            { clear - Heqhop Hdepth.
              specialize (vfill_to_lfilled lh0 []) as [H _].
              rewrite Hdepth in H. lia. }
            assert (j = p) as ->.
            { admit. }
            rewrite Nat.sub_diag lh_depth_plug /= Nat.add_sub in Hdepth'.
            rewrite Nat.sub_diag /= in Hlabels.
            inversion Hlabels; subst τs; clear Hlabels. 
            iDestruct (translate_types_length with "Hvss2") as "%Hlen2'".
            { exact Heq_some0. }
            rewrite Nat.sub_diag in Hlayer.
            rewrite lh_depth_plug /= in Hlayer.
            rewrite Nat.add_sub in Hlayer.
            replace ( iris_lfilled_properties.get_layer
                        (lh_plug (LH_rec [] (length ρ2) [] (LH_base [] []) []) lh) 
                        (lh_depth lh))
              with ( get_layer
                       (lh_plug (LH_rec [] (length ρ2) [] (LH_base [] []) []) lh) 
                       (lh_depth lh)) in Hlayer; last done.
            erewrite get_layer_plug_precise in Hlayer => //.
            2:{ admit. }
            inversion Hlayer; subst. 

            iApply (wp_br with "[]").
            3:{ rewrite seq.cats0 /=. 
                instantiate (1 := p).
                instantiate (1 := v_to_e_list (concat vss2)).
                instantiate (1 := lh_of_vh (replace_base lh0 vs0)).
                clear - Hgetbase Hdepth.
                apply lfilled_get_replace_base => //. } 
            ++ apply v_to_e_is_const_list.
            ++ rewrite v_to_e_length length_concat //.
            ++ admit. (* def of br_interp? or my proof? *) 
            ++ admit. (* fix def of br_interp *) 
            ++ iIntros "!> Hf Hrun".
               edestruct const_list_to_val as [vs Hvs]; first by apply v_to_e_is_const_li
               iApply wp_value.
               { apply of_to_val. rewrite app_nil_r. exact Hvs. }
               iSimpl. iFrame.
               iSplitL "Hvss2".
               ** apply v_to_e_list_to_val in Hvs as Hvs'.
                  apply v_to_e_inj in Hvs' as ->.
                  iExists _. iSplit; first done.
                  admit. 
               ** iExists _,_. iSplit; first done.
                  admit. *)
          -- (* still blocked *)
            admit. 
(*            assert (i > p) as Hip; first lia.
            destruct i; first lia.
            destruct (vh_decrease lh0) eqn:Hlh0.
            2:{ exfalso. clear - Hip Hlh0 Hdepth.
                 admit. (* painstaking dep-type induction *) } 
            iApply wp_value.
            { apply of_to_val. rewrite seq.cats0 /=. 
              simpl.
              unfold RichWasm.iris.language.iris.iris.to_val.
              simpl.
              rewrite seq.cats0.
              specialize (to_of_val (brV lh0)) as H.
              simpl in H.
              unfold RichWasm.iris.language.iris.iris.to_val in H.
              destruct (merge_values_list _) ; try by exfalso.
              inversion H; subst v0; clear H.
              rewrite Hlh0. 
              done. } 
            iSimpl. iFrame.
            iSplitL "Hbr".
            ++ admit. (* massage the br_interp layers *) 
            ++ admit. (* iExists _,_. iSplit; first done.
               iFrame.   *) *)
        * iApply wp_value.
          { apply of_to_val.
            rewrite seq.cats0 /=.
            unfold RichWasm.iris.language.iris.iris.to_val.
            simpl.
            specialize (to_of_val (retV s)) as H.
            simpl in H.
            unfold RichWasm.iris.language.iris.iris.to_val in H.
            destruct (merge_values_list _); try by exfalso.
            inversion H; subst v; clear H.
            done. }
          iSimpl.
          iDestruct "H" as "(%fr & Hfr & (%vssl & %vswl0' & -> & % & % & Htok) & Hrun & %vs0 & %vs & %Hgetbase & (%vss & -> & Hvss) & Hret)".
          iFrame.
          iSplit.
          -- iExists _,_. iSplit; first done. done.
          -- iExists _,_. iSplit; first done. iSplit; first done.
             iIntros (fr fr') "Hf".
             admit. (* generalise s in IH? *)
        * iDestruct "H" as "(%fr & Hfr & _ & _ & ?)"; done.
    - (* n is true *)
      admit. 
  Admitted.

  Lemma compat_br M F L L' wl wl' wlf es' i τs1 τs τs2 :
    let fe := fe_of_context F in
    let ψ := InstrT (τs1 ++ τs) τs2 in
    F.(fc_labels) !! i = Some (τs, L) ->
    Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (IBr ψ i)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_return M F L L' wl wl' wlf es' τs1 τs τs2 :
    let fe := fe_of_context F in
    let ψ := InstrT (τs1 ++ τs) τs2 in
    F.(fc_return) = τs ->
    Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (IReturn ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_local_get M F L wl wl' wlf es' i τ :
    let fe := fe_of_context F in
    let ψ := InstrT [] [τ] in
    let L' := <[ i := None]> L in
    L !! i = Some (Some τ) ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ILocalGet ψ i)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_local_get_copy M F L wl wl' wlf es' i τ :
    let fe := fe_of_context F in
    let ψ := InstrT [] [τ] in
    L !! i = Some (Some τ) ->
    has_copyability F τ ImCopy ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ILocalGet ψ i)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Admitted.

  Lemma compat_local_set M F L wl wl' wlf es' i τ :
    let fe := fe_of_context F in
    let ψ := InstrT [τ] [] in
    let L' := <[ i := Some τ ]> L in
    (∀ τ0, L !! i = Some (Some τ0) → has_dropability F τ0 ImDrop) ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ILocalSet ψ i)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_coderef M F L wl wl' wlf es' i ϕ :
    let fe := fe_of_context F in
    let τ := CodeRefT (VALTYPE (PrimR I32R) ImCopy ImDrop) ϕ in
    let ψ := InstrT [] [τ] in
    M.(mc_table) !! i = Some ϕ ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ICodeRef ψ i)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Admitted.

  Lemma compat_inst M F L wl wl' wlf es' ix ϕ ϕ' :
    let fe := fe_of_context F in
    let κ := VALTYPE (PrimR I32R) ImCopy ImDrop in
    let ψ := InstrT [CodeRefT κ ϕ] [CodeRefT κ ϕ'] in
    function_type_inst F ix ϕ ϕ' ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IInst ψ ix)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Admitted.

  Lemma compat_call M F L wl wl' wlf es' i ixs ϕ τs1 τs2 :
    let fe := fe_of_context F in
    let ψ := InstrT τs1 τs2 in
    M.(mc_functions) !! i = Some ϕ ->
    function_type_insts F ixs ϕ (MonoFunT τs1 τs2) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ICall ψ i ixs)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Admitted.

  Lemma compat_call_indirect M F L wl wl' wlf es' τs1 τs2 :
    let fe := fe_of_context F in
    let κ := VALTYPE (PrimR I32R) ImCopy ImDrop in
    let ψ := InstrT (τs1 ++ [CodeRefT κ (MonoFunT τs1 τs2)]) τs2 in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ICallIndirect ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Admitted.

  Lemma compat_inject_sum M F L wl wl' wlf es' i τs τ κ :
    let fe := fe_of_context F in
    let ψ := InstrT [τ] [SumT κ τs] in
    τs !! i = Some τ ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IInject ψ i)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Admitted.

  Lemma compat_inject_variant M F L wl wl' wlf es' μ i τ τ' τs κr κv :
    let fe := fe_of_context F in
    let ψ := InstrT [τ] [RefT κr μ (VariantT κv τs)] in
    τs !! i = Some τ' ->
    mono_mem μ ->
    stores_as F τ τ' ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IInject ψ i)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Admitted.

  Lemma compat_case_sum M F L L' wl wl' wlf es' ess τ' τs κ :
    let fe := fe_of_context F in
    let ψ := InstrT [SumT κ τs] [τ'] in
    Forall2
      (fun τ es =>
         forall wl wl' wlf es',
           run_codegen (compile_instrs mr fe es) wl = inr ((), wl', es') ->
           ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') (InstrT [τ] [τ']) L')
      τs ess ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ICase ψ L' ess)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_case_variant M F L L' wl wl' wlf es' ess τs τs' τ' κr κv μ :
    let fe := fe_of_context F in
    let ψ := InstrT [RefT κr μ (VariantT κv τs)] [τ'] in
    Forall2 (loads_as F) τs τs' ->
    Forall2
      (fun τ es =>
         (forall wl wl' wlf es',
             let fe := fe_of_context F in
             run_codegen (compile_instrs mr fe es) wl = inr ((), wl', es') ->
             ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') (InstrT [τ] [τ']) L'))
      τs' ess ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (ICase ψ L' ess)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_group M F L wl wl' wlf es' τs κ :
    let fe := fe_of_context F in
    let ψ := InstrT τs [ProdT κ τs] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IGroup ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ungroup M F L wl wl' wlf es' τs κ :
    let fe := fe_of_context F in
    let ψ := InstrT [ProdT κ τs] τs in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IUngroup ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Admitted.

  Lemma compat_fold M F L wl wl' wlf es' τ κ :
    let fe := fe_of_context F in
    let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
    let ψ := InstrT [τ0] [RecT κ τ] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IFold ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Admitted.

  Lemma compat_unfold M F L wl wl' wlf es' τ κ :
    let fe := fe_of_context F in
    let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
    let ψ := InstrT [RecT κ τ] [τ0] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IUnfold ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Admitted.

  Lemma compat_pack M F L wl wl' wlf es' τ τ' :
    let fe := fe_of_context F in
    let ψ := InstrT [τ] [τ'] in
    packed_existential F τ τ' ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IPack ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Admitted.

  Lemma compat_unpack M F F0' L L' L0 L0' wl wl' wlf es es' es0 τs1 τs2 ψ0 :
    let fe := fe_of_context F in
    let F' := F <| fc_labels ::= cons (τs2, L') |> in
    let ψ := InstrT τs1 τs2 in
    unpacked_existential F' L es ψ L' F0' L0 es0 ψ0 L0' ->
    has_instruction_type_ok F ψ L' ->
    (forall wl wl' wlf es',
        let fe0' := fe_of_context F0' in
        run_codegen (compile_instrs mr fe0' es0) wl = inr ((), wl', es') ->
        ⊢ have_instruction_type_sem rti sr mr M F0' L0 (wl ++ wl' ++ wlf) (to_e_list es') ψ0 L0') ->
    run_codegen (compile_instr mr fe (IUnpack ψ L' es)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_tag M F L wl wl' wlf es' :
    let fe := fe_of_context F in
    let ψ := InstrT [type_i32] [type_i31] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ITag ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Admitted.

  Lemma compat_untag M F L wl wl' wlf es' :
    let fe := fe_of_context F in
    let ψ := InstrT [type_i31] [type_i32] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IUntag ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Admitted.

  Lemma compat_new M F L wl wl' wlf es' τ τ' κ μ :
    let fe := fe_of_context F in
    let ψ := InstrT [τ] [RefT κ μ τ'] in
    mono_mem μ ->
    stores_as F τ τ' ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (INew ψ)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Admitted.

  Lemma compat_load M F L wl wl' wlf es' π pr κ μ τ τval :
    let fe := fe_of_context F in
    let ψ := InstrT [RefT κ μ τ] [RefT κ μ τ; τval] in
    resolves_path τ π None pr ->
    has_copyability F pr.(pr_target) ImCopy ->
    loads_as F pr.(pr_target) τval ->
    Forall (mono_size F) pr.(pr_prefix) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ILoad ψ π)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Admitted.

  Lemma compat_load_mm M F L wl wl' wlf es' π τ τval κ κ' σ pr :
    let fe := fe_of_context F in
    let ψ := InstrT [RefT κ (ConstM MemMM) τ] [RefT κ' (ConstM MemMM) (pr_replaced pr); τval] in
    resolves_path τ π (Some (type_mem_uninit σ (ConstM MemMM))) pr ->
    has_size F (pr_target pr) σ ->
    loads_as F (pr_target pr) τval ->
    Forall (mono_size F) (pr_prefix pr) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ILoad ψ π)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Admitted.

  Lemma compat_store M F L wl wl' wlf es' π pr κ μ τ τval :
    let fe := fe_of_context F in
    let ψ := InstrT [RefT κ μ τ; τval] [RefT κ μ τ] in
    resolves_path τ π None pr ->
    has_dropability F pr.(pr_target) ImDrop ->
    stores_as F τval pr.(pr_target) ->
    Forall (mono_size F) pr.(pr_prefix) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IStore ψ π)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Admitted.

  Lemma compat_store_mm M F L wl wl' wlf es' π pr κ κ' τ τval τmem :
    let fe := fe_of_context F in
    let ψ := InstrT [RefT κ (ConstM MemMM) τ; τval] [RefT κ' (ConstM MemMM) pr.(pr_replaced)] in
    stores_as F τval τmem ->
    resolves_path τ π (Some τmem) pr ->
    has_dropability F pr.(pr_target) ImDrop ->
    type_size_eq F pr.(pr_target) τmem ->
    Forall (mono_size F) pr.(pr_prefix) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IStore ψ π)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Admitted.

  Lemma compat_swap M F L wl wl' wlf es' π pr κ μ τ τval :
    let fe := fe_of_context F in
    let ψ := InstrT [RefT κ μ τ; τval] [RefT κ μ τ; τval] in
    resolves_path τ π None pr ->
    Forall (mono_size F) pr.(pr_prefix) ->
    loads_as F τval pr.(pr_target) ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ISwap ψ π)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L.
  Admitted.

  Lemma compat_nil M F L wl wl' wlf es' :
    let fe := fe_of_context F in
    run_codegen (compile_instrs mr fe []) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') (InstrT [] []) L.
  Proof.
    intros fe Hcompile.
    cbn in Hcompile.
    inversion Hcompile.

    unfold have_instruction_type_sem.
    iIntros (? ? ? ? ? ?) "Henv Hinst Hlf".
    iIntros (? ?) "Hvs Hframe Hfrinv Hfr Hrun".
    iDestruct "Hvs" as "(%vss & -> & Hvs)".
    iPoseProof (big_sepL2_length with "Hvs") as "%Hlenvs".
    cbn in Hlenvs.
    destruct vss; cbn in Hlenvs; inversion Hlenvs.
    rewrite !app_nil_l.
    unfold expr_interp.

    iApply lenient_wp_nil.
    unfold lp_combine, denote_logpred; cbn.
    iFrame.
    iExists []; auto.
  Qed.

  Lemma to_e_list_distributes e1 e2 :
    to_e_list (e1 ++ e2) = to_e_list e1 ++ to_e_list e2.
  Proof.
    unfold to_e_list. rewrite mathcomp.ssreflect.seq.map_cat. done.
  Qed.
  
  Lemma compat_cons M F L1 L2 L3 wl wl' wlf es' e es τs1 τs2 τs3 :
    let fe := fe_of_context F in
    (forall wl wl' wlf es',
        run_codegen (compile_instr mr fe e) wl = inr ((), wl', es') ->
        ⊢ have_instruction_type_sem rti sr mr M F L1 (wl ++ wl' ++ wlf) (to_e_list es') (InstrT τs1 τs2) L2) ->
    (forall wl wl' wlf es',
        run_codegen (compile_instrs mr fe es) wl = inr ((), wl', es') ->
        ⊢ have_instruction_type_sem rti sr mr M F L2 (wl ++ wl' ++ wlf) (to_e_list es') (InstrT τs2 τs3) L3) ->
    run_codegen (compile_instrs mr fe (e :: es)) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L1 (wl ++ wl' ++ wlf) (to_e_list es') (InstrT τs1 τs3) L3.
  Proof.
    intros fe He Hes Hcompile; rename wl' into wl''.
    (* Step 1: split out Hcompile into Hcompile_e and Hcompile_es *)

    (* For Hcompile_e *)
    unfold compile_instrs in Hcompile.
    cbn in Hcompile.
    inv_cg_bind Hcompile res wl1' wltest es1' es2' Hcompile Hcompile_empty; subst.
    inversion Hcompile_empty; subst; clear Hcompile_empty.

    inv_cg_bind Hcompile res' wl' wl'' e' es' Hcompile_e Hcompile_es_kinda; subst.

    assert (Hres: res' = ()). { admit. } 
    subst.
    autorewrite with list.
    rewrite -app_assoc.
    apply (He _ _ (wl'' ++ wlf)) in Hcompile_e as Hsem_e.


    (* For Hcompile_es: *)

    (* First, rework Hcompile_es_kinda. I'm *pretty* sure this is true *)
    (* Reasoning why I think this is true:
       - compile_instrs is defined as mapM_ (compile_instr fe)
       - mapM_ is defined as ignoring all output at returning ()
       - In Hcompile_es_kinda, we have the normal mapM, and res is a list of ()
       - After staring at some of the insides, I'm *pretty* sure replacing mapM
         with mapM_ results in res (list of ()) turning into just ().
       - then things fold in from there
       Not sure how to prove that atm
     *)
    assert (Hcompile_es:
             run_codegen (compile_instrs mr fe es) (wl ++ wl') = inr((), wl'', es')).
    { admit. }

    apply (Hes _ _ wlf) in Hcompile_es as Hsem_es. clear Hcompile_es_kinda.
    rewrite -app_assoc in Hcompile_es Hsem_es.

    (* a bit of prep for step 2 *)
    rewrite to_e_list_distributes.

    (* Can be temporary: *)
    clear Hcompile_e Hcompile_es He Hes.

    (* Step 2: let's get the type semantic! *)
    unfold have_instruction_type_sem.
    iIntros (? ? ? ? ? ?) "%Henv #Hinst #Hlf".
    iIntros (? ?) "Hvs Hframe Hfrinv Hfr Hrun".
    (* unfold expr_interp. *)

    (* Idea: pass resources into Hsem_e, then Hsem_es *)
    (* Start with all the pure stuff into both *)
    unfold have_instruction_type_sem in Hsem_e, Hsem_es.

    iPoseProof (Hsem_e) as "Hsem_e"; iPoseProof (Hsem_es) as "Hsem_es".
    iSpecialize ("Hsem_e" $! s__mem s__rep s__size se inst lh Henv with "Hinst Hlf").
    iSpecialize ("Hsem_es" $! s__mem s__rep s__size se inst lh Henv with "Hinst Hlf").

    (* Time to use the resources!*)
    iSpecialize("Hsem_e" $! fr vs with "Hvs Hframe Hfrinv Hfr Hrun").

    rewrite (app_assoc (v_to_e_list vs) (to_e_list e') (to_e_list es')).
    (* We have a goal with a lwp with two concatted expression lists. Our context has
       a resource for the lenient weakest precondition for the first of the two.
       lenient_wp_seq, then, seems perfect.

       However, the problem will arise from the fact that our lenient_wp es is stuck
       behind some resources.
     *)
    iApply (lenient_wp_seq with "[Hsem_e]").
    (* This line uses up the lenient_wp for e completely.*)
    - iApply "Hsem_e".
    - (* This is the trap case in the lemma. *)
      iEval (cbn).
      iIntros (f) "HT Hvs".
      iSplitR; done.
    - iEval (cbn).
      iIntros (w f) "Hvs Hfr Hfrinv".
      destruct w eqn:Hw; iEval (cbn) in "Hvs".
      + iDestruct "Hvs" as "(Hf & Hrun & Hvs)".
        iApply ("Hsem_es" with "[$Hvs] [$Hf] [$] [$] [$]").
      + done.
      + admit.
      + admit.
      + admit.
  Admitted.

  Lemma compat_frame M F L L' wl wl' wlf es es' τ τs1 τs2 :
    let fe := fe_of_context F in
    has_mono_rep F τ ->
    (forall wl wl' wlf es',
        run_codegen (compile_instrs mr fe es) wl = inr ((), wl', es') ->
        ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') (InstrT τs1 τs2) L') ->
    run_codegen (compile_instrs mr fe es) wl = inr ((), wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') (InstrT (τ :: τs1) (τ :: τs2)) L'.
  Admitted.

  Theorem fundamental_theorem M F L L' wl wl' wlf es es' tf :
    have_instruction_type M F L es tf L' ->
    let fe := fe_of_context F in
    run_codegen (compile_instrs mr fe es) wl = inr (tt, wl', es') ->
    ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') tf L'.
  Proof.
    intros Htype.
    generalize dependent es'.
    generalize dependent wlf.
    generalize dependent wl'.
    generalize dependent wl.
    induction Htype using have_instruction_type_mind with
      (P1 := fun M F L e ψ L' =>
               forall wl wl' wlf es',
                 let fe := fe_of_context F in
                 run_codegen (compile_instr mr fe e) wl = inr (tt, wl', es') ->
                 ⊢ have_instruction_type_sem rti sr mr M F L (wl ++ wl' ++ wlf) (to_e_list es') ψ L');
      intros wl wl' wlf es' fe Hcomp.
    - eapply compat_nop; eassumption.
    - eapply compat_unreachable; eassumption.
    - eapply compat_copy; eassumption.
    - eapply compat_drop; eassumption.
    - eapply compat_num; eassumption.
    - eapply compat_num_const; eassumption.
    - eapply compat_block; eassumption.
    - eapply compat_loop; eassumption.
    - eapply compat_ite with (es1 := es1); eassumption.
    - eapply compat_br; eassumption.
    - eapply compat_return; eassumption.
    - eapply compat_local_get; eassumption.
    - eapply compat_local_get_copy; eassumption.
    - eapply compat_local_set; eassumption.
    - eapply compat_coderef; eassumption.
    - eapply compat_inst; eassumption.
    - eapply compat_call; eassumption.
    - eapply compat_call_indirect; eassumption.
    - eapply compat_inject_sum; eassumption.
    - eapply compat_inject_variant; eassumption.
    - eapply compat_case_sum; eassumption.
    - eapply compat_case_variant; eassumption.
    - eapply compat_group; eassumption.
    - eapply compat_ungroup; eassumption.
    - eapply compat_fold; eassumption.
    - eapply compat_unfold; eassumption.
    - eapply compat_pack; eassumption.
    - eapply compat_unpack; eassumption.
    - eapply compat_tag; eassumption.
    - eapply compat_untag; eassumption.
    - eapply compat_new; eassumption.
    - eapply compat_load; eassumption.
    - eapply compat_load_mm; eassumption.
    - eapply compat_store; eassumption.
    - eapply compat_store_mm; eassumption.
    - eapply compat_swap; eassumption.
    - eapply compat_nil; eassumption.
    - eapply compat_cons; eassumption.
    - eapply compat_frame; eassumption.
  Qed.

End Fundamental.
 
