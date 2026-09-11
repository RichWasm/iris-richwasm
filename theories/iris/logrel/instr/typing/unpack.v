Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.substitution.
Require Import RichWasm.iris.logrel.logrel_properties.
Require Import RichWasm.iris.logrel.env_props.
Require Import RichWasm.kinding_subst.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section unpack.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma last_singleton {A:Type} (l:list A) a a' :
    last (l ++ [a]) = Some a' -> a = a'.
  Proof.
    intros H.
    pose proof (last_snoc a l) as H'.
    rewrite H in H'.
    inversion H'; done.
  Qed.

  Lemma locals_interp_ren ξm ξr ξs ξt (se se' : semantic_env (Σ:=Σ)) L oss :
    sem_env_ren ξm ξr ξs ξt se se' →
    locals_interp rti sr se L oss ⊣⊢ locals_interp rti sr se' (map (ren_type ξm ξr ξs ξt) L) oss.
  Proof.
    intros HR.
    unfold locals_interp; cbn.
    rewrite map_fmap big_sepL2_fmap_l.
    apply big_sepL2_proper; intros _ τ os _ _.
    exact (value_interp_ren _ _ _ _ _ _ _ _ τ HR (SAtoms os)).
  Qed.

  Lemma frame_interp_ren ξm ξr ξs ξt (se se' : semantic_env (Σ:=Σ)) ηss L WL fr :
    sem_env_ren ξm ξr ξs ξt se se' →
    frame_interp rti sr se ηss L WL fr ⊣⊢
      frame_interp rti sr se' ηss (map (ren_type ξm ξr ξs ξt) L) WL fr.
  Proof.
    intros HR; cbn.
    do 3 (f_equiv; intros ?).
    do 4 f_equiv.
    exact (locals_interp_ren _ _ _ _ _ _ _ _ HR).
  Qed.

  Lemma label_interp_ren ξm ξr ξs ξt (se se' : semantic_env (Σ:=Σ)) ηss fr WL lmask τs L ls :
    sem_env_ren ξm ξr ξs ξt se se' →
    label_interp rti sr se ηss fr WL lmask (τs, L) ls ⊣⊢
      label_interp rti sr se' ηss fr WL lmask
        (map (ren_type ξm ξr ξs ξt) τs, map (ren_type ξm ξr ξs ξt) L) ls.
  Proof.
    intros HR; destruct ls as [n P]; cbn -[translate_types values_interp frame_interp].
    rewrite <- (translate_types_ren _ _ _ _ _ _ _ HR).
    f_equiv; f_equiv.
    do 4 (f_equiv; intros ?).
    f_equiv.
    f_equiv; [exact (frame_interp_ren _ _ _ _ _ _ _ _ _ _ HR)|].
    do 4 f_equiv.
    exact (values_interp_ren _ _ _ _ _ _ _ _ _ HR _).
  Qed.

  Lemma labels_interp_ren ξm ξr ξs ξt (se se' : semantic_env (Σ:=Σ)) ηss fr WL lmask Ls B :
    sem_env_ren ξm ξr ξs ξt se se' →
    labels_interp rti sr se ηss fr WL lmask Ls B ⊣⊢
      labels_interp rti sr se' ηss fr WL lmask
        (map (λ '(τs, L), (map (ren_type ξm ξr ξs ξt) τs, map (ren_type ξm ξr ξs ξt) L)) Ls) B.
  Proof.
    intros HR; unfold labels_interp.
    rewrite map_fmap big_sepL2_fmap_l.
    apply big_sepL2_proper; intros k [τs L] ls _ _; cbn.
    exact (label_interp_ren _ _ _ _ _ _ _ _ _ _ _ _ _ HR).
  Qed.

  Lemma labels_interp_cons_iff (se : semantic_env (Σ:=Σ)) ηss fr WL lmask τs L Ls ls B :
    labels_interp rti sr se ηss fr WL lmask ((τs, L) :: Ls) (ls :: B) ⊣⊢
      label_interp rti sr se ηss fr WL lmask (τs, L) ls ∗
      labels_interp rti sr se ηss fr WL lmask Ls B.
  Proof. apply big_sepL2_cons. Qed.

  Lemma return_interp_ren ξm ξr ξs ξt (se se' : semantic_env (Σ:=Σ)) τr R :
    sem_env_ren ξm ξr ξs ξt se se' →
    return_interp rti sr se τr R ⊣⊢ return_interp rti sr se' (map (ren_type ξm ξr ξs ξt) τr) R.
  Proof.
    intros HR; destruct R as [[n P]|]; cbn -[translate_types values_interp]; [|done].
    rewrite <- (translate_types_ren _ _ _ _ _ _ _ HR).
    f_equiv; f_equiv.
    do 3 (f_equiv; intros ?).
    f_equiv.
    f_equiv.
    exact (values_interp_ren _ _ _ _ _ _ _ _ _ HR _).
  Qed.

  Lemma sem_env_interp_ren_ctx F (se : semantic_env (Σ:=Σ)) ξm ξt :
    sem_env_interp F se → sem_env_interp (subst_function_ctx ξm id id ξt F) se.
  Proof.
    intros [Hk Ht]; split; [exact Hk|].
    unfold type_ctx_interp in *; cbn.
    by rewrite (map_ext _ _ rinstId'_kind) map_id.
  Qed.

  Lemma compat_unpack M F F0' L L' L0 L0' wt wt' wtf wl wl' wlf es es' τs1 τs2 ψ0 :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let F' := F <| fc_labels ::= cons (τs2, L') |> in
    let ψ := InstrT τs1 τs2 in
    unpacked_existential F' L ψ L' F0' L0 ψ0 L0' ->
    has_instruction_type_ok M F ψ L' ->
    (forall wt wt' wtf wl wl' wlf es',
        let fe0' := fe_of_context F0' in
        let WT := wt ++ wt' ++ wtf in
        let WL := wl ++ wl' ++ wlf in
        let lmask := wlmask fe0' wl in
        run_codegen (compile_instrs mr fe0' es) wt wl = inr ((), wt', wl', es') ->
        ⊢ have_instr_type_sem rti sr mr M F0' L0 WT WL lmask es' ψ0 L0') ->
    run_codegen (compile_instr mr fe (IUnpack ψ L' es)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L'.
  Proof.
    intros * Hunpack Hty IH Hcg.
    cbn [compile_instr] in Hcg.
    unfold compile_unpack in Hcg.
    subst ψ; cbn [compile_unpack] in Hcg.
    inv_cg_bind Hcg ?τ ?wt ?wt ?wl ?wl ?es_emp ?es Hlast Hcg.
    inv_cg_try_option Hlast; subst; clear_nils.
    inv_cg_bind Hcg ?tf ?wt ?wt ?wl ?wl ?es_emp ?es Hft Hcg.
    inv_cg_try_option Hft; subst; clear_nils.
    fold (compile_instrs mr) in Hcg.
    apply wp_ignore in Hcg.
    destruct Hcg as (_ & [] & Hcg).

    iIntros (???????? Hse Hevs) "@@@@@@@@@@".
    destruct tf as [ts1 ts2].
    apply cwp_block_c in Hcg as Hcg_block.
    destruct Hcg_block as (es_c & Hcg_es & Hcg_block).

    apply bind_Some in Heq_some0 as (ts1' & Hts1 & Htrans).
    apply bind_Some in Htrans as (ts2' & Hts2 & [= <- <-]).
    iDestruct (translate_types_comp_interp_length with "Hos") as "%Hoslen"; [done|exact Hts1|].
    iDestruct (big_sepL2_length with "Hvs") as "%Hvslen".
    unfold ofe_car in Hvslen.
    apply has_values_length in Hevs as Hevslen.

    iApply (Hcg_block with "[$] [$] [-]").
    { lia. }
    { apply Is_true_true. by eapply has_values_is_consts. }

    iIntros "Hfr Hrun".
    clear Hcg_block Hcg.

    cbn in Hcg_es.
    inversion Hunpack; subst.
    - (* exists mem *)
      apply last_singleton in Heq_some as <-.
      assert (fe_extend_unpack fe (ExistsMemT κ τ0) = fe_of_context F1) as Hfe by done.
      rewrite Hfe in Hcg_es.
      apply (IH _ _ wtf _ _ wlf) in Hcg_es.
      subst WL WT. clear_nils.
      set (WL := wl ++ wl2 ++ wlf) in *; set (WT := wt ++ wt2 ++ wtf) in *.
      move WL at top; move WT at top.
      unfold have_instr_type_sem in Hcg_es.

      iDestruct (values_interp_app_l with "Hos") as "(%os1 & %os2 & -> & Hos1 & Hexists)".
      iEval (rewrite values_interp_one_eq value_interp_eq; cbn -[senv_insert_mem]) in "Hexists".
      iDestruct "Hexists" as "(%sκ & %Heval & %Hsksv & %μ & Hτ0)".
      assert (sem_env_ren S id id id se (senv_insert_mem μ se)) as HR
        by exact (sem_env_ren_shift_mem se μ).
      have Hlabels1 : fc_labels F1 = (map up τs2, map up L') :: map (λ '(τs, L), (map up τs, map up L)) (fc_labels F).
      { reflexivity. }

      iApply (cwp_wand with "[-]").
      { iPoseProof Hcg_es as "Hcg_es".
        iApply ("Hcg_es" $! (senv_insert_mem μ se) fr (os1 ++ os2) vs evs
                 with "[%] [//] [//] [] [] [$Hvs] [Hos1 Hτ0] [Hframe] [$] [$] [$] [$]").
        - by apply sem_env_insert_mem, sem_env_interp_ren_ctx.
        - rewrite Hlabels1.
          iApply labels_interp_cons_iff.
          iSplitR.
          + cbn [label_interp].
            iSplitR.
            * have Hts2s : translate_types se τs2 = Some ts2'.
              { eapply translate_types_comp_sem; [exact Hse|exact Hts2]. }
              by rewrite -(translate_types_ren _ _ _ _ _ _ _ HR) Hts2s.
            * iIntros "!>" (fr'' vs'' os θ') "%Hrel Hframe' Hrt Hown Hvs' Hos'".
              iFrame.
              iSplitR; [done|].
              iSplitL "Hframe'"; [by iApply (frame_interp_ren _ _ _ _ _ _ _ _ _ _ HR)|].
              by iApply (values_interp_ren _ _ _ _ _ _ _ _ _ HR).
          + by iApply (labels_interp_ren _ _ _ _ _ _ _ _ _ _ _ _ HR).
        - by iApply (return_interp_ren _ _ _ _ _ _ _ _ HR).
        - iApply (values_interp_app with "[Hos1] [Hτ0]").
          + by iApply (values_interp_ren _ _ _ _ _ _ _ _ _ HR).
          + iApply values_interp_one_eq.
            Transparent value_interp. iExact "Hτ0". Opaque value_interp.
        - by iApply (frame_interp_ren _ _ _ _ _ _ _ _ _ _ HR).
      }
      iIntros (fr' vs') "(%Hrel & Hframe & Hvals & Hrt & Hown)".
      iFrame.
      iSplitR; [done|].
      iDestruct "Hvals" as "(%os' & Hval & Hatom)".
      iSplitL "Hframe"; [by iApply (frame_interp_ren _ _ _ _ _ _ _ _ _ _ HR)|].
      iExists os'; iFrame.
      by iApply (values_interp_ren _ _ _ _ _ _ _ _ _ HR).
    - (* exists rep *)
      admit.
    - (* exists size *)
      admit.
    - (* exists type *)
      admit.
  Admitted.

End unpack.
