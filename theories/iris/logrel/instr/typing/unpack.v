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

  Lemma frame_interp_ren ξm ξr ξs ξt (se se' : semantic_env (Σ:=Σ)) ηss L WL fr :
    sem_env_ren ξm ξr ξs ξt se se' →
    frame_interp rti sr se ηss L WL fr ∗-∗
      frame_interp rti sr se' ηss (map (ren_type ξm ξr ξs ξt) L) WL fr.
  Proof.
    intros HR.
    iSplitR; iIntros "Hframe"; unfold frame_interp;
    iDestruct "Hframe" as "(%oss & %vss_L & %vs_WL & %flocs & %fprims & %resint & Hos & Hlocals)";
      iFrame; iExists vs_WL; repeat (iSplitR; try done).
    - cbn.
      (* yes *)
      admit.
    - (* yup *)
      admit.
  Admitted.

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
    destruct ψ as [τs1' τs2'].
    inv_cg_bind Hcg ?τ ?wt ?wt ?wl ?wl ?es_emp ?es Hlast Hcg.
    inv_cg_try_option Hlast; subst; clear_nils.
    inv_cg_bind Hcg ?tf ?wt ?wt ?wl ?wl ?es_emp ?es Hft Hcg.
    inv_cg_try_option Hft; subst; clear_nils.
    fold (compile_instrs mr) in Hcg.
    apply wp_ignore in Hcg.
    destruct Hcg as (_ & [] & Hcg).

    (* Start iris proof *)
    iIntros (???????? Hse Hevs) "@@@@@@@@@@".
    destruct tf as [ts1 ts2].
    apply cwp_block_c in Hcg as Hcg_block.
    destruct Hcg_block as (es_c & Hcg_es & Hcg_block).

    iAssert (⌜length evs = length ts1⌝%I) with "[Hvs Hos]" as "%Hlents1". {
      admit.
    }

    iApply (Hcg_block with "[$] [$] [-]").
    { done. }
    { apply Is_true_true. by eapply has_values_is_consts. }

    iIntros "Hfr Hrun".
    clear Hcg_block Hcg.

    (* now it's time to apply the IH *)
    cbn in Hcg_es.
    inversion Hunpack; subst.
    - (* exists mem *)
      apply last_singleton in Heq_some as Tosubst.
      subst τ.
      assert (fe_extend_unpack fe (ExistsMemT κ τ0) = fe_of_context F1). {
        done.
      }
      rewrite H in Hcg_es.
      apply (IH _ _ wtf _ _ wlf) in Hcg_es.

      (* this might be tough... *)
      subst WL WT. clear_nils.
      set (WL := wl ++ wl2 ++ wlf) in *; set (WT := wt ++ wt2 ++ wtf) in *.
      move WL at top; move WT at top.

      unfold have_instr_type_sem in Hcg_es.
      (* return interp: fine, because translate type length is invariant under ren shift, and the only
       thing that might get changed is values_interp, but se will also go up with F1 ideally so we should be fine *)
      (* labels_interp: translate types invariant, then frame interp is the question but should be fine (checking later)
       values_interp will be fine too, it's only upshifts *)
      (* frame interp: only thing relevant is locals getting uped (fc_locals doesn't change), and this is value interp
       with an updated se, so we should be fine as above *)
      (* yeah the value interp lemma is value_interp_ren and it will work, I just have to set up the new se correctly *)
      (* okay yes everything settles down to value_interp_ren ! *)

      (* I need to get the witness out of values_interp. I also need to get it out anyway for value_interp of τ0 *)
      iDestruct (values_interp_app_l with "Hos") as "(%os1 & %os2 & -> & Hos1 & Hexists)".
      rewrite values_interp_one_eq.
      rewrite value_interp_eq.
      Opaque senv_insert_mem.
      iEval (cbn) in "Hexists".
      iDestruct "Hexists" as "(%sκ & %Heval & %Hsksv & Hexists)".
      (* maybe not distinctly necessary but fun anyway *)
      destruct sκ as [ρ ξ | σ ξ]; cbn in Hsksv; try by inversion Hsksv.
      destruct Hsksv as [Hareps Href].

      iDestruct "Hexists" as "(%μ & Hτ0)".

      assert (sem_env_ren S id id id se (senv_insert_mem μ se)) as Hsemren by done.

      (* I think that we're pretty much ready to apply? *)
      iApply (cwp_wand with "[-]").
      {
        iPoseProof Hcg_es as "Hcg_es".
        iApply ("Hcg_es" $! (senv_insert_mem μ se) fr (os1 ++ os2) vs evs
                 with "[%] [//] [//] [] [] [$Hvs] [Hos1 Hτ0] [Hframe] [$] [$] [$] [$]"); try (iClear "Hcg_es").
        - (* I'm concerned for the other cases but I think this one is fine *)
          admit.
        - assert (typing.fc_locals F1 = typing.fc_locals F) by done.
          rewrite H0; clear H0.
          admit.
        - admit.
        - admit.
        - assert (typing.fc_locals F1 = typing.fc_locals F) by done.
          rewrite H0. unfold up; clear H0.
          pose proof (frame_interp_ren S id id id se (senv_insert_mem μ se)).
          specialize (H0 (typing.fc_locals F) L WL fr Hsemren).
          by iApply H0.
      }

      iIntros (fr' vs') "(%Hrel & Hframe & Hvals & Hrt & Hown)".
      iFrame.

      iSplitR; [ iPureIntro; done | iSplitR "Hvals"].
      + assert (typing.fc_locals F1 = typing.fc_locals F) by done.
        rewrite H0. unfold up; clear H0.
        pose proof (frame_interp_ren S id id id se (senv_insert_mem μ se)).
        specialize (H0 (typing.fc_locals F) L' WL fr' Hsemren).
        by iApply H0.
      + iDestruct "Hvals" as "(%os' & Hval & Hatom)".
        iFrame.
        pose proof (values_interp_ren rti sr mr S id id id se (senv_insert_mem μ se)).
        specialize (H0 τs2' Hsemren).
        by iApply H0.
      Transparent senv_insert_mem.
    - (* exists rep *)
      apply last_singleton in Heq_some as Tosubst.
      subst τ.
      assert (fe_extend_unpack fe (ExistsRepT κ τ0) = fe_of_context F1). {
        subst F1; unfold fe_extend_unpack, fe_of_context.
        unfold subst_function_ctx; cbn.
        subst F'; cbn. unfold set; cbn.
        subst fe. unfold fe_of_context; cbn.
        admit.
      }

      admit.
    - (* exists size *)
      apply last_singleton in Heq_some as Tosubst.
      subst τ.
      assert (fe_extend_unpack fe (ExistsSizeT κ τ0) = fe_of_context F1). {
        subst F1; unfold fe_extend_unpack, fe_of_context.
        unfold subst_function_ctx; cbn.
        subst F'; cbn. unfold set; cbn.
        subst fe. unfold fe_of_context; cbn.
        admit.
      }
      admit.
    - admit.
  Admitted.

End unpack.
