From iris.proofmode Require Export base proofmode classes.

From RichWasm Require Import syntax typing named_props.
From RichWasm.compiler Require Import prelude module.
Require Import RichWasm.iris.host.iris_host.
Require Import RichWasm.iris.rules.iris_rules.
From RichWasm.iris Require Import logrel memory util.
From RichWasm.iris Require Import logrel.instr.typing.
From RichWasm.iris Require Import logrel.env_props.
From RichWasm.iris Require Import logrel.instr.typing.inst.
From RichWasm.iris Require Import logrel.logrel_properties.
From RichWasm.iris Require Import language.cwp.

Module W := RichWasm.wasm.datatypes.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section function.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.

  Lemma bind_inr {A B C} (mx : A + B) (f : B -> A + C) (y : C) :
    mx ≫= f = inr y ↔ ∃ x : B, mx = inr x /\ f x = inr y.
  Proof.
    split.
    - intros H. destruct mx; first inversion H. by exists b.
    - by intros (x & -> & Hfx).
  Qed.

  Lemma try_opt_inr {E A} (err : E) c (a : A) :
    util.try_option err c = inr a →
    c = Some a.
  Proof.
    destruct c; cbn; intros Heq; by inversion Heq.
  Qed.

  Definition atom_zero (ι : atomic_rep) : atom :=
    match ι with
    | PtrR => PtrA (PtrInt 0%N)
    | I32R => I32A (Wasm_int.int_zero i32m)
    | I64R => I64A (Wasm_int.int_zero i64m)
    | F32R => F32A (Wasm_float.float_zero f32m)
    | F64R => F64A (Wasm_float.float_zero f64m)
    end.

  Lemma big_sepL2_concat_inv_l {X Y} {P : X → Y → iProp Σ} xss ys :
    ([∗ list] x; y ∈ concat xss; ys, P x y) -∗
    ∃ yss, ⌜ys = concat yss⌝ ∗ ([∗ list] xs; ys ∈ xss; yss, [∗ list] x; y ∈ xs; ys, P x y).
  Proof.
    revert ys.
    induction xss; iIntros (ys) "Hall".
    - iPoseProof (big_sepL2_nil_inv_l with "Hall") as "->".
      iExists [].
      by rewrite big_sepL2_nil.
    - cbn [concat].
      iPoseProof (big_sepL2_app_inv_l with "Hall") as "(%ys1 & %ys2 & -> & Hys1 & Hys2)".
      iPoseProof (IHxss with "Hys2") as "(%yss & -> & Hyss)".
      iExists (ys1 :: yss).
      by iFrame.
  Qed.

  Inductive ifunction_env_ok (locs: list representation) : kind_ctx → list kind → inner_function_type → function_env → Prop :=
  | FEMono fe κs τs1 τs2 ρs_P ηss_P ηss_L K :
    fe_type_vars fe = κs →
    fe_return fe = τs2 →
    mapM (type_rep κs) τs1 = Some ρs_P →
    mapM eval_rep_prim_empty ρs_P = Some ηss_P →
    mapM eval_rep_prim_empty locs = Some ηss_L →
    fe_locals fe = ηss_P ++ ηss_L →
    ifunction_env_ok locs K κs (MonoFunT τs1 τs2) fe
  | FEType K κs κ ϕ fe :
    ifunction_env_ok locs K (κ :: κs) ϕ fe →
    ifunction_env_ok locs K κs (ForallTypeT κ ϕ) fe.

  Inductive function_env_ok (locs : list representation) : kind_ctx → Core.function_type → function_env → Prop :=
  | FEInner K ϕ fe :
    ifunction_env_ok locs K [] ϕ fe →
    function_env_ok locs K (InnerFunT ϕ) fe
  | FEMem K ϕ fe :
    function_env_ok locs (K <| kc_mem_vars ::= S |>) ϕ fe →
    function_env_ok locs K (ForallMemT ϕ) fe
  | FERep K ϕ fe :
    function_env_ok locs (K <| kc_rep_vars ::= S |>) ϕ fe →
    function_env_ok locs K (ForallRepT ϕ) fe
  | FESize K ϕ fe :
    function_env_ok locs (K <| kc_size_vars ::= S |>) ϕ fe →
    function_env_ok locs K (ForallSizeT ϕ) fe.

  Lemma atom_interp_atom_zero ι :
    ⊢ atom_interp (atom_zero ι) (bitzero (translate_arep ι)).
  Proof.
    destruct ι; cbn; iStartProof; try done; [].
    iExists 0%N, Wasm_int.Int32.zero.
    iSplit; first done.
    iSplit; first done.
    iExists (RootInt 0).
    iPureIntro.
    split; last done.
    by constructor.
  Qed.

  Lemma atoms_interp_atom_zero ιs :
    ⊢ atoms_interp (map atom_zero ιs) (map bitzero (map translate_arep ιs)).
  Proof.
    induction ιs as [|ι ιs].
    - done.
    - cbn -[atom_interp].
      iPoseProof (atom_interp_atom_zero ι) as "H".
      iPoseProof IHιs as "IH".
      iFrame "H IH".
  Qed.

  Lemma atomss_interp_atom_zero ιss :
    ⊢ [∗ list] ιs ∈ ιss, atoms_interp (map atom_zero ιs) (map bitzero (map translate_arep ιs)).
  Proof.
    induction ιss as [|ιs ιss].
    - done.
    - cbn -[atom_interp].
      iPoseProof (atoms_interp_atom_zero ιs) as "H".
      iPoseProof IHιss as "IH".
      iFrame "H IH".
  Qed.

  Lemma atom_plug se ιs :
    ⊢ type_interp rti sr (type_plug_prim (map arep_to_prim ιs)) se (SAtoms (map atom_zero ιs)).
  Proof.
  Admitted.

  Lemma atomss_plug se ιss :
    ⊢ [∗ list] τ; os ∈ map type_plug_prim (map (map arep_to_prim) ιss); map (map atom_zero) ιss,
        type_interp rti sr τ se (SAtoms os).
  Proof.
    induction ιss as [| ιs ιss]; try done.
    iPoseProof IHιss as "IH".
    iPoseProof (atom_plug se ιs) as "H".
    iFrame "H IH".
  Qed.

  Lemma has_reps_type_reps_agree F τs ρs ρs' κs :
    Forall2 (has_rep F) τs ρs →
    fc_type_vars F = κs →
    mapM (type_rep κs) τs = Some ρs' →
    ρs = ρs'.
  Proof.
  Admitted.

  Lemma translate_types_agree τs κs se ts :
    type_ctx_interp κs se →
    prelude.translate_types κs τs = Some ts →
    translate_types (Σ := Σ) se τs = Some ts.
  Proof.
  Admitted.

  Lemma eval_rep_arep_to_prim locs ιss ηss :
    mapM (eval_rep EmptyEnv) locs = Some ιss →
    mapM (eval_rep_prim EmptyEnv) locs = Some ηss →
    ηss = map (map arep_to_prim) ιss.
  Proof.
    revert ιss ηss.
    induction locs as [| loc locs]; intros *; cbn; intros Hreps Hprims.
    - inversion Hreps. inversion Hprims.
      done.
    - apply bind_Some in Hreps.
      destruct Hreps as (ιs & Hrep & Hreps).
      apply bind_Some in Hreps.
      destruct Hreps as (ιss' & Hreps & Heq); inversion Heq; clear Heq.
      apply bind_Some in Hprims.
      destruct Hprims as (ηs & Hprim & Hprims).
      apply bind_Some in Hprims.
      destruct Hprims as (ηss' & Hprims & Heq); inversion Heq; clear Heq.
      cbn.
  Admitted.

  Lemma mapM_fmap {X Y Z} (xs : list X) (f : X → option Y) (g : Y → Z) :
    mapM (λ x, g <$> f x) xs = map g <$> mapM f xs.
  Proof.
    induction xs; cbn; try done.
    rewrite IHxs.
    destruct (mapM f xs), (f a); cbn; done.
  Qed.

  Lemma has_prims_arep_to_prims ιs os vs :
    has_areps ιs (SAtoms os) →
    atoms_interp os vs -∗
    ⌜has_prims (map arep_to_prim ιs) vs⌝.
  Proof.
  Admitted.

  Lemma has_kind_empty_type_skind (se : semantic_env (Σ := Σ)) F τ ρ ξ ιs :
    sem_env_interp F se →
    has_kind F τ (VALTYPE ρ ξ) →
    eval_rep EmptyEnv ρ = Some ιs →
    type_skind se τ = Some (SVALTYPE ιs ξ).
  Proof.
    intros Hse Hk Henv.
    eapply type_skind_has_kind_Some; eauto.
    cbn.
    erewrite eval_rep_emptyenv; eauto.
  Qed.

  Lemma has_reps_has_prims se F τ ρ ηs os vs :
    sem_env_interp F se →
    has_rep F τ ρ →
    eval_rep_prim EmptyEnv ρ = Some ηs →
    atoms_interp os vs -∗
    type_interp rti sr τ se (SAtoms os) -∗
    ⌜has_prims ηs vs⌝.
  Proof.
    iIntros (Hse Hrep Hev) "Hat Hty".
    inversion Hrep; subst.
    rewrite type_interp_eq.
    iDestruct "Hty" as "(%sk & %Hevk & %Hsk & Hty)".
    unfold eval_rep_prim in Hev.
    apply fmap_Some in Hev.
    destruct Hev as (ιs & Hevrep & ->).
    assert (sk = SVALTYPE ιs ξ).
    {
      erewrite has_kind_empty_type_skind in Hevk; eauto.
      congruence.
    }
    subst sk.
    inversion Hsk.
    by iApply (has_prims_arep_to_prims with "[$]").
  Qed.

  Lemma has_repss_has_primss se F τs ρs ηss oss vss :
    sem_env_interp F se →
    Forall2 (has_rep F) τs ρs →
    mapM (eval_rep_prim EmptyEnv) ρs = Some ηss →
    ([∗ list] os;vs ∈ oss; vss, atoms_interp os vs) -∗
    ([∗ list] τ;os ∈ τs;oss, type_interp rti sr τ se (SAtoms os)) -∗
    ⌜Forall2 has_prims ηss vss⌝.
  Proof.
    intros Hse Hrep.
    revert vss oss ηss.
    induction Hrep; intros * Hev; iIntros "Hat Hty".
    - cbn in Hev; inversion Hev; subst.
      iPoseProof (big_sepL2_nil_inv_l with "Hty") as "->".
      iPoseProof (big_sepL2_nil_inv_l with "Hat") as "->".
      done.
    - cbn in Hev.
      apply bind_Some in Hev.
      destruct Hev as (ηs & Hev & Hevs).
      apply bind_Some in Hevs.
      destruct Hevs as (ηss' & Hevs & Hret).
      inversion Hret; subst.
      iPoseProof (big_sepL2_cons_inv_l with "Hty") as "(%os & %oss' & -> & Hos & Hoss)".
      iPoseProof (big_sepL2_cons_inv_l with "Hat") as "(%vs & %vss' & -> & Hvs & Hvss)".
      iPoseProof (IHHrep with "Hvss Hoss") as "%Hall"; eauto.
      iPoseProof (has_reps_has_prims with "Hvs Hos") as "%Hfst"; eauto.
  Qed.

  Theorem interp_has_ifun_type ϕ : ∀ fe M K κs wt wt' wtf locs body tf mf' (se : semantic_env (Σ := Σ)),
    body_has_ifun_type M K locs body κs ϕ →
    kind_ctx_interp K se ->
    type_ctx_interp κs se ->
    translate_inner_func_type κs ϕ = Some tf ->
    ifunction_env_ok locs K κs ϕ fe ->
    compile_fun_body wt tf fe locs body = inr (wt', mf') →
    ∀ inst,
    ⊢ ⌜inst_types inst !! typeimm (modfunc_type mf') = Some tf⌝ -∗
      instance_interp rti sr mr M (wt ++ wt' ++ wtf) inst -∗
      inner_closure_interp rti sr ϕ se
        (FC_func_native inst tf mf'.(modfunc_locals) mf'.(modfunc_body)).
  Proof.
    induction ϕ; intros * Hty Hse1 Hse2 Htf Hfe Hcf inst;
      iIntros "%Hf #Hinst";
      rewrite inner_closure_interp_eq.
    - cbn [inner_closure_interp'].
      inversion Hty; subst.

      (* Open up the compiler *)
      unfold compile_fun_body in Hcf.
      destruct (insert_type wt tf) as [wt'' tid] eqn:Htid.
      apply bind_inr in Hcf.
      destruct Hcf as (res & Hcg & Hcf).
      destruct res as [[[[] wt_es] wl_es] es].
      apply bind_inr in Hcf.
      destruct Hcf as (ιs & Hevrep & Hcf).
      inversion Hcf; subst; clear Hcf.
      cbn in Htf.
      apply bind_Some in Htf.
      destruct Htf as (ts1 & Ht1 & Hts).
      apply bind_Some in Hts.
      destruct Hts as (ts2 & Ht2 & Hts).
      inversion Hts; subst.
      rename l into τs1.
      rename l0 into τs2.

      assert (fe = fe_of_context F).
      {
        destruct fe.
        inversion Hfe; subst.
        subst F.
        unfold fe_of_context.
        cbn.
        cbn in H14.
        rewrite H14.
        f_equal.
        unfold eval_rep_prim_empty  in *; cbn in *.
        f_equal.
        - assert (ρs_P = ρs_P0).
          { by eapply has_reps_type_reps_agree. }
          subst ρs_P0.
          rewrite H2 in H9.
          congruence.
        - rewrite H3 in H12.
          congruence.
      }
      subst fe.
      cbn [modfunc_locals modfunc_body].
      pose proof H6 as Hsem.
      eapply (fundamental_typing rti sr) in Hsem; last apply Hcg.
      instantiate (1 := []) in Hsem.
      (* now deal with closure_interp' *)
      cbn -[atoms_interp values_interp1 translate_types].
      cbn in Hf.
      cbn -[atom_interp translate_types].
      assert (translate_types (Σ:=Σ) se τs1 = prelude.translate_types κs τs1) as Htrans1.
      {
        rewrite Ht1.
        eapply translate_types_agree; eauto.
      }
      assert (translate_types (Σ:=Σ) se τs2 = prelude.translate_types κs τs2) as Htrans2.
      {
        rewrite Ht2.
        eapply translate_types_agree; eauto.
      }
      iSplitR; last iSplitR.
      { by rewrite Htrans1. }
      { by rewrite Htrans2. }
      iIntros "!> !> % % % Hats Hvs Htok Hown Hf Hrun".
      set (f := {| W.f_locs := vs1 ++ n_zeros (flat_map (map translate_arep) ιs ++ wl_es); W.f_inst := inst |}).
      change inst with (f_inst f).
      rewrite -!app_assoc.
      rewrite -!app_assoc in Hsem.
      instantiate (1 := wtf) in Hsem.
      clear_nils.
      unfold have_instr_type_sem in Hsem.
      change es with ([] ++ es).
      iPoseProof (Hsem with "[] [] Hinst") as "Hsem".
      {
        instantiate (1 := se).
        iPureIntro.
        subst F; done.
      }
      {
        instantiate (1 := []).
        instantiate (1 := []).
        done.
      }
      assert (ηss_L = map (map arep_to_prim) ιs).
      {
        rename H3 into Hevprim.
        apply try_opt_inr in Hevrep.
        unfold eval_rep_prim in Hevprim.
        rewrite mapM_fmap Hevrep in Hevprim.
        cbn in Hevprim; inversion Hevprim; subst ηss_L.
        done.
      }
      iApply (cwp_wand with "[-]").
      {
        iApply ("Hsem" with "[] [] [] [] [Hats Hvs] Htok Hown Hf Hrun"); iClear "Hsem"; clear Hsem.
        - unfold labels_interp.
          simpl fc_labels.
          iApply big_sepL2_singleton.
          iSplitR.
          { by rewrite Htrans2 Ht2. }
          iModIntro.
          iIntros (fr' vs' os' θ') "%Hrel Hfr Htok Hinv Hats Hvs".
          iFrame.
        - unfold return_interp.
          unfold F; cbn [fc_return].
          iSplitR.
          { by rewrite Htrans2 Ht2. }
          iModIntro.
          iIntros (vs' os' θ') "Hats Hvs Htok Hinv".
          iFrame.
        - by iApply big_sepL2_nil.
        - iExists [].
          iSplit; done.
        - subst F L.
          cbn -[atoms_interp atom_interp].
          iDestruct "Hvs" as "(%oss & -> & Hvs)".
          rewrite big_sepL2_fmap_l.
          iPoseProof (big_sepL2_concat_inv_l with "Hats") as "(%vss & -> & Hvss)".
          iAssert (⌜Forall2 has_prims ηss_P vss⌝%I) with "[Hvs Hvss]" as "%Hhasprims".
          {
            iApply (has_repss_has_primss with "Hvss Hvs"); eauto.
            split; cbn; done.
          }
          iExists (oss ++ _).
          iExists (vss ++ _).
          iExists _.
          iSplitR; last iSplitR; last iSplitR; last iSplitL "Hvss".
          + rewrite flat_map_concat_map.
            unfold n_zeros.
            change @seq.map with @map.
            rewrite map_app.
            rewrite concat_map.
            iEval (rewrite app_assoc).
            rewrite -concat_app.
            done.
          + iPureIntro.
            apply Forall2_app; first done.
            replace (map (map translate_arep) ιs) with (map (map translate_prim) ηss_L); swap 1 2.
            {
              subst ηss_L.
              unfold translate_arep.
              repeat setoid_rewrite map_map.
              done.
            }
            apply Forall2_fmap_r.
            apply Forall2_fmap_r.
            apply Forall_Forall2_diag.
            apply Forall_true.
            intros; cbn.
            unfold has_prims.
            apply Forall2_fmap_r.
            apply Forall2_fmap_r.
            apply Forall_Forall2_diag.
            apply Forall_true.
            intros [| | |]; done.
          + iPureIntro.
            apply Forall2_fmap_r.
            apply Forall_Forall2_diag.
            apply Forall_true.
            intros [| | |]; cbn; eauto.
          + instantiate (1 := map (map atom_zero) ιs).
            iApply (big_sepL2_app with "Hvss").
            rewrite !big_sepL2_fmap_l.
            rewrite !big_sepL2_fmap_r.
            iApply big_sepL_sepL2_diag.
            iApply (atomss_interp_atom_zero ιs).
          + iApply (big_sepL2_app with "Hvs").
            subst ηss_L.
            iApply atomss_plug.
      }
      iIntros (f' v')
        "(%Hfrel & Hfr & (%os_ret & Hos_ret & Hats_ret) & (%θ' & Htok) & Hinv)".
      by iFrame.
    - iIntros "!> %sk %sk_T %T %Hev %Hsub %Hsk".
      inversion Hty; subst.
      inversion Hfe; subst.
      iApply IHϕ; eauto.
      unfold type_ctx_interp in *.
      constructor.
      + intuition eauto.
        by apply eval_kind_type_irrel.
      + eapply Forall2_impl; eauto.
        intros.
        destruct y as [sk' [skT T']].
        by setoid_rewrite <- eval_kind_type_irrel_eq.
  Qed.

  Theorem interp_has_fun_type ϕ : ∀ M locs body fe K tf wt wt' wtf mf' (se : semantic_env (Σ := Σ)),
    body_has_fun_type M locs body K ϕ →
    kind_ctx_interp K se ->
    se.2 = [] ->
    function_env_ok locs K ϕ fe ->
    translate_func_type [] ϕ = Some tf ->
    compile_fun_body wt tf fe locs body = inr (wt', mf') →
    ∀ inst,
    ⊢ ⌜inst_types inst !! typeimm (modfunc_type mf') = Some tf⌝ -∗
      instance_interp rti sr mr M (wt ++ wt' ++ wtf) inst -∗
      closure_interp rti sr ϕ se
        (FC_func_native inst tf (modfunc_locals mf') (modfunc_body mf')).
  Proof.
    induction ϕ; intros * Hty Hse Hnil Hfe Htf Hcf inst;
      iIntros "%Hf #Hinst";
      inversion Hty; subst;
      inversion Hfe; subst;
      rewrite closure_interp_eq.
    - rewrite -inner_closure_interp_eq.
      iApply interp_has_ifun_type; eauto.
      destruct se; cbn in *; subst.
      by constructor.
    - iIntros "!> %μ".
      iApply IHϕ; eauto.
      destruct Hse as (? & ? & ?).
      destruct K.
      cbn in *.
      repeat split; cbn; eauto.
    - iIntros "!> %ιs".
      iApply IHϕ; eauto.
      destruct Hse as (? & ? & ?).
      destruct K.
      cbn in *.
      repeat split; cbn; eauto.
    - iIntros "!> %n".
      iApply IHϕ; eauto.
      destruct Hse as (? & ? & ?).
      destruct K.
      cbn in *.
      repeat split; cbn; eauto.
  Qed.

  Lemma fe_of_ifun_ty_ok κs ϕ locs fe K :
    fe_of_ifun_type κs ϕ locs = Some fe →
    ifunction_env_ok locs K κs ϕ fe.
  Proof.
    revert κs.
    induction ϕ; intros κs.
    - cbn.
      intros Hfe.
      apply bind_Some in Hfe.
      destruct Hfe as (ρs & Hρs & Hev).
      apply bind_Some in Hev.
      destruct Hev as (ηss_P & HP & Hev).
      apply bind_Some in Hev.
      destruct Hev as (ηss_L & HL & Hev).
      inversion Hev.
      by econstructor; eauto.
    - cbn.
      intros Hfe.
      constructor.
      by eapply IHϕ.
  Qed.

  Lemma fe_of_fun_ty_ok ϕ locs fe K :
    fe_of_fun_type ϕ locs = Some fe →
    function_env_ok locs K ϕ fe.
  Proof.
    revert K.
    induction ϕ; intros K Hfe;
      cbn in Hfe; try by (constructor; eauto).
    constructor.
    cbn in Hfe.
    apply fe_of_ifun_ty_ok; eauto.
  Qed.

  Lemma fe_of_mod_func_ok mf fe :
    fe_of_module_func mf = Some fe →
    function_env_ok (mf_locals mf) kc_empty (mf_type mf) fe.
  Proof.
    unfold fe_of_module_func.
    intros Hfe.
    by apply fe_of_fun_ty_ok.
  Qed.

  Lemma insert_type_inst_get wt tf wt' tid wtf :
    insert_type wt tf = (wt', tid) →
    (wt ++ option_list wt' ++ wtf) !! tid = Some tf.
  Proof.
    unfold insert_type.
    destruct (list_find (λ v2 : function_type, W.function_type_eqb tf v2) wt) as [[n ϕ]|] eqn:?.
    - intros Hret.
      inversion Hret; subst.
      cbn.
      rewrite list_find_Some in Heqo.
      destruct Heqo as (Hget & Heq & _).
      destruct (eqfunction_typeP tf ϕ); subst; try done.
      rewrite lookup_app_l; eauto.
      by apply lookup_lt_is_Some_1.
    - intros Hret.
      inversion Hret; subst.
      cbn.
      rewrite lookup_app_r; eauto.
      by rewrite Nat.sub_diag.
  Qed.

  Lemma modfun_type_is_translate_type mf tf wt' mf' inst wt fe wtf :
    translate_func_type [] (mf_type mf) = Some tf →
    compile_fun_body wt tf fe (mf_locals mf) (mf_body mf) = inr (wt', mf') →
    inst_types inst = wt ++ wt' ++ wtf →
    inst_types inst !! typeimm (modfunc_type mf') = Some tf.
  Proof.
    intros Htf Hcf Hinst.
    unfold compile_fun_body in Hcf.
    destruct (insert_type wt tf) as [wt'' tid] eqn:Htid.
    apply bind_inr in Hcf.
    destruct Hcf as ([[[[] wt2] wl] es] & Hcb & Hcf).
    apply bind_inr in Hcf.
    destruct Hcf as (ιss & Hiss & Hret).
    inversion Hret; subst; clear Hret.
    cbn.
    rewrite Hinst.
    rewrite -app_assoc.
    by apply insert_type_inst_get.
  Qed.

  Theorem fundamental_function : ∀ M wt wt' wtf mf mf',
    has_function_type M mf ->
    compile_function wt mf = inr (wt', mf') ->
    ⊢ has_func_type_sem rti sr module.mr M (wt ++ wt' ++ wtf) mf' mf.(mf_type).
  Proof.
    unfold has_function_type, compile_function.
    intros * Hty Hcf.
    apply bind_inr in Hcf.
    destruct Hcf as (tf & Htf & Hcf).
    apply bind_inr in Hcf.
    destruct Hcf as (fe & Hfe & Hcf).
    apply try_opt_inr in Htf.
    apply try_opt_inr in Hfe.
    unfold has_func_type_sem.
    iIntros "% % % Hinst".
    iAssert (⌜inst_types inst = wt ++ wt' ++ wtf⌝%I) with "[Hinst]" as "%Htys".
    {
      iDestruct "Hinst" as "[A B]".
      iApply "A".
    }
    pose proof H as Htf0.
    erewrite modfun_type_is_translate_type in Htf0; eauto.
    inversion Htf0; subst tf0.
    iApply interp_has_fun_type; eauto.
    - done.
    - by apply fe_of_mod_func_ok.
  Qed.

End function.
