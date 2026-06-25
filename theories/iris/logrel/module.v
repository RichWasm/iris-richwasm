From stdpp Require Import base.
From mathcomp Require Import eqtype ssreflect.
From iris.proofmode Require Export base proofmode classes.

From RichWasm Require Import syntax typing.
From RichWasm.compiler Require Import prelude module.
Require Import RichWasm.iris.host.iris_host.
Require Import RichWasm.iris.rules.iris_rules.
From RichWasm.iris Require Import logrel memory util.

Module W := RichWasm.wasm.datatypes.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Fundamental.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.
  Context `{!hvisG Σ}.
  Context `{!hmsG Σ}.
  Context `{!hasG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.

  Lemma bind_inr {A B C} (mx : A + B) (f : B -> A + C) (y : C) :
    mx ≫= f = inr y ↔ ∃ x : B, mx = inr x /\ f x = inr y.
  Proof.
    split.
    - intros H. destruct mx; first inversion H. by exists b.
    - by intros (x & -> & Hfx).
  Qed.

  Lemma check_start_Some m inst idx :
    is_true (check_start m inst (Some idx)) →
    ∃ ms msf,
      mod_start m = Some ms /\
      modstart_func ms = Mk_funcidx msf /\
      nth_error (inst_funcs inst) msf = Some idx.
  Proof.
    cbn.
    intros Hstart.
    eapply ssrbool.elimT in Hstart; last apply opt_eqP.
    rewrite bind_Some in Hstart.
    destruct Hstart as (ms & Hms & Hlookup).
    destruct (modstart_func ms) as [msf] eqn:?.
    eauto.
  Qed.

  Definition translate_function_type : Core.function_type → function_type.
  Admitted.

  Definition rt_imps : list extern_t := map ET_func rt_types.

  Definition mt_imps (mt : module_type) : list extern_t :=
    rt_imps ++ map (ET_func ∘ translate_function_type) mt.(mt_imports).

  Definition mt_table_exps (mt : module_type) : list extern_t.
  Admitted.

  Definition mt_exps (mt : module_type) : list extern_t :=
    map (ET_func ∘ translate_function_type) mt.(mt_exports) ++ mt_table_exps mt.

  Lemma type_functions rt_types wt m wt' defs c table :
    let ϕs := m_imports m ++ map mf_type (m_functions m) in
    let M := {| mc_functions := ϕs; mc_table := table |} in
    compile_functions (rt_types ++ wt) (m_functions m) = inr (wt', defs) →
    Forall (λ mf : module_function, has_function_type M mf (mf_type mf)) (m_functions m) →
    Forall2 (module_func_typing c) defs (map translate_function_type ϕs).
  Proof.
  Admitted.

  Theorem type_module m m' mt :
    has_module_type m mt ->
    compile_module m = inr m' ->
    module_typing m' (mt_imps mt) (mt_exps mt).
  Proof.
    iIntros (Hmt Hm).
    apply bind_inr in Hm as ([wt imps] & Himps_try & Hm).
    destruct (user_imports rt_types m.(module.m_imports)) as [[wt' imps']|] eqn:Himps;
      last inversion Himps_try.
    inversion Himps_try.
    subst wt' imps'.
    clear Himps_try.
    apply bind_inr in Hm as ([wt' defs] & Hdefs & Hm).

    set user_exps := map (user_export (funcimm mr.(mr_func_user))) m.(m_exports).
    set table_exps := map table_export m.(m_table).
    set start_func := table_start m.(m_table).
    set start_idx' := funcimm mr.(mr_func_user) + length imps + length defs.
    set start_idx := W.Mk_funcidx start_idx'.
    assert
      (m' =
         {|
           W.mod_types := rt_types ++ wt ++ wt';
           W.mod_funcs := defs ++ [start_func];
           W.mod_tables := [];
           W.mod_mems := [];
           W.mod_globals := rt_globals;
           W.mod_elem := [];
           W.mod_data := [];
           W.mod_start := Some (W.Build_module_start start_idx);
           W.mod_imports := rt_imports ++ imps;
           W.mod_exports := user_exps ++ table_exps
         |}) as Hm' by by inversion Hm.
    clear Hm.

    inversion Hmt; subst m0 mt.

    do 2 eexists; rewrite Hm'; intros.
    repeat split.
    - instantiate (1 := map translate_function_type ϕs ++ [instruction.W.Tf [] []]).
      apply Forall2_app.
      + by eapply type_functions.
      + constructor; last done.
        unfold module_func_typing.
        unfold start_func, table_start.
        repeat split.
        * admit.
    - admit.
    - done.
    - done.
    - unfold c.
      cbn.
      admit.
    - admit.
    - admit.
  Admitted.

  Definition mk_gen_exp_ts (m  : module.module) (mt : module_type) : list Core.function_type.
  Admitted.

  Theorem fundamental_module m m' mt :
    has_module_type m mt ->
    compile_module m = inr m' ->
    ⊢ module_interp rti sr compiler.module.mr mt (mk_gen_exp_ts m mt) m'.
  Proof.
    iIntros (Hmt Hm ??????) "Hmod Hrt Himps %Hlen_exps %Hlen_extra Hexps Hrt_inst Hfr Hrun".
    pose proof (type_module _ _ _ Hmt Hm) as Hmct.
    apply bind_inr in Hm as ([wt imps] & Himps_try & Hm).
    destruct (user_imports rt_types m.(module.m_imports)) as [[wt' imps']|] eqn:Himps;
      last inversion Himps_try.
    inversion Himps_try.
    subst wt' imps'.
    clear Himps_try.
    apply bind_inr in Hm as ([wt' defs] & Hdefs & Hm).

    set user_exps := map (user_export (funcimm mr.(mr_func_user))) m.(m_exports).
    set table_exps := map table_export m.(m_table).
    set start_func := table_start m.(m_table).
    set start_idx' := funcimm mr.(mr_func_user) + length imps + length defs.
    set start_idx := W.Mk_funcidx start_idx'.
    assert
      (m' =
         {|
           W.mod_types := rt_types ++ wt ++ wt';
           W.mod_funcs := defs ++ [start_func];
           W.mod_tables := [];
           W.mod_mems := [];
           W.mod_globals := rt_globals;
           W.mod_elem := [];
           W.mod_data := [];
           W.mod_start := Some (W.Build_module_start start_idx);
           W.mod_imports := rt_imports ++ imps;
           W.mod_exports := user_exps ++ table_exps
         |}) as Hm' by by inversion Hm.
    clear Hm.

    iApply (instantiation_spec_operational_start with "[$] [$] [-]").
    - instantiate (2 := m'). by rewrite Hm'.
    - apply Hmct.
    - repeat split.
      + rewrite Hm'.
        eexists [_]; eauto.
      + rewrite Hm'.
        exists []; eauto.
      + rewrite Hm'.
        exists []; eauto.
    - unfold instantiation_resources_pre.
      iSplitR; last iSplitR; last iSplitR; last iSplitR.
      + admit.
      + admit.
      + admit.
      + admit.
      + iPureIntro.
        rewrite Hm'.
        cbn.
        unfold user_exps.
        rewrite length_app.
        rewrite Hlen_exps.
        inversion Hmt.
        eapply util.nths_error_length in H0.
        rewrite -H0.
        rewrite !length_map.
        admit.
    - iIntros (?) "Hfr Hrun (Hmod & Himp & %inst & Hpost & Hhost)".
      iDestruct "Hpost" as
        "(% & % & % & % & % & % & Htypeck & %Hexps & %Htab_allocs & %Hwts' & %Helem_bound &
          %Hmem_allocs & %Hwms' & %Hdata_bound & %Hglob_init & %Hglob_allocs & Hinst)".
      destruct Hexps as
        (Hinst_types & Hext_funcs & Hext_tab & Hext_mem & Hext_globs & Hcheck_start).
      iDestruct "Hinst" as "(Hinst_func & Hinst_tab & Hinst_mem & Hinst_glob)".


      rewrite Hm' in Hcheck_start.
      eapply check_start_Some in Hcheck_start.
      destruct Hcheck_start as (ms & msf & Hms & Hmsf & Hidnstartmsf).
      cbn in Hms.
      inversion Hms; subst ms; clear Hms.
      inversion Hmsf; subst msf; clear Hmsf.

      iEval (unfold module_inst_resources_func) in "Hinst_func".
      iPoseProof (big_sepL2_lookup_acc with "Hinst_func") as "Hwfstart".
      { admit. }
      { instantiate (2 := funcimm (mr_func_user mr) + length defs).
        instantiate (1 := idnstart).
        rewrite lookup_drop.
        unfold start_idx' in Hidnstartmsf.
        rewrite -nth_error_lookup.
        replace (get_import_func_count m' + (funcimm (mr_func_user mr) + length defs))
          with (funcimm (mr_func_user mr) + length imps + length defs); first done.
        rewrite Hm'.
        rewrite Nat.add_assoc.
        rewrite (Nat.add_comm _ (funcimm _)).
        f_equal.
        f_equal.
        change @length with @seq.size.
        admit. }


      (* TODO: Find the ↦[wf] resource for idnstart. *)

      iApply wp_lift_wasm.
      change [AI_invoke idnstart] with ([] ++ [AI_invoke idnstart]).
      iApply (wp_invoke_native with "[$] [$]").
      + done.
      + by instantiate (1 := []).
      + done.
      + admit.
      + iIntros "!> (Hfr & Hrun & Hstart)".
        admit.
  Admitted.

End Fundamental.
