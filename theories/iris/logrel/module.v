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

  Theorem fundamental_module m m' mt :
    has_module_type m mt ->
    compile_module m = inr m' ->
    ⊢ module_interp rti sr mt m'.
  Proof.
    iIntros (Hmt Hm ????) "Hmod Hrt Himps %Hlen_exps Hexps Hfr Hrun".
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
    set start_idx := W.Mk_funcidx (funcimm mr.(mr_func_user) + length imps + length defs).
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
    - admit.
    - admit.
    - iFrame. admit.
    - iIntros (?) "Hfr Hrun (Hmod & Himp & %inst & Hpost & Hhost)".
      iDestruct "Hpost" as
        "(% & % & % & % & % & % & Htypeck & %Hexps & %Htab_allocs & %Hwts' & %Helem_bound &
          %Hmem_allocs & %Hwms' & %Hdata_bound & %Hglob_init & %Hglob_allocs & Hinst)".
      destruct Hexps as
        (Hinst_types & Hext_funcs & Hext_tab & Hext_mem & Hext_globs & Hcheck_start).
      iDestruct "Hinst" as "(Hinst_func & Hinst_tab & Hinst_mem & Hinst_glob)".

      rewrite Hm' in Hcheck_start.
      cbn in Hcheck_start.

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
