From iris.proofmode Require Export base proofmode classes.

From RichWasm Require Import syntax typing named_props.
From RichWasm.compiler Require Import prelude module.
Require Import RichWasm.iris.host.iris_host.
Require Import RichWasm.iris.rules.iris_rules.
From RichWasm.iris Require Import logrel memory util.
From RichWasm.iris Require Import logrel.instr.typing.
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

  Lemma insert_type_inst_get mr M wt tf wt' tid wtf inst :
    ⌜insert_type wt tf = (wt', tid)⌝ -∗
    instance_interp rti sr mr M (wt ++ option_list wt' ++ wtf) inst -∗
    ⌜inst_types inst !! tid = Some tf⌝.
  Proof.
  Admitted.

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

  Theorem fund_function_mono τs1 τs2 M wt wt' wtf mf mf' :
    has_function_type M mf (InnerFunT (MonoFunT τs1 τs2)) →
    compile_function wt mf = inr (wt', mf') →
    ⊢ has_func_type_sem rti sr module.mr M (wt ++ wt' ++ wtf) mf' (InnerFunT (MonoFunT τs1 τs2)).
  Proof.
    iIntros (Hϕ Hcf ?? Htf) "#Hinst".

    (* Open up the typing judgment *)
    inversion Hϕ.
    subst M0 mf0 ϕ ϕ0.
    set (fft := flatten_function_type mf.(mf_type)) in *.

    rename H0 into Hηss_L.
    rename H1 into Hρs_P.
    rename H2 into Hηss_P.
    rename H6 into Hψ.
    rename H3 into HL'.
    rename H into Hty.
    destruct tf as [ts1 ts2].

    (* Open up the compiler *)
    apply bind_inr in Hcf.
    destruct Hcf as (ft & Hft & Hcf).
    destruct (insert_type wt ft) as [wt'' tid] eqn:Htid.
    apply bind_inr in Hcf.
    destruct Hcf as (fe & Hfe & Hcf).
    apply bind_inr in Hcf.
    destruct Hcf as (res & Hcg & Hcf).
    destruct res as [[[[] wt_es] wl_es] es].
    apply bind_inr in Hcf.
    destruct Hcf as (ιs & Hevrep & Hcf).
    inversion Hcf; subst; clear Hcf.
    cbn.

    rewrite Hty in Hft.
    apply try_opt_inr in Hft.
    apply bind_Some in Hft.
    destruct Hft as (ts1' & Hts1' & Hft).
    apply bind_Some in Hft.
    destruct Hft as (ts2' & Hts2' & Hft).
    inversion Hft; subst ft.
    cbn in Htf.
    rewrite -app_assoc.
    iPoseProof (insert_type_inst_get with "[//] Hinst") as "%Hget".
    rewrite Hget in Htf; inversion Htf; subst ts1' ts2'.

    (* Show the function env matches what F says *)
    assert (fe_of_context F = fe).
    {
      revert Hfe; intros Hfe.
      unfold fe_of_context; cbn.
      apply try_opt_inr in Hfe.
      apply bind_Some in Hfe.
      destruct Hfe as (ρs_fe & Hρs & Hfe).
      apply bind_Some in Hfe.
      destruct Hfe as (ηss_P' & HηP' & Hfe).
      apply bind_Some in Hfe.
      destruct Hfe as (ηss_L' & HηL' & Hfe).
      inversion Hfe.
      unfold fft; cbn.
      f_equal.
      cbn in HηP', HηL'.
      assert (ρs_fe = ρs_P).
      { admit. }
      subst ρs_fe.
      rewrite Hηss_P in HηP'.
      rewrite Hηss_L in HηL'.
      congruence.
    }
    subst fe.

    unfold ψ in Hψ; clear ψ.
    unfold fft in Hψ.
    rewrite Hty in Hψ.
    cbn in Hψ.

    (* Obtain the semantic typing for the body of the fn *)
    pose proof Hψ as Hsem.
    eapply (fundamental_typing rti sr) in Hsem; last apply Hcg.
    instantiate (2 := wtf) in Hsem.
    clear_nils.

    (* now deal with closure_interp' *)
    rewrite closure_interp_eq.
    unfold closure_interp'.
    rewrite Hty.
    unfold mono_closure_interp.
    cbn -[atom_interp translate_types].
    assert (translate_types (Σ:=Σ) senv_empty τs1 = prelude.translate_types [] τs1) as Htrans1.
    { admit. }
    assert (translate_types (Σ:=Σ) senv_empty τs2 = prelude.translate_types [] τs2) as Htrans2.
    { admit. }
    iSplitR; last iSplitR.
    (* For both of these admits, we have to relate prelude.translate_types and
       logrel.translate_types. *)
    { by rewrite Htrans1 Hts1'. }
    { by rewrite Htrans2 Hts2'. }
    iIntros "!> !>".
    iIntros (vs1 os1 θ) "Hats Hoss Htok Hmask Hf Hr".
    unfold have_instr_type_sem in Hsem.
    set (fr := {| W.f_locs := vs1 ++ n_zeros (flat_map (map translate_arep) ιs ++ wl_es);
                 W.f_inst := inst |}).
    iPoseProof (Hsem $! senv_empty fr _ _ [] with "[] [] Hinst") as "Hsem"; clear Hsem.
    { iPureIntro.
      unfold sem_env_interp, F, K, fft, kc_of_fft; cbn.
      rewrite Hty; cbn.
      split.
      - done.
      - constructor.
    }
    {
      by instantiate (1 := []).
    }
    clear_nils.
    iApply (cwp_wand with "[-]").
    { iApply ("Hsem" with "[] [] [] [] [Hoss Hats] Htok Hmask Hf Hr"); iClear "Hsem".
      - unfold labels_interp.
        simpl fc_labels.
        unfold fft.
        rewrite Hty.
        iApply big_sepL2_singleton.
        iSplitR.
        { by rewrite Htrans2 Hts2'. }
        iModIntro.
        iIntros (fr' vs' os' θ') "%Hrel Hfr Htok Hinv Hats Hvs".
        iFrame.
      - unfold return_interp.
        unfold F; cbn [fc_return].
        unfold fft.
        rewrite Hty.
        iSplitR.
        { by rewrite Htrans2 Hts2'. }
        iModIntro.
        iIntros (vs' os' θ') "Hats Hvs Htok Hinv".
        iFrame.
      - by iApply big_sepL2_nil.
      - iExists [].
        iSplit; first done.
        by rewrite big_sepL2_nil.
      - unfold frame_interp. cbn -[atom_interp].
        iDestruct "Hoss" as "(%oss & -> & Hoss)".
        setoid_rewrite big_sepL2_fmap_l.
        unfold L, fft.
        rewrite Hty.
        cbn [flatten_function_type fft_in].
        iPoseProof (big_sepL2_concat_inv_l with "Hats") as "(%vss & -> & Hats)".
        iExists (oss ++ map (map atom_zero) ιs).
        iExists (vss ++ (map (n_zeros ∘ map translate_arep) ιs)).
        iExists (n_zeros wl_es).
        iFrame.
        repeat iSplitR; try iPureIntro.
        + unfold n_zeros; change @seq.map with @map.
          rewrite map_app concat_app -app_assoc.
          f_equal.
          f_equal.
          rewrite flat_map_concat_map.
          rewrite concat_map.
          rewrite map_map.
          done.
        + admit.
        + admit.
        + repeat setoid_rewrite big_sepL2_fmap_l.
          repeat setoid_rewrite big_sepL2_fmap_r.
          iApply big_sepL_sepL2_diag.
          admit.
        + repeat setoid_rewrite big_sepL2_fmap_l.
          repeat setoid_rewrite big_sepL2_fmap_r.
          admit.
    }
    {
      iIntros (f v)
       "(%Hfrel & Hfr & (%os_ret & Hos_ret & Hats_ret) & (%θ' & Htok) & Hinv)".
      by iFrame.
    }
  Admitted.

  Theorem fundamental_function ϕ : ∀ mr M wt wt' wtf mf mf',
    has_function_type M mf ϕ ->
    compile_function wt mf = inr (wt', mf') ->
    ⊢ has_func_type_sem rti sr mr M (wt ++ wt' ++ wtf) mf' ϕ.
  Proof.
    (* TODO: By induction on ϕ, build up an se such that sem_env_interp F se.
             Then use the fundamental theorem for instruction typing to show that the body of the
             function is well-behaved. *)
  Admitted.

End function.
