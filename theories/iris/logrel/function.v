From iris.proofmode Require Export base proofmode classes.

From RichWasm Require Import syntax typing named_props.
From RichWasm.compiler Require Import prelude module.
Require Import RichWasm.iris.host.iris_host.
Require Import RichWasm.iris.rules.iris_rules.
From RichWasm.iris Require Import logrel memory util.
From RichWasm.iris Require Import logrel.instr.typing.
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
    destruct Hcf as (ιs & Hevrep & Hcf).
    apply bind_inr in Hcf.
    destruct Hcf as (res & Hcg & Hcf).
    destruct res as [[[[] wt_es] wl_es] es].
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
        iAssert (⌜Forall2 has_prims ηss_P vss⌝%I) with "[Hats]" as "%Hprims".
        {
          admit.
        }
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
        + apply Forall2_app; first done.
          admit.
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

  Theorem fund_function_mem ϕ M wt wt' wtf mf mf' :
    has_function_type M mf (ForallMemT ϕ) →
    compile_function wt mf = inr (wt', mf') →
    ⊢ has_func_type_sem rti sr module.mr M (wt ++ wt' ++ wtf) mf' (ForallMemT ϕ).
  Proof.
  Admitted.

  Lemma fft_in_mem ϕ :
    fft_in (flatten_function_type (ForallMemT ϕ)) = fft_in (flatten_function_type ϕ).
  Proof.
  Admitted.

  Lemma fft_in_rep ϕ :
    fft_in (flatten_function_type (ForallRepT ϕ)) = fft_in (flatten_function_type ϕ).
  Proof.
  Admitted.

  Lemma fft_in_size ϕ :
    fft_in (flatten_function_type (ForallSizeT ϕ)) = fft_in (flatten_function_type ϕ).
  Proof.
  Admitted.

  Lemma fft_in_type κ ϕ :
    fft_in (flatten_inner_function_type (ForallTypeT κ ϕ)) = fft_in (flatten_inner_function_type ϕ).
  Proof.
  Admitted.

  Lemma fft_in_inner ϕ :
    fft_in (flatten_function_type (InnerFunT ϕ)) = fft_in (flatten_inner_function_type ϕ).
  Proof.
  Admitted.

  Lemma fft_out_mem ϕ :
    fft_out (flatten_function_type (ForallMemT ϕ)) = fft_out (flatten_function_type ϕ).
  Proof.
  Admitted.

  Lemma fft_out_rep ϕ :
    fft_out (flatten_function_type (ForallRepT ϕ)) = fft_out (flatten_function_type ϕ).
  Proof.
  Admitted.

  Lemma fft_out_size ϕ :
    fft_out (flatten_function_type (ForallSizeT ϕ)) = fft_out (flatten_function_type ϕ).
  Proof.
  Admitted.

  Lemma fft_out_type κ ϕ :
    fft_out (flatten_inner_function_type (ForallTypeT κ ϕ)) = fft_out (flatten_inner_function_type ϕ).
  Proof.
  Admitted.

  Lemma fft_out_inner ϕ :
    fft_out (flatten_function_type (InnerFunT ϕ)) = fft_out (flatten_inner_function_type ϕ).
  Proof.
  Admitted.


  Ltac do_ffts_hyp H :=
    rewrite
      ?fft_in_mem
      ?fft_in_rep
      ?fft_in_size
      ?fft_in_type
      ?fft_in_inner
      ?fft_out_mem
      ?fft_out_rep
      ?fft_out_size
      ?fft_out_type
      in H.

  Ltac do_ffts :=
    rewrite
      -> ?fft_in_mem,
      ?fft_in_rep,
      ?fft_in_size,
      ?fft_in_type,
      ?fft_out_mem,
      ?fft_out_rep,
      ?fft_out_size,
      ?fft_out_type
      in *.

  Lemma sem_env_interp_empty :
    sem_env_interp (Σ := Σ) fc_empty senv_empty.
  Proof.
    unfold sem_env_interp, kind_ctx_interp, type_ctx_interp, kc_mem_vars, kc_rep_vars, kc_size_vars.
    cbn.
    eauto.
  Qed.

  Definition insert_mems (e' : mem_env) (e : mem_env) : mem_env :=
    e' ++ e.

  Definition insert_reps (e' : rep_env) (e : rep_env) : rep_env :=
    e' ++ e.

  Definition insert_sizes (e' : size_env) (e : size_env) : size_env :=
    e' ++ e.

  Definition insert_types (e' : type_env) (e : type_env) : type_env (Σ := Σ) :=
    e' ++ e.

  Definition senv_insert_all (se' : semantic_env) (se : semantic_env) : semantic_env :=
    (
      insert_mems (senv_mems se') (senv_mems se),
      insert_reps (senv_reps se') (senv_reps se),
      insert_sizes (senv_sizes se') (senv_sizes se),
      insert_types (senv_types se') (senv_types se)
    ).

  Lemma senv_insert_id_l se :
    senv_insert_all senv_empty se = se.
  Proof.
    unfold senv_insert_all, senv_empty.
    by destruct se as [[[? ?] ?] ?].
  Qed.

  Lemma senv_insert_id_l' se' se :
    senv_mems se' = [] →
    senv_reps se' = [] →
    senv_sizes se' = [] →
    senv_types se' = [] →
    senv_insert_all se' se = se.
  Proof.
    intros Hm Hr Hs Ht.
    destruct se' as [[[? ?] ?] ?].
    cbn in *.
    subst.
    apply senv_insert_id_l.
  Qed.

  Definition flat_fn_mem_interp (ϕ : flat_function_type) (e : mem_env) : Prop :=
    ϕ.(fft_mem_vars) = length e.

  Definition flat_fn_rep_interp (ϕ : flat_function_type) (e : rep_env) : Prop :=
    ϕ.(fft_rep_vars) = length e.

  Definition flat_fn_size_interp (ϕ : flat_function_type) (e : size_env) : Prop :=
    ϕ.(fft_size_vars) = length e.

  Inductive flat_fn_interp (ϕ : flat_function_type) (se' : semantic_env (Σ := Σ)) : Prop :=
    FlatInterp :
      flat_fn_mem_interp ϕ (senv_mems se') →
      flat_fn_rep_interp ϕ (senv_reps se') →
      flat_fn_size_interp ϕ (senv_sizes se') →
      flat_fn_interp ϕ se'.

  (* This lemma is cribbed from inst.v but includes a subkinding. *)
  Lemma sem_env_interp_insert_type_weak F (se : semantic_env (Σ:=Σ)) κ sκ sκ_T T :
    sem_env_interp F se →
    eval_kind se κ = Some sκ →
    skind_has_stype sκ_T T →
    subskind_of sκ_T sκ →
    sem_env_interp (F <| fc_type_vars ::= app [κ] |>) (senv_insert_type sκ sκ_T T se).
  Proof.
  Admitted.

  (*
  Definition flat_closure_interp_wk (ϕ: flat_function_type) (se_r : semantic_env) (cl : function_closure) (FT : semantic_env -n> ClR) : iProp Σ :=
    □ ∀ se',
      let se_all := senv_insert_all se' se_r in
      ⌜flat_fn_interp ϕ se'⌝ -∗
      ∀ sks,
        ⌜mapM (eval_kind se_all) ϕ.(fft_type_vars) = Some sks⌝ -∗
        ⌜Forall2 (λ sk '(sk_T, T), subskind_of sk_T sk ∧
                                   skind_has_stype sk_T T)
                 sks (senv_types se')⌝ -∗
        FT se_all cl.

  Definition flat_closure_interp (ϕ: flat_function_type) (se : semantic_env) (cl : function_closure) : iProp Σ :=
    let ts1 := ϕ.(fft_in) in
    let ts2 := ϕ.(fft_out) in
    let Ts1 := map (type_interp rti sr) ts1 in
    let Ts2 := map (type_interp rti sr) ts2 in
    flat_closure_interp_wk ϕ se cl (mono_closure_interp rti sr ts1 ts2 Ts1 Ts2).
  *)
  Lemma type_inserts_swap se' sκ sκ_T T se :
    (senv_insert_all (senv_insert_all se' (senv_insert_type sκ sκ_T T senv_empty)) se) =
    (senv_insert_all se' (senv_insert_type sκ sκ_T T se)).
  Proof.
    destruct se as [[[m r] s] o].
    destruct se' as [[[m' r'] s'] o'].
    unfold senv_insert_all, senv_insert_type.
    cbn.
    clear_nils.
    done.
  Qed.

  Lemma fft_tys_forall κ ϕ :
    fft_type_vars (flatten_inner_function_type (ForallTypeT κ ϕ)) = κ :: fft_type_vars (flatten_inner_function_type ϕ).
  Proof.
    cbn.
    by destruct (flatten_inner_function_type ϕ) as [m r s t i o] eqn:Hfft.
  Qed.

  Inductive quant :=
  | QMem
  | QRep
  | QSize.

  Inductive iquant :=
  | QType (κ : kind).

  Inductive qfun_ty :=
  | QFun (qs : list quant) (iqs : list iquant) (ins : list type) (outs : list type).

  Fixpoint get_tys (ft : Core.inner_function_type) : list type * list type :=
    match ft with
    | ForallTypeT _ ft => get_tys ft
    | MonoFunT τs1 τs2 => (τs1, τs2)
    end.

  Fixpoint get_inner (ft : Core.function_type) : inner_function_type :=
    match ft with
    | InnerFunT ft => ft
    | ForallMemT ft
    | ForallRepT ft
    | ForallSizeT ft => get_inner ft
    end.

  Fixpoint istrip (ft : Core.inner_function_type) : list iquant :=
    match ft with
    | ForallTypeT κ ft => QType κ :: istrip ft
    | MonoFunT _ _ => []
    end.

  Fixpoint strip (ft : Core.function_type) : list quant :=
    match ft with
    | InnerFunT ft => []
    | ForallMemT ft => QMem :: strip ft
    | ForallRepT ft => QRep :: strip ft
    | ForallSizeT ft => QSize :: strip ft
    end.

  Definition qfun_of_fun (ft : Core.function_type) : qfun_ty :=
    let ift := get_inner ft in
    let '(τs1, τs2) := get_tys ift in
    let qs := strip ft in
    let iqs := istrip ift in
    QFun qs iqs τs1 τs2.

  Definition quantify1 (q : quant) : Core.function_type → Core.function_type :=
    match q with
    | QMem => ForallMemT
    | QRep => ForallRepT
    | QSize => ForallSizeT
    end.

  Definition quantify (qs : list quant) (ft : Core.function_type) : Core.function_type :=
    fold_right quantify1 ft qs.

  Definition iquantify1 (q : iquant) : Core.inner_function_type → Core.inner_function_type :=
    let '(QType κ) := q in
    ForallTypeT κ.

  Definition iquantify (qs : list iquant) (ft : inner_function_type) : inner_function_type :=
    fold_right iquantify1 ft qs.

  Definition fun_of_qfun (qfun : qfun_ty) : Core.function_type :=
    let '(QFun qs iqs τs1 τs2) := qfun in
    quantify qs (InnerFunT (iquantify iqs (MonoFunT τs1 τs2))).

  Lemma qfun_iso1 (ft : Core.function_type) :
     fun_of_qfun (qfun_of_fun ft) = ft.
  Proof.
  Admitted.

  Definition add_quant (q : quant) (F : function_ctx) : function_ctx :=
    match q with
    | QMem => F <| fc_kind_ctx ::= set kc_mem_vars S |>
    | QRep => F <| fc_kind_ctx ::= set kc_rep_vars S |>
    | QSize => F <| fc_kind_ctx ::= set kc_size_vars S |>
    end.

  Definition flatten_quants (qs : list quant) (F : function_ctx) : function_ctx :=
    fold_right add_quant F qs.

  Definition add_iquant (q : iquant) (F : function_ctx) : function_ctx :=
    match q with
    | QType κ => F <| fc_type_vars ::= λ x, app x [κ] |>
    end.

  Definition flatten_iquants (qs : list iquant) (F : function_ctx) : function_ctx :=
    fold_right add_iquant F qs.

  Definition flatten_qs (qs : list quant) (iqs : list iquant) (F : function_ctx) : function_ctx :=
    flatten_quants qs (flatten_iquants iqs F).

  Definition flatten_qfun (ft : qfun_ty) (F : function_ctx):=
    let '(QFun qs iqs _ _) := ft in
    flatten_qs qs iqs F.

  Definition quantify1_interp (q : quant) : (semantic_env (Σ := Σ) -n> ClR) -n> (semantic_env -n> ClR) :=
    match q with
    | QMem => forall_mem_interp
    | QRep => forall_rep_interp
    | QSize => forall_size_interp
    end.

  Definition quantify_interp (qs : list quant) (FT : semantic_env (Σ := Σ) -n> ClR) : semantic_env -n> ClR :=
    fold_right quantify1_interp FT qs.

  Definition iquantify1_interp (q : iquant) :=
    match q with
    | QType κ => forall_type_interp rti sr κ
    end.

  Definition iquantify_interp (qs : list iquant) (FT : semantic_env (Σ := Σ) -n> ClR) : semantic_env -n> ClR :=
    fold_right iquantify1_interp FT qs.

  Definition qclosure_interp (ft : qfun_ty) :=
    let '(QFun qs iqs τs1 τs2) := ft in
    let Ts1 := map (type_interp rti sr) τs1 in
    let Ts2 := map (type_interp rti sr) τs2 in
    quantify_interp qs (iquantify_interp iqs (mono_closure_interp rti sr τs1 τs2 Ts1 Ts2)).

  Lemma iquantify_interp_ok iqs ts1 ts2 se cl :
    let Ts1 := map (type_interp rti sr) ts1 in
    let Ts2 := map (type_interp rti sr) ts2 in
    iquantify_interp iqs (mono_closure_interp rti sr ts1 ts2 Ts1 Ts2) se cl
    ⊣⊢ inner_closure_interp rti sr (iquantify iqs (MonoFunT ts1 ts2)) se cl.
  Proof.
    intros Ts1 Ts2.
    setoid_rewrite inner_closure_interp_eq.
    revert se.
    induction iqs as [| [κ] iqs ]; first done.
    intros.
    cbn.
    setoid_rewrite IHiqs.
    setoid_rewrite inner_closure_interp_eq.
    reflexivity.
  Qed.

  Lemma qclosure_interp_ok_aux qs iqs ts1 ts2 se cl :
    let Ts1 := map (type_interp rti sr) ts1 in
    let Ts2 := map (type_interp rti sr) ts2 in
    quantify_interp qs (iquantify_interp iqs (mono_closure_interp rti sr ts1 ts2 Ts1 Ts2)) se cl
    ⊣⊢ closure_interp rti sr (quantify qs (InnerFunT (iquantify iqs (MonoFunT ts1 ts2)))) se cl.
  Proof.
    intros Ts1 Ts2.
    setoid_rewrite closure_interp_eq.
    revert se.
    induction qs as [| [ | | ] qs ].
    - cbn.
      intros se.
      rewrite iquantify_interp_ok inner_closure_interp_eq.
      done.
    - intros se; cbn;
      setoid_rewrite IHqs;
      by setoid_rewrite closure_interp_eq.
    - intros se; cbn;
      setoid_rewrite IHqs;
      by setoid_rewrite closure_interp_eq.
    - intros se; cbn;
      setoid_rewrite IHqs;
      by setoid_rewrite closure_interp_eq.
  Qed.

  Lemma qclosure_interp_ok qf se cl :
    qclosure_interp qf se cl ⊣⊢ closure_interp rti sr (fun_of_qfun qf) se cl.
  Proof.
    destruct qf as [qs iqs ts1 ts2].
    cbn.
    by rewrite qclosure_interp_ok_aux.
  Qed.

  Definition flat_q (q : quant) (ff : flat_function_type) : flat_function_type :=
    match q with
    | QMem => ff <| fft_mem_vars ::= S |>
    | QRep => ff <| fft_rep_vars ::= S |>
    | QSize => ff <| fft_size_vars ::= S|>
    end.

  Fixpoint flat_qs (qs : list quant) (ff : flat_function_type) : flat_function_type :=
    fold_right flat_q ff qs.

  Definition flat_iq (q : iquant) (ff : flat_function_type) : flat_function_type :=
    let 'QType k := q in
    ff <| fft_type_vars ::= app [k] |>.

  Fixpoint flat_iqs (qs : list iquant) (ff : flat_function_type) : flat_function_type :=
    fold_right flat_iq ff qs.

  Definition flat_mono ts1 ts2 :=
    {| fft_mem_vars := 0;
       fft_rep_vars := 0;
       fft_size_vars := 0;
       fft_type_vars := [];
       fft_in := ts1;
       fft_out := ts2 |}.

  Definition flat_qfun '(QFun qs iqs ts1 ts2 : qfun_ty) : flat_function_type :=
    flat_qs qs (flat_iqs iqs (flat_mono ts1 ts2)).

  Lemma flatten_iquantify iqs ts1 ts2 :
    flatten_inner_function_type (iquantify iqs (MonoFunT ts1 ts2)) = flat_iqs iqs (flat_mono ts1 ts2).
  Proof.
  Admitted.

  Lemma flatten_quantify qs ϕ :
    flatten_function_type (quantify qs (InnerFunT ϕ)) = flat_qs qs (flatten_inner_function_type ϕ).
  Admitted.

  Lemma flat_qfun_is_flatten ϕ :
    flatten_function_type (fun_of_qfun ϕ) = flat_qfun ϕ.
  Proof.
    destruct ϕ.
    cbn.
    by rewrite -flatten_iquantify -flatten_quantify.
  Qed.

  (*
  Lemma flat_iqs_clos iqs ts1 ts2 cl se FT :
    let Ts1 := map (type_interp rti sr) ts1 in
    let Ts2 := map (type_interp rti sr) ts2 in
    flat_closure_interp_wk (flat_iqs iqs (flat_mono ts1 ts2)) se cl FT -∗
    iquantify_interp iqs FT se cl.
  Proof.
    intros Ts1 Ts2.
    unfold flat_closure_interp, flat_closure_interp_wk, iquantify_interp.
    revert se FT.
    induction iqs using rev_ind; intros *.
    - cbn [flat_iqs foldr flat_mono fft_in fft_out].
      iIntros "#Hok".
      iSpecialize ("Hok" $! senv_empty).
      replace (senv_insert_all senv_empty se)
        with (se) by admit.
      by iApply "Hok".
    - destruct x as [k].
      iIntros "#Hok".
      rewrite foldr_snoc.
      iApply IHiqs.
      iIntros "!> %se' %Hflat %sks %Hev %Hall".
      iIntros "!> %sk %sk_T %T %Hev' %Hsub' %Hty".
      iSpecialize ("Hok" $! (senv_insert_type sk_T T se')).
      replace (senv_insert_all (senv_insert_type sk_T T se') se)
      with (senv_insert_type sk_T T (senv_insert_all se' se)) by admit.
      iApply "Hok".
      + admit.
      + admit.
  Admitted.

  (*
  Print sem_env_interp.
  Definition sem_env_qs_interp (qs : list quant) se : Prop := *)

  Lemma flat_qclos ϕ cl :
    flat_closure_interp (flat_qfun ϕ) senv_empty cl -∗
    qclosure_interp ϕ senv_empty cl.
  Proof.
  Admitted.
   *)

  Theorem fundamental_function ϕ : ∀ M wt wt' wtf mf mf',
    has_function_type M mf ϕ ->
    compile_function wt mf = inr (wt', mf') ->
    ⊢ has_func_type_sem rti sr module.mr M (wt ++ wt' ++ wtf) mf' ϕ.
  Proof.
    (* TODO: By induction on ϕ, build up an se such that sem_env_interp F se.
             Then use the fundamental theorem for instruction typing to show that the body of the
             function is well-behaved. *)
    unfold compile_function.
    intros * Hty Hcf.

    eapply bind_inr in Hcf.
    destruct Hcf as (ft & Hft & Hcf).
    destruct (insert_type wt ft) as [wt_tid tid] eqn:Hadd_ty.
    eapply bind_inr in Hcf.
    destruct Hcf as (fe & Hfe & Hcf).
    eapply bind_inr in Hcf.
    destruct Hcf as (ιs & Hevrep & Hcf).
    eapply bind_inr in Hcf.
    destruct Hcf as ([[[[] ft'] wl''] body] & Hcg & Hret).
    inversion Hret; subst; clear Hret.

    inversion Hty; subst.

    assert (fe = fe_of_context F).
    {
      (* annoying, might want to change some definitions here. *)
      admit.
    }
    subst fe.
    eapply fundamental_typing with (rti := rti) (sr := sr) (wtf := wtf) in H3; eauto.
    unfold has_func_type_sem.
    iIntros (inst tf Hinst) "Hinst".
    cbn.
    subst ϕ1 ϕ0.
    remember (mf_type mf) as ϕ in *.
    (*
    iAssert (flat_closure_interp (flatten_function_type ϕ) senv_empty (FC_func_native inst tf (flat_map (map translate_arep) ιs ++ wl'') body)) as "U".
    {
      unfold flat_closure_interp, flat_closure_interp_wk.
      iIntros "!> %se' %Hflat %sks %Hevk %Hall".
      unfold mono_closure_interp.
      destruct tf as [ts1 ts2].
      cbn -[atoms_interp type_interp translate_types].
      iSplit.
      { admit. }
      iSplit.
      { admit. }
      iIntros "!> !> %vs1 %os1 %θ Hats Hoss Htok Hinv Hf Hr".
      unfold have_instr_type_sem in H3.
      change body with ([] ++ body).
      iApply cwp_wand.
      { iApply H3; admit. }
      admit.
    }
    assert (ηss_L = map (map arep_to_prim) ιs) by admit.
    set (wta := (wt ++ (option_list wt_tid ++ ft') ++ wtf)) in *.
    clear_nils.
    rewrite <- (qfun_iso1 ϕ).
    iApply qclosure_interp_ok.
    rewrite flat_qfun_is_flatten.
    by iApply flat_qclos.
  *)
  Admitted.

End function.
