From mathcomp Require Import ssreflect ssrbool eqtype seq.

From stdpp Require Import base fin_maps option list.

From ExtLib.Structures Require Import Monads.
From ExtLib.Data.Monads Require Import StateMonad.

From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import list.
From iris.prelude Require Import options.

From Wasm.iris.helpers Require Export iris_properties.
From Wasm.iris.language Require Export iris_atomicity.
From Wasm.iris.rules Require Export iris_rules.
From Wasm.iris.logrel Require iris_logrel.

From RichWasm Require Import subst term typing.
From RichWasm.compiler Require Import codegen instrs modules types util.
From RichWasm.iris Require Import autowp gc num_reprs util.
From RichWasm.iris.logrel Require Import relations util.
From RichWasm.util Require Import debruijn stdpp_extlib.

Module RT := RichWasm.term.
Module T := RichWasm.typing.

Import uPred.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "1".

Ltac fill_vals_pred' vs :=
  instantiate ( 1 := (λ w, ⌜w = vs⌝ ∗ _)%I).

Ltac curry_hyps :=
  iRevert "∗";
  rewrite ? wand_curry.

Ltac fill_goal :=
  match goal with
  | |- environments.envs_entails _ ?E =>
      is_evar E;
      curry_hyps;
      try (iApply wand_refl; solve_constraints);
      instantiate (1:= ⌜True⌝%I); done
  end.

Ltac fill_vals_pred :=
  match goal with
  | |- environments.envs_entails _ (?g ?vs) =>
      fill_vals_pred' vs; iSplitR; [done | fill_goal]
  end.

Section Fundamental.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!rwasm_gcG Σ}.

  Variable sr : store_runtime.

  Lemma seq_map_map {A B} (f : A -> B) (l : list A) : seq.map f l = map f l.
  Admitted.

  Lemma Forall3_to_zip12
    {X Y Z: Type}
    (R: X -> Y -> Z -> Prop)
    xs ys zs :
    Forall3 R xs ys zs ->
    Forall2 (fun '(x, y) z => R x y z) (zip xs ys) zs.
  Admitted.

  Lemma Forall3_to_zip23
    {X Y Z: Type}
    (R: X -> Y -> Z -> Prop)
    xs ys zs :
    Forall3 R xs ys zs ->
    Forall2 (fun x '(y, z) => R x y z) xs (zip ys zs).
  Admitted.

  Lemma Forall3_from_zip12
    {X Y Z: Type}
    (R: X -> Y -> Z -> Prop)
    xs ys zs :
    length xs = length ys ->
    Forall2 (fun '(x, y) z => R x y z) (zip xs ys) zs ->
    Forall3 R xs ys zs.
  Proof.
  Admitted.

  Lemma Forall2_Forall3_mp2
    {A B C D : Type}
    (R : A -> B -> Prop)
    (P : C -> B -> D -> Prop)
    (l1 : list A)
    (l2 : list B)
    (l3 : list C)
    (l4 : list D) :
    Forall2 R l1 l2 ->
    Forall3 (fun x y z => forall a, R y a -> P x a z) l3 l1 l4 ->
    Forall3 (fun x a z => P x a z) l3 l2 l4.
  Proof.
  Admitted.

  Lemma compiler_wctx_mono M F es es' wl wl' x :
    run_codegen (compile_instrs M F es) wl = inr (x, wl', es') ->
    wl `prefix_of` wl'.
  Proof.
  Admitted.

  Lemma compat_struct_get M F L me fe ty cap l hty taus szs i es wl wl' :
    hty = StructType (combine taus szs) ->
    HasTypeInstr M F L
      (IStructGet (Arrow [RefT cap l hty] [RefT cap l hty; ty], LSig L L) i)
      (Arrow [RefT cap l hty] [RefT cap l hty; ty]) L ->
    run_codegen (compile_instr me fe
                   (IStructGet (Arrow [RefT cap l hty] [RefT cap l hty; ty], LSig L L) i)) wl =
    inr (tt, wl', es) ->
    ⊢ semantic_typing sr M F L [] (to_e_list es) (Arrow [RefT cap l hty] [RefT cap l hty; ty]) L.
  Proof.
    intros -> Htype Hcomp.
    iIntros "%inst %lh [Hinst Hctx] %f %vs [Hval Hfr]".
    rewrite interp_expr_eq.
    rewrite interp_frame_eq.
    iDestruct "Hval" as "[-> | (%vs' & -> & Hval)]".
    - (* trap *)
      admit.
    - iDestruct "Hval" as "(%vss & %Hvs' & Hval)".
      simpl in Hvs'. subst vs'.
      iPoseProof (big_sepL2_length with "[$Hval]") as "%Hlens".
      destruct vss as [|vs vss]; cbn in Hlens; first discriminate Hlens.
      destruct vss; cbn in Hlens; try discriminate Hlens. clear Hlens.
      rewrite big_sepL2_singleton.
      setoid_rewrite interp_value_phys_eq.
      cbn.
      setoid_rewrite app_nil_r.
      destruct l; first by iExFalso.

      (* Break the typing judgment apart. *)
      inversion Htype.
      subst C F0 L0 psi cap0 l tau n.
      rewrite <- H1 in *.
      clear taus szs Htype H1 H3 H2 H4 H11.
      rename taus0 into tys, szs0 into szs, H9 into Htys_szs_len, H12 into Htys_i, H13 into Hunr,
             H14 into HL_valid, H15 into Hhty_valid, H16 into Hty_valid, H17 into Hqual_valid.

      (* Break the compiler apart. *)
      unfold compile_instr, compile_struct_get in Hcomp.
      apply run_codegen_bind_dist in Hcomp.
      destruct Hcomp as (x1 & wl1 & es1 & es2 & Hcomp1 & Hcomp2 & Hes).
      cbn in Hcomp1.
      inversion Hcomp1.
      subst x1 wl1 es es1.
      clear Hcomp1.
      rewrite combine_split in Hcomp2; last assumption.
      rewrite <- nth_error_lookup in Hcomp2.
      rewrite Htys_i in Hcomp2.
      unfold try_option in Hcomp2.
      apply run_codegen_bind_dist in Hcomp2.
      destruct Hcomp2 as (field_ty & wl2 & es3 & es4 & Hcomp2 & Hcomp3 & Hes2).
      cbn in Hcomp2.
      inversion Hcomp2.
      subst field_ty wl2 es2 es3.
      clear Hcomp2.
      apply run_codegen_bind_dist in Hcomp3.
      destruct Hcomp3 as (offset & wl3 & es5 & es6 & Hcomp3 & Hcomp4 & Hes4).
      subst es4.
      apply run_codegen_lift_error_inr in Hcomp3.
      destruct Hcomp3 as (Hoffset & Hwl & Hes5).
      subst wl3 es5.
      apply run_codegen_bind_dist in Hcomp4.
      destruct Hcomp4 as (x4 & wl4 & es7 & es8 & Hcomp4 & Hcomp5 & Hes6).
      cbn in Hcomp4.
      inversion Hcomp4.
      subst x4 wl4 es6 es7.
      clear Hcomp4.
      apply run_codegen_bind_dist in Hcomp5.
      destruct Hcomp5 as (x5 & wl5 & es9 & es10 & Hcomp5 & Hcomp6 & Hes8).
      subst es8.
      apply run_codegen_bind_dist in Hcomp6.
      destruct Hcomp6 as (val & wl6 & es11 & es12 & Hcomp6 & Hcomp7 & Hes10).
      subst es10.
      apply run_codegen_bind_dist in Hcomp7.
      destruct Hcomp7 as (x7 & wl7 & es13 & es14 & Hcomp7 & Hcomp8 & Hes12).
      cbn in Hcomp7.
      inversion Hcomp7.
      subst x7 wl7 es12 es13.
      clear Hcomp7.
      apply run_codegen_bind_dist in Hcomp8.
      destruct Hcomp8 as (x8 & wl8 & es15 & es16 & Hcomp8 & Hcomp9 & Hes14).
      subst es14.
      destruct x5, x8 as [[] []].
      iSimpl.
      rename Hcomp5 into Hcomp1, Hcomp6 into Hcomp2, Hcomp8 into Hcomp3, Hcomp9 into Hcomp4,
             wl5 into wl1, wl6 into wl2, wl8 into wl3, es9 into es1, es11 into es2, es15 into es3,
             es16 into es4.

      destruct m.
      + (* GC *)
        admit.
      + (* MM *)
        admit.
  Admitted.

  Theorem fundamental_property M F L L' me fe es es' tf wl wl' :
    HasTypeInstrs M F L es tf L' ->
    run_codegen (compile_instrs me fe es) wl = inr (tt, wl', es') ->
    ⊢ semantic_typing sr M F L wl' (to_e_list es') tf L'.
  Proof.
    intros Htyp Hcomp.
    generalize dependent es'.
    induction Htyp using HasTypeInstrs_mind with (P := fun C F L e ta L' _ =>
      forall es',
      run_codegen (compile_instr me fe e) wl = inr (tt, wl', es') ->
      ⊢ semantic_typing sr C F L [] (to_e_list es') ta L');
    intros es' Hcomp.
    - (* INumConst *)
      admit.
    - (* IUnit *)
      admit.
    - (* INum *)
      admit.
    - (* IUnreachable *)
      admit.
    - (* INop *)
      admit.
    - (* IDrop *)
      admit.
    - (* IBlock *)
      admit.
    - (* ILoop *)
      admit.
    - (* IIte *)
      admit.
    - (* IBr *)
      admit.
    - (* IBrIf *)
      admit.
    - (* IBrTable *)
      admit.
    - (* IRet *)
      admit.
    - (* IGetLocal *)
      admit.
    - (* ISetLocal *)
      admit.
    - (* IGetGlobal *)
      admit.
    - (* ISetGlobal *)
      admit.
    - (* ICoderef *)
      admit.
    - (* ICallIndirect *)
      admit.
    - (* ICall *)
      admit.
    - (* IRecFold *)
      admit.
    - (* IRecUnfold *)
      admit.
    - (* IGroup *)
      admit.
    - (* IUngroup *)
      admit.
    - (* ICapSplit *)
      admit.
    - (* ICapJoin *)
      admit.
    - (* IRefDemote *)
      admit.
    - (* IMemPack *)
      admit.
    - (* IMemUnpack *)
      admit.
    - (* IStructMalloc *)
      admit.
    - (* IStructFree *)
      admit.
    - (* IStructGet *)
      eapply compat_struct_get with (i := n).
      + reflexivity.
      + apply TStructGet; assumption.
      + exact Hcomp.
    - (* IStructSet *)
      admit.
    - (* IStructSwap *)
      admit.
    - (* IVariantMalloc *)
      admit.
    - (* IVariantCase - Unrestricted *)
      admit.
    - (* IVariantCase - Linear *)
      admit.
    - (* IArrayMalloc *)
      admit.
    - (* IArrayGet *)
      admit.
    - (* IArraySet *)
      admit.
    - (* IArrayFree *)
      admit.
    - (* IExistPack *)
      admit.
    - (* IExistUnpack - Unrestricted *)
      admit.
    - (* IExistUnpack - Linear *)
      admit.
    - (* IRefSplit *)
      admit.
    - (* IRefJoin *)
      admit.
    - (* Empty *)
      admit.
    - (* Cons *)
      admit.
  Admitted.

  Notation "{{{{ P }}}} es {{{{ v , Q }}}}" :=
    (□ ∀ Φ, P -∗ (∀ v : iris.val, Q -∗ Φ v) -∗ WP (es : iris.expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).

  Notation "{{{{ P }}}} es @ E {{{{ v , Q }}}}" :=
    (□ ∀ Φ, P -∗ (∀ v : iris.val, Q -∗ Φ v) -∗ (WP (es : iris.expr) @ NotStuck ; E {{ v, Φ v }}))%I (at level 50).

  Definition if_spec tf e_then e_else k φ ψ f : ⊢
    {{{{ ⌜k ≠ Wasm_int.int_zero i32m⌝ ∗ φ ∗ ↪[frame] f }}}}
      [AI_basic (BI_block tf e_then)]
    {{{{ w, ψ w }}}} -∗
    {{{{ ⌜k = Wasm_int.int_zero i32m⌝ ∗ φ ∗ ↪[frame] f }}}}
      [AI_basic (BI_block tf e_else)]
    {{{{ w, ψ w }}}} -∗
    {{{{ φ ∗ ↪[frame] f }}}}
      to_e_list [BI_const (VAL_int32 k); BI_if tf e_then e_else]
    {{{{ w, ψ w }}}}.
  Proof.
    iIntros "#Hthen #Helse !>" (Φ) "[Hφ Hfr] HΦ".
    destruct (k == Wasm_int.int_zero i32m) eqn:Heq; move/eqP in Heq.
    - iApply (wp_if_false with "[$Hfr]") => //.
      iIntros "!> Hfr".
      iApply ("Helse" with "[$Hfr $Hφ //] [$]").
    - iApply (wp_if_true with "[$Hfr]") => //.
      iIntros "!> Hfr".
      iApply ("Hthen" with "[$Hfr $Hφ //] [$]").
  Qed.

  Lemma wp_take_drop {E ϕ es} n:
    WP es @ E {{ w, ϕ w }} ⊣⊢
    WP (take n es) ++ (drop n es) @ E {{ w, ϕ w }}.
  Proof.
    by rewrite (take_drop n es).
  Qed.

  Lemma even_iff_land1:
    forall p: positive,
      ((2 | p) <-> Pos.land p 1 = 0%N)%positive.
  Proof using.
    clear Σ logrel_na_invs0 wasmG0 rwasm_gcG0 sr.
    induction p; (split; [intros Hdiv| intros Hand]).
    - destruct Hdiv as [p' Hp'].
      lia.
    - unfold Pos.land in Hand.
      lia.
    - reflexivity.
    - exists p.
      lia.
    - inversion Hdiv.
      lia.
    - inversion Hand.
  Qed.

  Lemma odd_iff_land1:
    forall p: positive,
      (¬(2 | p) <-> Pos.land p 1 = 1%N)%positive.
  Proof using.
    clear Σ logrel_na_invs0 wasmG0 rwasm_gcG0 sr.
    induction p; (split; [intros Hdiv| intros Hand]).
    - reflexivity.
    - intros [d Hdiv].
      lia.
    - exfalso; apply Hdiv.
      exists p; lia.
    - inversion Hand.
    - reflexivity.
    - intros [d Hdiv].
      lia.
  Qed.

  Lemma gc_ptr_parity ℓ l32:
    ptr_repr (LocP ℓ GCMem) l32 ->
    wasm_bool (Wasm_int.Int32.eq Wasm_int.Int32.zero (Wasm_int.Int32.iand l32 (Wasm_int.Int32.repr 1))) = Wasm_int.int_zero i32m.
  Proof.
    clear Σ logrel_na_invs0 wasmG0 rwasm_gcG0 sr.
    unfold ptr_repr, word_aligned, Wasm_int.Int32.iand, Wasm_int.Int32.and, Z.land.
    intros [Hrepr Hdiv].
    cbn.
    assert (¬ (2 | Wasm_int.Int32.unsigned l32))%Z.
    {
      destruct Hrepr as [Hbdd Hconv].
      destruct l32; cbn in *.
      rewrite -(Z2N.id intval); [| lia].
      rewrite -Hconv.
      rewrite N2Z.inj_add.
      cbn.
      intros [ℓ' Hev].
      destruct Hdiv; subst ℓ.
      lia.
    }
    destruct (Wasm_int.Int32.unsigned l32) as [|p32|q32] eqn:Hl32.
    - destruct Hrepr as [Hbdd Hconv].
      destruct l32; cbn in *.
      rewrite Hl32 in Hconv.
      lia.
    - replace (Pos.land p32 1) with 1%N; [done |].
      symmetry.
      eapply odd_iff_land1.
      by rewrite Z.divide_Zpos in H.
    - destruct Hrepr as [Hbdd Hconv].
      destruct l32; cbn in *.
      rewrite Hl32 in Hconv.
      lia.
  Qed.

  Lemma lin_ptr_parity ℓ l32:
    ptr_repr (LocP ℓ LinMem) l32 ->
    wasm_bool (Wasm_int.Int32.eq Wasm_int.Int32.zero (Wasm_int.Int32.iand l32 (Wasm_int.Int32.repr 1))) <> Wasm_int.int_zero i32m.
  Proof.
    clear Σ logrel_na_invs0 wasmG0 rwasm_gcG0 sr.
    unfold ptr_repr, word_aligned, Wasm_int.Int32.iand, Wasm_int.Int32.and, Z.land.
    intros [Hrepr Hdiv].
    cbn.
    assert (2 | Wasm_int.Int32.unsigned l32)%Z.
    {
      destruct Hrepr as [Hbdd Hconv].
      destruct l32; cbn in *.
      destruct Hdiv as [d Hdiv].
      exists (Z.of_N d * 2)%Z.
      lia.
    }
    destruct (Wasm_int.Int32.unsigned l32) as [|p32|q32] eqn:Hl32.
    - done.
    - replace (Pos.land p32 1) with 0%N; [done |].
      symmetry.
      eapply even_iff_land1.
      by rewrite Z.divide_Zpos in H.
    - destruct l32; cbn in *; lia.
  Qed.

  Definition gc_bit_set_spec E ref_tmp ins outs gc_branch lin_branch wl wl' es ψ f ℓ l32 :
    f.(f_locs) !! ref_tmp = Some (VAL_int32 l32) ->
    ptr_repr (LocP ℓ GCMem) l32 ->
    run_codegen (emit (BI_get_local ref_tmp);;
                 if_gc_bit (W.Tf ins outs)
                   (tell gc_branch)
                   (tell lin_branch);;
                 ret tt)
                wl = inr (wl', es) ->
    ⊢ ↪[frame] f -∗
      ▷ (↪[frame] f -∗ WP [AI_basic (BI_block (Tf ins outs) gc_branch)] @ E {{ w, ψ w }}) -∗
      WP to_e_list es @ E {{ w, ψ w }}.
  Proof.
    intros Href Hrepr Hcomp.
    iIntros "Hfr Hbranch".

    cbn in Hcomp.
    inversion Hcomp.
    subst wl' es.
    clear Hcomp.
    rewrite !app_nil_r.

    iAssert emp%I as "HΦ";[done|].
    next_wp.
    {
      iApply (wp_wand with "[Hfr]").
      {
        iApply (wp_get_local with "[] [$Hfr]"); eauto.
        fill_imm_pred.
      }
      iIntros (v) "(%Hv & Hfr)".
      iFrame.
      iExists [VAL_int32 l32].
      iSplit; [auto|].
      iSplit; [auto|].
      fill_vals_pred.
    }
    cbn.
    iDestruct select (_ ∗ _)%I as "(%Hv & Hφ)".
    inversion Hv; clear Hv; subst v.
    next_wp.
    {
      iApply (wp_binop with "[$Hfr]").
      eauto.
      iIntros "!>".
      iExists _.
      iSplit; [auto|].
      iSplit; [auto|].
      fill_vals_pred.
    }
    cbn.
    iDestruct select (_ ∗ _)%I as "(%Hv & Hφ)".
    inversion Hv; clear Hv; subst v.
    next_wp.
    {
      iApply (wp_testop_i32 with "[$Hfr]").
      eauto.
      iIntros "!>".
      iExists _.
      iSplit; [eauto|].
      iSplit; [eauto|].
      fill_vals_pred.
    }
    {
      cbn.
      iDestruct select (_ ∗ _)%I as "(%Hv & Hφ)".
      inversion Hv; subst v; clear Hv.
      apply gc_ptr_parity in Hrepr.
      rewrite Hrepr.
      iApply (wp_if_false with "[$Hfr]").
      auto.
      iIntros "!> Hfr".
      iApply ("Hφ" with "[$]").
    }
    - iIntros "((%vs & %Heq & _) & _)"; congruence.
    - iIntros "((%vs & %Heq & _) & _)"; congruence.
    - iIntros "((%vs & %Heq & _) & _)"; congruence.
  Qed.

  Lemma read_value_deserialize_i32 sgn b i:
    deserialize_values b (Num (Int sgn RT.i32)) = [VAL_int32 i] ->
    wasm_deserialise b T_i32 = VAL_int32 i.
  Proof.
  Admitted.

  Definition gc_bit_not_set_spec E ref_tmp ins outs gc_branch lin_branch wl wl' es es' ψ f ℓ l32 :
    f.(f_locs) !! ref_tmp = Some (VAL_int32 l32) ->
    ptr_repr (LocP ℓ LinMem) l32 ->
    run_codegen (emit (BI_get_local ref_tmp);;
                 if_gc_bit (W.Tf ins outs)
                   (tell gc_branch)
                   (tell lin_branch);;
                 ret tt)
                wl = inr (wl', es) ->
    to_e_list es = es' ->
    ⊢ ↪[frame] f -∗
      ▷(↪[frame] f -∗ WP [AI_basic (BI_block (Tf ins outs) lin_branch)] @ E {{ w, ψ w }}) -∗
      WP es' @ E {{ w, ψ w }}.
  Proof.
    intros Href Hrepr Hcomp Hes.
    iIntros "Hfr Hφ".

    cbn in Hcomp.
    inversion Hcomp.
    subst wl' es.
    clear Hcomp.
    subst es'.
    rewrite !app_nil_r.

    cbn.
    iAssert emp%I as "HΦ"; [done|].
    next_wp.
    {
      iApply (wp_wand with "[Hfr]").
      {
        iApply (wp_get_local with "[] [$Hfr]"); eauto.
        fill_imm_pred.
      }
      iIntros (v) "(%Hv & Hfr)".
      iFrame.
      iExists [VAL_int32 l32].
      iSplit; [auto|].
      iSplit; [auto|].
      fill_vals_pred.
    }
    cbn.
    iDestruct select (_ ∗ _)%I as "(%Hv & Hφ)".
    inversion Hv; clear Hv; subst v.
    next_wp.
    {
      iApply (wp_binop with "[$Hfr]").
      eauto.
      iIntros "!>".
      iExists _.
      iSplit; [auto|].
      iSplit; [auto|].
      fill_vals_pred.
    }
    cbn.
    iDestruct select (_ ∗ _)%I as "(%Hv & Hφ)".
    inversion Hv; clear Hv; subst v.
    next_wp.
    {
      iApply (wp_testop_i32 with "[$Hfr]").
      eauto.
      iIntros "!>".
      iExists _.
      iSplit; [eauto|].
      iSplit; [eauto|].
      fill_vals_pred.
    }
    {
      cbn.
      iDestruct select (_ ∗ _)%I as "(%Hv & Hφ)".
      inversion Hv; subst v; clear Hv.
      pose proof (lin_ptr_parity _ _ Hrepr) as Hnz.
      iApply (wp_if_true with "[$Hfr]").
      apply Hnz.
      iIntros "!> Hfr".
      iApply ("Hφ" with "[$]").
    }
    - iIntros "((%vs & %Heq & _) & _)"; congruence.
    - iIntros "((%vs & %Heq & _) & _)"; congruence.
    - iIntros "((%vs & %Heq & _) & _)"; congruence.
  Qed.

  Lemma byte_div_repr b bs:
    Integers.Byte.repr (Integers.Byte.unsigned b + Memdata.int_of_bytes bs * 256) = b.
  Proof.
  Admitted.

  Lemma byte_div_skip b bs:
    ((Integers.Byte.unsigned b + Memdata.int_of_bytes bs * 256) `div` 256)%Z = Memdata.int_of_bytes bs.
  Proof.
  Admitted.

  Lemma encode_decode_int :
    forall sz bs,
      length bs = sz ->
      Memdata.encode_int sz (Memdata.decode_int bs) = bs.
  Proof.
    clear Σ logrel_na_invs0 wasmG0 rwasm_gcG0 sr.
    induction sz; intros bs Hlen.
    - destruct bs; simpl in Hlen; try lia.
      reflexivity.
    - destruct bs as [| b bs]; inversion Hlen.
      revert IHsz.
      unfold Memdata.encode_int, Memdata.decode_int.
      unfold Memdata.rev_if_be.
      Transparent Archi.big_endian.
      unfold Archi.big_endian.
      Opaque Archi.big_endian.
      intros IH.
      cbn.
      f_equal.
      + apply byte_div_repr.
      + rewrite <- IH by auto.
        rewrite byte_div_skip.
        congruence.
  Qed.

End Fundamental.
