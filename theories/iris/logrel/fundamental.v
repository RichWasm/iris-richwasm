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

From RichWasm.iris.helpers Require Export iris_properties.
From RichWasm.iris.language Require Export iris_atomicity lenient_wp lwp_pure lwp_structural lwp_resources lwp_trap.
From RichWasm.iris.rules Require Export iris_rules.

From RichWasm Require Import syntax typing.
From RichWasm.compiler Require Import codegen instrs modules types util.
From RichWasm.iris Require Import autowp gc num_reprs util.
From RichWasm.iris.logrel Require Import relations util.
From RichWasm.util Require Import debruijn stdpp_extlib.

Module RT := RichWasm.syntax.
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
  Context `{!RichWasmGCG Σ}.

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

  Lemma compiler_wctx_mono M es es' wl wl' x :
    run_codegen (compile_instrs M es) wl = inr (x, wl', es') ->
    wl `prefix_of` wl'.
  Proof.
  Admitted.

  Theorem fundamental_property M F L L' me es es' tf wl wl' :
    instrs_have_type M F L es tf L' ->
    run_codegen (compile_instrs me es) wl = inr (tt, wl', es') ->
    ⊢ has_type_semantic sr M F L wl' (to_e_list es') tf L'.
  Proof.
    intros Htyp Hcomp.
    generalize dependent es'.
    induction Htyp using instrs_have_type_mind with
      (P := fun C F L e ta L' _ => forall es',
      run_codegen (compile_instr me e) wl = inr (tt, wl', es') ->
      ⊢ has_type_semantic sr C F L [] (to_e_list es') ta L');
    intros es' Hcomp; admit.
  Admitted.

  (*
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

  (*
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
*)

*)
End Fundamental.
