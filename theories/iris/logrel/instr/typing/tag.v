Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.numerics.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section tag.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_tag M F L wt wt' wtf wl wl' wlf es' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [type_i32] [type_i31] in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ITag ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmask ψ Hok Hcg.

    cbn in Hcg; inversion Hcg; subst; clear Hcg.

    iIntros (??????????) "@@@@@@@@@@".
    iEval (rewrite values_interp_one_eq) in "Hos".
    iPoseProof (value_interp_i32 with "Hos") as "[%n %Hos]".
    subst os.
    iEval (rewrite atoms_interp_one_inv) in "Hvs".
    iDestruct "Hvs" as "[%v [-> Hvs]]".
    iEval (cbn) in "Hvs".
    iDestruct "Hvs" as "->".

    (* need to show evs is a number *)
    apply has_values_to_consts_inv in H0.
    cbn in H0. subst evs.
    change ([?x]++[?y;?z]) with ([x;y;z]).

    iApply (cwp_binop with "[$Hfr] [$Hrun]").
    - by cbn.
    - iFrame. iModIntro.
      iSplitR; auto.
      set (nN := Wasm_int.N_of_uint i32m n).
      assert (N_i32_repr nN n) by reflexivity.
      (* wrapped to 2^31 *)
      set (n_wr := (nN `mod` (2 ^ 31))%N).
      iExists [PtrA (PtrInt n_wr)].
      iSplitL.
      + iApply values_interp_one_eq.
        iApply value_interp_eq.
        iExists (SVALTYPE [PtrR] NoRefs).
        iPureIntro.
        repeat split; auto.
        * eexists; split; auto.
          apply Forall2_cons; split; [|by apply Forall2_nil].
          by cbn.
        * eexists; split; auto.
          apply Forall_cons; split; [|by apply Forall_nil].
          by cbn.
      + cbn.
        iSplit; auto.
        iExists (2 * n_wr)%N, _; iSplit; [|iSplit]; [| eauto | ].
        * iPureIntro.
          unfold Wasm_int.Int32.ishl; cbn.
          unfold Wasm_int.Int32.shl.
          cbn.
          rewrite Z.shiftl_mul_pow2; last done.
          rewrite Z.pow_1_r.
          unfold N_i32_repr, n_wr, Wasm_int.Int32.repr; cbn.
          rewrite Wasm_int.Int32.Z_mod_modulus_eq.
          change Wasm_int.Int32.modulus with (2^31 * 2)%Z.
          rewrite Zmult_mod_distr_r.
          replace (2%N) with (Z.to_N 2%Z) by done.
          rewrite Z.mul_comm.
          rewrite Z2N.inj_mul; try lia.
          {
            f_equal.
            destruct n; cbn.
            rewrite Z2N.inj_mod; auto; lia.
          }
          by apply Z.mod_pos.
        * iExists (RootInt n_wr).
          iPureIntro; split; eauto.
          constructor.
  Qed.

End tag.
