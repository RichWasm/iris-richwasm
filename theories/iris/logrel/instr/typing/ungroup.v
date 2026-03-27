Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section ungroup.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_ungroup M F L wt wt' wtf wl wl' wlf es' τs κ :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [ProdT κ τs] τs in
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IUngroup ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    (* intros fe WT WL ψ Hok Hcg. *)
    (* inversion Hok as [F' ψ' L' Hmono Hok']. *)
    (* subst F' ψ' L'. *)
    (* cbn in Hcg; inversion Hcg; subst wt' wl' es'. *)
    (* simpl to_e_list. *)
    (* iApply sem_type_erased_nop; first done. *)
    (* iIntros (se vs) "Hvs". *)
    (* rewrite values_interp_one_eq value_interp_eq. *)
    (* cbn. *)
    (* iDestruct "Hvs" as "(%κ' & %Hκ' & Hkind & Hvs)". *)
  Admitted.

End ungroup.
