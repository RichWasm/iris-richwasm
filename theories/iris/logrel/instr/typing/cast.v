Require Import RichWasm.iris.logrel.type_eq.
Require Import RichWasm.iris.logrel.instr.typing.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section cast.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_cast M F L wt wt' wtf wl wl' wlf es' τ τ' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let ψ := InstrT [τ] [τ'] in
    type_eq τ τ' ->
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (ICast ψ)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmask ψ Htype_eq Hok Hcg.
    inv_cg_ret Hcg.
    subst ψ WT WL wt' wl' es'.
    clear Hretval.
    clear_nils.
    destruct Hok as [[Hmono1 Hmono2] _].
    rewrite Forall_singleton in Hmono1.
    rewrite Forall_singleton in Hmono2.
    destruct Hmono1 as (ρ1 & Hrep1 & _).
    destruct Hmono2 as (ρ2 & Hrep2 & _).
    inversion Hrep1 as [F1 τ1 ρ1' ξ1 Hkind1]; subst F1 τ1 ρ1'.
    inversion Hrep2 as [F2 τ2 ρ2' ξ2 Hkind2]; subst F2 τ2 ρ2'.
    iApply sem_type_erased; first done.
    iIntros (se vs Hsemenv) "Hos".
    rewrite !values_interp_one_eq !value_interp_eq -!type_interp_eq.
    by iApply (type_interp_type_eq _ _ _ _ Htype_eq  _ _ _ _ _ Hkind1 Hkind2 with "Hos").
  Qed.

End cast.
