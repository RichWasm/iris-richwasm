Require Import RichWasm.iris.logrel.instr.typing.common.
Require Import RichWasm.iris.logrel.substitution.
Require Import RichWasm.iris.logrel.logrel_properties.
Require Import RichWasm.iris.logrel.env_props.
Require Import RichWasm.kinding_subst.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section inst.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.


  Lemma compat_inst M F L wt wt' wtf wl wl' wlf es' ix ϕ ϕ' :
    let fe := fe_of_context F in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let lmask := wlmask fe wl in
    let κ := VALTYPE (AtomR I32R) NoRefs in
    let ψ := InstrT [CodeRefT κ ϕ] [CodeRefT κ ϕ'] in
    function_type_inst F ix ϕ ϕ' ->
    has_instruction_type_ok M F ψ L ->
    run_codegen (compile_instr mr fe (IInst ψ ix)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    intros fe WT WL lmask κ ψ Hfinst Hok Hcg.
    cbn in Hcg; inversion Hcg; subst wt' wl' es'; clear Hcg.
    subst WT WL; clear_nils.
    have Hkind : has_kind_ft F ϕ.
    {
      destruct Hok as [[Hmono _] _].
      rewrite Forall_cons_iff in Hmono.
      destruct Hmono as [[ρ [Hrep _]] _].
      inversion Hrep as [? ? ? ? Hhas_kind]; subst.
      by inversion Hhas_kind.
    }
    iApply sem_type_erased; first done.
    iIntros (se vs Hse) "Hval".
    rewrite !values_interp_one_eq !value_interp_eq.
    iDestruct "Hval" as (sκ) "(%Hsk & %Hsv & Hval)".
    iExists sκ; iSplit; [done|]; iSplit; [done|].
    cbn.
    iDestruct "Hval" as (i i32 j cl) "(%Hrepr & %Hsv' & Hcl & Hinv1 & Hinv2)".
    iExists i, i32, j, cl; iFrame "Hinv1 Hinv2"; iSplit; [done|]; iSplit; [done|].
    by iApply (closure_interp_inst with "Hcl").
  Qed.

End inst.
