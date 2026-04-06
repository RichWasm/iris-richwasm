Require Import RichWasm.iris.logrel.instr.typing.common.

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
    has_instruction_type_ok F ψ L ->
    run_codegen (compile_instr mr fe (IInst ψ ix)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL lmask es' ψ L.
  Proof.
    (* intros fe WT WL κ ψ Hfinst Hok Hcg. *)
    (* cbn in Hcg; inversion Hcg; subst wt' wl' es'; clear Hcg. *)
    (* simpl to_e_list. *)
    (* iApply sem_type_erased; first done. *)
    (* iIntros (se vs) "Hrec". *)
    (* do 2 rewrite values_interp_one_eq value_interp_eq. *)
    (* cbn [subst_type]. *)
    (* cbn -[closure_interp0]. *)
    (* iDestruct "Hrec" as "(%κ' & %Hκ' & Hkindinterp & %i & %j & %cl & %Hvs & Hrec)". *)
    (* inversion Hκ'; subst κ'; clear Hκ'. *)
    (* inversion Hvs; subst vs; clear Hvs. *)
    (* iExists (SVALTYPE [I32R] ImCopy ImDrop). *)
    (* iSplit; first done. *)
    (* iFrame. *)
    (* iExists i, j, cl. *)
    (* iSplit; first done. *)
    (* iDestruct "Hrec" as "(Hrec & Hj & Hcl)". *)
    (* iFrame. *)
    (* iModIntro. *)
    (* (* prove that closure interp at ϕ implies closure interp at any instantiation ϕ' *) *)
    (* (* Will probably want to proceed by induction on function_type_inst? *) *)
  Admitted.

End inst.
