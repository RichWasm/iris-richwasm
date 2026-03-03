Require Import RecordUpdate.RecordUpdate.
From stdpp Require Import base list.

From iris.proofmode Require Import base tactics classes.
From Wasm Require Import operations.

From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import prelude codegen instruction module.
From RichWasm.iris Require Import autowp memory util wp_codegen.
From RichWasm.iris.language Require Import cwp logpred.
From RichWasm.iris.logrel Require Import relations_cwp fundamental_kinding.
Require Import RichWasm.iris.logrel.compat_cwp.common.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Fundamental.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_br M F L L' n_skip wt wt' wtf wl wl' wlf es' i τs1 τs τs2 :
    let fe := fe_of_context F <| fe_br_skip := n_skip |> in
    let WT := wt ++ wt' ++ wtf in
    let WL := wl ++ wl' ++ wlf in
    let ψ := InstrT (τs1 ++ τs) τs2 in
    F.(fc_labels) !! i = Some (τs, L) ->
    Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
    has_instruction_type_ok F ψ L' ->
    run_codegen (compile_instr mr fe (IBr ψ i)) wt wl = inr ((), wt', wl', es') ->
    ⊢ have_instr_type_sem rti sr mr M F L WT WL es' ψ L'.
  Proof.
    iIntros (fe WT WL Ψ Hi _ Hok Hcg se inst fr os vs θ B R Hse)
      "#HIinst HIB HIR HIvs HIos HIfr Hrt Hfr Hrun".
    inversion Hcg.
    subst WT WL Ψ wt' wl' es'.
    clear Hcg.
    clear_nils.
    (* TODO: labels_interp doesn't account for br_skip. *)
    assert (n_skip = []) by admit.
    subst n_skip.
    rewrite take_nil.
    cbn [seq.filter length].
    rewrite Nat.add_0_r.
    apply lookup_lt_Some in Hi as Hilen.
    iDestruct (big_sepL2_length with "HIB") as "%HBlen".
    assert (is_Some (B !! i)) as [[n P] HBi].
    { apply lookup_lt_is_Some. by rewrite <- HBlen. }
    iDestruct (big_sepL2_lookup_acc with "HIB") as "[Hbr _]".
    1, 2: done.
    iDestruct (values_interp_app with "HIos") as "(%os1 & %os2 & -> & HIos1 & HIos2)"; first done.
    iDestruct (atoms_interp_app with "HIvs") as "(%vs1 & %vs2 & -> & HIvs1 & HIvs2)".
    1, 2, 3: done.
    iDestruct "Hbr" as "[Htslen HP]".
    destruct (translate_types se τs) as [ts|] eqn:Hts; last done.
    iDestruct (translate_types_sem_interp_length with "HIos2") as "%Hos2len".
    1, 2: done.
    iDestruct (big_sepL2_length with "HIvs2") as "%Hvs2len".
    iSpecialize ("HP" with "[$HIvs2] [$HIos2] [$HIfr] [$Hrt]").
    iDestruct "Htslen" as "%Htslen".
    iClear "HIos1 HIvs1 HIR".
    rewrite map_app.
    rewrite <- app_assoc.
    iApply cwp_val_app.
    iApply (cwp_br with "[$] [$]").
    { done. }
    { rewrite <- Htslen. by rewrite <- Hos2len. }
    done.
  Admitted.

End Fundamental.
