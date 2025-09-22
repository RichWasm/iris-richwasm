(* Fundamental theorem for the kind system:
     well-kinded syntactic types are semantically well-kinded *)

From iris.proofmode Require Import base tactics classes.
From RichWasm Require Import layout syntax typing.
From RichWasm.compiler Require Import codegen instrs modules util.
From RichWasm.iris Require Import autowp gc.
From RichWasm.iris.logrel Require Import relations.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section FundamentalKinding.
  Context `{Σ: gFunctors}.
  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!RichWasmGCG Σ}.

  Variable sr : store_runtime.
  Variable mr : module_runtime.
  
  Lemma sizity_sized_le_unsized σ :
    sizity_interp (Σ:=Σ) (Sized σ) ⊑ sizity_interp Unsized.
  Proof.
    iIntros "%sv (%μ & %ws & %Hsv & %Hsz)".
    iPureIntro.
    do 2 eexists; split; eauto.
    intros; congruence.
  Qed.

  Theorem kinding_sound F s__mem s__rep s__size se τ κ : 
    has_kind F τ κ ->
    subst_env_interp F s__mem s__rep s__size se
    ⊢ kind_interp κ (value_interp sr se (subst_type s__mem s__rep s__size VarT τ)).
  Proof.
    intros Hkind. 
    revert s__mem s__rep s__size se.
    induction Hkind; intros; iIntros "Hsubst".
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
      (* CHANGE to use true by construction refinement *)
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

End FundamentalKinding.

