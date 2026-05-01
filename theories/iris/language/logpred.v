From RichWasm.iris.language Require Import iris_wp_def.
Import iris.algebra.list.

Set Bullet Behavior "Strict Subproofs".

Section logpred.
  Context `{!wasmG Σ}.
  Open Scope bi_scope.

  Record logp (A: Type) :=
    MkLP {
        lp_fr_inv: datatypes.frame -> A;
        lp_val: datatypes.frame -> list value -> A;
        lp_trap: A;
        lp_br: datatypes.frame -> forall n, valid_holed n -> A;
        lp_ret: simple_valid_holed -> A;
        lp_host: function_type -> hostfuncidx -> list value -> llholed -> A;
      }.
  Arguments MkLP {A}.
  Arguments lp_fr_inv {A}.
  Arguments lp_val {A}.
  Arguments lp_trap {A}.
  Arguments lp_br {A}.
  Arguments lp_ret {A}.
  Arguments lp_host {A}.

  Section LogpRelation.
    Context {A : Type} (R : relation A).
    Definition logp_relation : relation (logp A) :=
      λ Φ Ψ,
        pointwise_relation datatypes.frame R Φ.(lp_fr_inv) Ψ.(lp_fr_inv) /\
        pointwise_relation datatypes.frame (pointwise_relation (list value) R) Φ.(lp_val) Ψ.(lp_val) /\
        R Φ.(lp_trap) Ψ.(lp_trap) /\
        (∀ f n (lh: valid_holed n), R (Φ.(lp_br) f n lh) (Ψ.(lp_br) f n lh)) /\
        pointwise_relation simple_valid_holed R Φ.(lp_ret) Ψ.(lp_ret) /\
        pointwise_relation function_type
          (pointwise_relation hostfuncidx
             (pointwise_relation (list value)
                (pointwise_relation llholed R)))
          Φ.(lp_host) Ψ.(lp_host).
  End LogpRelation.

  Definition logpred := logp (iProp Σ).

  Global Instance logpred_equiv : Equiv logpred :=
    logp_relation equiv.

  Global Instance logpred_dist : Dist logpred :=
    λ n, logp_relation (dist n).


  Ltac split_ands :=
    repeat
      match goal with
      | H : _ /\ _ |- _ => destruct H
      | |- _ /\ _ => split
      end.
  Program Definition logpredO : ofe :=
    {| ofe_car := logpred;
       ofe_equiv := logpred_equiv;
       ofe_dist := logpred_dist |}.
  Final Obligation.
    split;
      unfold equiv, logpred_equiv, dist, logpred_dist, logp_relation.
    - intros x y; split.
      + intros;
        split_ands;
          repeat match goal with
                 | |- pointwise_relation _ _ _ _ => intros ?
                 | |- forall _, _ => intros ?
                 end;
          eapply (@mixin_equiv_dist _ _ _ _ (ofe_mixin (iPropO Σ)));
          try match goal with
              | H : _ |- _ => eapply H
              end.
      + intros Hn.
        repeat (rewrite forall_and_distr in Hn; destruct Hn as [? Hn]).
        split_ands;
          repeat match goal with
                 | |- pointwise_relation _ _ _ _ => intros ?
                 | |- forall _, _ => intros ?
                 end;
          eapply (@mixin_equiv_dist _ _ _ _ (ofe_mixin (iPropO Σ))); intros;
          try match goal with
              | H : _ |- _ => eapply H
              end.
    - intros n.
      split.
      + intros x.
        split_ands; reflexivity.
      + intros x y H.
        split_ands; by symmetry.
      + intros x y z Hxy Hyz.
        split_ands; etransitivity; by eauto.
    - intros n m x y Hxy Hlt.
      split_ands.
      + repeat intros ?; eapply mixin_dist_le; eauto; try eapply (iPropO Σ).
      + intros f vs.
        specialize (H0 f vs).
        eapply mixin_dist_le; [| eassumption | eassumption]; try eapply (iPropO Σ).
      + eapply mixin_dist_le; eauto; try eapply (iPropO Σ).
      + intros f n' lh.
        specialize (H2 f n' lh).
        eapply mixin_dist_le; [| eassumption | eassumption]; try eapply (iPropO Σ).
      + intros lh.
        eapply mixin_dist_le; eauto; try eapply (iPropO Σ).
      + intros ϕ hf vs lh.
        specialize (H4 ϕ hf vs lh).
        eapply mixin_dist_le; eauto; try eapply (iPropO Σ).
  Qed.

  Definition lp_noframe (Φ: logpred) : frame -> val -> iProp Σ :=
    λ f w,
      match w with
      | immV vs => ↪[RUN] ∗ Φ.(lp_val) f vs
      | trapV => ↪[BAIL] ∗ Φ.(lp_trap)
      | brV i lh => ↪[RUN] ∗ Φ.(lp_br) f i lh
      | retV lh => ↪[RUN] ∗ Φ.(lp_ret) lh
      | callHostV ft hidx vs lh => ↪[RUN] ∗ Φ.(lp_host) ft hidx vs lh
      end.

  Program Definition lp_noframe_ne : logpredO -n> leibnizO frame -n> leibnizO val -n> iPropO Σ :=
    λne Φ f v, lp_noframe Φ f v.
  Next Obligation. solve_proper. Qed.
  Next Obligation. solve_proper. Qed.
  Final Obligation.
    intros n Φ Ψ (Hfr_inv & Hval & Htrap & Hbr & Hret & Hhost) f v; cbn.
    destruct v; cbn.
    - f_equiv; apply Hval.
    - f_equiv; apply Htrap.
    - f_equiv; apply Hbr.
    - f_equiv; apply Hret.
    - f_equiv; apply Hhost.
  Qed.

  Definition denote_logpred (Φ: logpred) : val -> iProp Σ :=
    λ w, ∃ f, ↪[frame] f ∗ 
              Φ.(lp_fr_inv) f ∗ 
              lp_noframe Φ f w.

  Program Definition denote_logpred_ne : logpredO -n> leibnizO val -n> iPropO Σ :=
    λne Φ w, denote_logpred Φ w.
  Next Obligation. solve_proper. Qed.
  Final Obligation.
    intros n Φ Ψ (Hfr_inv & Hval & Htrap & Hbr & Hret & Hhost) w; cbn.
    unfold denote_logpred.
    f_equiv; intros f.
    f_equiv.
    f_equiv.
    - apply Hfr_inv.
    - by apply lp_noframe_ne.
  Qed.

  Notation "⟦ Φ ⟧" := (denote_logpred Φ).

  Definition lp_map {A B: Type} (f: A -> B) (p: logp A) : logp B :=
    {|
      lp_fr_inv := λ fr, f (lp_fr_inv p fr);
      lp_val := λ fr vs, f (lp_val p fr vs);
      lp_trap := f (lp_trap p);
      lp_br := λ fr n lh, f (lp_br p fr n lh);
      lp_ret := λ lh, f (lp_ret p lh);
      lp_host := λ ft hf vs lh, f (lp_host p ft hf vs lh)
    |}.

  Definition lp_map2 {A B C} (f: A -> B -> C) (Φ1: logp A) (Φ2: logp B) : logp C :=
    {|
      lp_fr_inv := λ fr, f (lp_fr_inv Φ1 fr) (lp_fr_inv Φ2 fr);
      lp_val := λ fr vs, f (lp_val Φ1 fr vs) (lp_val Φ2 fr vs);
      lp_trap := f (lp_trap Φ1) (lp_trap Φ2);
      lp_br := λ fr n lh, f (lp_br Φ1 fr n lh) (lp_br Φ2 fr n lh);
      lp_ret := λ lh, f (lp_ret Φ1 lh) (lp_ret Φ2 lh);
      lp_host := λ ft hf vs lh, f (lp_host Φ1 ft hf vs lh) (lp_host Φ2 ft hf vs lh)
    |}.

  Definition lp_const (Φ: iProp Σ) : logpred :=
    MkLP (λ fr, ⌜True⌝) (λ f vs, Φ) Φ (λ f n lh, Φ) (λ lh, Φ) (λ ft hf vs lh, Φ).

  Definition lp_emp : logpred :=
    lp_const emp.

  Definition lp_pure (φ: Prop) : logpred :=
    lp_const ⌜φ⌝.
  (*
    λ (n: nat) (Φ1 Φ2: logpred),
      lp_val Φ1 ≡{n}≡ lp_val Φ2 /\ 
      lp_trap Φ1 ≡{n}≡ lp_trap Φ2 ∧
      lp_br Φ1 ≡{n}≡ lp_br Φ2 ∧
      lp_ret Φ1 ≡{n}≡ lp_ret Φ2 ∧
      lp_host Φ1 ≡{n}≡ lp_host Φ2.
    *)

  Instance lp_equiv : Equiv logpred :=
    λ (Φ1 Φ2: logpred),
      forall lv, ⟦Φ1⟧ lv ⊣⊢ ⟦Φ2⟧ lv.

  Definition lp_entails (Φ1 Φ2: logpred) : Prop :=
    forall lv, ⟦Φ1⟧ lv ⊢ ⟦Φ2⟧ lv.
  
  Definition lp_and : logpred -> logpred -> logpred :=
    lp_map2 bi_and.

  Definition lp_or : logpred -> logpred -> logpred :=
    lp_map2 bi_or.

  Definition lp_impl : logpred -> logpred -> logpred :=
    lp_map2 bi_impl.

  Definition lp_dist_var {A X : Type} : (A -> logp X) -> logp (A -> X) :=
    λ p,
    {|
      lp_fr_inv := λ fr a, lp_fr_inv (p a) fr;
      lp_val := λ fr vs a, lp_val (p a) fr vs;
      lp_trap := λ a, lp_trap (p a);
      lp_br := λ fr n lh a, lp_br (p a) fr n lh;
      lp_ret := λ lh a, lp_ret (p a) lh;
      lp_host := λ ft hf vs lh a, lp_host (p a) ft hf vs lh;
    |}.

  Definition lp_forall (A: Type) (Φ: A -> logpred) : logpred :=
    lp_map bi_forall (lp_dist_var Φ).

  Definition lp_exist (A: Type) (Φ: A -> logpred) : logpred :=
    lp_map bi_exist (lp_dist_var Φ).

  Definition lp_sep : logpred -> logpred -> logpred :=
    lp_map2 bi_sep.

  Definition lp_wand : logpred -> logpred -> logpred :=
    lp_map2 bi_wand.

  Definition lp_persistently : logpred -> logpred :=
    lp_map bi_persistently.

  Definition lp_later : logpred -> logpred :=
    lp_map bi_later.
End logpred.

Arguments MkLP {A}.
Arguments lp_fr_inv {A}.
Arguments lp_val {A}.
Arguments lp_trap {A}.
Arguments lp_br {A}.
Arguments lp_ret {A}.
Arguments lp_host {A}.
