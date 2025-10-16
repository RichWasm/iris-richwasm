From RichWasm.iris.language Require Import iris_wp_def.
Import iris.algebra.list.
Section logpred.
  Context `{!wasmG Σ}.
  Open Scope bi_scope.

  Record logpredO :=
    MkLPO {
        lpo_fr: leibnizO datatypes.frame -n> iProp Σ;
        lpo_val: listO (leibnizO value) -n> iProp Σ;
        lpo_trap: iProp Σ;
        lpo_br: discrete_funO (λ n, leibnizO (valid_holed n) -n> iProp Σ);
        lpo_ret: leibnizO simple_valid_holed -n> iProp Σ;
        lpo_host: leibnizO function_type -n> leibnizO hostfuncidx -n> listO (leibnizO value) -n> leibnizO llholed -n> iProp Σ;
      }.

  Record logp (A: Type) :=
    MkLP {
        lp_fr: datatypes.frame -> A;
        lp_val: list value -> A;
        lp_trap: A;
        lp_br: forall n, valid_holed n -> A;
        lp_ret: simple_valid_holed -> A;
        lp_host: function_type -> hostfuncidx -> list value -> llholed -> A;
      }.
  Arguments MkLP {A}.
  Arguments lp_fr {A}.
  Arguments lp_val {A}.
  Arguments lp_trap {A}.
  Arguments lp_br {A}.
  Arguments lp_ret {A}.
  Arguments lp_host {A}.

  Definition logpred := logp (iProp Σ).

  Definition lp_noframe (Φ: logpred) : val -> iProp Σ :=
    λ w, match w with
         | immV vs => Φ.(lp_val) vs
         | trapV => ↪[BAIL] ∗ Φ.(lp_trap)
         | brV i lh => Φ.(lp_br) i lh
         | retV lh => Φ.(lp_ret) lh
         | callHostV ft hidx vs lh => Φ.(lp_host) ft hidx vs lh
         end.

  Definition denote_logpred (Φ: logpred) : val -> iProp Σ :=
    λ w, lp_noframe Φ w ∗
         ∃ f, ↪[frame] f ∗ Φ.(lp_fr) f.

  Notation "⟦ Φ ⟧" := (denote_logpred Φ).

  Definition lp_map {A B: Type} (f: A -> B) (p: logp A) : logp B :=
    {|
      lp_fr := λ fr, f (lp_fr p fr);
      lp_val := λ vs, f (lp_val p vs);
      lp_trap := f (lp_trap p);
      lp_br := λ n lh, f (lp_br p n lh);
      lp_ret := λ lh, f (lp_ret p lh);
      lp_host := λ ft hf vs lh, f (lp_host p ft hf vs lh)
    |}.

  Definition lp_map2 {A B C} (f: A -> B -> C) (Φ1: logp A) (Φ2: logp B) : logp C :=
    {|
      lp_fr := λ fr, f (lp_fr Φ1 fr) (lp_fr Φ2 fr);
      lp_val := λ vs, f (lp_val Φ1 vs) (lp_val Φ2 vs);
      lp_trap := f (lp_trap Φ1) (lp_trap Φ2);
      lp_br := λ n lh, f (lp_br Φ1 n lh) (lp_br Φ2 n lh);
      lp_ret := λ lh, f (lp_ret Φ1 lh) (lp_ret Φ2 lh);
      lp_host := λ ft hf vs lh, f (lp_host Φ1 ft hf vs lh) (lp_host Φ2 ft hf vs lh)
    |}.

  Definition lp_const (Φ: iProp Σ) : logpred :=
    MkLP (λ fr, ⌜True⌝) (λ vs, Φ) Φ (λ n lh, Φ) (λ lh, Φ) (λ ft hf vs lh, Φ).

  Definition lp_emp : logpred :=
    lp_const emp.

  Definition lp_pure (φ: Prop) : logpred :=
    lp_const ⌜φ⌝.

  Instance lp_dist : Dist logpred.
  Admitted.
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
      lp_fr := λ fr a, lp_fr (p a) fr;
      lp_val := λ vs a, lp_val (p a) vs;
      lp_trap := λ a, lp_trap (p a);
      lp_br := λ n lh a, lp_br (p a) n lh;
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

  Definition lp_ofe_mixin : OfeMixin logpred.
  Proof.
    split.
    - admit.
    - admit.
    - admit.
  Admitted.

  Instance lp_cofe_aux : Cofe (Ofe logpred lp_ofe_mixin).
  Admitted.

  Definition lp_bi_mixin : BiMixin lp_entails lp_emp lp_pure lp_and lp_or lp_impl lp_forall lp_exist lp_sep lp_wand.
  Proof.
  Admitted.

  Definition lp_bi_persistently_mixin : BiPersistentlyMixin lp_entails lp_emp lp_and lp_exist lp_sep lp_persistently.
  Admitted.

  Definition lp_bi_later_mixin : BiLaterMixin lp_entails lp_pure lp_or lp_impl lp_forall lp_exist lp_sep lp_persistently lp_later.
  Admitted.

  Canonical Structure lp_bi : bi :=
    {|
      bi_ofe_mixin := lp_ofe_mixin;
      bi_bi_mixin := lp_bi_mixin;
      bi_bi_persistently_mixin := lp_bi_persistently_mixin;
      bi_bi_later_mixin := lp_bi_later_mixin;
    |}.

  Definition lp_embed_mixin: BiEmbedMixin (iProp Σ) logpred lp_const.
  Proof.
  Admitted.

  Global Instance lp_embed : BiEmbed (iProp Σ) logpred :=
    {| bi_embed_mixin := lp_embed_mixin |}.

End logpred.

Arguments MkLP {A}.
Arguments lp_fr {A}.
Arguments lp_val {A}.
Arguments lp_trap {A}.
Arguments lp_br {A}.
Arguments lp_ret {A}.
Arguments lp_host {A}.
