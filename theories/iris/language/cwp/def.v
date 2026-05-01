From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import list.
From RichWasm.iris.language Require Import iris_wp_def lenient_wp logpred.
Require Import RichWasm.iris.language.cwp.base.

Set Bullet Behavior "Strict Subproofs".

Section def.

  Context `{!wasmG Σ}.

  Definition label_spec : Type := nat * (frame -> list value -> iProp Σ).

  Definition label_specO : ofe := prodO (leibnizO nat) (leibnizO frame -n> leibnizO (list value) -n> iPropO Σ).

  Definition label_ctxO : ofe := listO label_specO.

  Definition return_spec : Type := nat * (list value -> iProp Σ).

  Definition return_specO : ofe := prodO (leibnizO nat) (leibnizO (list value) -n> iPropO Σ).

  Definition return_ctxO : ofe := optionO return_specO.

  Definition fvs_pred : Type := frame -> list value -> iProp Σ.

  Definition fvs_predO := leibnizO frame -n> leibnizO (list value) -n> iPropO Σ.

  Definition label_wand (l1 l2 : label_spec) : iProp Σ :=
    ⌜fst l1 = fst l2⌝ ∗ ∀ f vs, ⌜length vs = fst l1⌝ -∗ snd l1 f vs -∗ snd l2 f vs.

  Definition label_ctx_wand (L1 L2 : list label_spec) : iProp Σ :=
    ⌜length L1 <= length L2⌝ ∗ [∗ list] l1; l2 ∈ L1; take (length L1) L2, label_wand l1 l2.

  Definition return_wand (r1 r2 : return_spec) : iProp Σ :=
    ⌜fst r1 = fst r2⌝ ∗ ∀ vs, ⌜length vs = fst r1⌝ -∗ snd r1 vs -∗ snd r2 vs.

  Definition return_ctx_wand (R1 R2 : option return_spec) : iProp Σ :=
    match R1, R2 with
    | Some _, None => False
    | Some r1, Some r2 => return_wand r1 r2
    | None, Some _ => True
    | None, None => True
    end%I.

  Definition fvs_combine (Φ : fvs_pred) (vs0 : list value) (f : frame) (vs : list value) : iProp Σ :=
    Φ f (vs0 ++ vs).

  Program Definition coe_label_spec : label_specO -> label_spec :=
    λ '(a, b), (a, λ f, b f).

  Definition coe_label_ctx : label_ctxO -> list label_spec :=
    fmap coe_label_spec.

  Definition coe_return_ctx : return_ctxO -> option return_spec :=
    λ R, match R with
         | Some (n, R') => Some (n, λ v, R' v)
         | None => None
         end.

  Definition cwp_post_br (f : frame) (i : nat) (vh : valid_holed i) (L : list label_spec) : iProp Σ :=
    match L !! (i - vh_depth vh) with
    | Some (n, P) => ∃ vs0 vs, ⌜get_base_l vh = vs0 ++ vs⌝ ∗ ⌜length vs = n⌝ ∗ P f vs
    | None => False
    end%I.

  (*
  Lemma coe_label_ctx_ext (L L' : label_ctxO) (k : nat) n:
    L ≡{n}≡ L' ->
    ∀ (S S' : label_specO),
      coe_label_ctx L !! k = Some (coe_label_spec S) ->
      coe_label_ctx L' !! k = Some (coe_label_spec S') ->
      S ≡{n}≡ S'.
  *)

  Program Definition cwp_post_br_ne (f : frame) (i : nat) (vh : valid_holed i) : label_ctxO -n> iProp Σ :=
    λne L,
      cwp_post_br f i vh (coe_label_ctx L).
  Final Obligation.
    intros * L L' Heq; cbn.
    unfold coe_label_ctx, cwp_post_br.
    rewrite !list_lookup_fmap.
    set (k := i - vh_depth vh).
    eapply (list_lookup_ne k) in Heq.
    unfold lookup in *.
    destruct Heq as [u v [Hn Ht] | ]; last done.
    destruct u, v; solve_proper.
  Qed.

  Definition cwp_post_ret (svh : simple_valid_holed) (R : option return_spec) : iProp Σ :=
    match R with
    | Some (n, P) => ∃ vs0 vs, ⌜simple_get_base_l svh = vs0 ++ vs⌝ ∗ ⌜length vs = n⌝ ∗ P vs
    | None => False
    end%I.

  Program Definition cwp_post_ret_ne (svh : simple_valid_holed) : return_ctxO -n> iProp Σ :=
    λne R, cwp_post_ret svh (coe_return_ctx R).
  Final Obligation.
    intros * R R' Heq; cbn.
    destruct Heq as [x y [Heq1 Heq2] |]; [cbn | done].
    destruct x, y; solve_proper.
  Qed.

  Definition cwp_post_lp L R Φ : logpred :=
      {| lp_fr_inv _ := True;
         lp_trap := True;
         lp_val f v := Φ f v;
         lp_br f i vh := cwp_post_br f i vh L;
         lp_ret svh := cwp_post_ret svh R;
         lp_host _ _ _ _ := False |}%I.

  Definition coe_fvs_pred : fvs_predO -> fvs_pred :=
    λ Φ, λ f v, Φ f v.

  Program Definition cwp_post_lp_ne : label_ctxO -n> return_ctxO -n> fvs_predO -n> logpredO :=
    λne L R Φ, cwp_post_lp (coe_label_ctx L) (coe_return_ctx R) (coe_fvs_pred Φ).
  Next Obligation.
    intros * p q Hpq.
    unfold coe_fvs_pred.
    split; repeat match goal with
           | |- _ /\ _ => split
           end;
      solve_proper.
  Qed.
  Next Obligation.
    intros * R R' HR p; cbn.
    unfold coe_fvs_pred.
    split; repeat match goal with
           | |- _ /\ _ => split
           end; try solve_proper.
    intros lh; cbn.
    by eapply cwp_post_ret_ne.
  Qed.
  Final Obligation.
    intros * L L' HL R p; cbn.
    unfold coe_fvs_pred.
    split; repeat match goal with
           | |- _ /\ _ => split
           end; try solve_proper.
    intros *; cbn.
    by eapply cwp_post_br_ne.
  Qed.

  Program Definition cwp_wasm (s : stuckness) (E : coPset) (es : list basic_instruction)
                     L R Φ :=
    lenient_wp s E (to_e_list es) (cwp_post_lp L R Φ).

  Program Definition cwp_wasm_ne (s : stuckness) (E : coPset) (es : list basic_instruction) :
    label_ctxO -n> return_ctxO -n> fvs_predO -n> iPropO Σ :=
    λne L R Φ,
      lenient_wp s E (to_e_list es) (cwp_post_lp (coe_label_ctx L) (coe_return_ctx R) (coe_fvs_pred Φ)).
  Next Obligation.
    intros * p q Hpq.
    eapply lenient_wp_ne.
    by eapply (cwp_post_lp_ne L R).
  Qed.
  Next Obligation.
    intros * R R' HR p; cbn.
    eapply lenient_wp_ne.
    by eapply (cwp_post_lp_ne L).
  Qed.
  Final Obligation.
    intros * L L' HL R p; cbn.
    eapply lenient_wp_ne.
    by eapply cwp_post_lp_ne.
  Qed.

End def.

Notation "'CWP' es @ s ; E 'UNDER' L ; R {{ Φ } }" :=
  (cwp_wasm s E es L R Φ) (at level 20, only parsing) : bi_scope.

Notation "'CWP' es @ s ; E 'UNDER' L ; R {{ f ; vs , Φ } }" :=
  (cwp_wasm s E es L R (fun f vs => Φ))
    (at level 20, format "'CWP'  '[hv' es  '/' @  '[hv' s ;  '/' E  ']' '/' 'UNDER'  '[hv' L ;  '/' R ']'  '/' {{  '[' f ;  vs ,  '/' Φ  ']' } } ']'") : bi_scope.

Notation "'CWP' es @ E 'UNDER' L ; R {{ Φ } }" :=
  (cwp_wasm NotStuck E es L R Φ) (at level 20, only parsing) : bi_scope.

Notation "'CWP' es @ E 'UNDER' L ; R {{ f ; vs , Φ } }" :=
  (cwp_wasm NotStuck E es L R (fun f vs => Φ))
    (at level 20, format "'CWP'  '[hv' es  '/' @  E  '/' 'UNDER'  '[hv' L ;  '/' R ']'  '/' {{  '[' f ;  vs ,  '/' Φ  ']' } } ']'") : bi_scope.

Notation "'CWP' es 'UNDER' L ; R {{ Φ } }" :=
  (cwp_wasm NotStuck top es L R Φ) (at level 20, only parsing) : bi_scope.

Notation "'CWP' es 'UNDER' L ; R {{ f ; vs , Φ } }" :=
  (cwp_wasm NotStuck top es L R (fun f vs => Φ))
    (at level 20, format "'CWP'  '[hv' es  '/' 'UNDER'  '[hv' L ;  '/' R ']'  '/' {{  '[' f ;  vs ,  '/' Φ  ']' } } ']'") : bi_scope.
