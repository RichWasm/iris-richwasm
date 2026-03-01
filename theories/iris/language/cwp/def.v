From RichWasm.iris.language Require Import iris_wp_def lenient_wp logpred.
Require Import RichWasm.iris.language.cwp.base.

Set Bullet Behavior "Strict Subproofs".

Section def.

  Context `{!wasmG Σ}.

  Definition label_spec : Type := nat * (frame -> list value -> iProp Σ).

  Definition return_spec : Type := nat * (list value -> iProp Σ).

  Definition fvs_pred : Type := frame -> list value -> iProp Σ.

  Definition label_wand (l1 l2 : label_spec) : iProp Σ :=
    ⌜fst l1 = fst l2⌝ ∗ ∀ f vs, snd l1 f vs -∗ snd l2 f vs.

  Definition label_ctx_wand (L1 L2 : list label_spec) : iProp Σ :=
    ⌜length L1 <= length L2⌝ ∗ [∗ list] l1; l2 ∈ L1; take (length L1) L2, label_wand l1 l2.

  Definition return_wand (r1 r2 : return_spec) : iProp Σ :=
    ⌜fst r1 = fst r2⌝ ∗ ∀ vs, snd r1 vs -∗ snd r2 vs.

  Definition return_ctx_wand (R1 R2 : option return_spec) : iProp Σ :=
    match R1, R2 with
    | Some _, None => False
    | Some r1, Some r2 => return_wand r1 r2
    | None, Some _ => True
    | None, None => True
    end%I.

  Definition fvs_combine (Φ : fvs_pred) (vs0 : list value) (f : frame) (vs : list value) : iProp Σ :=
    Φ f (vs0 ++ vs).

  Definition cwp_post_br (L : list label_spec) (f : frame) (i : nat) (vh : valid_holed i) : iProp Σ :=
    match L !! (i - vh_depth vh) with
    | Some (n, P) => ∃ vs0 vs, ⌜get_base_l vh = vs0 ++ vs⌝ ∗ ⌜length vs = n⌝ ∗ P f vs
    | None => False
    end%I.

  Definition cwp_post_ret (R : option return_spec) (svh : simple_valid_holed) : iProp Σ :=
    match R with
    | Some (n, P) => ∃ vs0 vs, ⌜simple_get_base_l svh = vs0 ++ vs⌝ ∗ ⌜length vs = n⌝ ∗ P vs
    | None => False
    end%I.

  Definition cwp_post_lp (L : list label_spec) (R : option return_spec) (Φ : fvs_pred) : logpred :=
    {| lp_fr_inv _ := True;
       lp_trap := True;
       lp_val := Φ;
       lp_br f i vh := cwp_post_br L f i vh;
       lp_ret svh := cwp_post_ret R svh;
       lp_host _ _ _ _ := False |}%I.

  Definition cwp_wasm
    (s : stuckness) (E : coPset) (es : list basic_instruction) (L : list label_spec)
    (R : option return_spec) (Φ : fvs_pred) :
    iProp Σ :=
    lenient_wp s E (to_e_list es) (cwp_post_lp L R Φ).

End def.

Notation "'CWP' es @ s ; E 'UNDER' L ; R {{ Φ } }" :=
  (cwp_wasm s E es L R Φ) (at level 20, only parsing) : bi_scope.

Notation "'CWP' es @ s ; E 'UNDER' L ; R {{ f ; vs , Φ } }" :=
  (cwp_wasm s E es L R (fun f vs => Φ))
    (at level 20, format "'CWP'  es  @  s ;  E  'UNDER'  L ;  R  {{  f ;  vs ,  Φ  } }") : bi_scope.

Notation "'CWP' es @ E 'UNDER' L ; R {{ Φ } }" :=
  (cwp_wasm NotStuck E es L R Φ) (at level 20, only parsing) : bi_scope.

Notation "'CWP' es @ E 'UNDER' L ; R {{ f ; vs , Φ } }" :=
  (cwp_wasm NotStuck E es L R (fun f vs => Φ))
    (at level 20, format "'CWP'  es  @  E  'UNDER'  L ;  R  {{  f ;  vs ,  Φ  } }") : bi_scope.
