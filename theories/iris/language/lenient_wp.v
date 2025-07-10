From RWasm.iris.language Require Import iris_wp_def.
Section lenient_wp.
  Context `{!wasmG Σ}.
  Print iris.val.
  Open Scope bi_scope.

  Record logpred :=
    MkLP {
        lp_val: list value → iProp Σ;
        lp_trap: iPropI Σ;
        lp_br: ∀ n: nat, valid_holed n → iProp Σ;
        lp_ret: simple_valid_holed → iProp Σ;
        lp_host: function_type → hostfuncidx → list value → llholed → iProp Σ;
      }.

  Definition denote_logpred (Φ: logpred) : val -> iProp Σ :=
    λ w, match w with
         | immV vs => Φ.(lp_val) vs
         | trapV => ↪[BAIL] ∗ Φ.(lp_trap)
         | brV i lh => Φ.(lp_br) i lh
         | retV lh => Φ.(lp_ret) lh
         | callHostV ft hidx vs lh => Φ.(lp_host) ft hidx vs lh
         end.

  Notation "⟦ Φ ⟧" := (denote_logpred Φ).

  Definition lenient_wp (s: stuckness) (E: coPset) (es: expr) (Φ: logpred): iProp Σ :=
    wp s E es ⟦Φ⟧.

End lenient_wp.
