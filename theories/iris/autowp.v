From iris.proofmode Require Import base tactics classes.
From iris.bi Require Export weakestpre.
From Wasm Require Import datatypes.
From RichWasm.iris.rules Require Export proofmode iris_rules.
From RichWasm.iris.language Require Export iris_wp_def lenient_wp logpred.

Inductive arity :=
| Ar (i: nat) (o: nat)
| VarAr.

Definition bi_ar (instr: basic_instruction) : arity :=
match instr with
| BI_unreachable => VarAr
| BI_nop => Ar 0 0
| BI_drop => Ar 1 0
| BI_select => Ar 3 1
| BI_block (Tf tn tm) body => Ar (length tn) (length tm)
| BI_loop (Tf tn tm) body => Ar (length tn) (length tm)
| BI_if (Tf tn tm) _ _ => Ar (length tn + 1) (length tm)
| BI_br x => VarAr
| BI_br_if x => VarAr
| BI_br_table x x0 => VarAr
| BI_return => VarAr
| BI_call x => VarAr
| BI_call_indirect x => VarAr
| BI_get_local x => Ar 0 1
| BI_set_local x => Ar 1 0
| BI_tee_local x => Ar 1 1
| BI_get_global x => Ar 0 1
| BI_set_global x => Ar 1 0
| BI_load x x0 x1 x2 x3 => Ar 1 1 
| BI_store x x0 x1 x2 x3 => Ar 2 0
| BI_current_memory x => Ar 0 1
| BI_grow_memory x => Ar 1 1
| BI_const x => Ar 0 1
| BI_unop x x0 => Ar 1 1
| BI_binop x x0 => Ar 2 1
| BI_testop x x0 => Ar 1 1
| BI_relop x x0 => Ar 2 1
| BI_cvtop x x0 x1 x2 => Ar 1 1
end.

Definition ai_ar (instr: administrative_instruction) :=
  match instr with
  | AI_basic b => bi_ar b
  | AI_trap => VarAr
  | AI_invoke x => VarAr
  | AI_label x x0 x1 => VarAr
  | AI_local x x0 x1 => VarAr
  | AI_call_host x x0 x1 => VarAr
  end.

Ltac destruct_length_eqn Hlen :=
  repeat (cbn in Hlen; 
          match type of Hlen with
          | context[length ?vs] => destruct vs; try discriminate Hlen
          end).
Ltac check_const_nat e :=
  match e with
  | S ?e => check_const_nat e
  | O => idtac
  | _ => fail
  end.
Ltac destruct_length_eqn' :=
  match goal with
  | H: length _ = ?n |- _ =>
      check_const_nat n;
      destruct_length_eqn H
  end.

Ltac wp_chomp n :=
  match goal with
  | |- context [ environments.envs_entails _ (@wp_wasm_ctx _ _ _ _ ?e _ _ _) ] =>
      iEval (rewrite -(@take_drop _ n e); simpl firstn; simpl skipn)
  | |- context [ environments.envs_entails _ (@wp _ _ _ _ _ _ _ ?e _) ] =>
      iEval (rewrite -(@take_drop _ n e); simpl firstn; simpl skipn)
  | |- context [ environments.envs_entails _ (@wp_wasm_ctx_frame _ _ _ _ ?e _ _ _ _ _) ] =>
      iEval (rewrite -(@take_drop _ n e); simpl firstn; simpl skipn)
  | |- context [ environments.envs_entails _ (@wp_wasm_frame _ _ _ _ ?e _ _ _) ] =>
      iEval (rewrite -(@take_drop _ n e); simpl firstn; simpl skipn)
  end.

Ltac fill_imm_pred :=
  match goal with
  | |- context [?g (immV ?v)] => instantiate (1:= λ w, ⌜w = immV v⌝%I) =>//
  end.

(* TODO: remove Σ *)
Ltac auto_logp Σ :=
  match goal with
  | |- context [lp_val ?r ?fr ?vs] =>
      let Φ :=
        constr:({|
          lp_fr_inv := (λ _, True);
          lp_val := (λ fr' vs', ⌜fr' = fr /\ vs' = vs⌝);
          lp_trap := False;
          lp_br := (λ _ _, False);
          lp_ret := (λ _, False);
          lp_host := (λ _ _ _ _, False)
        |}%I : @logpred Σ) in
        instantiate (1 := Φ);
        auto
  end.

Ltac seq_sz n m := 
  wp_chomp n;
  iApply (wp_seq _ _ _ (λ w, (∃ vs, ⌜w = immV vs⌝ ∗ ⌜length vs = m⌝ ∗ _ vs) ∗ ↪[frame] (_: frame))%I); 
  iSplitR; first last.

Ltac skip_sz n := 
  wp_chomp n;
  iApply wp_val_app; [done | iSplitR; first last].

Fixpoint stack_size (ais: list administrative_instruction) : nat * _ :=
  match ais with
  | ai :: ais =>
      match to_val_instr ai with
      | Val _ => 
          let (sz, ais) := stack_size ais in
          (1 + sz, ais)
      | NotVal _ => (0, ai :: ais)
      end
  | [] => (0, [])
  end.

Inductive shape :=
| Shape (to_skip: nat) (to_use: nat) (output: nat) (rest: nat)
| Unknown.

Definition ai_shp (ais: list administrative_instruction) : shape :=
  let '(sz, rest) := stack_size ais in
  match rest with
  | ai :: ais => 
      match ai_ar ai with
      | Ar n m =>
          if Nat.leb n sz
          then Shape (sz - n) (sz + 1) (sz - n + m) (length ais)
          else Unknown
      | VarAr => Unknown
      end
  | [] => Unknown
  end.

Ltac get_shp :=
  match goal with
  | |- context[ environments.envs_entails _ (wp NotStuck ?E ?e ?P) ] =>
      eval vm_compute in (ai_shp e)
  end.

Ltac next_wp :=
  match get_shp with
  | Shape _ _ _ 0 => fail 0
  | Shape 0 ?use ?outs (S ?rest) =>
      seq_sz use outs; 
      [iRename select (↪[frame] (_: datatypes.frame))%I into "Hfr";
       iSplitR "HΦ"|];
      [|iIntros (w) "((%vs & -> & % & ?) & Hfr)";
        destruct_length_eqn'
      |]
  | Shape ?to_skip ?use ?outs 0 =>
      skip_sz to_skip
  | Shape ?to_skip ?use ?outs (S ?rest) =>
      seq_sz use outs; 
      [iRename select (↪[frame] (_: datatypes.frame))%I into "Hfr";
       iSplitR "HΦ"
      |];
      [|iIntros (w) "((%vs & -> & % & ?) & Hfr)";
        destruct_length_eqn'
      |];
      first (skip_sz to_skip)
  | Unknown => fail 0
  end.

Ltac lwp_chomp n :=
  match goal with
  | |- context [ environments.envs_entails _ (@lenient_wp _ _ _ _ ?e _) ] =>
      iEval (rewrite -(@take_drop _ n e); simpl firstn; simpl skipn)
  end.
