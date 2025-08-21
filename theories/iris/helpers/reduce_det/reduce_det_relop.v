From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From RichWasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Lemma relop_det v1 v2 op t obs s f obs' s' f' es:
  reduce obs s f [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_relop t op)] obs' s' f' es ->
  reduce_det_goal obs s f [AI_basic (BI_const (VAL_int32 (wasm_bool (app_relop op v1 v2))))] obs' s' f' es [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_relop t op)].
Proof.
  move => Hred.
  by only_one [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ; AI_basic (BI_relop t op)] Hred.
Qed.
