From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From RWasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Lemma select_false_det v1 v2 n obs s f obs' s' f' es:
  n = Wasm_int.int_zero i32m ->
  reduce obs s f [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_const (VAL_int32 n)); AI_basic BI_select] obs' s' f' es ->
  reduce_det_goal obs s f [AI_basic (BI_const v2)] obs' s' f' es [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_const (VAL_int32 n)); AI_basic BI_select].
Proof.
  move => H Hred.
  only_one [AI_basic (BI_const v1) ; AI_basic (BI_const v2);
            AI_basic (BI_const (VAL_int32 n)) ; AI_basic BI_select] Hred ;
    [done | by inversion Heqes ; subst ].
Qed.

Lemma select_true_det v1 v2 n obs s f obs' s' f' es:
  n <> Wasm_int.int_zero i32m ->
  reduce obs s f [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_const (VAL_int32 n)); AI_basic BI_select] obs' s' f' es ->
  reduce_det_goal obs s f [AI_basic (BI_const v1)] obs' s' f' es [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_const (VAL_int32 n)); AI_basic BI_select].
Proof.
  move => H Hred.
  only_one [AI_basic (BI_const v1) ; AI_basic (BI_const v2);
            AI_basic (BI_const (VAL_int32 n)) ; AI_basic BI_select] Hred ;
    [ by inversion Heqes ; subst | done ].
Qed.
