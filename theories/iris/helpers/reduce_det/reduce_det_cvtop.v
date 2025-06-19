From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From RWasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Lemma cvtop_convert_det v v' t1 t2 sx obs s f obs' s' f' es:
  types_agree t1 v ->
  cvt t2 sx v = Some v' ->
  reduce obs s f [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] obs' s' f' es ->
  reduce_det_goal obs s f [AI_basic (BI_const v')] obs' s' f' es [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)].
Proof.
  move => H H0 Hred.
  by only_one [AI_basic (BI_const v) ; AI_basic (BI_cvtop t2 CVO_convert t1 sx)] Hred ;
     inversion Heqes ; subst ; rewrite H0 in H2 ;
     inversion H2 ; subst.
Qed.

Lemma cvtop_convert_none_det v t1 t2 sx obs s f obs' s' f' es:
  types_agree t1 v ->
  cvt t2 sx v = None ->
  reduce obs s f [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] obs' s' f' es ->
  reduce_det_goal Crash s f [AI_trap] obs' s' f' es [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)].
Proof.
  move => H H0 Hred.
  by only_one [AI_basic (BI_const v) ; AI_basic (BI_cvtop t2 CVO_convert t1 sx)] Hred ;
     inversion Heqes ; subst ; rewrite H0 in H2 ;
     inversion H2 ; subst.
Qed.

Lemma cvtop_reinterpret_det v t1 t2 obs s f obs' s' f' es:
  types_agree t1 v ->
  reduce obs s f [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] obs' s' f' es ->
  reduce_det_goal obs s f [AI_basic (BI_const (wasm_deserialise (bits v) t2))] obs' s' f' es
    [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)].
Proof.
  move => H Hred.
  by only_one [AI_basic (BI_const v) ; AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] Hred.
Qed.
