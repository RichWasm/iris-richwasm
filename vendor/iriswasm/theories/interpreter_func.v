(** Wasm interpreter **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From Wasm Require Import common.
From Coq Require Import ZArith.BinInt.
Require Import BinNat.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Export operations (* host *) type_checker.


Set Implicit Arguments.
Unset Strict Implicit.

Unset Printing Implicit Defensive.

Inductive res_crash : Type :=
| C_error : res_crash
| C_exhaustion : res_crash.

Scheme Equality for res_crash.
Definition res_crash_eqb c1 c2 := is_left (res_crash_eq_dec c1 c2).
Definition eqres_crashP : Equality.axiom res_crash_eqb :=
  eq_dec_Equality_axiom res_crash_eq_dec.

Canonical Structure res_crash_eqMixin := Equality.Mixin eqres_crashP.
Canonical Structure res_crash_eqType := Eval hnf in Equality.Pack (sort := res_crash) (Equality.Class res_crash_eqMixin).

Inductive res : Type :=
| R_crash : res_crash -> res
| R_trap : res
| R_value : list value -> res
| R_call_host : function_type -> hostfuncidx -> seq value -> res.

Definition res_eq_dec : forall r1 r2 : res, {r1 = r2} + {r1 <> r2}.
Proof. decidable_equality. Defined.

Definition res_eqb (r1 r2 : res) : bool := res_eq_dec r1 r2.
Definition eqresP : Equality.axiom res_eqb :=
  eq_dec_Equality_axiom res_eq_dec.

Canonical Structure res_eqMixin := Equality.Mixin eqresP.
Canonical Structure res_eqType := Eval hnf in Equality.Pack (sort := res) (Equality.Class res_eqMixin).

(* Section Host_func.

Variable host_instance : host.

(*Let store_record := store_record host_function. *)
(*Let administrative_instruction := administrative_instruction host_function.*)
Let host_state := host_state host_instance.

(*Let vs_to_es : seq value -> seq administrative_instruction := @vs_to_es _.*)

Variable host_application_impl : host_state -> store_record -> function_type -> host_function -> seq value ->
                       (host_state * option (store_record * result)).

Hypothesis host_application_impl_correct :
  (forall hs s ft hf vs hs' hres, (host_application_impl hs s ft hf vs = (hs', hres)) -> host_application hs s ft hf vs hs' hres). *)

Inductive res_step : Type :=
| RS_crash : res_crash -> res_step
| RS_break : nat -> list value -> res_step
| RS_return : list value -> res_step
| RS_call_host : function_type -> hostfuncidx -> seq value -> res_step
| RS_normal : list administrative_instruction -> res_step.

Definition res_step_eq_dec : forall r1 r2 : res_step, {r1 = r2} + {r1 <> r2}.
Proof. decidable_equality. Defined.

Definition res_step_eqb (r1 r2 : res_step) : bool := res_step_eq_dec r1 r2.
Definition eqres_stepP : Equality.axiom res_step_eqb :=
  eq_dec_Equality_axiom res_step_eq_dec.

Canonical Structure res_step_eqMixin := Equality.Mixin eqres_stepP.
Canonical Structure res_step_eqType := Eval hnf in Equality.Pack (sort := res_step) (Equality.Class res_step_eqMixin).

Definition crash_error := RS_crash C_error.

Definition depth := nat.

Definition fuel := nat.

Definition config_tuple := ((store_record * frame * list administrative_instruction)%type).

Definition config_one_tuple_without_e := (store_record * frame * list value)%type.

Definition res_tuple := (store_record * frame * res_step)%type.
(*
Fixpoint split_vals (es : list basic_instruction) : ((list value) * (list basic_instruction))%type :=
  match es with
  | (EConst v) :: es' =>
    let: (vs', es'') := split_vals es' in
    (v :: vs', es'')
  | _ => ([::], es)
  end.

(** [split_vals_e es]: takes the maximum initial segment of [es] whose elements
    are all of the form [AI_basic (EConst v)];
    returns a pair of lists [(ves, es')] where [ves] are those [v]'s in that initial
    segment and [es] is the remainder of the original [es]. **)
Fixpoint split_vals_e (es : list administrative_instruction) : ((list value) * (list administrative_instruction))%type :=
  match es with
  | (AI_basic (EConst v)) :: es' =>
    let: (vs', es'') := split_vals_e es' in
    (v :: vs', es'')
  | _ => ([::], es)
  end.

Fixpoint split_n (es : list value) (n : nat) : ((list value) * (list value))%type :=
  match (es, n) with
  | ([::], _) => ([::], [::])
  | (_, 0) => ([::], es)
  | (e :: esX, n.+1) =>
    let: (es', es'') := split_n esX n in
    (e :: es', es'')
  end.

Definition expect {A B : Type} (ao : option A) (f : A -> B) (b : B) : B :=
  match ao with
  | Some a => f a
  | None => b
  end.

Definition vs_to_es (vs : list value) : list administrative_instruction :=
  v_to_e_list (rev vs).

Definition e_is_trap (e : administrative_instruction) : bool :=
  match e with
  | AI_trap => true
  | _ => false
  end.

Lemma e_is_trapP : forall e, reflect (e = AI_trap) (e_is_trap e).
Proof.
  case => //= >; by [ apply: ReflectF | apply: ReflectT ].
Qed.

(** [es_is_trap es] is equivalent to [es == [:: AI_trap]]. **)
Definition es_is_trap (es : list administrative_instruction) : bool :=
  match es with
  | [::e] => e_is_trap e
  | _ => false
  end.

Lemma es_is_trapP : forall l, reflect (l = [::AI_trap]) (es_is_trap l).
Proof.
  case; first by apply: ReflectF.
  move=> // a l. case l => //=.
  - apply: (iffP (e_is_trapP _)); first by elim.
    by inversion 1.
  - move=> >. by apply: ReflectF.
Qed.*)

Fixpoint run_step_with_fuel (fuel : fuel) (d : depth) (cfg : config_tuple) : res_tuple :=
  let: (s, f, es) := cfg in
  match fuel with
  | 0 => (s, f, RS_crash C_exhaustion)
  | fuel.+1 =>
    let: (ves, es') := split_vals_e es in (** Framing out constants. **)
    match es' with
    | [::] => (s, f, crash_error)
    | e :: es'' =>
      if e_is_trap e
      then
        if (es'' != [::]) || (ves != [::])
        then (s, f, RS_normal [::AI_trap])
        else (s, f, crash_error)
      else
        let: (s', f', r) := run_one_step fuel d (s, f, (rev ves)) e in
        if r is RS_normal res
        then (s', f', RS_normal (res ++ es''))
        else (s', f', r)
    end
  end
    
with run_one_step (fuel : fuel) (d : depth) (cfg : config_one_tuple_without_e) (e : administrative_instruction) : res_tuple :=
  let: (s, f, ves) := cfg in
  match fuel with
  | 0 => (s, f, RS_crash C_exhaustion)
  | fuel.+1 =>
    match e with
    (* unop *)
    | AI_basic (BI_unop t op) =>
      if ves is v :: ves' then
        (s, f, RS_normal (vs_to_es (app_unop op v :: ves')))
      else (s, f, crash_error)
    (* binop *)
    | AI_basic (BI_binop t op) =>
      if ves is v2 :: v1 :: ves' then
        expect (app_binop op v1 v2)
               (fun v => (s, f, RS_normal (vs_to_es (v :: ves'))))
               (s, f, RS_normal ((vs_to_es ves') ++ [::AI_trap]))
      else (s, f, crash_error)
    (* testops *)
    | AI_basic (BI_testop T_i32 testop) =>
      if ves is (VAL_int32 c) :: ves' then
        (s, f, RS_normal (vs_to_es ((VAL_int32 (wasm_bool (@app_testop_i i32t testop c))) :: ves')))
      else (s, f, crash_error)
    | AI_basic (BI_testop T_i64 testop) =>
      if ves is (VAL_int64 c) :: ves' then
        (s, f, RS_normal (vs_to_es ((VAL_int32 (wasm_bool (@app_testop_i i64t testop c))) :: ves')))
      else (s, f, crash_error)
    | AI_basic (BI_testop _ _) => (s, f, crash_error)
    (* relops *)
    | AI_basic (BI_relop t op) =>
      if ves is v2 :: v1 :: ves' then
        (s, f, RS_normal (vs_to_es (VAL_int32 (wasm_bool (app_relop op v1 v2)) :: ves')))
      else (s, f, crash_error)
    (* convert & reinterpret *)
    | AI_basic (BI_cvtop t2 CVO_convert t1 sx) =>
      if ves is v :: ves' then
        if types_agree t1 v
        then
          expect (cvt t2 sx v) (fun v' =>
               (s, f, RS_normal (vs_to_es (v' :: ves'))))
            (s, f, RS_normal ((vs_to_es ves') ++ [::AI_trap]))
        else (s, f, crash_error)
      else (s, f, crash_error)
    | AI_basic (BI_cvtop t2 CVO_reinterpret t1 sx) =>
      if ves is v :: ves' then
        if types_agree t1 v && (sx == None)
        then (s, f, RS_normal (vs_to_es (wasm_deserialise (bits v) t2 :: ves')))
        else (s, f, crash_error)
      else (s, f, crash_error)
    (**)
    | AI_basic BI_unreachable => (s, f, RS_normal ((vs_to_es ves) ++ [::AI_trap]))
    | AI_basic BI_nop => (s, f, RS_normal (vs_to_es ves))
    | AI_basic BI_drop =>
      if ves is v :: ves' then
        (s, f, RS_normal (vs_to_es ves'))
      else (s, f, crash_error)
    | AI_basic BI_select =>
      if ves is (VAL_int32 c) :: v2 :: v1 :: ves' then
        if c == Wasm_int.int_zero i32m
        then (s, f, RS_normal (vs_to_es (v2 :: ves')))
        else (s, f, RS_normal (vs_to_es (v1 :: ves')))
      else (s, f, crash_error)
    | AI_basic (BI_block (Tf t1s t2s) es) =>
      if length ves >= length t1s
      then
        let: (ves', ves'')  := split_n ves (length t1s) in
        (s, f, RS_normal (vs_to_es ves''
                ++ [::AI_label (length t2s) [::] (vs_to_es ves' ++ to_e_list es)]))
      else (s, f, crash_error)
    | AI_basic (BI_loop (Tf t1s t2s) es) =>
      if length ves >= length t1s
      then
        let: (ves', ves'') := split_n ves (length t1s) in
        (s, f, RS_normal (vs_to_es ves''
                ++ [::AI_label (length t1s) [::AI_basic (BI_loop (Tf t1s t2s) es)]
                        (vs_to_es ves' ++ to_e_list es)]))
      else (s, f, crash_error)
    | AI_basic (BI_if tf es1 es2) =>
      if ves is VAL_int32 c :: ves' then
        if c == Wasm_int.int_zero i32m
        then (s, f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_block tf es2)]))
        else (s, f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_block tf es1)]))
      else (s, f, crash_error)
    | AI_basic (BI_br j) => (s, f, RS_break j ves)
    | AI_basic (BI_br_if j) =>
      if ves is VAL_int32 c :: ves' then
        if c == Wasm_int.int_zero i32m
        then (s, f, RS_normal (vs_to_es ves'))
        else (s, f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_br j)]))
      else (s, f, crash_error)
    | AI_basic (BI_br_table js j) =>
      if ves is VAL_int32 c :: ves' then
        let: k := Wasm_int.nat_of_uint i32m c in
        if k < length js
        then
          expect (List.nth_error js k) (fun js_at_k =>
              (s, f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_br js_at_k)])))
            (s, f, crash_error)
        else (s, f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_br j)]))
      else (s, f, crash_error)
    | AI_basic (BI_call j) =>
      if List.nth_error f.(f_inst).(inst_funcs) j is Some a then
        (s, f, RS_normal (vs_to_es ves ++ [::AI_invoke a]))
      else (s, f, crash_error)
    | AI_basic (BI_call_indirect j) =>
      if ves is VAL_int32 c :: ves' then
        match stab_addr s f (Wasm_int.nat_of_uint i32m c) with
        | Some a =>
          match List.nth_error s.(s_funcs) a with
          | Some cl =>
            if stypes s f.(f_inst) j == Some (cl_type cl)
            then (s, f, RS_normal (vs_to_es ves' ++ [::AI_invoke a]))
            else (s, f, RS_normal (vs_to_es ves' ++ [::AI_trap]))        
          | None => (s, f, crash_error)
          end
        | None => (s, f, RS_normal (vs_to_es ves' ++ [::AI_trap]))
        end
      else (s, f, crash_error)
    | AI_basic BI_return => (s, f, RS_return ves)
    | AI_basic (BI_get_local j) =>
      if j < length f.(f_locs)
      then
        expect (List.nth_error f.(f_locs) j) (fun vs_at_j =>
            (s, f, RS_normal (vs_to_es (vs_at_j :: ves))))
          (s, f, crash_error)
      else (s, f, crash_error)
    | AI_basic (BI_set_local j) =>
      if ves is v :: ves' then
        if j < length f.(f_locs)
        then (s, Build_frame (update_list_at f.(f_locs) j v) f.(f_inst), RS_normal (vs_to_es ves'))
        else (s, f, crash_error)
      else (s, f, crash_error)
    | AI_basic (BI_tee_local j) =>
      if ves is v :: ves' then
        (s, f, RS_normal (vs_to_es (v :: ves) ++ [::AI_basic (BI_set_local j)]))
      else (s, f, crash_error)
    | AI_basic (BI_get_global j) =>
      if sglob_val s f.(f_inst) j is Some xx
      then (s, f, RS_normal (vs_to_es (xx :: ves)))
      else (s, f, crash_error)
    | AI_basic (BI_set_global j) =>
      if ves is v :: ves' then
        if supdate_glob s f.(f_inst) j v is Some xx
        then (xx, f, RS_normal (vs_to_es ves'))
        else (s, f, crash_error)
      else (s, f, crash_error)
    | AI_basic (BI_load i t None a off) =>
      if ves is VAL_int32 k :: ves' then
        expect
          (smem_ind s f.(f_inst) i)
          (fun j =>
             if List.nth_error s.(s_mems) j is Some mem_s_j then
               expect
                 (load (mem_s_j) (Wasm_int.N_of_uint i32m k) off (length_t t))
                 (fun bs => (s, f, RS_normal (vs_to_es (wasm_deserialise bs t :: ves'))))
                 (s, f, RS_normal (vs_to_es ves' ++ [::AI_trap]))
             else (s, f, crash_error))
          (s, f, crash_error)
      else (s, f, crash_error)
    | AI_basic (BI_load i t (Some (tp, sx)) a off) =>
      if ves is VAL_int32 k :: ves' then
        expect
          (smem_ind s f.(f_inst) i)
          (fun j =>
             if List.nth_error s.(s_mems) j is Some mem_s_j then
               expect
                 (load_packed sx (mem_s_j) (Wasm_int.N_of_uint i32m k) off (length_tp tp) (length_t t))
                 (fun bs => (s, f, RS_normal (vs_to_es (wasm_deserialise bs t :: ves'))))
                 (s, f, RS_normal (vs_to_es ves' ++ [::AI_trap]))
             else (s, f, crash_error))
          (s, f, crash_error)
      else (s, f, crash_error)
    | AI_basic (BI_store i t None a off) =>
      if ves is v :: VAL_int32 k :: ves' then
        if types_agree t v
        then
          expect
            (smem_ind s f.(f_inst) i)
            (fun j =>
               if List.nth_error s.(s_mems) j is Some mem_s_j then
                 expect
                   (store mem_s_j (Wasm_int.N_of_uint i32m k) off (bits v) (length_t t))
                   (fun mem' =>
                      (upd_s_mem s (update_list_at s.(s_mems) j mem'), f, RS_normal (vs_to_es ves')))
                   (s, f, RS_normal (vs_to_es ves' ++ [::AI_trap]))
               else (s, f, crash_error))
            (s, f, crash_error)
        else (s, f, crash_error)
      else (s, f, crash_error)
    | AI_basic (BI_store i t (Some tp) a off) =>
      if ves is v :: VAL_int32 k :: ves' then
        if types_agree t v
        then
          expect
            (smem_ind s f.(f_inst) i)
            (fun j =>
               if List.nth_error s.(s_mems) j is Some mem_s_j then
                 expect
                   (store_packed mem_s_j (Wasm_int.N_of_uint i32m k) off (bits v) (length_tp tp))
                   (fun mem' =>
                      (upd_s_mem s (update_list_at s.(s_mems) j mem'), f, RS_normal (vs_to_es ves')))
                   (s, f, RS_normal (vs_to_es ves' ++ [::AI_trap]))
               else (s, f, crash_error))
            (s, f, crash_error)
        else (s, f, crash_error)
      else (s, f, crash_error)
    | AI_basic (BI_current_memory i) =>
      expect
        (smem_ind s f.(f_inst) i)
        (fun j =>
           if List.nth_error s.(s_mems) j is Some s_mem_s_j then
             (s, f, RS_normal (vs_to_es (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (mem_size s_mem_s_j))) :: ves)))
           else (s, f, crash_error))
        (s, f, crash_error)
    | AI_basic (BI_grow_memory i) =>
      if ves is VAL_int32 c :: ves' then
        expect
          (smem_ind s f.(f_inst) i)
          (fun j =>
            if List.nth_error s.(s_mems) j is Some s_mem_s_j then
              let: l := mem_size s_mem_s_j in
              let: mem' := mem_grow s_mem_s_j (Wasm_int.N_of_uint i32m c) in
              if mem' is Some mem'' then
                (upd_s_mem s (update_list_at s.(s_mems) j mem''), f,
                 RS_normal (vs_to_es (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat l)) :: ves')))
              else (s, f, crash_error)
            else (s, f, crash_error))
          (s, f, crash_error)
      else (s, f, crash_error)
    | AI_basic (BI_const _) => (s, f, crash_error)
    | AI_invoke a =>
      match List.nth_error s.(s_funcs) a with
      | Some cl => 
        match cl with
        | FC_func_native i (Tf t1s t2s) ts es =>
            let: n := length t1s in
            let: m := length t2s in
            if length ves >= n
            then
            let: (ves', ves'') := split_n ves n in
            let: zs := n_zeros ts in
            (s, f, RS_normal (vs_to_es ves''
                    ++ [::AI_local m (Build_frame (rev ves' ++ zs) i) [::AI_basic (BI_block (Tf [::] t2s) es)]]))
            else (s, f, crash_error)
        | FC_func_host (Tf t1s t2s) cl' =>
            let: n := length t1s in
            let: m := length t2s in
            if length ves >= n
            then
              let: (ves', ves'') := split_n ves n in
              (s, f, RS_call_host (Tf t1s t2s) cl' (rev ves'))
            (* match host_application_impl hs s (Tf t1s t2s) cl' (rev ves') with
            | (hs', Some (s', rves)) =>
                (hs', s', f, RS_normal (vs_to_es ves'' ++ (result_to_stack rves)))
            | (hs', None) => (hs', s, f, RS_normal (vs_to_es ves ++ [::AI_invoke a]))
            end *)
            else (s, f, crash_error)
        end
      | None => (s, f, crash_error)
      end
    | AI_label ln les es =>
      if es_is_trap es
      then (s, f, RS_normal (vs_to_es ves ++ [::AI_trap]))
      else
        if const_list es
        then (s, f, RS_normal (vs_to_es ves ++ es))
        else
          let: (s', f', res) := run_step_with_fuel fuel d (s, f, es) in
          match res with
          | RS_break 0 bvs =>
            if length bvs >= ln
            then (s', f', RS_normal ((vs_to_es ((take ln bvs) ++ ves)) ++ les))
            else (s', f', crash_error)
          | RS_break (n.+1) bvs => (s', f', RS_break n bvs)
          | RS_return rvs => (s', f', RS_return rvs)
          | RS_normal es' =>
            (s', f', RS_normal (vs_to_es ves ++ [::AI_label ln les es']))
          | RS_crash error => (s', f', RS_crash error)
          | RS_call_host tf h cvs => (s', f', RS_call_host tf h cvs)
          end
    | AI_local ln lf es =>
      if es_is_trap es
      then (s, f, RS_normal (vs_to_es ves ++ [::AI_trap]))
      else
        if const_list es
        then
          if length es == ln
          then (s, f, RS_normal (vs_to_es ves ++ es))
          else (s, f, crash_error)
        else
          let: (s', f', res) := run_step_with_fuel fuel d (s, lf, es) in
          match res with
          | RS_return rvs =>
            if length rvs >= ln
            then (s', f, RS_normal (vs_to_es (take ln rvs ++ ves)))
            else (s', f, crash_error)
          | RS_normal es' =>
            (s', f, RS_normal (vs_to_es ves ++ [::AI_local ln f' es']))
          | RS_crash error => (s', f, RS_crash error)
          | RS_break _ _ => (s', f, crash_error)
          | RS_call_host tf h cvs => (s', f', RS_call_host tf h cvs)
          end
    | AI_trap => (s, f, crash_error)
    | AI_call_host tf h vcs => (s, f, RS_call_host tf h vcs)
    end
  end.

(** Enough fuel so that [run_one_step] does not run out of exhaustion. **)
Definition run_one_step_fuel : administrative_instruction -> nat.
Proof.
  move=> es. induction es using administrative_instruction_rect';
    let rec aux v :=
      lazymatch goal with
      | F : TProp.Forall _ _ |- _ =>
        apply TProp.max in F;
        move: F;
        let n := fresh "n" in
        move=> n;
        aux (n + v)
      | |- _ => exact (v.+1)
      end in
    aux (1 : nat).
Defined.

(** Enough fuel so that [run_step] does not run out of exhaustion. **)
Definition run_step_fuel (cfg : config_tuple) : nat :=
  let: (s, f, es) := cfg in
  1 + List.fold_left max (List.map run_one_step_fuel es) 0.

Definition run_step (d : depth) (cfg : config_tuple) : res_tuple :=
  run_step_with_fuel (run_step_fuel cfg) d cfg.

Fixpoint run_v (fuel : fuel) (d : depth) (cfg : config_tuple) : ((store_record * res)%type) :=
  let: (s, f, es) := cfg in
  match fuel with
  | 0 => (s, R_crash C_exhaustion)
  | fuel.+1 =>
    if es_is_trap es
    then (s, R_trap)
    else
      if const_list es
      then (s, R_value (fst (split_vals_e es)))
      else
        let: (s', f', res) := run_step d (s, f, es) in
        match res with
        | RS_normal es' => run_v fuel d (s', f', es')
        | RS_crash error => (s', R_crash error)
        | RS_call_host tf h cvs => (s', R_call_host tf h cvs)
        | _ => (s', R_crash C_error)
        end
  end.


