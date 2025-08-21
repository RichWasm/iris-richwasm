(** Wasm: Instrumented operational semantics **)
(** This module defines an operational semantics that instruments the
    small-step semantics from opsem.v in order to classify traps. *)

From Wasm Require Import opsem.
From Coq Require Import ZArith.BinInt.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From RichWasm Require Import obs.
Require Export Wasm.operations (* host *).

Set Bullet Behavior "Strict Subproofs".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.

Inductive reduce_simple : obs -> seq.seq administrative_instruction -> obs -> seq.seq administrative_instruction -> Prop :=
(** unop **)
  | rs_unop : forall v op t,
    reduce_simple Run [::AI_basic (BI_const v); AI_basic (BI_unop t op)] Run [::AI_basic (BI_const (@app_unop op v))]
                   
(** binop **)
  | rs_binop_success : forall v1 v2 v op t,
    app_binop op v1 v2 = Some v ->
    reduce_simple Run [::AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] Run [::AI_basic (BI_const v)]
  | rs_binop_failure : forall v1 v2 op t,
    app_binop op v1 v2 = None ->
    reduce_simple Run [::AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] Bail [::AI_trap]

  (** testops **)
  | rs_testop_i32 :
    forall c testop,
    reduce_simple Run [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_testop T_i32 testop)] Run [::AI_basic (BI_const (VAL_int32 (wasm_bool (@app_testop_i i32t testop c))))]
  | rs_testop_i64 :
    forall c testop,
    reduce_simple Run [::AI_basic (BI_const (VAL_int64 c)); AI_basic (BI_testop T_i64 testop)] Run [::AI_basic (BI_const (VAL_int32 (wasm_bool (@app_testop_i i64t testop c))))]

                  
  (** relops **)
  | rs_relop: forall v1 v2 t op,
    reduce_simple Run [::AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_relop t op)] Run [::AI_basic (BI_const (VAL_int32 (wasm_bool (app_relop op v1 v2))))]
                    
  (** convert and reinterpret **)
  | rs_convert_success :
    forall t1 t2 v v' sx,
    types_agree t1 v ->
    cvt t2 sx v = Some v' ->
    reduce_simple Run [::AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] Run [::AI_basic (BI_const v')]
  | rs_convert_failure :
    forall t1 t2 v sx,
    types_agree t1 v ->
    cvt t2 sx v = None ->
    reduce_simple Run [::AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] Crash [::AI_trap]
  | rs_reinterpret :
    forall t1 t2 v,
    types_agree t1 v ->
    reduce_simple Run [::AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] Run [::AI_basic (BI_const (wasm_deserialise (bits v) t2))]

  (** control-flow operations **)
  | rs_unreachable :
    reduce_simple Run [::AI_basic BI_unreachable] Bail [::AI_trap]
  | rs_nop :
    reduce_simple Run [::AI_basic BI_nop] Run [::]
  | rs_drop :
    forall v,
    reduce_simple Run [::AI_basic (BI_const v); AI_basic BI_drop] Run [::]
  | rs_select_false :
    forall n v1 v2,
    n = Wasm_int.int_zero i32m ->
    reduce_simple Run [::AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_const (VAL_int32 n)); AI_basic BI_select] Run [::AI_basic (BI_const v2)]
  | rs_select_true :
    forall n v1 v2,
    n <> Wasm_int.int_zero i32m ->
    reduce_simple Run [::AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_const (VAL_int32 n)); AI_basic BI_select] Run [::AI_basic (BI_const v1)]
  | rs_block :
      forall vs es n m t1s t2s,
        const_list vs ->
        length vs = n ->
        length t1s = n ->
        length t2s = m ->
        reduce_simple Run (vs ++ [::AI_basic (BI_block (Tf t1s t2s) es)]) Run [::AI_label m [::] (vs ++ to_e_list es)]
  | rs_loop :
      forall vs es n m t1s t2s,
        const_list vs ->
        length vs = n ->
        length t1s = n ->
        length t2s = m ->
        reduce_simple Run (vs ++ [::AI_basic (BI_loop (Tf t1s t2s) es)]) Run [::AI_label n [::AI_basic (BI_loop (Tf t1s t2s) es)] (vs ++ to_e_list es)]
  | rs_if_false :
      forall n tf e1s e2s,
        n = Wasm_int.int_zero i32m ->
        reduce_simple Run ([::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)]) Run [::AI_basic (BI_block tf e2s)]
  | rs_if_true :
      forall n tf e1s e2s,
        n <> Wasm_int.int_zero i32m ->
        reduce_simple Run ([::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)]) Run [::AI_basic (BI_block tf e1s)]
  | rs_label_const :
      forall n es vs,
        const_list vs ->
        reduce_simple Run [::AI_label n es vs] Run vs
  | rs_label_trap :
      forall n es o,
        reduce_simple o [::AI_label n es [::AI_trap]] o [::AI_trap]
  | rs_br :
      forall n vs es i LI lh,
        const_list vs ->
        length vs = n ->
        lfilled i lh (vs ++ [::AI_basic (BI_br i)]) LI ->
        reduce_simple Run [::AI_label n es LI] Run (vs ++ es)
  | rs_br_if_false :
      forall n i,
        n = Wasm_int.int_zero i32m ->
        reduce_simple Run [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_br_if i)] Run [::]
  | rs_br_if_true :
      forall n i,
        n <> Wasm_int.int_zero i32m ->
        reduce_simple Run [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_br_if i)] Run [::AI_basic (BI_br i)]
  | rs_br_table : (* ??? *)
      forall iss c i j,
        length iss > Wasm_int.nat_of_uint i32m c ->
        List.nth_error iss (Wasm_int.nat_of_uint i32m c) = Some j ->
        reduce_simple Run [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] Run [::AI_basic (BI_br j)]
  | rs_br_table_length :
      forall iss c i,
        length iss <= (Wasm_int.nat_of_uint i32m c) ->
        reduce_simple Run [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] Run [::AI_basic (BI_br i)]
  | rs_local_const :
      forall es n f,
        const_list es ->
        length es = n ->
        reduce_simple Run [::AI_local n f es] Run es
  | rs_local_trap :
      forall o n f,
        reduce_simple o [::AI_local n f [::AI_trap]] o [::AI_trap]
  | rs_return : (* ??? *)
      forall n i vs es lh f,
        const_list vs ->
        length vs = n ->
        lfilled i lh (vs ++ [::AI_basic BI_return]) es ->
        reduce_simple Run [::AI_local n f es] Run vs
  | rs_tee_local :
      forall i v,
        is_const v ->
        reduce_simple Run [::v; AI_basic (BI_tee_local i)] Run [::v; v; AI_basic (BI_set_local i)]
  | rs_trap :
      forall es lh o,
        es <> [::AI_trap] ->
        lfilled 0 lh [::AI_trap] es ->
        reduce_simple o es o [::AI_trap]
  .

Inductive reduce : obs -> store_record -> frame -> list administrative_instruction ->
                   obs -> store_record -> frame -> list administrative_instruction -> Prop :=
  | r_simple :
      forall o o' e e' s f,
        reduce_simple o e o' e' ->
        reduce o s f e o' s f e'

  (** calling operations **)
  | r_call :
      forall s f i a,
        List.nth_error f.(f_inst).(inst_funcs) i = Some a ->
        reduce Run s f [::AI_basic (BI_call i)] Run s f [::AI_invoke a]
  | r_call_indirect_success :
      forall s f i a cl c ,
        stab_addr s f (Wasm_int.nat_of_uint i32m c) = Some a ->
        List.nth_error s.(s_funcs) a = Some cl ->
        stypes s f.(f_inst) i = Some (cl_type cl) ->
        reduce Run s f [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] Run s f [::AI_invoke a]
  | r_call_indirect_failure1 :
      forall s f i a cl c,
        stab_addr s f (Wasm_int.nat_of_uint i32m c) = Some a ->
        List.nth_error s.(s_funcs) a = Some cl ->
        stypes s f.(f_inst) i <> Some (cl_type cl) ->
        reduce Run s f [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] Crash s f [::AI_trap]
  | r_call_indirect_failure2 :
      forall s f i c,
        stab_addr s f (Wasm_int.nat_of_uint i32m c) = None ->
        reduce Run s f [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] Crash s f [::AI_trap]
  | r_invoke_native :
      forall a cl t1s t2s ts es ves vcs n m k zs s f f' i,
        List.nth_error s.(s_funcs) a = Some cl ->
        cl = FC_func_native i (Tf t1s t2s) ts es ->
        ves = v_to_e_list vcs ->
        length vcs = n ->
        length ts = k ->
        length t1s = n ->
        length t2s = m ->
        n_zeros ts = zs ->
        f'.(f_inst) = i ->
        f'.(f_locs) = vcs ++ zs ->
        reduce Run s f (ves ++ [::AI_invoke a]) Run s f [::AI_local m f' [::AI_basic (BI_block (Tf [::] t2s) es)]]
  | r_invoke_host :
      forall a cl h t1s t2s ves vcs m n s f,
        List.nth_error s.(s_funcs) a = Some cl ->
        cl = FC_func_host (Tf t1s t2s) h ->
        ves = v_to_e_list vcs ->
        length vcs = n ->
        length t1s = n ->
        length t2s = m ->
        reduce Run s f (ves ++ [::AI_invoke a]) Run s f [:: AI_call_host (Tf t1s t2s) h vcs]


  (** get, set, load, and store operations **)
  | r_get_local :
      forall f v j s,
        List.nth_error f.(f_locs) j = Some v ->
        reduce Run s f [::AI_basic (BI_get_local j)] Run s f [::AI_basic (BI_const v)]
  | r_set_local :
      forall f f' i v s vd,
        f'.(f_inst) = f.(f_inst) ->
        i < length f.(f_locs) ->
        f'.(f_locs) = set_nth vd f.(f_locs) i v ->
        reduce Run s f [::AI_basic (BI_const v); AI_basic (BI_set_local i)] Run s f' [::]
  | r_get_global :
      forall s f i v,
        sglob_val s f.(f_inst) i = Some v ->
        reduce Run s f [::AI_basic (BI_get_global i)] Run s f [::AI_basic (BI_const v)]
  | r_set_global :
      forall s f i v s',
        supdate_glob s f.(f_inst) i v = Some s' ->
        reduce Run s f [::AI_basic (BI_const v); AI_basic (BI_set_global i)] Run s' f [::]
  | r_load_success :
    forall s i f t bs k a off m im,
      smem_ind s f.(f_inst) im = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      load m (Wasm_int.N_of_uint i32m k) off (length_t t) = Some bs ->
      reduce Run s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_load im t None a off)] Run s f [::AI_basic (BI_const (wasm_deserialise bs t))]
  | r_load_failure :
    forall s i f t k a off m im,
      smem_ind s f.(f_inst) im = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      load m (Wasm_int.N_of_uint i32m k) off (length_t t) = None ->
      reduce Run s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_load im t None a off)] Crash s f [::AI_trap]
  | r_load_packed_success :
    forall s i f t tp k a off m bs sx im,
      smem_ind s f.(f_inst) im = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      load_packed sx m (Wasm_int.N_of_uint i32m k) off (length_tp tp) (length_t t) = Some bs ->
      reduce Run s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_load im t (Some (tp, sx)) a off)] Run s f [::AI_basic (BI_const (wasm_deserialise bs t))]
  | r_load_packed_failure :
    forall s i f t tp k a off m sx im,
      smem_ind s f.(f_inst) im = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      load_packed sx m (Wasm_int.N_of_uint i32m k) off (length_tp tp) (length_t t) = None ->
      reduce Run s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_load im t (Some (tp, sx)) a off)] Crash s f [::AI_trap]
  | r_store_success :
    forall t v s i f mem' k a off m im,
      types_agree t v ->
      smem_ind s f.(f_inst) im = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store m (Wasm_int.N_of_uint i32m k) off (bits v) (length_t t) = Some mem' ->
      reduce Run s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_const v); AI_basic (BI_store im t None a off)] Run (upd_s_mem s (update_list_at s.(s_mems) i mem')) f [::]
  | r_store_failure :
    forall t v s i f m k off a im,
      types_agree t v ->
      smem_ind s f.(f_inst) im = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store m (Wasm_int.N_of_uint i32m k) off (bits v) (length_t t) = None ->
      reduce Run s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_const v); AI_basic (BI_store im t None a off)] Crash s f [::AI_trap]
  | r_store_packed_success :
    forall t v s i f m k off a mem' tp im,
      types_agree t v ->
      smem_ind s f.(f_inst) im = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store_packed m (Wasm_int.N_of_uint i32m k) off (bits v) (length_tp tp) = Some mem' ->
      reduce Run s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_const v); AI_basic (BI_store im t (Some tp) a off)] Run (upd_s_mem s (update_list_at s.(s_mems) i mem')) f [::]
  | r_store_packed_failure :
    forall t v s i f m k off a tp im,
      types_agree t v ->
      smem_ind s f.(f_inst) im = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store_packed m (Wasm_int.N_of_uint i32m k) off (bits v) (length_tp tp) = None ->
      reduce Run s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_const v); AI_basic (BI_store im t (Some tp) a off)] Crash s f [::AI_trap]

  (** memory **)
  | r_current_memory :
      forall i f m n s im,
        smem_ind s f.(f_inst) im = Some i ->
        List.nth_error s.(s_mems) i = Some m ->
        mem_size m = n ->
        reduce Run s f [::AI_basic (BI_current_memory im)] Run s f [::AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat n))))]
  | r_grow_memory_success :
    forall s i f m n mem' c im,
      smem_ind s f.(f_inst) im = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      mem_size m = n ->
      mem_grow m (Wasm_int.N_of_uint i32m c) = Some mem' ->
      reduce Run s f [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_grow_memory im)] Run (upd_s_mem s (update_list_at s.(s_mems) i mem')) f [::AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat n))))]
  | r_grow_memory_failure :
      forall i f m n s c im,
        smem_ind s f.(f_inst) im = Some i ->
        List.nth_error s.(s_mems) i = Some m ->
        mem_size m = n ->
        reduce Run s f [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_grow_memory im)] Run s f [::AI_basic (BI_const (VAL_int32 int32_minus_one))]

  (** label and local **)
  | r_label :
      forall o s f es les o' s' f' es' les' k lh,
        reduce o s f es o' s' f' es' ->
        lfilled k lh es les ->
        lfilled k lh es' les' ->
        reduce o s f les o' s' f' les'
  | r_local :
      forall o s f es o' s' f' es' n f0,
        reduce o s f es o' s' f' es' ->
        reduce o s f0 [::AI_local n f es] o' s' f0 [::AI_local n f' es']
  .

Definition reduce_tuple o_s_f_es o'_s'_f'_es' : Prop :=
  let '(o, s, f, es) := o_s_f_es in
  let '(o', s', f', es') := o'_s'_f'_es' in
  reduce o s f es o' s' f' es'.

Definition reduce_trans :
    obs * store_record * frame * seq.seq administrative_instruction ->
    obs * store_record * frame * seq.seq administrative_instruction -> Prop :=
  Relations.Relation_Operators.clos_refl_trans _ reduce_tuple.

End Host.
