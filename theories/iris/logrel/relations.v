Require Import iris.proofmode.tactics.

From RichWasm.compiler Require Import codegen util instrs.
From RichWasm.iris Require Import gc memory.
From RichWasm.iris.language Require Import iris_wp_def lenient_wp logpred.
From RichWasm Require Import syntax typing layout util.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Relations.
  Context `{Σ: gFunctors}.
  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!RichWasmGCG Σ}.

  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Definition ns_fun (n : N) : namespace := nroot .@ "rwf" .@ n.
  Definition ns_ref (n : N) : namespace := nroot .@ "rwr" .@ n.
  Definition ns_tab (n : N) : namespace := nroot .@ "rwt" .@ n.
  Definition ns_glo (n : N) : namespace := nroot .@ "rwg" .@ n.

  Inductive semantic_value :=
  | SValues (vs : list value)
  | SWords (cm : concrete_memory) (ws : list word).

  Definition semantic_type := (leibnizO semantic_value -n> iProp Σ).
  Notation semantic_kind := (semantic_type -> iProp Σ).
  Notation semantic_env := (list.listO semantic_type).

  Notation SVR := (leibnizO semantic_value -n> iPropO Σ).
  Notation LVR := (leibnizO val -n> iPropO Σ).
  Notation VsR := (leibnizO (list value) -n> iPropO Σ).
  Notation FrR := (leibnizO frame -n> iPropO Σ).
  Notation ClR := (leibnizO function_closure -n> iPropO Σ).
  Notation ER := (leibnizO (list administrative_instruction) -n> iPropO Σ).

  Implicit Type L : leibnizO local_ctx.
  Implicit Type WL : leibnizO wlocal_ctx.

  Implicit Type es : leibnizO (list administrative_instruction).
  Implicit Type sv : leibnizO semantic_value.
  Implicit Type lv : leibnizO val.
  Implicit Type vs : leibnizO (list value).
  Implicit Type ws : leibnizO (list word).
  Implicit Type bs : leibnizO bytes.
  Implicit Type fr : leibnizO frame.
  Implicit Type cl : leibnizO function_closure.
  Implicit Type inst : leibnizO instance.

  Implicit Type τ : leibnizO type.
  Implicit Type τs : leibnizO (list type).
  Implicit Type ϕ : leibnizO function_type.
  Implicit Type ψ : leibnizO instruction_type.

  Notation value_relation := (semantic_env -n> leibnizO type -n> SVR).

  Definition value_type_interp (ty : W.value_type) (v : value) : Prop :=
    match ty with
    | T_i32 => exists n, v = VAL_int32 n
    | T_i64 => exists n, v = VAL_int64 n
    | T_f32 => exists n, v = VAL_float32 n
    | T_f64 => exists n, v = VAL_float64 n
    end.

  Definition result_type_interp (tys : W.result_type) (vs : list value) : Prop :=
    Forall2 value_type_interp tys vs.

  Definition primitive_rep_interp (ι : primitive_rep) (v : value) : Prop :=
    match ι with
    | PtrR => exists n, v = VAL_int32 n
    | I32R => exists n, v = VAL_int32 n
    | I64R => exists n, v = VAL_int64 n
    | F32R => exists n, v = VAL_float32 n
    | F64R => exists n, v = VAL_float64 n
    end.

  Definition representation_interp0 (ρ : representation) (vs : list value) : Prop :=
    exists ιs, eval_rep ρ = Some ιs /\ Forall2 primitive_rep_interp ιs vs.

  Definition representation_interp (ρ : representation) : semantic_type :=
    λne sv, (∃ vs, ⌜sv = SValues vs⌝ ∗ ⌜representation_interp0 ρ vs⌝)%I.
  
  Definition is_copy_operation (ρ: representation) (es: expr) : Prop :=
    ∃ fe me wl wl' (es': codegen.W.expr),
      run_codegen (idx ← save_stack_r fe ρ;
                   dup_roots_local me idx ρ;;
                   restore_stack_r idx ρ;;
                   restore_stack_r idx ρ) wl = inr ((), wl', es') /\
      to_e_list es' = es.
    
  Definition explicit_copy_spec (ρ: representation) (T: semantic_type) : iProp Σ :=
    ∀ fr vs es,
      ⌜is_copy_operation ρ es⌝ -∗
      ↪[frame] fr -∗
      ↪[RUN] -∗
      T (SValues vs) -∗
      lenient_wp NotStuck top (v_to_e_list vs ++ es)
        {| lp_fr := λ fr', ⌜fr = fr'⌝;
           lp_val := λ vs', (∃ vs1 vs2, ⌜vs' = vs1 ++ vs2⌝ ∗
                                          T (SValues vs1) ∗
                                          T (SValues vs2)) ∗
                            ↪[RUN];
           lp_trap := False;
           lp_br := λ _, False;
           lp_ret := λ _, False;
           lp_host := λ _ _ _ _, False |}.
      
                            
  Definition copyability_interp (ρ: representation) (χ : copyability) (T : semantic_type) : iProp Σ :=
    match χ with
    | NoCopy => True
    | ExCopy => explicit_copy_spec ρ T
    | ImCopy => ⌜forall sv, Persistent (T sv)⌝
    end.

  Definition size_interp (σ : size) (ws : list word) : Prop :=
    eval_size σ = Some (length ws).

  Definition sizity_interp (ζ : sizity) : semantic_type :=
    λne sv, ⌜∃ μ ws, sv = SWords μ ws /\ ∀ σ, ζ = Sized σ -> size_interp σ ws⌝%I.

  Definition memory_interp (μ : memory) : semantic_type :=
    λne sv, ⌜∃ cm ws, μ = ConstM cm /\ sv = SWords cm ws⌝%I.

  (* S refines T, written S ⊑ T. *)
  Definition semantic_type_le (S T : semantic_type) : Prop := forall sv, S sv -∗ T sv.

  #[export]
  Instance SqSubsetEq_semantic_type : SqSubsetEq semantic_type := semantic_type_le.

  Definition kind_as_type_interp (κ : kind) : semantic_type :=
    match κ with
    | VALTYPE ρ χ _ => representation_interp ρ
    | MEMTYPE ζ μ _ => λne sv, sizity_interp ζ sv ∗ memory_interp μ sv
    end%I.

  Definition kind_interp (κ : kind) : semantic_kind :=
    fun T =>
      (⌜T ⊑ kind_as_type_interp κ⌝ ∗
       match κ with
       | VALTYPE ρ χ _ => copyability_interp ρ χ T
       | MEMTYPE ζ μ δ => True
       end)%I.

  Definition values_interp0 (vrel : value_relation) (se : semantic_env) :
    leibnizO (list type) -n> VsR :=
    λne τs vs, (∃ vss, ⌜vs = concat vss⌝ ∗ [∗ list] τ; vs ∈ τs; vss, vrel se τ (SValues vs))%I.

  Definition mono_closure_interp0 (vrel : value_relation) (se : semantic_env) :
    leibnizO instruction_type -n> ClR :=
    λne ψ cl,
      let 'InstrT τs1 τs2 := ψ in
      match cl with
      | FC_func_native inst (Tf tfs1 tfs2) tlocs es =>
          ⌜translate_types [] τs1 = Some tfs1⌝ ∗
          ⌜translate_types [] τs2 = Some tfs2⌝ ∗
          ∀ vs1 fr,
            values_interp0 vrel se τs1 vs1 -∗
            ↪[frame] fr -∗
            lenient_wp NotStuck top
              [AI_local (length tfs2) (Build_frame (vs1 ++ n_zeros tlocs) inst) (to_e_list es)]
              {| lp_fr := fun fr' => ⌜fr = fr'⌝;
                 lp_val := fun vs2 => values_interp0 vrel se τs2 vs2 ∗ ↪[RUN];
                 lp_trap := True;
                 lp_br := fun _ => False;
                 lp_ret := fun _ => False;
                 lp_host := fun _ _ _ _ => False |}
        | FC_func_host _ _ => False
        end%I.

  Definition closure_interp0 (vrel : value_relation) (se : semantic_env) :
    leibnizO function_type -n> ClR :=
    λne ϕ cl,
      let fix go se ϕ s__mem s__rep s__size :=
        match ϕ with
        | MonoFunT ψ =>
            let ψ' := subst_instruction_type s__mem s__rep s__size VarT ψ in
            mono_closure_interp0 vrel se ψ' cl
        | ForallMemT ϕ' => ∀ μ, go se ϕ' (unscoped.scons μ s__mem) s__rep s__size
        | ForallRepT ϕ' => ∀ ρ, go se ϕ' s__mem (unscoped.scons ρ s__rep) s__size
        | ForallSizeT ϕ' => ∀ σ, go se ϕ' s__mem s__rep (unscoped.scons σ s__size)
        | ForallTypeT κ ϕ' => ∀ T, kind_interp κ T -∗ go (T :: se) ϕ' s__mem s__rep s__size
        end%I
      in
      go se ϕ VarM VarR VarS.

  Definition type_interp0 (vrel : value_relation) (se : semantic_env) : leibnizO type -n> SVR :=
    λne τ sv,
      match τ with
      | VarT t => (default (λne _, False) (se !! t)) sv
      | NumT _ _ => True
      | SumT (VALTYPE ρ _ _) τs =>
          ∃ i vs vs0 τ0 ρs ρ0 ixs,
            ⌜sv = SValues (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat i)) :: vs)⌝ ∗
              ⌜ρ = SumR ρs⌝ ∗
              ⌜τs !! i = Some τ⌝ ∗
              ⌜type_rep [] τ0 = Some ρ0⌝ ∗
              ⌜inject_sum_rep ρs ρ = Some ixs⌝ ∗
              ⌜nths_error vs ixs = Some vs0⌝ ∗
              ▷ vrel se τ0 (SValues vs0)
      | SumT (MEMTYPE _ (VarM _) _) _ => False
      | SumT (MEMTYPE _ (ConstM cm) _) τs =>
          ∃ wᵢ ws ws' bsᵢ i τ,
            ⌜sv = SWords cm (wᵢ :: ws ++ ws')⌝ ∗
              ⌜bsᵢ = serialize_Z_i32 (Z.of_nat i)⌝ ∗
              ⌜repr_word sr.(sr_gc_heap_start) ∅ wᵢ i⌝ ∗
              ⌜τs !! i = Some τ⌝ ∗
              ▷ vrel se τ (SWords cm ws)
      | ProdT (VALTYPE _ _ _) τs =>
          ∃ vss, ⌜sv = SValues (concat vss)⌝ ∗ [∗ list] vs; τ ∈ vss; τs, ▷ vrel se τ (SValues vs)
      | ProdT (MEMTYPE _ (VarM _) _) _ => False
      | ProdT (MEMTYPE _ (ConstM cm) _) τs =>
          ∃ wss,
            ⌜sv = SWords cm (concat wss)⌝ ∗ [∗ list] ws; τ ∈ wss; τs, ▷ vrel se τ (SWords cm ws)
      | RefT _ (VarM _) _ => False
      | RefT _ (ConstM MemMM) τ =>
          ∃ a ws ns bs,
            ⌜sv = SValues [VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N a))]⌝ ∗
              N.of_nat sr.(sr_mem_mm) ↦[wms][a] bs ∗
              ⌜repr_list_word sr.(sr_gc_heap_start) ∅ ws ns⌝ ∗
              ⌜bs = flat_map serialize_Z_i32 ns⌝ ∗
              ▷ vrel se τ (SWords MemMM ws)
      | RefT _ (ConstM MemGC) τ =>
          ∃ a ℓ,
            ⌜sv = SValues [VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N a))]⌝ ∗
              a ↦gcr ℓ ∗
              na_inv logrel_nais (ns_ref ℓ) (∃ ws, ℓ ↦gco ws ∗ ▷ vrel se τ (SWords MemGC ws))
      | GCPtrT _ τ =>
          ∃ ℓ,
            ⌜sv = SWords MemGC [WordPtr (PtrGC ℓ)]⌝ ∗
              na_inv logrel_nais (ns_ref ℓ) (∃ ws, ℓ ↦gco ws ∗ ▷ vrel se τ (SWords MemGC ws))
      | CodeRefT _ ϕ =>
          ∃ n cl,
            ⌜sv = SValues [VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N n))]⌝ ∗
              ▷ closure_interp0 vrel se ϕ cl ∗
              na_inv logrel_nais (ns_fun n) (n ↦[wf] cl)
      | RepT _ ρ' τ =>
          ∃ ρ ιs ιs' vs vs' rvs rvs' wss wss' ws,
            ⌜sv = SValues vs'⌝ ∗
              ⌜type_rep [] τ = Some ρ⌝ ∗
              ⌜eval_rep ρ = Some ιs⌝ ∗
              ⌜eval_rep ρ' = Some ιs'⌝ ∗
              ⌜to_rep_values ιs vs = Some rvs⌝ ∗
              ⌜to_rep_values ιs' vs' = Some rvs'⌝ ∗
              ⌜Forall2 (ser_value sr.(sr_gc_heap_start)) rvs wss⌝ ∗
              ⌜Forall2 (ser_value sr.(sr_gc_heap_start)) rvs' wss'⌝ ∗
              ⌜concat wss ++ ws = concat wss'⌝ ∗
              ▷ vrel se τ (SValues vs)
      | PadT (VALTYPE _ _ _) _ _ => False
      | PadT (MEMTYPE _ (VarM _) _) _ _ => False
      | PadT (MEMTYPE _ (ConstM cm) _) _ τ =>
          ∃ ws ws', ⌜sv = SWords cm (ws ++ ws')⌝ ∗ ▷ vrel se τ (SWords cm ws)
      | SerT (VALTYPE _ _ _) _ => False
      | SerT (MEMTYPE _ (VarM _) _) _ => False
      | SerT (MEMTYPE _ (ConstM cm) _) τ =>
          ∃ ρ ιs vs rvs ws wss,
            ⌜sv = SWords cm ws⌝ ∗
              ⌜type_rep [] τ = Some ρ⌝ ∗
              ⌜eval_rep ρ = Some ιs⌝ ∗
              ⌜to_rep_values ιs vs = Some rvs⌝ ∗
              ⌜Forall2 (ser_value sr.(sr_gc_heap_start)) rvs wss⌝ ∗
              ⌜ws = concat wss⌝ ∗
              ▷ vrel se τ (SValues vs)
      | RecT κ τ =>
          let τ' := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
          ▷ vrel se τ' sv
      | ExistsMemT _ τ =>
          ∃ μ,
            let τ' := subst_type (unscoped.scons μ VarM) VarR VarS VarT τ in
            ▷ vrel se τ' sv
      | ExistsRepT _ τ =>
          ∃ ρ,
            let τ' := subst_type VarM (unscoped.scons ρ VarR) VarS VarT τ in
            ▷ vrel se τ' sv
      | ExistsSizeT _ τ =>
          ∃ σ,
            let τ' := subst_type VarM VarR (unscoped.scons σ VarS) VarT τ in
            ▷ vrel se τ' sv
      | ExistsTypeT _ κ τ => ∃ T, ▷ kind_interp κ T ∗ ▷ vrel (T :: se) τ sv
      end%I.

  Definition value_se_interp0 (vrel : value_relation) (se : semantic_env) : leibnizO type -n> SVR :=
    λne τ sv,
      (∃ κ, ⌜type_kind [] τ = Some κ⌝ ∗ kind_as_type_interp κ sv ∗ type_interp0 vrel se τ sv)%I.

  (* TODO *)
  Local Instance NonExpansive_value_se_interp0 (vrel : value_relation) :
    NonExpansive (λ se, λne τ sv, value_se_interp0 vrel se τ sv).
  Admitted.

  Definition value_interp0 (vrel : value_relation) : value_relation :=
    λne se τ sv, value_se_interp0 vrel se τ sv.

  (* TODO *)
  Instance Contractive_value_interp0 : Contractive value_interp0.
  Admitted.

  Definition value_interp : semantic_env -n> leibnizO type -n> SVR := fixpoint value_interp0.

  Lemma value_interp_eq se τ sv :
    value_interp se τ sv ⊣⊢ value_interp0 value_interp se τ sv.
  Proof.
    do 3 f_equiv.
    apply fixpoint_unfold.
  Qed.

  Definition values_interp (se : semantic_env) : leibnizO (list type) -n> VsR :=
    values_interp0 value_interp se.

  Definition closure_interp (se : semantic_env) : leibnizO function_type -n> ClR :=
    closure_interp0 value_interp se.

  Definition frame_interp (se : semantic_env) :
    leibnizO local_ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> FrR :=
    λne L WL inst fr,
      (∃ vs__L vs__WL,
         ⌜fr = Build_frame (vs__L ++ vs__WL) inst⌝ ∗
           values_interp se L vs__L ∗
           ⌜result_type_interp WL vs__WL⌝ ∗
           na_own logrel_nais ⊤)%I.

  Definition expr_interp (se : semantic_env) :
    leibnizO (list type) -n> leibnizO function_ctx -n> leibnizO local_ctx -n> leibnizO wlocal_ctx -n>
      leibnizO instance -n> leibnizO lholed -n> ER :=
    λne τs F L WL inst lh es,
      lenient_wp NotStuck top es
                 {| lp_fr := frame_interp se L WL inst;
                    lp_val := fun vs => values_interp se τs vs ∗ ↪[RUN];
                    lp_trap := True;
                    lp_br := fun _ => True; (* TODO *)
                    lp_ret := fun _ => True; (* TODO *)
                    lp_host := fun _ _ _ _ => False |}%I.

  Definition instance_interp (M : module_ctx) (inst : instance) : iProp Σ :=
    (* TODO: alloc_mm spec *)
    (* TODO: alloc_gc spec *)
    (* TODO: free spec *)
    (* TODO: registerroot spec *)
    (* TODO: duproot spec *)
    (* TODO: unregisterroot spec *)
    ([∗ list] i ↦ ϕ ∈ M.(mc_functions),
       ∃ cl,
         let n := N.of_nat (i + funcimm mr.(mr_func_user)) in
         na_inv logrel_nais (ns_fun n) (n ↦[wf] cl) ∗ closure_interp [] ϕ cl) ∗
      ⌜inst.(inst_tab) !! tableimm mr.(mr_table) = Some sr.(sr_table)⌝ ∗
      (∃ off,
         let n_off := N.of_nat (globalimm mr.(mr_global_table_offset)) in
         let v_off := VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat off)) in
         n_off ↦[wg] Build_global MUT_mut v_off ∗
           ([∗ list] i ↦ ϕ ∈ M.(mc_table),
              ∃ i' cl,
                let nt := N.of_nat (off + i) in
                let nf := N.of_nat i' in
                na_inv logrel_nais (ns_tab nt) (N.of_nat sr.(sr_table) ↦[wt][nt] Some i') ∗
                na_inv logrel_nais (ns_fun nf) (nf ↦[wf] cl) ∗ closure_interp [] ϕ cl)) ∗
      ⌜inst.(inst_memory) !! memimm mr.(mr_mem_mm) = Some sr.(sr_mem_mm)⌝ ∗
      ⌜inst.(inst_memory) !! memimm mr.(mr_mem_gc) = Some sr.(sr_mem_gc)⌝ ∗
      ([∗ list] i ↦ '(m, τ) ∈ M.(mc_globals),
         let n := N.of_nat (globalimm mr.(mr_global_user) + i) in
         let m' := translate_mut m in
         na_inv logrel_nais (ns_glo n)
           (∃ vs, value_interp [] τ (SValues vs) ∗
                    [∗ list] j ↦ v ∈ vs, (n + N.of_nat j)%N ↦[wg] Build_global m' v)).

  Definition lholed_interp (F : function_ctx) (L L' : local_ctx) (inst : instance) (lh : lholed) :
    iProp Σ :=
    True. (* TODO *)

  Definition memory_closed (m: memory) :=
    match m with
    | VarM _ => False
    | ConstM _ => True
    end.
  
  Fixpoint repr_closedb (ρ: representation) : bool :=
    match ρ with
    | VarR x => false
    | SumR ρs 
    | ProdR ρs => forallb repr_closedb ρs
    | PrimR _ => true
    end.

  Definition repr_closed ρ : Prop := repr_closedb ρ.
      
  Fixpoint size_closedb (σ : size) : bool :=
    match σ with
    | VarS x => false
    | SumS σs
    | ProdS σs => forallb size_closedb σs
    | RepS ρ => repr_closedb ρ
    | ConstS _ => true
    end.
  
  Definition size_closed (σ : size) : Prop := size_closedb σ.

  Definition mem_subst_interp (F: function_ctx) (s : nat -> memory) : Prop :=
    ∀ m, m < F.(fc_mem_vars) -> memory_closed (s m).
  
  Definition rep_subst_interp (F: function_ctx) (s: nat -> representation) : Prop :=
    ∀ r, r < F.(fc_rep_vars) -> repr_closed (s r).
  
  Definition size_subst_interp (F: function_ctx) (s: nat -> size) : Prop :=
    forall r, r < F.(fc_size_vars) -> size_closed (s r).

  Definition subst_interp
    (F : function_ctx)
    (s__mem : nat -> memory) (s__rep : nat -> representation) (s__size : nat -> size) : Prop :=
    mem_subst_interp F s__mem /\
    rep_subst_interp F s__rep /\
    size_subst_interp F s__size.

  Definition subst_env_interp
    (F : function_ctx)
    (s__mem : nat -> memory) (s__rep : nat -> representation) (s__size : nat -> size)
    (se : semantic_env) :
    iProp Σ :=
    ⌜subst_interp F s__mem s__rep s__size ⌝ ∗
    [∗ list] T; κ ∈ se; F.(fc_type_vars), kind_interp κ T.

  Definition has_type_semantic
    (M : module_ctx) (F : function_ctx) (L : local_ctx) (WL : wlocal_ctx)
    (es : list administrative_instruction)
    '(InstrT τs1 τs2 : instruction_type) (L' : local_ctx) :
    iProp Σ :=
    (∀ s__mem s__rep s__size se inst lh,
       subst_env_interp F s__mem s__rep s__size se -∗
       instance_interp M inst -∗
       lholed_interp F L L' inst lh -∗
       let sub := map (subst_type s__mem s__rep s__size VarT) in
       ∀ fr vs,
         values_interp se (sub τs1) vs -∗
         frame_interp se (sub L) WL inst fr -∗
         ↪[frame] fr -∗
         ↪[RUN] -∗
         expr_interp se (sub τs2) F (sub L') WL inst lh (of_val (immV vs) ++ es))%I.

End Relations.
