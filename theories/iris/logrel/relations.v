Require Import iris.algebra.list.
Require Import iris.proofmode.tactics.

From Wasm.iris.helpers Require Import iris_properties.

From RichWasm.compiler Require Import prelude codegen instruction memory util.
From RichWasm.iris Require Import memory runtime util.
From RichWasm.iris.language Require Import iris_wp_def lenient_wp logpred.
From RichWasm Require Import syntax typing layout util.

Require Import Corelib.Init.Datatypes.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Relations.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.

  Definition ns_glo (n : N) : namespace := nroot .@ "rwg" .@ n.
  Definition ns_fun (n : N) : namespace := nroot .@ "rwf" .@ n.
  Definition ns_tab (n : N) : namespace := nroot .@ "rwt" .@ n.
  Definition ns_ref (n : N) : namespace := nroot .@ "rwr" .@ n.

  Inductive semantic_value :=
  | SValues (vs : list rep_value)
  | SWords (μ : concrete_memory) (ws : list word).

  Notation VR := (leibnizO value -n> iPropO Σ).
  Notation VsR := (leibnizO (list value) -n> iPropO Σ).
  Notation VssR := (leibnizO (list (list value)) -n> iPropO Σ).
  Notation RVsR := (leibnizO (list rep_value) -n> iPropO Σ).
  Notation RVssR := (leibnizO (list (list rep_value)) -n> iPropO Σ).
  Notation SVR := (leibnizO semantic_value -n> iPropO Σ).
  Notation LVR := (leibnizO val -n> iPropO Σ).

  Definition semantic_type : Type := SVR.
  Definition semantic_kind : Type := semantic_type -> Prop.
  Definition semantic_env : Type := listO (prodO (leibnizO kind) semantic_type).

  Notation FrR := (leibnizO frame -n> iPropO Σ).
  Notation ClR := (leibnizO function_closure -n> iPropO Σ).
  Notation CtxR := (leibnizO lholed -n> iPropO Σ).
  Notation ER := (leibnizO (list administrative_instruction) -n> iPropO Σ).
  Notation BR := (leibnizO lholed -n> leibnizO (list (list type * local_ctx)) -n>
                    discrete_funO (λ n, leibnizO (valid_holed n) -n> iProp Σ)).
  Notation RR := (leibnizO simple_valid_holed -n> iPropO Σ).

  Implicit Type L : leibnizO local_ctx.
  Implicit Type WL : leibnizO wlocal_ctx.

  Implicit Type es : leibnizO (list administrative_instruction).
  Implicit Type sv : leibnizO semantic_value.
  Implicit Type lv : leibnizO val.
  Implicit Type v : leibnizO value.
  Implicit Type rvs : leibnizO (list rep_value).
  Implicit Type rvss : leibnizO (list (list rep_value)).
  Implicit Type vs : leibnizO (list value).
  Implicit Type vss : leibnizO (list (list value)).
  Implicit Type ws : leibnizO (list word).
  Implicit Type bs : leibnizO bytes.
  Implicit Type fr : leibnizO frame.
  Implicit Type cl : leibnizO function_closure.
  Implicit Type inst : leibnizO instance.
  Implicit Type lh : leibnizO lholed.
  Implicit Type svh : leibnizO simple_valid_holed.

  Implicit Type τ : leibnizO type.
  Implicit Type τs : leibnizO (list type).
  Implicit Type τc : leibnizO (list (list type * local_ctx)).
  Implicit Type ϕ : leibnizO function_type.
  Implicit Type ιss : leibnizO (list (list primitive_rep)).

  Definition value_relation : Type := semantic_env -n> leibnizO type -n> SVR.

  Definition value_type_interp (ty : W.value_type) (v : value) : Prop :=
    match ty with
    | T_i32 => exists n, v = VAL_int32 n
    | T_i64 => exists n, v = VAL_int64 n
    | T_f32 => exists n, v = VAL_float32 n
    | T_f64 => exists n, v = VAL_float64 n
    end.

  Definition result_type_interp (tys : W.result_type) (vs : list value) : Prop :=
    Forall2 value_type_interp tys vs.

  (* Monotone interpretation of a wlocal_ctx *)
  Definition wl_interp (wlocal_offset : nat) (wl : wlocal_ctx) (fr : frame) : Prop :=
    ∃ vs vs__wl vs',
      fr.(f_locs) = vs ++ vs__wl ++ vs' /\ length vs = wlocal_offset /\ result_type_interp wl vs__wl.

  Definition root_pointer_interp (rp : root_pointer) (p : pointer) : iProp Σ :=
    match rp with
    | RootInt n => ⌜p = PtrInt n⌝
    | RootHeap μ a => ∃ ℓ, ⌜p = PtrHeap μ ℓ⌝ ∗ match μ with
                                              | MemMM => ℓ ↦addr a
                                              | MemGC => a ↦root ℓ
                                              end
    end.

  Definition rep_value_interp (rv : rep_value) : VR :=
    λne v,
      match rv with
      | PtrV p => ∃ n, ⌜v = VAL_int32 (Wasm_int.int_of_Z i32m n)⌝ ∗
                        ∃ rp, ⌜repr_root_pointer rp n⌝ ∗ root_pointer_interp rp p
      | I32V n => ⌜v = VAL_int32 n⌝
      | I64V n => ⌜v = VAL_int64 n⌝
      | F32V n => ⌜v = VAL_float32 n⌝
      | F64V n => ⌜v = VAL_float64 n⌝
      end%I.

  Definition rep_values_interp (rvs : list rep_value) : VsR :=
    λne vs, big_sepL2 (const rep_value_interp) rvs vs.

  Definition primitive_rep_interp (ι : primitive_rep) (rv : rep_value) : Prop :=
      match ι, rv with
      | PtrR, PtrV _
      | I32R, I32V _
      | I64R, I64V _
      | F32R, F32V _
      | F64R, F64V _ => True
      | _, _ => False
      end.

  Definition primitive_reps_interp (ιs : list primitive_rep) (sv : semantic_value) : Prop :=
    exists rvs, sv = SValues rvs /\ Forall2 primitive_rep_interp ιs rvs.

  Definition representation_interp (ρ : representation) (sv : semantic_value) : Prop :=
    match eval_rep ρ with
    | Some ιs => primitive_reps_interp ιs sv
    | None => False
    end.

  Definition forall_svalues (sv : semantic_value) (P : rep_value -> Prop) : Prop :=
    exists rvs, sv = SValues rvs /\ Forall P rvs.

  Definition ex_copy_interp (rv : rep_value) : Prop :=
    match rv with
    | PtrV (PtrHeap MemMM _) => False
    | _ => True
    end.

  Definition im_copy_interp (rv : rep_value) : Prop :=
    match rv with
    | PtrV (PtrHeap _ _) => False
    | _ => True
    end.

  Definition copyability_interp (χ : copyability) (T : semantic_type) : Prop :=
    match χ with
    | NoCopy => True
    | ExCopy => forall sv, T sv ⊢ T sv ∗ T sv ∗ ⌜forall_svalues sv ex_copy_interp⌝
    | ImCopy => forall sv, T sv ⊢ T sv ∗ T sv ∗ ⌜forall_svalues sv im_copy_interp⌝
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
    | VALTYPE ρ χ _ => λne sv, ⌜representation_interp ρ sv⌝
    | MEMTYPE ζ μ _ => λne sv, sizity_interp ζ sv ∗ memory_interp μ sv
    end%I.

  Definition kind_interp (κ : kind) : semantic_kind :=
    fun T =>
      T ⊑ kind_as_type_interp κ /\
        match κ with
        | VALTYPE ρ χ _ => copyability_interp χ T
        | MEMTYPE _ _ _ => True
        end.

  Definition values_interp0 (vrel : value_relation) (se : semantic_env) :
    leibnizO (list type) -n> RVsR :=
    λne τs rvs,
      (∃ rvss, ⌜rvs = concat rvss⌝ ∗ [∗ list] τ; rvs ∈ τs; rvss, vrel se τ (SValues rvs))%I.

  Definition mono_closure_interp0 (vrel : value_relation) (se : semantic_env) :
    leibnizO (list type) -n> leibnizO (list type) -n> ClR :=
    λne τs1 τs2 cl,
      match cl with
      | FC_func_native inst (Tf tfs1 tfs2) tlocs es =>
          □ ∀ vs1 rvs1 fr,
            ⌜translate_types (map fst se) τs1 = Some tfs1⌝ -∗
            ⌜translate_types (map fst se) τs2 = Some tfs2⌝ -∗
            rep_values_interp rvs1 vs1 -∗
            values_interp0 vrel se τs1 rvs1 -∗
            ↪[frame] fr -∗
            lenient_wp NotStuck top
              [AI_local (length tfs2) (Build_frame (vs1 ++ n_zeros tlocs) inst) (to_e_list es)]
              {| lp_fr := fun _ => True;
                 lp_fr_inv := fun fr' => ⌜fr = fr'⌝;
                 lp_val :=
                   fun vs2 =>
                     ∃ rvs2, rep_values_interp rvs2 vs2 ∗ values_interp0 vrel se τs2 rvs2;
                 lp_trap := True;
                 lp_br := fun _ _ => False;
                 lp_ret := fun _ => False;
                 lp_host := fun _ _ _ _ => False |}
        | FC_func_host _ _ => False
        end%I.

  Definition closure_interp0 (vrel : value_relation) (se : semantic_env) :
    leibnizO function_type -n> ClR :=
    λne ϕ cl,
      let fix go se ϕ s__mem s__rep s__size :=
        match ϕ with
        | MonoFunT τs1 τs2 =>
            let τs1' := map (subst_type s__mem s__rep s__size VarT) τs1 in
            let τs2' := map (subst_type s__mem s__rep s__size VarT) τs2 in
            mono_closure_interp0 vrel se τs1 τs2 cl
        | ForallMemT ϕ' => ∀ μ, go se ϕ' (unscoped.scons μ s__mem) s__rep s__size
        | ForallRepT ϕ' => ∀ ρ, go se ϕ' s__mem (unscoped.scons ρ s__rep) s__size
        | ForallSizeT ϕ' => ∀ σ, go se ϕ' s__mem s__rep (unscoped.scons σ s__size)
        | ForallTypeT κ ϕ' => ∀ T, ⌜kind_interp κ T⌝ -∗ go ((κ, T) :: se) ϕ' s__mem s__rep s__size
        end%I
      in
      go se ϕ VarM VarR VarS.

  (* TODO *)
  Global Instance Persistent_closure_interp0 vrel se ϕ cl : Persistent (closure_interp0 vrel se ϕ cl).
  Admitted.

  Definition type_var_interp (se : semantic_env) (t : nat) : SVR :=
    match (snd <$> se) !! t with
    | Some T => T
    | None => λne _, False%I
    end.

  Definition sum_interp
    (vrel : value_relation) (se : semantic_env) (ρs : list representation) (τs : list type) : SVR :=
    λne sv,
      (∃ i rvs rvs_i τ_i ρ_i ixs,
         ⌜sv = SValues (I32V (Wasm_int.int_of_Z i32m (Z.of_nat i)) :: rvs)⌝ ∗
           ⌜τs !! i = Some τ_i⌝ ∗
           ⌜type_rep (map fst se) τ_i = Some ρ_i⌝ ∗
           ⌜inject_sum_rep ρs ρ_i = Some ixs⌝ ∗
           ⌜nths_error rvs ixs = Some rvs_i⌝ ∗
           ▷ vrel se τ_i (SValues rvs_i))%I.

  Definition variant_interp
    (vrel : value_relation) (se : semantic_env) (cm : concrete_memory) (τs : list type) : SVR :=
    λne sv,
      (∃ i ws ws' τ,
         ⌜sv = SWords cm (WordInt (Z.of_nat i) :: ws ++ ws')⌝ ∗
           ⌜τs !! i = Some τ⌝ ∗
           ▷ vrel se τ (SWords cm ws))%I.

  Definition prod_interp (vrel : value_relation) (se : semantic_env) (τs : list type) : SVR :=
    λne sv,
      (∃ rvss,
         ⌜sv = SValues (concat rvss)⌝ ∗ [∗ list] rvs; τ ∈ rvss; τs, ▷ vrel se τ (SValues rvs))%I.

  Definition struct_interp
    (vrel : value_relation) (se : semantic_env) (cm : concrete_memory) (τs : list type) : SVR :=
    λne sv,
      (∃ wss,
         ⌜sv = SWords cm (concat wss)⌝ ∗ [∗ list] ws; τ ∈ wss; τs, ▷ vrel se τ (SWords cm ws))%I.

  Definition ref_mm_interp (vrel : value_relation) (se : semantic_env) (τ : type) : SVR :=
    λne sv,
      (∃ ℓ fs ws,
         ⌜sv = SValues [PtrV (PtrHeap MemMM ℓ)]⌝ ∗
           ℓ ↦layout fs ∗
           ℓ ↦heap ws ∗
           ▷ vrel se τ (SWords MemMM ws))%I.

  Definition ref_gc_interp (vrel : value_relation) (se : semantic_env) (τ : type) : SVR :=
    λne sv,
      (∃ ℓ fs,
         ⌜sv = SValues [PtrV (PtrHeap MemGC ℓ)]⌝ ∗
           na_inv logrel_nais (ns_ref ℓ)
             (∃ ws, ℓ ↦layout fs ∗ ℓ ↦heap ws ∗ ▷ vrel se τ (SWords MemGC ws)))%I.

  Definition coderef_interp (vrel : value_relation) (se : semantic_env) (ϕ : function_type) : SVR :=
    λne sv,
      (∃ i j cl,
         ⌜sv = SValues [I32V (Wasm_int.int_of_Z i32m (Z.of_N i))]⌝ ∗
           ▷ closure_interp0 vrel se ϕ cl ∗
           na_inv logrel_nais (ns_tab i) (N.of_nat sr.(sr_table) ↦[wt][i] Some j) ∗
           na_inv logrel_nais (ns_fun (N.of_nat j)) (N.of_nat j ↦[wf] cl))%I.

  Definition pad_interp
    (vrel : value_relation) (se : semantic_env) (cm : concrete_memory) (τ : type) : SVR :=
    λne sv, (∃ ws ws', ⌜sv = SWords cm (ws ++ ws')⌝ ∗ ▷ vrel se τ (SWords cm ws))%I.

  Definition ser_interp
    (vrel : value_relation) (se : semantic_env) (cm : concrete_memory) (τ : type) : SVR :=
    λne sv,
      (∃ rvs wss,
         ⌜sv = SWords cm (concat wss)⌝ ∗ ⌜Forall2 ser_value rvs wss⌝ ∗ ▷ vrel se τ (SValues rvs))%I.

  Definition rec_interp (vrel : value_relation) (se : semantic_env) (κ : kind) (τ : type) : SVR :=
    λne sv,
      let τ' := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
      (▷ vrel se τ' sv)%I.

  Definition exists_mem_interp (vrel : value_relation) (se : semantic_env) (τ : type) : SVR :=
    λne sv,
      (∃ μ,
         let τ' := subst_type (unscoped.scons μ VarM) VarR VarS VarT τ in
         ▷ vrel se τ' sv)%I.

  Definition exists_rep_interp (vrel : value_relation) (se : semantic_env) (τ : type) : SVR :=
    λne sv,
      (∃ ρ,
         let τ' := subst_type VarM (unscoped.scons ρ VarR) VarS VarT τ in
         ▷ vrel se τ' sv)%I.

  Definition exists_size_interp (vrel : value_relation) (se : semantic_env) (τ : type) : SVR :=
    λne sv,
      (∃ σ,
         let τ' := subst_type VarM VarR (unscoped.scons σ VarS) VarT τ in
         ▷ vrel se τ' sv)%I.

  Definition exists_type_interp
    (vrel : value_relation) (se : semantic_env) (κ : kind) (τ : type) : SVR :=
    λne sv, (∃ T, ⌜kind_interp κ T⌝ ∗ ▷ vrel ((κ, T) :: se) τ sv)%I.

  Definition type_interp0 (vrel : value_relation) (se : semantic_env) : leibnizO type -n> SVR :=
    λne τ,
      match τ with
      | VarT t => type_var_interp se t
      | I31T _
      | NumT _ _ => λne _, True
      | SumT (VALTYPE (SumR ρs) _ _) τs => sum_interp vrel se ρs τs
      | SumT _ _ => λne _, False
      | VariantT (VALTYPE _ _ _) _
      | VariantT (MEMTYPE _ (VarM _) _) _ => λne _, False
      | VariantT (MEMTYPE _ (ConstM cm) _) τs => variant_interp vrel se cm τs
      | ProdT (VALTYPE _ _ _) τs => prod_interp vrel se τs
      | ProdT (MEMTYPE _ _ _) _
      | StructT (VALTYPE _ _ _) _
      | StructT (MEMTYPE _ (VarM _) _) _ => λne _, False
      | StructT (MEMTYPE _ (ConstM cm) _) τs => struct_interp vrel se cm τs
      | RefT _ (VarM _) _ => λne _, False
      | RefT _ (ConstM MemMM) τ => ref_mm_interp vrel se τ
      | RefT _ (ConstM MemGC) τ => ref_gc_interp vrel se τ
      | CodeRefT _ ϕ => coderef_interp vrel se ϕ
      | PadT (VALTYPE _ _ _) _ _
      | PadT (MEMTYPE _ (VarM _) _) _ _ => λne _, False
      | PadT (MEMTYPE _ (ConstM cm) _) _ τ => pad_interp vrel se cm τ
      | SerT (VALTYPE _ _ _) _
      | SerT (MEMTYPE _ (VarM _) _) _ => λne _, False
      | SerT (MEMTYPE _ (ConstM cm) _) τ => ser_interp vrel se cm τ
      | RecT κ τ => rec_interp vrel se κ τ
      | ExistsMemT _ τ => exists_mem_interp vrel se τ
      | ExistsRepT _ τ => exists_rep_interp vrel se τ
      | ExistsSizeT _ τ => exists_size_interp vrel se τ
      | ExistsTypeT _ κ τ => exists_type_interp vrel se κ τ
      end%I.

  Definition value_se_interp0 (vrel : value_relation) (se : semantic_env) : leibnizO type -n> SVR :=
    λne τ sv,
      (∃ κ,
         ⌜type_kind (map fst se) τ = Some κ⌝ ∗
           kind_as_type_interp κ sv ∗
           type_interp0 vrel se τ sv)%I.

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

  Lemma value_interp_part_eq se τ :
    value_interp se τ ≡ value_interp0 value_interp se τ.
  Proof using.
    do 2 f_equiv.
    apply fixpoint_unfold.
  Qed.

  Lemma value_interp_eq se τ sv :
    value_interp se τ sv ⊣⊢ value_interp0 value_interp se τ sv.
  Proof.
    do 3 f_equiv.
    apply fixpoint_unfold.
  Qed.

  Definition values_interp (se : semantic_env) : leibnizO (list type) -n> RVsR :=
    values_interp0 value_interp se.

  Definition closure_interp (se : semantic_env) : leibnizO function_type -n> ClR :=
    closure_interp0 value_interp se.

  Definition locals_inv_interp : list (list primitive_rep) -> list (list rep_value) -> Prop :=
    Forall2 (Forall2 primitive_rep_interp).

  Definition locals_interp (se : semantic_env) : leibnizO local_ctx -n> RVssR :=
    (λne L rvss,
      [∗ list] τo; rvs ∈ L; rvss, ∀ τ, ⌜τo = Some τ⌝ -∗ value_interp se τ (SValues rvs))%I.

  Definition frame_interp (se : semantic_env) :
    leibnizO (list (list primitive_rep)) -n> leibnizO local_ctx -n> leibnizO wlocal_ctx -n>
      leibnizO instance -n> FrR :=
    λne ιss L WL inst fr,
      (∃ rvss_L vss_L vs_WL,
         ⌜fr = Build_frame (concat vss_L ++ vs_WL) inst⌝ ∗
           ⌜locals_inv_interp ιss rvss_L⌝ ∗
           ⌜result_type_interp WL vs_WL⌝ ∗
           rep_values_interp (concat rvss_L) (concat vss_L) ∗
           locals_interp se L rvss_L)%I.

  Fixpoint simple_get_base_l (lh : simple_valid_holed) :=
    match lh with
    | SH_base vs _ => vs
    | SH_rec _ _ _ lh' _ => simple_get_base_l lh'
    end.

  Definition return_interp (se : semantic_env) (τr : list type) : RR :=
    λne svh,
      (∃ vs0 vs rvs,
         ⌜simple_get_base_l svh = vs0 ++ vs⌝ ∗
           rep_values_interp rvs vs ∗
           values_interp se τr rvs ∗
           ∀ fr fr',
             ↪[frame] fr -∗
             ↪[RUN] -∗
             WP [AI_local (length vs) fr' (of_val (retV svh))]
                {{ lv,
                     ∃ rvs' vs',
                       ⌜lv = immV vs'⌝ ∗
                         rep_values_interp rvs' vs' ∗
                         values_interp se τr rvs' ∗
                         ↪[frame] fr }})%I.

  Program Definition br_interp0
    (se : semantic_env) (τr : list type) (ιss_L : list (list primitive_rep)) (L : local_ctx)
    (WL : wlocal_ctx) (inst : instance) (br_interp : BR) :
    BR :=
    λne lh τc, λ (j: nat), λne (vh: leibnizO (valid_holed j)),
      (∃ k p lh' lh'' τs es0 es es' vs0 vs rvs,
         ⌜get_base_l vh = vs0 ++ vs⌝ ∗
           ⌜lh_depth (lh_of_vh vh) = p⌝ ∗
           ⌜τc !! (j - p) = Some (τs, L)⌝ ∗
           ⌜get_layer lh (lh_depth lh - S (j - p)) = Some (es0, k, es, lh', es')⌝ ∗
           ⌜lh_depth lh'' = lh_depth lh - S (j - p)⌝ ∗
           ⌜is_Some (lh_minus lh lh'')⌝ ∗
           rep_values_interp rvs vs ∗
           values_interp se τs rvs ∗
           ∀ fr,
             ↪[frame] fr -∗
             frame_interp se ιss_L L WL inst fr -∗
             lenient_wp_ctx
               NotStuck top
               (of_val (immV vs) ++ [AI_basic (BI_br (j - p))])
               {| lp_fr := frame_interp se ιss_L L WL inst;
                  lp_fr_inv := const True;
                  lp_val :=
                    fun vs' => ∃ τs' rvs', rep_values_interp rvs' vs' ∗ values_interp se τs' rvs';
                  lp_trap := True;
                  lp_br := br_interp lh'' (drop (S (j - p)) τc);
                  lp_ret := return_interp se τr;
                  lp_host := fun _ _ _ _ => False |}
               (S (lh_depth lh')) (LH_rec es0 k es lh' es'))%I.

  (* TODO *)
  Instance Contractive_br_interp0 se τr ιss_L L WL inst :
    Contractive (br_interp0 se τr ιss_L L WL inst).
  Admitted.

  Definition br_interp
    (se : semantic_env) (τr : list type) (ιss_L : list (list primitive_rep)) (L : local_ctx)
    (WL : wlocal_ctx) (inst : instance) :
    BR :=
    fixpoint (br_interp0 se τr ιss_L L WL inst).

  Lemma br_interp_eq se τr ιss_L L WL inst n lh l vh :
    br_interp se τr ιss_L L WL inst lh l n vh ⊣⊢
      br_interp0 se τr ιss_L L WL inst (br_interp se τr ιss_L L WL inst) lh l n vh.
  Proof.
    f_equiv.
    (* f_equiv has some trouble with discrete_funO equivalences *)
    cut (br_interp se τr ιss_L L WL inst lh l
           ≡ br_interp0 se τr ιss_L L WL inst (br_interp se τr ιss_L L WL inst) lh l).
    { intros H.
      unfold equiv, ofe_equiv, discrete_funO, discrete_fun_equiv in H.
      apply H.
    }
    f_equiv.
    f_equiv.
    by rewrite -fixpoint_unfold.
  Qed.

  Definition expr_interp
    (se : semantic_env) (τr : list type) (τc : list (list type * local_ctx))
    (ιss_L : list (list primitive_rep)) (L : local_ctx) (WL : wlocal_ctx)
    (τs : list type) (inst : instance) (lh : lholed) :
    ER :=
    λne es,
      lenient_wp NotStuck top es
                 {| lp_fr := frame_interp se ιss_L L WL inst;
                    lp_fr_inv := const True;
                    lp_val := fun vs => ∃ rvs, values_interp se τs rvs ∗ rep_values_interp rvs vs;
                    lp_trap := True;
                    lp_br := br_interp se τr ιss_L L WL inst lh τc;
                    lp_ret := return_interp se τr;
                    lp_host := fun _ _ _ _ => False |}%I.

  Definition instance_rt_func_interp
    (i : funcidx) (a : funcaddr) (spec : function_closure -> Prop) (inst : instance) : iProp Σ :=
    ∃ cl,
      ⌜spec cl⌝ ∗
        ⌜inst.(inst_funcs) !! funcimm i = Some a⌝ ∗
        na_inv logrel_nais (ns_fun (N.of_nat a)) (N.of_nat a ↦[wf] cl).

  Definition instance_runtime_interp (mr : module_runtime) (inst : instance) : iProp Σ :=
    instance_rt_func_interp mr.(mr_func_mmalloc) sr.(sr_func_mmalloc) (spec_mmalloc rti sr) inst ∗
      instance_rt_func_interp
        mr.(mr_func_gcalloc) sr.(sr_func_gcalloc) (spec_gcalloc rti sr) inst ∗
      instance_rt_func_interp mr.(mr_func_setflag) sr.(sr_func_setflag) (spec_setflag rti sr) inst ∗
      instance_rt_func_interp mr.(mr_func_free) sr.(sr_func_free) (spec_free rti sr) inst ∗
      instance_rt_func_interp
        mr.(mr_func_registerroot) sr.(sr_func_registerroot) (spec_registerroot rti sr) inst ∗
      instance_rt_func_interp
        mr.(mr_func_unregisterroot) sr.(sr_func_unregisterroot) (spec_unregisterroot rti sr) inst.

  Definition instance_functions_interp (M : module_ctx) (mr : module_runtime) (inst : instance) :
    iProp Σ :=
    [∗ list] i ↦ ϕ ∈ M.(mc_functions),
      ∃ i' cl,
        ⌜inst.(inst_funcs) !! (funcimm mr.(mr_func_user) + i)%nat = Some i'⌝ ∗
          closure_interp [] ϕ cl ∗
          na_inv logrel_nais (ns_fun (N.of_nat i')) (N.of_nat i' ↦[wf] cl).

  Definition table_entry_interp (off : nat) (i : nat) (ϕ : function_type) : iProp Σ :=
    let nt := N.of_nat (off + i) in
    ∃ i' cl,
      closure_interp [] ϕ cl ∗
        na_inv logrel_nais (ns_tab nt) (N.of_nat sr.(sr_table) ↦[wt][nt] Some i') ∗
        na_inv logrel_nais (ns_fun (N.of_nat i')) (N.of_nat i' ↦[wf] cl).

  Definition instance_table_interp (M : module_ctx) (mr : module_runtime) (inst : instance) : iProp Σ :=
    ⌜inst.(inst_tab) !! tableimm mr.(mr_table) = Some sr.(sr_table)⌝ ∗
      ∃ i_off off,
        let g_off := Build_global MUT_mut (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat off))) in
        ([∗ list] i ↦ ϕ ∈ M.(mc_table), table_entry_interp off i ϕ) ∗
          ⌜inst.(inst_globs) !! globalimm mr.(mr_global_table_off) = Some i_off⌝ ∗
          na_inv logrel_nais (ns_glo (N.of_nat i_off)) (N.of_nat i_off ↦[wg] g_off).

  Definition instance_interp (M : module_ctx) (mr : module_runtime) (inst : instance) : iProp Σ :=
    instance_runtime_interp mr inst ∗
      instance_functions_interp M mr inst ∗
      ⌜inst.(inst_tab) !! tableimm mr.(mr_table) = Some sr.(sr_table)⌝ ∗
      instance_table_interp M mr inst ∗
      ⌜inst.(inst_memory) !! memimm mr.(mr_mem_mm) = Some sr.(sr_mem_mm)⌝ ∗
      ⌜inst.(inst_memory) !! memimm mr.(mr_mem_gc) = Some sr.(sr_mem_gc)⌝.

  Global Instance Persistent_instance_interp M mr inst : Persistent (instance_interp M mr inst).
  Proof.
    typeclasses eauto.
  Defined.

  Fixpoint lholed_valid (lh : lholed) : Prop :=
    match lh with
    | LH_base vs _ => is_true (const_list vs)
    | LH_rec vs _ _ lh' _ => is_true (const_list vs) ∧ lholed_valid lh'
    end.

  Fixpoint length_lholeds (se : semantic_env) (τc : list (list type * local_ctx)) (lh : lholed) :
    Prop :=
    match τc, lh with
    | [], LH_base _ _ => True
    | (τs, _) :: τc', LH_rec _ n _ lh' _ =>
        (forall rvs, values_interp se τs rvs -∗ ⌜length rvs = n⌝) /\ length_lholeds se τc' lh'
    | _, _ => False
    end.

  Definition continuation_interp
    (se : semantic_env) (τr : list type) (τc : list (list type * local_ctx))
    (ιss_L : list (list primitive_rep)) (L : local_ctx) (WL : wlocal_ctx)
    (inst : instance) (lh : lholed) (k : nat) (τs : list type) :
    iProp Σ :=
    (∃ j es0 es es' lh' lh'',
       ⌜get_layer lh (lh_depth lh - S k) = Some (es0, j, es, lh', es')⌝ ∧
         ⌜lh_depth lh'' = lh_depth lh - S k⌝ ∧
         ⌜is_Some (lh_minus lh lh'')⌝ ∧
         □ ∀ fr vs rvs,
             rep_values_interp rvs vs -∗
             values_interp se τs rvs -∗
             ↪[frame] fr -∗
             ↪[RUN] -∗
             frame_interp se ιss_L L WL inst fr -∗
             ∃ τs',
               expr_interp se τr (drop (S k) τc) ιss_L L WL τs' inst lh''
                 (es0 ++ of_val (immV vs) ++ es ++ es'))%I.

  Definition continuations_interp
    (se : semantic_env) (τr : list type) (τc : list (list type * local_ctx))
    (ιss_L : list (list primitive_rep)) (WL : wlocal_ctx) (inst : instance) :
    CtxR :=
    λne lh, ([∗ list] k ↦ '(τs, L) ∈ τc, continuation_interp se τr τc ιss_L L WL inst lh k τs)%I.

  Definition context_interp
    (se : semantic_env) (τr : list type) (τc : list (list type * local_ctx))
    (ιss_L : list (list primitive_rep)) (WL : wlocal_ctx) (inst : instance) :
    CtxR :=
    λne lh,
      (⌜base_is_empty lh⌝ ∗
         ⌜length_lholeds se (rev τc) lh⌝ ∗
         ⌜lholed_valid lh⌝ ∗
         continuations_interp se τr τc ιss_L WL inst lh)%I.

  Definition memory_closed (m : memory) : Prop :=
    match m with
    | VarM _ => False
    | ConstM _ => True
    end.

  Definition mem_subst_interp (K : kind_ctx) (s : nat -> memory) : Prop :=
    ∀ m, m < K.(kc_mem_vars) -> mem_ok kc_empty (s m).

  Definition rep_subst_interp (K : kind_ctx) (s : nat -> representation) : Prop :=
    ∀ r, r < K.(kc_rep_vars) -> rep_ok kc_empty (s r).

  Definition size_subst_interp (K : kind_ctx) (s : nat -> size) : Prop :=
    forall r, r < K.(kc_size_vars) -> size_ok kc_empty (s r).

  Definition subst_interp
    (K : kind_ctx)
    (s__mem : nat -> memory) (s__rep : nat -> representation) (s__size : nat -> size) : Prop :=
    mem_subst_interp K s__mem /\
    rep_subst_interp K s__rep /\
    size_subst_interp K s__size.

  Definition sem_env_interp κs s__mem s__rep s__size se : Prop :=
    Forall2 (fun κT κ => fst κT = subst_kind s__mem s__rep s__size κ /\ uncurry kind_interp κT) se κs.

  Definition subst_env_interp
    (F : function_ctx)
    (s__mem : nat -> memory) (s__rep : nat -> representation) (s__size : nat -> size)
    (se : semantic_env) :
    Prop :=
    subst_interp F.(fc_kind_ctx) s__mem s__rep s__size /\
      sem_env_interp F.(fc_type_vars) s__mem s__rep s__size se.

  Definition have_instruction_type_sem
    (mr : module_runtime)
    (M : module_ctx) (F : function_ctx) (L : local_ctx) (WL : wlocal_ctx)
    (es : list administrative_instruction)
    '(InstrT τs1 τs2 : instruction_type) (L' : local_ctx) :
    iProp Σ :=
    (∀ s__mem s__rep s__size se inst fr lh rvs vs,
       ⌜subst_env_interp F s__mem s__rep s__size se⌝ -∗
       instance_interp M mr inst -∗
       context_interp se F.(fc_return) F.(fc_labels) F.(fc_locals) WL inst lh -∗
       let sub := subst_type s__mem s__rep s__size VarT in
       rep_values_interp rvs vs -∗
       values_interp se (map sub τs1) rvs -∗
       frame_interp se F.(fc_locals) (map (option_map sub) L) WL inst fr -∗
       ↪[frame] fr -∗
       ↪[RUN] -∗
       expr_interp se F.(fc_return) F.(fc_labels) F.(fc_locals)
         (map (option_map sub) L') WL (map sub τs2) inst lh (of_val (immV vs) ++ es))%I.

End Relations.
