Require Import iris.algebra.list.
Require Import iris.proofmode.tactics.

From Wasm.iris.helpers Require Import iris_properties.

From RichWasm.compiler Require Import prelude codegen.
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
  | SAtoms (os : list atom)
  | SWords (ws : list word).

  Definition SVR : Type := leibnizO semantic_value -n> iPropO Σ.

  Definition semantic_type : Type := SVR.
  Definition semantic_kind : Type := semantic_type -> Prop.
  Definition mem_env : Type := listO (leibnizO base_memory).
  Definition rep_env : Type := listO (leibnizO (list atomic_rep)).
  Definition size_env : Type := listO (leibnizO nat).
  Definition type_env : Type := listO (prodO (leibnizO skind) semantic_type).
  Definition semantic_env : Type := prodO (prodO (prodO mem_env rep_env) size_env) type_env.

  Definition senv_empty : semantic_env := ([], [], [], []).

  Definition senv_mems (se : semantic_env) : mem_env :=
    let '(m, r, s, t) := se in m.

  Definition senv_reps (se: semantic_env) : rep_env :=
    let '(m, r, s, t) := se in r.

  Definition senv_sizes (se: semantic_env) : size_env :=
    let '(m, r, s, t) := se in s.

  Definition senv_types (se: semantic_env) : type_env :=
    let '(m, r, s, t) := se in t.

  Definition senv_kinds (se: semantic_env) : list skind :=
    map fst (senv_types se).

  Definition senv_insert_type : skind -> semantic_type -> semantic_env -> semantic_env :=
    λ κ T se,
      (senv_mems se, senv_reps se, senv_sizes se, (κ, T) :: senv_types se).

  Definition senv_insert_mem : base_memory → semantic_env → semantic_env. Admitted.
  Definition senv_insert_rep : list atomic_rep → semantic_env → semantic_env. Admitted.
  Definition senv_insert_size : nat → semantic_env → semantic_env. Admitted.

  #[global]
  Instance senv_mem_lookup : Lookup nat base_memory semantic_env :=
    λ idx se, senv_mems se !! idx.

  #[global]
  Instance senv_rep_lookup : Lookup nat (list atomic_rep) semantic_env :=
    λ idx se, senv_reps se !! idx.

  #[global]
  Instance senv_size_lookup : Lookup nat nat semantic_env :=
    λ idx se, senv_sizes se !! idx.

  #[global]
  Instance senv_type_lookup : Lookup nat (skind * semantic_type) semantic_env :=
    λ idx se, senv_types se !! idx.

  #[global]
  Instance senv_kind_lookup : Lookup nat skind semantic_env :=
    λ idx se, fst <$> senv_types se !! idx.

  Definition OsR : Type := leibnizO (list atom) -n> iPropO Σ.
  Definition ClR : Type := leibnizO function_closure -n> iPropO Σ.
  Definition CtxR : Type := leibnizO lholed -n> iPropO Σ.

  Definition BR : Type :=
    leibnizO lholed -n>
      leibnizO (list (list type * local_ctx)) -n>
      discrete_funO (fun n => leibnizO (valid_holed n) -n> iProp Σ).

  Implicit Type L : leibnizO local_ctx.
  Implicit Type WL : leibnizO wlocal_ctx.

  Implicit Type es : leibnizO (list administrative_instruction).
  Implicit Type sv : leibnizO semantic_value.
  Implicit Type lv : leibnizO val.
  Implicit Type v : leibnizO value.
  Implicit Type os : leibnizO (list atom).
  Implicit Type oss : leibnizO (list (list atom)).
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
  Implicit Type ιss : leibnizO (list (list atomic_rep)).
  Implicit Type ηss : leibnizO (list (list primitive)).

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
    | RootInt n =>
        match p with
        | PtrInt n' => ⌜n = n'⌝
        | _ => False
        end
    | RootHeap μ a => 
        match p with
        | PtrHeap μ' ℓ =>
            ⌜μ = μ'⌝ ∗ match μ with
                       | MemMM => ℓ ↦addr a
                       | MemGC => a ↦root ℓ
                       end
        | _ => False
        end
    end.

  Definition atom_interp (o : atom) : leibnizO value -n> iPropO Σ :=
    λne v,
      match o with
      | PtrA p => ∃ n, ⌜v = VAL_int32 (Wasm_int.int_of_Z i32m n)⌝ ∗
                        ∃ rp, ⌜repr_root_pointer rp n⌝ ∗ root_pointer_interp rp p
      | I32A n => ⌜v = VAL_int32 n⌝
      | I64A n => ⌜v = VAL_int64 n⌝
      | F32A n => ⌜v = VAL_float32 n⌝
      | F64A n => ⌜v = VAL_float64 n⌝
      end%I.

  Definition atoms_interp (os : list atom) : leibnizO (list value) -n> iPropO Σ :=
    λne vs, big_sepL2 (const atom_interp) os vs.

  Definition atom_fits_prim (η : primitive) (a : atom) : Prop :=
    match η, a with
    | I32P, PtrA _
    | I32P, I32A _
    | I64P, I64A _
    | F32P, F32A _
    | F64P, F64A _ => True
    | _, _ => False
    end.

  Definition has_arep (ι : atomic_rep) (a : atom) : Prop :=
      match ι, a with
      | PtrR, PtrA _
      | I32R, I32A _
      | I64R, I64A _
      | F32R, F32A _
      | F64R, F64A _ => True
      | _, _ => False
      end.

  Definition has_areps (ιs : list atomic_rep) (sv : semantic_value) : Prop :=
    exists os, sv = SAtoms os /\ Forall2 has_arep ιs os.

  Definition forall_satoms (sv : semantic_value) (P : atom -> Prop) : Prop :=
    exists os, sv = SAtoms os /\ Forall P os.

  Definition ex_copy_interp (o : atom) : Prop :=
    match o with
    | PtrA (PtrHeap MemMM _) => False
    | _ => True
    end.

  Definition im_copy_interp (o : atom) : Prop :=
    match o with
    | PtrA (PtrHeap _ _) => False
    | _ => True
    end.

  Definition copyability_interp (χ : copyability) (T : semantic_type) : Prop :=
    match χ with
    | NoCopy => True
    | ExCopy => forall sv, T sv ⊢ T sv ∗ T sv ∗ ⌜forall_satoms sv ex_copy_interp⌝
    | ImCopy => forall sv, T sv ⊢ T sv ∗ T sv ∗ ⌜forall_satoms sv im_copy_interp⌝
    end.

  Definition ssize_interp (n : nat) (sv : semantic_value) : Prop :=
    match sv with
    | SAtoms _ => False
    | SWords ws => n = length ws
    end.

  (* S refines T, written S ⊑ T. *)
  Definition semantic_type_le (S T : semantic_type) : Prop := forall sv, S sv -∗ T sv.

  #[export]
  Instance SqSubsetEq_semantic_type : SqSubsetEq semantic_type := semantic_type_le.

  Definition skind_as_type_interp (κ : skind) : semantic_type :=
    λne sv,
      match κ with
      | SVALTYPE ιs _ _ => ⌜has_areps ιs sv⌝
      | SMEMTYPE n _ => ⌜ssize_interp n sv⌝
      end%I.

  Definition skind_interp (κ : skind) : semantic_kind :=
    fun T =>
      T ⊑ skind_as_type_interp κ /\
        match κ with
        | SVALTYPE _ χ _ => copyability_interp χ T
        | SMEMTYPE _ _ => True
        end.

  Definition values_interp0 (vrel : value_relation) (se : semantic_env) :
    leibnizO (list type) -n> OsR :=
    λne τs os,
      (∃ oss, ⌜os = concat oss⌝ ∗ [∗ list] τ; os ∈ τs; oss, vrel se τ (SAtoms os))%I.

  Definition type_skind (se: semantic_env) (τ : type) : option skind :=
    match τ with
    | VarT x => se !! x
    | NumT κ _
    | SumT κ _
    | VariantT κ _
    | ProdT κ _
    | StructT κ _
    | RefT κ _ _
    | I31T κ
    | CodeRefT κ _
    | SerT κ _
    | RecT κ _
    | PlugT κ _
    | SpanT κ _
    | ExistsMemT κ _
    | ExistsRepT κ _
    | ExistsSizeT κ _
    | ExistsTypeT κ _ _ => eval_kind se κ
    end.

  Definition skind_rep (κ: skind) : option (list atomic_rep) :=
    match κ with
    | SVALTYPE ιs _ _ => Some ιs
    | _ => None
    end.

  Definition type_arep (se : semantic_env) (τ : type) : option (list atomic_rep) :=
    κ ← type_skind se τ;
    skind_rep κ.

  Definition translate_type (se : semantic_env) (τ : type) : option (list W.value_type) :=
    map translate_arep <$> type_arep se τ.
  
  Definition translate_types (se: semantic_env) (τs : list type) : option (list W.value_type) :=
    @concat _ <$> mapM (translate_type se) τs.

  Definition mono_closure_interp0 (vrel : value_relation) (se : semantic_env) :
    leibnizO (list type) -n> leibnizO (list type) -n> ClR :=
    λne τs1 τs2 cl,
      match cl with
      | FC_func_native inst (Tf tfs1 tfs2) tlocs es =>
          □ ∀ vs1 os1 fr θ,
            ⌜translate_types se τs1 = Some tfs1⌝ -∗
            ⌜translate_types se τs2 = Some tfs2⌝ -∗
            atoms_interp os1 vs1 -∗
            values_interp0 vrel se τs1 os1 -∗
            rt_token rti sr θ -∗
            ↪[frame] fr -∗
            lenient_wp NotStuck top
              [AI_local (length tfs2) (Build_frame (vs1 ++ n_zeros tlocs) inst) (to_e_list es)]
              {| lp_fr := fun _ => True;
                 lp_fr_inv := fun fr' => ⌜fr = fr'⌝;
                 lp_val :=
                   fun vs2 =>
                     ∃ os2 θ',
                       atoms_interp os2 vs2 ∗ values_interp0 vrel se τs2 os2 ∗ rt_token rti sr θ';
                 lp_trap := True;
                 lp_br := fun _ _ => False;
                 lp_ret := fun _ => False;
                 lp_host := fun _ _ _ _ => False |}
        | FC_func_host _ _ => False
        end%I.

  Fixpoint closure_interp0
    (vrel : value_relation) (se : semantic_env) (ϕ : leibnizO function_type) : ClR :=
    λne cl,
      match ϕ with
      | MonoFunT τs1 τs2 => mono_closure_interp0 vrel se τs1 τs2 cl
      | ForallMemT ϕ' => ∀ μ, closure_interp0 vrel (senv_insert_mem μ se) ϕ' cl
      | ForallRepT ϕ' => ∀ ρ, closure_interp0 vrel (senv_insert_rep ρ se) ϕ' cl
      | ForallSizeT ϕ' => ∀ σ, closure_interp0 vrel (senv_insert_size σ se) ϕ' cl
      | ForallTypeT κ ϕ' =>
          ∀ sκ T,
            ⌜eval_kind se κ = Some sκ⌝ -∗
            ⌜skind_interp sκ T⌝ -∗
            closure_interp0 vrel (senv_insert_type sκ T se) ϕ' cl
      end%I.

  (* TODO *)
  Global Instance Persistent_closure_interp0 vrel se ϕ cl : Persistent (closure_interp0 vrel se ϕ cl).
  Admitted.

  Global Instance closure_interp0_ne vrel se ϕ : NonExpansive2 (closure_interp0 vrel se).
  Admitted.

  Definition type_var_interp (se : semantic_env) (t : nat) : SVR :=
    match se !! t with
    | Some (_, T) => T
    | None => λne _, False%I
    end.

  Definition sum_interp
    (vrel : value_relation) (se : semantic_env) (ρs : list representation) (τs : list type) : SVR :=
    λne sv,
      (∃ i os os_i τ_i ιs ιs_i ixs,
         ⌜sv = SAtoms (I32A (Wasm_int.int_of_Z i32m (Z.of_nat i)) :: os)⌝ ∗
           ⌜τs !! i = Some τ_i⌝ ∗
           ⌜type_arep se τ_i = Some ιs_i⌝ ∗
           ⌜tail <$> eval_rep se (SumR ρs) = Some ιs⌝ ∗
           ⌜inject_sum_arep ιs ιs_i = Some ixs⌝ ∗
           ⌜nths_error os ixs = Some os_i⌝ ∗
           ▷ vrel se τ_i (SAtoms os_i))%I.

  Definition variant_interp
    (vrel : value_relation) (se : semantic_env) (τs : list type) : SVR :=
    λne sv,
      (∃ i ws ws' τ,
         ⌜sv = SWords (WordInt (Z.of_nat i) :: ws ++ ws')⌝ ∗
           ⌜τs !! i = Some τ⌝ ∗
           ▷ vrel se τ (SWords ws))%I.

  Definition prod_interp (vrel : value_relation) (se : semantic_env) (τs : list type) : SVR :=
    λne sv,
      (∃ oss, ⌜sv = SAtoms (concat oss)⌝ ∗ [∗ list] os; τ ∈ oss; τs, ▷ vrel se τ (SAtoms os))%I.

  Definition struct_interp (vrel : value_relation) (se : semantic_env) (τs : list type) : SVR :=
    λne sv,
      (∃ wss,
         ⌜sv = SWords (concat wss)⌝ ∗ [∗ list] ws; τ ∈ wss; τs, ▷ vrel se τ (SWords ws))%I.

  Definition ref_mm_interp (vrel : value_relation) (se : semantic_env) (τ : type) : SVR :=
    λne sv,
      (∃ ℓ fs ws,
         ⌜sv = SAtoms [PtrA (PtrHeap MemMM ℓ)]⌝ ∗
           ℓ ↦layout fs ∗
           ℓ ↦heap ws ∗
           ▷ vrel se τ (SWords ws))%I.

  Definition ref_gc_interp (vrel : value_relation) (se : semantic_env) (τ : type) : SVR :=
    λne sv,
      (∃ ℓ fs,
         ⌜sv = SAtoms [PtrA (PtrHeap MemGC ℓ)]⌝ ∗
           na_inv logrel_nais (ns_ref ℓ)
             (∃ ws, ℓ ↦layout fs ∗ ℓ ↦heap ws ∗ ▷ vrel se τ (SWords ws)))%I.

  Definition coderef_interp (vrel : value_relation) (se : semantic_env) (ϕ : function_type) : SVR :=
    λne sv,
      (∃ i j cl,
         ⌜sv = SAtoms [I32A (Wasm_int.int_of_Z i32m (Z.of_N i))]⌝ ∗
           ▷ closure_interp0 vrel se ϕ cl ∗
           na_inv logrel_nais (ns_tab i) (N.of_nat sr.(sr_table) ↦[wt][i] Some j) ∗
           na_inv logrel_nais (ns_fun (N.of_nat j)) (N.of_nat j ↦[wf] cl))%I.

  Definition ser_interp (vrel : value_relation) (se : semantic_env) (τ : type) : SVR :=
    λne sv,
      (∃ os, ⌜sv = SWords (flat_map serialize_atom os)⌝ ∗ ▷ vrel se τ (SAtoms os))%I.

  Definition plug_interp (se : semantic_env) (ρ : representation) : SVR :=
    λne sv, (∃ ιs, ⌜eval_rep se ρ = Some ιs⌝ ∗ ⌜has_areps ιs sv⌝)%I.

  Definition span_interp (se : semantic_env) (σ : size) : SVR :=
    λne sv, (∃ ws n, ⌜sv = SWords ws⌝ ∗ ⌜eval_size se σ = Some n⌝ ∗ ⌜length ws = n⌝)%I.

  Definition rec_interp (vrel : value_relation) (se : semantic_env) (κ : kind) (τ : type) : SVR :=
    λne sv,
      match eval_kind se κ with
      | Some sκ =>
          let T := λne sv, ▷ vrel se (RecT κ τ) sv in
          vrel (senv_insert_type sκ T se) τ sv
      | None => False
      end%I.

  Definition exists_mem_interp (vrel : value_relation) (se : semantic_env) (τ : type) : SVR :=
    λne sv, (∃ μ, ▷ vrel (senv_insert_mem μ se) τ sv)%I.

  Definition exists_rep_interp (vrel : value_relation) (se : semantic_env) (τ : type) : SVR :=
    λne sv, (∃ ιs, ▷ vrel (senv_insert_rep ιs se) τ sv)%I.

  Definition exists_size_interp (vrel : value_relation) (se : semantic_env) (τ : type) : SVR :=
    λne sv, (∃ n, ▷ vrel (senv_insert_size n se) τ sv)%I.

  Definition exists_type_interp
    (vrel : value_relation) (se : semantic_env) (κ : kind) (τ : type) : SVR :=
    λne sv, (∃ sκ T, ⌜eval_kind se κ = Some sκ⌝ ∗
                     ⌜skind_interp sκ T⌝ ∗
                     ▷ vrel (senv_insert_type sκ T se) τ sv)%I.

  Definition type_interp0 (vrel : value_relation) (se : semantic_env) : leibnizO type -n> SVR :=
    λne τ,
      match τ with
      | VarT t => type_var_interp se t
      | I31T _
      | NumT _ _ => λne _, True
      | SumT (VALTYPE (SumR ρs) _ _) τs => sum_interp vrel se ρs τs
      | SumT _ _ => λne _, False
      | VariantT _ τs => variant_interp vrel se τs
      | ProdT _ τs => prod_interp vrel se τs
      | StructT _ τs => struct_interp vrel se τs
      | RefT _ (VarM _) _ => λne _, False
      | RefT _ (BaseM MemMM) τ => ref_mm_interp vrel se τ
      | RefT _ (BaseM MemGC) τ => ref_gc_interp vrel se τ
      | CodeRefT _ ϕ => coderef_interp vrel se ϕ
      | SerT _ τ => ser_interp vrel se τ
      | PlugT _ ρ => plug_interp se ρ
      | SpanT _ σ => span_interp se σ
      | RecT κ τ => rec_interp vrel se κ τ
      | ExistsMemT _ τ => exists_mem_interp vrel se τ
      | ExistsRepT _ τ => exists_rep_interp vrel se τ
      | ExistsSizeT _ τ => exists_size_interp vrel se τ
      | ExistsTypeT _ κ τ => exists_type_interp vrel se κ τ
      end%I.

  Definition value_se_interp0 (vrel : value_relation) (se : semantic_env) : leibnizO type -n> SVR :=
    λne τ sv,
      (∃ κ,
         ⌜type_skind se τ = Some κ⌝ ∗
         skind_as_type_interp κ sv ∗
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

  Definition values_interp (se : semantic_env) : leibnizO (list type) -n> OsR :=
    values_interp0 value_interp se.

  Definition closure_interp (se : semantic_env) : leibnizO function_type -n> ClR :=
    λne ϕ, closure_interp0 value_interp se ϕ.

  Definition locals_interp (se : semantic_env) :
    leibnizO local_ctx -n> leibnizO (list (list atom)) -n> iPropO Σ :=
    λne L oss, ([∗ list] τ; os ∈ L; oss, value_interp se τ (SAtoms os))%I.

  Definition frame_interp (se : semantic_env) :
    leibnizO local_ctx -n> leibnizO wlocal_ctx -n> leibnizO instance -n> leibnizO frame -n>
      iPropO Σ :=
    λne L WL inst fr,
      (∃ oss_L vss_L vs_WL,
         ⌜fr = Build_frame (concat vss_L ++ vs_WL) inst⌝ ∗
           ⌜result_type_interp WL vs_WL⌝ ∗
           atoms_interp (concat oss_L) (concat vss_L) ∗
           locals_interp se L oss_L)%I.

  Fixpoint simple_get_base_l (lh : simple_valid_holed) :=
    match lh with
    | SH_base vs _ => vs
    | SH_rec _ _ _ lh' _ => simple_get_base_l lh'
    end.

  Definition return_interp (se : semantic_env) (τr : list type) :
    leibnizO simple_valid_holed -n> iPropO Σ :=
    λne svh,
      (∃ vs0 vs os,
         ⌜simple_get_base_l svh = vs0 ++ vs⌝ ∗
           atoms_interp os vs ∗
           values_interp se τr os ∗
           ∀ fr fr',
             ↪[frame] fr -∗
             ↪[RUN] -∗
             WP [AI_local (length vs) fr' (of_val (retV svh))]
                {{ lv,
                     ∃ os' vs',
                       ⌜lv = immV vs'⌝ ∗
                       atoms_interp os' vs' ∗
                       values_interp se τr os' ∗
                       ↪[frame] fr }})%I.

  Program Definition br_interp0
    (se : semantic_env) (τr : list type) (L : local_ctx) (WL : wlocal_ctx)
    (inst : instance) (br_interp : BR) :
    BR :=
    λne lh τc, λ j, λne (vh : leibnizO (valid_holed j)),
      (∃ k p lh' lh'' τs es0 es es' vs0 vs os,
         ⌜get_base_l vh = vs0 ++ vs⌝ ∗
           ⌜lh_depth (lh_of_vh vh) = p⌝ ∗
           ⌜τc !! (j - p) = Some (τs, L)⌝ ∗
           ⌜get_layer lh (lh_depth lh - S (j - p)) = Some (es0, k, es, lh', es')⌝ ∗
           ⌜lh_depth lh'' = lh_depth lh - S (j - p)⌝ ∗
           ⌜is_Some (lh_minus lh lh'')⌝ ∗
           atoms_interp os vs ∗
           values_interp se τs os ∗
           ∀ fr θ,
             frame_interp se L WL inst fr -∗
             rt_token rti sr θ -∗
             ↪[frame] fr -∗
             lenient_wp_ctx
               NotStuck top
               (of_val (immV vs) ++ [AI_basic (BI_br (j - p))])
               {| lp_fr := frame_interp se L WL inst;
                  lp_fr_inv := const True;
                  lp_val :=
                    fun vs' =>
                      ∃ τs' os' θ',
                        atoms_interp os' vs' ∗ values_interp se τs' os' ∗ rt_token rti sr θ';
                  lp_trap := True;
                  lp_br := br_interp lh'' (drop (S (j - p)) τc);
                  lp_ret := return_interp se τr;
                  lp_host := fun _ _ _ _ => False |}
               (S (lh_depth lh')) (LH_rec es0 k es lh' es'))%I.

  (* TODO *)
  Instance Contractive_br_interp0 se τr L WL inst : Contractive (br_interp0 se τr L WL inst).
  Admitted.

  Definition br_interp
    (se : semantic_env) (τr : list type) (L : local_ctx) (WL : wlocal_ctx) (inst : instance) :
    BR :=
    fixpoint (br_interp0 se τr L WL inst).

  Lemma br_interp_eq se τr L WL inst n lh l vh :
    br_interp se τr L WL inst lh l n vh ⊣⊢
      br_interp0 se τr L WL inst (br_interp se τr L WL inst) lh l n vh.
  Proof.
    f_equiv.
    (* f_equiv has some trouble with discrete_funO equivalences *)
    cut (br_interp se τr L WL inst lh l
           ≡ br_interp0 se τr L WL inst (br_interp se τr L WL inst) lh l).
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
    (L : local_ctx) (WL : wlocal_ctx)
    (τs : list type) (inst : instance) (lh : lholed) :
    leibnizO (list administrative_instruction) -n> iPropO Σ :=
    λne es,
      lenient_wp NotStuck top es
        {| lp_fr := frame_interp se L WL inst;
           lp_fr_inv := const True;
           lp_val :=
             fun vs =>
               ∃ os θ, values_interp se τs os ∗ atoms_interp os vs ∗ rt_token rti sr θ;
           lp_trap := True;
           lp_br := br_interp se τr L WL inst lh τc;
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
          closure_interp senv_empty ϕ cl ∗
          na_inv logrel_nais (ns_fun (N.of_nat i')) (N.of_nat i' ↦[wf] cl).

  Definition table_entry_interp (off : nat) (i : nat) (ϕ : function_type) : iProp Σ :=
    let nt := N.of_nat (off + i) in
    ∃ i' cl,
      closure_interp senv_empty ϕ cl ∗
        na_inv logrel_nais (ns_tab nt) (N.of_nat sr.(sr_table) ↦[wt][nt] Some i') ∗
        na_inv logrel_nais (ns_fun (N.of_nat i')) (N.of_nat i' ↦[wf] cl).

  Definition instance_table_interp (M : module_ctx) (mr : module_runtime) (inst : instance) : iProp Σ :=
    ⌜inst.(inst_tab) !! tableimm mr.(mr_table) = Some sr.(sr_table)⌝ ∗
      ∃ i_off off,
        let g_off := Build_global MUT_mut (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat off))) in
        ([∗ list] i ↦ ϕ ∈ M.(mc_table), table_entry_interp off i ϕ) ∗
          ⌜inst.(inst_globs) !! globalimm mr.(mr_global_table_off) = Some i_off⌝ ∗
          na_inv logrel_nais (ns_glo (N.of_nat i_off)) (N.of_nat i_off ↦[wg] g_off).

  Definition instance_interp
    (mr : module_runtime) (M : module_ctx) (WT : wtype_ctx) (inst : instance) : iProp Σ :=
    ⌜inst.(inst_types) = WT⌝ ∗
      instance_runtime_interp mr inst ∗
      instance_functions_interp M mr inst ∗
      ⌜inst.(inst_tab) !! tableimm mr.(mr_table) = Some sr.(sr_table)⌝ ∗
      instance_table_interp M mr inst ∗
      ⌜inst.(inst_memory) !! memimm mr.(mr_mem_mm) = Some sr.(sr_mem_mm)⌝ ∗
      ⌜inst.(inst_memory) !! memimm mr.(mr_mem_gc) = Some sr.(sr_mem_gc)⌝.

  Global Instance Persistent_instance_interp mr M WT inst : Persistent (instance_interp mr M WT inst).
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
    (L : local_ctx) (WL : wlocal_ctx)
    (inst : instance) (lh : lholed) (k : nat) (τs : list type) :
    iProp Σ :=
    (∃ j es0 es es' lh' lh'',
       ⌜get_layer lh (lh_depth lh - S k) = Some (es0, j, es, lh', es')⌝ ∧
         ⌜lh_depth lh'' = lh_depth lh - S k⌝ ∧
         ⌜is_Some (lh_minus lh lh'')⌝ ∧
         □ ∀ fr vs os θ,
             atoms_interp os vs -∗
             values_interp se τs os -∗
             frame_interp se L WL inst fr -∗
             rt_token rti sr θ -∗
             ↪[frame] fr -∗
             ↪[RUN] -∗
             ∃ τs',
               expr_interp se τr (drop (S k) τc) L WL τs' inst lh''
                 (es0 ++ of_val (immV vs) ++ es ++ es'))%I.

  Definition continuations_interp
    (se : semantic_env) (τr : list type) (τc : list (list type * local_ctx))
    (WL : wlocal_ctx) (inst : instance) :
    CtxR :=
    λne lh, ([∗ list] k ↦ '(τs, L) ∈ τc, continuation_interp se τr τc L WL inst lh k τs)%I.

  Definition labels_interp
    (se : semantic_env) (τr : list type) (τc : list (list type * local_ctx))
    (WL : wlocal_ctx) (inst : instance) :
    CtxR :=
    λne lh,
      (⌜base_is_empty lh⌝ ∗
         ⌜length_lholeds se (rev τc) lh⌝ ∗
         ⌜lholed_valid lh⌝ ∗
         continuations_interp se τr τc WL inst lh)%I.

  Definition memory_closed (m : memory) : Prop :=
    match m with
    | VarM _ => False
    | BaseM _ => True
    end.

  Definition kind_ctx_interp (K : kind_ctx) (se: semantic_env) : Prop :=
    K.(kc_mem_vars) = length (senv_mems se) /\
    K.(kc_rep_vars) = length (senv_reps se) /\
    K.(kc_size_vars) = length (senv_sizes se).
  
  Definition type_ctx_interp κs (se: semantic_env) : Prop :=
    Forall2 (fun κT κ => eval_kind se κ = Some (fst κT) /\
                      skind_interp (fst κT) (snd κT)) 
      (senv_types se) κs.

  Definition sem_env_interp (F : function_ctx) (se : semantic_env) : Prop :=
    kind_ctx_interp F.(fc_kind_ctx) se /\
    type_ctx_interp F.(fc_type_vars) se.

  Definition have_instruction_type_sem
    (mr : module_runtime)
    (M : module_ctx) (F : function_ctx) (L : local_ctx) (WT : wtype_ctx) (WL : wlocal_ctx)
    (es : list administrative_instruction)
    '(InstrT τs1 τs2 : instruction_type) (L' : local_ctx) :
    iProp Σ :=
    (∀ se inst lh fr os vs θ,
       ⌜sem_env_interp F se⌝ -∗
       instance_interp mr M WT inst -∗
       labels_interp se F.(fc_return) F.(fc_labels) WL inst lh -∗
       atoms_interp os vs -∗
       values_interp se τs1 os -∗
       frame_interp se L WL inst fr -∗
       rt_token rti sr θ -∗
       ↪[frame] fr -∗
       ↪[RUN] -∗
       expr_interp se F.(fc_return) F.(fc_labels) L' WL τs2 inst lh (of_val (immV vs) ++ es))%I.

End Relations.
