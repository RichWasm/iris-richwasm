Require Import iris.algebra.list.
Require Import iris.proofmode.proofmode.

From RichWasm.iris.helpers Require Import iris_properties.
Require Import RichWasm.iris.host.iris_host.

From RichWasm.named_props Require Import named_props.

From RichWasm.compiler Require Import prelude codegen.
From RichWasm.iris Require Import memory runtime util numerics.
From RichWasm.iris.language Require Import cwp iris_wp_def logpred.
From RichWasm Require Import syntax typing layout util.

Require Import Corelib.Init.Datatypes.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section instr.

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

  Notation SVR := (leibnizO semantic_value -n> iPropO Σ).

  Definition mem_env : Type := list base_memory.
  Definition rep_env : Type := list (list atomic_rep).
  Definition size_env : Type := list nat.
  Definition type_env : Type := listO (prodO (leibnizO skind) SVR).
  Definition semantic_env : Type := prodO (leibnizO (mem_env * rep_env * size_env)) type_env.

  Notation SVRO := (semantic_env -n> SVR).

  Implicit Types vrel : semantic_env -n> SVR.
  Implicit Types se : semantic_env.

  Definition senv_empty : semantic_env := ([], [], [], []).

  Program Definition senv_mems : semantic_env -n> leibnizO mem_env := λne se, se.1.1.1.
  Next Obligation.
    repeat intros ?; cbn.
    destruct H.
    by rewrite H.
  Qed.
  Program Definition senv_reps : semantic_env -n> leibnizO rep_env := λne se, se.1.1.2.
  Next Obligation.
    repeat intros ?; cbn.
    destruct H.
    by rewrite H.
  Qed.
  Program Definition senv_sizes : semantic_env -n> leibnizO size_env := λne se, se.1.2.
  Next Obligation.
    repeat intros ?; cbn.
    destruct H.
    by rewrite H.
  Qed.
  Program Definition senv_types : semantic_env -n> type_env := λne se, se.2.
  Solve All Obligations with solve_proper.

  #[global]
  Instance semantic_env_env : Env semantic_env :=
    {
      lookup_mem se i := senv_mems se !! i;
      lookup_rep se i := senv_reps se !! i;
      lookup_size se i := senv_sizes se !! i;
    }.

  Program Definition lookup_type : semantic_env -n> leibnizO nat -n> optionO (prodO (leibnizO skind) SVR) :=
    λne se i, senv_types se !! i.
  Solve All Obligations with solve_proper.

  Definition senv_insert_type (sκ : skind) (T : SVR) (se : semantic_env) : semantic_env :=
    (senv_mems se, senv_reps se, senv_sizes se, (sκ, T) :: senv_types se).

  Definition senv_insert_mem (μ : base_memory) (se : semantic_env) : semantic_env :=
    (μ :: senv_mems se, senv_reps se, senv_sizes se, senv_types se).

  Definition senv_insert_rep (ιs : list atomic_rep) (se : semantic_env) : semantic_env :=
    (senv_mems se, ιs :: senv_reps se, senv_sizes se, senv_types se).

  Definition senv_insert_size (n : nat) (se : semantic_env) : semantic_env :=
    (senv_mems se, senv_reps se, n :: senv_sizes se, senv_types se).

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
  Implicit Type v : leibnizO value.
  Implicit Type os : leibnizO (list atom).
  Implicit Type oss : leibnizO (list (list atom)).
  Implicit Type vs : leibnizO (list value).
  Implicit Type ws : leibnizO (list word).
  Implicit Type fr : leibnizO frame.
  Implicit Type cl : leibnizO function_closure.
  Implicit Type inst : leibnizO instance.

  (*Definition value_relation : Type := leibnizO type -n> semantic_env -n> semantic_type.*)
  Definition semantic_type := semantic_env -n> SVR.

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
                       | MemMM => ℓ ↦addr (μ, a)
                       | MemGC => a ↦root ℓ
                       end
        | _ => False
        end
    end.

  Definition atom_interp (o : atom) : leibnizO value -n> iPropO Σ :=
    λne v,
      match o with
      | PtrA p =>
          ∃ n n32,
            ⌜N_i32_repr n n32⌝ ∗
            ⌜v = VAL_int32 n32⌝ ∗
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

  Definition has_prim (η : primitive) (v : value) : Prop :=
    match η, v with
    | I32P, VAL_int32 _
    | I64P, VAL_int64 _
    | F32P, VAL_float32 _
    | F64P, VAL_float64 _ => True
    | _, _ => False
    end.

  Definition has_prims (ηs : list primitive) (vs : list value) : Prop :=
    Forall2 has_prim ηs vs.

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

  Definition forall_swords (sv : semantic_value) (P : word -> Prop) : Prop :=
    exists ws, sv = SWords ws /\ Forall P ws.

  Definition forall_ptr_atom (P : pointer -> Prop) (o : atom) : Prop :=
    match o with
    | PtrA p => P p
    | _ => True
    end.

  Definition forall_ptr_word (P : pointer -> Prop) (w : word) : Prop :=
    match w with
    | WordPtr p => P p
    | _ => True
    end.

  Definition norefs_ptr_interp (p : pointer) : Prop :=
    match p with
    | PtrInt _ => True
    | PtrHeap _ _ => False
    end.

  Definition gcrefs_ptr_interp (p : pointer) : Prop :=
    match p with
    | PtrInt _ => True
    | PtrHeap MemMM _ => False
    | PtrHeap MemGC _ => True
    end.

  Definition ref_flag_interp (ξ : ref_flag) : pointer -> Prop :=
    match ξ with
    | NoRefs => norefs_ptr_interp
    | GCRefs => gcrefs_ptr_interp
    | AnyRefs => const True
    end.

  Definition ref_flag_atoms_interp (ξ : ref_flag) (sv : semantic_value) : Prop :=
    forall_satoms sv (forall_ptr_atom (ref_flag_interp ξ)).

  Definition ref_flag_words_interp (ξ : ref_flag) (sv : semantic_value) : Prop :=
    forall_swords sv (forall_ptr_word (ref_flag_interp ξ)).

  Definition ssize_interp (n : nat) (sv : semantic_value) : Prop :=
    match sv with
    | SAtoms _ => False
    | SWords ws => n = length ws
    end.

  Definition svalue_in_skind (sv : semantic_value) (sκ : skind) : Prop :=
    match sκ with
    | SVALTYPE ιs ξ => has_areps ιs sv /\ ref_flag_atoms_interp ξ sv
    | SMEMTYPE n ξ => ssize_interp n sv /\ ref_flag_words_interp ξ sv
    end.

  Definition stype_in_skind (T : SVR) (sκ : skind) : Prop :=
    forall sv, T sv -∗ ⌜svalue_in_skind sv sκ⌝.

  (*
  Definition values_interp0 (vrel : value_relation) (se : semantic_env) :
    leibnizO (list type) -n> OsR :=
    λne τs os,
      (∃ oss, ⌜os = concat oss⌝ ∗ [∗ list] τ; os ∈ τs; oss, vrel τ se (SAtoms os))%I. *)

  Definition type_skind (se : semantic_env) (τ : type) : option skind :=
    match τ with
    | VarT x => fst <$> lookup_type se x
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

  Definition skind_rep (κ : skind) : option (list atomic_rep) :=
    match κ with
    | SVALTYPE ιs _ => Some ιs
    | _ => None
    end.

  Definition type_arep (se : semantic_env) (τ : type) : option (list atomic_rep) :=
    κ ← type_skind se τ;
    skind_rep κ.

  Definition translate_type (se : semantic_env) (τ : type) : option (list W.value_type) :=
    map translate_arep <$> type_arep se τ.
  
  Definition translate_types (se : semantic_env) (τs : list type) : option (list W.value_type) :=
    @concat _ <$> mapM (translate_type se) τs.

  (* Value type interpretations. *)
  Program Definition type_var_interp : leibnizO nat -n> SVRO :=
    λne t se,
      default (λne _, False%I) (snd <$> lookup_type se t).
  Solve All Obligations with solve_proper.

  Program Definition i31_interp : SVR :=
    λne _, True%I.

  Program Definition num_interp : leibnizO num_type -n> SVR :=
    λne nt _, True%I.

  Program Definition eval_rep_se : semantic_env -n> leibnizO representation -n> leibnizO (option (list atomic_rep)) :=
    λne se ρ, eval_rep se ρ.
  Next Obligation.
    intros.
    solve_proper.
  Qed.
  Next Obligation.
    repeat intros ?; cbn.
    revert H.
    revert x y.
    induction x0 using rep_ind; intros; cbn; try solve_proper.
    - by rewrite H.
    - f_equiv.
      apply Forall_mapM_ext.
      eapply Forall_impl; first apply H.
      cbn; intros.
      by apply H1.
    - f_equiv.
      apply Forall_mapM_ext.
      eapply Forall_impl; first apply H.
      cbn; intros.
      by apply H1.
  Qed.

  Program Definition eval_mem_se : semantic_env -n> leibnizO memory -n> leibnizO (option base_memory) :=
    λne se ρ, eval_mem se ρ.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    repeat intros ?; cbn.
    unfold eval_mem.
    destruct H, x0; auto.
    solve_proper.
  Qed.

  Program Definition sum_offset_se : semantic_env -n> leibnizO (list representation) -n> leibnizO nat -n> leibnizO (option nat) :=
    λne se ρs i, sum_offset se ρs i.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    unfold sum_offset.
    change (eval_rep) with (λ se ρ, eval_rep_se se ρ).
    repeat intros ?; cbn.
    f_equiv.
    apply eval_rep_se in H.
    cbn in H.
    apply Forall_mapM_ext; apply Forall_forall; intros.
    eapply H.
  Qed.

  Program Definition sum_interp (ρs : list representation) : listO SVRO -n> SVRO :=
    λne (τs : list SVRO) (se : semantic_env) sv,
      (∃ (i : nat) os off count,
         ⌜sv = SAtoms (I32A (Wasm_int.int_of_Z i32m (Z.of_nat i)) :: os)⌝ ∗
         ⌜sum_offset_se se ρs i = Some off⌝ ∗
         ⌜length <$> ρs !! i ≫= eval_rep se = Some count⌝ ∗
         match list_lookup i τs with
         | Some τi => τi se (SAtoms (take count (drop off os)))
         | None => False%I
         end)%I.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    intros ρs τs n se se' Hse sv.
    cbn.
    repeat (f_equiv;
            try match goal with
                | |- se = se' => fail 2
                | |- eval_rep se = eval_rep se' => fail 2
              end).
    - by eapply sum_offset_se.
    - destruct (ρs !! a); cbn; auto.
      by eapply eval_rep_se.
    - destruct (list_lookup a τs); solve_proper.
  Qed.
  Next Obligation.
    intros * se se' Hse sv sv'.
    cbn.
    repeat f_equiv.
    assert (Haa: se  !! a ≡{n}≡ se' !! a) by solve_proper.
    inversion Haa as [τi τi' Haa' Ha Ha'|Ha Ha']; unfold lookup in *;
      rewrite -Ha -Ha'.
    - apply Haa'.
    - done.
  Qed.

  Program Definition variant_interp : list semantic_type -n> semantic_env -n> SVR :=
    λne (τs : listO semantic_type) se sv,
      (∃ i n ws ws',
         ⌜N_nat_repr i n⌝ ∗
         ⌜sv = SWords (WordInt n :: ws ++ ws')⌝ ∗
         match list_lookup i τs with
         | Some τ => τ se (SWords ws)
         | None => False%I
         end)%I.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    repeat intros ?.
    cbn.
    repeat (f_equiv || solve_proper).
    destruct (list_lookup _ _); solve_proper.
  Qed.
  Next Obligation.
    intros i τs τs' Hτs se se'.
    cbn.
    do 10 f_equiv.
    eapply (list_lookup_ne a) in Hτs.
    inversion Hτs as [τi τi' Haa' Ha Ha'|Ha Ha'];
      unfold lookup in *; rewrite -Ha -Ha'.
    - solve_proper.
    - solve_proper.
  Qed.

  Program Definition prod_interp : listO semantic_type -n> semantic_type :=
    λne τs se sv,
      (∃ oss,
         ⌜sv = SAtoms (concat oss)⌝ ∗
         [∗ list] (τ : semantic_type); os ∈ τs; oss, τ se (SAtoms os))%I.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    intros k τs τs' Hτs se se'; cbn.
    f_equiv.
    f_equiv.
    f_equiv.
    erewrite (big_sepL2_ne_2);
      swap 1 4; swap 1 2; swap 3 2.
    - eapply Hτs.
    - reflexivity.
    - instantiate (1:= fun k0 t0 ats0 => t0 se (SAtoms ats0)).
      solve_proper.
    - reflexivity.
  Qed.

  Program Definition struct_interp : listO semantic_type -n> semantic_type :=
    λne τs se sv,
      (∃ wss,
          ⌜sv = SWords (concat wss)⌝ ∗
          [∗ list] ws; (τ: semantic_type) ∈ wss; τs, τ se (SWords ws))%I.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    intros k τs τs' Hτs se se'; cbn.
    f_equiv.
    f_equiv.
    f_equiv.
    erewrite (big_sepL2_ne_2);
      swap 1 4; swap 1 2; swap 3 2.
    - reflexivity.
    - eapply Hτs.
    - instantiate (1:= fun k0 ws0 t0 => t0 se (SWords ws0)).
      solve_proper.
    - reflexivity.
  Qed.

  Program Definition ref_mm_interp : semantic_type -n> semantic_type :=
    λne τ se sv,
      (∃ ℓ fs ws,
         ⌜sv = SAtoms [PtrA (PtrHeap MemMM ℓ)]⌝ ∗
         ℓ ↦layout fs ∗
         ℓ ↦heap ws ∗
         ▷ τ se (SWords ws))%I.
  Solve All Obligations with solve_proper.

  Program Definition ref_gc_interp : semantic_type -n> semantic_type :=
    λne τ se sv,
      (∃ ℓ fs,
         ⌜sv = SAtoms [PtrA (PtrHeap MemGC ℓ)]⌝ ∗
         na_inv logrel_nais (ns_ref ℓ)
         (∃ ws, ℓ ↦layout fs ∗ ℓ ↦heap ws ∗ ▷ τ se (SWords ws)))%I.
  Solve All Obligations with solve_proper.

  Program Definition ref_interp : leibnizO memory -n> semantic_type -n> semantic_type :=
    λne (μ : leibnizO memory) τ se,
      match eval_mem_se se μ with
      | Some MemMM => ref_mm_interp τ se
      | Some MemGC => ref_gc_interp τ se
      | None => λne sv, False%I
      end.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    cbn.
    intros μ τ n se se' Hse.
    replace (eval_mem se' μ) with (eval_mem se μ); swap 1 2.
    { by eapply eval_mem_se. }
    destruct (eval_mem se μ) as [[|]|] eqn:Heq; rewrite Heq; cbn; solve_proper.
  Qed.
  Next Obligation.
    cbn.
    intros μ k τ τ' Hτ se; cbn.
    destruct (eval_mem se μ) as [[|]|] eqn:Heq; rewrite Heq; cbn; solve_proper.
  Qed.
  Next Obligation.
    cbn.
    intros k μ μ' <- τ' se sv; cbn.
    solve_proper.
  Qed.

  Program Fixpoint type_interp (τ : leibnizO type) : semantic_env -n> SVR :=
      match τ with
      | VarT t =>
          type_var_interp t
      | I31T _ => i31_interp
      | NumT _ nt => num_interp nt
      | SumT (VALTYPE (SumR ρs) _) τs =>
          sum_interp ρs (map type_interp τs)
      | SumT _ _ => λne _ _, False%I
      | VariantT _ τs => variant_interp (map type_interp τs)
      | ProdT _ τs => prod_interp (map type_interp τs)
      | StructT _ τs => struct_interp (map type_interp τs)
      | RefT _ μ τ => ref_interp μ (type_interp τ)
      | _ => λne se (sv : leibnizO semantic_value), emp%I
      end.

  Fixpoint type_interp (τ : leibnizO type) : semantic_env -n> SVR :=
    λne (se : semantic_env),
      match τ with
      | VarT t => type_var_interp se t
      | I31T _ => i31_interp
      | NumT _ nt => num_interp nt
      | _ => λne (sv : leibnizO semantic_value), emp%I
      end.
      | SumT (VALTYPE (SumR ρs) _) τs => sum_interp ρs (map type_interp τs) se
      | _ => λne _, False%I
      end.
      | SumT _ _ => λne _, False
      | VariantT _ τs => variant_interp vrel se τs
      | ProdT _ τs => prod_interp vrel se τs
      | StructT _ τs => struct_interp vrel se τs
      | RefT _ μ τ => ref_interp vrel se μ τ
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

  Definition mono_closure_interp0 vrel (se : semantic_env) :
    leibnizO (list type) -n> leibnizO (list type) -n> ClR :=
    λne τs1 τs2 cl,
      match cl with
      | FC_func_native inst (Tf ts1 ts2) tlocs es =>
          ⌜translate_types se τs1 = Some ts1⌝ ∗
          ⌜translate_types se τs2 = Some ts2⌝ ∗
          □ ▷ ∀ vs1 os1 θ,
            atoms_interp os1 vs1 -∗
            values_interp0 vrel se τs1 os1 -∗
            rt_token rti sr θ -∗
            na_own logrel_nais ⊤ -∗
            ↪[frame] Build_frame (vs1 ++ n_zeros tlocs) inst -∗
            ↪[RUN] -∗
            let Φ vs2 :=
              (∃ os2, atoms_interp os2 vs2 ∗ values_interp0 vrel se τs2 os2) ∗
                (∃ θ', rt_token rti sr θ') ∗ na_own logrel_nais ⊤
            in
            CWP es UNDER [(length ts2, const Φ)]; Some (length ts2, Φ) {{ const Φ }}
      | FC_func_host _ _ => False
      end%I.

  Fixpoint closure_interp0
    (vrel : value_relation) (se : semantic_env) (ϕ : leibnizO function_type) : ClR :=
    λne cl,
      match ϕ with
      | MonoFunT τs1 τs2 => mono_closure_interp0 vrel se τs1 τs2 cl
      | ForallMemT ϕ' => ∀ μ, closure_interp0 vrel (senv_insert_mem μ se) ϕ' cl
      | ForallRepT ϕ' => ∀ ιs, closure_interp0 vrel (senv_insert_rep ιs se) ϕ' cl
      | ForallSizeT ϕ' => ∀ n, closure_interp0 vrel (senv_insert_size n se) ϕ' cl
      | ForallTypeT κ ϕ' =>
          ∃ sκ,
            ⌜eval_kind se κ = Some sκ⌝ ∗
              ∀ sκ_T T,
                ⌜subskind_of sκ_T sκ⌝ -∗
                ⌜stype_in_skind T sκ_T⌝ -∗
                closure_interp0 vrel (senv_insert_type sκ_T T se) ϕ' cl
      end%I.

  (* TODO *)
  Global Instance Persistent_closure_interp0 vrel se ϕ cl : Persistent (closure_interp0 vrel se ϕ cl).
  Admitted.

  Global Instance closure_interp0_ne vrel se ϕ : NonExpansive2 (closure_interp0 vrel se).
  Admitted.

  Definition variant_interp
    (vrel : value_relation) (se : semantic_env) (τs : list type) : SVR :=
    λne sv,
      (∃ i n ws ws' τ,
         ⌜N_nat_repr i n⌝ ∗
         ⌜sv = SWords (WordInt n :: ws ++ ws')⌝ ∗
         ⌜τs !! i = Some τ⌝ ∗
         ▷ vrel se τ (SWords ws))%I.

  Definition prod_interp (vrel : value_relation) (se : semantic_env) (τs : list type) : SVR :=
    λne sv,
      (∃ oss, ⌜sv = SAtoms (concat oss)⌝ ∗ [∗ list] τ; os ∈ τs; oss, vrel se τ (SAtoms os))%I.

  Definition struct_interp (vrel : value_relation) (se : semantic_env) (τs : list type) : SVR :=
    λne sv,
      (∃ wss,
         ⌜sv = SWords (concat wss)⌝ ∗ [∗ list] ws; τ ∈ wss; τs, vrel se τ (SWords ws))%I.

  Definition ref_mm_interp (vrel : value_relation) : leibnizO semantic_env -n> leibnizO type -n> SVR :=
    λne se τ sv,
      (∃ ℓ fs ws,
         ⌜sv = SAtoms [PtrA (PtrHeap MemMM ℓ)]⌝ ∗
           ℓ ↦layout fs ∗
           ℓ ↦heap ws ∗
           ▷ vrel se τ (SWords ws))%I.

  Definition ref_gc_interp (vrel : value_relation) : semantic_env -n> type -n> SVR :=
    λne vrel se τ sv,
      (∃ ℓ fs,
         ⌜sv = SAtoms [PtrA (PtrHeap MemGC ℓ)]⌝ ∗
           na_inv logrel_nais (ns_ref ℓ)
             (∃ ws, ℓ ↦layout fs ∗ ℓ ↦heap ws ∗ ▷ vrel se τ (SWords ws)))%I.

  Definition ref_interp : value_relation -n> semantic_env -n> leibnizO memory -n> leibnizO type -n> SVR :=
    λne vrel se (μ : leibnizO memory),
      match eval_mem se μ with
      | Some MemMM => ref_mm_interp vrel se
      | Some MemGC => ref_gc_interp vrel se
      | None => False
      end.

  Definition coderef_interp (vrel : value_relation) (se : semantic_env) (ϕ : function_type) : SVR :=
    λne sv,
      (∃ i i32 j cl,
         ⌜N_i32_repr i i32⌝ ∗
           ⌜sv = SAtoms [I32A i32]⌝ ∗
           closure_interp0 vrel se ϕ cl ∗
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
    λne sv,
      (∃ sκ T,
         ⌜eval_kind se κ = Some sκ⌝ ∗
           ⌜stype_in_skind T sκ⌝ ∗
           ▷ vrel (senv_insert_type sκ T se) τ sv)%I.

  Program Definition type_interp0 : value_relation -n> semantic_env -n> leibnizO type -n> SVR :=
    λne vrel se τ,
      match τ with
      | VarT t => type_var_interp se t
      | I31T _ => i31_interp
      | NumT _ nt => num_interp nt
      | SumT (VALTYPE (SumR ρs) _) τs => sum_interp vrel se ρs τs
      | SumT _ _ => λne _, False
      | VariantT _ τs => variant_interp vrel se τs
      | ProdT _ τs => prod_interp vrel se τs
      | StructT _ τs => struct_interp vrel se τs
      | RefT _ μ τ => ref_interp vrel se μ τ
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
  Next Obligation.

  Program Definition value_se_interp0 : value_relation -n> semantic_env -n> leibnizO type -n> SVR :=
    λne vrel se τ sv,
      (∃ sκ, ⌜type_skind se τ = Some sκ⌝ ∗ ⌜svalue_in_skind sv sκ⌝ ∗ type_interp0 vrel se τ sv)%I.

  (* TODO *)
  Local Instance NonExpansive_value_se_interp0 (vrel : value_relation) :
    NonExpansive (λ se, λne τ sv, value_se_interp0 vrel se τ sv).
  Proof.
    cbn.
    intros .
    destruct τ.
    - solve_proper.
    repeat intros ?; cbn; try solve_proper.
    solve_proper.
    intros k x y.
    induction τ.
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
    leibnizO (list (list primitive)) -n>
      leibnizO local_ctx -n>
      leibnizO wlocal_ctx -n>
      leibnizO frame -n>
      iPropO Σ :=
    λne ηss L WL fr,
      (∃ oss vs_L vs_WL,
         ⌜fr.(f_locs) = vs_L ++ vs_WL⌝ ∗
         ⌜has_prims (concat ηss) vs_L⌝ ∗
         ⌜result_type_interp WL vs_WL⌝ ∗
         atoms_interp (concat oss) vs_L ∗
         locals_interp se L oss)%I.

  Fixpoint simple_get_base_l (lh : simple_valid_holed) :=
    match lh with
    | SH_base vs _ => vs
    | SH_rec _ _ _ lh' _ => simple_get_base_l lh'
    end.

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
    ∃ i' cl nt zt,
      ⌜N_nat_repr (off + i) nt⌝ ∗
        ⌜N_Z_repr nt zt⌝ ∗
        ⌜zt < Wasm_int.Int32.modulus⌝%Z ∗
        closure_interp senv_empty ϕ cl ∗
        na_inv logrel_nais (ns_tab nt) (N.of_nat sr.(sr_table) ↦[wt][nt] Some i') ∗
        na_inv logrel_nais (ns_fun (N.of_nat i')) (N.of_nat i' ↦[wf] cl).

  Definition instance_table_interp (M : module_ctx) (mr : module_runtime) (inst : instance) : iProp Σ :=
    ⌜inst.(inst_tab) !! 0 = Some sr.(sr_table)⌝ ∗
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
      instance_table_interp M mr inst ∗
      ⌜inst.(inst_memory) !! memimm mr.(mr_mmmem) = Some sr.(sr_mem_mm)⌝ ∗
      ⌜inst.(inst_memory) !! memimm mr.(mr_gcmem) = Some sr.(sr_mem_gc)⌝.

  Global Instance Persistent_instance_interp mr M WT inst : Persistent (instance_interp mr M WT inst).
  Proof.
    typeclasses eauto.
  Defined.

  Definition mask_locs_eq (lmask : nat -> Prop) (fr fr' : frame) : Prop :=
    forall i, lmask i -> fr.(f_locs) !! i = fr'.(f_locs) !! i.

  Definition frame_rel (lmask : nat -> Prop) (fr fr' : frame) : Prop :=
    mask_locs_eq lmask fr fr' /\ fr.(f_inst) = fr'.(f_inst).

  Definition label_interp
    (se : semantic_env) (ηss : list (list primitive)) (fr0 : frame) (WL : wlocal_ctx)
    (lmask : nat -> Prop) '((τs, L) : list type * local_ctx) '((n, P) : label_spec) :
    iProp Σ :=
    (match translate_types se τs with Some ts => ⌜length ts = n⌝ | None => False end ∗
       □ (∀ fr vs os θ,
            ⌜frame_rel lmask fr0 fr⌝ -∗
            frame_interp se ηss L WL fr -∗
            rt_token rti sr θ -∗
            na_own logrel_nais ⊤ -∗
            atoms_interp os vs -∗
            values_interp se τs os -∗
            P fr vs))%I.

  Global Instance Persistent_label_interp se ηss fr0 WL lmask a b :
    Persistent (label_interp se ηss fr0 WL lmask a b).
  Proof.
    destruct a, b.
    typeclasses eauto.
  Defined.

  Definition labels_interp
    (se : semantic_env) (ηss : list (list primitive)) (fr : frame) (WL : wlocal_ctx)
    (lmask : nat -> Prop) :
    list (list type * local_ctx) -> list label_spec -> iProp Σ :=
    big_sepL2 (const (label_interp se ηss fr WL lmask)).

  Global Instance Persistent_labels_interp se ηss fr WL lmask l a :
    Persistent (labels_interp se ηss fr WL lmask l a).
  Proof.
    apply big_sepL2_persistent'. intros; cbn.
    typeclasses eauto.
  Defined.

  Definition return_interp (se : semantic_env) (τr : list type) (R : option return_spec) :
    iProp Σ :=
    match R with
    | Some (n, P) =>
        match translate_types se τr with Some ts => ⌜length ts = n⌝ | None => False end ∗
          □ ∀ vs os θ,
            atoms_interp os vs -∗
            values_interp se τr os -∗
            rt_token rti sr θ -∗
            na_own logrel_nais ⊤ -∗
            P vs
    | None => False
    end%I.

  Global Instance Persistent_return_interp se τr R : Persistent (return_interp se τr R).
  Proof.
    typeclasses eauto.
  Defined.

  Definition memory_closed (m : memory) : Prop :=
    match m with
    | VarM _ => False
    | BaseM _ => True
    end.

  Definition kind_ctx_interp (K : kind_ctx) (se: semantic_env) : Prop :=
    K.(kc_mem_vars) = length (senv_mems se) /\
    K.(kc_rep_vars) = length (senv_reps se) /\
    K.(kc_size_vars) = length (senv_sizes se).
  
  Definition type_ctx_interp (κs : list kind) (se : semantic_env) : Prop :=
    Forall2
      (fun κ '(sκ, T) => eval_kind se κ = Some sκ /\ stype_in_skind T sκ)
      κs
      (senv_types se).

  Definition sem_env_interp (F : function_ctx) (se : semantic_env) : Prop :=
    kind_ctx_interp F.(fc_kind_ctx) se /\
    type_ctx_interp F.(fc_type_vars) se.

  Definition have_instr_type_sem
    (mr : module_runtime)
    (M : module_ctx) (F : function_ctx) (L : local_ctx)
    (WT : wtype_ctx) (WL : wlocal_ctx) (lmask : nat -> Prop)
    (es : list basic_instruction)
    '(InstrT τs1 τs2 : instruction_type) (L' : local_ctx) :
    iProp Σ :=
    (∀ se fr os vs evs θ B R,
       "%Hse" ∷ ⌜sem_env_interp F se⌝ -∗
       "%Hevs" ∷ ⌜has_values evs vs⌝ -∗
       "#Hinst" ∷ instance_interp mr M WT fr.(f_inst) -∗
       "#Hlabels" ∷ labels_interp se F.(fc_locals) fr WL lmask F.(fc_labels) B -∗
       "#Hreturn" ∷ return_interp se F.(fc_return) R -∗
       "Hvs" ∷ atoms_interp os vs -∗
       "Hos" ∷ values_interp se τs1 os -∗
       "Hframe" ∷ frame_interp se F.(fc_locals) L WL fr -∗
       "Hrt" ∷ rt_token rti sr θ -∗
       "Hown" ∷ na_own logrel_nais ⊤ -∗
       "Hfr" ∷ ↪[frame] fr -∗
       "Hrun" ∷ ↪[RUN] -∗
       CWP evs ++ es UNDER B; R
           {{ fr'; vs',
              ⌜frame_rel lmask fr fr'⌝ ∗ frame_interp se F.(fc_locals) L' WL fr' ∗
                (∃ os', values_interp se τs2 os' ∗ atoms_interp os' vs') ∗
                (∃ θ', rt_token rti sr θ') ∗ na_own logrel_nais ⊤ }})%I.

End instr.

Section module.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!richwasmG Σ}.
  Context `{!hvisG Σ}.
  Context `{!hmsG Σ}.
  Context `{!hasG Σ}.

  Variable rti : rt_invariant Σ.
  Variable sr : store_runtime.

  (* TODO *)
  Definition module_interp (ω : module_type) (mr : module_runtime) (m : W.module) : iProp Σ :=
    (∀ i imports exports,
       i ↪[mods] m -∗
       (* TODO: Assert that indices in the module point to the global runtime funcaddrs. *)
       ([∗ list] i ↦ ϕ ∈ ω.(mt_imports),
          ∃ bs j cl,
            N.of_nat i ↪[vis] datatypes.Build_module_export bs (MED_func j) ∗
              N.of_nat (funcimm j) ↦[wf] cl ∗
              closure_interp rti sr senv_empty ϕ cl ∗
              ⌜imports !! (funcimm mr.(mr_func_user) + i)%nat = Some (N.of_nat (funcimm j))⌝) -∗
       ([∗ list] i ↦ '_ ∈ ω.(mt_exports),
          ∃ bs j,
            N.of_nat i ↪[vis] datatypes.Build_module_export bs (MED_func j) ∗
              ⌜exports !! i = Some (N.of_nat (funcimm j))⌝) -∗
       WP ([ID_instantiate exports i imports], []) : host_expr @ top
          {{ v : host_val,
             ⌜v = immHV []⌝ ∗
               i ↪[mods] m ∗
               ([∗ list] i ↦ ϕ ∈ ω.(mt_exports),
                 ∃ j cl, (* TODO: same j as precond *)
                   N.of_nat (funcimm j) ↦[wf] cl ∗ closure_interp rti sr senv_empty ϕ cl) }})%I.

  (* TODO *)
  Definition has_module_type_sem (m : W.module) (ω : module_type) : iProp Σ :=
    True%I.

End module.
