From mathcomp Require Import ssreflect.
From stdpp Require Import base list.
From RichWasm Require Import syntax typing util.
Require RichWasm.iris.logrel.
Require Import RecordUpdate.RecordUpdate.

Ltac fold_subst :=
  fold subst_type subst_size subst_representation subst_function_type.

Lemma subkind_of_subst s__rep s__size κ κ' :
  subkind_of κ κ' ->
  subkind_of (subst_kind s__rep s__size κ)
             (subst_kind s__rep s__size κ').
Proof.
  intros Hle.
  by destruct Hle; constructor.
Qed.


(* a deeply critical lemma that should almost certainly be true *)
Lemma has_kind_ft_through_inst_iff F ϕ ϕ' ix :
  function_type_inst F ix ϕ ϕ' ->
  (has_kind_ft F ϕ <->
     has_kind_ft F ϕ').
Proof.
Admitted.

Lemma has_kind_ft_through_inst F ϕ ϕ' ix :
  function_type_inst F ix ϕ ϕ' ->
  has_kind_ft F ϕ ->
  has_kind_ft F ϕ'.
Proof.
  intros.
  by apply (has_kind_ft_through_inst_iff F ϕ ϕ' ix H).
Qed.

Lemma has_kind_ft_through_inst_backwards F ϕ ϕ' ix :
  function_type_inst F ix ϕ ϕ' ->
  has_kind_ft F ϕ' ->
  has_kind_ft F ϕ.
Proof.
  intros.
  by apply (has_kind_ft_through_inst_iff F ϕ ϕ' ix H).
Qed.

  (* copied from typechecker.v *)
  Fixpoint get_all_lefts {A B : Type} (l: list (A + B)) : list A :=
    match l with
    | [] => []
    | a::l =>
        match a with
        | inl a => a:: get_all_lefts l
        | inr _ => get_all_lefts l
        end
    end.
  Fixpoint get_all_rights {A B : Type} (l: list (A + B)) : list B :=
    match l with
    | [] => []
    | a::l =>
        match a with
        | inl _ => get_all_rights l
        | inr b => b :: get_all_rights l
        end
    end.
  Definition kind_of_num (nt : num_type) : kind :=
    match nt with
    | IntT I32T => VALTYPE (AtomR I32R) NoRefs
    | IntT I64T => VALTYPE (AtomR I64R) NoRefs
    | FloatT F32T => VALTYPE (AtomR F32R) NoRefs
    | FloatT F64T => VALTYPE (AtomR F64R) NoRefs
    end.

  Definition kind_of_node (F : function_ctx) (τ : type) : kind :=
    match τ with
    | VarT t => match F.(fc_type_vars) !! t with
               | Some κ => κ
               | None => VALTYPE (AtomR I32R) NoRefs
               end
    | I31T κ | NumT κ _ | SumT κ _ | VariantT κ _ | ProdT κ _ | StructT κ _
    | RefT κ _ _ _ | CodeRefT κ _ | SerT κ _ | PlugT κ _ | SpanT κ _
    | RecT κ _ | ExistsMemT κ _ | ExistsRepT κ _ | ExistsSizeT κ _
    | ExistsTypeT κ _ _ => κ
    end.

  Definition get_rep_or_size κ :=
    match κ with
    | VALTYPE ρ _ => inl ρ
    | MEMTYPE σ _ => inr σ
    end.
  (* rebuilds the cached kind annotations that [subst] leaves stale *)
  Fixpoint refresh_kinds (F : function_ctx) (τ : type) : type :=
    match τ with
    | VarT t => VarT t
    | I31T _ => I31T (VALTYPE (AtomR PtrR) NoRefs)
    | NumT _ nt => NumT (kind_of_num nt) nt
    | SumT _ τs =>
        let τs' := map (refresh_kinds F) τs in
        let κs := map (kind_of_node F) τs' in
        SumT (VALTYPE (SumR (get_all_lefts (map get_rep_or_size κs)))
                (ref_flag_lub (map kind_ref_flag κs))) τs'
    | VariantT _ τs =>
        let τs' := map (refresh_kinds F) τs in
        let κs := map (kind_of_node F) τs' in
        VariantT (MEMTYPE (SumS (get_all_rights (map get_rep_or_size κs)))
                    (ref_flag_lub (map kind_ref_flag κs))) τs'
    | ProdT _ τs =>
        let τs' := map (refresh_kinds F) τs in
        let κs := map (kind_of_node F) τs' in
        ProdT (VALTYPE (ProdR (get_all_lefts (map get_rep_or_size κs)))
                 (ref_flag_lub (map kind_ref_flag κs))) τs'
    | StructT _ τs =>
        let τs' := map (refresh_kinds F) τs in
        let κs := map (kind_of_node F) τs' in
        StructT (MEMTYPE (ProdS (get_all_rights (map get_rep_or_size κs)))
                   (ref_flag_lub (map kind_ref_flag κs))) τs'
    | RefT _ μ β τ =>
        let κ := match μ with
                 | BaseM MemGC => VALTYPE (AtomR PtrR) GCRefs
                 | _ => VALTYPE (AtomR PtrR) AnyRefs
                 end in
        RefT κ μ β (refresh_kinds F τ)
    | CodeRefT _ ϕ => CodeRefT (VALTYPE (AtomR I32R) NoRefs) (refresh_kinds_ft F ϕ)
    | SerT _ τ =>
        let τ' := refresh_kinds F τ in
        let κ := match kind_of_node F τ' with
                 | VALTYPE ρ ξ => MEMTYPE (RepS ρ) ξ
                 | MEMTYPE σ ξ => MEMTYPE σ ξ
                 end in
        SerT κ τ'
    | PlugT _ ρ => PlugT (VALTYPE ρ NoRefs) ρ
    | SpanT _ σ => SpanT (MEMTYPE σ NoRefs) σ
    | RecT κ τ => RecT κ (refresh_kinds (F <| fc_type_vars ::= cons κ |>) τ)
    | ExistsMemT κ τ =>
        ExistsMemT κ (refresh_kinds (F <| fc_kind_ctx ::= set kc_mem_vars S |>) τ)
    | ExistsRepT κ τ =>
        ExistsRepT κ (refresh_kinds (add_rep_var F) τ)
    | ExistsSizeT κ τ =>
        ExistsSizeT κ (refresh_kinds (add_size_var F) τ)
    | ExistsTypeT κ κ0 τ =>
        ExistsTypeT κ κ0 (refresh_kinds (F <| fc_type_vars ::= cons κ0 |>) τ)
    end
  with refresh_kinds_ift (F : function_ctx) (ϕ : inner_function_type) : inner_function_type :=
         match ϕ with
         | MonoFunT τs1 τs2 => MonoFunT (map (refresh_kinds F) τs1) (map (refresh_kinds F) τs2)
         | ForallTypeT κ ϕ => ForallTypeT κ (refresh_kinds_ift (F <| fc_type_vars ::= cons κ |>) ϕ)
         end
  with refresh_kinds_ft (F : function_ctx) (ϕ : Core.function_type) : Core.function_type :=
         match ϕ with
         | InnerFunT ϕ => InnerFunT (refresh_kinds_ift F ϕ)
         | ForallMemT ϕ => ForallMemT (refresh_kinds_ft (F <| fc_kind_ctx ::= set kc_mem_vars S |>) ϕ)
         | ForallRepT ϕ => ForallRepT (refresh_kinds_ft (add_rep_var F) ϕ)
         | ForallSizeT ϕ => ForallSizeT (refresh_kinds_ft (add_size_var F) ϕ)
         end.

  (* copied from typechecker.v *)
  Lemma refresh_kinds_eq_mod_kinds :
    (forall τ F, type_eq_mod_kinds (refresh_kinds F τ) τ) /\
      (forall ϕ F, function_type_eq_mod_kinds (refresh_kinds_ft F ϕ) ϕ) /\
      (forall ϕ F, inner_function_type_eq_mod_kinds (refresh_kinds_ift F ϕ) ϕ).
  Proof.
    apply type_and_function_ind.
    - intros idx F; simpl; reflexivity.
    - intros κ F; simpl; exact I.
    - intros κ nt F; simpl; reflexivity.
    - intros κ ts IH F; simpl; induction IH as [|t ts' Hh Ht IHl]; simpl;
        [exact I | split; [apply Hh | exact IHl]].
    - intros κ ts IH F; simpl; induction IH as [|t ts' Hh Ht IHl]; simpl;
        [exact I | split; [apply Hh | exact IHl]].
    - intros κ ts IH F; simpl; induction IH as [|t ts' Hh Ht IHl]; simpl;
        [exact I | split; [apply Hh | exact IHl]].
    - intros κ ts IH F; simpl; induction IH as [|t ts' Hh Ht IHl]; simpl;
        [exact I | split; [apply Hh | exact IHl]].
    - intros κ μ β t IH F; simpl; split; [reflexivity | split; [reflexivity | apply IH]].
    - intros κ ft IH F; simpl; apply IH.
    - intros κ t IH F; simpl; apply IH.
    - intros κ ρ F; simpl; reflexivity.
    - intros κ σ F; simpl; reflexivity.
    - intros κ t IH F; simpl; apply IH.
    - intros κ t IH F; simpl; apply IH.
    - intros κ t IH F; simpl; apply IH.
    - intros κ t IH F; simpl; apply IH.
    - intros κ1 κ2 t IH F; simpl; split; [reflexivity | apply IH].
    - intros τs1 τs2 IH1 IH2 F; simpl; split;
        [ induction IH1 as [|t ts' Hh Ht IHl]; simpl; [exact I | split; [apply Hh | exact IHl]]
        | induction IH2 as [|t ts' Hh Ht IHl]; simpl; [exact I | split; [apply Hh | exact IHl]] ].
    - intros κ ft IH F; simpl; split; [reflexivity | apply IH].
    - done.
    - intros ft IH F; simpl; apply IH.
    - intros ft IH F; simpl; apply IH.
    - intros ft IH F; simpl; apply IH.
  Qed.


  Lemma kind_of_node_good F τ κ:
    has_kind F τ κ -> κ = kind_of_node F τ.
  Proof.
    intros Hkind.
    induction Hkind using has_kind_ind' with (P0 := const (const True)) (Pi := const (const True));
      intros; cbn; try done; try (rewrite <- IHHkind; done).
    rewrite H. done.
  Qed.

  (* NOT DONE P:M VERY FOUNDATIONAL BUT TRUE *)
  Lemma refresh_kinds_id :
    (* has_kind F τ κ -> τ = refresh_kinds F τ. *)
    (∀ τ F κ, has_kind F τ κ -> τ = refresh_kinds F τ) /\
      (∀ ϕ F, has_kind_ft F ϕ -> ϕ = refresh_kinds_ft F ϕ) /\
      (∀ iϕ F, has_kind_ift F iϕ -> iϕ = refresh_kinds_ift F iϕ).
  Proof.
    apply type_and_function_ind.
    (* checked a few cases, it's fine (especially the functions) *)
    13: { (* RecT *)
      intros *. intros IH. intros * Hkind.
      inversion Hkind; subst.
      apply IH in H3.
      cbn.
      rewrite <- H3.
      done.
    }
  Admitted.

  Lemma has_kind_subst_rec_helper :
    (∀ τ F κ, let τrec := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
              has_kind F (RecT κ τ) κ -> has_kind F τrec κ) /\
      (∀ (ϕ :Core.function_type), True) /\ (∀ (iϕ:inner_function_type), True).
  Proof.
    apply type_and_function_ind; try done.
    all: repeat (intros ?).
    all: unfold τrec; cbn in *;
      match goal with
      | H: ( has_kind _ (RecT _ _) _ ) |- _ => inversion H; subst
      end.
    1: {
      destruct idx.
      + cbn.
        constructor. done.
      + cbn.
        inversion H4; subst.
        constructor; try done.
      }
    1: inversion H4; subst; try done; subst κ1; cbn; constructor.
    1: inversion H4; subst; cbn; try constructor.
    (* okay base cases are chill *)
    10: {
      inversion H5; subst.
      clear H3 H7.
      apply H in H5.
      subst τrec.
      rewrite instId'_kind.
      eapply KRec.
      cbn in H5.
      (* this seems probably true.. *)
      admit.
    }
  Admitted.

  Lemma has_kind_rec_subst :
    (∀ τ F κ, let τrec := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
              has_kind F (RecT κ τ) κ -> has_kind F τrec κ).
  Proof. destruct has_kind_subst_rec_helper as (this & _). exact this. Qed.

  Lemma has_kind_ft_function_type_eq_mod_kinds:
    (∀ τ F κ subm subr subs subt,
        let substed := subst_type subm subr subs subt τ in
        has_kind F τ κ ->
        type_eq_mod_kinds τ substed ->
        τ = refresh_kinds F substed
    ) /\
    (∀ ϕ' F ϕ subm subr subs subt, let substed :=
      (subst_function_type subm subr subs subt ϕ) in
    has_kind_ft F ϕ' ->
    function_type_eq_mod_kinds ϕ' substed ->
    ϕ' = refresh_kinds_ft F substed) /\
    (∀ ϕ' F ϕ subm subr subs subt, let substed :=
      (subst_inner_function_type subm subr subs subt ϕ) in
    has_kind_ift F ϕ' ->
    inner_function_type_eq_mod_kinds ϕ' substed ->
    ϕ' = refresh_kinds_ift F substed).
  Proof.
    Opaque type_eq_mod_kinds.
    Opaque function_type_eq_mod_kinds.
    apply type_and_function_ind; intros * Hkind Heqmod; cbn in *;
      try (inversion Hkind; subst; done).
    Transparent type_eq_mod_kinds.
    Transparent function_type_eq_mod_kinds.
    1: {
      cbn in *.
      subst substed.
      destruct (subt idx) eqn:Hs; try done.
      subst; done.
    }
    6: {
      rename Hkind into IHkind; rename Heqmod into F.
      intros * Hkind Heqmod.
      inversion Hkind; subst.
      cbn in Heqmod.
      eapply IHkind in H3; try done.
      rewrite <- H3.
      subst κ1; done.
    }
    7: {
      cbn in *.
      rewrite <- Heqmod.
      inversion Hkind; subst; done.
    }
    16: {
      rename Hkind into IHkind; rename Heqmod into F.
      intros * Hkind Heqmod.
      cbn in *.
      inversion Hkind; subst.
      destruct (subst_function_type subm subr subs subt ϕ) eqn:hs;
        try done.
      assert (∃ f', ϕ = ForallMemT f'). {
        destruct ϕ; cbn in hs; inversion hs; try done.
        exists ϕ; done.
      }
      destruct H as (f' & ->).
      cbn in hs.
      inversion hs.
      subst f.
      eapply IHkind in H1; try done.
      rewrite H1.
      cbn.
      done.
    }
    14: {
      rename Hkind into IHkind; rename Heqmod into F.
      intros * Hkind Heqmod.
      cbn in *.
      inversion Hkind; subst.
      destruct (subst_inner_function_type subm subr subs subt ϕ) eqn:hs;
        try done.
      destruct Heqmod as (-> & Heqmod).
      assert (∃ κ' f', ϕ = ForallTypeT κ' f'). {
        destruct ϕ; cbn in hs; inversion hs; try done.
        eexists _, _; try done.
      }
      destruct H as (f' & κ' & ->).
      cbn in hs.
      inversion hs.
      subst i k.
      eapply IHkind in H3; try done.
      rewrite H3.
      cbn.
      done.
    }
    13: {
      rename Hkind into IHkind1; rename Heqmod into IHkind2.
      intros * Hkind Heqmod.
      cbn in *.
      destruct (subst_inner_function_type subm subr subs subt ϕ) eqn:hs;
        try done.
      (* okay yup this looks fine *)
      cbn.
      (* it looks annoying but fine to combine everything *)
      admit.
    }
  Admitted.
