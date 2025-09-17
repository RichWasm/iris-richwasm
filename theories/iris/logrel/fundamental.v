From RichWasm Require Import syntax typing.
From RichWasm.compiler Require Import codegen instrs modules util.
From RichWasm.iris Require Import autowp gc.
From RichWasm.iris.logrel Require Import relations.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Fundamental.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!RichWasmGCG Σ}.

  Variable sr : store_runtime.
  Variable mr : module_runtime.

  Lemma compat_nop M F L wl wl' es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := ArrowT [] [] in
    run_codegen (compile_instr me fe (INop ψ)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_unreachable M F L L' wl wl' τs1 τs2 es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := ArrowT τs1 τs2 in
    run_codegen (compile_instr me fe (IUnreachable ψ)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_copy M F L wl wl' τ es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    has_copyability F τ ExCopy ->
    let ψ := ArrowT [τ] [τ; τ] in
    run_codegen (compile_instr me fe (ICopy ψ)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_drop M F L wl wl' τ es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    has_dropability F τ ExDrop ->
    let ψ := ArrowT [τ] [] in
    run_codegen (compile_instr me fe (IDrop ψ)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_num M F L wl wl' ψ eₙ es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    num_instr_has_type eₙ ψ ->
    run_codegen (compile_instr me fe (INum ψ eₙ)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_num_const M F L wl wl' n ν κ es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    has_kind F (NumT κ ν) κ ->
    let ψ := ArrowT [] [NumT κ ν] in
    run_codegen (compile_instr me fe (INumConst ψ n)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_block M F L wl wl' ξ τs1 τs2 es es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let L' := update_locals ξ L in
    let F' := RecordSet.set fc_labels (cons (τs2, L')) F in
    let ψ := ArrowT τs1 τs2 in
    instrs_have_type M F' L es ψ L' ->
    (forall wl wl' es',
        let fe' := fe_of_context F' in
        run_codegen (compile_instrs me fe' es) wl = inr ((), wl', es') ->
        ⊢ has_type_semantic sr M F' L wl' (to_e_list es') ψ L') ->
    run_codegen (compile_instr me fe (IBlock ψ ξ es)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_loop M F L wl wl' es es' τs1 τs2 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let F' := RecordSet.set fc_labels (cons (τs1, L)) F in
    let ψ := ArrowT τs1 τs2 in
    instrs_have_type M F' L es ψ L ->
    (forall wl wl' es',
        let fe' := fe_of_context F' in
        run_codegen (compile_instrs me fe' es) wl = inr ((), wl', es') ->
        ⊢ has_type_semantic sr M F' L wl' (to_e_list es') ψ L) ->
    run_codegen (compile_instr me fe (ILoop ψ es)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ite M F L wl wl' es1 es2 es' ξ ψ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let L' := update_locals ξ L in
    instrs_have_type M F L es1 ψ L' ->
    instrs_have_type M F L es2 ψ L' ->
    (forall wl wl' es',
        run_codegen (compile_instrs me fe es1) wl = inr ((), wl', es') ->
        ⊢ has_type_semantic sr M F L wl' (to_e_list es') ψ L') ->
    (forall wl wl' es',
        run_codegen (compile_instrs me fe es2) wl = inr ((), wl', es') ->
        ⊢ has_type_semantic sr M F L wl' (to_e_list es') ψ L') ->
    run_codegen (compile_instr me fe (IIte ψ ξ es1 es2)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_br M F L wl wl' es' n τs1 τs τs2 ξ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    fc_labels F !! n = Some (τs, L) ->
    Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
    let ψ := ArrowT (τs1 ++ τs) τs2 in
    let L' := update_locals ξ L in
    run_codegen (compile_instr me fe (IBr ψ n)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_br_if M F L wl wl' es' n τs κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    fc_labels F !! n = Some (τs, L) ->
    let τ := NumT κ (IntT I32T) in
    has_kind F τ κ ->
    let ψ := ArrowT (τs ++ [τ]) τs in
    run_codegen (compile_instr me fe (IBrIf ψ n)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_br_table M F L L' wl wl' es' n ns τs τs1 τs2 κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    Forall (fun i => fc_labels F !! i = Some (τs, L)) (n :: ns) ->
    Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
    let τ := NumT κ (IntT I32T) in
    has_kind F τ κ ->
    let ψ := ArrowT (τs1 ++ τs ++ [τ]) τs2 in
    run_codegen (compile_instr me fe (IBrTable ψ ns n)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_return M F L L' wl wl' es' τs τs1 τs2 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    fc_return_type F = τs ->
    Forall (fun τ => has_dropability F τ ImDrop) τs1 ->
    let ψ := ArrowT (τs1 ++ τs) τs2 in
    run_codegen (compile_instr me fe (IReturn ψ)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_local_get M F L wl wl' es' n τ ρ κ κ0 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    L !! n = Some τ ->
    has_rep F τ ρ ->
    let τ' := RepT κ ρ (ProdT κ0 []) in
    has_kind F τ' κ ->
    let L' := <[n := τ']> L in
    let ψ := ArrowT [] [τ] in
    run_codegen (compile_instr me fe (ILocalGet ψ n)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_local_get_copy M F L wl wl' es' n τ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    L !! n = Some τ ->
    has_copyability F τ ImCopy ->
    let ψ := ArrowT [] [τ] in
    run_codegen (compile_instr me fe (ILocalGet ψ n)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_local_set M F L wl wl' es' n τ τ' ρ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    L !! n = Some τ ->
    has_dropability F τ ImDrop ->
    has_rep F τ ρ ->
    has_rep F τ' ρ ->
    let L' := <[n := τ']> L in
    let ψ := ArrowT [τ'] [] in
    run_codegen (compile_instr me fe (ILocalSet ψ n)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_global_get M F L wl wl' es' n m τ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    mc_globals M !! n = Some (m, τ) ->
    has_copyability F τ ImCopy ->
    let ψ := ArrowT [] [τ] in
    run_codegen (compile_instr me fe (IGlobalGet ψ n)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_global_set M F L wl wl' es' n τ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    mc_globals M !! n = Some (Mut, τ) ->
    has_dropability F τ ImDrop ->
    let ψ := ArrowT [τ] [] in
    run_codegen (compile_instr me fe (IGlobalSet ψ n)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_global_swap M F L wl wl' es' n τ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    mc_globals M !! n = Some (Mut, τ) ->
    let ψ := ArrowT [τ] [τ] in
    run_codegen (compile_instr me fe (IGlobalSwap ψ n)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_coderef M F L wl wl' es' i ϕ κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    mc_table M !! i = Some ϕ ->
    let τ := CodeRefT κ ϕ in
    has_kind F τ κ ->
    let ψ := ArrowT [] [τ] in
    run_codegen (compile_instr me fe (ICodeRef ψ i)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_inst M F L wl wl' es' ix ϕ ϕ' κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    inst_function_type F ix ϕ ϕ' ->
    let ψ := ArrowT [CodeRefT κ ϕ] [CodeRefT κ ϕ'] in
    run_codegen (compile_instr me fe (IInst ψ ix)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_call M F L wl wl' es' i ixs ϕ τs1 τs2 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    mc_table M !! i = Some ϕ ->
    let ψ := ArrowT τs1 τs2 in
    list_inst_function_type F ixs ϕ (FunT ψ) ->
    run_codegen (compile_instr me fe (ICall ψ i ixs)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_call_indirect M F L wl wl' es' τs1 τs2 κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let ψ := ArrowT (τs1 ++ [CodeRefT κ (FunT (ArrowT τs1 τs2))]) τs2 in
    run_codegen (compile_instr me fe (ICallIndirect ψ)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_inject M F L wl wl' es' i τs τ κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    τs !! i = Some τ ->
    let ψ := ArrowT [τ] [SumT κ τs] in
    run_codegen (compile_instr me fe (IInject ψ i)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_case M F L wl wl' es' ξ ess τ' τs κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let L' := update_locals ξ L in
    Forall2 (fun τ es => instrs_have_type M F L es (ArrowT [τ] [τ']) L') τs ess ->
    let ψ := ArrowT [SumT κ τs] [τ'] in
    run_codegen (compile_instr me fe (ICase ψ ξ ess)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_group M F L wl wl' es' τs ρs χ δ κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    Forall2 (fun τ ρ => has_kind F τ (VALTYPE ρ χ δ)) τs ρs ->
    let τ := ProdT κ τs in
    has_kind F τ κ ->
    let ψ := ArrowT τs [τ] in
    run_codegen (compile_instr me fe (IGroup ψ)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ungroup M F L wl wl' es' τs ρ χ δ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let κ := VALTYPE ρ χ δ in
    let τ := ProdT κ τs in
    has_kind F τ κ ->
    let ψ := ArrowT [τ] τs in
    run_codegen (compile_instr me fe (IUngroup ψ)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_fold M F L wl wl' es' τ κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    has_kind F τ κ ->
    let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
    let ψ := ArrowT [τ0] [RecT κ τ] in
    run_codegen (compile_instr me fe (IFold ψ)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_unfold M F L wl wl' es' τ κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let τ0 := subst_type VarM VarR VarS (unscoped.scons (RecT κ τ) VarT) τ in
    let ψ := ArrowT [RecT κ τ] [τ0] in
    run_codegen (compile_instr me fe (IUnfold ψ)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_pack M F L wl wl' es' τ τ' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    pack_existential_type F τ τ' ->
    let ψ := ArrowT [τ] [τ'] in
    run_codegen (compile_instr me fe (IPack ψ)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_unpack_mem M F L wl wl' es es' ξ τ τs1 τs2 κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let F' := RecordSet.set fc_mem_vars S (subst_function_ctx (up_memory VarM) VarR VarS VarT F) in
    let L' := update_locals ξ L in
    let weak := map (subst_type (up_memory VarM) VarR VarS VarT) in
    instrs_have_type M F' (weak L) es (ArrowT (weak τs1 ++ [τ]) (weak τs2)) (weak L') ->
    let ψ := ArrowT (τs1 ++ [ExMemT κ τ]) τs2 in
    (forall wl wl' es',
        let fe' := fe_of_context F' in
        run_codegen (compile_instrs me fe' es) wl = inr ((), wl', es') ->
        ⊢ has_type_semantic sr M F' (weak L) wl'
          (to_e_list es')
          (ArrowT (weak τs1 ++ [τ]) (weak τs2)) (weak L')) ->
    run_codegen (compile_instr me fe (IUnpack ψ ξ es)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_unpack_rep M F L wl wl' es es' ξ τ τs1 τs2 κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let F' := RecordSet.set fc_rep_vars S (subst_function_ctx VarM (up_representation VarR) VarS VarT F) in
    let L' := update_locals ξ L in
    let weak := map (subst_type VarM (up_representation VarR) VarS VarT) in
    instrs_have_type M F' (weak L) es (ArrowT (weak τs1 ++ [τ]) (weak τs2)) (weak L') ->
    let ψ := ArrowT (τs1 ++ [ExRepT κ τ]) τs2 in
    (forall wl wl' es',
        let fe' := fe_of_context F' in
        run_codegen (compile_instrs me fe' es) wl = inr ((), wl', es') ->
        ⊢ has_type_semantic sr M F' (weak L) wl'
          (to_e_list es')
          (ArrowT (weak τs1 ++ [τ]) (weak τs2)) (weak L')) ->
    run_codegen (compile_instr me fe (IUnpack ψ ξ es)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_unpack_size M F L wl wl' es es' ξ τ τs1 τs2 κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let F' := RecordSet.set fc_size_vars S (subst_function_ctx VarM VarR (up_size VarS) VarT F) in
    let L' := update_locals ξ L in
    let weak := map (subst_type VarM VarR (up_size VarS) VarT) : list type → list type in
    instrs_have_type M F' (weak L) es (ArrowT (weak τs1 ++ [τ]) (weak τs2)) (weak L') ->
    let ψ := ArrowT (τs1 ++ [ExRepT κ τ]) τs2 in
    (forall wl wl' es',
        let fe' := fe_of_context F' in
        run_codegen (compile_instrs me fe' es) wl = inr ((), wl', es') ->
        ⊢ has_type_semantic sr M F' (weak L) wl'
          (to_e_list es')
          (ArrowT (weak τs1 ++ [τ]) (weak τs2)) (weak L')) ->
    run_codegen (compile_instr me fe (IUnpack ψ ξ es)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_unpack_type M F L wl wl' es es' ξ τ τs1 τs2 κ κ0 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    let F' :=
      RecordSet.set fc_type_vars (cons κ0) (subst_function_ctx VarM VarR VarS (up_type VarT) F)
    in
    let L' := update_locals ξ L in
    let weak := map (subst_type VarM VarR VarS (up_type VarT)) in
    instrs_have_type M F' (weak L) es (ArrowT (weak τs1 ++ [τ]) (weak τs2)) (weak L') ->
    let ψ := ArrowT (τs1 ++ [ExTypeT κ κ0 τ]) τs2 in
    (forall wl wl' es',
        let fe' := fe_of_context F' in
        run_codegen (compile_instrs me fe' es) wl = inr ((), wl', es') ->
        ⊢ has_type_semantic sr M F' (weak L) wl'
          (to_e_list es')
          (ArrowT (weak τs1 ++ [τ]) (weak τs2)) (weak L')) ->
    run_codegen (compile_instr me fe (IUnpack ψ ξ es)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L'.
  Admitted.

  Lemma compat_wrap M F L wl wl' es' τ0 ρ0 ρ ιs0 ιs κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    mono_rep ρ0 ιs0 ->
    mono_rep ρ ιs ->
    convertible_to ιs0 ιs ->
    let τ := RepT κ ρ τ0 in
    has_kind F τ κ ->
    let ψ := ArrowT [τ0] [τ] in
    run_codegen (compile_instr me fe (IWrap ψ)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_unwrap M F L wl wl' es' τ0 ρ0 ρ ιs0 ιs κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    mono_rep ρ0 ιs0 ->
    mono_rep ρ ιs ->
    convertible_to ιs0 ιs ->
    let τ := RepT κ ρ τ0 in
    has_kind F τ κ ->
    let ψ := ArrowT [τ] [τ0] in
    run_codegen (compile_instr me fe (IUnwrap ψ)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ref_new M F L wl wl' es' μ τ0 τ0' κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    mono_mem μ ->
    stores_as F τ0 τ0' ->
    let τ := RefT κ μ τ0' in
    has_kind F τ κ ->
    let ψ := ArrowT [τ0] [τ] in
    run_codegen (compile_instr me fe (IRefNew ψ)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ref_load M F L wl wl' es' μ π τ0 τ0' τs__off ρ δ ιs κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    path_to π τ0 τs__off τ0' ->
    Forall (mono_sized F) τs__off ->
    has_kind F τ0' (VALTYPE ρ ImCopy δ) ->
    mono_rep ρ ιs ->
    let τ := RefT κ μ τ0 in
    has_kind F τ κ ->
    let ψ := ArrowT [τ] [τ; τ0'] in
    run_codegen (compile_instr me fe (IRefLoad ψ π)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ref_store M F L wl wl' es' μ π τ0 τs τ__π τᵥ κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    path_to π τ0 τs τ__π ->
    stores_as F τᵥ τ__π ->
    has_dropability F τ__π ImDrop ->
    let τ := RefT κ μ τ0 in
    has_kind F τ κ ->
    let ψ := ArrowT [τ; τᵥ] [τ] in
    run_codegen (compile_instr me fe (IRefStore ψ π)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ref_mm_store M F L wl wl' es' π τᵥ τᵥ' τₘ τₘ' τ0 τ0' σ n δ κ κ' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    stores_as F τᵥ τₘ' ->
    update_at π τ0 τₘ τ0' τₘ' ->
    has_kind F τₘ (MEMTYPE (Sized σ) (ConstM MemMM) ImDrop) ->
    has_kind F τₘ' (MEMTYPE (Sized σ) (ConstM MemMM) δ) ->
    mono_size σ n ->
    let τ := RefT κ (ConstM MemMM) τ0 in
    let τ' := RefT κ' (ConstM MemMM) τ0' in
    has_kind F τ κ ->
    has_kind F τ' κ' ->
    let ψ := ArrowT [τ; τᵥ'] [τ'] in
    run_codegen (compile_instr me fe (IRefStore ψ π)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ref_swap M F L wl wl' es' μ π τ0 τs__prefix τₘ τᵥ ρ ιs κ :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    mono_rep ρ ιs ->
    path_to π τ0 τs__prefix τₘ ->
    loads_as F τᵥ τₘ ->
    Forall (mono_sized F) τs__prefix ->
    let τ := RefT κ μ τ0 in
    has_kind F τ κ ->
    let ψ := ArrowT [τ; τᵥ] [τ; τᵥ] in
    run_codegen (compile_instr me fe (IRefSwap ψ π)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_ref_mm_swap M F L wl wl' es' π τ0 τ0' τs__prefix τₘ τₘ' τᵥ τᵥ' ρ ιs κ κ' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    mono_rep ρ ιs ->
    path_to π τ0 τs__prefix τₘ ->
    loads_as F τᵥ τₘ ->
    stores_as F τᵥ' τₘ' ->
    update_at π τ0 τₘ τ0' τₘ' ->
    Forall (mono_sized F) τs__prefix ->
    let τ := RefT κ (ConstM MemMM) τ0 in
    let τ' := RefT κ' (ConstM MemMM) τ0' in
    has_kind F τ κ ->
    has_kind F τ' κ' ->
    let ψ := ArrowT [τ; τᵥ'] [τ'; τᵥ] in
    run_codegen (compile_instr me fe (IRefSwap ψ π)) wl = inr ((), wl', es') ->
    ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L.
  Admitted.

  Lemma compat_nil M F L wl wl' es' :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    run_codegen (compile_instrs me fe []) es' = inr ((), wl, wl') ->
    ⊢ has_type_semantic sr M F L wl (to_e_list wl') (ArrowT [] []) L.
  Admitted.

  Lemma compat_cons M F L1 L2 L3 wl wl' es' e es τs1 τs2 τs3 :
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    instr_has_type M F L1 e (ArrowT τs1 τs2) L2 ->
    instrs_have_type M F L2 es (ArrowT τs2 τs3) L3 ->
    (forall es' wl wl',
        run_codegen (compile_instr me fe e) wl = inr ((), wl', es') ->
        ⊢ has_type_semantic sr M F L1 [] (to_e_list es') (ArrowT τs1 τs2) L2) ->
    (forall wl wl' es',
        run_codegen (compile_instrs me fe es) wl = inr ((), wl', es') ->
        ⊢ has_type_semantic sr M F L2 wl' (to_e_list es') (ArrowT τs2 τs3) L3) ->
    run_codegen (compile_instrs me fe (e :: es)) es' = inr ((), wl, wl') ->
    ⊢ has_type_semantic sr M F L1 wl (to_e_list wl') (ArrowT τs1 τs3) L3.
  Admitted.

  Theorem fundamental_theorem M F L L' wl wl' es es' tf :
    instrs_have_type M F L es tf L' ->
    let me := me_of_context M mr in
    let fe := fe_of_context F in
    run_codegen (compile_instrs me fe es) wl = inr (tt, wl', es') ->
    ⊢ has_type_semantic sr M F L wl' (to_e_list es') tf L'.
  Proof.
    intros Htype.
    generalize dependent es'.
    generalize dependent wl'.
    generalize dependent wl.
    induction Htype using instrs_have_type_mind with
      (P := fun M F L e ψ L' _ =>
              forall es' wl wl',
                let me := me_of_context M mr in
                let fe := fe_of_context F in
                run_codegen (compile_instr me fe e) wl = inr (tt, wl', es') ->
                ⊢ has_type_semantic sr M F L [] (to_e_list es') ψ L');
      intros me fe es' wl wl' Hcomp.
    - eapply compat_nop; eassumption.
    - eapply compat_unreachable; eassumption.
    - eapply compat_copy; eassumption.
    - eapply compat_drop; eassumption.
    - eapply compat_num; eassumption.
    - eapply compat_num_const; eassumption.
    - eapply compat_block; eassumption.
    - eapply compat_loop; eassumption.
    - eapply compat_ite.
      1: exact Htype1.
      all: eassumption.
    - eapply compat_br; eassumption.
    - eapply compat_br_if; eassumption.
    - eapply compat_br_table; eassumption.
    - eapply compat_return; eassumption.
    - eapply compat_local_get; eassumption.
    - eapply compat_local_get_copy; eassumption.
    - eapply compat_local_set; eassumption.
    - eapply compat_global_get; eassumption.
    - eapply compat_global_set; eassumption.
    - eapply compat_global_swap; eassumption.
    - eapply compat_coderef; eassumption.
    - eapply compat_inst; eassumption.
    - eapply compat_call; eassumption.
    - eapply compat_call_indirect; eassumption.
    - eapply compat_inject; eassumption.
    - eapply compat_case; eassumption.
    - eapply compat_group; eassumption.
    - eapply compat_ungroup; eassumption.
    - eapply compat_fold; eassumption.
    - eapply compat_unfold; eassumption.
    - eapply compat_pack; eassumption.
    - eapply compat_unpack_mem; eassumption.
    - eapply compat_unpack_rep; eassumption.
    - eapply compat_unpack_size; eassumption.
    - eapply compat_unpack_type; eassumption.
    - eapply compat_wrap.
      1: exact m.
      all: eassumption.
    - eapply compat_unwrap.
      1: exact m.
      all: eassumption.
    - eapply compat_ref_new; eassumption.
    - eapply compat_ref_load; eassumption.
    - eapply compat_ref_store; eassumption.
    - eapply compat_ref_mm_store; eassumption.
    - eapply compat_ref_swap; eassumption.
    - eapply compat_ref_mm_swap; eassumption.
    - eapply compat_nil; eassumption.
    - eapply compat_cons; eassumption.
  Qed.

End Fundamental.
