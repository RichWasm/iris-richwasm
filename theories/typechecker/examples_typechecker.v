Require Import RecordUpdate.RecordUpdate.
From stdpp Require Import base list.
From Stdlib.Strings Require Import String.

From RichWasm Require Import layout syntax typing util.
From RichWasm Require Import typechecker.
Set Bullet Behavior "Strict Subproofs".


Definition ll_1_plus_2 := {|
  m_imports := [];
  m_functions := [{|
    mf_type := (MonoFunT [] [(NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))]);
    mf_locals := [];
    mf_body := [
      (INumConst (InstrT [] [(NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))]) 1);
      (INumConst (InstrT [] [(NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))]) 2);
      (INum
        (InstrT
          [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T));
            (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))]
          [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))])
        (IInt2 I32T AddI))
    ];
  |}];
  m_table := [];
  m_exports := [{| me_name := "test"%string; me_desc := 0 |}];
|}.

Compute (has_module_type_checker_with_synth ll_1_plus_2).
(* ==> inl () : type_checker_res *)

Definition ll_1_plus_2_bad := {|
  m_imports := [];
  m_functions := [{|
    mf_type := (MonoFunT [] [(NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))]);
    mf_locals := [];
    mf_body := [
      (INumConst (InstrT [] [(NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))]) 1);
      (INumConst (InstrT [] [(NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I64T))]) 2);
      (INum
        (InstrT
          [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T));
            (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))]
          [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))])
        (IInt2 I32T AddI))
    ];
  |}];
  m_table := [];
  m_exports := [{| me_name := "test"%string; me_desc := 0 |}];
|}.



Compute (has_module_type_checker_with_synth ll_1_plus_2_bad).
(* ==> inr "function types don't equal" : type_checker_res *)
(* which I recognize isn't insanely helpful *)


Definition m := {|
  m_imports := [];
  m_functions :=
    [ {|
      mf_type :=
        (MonoFunT [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))] []);
      mf_locals := [ (AtomR F32R)];
      mf_body :=
        [ (ILocalGet (InstrT [] [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))])
          0);
          (INum
            (InstrT [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))]
              [ (NumT (VALTYPE (AtomR F32R) NoRefs) (FloatT F32T))])
            (ICvt (CReinterpret (IntT I32T))));
          (ILocalSet
            (InstrT [ (NumT (VALTYPE (AtomR F32R) NoRefs) (FloatT F32T))] []) 1)];
    |}];
  m_table := [];
  m_exports := [ {|
                 me_name := "_start"; me_desc := 0;
               |}];
|}.


Compute (has_module_type_checker_with_synth m).


Definition my_unpack :=
  {|
  m_imports := [];
  m_functions :=
    [ {|
      mf_type := (MonoFunT [] []);
      mf_locals := [];
      mf_body :=
        [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))])
          5);
          (IPack
            (InstrT [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))]
              [ (ExistsTypeT (VALTYPE (AtomR I32R) NoRefs)
                (VALTYPE (AtomR I32R) NoRefs) (VarT 0))]));
          (IUnpack
            (InstrT
              [ (ExistsTypeT (VALTYPE (AtomR I32R) NoRefs)
                (VALTYPE (AtomR I32R) NoRefs) (VarT 0))]
              [])
             []
             [ (IDrop (InstrT [ (VarT 0)] []))])];
    |}];
  m_table := [];
  m_exports := [ {|
                 me_name := "_start"; me_desc := 0;
               |}];
  |}.

Compute (has_module_type_checker_with_synth my_unpack).


Definition my_unpack3 := {|
  m_imports := [];
  m_functions :=
    [ {|
      mf_type := (MonoFunT [] []);
      mf_locals := [ (AtomR I32R)];
      mf_body :=
        [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))])
          5);
          (IPack
            (InstrT [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))]
              [ (ExistsTypeT (VALTYPE (AtomR I32R) NoRefs)
                (VALTYPE (AtomR I32R) NoRefs) (VarT 0))]));
          (ILocalSet
            (InstrT
              [ (ExistsTypeT (VALTYPE (AtomR I32R) NoRefs)
                (VALTYPE (AtomR I32R) NoRefs) (VarT 0))]
              [])
            0);
          (INumConst
            (InstrT [] [ (NumT (VALTYPE (AtomR F32R) NoRefs) (FloatT F32T))]) 7);
          (IPack
            (InstrT [ (NumT (VALTYPE (AtomR F32R) NoRefs) (FloatT F32T))]
              [ (ExistsTypeT (VALTYPE (AtomR F32R) NoRefs)
                (VALTYPE (AtomR F32R) NoRefs) (VarT 0))]));
          (IUnpack
            (InstrT
              [ (ExistsTypeT (VALTYPE (AtomR F32R) NoRefs)
                (VALTYPE (AtomR F32R) NoRefs) (VarT 0))]
              [])
            [
            (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) NoRefs)
              (ProdR [ (AtomR I32R)]))]
            [ (ILocalGet
              (InstrT []
                [ (ExistsTypeT (VALTYPE (AtomR I32R) NoRefs)
                  (VALTYPE (AtomR I32R) NoRefs) (VarT 0))])
              0);
              (IUnpack
                (InstrT
                  [ (VarT 0);
                    (ExistsTypeT (VALTYPE (AtomR I32R) NoRefs)
                      (VALTYPE (AtomR I32R) NoRefs) (VarT 0))]
                  [])
                [
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) NoRefs)
                  (ProdR [ (AtomR I32R)]))]
                [ (IDrop (InstrT [ (VarT 0)] [])); (IDrop (InstrT [ (VarT 1)] []))])])];
    |}];
  m_table := [];
  m_exports := [ {|
                 me_name := "_start"; me_desc := 0;
               |}];
|}.

Definition ϕs := my_unpack3.(m_imports) ++ map mf_type my_unpack3.(m_functions).
Definition M := Build_module_ctx ϕs [].
Definition mf := {|
      mf_type := (MonoFunT [] []);
      mf_locals := [ (AtomR I32R)];
      mf_body :=
        [ (INumConst (InstrT [] [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))])
          5);
          (IPack
            (InstrT [ (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T))]
              [ (ExistsTypeT (VALTYPE (AtomR I32R) NoRefs)
                (VALTYPE (AtomR I32R) NoRefs) (VarT 0))]));
          (ILocalSet
            (InstrT
              [ (ExistsTypeT (VALTYPE (AtomR I32R) NoRefs)
                (VALTYPE (AtomR I32R) NoRefs) (VarT 0))]
              [])
            0);
          (INumConst
            (InstrT [] [ (NumT (VALTYPE (AtomR F32R) NoRefs) (FloatT F32T))]) 7);
          (IPack
            (InstrT [ (NumT (VALTYPE (AtomR F32R) NoRefs) (FloatT F32T))]
              [ (ExistsTypeT (VALTYPE (AtomR F32R) NoRefs)
                (VALTYPE (AtomR F32R) NoRefs) (VarT 0))]));
          (IUnpack
            (InstrT
              [ (ExistsTypeT (VALTYPE (AtomR F32R) NoRefs)
                (VALTYPE (AtomR F32R) NoRefs) (VarT 0))]
              [])
            [
            (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) NoRefs)
              (ProdR [ (AtomR I32R)]))]
            [ (ILocalGet
              (InstrT []
                [ (ExistsTypeT (VALTYPE (AtomR I32R) NoRefs)
                  (VALTYPE (AtomR I32R) NoRefs) (VarT 0))])
              0);
              (IUnpack
                (InstrT
                  [ (VarT 0);
                    (ExistsTypeT (VALTYPE (AtomR I32R) NoRefs)
                      (VALTYPE (AtomR I32R) NoRefs) (VarT 0))]
                  [])
                [
                (PlugT (VALTYPE (ProdR [ (AtomR I32R)]) NoRefs)
                  (ProdR [ (AtomR I32R)]))]
                [ (IDrop (InstrT [ (VarT 0)] [])); (IDrop (InstrT [ (VarT 1)] []))])])];
    |}.

Compute (has_function_type_checker M mf mf.(mf_type)).
Definition ϕ := flatten_function_type mf.(mf_type).
Definition K := kc_of_fft ϕ.
Definition ηss_L := [[I32P]].
Definition F := Build_function_ctx ϕ.(fft_out) [] ηss_L [] K ϕ.(fft_type_vars).
Definition L := ϕ.(fft_in) ++ map type_plug_prim ηss_L.
Compute L.
Compute synth_possible_resulting_local_ctx_insts F mf.(mf_body) L.

Compute (has_module_type_checker_with_synth my_unpack3).
Notation "🐠" := list_elem_of_singleton.

Goal has_module_type my_unpack3 {| mt_imports := []; mt_exports := [MonoFunT [] []] |}.
Proof.
  econstructor.
  - by instantiate (1 := []).
  - done.
  - apply Forall_forall.
    intros mf Hmf.
    cbn in Hmf.
    apply 🐠 in Hmf.
    subst mf.
    econstructor.
    + done.
    + cbn. instantiate (1:= []). instantiate (1:= []). by apply Forall2_nil.
    + done.
    + instantiate (1 := [PlugT (VALTYPE (ProdR [AtomR I32R]) NoRefs) (ProdR [AtomR I32R])]).
      auto. cbn. apply Forall_singleton. econstructor. econstructor. constructor. apply Forall_singleton.
      constructor.
    + cbn.
      change ([?x;?y;?z;?w;?a;?b]) with ([x] ++ [y] ++ [z] ++ [w] ++ [a] ++ [b]).
      eapply TApp; [| eapply TApp; [|eapply TApp; [|eapply TApp;[|eapply TApp]]]].
      * (* NumConst instruction *)
        apply TSingleton.
        change (NumT (VALTYPE (AtomR I32R) NoRefs) (IntT I32T)) with (num_type_type (IntT I32T)).
        eapply TNumConst; repeat econstructor.
      * (* Pack instruction *)
        apply TSingleton.
        apply TPack.
        -- (* prove that it's a packed existential *)
           change (num_type_type (IntT I32T)) with (* aka manually give the witness *)
                  (subst_type VarM VarR VarS (unscoped.scons (num_type_type (IntT I32T)) VarT) (VarT 0)).
           (* If you're following along at home, note that
              - τ = (num_type_type (IntT I32T))
              - τ0 "=" subst τ into τ'
              - τ' = (VarT 0) *)
           apply PackType. (* need: τ and τ' have ok kinds *)
           ++ econstructor. (* easy *)
           ++ apply KVar.
              ** by cbn.
              ** repeat econstructor.
        -- (* prove that the instruction type is ok *)
           apply OKHasInstructionType.
           ++ (* mono rep *)
              constructor; apply Forall_singleton.
              ** econstructor.
                 --- econstructor. constructor.
                 --- constructor.
              ** econstructor.
                 --- econstructor. constructor; [repeat constructor | repeat constructor |].
                     apply KVar; [by cbn|].
                     repeat constructor.
                 --- constructor.

           ++ constructor; [|by apply Forall2_nil].
              econstructor; split; [econstructor; constructor|auto].
              constructor. cbn. apply Forall_singleton.
              constructor.
      * (* local set *)
        apply TSingleton.
        eapply TLocalSet.
        -- cbn. auto.
        -- econstructor. econstructor. econstructor.
           cbn. apply Forall_singleton; constructor.
        -- constructor.
           constructor; apply Forall_singleton.
              ** econstructor.
                 --- econstructor. constructor; [repeat constructor|repeat constructor |].
                     apply KVar;[by cbn|].
                     repeat constructor.
                 --- constructor.
              ** apply Forall_singleton. by apply Forall_nil.
              ** constructor; [|by apply Forall2_nil].
                 econstructor; split.
                 ++ econstructor. constructor; constructor; constructor.
                    constructor.
                 ++ cbn. auto.
      * (* NumConst instruction *)
        apply TSingleton.
        change (NumT (VALTYPE (AtomR F32R) NoRefs) (FloatT F32T)) with (num_type_type (FloatT F32T)).
        eapply TNumConst. constructor.
        ++ constructor; [by apply Forall_nil|apply Forall_singleton; econstructor;
                                             [econstructor;constructor| constructor]].
        ++ constructor; [|by apply Forall2_nil].
           econstructor; split.
           ** econstructor; econstructor; [repeat constructor|repeat constructor|].
              apply KVar;[by cbn|repeat constructor].
           ** by cbn.
      * (* Pack instruction *)
        apply TSingleton.
        apply TPack.
        -- (* prove that it's a packed existential *)
           change (num_type_type (FloatT F32T)) with (* aka manually give the witness *)
                  (subst_type VarM VarR VarS (unscoped.scons (num_type_type (FloatT F32T)) VarT) (VarT 0)).
           (* If you're following along at home, note that
              - τ = (num_type_type (IntT I32T))
              - τ0 "=" subst τ into τ'
              - τ' = (VarT 0) *)
           apply PackType. (* need: τ and τ' have ok kinds *)
           ++ econstructor. (* easy *)
           ++ apply KVar.
              ** by cbn.
              ** repeat econstructor.
        -- (* prove that the instruction type is ok *)
           apply OKHasInstructionType.
           ++ constructor; apply Forall_singleton.
              ** econstructor; [econstructor; constructor|constructor].
              ** econstructor.
                 --- econstructor. econstructor; [repeat constructor|repeat constructor|].
                     apply KVar; [by cbn|repeat constructor].
                 --- constructor.
           ++ constructor; [|by apply Forall2_nil].
              econstructor; split.
              ** econstructor; econstructor; [repeat constructor|repeat constructor|].
                 apply KVar;[by cbn|repeat constructor].
              ** by cbn.

      * (* unpack :( *)
        apply TSingleton.
        eapply TUnpack.
        -- (* unpacked existential *)
           rewrite <- (app_nil_l [ExistsTypeT (VALTYPE (AtomR F32R) NoRefs) _ _]).
           eapply UnpackType.
        -- (* have instr type on the changed inner blocks *)
           cbn.
           change ([?x;?yu]) with ([x] ++ [yu]).
           eapply TApp.
           ++ apply TFrame.
              1: {
                econstructor.
                - econstructor.
                  apply KVar; [by cbn|repeat constructor].
                - constructor.
              }
              apply TSingleton.
              eapply TLocalGetMove; auto.
              apply OKHasInstructionType.
              ** constructor; [by apply Forall_nil | apply Forall_singleton].
                 econstructor. econstructor.
                 --- constructor; [repeat constructor|repeat constructor|].
                     cbn.
                     apply KVar; [by cbn|repeat constructor].
                 --- constructor.
              ** constructor; [| by apply Forall2_nil].
                 econstructor; split.
                 --- econstructor. econstructor. cbn. constructor. apply Forall_singleton. constructor.
                 --- cbn. auto.
           ++ apply TSingleton.
              eapply TUnpack.
              ** change ([?x;?y]) with ([x]++[y]).
                 eapply UnpackType.
              ** cbn.
                 change ([?x;?yu]) with ([x] ++ [yu]).
                 eapply TApp.
                 --- apply TFrame.
                     1: {
                       econstructor.
                       - econstructor.
                         apply KVar; [by cbn|repeat constructor].
                       - constructor.
                     }
                     apply TSingleton.
                     apply TDrop.
                     constructor.
                     +++ constructor; last (by apply Forall_nil).
                         apply Forall_singleton.
                         econstructor.
                         *** econstructor. constructor.
                             ---- cbn. auto.
                             ---- constructor. constructor.
                         *** constructor.
                     +++ constructor; last by apply Forall2_nil.
                         econstructor; split.
                         *** econstructor.
                             econstructor. constructor. apply Forall_singleton. constructor.
                         *** auto.
                 --- apply TSingleton.
                     apply TDrop.
                     constructor.
                     +++ constructor; last (by apply Forall_nil).
                         apply Forall_singleton.
                         econstructor.
                         *** econstructor. constructor.
                             ---- cbn. auto.
                             ---- constructor. constructor.
                         *** constructor.
                     +++ constructor; last by apply Forall2_nil.
                         econstructor; split.
                         *** econstructor.
                             econstructor. constructor. apply Forall_singleton. constructor.
                         *** auto.

              ** constructor.
                 --- constructor; [|by apply Forall_nil].
                     apply Forall_cons; split; [|apply Forall_singleton].
                     +++ econstructor.
                         *** econstructor.
                             apply KVar.
                             ---- cbn; auto.
                             ---- econstructor. constructor.
                         *** constructor.
                     +++ econstructor.
                         *** econstructor. constructor; [repeat constructor|repeat constructor|].
                             apply KVar; [by cbn|]. constructor. constructor.
                         *** constructor.
                 --- constructor; [ |by apply Forall2_nil ].
                     econstructor; split.
                     +++ econstructor. econstructor. econstructor. apply Forall_singleton. econstructor.
                     +++ cbn; auto.
        -- constructor.
           ++ constructor; [apply Forall_singleton|by apply Forall_nil].
              econstructor; [econstructor; econstructor; [repeat constructor|repeat constructor|]|].
              ** apply KVar; [by cbn|].
                 repeat constructor.
              ** constructor.
           ++ constructor; [|by apply Forall2_nil].
              econstructor; split.
              +++ econstructor. econstructor. econstructor. apply Forall_singleton. econstructor.
              +++ cbn; auto.
Qed.
