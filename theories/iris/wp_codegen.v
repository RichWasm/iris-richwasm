Require Import iris.proofmode.tactics.

From RichWasm Require Import syntax typing.
From RichWasm.compiler Require Import codegen instrs modules util.
From RichWasm.iris Require Import autowp gc.
From RichWasm.iris.logrel Require Import relations.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section CodeGen.

  Context `{!logrel_na_invs Σ}.
  Context `{!wasmG Σ}.
  Context `{!rwasm_gcG Σ}.

  Variable sr : store_runtime.
  Variable me : module_env.
  Variable F : function_ctx.
  Variable L : local_ctx.
  Variable WL : wlocal_ctx.

  Lemma wp_if_c {A B} s E i tf (c1 : codegen A) (c2 : codegen B) wl wl' es x y Φ (f: frame) :
    run_codegen (if_c tf c1 c2) wl = inr (x, y, wl', es) ->
    exists wl1 es1 es2,
    run_codegen c1 wl = inr (x, wl1, es1) /\
    run_codegen c2 wl1 = inr (y, wl', es2) /\
    ⊢ ↪[frame] f -∗
      ↪[RUN] -∗
      ((⌜i <> Wasm_int.int_zero i32m⌝ ∧
        ▷ (↪[frame] f -∗ ↪[RUN] -∗ WP [AI_basic (BI_block tf es1)] @ s; E {{ v, Φ v }})) ∨
       (⌜i = Wasm_int.int_zero i32m⌝ ∧
        ▷ (↪[frame] f -∗ ↪[RUN] -∗ WP [AI_basic (BI_block tf es2)] @ s; E {{ v, Φ v }}))) -∗
      WP to_e_list (BI_const (VAL_int32 i) :: es) @ s; E {{ v, Φ v }}.
  Proof.
    intros Hcomp.
    unfold if_c in Hcomp.

    apply run_codegen_bind_dist in Hcomp.
    destruct Hcomp as (x1 & wl1 & es1 & es2 & Hcomp1 & Hcomp2 & Hes).
    destruct x1 as [x' es1'].
    subst es.
    apply run_codegen_capture in Hcomp1.
    destruct Hcomp1 as [Hcomp1 ->].

    apply run_codegen_bind_dist in Hcomp2.
    destruct Hcomp2 as (x2 & wl2 & es3 & es4 & Hcomp2 & Hcomp3 & Hes).
    destruct x2 as [y' es2'].
    subst es2.

    apply run_codegen_capture in Hcomp2.
    destruct Hcomp2 as [Hcomp2 ->].

    cbn in Hcomp3.
    inversion Hcomp3.
    subst x' y' wl2 es4.
    clear Hcomp3.
    rename es1' into es1, es2' into es2.

    exists wl1, es1, es2.
    split; first assumption.
    split; first assumption.

    iIntros "Hfr Hrun Hbl".
    iSimpl.
    iDestruct "Hbl" as "[[%Hi Hbl] | [%Hi Hbl]]".
    - by iApply (wp_if_true with "[Hfr] [Hrun]"); auto.
     - by iApply (wp_if_false with "[Hfr] [Hrun]"); auto.
  Qed.

  (* Generic monad operations. *)
  Lemma wp_ret {A} (a: A) wl v wl' es :
    run_codegen (Monad.ret a) wl = inr (v, wl', es) ->
    v = a /\ wl' = wl /\ es = [].
  Proof.
    cbn.
    intros Hcg.
    inversion Hcg; subst; done.
  Qed.

  Lemma wp_mapM_nil {A B} (f: A -> codegen (list B)) wl ys wl' es :
    run_codegen (mapM f []) wl = inr (ys, wl', es) ->
    wl' = wl /\
    ys = [] /\
    es = [].
  Proof.
    cbn.
    intros Hcg.
    inversion Hcg.
    done.
  Qed.
  
  Lemma wp_mapM_cons {A B} (f: A -> codegen (list B)) wl yss wl' es x xs :
    run_codegen (mapM f (x :: xs)) wl = inr (yss, wl', es) ->
    ∃ ys_x wl_x es_x yss_xs wl_xs es_xs,
      run_codegen (f x) wl = inr (ys_x, wl_x, es_x) /\
      run_codegen (mapM f xs) wl_x = inr (yss_xs, wl_xs, es_xs) /\
      yss = ys_x :: yss_xs /\
      wl' = wl_xs /\
      es = es_x ++ es_xs.
  Proof.
    cbn.
    intros Hcg.
    inv_cg_bind Hcg res1 wl1 es_fx es2 Hfx Hcg1.
    inv_cg_bind Hcg1 res2 wl2 es_fxs es3 Hfxs Hcg2.
    cbn in Hcg2.
    inversion Hcg2.
    subst.
    repeat eexists; eauto.
    rewrite app_nil_r; eauto.
  Qed.

  (* State monad operations. *) 
  Lemma wp_get wl v wl' es :
    run_codegen MonadState.get wl = inr (v, wl', es) ->
    v = wl /\
    wl' = wl /\
    es = [].
  Proof.
    unfold MonadState.get; cbn.
    intros Heq.
    inversion Heq; subst.
    tauto.
  Qed.

  Lemma wp_put wl v wl' wl'' es :
    run_codegen (MonadState.put wl') wl = inr (v, wl'', es) ->
    v = () /\
    wl'' = wl' /\
    es = [].
  Proof.
    unfold MonadState.put; cbn.
    intros Heq.
    inversion Heq; subst.
    tauto.
  Qed.
  
  (* Allocating locals. *)
  
  (* Monotone interpretation of a wlocal_ctx *)
  Definition interp_wl (wlocal_offset : nat) (wl : wlocal_ctx) (inst: instance) : frame -> Prop :=
    λ fr, ∃ vs vs__wl vs', fr = Build_frame (vs ++ vs__wl ++ vs') inst /\
                         result_type_interp wl vs__wl.

  Lemma wp_wlalloc fe ty wl wl' idx es :
    run_codegen (wlalloc fe ty) wl = inr (idx, wl', es) ->
    idx = Mk_localidx (fe_wlocal_offset fe + length wl) /\
    wl' = wl ++ [ty] /\
    es = [].
  Proof.
    unfold wlalloc.
    intros Hcg.
    inv_cg_bind Hcg res wl1 es_get es2 Hget Hcg1.
    inv_cg_bind Hcg1 res1 wl2 es_put es_ret Hput Hret.
    apply wp_get in Hget.
    apply wp_put in Hput.
    apply wp_ret in Hret.
    destruct Hget as (? & ? & ?).
    destruct Hput as (? & ? & ?).
    destruct Hret as (? & ? & ?).
    subst; done.
  Qed.

  (* Saving and restoring the stack. *)
  Lemma wp_save_stack_w s E Φ inst fe ty wl idx wl' es fr :
    run_codegen (save_stack_w fe ty) wl = inr (idx, wl', es) ->
    interp_wl (fe_wlocal_offset fe) wl' inst fr ->
    ⊢ ↪[frame] fr -∗
      ↪[RUN] -∗
      WP (to_e_list es) @ s; E {{ v, Φ v }}.
  Abort.


End CodeGen.
