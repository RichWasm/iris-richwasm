From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From Wasm.iris.logrel Require Export iris_fundamental.
From Wasm.iris.rules Require Export proofmode.
From RWasm.iris.allocator Require Export allocator_common.
From RWasm.iris.allocator Require Import misc_relocate reprs.
From RWasm.iris.allocator Require Import malloc_impl.

Import reprs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Module M := malloc_impl.
Section malloc.

Context `{!wasmG Σ} `{!allocG Σ}.

Locate "↦[wms][".

(* SPECS: block getters *)
Lemma spec_get_state E memidx blk next_addr blk_addr32 blk_var f :
  ⊢ {{{{ block_repr memidx blk next_addr ∗
         ⌜N_repr (block_addr blk) blk_addr32 ⌝ ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    (to_e_list (get_state blk_var)) @ E
    {{{{ v, ∃ st32, 
              ⌜v = (immV [VAL_int32 st32])⌝ ∗
              ⌜N_repr (state_to_N (block_flag blk)) st32 ⌝ ∗
              block_repr memidx blk next_addr ∗
              ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(Hblk & (%Hbdd & %Haddr) & %Hvar & %Hmem & Hfr) HΦ".
  wp_chomp 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗ ↪[frame] f)%I).
  iSplitR; [iIntros "(%H & ?)"; auto|].
  iSplitL "Hfr".
  - iApply wp_get_local; eauto.
  - iIntros (w) "(%Hw & Hfr)".
    subst w.
    simpl.
    iDestruct "Hblk" as "(Hbounds & (%st32 & (%Hst & Hstate)) & Hsize & Hnext & Hdata)".
    unfold state_off.
    replace memidx with (N.of_nat (N.to_nat memidx)) by lia.
    rewrite Haddr.
    iApply (wp_wand with "[Hstate Hfr]").
    (*
    instantiate (1:=(λ w, 
                       ((⌜w = immV [VAL_int32 st32]⌝ ∗
                         N.of_nat (N.to_nat memidx)↦[wms][Wasm_int.N_of_uint i32m blk_addr32 + 0]bits (VAL_int32 st32)) ∗ ↪[frame]f)%I)).
*)
    + iApply wp_load; try iFrame; eauto.
      fill_imm_pred.
    + iIntros (w) "((%Hw & Hptr) & Hfr)".
      subst w.
      iApply "HΦ".
      unfold block_repr, state_repr.
      rewrite Haddr.
      iExists st32; iFrame; auto.
Qed.

Lemma spec_get_final_state E memidx blk blk_addr blk_addr32 blk_var f :
  ⊢ {{{{ final_block_repr memidx blk blk_addr ∗
         ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    (to_e_list (get_state blk_var)) @ E
    {{{{ v, ∃ st32,
              ⌜v = (immV [VAL_int32 st32])⌝ ∗
              ⌜N_repr (state_to_N (final_block_flag blk)) st32 ⌝ ∗
              final_block_repr memidx blk blk_addr ∗
              ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(Hblk & (%Hbdd & %Haddr) & %Hvar & %Hmem & Hfr) HΦ".
  wp_chomp 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗ ↪[frame] f)%I).
  iSplitR; [iIntros "(%H & ?)"; auto|].
  iSplitL "Hfr".
  - iApply wp_get_local; eauto.
  - iIntros (w) "(%Hw & Hfr)".
    subst w.
    simpl.
    destruct blk.
    iDestruct "Hblk" as "(-> & Hbounds & (%st32 & (%Hst & Hstate)) & Hsize & Hnext & Hdata)".
    unfold state_off.
    replace memidx with (N.of_nat (N.to_nat memidx)) by lia.
    iApply (wp_wand with "[Hstate Hfr]").
    instantiate (1:=(λ w, 
                       ((⌜w = immV [VAL_int32 st32]⌝ ∗
                         N.of_nat (N.to_nat memidx)↦[wms][Wasm_int.N_of_uint i32m blk_addr32 + 0]bits (VAL_int32 st32)) ∗ ↪[frame]f)%I)).
    + subst blk_addr.
      iApply wp_load; auto.
      iFrame.
      by iModIntro.
    + iIntros (w) "((%Hw & Hptr) & Hfr)".
      subst w blk_addr.
      iApply "HΦ".
      unfold block_repr, state_repr.
      iExists st32; iFrame; auto.
Qed.

Lemma spec_get_next E memidx blk next_addr blk_addr32 f blk_var :
  ⊢ {{{{ block_repr memidx blk next_addr ∗
         ⌜N_repr (block_addr blk) blk_addr32 ⌝ ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    (to_e_list (get_next blk_var)) @ E
    {{{{ v, ∃ next_addr32,
              ⌜v = (immV [VAL_int32 next_addr32])⌝ ∗
              ⌜N_repr next_addr next_addr32 ⌝ ∗
              block_repr memidx blk next_addr ∗
              ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(Hblk & (%Hbdd & %Haddr) & %Hvar & %Hmem & Hfr) HΦ".
  wp_chomp 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗ ↪[frame] f)%I).
  iSplitR; [iIntros "(%H & ?)"; auto|].
  iSplitL "Hfr".
  - iApply wp_get_local; eauto.
  - iIntros (w) "(%Hw & Hfr)".
    subst w.
    simpl.
    iDestruct "Hblk" as "(Hbounds & Hstate & Hsize & (%next_addr32 & ((%Hbdd' & %Hnext_addr) & Hnext)) & Hdata)".
    replace memidx with (N.of_nat (N.to_nat memidx)) by lia.
    rewrite Haddr.
    iApply (wp_wand with "[Hnext Hfr]").
    instantiate (1:= λ w, ((⌜w = immV [VAL_int32 next_addr32]⌝ ∗ _) ∗ ↪[frame] f)%I).
    + iApply wp_load; try iFrame; auto.
    + iIntros (w) "((%Hw & Hptr) & Hfr)".
      subst w.
      iApply "HΦ".
      rewrite -Haddr.
      unfold block_repr, next_repr.
      iExists next_addr32; iFrame; auto.
Qed.

Lemma spec_get_final_next E memidx blk blk_addr blk_addr32 f blk_var :
  ⊢ {{{{ final_block_repr memidx blk blk_addr ∗
         ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    (to_e_list (get_next blk_var)) @ E
    {{{{ v, ∃ next_addr32,
            ⌜v = (immV [VAL_int32 next_addr32])⌝ ∗
            ⌜N_repr 0%N next_addr32 ⌝ ∗
            final_block_repr memidx blk blk_addr ∗
            ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(Hblk & (%Hbdd & %Haddr) & %Hvar & %Hmem & Hfr) HΦ".
  destruct blk.
  wp_chomp 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗ ↪[frame] f)%I).
  iSplitR; [iIntros "(%H & ?)"; auto|].
  iSplitL "Hfr".
  - iApply wp_get_local; eauto.
  - iIntros (w) "(%Hw & Hfr)".
    subst w.
    simpl.
    iDestruct "Hblk" as "(-> & Hbounds & Hstate & Hsize & (%next_addr32 & ((%Hbdd' & %Hnext_addr) & Hnext)) & Hdata)".
    replace memidx with (N.of_nat (N.to_nat memidx)) by lia.
    rewrite Haddr.
    iApply (wp_wand with "[Hnext Hfr]").
    instantiate (1:= λ w, ((⌜w = immV [VAL_int32 next_addr32]⌝ ∗ _) ∗ ↪[frame] f)%I).
    + iApply wp_load; try iFrame; auto.
    + iIntros (w) "((%Hw & Hptr) & Hfr)".
      subst w blk_addr.
      iApply "HΦ".
      unfold final_block_repr, next_repr.
      iExists next_addr32.
      iFrame; auto.
Qed.

Lemma spec_get_data E memidx blk blk_addr32 next_addr f blk_var : 
  ⊢ {{{{ ⌜N_repr (block_addr blk) blk_addr32⌝ ∗
         block_repr memidx blk next_addr ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    (to_e_list (get_data blk_var)) @ E
    {{{{ v, block_repr memidx blk next_addr ∗
              ∃ data_addr32,
                ⌜v = (immV [VAL_int32 data_addr32])⌝ ∗
                ⌜N_repr (block_addr blk + data_off) data_addr32⌝ ∗
                ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "((%Hbdd & %Haddr) & Hblk & %Hvar & %Hmem & Hfr) HΦ".
  wp_chomp 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗ ↪[frame] f)%I).
  iSplitR; [iIntros "(%H & ?)"; auto|].
  iSplitL "Hfr".
  - iApply wp_get_local; eauto.
  - iIntros (w) "(%Hw & Hfr)".
    iAssert (block_inbounds (block_size blk) (block_addr blk)) as "%Hbds".
    {
      by iDestruct "Hblk" as "(Hbds & Hblk')".
    } 
    iApply (wp_wand with "[Hfr]").
    instantiate (1 := λ v, (⌜v = immV [VAL_int32 (Wasm_int.Int32.iadd blk_addr32 (Wasm_int.Int32.repr 12))]⌝ ∗ ↪[frame] f)%I).
    + subst; cbn.
      iApply (wp_binop with "[Hfr]"); auto.
    + subst. 
      iIntros (w) "(%Hw & Hfr)".
      iApply "HΦ".
      iFrame.
      subst.
      iExists _; iSplit; auto.
      unfold data_off, blk_hdr_sz in *.
      iPureIntro.
      unfold Wasm_int.Int32.iadd.
      eapply N_repr_i32repr.
      * lia.
      * rewrite Wasm_int.Int32.unsigned_repr_eq.
        change ((12 `mod` Wasm_int.Int32.modulus)%Z) with 12%Z.
        rewrite N2Z.inj_add.
        f_equal.
        cbn in *.
        rewrite Haddr.
        rewrite Z2N.id; auto.
        apply Wasm_int.Int32.unsigned_range.
Qed.

Lemma spec_get_size E memidx blk next_addr blk_addr32 f blk_var : 
  ⊢ {{{{ block_repr memidx blk next_addr ∗
         ⌜N_repr (block_addr blk) blk_addr32⌝ ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    to_e_list (get_size blk_var) @ E
    {{{{ v, ∃ sz32,
              ⌜N_repr (block_size blk) sz32⌝ ∗
              ⌜v = (immV [VAL_int32 sz32])⌝ ∗
              block_repr memidx blk next_addr ∗
              ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(Hblk & (%Hbdd & %Haddr) & %Hvar & %Hmem & Hfr) HΦ".
  wp_chomp 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗ ↪[frame] f)%I).
  iSplitR; [iIntros "(%H & ?)"; auto|].
  iSplitL "Hfr".
  - iApply wp_get_local; eauto.
  - iIntros (w) "(%Hw & Hfr)".
    subst w.
    simpl.
    iDestruct "Hblk" as "(Hbounds & Hstate & (%sz32 & (%Hsz & Hsize)) & Hnext & Hdata)".
    replace memidx with (N.of_nat (N.to_nat memidx)) by lia.
    iApply (wp_wand with "[Hsize Hfr]").
    instantiate (1:=(λ w, 
                       ((⌜w = immV [VAL_int32 sz32]⌝ ∗
                         N.of_nat (N.to_nat memidx)↦[wms][Wasm_int.N_of_uint i32m blk_addr32 + size_off]bits (VAL_int32 sz32)) ∗ ↪[frame]f)%I)).
    + rewrite Haddr.
      iApply wp_load; auto.
      iFrame.
      by iModIntro.
    + iIntros (w) "((%Hw & Hptr) & Hfr)".
      subst w.
      rewrite -Haddr.
      iApply "HΦ".
      unfold block_repr, size_repr.
      iExists sz32; iFrame; auto.
Qed.

Lemma spec_get_final_size E memidx blk_addr blk_addr32 f blk blk_var : 
  ⊢ {{{{ final_block_repr memidx blk blk_addr ∗
         ⌜N_repr blk_addr blk_addr32⌝ ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    to_e_list (get_size blk_var) @ E
    {{{{ v, ∃ sz32,
              ⌜N_repr (final_block_sz blk) sz32⌝ ∗
              ⌜v = (immV [VAL_int32 sz32])⌝ ∗
              final_block_repr memidx blk blk_addr ∗
              ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(Hblk & (%Hbdd & %Haddr) & %Hvar & %Hmem & Hfr) HΦ".
  wp_chomp 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗ ↪[frame] f)%I).
  iSplitR; [iIntros "(%H & ?)"; auto|].
  iSplitL "Hfr".
  - iApply wp_get_local; eauto.
  - iIntros (w) "(%Hw & Hfr)".
    subst w.
    simpl.
    destruct blk.
    iDestruct "Hblk" as "(-> & Hbounds & Hstate & (%sz32 & (%Hsz & Hsize)) & Hdata)".
    replace memidx with (N.of_nat (N.to_nat memidx)) by lia.
    iApply (wp_wand with "[Hsize Hfr]").
    instantiate (1:=(λ w, 
                       ((⌜w = immV [VAL_int32 sz32]⌝ ∗
                         N.of_nat (N.to_nat memidx)↦[wms][Wasm_int.N_of_uint i32m blk_addr32 + size_off]bits (VAL_int32 sz32)) ∗ ↪[frame]f)%I)).
    + subst blk_addr.
      iApply wp_load; auto.
      iFrame.
      by iModIntro.
    + iIntros (w) "((%Hw & Hptr) & Hfr)".
      subst w blk_addr.
      iApply "HΦ".
      iExists sz32.
      by iFrame.
Qed.

(* SPECS: block setters *)
Lemma spec_set_next_basic E memidx blk_addr blk_addr32 next_addr next_addr32 f :
  ⊢ {{{{ ⌜N_repr blk_addr blk_addr32⌝ ∗
         ⌜N_repr next_addr next_addr32⌝ ∗
         own_vec memidx (blk_addr + next_off) 4 ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    to_e_list (BI_const (VAL_int32 blk_addr32) :: BI_const (VAL_int32 next_addr32) :: set_next) @ E
    {{{{ w, ⌜w = immV [] ⌝ ∗
            next_repr memidx next_addr blk_addr ∗
            ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(%Hblk & %Hnext & Hvec & %Hmem & Hfr) HΦ".
  cbn.
  unfold own_vec.
  replace memidx with (N.of_nat (N.to_nat memidx)) by lia.
  rewrite (N_repr_uint _ _ Hblk).
  iApply (wp_wand with "[Hfr Hvec]").
  {
    iDestruct "Hvec" as "(%next32 & %Hlen & Hnext')".
    iApply (wp_store (λ w, (⌜w = immV []⌝)%I)); try iFrame; auto.
    cbn; lia.
  }
  iIntros (v) "((Hv & Hnext) & Hfr)".
  iApply "HΦ".
  iFrame; auto.
Qed.

Lemma spec_set_next E blk memidx blk_addr32 next_addr0 next_addr next_addr32 f :
  ⊢ {{{{ ⌜N_repr (block_addr blk) blk_addr32⌝ ∗
          ⌜N_repr next_addr next_addr32⌝ ∗
          block_repr memidx blk next_addr0 ∗
          ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
          ↪[frame] f }}}}
    to_e_list (BI_const (VAL_int32 blk_addr32) :: BI_const (VAL_int32 next_addr32) :: set_next) @ E
    {{{{ w, ⌜w = immV [] ⌝ ∗
            block_repr memidx blk next_addr ∗
            ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(%Hblk & %Hnext & (Hbdd & Hst & Hsz & Hnext & Hdata) & %Hmem & Hfr) HΦ".
  iDestruct "Hnext" as "(%next32 & %Hrepr & Hvec)".
  iApply (spec_set_next_basic with "[$Hfr Hvec]").
  {
    iSplit; auto.
    iSplit; auto.
    iSplit; auto.
    iExists _.
    iFrame.
    rewrite (length_bits _ T_i32); eauto.
  }
  iIntros (w) "(-> & Hnext & Hfr)".
  unfold block_repr.
  iApply "HΦ"; iFrame; auto.
Qed.

(* need a version of this for
   - final blocks
   - free blocks
*)
Lemma spec_set_size_decr E memidx sz sz' sz32' blk_addr blk_addr32 next_addr f :
  ⊢ {{{{ ⌜N_repr blk_addr blk_addr32⌝ ∗
          ⌜N_repr sz' sz32'⌝ ∗
          ⌜(sz > sz')%N⌝ ∗
          block_repr memidx (FreeBlk blk_addr sz) next_addr ∗
          ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
          ↪[frame] f }}}}
    to_e_list (BI_const (VAL_int32 blk_addr32) :: BI_const (VAL_int32 sz32') :: M.set_size) @ E
    {{{{ w, block_repr memidx (FreeBlk blk_addr sz') next_addr ∗
            own_vec memidx (blk_addr + data_off + sz') (sz - sz') ∗
            ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(%Hblk & %Hsz' & %Hdecr & (Hbdd & Hst & Hsz & Hnext & Hdata) & %Hmem & Hfr) HΦ".
  cbn.
  replace memidx with (N.of_nat (N.to_nat memidx)) by lia.
  destruct Hblk as [Hblkbd Hblk].
  subst blk_addr.
  iApply (wp_wand with "[Hfr Hsz]").
  {
    iDestruct "Hsz" as "(%sz32 & (Hszr & Hsz))".
    iApply (wp_store (λ w, (⌜w = immV []⌝)%I)); try iFrame; auto.
  }
  iIntros (v) "((%Hv & Hsz) & Hfr)".
  cbn.
  iApply "HΦ".
  remember (sz - sz')%N as δ.
  replace sz with (sz' + δ)%N by lia.
  rewrite own_vec_split.
  iDestruct "Hdata" as "(Hdata & Hleft)".
  iFrame; auto.
  unfold block_inbounds.
  cbn.
  iDestruct "Hbdd" as "%Hbdd".
  iPureIntro.
  split; lia || auto.
Qed.

Lemma spec_set_size_final_setup E memidx sz' sz32' blk_addr blk_addr32 f :
  ⊢ {{{{ ⌜N_repr blk_addr blk_addr32⌝ ∗
          ⌜N_repr sz' sz32'⌝ ∗
          own_vec memidx (blk_addr + size_off) 4 ∗
          own_vec memidx (blk_addr + data_off) sz' ∗
          ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
          ↪[frame] f }}}}
    to_e_list (BI_const (VAL_int32 blk_addr32) :: BI_const (VAL_int32 sz32') :: M.set_size) @ E
    {{{{ w, ⌜w = immV [] ⌝ ∗ 
            size_repr memidx sz' blk_addr ∗
            own_vec memidx (blk_addr + data_off) sz' ∗
            ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(%Hblk & %Hsz' & Hszr & Hdata & %Hmem & Hfr) HΦ".
  cbn.
  replace memidx with (N.of_nat (N.to_nat memidx)) by lia.
  destruct Hblk as [Hblkbd Hblk].
  subst blk_addr.
  iApply (wp_wand with "[Hfr Hszr]").
  {
    iDestruct "Hszr" as "(%bs & (%Hbslen & Hsz))".
    iApply (wp_store (λ w, (⌜w = immV []⌝)%I)); try iFrame; auto.
    cbn; lia.
  }
  iIntros (v) "((%Hv & Hsz) & Hfr)".
  cbn.
  iApply "HΦ".
  iFrame; auto.
Qed.

Lemma spec_set_size_final E memidx sz sz' sz32' blk_addr blk_addr32 f :
  ⊢ {{{{ ⌜N_repr blk_addr blk_addr32⌝ ∗
          ⌜N_repr sz' sz32'⌝ ∗
          size_repr memidx sz blk_addr ∗
          own_vec memidx (blk_addr + data_off) sz' ∗
          ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
          ↪[frame] f }}}}
    to_e_list (BI_const (VAL_int32 blk_addr32) :: BI_const (VAL_int32 sz32') :: M.set_size) @ E
    {{{{ w, ⌜w = immV [] ⌝ ∗ 
            size_repr memidx sz' blk_addr ∗
            own_vec memidx (blk_addr + data_off) sz' ∗
            ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(%Hblk & %Hsz' & (%sz32 & %Hszr & Hpts) & Hdata & %Hmem & Hfr) HΦ".
  cbn.
  iApply (spec_set_size_final_setup with "[$Hpts $Hdata $Hfr //]").
  auto.
Qed.

Lemma spec_add_hdr_sz E f base32 base : 
  ⊢ {{{{ ⌜N_repr base base32⌝ ∗
          ⌜(Z.of_N (base+blk_hdr_sz) < Wasm_int.Int32.modulus)%Z⌝ ∗
          ↪[frame] f}}}}
     to_e_list (BI_const (VAL_int32 base32) :: add_hdr_sz) @ E
     {{{{ w, ∃ out32, ⌜w = immV [VAL_int32 out32]⌝ ∗ ⌜N_repr (base + blk_hdr_sz) out32⌝ ∗↪[frame] f}}}}.
Proof.
  iIntros "!>" (Φ) "(%Hbase & %Hbdd & Hfr) HΦ".
  cbn.
  iApply (wp_wand with "[Hfr]").
  instantiate (1:= λ w, ((∃ out32, ⌜w = immV [VAL_int32 out32]⌝ ∗
                                          ⌜N_repr (base + blk_hdr_sz) out32⌝)
                           ∗ ↪[frame] f)%I).
  {
    iApply (wp_binop with "[Hfr]"); auto.
    iModIntro.
    iExists _; iSplit; eauto.
    iPureIntro.
    destruct Hbase as [[Hpos Hbd] Hconv].
    apply N_repr_i32repr.
    - lia.
    - subst.
      cbn in *.
      revert Hbdd.
      replace blk_hdr_sz with (Z.to_N 12%Z) by reflexivity.
      rewrite !Z2N.id in Hpos.
      rewrite <- Z2N.inj_add; lia.
      apply Wasm_int.Int32.size_interval_1.
  }
  iIntros (w) "(Hw & Hfr)".
  iApply "HΦ"; iFrame.
Qed.

Lemma spec_sub_hdr_sz E f base32 base : 
  ⊢ {{{{ ⌜N_repr base base32⌝ ∗
         ⌜(base > blk_hdr_sz)%N⌝ ∗
          ↪[frame] f}}}}
     to_e_list (BI_const (VAL_int32 base32) :: sub_hdr_sz) @ E
     {{{{ w, ∃ out32, ⌜w = immV [VAL_int32 out32]⌝ ∗ ⌜N_repr (base - blk_hdr_sz) out32⌝ ∗↪[frame] f}}}}.
Proof.
  iIntros "!>" (Φ) "(%Hbase & %Hbdd & Hfr) HΦ".
  cbn.
  iApply (wp_wand with "[Hfr]").
  instantiate (1:= λ w, ((∃ out32, ⌜w = immV [VAL_int32 out32]⌝ ∗
                                          ⌜N_repr (base - blk_hdr_sz) out32⌝)
                           ∗ ↪[frame] f)%I).
  {
    iApply (wp_binop with "[Hfr]"); auto.
    iModIntro.
    iExists _; iSplit; eauto.
    iPureIntro.
    destruct Hbase as [[Hpos Hbd] Hconv].
    apply N_repr_i32repr.
    - lia.
    - subst.
      cbn in *.
      revert Hbdd.
      replace blk_hdr_sz with (Z.to_N 12%Z) by reflexivity.
      rewrite !Z2N.id in Hpos.
      rewrite <- Z2N.inj_sub; lia.
      apply Wasm_int.Int32.size_interval_1.
  }
  iIntros (w) "(Hw & Hfr)".
  iApply "HΦ"; iFrame.
Qed.

Lemma block_repr_inbounds memidx blk next_addr :
  block_repr memidx blk next_addr ⊢
  block_repr memidx blk next_addr ∗
  ⌜(Z.of_N (block_addr blk + blk_hdr_sz + block_size blk) < Wasm_int.Int32.modulus)%Z⌝.
Proof.
  iIntros "(%Hbounds & Hblk')".
  iFrame; auto.
Qed.

Lemma spec_get_total_size E memidx blk next_addr blk_addr32 f blk_var : 
  ⊢ {{{{ block_repr memidx blk next_addr ∗
         ⌜N_repr (block_addr blk) blk_addr32⌝ ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    to_e_list (get_total_size blk_var) @ E
    {{{{ v, ∃ sz32,
              ⌜N_repr (block_size blk + blk_hdr_sz) sz32⌝ ∗
              ⌜v = (immV [VAL_int32 sz32])⌝ ∗
              block_repr memidx blk next_addr ∗
              ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(Hblk & %Haddr & %Hvar & %Hmem & Hfr) HΦ".
  unfold get_total_size.
  erewrite to_e_list_cat.
  iApply wp_seq.
  iSplitR.
  all: swap 1 2.
  {
    iSplitR "HΦ".
    iApply (spec_get_size with "[Hblk Hfr]"); iFrame; auto.
    iIntros (w) "(%sz32 & %Hsz & %Hw & Hblk & Hfr)".
    iPoseProof (block_repr_inbounds with "Hblk") as "(Hblk & %Hbdd)".
    subst w.
    iApply (spec_add_hdr_sz with "[Hfr]"); iFrame; eauto.
    - iSplit.
      + auto.
      + iPureIntro; lia.
    - iIntros (w) "(%out32 & Hout & Houtr & Hfr)".
      iApply "HΦ".
      iExists _; iFrame.
  }
  iIntros "(%sz32 & %Hsz & %Heq & Hfr)".
  congruence.
Qed.

Lemma spec_mark_free E f memidx blk (sz: N) (blk_addr: N) (blk_addr32: i32) (next_addr: N) (sz_u sz_left: N) :
  ⊢ {{{{ block_repr memidx (UsedBlk blk_addr sz_u sz_left) next_addr ∗
         alloc_tok memidx (blk_addr + data_off) ∗
         own_vec memidx (blk_addr + data_off) sz_u ∗
         ⌜(sz = sz_u + sz_left)%N⌝ ∗
         ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         ⌜f.(f_locs) !! blk = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    (to_e_list (mark_free blk)) @ E
    {{{{ v, ⌜v = immV []⌝ ∗
            ⌜f.(f_locs) !! blk = Some (VAL_int32 blk_addr32)⌝ ∗
            block_repr memidx (FreeBlk blk_addr sz) next_addr ∗
            ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(Hblk & Htok & Hu & %Hsz & (%Haddrpf & %Haddr) & %Hblkvar & %Hmem & Hfr) HΦ".
  unfold mark_used.
  wp_chomp 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗
                           ↪[frame]f)%I).
  iSplitR; [iIntros "(%H & ?)"; auto|].
  iSplitL "Hfr".
  { iApply wp_get_local; eauto. }
  iIntros (w) "(%Hw & Hfr)".
  subst w.
  simpl block_repr at 1.
  iDestruct "Hblk" as "(Hbd & Hstate & Hsize & Hnext & Hvec)".
  iSimpl.
  iDestruct "Hstate" as (st32) "(%Hst32 & Hstfield)".
  iApply (wp_wand with "[Hstfield Htok Hfr]").
  - unfold state_off.
    iApply wp_store; eauto.
    by instantiate (1:= bits (VAL_int32 st32)).
    iFrame.
    iSplitR.
    fill_imm_pred.
    rewrite Haddr.
    rewrite N2Nat.id.
    by iFrame.
  - iIntros (w) "((%Hw & Hstfield) & Hfr)".
    subst w.
    iApply "HΦ".
    unfold block_repr, data_repr.
    rewrite Hsz.
    rewrite N2Nat.id.
    iFrame; auto.
    repeat iSplit; auto.
    rewrite own_vec_split.
    iFrame.
    iExists _.
    rewrite -Haddr.
    unfold state_off.
    by iFrame.
Qed.

Lemma spec_mark_free_final E f memidx blk sz blk_addr blk_addr32 :
  ⊢ {{{{ final_block_repr memidx (FinalBlk blk_addr sz) blk_addr ∗
         ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         ⌜f.(f_locs) !! blk = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    (to_e_list (mark_free blk)) @ E
    {{{{ v, ⌜v = immV []⌝ ∗
            block_repr memidx (FreeBlk blk_addr sz) 0 ∗
            ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(Hblk & (%Haddrpf & %Haddr) & %Hblkvar & %Hmem & Hfr) HΦ".
  unfold mark_used.
  wp_chomp 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗
                           ↪[frame]f)%I).
  iSplitR; [iIntros "(%H & ?)"; auto|].
  iSplitL "Hfr".
  { iApply wp_get_local; eauto. }
  iIntros (w) "(%Hw & Hfr)".
  subst w.
  simpl block_repr at 1.
  iDestruct "Hblk" as "(_ & Hbd & Hstate & Hsize & Hnext & Hvec)".
  iSimpl.
  iDestruct "Hstate" as (st32) "(%Hst32 & Hstfield)".
  iApply (wp_wand with "[Hstfield Hfr]").
  instantiate (1 := λ w, ((⌜w = immV [] ⌝ ∗ 
                        N.of_nat (N.to_nat memidx) ↦[wms][blk_addr + state_off]bits (value_of_uint BLK_FREE)) ∗
                        ↪[frame]f)%I).
  - unfold state_off.
    rewrite Haddr.
    iApply wp_store;
      eauto;
      try rewrite N2Nat.id;
      [| iFrame ];
      auto.
  - iIntros (w) "((%Hw & Hstfield) & Hfr)".
    subst w.
    iApply "HΦ".
    unfold block_repr, data_repr.
    rewrite N2Nat.id.
    iFrame; auto.
Qed.

Lemma spec_mark_used E f memidx blk sz blk_addr blk_addr32 next_addr sz_u sz_left :
  ⊢ {{{{ block_repr memidx (FreeBlk blk_addr sz) next_addr ∗
         ⌜(sz = sz_u + sz_left)%N⌝ ∗
         ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         ⌜f.(f_locs) !! blk = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    (to_e_list (mark_used blk)) @ E
    {{{{ v, ⌜v = immV []⌝ ∗
            ⌜f.(f_locs) !! blk = Some (VAL_int32 blk_addr32)⌝ ∗
            own_vec memidx (blk_addr + data_off) sz_u ∗
            (*alloc_tok memidx (blk_addr + data_off) ∗*)
            block_repr memidx (UsedBlk blk_addr sz_u sz_left) next_addr ∗
            ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "(Hblk & %Hsz & (%Haddrpf & %Hblk_addr_rep) & %Hblkvar & %Hmem & Hfr) HΦ".
  unfold mark_used.
  wp_chomp 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗
                           ↪[frame]f)%I).
  iSplitR; [iIntros "(%H & ?)"; auto|].
  iSplitL "Hfr".
  { iApply wp_get_local; eauto. }
  iIntros (w) "(%Hw & Hfr)".
  subst w.
  simpl block_repr at 1.
  iDestruct "Hblk" as "(Hbd & Hstate & Hsize & Hnext & Hvec)".
  iSimpl.
  iDestruct "Hstate" as (st32) "(%Hst32 & Hstfield)".
  iApply (wp_wand with "[Hstfield Hfr]").
  instantiate (1 := λ w, ((⌜w = immV [] ⌝ ∗ 
                        N.of_nat (N.to_nat memidx) ↦[wms][blk_addr + state_off]bits (value_of_uint BLK_USED)) ∗
                        ↪[frame]f)%I).
  - unfold state_off.
    rewrite Hblk_addr_rep.
    iApply wp_store;
      eauto;
      try rewrite N2Nat.id;
      [| iFrame ];
      auto.
  - iIntros (w) "((%Hw & Hstfield) & Hfr)".
    subst w.
    iApply "HΦ".
    unfold block_repr, state_repr.
    rewrite Hsz.
    rewrite N2Nat.id.
    iPoseProof (own_vec_split with "Hvec") as "(Hvec1 & Hvec2)".
    iFrame; auto.
Qed.

Lemma spec_mark_final E memidx blk_addr blk_addr32 blk f :
  ⊢ {{{{ own_vec memidx (blk_addr + state_off) 4 ∗
          ⌜N_repr blk_addr blk_addr32 ⌝ ∗
          ⌜f.(f_locs) !! blk = Some (VAL_int32 blk_addr32)⌝ ∗
          ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
          ↪[frame] f }}}}
    (to_e_list (mark_final blk)) @ E
    {{{{ v, ⌜v = immV []⌝ ∗
            state_repr memidx Final blk_addr ∗
            ↪[frame] f }}}}.
Proof.
  iIntros "!>" (Φ) "((%bs & %Hbs & Hslot) & (%Haddrpf & %Hblk_addr_rep) & %Hblkvar & %Hmem & Hfr) HΦ".
  wp_chomp 1.
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV [VAL_int32 blk_addr32]⌝ ∗
                           ↪[frame]f)%I).
  iSplitR.
  { iIntros "(%Htrap & Hfr)"; congruence. }
  iSplitL "Hfr".
  {
    iApply wp_get_local; eauto.
  }
  iIntros (w) "(%Hw & Hfr)".
  subst w; cbn.
  iApply (wp_wand with "[Hslot Hfr]").
  {
    iApply wp_store; eauto.
    all: swap 1 2.
    rewrite <- Hblk_addr_rep.
    rewrite N2Nat.id.
    iFrame.
    instantiate (1:= λ w, ⌜w = immV [] ⌝%I).
    eauto.
    cbn.
    lia.
  }
  iIntros (w) "((%Hw & Hpts) & Hfr)".
  iApply "HΦ".
  subst.
  iFrame; auto.
  iSplit; auto.
  unfold state_repr.
  rewrite N2Nat.id.
  iExists (Wasm_int.int_of_Z i32m (Z.of_N BLK_FINAL)).
  iFrame.
  auto.
Qed.

(* SPECS: block tests *)

Lemma spec_is_block_nonfinal_true E memidx blk blk_var blk_addr32 next_addr f :
  ⊢ {{{{ ⌜N_repr (block_addr blk) blk_addr32 ⌝ ∗
         block_repr memidx blk next_addr ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    to_e_list (is_block_nonfinal blk_var) @ E
    {{{{ w,⌜w = immV [VAL_int32 (wasm_bool true)]⌝ ∗
         block_repr memidx blk next_addr ∗
         ↪[frame] f }}}}.
Proof.
  iIntros (Φ) "!> (%Hblk_addr & Hblk & %Hvar & %Hmem & Hfr) HΦ".
  unfold is_block_nonfinal.
  erewrite to_e_list_cat.
  iApply wp_seq.
  iSplitR.
  all:swap 1 2.
  iSplitL "Hblk Hfr".
  - iApply (spec_get_state with "[Hblk Hfr]"); iFrame; eauto.
  - iIntros (w) "(%st32 & %Hw & %Hst & Hblk & Hfr)".
    subst w.
    cbn.
    iApply (wp_wand with "[Hfr]").
    + iApply (wp_relop with "[Hfr]"); auto.
      instantiate (1:=λ w, ⌜w = immV [VAL_int32 (wasm_bool true)]⌝%I).
      iModIntro.
      iPureIntro.
      assert (st32 <> (Wasm_int.int_of_Z i32m (Z.of_N BLK_FINAL))).
      {
        intro; subst.
        destruct blk; destruct Hst; cbn in *; discriminate.
      }
      cbn.
      rewrite Wasm_int.Int32.eq_false; auto.
    + iIntros (w) "(%Hw & Hfr)".
      subst.
      iApply "HΦ".
      iFrame; auto.
  - iIntros "(%st32 & %Htrap & _)".
    congruence.
Qed.

Lemma spec_is_block_nonfinal_false E memidx blk blk_var blk_addr blk_addr32 f :
  ⊢ {{{{ ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         final_block_repr memidx blk blk_addr ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    to_e_list (is_block_nonfinal blk_var) @ E
    {{{{ w,⌜w = immV [VAL_int32 (wasm_bool false)]⌝ ∗
         final_block_repr memidx blk blk_addr ∗
         ↪[frame] f }}}}.
Proof.
  iIntros (Φ) "!> (%Hblk_addr & Hblk & %Hvar & %Hmem & Hfr) HΦ".
  unfold is_block_nonfinal.
  erewrite to_e_list_cat.
  iApply wp_seq.
  iSplitR.
  all:swap 1 2.
  iSplitL "Hblk Hfr".
  - iApply (spec_get_final_state with "[Hblk Hfr]"); iFrame; eauto.
  - iIntros (w) "(%st32 & %Hw & %Hst & Hblk & Hfr)".
    subst w.
    cbn.
    iApply (wp_wand with "[Hfr]").
    + iApply (wp_relop with "[Hfr]"); auto.
      instantiate (1:=λ w, ⌜w = immV [VAL_int32 (wasm_bool false)]⌝%I).
      iModIntro.
      iPureIntro.
      assert (st32 = (Wasm_int.int_of_Z i32m (Z.of_N BLK_FINAL))).
      {
        inversion Hst as [Hbd Hst'].
        destruct blk.
        rewrite <- (Wasm_int.Int32.repr_unsigned st32).
        cbn in *.
        rewrite <- (Z2N.id (Wasm_int.Int32.unsigned st32)).
        rewrite <- Hst'.
        reflexivity.
        apply Wasm_int.Int32.size_interval_1.
      }
      cbn.
      subst.
      rewrite Wasm_int.Int32.eq_true; auto.
    + iIntros (w) "(%Hw & Hfr)".
      subst.
      iApply "HΦ".
      iFrame; auto.
  - iIntros "(%st32 & %Htrap & _)".
    congruence.
Qed.

Definition prop_repr (P : Prop) (b: bool) : Prop :=
  is_true b <-> P.

Lemma spec_is_block_free_true blk_addr blk_addr32 next_addr sz memidx blk_var f E:
  ⊢ {{{{ ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         block_repr memidx (FreeBlk blk_addr sz) next_addr ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    to_e_list (is_block_free blk_var) @ E
    {{{{ w, ⌜w = immV [VAL_int32 (wasm_bool true)]⌝ ∗
            block_repr memidx (FreeBlk blk_addr sz) next_addr ∗
            ↪[frame] f }}}}.
Proof.
  iIntros (Φ) "!> (%Hblk_addr & Hblk & %Hvar & %Hmem & Hfr) HΦ".
  unfold is_block_free.
  erewrite to_e_list_cat.
  iApply wp_seq.
  iSplitR.
  all:swap 1 2.
  iSplitL "Hblk Hfr".
  - iApply (spec_get_state with "[Hblk Hfr]"); iFrame; eauto.
  - iIntros (w) "(%st32 & %Hw & %Hst & Hblk & Hfr)".
    subst w.
    cbn.
    iApply (wp_wand with "[Hfr]").
    + iApply (wp_relop with "[Hfr]"); auto.
      instantiate (1:=λ w, ⌜w = immV [VAL_int32 (wasm_bool true)]⌝%I).
      iModIntro.
      iPureIntro.
      assert (st32 = (Wasm_int.int_of_Z i32m (Z.of_N BLK_FREE))).
      {
        inversion Hst as [Hbd Hst'].
        rewrite <- (Wasm_int.Int32.repr_unsigned st32).
        cbn in *.
        rewrite <- (Z2N.id (Wasm_int.Int32.unsigned st32)).
        rewrite <- Hst'.
        reflexivity.
        apply Wasm_int.Int32.size_interval_1.
      }
      subst.
      reflexivity.
    + iIntros (w) "(%Hw & Hfr)".
      subst.
      iApply "HΦ".
      iFrame; auto.
  - iIntros "(%st32 & %Htrap & _)".
    congruence.
Qed.

Lemma spec_is_block_free_false blk_addr blk_addr32 next_addr sz_u sz_l memidx blk_var f E:
  ⊢ {{{{ ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         block_repr memidx (UsedBlk blk_addr sz_u sz_l) next_addr ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    to_e_list (is_block_free blk_var) @ E
    {{{{ w, ⌜w = immV [VAL_int32 (wasm_bool false)]⌝ ∗
            block_repr memidx (UsedBlk blk_addr sz_u sz_l) next_addr ∗
            ↪[frame] f }}}}.
Proof.
  iIntros (Φ) "!> (%Hblk_addr & Hblk & %Hvar & %Hmem & Hfr) HΦ".
  unfold is_block_free.
  erewrite to_e_list_cat.
  iApply wp_seq.
  iSplitR.
  all:swap 1 2.
  iSplitL "Hblk Hfr".
  - iApply (spec_get_state with "[Hblk Hfr]"); iFrame; eauto.
  - iIntros (w) "(%st32 & %Hw & %Hst & Hblk & Hfr)".
    subst w.
    cbn.
    iApply (wp_wand with "[Hfr]").
    + iApply (wp_relop with "[Hfr]"); auto.
      instantiate (1:=λ w, ⌜w = immV [VAL_int32 (wasm_bool false)]⌝%I).
      iModIntro.
      iPureIntro.
      assert (st32 = (Wasm_int.int_of_Z i32m (Z.of_N BLK_USED))).
      {
        inversion Hst as [Hbd Hst'].
        rewrite <- (Wasm_int.Int32.repr_unsigned st32).
        cbn in *.
        rewrite <- (Z2N.id (Wasm_int.Int32.unsigned st32)).
        rewrite <- Hst'.
        reflexivity.
        apply Wasm_int.Int32.size_interval_1.
      }
      subst.
      reflexivity.
    + iIntros (w) "(%Hw & Hfr)".
      subst.
      iApply "HΦ".
      iFrame; auto.
  - iIntros "(%st32 & %Htrap & _)".
    congruence.
Qed.

Lemma spec_is_block_free_final blk_addr blk_addr32 blk memidx blk_var f E:
  ⊢ {{{{ ⌜N_repr blk_addr blk_addr32 ⌝ ∗
         final_block_repr memidx blk blk_addr ∗
         ⌜f.(f_locs) !! blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f }}}}
    to_e_list (is_block_free blk_var) @ E
    {{{{ w, ⌜w = immV [VAL_int32 (wasm_bool false)]⌝ ∗
            final_block_repr memidx blk blk_addr ∗
            ↪[frame] f }}}}.
Proof.
  iIntros (Φ) "!> (%Hblk_addr & Hblk & %Hvar & %Hmem & Hfr) HΦ".
  destruct blk.
  unfold is_block_free.
  erewrite to_e_list_cat.
  iApply wp_seq.
  iSplitR.
  all:swap 1 2.
  iSplitL "Hblk Hfr".
  - iApply (spec_get_final_state with "[Hblk Hfr]"); iFrame; eauto.
  - iIntros (w) "(%st32 & %Hw & %Hst & Hblk & Hfr)".
    subst w.
    cbn.
    iApply (wp_wand with "[Hfr]").
    + iApply (wp_relop with "[Hfr]"); auto.
      instantiate (1:=λ w, ⌜w = immV [VAL_int32 (wasm_bool false)]⌝%I).
      iModIntro.
      iPureIntro.
      assert (st32 = (Wasm_int.int_of_Z i32m (Z.of_N BLK_FINAL))).
      {
        inversion Hst as [Hbd Hst'].
        rewrite <- (Wasm_int.Int32.repr_unsigned st32).
        cbn in *.
        rewrite <- (Z2N.id (Wasm_int.Int32.unsigned st32)).
        rewrite <- Hst'.
        reflexivity.
        apply Wasm_int.Int32.size_interval_1.
      }
      subst.
      reflexivity.
    + iIntros (w) "(%Hw & Hfr)".
      subst.
      iApply "HΦ".
      iFrame; auto.
  - iIntros "(%st32 & %Htrap & _)".
    congruence.
Qed.

Lemma lt_ssrleq x y : 
  x < y ->
  ssrnat.leq (S x) y.
Proof.
  destruct (@ssrnat.ltP x y); auto.
Qed.

Lemma example E f n32 :
    ⊢ {{{{ 
            ⌜f.(f_locs) !! 0 = Some (VAL_int32 n32)⌝ ∗
            ↪[frame] f
      }}}}
      to_e_list ([BI_get_local 0; BI_get_local 0; BI_relop T_i32 (Relop_i ROI_eq)]) @ E
      {{{{ w, ⌜w = immV [VAL_int32 (wasm_bool true)]⌝ ∗ ↪[frame] f }}}}.
Proof.
  iIntros (Φ) "!> (%Hloc & Hfr) HΦ".
  wp_chomp 1.
  set (Φ' := (λ w, ⌜w = immV [VAL_int32 n32] ⌝ ∗ ↪[frame] f)%I).
  iApply (wp_seq _ _ _ Φ').
  iSplitR. { iIntros "(%Hw & _)" => //. }
  iSplitL "Hfr".
  {
    iApply wp_get_local; auto.
    assumption.
  }
  iIntros (w) "(%Hw & Hfr)".
  subst w.
  wp_chomp 2.
  iApply (wp_wand _ _ _ (λ w, ⌜w = immV [VAL_int32 Wasm_int.Int32.one]⌝ ∗  ↪[frame]f)%I with "[Hfr] [HΦ]"); auto.
  set (Φ'' := (λ w, ⌜w = immV [VAL_int32 n32; VAL_int32 n32] ⌝ ∗ ↪[frame] f)%I).
  iApply (wp_seq _ _ _ Φ'').
  iSplitR. { iIntros "(%Hw & _)" => //. }
  iSplitL "Hfr".
  {
    wp_chomp 1.
    iApply wp_val_app => //.
    iSplitR. { iIntros "!> (%Hw & _)" => //. }
    iApply wp_get_local; eauto.
  }
  iIntros (w) "(-> & Hfr)".
  simpl.
  iApply (wp_relop with "[Hfr]") =>//.
  cbn.
  rewrite Wasm_int.Int32.eq_true.
  auto.
Qed.

Lemma wp_get_locals vars vals E f :
  Forall2 (fun x v => f.(f_locs) !! x = Some v) vars vals ->
  ⊢ {{{{ ↪[frame] f }}}}
    to_e_list (List.map BI_get_local vars) @ E
    {{{{ w, ⌜w = immV vals⌝ ∗ ↪[frame] f }}}}.
Proof.
  induction 1.
  - iIntros (Φ) "!> Hfr HΦ".
    rewrite wp_unfold /wp_pre /=.
    iModIntro.
    iApply "HΦ".
    auto.
  - iIntros (Φ) "!> Hfr HΦ".
    wp_chomp 1.
    set (Φ' := (λ w, ⌜w = immV [y]⌝ ∗ ↪[frame]f)%I).
    iApply (wp_seq _ _ _ Φ').
    iSplitR. { iIntros "(%Hw & _)" => //. }
    iSplitL "Hfr".
    {
      iApply wp_get_local; auto.
      assumption.
    }
    iIntros (w) "(%Hw & Hfr)".
    subst w.
    iApply (wp_wand _ _ _ (λ w, ⌜w = immV (y::l')⌝ ∗ ↪[frame] f)%I with "[Hfr]"); auto.
    iApply wp_val_app; auto.
    iSplitR.
    { iIntros "!> (%Hw & _)" => //. }
    iApply (wp_wand with "[Hfr]").
    iApply (IHForall2 with "[Hfr]"); auto.
    iIntros (w) "(%Hw & Hfr)".
    iFrame.
    subst w; auto.
Qed.

Lemma unsigned_is_N:
  forall z: i32,
  Wasm_int.Int32.unsigned z = Z.of_N (Wasm_int.N_of_uint i32m z).
Proof.
  intros.
  cbn.
  rewrite Z2N.id =>//.
  apply Wasm_int.Int32.unsigned_range.
Qed.

Lemma unsigned_N_repr (z: i32) :
  N_repr (Z.to_N (Wasm_int.Int32.unsigned z)) z.
Proof.
  unfold N_repr.
  rewrite Z2N.id; [|apply Wasm_int.Int32.unsigned_range].
  split.
  - pose proof (Wasm_int.Int32.unsigned_range z).
    lia.
  - reflexivity.
Qed.

Lemma N_repr_inj (z: i32) (a b: N) :
  N_repr a z ->
  N_repr b z ->
  a = b.
Proof.
  unfold N_repr.
  intuition congruence.
Qed.

Lemma imul_repr:
  forall (x y z: N) x32 y32,
    N_repr x x32 ->
    N_repr y y32 ->
    (Z.of_N z < Wasm_int.Int32.modulus)%Z ->
    (x * y = z)%N ->
    N_repr z (Wasm_int.Int32.imul x32 y32).
Proof.
  intros ? ? ? ? ? [Hxbdd Hx] [Hybdd Hy] Hzbdd Hsum.
  split.
  - lia.
  - unfold Wasm_int.Int32.imul, Wasm_int.Int32.mul.
    rewrite !unsigned_is_N.
    unfold Wasm_int.Int32.repr.
    cbn.
    rewrite Wasm_int.Int32.Z_mod_modulus_id.
    rewrite Z2N.id; [|apply Wasm_int.Int32.unsigned_range].
    rewrite Z2N.id; [|apply Wasm_int.Int32.unsigned_range].
    rewrite Z2N.inj_mul; try apply Wasm_int.Int32.unsigned_range.
    rewrite !unsigned_is_N.
    rewrite <- Hy.
    rewrite <- Hx.
    now rewrite !N2Z.id.
    rewrite !Z2N.id; try apply Wasm_int.Int32.unsigned_range.
    rewrite !unsigned_is_N.
    lia.
Qed.

Lemma N_repr_repr x: 
  (-1 < x < Wasm_int.Int32.modulus)%Z ->
  N_repr (Z.to_N x) (Wasm_int.Int32.repr x).
Proof.
  intros H.
  unfold Wasm_int.Int32.repr.
  split.
  - lia.
  - cbn. 
    rewrite Wasm_int.Int32.Z_mod_modulus_id; lia.
Qed.

Lemma iadd_repr:
  forall (x y z: N) x32 y32,
    N_repr x x32 ->
    N_repr y y32 ->
    (Z.of_N z < Wasm_int.Int32.modulus)%Z ->
    (x + y = z)%N ->
    N_repr z (Wasm_int.Int32.iadd x32 y32).
Proof.
  intros ? ? ? ? ? [Hxbdd Hx] [Hybdd Hy] Hzbdd Hsum.
  split.
  - lia.
  - unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
    rewrite !unsigned_is_N.
    unfold Wasm_int.Int32.repr.
    cbn.
    rewrite Wasm_int.Int32.Z_mod_modulus_id.
    rewrite Z2N.id; [|apply Wasm_int.Int32.unsigned_range].
    rewrite Z2N.id; [|apply Wasm_int.Int32.unsigned_range].
    rewrite Z2N.inj_add; try apply Wasm_int.Int32.unsigned_range.
    rewrite !unsigned_is_N.
    rewrite <- Hy.
    rewrite <- Hx.
    now rewrite !N2Z.id.
    rewrite !Z2N.id; try apply Wasm_int.Int32.unsigned_range.
    rewrite !unsigned_is_N.
    lia.
Qed.

Lemma divu_repr:
  forall (x y z: N) x32 y32,
    N_repr x x32 ->
    N_repr y y32 ->
    (Z.of_N z < Wasm_int.Int32.modulus)%Z ->
    (x `div` y = z)%N ->
    N_repr z (Wasm_int.Int32.divu x32 y32).
Proof.
  intros ? ? ? ? ? [Hxbdd Hx] [Hybdd Hy] Hzbdd Hsum.
  split.
  - lia.
  - unfold Wasm_int.Int32.divu.
    rewrite !unsigned_is_N.
    cbn.
    rewrite Wasm_int.Int32.Z_mod_modulus_id.
    + rewrite Z2N.id; [|apply Wasm_int.Int32.unsigned_range].
      rewrite Z2N.id; [|apply Wasm_int.Int32.unsigned_range].
      rewrite Z2N.inj_div; try apply Wasm_int.Int32.unsigned_range.
      rewrite !unsigned_is_N.
      rewrite <- Hy.
      rewrite <- Hx.
      now rewrite !N2Z.id.
    + rewrite !Z2N.id; try apply Wasm_int.Int32.unsigned_range.
      rewrite !unsigned_is_N.
      rewrite <- Hy, <- Hx.
      lia.
Qed.

Lemma isub_repr:
  forall (x y z: N) x32 y32,
    N_repr x x32 ->
    N_repr y y32 ->
    (0 <= Z.of_N x - Z.of_N y)%Z ->
    (x - y = z)%N ->
    N_repr z (Wasm_int.Int32.isub x32 y32).
Proof.
  intros x y z x32 y32 [Hxbdd Hx] [Hybdd Hy] Hbdd Hsub.
  assert (Hzbdd: (-1 < Z.of_N z < Wasm_int.Int32.modulus)%Z) by lia.
  split; auto.
  unfold Wasm_int.Int32.isub.
  unfold Wasm_int.Int32.sub.
  cbn.
  rewrite Wasm_int.Int32.Z_mod_modulus_id.
  rewrite Z2N.inj_sub.
  rewrite !unsigned_is_N.
  rewrite <- Hx.
  rewrite <- Hy.
  rewrite !N2Z.id.
  auto.
  apply Wasm_int.Int32.unsigned_range.
  rewrite !unsigned_is_N.
  rewrite <- Hx, <- Hy.
  lia.
Qed.

Lemma ilt_repr :
  forall x y x32 y32,
    N_repr x x32 ->
    N_repr y y32 ->
    Wasm_int.Int32.ltu x32 y32 = (x <? y)%N.
Proof.
Admitted.

Lemma ilt_repr_true:
  forall x y x32 y32,
    N_repr x x32 ->
    N_repr y y32 ->
    (x < y)%N ->
    Wasm_int.Int32.ltu x32 y32 = true.
Proof.
Admitted.

Lemma ilt_repr_false:
  forall x y x32 y32,
    N_repr x x32 ->
    N_repr y y32 ->
    ¬(x < y)%N ->
    Wasm_int.Int32.ltu x32 y32 = false.
Proof.
Admitted.


(* "Effective" or functional versions of NoDup and ∉ *)
Fixpoint NotInEff {A} (x: A) (l: list A) : Prop :=
  match l with
  | [] => True
  | y :: l => x <> y /\ NotInEff x l
  end.

Lemma equiv_NotInEff {A} (x: A) (l: list A) :
  x ∉ l <-> NotInEff x l.
Proof.
  induction l.
  - simpl.
    cut (x ∉ []); [tauto|].
    intros H.
    inversion H.
  - split; intros H.
    + cbn.
      split.
      * intros Heq.
        subst x.
        apply H.
        by constructor.
      * apply IHl.
        intros Hin.
        apply H.
        by constructor.
    + intros Hin.
      inversion Hin; clear Hin; subst.
      * cbn in H.
        tauto.
      * cbn in H.
        tauto.
Qed.

Fixpoint NoDupEff {A} (l: list A) : Prop := 
  match l with
  | [] => True
  | x :: l => NotInEff x l /\ NoDupEff l
  end.

Lemma equiv_NoDupEff {A} (l: list A) :
  NoDup l <-> NoDupEff l.
Proof.
  induction l; cbn.
  - apply NoDup_nil.
  - split; intros H.
    + inversion H; clear H; subst.
      apply equiv_NotInEff in H2.
      tauto.
    + destruct H as [Hnotin Hnodup].
      apply equiv_NotInEff in Hnotin.
      constructor; tauto.
Qed.

Lemma set_nth_length_eq {T} (x: T) (l: seq.seq T) (i: nat) (d: T) :
    i < seq.size l ->
    length (set_nth x l i d) = length l.
Proof.
  rewrite length_is_size.
  intros.
  by rewrite size_set_nth maxn_nat_max max_r.
Qed.

Lemma set_nth_gt (i: nat) :
  ∀ {A : Type} (l : seq.seq A) (x0 : A) (x : A),
    i >= length l ->
    set_nth x0 l i x = l ++ ncons (i - length l) x0 [x].
Proof.
  induction i; intros.
  - destruct l.
    + reflexivity.
    + inversion H.
  - destruct l; simpl.
    + reflexivity.
    + simpl in *.
      assert (Hi: i >= length l) by lia.
      rewrite IHi; auto.
Qed.

Lemma set_nth_read_neq:
  ∀ {A : Type} (l : seq.seq A) (i j : nat) (x y : A),
    i <> j ->
    l !! j = Some y ->
    set_nth x l i x !! j = Some y.
Proof.
  intros.
  destruct (Nat.lt_dec i (seq.size l)).
  - rewrite update_list_at_is_set_nth.
    rewrite update_ne; auto.
    auto using lt_ssrleq.
  - rewrite set_nth_gt.
    + rewrite lookup_app_l; auto.
      apply lookup_lt_is_Some_1; auto.
    + rewrite length_is_size.
      lia.
Qed.

(* SPECS: block pinching *)
Lemma spec_pinch_block E f memidx old_sz blk_addr blk_addr32 reqd_sz reqd_sz32
  old_sz_var old_sz0 reqd_sz_var new_blk_var new_blk0 final_blk_var :
  ⊢
  {{{{
         final_block_repr memidx (FinalBlk blk_addr old_sz) blk_addr ∗
         ⌜(reqd_sz + blk_hdr_sz < old_sz)%N⌝ ∗
         ⌜N_repr blk_addr blk_addr32⌝ ∗
         ⌜N_repr reqd_sz reqd_sz32⌝ ∗
         ⌜NoDupEff [final_blk_var; reqd_sz_var; old_sz_var; new_blk_var]⌝ ∗
         ⌜f.(f_locs) !! final_blk_var = Some (VAL_int32 blk_addr32)⌝ ∗
         ⌜f.(f_locs) !! reqd_sz_var = Some (VAL_int32 reqd_sz32)⌝ ∗
         ⌜f.(f_locs) !! old_sz_var = Some old_sz0⌝ ∗
         ⌜f.(f_locs) !! new_blk_var = Some new_blk0 ⌝ ∗
         ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝ ∗
         ↪[frame] f
  }}}}
  to_e_list (pinch_block final_blk_var reqd_sz_var old_sz_var new_blk_var) @ E
  {{{{ w, ⌜w = immV [] ⌝ ∗
         block_repr memidx (FreeBlk blk_addr reqd_sz) (blk_addr + reqd_sz + blk_hdr_sz)%N ∗
         final_block_repr memidx (FinalBlk (blk_addr + reqd_sz + blk_hdr_sz) (old_sz - reqd_sz - blk_hdr_sz)) (blk_addr + reqd_sz + blk_hdr_sz) ∗
         ∃ new_addr32 old_sz32,
           ⌜N_repr (blk_addr + reqd_sz + blk_hdr_sz) new_addr32⌝ ∗
           ∃ f', ↪[frame] f' ∗
                 ⌜f'.(f_inst) = f.(f_inst)⌝ ∗
                 ⌜f'.(f_locs) = set_nth (VAL_int32 new_addr32)
                                  (set_nth (VAL_int32 old_sz32) (f_locs f) 
                                     old_sz_var (VAL_int32 old_sz32))
                                  new_blk_var (VAL_int32 new_addr32)⌝
  }}}}.
Proof.
  iIntros (Φ) "!> (Hblk & %Hspace & %Haddr32 & %Hsz32 & %Hdisj & %Hblk_var & %Hsz_var & %Hold_var & %Hnew_var & %Hmem & Hfr) HΦ".
  assert (final_blk_var < length f.(f_locs)) by auto using lookup_lt_is_Some_1.
  assert (reqd_sz_var < length f.(f_locs)) by auto using lookup_lt_is_Some_1.
  assert (old_sz_var < length f.(f_locs)) by auto using lookup_lt_is_Some_1.
  assert (new_blk_var < length f.(f_locs)) by auto using lookup_lt_is_Some_1.
  iPoseProof (final_block_inbounds _ _ _ with "Hblk") as "(%Hbdd & Hblk)".
  cbn in Hbdd.
  unfold pinch_block.
  erewrite !to_e_list_cat.
  set (Φ1 := λ w, (⌜w = immV []⌝ ∗
                  ∃ old32, 
                    ⌜N_repr old_sz old32 ⌝ ∗
                      final_block_repr memidx (FinalBlk blk_addr old_sz) blk_addr ∗
                    ↪[frame] {| f_locs := set_nth (VAL_int32 old32) (f_locs f) old_sz_var (VAL_int32 old32);
                               f_inst := f_inst f |})%I).
  iApply (wp_seq _ _ _ Φ1).
  iSplitL "".
  { iIntros "(%Htrap & _)"; congruence. }
  iSplitL "Hfr Hblk".
  {
    set (Φ1' := λ w, (∃ old32, 
                    ⌜w = immV [VAL_int32 old32]⌝ ∗
                    ⌜N_repr old_sz old32 ⌝ ∗
                      final_block_repr memidx (FinalBlk blk_addr old_sz) blk_addr ∗
                    ↪[frame] f)%I).
    iApply (wp_seq _ _ _ Φ1').
    iSplitR. { iIntros "(%tot & %Htrap & _)"; congruence. }
    iSplitL.
    + iApply (spec_get_final_size with "[Hblk Hfr]"); iFrame; eauto.
      unfold Φ1'.
      iIntros (v) "(%sz32 & %Hrep & -> & Hblk)".
      iExists sz32; auto.
    + iIntros (w) "(%sz32 & -> & %Hrep & Hblk & Hfr)".
      simpl app.
      iApply (wp_wand with "[Hfr]").
      {
        iApply wp_set_local; try iFrame; eauto.
        instantiate (1:= λ w, (⌜w = immV []⌝ ∗ ⌜N_repr old_sz sz32 ⌝)%I); auto.
      }
      iIntros (w) "(%Hw & H)".
      iFrame; auto.
  }
  iIntros (w) "(%Hw & (%old_sz32 & %Hold_sz & Hblk & Hfr))".
  clear Φ1.
  subst w.
  rewrite app_nil_l.
  set (new_addr := (blk_addr + reqd_sz + blk_hdr_sz)%N).
  set (f2 := {| f_locs := set_nth (VAL_int32 old_sz32) (f_locs f) old_sz_var (VAL_int32 old_sz32);
                f_inst := f_inst f |}).
  wp_chomp 2.
  set (Φ2 := λ w, (⌜w = immV [VAL_int32 blk_addr32; VAL_int32 reqd_sz32]⌝ ∗ ↪[frame] f2)%I).
  iApply (wp_seq _ _ _ Φ2).
  iSplitR. { iIntros "(%Hw & _)"; congruence. }
  iSplitL "Hfr".
  {
    iApply ((@wp_get_locals [final_blk_var; reqd_sz_var]) with "[Hfr]"); auto.
    repeat constructor.
    - cbn.
      rewrite update_list_at_is_set_nth; [|auto using lt_ssrleq].
      rewrite update_ne; auto.
      cbn in Hdisj.
      intuition.
    - cbn.
      rewrite update_list_at_is_set_nth; [|auto using lt_ssrleq].
      rewrite update_ne; auto.
      cbn in Hdisj.
      intuition.
  }
  iIntros (w) "(-> & Hfr)".
  set (Φ3 := λ w, (∃ tot32, ⌜w = immV [VAL_int32 blk_addr32; VAL_int32 tot32]⌝ ∗ ⌜N_repr (reqd_sz + blk_hdr_sz) tot32 ⌝ ∗ ↪[frame] f2)%I).
  wp_chomp 4.
  iApply (wp_seq _ _ _ Φ3).
  iSplitR. { iIntros "(%v & (%Hw & _))"; congruence. }
  iSplitL "Hfr".
  {
    wp_chomp 1.
    iApply wp_val_app =>//.
    iSplit. { iIntros "!> (%v & (%Hw & _))"; congruence. }
    iApply (spec_add_hdr_sz with "[Hfr]").
    + iFrame.
      iSplit; auto.
      iPureIntro. 
      lia.
    + iIntros (w) "(%out32 & (-> & %Hout & Hfr))".
      cbn.
      iExists _; iFrame; iSplit; auto.
  }
  iIntros (w) "(%out32 & (-> & %Hout & Hfr))".
  wp_chomp 3.
  set (Φ4 := λ w, ((∃ new_addr32, ⌜w = immV [VAL_int32 new_addr32]⌝ ∗ ⌜N_repr new_addr new_addr32 ⌝) ∗ ↪[frame]f2)%I).
  iApply (wp_seq _ _ _ Φ4).
  iSplitR. { iIntros "((%v & (%Hw & _)) & _)". congruence. }
  iSplitL "Hfr".
  {
    iApply (wp_binop with "[Hfr]"); auto.
    iModIntro.
    iExists _.
    cbn.
    iSplit; auto.
    iPureIntro.
    eapply iadd_repr; eauto || lia.
  }
  iIntros (w) "((%new_addr32 & %Hw & %Hnew_addr32) & Hfr)".
  subst w.
  clear Φ2.
  wp_chomp 2.
  set (f3 := {| f_locs := set_nth (VAL_int32 new_addr32) (f_locs f2) new_blk_var (VAL_int32 new_addr32);
                f_inst := f_inst f2 |}).
  set (Φ5 := λ w, (⌜w = immV []⌝ ∗ ↪[frame] f3)%I).
  iApply (wp_seq _ _ _ Φ5 _).
  iSplitR. { iIntros "(%Hw & _)"; congruence. }
  iSplitL "Hfr".
  {
    iApply wp_set_local; auto.
    eapply lookup_lt_is_Some_1.
    cbn.
    rewrite update_list_at_is_set_nth; [|auto using lt_ssrleq].
    rewrite update_ne; auto.
    cbn in Hdisj; intuition.
  }
  iIntros (w) "(%Hw & Hfr)".
  subst w.
  rewrite app_nil_l.
  wp_chomp 2.
  set (Φ6 := λ w, (⌜w = immV [VAL_int32 blk_addr32; VAL_int32 reqd_sz32]⌝ ∗ ↪[frame] f3)%I).
  iApply (wp_seq _ _ _ Φ6).
  iSplitR. { by iIntros "(%Hw & _)". }
  iSplitL "Hfr".
  {
    iApply (@wp_get_locals [final_blk_var; reqd_sz_var] with "[Hfr]"); [|eauto|].
    - constructor.
      + unfold f3.
        cbn.
        cbn in Hdisj.
        rewrite <- fmap_insert_set_nth; [| by rewrite set_nth_length_eq].
        rewrite list_lookup_insert_ne; [| intuition].
        rewrite <- fmap_insert_set_nth; [| auto ].
        rewrite list_lookup_insert_ne; [| intuition].
        eauto.
      + constructor; [| by constructor].
        cbn.
        cbn in Hdisj.
        rewrite <- fmap_insert_set_nth; [| by rewrite set_nth_length_eq].
        rewrite list_lookup_insert_ne; [| intuition].
        rewrite <- fmap_insert_set_nth; [| auto ].
        rewrite list_lookup_insert_ne; [| intuition].
        eauto.
    - iIntros (w) "(-> & Hfr)".
      iFrame; auto.
  }
  iIntros (w) "(%Hw & Hfr)". subst w.
  wp_chomp 3.
  set (Φ7 := λ w, (⌜w = immV []⌝ ∗ ↪[frame] f3 ∗ final_block_repr memidx (FinalBlk blk_addr reqd_sz) blk_addr ∗
                    own_vec memidx (blk_addr + data_off + reqd_sz) (blk_hdr_sz + (old_sz - reqd_sz - blk_hdr_sz)))%I).
  iApply (wp_seq _ _ _ Φ7).
  iSplitR. { iIntros "(%Hw & _)"; congruence. }
  iSplitL "Hfr Hblk".
  {
    iDestruct "Hblk" as "(_ & %Hbds & Hst & Hsz & Hnext & Hdata)".
    assert (Hszsplit: (old_sz = reqd_sz + (blk_hdr_sz + (old_sz - reqd_sz - blk_hdr_sz)))%N) by lia.
    rewrite Hszsplit.
    setoid_rewrite own_vec_split.
    iDestruct "Hdata" as "(Hdata & Hrest)".
    iApply (spec_set_size_final with "[Hfr Hsz Hdata]"); iFrame; auto.
    iIntros (w) "(-> & Hsz & Hdata & Hfr)".
    iFrame; auto.
    iSplit; auto.
    iPureIntro.
    lia.
  }
  (* mark_free *)
  iIntros (w) "(-> & Hfr & Hblk & Hrest)".
  rewrite app_nil_l.
  wp_chomp 3.
  iApply wp_seq.
  iSplitR; last first.
  iSplitL "Hfr Hblk".
  {
    iApply (spec_mark_free_final with "[Hfr Hblk]"); iFrame => //.
    - iSplit =>//.
      iSplit; iPureIntro; auto.
      cbn in Hdisj.
      apply set_nth_read_neq; [by intuition|].
      apply set_nth_read_neq; intuition.
    - auto.
  }
  (* get locals for set_next *)
  iIntros (w) "(-> & Hblk & Hfr)".
  wp_chomp 2.
  iApply wp_seq.
  iSplitR; last first.
  iSplitL "Hfr".
  {
    iApply (@wp_get_locals [final_blk_var; new_blk_var] with "[Hfr]"); try iFrame; auto.
    constructor.
    cbn in Hdisj.
    apply set_nth_read_neq; [intuition|].
    apply set_nth_read_neq; [intuition|eauto].
    constructor; [|constructor].
    apply set_nth_read.
  }
  (* set_next *)
  iIntros (w) "(-> & Hfr)".
  wp_chomp 3.
  iApply wp_seq. iSplitR; last first.
  iSplitL "Hfr Hblk".
  {
    iApply (spec_set_next with "[Hfr Hblk]"); iFrame; auto.
  }
  (* subdivide remaining space into header fields + data *)
  iPoseProof (own_vec_split with "Hrest") as "(Hhdr & Hdata')".
  iAssert ((_ ∗ _) ∗ _)%I with "[Hhdr]" as "((Hst & Hsz) & Hnext)".
  { 
    replace blk_hdr_sz with (4 + 4 + 4)%N.
    rewrite !own_vec_split.
    iFrame.
    reflexivity.
  }
  (* mark_final *)
  iIntros (w) "(-> & Hblk & Hfr)".
  wp_chomp 3.
  iApply wp_seq. iSplitR; last first. iSplitL "Hfr Hst".
  {
    iApply (spec_mark_final with "[Hfr Hst]").
    - unfold state_off.
      rewrite N.add_0_r.
      iFrame.
      replace (_ + _ + reqd_sz)%N with new_addr
        by (unfold data_off, new_addr; lia).
      iSplit; auto.
      iSplit; iPureIntro; auto.
      by rewrite set_nth_read.
    - auto.
  }
  (* get_locals for computing block size *)
  iIntros (w) "(-> & Hst & Hfr)".
  wp_chomp 3.
  iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
  {
    iApply (@wp_get_locals [new_blk_var; old_sz_var; reqd_sz_var] with "[Hfr]"); try iFrame; auto.
    cbn in Hdisj.
    repeat constructor.
    - by rewrite set_nth_read.
    - cbn.
      apply set_nth_read_neq; [intuition|].
      by rewrite set_nth_read.
    - cbn.
      apply set_nth_read_neq; [intuition|].
      apply set_nth_read_neq; intuition eauto.
  }
  (* subtract reqd - old - hdr to compute remaining size *)
  iIntros (w) "(-> & Hfr)".
  wp_chomp 5.
  iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
  {
    wp_chomp 2.
    iApply wp_val_app =>//.
    iSplitR; last first.
    iApply (wp_wand with "[Hfr]").
    iApply (wp_binop with "[Hfr]"); eauto.
    instantiate (1:= λ w, ⌜w= (immV [VAL_int32 (Wasm_int.int_add Wasm_int.Int32.Tmixin reqd_sz32 (Wasm_int.int_of_Z i32m (Z.of_N blk_hdr_sz)))])⌝%I).
    auto.
    iIntros (w).
    instantiate (1:= λ w, (⌜w= (immV [VAL_int32 new_addr32; VAL_int32 old_sz32; VAL_int32 (Wasm_int.int_add Wasm_int.Int32.Tmixin reqd_sz32 (Wasm_int.int_of_Z i32m (Z.of_N blk_hdr_sz)))])⌝ ∗ ↪[frame] f3)%I).
    iIntros "(-> & Hfr)".
    iFrame; auto.
    iIntros "!> (%Hw & _)". congruence.
  }
  iIntros (w) "(-> & Hfr)".
  wp_chomp 4.
  iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
  {
    wp_chomp 1.
    iApply wp_val_app =>//.
    iSplitR; last first.
    iApply (wp_wand with "[Hfr]").
    iApply (wp_binop with "[Hfr]"); eauto.
    instantiate (1:= λ w, ⌜w= (immV [VAL_int32
            (Wasm_int.int_sub Wasm_int.Int32.Tmixin old_sz32
               (Wasm_int.Int32.iadd reqd_sz32 (Wasm_int.Int32.repr 12)))])⌝%I).
    auto.
    iIntros (w).
    instantiate (1:= λ w, (⌜w= (immV [VAL_int32 new_addr32; VAL_int32
        (Wasm_int.int_sub Wasm_int.Int32.Tmixin old_sz32 (Wasm_int.Int32.iadd reqd_sz32 (Wasm_int.Int32.repr 12)))])⌝ ∗ ↪[frame] f3)%I).
    iIntros "(-> & Hfr)".
    iFrame; auto.
    iIntros "!> (%Hw & _)". congruence.
  }
  (* set_size *)
  iIntros (w) "(-> & Hfr)".
  wp_chomp 3.
  iApply wp_seq. iSplitR; last first. iSplitL "Hsz Hdata' Hfr".
  {
    iApply (spec_set_size_final_setup with "[$Hsz $Hdata' $Hfr]").
    unfold data_off.
    iPureIntro.
    split; [| split].
    - replace (blk_addr + blk_hdr_sz + reqd_sz)%N with new_addr by lia.
      auto.
    - replace (old_sz - reqd_sz - blk_hdr_sz)%N with (old_sz - (reqd_sz + blk_hdr_sz))%N by lia.
      eapply isub_repr; eauto.
      eapply iadd_repr; eauto.
      constructor; [|reflexivity].
      all:lia.
    - auto.
    - auto.
  }
  (* get_local for set_next *)
  iIntros (w) "(-> & (Hsz & Hdata & Hfr))".
  wp_chomp 1.
  iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
  {
    iApply (wp_get_local with "[] [$Hfr //]").
    - apply set_nth_read.
    - instantiate (1 := (λ w, ⌜w = immV [VAL_int32 new_addr32]⌝)%I).
      auto.
  }
  (* set_next *)
  iIntros (w) "(-> & Hfr)".
  iApply (spec_set_next_basic with "[$Hfr $Hnext]").
  {
    replace (blk_addr + data_off + reqd_sz)%N with new_addr
      by (unfold data_off; lia).
    instantiate (1:= 0%N).
    auto.
  }
  iIntros (w) "(-> & Hnext & Hfr)".
  unfold final_block_repr.
  iApply ("HΦ" with "[$Hblk Hdata Hsz Hst Hnext Hfr]").
  {
    unfold new_addr.
    unfold data_off.
    replace (blk_addr + blk_hdr_sz + reqd_sz)%N with (blk_addr + reqd_sz + blk_hdr_sz)%N by lia.
    iFrame.
    iSplit; auto.
    iSplit.
    - unfold block_inbounds.
      unfold f3, f2.
      cbn.
      iPureIntro.
      lia.
    - iExists _, _; auto.
  }
  all:iIntros "(%Hw & _)"; congruence.
Qed.

(* SPECS: block creation *)
(*TODO
*)
Lemma spec_new_block_prelude memidx final_blk_var final_sz final_blk_addr final_blk_addr32 reqd_sz reqd_sz_var reqd_sz32 f E :
  ⊢ {{{{
      final_block_repr memidx (FinalBlk final_blk_addr final_sz) final_blk_addr ∗
      ↪[frame] f ∗
      ⌜(Z.of_N (final_blk_addr + blk_hdr_sz + reqd_sz) < Wasm_int.Int32.modulus)%Z⌝ ∗
      ⌜N_repr final_blk_addr final_blk_addr32⌝ ∗
      ⌜N_repr reqd_sz reqd_sz32⌝ ∗
      ⌜NoDupEff [final_blk_var; reqd_sz_var]⌝ ∗
      ⌜f.(f_locs) !! final_blk_var = Some (VAL_int32 final_blk_addr32)⌝ ∗
      ⌜f.(f_locs) !! reqd_sz_var = Some (VAL_int32 reqd_sz32)⌝ ∗
      ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝
  }}}}
  to_e_list (BI_get_local reqd_sz_var :: (add_hdr_sz ++ get_size final_blk_var ++ [BI_relop T_i32 (Relop_i (ROI_lt SX_U))])) @ E
  {{{{ w, ⌜w = immV [VAL_int32 (wasm_bool (N.ltb (reqd_sz + blk_hdr_sz) final_sz)%N)]⌝ ∗
          final_block_repr memidx (FinalBlk final_blk_addr final_sz) final_blk_addr ∗
          ↪[frame] f  }}}}.
Proof.
  iIntros (Φ) "!> (Hblk & Hfr & %Hbdd & %Hfinal_blk_rep & %Hreqd_sz_rep & %Hdisj & %Hfinal_blk & %Hreqd_sz & %Hmem) HΦ".
  iPoseProof (final_block_inbounds with "Hblk") as "(%Hfbdd & Hblk)".
  cbn in Hfbdd.
  wp_chomp 1.
  iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
  {
    iApply (wp_get_local with "[] [$Hfr //]"); eauto.
    by instantiate (1 := λ w, ⌜w = immV [VAL_int32 reqd_sz32]⌝%I).
  }
  iIntros (w) "(-> & Hfr)".
  wp_chomp 3.
  iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
  {
    iApply (spec_add_hdr_sz with "[$Hfr]"); eauto.
    iSplit; auto.
    iPureIntro.
    lia.
  }
  iIntros (w) "(%out32 & -> & %Houtrep & Hfr)".
  wp_chomp 3.
  iApply wp_seq. iSplitR; last first. iSplitL "Hfr Hblk".
  wp_chomp 1.
  iApply wp_val_app; eauto.
  iSplitR; last first.
  {
    iApply (wp_wand with "[Hfr Hblk]").
    iApply (spec_get_final_size _ _ _ _ _ _ final_blk_var with "[$Hblk $Hfr //]").
    eauto.
    iIntros (w) "(%sz32 & %Hszrep & -> & Hblk & Hfr)".
    instantiate (1 := λ w, (∃ sz32 : i32, ⌜N_repr final_sz sz32⌝ ∗ ⌜w = immV [VAL_int32 out32; VAL_int32 sz32]⌝ ∗ final_block_repr memidx (FinalBlk final_blk_addr final_sz) final_blk_addr ∗  ↪[frame]f)%I).
    cbn.
    iExists _; iFrame; auto.
  }
  all:swap 1 2.
  iIntros (w) "(%sz32 & %Hszrep & -> & Hblk & Hfr)".
  wp_chomp 3.
  iApply (wp_wand with "[Hfr]").
  iApply (wp_relop with "[$Hfr]"); auto.
  instantiate (1:= λ w, ⌜w = immV [VAL_int32 (wasm_bool (app_relop (Relop_i (ROI_lt SX_U)) (VAL_int32 out32) (VAL_int32 sz32)))]⌝%I).
  auto.
  iIntros (w) "(-> & Hfr)".
  iApply "HΦ"; iFrame; auto.
  iPureIntro.
  setoid_rewrite ilt_repr; eauto.
  all:try iIntros "!>".
  all:try (iIntros "(%Hw & _)"; congruence).
  all:try (iIntros "(%out & %Hw & _)"; congruence).
  all:try (iIntros "(%sz & H & (%Hw & _))"; congruence).
Qed.

Lemma spec_new_block_space memidx final_blk_var final_sz final_blk_addr final_blk_addr32 
  reqd_sz reqd_sz_var reqd_sz32 old_sz_var old_sz0 new_blk_var new_blk0 actual_size_var actual_sz0 f E  :
  ⊢ {{{{
      final_block_repr memidx (FinalBlk final_blk_addr final_sz) final_blk_addr ∗
      ↪[frame] f ∗
      ⌜(reqd_sz + blk_hdr_sz < final_sz)%N ⌝ ∗
      ⌜N_repr final_blk_addr final_blk_addr32⌝ ∗
      ⌜N_repr reqd_sz reqd_sz32⌝ ∗
      ⌜NoDupEff [final_blk_var; reqd_sz_var; old_sz_var; new_blk_var; actual_size_var]⌝ ∗
      ⌜f.(f_locs) !! final_blk_var = Some (VAL_int32 final_blk_addr32)⌝ ∗
      ⌜f.(f_locs) !! reqd_sz_var = Some (VAL_int32 reqd_sz32)⌝ ∗
      ⌜f.(f_locs) !! old_sz_var = Some old_sz0⌝ ∗
      ⌜f.(f_locs) !! new_blk_var = Some new_blk0 ⌝ ∗
      ⌜f.(f_locs) !! actual_size_var = Some actual_sz0 ⌝ ∗
      ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝
  }}}}
  to_e_list (new_block final_blk_var reqd_sz_var old_sz_var new_blk_var actual_size_var) @ E
  {{{{ w, ⌜w = immV [] ⌝ ∗
         block_repr memidx (FreeBlk final_blk_addr reqd_sz) (final_blk_addr + reqd_sz + blk_hdr_sz)%N ∗
         final_block_repr memidx (FinalBlk (final_blk_addr + reqd_sz + blk_hdr_sz) (final_sz - reqd_sz - blk_hdr_sz)) (final_blk_addr + reqd_sz + blk_hdr_sz) ∗
         ∃ f', ↪[frame] f' ∗
               ⌜f_inst f' = f_inst f⌝
  }}}}.
Proof.
  iIntros (Φ) "!> (Hblk & Hfr & %Hspace & %Hfinal_blk_rep & %Hreqd_sz_rep & %Hdisj & %Hfinal_blk & %Hreqd_sz & %Hold_sz & %Hnew_blk & %Hactual_sz & %Hmem) HΦ".
  unfold new_block.
  iPoseProof (final_block_inbounds with "Hblk") as "(%Hfbdd & Hblk)".
  cbn in Hfbdd.
  wp_chomp 6.
  iApply wp_seq. iSplitR; last first. iSplitL "Hfr Hblk".
  {
    assert (NoDupEff [final_blk_var; reqd_sz_var]).
    {
      cbn in Hdisj.
      cbn.
      tauto.
    }
    assert (Z.of_N (final_blk_addr + blk_hdr_sz + reqd_sz) < Wasm_int.Int32.modulus)%Z.
    { lia. }
    iApply (spec_new_block_prelude with "[$Hfr $Hblk //]").
    auto.
  }
  iIntros (w) "(-> & Hblk & Hfr)".
  pose proof Hspace as Hspaceb.
  apply N.ltb_lt in Hspaceb.
  rewrite Hspaceb.
  iApply (wp_if_true with "[$Hfr]"); auto.
  {
    iIntros "!> Hfr".
    wp_chomp 0.
    iApply (wp_block with "[$Hfr]"); eauto.
    Locate "WP".
    Search wp_wasm_ctx wp.
    iIntros "!> Hfr".
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_emp; last first.
    iApply wp_ctx_bind; [by cbn |].
    assert (NoDupEff [final_blk_var; reqd_sz_var; old_sz_var; new_blk_var]).
    {
      cbn.
      cbn in Hdisj.
      tauto.
    }
    iApply (spec_pinch_block with "[$Hblk $Hfr //]").
    iIntros (w) "(-> & Hblk & Hfblk & (%new32 & %old32 & %Hnewrep & (%f' & Hfr & %Hfinst & %Hflocs)))".
    iIntros (x) "%Hfill".
    move /lfilledP in Hfill.
    inversion Hfill; subst.
    inversion H9; subst.
    cbn.
    iApply (wp_wand with "[Hfr]").
    iApply (wp_label_value with "[$Hfr]"); auto.
    instantiate (1:= λ w, ⌜w = immV [] ⌝%I).
    auto.
    iIntros (w) "(-> & Hfr)".
    iApply "HΦ".
    by iFrame.
  }
  iIntros "(%Hw & _)"; congruence.
Qed.

Lemma spec_mul_var_page_sz var pages32 f E :
  ⊢ {{{{ ↪[frame] f ∗
         ⌜f.(f_locs) !! var = Some (VAL_int32 pages32)⌝ }}}}
    to_e_list (mul_var_page_sz var) @ E
    {{{{ w, ⌜w = immV [] ⌝ ∗ 
            ↪[frame] {| 
              f_locs := set_nth
                          (VAL_int32 (Wasm_int.Int32.mul pages32 (Wasm_int.int_of_Z i32m (Z.of_N page_size))))
                          (f_locs f) var
                          (VAL_int32 (Wasm_int.Int32.mul pages32 (Wasm_int.int_of_Z i32m (Z.of_N page_size))));
              f_inst := f_inst f
            |}
    }}}}.
Proof.
  iIntros (Φ) "!> (Hfr & %Hvar) HΦ".
  wp_chomp 1.
  iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
  {
    iApply wp_get_local; eauto.
    fill_imm_pred.
  }
  iIntros (w) "(-> & Hfr)".
  wp_chomp 3.
  iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
  {
    iApply (wp_binop with "[$Hfr]"); eauto.
    match goal with 
    | |- context [?g (immV ?v)] => instantiate (1:= λ w, ⌜w = immV v⌝%I) =>//
    end.
  }
  iIntros (w) "(-> & Hfr)".
  iApply (wp_wand with "[Hfr]").
  iApply (wp_set_local with "[] [$Hfr]").
  apply lookup_lt_is_Some_1; auto.
  match goal with 
  | |- context [?g (immV ?v)] => instantiate (1:= λ w, ⌜w = immV v⌝%I) =>//
  end.
  iIntros (w) "(-> & Hfr)".
  iApply "HΦ"; iFrame; auto.
  iIntros "(%Hcontra & _)"; congruence.
  iIntros "(%Hcontra & _)"; congruence.
Qed.

Lemma N_div_contr (n m: N) :
  (n `div` m <= n)%N.
Proof.
  destruct (N.eq_dec m 0)%N.
  - subst.
    rewrite N.div_0_r.
    lia.
  - apply N.Div0.div_le_upper_bound.
    apply N.le_mul_l.
    auto.
Qed.

Lemma spec_new_block_no_space memidx memlen final_blk_var final_sz final_blk_addr final_blk_addr32 
  reqd_sz reqd_sz_var reqd_sz32 old_sz_var old_sz0 new_blk_var new_blk0 actual_size_var actual_sz0 f E  :
  ⊢ {{{{
      final_block_repr memidx (FinalBlk final_blk_addr final_sz) final_blk_addr ∗
      ↪[frame] f ∗
      memidx ↦[wmlength] memlen ∗
      ⌜(page_size | memlen)%N⌝ ∗
      ⌜(final_sz <= reqd_sz + blk_hdr_sz)%N ⌝ ∗
      ⌜(Z.of_N (final_blk_addr + blk_hdr_sz + reqd_sz) < Wasm_int.Int32.modulus)%Z⌝ ∗
      ⌜(Z.of_N (1 + blk_hdr_sz + reqd_sz) < Wasm_int.Int32.modulus)%Z⌝ ∗
      ⌜N_repr final_blk_addr final_blk_addr32⌝ ∗
      ⌜N_repr reqd_sz reqd_sz32⌝ ∗
      ⌜NoDupEff [final_blk_var; reqd_sz_var; old_sz_var; new_blk_var; actual_size_var]⌝ ∗
      ⌜f.(f_locs) !! final_blk_var = Some (VAL_int32 final_blk_addr32)⌝ ∗
      ⌜f.(f_locs) !! reqd_sz_var = Some (VAL_int32 reqd_sz32)⌝ ∗
      ⌜f.(f_locs) !! old_sz_var = Some old_sz0⌝ ∗
      ⌜f.(f_locs) !! new_blk_var = Some new_blk0 ⌝ ∗
      ⌜f.(f_locs) !! actual_size_var = Some actual_sz0 ⌝ ∗
      ⌜f.(f_inst).(inst_memory) !! 0 = Some (N.to_nat memidx)⌝
  }}}}
  to_e_list (new_block final_blk_var reqd_sz_var old_sz_var new_blk_var actual_size_var) @ E
  {{{{ w, ⌜w = immV [] ⌝ ∗
         block_repr memidx (FreeBlk final_blk_addr reqd_sz) (final_blk_addr + reqd_sz + blk_hdr_sz) ∗
         final_block_repr memidx (FinalBlk (final_blk_addr + reqd_sz + blk_hdr_sz) (final_sz - reqd_sz - blk_hdr_sz)) (final_blk_addr + reqd_sz + blk_hdr_sz) ∗
         ∃ f', ↪[frame] f' ∗ ⌜f_inst f' = f_inst f⌝
  }}}}.
Proof.
  iIntros (Φ) "!> (Hblk & Hfr & Hmemlen & %Hmemmod & %Hnospace & %Hbdd & %Hbdd' & %Hfinal_blk_rep 
                  & %Hreqd_sz_rep & %Hdisj & %Hfinal_blk 
                  & %Hreqd_sz & %Hold_sz & %Hnew_blk 
                  & %Hactual_sz & %Hmem) HΦ".
  unfold new_block.
  replace ((memidx↦[wmlength]memlen)%I)
    with (((N.of_nat (N.to_nat memidx)) ↦[wmlength]memlen)%I)
    by (rewrite (N2Nat.id memidx); done).
  iPoseProof (final_block_inbounds with "Hblk") as "(%Hfbdd & Hblk)".
  cbn in Hfbdd.
  wp_chomp 6.
  iApply wp_seq. iSplitR; last first. iSplitL "Hfr Hblk".
  {
    assert (NoDupEff [final_blk_var; reqd_sz_var]).
    {
      cbn in Hdisj.
      cbn.
      tauto.
    }
    clear Hfbdd. (* will mess up evar resolution by getting confused with Hbdd *)
    iApply (spec_new_block_prelude with "[$Hfr $Hblk //]").
    auto.
  }
  iIntros (w) "(-> & Hblk & Hfr)".
  pose proof Hnospace as Hnospaceb.
  apply N.ltb_ge in Hnospaceb.
  rewrite Hnospaceb.
  iApply (wp_if_false with "[$Hfr]"); auto.
  {
    iIntros "!> Hfr".
    wp_chomp 0.
    iApply (wp_block with "[$Hfr]"); eauto.
    iIntros "!> Hfr".
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_emp; last first.
    iApply wp_ctx_bind; [by cbn |].
    (* need in order to prevent unfolding of huge number later *)
    remember (Z.of_N page_size) as page_size_z.
    pose (reqd_pages := (((reqd_sz + blk_hdr_sz) `div` page_size) + 1)%N).
    pose (reqd_mem := (reqd_pages * page_size)%N).
    set (reqd_pages32 := (Wasm_int.Int32.iadd
                            (Wasm_int.Int32.divu 
                               (Wasm_int.Int32.iadd reqd_sz32 (Wasm_int.Int32.repr 12))
                               (Wasm_int.Int32.repr page_size_z))
                            (Wasm_int.Int32.repr 1))) in *.
    assert (Z.of_N ((reqd_sz + 12) `div` page_size + 1) < Wasm_int.Int32.modulus)%Z.
    { 
      cut (Z.of_N ((reqd_sz + 12) `div` page_size) < Wasm_int.Int32.modulus - 1)%Z; [lia|].
      rewrite N2Z.inj_div.
      rewrite N2Z.inj_add.
      assert ((1 < Z.of_N page_size)%Z) by done.
      assert ((1 < Wasm_int.Int32.modulus - 1)%Z) by done.
      apply Z.div_lt_upper_bound; auto.
      unfold blk_hdr_sz in Hbdd'.
      transitivity (Wasm_int.Int32.modulus - 1)%Z.
      - lia.
      - rewrite <- (Z.mul_1_l (_ - _)).
        by apply Z.mul_lt_mono_pos_r.
    }
    assert (N_repr reqd_pages reqd_pages32).
    {
      unfold reqd_pages, reqd_pages32, blk_hdr_sz.
      eapply iadd_repr; eauto.
      - pose proof (@N_div_contr (reqd_sz + 12) page_size).
        eapply divu_repr.
        + eapply iadd_repr.
          eassumption.
          by instantiate (1:=12%N).
          instantiate (1:=(reqd_sz + 12)%N).
          fold blk_hdr_sz.
          lia.
          auto.
        + rewrite Heqpage_size_z.
          instantiate (1:=page_size).
          unfold Wasm_int.Int32.repr.
          split; done.
        + lia.
        + auto.
      - done.
    }
    set (f' := {| f_locs := set_nth (VAL_int32 reqd_pages32) (f_locs f) actual_size_var (VAL_int32 reqd_pages32); f_inst := f_inst f |}).
    iApply (wp_wand with "[Hfr Hblk Hmemlen]").
    {
      wp_chomp 1. 
      iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
      {
        iApply (wp_get_local with "[] [$Hfr]").
        - apply Hreqd_sz.
        - by instantiate (1:= λ w, ⌜w = immV [VAL_int32 reqd_sz32]⌝%I).
      }
      iIntros (w) "(-> & Hfr)".
      wp_chomp 3.
      iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
      {
        iApply (wp_binop with "[$Hfr]").
        auto.
        match goal with 
        | |- context [?g (immV ?v)] => instantiate (1:= λ w, ⌜w = immV v⌝%I) =>//
        end.
      }
      iIntros (w) "(-> & Hfr)".
      wp_chomp 3.
      iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
      {
        iApply (wp_binop with "[$Hfr]").
        auto.
        match goal with 
        | |- context [?g (immV ?v)] => instantiate (1:= λ w, ⌜w = immV v⌝%I) =>//
        end.
      }
      iIntros (w) "(-> & Hfr)".
      (* prevent unfolding of huge number since wp_chomp will call simpl *)
      rewrite <- Heqpage_size_z.
      wp_chomp 3.
      iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
      {
        iApply (wp_binop with "[$Hfr]").
        cbn.
        fold reqd_pages32.
        auto.
        match goal with 
        | |- context [?g (immV ?v)] => instantiate (1:= λ w, ⌜w = immV v⌝%I) =>//
        end.
      }
      iIntros (w) "(-> & Hfr)".
      wp_chomp 2.
      iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
      {
        iApply (wp_tee_local with "[$Hfr]").
        iIntros "!> Hfr".
        wp_chomp 1.
        iApply wp_val_app;auto.
        iSplitR; last first.
        iApply (wp_wand with "[Hfr]").
        iApply (wp_set_local with "[] [$Hfr]");
          auto using lookup_lt_is_Some_1.
        match goal with 
        | |- context [?g (immV ?v)] => instantiate (1:= λ w, ⌜w = immV v⌝%I) =>//
        end.
        iIntros (w) "(-> & Hfr)".
        cbn.
        fold f'.
        match goal with 
        | |- context [?g (immV ?v)] => instantiate (1:= (λ w, ⌜w = immV v⌝ ∗ ↪[frame] f' )%I); by iFrame
        end.
        cbn.
        iIntros "!> (%Hw & _)" =>//.
      }
      iIntros (w) "(-> & Hfr)".
      wp_chomp 2.
      iApply wp_seq. iSplitR; last first. iSplitL "Hfr Hmemlen".
      {
        iApply (wp_grow_memory with "[$Hfr $Hmemlen]") =>//.
        iSplitL; match goal with 
                 | |- context [?g (immV ?v)] => instantiate (1:= λ w, ⌜w = immV v⌝%I) =>//
                 end.
      }
      iIntros (w) "[[Hsuccess | Hfailure] Hfr]".
      - iDestruct "Hsuccess" as "((-> & Hvec & Hmemlen) & %Hmembdd)".
        wp_chomp 2.
        iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
        {
          iApply (wp_set_local with "[] [$Hfr]").
          - rewrite set_nth_length_eq; auto using lookup_lt_is_Some_1.
          - match goal with 
            | |- context [?g (immV ?v)] => instantiate (1:= λ w, ⌜w = immV v⌝%I) =>//
            end.
        }
        iIntros (w) "(-> & Hfr)".
        wp_chomp 1.
        iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
        {
          iApply (wp_get_local with "[] [$Hfr]").
          - apply set_nth_read.
          - match goal with 
            | |- context [?g (immV ?v)] => instantiate (1:= λ w, ⌜w = immV v⌝%I) =>//
            end.
        }
        iIntros (w) "(-> & Hfr)".
        wp_chomp 3.
        iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
        {
          iApply (wp_relop with "[$Hfr]"); auto.
          match goal with 
          | |- context [?g (immV ?v)] => instantiate (1:= λ w, ⌜w = immV v⌝%I) =>//
          end.
        }
        iIntros (w) "(-> & Hfr)".
        simpl app_relop.
        assert ((memlen `div` page_size < page_limit + 1)%N).
        {
          unfold mem_in_bound in Hmembdd.
          lia.
        }
        assert ((Z.of_N (memlen `div` page_size) < Wasm_int.Int32.modulus - 1)%Z).
        {
          transitivity (Z.of_N (page_limit + 1)).
          lia.
          apply Z.ltb_lt; reflexivity.
        }
        rewrite Wasm_int.Int32.eq_false; swap 1 2.
        {
          intros Hcontra.
          apply (f_equal Wasm_int.Int32.unsigned) in Hcontra.
          revert Hcontra.
          cbn.
          rewrite nat_bin.
          rewrite N_nat_Z.
          pose proof (N2Z.is_nonneg (memlen `div` page_size)).
          cut ((Z.of_N (memlen `div` page_size) < Wasm_int.Int32.modulus - 1)%Z); [|by auto].
          intros Hmodbd.
          rewrite Wasm_int.Int32.Z_mod_modulus_id; lia.
        }
        iApply (wp_if_false with "[$Hfr]"); auto using Wasm_int.Int32.one_not_zero.
        iIntros "!> Hfr".
        wp_chomp 0.
        iApply (wp_block with "[$Hfr]"); eauto.
        iIntros "!> Hfr".
        iApply wp_wasm_empty_ctx.
        iApply wp_label_push_emp; last first.
        iApply wp_ctx_bind; [by cbn |].
        wp_chomp (length (mark_free final_blk_var)).
        iApply wp_seq. iSplitR; last first. iSplitL "Hfr Hblk".
        {
          iApply (spec_mark_free_final with "[$Hblk $Hfr]").
          - iSplit; iPureIntro; cbn; eauto.
            split; auto.
            cbn. erewrite set_nth_read_neq; auto.
            cbn in Hdisj; intuition.
            cbn. erewrite set_nth_read_neq; auto.
            cbn in Hdisj; intuition.
          - auto.
        }
        iIntros (w) "(-> & Hblock & Hfr)".
        wp_chomp 4.
        iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
        {
          cbn in Hdisj.
          iApply (spec_mul_var_page_sz with "[$Hfr]").
          - cbn.
            by erewrite set_nth_read.
          - auto.
        }
        iIntros (w) "(-> & Hfr)".
        wp_chomp 4.
        iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
        {
          cbn in Hdisj.
          iApply (spec_mul_var_page_sz with "[$Hfr]").
          - iPureIntro.
            apply set_nth_read_neq. intuition.
            apply set_nth_read_neq. intuition.
            apply set_nth_read.
          - auto.
        }
        iIntros (w) "(-> & Hfr)".
        wp_chomp 2.
        iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
        {
          iApply ((@wp_get_locals [final_blk_var; new_blk_var]) with "[Hfr]"); auto.
          cbn in Hdisj.
          constructor.
          cbn. erewrite set_nth_read_neq; auto.
          intuition.
          cbn. erewrite set_nth_read_neq; auto.
          intuition.
          cbn. erewrite set_nth_read_neq; auto.
          intuition.
          cbn. erewrite set_nth_read_neq; auto.
          intuition.
          eauto.
          constructor.
          cbn. erewrite set_nth_read_neq; eauto.
          intuition.
          cbn. erewrite set_nth_read; eauto.
          constructor.
        }
        fold f'.
        match goal with
        | |- context[ ↪[frame] ?f ] => set (f'' := f)
        end.
        iIntros (w) "(-> & Hfr)".
        rewrite <- Heqpage_size_z.
        assert (Z.of_N page_size < Wasm_int.Int32.modulus)%Z.
        {
          apply Z.ltb_lt; reflexivity.
        }
        assert (Z.of_N (reqd_pages * page_size) < Wasm_int.Int32.modulus)%Z.
        {
          unfold reqd_pages.
          rewrite N.mul_add_distr_r.
          zify.
          set (k := Z.of_N page_size).
          rewrite Z.mul_1_l.
          rewrite Z.lt_add_lt_sub_r.
          eapply Z.le_lt_trans.
          rewrite Z.mul_comm.
          eapply Z.mul_div_le.
          done.
          admit.
        }
        assert (N_repr (reqd_pages * page_size) (Wasm_int.Int32.mul reqd_pages32 (Wasm_int.Int32.repr page_size_z))).
        {
          clear f''.
          eapply imul_repr; eauto.
          rewrite Heqpage_size_z.
          constructor.
          split; eauto.
          unfold Wasm_int.Int32.repr.
          cbn.
          rewrite Wasm_int.Int32.Z_mod_modulus_id.
          by rewrite N2Z.id.
          split; eauto.
        }
        assert (N_repr memlen
                  (Wasm_int.Int32.mul (Wasm_int.Int32.repr
                                         (ssrnat.nat_of_bin (memlen `div` page_size)))
                     (Wasm_int.Int32.repr page_size_z))).
        {
          clear f''.
          replace (N_repr memlen) with (N_repr ((memlen `div` page_size) * page_size)%N).
          rewrite Heqpage_size_z.
          eapply imul_repr.
          - instantiate (1:= (memlen `div` page_size)%N).
            rewrite nat_bin.
            cut (N_repr (Z.to_N (Z.of_nat (N.to_nat (memlen `div` page_size)))) (Wasm_int.Int32.repr (Z.of_nat (N.to_nat (N.div memlen page_size))))).
            {
              intros H'.
              Search (Z.of_nat (N.to_nat _)).
              rewrite N_nat_Z in H'.
              rewrite N_nat_Z.
              rewrite N2Z.id in H'.
              exact H'.
            }
            apply N_repr_repr.
            split; try lia.
            pose proof (Nat2Z.is_nonneg (N.to_nat (memlen `div` page_size))).
            lia.
          - apply N_repr_repr.
            by vm_compute.
          - eapply Z.le_lt_trans.
            zify.
            rewrite Z.mul_comm.
            eapply Z.mul_div_le.
            by vm_compute.
            auto.
            eapply Z.lt_le_trans.
            instantiate (1:= (Z.of_N page_limit)).
            unfold mem_in_bound.
            admit.
            by vm_compute.
          - by rewrite N2Z.id.
          - f_equal.
            Locate "`mod`".
            rewrite - (N.add_0_r (_ * _)).
            apply  N.Lcm0.mod_divide in Hmemmod.
            rewrite -Hmemmod.
            rewrite N.mul_comm.
            symmetry.
            apply N.div_mod.
            done.
        }
        wp_chomp 3.
        iApply wp_seq. iSplitR; last first. iSplitL "Hfr Hblock".
        {
          iApply (spec_set_next with "[$Hblock $Hfr]"); cbn; auto.
        }
        iIntros (w) "(-> & Hblk & Hfr)".
        wp_chomp 2.
        iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
        {
          cbn in Hdisj.
          iApply ((@wp_get_locals [new_blk_var; actual_size_var]) with "[$Hfr]"); auto.
          constructor.
          cbn. apply set_nth_read_neq. intuition.
          cbn. apply set_nth_read.
          constructor.
          cbn. apply set_nth_read.
          constructor.
        }
        iIntros (w) "(-> & Hfr)".
        rewrite <- Heqpage_size_z.
        wp_chomp 4.
        iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
        {
          wp_chomp 1.
          iApply wp_val_app; auto.
          iSplitR; last first.
          fold sub_hdr_sz.
          iApply (wp_wand with "[Hfr]").
          iApply (spec_sub_hdr_sz with "[$Hfr]").
          iSplit; eauto.
          iPureIntro.
          admit.
          eauto.
          auto.
          instantiate (1 := (λ w : val,
                                (∃ out32 : i32,
                                    ⌜w =
                                      val_combine
                                        (immV
                                           [VAL_int32
                                              (Wasm_int.Int32.mul (Wasm_int.Int32.repr (ssrnat.nat_of_bin (memlen `div` page_size)))
                                                 (Wasm_int.Int32.repr page_size_z))]) (immV [VAL_int32 out32])⌝ ∗
                                    ⌜ N_repr (reqd_pages * page_size - blk_hdr_sz) out32⌝ ∗
                                    ↪[frame]f'')%I)).
          iIntros (w) "(%out32 & -> & %Hrep & Hfr)".
          iExists out32; by iFrame.
          by iIntros "!> (%out32 & %Hcontra & _)".
        }
        iIntros (w) "(%out32 & -> & %Houtrep & Hfr)".
        iPoseProof (repeat_own_vec with "[$Hvec]") as "Hvec".
        erewrite <- N_repr_uint by eassumption.
        set (new_mem_size := (reqd_pages * page_size)%N).
        assert (new_mem_size - blk_hdr_sz > reqd_sz)%N.
        { admit. }
        assert (Hsplitsz : (new_mem_size = blk_hdr_sz + (new_mem_size - blk_hdr_sz))%N) by lia.
        rewrite Hsplitsz.
        iPoseProof (own_vec_split with "Hvec") as "[Hnewhd Hnewdata]".
        iEval (change blk_hdr_sz with (4 + (4 + 4))%N) in "Hnewhd".
        iPoseProof (own_vec_split with "Hnewhd") as "[Hstate Hsznext]".
        iPoseProof (own_vec_split with "Hsznext") as "[Hsz Hnext]".
        wp_chomp 3.
        iApply wp_seq. iSplitR; last first. iSplitL "Hfr Hsz Hnewdata".
        {
          iApply (spec_set_size_final_setup with "[$Hfr $Hsz $Hnewdata]").
          - iPureIntro.
            rewrite N2Nat.id.
            intuition eauto.
          - eauto.
        }
        iIntros (w) "(-> & Hsz & Hvec & Hfr)".
        wp_chomp 1.
        iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
        {
          cbn in Hdisj.
          iApply (wp_get_local with "[] [$]").
          apply set_nth_read_neq.
          intuition.
          apply set_nth_read.
          fill_imm_pred.
        }
        iIntros (w) "(-> & Hfr)".
        rewrite <- Heqpage_size_z.
        wp_chomp 3.
        iApply wp_seq. iSplitR; last first. iSplitL "Hfr Hnext".
        {
          replace (memlen + 4 + 4)%N with (memlen + next_off)%N 
            by (unfold next_off; lia).
          iApply (spec_set_next_basic with "[$Hfr $Hnext]").
          iPureIntro.
          instantiate (1:= 0%N).
          intuition.
          split; by vm_compute.
          by rewrite N2Nat.id.
          auto.
        }
        iIntros (w) "(-> & Hnext & Hfr)".
        wp_chomp 3.
        iApply wp_seq. iSplitR; last first. iSplitL "Hfr Hstate".
        {
          cbn in Hdisj.
          iApply (spec_mark_final with "[$Hfr Hstate]").
          iSplitL.
          {
            unfold state_off.
            rewrite N.add_0_r.
            iFrame.
          }
          iPureIntro.
          intuition.
          eauto.
          cbn.
          eapply set_nth_read_neq.
          auto.
          cbn.
          rewrite Heqpage_size_z.
          by apply set_nth_read.
          by rewrite N2Nat.id.
          eauto.
        }
        iIntros (w) "(-> & Hstate & Hfr)".
        cbn.
        cbn in Hdisj.
        iApply (spec_pinch_block with "[$Hstate $Hsz $Hnext $Hfr $Hvec]").
        {
          iPureIntro.
          repeat match goal with
                 | |- _ /\ _ => split
                 end;
            repeat match goal with
              | |- _ !! _ = Some _ => eassumption
              | |- _ !! _ = Some _ => eapply set_nth_read_neq; [by intuition |]
              | |- _ !! _ = Some _ => by (eapply set_nth_read; eauto)
              end.
          reflexivity.
          rewrite Hsplitsz.
          unfold new_mem_size.
          unfold mem_in_bound in Hmembdd.
          admit. (* BORING ARITHMETIC *)
          instantiate (1:= reqd_sz).
          unfold new_mem_size, reqd_pages.
          admit. (* BORING ARITHMETIC *)
          rewrite -Heqpage_size_z.
          eauto.
          eassumption.
          cbn. intuition.
          rewrite N2Nat.id.
          eauto.
        }
        iIntros (w) "(-> & Hblk' & Hfinal & (%new32 & %old32 & %Hrep & (%f''' & Hfr & %Hfinst & %Hflocs)))".
        admit. 
        all:try (iIntros "(%Hw & _)"; congruence).
        all:try (iIntros "(%out32 & %Hw & _)"; cbn in *; congruence).
      (* FAILURE CASE *)
      - iDestruct "Hfailure" as "(-> & Hmemlen)".
        wp_chomp 2.
        iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
        {
          iApply (wp_set_local with "[] [$Hfr]").
          - rewrite set_nth_length_eq; auto using lookup_lt_is_Some_1.
          - match goal with 
            | |- context [?g (immV ?v)] => instantiate (1:= λ w, ⌜w = immV v⌝%I) =>//
            end.
        }
        iIntros (w) "(-> & Hfr)".
        wp_chomp 1.
        iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
        {
          iApply (wp_get_local with "[] [$Hfr]").
          - apply set_nth_read.
          - match goal with 
            | |- context [?g (immV ?v)] => instantiate (1:= λ w, ⌜w = immV v⌝%I) =>//
            end.
        }
        iIntros (w) "(-> & Hfr)".
        wp_chomp 3.
        iApply wp_seq. iSplitR; last first. iSplitL "Hfr".
        {
          iApply (wp_relop with "[$Hfr]"); auto.
          match goal with 
          | |- context [?g (immV ?v)] => instantiate (1:= λ w, ⌜w = immV v⌝%I) =>//
          end.
        }
        iIntros (w) "(-> & Hfr)".
        simpl app_relop.
        rewrite Wasm_int.Int32.eq_true.
        iApply (wp_if_true with "[$Hfr]"); auto using Wasm_int.Int32.one_not_zero.
        iIntros "!> Hfr".
        admit.
        all:iIntros "(%Hw & _)"; congruence.
      - iIntros "[[((%Hw & Hvec & Hmemlen) & Hbdd) | [%Hw _]] _]"; congruence.
      - iIntros "(%Hw & _)"; congruence.
      - iIntros "(%Hw & _)"; congruence.
      - iIntros "(%Hw & _)"; congruence.
      - iIntros "(%Hw & _)"; congruence.
      - iIntros "(%Hw & _)"; congruence.
    }
    iIntros (w) "H".
    simpl push_base.
    admit.
  }
  iIntros "(%Hw & _)"; congruence.
Abort.

(* This needs to have a freelist_repr postcondition *)
Lemma spec_new_block memidx final_blk_var final_sz final_blk_addr final_blk_addr32 
  reqd_sz reqd_sz_var reqd_sz32 old_sz_var old_sz0 new_blk_var new_blk0 actual_size_var actual_sz0 f E  :
  ⊢ {{{{
      final_block_repr memidx (FinalBlk final_blk_addr final_sz) final_blk_addr ∗
      ⌜(reqd_sz + blk_hdr_sz >= final_sz)%N ⌝ ∗

      ⌜N_repr final_blk_addr final_blk_addr32⌝ ∗
      ⌜N_repr reqd_sz reqd_sz32⌝ ∗
      ⌜f.(f_locs) !! final_blk_var = Some (VAL_int32 final_blk_addr32)⌝ ∗
      ⌜f.(f_locs) !! reqd_sz_var = Some (VAL_int32 reqd_sz32)⌝ ∗
      ⌜f.(f_locs) !! old_sz_var = Some old_sz0⌝ ∗
      ⌜f.(f_locs) !! new_blk_var = Some new_blk0 ⌝ ∗
      ⌜f.(f_locs) !! actual_size_var = Some actual_sz0 ⌝
  }}}}
  to_e_list (new_block final_blk_var reqd_sz_var old_sz_var new_blk_var actual_size_var) @ E
  {{{{ w, ⌜w = immV [] ⌝ (* TODO good postcondition for both cases *)
  }}}}.
Proof.
Abort.


(* SPECS: malloc *)
(*TODO
Lemma spec_malloc_loop_body
Lemma spec_malloc_body
Lemma spec_malloc
*)

(* SPECS: free *)
(*TODO
Lemma spec_free
*)

(* Keeping these but commenting out since I broke the proofs
Lemma spec_malloc E f0 reqd_sz (memidx: memaddr) blk :
  ⊢ {{{{ ⌜f0.(f_inst).(inst_memory) !! 0 = Some memidx⌝ ∗
         ⌜f0.(f_locs) !! 0 = Some (VAL_int32 reqd_sz)⌝ ∗
         ⌜length (f_locs f0) >= 2⌝ ∗
         blk_rep blk (N.of_nat memidx) 0 ∗
         ↪[frame] f0
    }}}}
    (to_e_list malloc) @ E
    {{{{ v, ∃ ret_addr, ⌜v = immV [value_of_uint ret_addr]⌝ ∗
            ∃ blk', blk_rep blk' (N.of_nat memidx) 0 ∗ 
                    own_block (N.of_nat memidx) ret_addr reqd_sz ∗
                    ↪[frame] f0 }}}}.
Proof.
  iIntros "!>" (Φ) "(%Hmemidx & %Hsz & %Hlen & Hblk & Hfr) HΦ".
  unfold malloc.
  erewrite !to_e_list_cat.
  set (f1 := {| f_locs := set_nth (value_of_uint 0) (f_locs f0) 1 (value_of_uint 0);
                f_inst := f_inst f0 |}).
  iApply wp_seq.
  instantiate (1 := λ v, (⌜v = immV []⌝ ∗ ↪[frame] f1)%I).
  iSplitR.
  { iIntros "(%Htrap & _)". auto. }
  iSplitL "Hfr".
  {
    cbn. 
    unfold i32const.
    iApply wp_set_local => //.
  }
  iIntros (w) "(%Htrap & Hfr)".
  subst w.
  iApply wp_wasm_empty_ctx.
  iApply (wp_loop_ctx with "[Hfr] [HΦ]") => //; eauto.
  iIntros "!> Hfr".
  iApply wp_label_push_emp.
  iApply wp_ctx_bind; [cbn; tauto|].
  cbn.
  take_drop_app_rewrite 1.
  iApply wp_seq; cbn.
  instantiate (1 := λ v, (⌜v = immV [value_of_uint 0]⌝ ∗ ↪[frame] f1)%I).
  iSplitR.
  { iIntros "(%Htrap & _)" => //. }
  iSplitL "Hfr".
  { 
    iApply wp_get_local => //.
    apply set_nth_read.
  }
  iIntros (w) "(%Hzero & Hfr)".
  subst w.
  take_drop_app_rewrite 2.
  iApply wp_seq; cbn.
Abort.

*)
End malloc.    
