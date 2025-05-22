Require Import Coq.NArith.BinNat.

Inductive state_flag :=
| Used
| Free
| Final.

Inductive block : Type :=
| UsedBlk
    (base_addr: N)
    (blk_used_size: N)
    (blk_leftover_size: N)
    (*(blk_padding: iProp Σ)*)
| FreeBlk
    (base_addr: N)
    (blk_size: N).

Inductive final_block : Type :=
| FinalBlk
    (base_addr: N)
    (blk_size: N).

Definition blocks : Type :=
  list block * final_block.

Definition block_flag blk :=
  match blk with
  | UsedBlk _ _ _ => Used
  | FreeBlk _ _ => Free
  end.

Definition final_block_flag blk :=
  match blk with
  | FinalBlk _ _ => Final
  end.

Definition block_size blk : N :=
  match blk with
  | UsedBlk _ sz_u sz_l => sz_u + sz_l
  | FreeBlk _ sz => sz
  end.

Definition block_addr blk : N :=
  match blk with
  | UsedBlk base_addr _ _
  | FreeBlk base_addr _ => base_addr
  end.

Definition final_block_sz (blk: final_block) : N :=
  match blk with
  | FinalBlk _ sz => sz
  end.

Definition final_block_addr (blk: final_block) : N :=
  match blk with
  | FinalBlk addr _ => addr
  end.

Definition blocks := gmap 
