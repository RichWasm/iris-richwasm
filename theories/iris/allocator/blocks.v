Require Import Coq.NArith.BinNat.

Inductive state_flag :=
| Used
| Free
| Final.

Inductive block : Type :=
| UsedBlk
    (blk_used_size: N)
    (blk_leftover_size: N)
    (*(blk_padding: iProp Σ)*)
| FreeBlk
    (blk_size: N).

Inductive final_block : Type :=
| FinalBlk
    (blk_size: N).

Definition blocks : Type :=
  list block * final_block.

Definition block_flag blk :=
  match blk with
  | UsedBlk _ _ => Used
  | FreeBlk _ => Free
  end.

Definition final_block_flag blk :=
  match blk with
  | FinalBlk _ => Final
  end.

Definition block_size blk : N :=
  match blk with
  | UsedBlk sz_u sz_l => sz_u + sz_l
  | FreeBlk sz => sz
  end.
