From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From Wasm.iris.logrel Require Export iris_fundamental.
From Wasm.iris.rules Require Export proofmode.
From RWasm.iris.allocator Require Export allocator_common misc_relocate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(*
IDEA
We are given an entire WebAssembly memory to work with.
[0   ......   mem_size - 1]

This memory is partitioned into a circular linked list of blocks.

enum state_t ::= FREE | USED | FINAL

struct block_t {
  state_t   state;
  i32       size; // must be nonzero
  i32       next;
  u8[size]  data; // user data
}

INITIAL STATE
If the memory has size mem_size,
put a block at address 0:
  { state = FINAL; next = 0; size = mem_size - 12 }

INVARIANTS
The first block is always at address 0.
The last block has next = 0.
If the last block is at address K, it occupies [ K ... mem_size - 1 ].
The last block is the unique block marked FINAL and never contains user data.

GROWING THE MEMORY
pinch_block(final_block, reqd_sz):
  new_total_sz = reqd_sz + 12
  new_block = final_block + new_total_sz

  final_block.size = reqd_sz
  final_block.state = FREE
  final_block.next = new_block

  new_block.state = FINAL
  new_block.size = final_block.size - new_total_sz
  new_block.next = 0

new_block(final_block, reqd_sz):
  if final_block.sz > reqd_sz + 12:
    return pinch_block(final_block, reqd_sz)
  else:
    final_block.state = FREE
    final_block.next = mem_size
    new_block = grow_mem(reqd_sz)
    if new_block == -1:
      return -1
    else:
      new_block.state = FINAL
      new_block.size = actual_sz
      final_block.next = new_block
      pinch_block(new_block, reqd_sz)

MALLOC
malloc(reqd_sz):
  b = 0
  while b.state != FINAL:
    if b.sz > reqd_sz && b.state == FREE:
       b.state = USED
       return b.data
    else:
       b = b.next
  // b is the final block
  new_block(b, reqd_sz) // will cause a return -1 if grow_memory fails
  b.state = USED
  return b.data

FREE
free(addr):
  if addr < 12:
    trap
  reqd_block = addr - 12
  b = 0
  while b.state != STOP:
    if b == reqd_block && b.state = USED:
      b.state = FREE
    else:
      b = b.next
  // address wasn't the address of a known allocation
  trap

*)
  
Definition get_state blk :=
  BI_get_local blk ::
  BI_load T_i32 None 0%N state_off ::
  nil.

Definition get_next blk :=
  BI_get_local blk ::
  BI_load T_i32 None 0%N next_off ::
  nil.

(* compute data pointer *)
Definition get_data blk :=
  BI_get_local blk ::
  u32const data_off ::
  BI_binop T_i32 (Binop_i BOI_add) ::
  nil.

Definition set_next :=
  [BI_store T_i32 None 0%N next_off].

(* this is the size of the data segment of the block *)
Definition get_size blk :=
  BI_get_local blk ::
  BI_load T_i32 None 0%N size_off ::
  nil.
  
Definition set_size :=
  [BI_store T_i32 None 0%N size_off].

Definition add_hdr_sz :=
  u32const blk_hdr_sz ::
  BI_binop T_i32 (Binop_i BOI_add) ::
  nil.

Definition sub_hdr_sz :=
  u32const blk_hdr_sz ::
  BI_binop T_i32 (Binop_i BOI_sub) ::
  nil.

(* this is the size of the whole block, including header! *)
Definition get_total_size blk :=
  get_size blk ++
  add_hdr_sz.

Definition mark_free blk :=
  [
    BI_get_local blk;
    u32const BLK_FREE;
    BI_store T_i32 None 0%N 0%N
  ].

Definition mark_used blk :=
  [
    BI_get_local blk;
    u32const BLK_USED;
    BI_store T_i32 None 0%N 0%N
  ].

Definition mark_final blk :=
  [
    BI_get_local blk;
    u32const BLK_FINAL;
    BI_store T_i32 None 0%N 0%N
  ].


Definition is_block_nonfinal blk :=
  get_state blk ++
  u32const BLK_FINAL ::
  BI_relop T_i32 (Relop_i ROI_ne) ::
  nil.

Definition is_block_free blk :=
  get_state blk ++
  u32const BLK_FREE ::
  BI_relop T_i32 (Relop_i ROI_eq) ::
  nil.

(*
  pinch_block final sz 
  locals declared: [i32]

  Take a final block of size M
    [hdr| M...                  ]
  and pinch off a new one of a given size N < M - 12. The leftovers become
  the new final block.
    [hdr| N ][hdr| ...          ]
  Returns the address of the new block.

  Parameters/Locals:
  0     rw, pointer to the final block.
  1     ro, requested size to pinch off.
  2     rw, storing the total size (incl headers) of the pinched block.
  3     rw, storing the address of the new final block.
*)
Definition pinch_block final_block reqd_sz old_sz new_block :=
  (* save size of entire block *)
   (get_size final_block ++
   BI_set_local old_sz ::
   nil) ++ 
  (* compute address of new final block *)
  ([BI_get_local final_block;
    BI_get_local reqd_sz] ++
   add_hdr_sz ++
   [BI_binop T_i32 (Binop_i BOI_add)]) ++
   (([BI_set_local new_block]) ++
  (* set up pinched block *)
  (BI_get_local final_block ::
   BI_get_local reqd_sz ::
   set_size ++
   mark_free final_block ++
   BI_get_local final_block ::
   BI_get_local new_block ::
   set_next)) ++
  (* set up new block's header *)
  mark_final new_block ++
  (* set new block size *)
  (BI_get_local new_block ::
   (* compute block size on top of stack *)
   BI_get_local old_sz ::
   BI_get_local reqd_sz :: 
   add_hdr_sz ++
   BI_binop T_i32 (Binop_i BOI_sub) ::
   (* write top of stack to $3.size *)
   set_size) ++
  (* new_block.next = 0 *)
  (BI_get_local new_block :: u32const 0%N :: set_next).


Definition mul_page_sz :=
  [u32const Wasm.operations.page_size;
   BI_binop T_i32 (Binop_i BOI_mul)].

Definition mul_var_page_sz var :=
  BI_get_local var ::
  mul_page_sz ++
  [BI_set_local var].

(*
  new_block: [i32; i32] -> [i32]
  Returns address of a block at least the requested size
  Parameters/Locals:
  0     parameter, pointer to final_block
  1     parameter, requested size
  2     local, actual size allocated
*)
Definition new_block final_block reqd_sz old_sz new_block actual_size :=
  BI_get_local reqd_sz ::
  add_hdr_sz ++
  get_size final_block ++
  BI_relop T_i32 (Relop_i (ROI_lt SX_U)) ::
  BI_if (Tf [] [])
    (* then *)
    (pinch_block final_block reqd_sz old_sz new_block)
    (* else *)
    (BI_get_local reqd_sz ::
     add_hdr_sz ++
     u32const Wasm.operations.page_size ::
     BI_binop T_i32 (Binop_i (BOI_div SX_U)) ::
     u32const 1%N ::
     BI_binop T_i32 (Binop_i BOI_add) ::
     BI_tee_local actual_size ::
     BI_grow_memory ::
     BI_set_local new_block ::
     BI_get_local new_block ::
     BI_const (VAL_int32 int32_minus_one) ::
     BI_relop T_i32 (Relop_i ROI_eq) ::
     BI_if (Tf [] [])
       [BI_const (VAL_int32 int32_minus_one);
        BI_unreachable]
       (mark_free final_block ++
        (* convert from pages to bytes *)
        mul_var_page_sz new_block ++
        mul_var_page_sz actual_size ++

        BI_get_local final_block ::
        BI_get_local new_block ::
        set_next ++

        BI_get_local new_block ::
        BI_get_local actual_size ::
        set_size ++

        pinch_block final_block reqd_sz old_sz new_block) :: nil) :: nil.

Definition malloc_loop_body reqd_sz cur_block :=
  (* break out of the loop if the block is final. *)
  is_block_nonfinal cur_block ++
  BI_br_if 1 ::
  (* Check if the block fits and is free. *)
  (* put the free flag at the top of the stack*)
  is_block_free cur_block ++
  (* Put a boolean representing whether the size is big enough at the top of the stack *)
  BI_get_local reqd_sz ::
  get_size cur_block ++ 
  BI_relop T_i32 (Relop_i (ROI_le SX_U)) ::
  (* Compute free && fits *)
  BI_binop T_i32 (Binop_i BOI_and) ::
  [BI_if (Tf [] []) 
    (* it's free and it fits, mark block as not free and return start *)
    (mark_used cur_block ++
     get_data cur_block ++ 
     [BI_return]) 
    (* if it isn't free or doesn't fit, try the next block *)
    (get_next cur_block ++
     [BI_set_local cur_block])]
  .

Definition malloc_body reqd_sz cur_block tmp1 tmp2 tmp3 :=
  (* Location of first block in the free list. *)
  i32const 0 ::
  (* Store the current block. *)
  BI_set_local cur_block ::
  BI_loop (Tf [] []) (malloc_loop_body reqd_sz cur_block) ::
  (* OK, we are at the end of the list! *)
  new_block cur_block reqd_sz tmp1 tmp2 tmp3 ++
  mark_used cur_block ++
  BI_get_local cur_block ::
  BI_return ::
  nil.
  
(*
  malloc: [i32] -> [i32]
  locals declared: [i32]

  Allocate a new block of memory of the requested size.
*)
Definition malloc :=
  malloc_body 0 1 2 3.

Definition free_body data_ptr :=
  BI_get_local data_ptr ::
  sub_hdr_sz ++
  BI_set_local data_ptr ::
  mark_free data_ptr ++
  BI_return ::
  nil.

Definition free :=
  free_body 0.
