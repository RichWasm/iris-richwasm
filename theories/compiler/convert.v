Require Import RecordUpdate.RecordUpdate.

From ExtLib.Structures Require Import Monads Reducible.

From stdpp Require Import numbers list.

From Wasm Require datatypes operations.
Require Import Wasm.numerics.

From RichWasm Require Import prelude layout syntax util.
From RichWasm.compiler Require Import prelude codegen util.

Module W. Include Wasm.datatypes <+ Wasm.operations. End W.

Record wordization :=
  { wz_ptrs : list W.localidx;
    wz_nums : list W.localidx }.

Definition wz_empty := {| wz_ptrs := []; wz_nums := [] |}.

Definition wz_of_ptrs (ptrs : list W.localidx) : wordization :=
  {| wz_ptrs := ptrs; wz_nums := [] |}.

Definition wz_of_nums (nums : list W.localidx) : wordization :=
  {| wz_ptrs := []; wz_nums := nums |}.

Definition wz_app (wz1 wz2 : wordization) : wordization :=
  {| wz_ptrs := wz1.(wz_ptrs) ++ wz2.(wz_ptrs);
     wz_nums := wz1.(wz_nums) ++ wz2.(wz_nums) |}.

Definition wz_next_ptr (wz : wordization) : option (W.localidx * wordization) :=
  match wz.(wz_ptrs) with
  | [] => None
  | i :: ixs => Some (i, wz <| wz_ptrs := ixs |>)
  end.

Definition wz_next_num (wz : wordization) : option (W.localidx * wordization) :=
  match wz.(wz_nums) with
  | [] => None
  | i :: ixs => Some (i, wz <| wz_nums := ixs |>)
  end.

Definition split_i64 (fe : function_env) : codegen unit :=
  i ← wlalloc fe W.T_i64;
  emit (W.BI_set_local (localimm i));;

  (* Low *)
  emit (W.BI_get_local (localimm i));;
  emit (W.BI_const (W.VAL_int64 (wasm_extend_u int32_minus_one)));;
  emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_and));;
  emit (W.BI_cvtop W.T_i32 W.CVO_convert W.T_i64 None);;

  (* High *)
  emit (W.BI_get_local (localimm i));;
  emit (W.BI_const (W.VAL_int64 (Wasm_int.int_of_Z i64m 32)));;
  emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_rotr));;
  emit (W.BI_cvtop W.T_i32 W.CVO_convert W.T_i32 None).

Definition join_i64 (fe : function_env) : codegen unit :=
  hi ← wlalloc fe W.T_i32;
  emit (W.BI_set_local (localimm hi));;
  emit (W.BI_cvtop W.T_i64 W.CVO_reinterpret W.T_i32 None);;
  emit (W.BI_get_local (localimm hi));;
  emit (W.BI_cvtop W.T_i64 W.CVO_reinterpret W.T_i32 None);;
  emit (W.BI_const (W.VAL_int64 (Wasm_int.int_of_Z i64m 32)));;
  emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_rotl));;
  emit (W.BI_binop W.T_i64 (W.Binop_i W.BOI_or)).

Definition to_words1 (fe : function_env) (ι : primitive_rep) : codegen wordization :=
  match ι with
  | PtrR => save_stack fe [PtrR] ≫= ret ∘ wz_of_ptrs
  | I32R => save_stack fe [I32R] ≫= ret ∘ wz_of_nums
  | I64R => split_i64 fe;; save_stack fe [I32R; I32R] ≫= ret ∘ wz_of_nums
  | F32R =>
      emit (W.BI_cvtop W.T_i32 W.CVO_reinterpret W.T_f32 None);;
      save_stack fe [I32R] ≫= ret ∘ wz_of_nums
  | F64R =>
      emit (W.BI_cvtop W.T_i64 W.CVO_reinterpret W.T_f64 None);;
      split_i64 fe;;
      save_stack fe [I32R; I32R] ≫= ret ∘ wz_of_nums
  end.

Definition to_words (fe : function_env) (ιs : list primitive_rep) : codegen wordization :=
  foldM (fun ι wz => wz' ← to_words1 fe ι; ret (wz_app wz wz')) (ret wz_empty) ιs.

Definition ptr_from_word (fe : function_env) (wz : wordization) : codegen wordization :=
  match wz_next_ptr wz with
  | None => emit (W.BI_const (W.VAL_int32 (Wasm_int.int_zero i32m)));; ret wz
  | Some (i, wz') => emit (W.BI_get_local (localimm i));; ret wz'
  end.

Definition i32_from_word (fe : function_env) (wz : wordization) :
  codegen wordization :=
  match wz_next_num wz with
  | None => emit (W.BI_const (W.VAL_int32 (Wasm_int.int_zero i32m)));; ret wz
  | Some (i, wz') => emit (W.BI_get_local (localimm i));; ret wz'
  end.

Definition i64_from_words (fe : function_env) (wz : wordization) : codegen wordization :=
  match wz_next_num wz with
  | None => emit (W.BI_const (W.VAL_int64 (Wasm_int.int_zero i64m)));; ret wz
  | Some (i, wz') =>
      emit (W.BI_get_local (localimm i));;
      match wz_next_num wz' with
      | None => emit (W.BI_cvtop W.T_i64 W.CVO_convert W.T_i32 (Some W.SX_U));; ret wz'
      | Some (j, wz'') => emit (W.BI_get_local (localimm j));; join_i64 fe;; ret wz''
      end
  end.

Definition from_words1 (fe : function_env) (wz : wordization) (ι : primitive_rep) :
  codegen wordization :=
  match ι with
  | PtrR => ptr_from_word fe wz
  | I32R => i32_from_word fe wz
  | I64R => i64_from_words fe wz
  | F32R =>
      wz' ← i32_from_word fe wz;
      emit (W.BI_cvtop W.T_f32 W.CVO_reinterpret W.T_i32 None);;
      ret wz'
  | F64R =>
      wz' ← i64_from_words fe wz;
      emit (W.BI_cvtop W.T_f64 W.CVO_reinterpret W.T_i64 None);;
      ret wz'
  end.

Definition from_words (fe : function_env) (wz : wordization) (ιs : list primitive_rep) :
  codegen unit :=
  ignore (foldM (fun ι wz => wz' ← from_words1 fe wz ι; ret wz') (ret wz) ιs).
