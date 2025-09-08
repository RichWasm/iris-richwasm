From Stdlib Require Import List.
Import ListNotations.
Require Import Stdlib.Strings.String.
Require Import Stdlib.ZArith.BinInt.

Require Import mathcomp.ssreflect.seq.

Require Import stdpp.list_numbers.

Require Wasm.datatypes.
Require Import Wasm.numerics.

From RichWasm Require Import syntax typing.
From RichWasm.compiler Require Import types util.

Module W := Wasm.datatypes.

Definition funcidx_table_set : W.immediate := 0.

Definition typeidx_nil_to_nil : W.immediate := 0.
Definition typeidx_i32_i32_to_nil : W.immediate := 1.

Definition globidx_table_next : W.immediate := 0.
Definition globidx_table_offset : W.immediate := 1.

Definition fe_of_contexts (F : function_ctx) (L : local_ctx) : option function_env :=
  ts ← mapM (fun τ => type_rep F.(fc_type_vars) τ ≫= translate_rep) L;
  mret {| fe_return_type := F.(fc_return_type);
          fe_type_vars := F.(fc_type_vars);
          fe_wlocal_offset := sum_list_with length ts |}.

Definition set_table_elem (start : W.immediate) (i f : nat) : W.expr :=
  [W.BI_get_local start;
   W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat i)));
   W.BI_binop W.T_i32 (W.Binop_i W.BOI_add);
   W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat f)));
   W.BI_call funcidx_table_set].

Definition start_func (table : list nat) : W.module_func :=
  {| W.modfunc_type := W.Mk_typeidx typeidx_nil_to_nil;
     W.modfunc_locals := [];
     W.modfunc_body :=
       [
         (* Remember the starting index of our section in the table. *)
         W.BI_get_global globidx_table_next;
         W.BI_set_global globidx_table_offset;
         (* Increment the index for the next module to use the table. *)
         W.BI_get_global globidx_table_offset;
         W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (length table))));
         W.BI_binop W.T_i32 (W.Binop_i W.BOI_add);
         W.BI_set_global globidx_table_next
       ] ++
       flatten (imap (set_table_elem 0) table) |}.

(* TODO: modfunc_type expects a typeidx while rwasm does this inline *)
Definition compile_func (func : module_function) : error + W.module_func :=
  inr {|
    W.modfunc_type := W.Mk_typeidx 0; (* TODO *)
    W.modfunc_locals := []; (* TODO *)
    W.modfunc_body := []; (* TODO *)
  |}.

Definition compile_module (module : module) : error + W.module :=
  let globals :=
    (* TODO *)
    [W.Build_module_glob
       (W.Build_global_type W.MUT_mut W.T_i32)
       [W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m 0))]]
  in
  let imports :=
    (* TODO *)
    [W.Build_module_import
       (String.list_byte_of_string "RichWasm")
       (String.list_byte_of_string "table_set")
       (W.ID_func typeidx_i32_i32_to_nil)]
  in
  inr {|
    W.mod_types := []; (* TODO *)
    W.mod_funcs := []; (* TODO *)
    W.mod_tables := []; (* TODO *)
    W.mod_mems := []; (* TODO *)
    W.mod_globals := globals;
    W.mod_elem := []; (* TODO *)
    W.mod_data := []; (* TODO *)
    W.mod_start := Some (W.Build_module_start (W.Mk_funcidx 0));
    W.mod_imports := imports;
    W.mod_exports := [] (* TODO *)
  |}.
