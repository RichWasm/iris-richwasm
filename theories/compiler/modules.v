From Coq Require Import List.
Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Import Coq.Lists.List.ListNotations.
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinInt.
Local Open Scope program_scope.

Require Import mathcomp.ssreflect.seq.

From stdpp Require Import -(notations) list_numbers pretty.

From ExtLib.Structures Require Import Functor Monads Reducible Traversable.
Import FunctorNotation.
Import MonadNotation.
Local Open Scope monad.
From ExtLib.Data Require Import List.
From ExtLib.Data.Monads Require Import EitherMonad StateMonad WriterMonad.

From Wasm Require datatypes operations.
Require Import Wasm.numerics.

From RichWasm Require term.
From RichWasm Require Import typing.
Require Import RichWasm.util.dlist.
Import RichWasm.util.dlist.Notation.
From RichWasm.compiler Require Import error functions numerics types.

Module R := term.
Module W := datatypes.

Definition compile_fun_type_idx (fun_type : R.FunType) : W.typeidx.
Admitted.

Definition funcidx_table_write : W.immediate := 0.

Definition typeidx_start : W.immediate := 0.

Definition typeidx_table_write : W.immediate := 1.

Definition globidx_table_next : W.immediate := 0.

Definition globidx_table_offset : W.immediate := 1.

Definition compile_table_elem (start : W.immediate) (i funcidx : nat) : W.expr :=
  [ W.BI_get_local start;
    W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat i)));
    W.BI_binop W.T_i32 (W.Binop_i W.BOI_add);
    W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat funcidx)));
    W.BI_call funcidx_table_write ].

Definition compile_start (table : R.Table) : W.module_func :=
  {| W.modfunc_type := W.Mk_typeidx typeidx_start;
     W.modfunc_locals := [];
     W.modfunc_body :=
       [ (* Remember the starting index of our section in the table. *)
         W.BI_get_global globidx_table_next;
         W.BI_set_global globidx_table_offset;
         (* Increment the index for the next module to use the table. *)
         W.BI_get_global globidx_table_offset;
         W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (length table))));
         W.BI_binop W.T_i32 (W.Binop_i W.BOI_add);
         W.BI_set_global globidx_table_next ] ++
       flatten (imap (compile_table_elem 0) table) |}.

Fixpoint compile_module (module : R.module TyAnn) : error + W.module :=
  let '(funcs, globs, table) := module in
  inr {|
    W.mod_types := []; (* TODO *)
    W.mod_funcs := []; (* TODO *)
    W.mod_tables := []; (* TODO *)
    W.mod_mems := []; (* TODO *)
    W.mod_globals := (* TODO *)
      [ W.Build_module_glob
          (W.Build_global_type W.MUT_mut W.T_i32)
          [ W.BI_const (W.VAL_int32 (Wasm_int.int_of_Z i32m 0)) ] ];
    W.mod_elem := []; (* TODO *)
    W.mod_data := []; (* TODO *)
    W.mod_start := Some (W.Build_module_start (W.Mk_funcidx 0)); (* TODO *)
    W.mod_imports := (* TODO *)
      [ W.Build_module_import
          (String.list_byte_of_string "RichWasm")
          (String.list_byte_of_string "modify_table")
          (W.ID_func typeidx_table_write) ];
    W.mod_exports := [] (* TODO *)
  |}

(* TODO: modfunc_type expects a typeidx while rwasm does this inline *)
with compile_func (func : R.Func TyAnn) : option W.module_func :=
  match func with
  | R.Fun exports fun_type sizes intrs =>
    Some {|
      W.modfunc_type := compile_fun_type_idx fun_type;
      W.modfunc_locals := []; (* TODO *)
      W.modfunc_body := []; (* TODO *)
    |}
  end

with compile_glob (glob : R.Glob TyAnn) : error + W.module_glob
with compile_table (table : R.Table) : error + W.module_table.
Admitted.
