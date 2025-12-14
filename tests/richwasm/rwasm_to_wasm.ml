open! Base
open! Stdlib.Format
open! Test_support
module AnnRichWasm = Richwasm_common.Annotated_syntax

include Test_runner.Outputter.Make (struct
  include Test_runner.Outputter.DefaultConfig
  open Test_utils
  open Richwasm_common

  type syntax = Syntax.Module.t
  type text = string
  type res = string

  let syntax_pipeline x =
    x
    |> Richwasm_common.Elaborate.elab_module
    |> or_fail_pp Richwasm_common.Elaborate.Err.pp
    |> Richwasm_common.Main.compile
    |> or_fail_pp Richwasm_common.Extract_compat.CompilerError.pp
    |> Richwasm_common.Main.wasm_ugly_printer

  let string_pipeline s =
    Parsexp.Single.parse_string_exn s
    |> Syntax.Module.t_of_sexp
    |> syntax_pipeline

  let examples = []

  let pp ff x =
    let pretty = true in
    let fmted =
      Wat2wasm.wat2wasm ~check:false x
      |> Result.map_error ~f:(asprintf "wat2wasm(unchecked): %s")
      |> Result.bind ~f:(Wasm2wat.wasm2wat ~pretty ~check:false)
      |> Result.map_error ~f:(asprintf "wasm2wat(unchecked): %s")
      |> or_fail_pp pp_print_string
    in
    fmted
    |> Wat2wasm.wat2wasm
    |> or_fail_pp (fun ff x -> fprintf ff "wat2wasm: %s\n%s" x fmted)
    |> Wasm2wat.pp_as_wat ~pretty ff
end)

let%expect_test "simple cases" =
  output
    {| 
    ((imports ())
       (functions
        (((typ (FunctionType () () ((Num (Int I32)))))
          (locals ())
          (body
           ((NumConst (Int I32) -1)
            (Inject 0
             ((Num (Int I32)) (Num (Int I32)) (Num (Int I32)) (Num (Int I32))))
            (Case (ValType ((Num (Int I32)))) InferFx
             ((Drop (NumConst (Int I32) 0))
              (Drop (NumConst (Int I32) 1))
              (Drop (NumConst (Int I32) 2))
              (Drop (NumConst (Int I32) 3)))))))))
       (table ()) (exports (((name _start) (desc (Func 0))))))
  |};
  [%expect
    {|
    (module
      (type $t0 (func (param i32 i32)))
      (type $t1 (func (param i32) (result i32)))
      (type $t2 (func (param i32 i32 i32)))
      (type $t3 (func (param i32)))
      (type $t4 (func (result i32)))
      (type $t5 (func))
      (type $t6 (func (param i32) (result i32)))
      (type $t7 (func (param i32)))
      (type $t8 (func (param i32)))
      (type $t9 (func (param i32)))
      (type $t10 (func (param i32)))
      (memory $richwasm.mmmem (import "richwasm" "mmmem") 0)
      (memory $richwasm.gcmem (import "richwasm" "gcmem") 0)
      (global $richwasm.tablenext (import "richwasm" "tablenext") (mut i32))
      (func $richwasm.tableset (import "richwasm" "tableset") (type $t0) (param i32 i32))
      (func $richwasm.mmalloc (import "richwasm" "mmalloc") (type $t1) (param i32) (result i32))
      (func $richwasm.gcalloc (import "richwasm" "gcalloc") (type $t1) (param i32) (result i32))
      (func $richwasm.setflag (import "richwasm" "setflag") (type $t2) (param i32 i32 i32))
      (func $richwasm.free (import "richwasm" "free") (type $t3) (param i32))
      (func $richwasm.registerroot (import "richwasm" "registerroot") (type $t1) (param i32) (result i32))
      (func $richwasm.unregisterroot (import "richwasm" "unregisterroot") (type $t3) (param i32))
      (table $richwasm.table (import "richwasm" "table") 0 funcref)
      (func $_start (export "_start") (type $t4) (result i32)
        (local $l0 i32) (local $l1 i32)
        (local.set $l0
          (i32.const 0))
        (i32.const 0)
        (local.set $l1
          (local.get $l0))
        (block $B0 (param i32) (result i32)
          (block $B1 (param i32)
            (block $B2 (param i32)
              (block $B3 (param i32)
                (block $B4 (param i32)
                  (br_table $B1 $B2 $B3 $B4 $B4)
                  (unreachable))
                (drop
                  (local.get $l1))
                (br 4 (;@0;)
                  (i32.const 3)))
              (drop
                (local.get $l1))
              (br 3 (;@0;)
                (i32.const 2)))
            (drop
              (local.get $l1))
            (br 2 (;@0;)
              (i32.const 1)))
          (drop
            (local.get $l1))
          (br 1 (;@0;)
            (i32.const 0))))
      (func $f8 (type $t5)
        (global.set $g1
          (global.get $richwasm.tablenext))
        (global.set $richwasm.tablenext
          (i32.add
            (global.get $g1)
            (i32.const 0))))
      (global $g1 (mut i32) (i32.const 0))
      (start $f8)) |}]
