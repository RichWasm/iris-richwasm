open! Base
open! Stdlib.Format
open! Test_support
module AnnRichWasm = Richwasm_common.Annotated_syntax

include Test_runner.MultiOutputter.Make (struct
  include Test_runner.MultiOutputter.DefaultConfig
  open Test_utils
  open Richwasm_lin_lang

  type syntax = Syntax.Module.t
  type text = string
  type res = string

  let elab x =
    x
    |> Richwasm_common.Elaborate.elab_module
    |> or_fail_pp Richwasm_common.Elaborate.Err.pp
    |> Richwasm_common.Main.compile
    |> or_fail_pp Richwasm_common.Main.pp_compile_err
    |> Richwasm_common.Main.wasm_ugly_printer

  let syntax_pipeline x =
    x |> Main.compile_ast |> or_fail_pp Main.CompileErr.pp |> elab

  let string_pipeline s = s |> Parse.from_string_exn |> syntax_pipeline
  let examples = Test_examples.Lin_lang.all

  let pp ff x =
    match Meta.Wat2wasm.wat2wasm x with
    | Ok wasm -> Meta.Wasm2wat.pp_as_wat ff wasm
    | Error err -> fprintf ff "wat2wasm Error: %s" err

  let pp_raw ff x = fprintf ff "%s" x
end)

let%expect_test "simple programs" =
  run {| 1 |};
  [%expect
    {|
      (module
        (type (;0;) (func (param i32 i32)))
        (type (;1;) (func (param i32) (result i32)))
        (type (;2;) (func (param i32 i32 i32)))
        (type (;3;) (func (param i32)))
        (type (;4;) (func (result i32)))
        (type (;5;) (func))
        (import "richwasm" "mmmem" (memory (;0;) 0))
        (import "richwasm" "gcmem" (memory (;1;) 0))
        (import "richwasm" "tablenext" (global (;0;) (mut i32)))
        (import "richwasm" "tableset" (func (;0;) (type 0)))
        (import "richwasm" "mmalloc" (func (;1;) (type 1)))
        (import "richwasm" "gcalloc" (func (;2;) (type 1)))
        (import "richwasm" "setflag" (func (;3;) (type 2)))
        (import "richwasm" "free" (func (;4;) (type 3)))
        (import "richwasm" "registerroot" (func (;5;) (type 1)))
        (import "richwasm" "unregisterroot" (func (;6;) (type 3)))
        (import "richwasm" "table" (table (;0;) 0 funcref))
        (func (;7;) (type 4) (result i32)
          i32.const 1)
        (func (;8;) (type 5)
          global.get 0
          global.set 1
          global.get 1
          i32.const 0
          i32.add
          global.set 0)
        (global (;1;) (mut i32) (i32.const 0))
        (export "" (func 7))
        (start 8)) |}];
  next ();
  [%expect
    {| (module (import "richwasm" "mmmem"(memory 0))(import "richwasm" "gcmem"(memory 0))(import "richwasm" "tablenext"(global (mut i32)))(import "richwasm" "tableset"(func (type 0)))(import "richwasm" "mmalloc"(func (type 1)))(import "richwasm" "gcalloc"(func (type 1)))(import "richwasm" "setflag"(func (type 2)))(import "richwasm" "free"(func (type 3)))(import "richwasm" "registerroot"(func (type 1)))(import "richwasm" "unregisterroot"(func (type 3)))(import "richwasm" "table"(table 0 funcref))(func (type 4) (local ) i32.const 1)(func (type 5) (local ) global.get 0 global.set 1 global.get 1 i32.const 0 i32.add global.set 0)(global (mut i32) i32.const 0)(start 8)(export "" (func 7))(type (func (param i32 i32) (result )))(type (func (param i32) (result i32)))(type (func (param i32 i32 i32) (result )))(type (func (param i32) (result )))(type (func (param ) (result i32)))(type (func (param ) (result )))) |}]

let%expect_test "examples" =
  output_examples ();
  [%expect
    {|
    -----------one-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (result i32)))
      (type (;5;) (func))
      (import "richwasm" "mmmem" (memory (;0;) 0))
      (import "richwasm" "gcmem" (memory (;1;) 0))
      (import "richwasm" "tablenext" (global (;0;) (mut i32)))
      (import "richwasm" "tableset" (func (;0;) (type 0)))
      (import "richwasm" "mmalloc" (func (;1;) (type 1)))
      (import "richwasm" "gcalloc" (func (;2;) (type 1)))
      (import "richwasm" "setflag" (func (;3;) (type 2)))
      (import "richwasm" "free" (func (;4;) (type 3)))
      (import "richwasm" "registerroot" (func (;5;) (type 1)))
      (import "richwasm" "unregisterroot" (func (;6;) (type 3)))
      (import "richwasm" "table" (table (;0;) 0 funcref))
      (func (;7;) (type 4) (result i32)
        i32.const 1)
      (func (;8;) (type 5)
        global.get 0
        global.set 1
        global.get 1
        i32.const 0
        i32.add
        global.set 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "" (func 7))
      (start 8))

    -----------flat_tuple-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (result i32 i32 i32 i32)))
      (type (;5;) (func))
      (import "richwasm" "mmmem" (memory (;0;) 0))
      (import "richwasm" "gcmem" (memory (;1;) 0))
      (import "richwasm" "tablenext" (global (;0;) (mut i32)))
      (import "richwasm" "tableset" (func (;0;) (type 0)))
      (import "richwasm" "mmalloc" (func (;1;) (type 1)))
      (import "richwasm" "gcalloc" (func (;2;) (type 1)))
      (import "richwasm" "setflag" (func (;3;) (type 2)))
      (import "richwasm" "free" (func (;4;) (type 3)))
      (import "richwasm" "registerroot" (func (;5;) (type 1)))
      (import "richwasm" "unregisterroot" (func (;6;) (type 3)))
      (import "richwasm" "table" (table (;0;) 0 funcref))
      (func (;7;) (type 4) (result i32 i32 i32 i32)
        i32.const 1
        i32.const 2
        i32.const 3
        i32.const 4
        nop)
      (func (;8;) (type 5)
        global.get 0
        global.set 1
        global.get 1
        i32.const 0
        i32.add
        global.set 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "" (func 7))
      (start 8))

    -----------nested_tuple-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (result i32 i32 i32 i32)))
      (type (;5;) (func))
      (import "richwasm" "mmmem" (memory (;0;) 0))
      (import "richwasm" "gcmem" (memory (;1;) 0))
      (import "richwasm" "tablenext" (global (;0;) (mut i32)))
      (import "richwasm" "tableset" (func (;0;) (type 0)))
      (import "richwasm" "mmalloc" (func (;1;) (type 1)))
      (import "richwasm" "gcalloc" (func (;2;) (type 1)))
      (import "richwasm" "setflag" (func (;3;) (type 2)))
      (import "richwasm" "free" (func (;4;) (type 3)))
      (import "richwasm" "registerroot" (func (;5;) (type 1)))
      (import "richwasm" "unregisterroot" (func (;6;) (type 3)))
      (import "richwasm" "table" (table (;0;) 0 funcref))
      (func (;7;) (type 4) (result i32 i32 i32 i32)
        i32.const 1
        i32.const 2
        nop
        i32.const 3
        i32.const 4
        nop
        nop)
      (func (;8;) (type 5)
        global.get 0
        global.set 1
        global.get 1
        i32.const 0
        i32.add
        global.set 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "" (func 7))
      (start 8))

    -----------single_sum-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (result i32)))
      (type (;5;) (func))
      (import "richwasm" "mmmem" (memory (;0;) 0))
      (import "richwasm" "gcmem" (memory (;1;) 0))
      (import "richwasm" "tablenext" (global (;0;) (mut i32)))
      (import "richwasm" "tableset" (func (;0;) (type 0)))
      (import "richwasm" "mmalloc" (func (;1;) (type 1)))
      (import "richwasm" "gcalloc" (func (;2;) (type 1)))
      (import "richwasm" "setflag" (func (;3;) (type 2)))
      (import "richwasm" "free" (func (;4;) (type 3)))
      (import "richwasm" "registerroot" (func (;5;) (type 1)))
      (import "richwasm" "unregisterroot" (func (;6;) (type 3)))
      (import "richwasm" "table" (table (;0;) 0 funcref))
      (func (;7;) (type 4) (result i32)
        nop
        i32.const 0)
      (func (;8;) (type 5)
        global.get 0
        global.set 1
        global.get 1
        i32.const 0
        i32.add
        global.set 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "" (func 7))
      (start 8))

    -----------double_sum-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (result i32 i32)))
      (type (;5;) (func))
      (import "richwasm" "mmmem" (memory (;0;) 0))
      (import "richwasm" "gcmem" (memory (;1;) 0))
      (import "richwasm" "tablenext" (global (;0;) (mut i32)))
      (import "richwasm" "tableset" (func (;0;) (type 0)))
      (import "richwasm" "mmalloc" (func (;1;) (type 1)))
      (import "richwasm" "gcalloc" (func (;2;) (type 1)))
      (import "richwasm" "setflag" (func (;3;) (type 2)))
      (import "richwasm" "free" (func (;4;) (type 3)))
      (import "richwasm" "registerroot" (func (;5;) (type 1)))
      (import "richwasm" "unregisterroot" (func (;6;) (type 3)))
      (import "richwasm" "table" (table (;0;) 0 funcref))
      (func (;7;) (type 4) (result i32 i32)
        (local i32)
        i32.const 15
        local.set 0
        i32.const 1
        local.get 0)
      (func (;8;) (type 5)
        global.get 0
        global.set 1
        global.get 1
        i32.const 0
        i32.add
        global.set 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "" (func 7))
      (start 8))

    -----------arith_add-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (result i32)))
      (type (;5;) (func))
      (import "richwasm" "mmmem" (memory (;0;) 0))
      (import "richwasm" "gcmem" (memory (;1;) 0))
      (import "richwasm" "tablenext" (global (;0;) (mut i32)))
      (import "richwasm" "tableset" (func (;0;) (type 0)))
      (import "richwasm" "mmalloc" (func (;1;) (type 1)))
      (import "richwasm" "gcalloc" (func (;2;) (type 1)))
      (import "richwasm" "setflag" (func (;3;) (type 2)))
      (import "richwasm" "free" (func (;4;) (type 3)))
      (import "richwasm" "registerroot" (func (;5;) (type 1)))
      (import "richwasm" "unregisterroot" (func (;6;) (type 3)))
      (import "richwasm" "table" (table (;0;) 0 funcref))
      (func (;7;) (type 4) (result i32)
        i32.const 9
        i32.const 10
        i32.add)
      (func (;8;) (type 5)
        global.get 0
        global.set 1
        global.get 1
        i32.const 0
        i32.add
        global.set 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "" (func 7))
      (start 8))

    -----------arith_sub-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (result i32)))
      (type (;5;) (func))
      (import "richwasm" "mmmem" (memory (;0;) 0))
      (import "richwasm" "gcmem" (memory (;1;) 0))
      (import "richwasm" "tablenext" (global (;0;) (mut i32)))
      (import "richwasm" "tableset" (func (;0;) (type 0)))
      (import "richwasm" "mmalloc" (func (;1;) (type 1)))
      (import "richwasm" "gcalloc" (func (;2;) (type 1)))
      (import "richwasm" "setflag" (func (;3;) (type 2)))
      (import "richwasm" "free" (func (;4;) (type 3)))
      (import "richwasm" "registerroot" (func (;5;) (type 1)))
      (import "richwasm" "unregisterroot" (func (;6;) (type 3)))
      (import "richwasm" "table" (table (;0;) 0 funcref))
      (func (;7;) (type 4) (result i32)
        i32.const 67
        i32.const 41
        i32.sub)
      (func (;8;) (type 5)
        global.get 0
        global.set 1
        global.get 1
        i32.const 0
        i32.add
        global.set 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "" (func 7))
      (start 8))

    -----------arith_mul-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (result i32)))
      (type (;5;) (func))
      (import "richwasm" "mmmem" (memory (;0;) 0))
      (import "richwasm" "gcmem" (memory (;1;) 0))
      (import "richwasm" "tablenext" (global (;0;) (mut i32)))
      (import "richwasm" "tableset" (func (;0;) (type 0)))
      (import "richwasm" "mmalloc" (func (;1;) (type 1)))
      (import "richwasm" "gcalloc" (func (;2;) (type 1)))
      (import "richwasm" "setflag" (func (;3;) (type 2)))
      (import "richwasm" "free" (func (;4;) (type 3)))
      (import "richwasm" "registerroot" (func (;5;) (type 1)))
      (import "richwasm" "unregisterroot" (func (;6;) (type 3)))
      (import "richwasm" "table" (table (;0;) 0 funcref))
      (func (;7;) (type 4) (result i32)
        i32.const 42
        i32.const 10
        i32.mul)
      (func (;8;) (type 5)
        global.get 0
        global.set 1
        global.get 1
        i32.const 0
        i32.add
        global.set 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "" (func 7))
      (start 8))

    -----------arith_div-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (result i32)))
      (type (;5;) (func))
      (import "richwasm" "mmmem" (memory (;0;) 0))
      (import "richwasm" "gcmem" (memory (;1;) 0))
      (import "richwasm" "tablenext" (global (;0;) (mut i32)))
      (import "richwasm" "tableset" (func (;0;) (type 0)))
      (import "richwasm" "mmalloc" (func (;1;) (type 1)))
      (import "richwasm" "gcalloc" (func (;2;) (type 1)))
      (import "richwasm" "setflag" (func (;3;) (type 2)))
      (import "richwasm" "free" (func (;4;) (type 3)))
      (import "richwasm" "registerroot" (func (;5;) (type 1)))
      (import "richwasm" "unregisterroot" (func (;6;) (type 3)))
      (import "richwasm" "table" (table (;0;) 0 funcref))
      (func (;7;) (type 4) (result i32)
        i32.const 0
        i32.const 10
        i32.div_s)
      (func (;8;) (type 5)
        global.get 0
        global.set 1
        global.get 1
        i32.const 0
        i32.add
        global.set 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "" (func 7))
      (start 8))

    -----------app_ident-----------
    FAILURE (PopEmptyStack LocalSet)
    -----------nested_arith-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (result i32)))
      (type (;5;) (func))
      (import "richwasm" "mmmem" (memory (;0;) 0))
      (import "richwasm" "gcmem" (memory (;1;) 0))
      (import "richwasm" "tablenext" (global (;0;) (mut i32)))
      (import "richwasm" "tableset" (func (;0;) (type 0)))
      (import "richwasm" "mmalloc" (func (;1;) (type 1)))
      (import "richwasm" "gcalloc" (func (;2;) (type 1)))
      (import "richwasm" "setflag" (func (;3;) (type 2)))
      (import "richwasm" "free" (func (;4;) (type 3)))
      (import "richwasm" "registerroot" (func (;5;) (type 1)))
      (import "richwasm" "unregisterroot" (func (;6;) (type 3)))
      (import "richwasm" "table" (table (;0;) 0 funcref))
      (func (;7;) (type 4) (result i32)
        i32.const 9
        i32.const 10
        i32.add
        i32.const 5
        i32.mul)
      (func (;8;) (type 5)
        global.get 0
        global.set 1
        global.get 1
        i32.const 0
        i32.add
        global.set 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "" (func 7))
      (start 8))

    -----------let_bind-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (result i32)))
      (type (;5;) (func))
      (import "richwasm" "mmmem" (memory (;0;) 0))
      (import "richwasm" "gcmem" (memory (;1;) 0))
      (import "richwasm" "tablenext" (global (;0;) (mut i32)))
      (import "richwasm" "tableset" (func (;0;) (type 0)))
      (import "richwasm" "mmalloc" (func (;1;) (type 1)))
      (import "richwasm" "gcalloc" (func (;2;) (type 1)))
      (import "richwasm" "setflag" (func (;3;) (type 2)))
      (import "richwasm" "free" (func (;4;) (type 3)))
      (import "richwasm" "registerroot" (func (;5;) (type 1)))
      (import "richwasm" "unregisterroot" (func (;6;) (type 3)))
      (import "richwasm" "table" (table (;0;) 0 funcref))
      (func (;7;) (type 4) (result i32)
        (local i32)
        i32.const 10
        local.set 0
        local.get 0)
      (func (;8;) (type 5)
        global.get 0
        global.set 1
        global.get 1
        i32.const 0
        i32.add
        global.set 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "" (func 7))
      (start 8))

    -----------add_one_program-----------
    FAILURE (TODO pack)
    -----------add_tup_ref-----------
    wat2wasm Error: -:1:1115: error: type mismatch in local.set, expected [i32] but got []
    ... local.tee 9 end end local.set 3 local.set 10 local.get 10 i32.const 1 i32...
                                        ^^^^^^^^^

    -----------print_10-----------
    FAILURE (InvalidTableIdx 0)
    -----------factorial_program-----------
    FAILURE (TODO pack)
    -----------safe_div-----------
    FAILURE (TODO elab_local_fx)
    -----------incr_n-----------
    FAILURE (TODO pack)
    -----------fix_factorial[invalid]-----------
    FAILURE (PopEmptyStack LocalSet)
    -----------unboxed_list[invalid]-----------
    FAILURE (Codegen
     (CannotResolveRepOfRecTypeWithoutIndirection (Var (0 ("\206\177")))))
    -----------boxed_list-----------
    FAILURE (PopEmptyStack LocalSet)
    -----------peano_3-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (result i32 i32)))
      (type (;5;) (func))
      (import "richwasm" "mmmem" (memory (;0;) 0))
      (import "richwasm" "gcmem" (memory (;1;) 0))
      (import "richwasm" "tablenext" (global (;0;) (mut i32)))
      (import "richwasm" "tableset" (func (;0;) (type 0)))
      (import "richwasm" "mmalloc" (func (;1;) (type 1)))
      (import "richwasm" "gcalloc" (func (;2;) (type 1)))
      (import "richwasm" "setflag" (func (;3;) (type 2)))
      (import "richwasm" "free" (func (;4;) (type 3)))
      (import "richwasm" "registerroot" (func (;5;) (type 1)))
      (import "richwasm" "unregisterroot" (func (;6;) (type 3)))
      (import "richwasm" "table" (table (;0;) 0 funcref))
      (func (;7;) (type 4) (result i32 i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        nop
        i32.const 0
        local.get 0
        local.set 2
        local.set 1
        i32.const 2
        call 1
        local.set 3
        local.get 3
        i32.const 0
        i32.const 0
        call 3
        local.get 3
        i32.const 1
        i32.const 1
        call 3
        local.get 3
        local.get 2
        i32.store offset=3 align=2
        local.get 3
        local.get 1
        i32.store offset=7 align=2
        local.get 3
        local.set 4
        i32.const 1
        local.get 4
        local.set 6
        local.set 5
        i32.const 2
        call 1
        local.set 7
        local.get 7
        i32.const 0
        i32.const 0
        call 3
        local.get 7
        i32.const 1
        i32.const 1
        call 3
        local.get 7
        local.get 6
        i32.store offset=3 align=2
        local.get 7
        local.get 5
        i32.store offset=7 align=2
        local.get 7
        local.set 8
        i32.const 1
        local.get 8
        local.set 10
        local.set 9
        i32.const 2
        call 1
        local.set 11
        local.get 11
        i32.const 0
        i32.const 0
        call 3
        local.get 11
        i32.const 1
        i32.const 1
        call 3
        local.get 11
        local.get 10
        i32.store offset=3 align=2
        local.get 11
        local.get 9
        i32.store offset=7 align=2
        local.get 11
        local.set 12
        i32.const 1
        local.get 12)
      (func (;8;) (type 5)
        global.get 0
        global.set 1
        global.get 1
        i32.const 0
        i32.add
        global.set 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "" (func 7))
      (start 8))

    -----------peano-----------
    FAILURE (TODO elab_local_fx)
    -----------mini_zip-----------
    FAILURE (TODO pack) |}]
