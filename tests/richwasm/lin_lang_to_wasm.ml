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
    |> or_fail_pp Richwasm_common.Extract_compat.CompilerError.pp
    |> Richwasm_common.Main.wasm_ugly_printer

  let syntax_pipeline x =
    x |> Main.compile_ast |> or_fail_pp Main.CompileErr.pp |> elab

  let string_pipeline s = s |> Parse.from_string_exn |> syntax_pipeline
  let examples = Test_examples.Lin_lang.all

  let pp ff x =
    match Wat2wasm.wat2wasm x with
    | Ok wasm -> Wasm2wat.pp_as_wat ff wasm
    | Error _ ->
        fprintf ff "FAILURE wat2wasm2wat validation!@.";
        (match Wat2wasm.wat2wasm ~check:false x with
        | Ok wasm ->
            (match Wasm2wat.wasm2wat ~check:false wasm with
            | Ok wat ->
                let err =
                  Wat2wasm.wat2wasm wat |> Result.error |> Option.value_exn
                in
                fprintf ff "%s\n\n%s" wat err
            | Error err -> fprintf ff "UNCHECKED wasm2wat Error: %s" err)
        | Error err -> fprintf ff "UNCHECKED Wat2wasm Error: %s" err)

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
        (export "_start" (func 7))
        (start 8)) |}];
  next ();
  [%expect
    {| (module (import "richwasm" "mmmem"(memory 0))(import "richwasm" "gcmem"(memory 0))(import "richwasm" "tablenext"(global (mut i32)))(import "richwasm" "tableset"(func (type 0)))(import "richwasm" "mmalloc"(func (type 1)))(import "richwasm" "gcalloc"(func (type 1)))(import "richwasm" "setflag"(func (type 2)))(import "richwasm" "free"(func (type 3)))(import "richwasm" "registerroot"(func (type 1)))(import "richwasm" "unregisterroot"(func (type 3)))(import "richwasm" "table"(table 0 funcref))(func (type 4) (local ) i32.const 1)(func (type 5) (local ) global.get 0 global.set 1 global.get 1 i32.const 0 i32.add global.set 0)(global (mut i32) i32.const 0)(start 8)(export "_start" (func 7))(type (func (param i32 i32) (result )))(type (func (param i32) (result i32)))(type (func (param i32 i32 i32) (result )))(type (func (param i32) (result )))(type (func (param ) (result i32)))(type (func (param ) (result )))) |}]

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
      (export "_start" (func 7))
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
      (export "_start" (func 7))
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
      (export "_start" (func 7))
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
      (export "_start" (func 7))
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
      (export "_start" (func 7))
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
      (export "_start" (func 7))
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
      (export "_start" (func 7))
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
      (export "_start" (func 7))
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
      (export "_start" (func 7))
      (start 8))

    -----------app_ident-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (param i32 i32) (result i32)))
      (type (;5;) (func (result i32)))
      (type (;6;) (func))
      (type (;7;) (func))
      (type (;8;) (func))
      (type (;9;) (func))
      (type (;10;) (func))
      (type (;11;) (func (param i32 i32) (result i32)))
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
      (func (;7;) (type 4) (param i32 i32) (result i32)
        (local i32 i32 i32 i32 i32)
        local.get 0
        local.get 1
        nop
        local.set 3
        local.set 2
        local.get 2
        local.tee 5
        local.get 5
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
          unreachable
        else
          local.get 5
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
          end
        end
        local.set 6
        local.get 6
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 6
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 6
            call 4
          else
            local.get 6
            call 6
          end
        end
        nop
        local.get 3
        local.set 4
        local.get 4
        local.get 4
        drop
        local.get 2
        drop
        local.get 3
        drop)
      (func (;8;) (type 5) (result i32)
        (local i32 i32 i32 i32 i32)
        i32.const 0
        global.get 1
        i32.add
        nop
        i32.const 0
        call 1
        local.set 4
        local.get 4
        nop
        block (param i32 i32) (result i32)  ;; label = @1
          local.set 1
          local.set 0
          local.get 0
          local.get 1
          nop
          local.set 3
          local.set 2
          local.get 3
          i32.const 10
          nop
          local.get 2
          call_indirect (type 4)
          local.get 2
          drop
          local.get 3
          drop
          local.get 0
          local.get 1
          drop
          drop
        end)
      (func (;9;) (type 6)
        global.get 0
        global.set 1
        global.get 1
        i32.const 1
        i32.add
        global.set 0
        global.get 1
        i32.const 0
        i32.add
        i32.const 7
        call 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "_start" (func 8))
      (export "__rw_table_func_7" (func 7))
      (start 9))

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
      (export "_start" (func 7))
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
        local.get 0
        local.get 0
        drop)
      (func (;8;) (type 5)
        global.get 0
        global.set 1
        global.get 1
        i32.const 0
        i32.add
        global.set 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "_start" (func 7))
      (start 8))

    -----------add_one_program-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (param i32 i32) (result i32)))
      (type (;5;) (func (result i32)))
      (type (;6;) (func))
      (type (;7;) (func))
      (type (;8;) (func))
      (type (;9;) (func (param i32 i32) (result i32)))
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
      (func (;7;) (type 4) (param i32 i32) (result i32)
        (local i32 i32 i32)
        local.get 0
        local.get 1
        nop
        local.set 3
        local.set 2
        local.get 3
        i32.const 1
        i32.add
        local.get 2
        local.set 4
        local.get 4
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 4
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 4
            call 4
          else
            local.get 4
            call 6
          end
        end
        local.get 3
        drop)
      (func (;8;) (type 5) (result i32)
        (local i32 i32 i32 i32 i32)
        i32.const 0
        global.get 1
        i32.add
        nop
        i32.const 0
        call 1
        local.set 4
        local.get 4
        nop
        block (param i32 i32) (result i32)  ;; label = @1
          local.set 1
          local.set 0
          local.get 0
          local.get 1
          nop
          local.set 3
          local.set 2
          local.get 3
          i32.const 42
          nop
          local.get 2
          call_indirect (type 4)
          local.get 2
          drop
          local.get 3
          drop
          local.get 0
          local.get 1
          drop
          drop
        end)
      (func (;9;) (type 6)
        global.get 0
        global.set 1
        global.get 1
        i32.const 1
        i32.add
        global.set 0
        global.get 1
        i32.const 0
        i32.add
        i32.const 7
        call 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "add-one" (func 7))
      (export "_start" (func 8))
      (export "__rw_table_func_7" (func 7))
      (start 9))

    -----------add_tup_ref-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (result i32)))
      (type (;5;) (func))
      (type (;6;) (func))
      (type (;7;) (func))
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
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 2
        local.set 5
        i32.const 1
        call 1
        local.set 6
        local.get 6
        i32.const 0
        i32.const 0
        call 3
        local.get 6
        local.get 5
        i32.store offset=3 align=2
        local.get 6
        local.set 0
        i32.const 1
        local.get 0
        nop
        nop
        local.set 2
        local.set 1
        local.get 2
        local.tee 7
        local.get 7
        i32.const 0
        i32.const 0
        call 3
        local.get 7
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 7
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 7
            i32.load offset=3 align=2
            local.tee 8
          else
            local.get 7
            i32.load offset=1 align=2
            local.tee 9
          end
        end
        local.set 3
        local.set 10
        local.get 10
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 10
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 10
            call 4
          else
            local.get 10
            call 6
          end
        end
        local.get 3
        local.set 4
        local.get 1
        local.get 4
        i32.add
        local.get 4
        drop
        local.get 1
        drop
        local.get 2
        drop
        local.get 0
        drop)
      (func (;8;) (type 5)
        global.get 0
        global.set 1
        global.get 1
        i32.const 0
        i32.add
        global.set 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "_start" (func 7))
      (start 8))

    -----------print_10-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func))
      (type (;5;) (func (param i32 i32)))
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
      (import "" "" (func (;7;) (type 0)))
      (func (;8;) (type 0) (param i32 i32)
        local.get 0
        local.get 1
        call 7)
      (func (;9;) (type 4)
        (local i32 i32 i32 i32 i32)
        i32.const 0
        global.get 1
        i32.add
        nop
        i32.const 0
        call 1
        local.set 4
        local.get 4
        nop
        block (param i32 i32)  ;; label = @1
          local.set 1
          local.set 0
          local.get 0
          local.get 1
          nop
          local.set 3
          local.set 2
          local.get 3
          i32.const 10
          nop
          local.get 2
          call_indirect (type 0)
          local.get 2
          drop
          local.get 3
          drop
          local.get 0
          local.get 1
          drop
          drop
        end)
      (func (;10;) (type 4)
        global.get 0
        global.set 1
        global.get 1
        i32.const 1
        i32.add
        global.set 0
        global.get 1
        i32.const 0
        i32.add
        i32.const 7
        call 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "_start" (func 8))
      (export "__rw_table_func_7" (func 7))
      (start 10))

    -----------closure-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (result i32)))
      (type (;5;) (func))
      (type (;6;) (func))
      (type (;7;) (func))
      (type (;8;) (func (param i32 i32) (result i32)))
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
      (func (;7;) (type 1) (param i32) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32)
        local.get 0
        nop
        local.set 1
        local.get 1
        local.tee 4
        local.get 4
        i32.const 0
        i32.const 0
        call 3
        local.get 4
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 4
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 4
            i32.load offset=3 align=2
            local.tee 5
          else
            local.get 4
            i32.load offset=1 align=2
            local.tee 6
          end
        end
        local.set 2
        local.set 7
        local.get 7
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 7
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 7
            call 4
          else
            local.get 7
            call 6
          end
        end
        local.get 2
        nop
        local.set 3
        local.get 3
        local.get 3
        drop
        local.get 1
        drop)
      (func (;8;) (type 4) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32)
        i32.const 10
        local.set 0
        i32.const 0
        global.get 1
        i32.add
        local.get 0
        nop
        local.set 5
        i32.const 1
        call 1
        local.set 6
        local.get 6
        i32.const 0
        i32.const 0
        call 3
        local.get 6
        local.get 5
        i32.store offset=3 align=2
        local.get 6
        nop
        block (param i32 i32) (result i32)  ;; label = @1
          local.set 2
          local.set 1
          local.get 1
          local.get 2
          nop
          local.set 4
          local.set 3
          local.get 4
          nop
          nop
          local.get 3
          call_indirect (type 1)
          local.get 3
          drop
          local.get 4
          drop
          local.get 1
          local.get 2
          drop
          drop
        end
        local.get 0
        drop)
      (func (;9;) (type 5)
        global.get 0
        global.set 1
        global.get 1
        i32.const 1
        i32.add
        global.set 0
        global.get 1
        i32.const 0
        i32.add
        i32.const 7
        call 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "_start" (func 8))
      (export "__rw_table_func_7" (func 7))
      (start 9))

    -----------closure_call_var-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (param i32 i32) (result i32)))
      (type (;5;) (func (result i32)))
      (type (;6;) (func))
      (type (;7;) (func))
      (type (;8;) (func))
      (type (;9;) (func (param i32 i32) (result i32)))
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
      (func (;7;) (type 4) (param i32 i32) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32)
        local.get 0
        local.get 1
        nop
        local.set 3
        local.set 2
        local.get 2
        local.tee 7
        local.get 7
        i32.const 0
        i32.const 0
        call 3
        local.get 7
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 7
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 7
            i32.load offset=3 align=2
            local.tee 8
          else
            local.get 7
            i32.load offset=1 align=2
            local.tee 9
          end
        end
        local.set 4
        local.set 10
        local.get 10
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 10
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 10
            call 4
          else
            local.get 10
            call 6
          end
        end
        local.get 4
        nop
        local.set 5
        local.get 3
        local.set 6
        local.get 6
        local.get 5
        i32.add
        local.get 6
        drop
        local.get 5
        drop
        local.get 2
        drop
        local.get 3
        drop)
      (func (;8;) (type 5) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 21
        local.set 0
        i32.const 1
        local.set 1
        i32.const 0
        global.get 1
        i32.add
        local.get 1
        nop
        local.set 6
        i32.const 1
        call 1
        local.set 7
        local.get 7
        i32.const 0
        i32.const 0
        call 3
        local.get 7
        local.get 6
        i32.store offset=3 align=2
        local.get 7
        nop
        block (param i32 i32) (result i32)  ;; label = @1
          local.set 3
          local.set 2
          local.get 2
          local.get 3
          nop
          local.set 5
          local.set 4
          local.get 5
          local.get 0
          nop
          local.get 4
          call_indirect (type 4)
          local.get 4
          drop
          local.get 5
          drop
          local.get 2
          local.get 3
          drop
          drop
        end
        local.get 1
        drop
        local.get 0
        drop)
      (func (;9;) (type 6)
        global.get 0
        global.set 1
        global.get 1
        i32.const 1
        i32.add
        global.set 0
        global.get 1
        i32.const 0
        i32.add
        i32.const 7
        call 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "_start" (func 8))
      (export "__rw_table_func_7" (func 7))
      (start 9))

    -----------factorial_program-----------
    FAILURE wat2wasm2wat validation!
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (param i32 i32) (result i32)))
      (type (;5;) (func (result i32)))
      (type (;6;) (func))
      (type (;7;) (func (param i32) (result i32)))
      (type (;8;) (func (param i32 i32) (result i32)))
      (type (;9;) (func))
      (type (;10;) (func))
      (type (;11;) (func (param i32 i32) (result i32)))
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
      (func (;7;) (type 4) (param i32 i32) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        local.get 0
        local.get 1
        nop
        local.set 3
        local.set 2
        local.get 3
        i32.const 0
        i32.eqz
        if (param i32) (result i32)  ;; label = @1
          i32.const 1
        else
          local.get 3
          i32.const 1
          i32.sub
          local.set 4
          i32.const 0
          global.get 1
          i32.add
          nop
          i32.const 0
          call 1
          local.set 10
          local.get 10
          nop
          block (param i32 i32) (result i32)  ;; label = @2
            local.set 6
            local.set 5
            local.get 5
            local.get 6
            nop
            local.set 8
            local.set 7
            local.get 8
            local.get 4
            nop
            local.get 7
            call_indirect (type 4)
            local.get 7
            drop
            local.get 8
            drop
            local.get 5
            local.get 6
            drop
            drop
          end
          local.set 9
          local.get 3
          local.get 9
          i32.mul
          local.get 9
          drop
          local.get 4
          drop
        end
        local.get 2
        local.set 11
        local.get 11
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 11
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 11
            call 4
          else
            local.get 11
            call 6
          end
        end
        local.get 3
        drop)
      (func (;8;) (type 5) (result i32)
        (local i32 i32 i32 i32 i32)
        i32.const 0
        global.get 1
        i32.add
        nop
        i32.const 0
        call 1
        local.set 4
        local.get 4
        nop
        block (param i32 i32) (result i32)  ;; label = @1
          local.set 1
          local.set 0
          local.get 0
          local.get 1
          nop
          local.set 3
          local.set 2
          local.get 3
          i32.const 5
          nop
          local.get 2
          call_indirect (type 4)
          local.get 2
          drop
          local.get 3
          drop
          local.get 0
          local.get 1
          drop
          drop
        end)
      (func (;9;) (type 6)
        global.get 0
        global.set 1
        global.get 1
        i32.const 1
        i32.add
        global.set 0
        global.get 1
        i32.const 0
        i32.add
        i32.const 7
        call 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "factorial" (func 7))
      (export "_start" (func 8))
      (export "__rw_table_func_7" (func 7))
      (start 9))


    -:36:7: error: type mismatch at end of `if true` branch, expected [] but got [i32]
          i32.const 1
          ^^^^^^^^^
    -:81:5: error: type mismatch at end of `if false` branch, expected [] but got [i32]
        end
        ^^^

    -----------safe_div-----------
    FAILURE (InstrErr
     (error
      (BlockErr (error (PopEmptyStack LocalSet)) (instr (LocalSet 3))
       (env
        ((local_offset 1) (kinds ()) (labels (((Num (Int I32)))))
         (return ((Num (Int I32))))
         (functions
          ((FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Prod ((Num (Int I32)) (Num (Int I32)))))))
            ((Sum ((Num (Int I32)) (Prod ())))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ()))) (Sum ((Num (Int I32)) (Prod ()))))))
            ((Num (Int I32))))
           (FunctionType () () ((Num (Int I32))))))
         (table
          ((FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Prod ((Num (Int I32)) (Num (Int I32)))))))
            ((Sum ((Num (Int I32)) (Prod ())))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ()))) (Sum ((Num (Int I32)) (Prod ()))))))
            ((Num (Int I32))))))
         (lfx (InferFx))))
       (state
        ((locals
          ((Plug (Prod ((Atom I32) (Atom I32) (Atom I32))))
           (Ref (Base MM) (Ser (Prod ()))) (Sum ((Num (Int I32)) (Prod ())))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ()))))
         (stack ())))))
     (instr
      (Case (ValType ((Num (Int I32)))) InferFx
       (((LocalSet 3) (LocalGet 3 Follow) (LocalGet 3 Move) Drop)
        ((LocalSet 4) (NumConst (Int I32) 0) (LocalGet 4 Move) Drop))))
     (env
      ((local_offset 1) (kinds ()) (labels ()) (return ((Num (Int I32))))
       (functions
        ((FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Prod ((Num (Int I32)) (Num (Int I32)))))))
          ((Sum ((Num (Int I32)) (Prod ())))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ()))) (Sum ((Num (Int I32)) (Prod ()))))))
          ((Num (Int I32))))
         (FunctionType () () ((Num (Int I32))))))
       (table
        ((FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Prod ((Num (Int I32)) (Num (Int I32)))))))
          ((Sum ((Num (Int I32)) (Prod ())))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ()))) (Sum ((Num (Int I32)) (Prod ()))))))
          ((Num (Int I32))))))
       (lfx ())))
     (state
      ((locals
        ((Plug (Prod ((Atom I32) (Atom I32) (Atom I32))))
         (Ref (Base MM) (Ser (Prod ()))) (Sum ((Num (Int I32)) (Prod ())))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ()))))
       (stack ((Sum ((Num (Int I32)) (Prod ()))))))))
    -----------incr_n-----------
    FAILURE wat2wasm2wat validation!
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (param i32 i32) (result i32)))
      (type (;5;) (func (param i32 i32 i32) (result i32)))
      (type (;6;) (func (result i32)))
      (type (;7;) (func))
      (type (;8;) (func))
      (type (;9;) (func))
      (type (;10;) (func (param i32) (result i32)))
      (type (;11;) (func))
      (type (;12;) (func))
      (type (;13;) (func (param i32 i32) (result i32)))
      (type (;14;) (func (param i32 i32) (result i32)))
      (type (;15;) (func))
      (type (;16;) (func))
      (type (;17;) (func (param i32 i32) (result i32)))
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
      (func (;7;) (type 4) (param i32 i32) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        local.get 0
        local.get 1
        nop
        local.set 3
        local.set 2
        local.get 3
        i32.const 0
        local.set 9
        local.set 10
        local.get 10
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 10
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 10
            i32.load offset=3 align=2
            local.tee 11
            local.get 10
            local.get 9
            i32.store offset=3 align=2
          else
            local.get 10
            i32.load offset=1 align=2
            local.tee 12
            local.get 10
            local.get 9
            i32.store offset=1 align=2
          end
        end
        nop
        nop
        local.set 5
        local.set 4
        local.get 5
        i32.const 1
        i32.add
        local.set 6
        local.get 4
        local.get 6
        local.set 13
        local.set 14
        local.get 14
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 14
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 14
            i32.load offset=3 align=2
            local.tee 15
            local.get 14
            local.get 13
            i32.store offset=3 align=2
          else
            local.get 14
            i32.load offset=1 align=2
            local.tee 16
            local.get 14
            local.get 13
            i32.store offset=1 align=2
          end
        end
        nop
        nop
        local.set 8
        local.set 7
        local.get 7
        local.get 7
        drop
        local.get 8
        drop
        local.get 6
        drop
        local.get 4
        drop
        local.get 5
        drop
        local.get 2
        local.set 17
        local.get 17
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 17
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 17
            call 4
          else
            local.get 17
            call 6
          end
        end
        local.get 3
        drop)
      (func (;8;) (type 5) (param i32 i32 i32) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        local.get 0
        local.get 1
        local.get 2
        nop
        local.set 5
        local.set 4
        local.set 3
        local.get 4
        local.get 5
        nop
        local.set 7
        local.set 6
        local.get 7
        i32.const 0
        i32.eqz
        if (param i32) (result i32)  ;; label = @1
          local.get 6
          local.tee 19
          local.get 19
          i32.const 0
          i32.const 0
          call 3
          local.get 19
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 19
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 19
              i32.load offset=3 align=2
              local.tee 20
            else
              local.get 19
              i32.load offset=1 align=2
              local.tee 21
            end
          end
          local.set 8
          local.set 22
          local.get 22
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 22
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 22
              call 4
            else
              local.get 22
              call 6
            end
          end
          local.get 8
        else
          i32.const 0
          global.get 1
          i32.add
          nop
          i32.const 0
          call 1
          local.set 23
          local.get 23
          nop
          block (param i32 i32) (result i32)  ;; label = @2
            local.set 10
            local.set 9
            local.get 9
            local.get 10
            nop
            local.set 12
            local.set 11
            local.get 12
            local.get 6
            nop
            local.get 11
            call_indirect (type 4)
            local.get 11
            drop
            local.get 12
            drop
            local.get 9
            local.get 10
            drop
            drop
          end
          local.set 13
          local.get 7
          i32.const 1
          i32.sub
          local.set 14
          i32.const 1
          global.get 1
          i32.add
          nop
          i32.const 0
          call 1
          local.set 24
          local.get 24
          nop
          block (param i32 i32) (result i32)  ;; label = @2
            local.set 16
            local.set 15
            local.get 15
            local.get 16
            nop
            local.set 18
            local.set 17
            local.get 18
            local.get 13
            local.get 14
            nop
            nop
            local.get 17
            call_indirect (type 5)
            local.get 17
            drop
            local.get 18
            drop
            local.get 15
            local.get 16
            drop
            drop
          end
          local.get 14
          drop
          local.get 13
          drop
        end
        local.get 6
        drop
        local.get 7
        drop
        local.get 3
        local.set 25
        local.get 25
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 25
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 25
            call 4
          else
            local.get 25
            call 6
          end
        end
        local.get 4
        local.get 5
        drop
        drop)
      (func (;9;) (type 6) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 10
        local.set 5
        i32.const 1
        call 1
        local.set 6
        local.get 6
        i32.const 0
        i32.const 0
        call 3
        local.get 6
        local.get 5
        i32.store offset=3 align=2
        local.get 6
        local.set 0
        i32.const 1
        global.get 1
        i32.add
        nop
        i32.const 0
        call 1
        local.set 7
        local.get 7
        nop
        block (param i32 i32) (result i32)  ;; label = @1
          local.set 2
          local.set 1
          local.get 1
          local.get 2
          nop
          local.set 4
          local.set 3
          local.get 4
          local.get 0
          i32.const 3
          nop
          nop
          local.get 3
          call_indirect (type 5)
          local.get 3
          drop
          local.get 4
          drop
          local.get 1
          local.get 2
          drop
          drop
        end
        local.get 0
        drop)
      (func (;10;) (type 7)
        global.get 0
        global.set 1
        global.get 1
        i32.const 2
        i32.add
        global.set 0
        global.get 1
        i32.const 0
        i32.add
        i32.const 7
        call 0
        global.get 1
        i32.const 1
        i32.add
        i32.const 8
        call 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "incr_n" (func 8))
      (export "_start" (func 9))
      (export "__rw_table_func_7" (func 7))
      (export "__rw_table_func_8" (func 8))
      (start 10))


    -:72:5: error: type mismatch in local.set, expected [i32] but got []
        local.set 4
        ^^^^^^^^^
    -:111:5: error: type mismatch in local.set, expected [i32] but got []
        local.set 7
        ^^^^^^^^^
    -:210:7: error: type mismatch at end of `if true` branch, expected [] but got [i32]
          local.get 8
          ^^^^^^^^^
    -:285:5: error: type mismatch at end of `if false` branch, expected [] but got [i32]
        end
        ^^^

    -----------fix_factorial[invalid]-----------
    FAILURE (InstrErr
     (error
      (BlockErr
       (error
        (UngroupNonProd
         (CodeRef
          (FunctionType ()
           ((Prod
             ((Ref (Base MM) (Ser (Var 0)))
              (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
               (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                  ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (CodeRef
                     (FunctionType ()
                      ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                      ((Num (Int I32))))))))))))))
           ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
             (CodeRef
              (FunctionType ()
               ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
               ((Num (Int I32)))))))))))
       (instr Ungroup)
       (env
        ((local_offset 1) (kinds ((VALTYPE (Atom Ptr) NoCopy ExDrop)))
         (labels
          (((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
             (CodeRef
              (FunctionType ()
               ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
               ((Num (Int I32)))))))))
         (return
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32))))))))
         (functions
          ((FunctionType ()
            ((Prod
              ((Ref (Base MM)
                (Ser
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (CodeRef
                     (FunctionType ()
                      ((Prod
                        ((Ref (Base MM) (Ser (Var 0)))
                         (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                          (CodeRef
                           (FunctionType ()
                            ((Prod
                              ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                            ((Num (Int I32)))))))))
                      ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                        (CodeRef
                         (FunctionType ()
                          ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                          ((Num (Int I32))))))))))))))
               (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
                (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                 (CodeRef
                  (FunctionType ()
                   ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                   ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                     (CodeRef
                      (FunctionType ()
                       ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                       ((Num (Int I32))))))))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32))))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (CodeRef
                 (FunctionType ()
                  ((Prod
                    ((Ref (Base MM) (Ser (Var 0)))
                     (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                      (CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                        ((Num (Int I32)))))))))
                  ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (CodeRef
                     (FunctionType ()
                      ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                      ((Num (Int I32)))))))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32))))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM)
                (Ser
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (CodeRef
                     (FunctionType ()
                      ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                      ((Num (Int I32))))))))))
               (Num (Int I32)))))
            ((Num (Int I32))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32)))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32))))))))
           (FunctionType () () ((Num (Int I32))))))
         (table
          ((FunctionType ()
            ((Prod
              ((Ref (Base MM)
                (Ser
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (CodeRef
                     (FunctionType ()
                      ((Prod
                        ((Ref (Base MM) (Ser (Var 0)))
                         (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                          (CodeRef
                           (FunctionType ()
                            ((Prod
                              ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                            ((Num (Int I32)))))))))
                      ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                        (CodeRef
                         (FunctionType ()
                          ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                          ((Num (Int I32))))))))))))))
               (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
                (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                 (CodeRef
                  (FunctionType ()
                   ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                   ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                     (CodeRef
                      (FunctionType ()
                       ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                       ((Num (Int I32))))))))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32))))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (CodeRef
                 (FunctionType ()
                  ((Prod
                    ((Ref (Base MM) (Ser (Var 0)))
                     (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                      (CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                        ((Num (Int I32)))))))))
                  ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (CodeRef
                     (FunctionType ()
                      ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                      ((Num (Int I32)))))))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32))))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM)
                (Ser
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (CodeRef
                     (FunctionType ()
                      ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                      ((Num (Int I32))))))))))
               (Num (Int I32)))))
            ((Num (Int I32))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32)))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32))))))))))
         (lfx (InferFx))))
       (state
        ((locals
          ((Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
           (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
            (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
             (CodeRef
              (FunctionType () ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
               ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                 (CodeRef
                  (FunctionType ()
                   ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                   ((Num (Int I32)))))))))))
           (Plug (Prod ((Atom I32))))
           (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType ()
              ((Prod
                ((Ref (Base MM) (Ser (Var 0)))
                 (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32)))))))))
              ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32))))))))))
           (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
            (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
             (CodeRef
              (FunctionType () ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
               ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                 (CodeRef
                  (FunctionType ()
                   ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                   ((Num (Int I32)))))))))))
           (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType ()
              ((Prod
                ((Ref (Base MM) (Ser (Var 0)))
                 (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
                  (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                   (CodeRef
                    (FunctionType ()
                     ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                     ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                       (CodeRef
                        (FunctionType ()
                         ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                         ((Num (Int I32))))))))))))))
              ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32))))))))))
           (CodeRef
            (FunctionType ()
             ((Prod
               ((Ref (Base MM) (Ser (Var 0)))
                (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
                 (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                    ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                      (CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                        ((Num (Int I32))))))))))))))
             ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
               (CodeRef
                (FunctionType ()
                 ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                 ((Num (Int I32)))))))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))))
         (stack
          ((CodeRef
            (FunctionType ()
             ((Prod
               ((Ref (Base MM) (Ser (Var 0)))
                (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
                 (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                    ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                      (CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                        ((Num (Int I32))))))))))))))
             ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
               (CodeRef
                (FunctionType ()
                 ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                 ((Num (Int I32)))))))))))))))
     (instr
      (Unpack
       (ArrowType 1
        ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
          (CodeRef
           (FunctionType ()
            ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
            ((Num (Int I32))))))))
       InferFx
       ((LocalSet 7) (LocalGet 7 Follow) Ungroup (LocalSet 9) (LocalSet 8)
        (LocalGet 9 Follow) (LocalGet 5 Follow) (Group 2) (LocalGet 8 Follow)
        CallIndirect (LocalGet 8 Move) Drop (LocalGet 9 Move) Drop
        (LocalGet 7 Move) Drop)))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return
        ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
          (CodeRef
           (FunctionType ()
            ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
            ((Num (Int I32))))))))
       (functions
        ((FunctionType ()
          ((Prod
            ((Ref (Base MM)
              (Ser
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType ()
                    ((Prod
                      ((Ref (Base MM) (Ser (Var 0)))
                       (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                        (CodeRef
                         (FunctionType ()
                          ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                          ((Num (Int I32)))))))))
                    ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                      (CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                        ((Num (Int I32))))))))))))))
             (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
              (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
               (CodeRef
                (FunctionType () ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                 ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                   (CodeRef
                    (FunctionType ()
                     ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                     ((Num (Int I32))))))))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32))))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod
                  ((Ref (Base MM) (Ser (Var 0)))
                   (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (CodeRef
                     (FunctionType ()
                      ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                      ((Num (Int I32)))))))))
                ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32)))))))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32))))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM)
              (Ser
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32))))))))))
             (Num (Int I32)))))
          ((Num (Int I32))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32)))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32))))))))
         (FunctionType () () ((Num (Int I32))))))
       (table
        ((FunctionType ()
          ((Prod
            ((Ref (Base MM)
              (Ser
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType ()
                    ((Prod
                      ((Ref (Base MM) (Ser (Var 0)))
                       (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                        (CodeRef
                         (FunctionType ()
                          ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                          ((Num (Int I32)))))))))
                    ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                      (CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                        ((Num (Int I32))))))))))))))
             (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
              (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
               (CodeRef
                (FunctionType () ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                 ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                   (CodeRef
                    (FunctionType ()
                     ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                     ((Num (Int I32))))))))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32))))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod
                  ((Ref (Base MM) (Ser (Var 0)))
                   (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (CodeRef
                     (FunctionType ()
                      ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                      ((Num (Int I32)))))))))
                ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32)))))))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32))))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM)
              (Ser
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32))))))))))
             (Num (Int I32)))))
          ((Num (Int I32))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32)))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32))))))))))
       (lfx ())))
     (state
      ((locals
        ((Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
         (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
          (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
           (CodeRef
            (FunctionType () ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
             ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
               (CodeRef
                (FunctionType ()
                 ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                 ((Num (Int I32)))))))))))
         (Plug (Prod ((Atom I32))))
         (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
          (CodeRef
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Var 0)))
               (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32)))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32))))))))))
         (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
          (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
           (CodeRef
            (FunctionType () ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
             ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
               (CodeRef
                (FunctionType ()
                 ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                 ((Num (Int I32)))))))))))
         (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
          (CodeRef
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Var 0)))
               (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
                (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                 (CodeRef
                  (FunctionType ()
                   ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                   ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                     (CodeRef
                      (FunctionType ()
                       ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                       ((Num (Int I32))))))))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32))))))))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32))))))
       (stack
        ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
          (CodeRef
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Var 0)))
               (Rec (VALTYPE (Atom I32) NoCopy ExDrop)
                (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                 (CodeRef
                  (FunctionType ()
                   ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                   ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                     (CodeRef
                      (FunctionType ()
                       ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                       ((Num (Int I32))))))))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32)))))))))))))))
    -----------unboxed_list[invalid]-----------
    FAILURE (Codegen
     (CannotResolveRepOfRecTypeWithoutIndirection (Var (0 ("\206\177")))))
    -----------boxed_list-----------
    FAILURE (InstrErr
     (error
      (BlockErr (error (PopEmptyStack LocalSet)) (instr (LocalSet 5))
       (env
        ((local_offset 1) (kinds ())
         (labels
          (((Sum
             ((Prod ())
              (Prod
               ((Num (Int I32))
                (Ref (Base MM)
                 (Ser
                  (Rec
                   (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                    NoCopy ExDrop)
                   (Sum
                    ((Prod ())
                     (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0)))))))))))))))))
         (return
          ((Rec
            (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
             ExDrop)
            (Sum
             ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))
         (functions
          ((FunctionType ()
            ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
            ((Num (Int I32))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32))))))
                 (Rec
                  (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                   NoCopy ExDrop)
                  (Sum
                   ((Prod ())
                    (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0)))))))))))))
            ((Rec
              (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
               ExDrop)
              (Sum
               ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))
           (FunctionType () ()
            ((Rec
              (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
               ExDrop)
              (Sum
               ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))
         (table
          ((FunctionType ()
            ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
            ((Num (Int I32))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32))))))
                 (Rec
                  (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                   NoCopy ExDrop)
                  (Sum
                   ((Prod ())
                    (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0)))))))))))))
            ((Rec
              (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
               ExDrop)
              (Sum
               ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))
         (lfx (InferFx))))
       (state
        ((locals
          ((Plug (Prod ((Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32))))
           (Ref (Base MM) (Ser (Prod ())))
           (Plug (Prod ((Atom I32) (Atom I32) (Atom I32) (Atom I32))))
           (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32))))))
           (Plug (Prod ((Atom I32) (Atom I32) (Atom I32)))) (Plug (Prod ()))
           (Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32) (Atom I32) (Atom I32))))))
         (stack ())))))
     (instr
      (Case
       (ValType
        ((Sum
          ((Prod ())
           (Prod
            ((Num (Int I32))
             (Ref (Base MM)
              (Ser
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
                 ExDrop)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))))))
       InferFx
       (((LocalSet 5) (LocalGet 5 Follow)
         (Inject 0
          ((Prod ())
           (Prod
            ((Num (Int I32))
             (Ref (Base MM)
              (Ser
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
                 ExDrop)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))))
         (LocalGet 5 Move) Drop)
        ((LocalSet 6) (LocalGet 6 Follow) Ungroup (LocalSet 8) (LocalSet 7)
         (LocalGet 3 Follow)
         (Unpack (ArrowType 1 ((Num (Int I32)))) InferFx
          ((LocalSet 9) (LocalGet 9 Follow) Ungroup (LocalSet 11) (LocalSet 10)
           (LocalGet 11 Follow) (LocalGet 7 Follow) (Group 2)
           (LocalGet 10 Follow) CallIndirect (LocalGet 10 Move) Drop
           (LocalGet 11 Move) Drop (LocalGet 9 Move) Drop))
         (CodeRef 1) (Group 0) (New MM) (Group 2)
         (Pack (Type (Prod ()))
          (Prod
           ((CodeRef
             (FunctionType ()
              ((Prod
                ((Ref (Base MM) (Ser (Var 0)))
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (CodeRef
                     (FunctionType ()
                      ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                      ((Num (Int I32))))))
                   (Rec
                    (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr)))))
                     NoCopy ExDrop)
                    (Sum
                     ((Prod ())
                      (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0)))))))))))))
              ((Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
                 ExDrop)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0)))))))))))
            (Ref (Base MM) (Ser (Var 0))))))
         (Unpack
          (ArrowType 1
           ((Rec
             (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
              ExDrop)
             (Sum
              ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))
          InferFx
          ((LocalSet 12) (LocalGet 12 Follow) Ungroup (LocalSet 14) (LocalSet 13)
           (LocalGet 14 Follow) (LocalGet 3 Follow) (LocalGet 8 Follow)
           (Load (Path ()) Move) (LocalSet 15) Drop (LocalGet 15 Move) (Group 2)
           (Group 2) (LocalGet 13 Follow) CallIndirect (LocalGet 13 Move) Drop
           (LocalGet 14 Move) Drop (LocalGet 12 Move) Drop))
         (New MM) (Group 2)
         (Inject 1
          ((Prod ())
           (Prod
            ((Num (Int I32))
             (Ref (Base MM)
              (Ser
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
                 ExDrop)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))))
         (LocalGet 7 Move) Drop (LocalGet 8 Move) Drop (LocalGet 6 Move) Drop))))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return
        ((Rec
          (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
           ExDrop)
          (Sum
           ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))
       (functions
        ((FunctionType ()
          ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
          ((Num (Int I32))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Prod
              ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32))))))
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
                 ExDrop)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0)))))))))))))
          ((Rec
            (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
             ExDrop)
            (Sum
             ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))
         (FunctionType () ()
          ((Rec
            (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
             ExDrop)
            (Sum
             ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))
       (table
        ((FunctionType ()
          ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
          ((Num (Int I32))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Prod
              ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32))))))
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
                 ExDrop)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0)))))))))))))
          ((Rec
            (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
             ExDrop)
            (Sum
             ((Prod ()) (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0))))))))))))
       (lfx ())))
     (state
      ((locals
        ((Plug (Prod ((Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32))))
         (Ref (Base MM) (Ser (Prod ())))
         (Plug (Prod ((Atom I32) (Atom I32) (Atom I32) (Atom I32))))
         (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
          (CodeRef
           (FunctionType ()
            ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
            ((Num (Int I32))))))
         (Plug (Prod ((Atom I32) (Atom I32) (Atom I32)))) (Plug (Prod ()))
         (Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32) (Atom I32) (Atom I32))))))
       (stack
        ((Sum
          ((Prod ())
           (Prod
            ((Num (Int I32))
             (Ref (Base MM)
              (Ser
               (Rec
                (VALTYPE (Sum ((Prod ()) (Prod ((Atom I32) (Atom Ptr))))) NoCopy
                 ExDrop)
                (Sum
                 ((Prod ())
                  (Prod ((Num (Int I32)) (Ref (Base MM) (Ser (Var 0)))))))))))))))))))
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
      (export "_start" (func 7))
      (start 8))

    -----------peano-----------
    FAILURE (InstrErr
     (error
      (BlockErr (error (PopEmptyStack LocalSet)) (instr (LocalSet 5))
       (env
        ((local_offset 1) (kinds ())
         (labels
          (((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
             (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))
         (return
          ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
            (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
         (functions
          ((FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Prod
                ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                  (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))
                 (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                  (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))))
            ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
              (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
           (FunctionType ()
            ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
            ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
              (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))
            ((Num (Int I32))))
           (FunctionType () () ((Num (Int I32))))))
         (table
          ((FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Prod
                ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                  (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))
                 (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                  (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))))
            ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
              (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
           (FunctionType ()
            ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
            ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
              (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))
            ((Num (Int I32))))))
         (lfx (InferFx))))
       (state
        ((locals
          ((Plug (Prod ((Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32))))
           (Ref (Base MM) (Ser (Prod ())))
           (Plug (Prod ((Atom I32) (Atom I32) (Atom I32) (Atom I32))))
           (Plug (Prod ((Atom I32) (Atom I32))))
           (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
            (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))
           (Plug (Prod ())) (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32) (Atom I32))))))
         (stack ())))))
     (instr
      (Case
       (ValType
        ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
          (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
       InferFx
       (((LocalSet 5) (LocalGet 4 Follow) (LocalGet 5 Move) Drop)
        ((LocalSet 6) (CodeRef 0) (Group 0) (New MM) (Group 2)
         (Pack (Type (Prod ()))
          (Prod
           ((CodeRef
             (FunctionType ()
              ((Prod
                ((Ref (Base MM) (Ser (Var 0)))
                 (Prod
                  ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                    (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))
                   (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                    (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))))
              ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))
            (Ref (Base MM) (Ser (Var 0))))))
         (Unpack
          (ArrowType 1
           ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
             (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
          InferFx
          ((LocalSet 7) (LocalGet 7 Follow) Ungroup (LocalSet 9) (LocalSet 8)
           (LocalGet 9 Follow) (LocalGet 6 Follow) (Load (Path ()) Move)
           (LocalSet 10) Drop (LocalGet 10 Move) (LocalGet 4 Follow) (Group 2)
           (Group 2) (LocalGet 8 Follow) CallIndirect (LocalGet 8 Move) Drop
           (LocalGet 9 Move) Drop (LocalGet 7 Move) Drop))
         (New MM)
         (Inject 1
          ((Prod ())
           (Ref (Base MM)
            (Ser
             (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
              (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))))
         (Fold
          (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
           (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))
         (LocalGet 6 Move) Drop))))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return
        ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
          (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
       (functions
        ((FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Prod
              ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))
               (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))))
          ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
            (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
         (FunctionType ()
          ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
          ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
            (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
              (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))
          ((Num (Int I32))))
         (FunctionType () () ((Num (Int I32))))))
       (table
        ((FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Prod
              ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))
               (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
                (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))))
          ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
            (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
         (FunctionType ()
          ((Prod ((Ref (Base MM) (Ser (Prod ()))) (Num (Int I32)))))
          ((Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
            (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
              (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))
          ((Num (Int I32))))))
       (lfx ())))
     (state
      ((locals
        ((Plug (Prod ((Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32))))
         (Ref (Base MM) (Ser (Prod ())))
         (Plug (Prod ((Atom I32) (Atom I32) (Atom I32) (Atom I32))))
         (Plug (Prod ((Atom I32) (Atom I32))))
         (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
          (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0))))))
         (Plug (Prod ())) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32) (Atom I32))))))
       (stack
        ((Sum
          ((Prod ())
           (Ref (Base MM)
            (Ser
             (Rec (VALTYPE (Sum ((Prod ()) (Atom Ptr))) NoCopy ExDrop)
              (Sum ((Prod ()) (Ref (Base MM) (Ser (Var 0)))))))))))))))
    -----------mini_zip-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (param i32 i32) (result i32)))
      (type (;5;) (func (param i32 i32 i32) (result i32 i32)))
      (type (;6;) (func (param i32 i32 i32) (result i32)))
      (type (;7;) (func))
      (type (;8;) (func))
      (type (;9;) (func))
      (type (;10;) (func (param i32 i32) (result i32)))
      (type (;11;) (func (param i32 i32) (result i32)))
      (type (;12;) (func))
      (type (;13;) (func))
      (type (;14;) (func))
      (type (;15;) (func))
      (type (;16;) (func (param i32) (result i32)))
      (type (;17;) (func (param i32) (result i32)))
      (type (;18;) (func (param i32) (result i32)))
      (type (;19;) (func (param i32) (result i32)))
      (type (;20;) (func))
      (type (;21;) (func))
      (type (;22;) (func))
      (type (;23;) (func))
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
      (func (;7;) (type 4) (param i32 i32) (result i32)
        (local i32 i32 i32)
        local.get 0
        local.get 1
        nop
        local.set 3
        local.set 2
        local.get 3
        i32.const 1
        i32.add
        local.get 2
        local.set 4
        local.get 4
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 4
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 4
            call 4
          else
            local.get 4
            call 6
          end
        end
        local.get 3
        drop)
      (func (;8;) (type 5) (param i32 i32 i32) (result i32 i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        local.get 0
        local.get 1
        local.get 2
        nop
        local.set 5
        local.set 4
        local.set 3
        local.get 4
        local.get 5
        nop
        local.set 7
        local.set 6
        i32.const 0
        global.get 1
        i32.add
        nop
        i32.const 0
        call 1
        local.set 16
        local.get 16
        nop
        block (param i32 i32) (result i32)  ;; label = @1
          local.set 9
          local.set 8
          local.get 8
          local.get 9
          nop
          local.set 11
          local.set 10
          local.get 11
          local.get 6
          nop
          local.get 10
          call_indirect (type 4)
          local.get 10
          drop
          local.get 11
          drop
          local.get 8
          local.get 9
          drop
          drop
        end
        i32.const 0
        global.get 1
        i32.add
        nop
        i32.const 0
        call 1
        local.set 17
        local.get 17
        nop
        block (param i32 i32) (result i32)  ;; label = @1
          local.set 13
          local.set 12
          local.get 12
          local.get 13
          nop
          local.set 15
          local.set 14
          local.get 15
          local.get 7
          nop
          local.get 14
          call_indirect (type 4)
          local.get 14
          drop
          local.get 15
          drop
          local.get 12
          local.get 13
          drop
          drop
        end
        nop
        local.get 6
        drop
        local.get 7
        drop
        local.get 3
        local.set 18
        local.get 18
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 18
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 18
            call 4
          else
            local.get 18
            call 6
          end
        end
        local.get 4
        local.get 5
        drop
        drop)
      (func (;9;) (type 6) (param i32 i32 i32) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        local.get 0
        local.get 1
        local.get 2
        nop
        local.set 5
        local.set 4
        local.set 3
        local.get 4
        local.get 5
        nop
        local.set 7
        local.set 6
        local.get 6
        local.tee 10
        local.get 10
        i32.const 0
        i32.const 0
        call 3
        local.get 10
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 10
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 10
            i32.load offset=3 align=2
            local.tee 11
          else
            local.get 10
            i32.load offset=1 align=2
            local.tee 12
          end
        end
        local.set 8
        local.set 13
        local.get 13
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 13
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 13
            call 4
          else
            local.get 13
            call 6
          end
        end
        local.get 8
        local.get 7
        local.tee 14
        local.get 14
        i32.const 0
        i32.const 0
        call 3
        local.get 14
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 14
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 14
            i32.load offset=3 align=2
            local.tee 15
            local.get 15
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 15
              i32.const 2
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              end
            end
          else
            local.get 14
            i32.load offset=1 align=2
            local.tee 16
            local.get 16
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 16
              i32.const 2
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                call 5
              end
            end
          end
        end
        local.set 9
        local.set 17
        local.get 17
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 17
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 17
            call 4
          else
            local.get 17
            call 6
          end
        end
        local.get 9
        nop
        local.set 19
        local.set 18
        i32.const 2
        call 1
        local.set 20
        local.get 20
        i32.const 0
        i32.const 0
        call 3
        local.get 20
        i32.const 1
        i32.const 1
        call 3
        local.get 20
        local.get 19
        i32.store offset=3 align=2
        local.get 20
        local.get 18
        i32.store offset=7 align=2
        local.get 20
        local.get 6
        drop
        local.get 7
        drop
        local.get 3
        local.set 21
        local.get 21
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 21
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 21
            call 4
          else
            local.get 21
            call 6
          end
        end
        local.get 4
        local.get 5
        drop
        drop)
      (func (;10;) (type 7)
        global.get 0
        global.set 1
        global.get 1
        i32.const 3
        i32.add
        global.set 0
        global.get 1
        i32.const 0
        i32.add
        i32.const 7
        call 0
        global.get 1
        i32.const 1
        i32.add
        i32.const 8
        call 0
        global.get 1
        i32.const 2
        i32.add
        i32.const 9
        call 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "typle_add1" (func 8))
      (export "__rw_table_func_7" (func 7))
      (export "__rw_table_func_8" (func 8))
      (export "__rw_table_func_9" (func 9))
      (start 10)) |}]
