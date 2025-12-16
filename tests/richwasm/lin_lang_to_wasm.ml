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
    x
    |> Main.compile_ast
    |> Main.Res.T.run
    |> fst
    |> or_fail_pp Main.CompileErr.pp
    |> elab

  let string_pipeline s = s |> Parse.from_string_exn |> syntax_pipeline
  let examples = Test_examples.Lin_lang.all

  let pp ff x =
    let fmted =
      Wat2wasm.wat2wasm ~check:false x
      |> Result.map_error ~f:(asprintf "wat2wasm(unchecked): %s")
      |> Result.bind ~f:(Wasm2wat.wasm2wat ~check:false)
      |> Result.map_error ~f:(asprintf "wasm2wat(unchecked): %s")
      |> or_fail_pp pp_print_string
    in
    fmted
    |> Wat2wasm.wat2wasm
    |> or_fail_pp (fun ff x -> fprintf ff "wat2wasm: %s\n%s" x fmted)
    |> Wasm2wat.pp_as_wat ff

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
      (type (;6;) (func (param i32 i32) (result i32)))
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

    -----------triangle_tl-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (param i32 i32) (result i32)))
      (type (;5;) (func (result i32)))
      (type (;6;) (func))
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
        (local i32 i32 i32 i32 i32 i32 i32 i32)
        local.get 0
        local.get 1
        nop
        local.set 3
        local.set 2
        local.get 3
        i32.eqz
        if (result i32)  ;; label = @1
          i32.const 0
        else
          local.get 3
          i32.const 0
          global.get 1
          i32.add
          nop
          i32.const 0
          call 1
          local.set 8
          local.get 8
          nop
          block (param i32 i32) (result i32)  ;; label = @2
            local.set 5
            local.set 4
            local.get 4
            local.get 5
            nop
            local.set 7
            local.set 6
            local.get 7
            local.get 3
            i32.const 1
            i32.sub
            nop
            local.get 6
            call_indirect (type 4)
            local.get 6
            drop
            local.get 7
            drop
            local.get 4
            local.get 5
            drop
            drop
          end
          i32.add
        end
        local.get 2
        local.set 9
        local.get 9
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 9
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 9
            call 4
          else
            local.get 9
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

    -----------factorial_tl-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (param i32 i32) (result i32)))
      (type (;5;) (func (result i32)))
      (type (;6;) (func))
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
        i32.eqz
        if (result i32)  ;; label = @1
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

    -----------safe_div-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (param i32 i32 i32) (result i32 i32)))
      (type (;5;) (func (param i32 i32 i32) (result i32)))
      (type (;6;) (func (result i32)))
      (type (;7;) (func))
      (type (;8;) (func (result i32 i32)))
      (type (;9;) (func (param i32 i32) (result i32 i32)))
      (type (;10;) (func (param i32 i32) (result i32)))
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
      (func (;7;) (type 4) (param i32 i32 i32) (result i32 i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32)
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
        i32.eqz
        if (result i32 i32)  ;; label = @1
          nop
          i32.const 1
          local.get 9
        else
          local.get 6
          local.get 7
          i32.div_s
          local.set 8
          local.get 8
          local.set 10
          i32.const 0
          local.get 10
          local.get 8
          drop
        end
        local.get 6
        drop
        local.get 7
        drop
        local.get 3
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
        local.get 4
        local.get 5
        drop
        drop)
      (func (;8;) (type 5) (param i32 i32 i32) (result i32)
        (local i32 i32 i32 i32 i32 i32)
        local.get 0
        local.get 1
        local.get 2
        nop
        local.set 5
        local.set 4
        local.set 3
        local.get 4
        local.get 5
        local.set 7
        block (param i32) (result i32)  ;; label = @1
          block (param i32)  ;; label = @2
            block (param i32)  ;; label = @3
              block (param i32)  ;; label = @4
                br_table 2 (;@2;) 1 (;@3;) 0 (;@4;)
              end
              unreachable
            end
            i32.const 0
            br 2 (;@0;)
          end
          local.get 7
          local.set 6
          local.get 6
          local.get 6
          drop
          br 1 (;@0;)
        end
        local.get 3
        local.set 8
        local.get 8
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 8
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 8
            call 4
          else
            local.get 8
            call 6
          end
        end
        local.get 4
        local.get 5
        drop
        drop)
      (func (;9;) (type 6) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 0
        global.get 1
        i32.add
        nop
        i32.const 0
        call 1
        local.set 10
        local.get 10
        nop
        block (param i32 i32) (result i32 i32)  ;; label = @1
          local.set 1
          local.set 0
          local.get 0
          local.get 1
          nop
          local.set 3
          local.set 2
          local.get 3
          i32.const 10
          i32.const 0
          nop
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
        end
        local.set 5
        local.set 4
        i32.const 1
        global.get 1
        i32.add
        nop
        i32.const 0
        call 1
        local.set 11
        local.get 11
        nop
        block (param i32 i32) (result i32)  ;; label = @1
          local.set 7
          local.set 6
          local.get 6
          local.get 7
          nop
          local.set 9
          local.set 8
          local.get 9
          local.get 4
          local.get 5
          nop
          local.get 8
          call_indirect (type 5)
          local.get 8
          drop
          local.get 9
          drop
          local.get 6
          local.get 7
          drop
          drop
        end
        local.get 4
        local.get 5
        drop
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
      (export "_start" (func 9))
      (export "__rw_table_func_7" (func 7))
      (export "__rw_table_func_8" (func 8))
      (start 10))

    -----------incr_n-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (param i32 i32) (result i32)))
      (type (;5;) (func (param i32 i32 i32) (result i32)))
      (type (;6;) (func (result i32)))
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
      (func (;7;) (type 4) (param i32 i32) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        local.get 0
        local.get 1
        nop
        local.set 3
        local.set 2
        local.get 3
        i32.const 0
        local.set 8
        local.tee 9
        local.get 9
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 9
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 9
            i32.load offset=3 align=2
            local.tee 10
            local.get 9
            local.get 8
            i32.store offset=3 align=2
          else
            local.get 9
            i32.load offset=1 align=2
            local.tee 11
            local.get 9
            local.get 8
            i32.store offset=1 align=2
          end
        end
        nop
        nop
        local.set 5
        local.set 4
        local.get 4
        local.get 5
        i32.const 1
        i32.add
        local.set 12
        local.tee 13
        local.get 13
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 13
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 13
            i32.load offset=3 align=2
            local.tee 14
            local.get 13
            local.get 12
            i32.store offset=3 align=2
          else
            local.get 13
            i32.load offset=1 align=2
            local.tee 15
            local.get 13
            local.get 12
            i32.store offset=1 align=2
          end
        end
        nop
        nop
        local.set 7
        local.set 6
        local.get 6
        local.get 6
        drop
        local.get 7
        drop
        local.get 4
        drop
        local.get 5
        drop
        local.get 2
        local.set 16
        local.get 16
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 16
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 16
            call 4
          else
            local.get 16
            call 6
          end
        end
        local.get 3
        drop)
      (func (;8;) (type 5) (param i32 i32 i32) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
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
        i32.eqz
        if (result i32)  ;; label = @1
          local.get 6
          local.tee 17
          local.get 17
          i32.const 0
          i32.const 0
          call 3
          local.get 17
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 17
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 17
              i32.load offset=3 align=2
              local.tee 18
            else
              local.get 17
              i32.load offset=1 align=2
              local.tee 19
            end
          end
          local.set 8
          local.set 20
          local.get 20
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 20
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 20
              call 4
            else
              local.get 20
              call 6
            end
          end
          local.get 8
        else
          i32.const 1
          global.get 1
          i32.add
          nop
          i32.const 0
          call 1
          local.set 21
          local.get 21
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
            i32.const 0
            global.get 1
            i32.add
            nop
            i32.const 0
            call 1
            local.set 22
            local.get 22
            nop
            block (param i32 i32) (result i32)  ;; label = @3
              local.set 14
              local.set 13
              local.get 13
              local.get 14
              nop
              local.set 16
              local.set 15
              local.get 16
              local.get 6
              nop
              local.get 15
              call_indirect (type 4)
              local.get 15
              drop
              local.get 16
              drop
              local.get 13
              local.get 14
              drop
              drop
            end
            local.get 7
            i32.const 1
            i32.sub
            nop
            nop
            local.get 11
            call_indirect (type 5)
            local.get 11
            drop
            local.get 12
            drop
            local.get 9
            local.get 10
            drop
            drop
          end
        end
        local.get 6
        drop
        local.get 7
        drop
        local.get 3
        local.set 23
        local.get 23
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 23
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 23
            call 4
          else
            local.get 23
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

    -----------fix_factorial[invalid]-----------
    FAILURE (InstrErr
     (error
      (BlockErr
       (error
        (ExpectedEqStack
         (Fold0
          (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
           (Prod
            ((CodeRef
              (FunctionType ()
               ((Prod
                 ((Ref (Base MM) (Ser (Var 0)))
                  (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) NoCopy ExDrop)
                   (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (Prod
                     ((CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                        ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                          (Prod
                           ((CodeRef
                             (FunctionType ()
                              ((Prod
                                ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                              ((Num (Int I32)))))
                            (Ref (Base MM) (Ser (Var 0)))))))))
                      (Ref (Base MM) (Ser (Var 0))))))))))
               ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                 (Prod
                  ((CodeRef
                    (FunctionType ()
                     ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                     ((Num (Int I32)))))
                   (Ref (Base MM) (Ser (Var 0)))))))))
             (Ref (Base MM) (Ser (Var 0))))))
          (Plug (Prod ((Atom I32) (Atom I32)))))))
       (instr
        (Fold
         (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) NoCopy ExDrop)
          (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
           (Prod
            ((CodeRef
              (FunctionType () ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
               ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                 (Prod
                  ((CodeRef
                    (FunctionType ()
                     ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                     ((Num (Int I32)))))
                   (Ref (Base MM) (Ser (Var 0)))))))))
             (Ref (Base MM) (Ser (Var 0)))))))))
       (env
        ((local_offset 1)
         (kinds
          ((VALTYPE (Prod ((Prod ((Atom I32) (Atom Ptr))))) NoCopy ExDrop)))
         (labels
          (((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
             (Prod
              ((CodeRef
                (FunctionType ()
                 ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                 ((Num (Int I32)))))
               (Ref (Base MM) (Ser (Var 0)))))))))
         (return
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (Prod
             ((CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32)))))
              (Ref (Base MM) (Ser (Var 0))))))))
         (functions
          ((FunctionType ()
            ((Prod
              ((Ref (Base MM)
                (Ser
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (Prod
                     ((CodeRef
                       (FunctionType ()
                        ((Prod
                          ((Ref (Base MM) (Ser (Var 0)))
                           (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                            (Prod
                             ((CodeRef
                               (FunctionType ()
                                ((Prod
                                  ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                                ((Num (Int I32)))))
                              (Ref (Base MM) (Ser (Var 0)))))))))
                        ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                          (Prod
                           ((CodeRef
                             (FunctionType ()
                              ((Prod
                                ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                              ((Num (Int I32)))))
                            (Ref (Base MM) (Ser (Var 0)))))))))
                      (Ref (Base MM) (Ser (Var 0))))))))))
               (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) NoCopy ExDrop)
                (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                 (Prod
                  ((CodeRef
                    (FunctionType ()
                     ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                     ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                       (Prod
                        ((CodeRef
                          (FunctionType ()
                           ((Prod
                             ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                           ((Num (Int I32)))))
                         (Ref (Base MM) (Ser (Var 0)))))))))
                   (Ref (Base MM) (Ser (Var 0))))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (Prod
               ((CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Ref (Base MM) (Ser (Var 0))))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (Prod
                 ((CodeRef
                   (FunctionType ()
                    ((Prod
                      ((Ref (Base MM) (Ser (Var 0)))
                       (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                        (Prod
                         ((CodeRef
                           (FunctionType ()
                            ((Prod
                              ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                            ((Num (Int I32)))))
                          (Ref (Base MM) (Ser (Var 0)))))))))
                    ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                      (Prod
                       ((CodeRef
                         (FunctionType ()
                          ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                          ((Num (Int I32)))))
                        (Ref (Base MM) (Ser (Var 0)))))))))
                  (Ref (Base MM) (Ser (Var 0)))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (Prod
               ((CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Ref (Base MM) (Ser (Var 0))))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM)
                (Ser
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (Prod
                     ((CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                        ((Num (Int I32)))))
                      (Ref (Base MM) (Ser (Var 0))))))))))
               (Num (Int I32)))))
            ((Num (Int I32))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (Prod
                 ((CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32)))))
                  (Ref (Base MM) (Ser (Var 0)))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (Prod
               ((CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Ref (Base MM) (Ser (Var 0))))))))
           (FunctionType () () ((Num (Int I32))))))
         (table
          ((FunctionType ()
            ((Prod
              ((Ref (Base MM)
                (Ser
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (Prod
                     ((CodeRef
                       (FunctionType ()
                        ((Prod
                          ((Ref (Base MM) (Ser (Var 0)))
                           (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                            (Prod
                             ((CodeRef
                               (FunctionType ()
                                ((Prod
                                  ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                                ((Num (Int I32)))))
                              (Ref (Base MM) (Ser (Var 0)))))))))
                        ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                          (Prod
                           ((CodeRef
                             (FunctionType ()
                              ((Prod
                                ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                              ((Num (Int I32)))))
                            (Ref (Base MM) (Ser (Var 0)))))))))
                      (Ref (Base MM) (Ser (Var 0))))))))))
               (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) NoCopy ExDrop)
                (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                 (Prod
                  ((CodeRef
                    (FunctionType ()
                     ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                     ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                       (Prod
                        ((CodeRef
                          (FunctionType ()
                           ((Prod
                             ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                           ((Num (Int I32)))))
                         (Ref (Base MM) (Ser (Var 0)))))))))
                   (Ref (Base MM) (Ser (Var 0))))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (Prod
               ((CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Ref (Base MM) (Ser (Var 0))))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (Prod
                 ((CodeRef
                   (FunctionType ()
                    ((Prod
                      ((Ref (Base MM) (Ser (Var 0)))
                       (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                        (Prod
                         ((CodeRef
                           (FunctionType ()
                            ((Prod
                              ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                            ((Num (Int I32)))))
                          (Ref (Base MM) (Ser (Var 0)))))))))
                    ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                      (Prod
                       ((CodeRef
                         (FunctionType ()
                          ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                          ((Num (Int I32)))))
                        (Ref (Base MM) (Ser (Var 0)))))))))
                  (Ref (Base MM) (Ser (Var 0)))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (Prod
               ((CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Ref (Base MM) (Ser (Var 0))))))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM)
                (Ser
                 (Prod
                  ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (Prod
                     ((CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                        ((Num (Int I32)))))
                      (Ref (Base MM) (Ser (Var 0))))))))))
               (Num (Int I32)))))
            ((Num (Int I32))))
           (FunctionType ()
            ((Prod
              ((Ref (Base MM) (Ser (Prod ())))
               (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (Prod
                 ((CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32)))))
                  (Ref (Base MM) (Ser (Var 0)))))))))
            ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (Prod
               ((CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Ref (Base MM) (Ser (Var 0))))))))))
         (lfx (InferFx))))
       (state
        ((locals
          ((Plug (Prod ((Atom I32) (Atom I32) (Atom I32))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32) (Atom I32))))
           (Plug (Prod ())) (Plug (Prod ((Atom I32) (Atom I32))))
           (Plug (Prod ((Atom I32) (Atom I32))))
           (Plug (Prod ((Atom I32) (Atom I32))))
           (CodeRef
            (FunctionType ()
             ((Prod
               ((Ref (Base MM) (Ser (Var 0)))
                (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) NoCopy ExDrop)
                 (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (Prod
                   ((CodeRef
                     (FunctionType ()
                      ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                      ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                        (Prod
                         ((CodeRef
                           (FunctionType ()
                            ((Prod
                              ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                            ((Num (Int I32)))))
                          (Ref (Base MM) (Ser (Var 0)))))))))
                    (Ref (Base MM) (Ser (Var 0))))))))))
             ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
               (Prod
                ((CodeRef
                  (FunctionType ()
                   ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                   ((Num (Int I32)))))
                 (Ref (Base MM) (Ser (Var 0)))))))))
           (Plug (Prod ((Atom I32))))))
         (stack
          ((Plug (Prod ((Atom I32) (Atom I32)))) (Ref (Base MM) (Ser (Var 0)))))))))
     (instr
      (Unpack
       (ValType
        ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
          (Prod
           ((CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32)))))
            (Ref (Base MM) (Ser (Var 0))))))))
       InferFx
       ((LocalSet 6) (LocalGet 6 Follow) Ungroup (LocalSet 8) (LocalSet 7)
        (LocalGet 8 Follow) (LocalGet 5 Follow)
        (Fold
         (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) NoCopy ExDrop)
          (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
           (Prod
            ((CodeRef
              (FunctionType () ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
               ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                 (Prod
                  ((CodeRef
                    (FunctionType ()
                     ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                     ((Num (Int I32)))))
                   (Ref (Base MM) (Ser (Var 0)))))))))
             (Ref (Base MM) (Ser (Var 0))))))))
        (Group 2) (LocalGet 7 Follow) CallIndirect (LocalGet 7 Move) Drop
        (LocalGet 8 Move) Drop (LocalGet 6 Move) Drop)))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return
        ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
          (Prod
           ((CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32)))))
            (Ref (Base MM) (Ser (Var 0))))))))
       (functions
        ((FunctionType ()
          ((Prod
            ((Ref (Base MM)
              (Ser
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (Prod
                   ((CodeRef
                     (FunctionType ()
                      ((Prod
                        ((Ref (Base MM) (Ser (Var 0)))
                         (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                          (Prod
                           ((CodeRef
                             (FunctionType ()
                              ((Prod
                                ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                              ((Num (Int I32)))))
                            (Ref (Base MM) (Ser (Var 0)))))))))
                      ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                        (Prod
                         ((CodeRef
                           (FunctionType ()
                            ((Prod
                              ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                            ((Num (Int I32)))))
                          (Ref (Base MM) (Ser (Var 0)))))))))
                    (Ref (Base MM) (Ser (Var 0))))))))))
             (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) NoCopy ExDrop)
              (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
               (Prod
                ((CodeRef
                  (FunctionType ()
                   ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                   ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                     (Prod
                      ((CodeRef
                        (FunctionType ()
                         ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                         ((Num (Int I32)))))
                       (Ref (Base MM) (Ser (Var 0)))))))))
                 (Ref (Base MM) (Ser (Var 0))))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (Prod
             ((CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32)))))
              (Ref (Base MM) (Ser (Var 0))))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (Prod
               ((CodeRef
                 (FunctionType ()
                  ((Prod
                    ((Ref (Base MM) (Ser (Var 0)))
                     (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                      (Prod
                       ((CodeRef
                         (FunctionType ()
                          ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                          ((Num (Int I32)))))
                        (Ref (Base MM) (Ser (Var 0)))))))))
                  ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (Prod
                     ((CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                        ((Num (Int I32)))))
                      (Ref (Base MM) (Ser (Var 0)))))))))
                (Ref (Base MM) (Ser (Var 0)))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (Prod
             ((CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32)))))
              (Ref (Base MM) (Ser (Var 0))))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM)
              (Ser
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (Prod
                   ((CodeRef
                     (FunctionType ()
                      ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                      ((Num (Int I32)))))
                    (Ref (Base MM) (Ser (Var 0))))))))))
             (Num (Int I32)))))
          ((Num (Int I32))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (Prod
               ((CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Ref (Base MM) (Ser (Var 0)))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (Prod
             ((CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32)))))
              (Ref (Base MM) (Ser (Var 0))))))))
         (FunctionType () () ((Num (Int I32))))))
       (table
        ((FunctionType ()
          ((Prod
            ((Ref (Base MM)
              (Ser
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (Prod
                   ((CodeRef
                     (FunctionType ()
                      ((Prod
                        ((Ref (Base MM) (Ser (Var 0)))
                         (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                          (Prod
                           ((CodeRef
                             (FunctionType ()
                              ((Prod
                                ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                              ((Num (Int I32)))))
                            (Ref (Base MM) (Ser (Var 0)))))))))
                      ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                        (Prod
                         ((CodeRef
                           (FunctionType ()
                            ((Prod
                              ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                            ((Num (Int I32)))))
                          (Ref (Base MM) (Ser (Var 0)))))))))
                    (Ref (Base MM) (Ser (Var 0))))))))))
             (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) NoCopy ExDrop)
              (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
               (Prod
                ((CodeRef
                  (FunctionType ()
                   ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                   ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                     (Prod
                      ((CodeRef
                        (FunctionType ()
                         ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                         ((Num (Int I32)))))
                       (Ref (Base MM) (Ser (Var 0)))))))))
                 (Ref (Base MM) (Ser (Var 0))))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (Prod
             ((CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32)))))
              (Ref (Base MM) (Ser (Var 0))))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (Prod
               ((CodeRef
                 (FunctionType ()
                  ((Prod
                    ((Ref (Base MM) (Ser (Var 0)))
                     (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                      (Prod
                       ((CodeRef
                         (FunctionType ()
                          ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                          ((Num (Int I32)))))
                        (Ref (Base MM) (Ser (Var 0)))))))))
                  ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                    (Prod
                     ((CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                        ((Num (Int I32)))))
                      (Ref (Base MM) (Ser (Var 0)))))))))
                (Ref (Base MM) (Ser (Var 0)))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (Prod
             ((CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32)))))
              (Ref (Base MM) (Ser (Var 0))))))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM)
              (Ser
               (Prod
                ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                  (Prod
                   ((CodeRef
                     (FunctionType ()
                      ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                      ((Num (Int I32)))))
                    (Ref (Base MM) (Ser (Var 0))))))))))
             (Num (Int I32)))))
          ((Num (Int I32))))
         (FunctionType ()
          ((Prod
            ((Ref (Base MM) (Ser (Prod ())))
             (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
              (Prod
               ((CodeRef
                 (FunctionType ()
                  ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                  ((Num (Int I32)))))
                (Ref (Base MM) (Ser (Var 0)))))))))
          ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
            (Prod
             ((CodeRef
               (FunctionType ()
                ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                ((Num (Int I32)))))
              (Ref (Base MM) (Ser (Var 0))))))))))
       (lfx ())))
     (state
      ((locals
        ((Plug (Prod ((Atom I32) (Atom I32) (Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32) (Atom I32))))
         (Plug (Prod ())) (Plug (Prod ((Atom I32) (Atom I32))))
         (Plug (Prod ((Atom I32) (Atom I32))))
         (Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32))))))
       (stack
        ((Exists
          (Type (VALTYPE (Prod ((Prod ((Atom I32) (Atom Ptr))))) NoCopy ExDrop))
          (Prod
           ((CodeRef
             (FunctionType ()
              ((Prod
                ((Ref (Base MM) (Ser (Var 0)))
                 (Rec (VALTYPE (Prod ((Atom I32) (Atom Ptr))) NoCopy ExDrop)
                  (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                   (Prod
                    ((CodeRef
                      (FunctionType ()
                       ((Prod ((Ref (Base MM) (Ser (Var 0))) (Var 1))))
                       ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                         (Prod
                          ((CodeRef
                            (FunctionType ()
                             ((Prod
                               ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                             ((Num (Int I32)))))
                           (Ref (Base MM) (Ser (Var 0)))))))))
                     (Ref (Base MM) (Ser (Var 0))))))))))
              ((Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
                (Prod
                 ((CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32)))))
                  (Ref (Base MM) (Ser (Var 0)))))))))
            (Ref (Base MM) (Ser (Var 0)))))))))))
    -----------unboxed_list[invalid]-----------
    FAILURE (Codegen
     (CannotResolveRepOfRecTypeWithoutIndirection (Var (0 ("\206\177")))))
    -----------boxed_list-----------
    FAILURE (InstrErr
     (error
      (CannotInferLfx
       (Case
        (1 3
         ((Plug
           (Prod
            ((Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32))))
          (Ref (Base MM) (Ser (Prod ())))
          (Plug (Prod ((Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32))))
          (Plug (Prod ((Atom I32) (Atom I32))))
          (Plug (Prod ((Atom I32) (Atom I32) (Atom I32)))) (Plug (Prod ()))
          (Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
          (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32) (Atom I32))))
          (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
          (Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
          (Plug (Prod ((Atom I32))))
          (Plug (Prod ((Atom I32) (Atom I32) (Atom I32)))))
         ((Plug
           (Prod
            ((Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32))))
          (Ref (Base MM) (Ser (Prod ())))
          (Plug (Prod ((Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32))))
          (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
           (Prod
            ((CodeRef
              (FunctionType ()
               ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
               ((Num (Int I32)))))
             (Ref (Base MM) (Ser (Var 0))))))
          (Plug (Prod ((Atom I32) (Atom I32) (Atom I32)))) (Plug (Prod ()))
          (Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
          (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32) (Atom I32))))
          (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
          (Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
          (Plug (Prod ((Atom I32))))
          (Plug (Prod ((Atom I32) (Atom I32) (Atom I32)))))))))
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
         (Unpack (ValType ((Num (Int I32)))) InferFx
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
                    (Prod
                     ((CodeRef
                       (FunctionType ()
                        ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                        ((Num (Int I32)))))
                      (Ref (Base MM) (Ser (Var 0))))))
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
          (ValType
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
                (Prod
                 ((CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32)))))
                  (Ref (Base MM) (Ser (Var 0))))))
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
                (Prod
                 ((CodeRef
                   (FunctionType ()
                    ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
                    ((Num (Int I32)))))
                  (Ref (Base MM) (Ser (Var 0))))))
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
        ((Plug
          (Prod
           ((Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32))))
         (Ref (Base MM) (Ser (Prod ())))
         (Plug (Prod ((Atom I32) (Atom I32) (Atom I32) (Atom I32) (Atom I32))))
         (Exists (Type (VALTYPE (Atom Ptr) NoCopy ExDrop))
          (Prod
           ((CodeRef
             (FunctionType ()
              ((Prod ((Ref (Base MM) (Ser (Var 0))) (Num (Int I32)))))
              ((Num (Int I32)))))
            (Ref (Base MM) (Ser (Var 0))))))
         (Plug (Prod ((Atom I32) (Atom I32) (Atom I32)))) (Plug (Prod ()))
         (Plug (Prod ((Atom I32) (Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32) (Atom I32))))
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
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func (param i32 i32 i32 i32 i32) (result i32 i32)))
      (type (;5;) (func (param i32 i32) (result i32 i32)))
      (type (;6;) (func (param i32 i32 i32) (result i32)))
      (type (;7;) (func (result i32)))
      (type (;8;) (func))
      (type (;9;) (func (param i32) (result i32 i32)))
      (type (;10;) (func (result i32 i32)))
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
      (func (;7;) (type 4) (param i32 i32 i32 i32 i32) (result i32 i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        local.get 0
        local.get 1
        local.get 2
        local.get 3
        local.get 4
        nop
        local.set 9
        local.set 8
        local.set 7
        local.set 6
        local.set 5
        local.get 6
        local.get 7
        local.get 8
        local.get 9
        nop
        local.set 13
        local.set 12
        local.set 11
        local.set 10
        local.get 10
        local.get 11
        local.set 21
        block (param i32) (result i32 i32)  ;; label = @1
          block (param i32)  ;; label = @2
            block (param i32)  ;; label = @3
              block (param i32)  ;; label = @4
                br_table 2 (;@2;) 1 (;@3;) 0 (;@4;)
              end
              unreachable
            end
            local.get 21
            local.set 14
            i32.const 0
            global.get 1
            i32.add
            nop
            i32.const 0
            call 1
            local.set 22
            local.get 22
            nop
            block (param i32 i32) (result i32 i32)  ;; label = @3
              local.set 16
              local.set 15
              local.get 15
              local.get 16
              nop
              local.set 18
              local.set 17
              local.get 18
              local.get 14
              local.tee 23
              local.get 23
              i32.const 0
              i32.const 0
              call 3
              local.get 23
              i32.const 1
              i32.const 0
              call 3
              local.get 23
              i32.const 1
              i32.and
              i32.eqz
              if (result i32 i32)  ;; label = @4
                unreachable
              else
                local.get 23
                i32.const 2
                i32.and
                i32.eqz
                if (result i32 i32)  ;; label = @5
                  local.get 23
                  i32.load offset=3 align=2
                  local.tee 24
                  local.get 24
                  i32.const 1
                  i32.and
                  i32.eqz
                  if (param i32) (result i32)  ;; label = @6
                  else
                    local.get 24
                    i32.const 2
                    i32.and
                    i32.eqz
                    if (param i32) (result i32)  ;; label = @7
                    end
                  end
                  local.get 23
                  i32.load offset=7 align=2
                  local.tee 25
                else
                  local.get 23
                  i32.load offset=1 align=2
                  local.tee 26
                  local.get 26
                  i32.const 1
                  i32.and
                  i32.eqz
                  if (param i32) (result i32)  ;; label = @6
                  else
                    local.get 26
                    i32.const 2
                    i32.and
                    i32.eqz
                    if (param i32) (result i32)  ;; label = @7
                    else
                      call 5
                    end
                  end
                  local.get 23
                  i32.load offset=5 align=2
                  local.tee 27
                end
              end
              local.set 20
              local.set 19
              local.set 28
              local.get 28
              i32.const 1
              i32.and
              i32.eqz
              if  ;; label = @4
              else
                local.get 28
                i32.const 2
                i32.and
                i32.eqz
                if  ;; label = @5
                  local.get 28
                  call 4
                else
                  local.get 28
                  call 6
                end
              end
              local.get 19
              local.get 20
              local.get 12
              local.get 13
              nop
              nop
              local.get 17
              call_indirect (type 4)
              local.get 17
              drop
              local.get 18
              drop
              local.get 15
              local.get 16
              drop
              drop
            end
            local.set 30
            local.set 29
            i32.const 2
            call 1
            local.set 31
            local.get 31
            i32.const 0
            i32.const 0
            call 3
            local.get 31
            i32.const 1
            i32.const 1
            call 3
            local.get 31
            local.get 30
            i32.store offset=3 align=2
            local.get 31
            local.get 29
            i32.store offset=7 align=2
            local.get 31
            local.set 32
            i32.const 1
            local.get 32
            local.get 14
            drop
            br 2 (;@0;)
          end
          local.get 12
          local.get 13
          br 1 (;@0;)
        end
        local.get 10
        local.get 11
        drop
        drop
        local.get 12
        local.get 13
        drop
        drop
        local.get 5
        local.set 33
        local.get 33
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 33
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 33
            call 4
          else
            local.get 33
            call 6
          end
        end
        local.get 6
        local.get 7
        local.get 8
        local.get 9
        drop
        drop
        drop
        drop)
      (func (;8;) (type 5) (param i32 i32) (result i32 i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        local.get 0
        local.get 1
        nop
        local.set 3
        local.set 2
        local.get 3
        i32.eqz
        if (result i32 i32)  ;; label = @1
          nop
          i32.const 0
          local.get 8
        else
          i32.const 1
          global.get 1
          i32.add
          nop
          i32.const 0
          call 1
          local.set 9
          local.get 9
          nop
          block (param i32 i32) (result i32 i32)  ;; label = @2
            local.set 5
            local.set 4
            local.get 4
            local.get 5
            nop
            local.set 7
            local.set 6
            local.get 7
            local.get 3
            i32.const 1
            i32.sub
            nop
            local.get 6
            call_indirect (type 5)
            local.get 6
            drop
            local.get 7
            drop
            local.get 4
            local.get 5
            drop
            drop
          end
          local.set 11
          local.set 10
          i32.const 2
          call 1
          local.set 12
          local.get 12
          i32.const 0
          i32.const 0
          call 3
          local.get 12
          i32.const 1
          i32.const 1
          call 3
          local.get 12
          local.get 11
          i32.store offset=3 align=2
          local.get 12
          local.get 10
          i32.store offset=7 align=2
          local.get 12
          local.set 13
          i32.const 1
          local.get 13
        end
        local.get 2
        local.set 14
        local.get 14
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 14
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 14
            call 4
          else
            local.get 14
            call 6
          end
        end
        local.get 3
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
        local.set 13
        block (param i32) (result i32)  ;; label = @1
          block (param i32)  ;; label = @2
            block (param i32)  ;; label = @3
              block (param i32)  ;; label = @4
                br_table 2 (;@2;) 1 (;@3;) 0 (;@4;)
              end
              unreachable
            end
            local.get 13
            local.set 6
            i32.const 1
            i32.const 2
            global.get 1
            i32.add
            nop
            i32.const 0
            call 1
            local.set 14
            local.get 14
            nop
            block (param i32 i32) (result i32)  ;; label = @3
              local.set 8
              local.set 7
              local.get 7
              local.get 8
              nop
              local.set 10
              local.set 9
              local.get 10
              local.get 6
              local.tee 15
              local.get 15
              i32.const 0
              i32.const 0
              call 3
              local.get 15
              i32.const 1
              i32.const 0
              call 3
              local.get 15
              i32.const 1
              i32.and
              i32.eqz
              if (result i32 i32)  ;; label = @4
                unreachable
              else
                local.get 15
                i32.const 2
                i32.and
                i32.eqz
                if (result i32 i32)  ;; label = @5
                  local.get 15
                  i32.load offset=3 align=2
                  local.tee 16
                  local.get 16
                  i32.const 1
                  i32.and
                  i32.eqz
                  if (param i32) (result i32)  ;; label = @6
                  else
                    local.get 16
                    i32.const 2
                    i32.and
                    i32.eqz
                    if (param i32) (result i32)  ;; label = @7
                    end
                  end
                  local.get 15
                  i32.load offset=7 align=2
                  local.tee 17
                else
                  local.get 15
                  i32.load offset=1 align=2
                  local.tee 18
                  local.get 18
                  i32.const 1
                  i32.and
                  i32.eqz
                  if (param i32) (result i32)  ;; label = @6
                  else
                    local.get 18
                    i32.const 2
                    i32.and
                    i32.eqz
                    if (param i32) (result i32)  ;; label = @7
                    else
                      call 5
                    end
                  end
                  local.get 15
                  i32.load offset=5 align=2
                  local.tee 19
                end
              end
              local.set 12
              local.set 11
              local.set 20
              local.get 20
              i32.const 1
              i32.and
              i32.eqz
              if  ;; label = @4
              else
                local.get 20
                i32.const 2
                i32.and
                i32.eqz
                if  ;; label = @5
                  local.get 20
                  call 4
                else
                  local.get 20
                  call 6
                end
              end
              local.get 11
              local.get 12
              nop
              local.get 9
              call_indirect (type 6)
              local.get 9
              drop
              local.get 10
              drop
              local.get 7
              local.get 8
              drop
              drop
            end
            i32.add
            local.get 6
            drop
            br 2 (;@0;)
          end
          i32.const 0
          br 1 (;@0;)
        end
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
      (func (;10;) (type 7) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 1
        global.get 1
        i32.add
        nop
        i32.const 0
        call 1
        local.set 22
        local.get 22
        nop
        block (param i32 i32) (result i32 i32)  ;; label = @1
          local.set 1
          local.set 0
          local.get 0
          local.get 1
          nop
          local.set 3
          local.set 2
          local.get 3
          i32.const 6
          nop
          local.get 2
          call_indirect (type 5)
          local.get 2
          drop
          local.get 3
          drop
          local.get 0
          local.get 1
          drop
          drop
        end
        local.set 5
        local.set 4
        i32.const 1
        global.get 1
        i32.add
        nop
        i32.const 0
        call 1
        local.set 23
        local.get 23
        nop
        block (param i32 i32) (result i32 i32)  ;; label = @1
          local.set 7
          local.set 6
          local.get 6
          local.get 7
          nop
          local.set 9
          local.set 8
          local.get 9
          i32.const 7
          nop
          local.get 8
          call_indirect (type 5)
          local.get 8
          drop
          local.get 9
          drop
          local.get 6
          local.get 7
          drop
          drop
        end
        local.set 11
        local.set 10
        i32.const 0
        global.get 1
        i32.add
        nop
        i32.const 0
        call 1
        local.set 24
        local.get 24
        nop
        block (param i32 i32) (result i32 i32)  ;; label = @1
          local.set 13
          local.set 12
          local.get 12
          local.get 13
          nop
          local.set 15
          local.set 14
          local.get 15
          local.get 4
          local.get 5
          local.get 10
          local.get 11
          nop
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
        local.set 17
        local.set 16
        i32.const 2
        global.get 1
        i32.add
        nop
        i32.const 0
        call 1
        local.set 25
        local.get 25
        nop
        block (param i32 i32) (result i32)  ;; label = @1
          local.set 19
          local.set 18
          local.get 18
          local.get 19
          nop
          local.set 21
          local.set 20
          local.get 21
          local.get 16
          local.get 17
          nop
          local.get 20
          call_indirect (type 6)
          local.get 20
          drop
          local.get 21
          drop
          local.get 18
          local.get 19
          drop
          drop
        end
        local.get 16
        local.get 17
        drop
        drop
        local.get 10
        local.get 11
        drop
        drop
        local.get 4
        local.get 5
        drop
        drop)
      (func (;11;) (type 8)
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
      (export "_start" (func 10))
      (export "__rw_table_func_7" (func 7))
      (export "__rw_table_func_8" (func 8))
      (export "__rw_table_func_9" (func 9))
      (start 11))

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
