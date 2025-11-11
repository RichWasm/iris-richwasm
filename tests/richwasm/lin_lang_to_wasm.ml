open! Base
open! Stdlib.Format
open! Test_support
module AnnRichWasm = Richwasm_common.Annotated_syntax

include Test_runner.MultiOutputter.Make (struct
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
    |> Richwasm_common.Main.serialize
    |> String.of_char_list

  let syntax_pipeline x =
    x |> Main.compile_ast |> or_fail_pp Main.CompileErr.pp |> elab

  let string_pipeline s = s |> Parse.from_string_exn |> syntax_pipeline
  let examples = Test_examples.Lin_lang.all
  let pp = Meta.Wasm2wat.pp_as_wat
  let pp_raw = fun ff x -> fprintf ff "\"%s\"" (String.escaped x)
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
    {| "\000asm\001\000\000\000\001\028\006`\002\127\127\000`\001\127\001\127`\003\127\127\127\000`\001\127\000`\000\001\127`\000\000\002\221\001\011\brichwasm\005mmmem\002\000\000\brichwasm\005gcmem\002\000\000\brichwasm\ttablenext\003\127\001\brichwasm\btableset\000\000\brichwasm\007mmalloc\000\001\brichwasm\007gcalloc\000\001\brichwasm\007setflag\000\002\brichwasm\004free\000\003\brichwasm\012registerroot\000\001\brichwasm\014unregisterroot\000\003\brichwasm\005table\001p\000\000\003\003\002\004\005\006\006\001\127\001A\000\011\007\004\001\000\000\007\b\001\b\n\020\002\004\000A\001\011\r\000#\000$\001#\001A\000j$\000\011" |}]

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
    FAILURE (TODO memory)
    -----------add_tup_ref-----------
    FAILURE (TODO memory)
    -----------print_10-----------
    FAILURE (InvalidTableIdx 0)
    -----------factorial_program-----------
    FAILURE (TODO memory)
    -----------safe_div-----------
    FAILURE (TODO "check lfx")
    -----------incr_n-----------
    FAILURE (TODO memory)
    -----------fix_factorial[invalid]-----------
    FAILURE (PopEmptyStack LocalSet)
    -----------unboxed_list[invalid]-----------
    FAILURE (Codegen
     (CannotResolveRepOfRecTypeWithoutIndirection (Var (0 ("\206\177")))))
    -----------boxed_list-----------
    FAILURE (PopEmptyStack LocalSet)
    -----------peano_3-----------
    FAILURE (TODO memory)
    -----------peano-----------
    FAILURE (TODO elab_local_fx)
    -----------mini_zip-----------
    FAILURE (TODO memory) |}]
