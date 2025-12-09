open! Base
open! Stdlib.Format
open! Test_support
module AnnRichWasm = Richwasm_common.Annotated_syntax

include Test_runner.MultiOutputter.Make (struct
  include Test_runner.MultiOutputter.DefaultConfig
  open Test_utils
  open Richwasm_mini_ml

  type syntax = Syntax.Source.Module.t
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
    x |> Convert.cc_module |> Codegen.compile_module |> elab

  let string_pipeline s = s |> Parse.from_string_exn |> syntax_pipeline
  let examples = Test_examples.Mini_ml.all

  let pp ff x =
    match Meta.Wat2wasm.wat2wasm x with
    | Ok wasm -> Meta.Wasm2wat.pp_as_wat ff wasm
    | Error err ->
        fprintf ff "FAILURE wat2wasm2wat validation!\n";
        (match Meta.Wat2wasm.wat2wasm ~check:false x with
        | Ok wasm ->
            Meta.Wasm2wat.pp_as_wat ~check:false ff wasm;
            fprintf ff "Wat2wasm Error: %s" err
        | Error err -> fprintf ff "UNCHECKED Wat2wasm Error: %s" err)

  let pp_raw ff x = fprintf ff "%s" x
end)

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
      (func (;7;) (type 1) (param i32) (result i32)
        (local i32)
        i32.const 1
        i32.const 1
        i32.shl)
      (func (;8;) (type 4)
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
      (export "_start" (func 7))
      (start 8))

    -----------tuple-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func))
      (type (;5;) (func (param i32 i32)))
      (type (;6;) (func (param i32 i32)))
      (type (;7;) (func (param i32 i32)))
      (type (;8;) (func (param i32 i32)))
      (type (;9;) (func (param i32 i32)))
      (type (;10;) (func (param i32 i32)))
      (type (;11;) (func (param i32 i32)))
      (type (;12;) (func (param i32 i32)))
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
        (local i32 i32 i32 i32 i32 i32)
        i32.const 4
        i32.const 1
        i32.shl
        i32.const 3
        i32.const 1
        i32.shl
        i32.const 2
        i32.const 1
        i32.shl
        i32.const 1
        i32.const 1
        i32.shl
        nop
        local.set 4
        local.set 3
        local.set 2
        local.set 1
        i32.const 4
        call 2
        local.set 5
        local.get 5
        i32.const 0
        i32.const 1
        call 3
        local.get 5
        i32.const 1
        i32.const 1
        call 3
        local.get 5
        i32.const 2
        i32.const 1
        call 3
        local.get 5
        i32.const 3
        i32.const 1
        call 3
        local.get 5
        local.get 4
        local.get 4
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store offset=1 align=2
        else
          local.get 4
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store offset=1 align=2
          else
            i32.load offset=1 align=2
            i32.store offset=1 align=2
            local.get 4
            call 6
          end
        end
        local.get 5
        local.get 3
        local.get 3
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store offset=5 align=2
        else
          local.get 3
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store offset=5 align=2
          else
            i32.load offset=1 align=2
            i32.store offset=5 align=2
            local.get 3
            call 6
          end
        end
        local.get 5
        local.get 2
        local.get 2
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store offset=9 align=2
        else
          local.get 2
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store offset=9 align=2
          else
            i32.load offset=1 align=2
            i32.store offset=9 align=2
            local.get 2
            call 6
          end
        end
        local.get 5
        local.get 1
        local.get 1
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store offset=13 align=2
        else
          local.get 1
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store offset=13 align=2
          else
            i32.load offset=1 align=2
            i32.store offset=13 align=2
            local.get 1
            call 6
          end
        end
        local.get 5
        call 5)
      (func (;8;) (type 4)
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
      (export "_start" (func 7))
      (start 8))

    -----------tuple_nested-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func))
      (type (;5;) (func (param i32 i32)))
      (type (;6;) (func (param i32 i32)))
      (type (;7;) (func (param i32 i32)))
      (type (;8;) (func (param i32 i32)))
      (type (;9;) (func (param i32 i32)))
      (type (;10;) (func (param i32 i32)))
      (type (;11;) (func (param i32 i32)))
      (type (;12;) (func (param i32 i32)))
      (type (;13;) (func (param i32 i32)))
      (type (;14;) (func (param i32 i32)))
      (type (;15;) (func (param i32 i32)))
      (type (;16;) (func (param i32 i32)))
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
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 4
        i32.const 1
        i32.shl
        i32.const 3
        i32.const 1
        i32.shl
        nop
        local.set 2
        local.set 1
        i32.const 2
        call 2
        local.set 3
        local.get 3
        i32.const 0
        i32.const 1
        call 3
        local.get 3
        i32.const 1
        i32.const 1
        call 3
        local.get 3
        local.get 2
        local.get 2
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store offset=1 align=2
        else
          local.get 2
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store offset=1 align=2
          else
            i32.load offset=1 align=2
            i32.store offset=1 align=2
            local.get 2
            call 6
          end
        end
        local.get 3
        local.get 1
        local.get 1
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store offset=5 align=2
        else
          local.get 1
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store offset=5 align=2
          else
            i32.load offset=1 align=2
            i32.store offset=5 align=2
            local.get 1
            call 6
          end
        end
        local.get 3
        call 5
        i32.const 2
        i32.const 1
        i32.shl
        i32.const 1
        i32.const 1
        i32.shl
        nop
        local.set 5
        local.set 4
        i32.const 2
        call 2
        local.set 6
        local.get 6
        i32.const 0
        i32.const 1
        call 3
        local.get 6
        i32.const 1
        i32.const 1
        call 3
        local.get 6
        local.get 5
        local.get 5
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store offset=1 align=2
        else
          local.get 5
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store offset=1 align=2
          else
            i32.load offset=1 align=2
            i32.store offset=1 align=2
            local.get 5
            call 6
          end
        end
        local.get 6
        local.get 4
        local.get 4
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store offset=5 align=2
        else
          local.get 4
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store offset=5 align=2
          else
            i32.load offset=1 align=2
            i32.store offset=5 align=2
            local.get 4
            call 6
          end
        end
        local.get 6
        call 5
        nop
        local.set 8
        local.set 7
        i32.const 2
        call 2
        local.set 9
        local.get 9
        i32.const 0
        i32.const 1
        call 3
        local.get 9
        i32.const 1
        i32.const 1
        call 3
        local.get 9
        local.get 8
        local.get 8
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store offset=1 align=2
        else
          local.get 8
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store offset=1 align=2
          else
            i32.load offset=1 align=2
            i32.store offset=1 align=2
            local.get 8
            call 6
          end
        end
        local.get 9
        local.get 7
        local.get 7
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store offset=5 align=2
        else
          local.get 7
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store offset=5 align=2
          else
            i32.load offset=1 align=2
            i32.store offset=5 align=2
            local.get 7
            call 6
          end
        end
        local.get 9
        call 5)
      (func (;8;) (type 4)
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
      (export "_start" (func 7))
      (start 8))

    -----------tuple_project-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func))
      (type (;5;) (func (param i32 i32)))
      (type (;6;) (func (param i32 i32)))
      (type (;7;) (func (param i32 i32)))
      (type (;8;) (func (param i32 i32)))
      (type (;9;) (func (param i32) (result i32)))
      (type (;10;) (func (param i32) (result i32)))
      (type (;11;) (func (param i32) (result i32)))
      (type (;12;) (func (param i32) (result i32)))
      (type (;13;) (func))
      (type (;14;) (func))
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
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 7
        i32.const 1
        i32.shl
        i32.const 42
        i32.const 1
        i32.shl
        nop
        local.set 3
        local.set 2
        i32.const 2
        call 2
        local.set 4
        local.get 4
        i32.const 0
        i32.const 1
        call 3
        local.get 4
        i32.const 1
        i32.const 1
        call 3
        local.get 4
        local.get 3
        local.get 3
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store offset=1 align=2
        else
          local.get 3
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store offset=1 align=2
          else
            i32.load offset=1 align=2
            i32.store offset=1 align=2
            local.get 3
            call 6
          end
        end
        local.get 4
        local.get 2
        local.get 2
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store offset=5 align=2
        else
          local.get 2
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store offset=5 align=2
          else
            i32.load offset=1 align=2
            i32.store offset=5 align=2
            local.get 2
            call 6
          end
        end
        local.get 4
        call 5
        local.tee 5
        local.get 5
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 5
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 5
            i32.load offset=7 align=2
            local.tee 6
            local.get 6
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 6
              i32.const 2
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                i32.load offset=1 align=2
                call 5
              end
            end
          else
            local.get 5
            i32.load offset=5 align=2
            local.tee 7
            local.get 7
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 7
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
        local.set 1
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
        local.get 1)
      (func (;8;) (type 4)
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
      (export "_start" (func 7))
      (start 8))

    -----------sum_unit-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func))
      (type (;5;) (func (param i32 i32)))
      (type (;6;) (func (param i32 i32)))
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
        (local i32 i32 i32 i32 i32)
        nop
        i32.const 0
        call 2
        local.set 1
        local.get 1
        call 5
        local.set 2
        i32.const 2
        call 2
        local.set 3
        local.get 3
        i32.const 1
        i32.const 1
        call 3
        i32.const 0
        local.set 4
        local.get 3
        local.get 4
        i32.store offset=1 align=2
        local.get 3
        local.get 2
        local.get 2
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store offset=5 align=2
        else
          local.get 2
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store offset=5 align=2
          else
            i32.load offset=1 align=2
            i32.store offset=5 align=2
            local.get 2
            call 6
          end
        end
        local.get 3
        call 5)
      (func (;8;) (type 4)
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
      (export "_start" (func 7))
      (start 8))

    -----------sum_option-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func))
      (type (;5;) (func (param i32 i32)))
      (type (;6;) (func (param i32 i32)))
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
        (local i32 i32 i32 i32)
        i32.const 15
        i32.const 1
        i32.shl
        local.set 1
        i32.const 2
        call 2
        local.set 2
        local.get 2
        i32.const 1
        i32.const 1
        call 3
        i32.const 1
        local.set 3
        local.get 2
        local.get 3
        i32.store offset=1 align=2
        local.get 2
        local.get 1
        local.get 1
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store offset=5 align=2
        else
          local.get 1
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store offset=5 align=2
          else
            i32.load offset=1 align=2
            i32.store offset=5 align=2
            local.get 1
            call 6
          end
        end
        local.get 2
        call 5)
      (func (;8;) (type 4)
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
      (export "_start" (func 7))
      (start 8))

    -----------add-----------
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
      (func (;7;) (type 1) (param i32) (result i32)
        (local i32)
        i32.const 1
        i32.const 1
        i32.shl
        i32.const 1
        i32.shr_u
        i32.const 2
        i32.const 1
        i32.shl
        i32.const 1
        i32.shr_u
        i32.add
        i32.const 1
        i32.shl)
      (func (;8;) (type 4)
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
      (export "_start" (func 7))
      (start 8))

    -----------sub-----------
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
      (func (;7;) (type 1) (param i32) (result i32)
        (local i32)
        i32.const 1
        i32.const 1
        i32.shl
        i32.const 1
        i32.shr_u
        i32.const 2
        i32.const 1
        i32.shl
        i32.const 1
        i32.shr_u
        i32.sub
        i32.const 1
        i32.shl)
      (func (;8;) (type 4)
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
      (export "_start" (func 7))
      (start 8))

    -----------mul-----------
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
      (func (;7;) (type 1) (param i32) (result i32)
        (local i32)
        i32.const 1
        i32.const 1
        i32.shl
        i32.const 1
        i32.shr_u
        i32.const 2
        i32.const 1
        i32.shl
        i32.const 1
        i32.shr_u
        i32.mul
        i32.const 1
        i32.shl)
      (func (;8;) (type 4)
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
      (export "_start" (func 7))
      (start 8))

    -----------div-----------
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
      (func (;7;) (type 1) (param i32) (result i32)
        (local i32)
        i32.const 1
        i32.const 1
        i32.shl
        i32.const 1
        i32.shr_u
        i32.const 2
        i32.const 1
        i32.shl
        i32.const 1
        i32.shr_u
        i32.div_s
        i32.const 1
        i32.shl)
      (func (;8;) (type 4)
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
      (export "_start" (func 7))
      (start 8))

    -----------math-----------
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
      (func (;7;) (type 1) (param i32) (result i32)
        (local i32)
        i32.const 2
        i32.const 1
        i32.shl
        i32.const 1
        i32.shr_u
        i32.const 6
        i32.const 1
        i32.shl
        i32.const 1
        i32.shr_u
        i32.mul
        i32.const 1
        i32.shl
        i32.const 1
        i32.shr_u
        i32.const 3
        i32.const 1
        i32.shl
        i32.const 1
        i32.shr_u
        i32.div_s
        i32.const 1
        i32.shl)
      (func (;8;) (type 4)
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
      (export "_start" (func 7))
      (start 8))

    -----------basic_let-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func))
      (type (;5;) (func))
      (type (;6;) (func))
      (type (;7;) (func))
      (type (;8;) (func))
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
        (local i32 i32 i32 i32)
        i32.const 10
        i32.const 1
        i32.shl
        local.set 1
        local.get 1
        local.set 2
        local.get 2
        local.get 2
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 2
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 2
            i32.load offset=1 align=2
            call 5
            local.set 2
          end
        end
        local.get 2
        local.set 1
        local.get 1
        local.set 3
        local.get 3
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 3
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 3
            call 4
          else
            local.get 3
            call 6
          end
        end)
      (func (;8;) (type 4)
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
      (export "_start" (func 7))
      (start 8))

    -----------return_one-----------
    FAILURE (InstrErr
     (error
      (PackMismatch
       (Ref (Base GC)
        (Struct
         ((Ser (Ref (Base GC) (Struct ())))
          (Ser
           (CodeRef
            (FunctionType ()
             ((Ref (Base GC)
               (Struct
                ((Ser (Ref (Base GC) (Struct ())))
                 (Ser (Ref (Base GC) (Struct ())))))))
             (I31)))))))
       (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
        (Ref (Base GC)
         (Struct
          ((Ser (Var 0))
           (Ser
            (CodeRef
             (FunctionType ()
              ((Ref (Base GC)
                (Struct ((Ser (Var 0)) (Ser (Ref (Base GC) (Struct ())))))))
              (I31))))))))))
     (instr
      (Pack (Type (Ref (Base GC) (Struct ())))
       (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
        (Ref (Base GC)
         (Struct
          ((Ser (Var 0))
           (Ser
            (CodeRef
             (FunctionType ()
              ((Ref (Base GC)
                (Struct ((Ser (Var 0)) (Ser (Ref (Base GC) (Struct ())))))))
              (I31))))))))))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return
        ((Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
          (Ref (Base GC)
           (Struct
            ((Ser (Var 0))
             (Ser
              (CodeRef
               (FunctionType ()
                ((Ref (Base GC)
                  (Struct ((Ser (Var 0)) (Ser (Ref (Base GC) (Struct ())))))))
                (I31))))))))))
       (functions
        ((FunctionType ()
          ((Ref (Base GC)
            (Struct
             ((Ser (Ref (Base GC) (Struct ())))
              (Ser (Ref (Base GC) (Struct ())))))))
          (I31))
         (FunctionType () ((Ref (Base GC) (Struct ())))
          ((Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
            (Ref (Base GC)
             (Struct
              ((Ser (Var 0))
               (Ser
                (CodeRef
                 (FunctionType ()
                  ((Ref (Base GC)
                    (Struct ((Ser (Var 0)) (Ser (Ref (Base GC) (Struct ())))))))
                  (I31))))))))))))
       (table
        ((FunctionType ()
          ((Ref (Base GC)
            (Struct
             ((Ser (Ref (Base GC) (Struct ())))
              (Ser (Ref (Base GC) (Struct ())))))))
          (I31))
         (FunctionType () ((Ref (Base GC) (Struct ())))
          ((Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
            (Ref (Base GC)
             (Struct
              ((Ser (Var 0))
               (Ser
                (CodeRef
                 (FunctionType ()
                  ((Ref (Base GC)
                    (Struct ((Ser (Var 0)) (Ser (Ref (Base GC) (Struct ())))))))
                  (I31))))))))))))
       (lfx ())))
     (state
      ((locals ((Ref (Base GC) (Struct ())) (Plug (Atom Ptr))))
       (stack
        ((Ref (Base GC)
          (Struct
           ((Ser (Ref (Base GC) (Struct ())))
            (Ser
             (CodeRef
              (FunctionType ()
               ((Ref (Base GC)
                 (Struct
                  ((Ser (Ref (Base GC) (Struct ())))
                   (Ser (Ref (Base GC) (Struct ())))))))
               (I31))))))))))))
    -----------add_one-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func))
      (type (;5;) (func))
      (type (;6;) (func))
      (type (;7;) (func (param i32) (result i32)))
      (type (;8;) (func (param i32) (result i32)))
      (type (;9;) (func (param i32) (result i32)))
      (type (;10;) (func (param i32) (result i32)))
      (type (;11;) (func))
      (type (;12;) (func))
      (type (;13;) (func))
      (type (;14;) (func))
      (type (;15;) (func))
      (type (;16;) (func))
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
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        local.get 0
        local.set 3
        local.get 3
        local.get 3
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 3
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 3
            i32.load offset=1 align=2
            call 5
            local.set 3
          end
        end
        local.get 3
        local.set 0
        local.tee 4
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
            i32.load offset=7 align=2
            local.tee 5
            local.get 5
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 5
              i32.const 2
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                i32.load offset=1 align=2
                call 5
              end
            end
          else
            local.get 4
            i32.load offset=5 align=2
            local.tee 6
            local.get 6
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 6
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
        local.set 1
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
        local.get 1
        local.set 2
        local.get 2
        local.set 8
        local.get 8
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
          else
            local.get 8
            i32.load offset=1 align=2
            call 5
            local.set 8
          end
        end
        local.get 8
        local.set 2
        i32.const 1
        i32.shr_u
        i32.const 1
        i32.const 1
        i32.shl
        i32.const 1
        i32.shr_u
        i32.add
        i32.const 1
        i32.shl
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
        end)
      (func (;8;) (type 4)
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
      (export "add1" (func 7))
      (start 8))

    -----------id-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func))
      (type (;5;) (func))
      (type (;6;) (func))
      (type (;7;) (func (param i32) (result i32)))
      (type (;8;) (func (param i32) (result i32)))
      (type (;9;) (func (param i32) (result i32)))
      (type (;10;) (func (param i32) (result i32)))
      (type (;11;) (func))
      (type (;12;) (func))
      (type (;13;) (func))
      (type (;14;) (func))
      (type (;15;) (func))
      (type (;16;) (func))
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
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        local.get 0
        local.set 3
        local.get 3
        local.get 3
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 3
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 3
            i32.load offset=1 align=2
            call 5
            local.set 3
          end
        end
        local.get 3
        local.set 0
        local.tee 4
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
            i32.load offset=7 align=2
            local.tee 5
            local.get 5
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 5
              i32.const 2
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                i32.load offset=1 align=2
                call 5
              end
            end
          else
            local.get 4
            i32.load offset=5 align=2
            local.tee 6
            local.get 6
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 6
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
        local.set 1
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
        local.get 1
        local.set 2
        local.get 2
        local.set 8
        local.get 8
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
          else
            local.get 8
            i32.load offset=1 align=2
            call 5
            local.set 8
          end
        end
        local.get 8
        local.set 2
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
        end)
      (func (;8;) (type 4)
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
      (export "id" (func 7))
      (start 8))

    -----------apply_id-----------
    FAILURE (InstrErr
     (error
      (PackMismatch
       (Ref (Base GC)
        (Struct
         ((Ser (Ref (Base GC) (Struct ())))
          (Ser
           (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
            (Ref (Base GC)
             (Struct
              ((Ser (Var 0))
               (Ser
                (CodeRef
                 (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
                  ((Ref (Base GC) (Struct ((Ser (Var 1)) (Ser (Var 0))))))
                  ((Var 0)))))))))))))
       (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
        (Ref (Base GC)
         (Struct
          ((Ser (Var 0))
           (Ser
            (CodeRef
             (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
              ((Ref (Base GC) (Struct ((Ser (Var 1)) (Ser (Var 0)))))) ((Var 0)))))))))))
     (instr
      (Pack (Type (Ref (Base GC) (Struct ())))
       (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
        (Ref (Base GC)
         (Struct
          ((Ser (Var 0))
           (Ser
            (CodeRef
             (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
              ((Ref (Base GC) (Struct ((Ser (Var 1)) (Ser (Var 0)))))) ((Var 0)))))))))))
     (env
      ((local_offset 1) (kinds ()) (labels ()) (return (I31))
       (functions
        ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
          ((Ref (Base GC)
            (Struct ((Ser (Ref (Base GC) (Struct ()))) (Ser (Var 0))))))
          ((Var 0)))
         (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
       (table
        ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
          ((Ref (Base GC)
            (Struct ((Ser (Ref (Base GC) (Struct ()))) (Ser (Var 0))))))
          ((Var 0)))
         (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
       (lfx ())))
     (state
      ((locals
        ((Ref (Base GC) (Struct ())) (Plug (Atom Ptr)) (Plug (Atom Ptr))
         (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr))
         (Plug (Atom Ptr))))
       (stack
        ((Ref (Base GC)
          (Struct
           ((Ser (Ref (Base GC) (Struct ())))
            (Ser
             (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
              (Ref (Base GC)
               (Struct
                ((Ser (Var 0))
                 (Ser
                  (CodeRef
                   (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
                    ((Ref (Base GC) (Struct ((Ser (Var 1)) (Ser (Var 0))))))
                    ((Var 0))))))))))))))))))
    -----------opt_case-----------
    FAILURE EFail
    -----------poly_len-----------
    FAILURE (InstrErr
     (error
      (BlockErr
       (error
        (PackMismatch
         (Ref (Base GC)
          (Struct
           ((Ser (Ref (Base GC) (Struct ())))
            (Ser
             (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
              (Ref (Base GC)
               (Struct
                ((Ser (Var 0))
                 (Ser
                  (CodeRef
                   (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
                    ((Ref (Base GC)
                      (Struct
                       ((Ser (Var 1))
                        (Ser
                         (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                          (Ref (Base GC)
                           (Variant
                            ((Ser (Ref (Base GC) (Struct ())))
                             (Ser
                              (Ref (Base GC)
                               (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
                    (I31))))))))))))
         (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
          (Ref (Base GC)
           (Struct
            ((Ser (Var 0))
             (Ser
              (CodeRef
               (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
                ((Ref (Base GC)
                  (Struct
                   ((Ser (Var 1))
                    (Ser
                     (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                      (Ref (Base GC)
                       (Variant
                        ((Ser (Ref (Base GC) (Struct ())))
                         (Ser
                          (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
                (I31))))))))))
       (instr
        (Pack (Type (Ref (Base GC) (Struct ())))
         (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
          (Ref (Base GC)
           (Struct
            ((Ser (Var 0))
             (Ser
              (CodeRef
               (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
                ((Ref (Base GC)
                  (Struct
                   ((Ser (Var 1))
                    (Ser
                     (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                      (Ref (Base GC)
                       (Variant
                        ((Ser (Ref (Base GC) (Struct ())))
                         (Ser
                          (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
                (I31))))))))))
       (env
        ((local_offset 1) (kinds ((VALTYPE (Atom Ptr) ExCopy ExDrop)))
         (labels ((I31))) (return (I31))
         (functions
          ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
            ((Ref (Base GC)
              (Struct
               ((Ser (Ref (Base GC) (Struct ())))
                (Ser
                 (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                  (Ref (Base GC)
                   (Variant
                    ((Ser (Ref (Base GC) (Struct ())))
                     (Ser
                      (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
            (I31))
           (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
         (table
          ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
            ((Ref (Base GC)
              (Struct
               ((Ser (Ref (Base GC) (Struct ())))
                (Ser
                 (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                  (Ref (Base GC)
                   (Variant
                    ((Ser (Ref (Base GC) (Struct ())))
                     (Ser
                      (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
            (I31))
           (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
         (lfx (InferFx))))
       (state
        ((locals
          ((Ref (Base GC)
            (Struct
             ((Ser (Ref (Base GC) (Struct ())))
              (Ser
               (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                (Ref (Base GC)
                 (Variant
                  ((Ser (Ref (Base GC) (Struct ())))
                   (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))))))
           (Plug (Atom Ptr))
           (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
            (Ref (Base GC)
             (Variant
              ((Ser (Ref (Base GC) (Struct ())))
               (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))
           (Ref (Base GC)
            (Variant
             ((Ser (Ref (Base GC) (Struct ())))
              (Ser
               (Ref (Base GC)
                (Variant
                 ((Ser (Var 0))
                  (Ser
                   (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                    (Ref (Base GC)
                     (Variant
                      ((Ser (Ref (Base GC) (Struct ())))
                       (Ser
                        (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))))))))))
           (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr))
           (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr))
           (Plug (Atom Ptr)) (Plug (Atom Ptr))))
         (stack
          ((Ref (Base GC)
            (Struct
             ((Ser (Ref (Base GC) (Struct ())))
              (Ser
               (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
                (Ref (Base GC)
                 (Struct
                  ((Ser (Var 0))
                   (Ser
                    (CodeRef
                     (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
                      ((Ref (Base GC)
                        (Struct
                         ((Ser (Var 1))
                          (Ser
                           (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                            (Ref (Base GC)
                             (Variant
                              ((Ser (Ref (Base GC) (Struct ())))
                               (Ser
                                (Ref (Base GC)
                                 (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
                      (I31))))))))))))
           (Num (Int I32))))))))
     (instr
      (CaseLoad (ArrowType 1 (I31)) Copy InferFx
       (((LocalSet 10) (NumConst (Int I32) 0) Tag (LocalGet 10 Move) Drop)
        ((LocalSet 3) (NumConst (Int I32) 1) Tag Untag (Group 0) (New GC)
         (Cast (Ref (Base GC) (Struct ()))) (CodeRef 0) (Group 2) (New GC)
         (Cast
          (Ref (Base GC)
           (Struct
            ((Ser (Ref (Base GC) (Struct ())))
             (Ser
              (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
               (Ref (Base GC)
                (Struct
                 ((Ser (Var 0))
                  (Ser
                   (CodeRef
                    (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
                     ((Ref (Base GC)
                       (Struct
                        ((Ser (Var 1))
                         (Ser
                          (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                           (Ref (Base GC)
                            (Variant
                             ((Ser (Ref (Base GC) (Struct ())))
                              (Ser
                               (Ref (Base GC)
                                (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
                     (I31)))))))))))))
         (Pack (Type (Ref (Base GC) (Struct ())))
          (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
           (Ref (Base GC)
            (Struct
             ((Ser (Var 0))
              (Ser
               (CodeRef
                (FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
                 ((Ref (Base GC)
                   (Struct
                    ((Ser (Var 1))
                     (Ser
                      (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                       (Ref (Base GC)
                        (Variant
                         ((Ser (Ref (Base GC) (Struct ())))
                          (Ser
                           (Ref (Base GC)
                            (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
                 (I31)))))))))
         (New GC) (Load (Path ()) Follow) (LocalSet 4) Drop (LocalGet 4 Move)
         (Unpack (ArrowType 1 (I31)) InferFx
          ((LocalSet 4) (LocalGet 5 Move) Copy (LocalSet 5)
           (Load (Path (0)) Follow) (LocalSet 6) Drop (LocalGet 6 Move)
           (LocalSet 7) (LocalGet 5 Move) Copy (LocalSet 5)
           (Load (Path (1)) Follow) (LocalSet 8) Drop (LocalGet 8 Move)
           (LocalSet 9) (LocalGet 3 Move) Copy (LocalSet 3)
           (Fold
            (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
             (Ref (Base GC)
              (Variant
               ((Ser (Ref (Base GC) (Struct ())))
                (Ser (Ref (Base GC) (Variant ((Ser (Var 2)) (Ser (Var 0)))))))))))
           (LocalGet 9 Move) Copy (LocalSet 9) (Inst (Type (Var 1))) CallIndirect
           (LocalGet 9 Move) Drop (LocalGet 7 Move) Drop (LocalGet 4 Move) Drop))
         Untag (Num (Int2 I32 Add)) Tag (LocalGet 3 Move) Drop))))
     (env
      ((local_offset 1) (kinds ((VALTYPE (Atom Ptr) ExCopy ExDrop))) (labels ())
       (return (I31))
       (functions
        ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
          ((Ref (Base GC)
            (Struct
             ((Ser (Ref (Base GC) (Struct ())))
              (Ser
               (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                (Ref (Base GC)
                 (Variant
                  ((Ser (Ref (Base GC) (Struct ())))
                   (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
          (I31))
         (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
       (table
        ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
          ((Ref (Base GC)
            (Struct
             ((Ser (Ref (Base GC) (Struct ())))
              (Ser
               (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                (Ref (Base GC)
                 (Variant
                  ((Ser (Ref (Base GC) (Struct ())))
                   (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
          (I31))
         (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
       (lfx ())))
     (state
      ((locals
        ((Ref (Base GC)
          (Struct
           ((Ser (Ref (Base GC) (Struct ())))
            (Ser
             (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
              (Ref (Base GC)
               (Variant
                ((Ser (Ref (Base GC) (Struct ())))
                 (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))))))
         (Plug (Atom Ptr))
         (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
          (Ref (Base GC)
           (Variant
            ((Ser (Ref (Base GC) (Struct ())))
             (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))
         (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr))
         (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr))
         (Plug (Atom Ptr))))
       (stack
        ((Ref (Base GC)
          (Variant
           ((Ser (Ref (Base GC) (Struct ())))
            (Ser
             (Ref (Base GC)
              (Variant
               ((Ser (Var 0))
                (Ser
                 (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
                  (Ref (Base GC)
                   (Variant
                    ((Ser (Ref (Base GC) (Struct ())))
                     (Ser
                      (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))))))))))
    -----------mini_zip-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func))
      (type (;5;) (func))
      (type (;6;) (func))
      (type (;7;) (func (param i32) (result i32)))
      (type (;8;) (func (param i32) (result i32)))
      (type (;9;) (func (param i32) (result i32)))
      (type (;10;) (func (param i32) (result i32)))
      (type (;11;) (func))
      (type (;12;) (func))
      (type (;13;) (func))
      (type (;14;) (func))
      (type (;15;) (func (param i32) (result i32)))
      (type (;16;) (func (param i32) (result i32)))
      (type (;17;) (func (param i32) (result i32)))
      (type (;18;) (func (param i32) (result i32)))
      (type (;19;) (func))
      (type (;20;) (func))
      (type (;21;) (func (param i32) (result i32)))
      (type (;22;) (func (param i32) (result i32)))
      (type (;23;) (func (param i32) (result i32)))
      (type (;24;) (func (param i32) (result i32)))
      (type (;25;) (func))
      (type (;26;) (func))
      (type (;27;) (func))
      (type (;28;) (func))
      (type (;29;) (func (param i32) (result i32)))
      (type (;30;) (func (param i32) (result i32)))
      (type (;31;) (func (param i32) (result i32)))
      (type (;32;) (func (param i32) (result i32)))
      (type (;33;) (func))
      (type (;34;) (func))
      (type (;35;) (func (param i32) (result i32)))
      (type (;36;) (func (param i32) (result i32)))
      (type (;37;) (func (param i32) (result i32)))
      (type (;38;) (func (param i32) (result i32)))
      (type (;39;) (func))
      (type (;40;) (func))
      (type (;41;) (func (param i32 i32)))
      (type (;42;) (func (param i32 i32)))
      (type (;43;) (func (param i32 i32)))
      (type (;44;) (func (param i32 i32)))
      (type (;45;) (func (param i32 i32)))
      (type (;46;) (func (param i32 i32)))
      (type (;47;) (func))
      (type (;48;) (func))
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
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        local.get 0
        local.set 7
        local.get 7
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
          else
            local.get 7
            i32.load offset=1 align=2
            call 5
            local.set 7
          end
        end
        local.get 7
        local.set 0
        local.tee 8
        local.get 8
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 8
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 8
            i32.load offset=7 align=2
            local.tee 9
            local.get 9
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 9
              i32.const 2
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                i32.load offset=1 align=2
                call 5
              end
            end
          else
            local.get 8
            i32.load offset=5 align=2
            local.tee 10
            local.get 10
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 10
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
        local.set 1
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
        local.get 1
        local.set 2
        local.get 2
        local.set 12
        local.get 12
        local.get 12
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 12
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 12
            i32.load offset=1 align=2
            call 5
            local.set 12
          end
        end
        local.get 12
        local.set 2
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
            i32.load offset=7 align=2
            local.tee 14
            local.get 14
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 14
              i32.const 2
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                i32.load offset=1 align=2
                call 5
              end
            end
          else
            local.get 13
            i32.load offset=5 align=2
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
              else
                call 5
              end
            end
          end
        end
        local.set 3
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
        local.tee 17
        local.get 17
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 17
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 17
            i32.load offset=3 align=2
            local.tee 18
            local.get 18
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 18
              i32.const 2
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                i32.load offset=1 align=2
                call 5
              end
            end
          else
            local.get 17
            i32.load offset=1 align=2
            local.tee 19
            local.get 19
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 19
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
        local.set 4
        local.set 20
        local.get 20
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 20
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 20
            call 4
          else
            local.get 20
            call 6
          end
        end
        local.get 4
        local.get 2
        local.set 21
        local.get 21
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
          else
            local.get 21
            i32.load offset=1 align=2
            call 5
            local.set 21
          end
        end
        local.get 21
        local.set 2
        local.tee 22
        local.get 22
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 22
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 22
            i32.load offset=3 align=2
            local.tee 23
            local.get 23
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 23
              i32.const 2
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                i32.load offset=1 align=2
                call 5
              end
            end
          else
            local.get 22
            i32.load offset=1 align=2
            local.tee 24
            local.get 24
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 24
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
        local.set 5
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
        local.get 5
        local.tee 26
        local.get 26
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 26
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 26
            i32.load offset=3 align=2
            local.tee 27
            local.get 27
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 27
              i32.const 2
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                i32.load offset=1 align=2
                call 5
              end
            end
          else
            local.get 26
            i32.load offset=1 align=2
            local.tee 28
            local.get 28
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 28
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
        local.set 6
        local.set 29
        local.get 29
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 29
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 29
            call 4
          else
            local.get 29
            call 6
          end
        end
        local.get 6
        nop
        local.set 31
        local.set 30
        i32.const 2
        call 2
        local.set 32
        local.get 32
        i32.const 0
        i32.const 1
        call 3
        local.get 32
        i32.const 1
        i32.const 1
        call 3
        local.get 32
        local.get 31
        local.get 31
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store offset=1 align=2
        else
          local.get 31
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store offset=1 align=2
          else
            i32.load offset=1 align=2
            i32.store offset=1 align=2
            local.get 31
            call 6
          end
        end
        local.get 32
        local.get 30
        local.get 30
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store offset=5 align=2
        else
          local.get 30
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store offset=5 align=2
          else
            i32.load offset=1 align=2
            i32.store offset=5 align=2
            local.get 30
            call 6
          end
        end
        local.get 32
        call 5
        local.set 33
        i32.const 1
        call 2
        local.set 34
        local.get 34
        i32.const 0
        i32.const 1
        call 3
        local.get 34
        local.get 33
        local.get 33
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store offset=1 align=2
        else
          local.get 33
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store offset=1 align=2
          else
            i32.load offset=1 align=2
            i32.store offset=1 align=2
            local.get 33
            call 6
          end
        end
        local.get 34
        call 5
        local.get 2
        local.set 35
        local.get 35
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 35
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 35
            call 4
          else
            local.get 35
            call 6
          end
        end)
      (func (;8;) (type 4)
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
      (export "mini_zip" (func 7))
      (start 8))

    -----------closure_simpl-----------
    FAILURE (InstrErr
     (error
      (PackMismatch
       (Ref (Base GC)
        (Struct
         ((Ser (Ref (Base GC) (Struct ((Ser I31)))))
          (Ser
           (CodeRef
            (FunctionType ()
             ((Ref (Base GC)
               (Struct
                ((Ser (Ref (Base GC) (Struct ((Ser I31)))))
                 (Ser (Ref (Base GC) (Struct ())))))))
             (I31)))))))
       (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
        (Ref (Base GC)
         (Struct
          ((Ser (Var 0))
           (Ser
            (CodeRef
             (FunctionType ()
              ((Ref (Base GC)
                (Struct ((Ser (Var 0)) (Ser (Ref (Base GC) (Struct ())))))))
              (I31))))))))))
     (instr
      (Pack (Type (Ref (Base GC) (Struct ((Ser I31)))))
       (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
        (Ref (Base GC)
         (Struct
          ((Ser (Var 0))
           (Ser
            (CodeRef
             (FunctionType ()
              ((Ref (Base GC)
                (Struct ((Ser (Var 0)) (Ser (Ref (Base GC) (Struct ())))))))
              (I31))))))))))
     (env
      ((local_offset 1) (kinds ()) (labels ()) (return (I31))
       (functions
        ((FunctionType ()
          ((Ref (Base GC)
            (Struct
             ((Ser (Ref (Base GC) (Struct ((Ser I31)))))
              (Ser (Ref (Base GC) (Struct ())))))))
          (I31))
         (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
       (table
        ((FunctionType ()
          ((Ref (Base GC)
            (Struct
             ((Ser (Ref (Base GC) (Struct ((Ser I31)))))
              (Ser (Ref (Base GC) (Struct ())))))))
          (I31))
         (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
       (lfx ())))
     (state
      ((locals
        ((Ref (Base GC) (Struct ())) I31 (Plug (Atom Ptr)) (Plug (Atom Ptr))
         (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr))
         (Plug (Atom Ptr)) (Plug (Atom Ptr))))
       (stack
        ((Ref (Base GC)
          (Struct
           ((Ser (Ref (Base GC) (Struct ((Ser I31)))))
            (Ser
             (CodeRef
              (FunctionType ()
               ((Ref (Base GC)
                 (Struct
                  ((Ser (Ref (Base GC) (Struct ((Ser I31)))))
                   (Ser (Ref (Base GC) (Struct ())))))))
               (I31))))))))))))
    -----------closure_complex-----------
    FAILURE (InstrErr
     (error
      (NonRef Load
       (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
        (Ref (Base GC)
         (Struct
          ((Ser (Var 0))
           (Ser
            (CodeRef
             (FunctionType ()
              ((Ref (Base GC) (Struct ((Ser (Var 0)) (Ser I31))))) (I31))))))))))
     (instr (Load (Path ()) Follow))
     (env
      ((local_offset 1) (kinds ()) (labels ()) (return (I31))
       (functions
        ((FunctionType ()
          ((Ref (Base GC)
            (Struct
             ((Ser
               (Ref (Base GC)
                (Struct
                 ((Ser
                   (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
                    (Ref (Base GC)
                     (Struct
                      ((Ser (Var 0))
                       (Ser
                        (CodeRef
                         (FunctionType ()
                          ((Ref (Base GC) (Struct ((Ser (Var 0)) (Ser I31)))))
                          (I31)))))))))
                  (Ser I31)))))
              (Ser I31)))))
          (I31))
         (FunctionType ()
          ((Ref (Base GC)
            (Struct ((Ser (Ref (Base GC) (Struct ((Ser I31))))) (Ser I31)))))
          (I31))
         (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
       (table
        ((FunctionType ()
          ((Ref (Base GC)
            (Struct
             ((Ser
               (Ref (Base GC)
                (Struct
                 ((Ser
                   (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
                    (Ref (Base GC)
                     (Struct
                      ((Ser (Var 0))
                       (Ser
                        (CodeRef
                         (FunctionType ()
                          ((Ref (Base GC) (Struct ((Ser (Var 0)) (Ser I31)))))
                          (I31)))))))))
                  (Ser I31)))))
              (Ser I31)))))
          (I31))
         (FunctionType ()
          ((Ref (Base GC)
            (Struct ((Ser (Ref (Base GC) (Struct ((Ser I31))))) (Ser I31)))))
          (I31))
         (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
       (lfx ())))
     (state
      ((locals
        ((Ref (Base GC)
          (Struct
           ((Ser
             (Ref (Base GC)
              (Struct
               ((Ser
                 (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
                  (Ref (Base GC)
                   (Struct
                    ((Ser (Var 0))
                     (Ser
                      (CodeRef
                       (FunctionType ()
                        ((Ref (Base GC) (Struct ((Ser (Var 0)) (Ser I31)))))
                        (I31)))))))))
                (Ser I31)))))
            (Ser I31))))
         (Plug (Atom Ptr))
         (Ref (Base GC)
          (Struct
           ((Ser
             (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
              (Ref (Base GC)
               (Struct
                ((Ser (Var 0))
                 (Ser
                  (CodeRef
                   (FunctionType ()
                    ((Ref (Base GC) (Struct ((Ser (Var 0)) (Ser I31)))))
                    (I31)))))))))
            (Ser I31))))
         (Plug (Atom Ptr)) I31 (Plug (Atom Ptr))
         (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
          (Ref (Base GC)
           (Struct
            ((Ser (Var 0))
             (Ser
              (CodeRef
               (FunctionType ()
                ((Ref (Base GC) (Struct ((Ser (Var 0)) (Ser I31))))) (I31))))))))
         (Plug (Atom Ptr)) I31 (Plug (Atom Ptr)) (Plug (Atom Ptr))
         (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr))
         (Plug (Atom Ptr))))
       (stack
        ((Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
          (Ref (Base GC)
           (Struct
            ((Ser (Var 0))
             (Ser
              (CodeRef
               (FunctionType ()
                ((Ref (Base GC) (Struct ((Ser (Var 0)) (Ser I31))))) (I31))))))))))))) |}]
