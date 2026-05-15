open! Base
open! Stdlib.Format
open! Richwasm_support
open! Test_support
open Richwasm_support.Pipeline
module AnnRichWasm = Richwasm_common.Annotated_syntax

include Test_runner.MultiOutputter.Make (struct
  include Test_runner.MultiOutputter.DefaultConfig
  open Richwasm_mini_ml

  type syntax = Syntax.Source.Module.t
  type text = string
  type res = string

  let syntax_pipeline x = ml_pipeline x |> wasm_pipeline
  let string_pipeline s = ml_str_pipeline s |> wasm_pipeline
  let examples = Test_examples.Mini_ml.all
  let pp ff x = pp_wasm ff x
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
        (local i32 i32)
        i32.const 1
        i32.const 1
        i32.shl
        local.get 0
        local.set 2
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
            local.get 2
            call 4
          else
            local.get 2
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
      (export "__rw_table_func_7" (func 7))
      (start 8))

    -----------tuple-----------
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
        (local i32 i32 i32 i32 i32 i32 i32)
        i32.const 1
        i32.const 1
        i32.shl
        i32.const 2
        i32.const 1
        i32.shl
        i32.const 3
        i32.const 1
        i32.shl
        i32.const 4
        i32.const 1
        i32.shl
        local.set 5
        local.set 4
        local.set 3
        local.set 2
        i32.const 4
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
        i32.const 2
        i32.const 1
        call 3
        local.get 6
        i32.const 3
        i32.const 1
        call 3
        local.get 6
        local.get 2
        local.get 2
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 2
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 2
            call 6
          end
        end
        local.get 6
        local.get 3
        local.get 3
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=5 align=2
        else
          local.get 3
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=5 align=2
            local.get 3
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
          i32.store 1 offset=9 align=2
        else
          local.get 4
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=9 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=9 align=2
            local.get 4
            call 6
          end
        end
        local.get 6
        local.get 5
        local.get 5
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=13 align=2
        else
          local.get 5
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=13 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=13 align=2
            local.get 5
            call 6
          end
        end
        local.get 6
        call 5
        local.get 0
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
      (export "__rw_table_func_7" (func 7))
      (start 8))

    -----------tuple_nested-----------
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
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 1
        i32.const 1
        i32.shl
        i32.const 2
        i32.const 1
        i32.shl
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
        local.get 2
        local.get 2
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 2
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 2
            call 6
          end
        end
        local.get 4
        local.get 3
        local.get 3
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=5 align=2
        else
          local.get 3
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=5 align=2
            local.get 3
            call 6
          end
        end
        local.get 4
        call 5
        i32.const 3
        i32.const 1
        i32.shl
        i32.const 4
        i32.const 1
        i32.shl
        local.set 6
        local.set 5
        i32.const 2
        call 2
        local.set 7
        local.get 7
        i32.const 0
        i32.const 1
        call 3
        local.get 7
        i32.const 1
        i32.const 1
        call 3
        local.get 7
        local.get 5
        local.get 5
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 5
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 5
            call 6
          end
        end
        local.get 7
        local.get 6
        local.get 6
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=5 align=2
        else
          local.get 6
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=5 align=2
            local.get 6
            call 6
          end
        end
        local.get 7
        call 5
        local.set 9
        local.set 8
        i32.const 2
        call 2
        local.set 10
        local.get 10
        i32.const 0
        i32.const 1
        call 3
        local.get 10
        i32.const 1
        i32.const 1
        call 3
        local.get 10
        local.get 8
        local.get 8
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 8
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 8
            call 6
          end
        end
        local.get 10
        local.get 9
        local.get 9
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=5 align=2
        else
          local.get 9
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=5 align=2
            local.get 9
            call 6
          end
        end
        local.get 10
        call 5
        local.get 0
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
      (export "__rw_table_func_7" (func 7))
      (start 8))

    -----------tuple_project-----------
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
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 42
        i32.const 1
        i32.shl
        i32.const 7
        i32.const 1
        i32.shl
        local.set 4
        local.set 3
        i32.const 2
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
        local.get 3
        local.get 3
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 3
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 3
            call 6
          end
        end
        local.get 5
        local.get 4
        local.get 4
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=5 align=2
        else
          local.get 4
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=5 align=2
            local.get 4
            call 6
          end
        end
        local.get 5
        call 5
        local.tee 6
        local.get 6
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 6
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 6
            i32.load offset=7 align=2
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 6
            i32.load 1 offset=1 align=2
            i32.load 1 offset=5 align=2
            local.tee 8
            local.get 8
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 8
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
        local.get 1
        local.get 0
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
      (export "__rw_table_func_7" (func 7))
      (start 8))

    -----------sum_unit-----------
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
        (local i32 i32 i32 i32 i32 i32)
        i32.const 0
        call 2
        local.set 2
        local.get 2
        call 5
        local.set 3
        i32.const 2
        call 2
        local.set 4
        local.get 4
        i32.const 1
        i32.const 1
        call 3
        i32.const 0
        local.set 5
        local.get 4
        local.get 5
        i32.store 1 offset=1 align=2
        local.get 4
        local.get 3
        local.get 3
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=5 align=2
        else
          local.get 3
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=5 align=2
            local.get 3
            call 6
          end
        end
        local.get 4
        call 5
        local.get 0
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
      (export "__rw_table_func_7" (func 7))
      (start 8))

    -----------sum_option-----------
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
        (local i32 i32 i32 i32 i32)
        i32.const 15
        i32.const 1
        i32.shl
        local.set 2
        i32.const 2
        call 2
        local.set 3
        local.get 3
        i32.const 1
        i32.const 1
        call 3
        i32.const 1
        local.set 4
        local.get 3
        local.get 4
        i32.store 1 offset=1 align=2
        local.get 3
        local.get 2
        local.get 2
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=5 align=2
        else
          local.get 2
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=5 align=2
            local.get 2
            call 6
          end
        end
        local.get 3
        call 5
        local.get 0
        local.set 5
        local.get 5
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 5
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 5
            call 4
          else
            local.get 5
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
      (export "__rw_table_func_7" (func 7))
      (start 8))

    -----------basic_if-----------
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
        (local i32 i32)
        i32.const 0
        i32.const 1
        i32.shl
        i32.const 1
        i32.shr_u
        i32.const 0
        i32.eq
        if (result i32)  ;; label = @1
          i32.const 1
          i32.const 1
          i32.shl
        else
          i32.const 2
          i32.const 1
          i32.shl
        end
        local.get 0
        local.set 2
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
            local.get 2
            call 4
          else
            local.get 2
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
      (export "__rw_table_func_7" (func 7))
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
        (local i32 i32)
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
        i32.shl
        local.get 0
        local.set 2
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
            local.get 2
            call 4
          else
            local.get 2
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
      (export "__rw_table_func_7" (func 7))
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
        (local i32 i32)
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
        i32.shl
        local.get 0
        local.set 2
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
            local.get 2
            call 4
          else
            local.get 2
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
      (export "__rw_table_func_7" (func 7))
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
        (local i32 i32)
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
        i32.shl
        local.get 0
        local.set 2
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
            local.get 2
            call 4
          else
            local.get 2
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
      (export "__rw_table_func_7" (func 7))
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
        (local i32 i32)
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
        i32.shl
        local.get 0
        local.set 2
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
            local.get 2
            call 4
          else
            local.get 2
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
      (export "__rw_table_func_7" (func 7))
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
        (local i32 i32)
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
        i32.shl
        local.get 0
        local.set 2
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
            local.get 2
            call 4
          else
            local.get 2
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
      (export "__rw_table_func_7" (func 7))
      (start 8))

    -----------basic_let-----------
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
        (local i32 i32 i32 i32 i32)
        i32.const 10
        i32.const 1
        i32.shl
        local.set 1
        local.get 1
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
            i32.load 1 offset=1 align=2
            call 5
            local.set 3
          end
        end
        local.get 3
        local.set 1
        local.get 1
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
        local.get 0
        local.set 5
        local.get 5
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 5
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 5
            call 4
          else
            local.get 5
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
      (export "__rw_table_func_7" (func 7))
      (start 8))

    -----------return_one-----------
    FAILURE Typechecker failed with error(s):
    can't module check types not equal
    -----------iife-----------
    FAILURE Typechecker failed with error(s):
    can't module check types not equal
    -----------add_one-----------
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
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        local.get 0
        local.set 4
        local.get 4
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
          else
            local.get 4
            i32.load 1 offset=1 align=2
            call 5
            local.set 4
          end
        end
        local.get 4
        local.set 0
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 5
            i32.load 1 offset=1 align=2
            i32.load 1 offset=5 align=2
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
        local.get 1
        local.set 2
        local.get 2
        local.set 9
        local.get 9
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
          else
            local.get 9
            i32.load 1 offset=1 align=2
            call 5
            local.set 9
          end
        end
        local.get 9
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
        local.get 0
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
      (export "__rw_table_func_7" (func 7))
      (start 8))

    -----------id-----------
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
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        local.get 0
        local.set 4
        local.get 4
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
          else
            local.get 4
            i32.load 1 offset=1 align=2
            call 5
            local.set 4
          end
        end
        local.get 4
        local.set 0
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 5
            i32.load 1 offset=1 align=2
            i32.load 1 offset=5 align=2
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
        local.get 1
        local.set 2
        local.get 2
        local.set 9
        local.get 9
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
          else
            local.get 9
            i32.load 1 offset=1 align=2
            call 5
            local.set 9
          end
        end
        local.get 9
        local.set 2
        local.get 2
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
        local.get 0
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
      (export "__rw_table_func_7" (func 7))
      (start 8))

    -----------assign-----------
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
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 0
        i32.const 1
        i32.shl
        local.set 5
        i32.const 1
        call 2
        local.set 6
        local.get 6
        i32.const 0
        i32.const 1
        call 3
        local.get 6
        local.get 5
        local.get 5
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 5
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 5
            call 6
          end
        end
        local.get 6
        call 5
        local.set 1
        local.get 1
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
            i32.load 1 offset=1 align=2
            call 5
            local.set 7
          end
        end
        local.get 7
        local.set 1
        i32.const 1
        i32.const 1
        i32.shl
        local.set 8
        local.tee 9
        local.get 9
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
          unreachable
        else
          local.get 9
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 9
            local.get 8
            i32.store offset=3 align=2
          else
            local.get 9
            local.get 8
            local.get 8
            i32.const 1
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=1 align=2
            else
              local.get 8
              i32.const 2
              i32.and
              i32.eqz
              if (param i32 i32)  ;; label = @4
                i32.store 1 offset=1 align=2
              else
                i32.load 1 offset=1 align=2
                i32.store 1 offset=1 align=2
                local.get 8
                call 6
              end
            end
          end
        end
        local.get 9
        i32.const 0
        i32.const 1
        call 3
        local.set 2
        local.get 1
        local.set 10
        local.get 10
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
          else
            local.get 10
            i32.load 1 offset=1 align=2
            call 5
            local.set 10
          end
        end
        local.get 10
        local.set 1
        local.tee 11
        local.get 11
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 11
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 11
            i32.load offset=3 align=2
            local.tee 12
            local.get 12
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 12
              i32.const 2
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 11
            i32.load 1 offset=1 align=2
            i32.load 1 offset=1 align=2
            local.tee 13
            local.get 13
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 13
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
        local.get 2
        local.set 15
        local.get 15
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 15
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 15
            call 4
          else
            local.get 15
            call 6
          end
        end
        local.get 1
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
        local.get 0
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
      (export "__rw_table_func_7" (func 7))
      (start 8))

    -----------apply_id-----------
    FAILURE (InstrErr
     (error
      (BlockErr
       (error
        (ExpectedUnqualidfiedCoderef
         (CodeRef
          (FunctionType ((Type (VALTYPE (Atom Ptr) GCRefs)))
           ((Ref (Base GC) (Struct ((Ser I31) (Ser (Var 0)))))) ((Var 0))))))
       (instr CallIndirect)
       (env
        ((local_offset 1) (kinds ((VALTYPE (Atom Ptr) GCRefs))) (labels ((I31)))
         (return (I31))
         (functions
          ((FunctionType ((Type (VALTYPE (Atom Ptr) GCRefs)))
            ((Ref (Base GC)
              (Struct ((Ser (Ref (Base GC) (Struct ()))) (Ser (Var 0))))))
            ((Var 0)))
           (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
         (table
          ((FunctionType ((Type (VALTYPE (Atom Ptr) GCRefs)))
            ((Ref (Base GC)
              (Struct ((Ser (Ref (Base GC) (Struct ()))) (Ser (Var 0))))))
            ((Var 0)))
           (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
         (lfx (InferFx))))
       (state
        ((locals
          ((Ref (Base GC) (Struct ()))
           (Ref (Base GC)
            (Struct
             ((Ser (Var 0))
              (Ser
               (CodeRef
                (FunctionType ((Type (VALTYPE (Atom Ptr) GCRefs)))
                 ((Ref (Base GC) (Struct ((Ser (Var 1)) (Ser (Var 0))))))
                 ((Var 0))))))))
           (Plug (Prod ((Atom I32)))) (Var 0) (Plug (Prod ((Atom I32))))
           (CodeRef
            (FunctionType ((Type (VALTYPE (Atom Ptr) GCRefs)))
             ((Ref (Base GC) (Struct ((Ser (Var 1)) (Ser (Var 0)))))) ((Var 0))))
           (Plug (Prod ((Atom I32))))))
         (stack
          ((CodeRef
            (FunctionType ((Type (VALTYPE (Atom Ptr) GCRefs)))
             ((Ref (Base GC) (Struct ((Ser I31) (Ser (Var 0)))))) ((Var 0))))
           I31))))))
     (instr
      (Unpack (ValType (I31)) InferFx
       ((LocalSet 1) (LocalGet 1 Move) Copy (LocalSet 1) (Load (Path (0)) Follow)
        (LocalSet 2) Drop (LocalGet 2 Move) (LocalSet 3) (LocalGet 1 Move) Copy
        (LocalSet 1) (Load (Path (1)) Follow) (LocalSet 4) Drop (LocalGet 4 Move)
        (LocalSet 5) (NumConst (Int I32) 42) Tag (LocalGet 5 Move) Copy
        (LocalSet 5) (Inst (Type I31)) CallIndirect (LocalGet 5 Move) Drop
        (LocalGet 3 Move) Drop (LocalGet 1 Move) Drop)))
     (env
      ((local_offset 1) (kinds ()) (labels ()) (return (I31))
       (functions
        ((FunctionType ((Type (VALTYPE (Atom Ptr) GCRefs)))
          ((Ref (Base GC)
            (Struct ((Ser (Ref (Base GC) (Struct ()))) (Ser (Var 0))))))
          ((Var 0)))
         (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
       (table
        ((FunctionType ((Type (VALTYPE (Atom Ptr) GCRefs)))
          ((Ref (Base GC)
            (Struct ((Ser (Ref (Base GC) (Struct ()))) (Ser (Var 0))))))
          ((Var 0)))
         (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
       (lfx ())))
     (state
      ((locals
        ((Ref (Base GC) (Struct ())) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32))))))
       (stack
        ((Exists (Type (VALTYPE (Atom Ptr) GCRefs))
          (Ref (Base GC)
           (Struct
            ((Ser (Var 0))
             (Ser
              (CodeRef
               (FunctionType ((Type (VALTYPE (Atom Ptr) GCRefs)))
                ((Ref (Base GC) (Struct ((Ser (Var 1)) (Ser (Var 0))))))
                ((Var 0))))))))))))))
    -----------opt_case-----------
    FAILURE (InstrErr (error (PopEmptyStack Drop)) (instr Drop)
     (env
      ((local_offset 1) (kinds ()) (labels ()) (return (I31))
       (functions ((FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
       (table ((FunctionType () ((Ref (Base GC) (Struct ()))) (I31)))) (lfx ())))
     (state
      ((locals
        ((Ref (Base GC) (Struct ()))
         (Ref (Base GC) (Variant ((Ser (Ref (Base GC) (Struct ()))) (Ser I31))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32)))) I31
         (Plug (Prod ((Atom I32))))))
       (stack ()))))
    -----------poly_len-----------
    FAILURE (InstrErr
     (error
      (BlockErr
       (error
        (BlockErr
         (error
          (LoadRefNonSer
           (Variant
            ((Ser (Var 0))
             (Ser
              (Rec (VALTYPE (Atom Ptr) GCRefs)
               (Ref (Base GC)
                (Variant
                 ((Ser (Ref (Base GC) (Struct ())))
                  (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
         (instr (Load (Path ()) Follow))
         (env
          ((local_offset 1)
           (kinds ((VALTYPE (Atom Ptr) GCRefs) (VALTYPE (Atom Ptr) GCRefs)))
           (labels ((I31) (I31))) (return (I31))
           (functions
            ((FunctionType ((Type (VALTYPE (Atom Ptr) GCRefs)))
              ((Ref (Base GC)
                (Struct
                 ((Ser (Ref (Base GC) (Struct ())))
                  (Ser
                   (Rec (VALTYPE (Atom Ptr) GCRefs)
                    (Ref (Base GC)
                     (Variant
                      ((Ser (Ref (Base GC) (Struct ())))
                       (Ser
                        (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
              (I31))
             (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
           (table
            ((FunctionType ((Type (VALTYPE (Atom Ptr) GCRefs)))
              ((Ref (Base GC)
                (Struct
                 ((Ser (Ref (Base GC) (Struct ())))
                  (Ser
                   (Rec (VALTYPE (Atom Ptr) GCRefs)
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
                 (Rec (VALTYPE (Atom Ptr) GCRefs)
                  (Ref (Base GC)
                   (Variant
                    ((Ser (Ref (Base GC) (Struct ())))
                     (Ser
                      (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))))))
             (Plug (Prod ((Atom I32))))
             (Rec (VALTYPE (Atom Ptr) GCRefs)
              (Ref (Base GC)
               (Variant
                ((Ser (Ref (Base GC) (Struct ())))
                 (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))
             (Ref (Base GC)
              (Variant
               ((Ser (Var 0))
                (Ser
                 (Rec (VALTYPE (Atom Ptr) GCRefs)
                  (Ref (Base GC)
                   (Variant
                    ((Ser (Ref (Base GC) (Struct ())))
                     (Ser
                      (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))))))
             (Ref (Base GC)
              (Struct
               ((Ser (Var 0))
                (Ser
                 (CodeRef
                  (FunctionType ((Type (VALTYPE (Atom Ptr) GCRefs)))
                   ((Ref (Base GC)
                     (Struct
                      ((Ser (Var 1))
                       (Ser
                        (Rec (VALTYPE (Atom Ptr) GCRefs)
                         (Ref (Base GC)
                          (Variant
                           ((Ser (Ref (Base GC) (Struct ())))
                            (Ser
                             (Ref (Base GC)
                              (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
                   (I31)))))))
             (Plug (Prod ((Atom I32)))) (Var 0) (Plug (Prod ((Atom I32))))
             (CodeRef
              (FunctionType ((Type (VALTYPE (Atom Ptr) GCRefs)))
               ((Ref (Base GC)
                 (Struct
                  ((Ser (Var 1))
                   (Ser
                    (Rec (VALTYPE (Atom Ptr) GCRefs)
                     (Ref (Base GC)
                      (Variant
                       ((Ser (Ref (Base GC) (Struct ())))
                        (Ser
                         (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
               (I31)))
             (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
             (Plug (Prod ((Atom I32))))))
           (stack
            ((Ref (Base GC)
              (Variant
               ((Ser (Var 0))
                (Ser
                 (Rec (VALTYPE (Atom Ptr) GCRefs)
                  (Ref (Base GC)
                   (Variant
                    ((Ser (Ref (Base GC) (Struct ())))
                     (Ser
                      (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))))))))))))
       (instr
        (Unpack (ValType (I31)) InferFx
         ((LocalSet 4) (LocalGet 4 Move) Copy (LocalSet 4)
          (Load (Path (0)) Follow) (LocalSet 5) Drop (LocalGet 5 Move)
          (LocalSet 6) (LocalGet 4 Move) Copy (LocalSet 4)
          (Load (Path (1)) Follow) (LocalSet 7) Drop (LocalGet 7 Move)
          (LocalSet 8) (LocalGet 3 Move) Copy (LocalSet 3)
          (Load (Path ()) Follow)
          (Fold
           (Ref (Base GC)
            (Variant
             ((Ser (Ref (Base GC) (Struct ())))
              (Ser (Ref (Base GC) (Variant ((Ser (Var 2)) (Ser (Var 0))))))))))
          (New GC) (LocalGet 8 Move) Copy (LocalSet 8) (Inst (Type (Var 1)))
          CallIndirect (LocalGet 8 Move) Drop (LocalGet 6 Move) Drop
          (LocalGet 4 Move) Drop)))
       (env
        ((local_offset 1) (kinds ((VALTYPE (Atom Ptr) GCRefs))) (labels ((I31)))
         (return (I31))
         (functions
          ((FunctionType ((Type (VALTYPE (Atom Ptr) GCRefs)))
            ((Ref (Base GC)
              (Struct
               ((Ser (Ref (Base GC) (Struct ())))
                (Ser
                 (Rec (VALTYPE (Atom Ptr) GCRefs)
                  (Ref (Base GC)
                   (Variant
                    ((Ser (Ref (Base GC) (Struct ())))
                     (Ser
                      (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
            (I31))
           (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
         (table
          ((FunctionType ((Type (VALTYPE (Atom Ptr) GCRefs)))
            ((Ref (Base GC)
              (Struct
               ((Ser (Ref (Base GC) (Struct ())))
                (Ser
                 (Rec (VALTYPE (Atom Ptr) GCRefs)
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
               (Rec (VALTYPE (Atom Ptr) GCRefs)
                (Ref (Base GC)
                 (Variant
                  ((Ser (Ref (Base GC) (Struct ())))
                   (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))))))
           (Plug (Prod ((Atom I32))))
           (Rec (VALTYPE (Atom Ptr) GCRefs)
            (Ref (Base GC)
             (Variant
              ((Ser (Ref (Base GC) (Struct ())))
               (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))
           (Ref (Base GC)
            (Variant
             ((Ser (Var 0))
              (Ser
               (Rec (VALTYPE (Atom Ptr) GCRefs)
                (Ref (Base GC)
                 (Variant
                  ((Ser (Ref (Base GC) (Struct ())))
                   (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
           (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))))
         (stack
          ((Exists (Type (VALTYPE (Atom Ptr) GCRefs))
            (Ref (Base GC)
             (Struct
              ((Ser (Var 0))
               (Ser
                (CodeRef
                 (FunctionType ((Type (VALTYPE (Atom Ptr) GCRefs)))
                  ((Ref (Base GC)
                    (Struct
                     ((Ser (Var 1))
                      (Ser
                       (Rec (VALTYPE (Atom Ptr) GCRefs)
                        (Ref (Base GC)
                         (Variant
                          ((Ser (Ref (Base GC) (Struct ())))
                           (Ser
                            (Ref (Base GC)
                             (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
                  (I31))))))))
           (Num (Int I32))))))))
     (instr
      (CaseLoad (ValType (I31)) Copy InferFx
       (((LocalSet 9) (NumConst (Int I32) 0) Tag (LocalGet 9 Move) Drop)
        ((LocalSet 3) (NumConst (Int I32) 1) Tag Untag (CodeRef 0) (Group 0)
         (New GC) (Cast (Ref (Base GC) (Struct ()))) (Group 2) (New GC)
         (Cast
          (Ref (Base GC)
           (Struct
            ((Ser (Ref (Base GC) (Struct ())))
             (Ser
              (CodeRef
               (FunctionType ((Type (VALTYPE (Atom Ptr) GCRefs)))
                ((Ref (Base GC)
                  (Struct
                   ((Ser (Ref (Base GC) (Struct ())))
                    (Ser
                     (Rec (VALTYPE (Atom Ptr) GCRefs)
                      (Ref (Base GC)
                       (Variant
                        ((Ser (Ref (Base GC) (Struct ())))
                         (Ser
                          (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
                (I31))))))))
         (Pack (Type (Ref (Base GC) (Struct ())))
          (Ref (Base GC)
           (Struct
            ((Ser (Var 0))
             (Ser
              (CodeRef
               (FunctionType ((Type (VALTYPE (Atom Ptr) GCRefs)))
                ((Ref (Base GC)
                  (Struct
                   ((Ser (Var 1))
                    (Ser
                     (Rec (VALTYPE (Atom Ptr) GCRefs)
                      (Ref (Base GC)
                       (Variant
                        ((Ser (Ref (Base GC) (Struct ())))
                         (Ser
                          (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
                (I31))))))))
         (Unpack (ValType (I31)) InferFx
          ((LocalSet 4) (LocalGet 4 Move) Copy (LocalSet 4)
           (Load (Path (0)) Follow) (LocalSet 5) Drop (LocalGet 5 Move)
           (LocalSet 6) (LocalGet 4 Move) Copy (LocalSet 4)
           (Load (Path (1)) Follow) (LocalSet 7) Drop (LocalGet 7 Move)
           (LocalSet 8) (LocalGet 3 Move) Copy (LocalSet 3)
           (Load (Path ()) Follow)
           (Fold
            (Ref (Base GC)
             (Variant
              ((Ser (Ref (Base GC) (Struct ())))
               (Ser (Ref (Base GC) (Variant ((Ser (Var 2)) (Ser (Var 0))))))))))
           (New GC) (LocalGet 8 Move) Copy (LocalSet 8) (Inst (Type (Var 1)))
           CallIndirect (LocalGet 8 Move) Drop (LocalGet 6 Move) Drop
           (LocalGet 4 Move) Drop))
         Untag (Num (Int2 I32 Add)) Tag (LocalGet 3 Move) Drop))))
     (env
      ((local_offset 1) (kinds ((VALTYPE (Atom Ptr) GCRefs))) (labels ())
       (return (I31))
       (functions
        ((FunctionType ((Type (VALTYPE (Atom Ptr) GCRefs)))
          ((Ref (Base GC)
            (Struct
             ((Ser (Ref (Base GC) (Struct ())))
              (Ser
               (Rec (VALTYPE (Atom Ptr) GCRefs)
                (Ref (Base GC)
                 (Variant
                  ((Ser (Ref (Base GC) (Struct ())))
                   (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))
          (I31))
         (FunctionType () ((Ref (Base GC) (Struct ()))) (I31))))
       (table
        ((FunctionType ((Type (VALTYPE (Atom Ptr) GCRefs)))
          ((Ref (Base GC)
            (Struct
             ((Ser (Ref (Base GC) (Struct ())))
              (Ser
               (Rec (VALTYPE (Atom Ptr) GCRefs)
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
             (Rec (VALTYPE (Atom Ptr) GCRefs)
              (Ref (Base GC)
               (Variant
                ((Ser (Ref (Base GC) (Struct ())))
                 (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))))))
         (Plug (Prod ((Atom I32))))
         (Rec (VALTYPE (Atom Ptr) GCRefs)
          (Ref (Base GC)
           (Variant
            ((Ser (Ref (Base GC) (Struct ())))
             (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32))))))
       (stack
        ((Ref (Base GC)
          (Variant
           ((Ser (Ref (Base GC) (Struct ())))
            (Ser
             (Ref (Base GC)
              (Variant
               ((Ser (Var 0))
                (Ser
                 (Rec (VALTYPE (Atom Ptr) GCRefs)
                  (Ref (Base GC)
                   (Variant
                    ((Ser (Ref (Base GC) (Struct ())))
                     (Ser
                      (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))))))))))
    -----------mini_zip-----------
    FAILURE Typechecker failed with error(s):
    can't module check types not_equal
    -----------closure_simpl-----------
    FAILURE Typechecker failed with error(s):
    can't module check types not equal
    -----------closure_complex-----------
    FAILURE Typechecker failed with error(s):
    can't module check
      instruction has more arguments than large have_instruction type has, or can't frame out
      types not equal |}]
