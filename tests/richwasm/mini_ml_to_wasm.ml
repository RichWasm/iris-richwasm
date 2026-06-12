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
        (local i32)
        i32.const 1
        i32.const 1
        i32.shl
        local.get 0
        local.set 1
        local.get 1
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 1
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 1
            call 4
          else
            local.get 1
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
        (local i32 i32 i32 i32 i32 i32)
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
        local.get 1
        local.get 1
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 1
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 1
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
        local.get 5
        local.get 3
        local.get 3
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=9 align=2
        else
          local.get 3
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=9 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=9 align=2
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
          i32.store 1 offset=13 align=2
        else
          local.get 4
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=13 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=13 align=2
            local.get 4
            call 6
          end
        end
        local.get 5
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
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 1
        i32.const 1
        i32.shl
        i32.const 2
        i32.const 1
        i32.shl
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
        local.get 1
        local.get 1
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 1
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 1
            call 6
          end
        end
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
        i32.const 3
        i32.const 1
        i32.shl
        i32.const 4
        i32.const 1
        i32.shl
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
        local.get 4
        local.get 4
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 4
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
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
          i32.store 1 offset=5 align=2
        else
          local.get 5
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=5 align=2
            local.get 5
            call 6
          end
        end
        local.get 6
        call 5
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
        local.get 7
        local.get 7
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 7
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 7
            call 6
          end
        end
        local.get 9
        local.get 8
        local.get 8
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=5 align=2
        else
          local.get 8
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=5 align=2
            local.get 8
            call 6
          end
        end
        local.get 9
        call 5
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
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 42
        i32.const 1
        i32.shl
        i32.const 7
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
            local.set 5
            local.get 5
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
        local.get 0
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
      (export "_start" (func 7))
      (export "__rw_table_func_7" (func 7))
      (start 8))

    -----------utuple-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func))
      (type (;5;) (func (param i32) (result i32 i32)))
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
      (func (;7;) (type 5) (param i32) (result i32 i32)
        (local i32)
        i32.const 1
        i32.const 1
        i32.shl
        i32.const 2
        i32.const 1
        i32.shl
        local.get 0
        local.set 1
        local.get 1
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 1
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 1
            call 4
          else
            local.get 1
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

    -----------utuple_split-----------
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
        i32.const 42
        i32.const 1
        i32.shl
        i32.const 7
        i32.const 1
        i32.shl
        local.set 2
        local.set 1
        local.get 2
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
        local.set 2
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
        local.get 2
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
        end
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

    -----------utuple_let-----------
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
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 1
        i32.const 1
        i32.shl
        i32.const 2
        i32.const 1
        i32.shl
        local.set 2
        local.set 1
        local.get 1
        local.get 2
        local.set 6
        local.set 5
        local.get 5
        local.get 6
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
          else
            local.get 5
            i32.load 1 offset=1 align=2
            call 5
            local.set 5
          end
        end
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
          else
            local.get 6
            i32.load 1 offset=1 align=2
            call 5
            local.set 6
          end
        end
        local.get 5
        local.get 6
        local.set 2
        local.set 1
        local.set 4
        local.set 3
        local.get 3
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
        local.set 3
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
        local.get 0
        local.set 12
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
            local.get 12
            call 4
          else
            local.get 12
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

    -----------utuple_in_tuple-----------
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
        i32.const 1
        i32.const 1
        i32.shl
        i32.const 2
        i32.const 1
        i32.shl
        i32.const 3
        i32.const 1
        i32.shl
        local.set 3
        local.set 2
        local.set 1
        i32.const 3
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
        i32.const 2
        i32.const 1
        call 3
        local.get 4
        local.get 1
        local.get 1
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 1
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 1
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
        local.get 4
        local.get 3
        local.get 3
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=9 align=2
        else
          local.get 3
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=9 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=9 align=2
            local.get 3
            call 6
          end
        end
        local.get 4
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

    -----------utuple_of_tuple-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func))
      (type (;5;) (func (param i32) (result i32 i32)))
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
      (func (;7;) (type 5) (param i32) (result i32 i32)
        (local i32 i32 i32 i32)
        i32.const 1
        i32.const 1
        i32.shl
        i32.const 2
        i32.const 1
        i32.shl
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
        local.get 1
        local.get 1
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 1
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 1
            call 6
          end
        end
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
        i32.const 3
        i32.const 1
        i32.shl
        local.get 0
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

    -----------utuple_ref-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func))
      (type (;5;) (func (param i32) (result i32 i32)))
      (type (;6;) (func (result i32 i32)))
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
      (func (;7;) (type 5) (param i32) (result i32 i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 1
        i32.const 1
        i32.shl
        i32.const 2
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
        if (result i32 i32)  ;; label = @1
          unreachable
        else
          local.get 6
          i32.const 2
          i32.and
          i32.eqz
          if (result i32 i32)  ;; label = @2
            local.get 6
            i32.load offset=3 align=2
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
            local.get 6
            i32.load offset=7 align=2
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 6
            i32.load 1 offset=1 align=2
            local.set 6
            local.get 6
            i32.load 1 offset=1 align=2
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
                call 5
              end
            end
            local.get 6
            i32.load 1 offset=5 align=2
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
        local.set 2
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
        local.get 2
        local.get 0
        local.set 12
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
            local.get 12
            call 4
          else
            local.get 12
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

    -----------utuple_fn-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func))
      (type (;5;) (func (result i32 i32)))
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
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        local.get 0
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
        local.set 0
        local.tee 10
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
            local.get 11
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 11
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
            local.get 10
            i32.load 1 offset=1 align=2
            local.set 10
            local.get 10
            i32.load 1 offset=1 align=2
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
                call 5
              end
            end
          end
        end
        local.set 1
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
        local.get 1
        local.set 2
        local.get 0
        local.set 14
        local.get 14
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
          else
            local.get 14
            i32.load 1 offset=1 align=2
            call 5
            local.set 14
          end
        end
        local.get 14
        local.set 0
        local.tee 15
        local.get 15
        i32.const 1
        i32.and
        i32.eqz
        if (result i32 i32)  ;; label = @1
          unreachable
        else
          local.get 15
          i32.const 2
          i32.and
          i32.eqz
          if (result i32 i32)  ;; label = @2
            local.get 15
            i32.load offset=7 align=2
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
            local.get 15
            i32.load offset=11 align=2
            local.tee 17
            local.get 17
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 17
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
            local.get 15
            i32.load 1 offset=1 align=2
            local.set 15
            local.get 15
            i32.load 1 offset=5 align=2
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
                call 5
              end
            end
            local.get 15
            i32.load 1 offset=9 align=2
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
        local.set 3
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
        local.get 3
        local.get 4
        local.set 6
        local.set 5
        local.get 5
        local.get 6
        local.set 22
        local.set 21
        local.get 21
        local.get 22
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
            i32.load 1 offset=1 align=2
            call 5
            local.set 21
          end
        end
        local.get 22
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 22
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 22
            i32.load 1 offset=1 align=2
            call 5
            local.set 22
          end
        end
        local.get 21
        local.get 22
        local.set 6
        local.set 5
        local.set 8
        local.set 7
        local.get 7
        local.set 23
        local.get 23
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
          else
            local.get 23
            i32.load 1 offset=1 align=2
            call 5
            local.set 23
          end
        end
        local.get 23
        local.set 7
        local.get 7
        local.set 24
        local.get 24
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 24
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 24
            call 4
          else
            local.get 24
            call 6
          end
        end
        local.get 8
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
        local.get 6
        local.set 26
        local.get 26
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 26
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 26
            call 4
          else
            local.get 26
            call 6
          end
        end
        local.set 27
        local.get 27
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 27
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 27
            call 4
          else
            local.get 27
            call 6
          end
        end
        local.get 2
        local.set 28
        local.get 28
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 28
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 28
            call 4
          else
            local.get 28
            call 6
          end
        end
        local.get 0
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
        end)
      (func (;8;) (type 1) (param i32) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 0
        call 2
        local.set 6
        local.get 6
        call 5
        i32.const 0
        global.get 1
        i32.add
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
        i32.const 0
        call 3
        local.get 9
        local.get 7
        local.get 7
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 7
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 7
            call 6
          end
        end
        local.get 9
        local.get 8
        i32.store 1 offset=5 align=2
        local.get 9
        call 5
        block (param i32) (result i32)  ;; label = @1
          local.set 1
          local.get 1
          local.set 10
          local.get 10
          local.get 10
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 10
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
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
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 11
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 11
              i32.load offset=3 align=2
              local.tee 12
              local.get 12
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 12
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  i32.load 1 offset=1 align=2
                  call 5
                end
              end
            else
              local.get 11
              i32.load 1 offset=1 align=2
              local.set 11
              local.get 11
              i32.load 1 offset=1 align=2
              local.tee 13
              local.get 13
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 13
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  call 5
                end
              end
            end
          end
          local.set 2
          local.set 14
          local.get 14
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 14
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 14
              call 4
            else
              local.get 14
              call 6
            end
          end
          local.get 2
          local.set 3
          local.get 1
          local.set 15
          local.get 15
          local.get 15
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 15
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 15
              i32.load 1 offset=1 align=2
              call 5
              local.set 15
            end
          end
          local.get 15
          local.set 1
          local.tee 16
          local.get 16
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 16
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 16
              i32.load offset=7 align=2
              local.tee 17
            else
              local.get 16
              i32.load 1 offset=1 align=2
              local.set 16
              local.get 16
              i32.load 1 offset=5 align=2
              local.tee 18
            end
          end
          local.set 4
          local.set 19
          local.get 19
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 19
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 19
              call 4
            else
              local.get 19
              call 6
            end
          end
          local.get 4
          local.set 5
          local.get 3
          local.set 20
          local.get 20
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
            else
              local.get 20
              i32.load 1 offset=1 align=2
              call 5
              local.set 20
            end
          end
          local.get 20
          local.set 3
          i32.const 5
          i32.const 1
          i32.shl
          i32.const 6
          i32.const 1
          i32.shl
          local.set 23
          local.set 22
          local.set 21
          i32.const 3
          call 2
          local.set 24
          local.get 24
          i32.const 0
          i32.const 1
          call 3
          local.get 24
          i32.const 1
          i32.const 1
          call 3
          local.get 24
          i32.const 2
          i32.const 1
          call 3
          local.get 24
          local.get 21
          local.get 21
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            local.get 21
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=1 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=1 align=2
              local.get 21
              call 6
            end
          end
          local.get 24
          local.get 22
          local.get 22
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            local.get 22
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=5 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=5 align=2
              local.get 22
              call 6
            end
          end
          local.get 24
          local.get 23
          local.get 23
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=9 align=2
          else
            local.get 23
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=9 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=9 align=2
              local.get 23
              call 6
            end
          end
          local.get 24
          call 5
          local.get 5
          local.set 25
          local.get 25
          local.get 25
          local.set 5
          call_indirect (type 1)
          local.get 5
          drop
          local.get 3
          local.set 26
          local.get 26
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 26
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 26
              call 4
            else
              local.get 26
              call 6
            end
          end
          local.get 1
          local.set 27
          local.get 27
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 27
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 27
              call 4
            else
              local.get 27
              call 6
            end
          end
        end
        local.get 0
        local.set 28
        local.get 28
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 28
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 28
            call 4
          else
            local.get 28
            call 6
          end
        end)
      (func (;9;) (type 4)
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
      (export "_start" (func 8))
      (export "__rw_table_func_7" (func 7))
      (export "__rw_table_func_8" (func 8))
      (start 9))

    -----------utuple_ret-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func))
      (type (;5;) (func (param i32) (result i32 i32)))
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
      (func (;7;) (type 5) (param i32) (result i32 i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        local.get 0
        local.set 5
        local.get 5
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
          else
            local.get 5
            i32.load 1 offset=1 align=2
            call 5
            local.set 5
          end
        end
        local.get 5
        local.set 0
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
            i32.load offset=3 align=2
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
            local.set 6
            local.get 6
            i32.load 1 offset=1 align=2
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
        local.set 2
        local.get 0
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
        local.set 0
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
            i32.load offset=7 align=2
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
            local.set 11
            local.get 11
            i32.load 1 offset=5 align=2
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
        local.set 4
        local.get 4
        local.set 15
        local.get 15
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
          else
            local.get 15
            i32.load 1 offset=1 align=2
            call 5
            local.set 15
          end
        end
        local.get 15
        local.set 4
        i32.const 9
        i32.const 1
        i32.shl
        local.get 4
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
        local.get 0
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
        end)
      (func (;8;) (type 1) (param i32) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 0
        call 2
        local.set 8
        local.get 8
        call 5
        i32.const 0
        global.get 1
        i32.add
        local.set 10
        local.set 9
        i32.const 2
        call 2
        local.set 11
        local.get 11
        i32.const 0
        i32.const 1
        call 3
        local.get 11
        i32.const 1
        i32.const 0
        call 3
        local.get 11
        local.get 9
        local.get 9
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 9
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 9
            call 6
          end
        end
        local.get 11
        local.get 10
        i32.store 1 offset=5 align=2
        local.get 11
        call 5
        block (param i32) (result i32 i32)  ;; label = @1
          local.set 1
          local.get 1
          local.set 12
          local.get 12
          local.get 12
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 12
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 12
              i32.load 1 offset=1 align=2
              call 5
              local.set 12
            end
          end
          local.get 12
          local.set 1
          local.tee 13
          local.get 13
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 13
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 13
              i32.load offset=3 align=2
              local.tee 14
              local.get 14
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 14
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  i32.load 1 offset=1 align=2
                  call 5
                end
              end
            else
              local.get 13
              i32.load 1 offset=1 align=2
              local.set 13
              local.get 13
              i32.load 1 offset=1 align=2
              local.tee 15
              local.get 15
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 15
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  call 5
                end
              end
            end
          end
          local.set 2
          local.set 16
          local.get 16
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 16
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 16
              call 4
            else
              local.get 16
              call 6
            end
          end
          local.get 2
          local.set 3
          local.get 1
          local.set 17
          local.get 17
          local.get 17
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 17
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 17
              i32.load 1 offset=1 align=2
              call 5
              local.set 17
            end
          end
          local.get 17
          local.set 1
          local.tee 18
          local.get 18
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 18
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 18
              i32.load offset=7 align=2
              local.tee 19
            else
              local.get 18
              i32.load 1 offset=1 align=2
              local.set 18
              local.get 18
              i32.load 1 offset=5 align=2
              local.tee 20
            end
          end
          local.set 4
          local.set 21
          local.get 21
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 21
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 21
              call 4
            else
              local.get 21
              call 6
            end
          end
          local.get 4
          local.set 5
          local.get 3
          local.set 22
          local.get 22
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
            else
              local.get 22
              i32.load 1 offset=1 align=2
              call 5
              local.set 22
            end
          end
          local.get 22
          local.set 3
          i32.const 4
          i32.const 1
          i32.shl
          local.set 24
          local.set 23
          i32.const 2
          call 2
          local.set 25
          local.get 25
          i32.const 0
          i32.const 1
          call 3
          local.get 25
          i32.const 1
          i32.const 1
          call 3
          local.get 25
          local.get 23
          local.get 23
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            local.get 23
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=1 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=1 align=2
              local.get 23
              call 6
            end
          end
          local.get 25
          local.get 24
          local.get 24
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            local.get 24
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=5 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=5 align=2
              local.get 24
              call 6
            end
          end
          local.get 25
          call 5
          local.get 5
          local.set 26
          local.get 26
          local.get 26
          local.set 5
          call_indirect (type 5)
          local.get 5
          drop
          local.get 3
          local.set 27
          local.get 27
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 27
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 27
              call 4
            else
              local.get 27
              call 6
            end
          end
          local.get 1
          local.set 28
          local.get 28
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 28
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 28
              call 4
            else
              local.get 28
              call 6
            end
          end
        end
        local.set 7
        local.set 6
        local.get 7
        local.set 29
        local.get 29
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
          else
            local.get 29
            i32.load 1 offset=1 align=2
            call 5
            local.set 29
          end
        end
        local.get 29
        local.set 7
        local.get 6
        local.set 30
        local.get 30
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 30
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 30
            call 4
          else
            local.get 30
            call 6
          end
        end
        local.get 7
        local.set 31
        local.get 31
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 31
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 31
            call 4
          else
            local.get 31
            call 6
          end
        end
        local.get 0
        local.set 32
        local.get 32
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 32
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 32
            call 4
          else
            local.get 32
            call 6
          end
        end)
      (func (;9;) (type 4)
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
      (export "_start" (func 8))
      (export "__rw_table_func_7" (func 7))
      (export "__rw_table_func_8" (func 8))
      (start 9))

    -----------lin_make-----------
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
      (import "" "" (func (;7;) (type 1)))
      (func (;8;) (type 1) (param i32) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 0
        call 2
        local.set 6
        local.get 6
        call 5
        i32.const 0
        global.get 1
        i32.add
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
        i32.const 0
        call 3
        local.get 9
        local.get 7
        local.get 7
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 7
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 7
            call 6
          end
        end
        local.get 9
        local.get 8
        i32.store 1 offset=5 align=2
        local.get 9
        call 5
        block (param i32) (result i32)  ;; label = @1
          local.set 1
          local.get 1
          local.set 10
          local.get 10
          local.get 10
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 10
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
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
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 11
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 11
              i32.load offset=3 align=2
              local.tee 12
              local.get 12
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 12
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  i32.load 1 offset=1 align=2
                  call 5
                end
              end
            else
              local.get 11
              i32.load 1 offset=1 align=2
              local.set 11
              local.get 11
              i32.load 1 offset=1 align=2
              local.tee 13
              local.get 13
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 13
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  call 5
                end
              end
            end
          end
          local.set 2
          local.set 14
          local.get 14
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 14
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 14
              call 4
            else
              local.get 14
              call 6
            end
          end
          local.get 2
          local.set 3
          local.get 1
          local.set 15
          local.get 15
          local.get 15
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 15
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 15
              i32.load 1 offset=1 align=2
              call 5
              local.set 15
            end
          end
          local.get 15
          local.set 1
          local.tee 16
          local.get 16
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 16
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 16
              i32.load offset=7 align=2
              local.tee 17
            else
              local.get 16
              i32.load 1 offset=1 align=2
              local.set 16
              local.get 16
              i32.load 1 offset=5 align=2
              local.tee 18
            end
          end
          local.set 4
          local.set 19
          local.get 19
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 19
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 19
              call 4
            else
              local.get 19
              call 6
            end
          end
          local.get 4
          local.set 5
          local.get 3
          local.set 20
          local.get 20
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
            else
              local.get 20
              i32.load 1 offset=1 align=2
              call 5
              local.set 20
            end
          end
          local.get 20
          local.set 3
          i32.const 5
          i32.const 1
          i32.shl
          local.set 22
          local.set 21
          i32.const 2
          call 2
          local.set 23
          local.get 23
          i32.const 0
          i32.const 1
          call 3
          local.get 23
          i32.const 1
          i32.const 1
          call 3
          local.get 23
          local.get 21
          local.get 21
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            local.get 21
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=1 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=1 align=2
              local.get 21
              call 6
            end
          end
          local.get 23
          local.get 22
          local.get 22
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            local.get 22
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=5 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=5 align=2
              local.get 22
              call 6
            end
          end
          local.get 23
          call 5
          local.get 5
          local.set 24
          local.get 24
          local.get 24
          local.set 5
          call_indirect (type 1)
          local.get 5
          drop
          local.get 3
          local.set 25
          local.get 25
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 25
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 25
              call 4
            else
              local.get 25
              call 6
            end
          end
          local.get 1
          local.set 26
          local.get 26
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 26
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 26
              call 4
            else
              local.get 26
              call 6
            end
          end
        end
        local.get 0
        local.set 27
        local.get 27
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 27
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 27
            call 4
          else
            local.get 27
            call 6
          end
        end)
      (func (;9;) (type 4)
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
      (export "_start" (func 8))
      (export "__rw_table_func_7" (func 7))
      (export "__rw_table_func_8" (func 8))
      (start 9))

    -----------lin_deref-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func))
      (type (;5;) (func (param i32) (result i32 i32)))
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
      (import "" "" (func (;7;) (type 1)))
      (func (;8;) (type 5) (param i32) (result i32 i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 0
        call 2
        local.set 6
        local.get 6
        call 5
        i32.const 0
        global.get 1
        i32.add
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
        i32.const 0
        call 3
        local.get 9
        local.get 7
        local.get 7
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 7
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 7
            call 6
          end
        end
        local.get 9
        local.get 8
        i32.store 1 offset=5 align=2
        local.get 9
        call 5
        block (param i32) (result i32)  ;; label = @1
          local.set 1
          local.get 1
          local.set 10
          local.get 10
          local.get 10
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 10
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
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
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 11
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 11
              i32.load offset=3 align=2
              local.tee 12
              local.get 12
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 12
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  i32.load 1 offset=1 align=2
                  call 5
                end
              end
            else
              local.get 11
              i32.load 1 offset=1 align=2
              local.set 11
              local.get 11
              i32.load 1 offset=1 align=2
              local.tee 13
              local.get 13
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 13
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  call 5
                end
              end
            end
          end
          local.set 2
          local.set 14
          local.get 14
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 14
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 14
              call 4
            else
              local.get 14
              call 6
            end
          end
          local.get 2
          local.set 3
          local.get 1
          local.set 15
          local.get 15
          local.get 15
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 15
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 15
              i32.load 1 offset=1 align=2
              call 5
              local.set 15
            end
          end
          local.get 15
          local.set 1
          local.tee 16
          local.get 16
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 16
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 16
              i32.load offset=7 align=2
              local.tee 17
            else
              local.get 16
              i32.load 1 offset=1 align=2
              local.set 16
              local.get 16
              i32.load 1 offset=5 align=2
              local.tee 18
            end
          end
          local.set 4
          local.set 19
          local.get 19
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 19
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 19
              call 4
            else
              local.get 19
              call 6
            end
          end
          local.get 4
          local.set 5
          local.get 3
          local.set 20
          local.get 20
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
            else
              local.get 20
              i32.load 1 offset=1 align=2
              call 5
              local.set 20
            end
          end
          local.get 20
          local.set 3
          i32.const 5
          i32.const 1
          i32.shl
          local.set 22
          local.set 21
          i32.const 2
          call 2
          local.set 23
          local.get 23
          i32.const 0
          i32.const 1
          call 3
          local.get 23
          i32.const 1
          i32.const 1
          call 3
          local.get 23
          local.get 21
          local.get 21
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            local.get 21
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=1 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=1 align=2
              local.get 21
              call 6
            end
          end
          local.get 23
          local.get 22
          local.get 22
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            local.get 22
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=5 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=5 align=2
              local.get 22
              call 6
            end
          end
          local.get 23
          call 5
          local.get 5
          local.set 24
          local.get 24
          local.get 24
          local.set 5
          call_indirect (type 1)
          local.get 5
          drop
          local.get 3
          local.set 25
          local.get 25
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 25
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 25
              call 4
            else
              local.get 25
              call 6
            end
          end
          local.get 1
          local.set 26
          local.get 26
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 26
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 26
              call 4
            else
              local.get 26
              call 6
            end
          end
        end
        local.tee 27
        local.get 27
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 27
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 27
            i32.load offset=3 align=2
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 27
            i32.load 1 offset=1 align=2
            local.set 27
            local.get 27
            i32.load 1 offset=1 align=2
            local.tee 29
            local.get 29
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 29
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
        local.get 0
        local.set 30
        local.get 30
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 30
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 30
            call 4
          else
            local.get 30
            call 6
          end
        end)
      (func (;9;) (type 4)
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
      (export "_start" (func 8))
      (export "__rw_table_func_7" (func 7))
      (export "__rw_table_func_8" (func 8))
      (start 9))

    -----------lin_assign-----------
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
      (import "" "" (func (;7;) (type 1)))
      (func (;8;) (type 1) (param i32) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 0
        call 2
        local.set 6
        local.get 6
        call 5
        i32.const 0
        global.get 1
        i32.add
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
        i32.const 0
        call 3
        local.get 9
        local.get 7
        local.get 7
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 7
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 7
            call 6
          end
        end
        local.get 9
        local.get 8
        i32.store 1 offset=5 align=2
        local.get 9
        call 5
        block (param i32) (result i32)  ;; label = @1
          local.set 1
          local.get 1
          local.set 10
          local.get 10
          local.get 10
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 10
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
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
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 11
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 11
              i32.load offset=3 align=2
              local.tee 12
              local.get 12
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 12
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  i32.load 1 offset=1 align=2
                  call 5
                end
              end
            else
              local.get 11
              i32.load 1 offset=1 align=2
              local.set 11
              local.get 11
              i32.load 1 offset=1 align=2
              local.tee 13
              local.get 13
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 13
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  call 5
                end
              end
            end
          end
          local.set 2
          local.set 14
          local.get 14
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 14
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 14
              call 4
            else
              local.get 14
              call 6
            end
          end
          local.get 2
          local.set 3
          local.get 1
          local.set 15
          local.get 15
          local.get 15
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 15
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 15
              i32.load 1 offset=1 align=2
              call 5
              local.set 15
            end
          end
          local.get 15
          local.set 1
          local.tee 16
          local.get 16
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 16
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 16
              i32.load offset=7 align=2
              local.tee 17
            else
              local.get 16
              i32.load 1 offset=1 align=2
              local.set 16
              local.get 16
              i32.load 1 offset=5 align=2
              local.tee 18
            end
          end
          local.set 4
          local.set 19
          local.get 19
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 19
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 19
              call 4
            else
              local.get 19
              call 6
            end
          end
          local.get 4
          local.set 5
          local.get 3
          local.set 20
          local.get 20
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
            else
              local.get 20
              i32.load 1 offset=1 align=2
              call 5
              local.set 20
            end
          end
          local.get 20
          local.set 3
          i32.const 5
          i32.const 1
          i32.shl
          local.set 22
          local.set 21
          i32.const 2
          call 2
          local.set 23
          local.get 23
          i32.const 0
          i32.const 1
          call 3
          local.get 23
          i32.const 1
          i32.const 1
          call 3
          local.get 23
          local.get 21
          local.get 21
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            local.get 21
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=1 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=1 align=2
              local.get 21
              call 6
            end
          end
          local.get 23
          local.get 22
          local.get 22
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            local.get 22
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=5 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=5 align=2
              local.get 22
              call 6
            end
          end
          local.get 23
          call 5
          local.get 5
          local.set 24
          local.get 24
          local.get 24
          local.set 5
          call_indirect (type 1)
          local.get 5
          drop
          local.get 3
          local.set 25
          local.get 25
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 25
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 25
              call 4
            else
              local.get 25
              call 6
            end
          end
          local.get 1
          local.set 26
          local.get 26
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 26
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 26
              call 4
            else
              local.get 26
              call 6
            end
          end
        end
        i32.const 8
        i32.const 1
        i32.shl
        local.set 27
        local.tee 28
        local.get 28
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
          unreachable
        else
          local.get 28
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 28
            local.get 27
            i32.store offset=3 align=2
          else
            local.get 28
            i32.load 1 offset=1 align=2
            local.set 28
            local.get 28
            local.get 27
            local.get 27
            i32.const 1
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=1 align=2
            else
              local.get 27
              i32.const 2
              i32.and
              i32.eqz
              if (param i32 i32)  ;; label = @4
                i32.store 1 offset=1 align=2
              else
                i32.load 1 offset=1 align=2
                i32.store 1 offset=1 align=2
                local.get 27
                call 6
              end
            end
          end
        end
        local.get 28
        i32.const 0
        i32.const 1
        call 3
        local.get 0
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
        end)
      (func (;9;) (type 4)
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
      (export "_start" (func 8))
      (export "__rw_table_func_7" (func 7))
      (export "__rw_table_func_8" (func 8))
      (start 9))

    -----------lin_let-----------
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
      (import "" "" (func (;7;) (type 1)))
      (func (;8;) (type 1) (param i32) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 0
        call 2
        local.set 7
        local.get 7
        call 5
        i32.const 0
        global.get 1
        i32.add
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
        i32.const 0
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
        i32.store 1 offset=5 align=2
        local.get 10
        call 5
        block (param i32) (result i32)  ;; label = @1
          local.set 1
          local.get 1
          local.set 11
          local.get 11
          local.get 11
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 11
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 11
              i32.load 1 offset=1 align=2
              call 5
              local.set 11
            end
          end
          local.get 11
          local.set 1
          local.tee 12
          local.get 12
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 12
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 12
              i32.load offset=3 align=2
              local.tee 13
              local.get 13
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 13
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  i32.load 1 offset=1 align=2
                  call 5
                end
              end
            else
              local.get 12
              i32.load 1 offset=1 align=2
              local.set 12
              local.get 12
              i32.load 1 offset=1 align=2
              local.tee 14
              local.get 14
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 14
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  call 5
                end
              end
            end
          end
          local.set 2
          local.set 15
          local.get 15
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 15
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 15
              call 4
            else
              local.get 15
              call 6
            end
          end
          local.get 2
          local.set 3
          local.get 1
          local.set 16
          local.get 16
          local.get 16
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 16
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 16
              i32.load 1 offset=1 align=2
              call 5
              local.set 16
            end
          end
          local.get 16
          local.set 1
          local.tee 17
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
              i32.load offset=7 align=2
              local.tee 18
            else
              local.get 17
              i32.load 1 offset=1 align=2
              local.set 17
              local.get 17
              i32.load 1 offset=5 align=2
              local.tee 19
            end
          end
          local.set 4
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
          local.get 4
          local.set 5
          local.get 3
          local.set 21
          local.get 21
          local.get 21
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 21
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 21
              i32.load 1 offset=1 align=2
              call 5
              local.set 21
            end
          end
          local.get 21
          local.set 3
          i32.const 3
          i32.const 1
          i32.shl
          local.set 23
          local.set 22
          i32.const 2
          call 2
          local.set 24
          local.get 24
          i32.const 0
          i32.const 1
          call 3
          local.get 24
          i32.const 1
          i32.const 1
          call 3
          local.get 24
          local.get 22
          local.get 22
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            local.get 22
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=1 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=1 align=2
              local.get 22
              call 6
            end
          end
          local.get 24
          local.get 23
          local.get 23
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            local.get 23
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=5 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=5 align=2
              local.get 23
              call 6
            end
          end
          local.get 24
          call 5
          local.get 5
          local.set 25
          local.get 25
          local.get 25
          local.set 5
          call_indirect (type 1)
          local.get 5
          drop
          local.get 3
          local.set 26
          local.get 26
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 26
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 26
              call 4
            else
              local.get 26
              call 6
            end
          end
          local.get 1
          local.set 27
          local.get 27
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 27
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 27
              call 4
            else
              local.get 27
              call 6
            end
          end
        end
        local.set 6
        local.get 6
        i32.const 9
        i32.const 1
        i32.shl
        local.set 28
        local.tee 29
        local.get 29
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
          unreachable
        else
          local.get 29
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 29
            local.get 28
            i32.store offset=3 align=2
          else
            local.get 29
            i32.load 1 offset=1 align=2
            local.set 29
            local.get 29
            local.get 28
            local.get 28
            i32.const 1
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=1 align=2
            else
              local.get 28
              i32.const 2
              i32.and
              i32.eqz
              if (param i32 i32)  ;; label = @4
                i32.store 1 offset=1 align=2
              else
                i32.load 1 offset=1 align=2
                i32.store 1 offset=1 align=2
                local.get 28
                call 6
              end
            end
          end
        end
        local.get 29
        i32.const 0
        i32.const 1
        call 3
        local.get 6
        drop
        local.get 0
        local.set 30
        local.get 30
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 30
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 30
            call 4
          else
            local.get 30
            call 6
          end
        end)
      (func (;9;) (type 4)
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
      (export "_start" (func 8))
      (export "__rw_table_func_7" (func 7))
      (export "__rw_table_func_8" (func 8))
      (start 9))

    -----------lin_roundtrip-----------
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func))
      (type (;5;) (func (param i32) (result i32 i32)))
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
      (import "" "" (func (;7;) (type 1)))
      (func (;8;) (type 5) (param i32) (result i32 i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 0
        call 2
        local.set 8
        local.get 8
        call 5
        i32.const 0
        global.get 1
        i32.add
        local.set 10
        local.set 9
        i32.const 2
        call 2
        local.set 11
        local.get 11
        i32.const 0
        i32.const 1
        call 3
        local.get 11
        i32.const 1
        i32.const 0
        call 3
        local.get 11
        local.get 9
        local.get 9
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 9
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 9
            call 6
          end
        end
        local.get 11
        local.get 10
        i32.store 1 offset=5 align=2
        local.get 11
        call 5
        block (param i32) (result i32)  ;; label = @1
          local.set 1
          local.get 1
          local.set 12
          local.get 12
          local.get 12
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 12
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 12
              i32.load 1 offset=1 align=2
              call 5
              local.set 12
            end
          end
          local.get 12
          local.set 1
          local.tee 13
          local.get 13
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 13
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 13
              i32.load offset=3 align=2
              local.tee 14
              local.get 14
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 14
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  i32.load 1 offset=1 align=2
                  call 5
                end
              end
            else
              local.get 13
              i32.load 1 offset=1 align=2
              local.set 13
              local.get 13
              i32.load 1 offset=1 align=2
              local.tee 15
              local.get 15
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 15
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  call 5
                end
              end
            end
          end
          local.set 2
          local.set 16
          local.get 16
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 16
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 16
              call 4
            else
              local.get 16
              call 6
            end
          end
          local.get 2
          local.set 3
          local.get 1
          local.set 17
          local.get 17
          local.get 17
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 17
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 17
              i32.load 1 offset=1 align=2
              call 5
              local.set 17
            end
          end
          local.get 17
          local.set 1
          local.tee 18
          local.get 18
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 18
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 18
              i32.load offset=7 align=2
              local.tee 19
            else
              local.get 18
              i32.load 1 offset=1 align=2
              local.set 18
              local.get 18
              i32.load 1 offset=5 align=2
              local.tee 20
            end
          end
          local.set 4
          local.set 21
          local.get 21
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 21
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 21
              call 4
            else
              local.get 21
              call 6
            end
          end
          local.get 4
          local.set 5
          local.get 3
          local.set 22
          local.get 22
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
            else
              local.get 22
              i32.load 1 offset=1 align=2
              call 5
              local.set 22
            end
          end
          local.get 22
          local.set 3
          i32.const 3
          i32.const 1
          i32.shl
          local.set 24
          local.set 23
          i32.const 2
          call 2
          local.set 25
          local.get 25
          i32.const 0
          i32.const 1
          call 3
          local.get 25
          i32.const 1
          i32.const 1
          call 3
          local.get 25
          local.get 23
          local.get 23
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            local.get 23
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=1 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=1 align=2
              local.get 23
              call 6
            end
          end
          local.get 25
          local.get 24
          local.get 24
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            local.get 24
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=5 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=5 align=2
              local.get 24
              call 6
            end
          end
          local.get 25
          call 5
          local.get 5
          local.set 26
          local.get 26
          local.get 26
          local.set 5
          call_indirect (type 1)
          local.get 5
          drop
          local.get 3
          local.set 27
          local.get 27
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 27
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 27
              call 4
            else
              local.get 27
              call 6
            end
          end
          local.get 1
          local.set 28
          local.get 28
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 28
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 28
              call 4
            else
              local.get 28
              call 6
            end
          end
        end
        i32.const 8
        i32.const 1
        i32.shl
        local.set 29
        local.tee 30
        local.get 30
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
          unreachable
        else
          local.get 30
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 30
            local.get 29
            i32.store offset=3 align=2
          else
            local.get 30
            i32.load 1 offset=1 align=2
            local.set 30
            local.get 30
            local.get 29
            local.get 29
            i32.const 1
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=1 align=2
            else
              local.get 29
              i32.const 2
              i32.and
              i32.eqz
              if (param i32 i32)  ;; label = @4
                i32.store 1 offset=1 align=2
              else
                i32.load 1 offset=1 align=2
                i32.store 1 offset=1 align=2
                local.get 29
                call 6
              end
            end
          end
        end
        local.get 30
        i32.const 0
        i32.const 1
        call 3
        local.tee 31
        local.get 31
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 31
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 31
            i32.load offset=3 align=2
            local.tee 32
            local.get 32
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 32
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
            local.get 31
            i32.load 1 offset=1 align=2
            local.set 31
            local.get 31
            i32.load 1 offset=1 align=2
            local.tee 33
            local.get 33
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 33
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
        local.set 7
        local.set 6
        local.get 6
        local.get 7
        local.set 34
        local.get 34
        local.get 34
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 34
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 34
            i32.load 1 offset=1 align=2
            call 5
            local.set 34
          end
        end
        local.get 34
        local.set 7
        local.get 6
        drop
        local.get 7
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
        end
        local.get 0
        local.set 36
        local.get 36
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 36
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 36
            call 4
          else
            local.get 36
            call 6
          end
        end)
      (func (;9;) (type 4)
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
      (export "_start" (func 8))
      (export "__rw_table_func_7" (func 7))
      (export "__rw_table_func_8" (func 8))
      (start 9))

    -----------lin_reuse_rejected-----------
    FAILURE (InstrErr (error (NonRef Store (Plug (Prod ((Atom I32))))))
     (instr (Store (Path ())))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return
        ((Prod ((Ref (Base MM) Mut (Ser I31)) (Ref (Base MM) Mut (Ser I31))))))
       (functions
        ((FunctionType ()
          ((Ref (Base GC) Imm
            (Struct ((Ser (Ref (Base GC) Imm (Struct ()))) (Ser I31)))))
          ((Ref (Base MM) Mut (Ser I31))))
         (FunctionType () ((Ref (Base GC) Imm (Struct ())))
          ((Prod ((Ref (Base MM) Mut (Ser I31)) (Ref (Base MM) Mut (Ser I31))))))))
       (table
        ((FunctionType ()
          ((Ref (Base GC) Imm
            (Struct ((Ser (Ref (Base GC) Imm (Struct ()))) (Ser I31)))))
          ((Ref (Base MM) Mut (Ser I31))))
         (FunctionType () ((Ref (Base GC) Imm (Struct ())))
          ((Prod ((Ref (Base MM) Mut (Ser I31)) (Ref (Base MM) Mut (Ser I31))))))))
       (lfx ())))
     (state
      ((locals
        ((Ref (Base GC) Imm (Struct ())) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32)))) (Plug (Prod ((Atom I32))))
         (Plug (Prod ((Atom I32))))))
       (stack (I31 (Plug (Prod ((Atom I32)))) (Ref (Base MM) Mut (Ser I31)))))))
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
        (local i32 i32 i32 i32 i32)
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
        i32.store 1 offset=1 align=2
        local.get 2
        local.get 1
        local.get 1
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=5 align=2
        else
          local.get 1
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=5 align=2
            local.get 1
            call 6
          end
        end
        local.get 2
        call 5
        local.get 0
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
        (local i32)
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
        local.set 1
        local.get 1
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 1
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 1
            call 4
          else
            local.get 1
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
        i32.shl
        local.get 0
        local.set 1
        local.get 1
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 1
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 1
            call 4
          else
            local.get 1
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
        i32.shl
        local.get 0
        local.set 1
        local.get 1
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 1
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 1
            call 4
          else
            local.get 1
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
        i32.shl
        local.get 0
        local.set 1
        local.get 1
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 1
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 1
            call 4
          else
            local.get 1
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
        i32.shl
        local.get 0
        local.set 1
        local.get 1
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 1
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 1
            call 4
          else
            local.get 1
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
        i32.shl
        local.get 0
        local.set 1
        local.get 1
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 1
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 1
            call 4
          else
            local.get 1
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
            i32.load 1 offset=1 align=2
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
        end
        local.get 0
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
        local.get 0
        local.set 5
        local.get 5
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
          else
            local.get 5
            i32.load 1 offset=1 align=2
            call 5
            local.set 5
          end
        end
        local.get 5
        local.set 0
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
            i32.load offset=3 align=2
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
            local.set 6
            local.get 6
            i32.load 1 offset=1 align=2
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
        local.set 2
        local.get 0
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
        local.set 0
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
            i32.load offset=7 align=2
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
            local.set 11
            local.get 11
            i32.load 1 offset=5 align=2
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
        local.set 4
        i32.const 1
        i32.const 1
        i32.shl
        local.get 4
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
      (func (;8;) (type 1) (param i32) (result i32)
        (local i32 i32 i32 i32 i32)
        i32.const 0
        call 2
        local.set 1
        local.get 1
        call 5
        i32.const 0
        global.get 1
        i32.add
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
        i32.const 0
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
        i32.store 1 offset=5 align=2
        local.get 4
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
      (func (;9;) (type 4)
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
      (export "_start" (func 8))
      (export "__rw_table_func_7" (func 7))
      (export "__rw_table_func_8" (func 8))
      (start 9))

    -----------iife-----------
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
        local.get 0
        local.set 5
        local.get 5
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
          else
            local.get 5
            i32.load 1 offset=1 align=2
            call 5
            local.set 5
          end
        end
        local.get 5
        local.set 0
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
            i32.load offset=3 align=2
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
            local.set 6
            local.get 6
            i32.load 1 offset=1 align=2
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
        local.set 2
        local.get 0
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
        local.set 0
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
            i32.load offset=7 align=2
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
            local.set 11
            local.get 11
            i32.load 1 offset=5 align=2
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
        local.set 4
        i32.const 1
        i32.const 1
        i32.shl
        local.get 4
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
      (func (;8;) (type 1) (param i32) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 0
        call 2
        local.set 6
        local.get 6
        call 5
        i32.const 0
        global.get 1
        i32.add
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
        i32.const 0
        call 3
        local.get 9
        local.get 7
        local.get 7
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 7
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 7
            call 6
          end
        end
        local.get 9
        local.get 8
        i32.store 1 offset=5 align=2
        local.get 9
        call 5
        block (param i32) (result i32)  ;; label = @1
          local.set 1
          local.get 1
          local.set 10
          local.get 10
          local.get 10
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 10
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
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
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 11
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 11
              i32.load offset=3 align=2
              local.tee 12
              local.get 12
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 12
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  i32.load 1 offset=1 align=2
                  call 5
                end
              end
            else
              local.get 11
              i32.load 1 offset=1 align=2
              local.set 11
              local.get 11
              i32.load 1 offset=1 align=2
              local.tee 13
              local.get 13
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 13
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  call 5
                end
              end
            end
          end
          local.set 2
          local.set 14
          local.get 14
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 14
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 14
              call 4
            else
              local.get 14
              call 6
            end
          end
          local.get 2
          local.set 3
          local.get 1
          local.set 15
          local.get 15
          local.get 15
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 15
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 15
              i32.load 1 offset=1 align=2
              call 5
              local.set 15
            end
          end
          local.get 15
          local.set 1
          local.tee 16
          local.get 16
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 16
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 16
              i32.load offset=7 align=2
              local.tee 17
            else
              local.get 16
              i32.load 1 offset=1 align=2
              local.set 16
              local.get 16
              i32.load 1 offset=5 align=2
              local.tee 18
            end
          end
          local.set 4
          local.set 19
          local.get 19
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 19
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 19
              call 4
            else
              local.get 19
              call 6
            end
          end
          local.get 4
          local.set 5
          local.get 3
          local.set 20
          local.get 20
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
            else
              local.get 20
              i32.load 1 offset=1 align=2
              call 5
              local.set 20
            end
          end
          local.get 20
          local.set 3
          i32.const 0
          call 2
          local.set 21
          local.get 21
          call 5
          local.set 23
          local.set 22
          i32.const 2
          call 2
          local.set 24
          local.get 24
          i32.const 0
          i32.const 1
          call 3
          local.get 24
          i32.const 1
          i32.const 1
          call 3
          local.get 24
          local.get 22
          local.get 22
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            local.get 22
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=1 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=1 align=2
              local.get 22
              call 6
            end
          end
          local.get 24
          local.get 23
          local.get 23
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            local.get 23
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=5 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=5 align=2
              local.get 23
              call 6
            end
          end
          local.get 24
          call 5
          local.get 5
          local.set 25
          local.get 25
          local.get 25
          local.set 5
          call_indirect (type 1)
          local.get 5
          drop
          local.get 3
          local.set 26
          local.get 26
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 26
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 26
              call 4
            else
              local.get 26
              call 6
            end
          end
          local.get 1
          local.set 27
          local.get 27
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 27
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 27
              call 4
            else
              local.get 27
              call 6
            end
          end
        end
        local.get 0
        local.set 28
        local.get 28
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 28
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 28
            call 4
          else
            local.get 28
            call 6
          end
        end)
      (func (;9;) (type 4)
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
      (export "_start" (func 8))
      (export "__rw_table_func_7" (func 7))
      (export "__rw_table_func_8" (func 8))
      (start 9))

    -------------------------------
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
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        local.get 0
        local.set 5
        local.get 5
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
          else
            local.get 5
            i32.load 1 offset=1 align=2
            call 5
            local.set 5
          end
        end
        local.get 5
        local.set 0
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
            i32.load offset=3 align=2
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
            local.set 6
            local.get 6
            i32.load 1 offset=1 align=2
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
        local.set 2
        local.get 0
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
        local.set 0
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
            i32.load offset=7 align=2
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
            local.set 11
            local.get 11
            i32.load 1 offset=5 align=2
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
        local.set 4
        local.get 4
        local.set 15
        local.get 15
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
          else
            local.get 15
            i32.load 1 offset=1 align=2
            call 5
            local.set 15
          end
        end
        local.get 15
        local.set 4
        local.get 4
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
        local.get 0
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
        end)
      (func (;8;) (type 1) (param i32) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 0
        call 2
        local.set 6
        local.get 6
        call 5
        i32.const 0
        global.get 1
        i32.add
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
        i32.const 0
        call 3
        local.get 9
        local.get 7
        local.get 7
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 7
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 7
            call 6
          end
        end
        local.get 9
        local.get 8
        i32.store 1 offset=5 align=2
        local.get 9
        call 5
        block (param i32) (result i32)  ;; label = @1
          local.set 1
          local.get 1
          local.set 10
          local.get 10
          local.get 10
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 10
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
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
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 11
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 11
              i32.load offset=3 align=2
              local.tee 12
              local.get 12
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 12
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  i32.load 1 offset=1 align=2
                  call 5
                end
              end
            else
              local.get 11
              i32.load 1 offset=1 align=2
              local.set 11
              local.get 11
              i32.load 1 offset=1 align=2
              local.tee 13
              local.get 13
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 13
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  call 5
                end
              end
            end
          end
          local.set 2
          local.set 14
          local.get 14
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 14
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 14
              call 4
            else
              local.get 14
              call 6
            end
          end
          local.get 2
          local.set 3
          local.get 1
          local.set 15
          local.get 15
          local.get 15
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 15
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 15
              i32.load 1 offset=1 align=2
              call 5
              local.set 15
            end
          end
          local.get 15
          local.set 1
          local.tee 16
          local.get 16
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 16
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 16
              i32.load offset=7 align=2
              local.tee 17
            else
              local.get 16
              i32.load 1 offset=1 align=2
              local.set 16
              local.get 16
              i32.load 1 offset=5 align=2
              local.tee 18
            end
          end
          local.set 4
          local.set 19
          local.get 19
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 19
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 19
              call 4
            else
              local.get 19
              call 6
            end
          end
          local.get 4
          local.set 5
          local.get 3
          local.set 20
          local.get 20
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
            else
              local.get 20
              i32.load 1 offset=1 align=2
              call 5
              local.set 20
            end
          end
          local.get 20
          local.set 3
          i32.const 5
          i32.const 1
          i32.shl
          local.set 22
          local.set 21
          i32.const 2
          call 2
          local.set 23
          local.get 23
          i32.const 0
          i32.const 1
          call 3
          local.get 23
          i32.const 1
          i32.const 1
          call 3
          local.get 23
          local.get 21
          local.get 21
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            local.get 21
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=1 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=1 align=2
              local.get 21
              call 6
            end
          end
          local.get 23
          local.get 22
          local.get 22
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            local.get 22
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=5 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=5 align=2
              local.get 22
              call 6
            end
          end
          local.get 23
          call 5
          local.get 5
          local.set 24
          local.get 24
          local.get 24
          local.set 5
          call_indirect (type 1)
          local.get 5
          drop
          local.get 3
          local.set 25
          local.get 25
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 25
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 25
              call 4
            else
              local.get 25
              call 6
            end
          end
          local.get 1
          local.set 26
          local.get 26
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 26
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 26
              call 4
            else
              local.get 26
              call 6
            end
          end
        end
        local.get 0
        local.set 27
        local.get 27
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 27
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 27
            call 4
          else
            local.get 27
            call 6
          end
        end)
      (func (;9;) (type 4)
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
      (export "_start" (func 8))
      (export "__rw_table_func_7" (func 7))
      (export "__rw_table_func_8" (func 8))
      (start 9))

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
            i32.load 1 offset=1 align=2
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 4
            i32.load 1 offset=1 align=2
            local.set 4
            local.get 4
            i32.load 1 offset=5 align=2
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
            i32.load 1 offset=1 align=2
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
        end
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
            i32.load 1 offset=1 align=2
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 4
            i32.load 1 offset=1 align=2
            local.set 4
            local.get 4
            i32.load 1 offset=5 align=2
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
            i32.load 1 offset=1 align=2
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
        end
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
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 0
        i32.const 1
        i32.shl
        local.set 4
        i32.const 1
        call 2
        local.set 5
        local.get 5
        i32.const 0
        i32.const 1
        call 3
        local.get 5
        local.get 4
        local.get 4
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 4
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 4
            call 6
          end
        end
        local.get 5
        call 5
        local.set 1
        local.get 1
        local.set 6
        local.get 6
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
          else
            local.get 6
            i32.load 1 offset=1 align=2
            call 5
            local.set 6
          end
        end
        local.get 6
        local.set 1
        i32.const 1
        i32.const 1
        i32.shl
        local.set 7
        local.tee 8
        local.get 8
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
          unreachable
        else
          local.get 8
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 8
            local.get 7
            i32.store offset=3 align=2
          else
            local.get 8
            i32.load 1 offset=1 align=2
            local.set 8
            local.get 8
            local.get 7
            local.get 7
            i32.const 1
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=1 align=2
            else
              local.get 7
              i32.const 2
              i32.and
              i32.eqz
              if (param i32 i32)  ;; label = @4
                i32.store 1 offset=1 align=2
              else
                i32.load 1 offset=1 align=2
                i32.store 1 offset=1 align=2
                local.get 7
                call 6
              end
            end
          end
        end
        local.get 8
        i32.const 0
        i32.const 1
        call 3
        local.set 2
        local.get 1
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
        local.set 1
        local.tee 10
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
            local.get 11
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 11
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
            local.get 10
            i32.load 1 offset=1 align=2
            local.set 10
            local.get 10
            i32.load 1 offset=1 align=2
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
                call 5
              end
            end
          end
        end
        local.set 3
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
        local.get 3
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
        local.get 1
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
        local.get 0
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
            i32.load 1 offset=1 align=2
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 4
            i32.load 1 offset=1 align=2
            local.set 4
            local.get 4
            i32.load 1 offset=5 align=2
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
            i32.load 1 offset=1 align=2
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
        end
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
      (func (;8;) (type 1) (param i32) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 0
        call 2
        local.set 6
        local.get 6
        call 5
        i32.const 0
        global.get 1
        i32.add
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
        i32.const 0
        call 3
        local.get 9
        local.get 7
        local.get 7
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 7
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 7
            call 6
          end
        end
        local.get 9
        local.get 8
        i32.store 1 offset=5 align=2
        local.get 9
        call 5
        block (param i32) (result i32)  ;; label = @1
          local.set 1
          local.get 1
          local.set 10
          local.get 10
          local.get 10
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 10
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
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
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 11
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 11
              i32.load offset=3 align=2
              local.tee 12
              local.get 12
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 12
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  i32.load 1 offset=1 align=2
                  call 5
                end
              end
            else
              local.get 11
              i32.load 1 offset=1 align=2
              local.set 11
              local.get 11
              i32.load 1 offset=1 align=2
              local.tee 13
              local.get 13
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 13
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  call 5
                end
              end
            end
          end
          local.set 2
          local.set 14
          local.get 14
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 14
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 14
              call 4
            else
              local.get 14
              call 6
            end
          end
          local.get 2
          local.set 3
          local.get 1
          local.set 15
          local.get 15
          local.get 15
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 15
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 15
              i32.load 1 offset=1 align=2
              call 5
              local.set 15
            end
          end
          local.get 15
          local.set 1
          local.tee 16
          local.get 16
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 16
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 16
              i32.load offset=7 align=2
              local.tee 17
            else
              local.get 16
              i32.load 1 offset=1 align=2
              local.set 16
              local.get 16
              i32.load 1 offset=5 align=2
              local.tee 18
            end
          end
          local.set 4
          local.set 19
          local.get 19
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 19
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 19
              call 4
            else
              local.get 19
              call 6
            end
          end
          local.get 4
          local.set 5
          local.get 3
          local.set 20
          local.get 20
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
            else
              local.get 20
              i32.load 1 offset=1 align=2
              call 5
              local.set 20
            end
          end
          local.get 20
          local.set 3
          i32.const 42
          i32.const 1
          i32.shl
          local.set 22
          local.set 21
          i32.const 2
          call 2
          local.set 23
          local.get 23
          i32.const 0
          i32.const 1
          call 3
          local.get 23
          i32.const 1
          i32.const 1
          call 3
          local.get 23
          local.get 21
          local.get 21
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            local.get 21
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=1 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=1 align=2
              local.get 21
              call 6
            end
          end
          local.get 23
          local.get 22
          local.get 22
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            local.get 22
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=5 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=5 align=2
              local.get 22
              call 6
            end
          end
          local.get 23
          call 5
          local.get 5
          local.set 24
          local.get 24
          local.get 24
          local.set 5
          call_indirect (type 1)
          local.get 5
          drop
          local.get 3
          local.set 25
          local.get 25
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 25
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 25
              call 4
            else
              local.get 25
              call 6
            end
          end
          local.get 1
          local.set 26
          local.get 26
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 26
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 26
              call 4
            else
              local.get 26
              call 6
            end
          end
        end
        local.get 0
        local.set 27
        local.get 27
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 27
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 27
            call 4
          else
            local.get 27
            call 6
          end
        end)
      (func (;9;) (type 4)
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
      (export "id" (func 7))
      (export "_start" (func 8))
      (export "__rw_table_func_7" (func 7))
      (export "__rw_table_func_8" (func 8))
      (start 9))

    -----------opt_case-----------
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
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 42
        i32.const 1
        i32.shl
        local.set 5
        i32.const 2
        call 2
        local.set 6
        local.get 6
        i32.const 1
        i32.const 1
        call 3
        i32.const 1
        local.set 7
        local.get 6
        local.get 7
        i32.store 1 offset=1 align=2
        local.get 6
        local.get 5
        local.get 5
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=5 align=2
        else
          local.get 5
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=5 align=2
            local.get 5
            call 6
          end
        end
        local.get 6
        call 5
        local.set 1
        local.get 1
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
            i32.load 1 offset=1 align=2
            call 5
            local.set 8
          end
        end
        local.get 8
        local.set 1
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
            local.set 11
            i32.const 0
            block (param i32) (result i32)  ;; label = @3
              local.get 11
              i32.const 0
              i32.ne
              br_if 0 (;@3;)
              drop
              local.get 9
              i32.load offset=7 align=2
              local.tee 12
              local.get 12
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 12
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  i32.load 1 offset=1 align=2
                  call 5
                end
              end
              local.set 2
              i32.const 0
              i32.const 1
              i32.shl
              local.get 2
              local.set 13
              local.get 13
              i32.const 1
              i32.and
              i32.eqz
              if  ;; label = @4
              else
                local.get 13
                i32.const 2
                i32.and
                i32.eqz
                if  ;; label = @5
                  local.get 13
                  call 4
                else
                  local.get 13
                  call 6
                end
              end
            end
            block (param i32) (result i32)  ;; label = @3
              local.get 11
              i32.const 1
              i32.ne
              br_if 0 (;@3;)
              drop
              local.get 9
              i32.load offset=7 align=2
              local.tee 14
              local.get 14
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 14
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  i32.load 1 offset=1 align=2
                  call 5
                end
              end
              local.set 3
              local.get 3
              local.set 15
              local.get 15
              local.get 15
              i32.const 1
              i32.and
              i32.eqz
              if  ;; label = @4
              else
                local.get 15
                i32.const 2
                i32.and
                i32.eqz
                if  ;; label = @5
                else
                  local.get 15
                  i32.load 1 offset=1 align=2
                  call 5
                  local.set 15
                end
              end
              local.get 15
              local.set 3
              local.get 3
              local.set 16
              local.get 16
              i32.const 1
              i32.and
              i32.eqz
              if  ;; label = @4
              else
                local.get 16
                i32.const 2
                i32.and
                i32.eqz
                if  ;; label = @5
                  local.get 16
                  call 4
                else
                  local.get 16
                  call 6
                end
              end
            end
          else
            local.get 9
            i32.load 1 offset=1 align=2
            local.set 9
            local.get 9
            i32.load 1 offset=1 align=2
            local.tee 17
            local.set 18
            i32.const 0
            block (param i32) (result i32)  ;; label = @3
              local.get 18
              i32.const 0
              i32.ne
              br_if 0 (;@3;)
              drop
              local.get 9
              i32.load 1 offset=5 align=2
              local.tee 19
              local.get 19
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 19
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  call 5
                end
              end
              local.set 2
              i32.const 0
              i32.const 1
              i32.shl
              local.get 2
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
            end
            block (param i32) (result i32)  ;; label = @3
              local.get 18
              i32.const 1
              i32.ne
              br_if 0 (;@3;)
              drop
              local.get 9
              i32.load 1 offset=5 align=2
              local.tee 21
              local.get 21
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 21
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  call 5
                end
              end
              local.set 3
              local.get 3
              local.set 22
              local.get 22
              local.get 22
              i32.const 1
              i32.and
              i32.eqz
              if  ;; label = @4
              else
                local.get 22
                i32.const 2
                i32.and
                i32.eqz
                if  ;; label = @5
                else
                  local.get 22
                  i32.load 1 offset=1 align=2
                  call 5
                  local.set 22
                end
              end
              local.get 22
              local.set 3
              local.get 3
              local.set 23
              local.get 23
              i32.const 1
              i32.and
              i32.eqz
              if  ;; label = @4
              else
                local.get 23
                i32.const 2
                i32.and
                i32.eqz
                if  ;; label = @5
                  local.get 23
                  call 4
                else
                  local.get 23
                  call 6
                end
              end
            end
          end
        end
        local.set 4
        local.set 24
        local.get 24
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 24
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 24
            call 4
          else
            local.get 24
            call 6
          end
        end
        local.get 4
        local.get 1
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
        local.get 0
        local.set 26
        local.get 26
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 26
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 26
            call 4
          else
            local.get 26
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

    -----------poly_len-----------
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
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        local.get 0
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
            i32.load 1 offset=1 align=2
            call 5
            local.set 12
          end
        end
        local.get 12
        local.set 0
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 13
            i32.load 1 offset=1 align=2
            local.set 13
            local.get 13
            i32.load 1 offset=5 align=2
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
        local.set 1
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
        local.get 1
        local.set 2
        local.get 2
        local.set 17
        local.get 17
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
          else
            local.get 17
            i32.load 1 offset=1 align=2
            call 5
            local.set 17
          end
        end
        local.get 17
        local.set 2
        nop
        local.tee 18
        local.get 18
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 18
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 18
            i32.load offset=3 align=2
            local.tee 19
            local.set 20
            i32.const 0
            block (param i32) (result i32)  ;; label = @3
              local.get 20
              i32.const 0
              i32.ne
              br_if 0 (;@3;)
              drop
              local.get 18
              i32.load offset=7 align=2
              local.tee 21
              local.get 21
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 21
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  i32.load 1 offset=1 align=2
                  call 5
                end
              end
              local.set 3
              i32.const 0
              i32.const 1
              i32.shl
              local.get 3
              local.set 22
              local.get 22
              i32.const 1
              i32.and
              i32.eqz
              if  ;; label = @4
              else
                local.get 22
                i32.const 2
                i32.and
                i32.eqz
                if  ;; label = @5
                  local.get 22
                  call 4
                else
                  local.get 22
                  call 6
                end
              end
            end
            block (param i32) (result i32)  ;; label = @3
              local.get 20
              i32.const 1
              i32.ne
              br_if 0 (;@3;)
              drop
              local.get 18
              i32.load offset=7 align=2
              local.tee 23
              local.get 23
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 23
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  i32.load 1 offset=1 align=2
                  call 5
                end
              end
              local.set 4
              i32.const 1
              i32.const 1
              i32.shl
              i32.const 1
              i32.shr_u
              i32.const 0
              call 2
              local.set 24
              local.get 24
              call 5
              i32.const 0
              global.get 1
              i32.add
              local.set 26
              local.set 25
              i32.const 2
              call 2
              local.set 27
              local.get 27
              i32.const 0
              i32.const 1
              call 3
              local.get 27
              i32.const 1
              i32.const 0
              call 3
              local.get 27
              local.get 25
              local.get 25
              i32.const 1
              i32.and
              i32.eqz
              if (param i32 i32)  ;; label = @4
                i32.store 1 offset=1 align=2
              else
                local.get 25
                i32.const 2
                i32.and
                i32.eqz
                if (param i32 i32)  ;; label = @5
                  i32.store 1 offset=1 align=2
                else
                  i32.load 1 offset=1 align=2
                  i32.store 1 offset=1 align=2
                  local.get 25
                  call 6
                end
              end
              local.get 27
              local.get 26
              i32.store 1 offset=5 align=2
              local.get 27
              call 5
              block (param i32) (result i32)  ;; label = @4
                local.set 5
                local.get 5
                local.set 28
                local.get 28
                local.get 28
                i32.const 1
                i32.and
                i32.eqz
                if  ;; label = @5
                else
                  local.get 28
                  i32.const 2
                  i32.and
                  i32.eqz
                  if  ;; label = @6
                  else
                    local.get 28
                    i32.load 1 offset=1 align=2
                    call 5
                    local.set 28
                  end
                end
                local.get 28
                local.set 5
                local.tee 29
                local.get 29
                i32.const 1
                i32.and
                i32.eqz
                if (result i32)  ;; label = @5
                  unreachable
                else
                  local.get 29
                  i32.const 2
                  i32.and
                  i32.eqz
                  if (result i32)  ;; label = @6
                    local.get 29
                    i32.load offset=3 align=2
                    local.tee 30
                    local.get 30
                    i32.const 1
                    i32.and
                    i32.eqz
                    if (param i32) (result i32)  ;; label = @7
                    else
                      local.get 30
                      i32.const 2
                      i32.and
                      i32.eqz
                      if (param i32) (result i32)  ;; label = @8
                      else
                        i32.load 1 offset=1 align=2
                        call 5
                      end
                    end
                  else
                    local.get 29
                    i32.load 1 offset=1 align=2
                    local.set 29
                    local.get 29
                    i32.load 1 offset=1 align=2
                    local.tee 31
                    local.get 31
                    i32.const 1
                    i32.and
                    i32.eqz
                    if (param i32) (result i32)  ;; label = @7
                    else
                      local.get 31
                      i32.const 2
                      i32.and
                      i32.eqz
                      if (param i32) (result i32)  ;; label = @8
                      else
                        call 5
                      end
                    end
                  end
                end
                local.set 6
                local.set 32
                local.get 32
                i32.const 1
                i32.and
                i32.eqz
                if  ;; label = @5
                else
                  local.get 32
                  i32.const 2
                  i32.and
                  i32.eqz
                  if  ;; label = @6
                    local.get 32
                    call 4
                  else
                    local.get 32
                    call 6
                  end
                end
                local.get 6
                local.set 7
                local.get 5
                local.set 33
                local.get 33
                local.get 33
                i32.const 1
                i32.and
                i32.eqz
                if  ;; label = @5
                else
                  local.get 33
                  i32.const 2
                  i32.and
                  i32.eqz
                  if  ;; label = @6
                  else
                    local.get 33
                    i32.load 1 offset=1 align=2
                    call 5
                    local.set 33
                  end
                end
                local.get 33
                local.set 5
                local.tee 34
                local.get 34
                i32.const 1
                i32.and
                i32.eqz
                if (result i32)  ;; label = @5
                  unreachable
                else
                  local.get 34
                  i32.const 2
                  i32.and
                  i32.eqz
                  if (result i32)  ;; label = @6
                    local.get 34
                    i32.load offset=7 align=2
                    local.tee 35
                  else
                    local.get 34
                    i32.load 1 offset=1 align=2
                    local.set 34
                    local.get 34
                    i32.load 1 offset=5 align=2
                    local.tee 36
                  end
                end
                local.set 8
                local.set 37
                local.get 37
                i32.const 1
                i32.and
                i32.eqz
                if  ;; label = @5
                else
                  local.get 37
                  i32.const 2
                  i32.and
                  i32.eqz
                  if  ;; label = @6
                    local.get 37
                    call 4
                  else
                    local.get 37
                    call 6
                  end
                end
                local.get 8
                local.set 9
                local.get 7
                local.set 38
                local.get 38
                local.get 38
                i32.const 1
                i32.and
                i32.eqz
                if  ;; label = @5
                else
                  local.get 38
                  i32.const 2
                  i32.and
                  i32.eqz
                  if  ;; label = @6
                  else
                    local.get 38
                    i32.load 1 offset=1 align=2
                    call 5
                    local.set 38
                  end
                end
                local.get 38
                local.set 7
                local.get 4
                local.set 39
                local.get 39
                local.get 39
                i32.const 1
                i32.and
                i32.eqz
                if  ;; label = @5
                else
                  local.get 39
                  i32.const 2
                  i32.and
                  i32.eqz
                  if  ;; label = @6
                  else
                    local.get 39
                    i32.load 1 offset=1 align=2
                    call 5
                    local.set 39
                  end
                end
                local.get 39
                local.set 4
                local.tee 40
                local.get 40
                i32.const 1
                i32.and
                i32.eqz
                if (result i32)  ;; label = @5
                  unreachable
                else
                  local.get 40
                  i32.const 2
                  i32.and
                  i32.eqz
                  if (result i32)  ;; label = @6
                    local.get 40
                    i32.load offset=7 align=2
                    local.tee 41
                    local.get 41
                    i32.const 1
                    i32.and
                    i32.eqz
                    if (param i32) (result i32)  ;; label = @7
                    else
                      local.get 41
                      i32.const 2
                      i32.and
                      i32.eqz
                      if (param i32) (result i32)  ;; label = @8
                      else
                        i32.load 1 offset=1 align=2
                        call 5
                      end
                    end
                  else
                    local.get 40
                    i32.load 1 offset=1 align=2
                    local.set 40
                    local.get 40
                    i32.load 1 offset=5 align=2
                    local.tee 42
                    local.get 42
                    i32.const 1
                    i32.and
                    i32.eqz
                    if (param i32) (result i32)  ;; label = @7
                    else
                      local.get 42
                      i32.const 2
                      i32.and
                      i32.eqz
                      if (param i32) (result i32)  ;; label = @8
                      else
                        call 5
                      end
                    end
                  end
                end
                local.set 10
                local.set 43
                local.get 43
                i32.const 1
                i32.and
                i32.eqz
                if  ;; label = @5
                else
                  local.get 43
                  i32.const 2
                  i32.and
                  i32.eqz
                  if  ;; label = @6
                    local.get 43
                    call 4
                  else
                    local.get 43
                    call 6
                  end
                end
                local.get 10
                local.set 45
                local.set 44
                i32.const 2
                call 2
                local.set 46
                local.get 46
                i32.const 0
                i32.const 1
                call 3
                local.get 46
                i32.const 1
                i32.const 1
                call 3
                local.get 46
                local.get 44
                local.get 44
                i32.const 1
                i32.and
                i32.eqz
                if (param i32 i32)  ;; label = @5
                  i32.store 1 offset=1 align=2
                else
                  local.get 44
                  i32.const 2
                  i32.and
                  i32.eqz
                  if (param i32 i32)  ;; label = @6
                    i32.store 1 offset=1 align=2
                  else
                    i32.load 1 offset=1 align=2
                    i32.store 1 offset=1 align=2
                    local.get 44
                    call 6
                  end
                end
                local.get 46
                local.get 45
                local.get 45
                i32.const 1
                i32.and
                i32.eqz
                if (param i32 i32)  ;; label = @5
                  i32.store 1 offset=5 align=2
                else
                  local.get 45
                  i32.const 2
                  i32.and
                  i32.eqz
                  if (param i32 i32)  ;; label = @6
                    i32.store 1 offset=5 align=2
                  else
                    i32.load 1 offset=1 align=2
                    i32.store 1 offset=5 align=2
                    local.get 45
                    call 6
                  end
                end
                local.get 46
                call 5
                local.get 9
                local.set 47
                local.get 47
                local.get 47
                local.set 9
                call_indirect (type 1)
                local.get 9
                drop
                local.get 7
                local.set 48
                local.get 48
                i32.const 1
                i32.and
                i32.eqz
                if  ;; label = @5
                else
                  local.get 48
                  i32.const 2
                  i32.and
                  i32.eqz
                  if  ;; label = @6
                    local.get 48
                    call 4
                  else
                    local.get 48
                    call 6
                  end
                end
                local.get 5
                local.set 49
                local.get 49
                i32.const 1
                i32.and
                i32.eqz
                if  ;; label = @5
                else
                  local.get 49
                  i32.const 2
                  i32.and
                  i32.eqz
                  if  ;; label = @6
                    local.get 49
                    call 4
                  else
                    local.get 49
                    call 6
                  end
                end
              end
              i32.const 1
              i32.shr_u
              i32.add
              i32.const 1
              i32.shl
              local.get 4
              local.set 50
              local.get 50
              i32.const 1
              i32.and
              i32.eqz
              if  ;; label = @4
              else
                local.get 50
                i32.const 2
                i32.and
                i32.eqz
                if  ;; label = @5
                  local.get 50
                  call 4
                else
                  local.get 50
                  call 6
                end
              end
            end
          else
            local.get 18
            i32.load 1 offset=1 align=2
            local.set 18
            local.get 18
            i32.load 1 offset=1 align=2
            local.tee 51
            local.set 52
            i32.const 0
            block (param i32) (result i32)  ;; label = @3
              local.get 52
              i32.const 0
              i32.ne
              br_if 0 (;@3;)
              drop
              local.get 18
              i32.load 1 offset=5 align=2
              local.tee 53
              local.get 53
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 53
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  call 5
                end
              end
              local.set 3
              i32.const 0
              i32.const 1
              i32.shl
              local.get 3
              local.set 54
              local.get 54
              i32.const 1
              i32.and
              i32.eqz
              if  ;; label = @4
              else
                local.get 54
                i32.const 2
                i32.and
                i32.eqz
                if  ;; label = @5
                  local.get 54
                  call 4
                else
                  local.get 54
                  call 6
                end
              end
            end
            block (param i32) (result i32)  ;; label = @3
              local.get 52
              i32.const 1
              i32.ne
              br_if 0 (;@3;)
              drop
              local.get 18
              i32.load 1 offset=5 align=2
              local.tee 55
              local.get 55
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 55
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  call 5
                end
              end
              local.set 4
              i32.const 1
              i32.const 1
              i32.shl
              i32.const 1
              i32.shr_u
              i32.const 0
              call 2
              local.set 56
              local.get 56
              call 5
              i32.const 0
              global.get 1
              i32.add
              local.set 58
              local.set 57
              i32.const 2
              call 2
              local.set 59
              local.get 59
              i32.const 0
              i32.const 1
              call 3
              local.get 59
              i32.const 1
              i32.const 0
              call 3
              local.get 59
              local.get 57
              local.get 57
              i32.const 1
              i32.and
              i32.eqz
              if (param i32 i32)  ;; label = @4
                i32.store 1 offset=1 align=2
              else
                local.get 57
                i32.const 2
                i32.and
                i32.eqz
                if (param i32 i32)  ;; label = @5
                  i32.store 1 offset=1 align=2
                else
                  i32.load 1 offset=1 align=2
                  i32.store 1 offset=1 align=2
                  local.get 57
                  call 6
                end
              end
              local.get 59
              local.get 58
              i32.store 1 offset=5 align=2
              local.get 59
              call 5
              block (param i32) (result i32)  ;; label = @4
                local.set 5
                local.get 5
                local.set 60
                local.get 60
                local.get 60
                i32.const 1
                i32.and
                i32.eqz
                if  ;; label = @5
                else
                  local.get 60
                  i32.const 2
                  i32.and
                  i32.eqz
                  if  ;; label = @6
                  else
                    local.get 60
                    i32.load 1 offset=1 align=2
                    call 5
                    local.set 60
                  end
                end
                local.get 60
                local.set 5
                local.tee 61
                local.get 61
                i32.const 1
                i32.and
                i32.eqz
                if (result i32)  ;; label = @5
                  unreachable
                else
                  local.get 61
                  i32.const 2
                  i32.and
                  i32.eqz
                  if (result i32)  ;; label = @6
                    local.get 61
                    i32.load offset=3 align=2
                    local.tee 62
                    local.get 62
                    i32.const 1
                    i32.and
                    i32.eqz
                    if (param i32) (result i32)  ;; label = @7
                    else
                      local.get 62
                      i32.const 2
                      i32.and
                      i32.eqz
                      if (param i32) (result i32)  ;; label = @8
                      else
                        i32.load 1 offset=1 align=2
                        call 5
                      end
                    end
                  else
                    local.get 61
                    i32.load 1 offset=1 align=2
                    local.set 61
                    local.get 61
                    i32.load 1 offset=1 align=2
                    local.tee 63
                    local.get 63
                    i32.const 1
                    i32.and
                    i32.eqz
                    if (param i32) (result i32)  ;; label = @7
                    else
                      local.get 63
                      i32.const 2
                      i32.and
                      i32.eqz
                      if (param i32) (result i32)  ;; label = @8
                      else
                        call 5
                      end
                    end
                  end
                end
                local.set 6
                local.set 64
                local.get 64
                i32.const 1
                i32.and
                i32.eqz
                if  ;; label = @5
                else
                  local.get 64
                  i32.const 2
                  i32.and
                  i32.eqz
                  if  ;; label = @6
                    local.get 64
                    call 4
                  else
                    local.get 64
                    call 6
                  end
                end
                local.get 6
                local.set 7
                local.get 5
                local.set 65
                local.get 65
                local.get 65
                i32.const 1
                i32.and
                i32.eqz
                if  ;; label = @5
                else
                  local.get 65
                  i32.const 2
                  i32.and
                  i32.eqz
                  if  ;; label = @6
                  else
                    local.get 65
                    i32.load 1 offset=1 align=2
                    call 5
                    local.set 65
                  end
                end
                local.get 65
                local.set 5
                local.tee 66
                local.get 66
                i32.const 1
                i32.and
                i32.eqz
                if (result i32)  ;; label = @5
                  unreachable
                else
                  local.get 66
                  i32.const 2
                  i32.and
                  i32.eqz
                  if (result i32)  ;; label = @6
                    local.get 66
                    i32.load offset=7 align=2
                    local.tee 67
                  else
                    local.get 66
                    i32.load 1 offset=1 align=2
                    local.set 66
                    local.get 66
                    i32.load 1 offset=5 align=2
                    local.tee 68
                  end
                end
                local.set 8
                local.set 69
                local.get 69
                i32.const 1
                i32.and
                i32.eqz
                if  ;; label = @5
                else
                  local.get 69
                  i32.const 2
                  i32.and
                  i32.eqz
                  if  ;; label = @6
                    local.get 69
                    call 4
                  else
                    local.get 69
                    call 6
                  end
                end
                local.get 8
                local.set 9
                local.get 7
                local.set 70
                local.get 70
                local.get 70
                i32.const 1
                i32.and
                i32.eqz
                if  ;; label = @5
                else
                  local.get 70
                  i32.const 2
                  i32.and
                  i32.eqz
                  if  ;; label = @6
                  else
                    local.get 70
                    i32.load 1 offset=1 align=2
                    call 5
                    local.set 70
                  end
                end
                local.get 70
                local.set 7
                local.get 4
                local.set 71
                local.get 71
                local.get 71
                i32.const 1
                i32.and
                i32.eqz
                if  ;; label = @5
                else
                  local.get 71
                  i32.const 2
                  i32.and
                  i32.eqz
                  if  ;; label = @6
                  else
                    local.get 71
                    i32.load 1 offset=1 align=2
                    call 5
                    local.set 71
                  end
                end
                local.get 71
                local.set 4
                local.tee 72
                local.get 72
                i32.const 1
                i32.and
                i32.eqz
                if (result i32)  ;; label = @5
                  unreachable
                else
                  local.get 72
                  i32.const 2
                  i32.and
                  i32.eqz
                  if (result i32)  ;; label = @6
                    local.get 72
                    i32.load offset=7 align=2
                    local.tee 73
                    local.get 73
                    i32.const 1
                    i32.and
                    i32.eqz
                    if (param i32) (result i32)  ;; label = @7
                    else
                      local.get 73
                      i32.const 2
                      i32.and
                      i32.eqz
                      if (param i32) (result i32)  ;; label = @8
                      else
                        i32.load 1 offset=1 align=2
                        call 5
                      end
                    end
                  else
                    local.get 72
                    i32.load 1 offset=1 align=2
                    local.set 72
                    local.get 72
                    i32.load 1 offset=5 align=2
                    local.tee 74
                    local.get 74
                    i32.const 1
                    i32.and
                    i32.eqz
                    if (param i32) (result i32)  ;; label = @7
                    else
                      local.get 74
                      i32.const 2
                      i32.and
                      i32.eqz
                      if (param i32) (result i32)  ;; label = @8
                      else
                        call 5
                      end
                    end
                  end
                end
                local.set 10
                local.set 75
                local.get 75
                i32.const 1
                i32.and
                i32.eqz
                if  ;; label = @5
                else
                  local.get 75
                  i32.const 2
                  i32.and
                  i32.eqz
                  if  ;; label = @6
                    local.get 75
                    call 4
                  else
                    local.get 75
                    call 6
                  end
                end
                local.get 10
                local.set 77
                local.set 76
                i32.const 2
                call 2
                local.set 78
                local.get 78
                i32.const 0
                i32.const 1
                call 3
                local.get 78
                i32.const 1
                i32.const 1
                call 3
                local.get 78
                local.get 76
                local.get 76
                i32.const 1
                i32.and
                i32.eqz
                if (param i32 i32)  ;; label = @5
                  i32.store 1 offset=1 align=2
                else
                  local.get 76
                  i32.const 2
                  i32.and
                  i32.eqz
                  if (param i32 i32)  ;; label = @6
                    i32.store 1 offset=1 align=2
                  else
                    i32.load 1 offset=1 align=2
                    i32.store 1 offset=1 align=2
                    local.get 76
                    call 6
                  end
                end
                local.get 78
                local.get 77
                local.get 77
                i32.const 1
                i32.and
                i32.eqz
                if (param i32 i32)  ;; label = @5
                  i32.store 1 offset=5 align=2
                else
                  local.get 77
                  i32.const 2
                  i32.and
                  i32.eqz
                  if (param i32 i32)  ;; label = @6
                    i32.store 1 offset=5 align=2
                  else
                    i32.load 1 offset=1 align=2
                    i32.store 1 offset=5 align=2
                    local.get 77
                    call 6
                  end
                end
                local.get 78
                call 5
                local.get 9
                local.set 79
                local.get 79
                local.get 79
                local.set 9
                call_indirect (type 1)
                local.get 9
                drop
                local.get 7
                local.set 80
                local.get 80
                i32.const 1
                i32.and
                i32.eqz
                if  ;; label = @5
                else
                  local.get 80
                  i32.const 2
                  i32.and
                  i32.eqz
                  if  ;; label = @6
                    local.get 80
                    call 4
                  else
                    local.get 80
                    call 6
                  end
                end
                local.get 5
                local.set 81
                local.get 81
                i32.const 1
                i32.and
                i32.eqz
                if  ;; label = @5
                else
                  local.get 81
                  i32.const 2
                  i32.and
                  i32.eqz
                  if  ;; label = @6
                    local.get 81
                    call 4
                  else
                    local.get 81
                    call 6
                  end
                end
              end
              i32.const 1
              i32.shr_u
              i32.add
              i32.const 1
              i32.shl
              local.get 4
              local.set 82
              local.get 82
              i32.const 1
              i32.and
              i32.eqz
              if  ;; label = @4
              else
                local.get 82
                i32.const 2
                i32.and
                i32.eqz
                if  ;; label = @5
                  local.get 82
                  call 4
                else
                  local.get 82
                  call 6
                end
              end
            end
          end
        end
        local.set 11
        local.set 83
        local.get 83
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 83
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 83
            call 4
          else
            local.get 83
            call 6
          end
        end
        local.get 11
        local.get 2
        local.set 84
        local.get 84
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 84
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 84
            call 4
          else
            local.get 84
            call 6
          end
        end
        local.get 0
        local.set 85
        local.get 85
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 85
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 85
            call 4
          else
            local.get 85
            call 6
          end
        end)
      (func (;8;) (type 1) (param i32) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 0
        call 2
        local.set 6
        local.get 6
        call 5
        i32.const 0
        global.get 1
        i32.add
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
        i32.const 0
        call 3
        local.get 9
        local.get 7
        local.get 7
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 7
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 7
            call 6
          end
        end
        local.get 9
        local.get 8
        i32.store 1 offset=5 align=2
        local.get 9
        call 5
        block (param i32) (result i32)  ;; label = @1
          local.set 1
          local.get 1
          local.set 10
          local.get 10
          local.get 10
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 10
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
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
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 11
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 11
              i32.load offset=3 align=2
              local.tee 12
              local.get 12
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 12
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  i32.load 1 offset=1 align=2
                  call 5
                end
              end
            else
              local.get 11
              i32.load 1 offset=1 align=2
              local.set 11
              local.get 11
              i32.load 1 offset=1 align=2
              local.tee 13
              local.get 13
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 13
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  call 5
                end
              end
            end
          end
          local.set 2
          local.set 14
          local.get 14
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 14
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 14
              call 4
            else
              local.get 14
              call 6
            end
          end
          local.get 2
          local.set 3
          local.get 1
          local.set 15
          local.get 15
          local.get 15
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 15
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 15
              i32.load 1 offset=1 align=2
              call 5
              local.set 15
            end
          end
          local.get 15
          local.set 1
          local.tee 16
          local.get 16
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 16
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 16
              i32.load offset=7 align=2
              local.tee 17
            else
              local.get 16
              i32.load 1 offset=1 align=2
              local.set 16
              local.get 16
              i32.load 1 offset=5 align=2
              local.tee 18
            end
          end
          local.set 4
          local.set 19
          local.get 19
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 19
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 19
              call 4
            else
              local.get 19
              call 6
            end
          end
          local.get 4
          local.set 5
          local.get 3
          local.set 20
          local.get 20
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
            else
              local.get 20
              i32.load 1 offset=1 align=2
              call 5
              local.set 20
            end
          end
          local.get 20
          local.set 3
          i32.const 1
          i32.const 1
          i32.shl
          i32.const 0
          call 2
          local.set 21
          local.get 21
          call 5
          local.set 22
          i32.const 2
          call 2
          local.set 23
          local.get 23
          i32.const 1
          i32.const 1
          call 3
          i32.const 0
          local.set 24
          local.get 23
          local.get 24
          i32.store 1 offset=1 align=2
          local.get 23
          local.get 22
          local.get 22
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            local.get 22
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=5 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=5 align=2
              local.get 22
              call 6
            end
          end
          local.get 23
          call 5
          nop
          local.set 26
          local.set 25
          i32.const 2
          call 2
          local.set 27
          local.get 27
          i32.const 0
          i32.const 1
          call 3
          local.get 27
          i32.const 1
          i32.const 1
          call 3
          local.get 27
          local.get 25
          local.get 25
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            local.get 25
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=1 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=1 align=2
              local.get 25
              call 6
            end
          end
          local.get 27
          local.get 26
          local.get 26
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            local.get 26
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=5 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=5 align=2
              local.get 26
              call 6
            end
          end
          local.get 27
          call 5
          local.set 28
          i32.const 2
          call 2
          local.set 29
          local.get 29
          i32.const 1
          i32.const 1
          call 3
          i32.const 1
          local.set 30
          local.get 29
          local.get 30
          i32.store 1 offset=1 align=2
          local.get 29
          local.get 28
          local.get 28
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            local.get 28
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=5 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=5 align=2
              local.get 28
              call 6
            end
          end
          local.get 29
          call 5
          nop
          local.set 32
          local.set 31
          i32.const 2
          call 2
          local.set 33
          local.get 33
          i32.const 0
          i32.const 1
          call 3
          local.get 33
          i32.const 1
          i32.const 1
          call 3
          local.get 33
          local.get 31
          local.get 31
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            local.get 31
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=1 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=1 align=2
              local.get 31
              call 6
            end
          end
          local.get 33
          local.get 32
          local.get 32
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            local.get 32
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=5 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=5 align=2
              local.get 32
              call 6
            end
          end
          local.get 33
          call 5
          local.get 5
          local.set 34
          local.get 34
          local.get 34
          local.set 5
          call_indirect (type 1)
          local.get 5
          drop
          local.get 3
          local.set 35
          local.get 35
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 35
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 35
              call 4
            else
              local.get 35
              call 6
            end
          end
          local.get 1
          local.set 36
          local.get 36
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 36
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 36
              call 4
            else
              local.get 36
              call 6
            end
          end
        end
        local.get 0
        local.set 37
        local.get 37
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 37
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 37
            call 4
          else
            local.get 37
            call 6
          end
        end)
      (func (;9;) (type 4)
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
      (export "len" (func 7))
      (export "_start" (func 8))
      (export "__rw_table_func_7" (func 7))
      (export "__rw_table_func_8" (func 8))
      (start 9))

    -----------poly_id_apply-----------
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
            i32.load 1 offset=1 align=2
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 4
            i32.load 1 offset=1 align=2
            local.set 4
            local.get 4
            i32.load 1 offset=5 align=2
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
            i32.load 1 offset=1 align=2
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
        end
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
      (func (;8;) (type 1) (param i32) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        local.get 0
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
            i32.load 1 offset=1 align=2
            call 5
            local.set 8
          end
        end
        local.get 8
        local.set 0
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
            i32.load offset=7 align=2
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 9
            i32.load 1 offset=1 align=2
            local.set 9
            local.get 9
            i32.load 1 offset=5 align=2
            local.tee 11
            local.get 11
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 11
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
        local.set 12
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
            local.get 12
            call 4
          else
            local.get 12
            call 6
          end
        end
        local.get 1
        local.set 2
        i32.const 0
        call 2
        local.set 13
        local.get 13
        call 5
        i32.const 0
        global.get 1
        i32.add
        local.set 15
        local.set 14
        i32.const 2
        call 2
        local.set 16
        local.get 16
        i32.const 0
        i32.const 1
        call 3
        local.get 16
        i32.const 1
        i32.const 0
        call 3
        local.get 16
        local.get 14
        local.get 14
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 14
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 14
            call 6
          end
        end
        local.get 16
        local.get 15
        i32.store 1 offset=5 align=2
        local.get 16
        call 5
        block (param i32) (result i32)  ;; label = @1
          local.set 3
          local.get 3
          local.set 17
          local.get 17
          local.get 17
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 17
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 17
              i32.load 1 offset=1 align=2
              call 5
              local.set 17
            end
          end
          local.get 17
          local.set 3
          local.tee 18
          local.get 18
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 18
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 18
              i32.load offset=3 align=2
              local.tee 19
              local.get 19
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 19
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  i32.load 1 offset=1 align=2
                  call 5
                end
              end
            else
              local.get 18
              i32.load 1 offset=1 align=2
              local.set 18
              local.get 18
              i32.load 1 offset=1 align=2
              local.tee 20
              local.get 20
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 20
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  call 5
                end
              end
            end
          end
          local.set 4
          local.set 21
          local.get 21
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 21
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 21
              call 4
            else
              local.get 21
              call 6
            end
          end
          local.get 4
          local.set 5
          local.get 3
          local.set 22
          local.get 22
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
            else
              local.get 22
              i32.load 1 offset=1 align=2
              call 5
              local.set 22
            end
          end
          local.get 22
          local.set 3
          local.tee 23
          local.get 23
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 23
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 23
              i32.load offset=7 align=2
              local.tee 24
            else
              local.get 23
              i32.load 1 offset=1 align=2
              local.set 23
              local.get 23
              i32.load 1 offset=5 align=2
              local.tee 25
            end
          end
          local.set 6
          local.set 26
          local.get 26
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 26
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 26
              call 4
            else
              local.get 26
              call 6
            end
          end
          local.get 6
          local.set 7
          local.get 5
          local.set 27
          local.get 27
          local.get 27
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 27
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 27
              i32.load 1 offset=1 align=2
              call 5
              local.set 27
            end
          end
          local.get 27
          local.set 5
          local.get 2
          local.set 28
          local.get 28
          local.get 28
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 28
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 28
              i32.load 1 offset=1 align=2
              call 5
              local.set 28
            end
          end
          local.get 28
          local.set 2
          local.set 30
          local.set 29
          i32.const 2
          call 2
          local.set 31
          local.get 31
          i32.const 0
          i32.const 1
          call 3
          local.get 31
          i32.const 1
          i32.const 1
          call 3
          local.get 31
          local.get 29
          local.get 29
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            local.get 29
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=1 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=1 align=2
              local.get 29
              call 6
            end
          end
          local.get 31
          local.get 30
          local.get 30
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            local.get 30
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=5 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=5 align=2
              local.get 30
              call 6
            end
          end
          local.get 31
          call 5
          local.get 7
          local.set 32
          local.get 32
          local.get 32
          local.set 7
          call_indirect (type 1)
          local.get 7
          drop
          local.get 5
          local.set 33
          local.get 33
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 33
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 33
              call 4
            else
              local.get 33
              call 6
            end
          end
          local.get 3
          local.set 34
          local.get 34
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 34
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 34
              call 4
            else
              local.get 34
              call 6
            end
          end
        end
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
        end
        local.get 0
        local.set 36
        local.get 36
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 36
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 36
            call 4
          else
            local.get 36
            call 6
          end
        end)
      (func (;9;) (type 1) (param i32) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 0
        call 2
        local.set 6
        local.get 6
        call 5
        i32.const 1
        global.get 1
        i32.add
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
        i32.const 0
        call 3
        local.get 9
        local.get 7
        local.get 7
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 7
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 7
            call 6
          end
        end
        local.get 9
        local.get 8
        i32.store 1 offset=5 align=2
        local.get 9
        call 5
        block (param i32) (result i32)  ;; label = @1
          local.set 1
          local.get 1
          local.set 10
          local.get 10
          local.get 10
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 10
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
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
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 11
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 11
              i32.load offset=3 align=2
              local.tee 12
              local.get 12
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 12
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  i32.load 1 offset=1 align=2
                  call 5
                end
              end
            else
              local.get 11
              i32.load 1 offset=1 align=2
              local.set 11
              local.get 11
              i32.load 1 offset=1 align=2
              local.tee 13
              local.get 13
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 13
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  call 5
                end
              end
            end
          end
          local.set 2
          local.set 14
          local.get 14
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 14
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 14
              call 4
            else
              local.get 14
              call 6
            end
          end
          local.get 2
          local.set 3
          local.get 1
          local.set 15
          local.get 15
          local.get 15
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 15
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 15
              i32.load 1 offset=1 align=2
              call 5
              local.set 15
            end
          end
          local.get 15
          local.set 1
          local.tee 16
          local.get 16
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 16
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 16
              i32.load offset=7 align=2
              local.tee 17
            else
              local.get 16
              i32.load 1 offset=1 align=2
              local.set 16
              local.get 16
              i32.load 1 offset=5 align=2
              local.tee 18
            end
          end
          local.set 4
          local.set 19
          local.get 19
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 19
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 19
              call 4
            else
              local.get 19
              call 6
            end
          end
          local.get 4
          local.set 5
          local.get 3
          local.set 20
          local.get 20
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
            else
              local.get 20
              i32.load 1 offset=1 align=2
              call 5
              local.set 20
            end
          end
          local.get 20
          local.set 3
          i32.const 5
          i32.const 1
          i32.shl
          local.set 22
          local.set 21
          i32.const 2
          call 2
          local.set 23
          local.get 23
          i32.const 0
          i32.const 1
          call 3
          local.get 23
          i32.const 1
          i32.const 1
          call 3
          local.get 23
          local.get 21
          local.get 21
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            local.get 21
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=1 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=1 align=2
              local.get 21
              call 6
            end
          end
          local.get 23
          local.get 22
          local.get 22
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            local.get 22
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=5 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=5 align=2
              local.get 22
              call 6
            end
          end
          local.get 23
          call 5
          local.get 5
          local.set 24
          local.get 24
          local.get 24
          local.set 5
          call_indirect (type 1)
          local.get 5
          drop
          local.get 3
          local.set 25
          local.get 25
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 25
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 25
              call 4
            else
              local.get 25
              call 6
            end
          end
          local.get 1
          local.set 26
          local.get 26
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 26
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 26
              call 4
            else
              local.get 26
              call 6
            end
          end
        end
        local.get 0
        local.set 27
        local.get 27
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 27
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 27
            call 4
          else
            local.get 27
            call 6
          end
        end)
      (func (;10;) (type 4)
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
      (export "id" (func 7))
      (export "apply" (func 8))
      (export "_start" (func 9))
      (export "__rw_table_func_7" (func 7))
      (export "__rw_table_func_8" (func 8))
      (export "__rw_table_func_9" (func 9))
      (start 10))

    -----------mini_zip-----------
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
            i32.load 1 offset=1 align=2
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 8
            i32.load 1 offset=1 align=2
            local.set 8
            local.get 8
            i32.load 1 offset=5 align=2
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
            i32.load 1 offset=1 align=2
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
            i32.load offset=3 align=2
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 13
            i32.load 1 offset=1 align=2
            local.set 13
            local.get 13
            i32.load 1 offset=1 align=2
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 17
            i32.load 1 offset=1 align=2
            local.set 17
            local.get 17
            i32.load 1 offset=1 align=2
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
            i32.load 1 offset=1 align=2
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
            i32.load offset=7 align=2
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 22
            i32.load 1 offset=1 align=2
            local.set 22
            local.get 22
            i32.load 1 offset=5 align=2
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 26
            i32.load 1 offset=1 align=2
            local.set 26
            local.get 26
            i32.load 1 offset=1 align=2
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
        local.get 30
        local.get 30
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 30
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 30
            call 6
          end
        end
        local.get 32
        local.get 31
        local.get 31
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=5 align=2
        else
          local.get 31
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=5 align=2
            local.get 31
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
          i32.store 1 offset=1 align=2
        else
          local.get 33
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
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
        end
        local.get 0
        local.set 36
        local.get 36
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 36
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 36
            call 4
          else
            local.get 36
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
      (export "__rw_table_func_7" (func 7))
      (start 8))

    -----------closure_simpl-----------
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
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
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
            i32.load 1 offset=1 align=2
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
            i32.load offset=3 align=2
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 8
            i32.load 1 offset=1 align=2
            local.set 8
            local.get 8
            i32.load 1 offset=1 align=2
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
        local.get 0
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
            i32.load 1 offset=1 align=2
            call 5
            local.set 12
          end
        end
        local.get 12
        local.set 0
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 13
            i32.load 1 offset=1 align=2
            local.set 13
            local.get 13
            i32.load 1 offset=5 align=2
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
        local.set 4
        local.get 2
        local.set 17
        local.get 17
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
          else
            local.get 17
            i32.load 1 offset=1 align=2
            call 5
            local.set 17
          end
        end
        local.get 17
        local.set 2
        local.tee 18
        local.get 18
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 18
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 18
            i32.load offset=3 align=2
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 18
            i32.load 1 offset=1 align=2
            local.set 18
            local.get 18
            i32.load 1 offset=1 align=2
            local.tee 20
            local.get 20
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 20
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
        local.get 5
        local.set 6
        local.get 6
        local.set 22
        local.get 22
        local.get 22
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 22
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 22
            i32.load 1 offset=1 align=2
            call 5
            local.set 22
          end
        end
        local.get 22
        local.set 6
        local.get 6
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
        local.set 24
        local.get 24
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 24
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 24
            call 4
          else
            local.get 24
            call 6
          end
        end
        local.get 2
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
        local.get 0
        local.set 26
        local.get 26
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 26
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 26
            call 4
          else
            local.get 26
            call 6
          end
        end)
      (func (;8;) (type 1) (param i32) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 1
        i32.const 1
        i32.shl
        local.set 1
        local.get 1
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
            i32.load 1 offset=1 align=2
            call 5
            local.set 8
          end
        end
        local.get 8
        local.set 1
        local.set 9
        i32.const 1
        call 2
        local.set 10
        local.get 10
        i32.const 0
        i32.const 1
        call 3
        local.get 10
        local.get 9
        local.get 9
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 9
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 9
            call 6
          end
        end
        local.get 10
        call 5
        i32.const 0
        global.get 1
        i32.add
        local.set 12
        local.set 11
        i32.const 2
        call 2
        local.set 13
        local.get 13
        i32.const 0
        i32.const 1
        call 3
        local.get 13
        i32.const 1
        i32.const 0
        call 3
        local.get 13
        local.get 11
        local.get 11
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 11
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 11
            call 6
          end
        end
        local.get 13
        local.get 12
        i32.store 1 offset=5 align=2
        local.get 13
        call 5
        local.set 2
        local.get 2
        local.set 14
        local.get 14
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
          else
            local.get 14
            i32.load 1 offset=1 align=2
            call 5
            local.set 14
          end
        end
        local.get 14
        local.set 2
        block (param i32) (result i32)  ;; label = @1
          local.set 3
          local.get 3
          local.set 15
          local.get 15
          local.get 15
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 15
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 15
              i32.load 1 offset=1 align=2
              call 5
              local.set 15
            end
          end
          local.get 15
          local.set 3
          local.tee 16
          local.get 16
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 16
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 16
              i32.load offset=3 align=2
              local.tee 17
              local.get 17
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 17
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  i32.load 1 offset=1 align=2
                  call 5
                end
              end
            else
              local.get 16
              i32.load 1 offset=1 align=2
              local.set 16
              local.get 16
              i32.load 1 offset=1 align=2
              local.tee 18
              local.get 18
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 18
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  call 5
                end
              end
            end
          end
          local.set 4
          local.set 19
          local.get 19
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 19
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 19
              call 4
            else
              local.get 19
              call 6
            end
          end
          local.get 4
          local.set 5
          local.get 3
          local.set 20
          local.get 20
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
            else
              local.get 20
              i32.load 1 offset=1 align=2
              call 5
              local.set 20
            end
          end
          local.get 20
          local.set 3
          local.tee 21
          local.get 21
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 21
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 21
              i32.load offset=7 align=2
              local.tee 22
            else
              local.get 21
              i32.load 1 offset=1 align=2
              local.set 21
              local.get 21
              i32.load 1 offset=5 align=2
              local.tee 23
            end
          end
          local.set 6
          local.set 24
          local.get 24
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 24
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 24
              call 4
            else
              local.get 24
              call 6
            end
          end
          local.get 6
          local.set 7
          local.get 5
          local.set 25
          local.get 25
          local.get 25
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 25
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 25
              i32.load 1 offset=1 align=2
              call 5
              local.set 25
            end
          end
          local.get 25
          local.set 5
          i32.const 0
          call 2
          local.set 26
          local.get 26
          call 5
          local.set 28
          local.set 27
          i32.const 2
          call 2
          local.set 29
          local.get 29
          i32.const 0
          i32.const 1
          call 3
          local.get 29
          i32.const 1
          i32.const 1
          call 3
          local.get 29
          local.get 27
          local.get 27
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            local.get 27
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=1 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=1 align=2
              local.get 27
              call 6
            end
          end
          local.get 29
          local.get 28
          local.get 28
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            local.get 28
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=5 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=5 align=2
              local.get 28
              call 6
            end
          end
          local.get 29
          call 5
          local.get 7
          local.set 30
          local.get 30
          local.get 30
          local.set 7
          call_indirect (type 1)
          local.get 7
          drop
          local.get 5
          local.set 31
          local.get 31
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 31
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 31
              call 4
            else
              local.get 31
              call 6
            end
          end
          local.get 3
          local.set 32
          local.get 32
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 32
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 32
              call 4
            else
              local.get 32
              call 6
            end
          end
        end
        local.get 2
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
        local.get 1
        local.set 34
        local.get 34
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 34
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 34
            call 4
          else
            local.get 34
            call 6
          end
        end
        local.get 0
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
      (func (;9;) (type 4)
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
      (export "_start" (func 8))
      (export "__rw_table_func_7" (func 7))
      (export "__rw_table_func_8" (func 8))
      (start 9))

    -----------closure_complex-----------
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
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        local.get 0
        local.set 14
        local.get 14
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
          else
            local.get 14
            i32.load 1 offset=1 align=2
            call 5
            local.set 14
          end
        end
        local.get 14
        local.set 0
        local.tee 15
        local.get 15
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 15
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 15
            i32.load offset=3 align=2
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 15
            i32.load 1 offset=1 align=2
            local.set 15
            local.get 15
            i32.load 1 offset=1 align=2
            local.tee 17
            local.get 17
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 17
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
        local.get 1
        local.set 2
        local.get 0
        local.set 19
        local.get 19
        local.get 19
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 19
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 19
            i32.load 1 offset=1 align=2
            call 5
            local.set 19
          end
        end
        local.get 19
        local.set 0
        local.tee 20
        local.get 20
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 20
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 20
            i32.load offset=7 align=2
            local.tee 21
            local.get 21
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 21
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
            local.get 20
            i32.load 1 offset=1 align=2
            local.set 20
            local.get 20
            i32.load 1 offset=5 align=2
            local.tee 22
            local.get 22
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 22
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
        local.get 3
        local.set 4
        local.get 2
        local.set 24
        local.get 24
        local.get 24
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 24
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 24
            i32.load 1 offset=1 align=2
            call 5
            local.set 24
          end
        end
        local.get 24
        local.set 2
        local.tee 25
        local.get 25
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 25
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 25
            i32.load offset=3 align=2
            local.tee 26
            local.get 26
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 26
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
            local.get 25
            i32.load 1 offset=1 align=2
            local.set 25
            local.get 25
            i32.load 1 offset=1 align=2
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
                call 5
              end
            end
          end
        end
        local.set 5
        local.set 28
        local.get 28
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 28
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 28
            call 4
          else
            local.get 28
            call 6
          end
        end
        local.get 5
        local.set 6
        local.get 2
        local.set 29
        local.get 29
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
          else
            local.get 29
            i32.load 1 offset=1 align=2
            call 5
            local.set 29
          end
        end
        local.get 29
        local.set 2
        local.tee 30
        local.get 30
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 30
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 30
            i32.load offset=7 align=2
            local.tee 31
            local.get 31
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 31
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
            local.get 30
            i32.load 1 offset=1 align=2
            local.set 30
            local.get 30
            i32.load 1 offset=5 align=2
            local.tee 32
            local.get 32
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 32
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
        local.set 7
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
        local.get 7
        local.set 8
        local.get 6
        local.set 34
        local.get 34
        local.get 34
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 34
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 34
            i32.load 1 offset=1 align=2
            call 5
            local.set 34
          end
        end
        local.get 34
        local.set 6
        block (param i32) (result i32)  ;; label = @1
          local.set 9
          local.get 9
          local.set 35
          local.get 35
          local.get 35
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 35
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 35
              i32.load 1 offset=1 align=2
              call 5
              local.set 35
            end
          end
          local.get 35
          local.set 9
          local.tee 36
          local.get 36
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 36
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 36
              i32.load offset=3 align=2
              local.tee 37
              local.get 37
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 37
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  i32.load 1 offset=1 align=2
                  call 5
                end
              end
            else
              local.get 36
              i32.load 1 offset=1 align=2
              local.set 36
              local.get 36
              i32.load 1 offset=1 align=2
              local.tee 38
              local.get 38
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 38
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  call 5
                end
              end
            end
          end
          local.set 10
          local.set 39
          local.get 39
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 39
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 39
              call 4
            else
              local.get 39
              call 6
            end
          end
          local.get 10
          local.set 11
          local.get 9
          local.set 40
          local.get 40
          local.get 40
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 40
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 40
              i32.load 1 offset=1 align=2
              call 5
              local.set 40
            end
          end
          local.get 40
          local.set 9
          local.tee 41
          local.get 41
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 41
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 41
              i32.load offset=7 align=2
              local.tee 42
            else
              local.get 41
              i32.load 1 offset=1 align=2
              local.set 41
              local.get 41
              i32.load 1 offset=5 align=2
              local.tee 43
            end
          end
          local.set 12
          local.set 44
          local.get 44
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 44
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 44
              call 4
            else
              local.get 44
              call 6
            end
          end
          local.get 12
          local.set 13
          local.get 11
          local.set 45
          local.get 45
          local.get 45
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 45
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 45
              i32.load 1 offset=1 align=2
              call 5
              local.set 45
            end
          end
          local.get 45
          local.set 11
          local.get 4
          local.set 46
          local.get 46
          local.get 46
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 46
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 46
              i32.load 1 offset=1 align=2
              call 5
              local.set 46
            end
          end
          local.get 46
          local.set 4
          local.set 48
          local.set 47
          i32.const 2
          call 2
          local.set 49
          local.get 49
          i32.const 0
          i32.const 1
          call 3
          local.get 49
          i32.const 1
          i32.const 1
          call 3
          local.get 49
          local.get 47
          local.get 47
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            local.get 47
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=1 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=1 align=2
              local.get 47
              call 6
            end
          end
          local.get 49
          local.get 48
          local.get 48
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            local.get 48
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=5 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=5 align=2
              local.get 48
              call 6
            end
          end
          local.get 49
          call 5
          local.get 13
          local.set 50
          local.get 50
          local.get 50
          local.set 13
          call_indirect (type 1)
          local.get 13
          drop
          local.get 11
          local.set 51
          local.get 51
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 51
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 51
              call 4
            else
              local.get 51
              call 6
            end
          end
          local.get 9
          local.set 52
          local.get 52
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 52
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 52
              call 4
            else
              local.get 52
              call 6
            end
          end
        end
        i32.const 1
        i32.shr_u
        local.get 8
        local.set 53
        local.get 53
        local.get 53
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 53
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 53
            i32.load 1 offset=1 align=2
            call 5
            local.set 53
          end
        end
        local.get 53
        local.set 8
        i32.const 1
        i32.shr_u
        i32.add
        i32.const 1
        i32.shl
        local.get 8
        local.set 54
        local.get 54
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 54
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 54
            call 4
          else
            local.get 54
            call 6
          end
        end
        local.get 6
        local.set 55
        local.get 55
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 55
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 55
            call 4
          else
            local.get 55
            call 6
          end
        end
        local.get 4
        local.set 56
        local.get 56
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 56
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 56
            call 4
          else
            local.get 56
            call 6
          end
        end
        local.get 2
        local.set 57
        local.get 57
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 57
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 57
            call 4
          else
            local.get 57
            call 6
          end
        end
        local.get 0
        local.set 58
        local.get 58
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 58
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 58
            call 4
          else
            local.get 58
            call 6
          end
        end)
      (func (;8;) (type 1) (param i32) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
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
            i32.load 1 offset=1 align=2
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
            i32.load offset=3 align=2
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 8
            i32.load 1 offset=1 align=2
            local.set 8
            local.get 8
            i32.load 1 offset=1 align=2
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
        local.get 0
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
            i32.load 1 offset=1 align=2
            call 5
            local.set 12
          end
        end
        local.get 12
        local.set 0
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 13
            i32.load 1 offset=1 align=2
            local.set 13
            local.get 13
            i32.load 1 offset=5 align=2
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
        local.set 4
        local.get 2
        local.set 17
        local.get 17
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
          else
            local.get 17
            i32.load 1 offset=1 align=2
            call 5
            local.set 17
          end
        end
        local.get 17
        local.set 2
        local.tee 18
        local.get 18
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 18
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 18
            i32.load offset=3 align=2
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
                i32.load 1 offset=1 align=2
                call 5
              end
            end
          else
            local.get 18
            i32.load 1 offset=1 align=2
            local.set 18
            local.get 18
            i32.load 1 offset=1 align=2
            local.tee 20
            local.get 20
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 20
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
        local.get 5
        local.set 6
        local.get 6
        local.set 22
        local.get 22
        local.get 22
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 22
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 22
            i32.load 1 offset=1 align=2
            call 5
            local.set 22
          end
        end
        local.get 22
        local.set 6
        i32.const 1
        i32.shr_u
        local.get 4
        local.set 23
        local.get 23
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
          else
            local.get 23
            i32.load 1 offset=1 align=2
            call 5
            local.set 23
          end
        end
        local.get 23
        local.set 4
        i32.const 1
        i32.shr_u
        i32.add
        i32.const 1
        i32.shl
        local.get 6
        local.set 24
        local.get 24
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 24
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 24
            call 4
          else
            local.get 24
            call 6
          end
        end
        local.get 4
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
        local.get 2
        local.set 26
        local.get 26
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 26
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 26
            call 4
          else
            local.get 26
            call 6
          end
        end
        local.get 0
        local.set 27
        local.get 27
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 27
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 27
            call 4
          else
            local.get 27
            call 6
          end
        end)
      (func (;9;) (type 1) (param i32) (result i32)
        (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
        i32.const 1
        i32.const 1
        i32.shl
        local.set 1
        local.get 1
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
        local.set 1
        local.set 10
        i32.const 1
        call 2
        local.set 11
        local.get 11
        i32.const 0
        i32.const 1
        call 3
        local.get 11
        local.get 10
        local.get 10
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 10
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 10
            call 6
          end
        end
        local.get 11
        call 5
        i32.const 1
        global.get 1
        i32.add
        local.set 13
        local.set 12
        i32.const 2
        call 2
        local.set 14
        local.get 14
        i32.const 0
        i32.const 1
        call 3
        local.get 14
        i32.const 1
        i32.const 0
        call 3
        local.get 14
        local.get 12
        local.get 12
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 12
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 12
            call 6
          end
        end
        local.get 14
        local.get 13
        i32.store 1 offset=5 align=2
        local.get 14
        call 5
        local.set 2
        local.get 2
        local.set 15
        local.get 15
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
          else
            local.get 15
            i32.load 1 offset=1 align=2
            call 5
            local.set 15
          end
        end
        local.get 15
        local.set 2
        local.get 1
        local.set 16
        local.get 16
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
          else
            local.get 16
            i32.load 1 offset=1 align=2
            call 5
            local.set 16
          end
        end
        local.get 16
        local.set 1
        local.set 18
        local.set 17
        i32.const 2
        call 2
        local.set 19
        local.get 19
        i32.const 0
        i32.const 1
        call 3
        local.get 19
        i32.const 1
        i32.const 1
        call 3
        local.get 19
        local.get 17
        local.get 17
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 17
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 17
            call 6
          end
        end
        local.get 19
        local.get 18
        local.get 18
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=5 align=2
        else
          local.get 18
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=5 align=2
            local.get 18
            call 6
          end
        end
        local.get 19
        call 5
        i32.const 0
        global.get 1
        i32.add
        local.set 21
        local.set 20
        i32.const 2
        call 2
        local.set 22
        local.get 22
        i32.const 0
        i32.const 1
        call 3
        local.get 22
        i32.const 1
        i32.const 0
        call 3
        local.get 22
        local.get 20
        local.get 20
        i32.const 1
        i32.and
        i32.eqz
        if (param i32 i32)  ;; label = @1
          i32.store 1 offset=1 align=2
        else
          local.get 20
          i32.const 2
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            i32.load 1 offset=1 align=2
            i32.store 1 offset=1 align=2
            local.get 20
            call 6
          end
        end
        local.get 22
        local.get 21
        i32.store 1 offset=5 align=2
        local.get 22
        call 5
        local.set 3
        local.get 3
        local.set 23
        local.get 23
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
          else
            local.get 23
            i32.load 1 offset=1 align=2
            call 5
            local.set 23
          end
        end
        local.get 23
        local.set 3
        block (param i32) (result i32)  ;; label = @1
          local.set 4
          local.get 4
          local.set 24
          local.get 24
          local.get 24
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 24
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 24
              i32.load 1 offset=1 align=2
              call 5
              local.set 24
            end
          end
          local.get 24
          local.set 4
          local.tee 25
          local.get 25
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 25
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 25
              i32.load offset=3 align=2
              local.tee 26
              local.get 26
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 26
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  i32.load 1 offset=1 align=2
                  call 5
                end
              end
            else
              local.get 25
              i32.load 1 offset=1 align=2
              local.set 25
              local.get 25
              i32.load 1 offset=1 align=2
              local.tee 27
              local.get 27
              i32.const 1
              i32.and
              i32.eqz
              if (param i32) (result i32)  ;; label = @4
              else
                local.get 27
                i32.const 2
                i32.and
                i32.eqz
                if (param i32) (result i32)  ;; label = @5
                else
                  call 5
                end
              end
            end
          end
          local.set 5
          local.set 28
          local.get 28
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 28
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 28
              call 4
            else
              local.get 28
              call 6
            end
          end
          local.get 5
          local.set 6
          local.get 4
          local.set 29
          local.get 29
          local.get 29
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 29
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 29
              i32.load 1 offset=1 align=2
              call 5
              local.set 29
            end
          end
          local.get 29
          local.set 4
          local.tee 30
          local.get 30
          i32.const 1
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            unreachable
          else
            local.get 30
            i32.const 2
            i32.and
            i32.eqz
            if (result i32)  ;; label = @3
              local.get 30
              i32.load offset=7 align=2
              local.tee 31
            else
              local.get 30
              i32.load 1 offset=1 align=2
              local.set 30
              local.get 30
              i32.load 1 offset=5 align=2
              local.tee 32
            end
          end
          local.set 7
          local.set 33
          local.get 33
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 33
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 33
              call 4
            else
              local.get 33
              call 6
            end
          end
          local.get 7
          local.set 8
          local.get 6
          local.set 34
          local.get 34
          local.get 34
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 34
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
            else
              local.get 34
              i32.load 1 offset=1 align=2
              call 5
              local.set 34
            end
          end
          local.get 34
          local.set 6
          i32.const 3
          i32.const 1
          i32.shl
          local.set 36
          local.set 35
          i32.const 2
          call 2
          local.set 37
          local.get 37
          i32.const 0
          i32.const 1
          call 3
          local.get 37
          i32.const 1
          i32.const 1
          call 3
          local.get 37
          local.get 35
          local.get 35
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=1 align=2
          else
            local.get 35
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=1 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=1 align=2
              local.get 35
              call 6
            end
          end
          local.get 37
          local.get 36
          local.get 36
          i32.const 1
          i32.and
          i32.eqz
          if (param i32 i32)  ;; label = @2
            i32.store 1 offset=5 align=2
          else
            local.get 36
            i32.const 2
            i32.and
            i32.eqz
            if (param i32 i32)  ;; label = @3
              i32.store 1 offset=5 align=2
            else
              i32.load 1 offset=1 align=2
              i32.store 1 offset=5 align=2
              local.get 36
              call 6
            end
          end
          local.get 37
          call 5
          local.get 8
          local.set 38
          local.get 38
          local.get 38
          local.set 8
          call_indirect (type 1)
          local.get 8
          drop
          local.get 6
          local.set 39
          local.get 39
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 39
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 39
              call 4
            else
              local.get 39
              call 6
            end
          end
          local.get 4
          local.set 40
          local.get 40
          i32.const 1
          i32.and
          i32.eqz
          if  ;; label = @2
          else
            local.get 40
            i32.const 2
            i32.and
            i32.eqz
            if  ;; label = @3
              local.get 40
              call 4
            else
              local.get 40
              call 6
            end
          end
        end
        local.get 3
        local.set 41
        local.get 41
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 41
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 41
            call 4
          else
            local.get 41
            call 6
          end
        end
        local.get 2
        local.set 42
        local.get 42
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 42
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 42
            call 4
          else
            local.get 42
            call 6
          end
        end
        local.get 1
        local.set 43
        local.get 43
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 43
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 43
            call 4
          else
            local.get 43
            call 6
          end
        end
        local.get 0
        local.set 44
        local.get 44
        i32.const 1
        i32.and
        i32.eqz
        if  ;; label = @1
        else
          local.get 44
          i32.const 2
          i32.and
          i32.eqz
          if  ;; label = @2
            local.get 44
            call 4
          else
            local.get 44
            call 6
          end
        end)
      (func (;10;) (type 4)
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
      (export "_start" (func 9))
      (export "__rw_table_func_7" (func 7))
      (export "__rw_table_func_8" (func 8))
      (export "__rw_table_func_9" (func 9))
      (start 10)) |}]
