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
    |> or_fail_pp Richwasm_common.Main.pp_compile_err
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
        i32.const 0
        i32.add
        global.set 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "_start" (func 7))
      (start 8))

    -----------tuple-----------
    FAILURE wat2wasm2wat validation!
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func))
      (type (;5;) (func (param i32)))
      (type (;6;) (func (param i32)))
      (type (;7;) (func (param i32)))
      (type (;8;) (func (param i32)))
      (type (;9;) (func (param i32)))
      (type (;10;) (func (param i32)))
      (type (;11;) (func (param i32)))
      (type (;12;) (func (param i32)))
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
        if (param i32)  ;; label = @1
          i32.store offset=1 align=2
        else
          local.get 4
          i32.const 2
          i32.and
          i32.eqz
          if (param i32)  ;; label = @2
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
        if (param i32)  ;; label = @1
          i32.store offset=5 align=2
        else
          local.get 3
          i32.const 2
          i32.and
          i32.eqz
          if (param i32)  ;; label = @2
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
        if (param i32)  ;; label = @1
          i32.store offset=9 align=2
        else
          local.get 2
          i32.const 2
          i32.and
          i32.eqz
          if (param i32)  ;; label = @2
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
        if (param i32)  ;; label = @1
          i32.store offset=13 align=2
        else
          local.get 1
          i32.const 2
          i32.and
          i32.eqz
          if (param i32)  ;; label = @2
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
        i32.const 0
        i32.add
        global.set 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "_start" (func 7))
      (start 8))
    Wat2wasm Error: -:1:999: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...nst 1 i32.and i32.eqz if(type 5) i32.store 0 offset=1 align=2 else local.g...
                                        ^^^^^^^^^
    -:1:1084: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...nst 2 i32.and i32.eqz if(type 6) i32.store 0 offset=1 align=2 else i32.loa...
                                        ^^^^^^^^^
    -:1:1146: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...else i32.load 0 offset=1 align=2 i32.store 0 offset=1 align=2 local.get 4 ...
                                        ^^^^^^^^^
    -:1:1277: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...nst 1 i32.and i32.eqz if(type 7) i32.store 0 offset=5 align=2 else local.g...
                                        ^^^^^^^^^
    -:1:1362: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...nst 2 i32.and i32.eqz if(type 8) i32.store 0 offset=5 align=2 else i32.loa...
                                        ^^^^^^^^^
    -:1:1424: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...else i32.load 0 offset=1 align=2 i32.store 0 offset=5 align=2 local.get 3 ...
                                        ^^^^^^^^^
    -:1:1555: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...nst 1 i32.and i32.eqz if(type 9) i32.store 0 offset=9 align=2 else local.g...
                                        ^^^^^^^^^
    -:1:1641: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...st 2 i32.and i32.eqz if(type 10) i32.store 0 offset=9 align=2 else i32.loa...
                                        ^^^^^^^^^
    -:1:1703: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...else i32.load 0 offset=1 align=2 i32.store 0 offset=9 align=2 local.get 2 ...
                                        ^^^^^^^^^
    -:1:1835: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...st 1 i32.and i32.eqz if(type 11) i32.store 0 offset=13 align=2 else local....
                                        ^^^^^^^^^
    -:1:1922: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...st 2 i32.and i32.eqz if(type 12) i32.store 0 offset=13 align=2 else i32.lo...
                                        ^^^^^^^^^
    -:1:1985: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...else i32.load 0 offset=1 align=2 i32.store 0 offset=13 align=2 local.get 1...
                                        ^^^^^^^^^
    -:1:2054: error: type mismatch at end of function, expected [] but got [i32, i32, i32, i32]
    ...l.get 1 call 6 end end local.get 5 call 5)(func (type 4) (local ) global.g...
                                          ^^^^

    -----------tuple_nested-----------
    FAILURE wat2wasm2wat validation!
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func))
      (type (;5;) (func (param i32)))
      (type (;6;) (func (param i32)))
      (type (;7;) (func (param i32)))
      (type (;8;) (func (param i32)))
      (type (;9;) (func (param i32)))
      (type (;10;) (func (param i32)))
      (type (;11;) (func (param i32)))
      (type (;12;) (func (param i32)))
      (type (;13;) (func (param i32)))
      (type (;14;) (func (param i32)))
      (type (;15;) (func (param i32)))
      (type (;16;) (func (param i32)))
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
        if (param i32)  ;; label = @1
          i32.store offset=1 align=2
        else
          local.get 2
          i32.const 2
          i32.and
          i32.eqz
          if (param i32)  ;; label = @2
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
        if (param i32)  ;; label = @1
          i32.store offset=5 align=2
        else
          local.get 1
          i32.const 2
          i32.and
          i32.eqz
          if (param i32)  ;; label = @2
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
        if (param i32)  ;; label = @1
          i32.store offset=1 align=2
        else
          local.get 5
          i32.const 2
          i32.and
          i32.eqz
          if (param i32)  ;; label = @2
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
        if (param i32)  ;; label = @1
          i32.store offset=5 align=2
        else
          local.get 4
          i32.const 2
          i32.and
          i32.eqz
          if (param i32)  ;; label = @2
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
        if (param i32)  ;; label = @1
          i32.store offset=1 align=2
        else
          local.get 8
          i32.const 2
          i32.and
          i32.eqz
          if (param i32)  ;; label = @2
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
        if (param i32)  ;; label = @1
          i32.store offset=5 align=2
        else
          local.get 7
          i32.const 2
          i32.and
          i32.eqz
          if (param i32)  ;; label = @2
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
        i32.const 0
        i32.add
        global.set 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "_start" (func 7))
      (start 8))
    Wat2wasm Error: -:1:841: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...nst 1 i32.and i32.eqz if(type 5) i32.store 0 offset=1 align=2 else local.g...
                                        ^^^^^^^^^
    -:1:926: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...nst 2 i32.and i32.eqz if(type 6) i32.store 0 offset=1 align=2 else i32.loa...
                                        ^^^^^^^^^
    -:1:988: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...else i32.load 0 offset=1 align=2 i32.store 0 offset=1 align=2 local.get 2 ...
                                        ^^^^^^^^^
    -:1:1119: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...nst 1 i32.and i32.eqz if(type 7) i32.store 0 offset=5 align=2 else local.g...
                                        ^^^^^^^^^
    -:1:1204: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...nst 2 i32.and i32.eqz if(type 8) i32.store 0 offset=5 align=2 else i32.loa...
                                        ^^^^^^^^^
    -:1:1266: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...else i32.load 0 offset=1 align=2 i32.store 0 offset=5 align=2 local.get 1 ...
                                        ^^^^^^^^^
    -:1:1625: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...nst 1 i32.and i32.eqz if(type 9) i32.store 0 offset=1 align=2 else local.g...
                                        ^^^^^^^^^
    -:1:1711: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...st 2 i32.and i32.eqz if(type 10) i32.store 0 offset=1 align=2 else i32.loa...
                                        ^^^^^^^^^
    -:1:1773: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...else i32.load 0 offset=1 align=2 i32.store 0 offset=1 align=2 local.get 5 ...
                                        ^^^^^^^^^
    -:1:1905: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...st 1 i32.and i32.eqz if(type 11) i32.store 0 offset=5 align=2 else local.g...
                                        ^^^^^^^^^
    -:1:1991: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...st 2 i32.and i32.eqz if(type 12) i32.store 0 offset=5 align=2 else i32.loa...
                                        ^^^^^^^^^
    -:1:2053: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...else i32.load 0 offset=1 align=2 i32.store 0 offset=5 align=2 local.get 4 ...
                                        ^^^^^^^^^
    -:1:2349: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...st 1 i32.and i32.eqz if(type 13) i32.store 0 offset=1 align=2 else local.g...
                                        ^^^^^^^^^
    -:1:2435: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...st 2 i32.and i32.eqz if(type 14) i32.store 0 offset=1 align=2 else i32.loa...
                                        ^^^^^^^^^
    -:1:2497: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...else i32.load 0 offset=1 align=2 i32.store 0 offset=1 align=2 local.get 8 ...
                                        ^^^^^^^^^
    -:1:2629: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...st 1 i32.and i32.eqz if(type 15) i32.store 0 offset=5 align=2 else local.g...
                                        ^^^^^^^^^
    -:1:2715: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...st 2 i32.and i32.eqz if(type 16) i32.store 0 offset=5 align=2 else i32.loa...
                                        ^^^^^^^^^
    -:1:2777: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...else i32.load 0 offset=1 align=2 i32.store 0 offset=5 align=2 local.get 7 ...
                                        ^^^^^^^^^
    -:1:2845: error: type mismatch at end of function, expected [] but got [... i32, i32, i32, i32]
    ...l.get 7 call 6 end end local.get 9 call 5)(func (type 4) (local ) global.g...
                                          ^^^^

    -----------tuple_project-----------
    FAILURE wat2wasm2wat validation!
    (module
      (type (;0;) (func (param i32 i32)))
      (type (;1;) (func (param i32) (result i32)))
      (type (;2;) (func (param i32 i32 i32)))
      (type (;3;) (func (param i32)))
      (type (;4;) (func))
      (type (;5;) (func (param i32)))
      (type (;6;) (func (param i32)))
      (type (;7;) (func (param i32)))
      (type (;8;) (func (param i32)))
      (type (;9;) (func (param i32) (result i32)))
      (type (;10;) (func (param i32) (result i32)))
      (type (;11;) (func (param i32) (result i32)))
      (type (;12;) (func (param i32) (result i32)))
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
        i32.const 7
        i32.const 1
        i32.shl
        i32.const 42
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
        if (param i32)  ;; label = @1
          i32.store offset=1 align=2
        else
          local.get 2
          i32.const 2
          i32.and
          i32.eqz
          if (param i32)  ;; label = @2
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
        if (param i32)  ;; label = @1
          i32.store offset=5 align=2
        else
          local.get 1
          i32.const 2
          i32.and
          i32.eqz
          if (param i32)  ;; label = @2
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
        local.set 4
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
        end)
      (func (;8;) (type 4)
        global.get 0
        global.set 1
        global.get 1
        i32.const 0
        i32.add
        global.set 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "_start" (func 7))
      (start 8))
    Wat2wasm Error: -:1:830: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...nst 1 i32.and i32.eqz if(type 5) i32.store 0 offset=1 align=2 else local.g...
                                        ^^^^^^^^^
    -:1:915: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...nst 2 i32.and i32.eqz if(type 6) i32.store 0 offset=1 align=2 else i32.loa...
                                        ^^^^^^^^^
    -:1:977: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...else i32.load 0 offset=1 align=2 i32.store 0 offset=1 align=2 local.get 2 ...
                                        ^^^^^^^^^
    -:1:1108: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...nst 1 i32.and i32.eqz if(type 7) i32.store 0 offset=5 align=2 else local.g...
                                        ^^^^^^^^^
    -:1:1193: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...nst 2 i32.and i32.eqz if(type 8) i32.store 0 offset=5 align=2 else i32.loa...
                                        ^^^^^^^^^
    -:1:1255: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...else i32.load 0 offset=1 align=2 i32.store 0 offset=5 align=2 local.get 1 ...
                                        ^^^^^^^^^
    -:1:1382: error: type mismatch at end of function, expected [] but got [i32, i32]
    ...l.get 4 i32.const 1 i32.and i32.eqz if(result i32) unreachable else local....
                                           ^^

    -----------sum_unit-----------
    FAILURE (InstrErr
     (error
      (Ctx
       (error
        (CannotMeet "expected memtype" (VALTYPE (AtomR PtrR) ExCopy ExDrop)))
       (ctx
        (InstrTOut ((Ref (Base GC) (Variant ((Ref (Base GC) (Struct ()))))))))))
     (instr (Inject (GC) 0 ((Ref (Base GC) (Struct ())))))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return ((Ref (Base GC) (Struct ()))))
       (functions
        ((FunctionType () ((Ref (Base GC) (Struct ())))
          ((Ref (Base GC) (Struct ()))))))
       (table ()) (lfx ())))
     (state
      ((locals ((Ref (Base GC) (Struct ())) (Plug (Atom Ptr))))
       (stack ((Ref (Base GC) (Struct ())))))))
    -----------sum_option-----------
    FAILURE (InstrErr
     (error
      (Ctx
       (error
        (CannotMeet "expected memtype" (VALTYPE (AtomR PtrR) ExCopy ExDrop)))
       (ctx
        (InstrTOut ((Ref (Base GC) (Variant ((Ref (Base GC) (Struct ())) I31))))))))
     (instr (Inject (GC) 1 ((Ref (Base GC) (Struct ())) I31)))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return ((Ref (Base GC) (Struct ()))))
       (functions
        ((FunctionType () ((Ref (Base GC) (Struct ())))
          ((Ref (Base GC) (Struct ()))))))
       (table ()) (lfx ())))
     (state
      ((locals ((Ref (Base GC) (Struct ())) (Plug (Atom Ptr)))) (stack (I31)))))
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
        i32.const 0
        i32.add
        global.set 0)
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
        i32.const 0
        i32.add
        global.set 0)
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
        i32.const 0
        i32.add
        global.set 0)
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
        i32.const 0
        i32.add
        global.set 0)
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
        i32.const 0
        i32.add
        global.set 0)
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
        i32.const 0
        i32.add
        global.set 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "_start" (func 7))
      (start 8))

    -----------return_one-----------
    FAILURE (InstrErr (error (InvalidTableIdx 0)) (instr (CodeRef 0))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return ((Ref (Base GC) (Struct ()))))
       (functions
        ((FunctionType ()
          ((Ref (Base GC)
            (Struct
             ((Ser (Ref (Base GC) (Struct ())))
              (Ser (Ref (Base GC) (Struct ())))))))
          (I31))
         (FunctionType () ((Ref (Base GC) (Struct ())))
          ((Ref (Base GC) (Struct ()))))))
       (table ()) (lfx ())))
     (state
      ((locals ((Ref (Base GC) (Struct ())) (Plug (Atom Ptr))))
       (stack ((Ref (Base GC) (Struct ())))))))
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
        (local i32 i32 i32 i32 i32 i32 i32 i32)
        local.get 0
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
        local.set 0
        local.set 3
        local.get 3
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 3
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 3
            i32.load offset=7 align=2
            local.tee 4
            local.get 4
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 4
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
            local.get 3
            i32.load offset=5 align=2
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
                call 5
              end
            end
          end
        end
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
            i32.load offset=1 align=2
            call 5
            local.set 6
          end
        end
        local.get 6
        local.set 1
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
        local.get 1
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
        i32.const 0
        i32.add
        global.set 0)
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
        (local i32 i32 i32 i32 i32 i32 i32 i32)
        local.get 0
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
        local.set 0
        local.set 3
        local.get 3
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 3
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 3
            i32.load offset=7 align=2
            local.tee 4
            local.get 4
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 4
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
            local.get 3
            i32.load offset=5 align=2
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
                call 5
              end
            end
          end
        end
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
            i32.load offset=1 align=2
            call 5
            local.set 6
          end
        end
        local.get 6
        local.set 1
        local.get 1
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
        i32.const 0
        i32.add
        global.set 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "id" (func 7))
      (start 8))

    -----------apply_id-----------
    FAILURE (InstrErr (error (InvalidTableIdx 0)) (instr (CodeRef 0))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return ((Ref (Base GC) (Struct ()))))
       (functions
        ((FunctionType ((Type (VALTYPE (Atom Ptr) ExCopy ExDrop)))
          ((Ref (Base GC)
            (Struct ((Ser (Ref (Base GC) (Struct ()))) (Ser (Var 0))))))
          ((Var 0)))
         (FunctionType () ((Ref (Base GC) (Struct ())))
          ((Ref (Base GC) (Struct ()))))))
       (table ()) (lfx ())))
     (state
      ((locals
        ((Ref (Base GC) (Struct ())) (Plug (Atom Ptr)) (Plug (Atom Ptr))
         (Plug (Atom Ptr)) (Plug (Atom Ptr))))
       (stack ((Ref (Base GC) (Struct ())))))))
    -----------opt_case-----------
    FAILURE (InstrErr
     (error
      (Ctx
       (error
        (CannotMeet "expected memtype" (VALTYPE (AtomR PtrR) ExCopy ExDrop)))
       (ctx
        (InstrTOut ((Ref (Base GC) (Variant ((Ref (Base GC) (Struct ())) I31))))))))
     (instr (Inject (GC) 1 ((Ref (Base GC) (Struct ())) I31)))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return ((Ref (Base GC) (Struct ()))))
       (functions
        ((FunctionType () ((Ref (Base GC) (Struct ())))
          ((Ref (Base GC) (Struct ()))))))
       (table ()) (lfx ())))
     (state
      ((locals
        ((Ref (Base GC) (Struct ())) (Plug (Atom Ptr)) (Plug (Atom Ptr))
         (Plug (Atom Ptr)) (Plug (Atom Ptr))))
       (stack (I31)))))
    -----------poly_len-----------
    FAILURE (InstrErr
     (error
      (BlockErr (error (InvalidTableIdx 0)) (instr (CodeRef 0))
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
           (FunctionType () ((Ref (Base GC) (Struct ())))
            ((Ref (Base GC) (Struct ()))))))
         (table ()) (lfx ((LocalFx ((3 (Prod ()))))))))
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
           (Plug (Atom Ptr)) (Plug (Atom Ptr))))
         (stack ((Ref (Base GC) (Struct ())) (Num (Int I32))))))))
     (instr
      (Case (ArrowType 1 (I31)) (LocalFx ((3 (Prod ()))))
       (((LocalSet 6) (NumConst (Int I32) 0) Tag (LocalGet 6 Move) Drop)
        ((LocalSet 2) (NumConst (Int I32) 1) Tag Untag (Group 0) (New GC)
         (Cast (Ref (Base GC) (Struct ()))) (CodeRef 0) (Group 2) (New GC)
         (Cast
          (Ref (Base GC)
           (Struct
            ((Ser (Ref (Base GC) (Struct ())))
             (Ser
              (Ref (Base GC)
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
                       (I31)))))))))))))))
         (Pack (Type (Ref (Base GC) (Struct ())))
          (Ref (Base GC)
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
                   (I31)))))))))))
         (New GC) (Load (Path ()) Follow)
         (Unpack (ArrowType 1 (I31)) (LocalFx ((3 (Prod ()))))
          ((LocalSet 3) (LocalGet 3 Move) Copy (LocalSet 3)
           (Load (Path (0)) Follow) (LocalSet 4) (LocalGet 3 Move) Copy
           (LocalSet 3) (Load (Path (1)) Follow) (LocalSet 5) (LocalGet 2 Move)
           Copy (LocalSet 2)
           (Fold
            (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
             (Ref (Base GC)
              (Variant
               ((Ser (Ref (Base GC) (Struct ())))
                (Ser (Ref (Base GC) (Variant ((Ser (Var 2)) (Ser (Var 0)))))))))))
           (LocalGet 5 Move) Copy (LocalSet 5) (Inst (Type (Var 1))) CallIndirect
           (LocalGet 5 Move) Drop (LocalGet 4 Move) Drop (LocalGet 3 Move) Drop))
         Untag (Num (Int2 I32 Add)) Tag (LocalGet 2 Move) Drop))))
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
         (FunctionType () ((Ref (Base GC) (Struct ())))
          ((Ref (Base GC) (Struct ()))))))
       (table ()) (lfx ())))
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
         (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
          (Ref (Base GC)
           (Variant
            ((Ser (Ref (Base GC) (Struct ())))
             (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))
         (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr))
         (Plug (Atom Ptr)) (Plug (Atom Ptr))))
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
                      (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0))))))))))))))))))
         (Ref (Base GC)
          (Struct
           ((Ser (Ref (Base GC) (Struct ())))
            (Ser
             (Rec (VALTYPE (Atom Ptr) ExCopy ExDrop)
              (Ref (Base GC)
               (Variant
                ((Ser (Ref (Base GC) (Struct ())))
                 (Ser (Ref (Base GC) (Variant ((Ser (Var 1)) (Ser (Var 0)))))))))))))))))))
    -----------mini_zip-----------
    FAILURE wat2wasm2wat validation!
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
      (type (;13;) (func (param i32) (result i32)))
      (type (;14;) (func (param i32) (result i32)))
      (type (;15;) (func (param i32) (result i32)))
      (type (;16;) (func (param i32) (result i32)))
      (type (;17;) (func (param i32) (result i32)))
      (type (;18;) (func (param i32) (result i32)))
      (type (;19;) (func (param i32) (result i32)))
      (type (;20;) (func (param i32) (result i32)))
      (type (;21;) (func))
      (type (;22;) (func))
      (type (;23;) (func (param i32) (result i32)))
      (type (;24;) (func (param i32) (result i32)))
      (type (;25;) (func (param i32) (result i32)))
      (type (;26;) (func (param i32) (result i32)))
      (type (;27;) (func (param i32) (result i32)))
      (type (;28;) (func (param i32) (result i32)))
      (type (;29;) (func (param i32) (result i32)))
      (type (;30;) (func (param i32) (result i32)))
      (type (;31;) (func (param i32)))
      (type (;32;) (func (param i32)))
      (type (;33;) (func (param i32)))
      (type (;34;) (func (param i32)))
      (type (;35;) (func (param i32)))
      (type (;36;) (func (param i32)))
      (type (;37;) (func))
      (type (;38;) (func))
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
        local.set 0
        local.set 3
        local.get 3
        i32.const 1
        i32.and
        i32.eqz
        if (result i32)  ;; label = @1
          unreachable
        else
          local.get 3
          i32.const 2
          i32.and
          i32.eqz
          if (result i32)  ;; label = @2
            local.get 3
            i32.load offset=7 align=2
            local.tee 4
            local.get 4
            i32.const 1
            i32.and
            i32.eqz
            if (param i32) (result i32)  ;; label = @3
            else
              local.get 4
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
            local.get 3
            i32.load offset=5 align=2
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
                call 5
              end
            end
          end
        end
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
            i32.load offset=1 align=2
            call 5
            local.set 6
          end
        end
        local.get 6
        local.set 1
        local.set 7
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
                i32.load offset=1 align=2
                call 5
              end
            end
          else
            local.get 7
            i32.load offset=5 align=2
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
          end
        end
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
                i32.load offset=1 align=2
                call 5
              end
            end
          else
            local.get 10
            i32.load offset=1 align=2
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
        local.get 1
        local.set 13
        local.get 13
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
          else
            local.get 13
            i32.load offset=1 align=2
            call 5
            local.set 13
          end
        end
        local.get 13
        local.set 1
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
                i32.load offset=1 align=2
                call 5
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
        local.set 17
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
        nop
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
        i32.const 1
        call 3
        local.get 22
        local.get 21
        local.get 21
        i32.const 1
        i32.and
        i32.eqz
        if (param i32)  ;; label = @1
          i32.store offset=1 align=2
        else
          local.get 21
          i32.const 2
          i32.and
          i32.eqz
          if (param i32)  ;; label = @2
            i32.store offset=1 align=2
          else
            i32.load offset=1 align=2
            i32.store offset=1 align=2
            local.get 21
            call 6
          end
        end
        local.get 22
        local.get 20
        local.get 20
        i32.const 1
        i32.and
        i32.eqz
        if (param i32)  ;; label = @1
          i32.store offset=5 align=2
        else
          local.get 20
          i32.const 2
          i32.and
          i32.eqz
          if (param i32)  ;; label = @2
            i32.store offset=5 align=2
          else
            i32.load offset=1 align=2
            i32.store offset=5 align=2
            local.get 20
            call 6
          end
        end
        local.get 22
        call 5
        local.set 23
        i32.const 1
        call 2
        local.set 24
        local.get 24
        i32.const 0
        i32.const 1
        call 3
        local.get 24
        local.get 23
        local.get 23
        i32.const 1
        i32.and
        i32.eqz
        if (param i32)  ;; label = @1
          i32.store offset=1 align=2
        else
          local.get 23
          i32.const 2
          i32.and
          i32.eqz
          if (param i32)  ;; label = @2
            i32.store offset=1 align=2
          else
            i32.load offset=1 align=2
            i32.store offset=1 align=2
            local.get 23
            call 6
          end
        end
        local.get 24
        call 5
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
        end)
      (func (;8;) (type 4)
        global.get 0
        global.set 1
        global.get 1
        i32.const 0
        i32.add
        global.set 0)
      (global (;1;) (mut i32) (i32.const 0))
      (export "mini_zip" (func 7))
      (start 8))
    Wat2wasm Error: -:1:4330: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...st 1 i32.and i32.eqz if(type 31) i32.store 0 offset=1 align=2 else local.g...
                                        ^^^^^^^^^
    -:1:4417: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...st 2 i32.and i32.eqz if(type 32) i32.store 0 offset=1 align=2 else i32.loa...
                                        ^^^^^^^^^
    -:1:4479: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...else i32.load 0 offset=1 align=2 i32.store 0 offset=1 align=2 local.get 21...
                                        ^^^^^^^^^
    -:1:4615: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...st 1 i32.and i32.eqz if(type 33) i32.store 0 offset=5 align=2 else local.g...
                                        ^^^^^^^^^
    -:1:4702: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...st 2 i32.and i32.eqz if(type 34) i32.store 0 offset=5 align=2 else i32.loa...
                                        ^^^^^^^^^
    -:1:4764: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...else i32.load 0 offset=1 align=2 i32.store 0 offset=5 align=2 local.get 20...
                                        ^^^^^^^^^
    -:1:5009: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...st 1 i32.and i32.eqz if(type 35) i32.store 0 offset=1 align=2 else local.g...
                                        ^^^^^^^^^
    -:1:5096: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...st 2 i32.and i32.eqz if(type 36) i32.store 0 offset=1 align=2 else i32.loa...
                                        ^^^^^^^^^
    -:1:5158: error: type mismatch in i32.store, expected [i32, i32] but got [i32]
    ...else i32.load 0 offset=1 align=2 i32.store 0 offset=1 align=2 local.get 23...
                                        ^^^^^^^^^
    -:1:5301: error: type mismatch at end of function, expected [] but got [i32, i32, i32]
    ....get 25 i32.const 1 i32.and i32.eqz if(type 37) else local.get 25 i32.cons...
                                           ^^

    -----------closure_simpl-----------
    FAILURE (InstrErr (error (InvalidTableIdx 0)) (instr (CodeRef 0))
     (env
      ((local_offset 1) (kinds ()) (labels ())
       (return ((Ref (Base GC) (Struct ()))))
       (functions
        ((FunctionType ()
          ((Ref (Base GC)
            (Struct
             ((Ser (Ref (Base GC) (Struct ((Ser I31)))))
              (Ser (Ref (Base GC) (Struct ())))))))
          (I31))
         (FunctionType () ((Ref (Base GC) (Struct ())))
          ((Ref (Base GC) (Struct ()))))))
       (table ()) (lfx ())))
     (state
      ((locals
        ((Ref (Base GC) (Struct ())) I31 (Plug (Atom Ptr)) (Plug (Atom Ptr))
         (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr))))
       (stack ((Ref (Base GC) (Struct ((Ser I31)))))))))
    -----------closure_complex-----------
    FAILURE (InstrErr
     (error
      (IncorrectLocalFx unpack 5
       ((Ref (Base GC)
         (Struct
          ((Ser
            (Ref (Base GC)
             (Struct
              ((Ser
                (Ref (Base GC)
                 (Ser
                  (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
                   (Ref (Base GC)
                    (Struct
                     ((Ser (Var 0))
                      (Ser
                       (CodeRef
                        (FunctionType ()
                         ((Ref (Base GC) (Struct ((Ser (Var 0)) (Ser I31)))))
                         (I31)))))))))))
               (Ser I31)))))
           (Ser I31))))
        (Ref (Base GC)
         (Struct
          ((Ser
            (Ref (Base GC)
             (Ser
              (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
               (Ref (Base GC)
                (Struct
                 ((Ser (Var 0))
                  (Ser
                   (CodeRef
                    (FunctionType ()
                     ((Ref (Base GC) (Struct ((Ser (Var 0)) (Ser I31)))))
                     (I31)))))))))))
           (Ser I31))))
        I31
        (Ref (Base GC)
         (Ser
          (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
           (Ref (Base GC)
            (Struct
             ((Ser (Var 0))
              (Ser
               (CodeRef
                (FunctionType ()
                 ((Ref (Base GC) (Struct ((Ser (Var 0)) (Ser I31))))) (I31))))))))))
        I31 (Prod ()) (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr)))
       ((Ref (Base GC)
         (Struct
          ((Ser
            (Ref (Base GC)
             (Struct
              ((Ser
                (Ref (Base GC)
                 (Ser
                  (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
                   (Ref (Base GC)
                    (Struct
                     ((Ser (Var 0))
                      (Ser
                       (CodeRef
                        (FunctionType ()
                         ((Ref (Base GC) (Struct ((Ser (Var 0)) (Ser I31)))))
                         (I31)))))))))))
               (Ser I31)))))
           (Ser I31))))
        (Ref (Base GC)
         (Struct
          ((Ser
            (Ref (Base GC)
             (Ser
              (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
               (Ref (Base GC)
                (Struct
                 ((Ser (Var 0))
                  (Ser
                   (CodeRef
                    (FunctionType ()
                     ((Ref (Base GC) (Struct ((Ser (Var 0)) (Ser I31)))))
                     (I31)))))))))))
           (Ser I31))))
        I31
        (Ref (Base GC)
         (Ser
          (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
           (Ref (Base GC)
            (Struct
             ((Ser (Var 0))
              (Ser
               (CodeRef
                (FunctionType ()
                 ((Ref (Base GC) (Struct ((Ser (Var 0)) (Ser I31))))) (I31))))))))))
        I31 (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom I32))
        (Plug (Atom Ptr)))))
     (instr
      (Unpack (ArrowType 1 (I31)) (LocalFx ((5 (Prod ()))))
       ((LocalSet 5) (LocalGet 5 Move) Copy (LocalSet 5) (Load (Path (0)) Follow)
        (LocalSet 6) (LocalGet 5 Move) Copy (LocalSet 5) (Load (Path (1)) Follow)
        (LocalSet 7) (LocalGet 2 Move) Copy (LocalSet 2) (LocalGet 7 Move) Copy
        (LocalSet 7) CallIndirect (LocalGet 7 Move) Drop (LocalGet 6 Move) Drop
        (LocalGet 5 Move) Drop)))
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
                   (Ref (Base GC)
                    (Ser
                     (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
                      (Ref (Base GC)
                       (Struct
                        ((Ser (Var 0))
                         (Ser
                          (CodeRef
                           (FunctionType ()
                            ((Ref (Base GC) (Struct ((Ser (Var 0)) (Ser I31)))))
                            (I31)))))))))))
                  (Ser I31)))))
              (Ser I31)))))
          (I31))
         (FunctionType ()
          ((Ref (Base GC)
            (Struct ((Ser (Ref (Base GC) (Struct ((Ser I31))))) (Ser I31)))))
          (I31))
         (FunctionType () ((Ref (Base GC) (Struct ())))
          ((Ref (Base GC) (Struct ()))))))
       (table ()) (lfx ())))
     (state
      ((locals
        ((Ref (Base GC)
          (Struct
           ((Ser
             (Ref (Base GC)
              (Struct
               ((Ser
                 (Ref (Base GC)
                  (Ser
                   (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
                    (Ref (Base GC)
                     (Struct
                      ((Ser (Var 0))
                       (Ser
                        (CodeRef
                         (FunctionType ()
                          ((Ref (Base GC) (Struct ((Ser (Var 0)) (Ser I31)))))
                          (I31)))))))))))
                (Ser I31)))))
            (Ser I31))))
         (Ref (Base GC)
          (Struct
           ((Ser
             (Ref (Base GC)
              (Ser
               (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
                (Ref (Base GC)
                 (Struct
                  ((Ser (Var 0))
                   (Ser
                    (CodeRef
                     (FunctionType ()
                      ((Ref (Base GC) (Struct ((Ser (Var 0)) (Ser I31)))))
                      (I31)))))))))))
            (Ser I31))))
         I31
         (Ref (Base GC)
          (Ser
           (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
            (Ref (Base GC)
             (Struct
              ((Ser (Var 0))
               (Ser
                (CodeRef
                 (FunctionType ()
                  ((Ref (Base GC) (Struct ((Ser (Var 0)) (Ser I31))))) (I31))))))))))
         I31 (Plug (Atom Ptr)) (Plug (Atom Ptr)) (Plug (Atom Ptr))
         (Plug (Atom Ptr))))
       (stack
        ((Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
          (Ref (Base GC)
           (Struct
            ((Ser (Var 0))
             (Ser
              (CodeRef
               (FunctionType ()
                ((Ref (Base GC) (Struct ((Ser (Var 0)) (Ser I31))))) (I31))))))))
         (Ref (Base GC)
          (Ser
           (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
            (Ref (Base GC)
             (Struct
              ((Ser (Var 0))
               (Ser
                (CodeRef
                 (FunctionType ()
                  ((Ref (Base GC) (Struct ((Ser (Var 0)) (Ser I31))))) (I31))))))))))
         (Ref (Base GC)
          (Struct
           ((Ser
             (Ref (Base GC)
              (Ser
               (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
                (Ref (Base GC)
                 (Struct
                  ((Ser (Var 0))
                   (Ser
                    (CodeRef
                     (FunctionType ()
                      ((Ref (Base GC) (Struct ((Ser (Var 0)) (Ser I31)))))
                      (I31)))))))))))
            (Ser I31))))
         (Ref (Base GC)
          (Struct
           ((Ser
             (Ref (Base GC)
              (Ser
               (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
                (Ref (Base GC)
                 (Struct
                  ((Ser (Var 0))
                   (Ser
                    (CodeRef
                     (FunctionType ()
                      ((Ref (Base GC) (Struct ((Ser (Var 0)) (Ser I31)))))
                      (I31)))))))))))
            (Ser I31))))
         (Ref (Base GC)
          (Struct
           ((Ser
             (Ref (Base GC)
              (Struct
               ((Ser
                 (Ref (Base GC)
                  (Ser
                   (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
                    (Ref (Base GC)
                     (Struct
                      ((Ser (Var 0))
                       (Ser
                        (CodeRef
                         (FunctionType ()
                          ((Ref (Base GC) (Struct ((Ser (Var 0)) (Ser I31)))))
                          (I31)))))))))))
                (Ser I31)))))
            (Ser I31))))
         (Ref (Base GC)
          (Struct
           ((Ser
             (Ref (Base GC)
              (Struct
               ((Ser
                 (Ref (Base GC)
                  (Ser
                   (Exists (Type (VALTYPE (Atom Ptr) ExCopy ExDrop))
                    (Ref (Base GC)
                     (Struct
                      ((Ser (Var 0))
                       (Ser
                        (CodeRef
                         (FunctionType ()
                          ((Ref (Base GC) (Struct ((Ser (Var 0)) (Ser I31)))))
                          (I31)))))))))))
                (Ser I31)))))
            (Ser I31))))))))) |}]
