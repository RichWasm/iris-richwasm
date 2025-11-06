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

let%expect_test "basic functionality" =
  run {| 1 |};
  [%expect
    {|
      Error: 000012e: error: unfinished section (expected end: 0x12f) |}];
  next ();
  [%expect
    {| "\000asm\001\000\000\000\001*\t`\002\127\127\000`\001\127\001\127`\001\127\001\127`\003\127\127\127\000`\001\127\000`\001\127\001\127`\001\127\000`\000\001\127`\000\000\002\225\001\011\brichwasm\006mem_mm\002\000\000\brichwasm\006mem_gc\002\000\000\brichwasm\ntable_next\003\127\001\brichwasm\ttable_set\000\000\brichwasm\007mmalloc\000\001\brichwasm\007gcalloc\000\002\brichwasm\007setflag\000\003\brichwasm\004free\000\004\brichwasm\012registerroot\000\005\brichwasm\014unregisterroot\000\006\brichwasm\005table\001p\000\000\003\003\002\007\b\006\006\001\127\001A\000\011\007\004\001\000\000\007\b\002\001\b\n\020\002\004\000A\001\011\r\000#\000$\001#\001A\000j$\000\011" |}]
