open! Core
open! Core_unix
open! Stdlib.Format

let or_fail (p : 'b -> string) : ('a, 'b) Result.t -> 'a = function
  | Ok x -> x
  | Error err -> failwith (p err)

let or_fail_pp (pp : formatter -> 'b -> unit) : ('a, 'b) Result.t -> 'a =
  or_fail (asprintf "%a" pp)

module AnnRichWasm = Richwasm_common.Annotated_syntax
module RichWasm = Richwasm_common.Syntax

let ll_pipeline x =
  let open Richwasm_lin_lang in
  x
  |> Parse.from_string_exn
  |> Main.compile_ast
  |> Main.Res.T.run
  |> fst
  |> or_fail_pp Main.CompileErr.pp

let elab_pipeline x =
  x
  |> Richwasm_common.Elaborate.elab_module
  |> or_fail_pp Richwasm_common.Elaborate.Err.pp

let pp_rwasm = function
  | `pp -> RichWasm.Module.pp
  | `sexp -> RichWasm.Module.pp_sexp
  | `rocq -> failwith "no rocq pp for unannotated richwasm"

let pp_rwasm_ann = function
  | `pp -> AnnRichWasm.Module.pp
  | `sexp -> AnnRichWasm.Module.pp_sexp
  | `rocq -> AnnRichWasm.Module.pp_rocq

let get_contents = function
  | "-" -> In_channel.input_all In_channel.stdin
  | filename -> In_channel.read_all filename

let file_or_stdin name =
  let open Command.Param in
  anon (maybe_with_default "-" (name %: Filename_unix.arg_type))

let richwasm_pp_spec =
  let open Command.Param in
  let of_string = function
    | "pp" -> `pp
    | "sexp" -> `sexp
    | "rocq" -> `rocq
    | x -> failwith (sprintf "expected on of `pp`, `sexp`, or `rocq`; got %s" x)
  in
  let arg_type = Core.Command.Arg_type.create of_string in
  flag "pp"
    (optional_with_default `pp arg_type)
    ~doc:"mode RichWasm pretty printer (mode is `pp`, `sexp`, or `rocq`)"
    ~aliases:[ "pretty" ]

let richwasm_elab_flag =
  let open Command.Param in
  flag "elab"
    (optional_with_default true bool)
    ~doc:"Output elaborated "
    ~aliases:[ "elaborate"; "annotate" ]

let mk_ff () =
  let ff = formatter_of_out_channel Stdlib.stdout in
  pp_set_margin ff 80;
  pp_set_max_indent ff 80;
  ff

let handle_rw pp elab x =
  let ff = mk_ff () in
  (match elab with
  | true -> x |> elab_pipeline |> pp_rwasm_ann pp ff
  | false -> x |> pp_rwasm pp ff);
  fprintf ff "\n"

let ll2rw =
  Command.basic ~summary:"Compile a lin-lang module to RichWasm."
    (let%map_open.Command linlang = file_or_stdin "linlang"
     and pp = richwasm_pp_spec
     and elab = richwasm_elab_flag in
     fun () -> get_contents linlang |> ll_pipeline |> handle_rw pp elab)

let mml2rw =
  Command.basic ~summary:"Compile a mini-ml module to RichWasm."
    (let%map_open.Command miniml = file_or_stdin "miniml"
     and pp = richwasm_pp_spec in
     fun () ->
       ignore (miniml, pp);
       failwith "TODO")

let rw_elab =
  Command.basic
    ~summary:"Elaborate a RichWasm module (from sexp unannotated RichWasm)."
    (let%map_open.Command richwasm = file_or_stdin "richwasm"
     and pp = richwasm_pp_spec in
     fun () ->
       get_contents richwasm
       |> Parsexp.Single.parse_string_exn
       |> RichWasm.Module.t_of_sexp
       |> handle_rw pp true)

let rw2wasm =
  Command.basic ~summary:"Compile a RichWasm (sexp) module to wasm."
    (let%map_open.Command richwasm = file_or_stdin "richwasm" in
     fun () ->
       get_contents richwasm
       |> Parsexp.Single.parse_string_exn
       |> AnnRichWasm.Module.t_of_sexp
       |> Richwasm_common.Main.compile
       |> or_fail_pp Richwasm_common.Extract_compat.CompilerError.pp
       |> Richwasm_common.Main.wasm_ugly_printer
       |> print_endline)

let command =
  Command.group ~summary:"iris-richwasm"
    [
      ("ll2rw", ll2rw);
      ("mml2rw", mml2rw);
      ("rw-elab", rw_elab);
      ("rw2wasm", rw2wasm);
    ]

let () = Command_unix.run command
