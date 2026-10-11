open! Base
open Stdlib.Format
module W = Richwasm_workspace
module Common = Richwasm_common

let render pp x =
  let buf = Buffer.create 1024 in
  let ff = formatter_of_buffer buf in
  pp_set_margin ff 100;
  pp_set_max_indent ff 80;
  fprintf ff "%a@?" pp x;
  Buffer.contents buf

let ( let* ) r f = Result.bind r ~f

module Make (Asm : sig
  type wasm

  val wat2wasm : string -> (wasm, string) Result.t
  val wasm2wat : wasm -> (string, string) Result.t
end) =
struct
  let compile (lang : W.lang) (source : string) :
      W.stage list * (Asm.wasm * string option, string * string) Result.t =
    let stages = ref [] in
    let show title view pp x =
      stages := W.{ title; view; text = render pp x } :: !stages
    in
    let stage name pp r =
      Result.map_error r ~f:(fun e -> (name, render pp e))
    in
    let assemble wat =
      let* wasm = stage "wat2wasm" pp_print_string (Asm.wat2wasm wat) in
      let* pretty = stage "wasm2wat" pp_print_string (Asm.wasm2wat wasm) in
      show "Wasm" Wat pp_print_string pretty;
      Ok wasm
    in
    let through_rich_wasm front_end =
      let* rw = front_end in
      show "RichWasm" RichWasm_pretty Common.Syntax.Module.pp rw;
      let* ann =
        stage "elaborate" Common.Elaborate.Err.pp
          (Common.Elaborate.elab_module rw)
      in
      show "Elaborated" RichWasm_pretty Common.Annotated_syntax.Module.pp ann;
      let* () =
        stage "typecheck" Common.Main.pp_typecheck_errors
          (Common.Main.typecheck ann)
      in
      let* wasm_mod =
        stage "compile" Common.Extract_compat.CompilerError.pp
          (Common.Main.compile ann)
      in
      let* wasm = assemble (Common.Main.wasm_ugly_printer wasm_mod) in
      Ok (wasm, Common.Main.start_type_sexp rw)
    in
    let result =
      match lang with
      | MiniML ->
          through_rich_wasm
            (let open Richwasm_mini_ml in
             let* ast = stage "parse" Parse.Err.pp (Parse.from_string source) in
             stage "compile" Main.CompileErr.pp
               (fst (Main.Res.run (Main.compile_ast ast))))
      | LinLang ->
          through_rich_wasm
            (let open Richwasm_lin_lang in
             let* ast = stage "parse" Parse.Err.pp (Parse.from_string source) in
             stage "compile" Main.CompileErr.pp
               (fst (Main.Res.run (Main.compile_ast ast))))
      | RichWasm ->
          through_rich_wasm
            (let* sexp =
               stage "parse"
                 (Parsexp.Parse_error.report ~filename:"source")
                 (Parsexp.Single.parse_string source)
             in
             match Common.Syntax.Module.t_of_sexp sexp with
             | m -> Ok m
             | exception e -> Error ("parse", Exn.to_string e))
      | Wasm ->
          let* wasm = assemble source in
          Ok (wasm, None)
    in
    (List.rev !stages, result)
end
