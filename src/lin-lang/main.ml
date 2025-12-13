open! Base
open Stdlib.Format
module LinLangSyntax = Syntax
module RichWasmSyntax = Richwasm_common.Syntax

module CompileErr = struct
  type t =
    | Parse of Parse.Err.t
    | Index of Index.Err.t
    | Typecheck of Typecheck.Err.t
    | Cc of Cc.Compile.Err.t
    | Codegen of Codegen.Err.t
  [@@deriving sexp_of, variants]

  let pp ff x = Sexp.pp_hum ff (sexp_of_t x)
end

module Res = Util.LogResultM (CompileErr) (String)

type compile_res = RichWasmSyntax.Module.t Res.t

let ( >>? ) x (name, f, pp, err_map) =
  let open Res in
  let lift_result_map_err (r : ('a, 'e) Result.t) ~(err_map : 'e -> error) :
      'a t =
    match r with
    | Ok x -> ret x
    | Error e -> fail (err_map e)
  in

  let log_pp ~name (pp : formatter -> 'a -> unit) (x : 'a) : unit t =
    let len = String.length name in
    let lpad = Util.pad ~fill:'=' ((78 - len) / 2) in
    let rpad = lpad ^ if len % 2 = 0 then "" else "=" in
    tell
      (Ocolor_format.asprintf "@{<blue>%s@} @{<orange>%s@} @{<blue>%s@}@.%a"
         lpad name rpad pp x)
  in

  x >>= fun v ->
  lift_result_map_err (f v) ~err_map >>= fun out ->
  let+ () = log_pp ~name pp out in
  out

let compile_ast (ast : LinLangSyntax.Module.t) : compile_res =
  let open CompileErr in
  let module RWMod = RichWasmSyntax.Module in
  Res.ret ast
  >>? Index.("index", Compile.compile_module, IR.Module.pp, index)
  >>? Typecheck.("typecheck", Compile.compile_module, IR.Module.pp, typecheck)
  >>? Cc.("cc", Compile.compile_module, IR.Module.pp, cc)
  >>? Codegen.("codegen", Compile.compile_module, RWMod.pp, codegen)

let compile_str (str : string) : compile_res =
  let open Res in
  ret str
  >>? ("parse", Parse.from_string, Syntax.Module.pp, CompileErr.parse)
  >>= compile_ast
