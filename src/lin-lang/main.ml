open! Base
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

module Res = Util.ResultM (CompileErr)

type compile_res = RichWasmSyntax.Module.t Res.t

let compile_ast (ast : LinLangSyntax.Module.t) : compile_res =
  let open Res in
  let ( >>? ) x (f, map_err) =
    x >>= fun v -> f v |> Result.map_error ~f:map_err
  in

  Ok ast
  >>? (Index.Compile.compile_module, CompileErr.index)
  >>? (Typecheck.Compile.compile_module, CompileErr.typecheck)
  >>? (Cc.Compile.compile_module, CompileErr.cc)
  >>? (Codegen.Compile.compile_module, CompileErr.codegen)

let compile_str (str : string) : compile_res =
  let open Res in
  str
  |> Parse.from_string
  |> Result.map_error ~f:CompileErr.parse
  >>= compile_ast
