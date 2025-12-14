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

(* need rank2 polymorphism *)
type asprintf = { asprintf : 'a. ('a, formatter, unit, string) format4 -> 'a }

let ( >>? ) ~(asprintf : asprintf) m (name, f, pp, err_map) =
  let open Res in
  let log_pp x : unit t =
    let len = String.length name in
    let fill = '=' in
    tell
      (asprintf.asprintf "@{<blue>%a@} @{<orange>%s@} @{<blue>%a@}@.%a"
         (Util.pp_pad ~fill ~len) false name (Util.pp_pad ~fill ~len) true pp x)
  in

  m >>= fun x ->
  f x |> Result.map_error ~f:err_map |> lift_result >>= fun y ->
  log_pp y >>= fun () -> ret y

let compile_ast
    ?(asprintf : asprintf = { asprintf })
    (ast : LinLangSyntax.Module.t) : compile_res =
  let open CompileErr in
  let module RWMod = RichWasmSyntax.Module in
  let ( >>? ) x y = ( >>? ) ~asprintf x y in
  Res.ret ast
  >>? Index.("index", Compile.compile_module, IR.Module.pp, index)
  >>? Typecheck.("typecheck", Compile.compile_module, IR.Module.pp, typecheck)
  >>? Cc.("cc", Compile.compile_module, IR.Module.pp, cc)
  >>? Codegen.("codegen", Compile.compile_module, RWMod.pp, codegen)

let compile_str ?(asprintf : asprintf = { asprintf }) (str : string) :
    compile_res =
  let open Res in
  let ( >>? ) x y = ( >>? ) ~asprintf x y in
  ret str
  >>? ("parse", Parse.from_string, Syntax.Module.pp, CompileErr.parse)
  >>= compile_ast ~asprintf
